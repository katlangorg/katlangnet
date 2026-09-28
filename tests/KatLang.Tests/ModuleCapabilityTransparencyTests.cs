using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Rendering;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// PV-02 (semantic-constitution audit, September 2026): configuring a module downloader is a
/// CAPABILITY, never a meaning. Module elaboration transforms actual <c>load</c> directives and
/// nothing else, so a program without a directive — and every load-free subtree of a program
/// with one — means exactly what it means without a downloader: the same elaborated tree, the
/// same members, signatures, <c>open</c> provision, values, errors, host calls, and seeded draws,
/// on every route.
/// <para>
/// The defect: the loader re-applied the parser's definition-body merge (SYN-05) to EVERY
/// property by shape, so a written <c>A = { { public X = 1 ⏎ 5 } }</c> — which the parser had
/// already merged once — lost a second boundary whenever a downloader was configured, even for
/// source without a <c>load</c>: <c>A.X</c> read the nested member instead of falling back
/// (<c>S[1, 5]</c> instead of <c>S[100, 5]</c>) and <c>A = { { y + 1 } }</c> gained the parameter
/// <c>y</c>. The merge now happens only where it is meant to: a zero-parameter definition whose
/// WRITTEN body is exactly one directive (<c>P = load(u)</c>, and so <c>P = { load(u) }</c>) is
/// the module, exactly as <c>P = { module text }</c> is the block.
/// </para>
/// <para>
/// The oracle for load-free source is the synchronous public engine WITHOUT a downloader; for
/// load-bearing source it is the same engine running the program with each module written
/// inline. Host-only by nature: Lean models neither source loading nor host configuration, and
/// it already evaluates the no-downloader tree these tests prove every route elaborates.
/// </para>
/// </summary>
public class ModuleCapabilityTransparencyTests
{
    private const long Seed = 7;

    private const string BlockModule = "https://katlang.org/pv02/block.kat";
    private const string LibModule = "https://katlang.org/pv02/lib.kat";
    private const string NestedModule = "https://katlang.org/pv02/nested.kat";
    private const string PairModule = "https://katlang.org/pv02/pair.kat";
    private const string MembersModule = "https://katlang.org/pv02/members.kat";
    private const string MissingModule = "https://katlang.org/pv02/missing.kat";

    private const string BlockModuleText = "public X = 1\n5";
    private const string LibModuleText = "public Z = 41";

    // A module whose own text writes a nested property block: module content keeps its written
    // structure exactly like document content does.
    private const string NestedModuleText =
        "X(a) = 100\npublic P = {\n    {\n        public X = 1\n        5\n    }\n}\npublic Q = P.X";

    // ── The two audit reproductions, verbatim ──────────────────────────────────────────────

    private const string StructuralMemberRepro = """
        X(a) = 100

        A = {
            {
                public X = 1
                5
            }
        }

        A.X
        A
        """;

    private const string InferredSignatureRepro = """
        A = {
            {
                y + 1
            }
        }

        A(5)
        """;

    // ── Routes ─────────────────────────────────────────────────────────────────────────────

    public enum Route
    {
        /// <summary>The oracle: <see cref="KatLangEngine.Run"/> without a downloader.</summary>
        EngineSync,
        EngineAsync,
        EngineAsyncWithDownloader,
        EngineAsyncWithSuspendingDownloader,
        /// <summary>An async host operation is present, so the async twin evaluator runs.</summary>
        EngineAsyncTwinWithDownloader,
        GenericWithDownloader,
        OptimizedWithDownloader,
        ForcedTwinWithDownloader,
    }

    private static readonly Route[] LoadFreeRoutes = Enum.GetValues<Route>();

    // A tree carrying deferred module regions is async-only by contract (the synchronous
    // evaluators refuse it with InvalidOperationException), so deferred cases run these.
    private static readonly Route[] AsyncDownloaderRoutes =
    [
        Route.EngineAsyncWithDownloader,
        Route.EngineAsyncWithSuspendingDownloader,
        Route.EngineAsyncTwinWithDownloader,
        Route.ForcedTwinWithDownloader,
    ];

    private static readonly Route[] DownloaderRoutes =
    [
        .. AsyncDownloaderRoutes,
        Route.GenericWithDownloader,
        Route.OptimizedWithDownloader,
    ];

    private sealed record Observation(
        string Kind,
        Result? Value,
        int EmittedCount,
        IReadOnlyList<string> Codes,
        IReadOnlyList<string> HostCalls)
    {
        public override string ToString()
            => $"{Kind} {(Value is null ? "" : Neutral(Value))} n={EmittedCount} codes=[{string.Join(",", Codes)}] host=[{string.Join(",", HostCalls)}]";
    }

    private sealed class ModuleServer(params (string Url, string Source)[] modules)
    {
        private readonly Dictionary<string, string> _modules =
            modules.ToDictionary(module => module.Url, module => module.Source, StringComparer.Ordinal);

        public Dictionary<string, int> Fetches { get; } = new(StringComparer.Ordinal);

        public ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            Fetches[url] = Fetches.GetValueOrDefault(url) + 1;
            return _modules.TryGetValue(url, out var source)
                ? ValueTask.FromResult(source)
                : throw new InvalidOperationException($"404: {url}");
        }

        // Genuinely suspends source processing before every module arrives.
        public async ValueTask<string> DownloadSuspending(string url, CancellationToken cancellationToken)
        {
            await Task.Yield();
            return await Download(url, cancellationToken);
        }
    }

    private static ModuleServer Modules() => new(
        (BlockModule, BlockModuleText),
        (LibModule, LibModuleText),
        (NestedModule, NestedModuleText),
        (PairModule, "10, 20"),
        (MembersModule, "public P = 7\n3, 4"));

    private static HostOperations HostOperationsFor(List<string> hostCalls, bool withAsyncOperation)
    {
        var tick = HostOperation.Create("tick", (_, _) =>
        {
            hostCalls.Add("tick");
            return new Result.Atom((Decimal128)hostCalls.Count);
        });
        return withAsyncOperation
            ? HostOperations.Create(tick, HostOperation.CreateAsync("pause", async (_, _) =>
            {
                await Task.Yield();
                return new Result.Atom((Decimal128)0);
            }))
            : HostOperations.Create(tick);
    }

    private static RunOptions OptionsFor(
        Route route,
        List<string> hostCalls,
        ModuleServer modules)
    {
        Func<string, CancellationToken, ValueTask<string>>? downloader = route switch
        {
            Route.EngineSync or Route.EngineAsync => null,
            Route.EngineAsyncWithSuspendingDownloader => modules.DownloadSuspending,
            _ => modules.Download,
        };
        var asyncOperation = route is Route.EngineAsyncTwinWithDownloader or Route.ForcedTwinWithDownloader;
        return new RunOptions
        {
            RandomSeed = Seed,
            HostOperations = HostOperationsFor(hostCalls, asyncOperation),
            DownloadCode = downloader,
        };
    }

    private static async Task<Observation> ObserveAsync(Route route, string source, ModuleServer modules)
    {
        var hostCalls = new List<string>();
        var options = OptionsFor(route, hostCalls, modules);
        switch (route)
        {
            case Route.EngineSync:
                return FromRunResult(KatLangEngine.Run(source, options), hostCalls);
            case Route.EngineAsync:
            case Route.EngineAsyncWithDownloader:
            case Route.EngineAsyncWithSuspendingDownloader:
            case Route.EngineAsyncTwinWithDownloader:
                return FromRunResult(await KatLangEngine.RunAsync(source, options), hostCalls);
        }

        var parsed = await Parser.ParseAsync(source, options);
        if (parsed.HasErrors)
        {
            return new Observation(
                "parseFailure",
                null,
                0,
                [.. parsed.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).Select(d => d.Code.ToString())],
                [.. hostCalls]);
        }

        var program = new Expr.AlgorithmExpr(parsed.Root);
        var (result, _) = route switch
        {
            Route.GenericWithDownloader => Evaluator.RunCountedObserved(
                program, enableOptimizations: false, hostOperations: options.HostOperations, randomSeed: Seed),
            Route.OptimizedWithDownloader => Evaluator.RunCountedObserved(
                program, enableOptimizations: true, hostOperations: options.HostOperations, randomSeed: Seed),
            Route.ForcedTwinWithDownloader => await Evaluator.RunCountedObservedAsync(
                program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                hostOperations: options.HostOperations,
                randomSeed: Seed),
            _ => throw new ArgumentOutOfRangeException(nameof(route), route, null),
        };

        return result.IsError
            ? new Observation("evalFailure", null, 0, [KatLangError.FromEvalError(result.Error).Code.ToString()], [.. hostCalls])
            : new Observation("ok", result.Value.Value, result.Value.EmittedCount, [], [.. hostCalls]);
    }

    private static Observation FromRunResult(RunResult result, List<string> hostCalls) => result switch
    {
        RunResult.Success success => new("ok", success.Value, success.EmittedCount, [], [.. hostCalls]),
        RunResult.EvalFailure failure => new("evalFailure", null, 0, [.. failure.Errors.Select(error => error.Code.ToString())], [.. hostCalls]),
        RunResult.ParseFailure failure => new("parseFailure", null, 0, [.. failure.Errors.Select(error => error.Code.ToString())], [.. hostCalls]),
        RunResult.NoProgramOutput none => new("noOutput", null, 0, [none.Diagnostic.Code.ToString()], [.. hostCalls]),
    };

    private static void AssertSameObservation(Observation expected, Observation actual, string context)
    {
        Assert.True(
            expected.Kind == actual.Kind
                && expected.EmittedCount == actual.EmittedCount
                && (expected.Value is null
                    ? actual.Value is null
                    : actual.Value is not null && Result.ValueComparer.Equals(expected.Value, actual.Value))
                && expected.Codes.SequenceEqual(actual.Codes)
                && expected.HostCalls.SequenceEqual(actual.HostCalls),
            $"{context}: expected {expected}, got {actual}");
    }

    private static string Neutral(Result value) => value switch
    {
        Result.Atom atom => ValueTextRenderer.FormatNumberInvariant(atom.Value),
        Result.Str text => "'" + text.Value + "'",
        Result.Bool boolean => boolean.Value ? "true" : "false",
        Result.SequenceValue sequence => "S[" + string.Join(", ", sequence.Items.Select(Neutral)) + "]",
        Result.ListValue list => "L[" + string.Join(", ", list.Items.Select(Neutral)) + "]",
    };

    /// <summary>
    /// Runs <paramref name="source"/> on every route in <paramref name="routes"/> and requires the
    /// oracle observation on each; returns the oracle for further assertions.
    /// </summary>
    private static async Task<Observation> AssertEveryRouteMatchesAsync(
        Observation oracle,
        string source,
        IEnumerable<Route> routes,
        ModuleServer modules)
    {
        foreach (var route in routes)
            AssertSameObservation(oracle, await ObserveAsync(route, source, modules), route.ToString());
        return oracle;
    }

    private static void AssertOk(Observation observation, string expectedNeutral, params string[] expectedHostCalls)
    {
        Assert.True(observation.Kind == "ok", $"expected success, got {observation}");
        Assert.Equal(expectedNeutral, Neutral(observation.Value!));
        Assert.Equal(expectedHostCalls, observation.HostCalls);
    }

    private static void AssertEvalFailure(Observation observation, KatLangErrorCode expected)
    {
        Assert.True(observation.Kind == "evalFailure", $"expected an evaluation failure, got {observation}");
        Assert.Equal([expected.ToString()], observation.Codes);
    }

    private static ParseResult ParseClean(string source, RunOptions options)
    {
        var parsed = Parser.Parse(source, options);
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        return parsed;
    }

    private static async Task<ParseResult> ParseCleanAsync(string source, RunOptions options)
    {
        var parsed = await Parser.ParseAsync(source, options);
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        return parsed;
    }

    private static RunOptions ParseOptions(Func<string, CancellationToken, ValueTask<string>>? downloader = null)
        => new() { HostOperations = HostOperationsFor([], withAsyncOperation: false), DownloadCode = downloader };

    // ── Test A / Test B: the audit reproductions on every route ─────────────────────────────

    [Fact]
    public async Task StructuralMemberRepro_NestedBlockStaysABoundary_WithAndWithoutADownloader()
    {
        var modules = Modules();
        var oracle = await ObserveAsync(Route.EngineSync, StructuralMemberRepro, modules);
        // X is not a direct member of A — the written inner block owns it — so A.X falls back
        // to the lexical X(a).
        AssertOk(oracle, "S[100, 5]");
        await AssertEveryRouteMatchesAsync(oracle, StructuralMemberRepro, LoadFreeRoutes, modules);
        Assert.Empty(modules.Fetches);
    }

    [Fact]
    public async Task InferredSignatureRepro_InnerBlockOwnsItsFreeName_WithAndWithoutADownloader()
    {
        var modules = Modules();
        var oracle = await ObserveAsync(Route.EngineSync, InferredSignatureRepro, modules);
        // y belongs to the written inner block, so A declares no parameter and A(5) is an
        // arity error on every route — never 6.
        AssertEvalFailure(oracle, KatLangErrorCode.ArityMismatch);
        await AssertEveryRouteMatchesAsync(oracle, InferredSignatureRepro, LoadFreeRoutes, modules);
        Assert.Empty(modules.Fetches);
    }

    // ── Test C: ownership, members, open provision, signatures, effects ─────────────────────

    public static TheoryData<string, string, string, string[]> LoadFreePrograms => new()
    {
        {
            // public and private members, output, and lookup from outside: the nested block's
            // members are not A's; Inner (one written brace) is the block itself.
            "ownership-public-private-output",
            """
            X(a) = 100
            Hidden(a) = 200
            A = {
                {
                    public X = 1
                    Hidden = 2
                    X + Hidden
                }
            }
            Inner = {
                public X = 10
                Hidden = 20
                X + Hidden
            }
            A.X, A.Hidden, A, Inner.X, Inner.Hidden, Inner
            """,
            "S[100, 200, 3, 10, 20, 30]",
            []
        },
        {
            // open provision: A has no member V, so B's V stays B's own inferred parameter.
            "open-provider",
            """
            A = {
                {
                    public V = 3
                    V
                }
            }
            B = {
                open A
                V + 1
            }
            B(10), A
            """,
            "S[11, 3]",
            []
        },
        {
            // an explicit parameter owner and a nested property body
            "explicit-parameter-owner",
            """
            X(a) = 7
            F(k) = {
                P = {
                    {
                        public X = k * 10
                        0
                    }
                }
                P.X
            }
            F(3)
            """,
            "7",
            []
        },
        {
            // the same text in a clause-family branch and in an ordinary body
            "family-branch-and-ordinary-body",
            """
            X(a) = 100
            F(0) = {
                P = {
                    {
                        public X = 1
                        5
                    }
                }
                P.X
            }
            F(n) = n
            G = {
                P = {
                    {
                        public X = 1
                        5
                    }
                }
                P.X
            }
            F(0), F(9), G
            """,
            "S[100, 9, 100]",
            []
        },
        {
            // one host call, one cached property, the member access falls back
            "host-effects-and-cache",
            """
            V(a) = 7
            A = {
                {
                    public V = tick()
                    V + 100
                }
            }
            A, A.V, A
            """,
            "S[101, 7, 101]",
            ["tick"]
        },
        {
            // three levels of written nesting, one-line nesting, a parameter receiver, and
            // collection consumers
            "deeper-nesting-and-consumers",
            """
            X(a) = 100
            A = {
                {
                    {
                        public X = 1
                        5
                    }
                }
            }
            B = { { public X = 2 } }
            H(q) = q.X
            A.X, A, B.X, H(A), count(A), [A]
            """,
            "S[100, 5, 100, 100, 1, L[5]]",
            []
        },
    };

    [Theory]
    [MemberData(nameof(LoadFreePrograms))]
    public async Task LoadFreeSource_MeansTheSameOnEveryRoute_WithAndWithoutADownloader(
        string id, string source, string expected, string[] expectedHostCalls)
    {
        _ = id;
        var modules = Modules();
        ParseClean(source, ParseOptions());
        var oracle = await ObserveAsync(Route.EngineSync, source, modules);
        AssertOk(oracle, expected, expectedHostCalls);
        await AssertEveryRouteMatchesAsync(oracle, source, LoadFreeRoutes, modules);
        Assert.Empty(modules.Fetches);
    }

    [Fact]
    public async Task SeededDraws_InALoadFreeNestedBlock_AreIdenticalWithAndWithoutADownloader()
    {
        const string source = """
            V(a) = 7
            A = {
                {
                    public V = randomInt(0, 1000000)
                    V
                }
            }
            A, A.V, A
            """;
        var modules = Modules();
        var oracle = await ObserveAsync(Route.EngineSync, source, modules);
        var items = Assert.IsType<Result.SequenceValue>(oracle.Value).Items;
        Assert.Equal(3, items.Count);
        Assert.Equal("7", Neutral(items[1]));
        Assert.True(Result.ValueComparer.Equals(items[0], items[2]));
        await AssertEveryRouteMatchesAsync(oracle, source, LoadFreeRoutes, modules);
    }

    // ── Structure and editor: the elaborated program itself is the same ─────────────────────

    public static TheoryData<string> LoadFreeSources => new()
    {
        StructuralMemberRepro,
        InferredSignatureRepro,
        "X(a) = 100\nA = { { public X = 1 } }\nA.X",
        "A = {\n    {\n        public V = 3\n        V\n    }\n}\nB = {\n    open A\n    V + 1\n}\nB(10), A",
        "X(a) = 7\nF(0) = {\n    P = {\n        {\n            public X = 1\n        }\n    }\n    P.X\n}\nF(n) = n\nF(0), F(4)",
    };

    [Theory]
    [MemberData(nameof(LoadFreeSources))]
    public async Task LoadFreeSource_ElaboratesToTheSameTree_WithAndWithoutADownloader(string source)
    {
        var modules = Modules();
        var withoutDownloader = ParseClean(source, ParseOptions());
        var withDownloader = await ParseCleanAsync(source, ParseOptions(modules.Download));

        Assert.Equal(
            LeanAstEncoder.EncodeProgram(withoutDownloader.Root),
            LeanAstEncoder.EncodeProgram(withDownloader.Root));
        Assert.Empty(modules.Fetches);
    }

    [Fact]
    public async Task WrittenNestedBlock_IsNeverMergedIntoItsDefinition_ByModuleElaboration()
    {
        var modules = Modules();
        foreach (var parsed in new[]
                 {
                     ParseClean(StructuralMemberRepro, ParseOptions()),
                     await ParseCleanAsync(StructuralMemberRepro, ParseOptions(modules.Download)),
                 })
        {
            // A is the OUTER written block: no members of its own, one output row that is the
            // inner written block, which declares the public X.
            var a = Assert.IsType<Algorithm.User>(Assert.Single(parsed.Root.Properties, p => p.Name == "A").Value);
            Assert.Empty(a.Properties);
            var inner = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(a.Output)).Algorithm;
            var x = Assert.Single(inner.Properties);
            Assert.Equal("X", x.Name);
            Assert.True(x.IsPublic);
        }
    }

    [Fact]
    public async Task EditorResolution_OfTheDotMember_IsTheSameWithAndWithoutADownloader()
    {
        // RES-09: the editor model of a downloader parse selects what the plain parse selects —
        // the member X of `A.X` is the lexical X(a) on line 1, never the nested block's X.
        var modules = Modules();
        var models = new[]
        {
            SemanticModelBuilder.Build(ParseClean(StructuralMemberRepro, ParseOptions())),
            SemanticModelBuilder.Build(await ParseCleanAsync(StructuralMemberRepro, ParseOptions(modules.Download))),
        };
        var lines = StructuralMemberRepro.Split('\n');
        var row = Array.FindIndex(lines, line => line.TrimEnd('\r') == "A.X") + 1;
        foreach (var model in models)
        {
            var resolution = model.FindResolutionAt(new SourcePosition(row, 3));
            Assert.NotNull(resolution);
            var declaration = Assert.IsType<DeclarationOccurrence>(resolution.ResolvedDeclaration);
            Assert.Equal(new SourcePosition(1, 1), declaration.Span.Start);
        }
    }

    // ── Test D / Test E: real module loading keeps its meaning ──────────────────────────────

    public static TheoryData<string, string, string, string> LoadBearingPrograms => new()
    {
        {
            // A zero-parameter definition written as exactly one directive IS the module —
            // `P = { load(u) }` is the same body (SYN-05), and so is the redundant group.
            "directive-body-is-the-module",
            $"X(a) = 100\nP = load('{BlockModule}')\nQ = {{ load('{BlockModule}') }}\nR = (load('{BlockModule}'))\nP.X, P, Q.X, Q, R.X, R",
            $"X(a) = 100\nP = {{ {BlockModuleText} }}\nQ = {{ {BlockModuleText} }}\nR = {{ {BlockModuleText} }}\nP.X, P, Q.X, Q, R.X, R",
            "S[1, 5, 1, 5, 1, 5]"
        },
        {
            // A directive inside a written nested block is replaced where it stands; the
            // written boundaries around it stay.
            "nested-directive-keeps-the-written-nesting",
            $"X(a) = 100\nP = {{ {{ load('{BlockModule}') }} }}\nP.X, P",
            $"X(a) = 100\nP = {{ {{ {{ {BlockModuleText} }} }} }}\nP.X, P",
            "S[100, 5]"
        },
        {
            // module TEXT keeps its own written nesting too
            "module-text-keeps-its-nesting",
            $"M = load('{NestedModule}')\nM.Q, M.P",
            $"M = {{\n{NestedModuleText}\n}}\nM.Q, M.P",
            "S[100, 5]"
        },
        {
            // an unrelated load elsewhere leaves every load-free subtree as written
            "unrelated-root-load",
            $"L = load('{LibModule}')\nX(a) = 100\nA = {{\n    {{\n        public X = 1\n        5\n    }}\n}}\nA.X, A, L.Z",
            $"L = {{ {LibModuleText} }}\nX(a) = 100\nA = {{\n    {{\n        public X = 1\n        5\n    }}\n}}\nA.X, A, L.Z",
            "S[100, 5, 41]"
        },
        {
            // a load inside the nested block itself
            "load-inside-the-nested-block",
            $"X(a) = 100\nA = {{\n    {{\n        L = load('{LibModule}')\n        public X = 1\n        5 + L.Z\n    }}\n}}\nA.X, A",
            $"X(a) = 100\nA = {{\n    {{\n        L = {{ {LibModuleText} }}\n        public X = 1\n        5 + L.Z\n    }}\n}}\nA.X, A",
            "S[100, 46]"
        },
        {
            // a load beside a nested property block inside a parameterized definition
            "load-beside-a-nested-block-in-a-parameterized-body",
            $"X(a) = 7\nF(k) = {{\n    L = load('{LibModule}')\n    P = {{\n        {{\n            public X = k * 10\n            0\n        }}\n    }}\n    P.X + L.Z\n}}\nF(3)",
            $"X(a) = 7\nF(k) = {{\n    L = {{ {LibModuleText} }}\n    P = {{\n        {{\n            public X = k * 10\n            0\n        }}\n    }}\n    P.X + L.Z\n}}\nF(3)",
            "48"
        },
        {
            // `open load(u)` and its `open 'u'` sugar
            "open-load-forms",
            $"A = {{\n    open load('{BlockModule}')\n    X\n}}\nB = {{\n    open '{BlockModule}'\n    X\n}}\nA, B",
            $"A = {{\n    open {{ {BlockModuleText} }}\n    X\n}}\nB = {{\n    open {{ {BlockModuleText} }}\n    X\n}}\nA, B",
            "S[1, 1]"
        },
        {
            // opening module text that writes its own nested block
            "open-module-with-nested-text",
            $"open '{NestedModule}'\nQ, P",
            $"open {{\n{NestedModuleText}\n}}\nQ, P",
            "S[100, 5]"
        },
        {
            // forms the fix leaves exactly as they were: deconstruction keeps its written
            // right-hand side, a parameterized definition keeps the module as one nested block
            // output (MOD-07's zero-parameter caveat)
            "unchanged-deconstruction-and-parameterized-forms",
            $"a, b = load('{PairModule}')\nF(y) = load('{MembersModule}')\na + b, F(1)",
            "a, b = { 10, 20 }\nF(y) = { { public P = 7\n3, 4 } }\na + b, F(1)",
            "S[30, S[3, 4]]"
        },
    };

    [Theory]
    [MemberData(nameof(LoadBearingPrograms))]
    public async Task LoadBearingSource_MeansWhatItsInlineTextMeans_OnEveryDownloaderRoute(
        string id, string source, string inline, string expected)
    {
        _ = id;
        var modules = Modules();
        ParseClean(inline, ParseOptions());
        await ParseCleanAsync(source, ParseOptions(modules.Download));

        var oracle = await ObserveAsync(Route.EngineSync, inline, modules);
        AssertOk(oracle, expected);
        await AssertEveryRouteMatchesAsync(oracle, source, DownloaderRoutes, modules);
    }

    [Fact]
    public async Task DirectiveBody_IsTheSplicedModule_WhileAWrittenNestingAroundADirectiveIsKept()
    {
        var modules = Modules();
        var parsed = await ParseCleanAsync(
            $"P = load('{BlockModule}')\nQ = {{ load('{BlockModule}') }}\nN = {{ {{ load('{BlockModule}') }} }}\nP, Q, N",
            ParseOptions(modules.Download));
        Algorithm Value(string name) => Assert.Single(parsed.Root.Properties, p => p.Name == name).Value;

        foreach (var name in new[] { "P", "Q" })
        {
            var module = Assert.IsType<Algorithm.User>(Value(name));
            Assert.True(module.IsModuleElaborated, $"{name} should be the spliced module itself.");
            Assert.Equal("X", Assert.Single(module.Properties).Name);
        }

        // N keeps both written braces: its body is a wrapper whose one row is the written inner
        // block, whose one row is the spliced module.
        var n = Assert.IsType<Algorithm.User>(Value("N"));
        Assert.False(n.IsModuleElaborated);
        Assert.Empty(n.Properties);
        var written = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(n.Output)).Algorithm);
        Assert.False(written.IsModuleElaborated);
        var spliced = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(written.Output)).Algorithm);
        Assert.True(spliced.IsModuleElaborated);
    }

    // ── Test F: branch-lazy (deferred) module regions ───────────────────────────────────────

    private const string NestedBranchBody = """
            P = {
                {
                    public X = 1
                    5
                }
            }
        """;

    public static TheoryData<string, string, string, string> DeferredPrograms => new()
    {
        {
            // A selected branch that owns an unrelated load: its load-free nested block is kept,
            // exactly like the same text in an ordinary body and in the eager inline program.
            "selected-branch-with-an-unrelated-load",
            $"X(a) = 100\nF(0) = {{\n    L = load('{LibModule}')\n{NestedBranchBody}\n    P.X + L.Z\n}}\nF(n) = n\nG = {{\n{NestedBranchBody}\n    P.X\n}}\nF(0), F(9), G",
            $"X(a) = 100\nF(0) = {{\n    L = {{ {LibModuleText} }}\n{NestedBranchBody}\n    P.X + L.Z\n}}\nF(n) = n\nG = {{\n{NestedBranchBody}\n    P.X\n}}\nF(0), F(9), G",
            "S[141, 9, 100]"
        },
        {
            // A never-selected branch performs no module work; the load-free rest is as written.
            "unselected-branch-with-a-missing-module",
            $"X(a) = 100\nF(0) = {{\n    L = load('{MissingModule}')\n    L.Z\n}}\nF(n) = n\nG = {{\n{NestedBranchBody}\n    P.X\n}}\nF(9), G",
            $"X(a) = 100\nF(0) = {{\n    L = {{ {LibModuleText} }}\n    L.Z\n}}\nF(n) = n\nG = {{\n{NestedBranchBody}\n    P.X\n}}\nF(9), G",
            "S[9, 100]"
        },
        {
            // A directive body inside a materialized branch is the module exactly as eagerly
            // (G's single-clause body elaborates the same text eagerly).
            "directive-body-in-a-materialized-branch",
            $"F(0) = {{\n    P = load('{BlockModule}')\n    P.X\n}}\nF(n) = n\nG(z) = {{\n    P = load('{BlockModule}')\n    P.X + z\n}}\nF(0), F(2), G(0)",
            $"F(0) = {{\n    P = {{ {BlockModuleText} }}\n    P.X\n}}\nF(n) = n\nG(z) = {{\n    P = {{ {BlockModuleText} }}\n    P.X + z\n}}\nF(0), F(2), G(0)",
            "S[1, 2, 1]"
        },
    };

    [Theory]
    [MemberData(nameof(DeferredPrograms))]
    public async Task DeferredBranchSource_MeansWhatItsInlineTextMeans(
        string id, string source, string inline, string expected)
    {
        _ = id;
        var modules = Modules();
        ParseClean(inline, ParseOptions());
        await ParseCleanAsync(source, ParseOptions(modules.Download));

        var oracle = await ObserveAsync(Route.EngineSync, inline, modules);
        AssertOk(oracle, expected);
        await AssertEveryRouteMatchesAsync(oracle, source, AsyncDownloaderRoutes, modules);
        Assert.Equal(0, modules.Fetches.GetValueOrDefault(MissingModule));
    }

    // These cases distinguish directive identity from output shape, including negative
    // controls where the module has the same value but must not become P's member provider.
    [Theory]
    [InlineData("P = $LOAD", "P = $MODULE", true)]
    [InlineData("P = { $LOAD }", "P = $MODULE", true)]
    [InlineData("P = (($LOAD))", "P = $MODULE", true)]
    [InlineData("P = ({ ($LOAD) })", "P = $MODULE", true)]
    [InlineData("P = { { $LOAD } }", "P = { { $MODULE } }", false)]
    [InlineData("P(x) = $LOAD", "P(x) = { $MODULE }", false)]
    [InlineData("P(*xs) = $LOAD", "P(*xs) = { $MODULE }", false)]
    [InlineData("P = { K = 9\n$LOAD }", "P = { K = 9\n$MODULE }", false)]
    [InlineData("P = { $LOAD\nK = 9 }", "P = { $MODULE\nK = 9 }", false)]
    [InlineData("P = { open { public K = 9 }\n$LOAD }", "P = { open { public K = 9 }\n$MODULE }", false)]
    [InlineData("P = $LOAD, 9", "P = $MODULE, 9", false)]
    [InlineData("P = ($LOAD*)", "P = ($MODULE*)", false)]
    [InlineData("P = [$LOAD]", "P = [$MODULE]", false)]
    [InlineData("P = $LOAD.X", "P = $MODULE.X", false)]
    [InlineData("P = { X = $LOAD\nX }", "P = { X = $MODULE\nX }", false)]
    public async Task DirectiveBodyRecognition_PreservesEveryOtherOwner(
        string sourceTemplate, string inlineTemplate, bool isModule)
    {
        var source = sourceTemplate.Replace("$LOAD", $"load('{BlockModule}')");
        var inline = inlineTemplate.Replace("$MODULE", $"{{ {BlockModuleText} }}");
        var oracle = ParseClean(inline, ParseOptions());
        foreach (var suspending in new[] { false, true })
        {
            var modules = Modules();
            var parsed = await ParseCleanAsync(source,
                ParseOptions(suspending ? modules.DownloadSuspending : modules.Download));
            var p = Assert.IsType<Algorithm.User>(Assert.Single(parsed.Root.Properties, p => p.Name == "P").Value);
            Assert.Equal(isModule, p.IsModuleElaborated);
            Assert.Equal(LeanAstEncoder.EncodeProgram(oracle.Root), LeanAstEncoder.EncodeProgram(parsed.Root));
            Assert.Equal(1, Assert.Single(modules.Fetches).Value);
            if (source.StartsWith("P(", StringComparison.Ordinal))
                Assert.True(p.HasExplicitParameterList);
        }
    }

    [Fact]
    public async Task LoadFreeWalk_IsObserved_AndKeepsDeclarationIdentityAndStructure()
    {
        // Observe the actual loader stage directly, alongside the public-pipeline tests above:
        // an unused mock downloader alone is not evidence that this walk executed.
        var raw = SourceProvenance.ParseSyntaxValidRoot(StructuralMemberRepro);
        var written = Assert.Single(raw.Properties, p => p.Name == "A").Value;
        var observations = new FrontEndTraversalObservations();
        var diagnostics = new DiagnosticBag();
        var modules = Modules();
        var loader = new ModuleLoader(diagnostics, modules.Download) { TraversalObservations = observations };
        var loaded = await loader.ElaborateAsync(raw);
        Assert.True(observations.LoaderWalkExpansions > 0);
        Assert.Empty(diagnostics);
        Assert.Empty(modules.Fetches);
        Assert.Equal(LeanAstEncoder.EncodeProgram(raw), LeanAstEncoder.EncodeProgram(loaded));
        Assert.Same(written.Declaration, Assert.Single(loaded.Properties, p => p.Name == "A").Value.Declaration);
    }

    [Theory]
    [InlineData("load('$URL')", "$MODULE", "S[1, 5]")]
    [InlineData("{ load('$URL') }", "$MODULE", "S[1, 5]")]
    [InlineData("{ { load('$URL') } }", "{ { $MODULE } }", "S[100, 5]")]
    public async Task RecursiveModuleText_MergesOnlyItsOwnDirectives(
        string body, string inlineBody, string expected)
    {
        var remote = "public Q = " + body.Replace("$URL", BlockModule);
        var inline = "X(a) = 100\nM = { public Q = "
            + inlineBody.Replace("$MODULE", $"{{ {BlockModuleText} }}") + " }\nM.Q.X, M.Q";
        var source = $"X(a) = 100\nM = load('{NestedModule}')\nM.Q.X, M.Q";
        var oracle = await ObserveAsync(Route.EngineSync, inline, Modules());
        AssertOk(oracle, expected);
        foreach (var route in DownloaderRoutes)
        {
            var modules = new ModuleServer((NestedModule, remote), (BlockModule, BlockModuleText));
            AssertSameObservation(oracle, await ObserveAsync(route, source, modules), route.ToString());
            Assert.Equal(1, modules.Fetches[NestedModule]);
            Assert.Equal(1, modules.Fetches[BlockModule]);
        }
        var parsed = await ParseCleanAsync(source,
            ParseOptions(new ModuleServer((NestedModule, remote), (BlockModule, BlockModuleText)).Download));
        Assert.Equal(LeanAstEncoder.EncodeProgram(ParseClean(inline, ParseOptions()).Root),
            LeanAstEncoder.EncodeProgram(parsed.Root));
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("host-refused")]
    [InlineData("malformed")]
    [InlineData("nonliteral")]
    [InlineData("wrong-arity")]
    [InlineData("runtime-position")]
    public async Task RefusedDirective_KeepsItsWrittenBody_OnBothDownloaderCompletionModes(string failure)
    {
        var directive = failure switch
        {
            "host-refused" => "load('https://refused.invalid/m.kat')",
            "nonliteral" => "load(u)",
            "wrong-arity" => "load()",
            "runtime-position" => $"1 + load('{MissingModule}')",
            _ => $"load('{MissingModule}')",
        };
        var source = $"P = {directive}\n{StructuralMemberRepro}";
        SourceProvenance.ParseSyntaxValidRoot(source);
        var expectedCode = failure switch
        {
            "host-refused" => DiagnosticCode.InvalidLoadUrl,
            "malformed" => DiagnosticCode.InvalidLoadedSource,
            "missing" => DiagnosticCode.LoadFetchFailed,
            _ => DiagnosticCode.InvalidLoadDirective,
        };
        // The missing-module pipeline is deliberately provisional; compare its structure,
        // not the different diagnostics for unavailable versus refused acquisition.
        var unavailable = Parser.Parse(source);
        Assert.True(unavailable.HasErrors);
        foreach (var suspending in new[] { false, true })
        {
            var modules = failure == "malformed"
                ? new ModuleServer((MissingModule, "public X = (")) : Modules();
            var options = ParseOptions(suspending ? modules.DownloadSuspending : modules.Download);
            var refused = await Parser.ParseAsync(source, options);
            Assert.True(refused.HasErrors);
            Assert.Equal([expectedCode], refused.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).Select(d => d.Code));
            Assert.Equal(LeanAstEncoder.EncodeProgram(unavailable.Root), LeanAstEncoder.EncodeProgram(refused.Root));
            var p = Assert.IsType<Algorithm.User>(Assert.Single(refused.Root.Properties, p => p.Name == "P").Value);
            Assert.False(p.IsModuleElaborated);
            Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, options));
            if (failure is "host-refused" or "nonliteral" or "wrong-arity" or "runtime-position")
                Assert.Empty(modules.Fetches);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CanonicalAliasesShareCachedDraw_WhileInlineOpenKeepsItsOwner(bool inlineOpen)
    {
        const string moduleText = "public V = randomInt(0, 1000000)";
        var open = inlineOpen ? $"open load('{BlockModule}')" : "open A";
        var source = $"{open}\nA = load('{BlockModule}')\nB = load('https://KATLANG.ORG:443/pv02/./block.kat#alias')\nA.V, B.V, V, randomInt(0, 1000000)";
        // An inline open provider has its own lexical owner (MOD-06). Named open A
        // navigates A instead. Keep that established difference in the independent oracle.
        var inline = inlineOpen ? $"open {{ {moduleText} }}" : "open A";
        var oracle = await ObserveAsync(Route.EngineSync,
            $"{inline}\nA = {{ {moduleText} }}\nA.V, A.V, V, randomInt(0, 1000000)", Modules());
        Assert.Equal("ok", oracle.Kind);
        foreach (var route in DownloaderRoutes)
        {
            var modules = new ModuleServer((BlockModule, moduleText));
            AssertSameObservation(oracle, await ObserveAsync(route, source, modules), route.ToString());
            Assert.Equal(1, Assert.Single(modules.Fetches).Value);
        }
        var parsed = await ParseCleanAsync(source, ParseOptions(new ModuleServer((BlockModule, moduleText)).Download));
        var a = Assert.Single(parsed.Root.Properties, p => p.Name == "A").Value;
        var b = Assert.Single(parsed.Root.Properties, p => p.Name == "B").Value;
        Assert.Same(a.Declaration, b.Declaration);
        if (inlineOpen)
        {
            var opened = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(parsed.Root.Opens)).Algorithm;
            Assert.Same(a.Declaration, opened.Declaration);
        }
    }

    [Theory]
    [InlineData("A = { { x + y } }\nA(5)")]
    [InlineData("A(z) = { { x + y + z } }\nA(5)")]
    [InlineData("A(*xs) = { { xs.count } }\nA(1, 2)")]
    [InlineData("A = { { map([1, 2], { x + 1 }) } }\nA")]
    [InlineData("A = { { x.F(y) } }\nA(5)")]
    [InlineData("A = { { X = 2\nX + y } }\nA(5)")]
    public async Task InferenceAndCallbacks_KeepTheirOwners_WhenLoadingIsUnused(string source)
    {
        var modules = Modules();
        var without = ParseClean(source, ParseOptions());
        var with = await ParseCleanAsync(source, ParseOptions(modules.Download));
        Assert.Equal(LeanAstEncoder.EncodeProgram(without.Root), LeanAstEncoder.EncodeProgram(with.Root));
        var oracle = await ObserveAsync(Route.EngineSync, source, modules);
        await AssertEveryRouteMatchesAsync(oracle, source, LoadFreeRoutes, modules);
        Assert.Empty(modules.Fetches);
    }
}
