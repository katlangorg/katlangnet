using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// A DEFERRED BRANCH THAT REACHES A MODULE THE PROGRAM ALREADY ELABORATED (constitution MOD-10; Q-31 H-P and
/// Q-32 I-U). One canonical URL is ONE module declaration per compiled program, elaborated and validated ONCE:
/// the units of an error-free operation are published to the loader's <see cref="ModuleUnitRegistry"/>, and a
/// later operation (a deferred branch's materialization) that splices the same module receives the very
/// declaration, pass by pass.
///
/// <para>That reach used to throw out of <see cref="KatLangEngine.RunAsync"/>. Between its own resolution and
/// its own exposure a materialized unit holds a received module as the RESOLVED view the earlier operation
/// published, while the lookup facts it inherits name every body of that module by its CLASSIFIED view
/// (exposure replaced the resolved ones when that operation completed). Three consumers of the unit's
/// open-provider validation asked those facts about the resolved view:</para>
/// <list type="bullet">
///   <item>the WALK INTO the module built a level bound to no facts, and the first open list below it asked for a
///   standalone analysis the chain cannot give: <see cref="InvalidOperationException"/>, "Standalone structural
///   lookup requires explicit source phase/admission provenance." (a module with an open anywhere in it);</item>
///   <item>a DOTTED OPEN PATH whose head names an in-branch holder of the module was refused as a supplied
///   view: <see cref="ArgumentException"/>, "The supplied view requires its own explicit structural
///   admission." (any module, a valid path included);</item>
///   <item>the DESCRIPTION of an unresolvable block-headed path through the module found it unavailable and
///   stayed silent: no exception, the target was dropped and the branch ran (constitution PV-11 broken).</item>
/// </list>
/// <para>Now the unit's open-provider validation does not walk a module an earlier operation completed
/// (<see cref="ModuleUnitRegistry.HasCompleted"/>: it was validated there, once), and the facts answer for the
/// view a module root held before exposure replaced it (<c>CompletedStaticStructures.MarkSupersededModuleView</c>).</para>
///
/// <para><b>The oracle is a twin.</b> Each program is paired with one in which the branch reaches the module
/// FIRST (its control: nothing else loaded it, the path that always worked) or in which nothing is deferred (its
/// eager twin). Both must give the same value, or the same single error by code, message and span. Every program
/// runs through <see cref="KatLangEngine.RunAsync"/> with an in-memory downloader that counts its calls; every
/// source is checked for a clean parse first.</para>
/// </summary>
public class DeferredBranchSharedModuleTests
{
    private const string Host = "modules.example";

    private static string Url(string name) => $"https://{Host}/{name}.kat";

    private static string Open(params string[] names)
        => "open " + string.Join(", ", names.Select(name => $"'{Url(name)}'"));

    private static string Load(string name) => $"load('{Url(name)}')";

    /// <summary>A module that is one clause family: the load-bearing branch <c>name(0)</c> and its fallback.</summary>
    private static string Family(string name, params string[] rows)
        => $"public {name}(0) = {{\n" + string.Concat(rows.Select(row => "  " + row + "\n")) + $"}}\npublic {name}(n) = n\n";

    private static readonly Dictionary<string, string> Library = new(StringComparer.Ordinal)
    {
        // The shared modules.
        ["leaf"] = "public Z = 1\n",
        // An open at its root.
        ["shared"] = Open("leaf") + "\npublic Y = Z + 4\n",
        // An open in a nested body only.
        ["nested"] = "public Y = {\n  " + Open("leaf") + "\n  Z + 4\n}\n",
        // An open at its root, and a public member block.
        ["lib"] = Open("leaf") + "\npublic Sub = {\n  public X = Z + 6\n}\npublic Y = Z + 4\n",
        // No open anywhere.
        ["plain"] = "public Sub = {\n  public X = 7\n}\npublic Y = 5\n",
        // The module root becomes a structural forwarding carrier, with its own public namespace.
        ["carrier"] = Open("leaf") + "\npublic Y = Z + 4\nNext(x) = x + 1\nNext\n",
        // A parameterized module: callable, never an open provider.
        ["needs"] = "public V = 3\nq + 1\n",
        // A member that counts its evaluations.
        ["counter"] = "public T = tick()\n",
        // A module the branch loads first, which itself opens the shared one.
        ["fresh"] = Open("shared") + "\npublic Q = Y + 1\n",

        // The families.
        ["opens-shared"] = Family("H", Open("shared"), "Y"),
        ["holds-shared"] = Family("H", "M = " + Load("shared"), "M.Y"),
        ["aliases-shared"] = Family("H", "open M", "M = " + Load("shared"), "Y"),
        ["references-shared"] = Family("H", "open P", "M = " + Load("shared"), "P = M", "Y"),
        ["references-sub"] = Family("H", "open P.Sub", "M = " + Load("lib"), "P = M", "X"),
        ["opens-carrier"] = Family("H", Open("carrier"), "Y"),
        ["references-carrier"] = Family("H", "open P", "M = " + Load("carrier"), "P = M", "Y"),
        ["opens-nested"] = Family("H", Open("nested"), "Y"),
        ["opens-fresh"] = Family("H", Open("fresh"), "Q"),
        ["opens-needs"] = Family("H", Open("needs"), "V"),
        ["reads-counter"] = Family("H", Open("counter"), "T"),
        ["two-opens"] = Family("L", Open("shared"), "Y") + Family("R", Open("shared"), "Y + 1"),
        ["two-holds"] = Family("L", "M = " + Load("shared"), "M.Y") + Family("R", "M = " + Load("shared"), "M.Y + 1"),
        // A branch that opens a module whose own branch opens the shared one.
        ["outer"] = Family("G", Open("opens-shared"), "H(0) + 100"),
        // The eager twin of opens-shared: the holder at the module's root, `open M` in a load-free branch.
        ["eager-twin"] = "M = " + Load("shared") + "\n" + Family("H", "open M", "Y"),

        // Dotted open paths through the shared module.
        ["dotted-name"] = Family("H", "open M.Sub", "M = " + Load("lib"), "X"),
        ["dotted-block"] = Family("H", "open " + Load("lib") + ".Sub", "X"),
        ["dotted-name-plain"] = Family("H", "open M.Sub", "M = " + Load("plain"), "X"),
        ["dotted-block-plain"] = Family("H", "open " + Load("plain") + ".Sub", "X"),
        ["missing-name"] = Family("H", "open M.Nope", "M = " + Load("lib"), "1"),
        ["missing-block"] = Family("H", "open " + Load("lib") + ".Nope", "1"),
        ["missing-name-plain"] = Family("H", "open M.Nope", "M = " + Load("plain"), "1"),
        ["missing-block-plain"] = Family("H", "open " + Load("plain") + ".Nope", "1"),

        // The cyclic cases (DeferredLoadCycleTests): ma's branch opens mb, which opens ma eagerly.
        ["ma"] = Family("H", Open("mb"), "Y") + "public Z = 1\n",
        ["mb"] = Open("ma") + "\npublic Y = Z + 4\n",
        ["ma-load"] = Family("H", "M = " + Load("mb-load"), "M.Y") + "public Z = 1\n",
        ["mb-load"] = "M = " + Load("ma-load") + "\npublic Y = M.Z + 4\n",
    };

    /// <summary>The in-memory host of one run: download counts per module.</summary>
    private sealed class RunHost
    {
        public Dictionary<string, int> Fetches { get; } = new(StringComparer.Ordinal);

        public int this[string module] => Fetches.GetValueOrDefault(Url(module));

        public RunOptions Options => new()
        {
            AllowedHosts = [Host],
            DownloadCode = (url, _) =>
            {
                lock (Fetches)
                    Fetches[url] = Fetches.GetValueOrDefault(url) + 1;
                var name = url[$"https://{Host}/".Length..^".kat".Length];
                return Library.TryGetValue(name, out var source)
                    ? ValueTask.FromResult(source)
                    : throw new InvalidOperationException($"404: {url}");
            },
        };
    }

    /// <summary>What <c>main</c> did with the program before the fix (measured 2026-11-17 on <c>eb67160c</c>).</summary>
    public enum Before
    {
        /// <summary>Threw <see cref="InvalidOperationException"/> from <c>ElaboratedPropertyScope.StandaloneAnalysis</c>.</summary>
        ThrewInvalidOperation,

        /// <summary>Threw <see cref="ArgumentException"/> from <c>CompletedStructureContext.Open</c>.</summary>
        ThrewArgument,

        /// <summary>Dropped an unresolvable open target and ran the branch.</summary>
        AcceptedSilently,

        /// <summary>Gave the result it gives now: a guard that the fix changes nothing here.</summary>
        Same,

        /// <summary>Additional review coverage; no baseline outcome was measured.</summary>
        NotMeasured,
    }

    /// <summary>
    /// One program: its source, the twin that must agree with it (null when the program is its own control), and
    /// the expected outcome: a displayed value, or one error by code and message.
    /// </summary>
    public sealed record Case(string Name, Before Before, string Source, string? Twin, string? Value,
        KatLangErrorCode? Code = null, string? Message = null)
    {
        public override string ToString() => Name;
    }

    private static string Program(string opens, string output) => opens + "\n" + output + "\n";

    private static string RootFamily(string prefix, params string[] rows)
        => prefix + "H(0) = {\n" + string.Concat(rows.Select(row => "  " + row + "\n")) + "}\nH(n) = n\nH(0)\n";

    private const string MissingNameMessage = "'M.Nope' cannot be opened because 'M' has no property named 'Nope'.";
    private const string MissingBlockMessage = "'{...}.Nope' cannot be opened because '{...}' has no property named 'Nope'.";

    private static Case Refused(string name, Before before, string family, string shared, string message)
        => new(name, before, Program(Open(family, shared), "H(0)"), Program(Open(family), "H(0)"), Value: null,
            KatLangErrorCode.UnresolvedOpenTarget, message);

    private static readonly Case[] Cases =
    [
        // ── The reported repro, and the same branch written the other ways ──
        new("Repro: the document and the module's branch both open it", Before.ThrewInvalidOperation,
            Program(Open("opens-shared", "shared"), "H(0)"), Program(Open("opens-shared"), "H(0)"), "5"),
        new("Repro, the document's open first", Before.ThrewInvalidOperation,
            Program(Open("shared", "opens-shared"), "H(0)"), Program(Open("opens-shared"), "H(0)"), "5"),
        new("Repro against its eager twin (holder at the module root, open M in the branch)", Before.ThrewInvalidOperation,
            Program(Open("opens-shared", "shared"), "H(0)"), Program(Open("eager-twin", "shared"), "H(0)"), "5"),
        new("load(...) holder in the branch", Before.ThrewInvalidOperation,
            Program(Open("holds-shared", "shared"), "H(0)"), Program(Open("holds-shared"), "H(0)"), "5"),
        new("Open through an in-branch alias of the load", Before.ThrewInvalidOperation,
            Program(Open("aliases-shared", "shared"), "H(0)"), Program(Open("aliases-shared"), "H(0)"), "5"),
        new("The shared module's open sits in a nested body", Before.ThrewInvalidOperation,
            Program(Open("opens-nested", "nested"), "H(0)"), Program(Open("opens-nested"), "H(0)"), "5"),
        new("Through a module the branch loads first, which opens it", Before.ThrewInvalidOperation,
            Program(Open("opens-fresh", "shared"), "H(0)"), Program(Open("opens-fresh"), "H(0)"), "6"),
        new("A branch of a module whose own branch opens it", Before.ThrewInvalidOperation,
            Program(Open("outer", "shared"), "G(0)"), Program(Open("outer"), "G(0)"), "105"),

        // ── A family the document writes itself ──
        new("Document family opens the module the document opened", Before.ThrewInvalidOperation,
            RootFamily(Open("shared") + "\n", Open("shared"), "Y + 10"),
            RootFamily("", Open("shared"), "Y + 10"), "15"),
        new("Document family holds the module the document holds", Before.ThrewInvalidOperation,
            RootFamily("D = " + Load("shared") + "\n", "M = " + Load("shared"), "M.Y + D.Y"),
            "D = " + Load("shared") + "\nH0 = {\n  M = " + Load("shared") + "\n  M.Y + D.Y\n}\nH0\n", "10"),
        new("Document family opens the document's alias and loads another module", Before.Same,
            RootFamily("D = " + Load("shared") + "\n", "open D", "K = " + Load("leaf"), "Y + K.Z"), null, "6"),
        new("Open through a transparent reference to an in-branch holder", Before.NotMeasured,
            Program(Open("references-shared", "shared"), "H(0)"), Program(Open("references-shared"), "H(0)"), "5"),
        new("Dotted open through a transparent reference to an in-branch holder", Before.NotMeasured,
            Program(Open("references-sub", "lib"), "H(0)"), Program(Open("references-sub"), "H(0)"), "7"),
        new("The shared module root is a forwarding carrier", Before.NotMeasured,
            Program(Open("opens-carrier", "carrier"), "H(0)"), Program(Open("opens-carrier"), "H(0)"), "5"),
        new("Transparent reference to a shared module whose root is a forwarding carrier", Before.NotMeasured,
            Program(Open("references-carrier", "carrier"), "H(0)"), Program(Open("references-carrier"), "H(0)"), "5"),

        // ── One module through two routes: the first materialization completes it, the second receives it ──
        new("Two branches open it", Before.ThrewInvalidOperation,
            Program(Open("two-opens"), "L(0), R(0)"), null, "5\n6"),
        new("Two branches hold it", Before.ThrewInvalidOperation,
            Program(Open("two-holds"), "L(0), R(0)"), null, "5\n6"),
        new("One branch directly, then another through a module that opens it", Before.ThrewInvalidOperation,
            Program(Open("opens-fresh", "two-opens"), "L(0), H(0)"), null, "5\n6"),
        new("Two document branches open it", Before.ThrewInvalidOperation,
            "L(0) = {\n  " + Open("shared") + "\n  Y\n}\nL(n) = n\nR(0) = {\n  " + Open("shared") + "\n  Y + 1\n}\nR(n) = n\nL(0), R(0)\n",
            null, "5\n6"),

        // ── Dotted open paths through the shared module ──
        new("Dotted open, name head", Before.ThrewArgument,
            Program(Open("dotted-name", "lib"), "H(0)"), Program(Open("dotted-name"), "H(0)"), "7"),
        new("Dotted open, name head, module without an open", Before.ThrewArgument,
            Program(Open("dotted-name-plain", "plain"), "H(0)"), Program(Open("dotted-name-plain"), "H(0)"), "7"),
        new("Dotted open, load(...) head", Before.ThrewInvalidOperation,
            Program(Open("dotted-block", "lib"), "H(0)"), Program(Open("dotted-block"), "H(0)"), "7"),
        new("Dotted open, load(...) head, module without an open", Before.Same,
            Program(Open("dotted-block-plain", "plain"), "H(0)"), Program(Open("dotted-block-plain"), "H(0)"), "7"),
        new("Dotted read through an in-branch holder", Before.ThrewInvalidOperation,
            RootFamily("D = " + Load("lib") + "\n", "M = " + Load("lib"), "M.Sub.X + D.Y"), null, "12"),

        // ── An unresolvable path through the shared module is reported, exactly as in the control ──
        Refused("Missing step, name head", Before.ThrewArgument, "missing-name", "lib", MissingNameMessage),
        Refused("Missing step, name head, module without an open", Before.ThrewArgument, "missing-name-plain", "plain", MissingNameMessage),
        Refused("Missing step, load(...) head", Before.ThrewInvalidOperation, "missing-block", "lib", MissingBlockMessage),
        Refused("Missing step, load(...) head, module without an open", Before.AcceptedSilently, "missing-block-plain", "plain", MissingBlockMessage),

        // ── Unchanged rules ──
        new("A parameterized module is refused as a provider", Before.Same,
            Open("opens-needs") + "\nD = " + Load("needs") + "\nH(0), D(1)\n", Program(Open("opens-needs"), "H(0)"), Value: null,
            KatLangErrorCode.IllegalInOpen,
            "'{...}' cannot be opened because open providers must have an empty effective parameter list (found: q)."),
        new("Cyclic: open ma, mb", Before.Same, Program(Open("ma", "mb"), "H(0)"), null, Value: null,
            KatLangErrorCode.LoadCycle, "load cycle detected: " + Url("mb")),
        new("Cyclic: open mb, ma", Before.Same, Program(Open("mb", "ma"), "H(0)"), null, Value: null,
            KatLangErrorCode.LoadCycle, "load cycle detected: " + Url("mb")),
        new("Cyclic: open ma", Before.Same, Program(Open("ma"), "H(0)"), null, Value: null,
            KatLangErrorCode.LoadCycle, "load cycle detected: " + Url("ma")),
        new("Cyclic: document load holders, branch open", Before.NotMeasured,
            "A = " + Load("ma") + "\nB = " + Load("mb") + "\nA.H(0)\n", null, Value: null,
            KatLangErrorCode.LoadCycle, "load cycle detected: " + Url("mb")),
        new("Cyclic: document and modules use load holders", Before.NotMeasured,
            "A = " + Load("ma-load") + "\nB = " + Load("mb-load") + "\nA.H(0)\n", null, Value: null,
            KatLangErrorCode.LoadCycle, "load cycle detected: " + Url("mb-load")),
    ];

    public static TheoryData<Case> AllCases()
    {
        var data = new TheoryData<Case>();
        foreach (var item in Cases)
            data.Add(item);
        return data;
    }

    /// <summary>The whole front end over a program: every module text is clean raw syntax, and the parse is clean.</summary>
    private static async Task<SourceProvenance> ParseClean(string source, RunHost host)
    {
        foreach (var module in Library.Values)
            SourceProvenance.ParseSyntaxValidRoot(module);
        var parsed = await SourceProvenance.ParseValidAsync(source, host.Options);
        Assert.Empty(parsed.Diagnostics);
        return parsed;
    }

    private static (KatLangErrorCode Code, string Message, SourceSpan? Span, bool IsResourceLimit) Facts(KatLangError error)
        => (error.Code, error.Message, error.Span, error.IsResourceLimit);

    /// <summary>The displayed value with one line per output value, whatever the platform's line ending is.</summary>
    private static string Display(RunResult.Success success) => success.ToDisplayString().ReplaceLineEndings("\n");

    /// <summary>One run's outcome in comparable form: the displayed value, or the errors by code, message and span.</summary>
    private static string Outcome(RunResult result)
        => result switch
        {
            RunResult.Success success => "value " + Display(success),
            RunResult.EvalFailure failure => "evaluation error " + string.Join(" | ", failure.Errors.Select(Facts)),
            RunResult.ParseFailure failure => "parse error " + string.Join(" | ", failure.Errors.Select(Facts)),
            _ => result.GetType().Name,
        };

    // ── The result or diagnostic ────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(AllCases))]
    public async Task Program_HasItsDefinedResult_AndAgreesWithItsTwin(Case item)
    {
        var host = new RunHost();
        var parsed = await ParseClean(item.Source, host);
        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(parsed.Root)), "the program holds no deferred region");

        var result = await KatLangEngine.RunAsync(item.Source, new RunHost().Options);
        if (item.Value is { } value)
        {
            Assert.Equal(value, Display(Assert.IsType<RunResult.Success>(result)));
        }
        else
        {
            var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
            Assert.Equal(item.Code, error.Code);
            Assert.False(error.IsResourceLimit);
            Assert.Contains(item.Message!, error.Message, StringComparison.Ordinal);
            Assert.NotNull(error.Span);
        }

        if (item.Twin is not { } twin)
            return;
        await ParseClean(twin, new RunHost());
        var twinResult = await KatLangEngine.RunAsync(twin, new RunHost().Options);
        if (item.Value is not null)
        {
            // A value twin may be written differently (an eager twin): the value is what agrees.
            Assert.Equal(item.Value, Display(Assert.IsType<RunResult.Success>(twinResult)));
        }
        else
        {
            // An error twin keeps every token of the family's module at its position: code, message and span agree.
            Assert.Equal(Outcome(twinResult), Outcome(result));
        }
    }

    [Theory]
    [MemberData(nameof(AllCases))]
    public async Task Program_GivesTheSameOutcome_OnEverySelectionAndEveryRun(Case item)
    {
        // A refused materialization is never cached, a published one is: the outcome is the same either way.
        var options = new RunHost().Options;
        var first = Outcome(await KatLangEngine.RunAsync(item.Source, options));
        Assert.Equal(first, Outcome(await KatLangEngine.RunAsync(item.Source, options)));

        // One parsed tree, evaluated twice: the second run meets a materialized region, or refuses again.
        var parsed = await ParseClean(item.Source, new RunHost());
        var expr = new Expr.AlgorithmExpr(parsed.Root);
        var once = await Evaluator.RunFlatAsync(expr, null, CancellationToken.None);
        var again = await Evaluator.RunFlatAsync(expr, null, CancellationToken.None);
        Assert.Equal(item.Value is not null, once.IsOk);
        Assert.Equal(once.IsOk, again.IsOk);
        if (once.IsOk)
            Assert.Equal(once.Value, again.Value);
    }

    // ── No public entry point throws ────────────────────────────────────────

    /// <summary>
    /// Every public entry point that can reach these programs returns a structured outcome. The synchronous
    /// entries cannot reach a load at all: with a downloader they refuse the OPTIONS before reading the source
    /// (the documented async-only contract, <see cref="KatLangEngine.Run(string, RunOptions?)"/>), and without
    /// one a <c>load</c> is the established parse error. Both are pinned so that neither is mistaken for, nor
    /// hides, an exception about the program.
    /// </summary>
    [Theory]
    [MemberData(nameof(AllCases))]
    public async Task NoPublicEntryPoint_ThrowsForTheProgram(Case item)
    {
        var source = item.Source;

        // The asynchronous front end and engine.
        var parsed = await Parser.ParseAsync(source, new RunHost().Options);
        Assert.False(parsed.HasErrors);
        var run = await KatLangEngine.RunAsync(source, new RunHost().Options);
        Assert.Equal(item.Value is not null, run is RunResult.Success);

        // The asynchronous evaluator over the parsed tree: a structured result, error or value.
        var expr = new Expr.AlgorithmExpr(parsed.Root);
        var evaluated = await Evaluator.RunAsync(expr);
        Assert.Equal(item.Value is not null, evaluated.IsOk);
        var flat = await Evaluator.RunFlatAsync(expr);
        Assert.Equal(item.Value is not null, flat.IsOk);
        if (!flat.IsOk)
        {
            var error = flat.Error;
            while (error is EvalError.WithContext context)
                error = context.Inner;
            Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(error);
        }

        // The atoms projection throws exactly its documented exception for a program that did not succeed.
        if (item.Value is not null)
        {
            var atoms = await KatLangEngine.EvaluateToAtomsAsync(source, new RunHost().Options);
            Assert.Equal(((RunResult.Success)run).Atoms, atoms);
        }
        else
        {
            var failure = await Assert.ThrowsAsync<KatLangException>(() => KatLangEngine.EvaluateToAtomsAsync(source, new RunHost().Options));
            Assert.Equal(item.Code, Assert.Single(failure.Errors).Code);
        }

        // The synchronous entries without a downloader: the load is unavailable, a parse error, never an exception.
        var unavailable = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.All(unavailable.Errors, error => Assert.Equal(KatLangErrorCode.LoadElaborationUnavailable, error.Code));
        Assert.True(Parser.Parse(source).HasErrors);

        // With a downloader they refuse the options, whatever the source says: the same exception for "1".
        var refused = Assert.Throws<InvalidOperationException>(() => KatLangEngine.Run(source, new RunHost().Options));
        Assert.Contains("RunOptions.DownloadCode is configured", refused.Message, StringComparison.Ordinal);
        Assert.Equal(refused.Message, Assert.Throws<InvalidOperationException>(() => KatLangEngine.Run("1", new RunHost().Options)).Message);
        Assert.Equal(refused.Message, Assert.Throws<InvalidOperationException>(() => Parser.Parse(source, new RunHost().Options)).Message);
    }

    // ── One declaration, elaborated once ────────────────────────────────────

    [Fact]
    public async Task ReviewAliasShapes_KeepTheReferenceAndCarrierDistinction()
    {
        var parsed = await ParseClean("open P\nM = " + Load("carrier") + "\nP = M\nY\n", new RunHost());
        var module = Assert.IsType<Algorithm.Alias>(Assert.Single(parsed.Root.Properties, property => property.Name == "M").Value);
        Assert.True(module.IsModuleRoot);
        Assert.False(module.IsReference);
        var reference = Assert.IsType<Algorithm.Alias>(Assert.Single(parsed.Root.Properties, property => property.Name == "P").Value);
        Assert.True(reference.IsReference);
    }

    [Fact]
    public async Task SharedModule_IsDownloadedOnce_AndItsMemberIsOneStoredValue()
    {
        // The document reads the member, the branch reads it through its own open, the document reads it again:
        // one module declaration, one member binding, so one evaluation of tick().
        var source = Program(Open("reads-counter", "counter"), "T, H(0), T");
        var host = new RunHost();
        await ParseClean(source, host);
        var result = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, host.Options));
        Assert.Equal([(Decimal128)1, (Decimal128)1, (Decimal128)1], result.Atoms);
        // ParseClean and the run are two parses of the document: each downloads each module once.
        Assert.Equal(2, host["counter"]);
        Assert.Equal(2, host["reads-counter"]);

        // The branch first: the same single evaluation.
        var branchFirst = Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync(Program(Open("reads-counter", "counter"), "H(0), T, H(0)"), new RunHost().Options));
        Assert.Equal([(Decimal128)1, (Decimal128)1, (Decimal128)1], branchFirst.Atoms);
    }

    [Fact]
    public async Task ReproSelectedRepeatedly_MaterializesOnce()
    {
        var source = Open("opens-shared", "shared") + "\nStep(x) = H(0) + x\nStep(0).repeat(3)\n";
        var host = new RunHost();
        var result = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, host.Options));
        Assert.Equal("15", result.ToDisplayString());
        Assert.Equal(1, host["opens-shared"]);
        Assert.Equal(1, host["shared"]);
        Assert.Equal(1, host["leaf"]);

        var parsed = await ParseClean(source, new RunHost());
        var region = Regions(parsed.Root).Single();
        Assert.Equal(0, region.MaterializationAttempts);
        var flat = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root), null, CancellationToken.None);
        Assert.Equal([(Decimal128)15], flat.Value);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.True(region.IsMaterialized);
    }

    private static List<DeferredModuleRegion> Regions(Algorithm root)
    {
        var regions = new List<DeferredModuleRegion>();
        var visited = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        pending.Push(root);
        while (pending.TryPop(out var node))
        {
            if (!visited.Add(node))
                continue;
            if (node is Algorithm { DeferredRegion: { } region } && !regions.Contains(region))
                regions.Add(region);
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                pending.Push(child);
        }

        return regions;
    }

    // ── The provenance itself ───────────────────────────────────────────────

    [Fact]
    public void Registry_KnowsTheResolvedUnitsOfPublishedOperations_AndNoOther()
    {
        var registry = new ModuleUnitRegistry();
        var import = SourceProvenance.ParseSyntaxValidRoot("public X = 1\n") with { IsModuleElaborated = true };
        var detected = import with { };
        var resolved = import with { };
        var classified = import with { };

        // An operation that reports an error publishes nothing: none of its units is completed.
        var failed = registry.BeginOperation();
        failed.Add(ModuleUnitPass.Detection, import, detected);
        failed.Add(ModuleUnitPass.Resolution, detected, resolved);
        failed.Add(ModuleUnitPass.Exposure, resolved, classified);
        Assert.False(registry.HasCompleted(resolved));

        // One that stopped before exposure and published (never the pipeline's case) completed nothing either.
        var partial = registry.BeginOperation();
        partial.Add(ModuleUnitPass.Detection, import, detected);
        partial.Add(ModuleUnitPass.Resolution, detected, resolved);
        partial.Publish();
        Assert.False(registry.HasCompleted(resolved));

        // The published unit of a whole pipeline: its RESOLVED view is the completed one, and only that view.
        var complete = registry.BeginOperation();
        complete.Add(ModuleUnitPass.Exposure, resolved, classified);
        complete.Publish();
        Assert.True(registry.HasCompleted(resolved));
        Assert.False(registry.HasCompleted(import));
        Assert.False(registry.HasCompleted(detected));
        Assert.False(registry.HasCompleted(classified));
        Assert.False(registry.HasCompleted(resolved with { }));
    }

    [Fact]
    public void SupersededModuleView_IsAnsweredByItsContext_AndEveryOtherViewStaysSupplied()
    {
        var prelude = BuiltinRegistry.SharedSemanticPreludeAlgorithm;
        var preludeKey = new StaticScopeKey(null, OpenProviderIdentity.RootLevelDeclaration);
        static CompletedStaticStructures.Selection Self(StaticScopeKey key, Algorithm body)
            => new(StaticFactKind.Structure, key, OpenProviderIdentity.DeclaredAtRoot(body));
        static CompletedStaticStructures.BodyFacts FactsOf(Algorithm body, StaticScopeKey key)
            => new(body, Self(key, body), Self(key, body), new Dictionary<string, StaticScopeKey>(), new HashSet<string>(), []);

        // The publishing operation: a loaded module's root and an ordinary block, each published as resolved.
        var resolvedModule = SourceProvenance.ParseSyntaxValidRoot("public X = 1\n") with { IsModuleElaborated = true };
        var resolvedBlock = SourceProvenance.ParseSyntaxValidRoot("public X = 2\n");
        Assert.True(resolvedModule.IsModuleRoot);
        var moduleKey = new StaticScopeKey(preludeKey, OpenProviderIdentity.DeclarationOf(resolvedModule));
        var blockKey = new StaticScopeKey(preludeKey, OpenProviderIdentity.DeclarationOf(resolvedBlock));
        var facts = new CompletedStaticStructures(preludeKey);
        facts.Add(preludeKey, new(prelude, CompletedStaticStructures.Selection.Unavailable, CompletedStaticStructures.Selection.Unavailable,
            new Dictionary<string, StaticScopeKey>(), new HashSet<string>(), []));
        facts.Add(moduleKey, FactsOf(resolvedModule, moduleKey));
        facts.Add(blockKey, FactsOf(resolvedBlock, blockKey));
        var publication = new CompletedStructurePublication(facts);
        CompletedStaticStructures.Attach(resolvedModule, publication);
        CompletedStaticStructures.Attach(resolvedBlock, publication);

        // Exposure replaces both views with the ones it classified (copies carry the publication, as `with` does).
        var classifiedModule = resolvedModule with { };
        var classifiedBlock = resolvedBlock with { };
        var storage = facts.RetainedStorageUnits;
        facts.Retarget(moduleKey, classifiedModule);
        facts.Retarget(blockKey, classifiedBlock);
        // The mark is on the view: the table retains, and counts, nothing for it.
        Assert.Equal(storage, facts.RetainedStorageUnits);
        Assert.Same(classifiedModule, facts.Facts(moduleKey)!.Body);
        facts.Seal();

        // Only the module root's replaced view is marked, with its context and itself.
        Assert.Same(moduleKey, resolvedModule.CompletedStructure!.SupersededAt);
        Assert.Same(resolvedModule, resolvedModule.CompletedStructure.SupersededView);
        Assert.Same(facts, resolvedModule.CompletedStructure.Facts);
        Assert.Null(classifiedModule.CompletedStructure!.SupersededAt);
        Assert.Null(resolvedBlock.CompletedStructure!.SupersededAt);
        Assert.Same(publication, resolvedBlock.CompletedStructure);

        var context = facts.Context(preludeKey);
        var level = ElaboratedScopeLookup.CreateScope(prelude, completedContext: context);

        // The view the facts name, and the view they named one pass earlier, are one definition: the same answers.
        foreach (var view in new Algorithm[] { classifiedModule, resolvedModule })
        {
            var opened = context.Open(view, level);
            Assert.NotNull(opened);
            Assert.Same(classifiedModule, opened.Value.Target);
            var receiver = context.Receiver(view, level);
            Assert.NotNull(receiver);
            Assert.Same(classifiedModule, receiver.Value.Structure);
            Assert.False(context.OpenIsUnavailable(view, level));
        }

        // No level is built over the superseded view: its nested bodies are not named by these facts.
        Assert.NotNull(CompletedStructureContext.For(classifiedModule, level));
        Assert.Null(CompletedStructureContext.For(resolvedModule, level));

        // A copy of either view is a supplied view, the copy of the superseded one included (it carries the mark of
        // the view it was copied from); so is the replaced view of a body that is no module root.
        foreach (var supplied in new Algorithm[] { classifiedModule with { }, resolvedModule with { }, resolvedBlock })
        {
            Assert.Throws<ArgumentException>(() => context.Open(supplied, level));
            Assert.Throws<ArgumentException>(() => context.Receiver(supplied, level));
            Assert.True(context.OpenIsUnavailable(supplied, level));
            Assert.Null(CompletedStructureContext.For(supplied, level));
        }
    }
}
