using System.Numerics;
using System.Reflection;
using System.Runtime.CompilerServices;

namespace KatLang.Formatting.PublicApi.Tests;

/// <summary>
/// M6 public elaboration boundary (v0.8.187, intentional breaking change): the
/// individual front-end elaboration passes are implementation stages of the one
/// authoritative pipeline and are no longer public. Before this change a host
/// could compose <c>ParameterDetector.Detect</c> →
/// <c>ImplicitArgumentResolver.Resolve</c> publicly and evaluate the result —
/// an AST whose <c>Property.Exposure</c> metadata was never finalized by the
/// (always-internal) <c>PropertyExposureResolver</c>, so it observably diverged
/// from engine-parsed source. The v0.8.188 follow-up applied the same rule to
/// <c>ModuleLoader</c>: load elaboration alone is an even more incomplete stage
/// (no parameter detection at all). This suite runs WITHOUT friend access and
/// pins: the passes are not publicly discoverable, no public signature leaks
/// them, the missing stages were not exposed to "complete" the partial API, and
/// the supported public layers (<c>Parser.Parse</c>/<c>ParseAsync</c>,
/// <c>KatLangEngine</c>) remain available and perform complete elaboration.
/// </summary>
public class PublicElaborationSurfaceTests
{
    private static readonly Assembly KatLangAssembly = typeof(KatLangEngine).Assembly;

    private static readonly string[] ForbiddenElaborationTypeNames =
    [
        "KatLang.ParameterDetector",
        "KatLang.ImplicitArgumentResolver",
        "KatLang.ModuleLoader",
        "KatLang.PropertyExposureResolver",
        "KatLang.FrontEndPipeline",
        "KatLang.FrontEndResult",
        "KatLang.SyntaxParseResult",
        "KatLang.PropertyDependencyGraphBuilder",
        "KatLang.PropertyDependencyGraph",
        "KatLang.PropertyDependencySummaryGraph",
    ];

    /// <summary>
    /// The property `Prop` captures the ancestor-owned parameter `x`, so the
    /// complete pipeline must classify it local-only and structural dot access
    /// must refuse it with the dedicated structured error.
    /// </summary>
    private const string LocalOnlyWitnessProgram = """
        Algo(x) = {
            Prop = x + 1
            x
        }
        Algo.Prop
        """;

    /// <summary>
    /// These assertions are only meaningful from a non-friend consumer: friend
    /// assemblies see internal types regardless of the public surface.
    /// </summary>
    [Fact]
    public void ThisProject_IsNotAFriendOfTheKatLangAssembly()
        => Assert.DoesNotContain(
            KatLangAssembly.GetCustomAttributes(typeof(InternalsVisibleToAttribute), false)
                .Cast<InternalsVisibleToAttribute>(),
            attribute => attribute.AssemblyName.StartsWith(
                typeof(PublicElaborationSurfaceTests).Assembly.GetName().Name!,
                StringComparison.Ordinal));

    [Fact]
    public void IndividualElaborationPasses_AreNotPubliclyDiscoverable()
    {
        // GetExportedTypes covers public nested types; GetForwardedTypes closes
        // the separate metadata route by which this assembly could publicly
        // redirect one of these full names to another assembly.
        var visibleTypeNames = KatLangAssembly.GetExportedTypes()
            .Concat(KatLangAssembly.GetForwardedTypes())
            .Select(type => type.FullName)
            .ToHashSet(StringComparer.Ordinal);

        Assert.DoesNotContain(ForbiddenElaborationTypeNames, visibleTypeNames.Contains);

        // Honesty guard for the name checks above: the stages still exist as
        // non-visible types under these exact full names. No missing entry is
        // silently discarded, and IsVisible covers top-level and nested forms.
        foreach (var name in ForbiddenElaborationTypeNames)
        {
            var type = KatLangAssembly.GetType(name, throwOnError: false, ignoreCase: false);
            Assert.NotNull(type);
            Assert.Same(KatLangAssembly, type.Assembly);
            Assert.Equal(name, type.FullName);
            Assert.False(type.IsVisible, $"{name} is publicly visible.");
        }
    }

    /// <summary>
    /// No public method, constructor, property, field, or event may mention an
    /// internal elaboration-stage type anywhere in its signature — that would
    /// re-open the partial-composition route through a facade.
    /// </summary>
    [Fact]
    public void NoPublicSignature_MentionsAnInternalElaborationStage()
    {
        var forbidden = ForbiddenElaborationTypeNames
            .Select(name => KatLangAssembly.GetType(name, throwOnError: true, ignoreCase: false)!)
            .ToHashSet();

        static IEnumerable<Type> Unwrap(Type type)
        {
            var pending = new Stack<Type>();
            var visited = new HashSet<Type>();
            pending.Push(type);

            while (pending.TryPop(out var current))
            {
                if (!visited.Add(current))
                    continue;

                if (current.HasElementType)
                {
                    pending.Push(current.GetElementType()!);
                    continue;
                }

                if (current.IsFunctionPointer)
                {
                    pending.Push(current.GetFunctionPointerReturnType());
                    foreach (var parameterType in current.GetFunctionPointerParameterTypes())
                        pending.Push(parameterType);
                    foreach (var callingConvention in current.GetFunctionPointerCallingConventions())
                        pending.Push(callingConvention);
                    continue;
                }

                if (current.IsGenericParameter)
                {
                    foreach (var constraint in current.GetGenericParameterConstraints())
                        pending.Push(constraint);
                    continue;
                }

                yield return current.IsGenericType ? current.GetGenericTypeDefinition() : current;
                if (current.IsGenericType)
                {
                    foreach (var argument in current.GetGenericArguments())
                        pending.Push(argument);
                }
            }
        }

        const BindingFlags PublicSurface =
            BindingFlags.Public | BindingFlags.Instance | BindingFlags.Static | BindingFlags.FlattenHierarchy;

        var leaks = new List<string>();
        foreach (var type in KatLangAssembly.GetExportedTypes().Concat(KatLangAssembly.GetForwardedTypes()).Distinct())
        {
            void Check(Type mentioned, string member)
            {
                if (Unwrap(mentioned).Any(forbidden.Contains))
                    leaks.Add($"{type.FullName}.{member}");
            }

            void CheckParameter(ParameterInfo parameter, string member)
            {
                Check(parameter.ParameterType, member);
                foreach (var modifier in parameter.GetRequiredCustomModifiers())
                    Check(modifier, member);
                foreach (var modifier in parameter.GetOptionalCustomModifiers())
                    Check(modifier, member);
            }

            static IEnumerable<Type> GenericConstraints(IEnumerable<Type> genericArguments)
                => genericArguments
                    .Where(static argument => argument.IsGenericParameter)
                    .SelectMany(static argument => argument.GetGenericParameterConstraints());

            if (type.BaseType is { } baseType)
                Check(baseType, "base type");
            foreach (var implementedInterface in type.GetInterfaces())
                Check(implementedInterface, "interface");
            foreach (var constraint in GenericConstraints(type.GetGenericArguments()))
                Check(constraint, "generic constraint");

            foreach (var method in type.GetMethods(PublicSurface))
            {
                Check(method.ReturnType, method.Name);
                CheckParameter(method.ReturnParameter, method.Name + " return");
                foreach (var parameter in method.GetParameters())
                    CheckParameter(parameter, method.Name);
                foreach (var constraint in GenericConstraints(method.GetGenericArguments()))
                    Check(constraint, method.Name + " generic constraint");
            }

            foreach (var constructor in type.GetConstructors(PublicSurface))
            foreach (var parameter in constructor.GetParameters())
                CheckParameter(parameter, ".ctor");

            foreach (var property in type.GetProperties(PublicSurface))
            {
                Check(property.PropertyType, property.Name);
                foreach (var modifier in property.GetRequiredCustomModifiers())
                    Check(modifier, property.Name);
                foreach (var modifier in property.GetOptionalCustomModifiers())
                    Check(modifier, property.Name);
                foreach (var parameter in property.GetIndexParameters())
                    CheckParameter(parameter, property.Name);
            }

            foreach (var field in type.GetFields(PublicSurface))
            {
                Check(field.FieldType, field.Name);
                foreach (var modifier in field.GetRequiredCustomModifiers())
                    Check(modifier, field.Name);
                foreach (var modifier in field.GetOptionalCustomModifiers())
                    Check(modifier, field.Name);
            }

            foreach (var eventInfo in type.GetEvents(PublicSurface))
            {
                if (eventInfo.EventHandlerType is { } handlerType)
                    Check(handlerType, eventInfo.Name);
            }
        }

        Assert.True(leaks.Count == 0, "Public signatures leak internal elaboration stages: " + string.Join(", ", leaks));
    }

    /// <summary>
    /// The deliberately lower-level evaluator accepts host ASTs but does not
    /// parse or elaborate them. A Resolve node naming an explicitly declared
    /// parameter therefore remains a lexical lookup and fails; only the complete
    /// source front end is entitled to rewrite it to Expr.Param.
    /// </summary>
    [Fact]
    public async Task EvaluatorEntryPoints_RemainPublicRawAstEvaluation()
    {
        var rawFunction = new Algorithm.User(
            Parent: null,
            Parameters: [new ParameterDeclaration("x")],
            Opens: [],
            Properties: [],
            Output: [new Expr.Resolve("x")]);
        var rawCall = new Expr.Call(new Expr.AlgorithmExpr(rawFunction), [new Expr.Num(7)]);

        var sync = Evaluator.Run(rawCall);
        var asyncResult = await Evaluator.RunAsync(rawCall);

        Assert.True(sync.IsError);
        Assert.Equal(KatLangErrorCode.UnknownName, KatLangError.FromEvalError(sync.Error).Code);
        Assert.True(asyncResult.IsError);
        Assert.Equal(KatLangErrorCode.UnknownName, KatLangError.FromEvalError(asyncResult.Error).Code);
    }

    /// <summary>
    /// The supported parse layer: compile-time bindings prove the entry-point
    /// shapes, and the returned AST publicly shows that elaboration ran to
    /// completion — the exposure metadata only <c>PropertyExposureResolver</c>
    /// computes is finalized on it.
    /// </summary>
    [Fact]
    public void SupportedParserEntryPoints_RemainPublic_AndElaborateCompletely()
    {
        Func<string, ParseResult> parse = Parser.Parse;
        Func<string, RunOptions?, ParseResult> parseWithOptions = Parser.Parse;
        Func<string, RunOptions?, Task<ParseResult>> parseAsync = Parser.ParseAsync;
        Assert.NotNull(parse);
        Assert.NotNull(parseWithOptions);
        Assert.NotNull(parseAsync);

        var parsed = parse(LocalOnlyWitnessProgram);
        Assert.False(parsed.HasErrors);

        var algo = Assert.Single(parsed.Root.Properties, property => property.Name == "Algo");
        var prop = Assert.Single(algo.Value.Properties, property => property.Name == "Prop");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, prop.Exposure);
    }

    /// <summary>
    /// The supported execution layer: compile-time bindings prove the engine
    /// entry-point shapes, and the run classifies the M6 witness with the
    /// authoritative structured error — evaluation saw finalized exposure.
    /// </summary>
    [Fact]
    public void SupportedEngineEntryPoints_RemainPublic_AndSeeFinalizedExposure()
    {
        Func<string, RunOptions?, RunResult> run = KatLangEngine.Run;
        Func<string, RunOptions?, Task<RunResult>> runAsync = KatLangEngine.RunAsync;
        Func<string, RunOptions?, IReadOnlyList<Decimal128>> evaluateToAtoms = KatLangEngine.EvaluateToAtoms;
        Func<string, RunOptions?, Task<IReadOnlyList<Decimal128>>> evaluateToAtomsAsync = KatLangEngine.EvaluateToAtomsAsync;
        Func<string, RunOptions?, string> evaluateToString = KatLangEngine.EvaluateToString;
        Func<string, RunOptions?, Task<string>> evaluateToStringAsync = KatLangEngine.EvaluateToStringAsync;
        Assert.NotNull(run);
        Assert.NotNull(runAsync);
        Assert.NotNull(evaluateToAtoms);
        Assert.NotNull(evaluateToAtomsAsync);
        Assert.NotNull(evaluateToString);
        Assert.NotNull(evaluateToStringAsync);

        var failure = Assert.IsType<RunResult.EvalFailure>(run(LocalOnlyWitnessProgram, null));
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty, Assert.Single(failure.Errors).Code);
    }

    /// <summary>
    /// M1 completion (v0.8.189): every compiled <c>ModuleLoader</c> constructor
    /// requires the one host-supplied downloader contract. This metadata-level
    /// pin prevents a downloader-less/optional constructor path from returning;
    /// friend tests separately prove that explicit null is rejected at runtime
    /// and that the supplied delegate is the one invoked. This deliberately does
    /// not ban unrelated <c>System.Net.*</c> metadata from the whole assembly —
    /// assembly references are neither necessary nor sufficient evidence that
    /// module transport exists.
    /// </summary>
    [Fact]
    public void ModuleLoader_ConstructorsHaveNoDownloaderlessPath()
    {
        var loaderType = KatLangAssembly.GetType(
            "KatLang.ModuleLoader", throwOnError: true, ignoreCase: false)!;
        var downloaderType = typeof(Func<string, CancellationToken, ValueTask<string>>);
        var constructors = loaderType.GetConstructors(
            BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);

        Assert.NotEmpty(constructors);
        Assert.All(constructors, constructor =>
        {
            var downloader = Assert.Single(
                constructor.GetParameters(),
                parameter => parameter.ParameterType == downloaderType);
            Assert.Equal("downloadCode", downloader.Name);
            Assert.False(downloader.IsOptional);
            Assert.False(downloader.HasDefaultValue);
        });
    }
}
