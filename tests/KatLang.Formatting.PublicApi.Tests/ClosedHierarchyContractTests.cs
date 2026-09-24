using System.Reflection;
using System.Text;

namespace KatLang.Formatting.PublicApi.Tests;

/// <summary>
/// Pins the C# <c>closed</c> contract of KatLang's finite variant hierarchies
/// against the COMPILED public assembly, exactly as a NuGet consumer meets it:
/// small consumer programs are compiled with the pinned SDK's own C# compiler
/// (<c>global.json</c> — the one SDK authority) against the built
/// <c>KatLang.dll</c>, and the compiler's verdict is the assertion.
///
/// <para>Why a compile probe and not reflection alone: a <c>private</c> or
/// <c>private protected</c> ordinary constructor never closed these record
/// hierarchies, because a record's synthesized COPY constructor is
/// <c>protected</c> — <c>sealed record Rogue(RunResult o) : RunResult(o)</c>
/// compiled from another assembly against the pre-<c>closed</c> package and could
/// reach a production "unknown variant" fallback — and <see cref="ErrorContext"/>,
/// which declares no constructor at all, was derivable through its synthesized
/// protected ordinary constructor as well. Only the compiler enforces the
/// closure (CS9382 for a foreign derivation), so only the compiler can witness it.
/// Reflection pins the CHEAP half: which types carry the closed metadata.</para>
///
/// <para>The suite distinguishes "closed externally" from "broken hierarchy": the
/// same compiler must ACCEPT a consumer that constructs a built-in variant of every
/// root and switches exhaustively — with no catch-all arm and <c>CS8509</c>/
/// <c>CS8655</c> as errors — over every root whose variants are all public. Two
/// deliberate negative controls keep the exhaustiveness verdict from being
/// vacuous: a switch that omits one variant must fail, and a switch over
/// <see cref="EvalError"/>, which keeps one INTERNAL variant, must fail for a
/// consumer no matter how many public variants it names (hosts classify through
/// <see cref="EvalError.Code"/>, never by enumerating variants).</para>
/// </summary>
public class ClosedHierarchyContractTests
{
    private static readonly Assembly KatLangAssembly = typeof(KatLangEngine).Assembly;

    /// <summary>
    /// One row per closed root the package ships: the root and a legitimate
    /// consumer construction of one of its built-in variants (the exhaustive
    /// switch and the rogue derivation are generated from the compiled assembly,
    /// so the table never needs to enumerate variants). Ratcheted both ways by
    /// <see cref="ClosedRoots_AreExactlyTheTabledFiniteHierarchies"/>.
    /// </summary>
    private sealed record ClosedHierarchy(Type Root, string LegitimateConstruction);

    private static readonly IReadOnlyList<ClosedHierarchy> ClosedHierarchies =
    [
        new(typeof(Expr), "new KatLang.Expr.Param(\"x\")"),
        new(typeof(RunResult), "KatLang.KatLangEngine.Run(\"1 +\")"),
        new(typeof(EvalError), "new KatLang.EvalError.DivByZero()"),
        new(typeof(Result), "new KatLang.Result.Str(\"s\")"),
        new(typeof(Algorithm), "new KatLang.Algorithm.Conditional(null, [], [])"),
        new(typeof(Pattern), "new KatLang.Pattern.Bind(\"x\")"),
        new(typeof(ParameterPattern), "new KatLang.CaptureParameterPattern(\"x\")"),
        // The one root whose variants are structured evaluation-context FRAMES rather
        // than values: hosts still construct every built-in context, and attach
        // free-form text through TextErrorContext / EvalError.WithContext(string, inner).
        new(typeof(ErrorContext), "new KatLang.TextErrorContext(\"text\")"),
    ];

    public static TheoryData<Type> ClosedRoots
    {
        get
        {
            var data = new TheoryData<Type>();
            foreach (var hierarchy in ClosedHierarchies)
                data.Add(hierarchy.Root);
            return data;
        }
    }

    /// <summary>The closed roots every consumer can switch over exhaustively: those whose variants are all public.</summary>
    public static TheoryData<Type> ConsumerExhaustiveRoots
    {
        get
        {
            var data = new TheoryData<Type>();
            foreach (var hierarchy in ClosedHierarchies)
            {
                if (HasOnlyPublicVariants(hierarchy.Root))
                    data.Add(hierarchy.Root);
            }

            return data;
        }
    }

    // ── Metadata: which types are closed ────────────────────────────────────

    [Fact]
    public void ClosedRoots_AreExactlyTheTabledFiniteHierarchies()
    {
        var closedInAssembly = KatLangAssembly.GetExportedTypes()
            .Where(IsClosedType)
            .Select(type => type.FullName!)
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToList();
        var tabled = ClosedHierarchies
            .Select(hierarchy => hierarchy.Root.FullName!)
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToList();

        // A newly closed public type joins the table (so it gets the compile probes); a
        // root that silently lost `closed` is caught here before the slower probes run.
        Assert.Equal(tabled, closedInAssembly);
    }

    [Theory]
    [MemberData(nameof(ClosedRoots))]
    public void ClosedRoot_IsImplicitlyAbstract_WithOnlyDeclaredVariants(Type root)
    {
        Assert.True(root.IsAbstract, $"{root.Name} must be implicitly abstract: only its declared variants are instantiable.");
        Assert.False(root.IsSealed, $"{root.Name} is a hierarchy root, not a sealed leaf.");
        Assert.NotEmpty(DirectVariants(root));
        Assert.All(DirectVariants(root), variant => Assert.True(
            variant.IsSealed,
            $"{variant.FullName} must be sealed: every closed root's variants are the leaves of the hierarchy."));
    }

    // ── Compiler: external derivation is rejected ───────────────────────────

    [Fact]
    public void EveryClosedRoot_RejectsExternalDerivation_ThroughEveryDerivableConstructor()
    {
        // One probe per derivation route the root's constructors leave open to a
        // derived record: always the synthesized protected copy constructor, plus
        // the ordinary route for a root that declares no constructor of its own
        // (ErrorContext), whose default constructor is protected too.
        var probes = ClosedHierarchies
            .SelectMany(hierarchy => RogueDerivations(hierarchy.Root).Select(probe => (hierarchy.Root, probe.Name, probe.Source)))
            .ToList();
        Assert.Contains(probes, probe => probe.Root == typeof(ErrorContext) && probe.Name == RogueOrdinaryName(typeof(ErrorContext)));

        var source = new StringBuilder("namespace Rogue;\n");
        foreach (var probe in probes)
            source.Append(probe.Source).Append('\n');

        var compilation = Compile(source.ToString(), "rogue");

        Assert.NotEqual(0, compilation.ExitCode);
        foreach (var probe in probes)
        {
            Assert.True(
                compilation.Diagnostics.Any(d => d.Code == "CS9382" && d.Message.Contains($"'{probe.Name}'", StringComparison.Ordinal)),
                $"Deriving {probe.Name} from the closed {probe.Root.Name} must be refused with CS9382."
                + Environment.NewLine + compilation.Output);
        }

        // CS9382 is the ONLY reason the file fails: any other error would mean the
        // derivation was stopped by something other than the closed contract (an
        // inaccessible constructor, a missing abstract override), which is not the
        // guarantee under test.
        Assert.All(compilation.Diagnostics, d => Assert.Equal("CS9382", d.Code));
        Assert.Equal(probes.Count, compilation.Diagnostics.Count);
    }

    // ── Compiler: the hierarchies stay usable and consumer-exhaustive ───────

    [Fact]
    public void EveryClosedRoot_StaysConstructible_AndConsumerSwitchesAreExhaustiveWithoutCatchAll()
    {
        var source = new StringBuilder("namespace Consumer;\npublic static class Usage\n{\n");
        foreach (var hierarchy in ClosedHierarchies)
        {
            source.Append($"    public static {FullName(hierarchy.Root)} Make{hierarchy.Root.Name}() => {hierarchy.LegitimateConstruction};\n");
            if (HasOnlyPublicVariants(hierarchy.Root))
                source.Append(ExhaustiveSwitch(hierarchy.Root, omit: null));
        }

        source.Append("}\n");

        var compilation = Compile(source.ToString(), "consumer");

        Assert.True(
            compilation.ExitCode == 0 && compilation.Diagnostics.Count == 0,
            "A consumer constructing a built-in variant of every closed root, and switching over every all-public root "
            + "with no catch-all arm under CS8509/CS8655-as-errors, must compile cleanly." + Environment.NewLine + compilation.Output);
    }

    [Theory]
    [MemberData(nameof(ConsumerExhaustiveRoots))]
    public void ExhaustivenessVerdict_IsLive_AnOmittedVariantFailsToCompile(Type root)
    {
        // Negative control for the positive probe above, per consumer-exhaustive
        // root: the same compiler settings must reject a switch that skips one
        // public variant, naming that variant.
        var omitted = DirectVariants(root).First();
        var source = "namespace Consumer;\npublic static class Usage\n{\n"
            + ExhaustiveSwitch(root, omit: omitted)
            + "}\n";

        var compilation = Compile(source, "omitted-" + root.Name);

        Assert.NotEqual(0, compilation.ExitCode);
        var error = Assert.Single(compilation.Diagnostics);
        Assert.Equal("CS8509", error.Code);
        Assert.Contains(FullName(omitted), error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void HierarchyWithAnInternalVariant_IsNeverExhaustiveForAConsumer()
    {
        // EvalError keeps one internal variant, so no consumer switch is exhaustive
        // however many public variants it names — the documented reason hosts
        // classify through EvalError.Code. This pins that documentation: should the
        // last internal variant ever become public, the claim (and this test) change.
        Assert.False(HasOnlyPublicVariants(typeof(EvalError)));
        Assert.All(ClosedHierarchies.Where(h => h.Root != typeof(EvalError)), h => Assert.True(
            HasOnlyPublicVariants(h.Root),
            $"{h.Root.Name} is documented as consumer-exhaustive; a non-public variant would silently break that."));

        var source = "namespace Consumer;\npublic static class Usage\n{\n"
            + ExhaustiveSwitch(typeof(EvalError), omit: null)
            + "}\n";

        var compilation = Compile(source, "internal-variant");

        Assert.NotEqual(0, compilation.ExitCode);
        var error = Assert.Single(compilation.Diagnostics);
        Assert.Equal("CS8509", error.Code);
    }

    // ── Generated consumer source ───────────────────────────────────────────

    private static bool IsClosedType(Type type)
        => type.GetCustomAttributesData().Any(attribute =>
            attribute.AttributeType.FullName == "System.Runtime.CompilerServices.IsClosedTypeAttribute");

    /// <summary>Direct derived types declared anywhere in the assembly, public or not.</summary>
    private static IReadOnlyList<Type> DirectVariants(Type root)
        => KatLangAssembly.GetTypes()
            .Where(type => type.BaseType == root)
            .OrderBy(type => type.FullName, StringComparer.Ordinal)
            .ToList();

    private static bool HasOnlyPublicVariants(Type root)
        => DirectVariants(root).All(variant => variant.IsPublic || variant.IsNestedPublic);

    private static string FullName(Type type) => PublicApiSurfaceRenderer.Format(type);

    private static string RogueName(Type root) => "Rogue" + root.Name;

    private static string RogueOrdinaryName(Type root) => "RogueOrdinary" + root.Name;

    /// <summary>
    /// Records deriving from <paramref name="root"/> through every constructor a
    /// derived record could reach: the synthesized protected copy constructor —
    /// the route that stayed open under a private ordinary constructor — and, for a
    /// root whose ordinary parameterless constructor is itself derivable (declared
    /// or synthesized as protected/public), that ordinary route too. The probes are
    /// abstract records, so an assembly-private abstract implementation hook does
    /// not independently prevent derivation. Externally reachable abstract members
    /// are implemented; only the closed contract must reject the derivation.
    /// </summary>
    private static IReadOnlyList<(string Name, string Source)> RogueDerivations(Type root)
    {
        var rootName = FullName(root);
        var overrides = AbstractMemberOverrides(root);
        var probes = new List<(string, string)>
        {
            (RogueName(root), $"public abstract record {RogueName(root)}({rootName} original) : {rootName}(original)\n{{\n{overrides}}}\n"),
        };

        var ordinaryDerivable = root.GetConstructors(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance)
            .Any(constructor => constructor.GetParameters().Length == 0
                && (constructor.IsPublic || constructor.IsFamily || constructor.IsFamilyOrAssembly));
        if (ordinaryDerivable)
            probes.Add((RogueOrdinaryName(root), $"public abstract record {RogueOrdinaryName(root)}() : {rootName}\n{{\n{overrides}}}\n"));

        return probes;
    }

    /// <summary>
    /// Overrides for every externally reachable abstract property and method of
    /// <paramref name="root"/> (the record's own synthesized members, such as the
    /// clone method, are excluded), so a probe fails only for the reason under test.
    /// </summary>
    private static string AbstractMemberOverrides(Type root)
    {
        const BindingFlags declared = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance;
        var properties = root.GetProperties(declared)
            .Where(property => property.GetGetMethod(nonPublic: true) is { IsAbstract: true } getter
                && IsExternallyReachable(getter))
            .Select(property => $"    {OverrideAccess(property.GetGetMethod(nonPublic: true)!)} override {FullName(property.PropertyType)} {property.Name} => default!;\n");
        var methods = root.GetMethods(declared)
            .Where(method => method is { IsAbstract: true, IsSpecialName: false }
                && IsExternallyReachable(method)
                && !method.Name.Contains('<', StringComparison.Ordinal))
            .Select(method =>
            {
                var parameters = string.Join(", ", method.GetParameters().Select(parameter => $"{FullName(parameter.ParameterType)} {parameter.Name}"));
                var returnsVoid = method.ReturnType == typeof(void);
                return $"    {OverrideAccess(method)} override {(returnsVoid ? "void" : FullName(method.ReturnType))} {method.Name}({parameters}) {(returnsVoid ? "{ }" : "=> default!;")}\n";
            });

        return string.Concat(properties) + string.Concat(methods);
    }

    private static bool IsExternallyReachable(MethodInfo method)
        => method.IsPublic || method.IsFamily || method.IsFamilyOrAssembly;

    private static string OverrideAccess(MethodInfo method) => method.IsPublic ? "public" : "protected";

    /// <summary>
    /// A switch expression over every direct variant of <paramref name="root"/>
    /// (minus <paramref name="omit"/>), deliberately WITHOUT a catch-all arm, so
    /// the compiler alone decides whether the hierarchy is exhaustively covered.
    /// </summary>
    private static string ExhaustiveSwitch(Type root, Type? omit)
    {
        var arms = DirectVariants(root)
            .Where(variant => variant != omit && (variant.IsPublic || variant.IsNestedPublic))
            .Select((variant, index) => $"        {FullName(variant)} => {index},\n");

        return $"    public static int Classify{root.Name}({FullName(root)} value) => value switch\n    {{\n{string.Concat(arms)}    }};\n";
    }

    // ── The pinned SDK's compiler ───────────────────────────────────────────

    private static CompilationResult Compile(string source, string probeName) => ConsumerCompiler.Compile(source, probeName);
}
