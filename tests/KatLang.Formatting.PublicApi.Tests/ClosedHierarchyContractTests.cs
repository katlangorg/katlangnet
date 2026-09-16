using System.Diagnostics;
using System.Reflection;
using System.Runtime.InteropServices;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

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
        new(typeof(RunResult), "new KatLang.RunResult.ParseFailure([])"),
        new(typeof(EvalError), "new KatLang.EvalError.DivByZero()"),
        new(typeof(Result), "new KatLang.Result.Str(\"s\")"),
        new(typeof(Algorithm), "new KatLang.Algorithm.Conditional(null, [], [])"),
        new(typeof(Pattern), "new KatLang.Pattern.Bind(\"x\")"),
        new(typeof(ParameterPattern), "new KatLang.CaptureParameterPattern(\"x\")"),
        new(
            typeof(CallableBindingNode),
            "new KatLang.CaptureBindingNode(new KatLang.CallableBindingCapture(\"x\", KatLang.ParameterKind.Normal, KatLang.CallableParameterSource.Explicit))"),
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
    /// or synthesized as protected/public), that ordinary route too. Each implements
    /// every abstract member so that, were the root open, nothing else could stop
    /// the derivation from compiling.
    /// </summary>
    private static IReadOnlyList<(string Name, string Source)> RogueDerivations(Type root)
    {
        var rootName = FullName(root);
        var overrides = AbstractMemberOverrides(root);
        var probes = new List<(string, string)>
        {
            (RogueName(root), $"public sealed record {RogueName(root)}({rootName} original) : {rootName}(original)\n{{\n{overrides}}}\n"),
        };

        var ordinaryDerivable = root.GetConstructors(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance)
            .Any(constructor => constructor.GetParameters().Length == 0
                && (constructor.IsPublic || constructor.IsFamily || constructor.IsFamilyOrAssembly));
        if (ordinaryDerivable)
            probes.Add((RogueOrdinaryName(root), $"public sealed record {RogueOrdinaryName(root)}() : {rootName}\n{{\n{overrides}}}\n"));

        return probes;
    }

    /// <summary>
    /// Overrides for every abstract property and method of <paramref name="root"/>
    /// a derived record must implement (the record's own synthesized members, such
    /// as the clone method, are excluded), so a probe fails only for the reason
    /// under test.
    /// </summary>
    private static string AbstractMemberOverrides(Type root)
    {
        const BindingFlags declared = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance;
        var properties = root.GetProperties(declared)
            .Where(property => property.GetGetMethod(nonPublic: true) is { IsAbstract: true, IsPrivate: false })
            .Select(property => $"    public override {FullName(property.PropertyType)} {property.Name} => default!;\n");
        var methods = root.GetMethods(declared)
            .Where(method => method is { IsAbstract: true, IsPrivate: false, IsSpecialName: false }
                && !method.Name.Contains('<', StringComparison.Ordinal))
            .Select(method =>
            {
                var parameters = string.Join(", ", method.GetParameters().Select(parameter => $"{FullName(parameter.ParameterType)} {parameter.Name}"));
                var returnsVoid = method.ReturnType == typeof(void);
                return $"    public override {(returnsVoid ? "void" : FullName(method.ReturnType))} {method.Name}({parameters}) {(returnsVoid ? "{ }" : "=> default!;")}\n";
            });

        return string.Concat(properties) + string.Concat(methods);
    }

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

    private sealed record CompilerDiagnostic(string Code, string Message);

    private sealed record CompilationResult(int ExitCode, string Output, IReadOnlyList<CompilerDiagnostic> Diagnostics);

    private static readonly Regex DiagnosticLine = new(
        @"\berror (?<code>CS\d{4}): (?<message>.*)$",
        RegexOptions.Compiled | RegexOptions.Multiline);

    /// <summary>
    /// Compiles <paramref name="source"/> as a library against the KatLang assembly
    /// under test with <c>csc.dll</c> of the SDK pinned in <c>global.json</c>, the
    /// compiler that built the assembly. Nullable annotations are on and
    /// <c>CS8509</c>/<c>CS8655</c> are errors, as in the repository's projects.
    /// </summary>
    private static CompilationResult Compile(string source, string probeName)
    {
        var workDirectory = Path.Combine(Path.GetTempPath(), $"katlang-closed-{probeName}-{Guid.NewGuid():N}");
        Directory.CreateDirectory(workDirectory);
        try
        {
            var sourcePath = Path.Combine(workDirectory, probeName + ".cs");
            var responsePath = Path.Combine(workDirectory, probeName + ".rsp");
            var outputPath = Path.Combine(workDirectory, probeName + ".dll");
            File.WriteAllText(sourcePath, source);

            var response = new StringBuilder();
            response.Append("-noconfig\n-nostdlib\n-nologo\n-target:library\n-nullable:enable\n-warnaserror+:CS8509,CS8655\n");
            foreach (var reference in ReferenceAssemblies())
                response.Append("-reference:\"").Append(reference).Append("\"\n");
            response.Append("-out:\"").Append(outputPath).Append("\"\n");
            response.Append('"').Append(sourcePath).Append("\"\n");
            File.WriteAllText(responsePath, response.ToString());

            var startInfo = new ProcessStartInfo(DotnetHost())
            {
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                UseShellExecute = false,
                CreateNoWindow = true,
            };
            startInfo.ArgumentList.Add("exec");
            startInfo.ArgumentList.Add(PinnedCompilerPath());
            startInfo.ArgumentList.Add("@" + responsePath);
            startInfo.Environment["DOTNET_NOLOGO"] = "1";

            using var process = new Process { StartInfo = startInfo };
            process.Start();
            var stdout = process.StandardOutput.ReadToEndAsync();
            var stderr = process.StandardError.ReadToEndAsync();
            if (!process.WaitForExit(120_000))
            {
                try { process.Kill(entireProcessTree: true); }
                catch { /* already exited */ }
                throw new InvalidOperationException($"The C# compiler did not finish compiling the '{probeName}' probe within 120 seconds.");
            }

            var output = stdout.GetAwaiter().GetResult() + stderr.GetAwaiter().GetResult();
            var diagnostics = DiagnosticLine.Matches(output)
                .Select(match => new CompilerDiagnostic(match.Groups["code"].Value, match.Groups["message"].Value.TrimEnd()))
                .ToList();
            return new CompilationResult(process.ExitCode, output, diagnostics);
        }
        finally
        {
            try { Directory.Delete(workDirectory, recursive: true); }
            catch { /* best-effort cleanup of the probe directory */ }
        }
    }

    /// <summary>
    /// The framework and package assemblies the test host itself runs against —
    /// the KatLang assembly under test included — so the probe binds exactly what
    /// this process binds.
    /// </summary>
    private static IReadOnlyList<string> ReferenceAssemblies()
    {
        var trusted = AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES") as string
            ?? throw new InvalidOperationException("The test host exposes no TRUSTED_PLATFORM_ASSEMBLIES list to reference.");
        var references = trusted
            .Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Where(path => path.EndsWith(".dll", StringComparison.OrdinalIgnoreCase))
            .ToList();
        if (!references.Contains(KatLangAssembly.Location, StringComparer.OrdinalIgnoreCase))
            references.Add(KatLangAssembly.Location);
        return references;
    }

    private static string DotnetHost()
    {
        var host = Environment.GetEnvironmentVariable("DOTNET_HOST_PATH");
        if (!string.IsNullOrEmpty(host) && File.Exists(host))
            return host;

        var candidate = Path.Combine(DotnetRoot(), RuntimeInformation.IsOSPlatform(OSPlatform.Windows) ? "dotnet.exe" : "dotnet");
        return File.Exists(candidate) ? candidate : "dotnet";
    }

    /// <summary>
    /// <c>csc.dll</c> of the SDK version pinned by the repository's <c>global.json</c>:
    /// the probes must use the compiler that built the assembly, not whichever
    /// newest SDK happens to be installed. A missing pinned SDK is a blocked test,
    /// never a pass.
    /// </summary>
    private static string PinnedCompilerPath()
    {
        var globalJson = Path.Combine(RepoRoot.Find(), "global.json");
        using var document = JsonDocument.Parse(File.ReadAllText(globalJson));
        var version = document.RootElement.GetProperty("sdk").GetProperty("version").GetString()
            ?? throw new InvalidOperationException("global.json pins no SDK version.");

        var compiler = Path.Combine(DotnetRoot(), "sdk", version, "Roslyn", "bincore", "csc.dll");
        if (!File.Exists(compiler))
        {
            throw new InvalidOperationException(
                $"The pinned SDK {version} (global.json) has no compiler at '{compiler}'; the closed-hierarchy probes cannot run.");
        }

        return compiler;
    }

    /// <summary>The dotnet installation hosting this test run: the muxer's directory when known, else the runtime's ancestor.</summary>
    private static string DotnetRoot()
    {
        var host = Environment.GetEnvironmentVariable("DOTNET_HOST_PATH");
        if (!string.IsNullOrEmpty(host) && File.Exists(host) && Path.GetDirectoryName(host) is { } hostDirectory)
            return hostDirectory;

        var configured = Environment.GetEnvironmentVariable("DOTNET_ROOT");
        if (!string.IsNullOrEmpty(configured) && Directory.Exists(configured))
            return configured;

        // <root>/shared/Microsoft.NETCore.App/<version>/ → <root>
        var runtime = RuntimeEnvironment.GetRuntimeDirectory().TrimEnd(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar);
        return Path.GetFullPath(Path.Combine(runtime, "..", "..", ".."));
    }
}
