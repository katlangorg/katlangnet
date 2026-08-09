namespace KatLang.Tests;

/// <summary>
/// Parity between the RUNTIME prelude (<c>BuiltinRegistry.CreateRuntimePreludeAlgorithm</c>,
/// the outermost scope of every evaluation) and the SEMANTIC prelude
/// (<c>CreateSemanticPreludeAlgorithm</c>, the outermost scope of
/// <c>ElaboratedScopeLookup</c> and therefore of parameter detection and the
/// editor).
///
/// <para>
/// A name present in only one of them silently changes lookup for one consumer:
/// a builtin missing from the semantic prelude turns every use into an implicit
/// parameter (rewriting the program), and one missing from the runtime prelude
/// turns a name the editor resolves into an evaluation failure.
/// </para>
///
/// <para>
/// <b>Relationship to <c>BuiltinRegistryParityTests</c>:</b> that suite already
/// pins the NAME inventories — each prelude's builtin names and declared extra
/// names against the registry, plus the Math member inventory. What it does not
/// pin, and what a Track 11 mutation showed survives the whole suite, is
/// per-name METADATA: a builtin that is public in one prelude and private in the
/// other changes nothing observable in any existing test. These tests therefore
/// assert the runtime/semantic relation directly — identity, visibility,
/// exposure, Math parameter names, body shape, and prelude flatness — with the
/// two intended differences stated positively rather than merely tolerated.
/// </para>
///
/// <para>
/// Exactly two differences are intended, and both are asserted positively here
/// rather than merely tolerated:
/// <list type="number">
/// <item><c>load</c> exists ONLY in the semantic prelude — default parse/run
/// entry points reject unresolved <c>load</c>, so only elaboration-enabled
/// paths may see it.</item>
/// <item><c>Math</c> members share names, visibility, and parameter names, but
/// the runtime flavor carries an executable body (a native call, or a literal
/// for a constant) where the signature-only flavor carries none.</item>
/// </list>
/// </para>
/// </summary>
public class PreludeParityTests
{
    private static Algorithm.User Runtime() => BuiltinRegistry.CreateRuntimePreludeAlgorithm();

    private static Algorithm.User Semantic() => BuiltinRegistry.CreateSemanticPreludeAlgorithm();

    /// <summary>The one name the semantic prelude adds.</summary>
    private const string SemanticOnlyName = "load";

    [Fact]
    public void PreludeNameSetsAgreeExceptForLoad()
    {
        var runtime = Runtime().Properties.Select(static p => p.Name).ToList();
        var semantic = Semantic().Properties.Select(static p => p.Name).ToList();

        Assert.Equal(runtime.Count, runtime.Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(semantic.Count, semantic.Distinct(StringComparer.Ordinal).Count());

        var runtimeOnly = runtime.Except(semantic, StringComparer.Ordinal).Order(StringComparer.Ordinal).ToList();
        var semanticOnly = semantic.Except(runtime, StringComparer.Ordinal).Order(StringComparer.Ordinal).ToList();

        Assert.True(
            runtimeOnly.Count == 0,
            $"Names in the RUNTIME prelude only (the editor would treat these as implicit parameters): " +
            $"{string.Join(", ", runtimeOnly)}");
        Assert.True(
            semanticOnly is [SemanticOnlyName],
            $"Names in the SEMANTIC prelude only: expected exactly [{SemanticOnlyName}], got " +
            $"[{string.Join(", ", semanticOnly)}]");
    }

    [Fact]
    public void EveryBuiltinAppearsInBothPreludesWithTheSameIdentityAndVisibility()
    {
        var runtime = Runtime().Properties.ToDictionary(static p => p.Name, StringComparer.Ordinal);
        var semantic = Semantic().Properties.ToDictionary(static p => p.Name, StringComparer.Ordinal);

        var missing = new List<string>();
        foreach (var builtin in BuiltinRegistry.AllBuiltins)
        {
            if (!runtime.ContainsKey(builtin.Name)) missing.Add($"runtime:{builtin.Name}");
            if (!semantic.ContainsKey(builtin.Name)) missing.Add($"semantic:{builtin.Name}");
        }

        Assert.True(missing.Count == 0, $"Builtins absent from a prelude: {string.Join(", ", missing)}");

        var differences = new List<string>();
        foreach (var builtin in BuiltinRegistry.AllBuiltins)
        {
            var r = runtime[builtin.Name];
            var s = semantic[builtin.Name];

            if (r.IsPublic != s.IsPublic)
                differences.Add($"{builtin.Name}: IsPublic runtime={r.IsPublic} semantic={s.IsPublic}");
            if (r.Exposure != s.Exposure)
                differences.Add($"{builtin.Name}: Exposure runtime={r.Exposure} semantic={s.Exposure}");
            if (r.Value is not Algorithm.Builtin(var runtimeId))
                differences.Add($"{builtin.Name}: runtime value is {r.Value.GetType().Name}, not Algorithm.Builtin");
            else if (s.Value is not Algorithm.Builtin(var semanticId))
                differences.Add($"{builtin.Name}: semantic value is {s.Value.GetType().Name}, not Algorithm.Builtin");
            else if (runtimeId != semanticId)
                differences.Add($"{builtin.Name}: BuiltinId runtime={runtimeId} semantic={semanticId}");
            else if (runtimeId != builtin.Id)
                differences.Add($"{builtin.Name}: BuiltinId {runtimeId} does not match registry id {builtin.Id}");
        }

        Assert.True(differences.Count == 0, string.Join(Environment.NewLine, differences));
    }

    [Fact]
    public void MathSurfaceAgreesOnNamesVisibilityAndParameters()
    {
        var runtimeMath = Assert.IsType<Algorithm.User>(MathOf(Runtime()));
        var semanticMath = Assert.IsType<Algorithm.User>(MathOf(Semantic()));

        var runtimeNames = runtimeMath.Properties.Select(static p => p.Name).ToList();
        var semanticNames = semanticMath.Properties.Select(static p => p.Name).ToList();
        Assert.Equal(runtimeNames, semanticNames);

        var differences = new List<string>();
        for (var i = 0; i < runtimeNames.Count; i++)
        {
            var r = runtimeMath.Properties[i];
            var s = semanticMath.Properties[i];

            if (r.IsPublic != s.IsPublic)
                differences.Add($"Math.{r.Name}: IsPublic runtime={r.IsPublic} semantic={s.IsPublic}");
            if (r.Exposure != s.Exposure)
                differences.Add($"Math.{r.Name}: Exposure runtime={r.Exposure} semantic={s.Exposure}");

            var runtimeParameters = r.Value.Parameters.Select(static p => p.Name).ToList();
            var semanticParameters = s.Value.Parameters.Select(static p => p.Name).ToList();
            if (!runtimeParameters.SequenceEqual(semanticParameters, StringComparer.Ordinal))
            {
                differences.Add(
                    $"Math.{r.Name}: parameters runtime=({string.Join(", ", runtimeParameters)}) " +
                    $"semantic=({string.Join(", ", semanticParameters)})");
            }
        }

        Assert.True(differences.Count == 0, string.Join(Environment.NewLine, differences));
        Assert.NotEmpty(runtimeNames);
    }

    /// <summary>
    /// The intended body difference, asserted positively: every runtime Math
    /// member is executable and every signature-only member is not. Without
    /// this, "the bodies differ" could silently become "some bodies went
    /// missing from the runtime prelude".
    /// </summary>
    [Fact]
    public void MathBodiesDifferExactlyAsIntended()
    {
        var runtimeMath = MathOf(Runtime());
        var semanticMath = MathOf(Semantic());

        foreach (var member in runtimeMath.Properties)
        {
            Assert.True(
                member.Value.Output.Count == 1,
                $"Runtime Math.{member.Name} must have exactly one output expression, got {member.Value.Output.Count}.");
            Assert.True(
                member.Value.Output[0] is Expr.NativeCall or Expr.Num,
                $"Runtime Math.{member.Name} output is {member.Value.Output[0].GetType().Name}; " +
                "expected a native call, or a literal for a constant.");
        }

        foreach (var member in semanticMath.Properties)
        {
            Assert.True(
                member.Value.Output.Count == 0,
                $"Signature-only Math.{member.Name} must carry no body, got {member.Value.Output.Count} output expression(s).");
        }
    }

    [Fact]
    public void LoadIsSemanticOnlyAndKeepsItsDocumentedShape()
    {
        Assert.DoesNotContain(Runtime().Properties, static p => p.Name == SemanticOnlyName);

        var load = Assert.Single(Semantic().Properties, static p => p.Name == SemanticOnlyName);
        Assert.True(load.IsPublic);
        Assert.Equal(PropertyExposure.Exported, load.Exposure);
        Assert.Equal(BuiltinRegistry.LoadParameterNames, load.Value.Parameters.Select(static p => p.Name).ToList());
    }

    /// <summary>
    /// Both preludes must be flat containers: no parameters, no opens, no
    /// output. A prelude that acquired an output would make the outermost scope
    /// itself evaluable, and one that acquired an `open` would give every
    /// program an invisible extra provider.
    /// </summary>
    [Fact]
    public void BothPreludesAreFlatContainers()
    {
        foreach (var (label, prelude) in new (string, Algorithm.User)[] { ("runtime", Runtime()), ("semantic", Semantic()) })
        {
            Assert.True(prelude.Parameters.Count == 0, $"{label} prelude declares parameters.");
            Assert.True(prelude.Opens.Count == 0, $"{label} prelude declares opens.");
            Assert.True(prelude.Output.Count == 0, $"{label} prelude declares output.");
            Assert.All(prelude.Properties, property => Assert.True(
                property.IsPublic && property.Exposure == PropertyExposure.Exported,
                $"{label} prelude member '{property.Name}' is not public+exported."));
        }
    }

    private static Algorithm MathOf(Algorithm.User prelude)
        => Assert.Single(prelude.Properties, static p => p.Name == "Math").Value;
}
