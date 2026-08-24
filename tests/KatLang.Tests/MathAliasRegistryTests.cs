using System.Reflection;

namespace KatLang.Tests;

/// <summary>
/// Pins the predefined lower-camel-case Math alias surface at the registry and
/// prelude level: the explicit 21-alias inventory, fail-loud metadata
/// validation, prelude projection with canonical <c>Algorithm.Value</c>
/// REFERENCE identity, the derived name inventories, the closed-member
/// invariant safe sharing depends on, and host-operation reservation.
/// </summary>
public class MathAliasRegistryTests
{
    /// <summary>
    /// The complete alias inventory, restated BY HAND so any change to the
    /// registry's mapping is a reviewed diff in two places.
    /// </summary>
    private static readonly IReadOnlyDictionary<string, string> ExpectedAliases =
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["Pi"] = "pi",
            ["E"] = "e",
            ["Abs"] = "abs",
            ["Ceil"] = "ceil",
            ["Floor"] = "floor",
            ["Round"] = "round",
            ["Sign"] = "sign",
            ["Sqrt"] = "sqrt",
            ["Ln"] = "ln",
            ["Lg"] = "lg",
            ["Sin"] = "sin",
            ["Asin"] = "asin",
            ["Cos"] = "cos",
            ["Acos"] = "acos",
            ["Tan"] = "tan",
            ["Atan"] = "atan",
            ["Atan2"] = "atan2",
            ["Pow"] = "pow",
            ["Log"] = "log",
            ["Random"] = "random",
            ["RandomInt"] = "randomInt",
        };

    [Fact]
    public void AliasInventory_IsExactlyTheDocumentedTable()
    {
        Assert.Equal(21, ExpectedAliases.Count);
        Assert.Equal(ExpectedAliases.Count, BuiltinRegistry.MathMembers.Count);

        foreach (var member in BuiltinRegistry.MathMembers)
        {
            Assert.True(
                ExpectedAliases.TryGetValue(member.Name, out var expectedAlias),
                $"Math member '{member.Name}' has no documented alias expectation.");
            Assert.Equal(expectedAlias, member.PreludeAlias);
        }
    }

    [Fact]
    public void DerivedNameInventories_ComeFromTheAliasMetadata()
    {
        var aliases = BuiltinRegistry.MathMembers.Select(static member => member.PreludeAlias).ToArray();

        Assert.Equal(aliases, BuiltinRegistry.MathAliasNames);
        Assert.Equal(
            new[] { "Math" }.Concat(aliases).OrderBy(static name => name, StringComparer.Ordinal),
            BuiltinRegistry.RuntimePreludeExtraNames.OrderBy(static name => name, StringComparer.Ordinal));
        Assert.Equal(
            new[] { "Math", "load" }.Concat(aliases).OrderBy(static name => name, StringComparer.Ordinal),
            BuiltinRegistry.SemanticPreludeExtraNames.OrderBy(static name => name, StringComparer.Ordinal));

        foreach (var alias in aliases)
        {
            Assert.Contains(alias, BuiltinRegistry.ParameterDetectorPreludeNames);
            // Aliases exist in the RUNTIME prelude, so they are eligible as
            // ordinary lexical dot-call fallbacks (`x.cos`), unlike `load`.
            Assert.True(BuiltinRegistry.IsRuntimePreludeName(alias));
        }

        Assert.False(BuiltinRegistry.IsRuntimePreludeName("load"));
    }

    [Fact]
    public void RegistryInventories_AreImmutableSnapshots()
    {
        var members = Assert.IsAssignableFrom<IList<MathMemberDescriptor>>(BuiltinRegistry.MathMembers);
        Assert.True(members.IsReadOnly);
        Assert.Throws<NotSupportedException>(() => members[0] = new MathMemberDescriptor(
            "Changed", MathMemberKind.Constant, "changed"));

        foreach (var inventory in new[]
        {
            BuiltinRegistry.MathAliasNames,
            BuiltinRegistry.MathMemberNames,
            BuiltinRegistry.RuntimePreludeExtraNames,
            BuiltinRegistry.SemanticPreludeExtraNames,
            BuiltinRegistry.ParameterDetectorPreludeNames,
        })
        {
            var list = Assert.IsAssignableFrom<IList<string>>(inventory);
            Assert.True(list.IsReadOnly);
            Assert.Throws<NotSupportedException>(() => list[0] = "changed");
        }

        // Host-name validation is process-wide and read-only too; no caller can
        // mutate reservation while another configuration is being created.
        var reservedNames = Assert.IsAssignableFrom<ISet<string>>(HostOperations.ReservedPreludeNames);
        Assert.True(reservedNames.IsReadOnly);
        Assert.Throws<NotSupportedException>(() => reservedNames.Add("changed"));
    }

    [Fact]
    public void RuntimeAndSemanticPreludes_ProjectEveryAliasWithReferenceIdenticalCanonicalValue()
    {
        foreach (var prelude in new[]
        {
            BuiltinRegistry.CreateRuntimePreludeAlgorithm(),
            BuiltinRegistry.CreateSemanticPreludeAlgorithm(),
        })
        {
            AssertAliasesShareCanonicalValues(prelude);
        }
    }

    [Fact]
    public void HostExtendedPreludes_RetainEveryAliasExactlyOnceWithCanonicalIdentity()
    {
        var hostOperations = HostOperations.Create(HostOperation.Create(
            "Abs",
            static (_, _) => new Result.Atom(123),
            "value"));

        foreach (var prelude in new[]
        {
            hostOperations.RuntimePreludeAlgorithm,
            hostOperations.SemanticPreludeAlgorithm,
        })
        {
            AssertAliasesShareCanonicalValues(prelude);
            foreach (var alias in ExpectedAliases.Values)
                Assert.Single(prelude.Properties, property => property.Name == alias);

            // Canonical PascalCase names remain independent legal host names.
            Assert.Single(prelude.Properties, static property => property.Name == "Abs");
        }
    }

    [Fact]
    public void EvaluatorAndSemanticBuilderStaticPreludes_ShareCanonicalAliasValues()
    {
        // The instances evaluation and the semantic model ACTUALLY use, not
        // freshly constructed ones.
        AssertAliasesShareCanonicalValues(GetStaticPrelude(typeof(Evaluator), "PreludeAlg"));

        var semanticBuilderType = typeof(Semantics.SemanticModelBuilder).GetNestedType("Builder", BindingFlags.NonPublic)
            ?? throw new InvalidOperationException("SemanticModelBuilder.Builder was not found.");
        AssertAliasesShareCanonicalValues(GetStaticPrelude(semanticBuilderType, "PreludeAlgorithm"));
    }

    [Fact]
    public void SharedStaticPreludeAliases_AreSafeAcrossConcurrentRuns()
    {
        var root = SourceProvenance.ParseValid("sin(pi / 2), cos(0), abs(-3)").Root;
        var failures = new System.Collections.Concurrent.ConcurrentBag<string>();

        Parallel.For(0, 128, _ =>
        {
            try
            {
                var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(root));
                if (result.IsError)
                    failures.Add(result.Error.ToString() ?? "unknown error");
                else if (!result.Value.SequenceEqual([1m, 1m, 3m]))
                    failures.Add($"unexpected result: {string.Join(", ", result.Value)}");
            }
            catch (Exception exception)
            {
                failures.Add(exception.ToString());
            }
        });

        Assert.Empty(failures);
    }

    private static Algorithm.User GetStaticPrelude(Type type, string fieldName)
    {
        var field = type.GetField(fieldName, BindingFlags.Static | BindingFlags.NonPublic)
            ?? throw new InvalidOperationException($"Field {type.FullName}.{fieldName} was not found.");
        return Assert.IsType<Algorithm.User>(field.GetValue(null));
    }

    private static void AssertAliasesShareCanonicalValues(Algorithm.User prelude)
    {
        var math = Assert.IsType<Algorithm.User>(
            Assert.Single(prelude.Properties, static property => property.Name == "Math").Value);

        foreach (var member in BuiltinRegistry.MathMembers)
        {
            var canonical = Assert.Single(math.Properties, property => property.Name == member.Name);
            var alias = Assert.Single(prelude.Properties, property => property.Name == member.PreludeAlias);

            // THE identity invariant: the alias's value IS the canonical member's
            // algorithm instance — never a duplicate constant, native call, or
            // forwarding wrapper.
            Assert.Same(canonical.Value, alias.Value);
            Assert.True(alias.IsPublic);
        }
    }

    [Fact]
    public void MathAlgorithm_ContainsOnlyCanonicalPascalCaseMembers()
    {
        foreach (var flavor in new[] { MathAlgorithmFlavor.Runtime, MathAlgorithmFlavor.SignatureOnly })
        {
            var math = BuiltinRegistry.CreateMathAlgorithm(flavor);
            var names = math.Properties.Select(static property => property.Name).ToHashSet(StringComparer.Ordinal);

            Assert.Equal(
                BuiltinRegistry.MathMemberNames.OrderBy(static name => name, StringComparer.Ordinal),
                names.OrderBy(static name => name, StringComparer.Ordinal));

            foreach (var alias in BuiltinRegistry.MathAliasNames)
                Assert.DoesNotContain(alias, names);
        }
    }

    [Fact]
    public void MathMemberAlgorithms_AreClosedOverDeclaredParametersOnly()
    {
        // Safe target sharing depends on Math member algorithms being CLOSED:
        // parentless, no local properties or opens, and an output that is only
        // the constant or the native call over the declared parameters.
        var runtime = BuiltinRegistry.CreateMathAlgorithm(MathAlgorithmFlavor.Runtime);
        foreach (var member in BuiltinRegistry.MathMembers)
        {
            var algorithm = Assert.IsType<Algorithm.User>(
                Assert.Single(runtime.Properties, property => property.Name == member.Name).Value);

            Assert.Null(algorithm.Parent);
            Assert.Empty(algorithm.Opens);
            Assert.Empty(algorithm.Properties);
            Assert.Equal(member.Arity, algorithm.Params.Count);

            var output = Assert.Single(algorithm.Output);
            if (member.Kind == MathMemberKind.Constant)
            {
                Assert.IsType<Expr.Num>(output);
            }
            else
            {
                var nativeCall = Assert.IsType<Expr.NativeCall>(output);
                Assert.Equal(member.Name, nativeCall.FnName);
                Assert.Equal(algorithm.Params, nativeCall.ArgNames);
            }
        }

        var signatureOnly = BuiltinRegistry.CreateMathAlgorithm(MathAlgorithmFlavor.SignatureOnly);
        foreach (var property in signatureOnly.Properties)
        {
            var algorithm = Assert.IsType<Algorithm.User>(property.Value);
            Assert.Null(algorithm.Parent);
            Assert.Empty(algorithm.Opens);
            Assert.Empty(algorithm.Properties);
            Assert.Empty(algorithm.Output);
        }
    }

    [Fact]
    public void MathCallableFacts_ShareCanonicalIdentityAcrossSpellings()
    {
        foreach (var member in BuiltinRegistry.MathMembers)
        {
            if (member.Kind == MathMemberKind.Constant)
            {
                Assert.False(BuiltinRegistry.TryGetMathMemberFacts(member.Name, out _));
                Assert.False(BuiltinRegistry.TryGetMathAliasFacts(member.PreludeAlias, out _));
                continue;
            }

            Assert.True(BuiltinRegistry.TryGetMathMemberFacts(member.Name, out var canonicalFacts));
            Assert.True(BuiltinRegistry.TryGetMathAliasFacts(member.PreludeAlias, out var aliasFacts));

            Assert.Equal($"Math.{member.Name}", canonicalFacts!.CanonicalKey);
            Assert.Equal(canonicalFacts.CanonicalKey, aliasFacts!.CanonicalKey);
            Assert.Equal(member.Name, canonicalFacts.SpelledName);
            Assert.Equal(member.PreludeAlias, aliasFacts.SpelledName);
            Assert.Equal(
                canonicalFacts.Signature.ParameterNames,
                aliasFacts.Signature.ParameterNames);
            Assert.True(canonicalFacts.HasStrictValueArguments);
            Assert.True(aliasFacts.HasStrictValueArguments);

            // The alias spelling never looks up canonical facts and vice versa.
            Assert.False(BuiltinRegistry.TryGetMathMemberFacts(member.PreludeAlias, out _));
            Assert.False(BuiltinRegistry.TryGetMathAliasFacts(member.Name, out _));
        }

        Assert.Equal("round(x, y)", GetAliasFacts("round").Signature.DisplayText);
        Assert.Equal("atan2(y, x)", GetAliasFacts("atan2").Signature.DisplayText);
        Assert.Equal("log(x, y)", GetAliasFacts("log").Signature.DisplayText);
        Assert.Equal("random(start, end)", GetAliasFacts("random").Signature.DisplayText);
        Assert.Equal("randomInt(start, end)", GetAliasFacts("randomInt").Signature.DisplayText);
    }

    private static MathCallableFacts GetAliasFacts(string alias)
    {
        Assert.True(BuiltinRegistry.TryGetMathAliasFacts(alias, out var facts));
        return facts!;
    }

    [Fact]
    public void MetadataValidation_FailsLoudlyOnInvalidAliases()
    {
        var reserved = BuiltinRegistry.BuiltinNames.Concat(["Math", "load"]).ToArray();

        MathMemberDescriptor Member(string name, string alias)
            => new(name, MathMemberKind.UnaryFunction, alias);

        // A valid list passes.
        BuiltinRegistry.ValidateMathMemberMetadataCore([Member("Sin", "sin")], reserved);

        var invalidMemberName = Assert.Throws<InvalidOperationException>(
            () => BuiltinRegistry.ValidateMathMemberMetadataCore([Member("not valid", "sin")], reserved));
        Assert.Contains("Math member name", invalidMemberName.Message);
        Assert.Contains("not a valid KatLang identifier", invalidMemberName.Message);

        var duplicateMemberName = Assert.Throws<InvalidOperationException>(
            () => BuiltinRegistry.ValidateMathMemberMetadataCore(
                [Member("Sin", "sin"), Member("Sin", "sine")], reserved));
        Assert.Contains("declared more than once", duplicateMemberName.Message);

        var invalidIdentifier = Assert.Throws<InvalidOperationException>(
            () => BuiltinRegistry.ValidateMathMemberMetadataCore([Member("Sin", "not valid")], reserved));
        Assert.Contains("not a valid KatLang identifier", invalidIdentifier.Message);

        var missing = Assert.Throws<InvalidOperationException>(
            () => BuiltinRegistry.ValidateMathMemberMetadataCore(
                [new MathMemberDescriptor("Sin", MathMemberKind.UnaryFunction, null!)], reserved));
        Assert.Contains("not a valid KatLang identifier", missing.Message);

        var duplicate = Assert.Throws<InvalidOperationException>(
            () => BuiltinRegistry.ValidateMathMemberMetadataCore(
                [Member("Sin", "sin"), Member("Cos", "sin")], reserved));
        Assert.Contains("another Math member already uses", duplicate.Message);

        Assert.False(Lexer.IsValidIdentifier("Math.Sin"));

        foreach (var collision in reserved)
        {
            var collided = Assert.Throws<InvalidOperationException>(
                () => BuiltinRegistry.ValidateMathMemberMetadataCore([Member("Sin", collision)], reserved));
            Assert.Contains("collides with an existing prelude name", collided.Message);
        }
    }

    [Fact]
    public void HostOperations_RejectAliasNamesAsReserved()
    {
        static Result Implementation(IReadOnlyList<Result> args, CancellationToken token) => new Result.Atom(1);

        foreach (var alias in BuiltinRegistry.MathAliasNames)
        {
            Assert.Contains(alias, HostOperations.ReservedPreludeNames);
            var exception = Assert.Throws<ArgumentException>(() => HostOperation.Create(alias, Implementation));
            Assert.Contains("reserved by the KatLang prelude", exception.Message);
            Assert.Contains("Math member aliases", exception.Message);
        }

        // Canonical PascalCase member names are NOT prelude names: a host
        // operation named `Abs` stays legal (it never shadows `Math.Abs`).
        var canonical = HostOperation.Create("Abs", Implementation, "value");
        Assert.Equal("Abs", canonical.Name);
    }
}
