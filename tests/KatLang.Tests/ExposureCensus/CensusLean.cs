using System.Text;
using System.Security.Cryptography;

namespace KatLang.Tests.ExposureCensus;

/// <summary>
/// The model check M (brief section 2), run OUTSIDE the canonical Lean targets: an emit step writes
/// every tree's encoding into ignored Lean files that print, per encoding, its id, <c>paramsBound</c>,
/// <c>exposureFull</c> and the Lean evaluator's outcome in the census's neutral rendering; after
/// <c>lake env lean &lt;file&gt;</c> has run each file, a check step compares that output with the C#
/// verdicts (O and the C# outcomes) and produces M1–M4.
/// </summary>
internal static class CensusLean
{
    public const int BatchSize = 150;

    // The neutral raw-structure encoding and innermost-error categories of LanguageSpecCases.lean (shared
    // with SemanticExplorerHarness.Neutral / ErrorCategory), plus the subject of the three name errors.
    private const string Preamble = """
        import KatLangArityLaws.NavigationSourceDomain
        open KatLang KatLang.NavigationSourceDomain
        set_option maxRecDepth 100000
        set_option maxHeartbeats 0

        namespace ExposureCensus

        partial def neutral : Result -> String
          | .atom n => toString n
          | .str s => "'" ++ s ++ "'"
          | .bool b => Result.boolText b
          | .sequenceValue rs => "S[" ++ String.intercalate ", " (rs.map neutral) ++ "]"
          | .listValue rs => "L[" ++ String.intercalate ", " (rs.map neutral) ++ "]"
          | .callRef _ => "CallReference"
          | .argView _ => "CallReference"

        partial def errCategory : Error -> String
          | .withContext _ inner => errCategory inner
          | .arityMismatch _ _ => "arity"
          | .badArity => "arity"
          | .branchArityMismatch _ _ _ => "arity"
          | .branchOutputArityMismatch _ _ _ => "arity"
          | .badIndex => "index"
          | .typeMismatch _ => "type"
          | .missingOutput _ => "missingOutput"
          | .spreadMissingOutput => "spreadMissingOutput"
          | .unknownName _ => "unknownName"
          | .divByZero => "div0"
          | .demandCycle => "demandCycle"
          | .noMatchingBranch _ => "branch"
          | .unknownProperty _ _ => "unknownProperty"
          | .notPublicProperty _ _ => "notPublicProperty"
          | .localOnlyProperty _ _ _ => "localOnlyProperty"
          | .notAnAlgorithm _ => "notAnAlgorithm"
          | .illegalInOpen _ => "illegalInOpen"
          | .badOpenForm _ => "badOpenForm"
          | .illegalInEval _ => "illegalInEval"
          | .ambiguousOpen _ _ => "ambiguousOpen"
          | .duplicateProperty _ => "duplicateProperty"
          | .duplicateBranchPattern => "duplicateBranchPattern"
          | .explicitParamsRequireOutput => "explicitParamsRequireOutput"
          | .unresolvedImplicitParams _ => "unresolvedImplicitParams"
          | .fuelExhausted => "incomplete"

        partial def errSubject : Error -> String
          | .withContext _ inner => errSubject inner
          | .localOnlyProperty _ name _ => ":" ++ name
          | .unknownName name => ":" ++ name
          | .unknownProperty _ name => ":" ++ name
          | _ => ""

        def render : Except Error Result -> String
          | .ok r => "ok " ++ neutral r
          | .error e => "err " ++ errCategory e ++ errSubject e

        def report (id : String) (e : Expr) : IO Unit :=
          IO.println s!"CENSUS\t{id}\t{paramsBound e}\t{exposureFull e}\t{render (runResult e)}"

        end ExposureCensus
        open ExposureCensus

        """;

    /// <summary>Writes the batch files and a manifest of the C# side (id, role, copy key, C# outcome).</summary>
    public static int Emit(IReadOnlyList<CensusLeanItem> items, string directory)
    {
        Directory.CreateDirectory(directory);
        var manifest = new StringBuilder();
        var batch = 0;
        for (var start = 0; start < items.Count; start += BatchSize, batch++)
        {
            var file = new StringBuilder(Preamble.Replace("\r", ""));
            foreach (var item in items.Skip(start).Take(BatchSize))
            {
                var encoding = LeanAstEncoder.EncodeProgram(item.Tree);
                file.Append($"#eval report {LeanAstEncoder.QuoteString(item.Id)} ({encoding})\n");
                manifest.Append(ManifestLine(item, encoding)).Append('\n');
            }
            File.WriteAllText(Path.Combine(directory, $"census-{batch:D4}.lean"), file.ToString());
        }
        File.WriteAllText(Path.Combine(directory, "manifest.tsv"), manifest.ToString());
        return batch;
    }

    public sealed record LeanLine(string Id, bool ParamsBound, bool ExposureFull, string Outcome);

    private static string ManifestLine(CensusLeanItem item, string encoding)
        => $"{item.Id}\t{item.CaseId}\t{item.CopyKey}\t{item.Role}\t{item.CSharpOutcome}\t"
            + Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(encoding)));

    public static Dictionary<string, LeanLine> ReadOutputs(string directory)
    {
        var lines = new Dictionary<string, LeanLine>(StringComparer.Ordinal);
        foreach (var path in Directory.GetFiles(directory, "census-*.out").Order(StringComparer.Ordinal))
            foreach (var line in File.ReadLines(path))
            {
                if (!line.StartsWith("CENSUS\t", StringComparison.Ordinal)) continue;
                var parts = line.Split('\t');
                if (parts.Length != 5 || !bool.TryParse(parts[2], out var bound) || !bool.TryParse(parts[3], out var full)
                    || !lines.TryAdd(parts[1], new LeanLine(parts[1], bound, full, parts[4])))
                    throw new InvalidDataException($"Malformed or duplicate Lean observation in {path}: {line}");
            }
        return lines;
    }

    /// <summary>M1–M4, requiring complete output and a manifest matching the current trees and C# verdicts.</summary>
    public static List<CensusGap> Check(string directory, IReadOnlyList<CensusLeanItem> expected)
    {
        var manifest = File.ReadAllLines(Path.Combine(directory, "manifest.tsv"));
        if (expected.Count == 0 || !manifest.SequenceEqual(expected.Select(item => ManifestLine(item, LeanAstEncoder.EncodeProgram(item.Tree)))))
            throw new InvalidDataException("The Lean manifest does not match the current census encodings and C# verdicts. Emit and run fresh batches.");
        var lean = ReadOutputs(directory);
        if (expected.Select(item => item.Id).Distinct(StringComparer.Ordinal).Count() != expected.Count
            || !lean.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(expected.Select(item => item.Id)))
            throw new InvalidDataException("Lean output is incomplete or contains unexpected encodings; every manifest item must be evaluated exactly once.");
        var gaps = new List<CensusGap>();
        var copyAdmission = new Dictionary<(string Case, string Copy), (string Role, bool AnyFull, bool AllFull)>();
        foreach (var row in manifest)
        {
            var parts = row.Split('\t');
            var (id, caseId, copyKey, role, csharp) = (parts[0], parts[1], parts[2], parts[3], parts[4]);
            var probe = id[(id.LastIndexOf('#') + 1)..];
            var line = lean[id];
            if (line.Outcome != csharp)
                gaps.Add(new CensusGap("M4", "engine-disagreement-lean", caseId, copyKey, $"{probe}: C#={csharp}; Lean={line.Outcome}"));
            if (role == "real")
            {
                if (!line.ParamsBound || !line.ExposureFull)
                    gaps.Add(new CensusGap("M1", "model-refuses-source", caseId, "-", $"{probe}: paramsBound={line.ParamsBound}; exposureFull={line.ExposureFull}"));
                continue;
            }
            var key = (caseId, copyKey);
            copyAdmission[key] = copyAdmission.TryGetValue(key, out var seen)
                ? (role, seen.AnyFull || line.ExposureFull, seen.AllFull && line.ExposureFull)
                : (role, line.ExposureFull, line.ExposureFull);
        }
        foreach (var ((caseId, copyKey), (role, anyFull, allFull)) in copyAdmission.OrderBy(k => k.Key.Case, StringComparer.Ordinal).ThenBy(k => k.Key.Copy, StringComparer.Ordinal))
        {
            var reader = copyKey[..copyKey.IndexOf(':')];
            var requirement = "r=" + copyKey[(copyKey.IndexOf(':') + 1)..];
            if (role == "copy-needed" && anyFull)
                gaps.Add(new CensusGap("M2", "model-false-admission", caseId, reader, requirement));
            else if (role == "copy-unneeded" && !allFull)
                gaps.Add(new CensusGap("M3", "model-stricter", caseId, reader, requirement));
        }
        return gaps;
    }
}
