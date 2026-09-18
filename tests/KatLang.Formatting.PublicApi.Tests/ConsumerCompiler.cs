using System.Diagnostics;
using System.Reflection;
using System.Runtime.InteropServices;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace KatLang.Formatting.PublicApi.Tests;

internal sealed record CompilerDiagnostic(string Code, string Message, int? Line = null);

internal sealed record CompilationResult(int ExitCode, string Output, IReadOnlyList<CompilerDiagnostic> Diagnostics);

/// <summary>
/// Compiles small CONSUMER programs against the built KatLang assembly with the pinned
/// SDK's own C# compiler (<c>global.json</c> — the one SDK authority), exactly as a NuGet
/// consumer meets the package: this test project is deliberately not a friend assembly,
/// and neither is the probe, so what the compiler accepts or refuses here is the public
/// contract. Shared by the closed-hierarchy probes (<see cref="ClosedHierarchyContractTests"/>)
/// and the variant-ownership probes (<see cref="AlgorithmPublicSurfaceTests"/>).
/// </summary>
internal static class ConsumerCompiler
{
    private static readonly Assembly KatLangAssembly = typeof(KatLangEngine).Assembly;

    // `path(line,col): error CSnnnn: message`; a location-free diagnostic keeps Line null.
    private static readonly Regex DiagnosticLine = new(
        @"(?:\((?<line>\d+),\d+\): )?\berror (?<code>CS\d{4}): (?<message>.*)$",
        RegexOptions.Compiled | RegexOptions.Multiline);

    /// <summary>
    /// Compiles <paramref name="source"/> as a library against the KatLang assembly
    /// under test with <c>csc.dll</c> of the SDK pinned in <c>global.json</c>, the
    /// compiler that built the assembly. Nullable annotations are on and
    /// <c>CS8509</c>/<c>CS8655</c> are errors, as in the repository's projects.
    /// </summary>
    internal static CompilationResult Compile(string source, string probeName)
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
                .Select(match => new CompilerDiagnostic(
                    match.Groups["code"].Value,
                    match.Groups["message"].Value.TrimEnd(),
                    match.Groups["line"].Success ? int.Parse(match.Groups["line"].Value, System.Globalization.CultureInfo.InvariantCulture) : null))
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
                $"The pinned SDK {version} (global.json) has no compiler at '{compiler}'; the consumer compile probes cannot run.");
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
