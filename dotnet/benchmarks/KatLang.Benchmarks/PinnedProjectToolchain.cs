using System.Reflection;
using BenchmarkDotNet.Configs;
using BenchmarkDotNet.Jobs;
using BenchmarkDotNet.Loggers;
using BenchmarkDotNet.Toolchains;
using BenchmarkDotNet.Toolchains.CsProj;
using BenchmarkDotNet.Toolchains.DotNetCli;

namespace KatLang.Benchmarks;

/// <summary>
/// Makes BenchmarkDotNet build THIS project, whatever other copies of
/// <c>KatLang.Benchmarks.csproj</c> exist below the repository root.
/// </summary>
/// <remarks>
/// BenchmarkDotNet 0.14.0's <see cref="CsProjGenerator"/> finds the project to build by file name: it
/// starts from a discovered solution/project root or the current directory and enumerates every
/// <c>KatLang.Benchmarks.csproj</c>
/// below it, and throws "Found more than one matching project file" when git-ignored scratch copies
/// exist under <c>artifacts/</c> or <c>.claude/worktrees/</c>; every benchmark is then reported as NA.
/// The build pins the path of the project being compiled (<c>$(MSBuildProjectFullPath)</c>) into the
/// assembly, and a mutator job applies a toolchain that is the stock .NET CLI csproj toolchain except
/// that it returns that path, so attribute jobs (<c>[SimpleJob]</c>) and command-line jobs
/// (<c>--job dry</c>) are all built from this project and never searched for.
/// </remarks>
internal static class PinnedProjectToolchain
{
	internal const string ProjectPathMetadataKey = "KatLang.Benchmarks.ProjectPath";

	private const string TargetFrameworkMoniker = "net11.0";

	public static IConfig CreateConfig()
	{
		var project = ResolveProjectFile();
		// The same parts CsProjCoreToolchain.From(NetCoreAppSettings) assembles; null means "the default
		// dotnet CLI / packages folder / runtime version", as in NetCoreAppSettings.
		var toolchain = new Toolchain(
			"CsProj (pinned project)",
			new PinnedProjectGenerator(TargetFrameworkMoniker, project),
			new DotNetCliBuilder(TargetFrameworkMoniker),
			new DotNetCliExecutor(customDotNetCliPath: null!));

		// A mutator is applied to every runnable job, including attribute and command-line jobs.
		return DefaultConfig.Instance.AddJob(new Job("PinnedProject").WithToolchain(toolchain).AsMutator());
	}

	private static FileInfo ResolveProjectFile()
	{
		var path = typeof(PinnedProjectToolchain).Assembly
			.GetCustomAttributes<AssemblyMetadataAttribute>()
			.SingleOrDefault(attribute => attribute.Key == ProjectPathMetadataKey)?.Value;
		if (string.IsNullOrEmpty(path))
		{
			throw new InvalidOperationException(
				$"The benchmark assembly carries no '{ProjectPathMetadataKey}' metadata; rebuild KatLang.Benchmarks.csproj.");
		}

		var project = new FileInfo(path);
		if (!project.Exists)
		{
			throw new InvalidOperationException(
				$"The benchmark project this assembly was built from no longer exists: {project.FullName}. Rebuild from the current checkout.");
		}

		return project;
	}

	private sealed class PinnedProjectGenerator(string targetFrameworkMoniker, FileInfo project)
		: CsProjGenerator(targetFrameworkMoniker, cliPath: null!, packagesPath: null!, runtimeFrameworkVersion: null!)
	{
		protected override FileInfo GetProjectFilePath(Type benchmarkTarget, ILogger logger) => project;
	}
}
