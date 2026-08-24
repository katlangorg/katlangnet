using System.Collections.Frozen;

namespace KatLang;

/// <summary>
/// One named host-provided operation callable from KatLang programs.
///
/// <para>A host operation is the supported way for an embedding host to expose a .NET
/// computation — including a genuinely asynchronous one — to KatLang evaluation without
/// changing the language: the operation's name becomes an ambient callable exactly like
/// the built-in <c>Math</c> members, resolved through the ordinary prelude fallback, so
/// a program simply writes <c>Data</c> or <c>Fetch(id)</c>. Program-defined properties
/// shadow host operations by the ordinary ownership-first lookup rule, and no KatLang
/// syntax is added or changed.</para>
///
/// <para><b>Invocation contract.</b> The implementation delegate receives one evaluated
/// KatLang <see cref="Result"/> per declared parameter, in declaration order (an empty
/// list for a zero-parameter operation), plus the run's evaluation cancellation token
/// (<see cref="RunOptions.EvaluationCancellationToken"/> or the token passed to the
/// evaluator entry point). It must return a non-null <see cref="Result"/>; construct
/// values with the public constructors (<see cref="Result.Atom"/>,
/// <see cref="Result.Str"/>, <see cref="Result.SequenceValue"/>,
/// <see cref="Result.ListValue"/>). The delegate is invoked exactly once per KatLang-level
/// evaluation of the operation — a suspension and resumption of an asynchronous operation
/// never replays it — and a zero-parameter operation accessed property-style
/// (<c>Data</c>) participates in the ordinary per-run zero-argument property cache, while
/// an explicit call (<c>Data()</c>) bypasses that property's cache entry, exactly like
/// any other KatLang property.</para>
///
/// <para><b>Exception contract.</b> Exceptions thrown by the delegate (or a faulted
/// awaitable returned by an asynchronous operation) propagate to the host unchanged —
/// they are host exceptions, never converted into KatLang diagnostics or absorbed into
/// values. An <see cref="OperationCanceledException"/> carrying the supplied token is the
/// ordinary cooperative-cancellation outcome. To produce a KatLang-visible failure,
/// return a value encoding it instead of throwing.</para>
///
/// <para><b>Synchronous vs asynchronous.</b> A synchronous operation
/// (<see cref="Create"/>) works on every entry point, synchronous and asynchronous, and
/// never causes an asynchronous entry point to leave its synchronous fast path. An
/// asynchronous operation (<see cref="CreateAsync"/>) is usable only through the
/// asynchronous entry points (<see cref="KatLangEngine.RunAsync"/>,
/// <c>Evaluator.RunAsync</c>, and the async engine conveniences); when its
/// <see cref="ValueTask{TResult}"/> completes asynchronously the whole evaluation
/// genuinely suspends — no thread is blocked — and resumes at the same point when the
/// operation completes. The delegate must never block the calling thread to simulate
/// synchronous completion. Configuring an asynchronous operation on a synchronous entry
/// point is rejected with <see cref="InvalidOperationException"/> before any evaluation.</para>
///
/// <para>Instances are immutable and safe to share across concurrent runs. Like the
/// zero-argument property cache seam and <see cref="RunOptions.DownloadCode"/>, the
/// delegate is host code running inside an evaluation: it may reentrantly start nested
/// KatLang runs, and after a genuine suspension the continuation may resume on a
/// different thread than the one that started the run.</para>
/// </summary>
public sealed class HostOperation
{
    private HostOperation(
        string name,
        IReadOnlyList<string> parameterNames,
        Func<IReadOnlyList<Result>, CancellationToken, Result>? synchronousImplementation,
        Func<IReadOnlyList<Result>, CancellationToken, ValueTask<Result>>? asynchronousImplementation)
    {
        Name = name;
        ParameterNames = parameterNames;
        SynchronousImplementation = synchronousImplementation;
        AsynchronousImplementation = asynchronousImplementation;
    }

    /// <summary>The KatLang name programs use to reference this operation.</summary>
    public string Name { get; }

    /// <summary>
    /// Declared parameter names, in call order. An empty list makes the operation a
    /// zero-parameter property-like value. The names appear in diagnostics and callable
    /// metadata; calls bind arguments positionally like every KatLang call.
    /// </summary>
    public IReadOnlyList<string> ParameterNames { get; }

    /// <summary>
    /// True when this operation was created with <see cref="CreateAsync"/> and may
    /// complete asynchronously. Asynchronous operations require the asynchronous entry
    /// points and route the run through the evaluator's async twin path.
    /// </summary>
    public bool IsAsynchronous => AsynchronousImplementation is not null;

    internal Func<IReadOnlyList<Result>, CancellationToken, Result>? SynchronousImplementation { get; }

    internal Func<IReadOnlyList<Result>, CancellationToken, ValueTask<Result>>? AsynchronousImplementation { get; }

    /// <summary>
    /// The internal native-dispatch name of this operation's synthesized wrapper body.
    /// The <c>host:</c> prefix contains a character no KatLang identifier can contain,
    /// so a host operation can never collide with a built-in native function name
    /// (for example a host operation named <c>Abs</c> never shadows <c>Math.Abs</c>'s
    /// native dispatch).
    /// </summary>
    internal string NativeName => HostOperations.NativeNamePrefix + Name;

    /// <summary>
    /// Creates a SYNCHRONOUS host operation. See the class documentation for the
    /// invocation and exception contracts.
    /// </summary>
    /// <param name="name">Operation name: a valid KatLang identifier (not a language
    /// keyword) that is not a reserved prelude name (a builtin name, <c>Math</c>,
    /// <c>load</c>, or a Math member alias such as <c>pi</c> or <c>sin</c>).</param>
    /// <param name="implementation">Receives the evaluated argument values (one per
    /// declared parameter, in order) and the run's evaluation cancellation token, and
    /// returns the operation's non-null KatLang value.</param>
    /// <param name="parameterNames">Declared parameter names; empty for a
    /// zero-parameter, property-like operation.</param>
    public static HostOperation Create(
        string name,
        Func<IReadOnlyList<Result>, CancellationToken, Result> implementation,
        params string[] parameterNames)
    {
        ArgumentNullException.ThrowIfNull(implementation);
        var validatedParameterNames = ValidateSignature(name, parameterNames);
        return new HostOperation(name, validatedParameterNames, implementation, asynchronousImplementation: null);
    }

    /// <summary>
    /// Creates an ASYNCHRONOUS host operation. The returned <see cref="ValueTask{TResult}"/>
    /// may complete asynchronously; an incomplete one genuinely suspends the evaluation
    /// and resumes it — without replaying any evaluated work — when the operation
    /// completes. See the class documentation for the invocation and exception contracts.
    /// </summary>
    /// <param name="name">Operation name: a valid KatLang identifier (not a language
    /// keyword) that is not a reserved prelude name (a builtin name, <c>Math</c>,
    /// <c>load</c>, or a Math member alias such as <c>pi</c> or <c>sin</c>).</param>
    /// <param name="implementation">Receives the evaluated argument values (one per
    /// declared parameter, in order) and the run's evaluation cancellation token, and
    /// returns the operation's non-null KatLang value. It must not block the calling
    /// thread.</param>
    /// <param name="parameterNames">Declared parameter names; empty for a
    /// zero-parameter, property-like operation.</param>
    public static HostOperation CreateAsync(
        string name,
        Func<IReadOnlyList<Result>, CancellationToken, ValueTask<Result>> implementation,
        params string[] parameterNames)
    {
        ArgumentNullException.ThrowIfNull(implementation);
        var validatedParameterNames = ValidateSignature(name, parameterNames);
        return new HostOperation(name, validatedParameterNames, synchronousImplementation: null, implementation);
    }

    private static IReadOnlyList<string> ValidateSignature(string name, string[] parameterNames)
    {
        ArgumentNullException.ThrowIfNull(name);
        ArgumentNullException.ThrowIfNull(parameterNames);

        if (!Lexer.IsValidIdentifier(name))
        {
            throw new ArgumentException(
                $"Host operation name '{name}' is not a valid KatLang identifier " +
                "(a non-keyword starting with a letter or '_', followed by letters, digits, or '_').",
                nameof(name));
        }

        if (HostOperations.ReservedPreludeNames.Contains(name))
        {
            throw new ArgumentException(
                $"Host operation name '{name}' is reserved by the KatLang prelude " +
                "(builtin names, 'Math', 'load', and the Math member aliases such as " +
                "'pi' and 'sin' cannot be redefined by host operations).",
                nameof(name));
        }

        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var parameterName in parameterNames)
        {
            if (parameterName is null || !Lexer.IsValidIdentifier(parameterName))
            {
                throw new ArgumentException(
                    $"Host operation '{name}' declares parameter name '{parameterName}', " +
                    "which is not a valid KatLang identifier.",
                    nameof(parameterNames));
            }

            if (!seen.Add(parameterName))
            {
                throw new ArgumentException(
                    $"Host operation '{name}' declares duplicate parameter name '{parameterName}'.",
                    nameof(parameterNames));
            }
        }

        return Array.AsReadOnly(parameterNames.ToArray());
    }
}

/// <summary>
/// A validated, immutable set of <see cref="HostOperation"/>s configured for KatLang runs
/// via <see cref="RunOptions.HostOperations"/> or the <c>Evaluator.Run</c>/<c>RunAsync</c>
/// host-operation overloads.
///
/// <para>The set is pure configuration, exactly like <see cref="EvaluationLimits"/>:
/// immutable, safe to share across concurrent and sequential runs, and holding no
/// per-run state. Sharing one instance across runs also keeps the synthesized ambient
/// declarations reference-identical, so per-run caching behaves consistently across
/// those runs; all run state still lives in run-scoped evaluator structures, so nothing
/// ever leaks between runs through this object.</para>
///
/// <para>Each operation is exposed to programs as an ambient prelude member — the same
/// mechanism that provides <c>Math</c> — so operation names resolve during front-end
/// parameter detection (a referenced operation name does not become an implicit
/// parameter) and during evaluation, and program-defined properties shadow them by the
/// ordinary ownership-first lookup rule.</para>
/// </summary>
public sealed class HostOperations
{
    /// <summary>
    /// Prefix of the internal native-dispatch names of host-operation wrapper bodies.
    /// Contains <c>':'</c>, which no KatLang identifier can contain, so host dispatch
    /// names can never collide with built-in native function names.
    /// </summary>
    internal const string NativeNamePrefix = "host:";

    /// <summary>
    /// Names host operations may not use: redefining a builtin, <c>Math</c>,
    /// <c>load</c>, or a Math member alias (<c>pi</c>, <c>sin</c>, ...) would
    /// make one prelude declare the same name twice. Derived from the semantic
    /// prelude's actual property inventory, so new prelude vocabulary is
    /// reserved automatically.
    /// </summary>
    internal static readonly IReadOnlySet<string> ReservedPreludeNames =
        BuiltinRegistry.CreateSemanticPreludeAlgorithm().Properties
            .Select(static property => property.Name)
            .ToFrozenSet(StringComparer.Ordinal);

    private readonly Dictionary<string, HostOperation> _operationsByNativeName;

    private HostOperations(IReadOnlyList<HostOperation> operations)
    {
        Operations = Array.AsReadOnly(operations.ToArray());
        _operationsByNativeName = Operations.ToDictionary(
            static operation => operation.NativeName,
            StringComparer.Ordinal);
        ContainsAsynchronousOperations = Operations.Any(static operation => operation.IsAsynchronous);

        // Built once per (immutable) set and reused by every run configured with it:
        // the runtime prelude is what evaluation resolves names against, and the
        // signature-only semantic prelude is what front-end parameter detection
        // resolves against — the same name-level split the built-in Math module uses.
        RuntimePreludeAlgorithm = CreateExtendedPrelude(
            BuiltinRegistry.CreateRuntimePreludeAlgorithm(),
            Operations,
            static operation => new Expr.NativeCall(operation.NativeName, operation.ParameterNames));
        SemanticPreludeAlgorithm = CreateExtendedPrelude(
            BuiltinRegistry.CreateSemanticPreludeAlgorithm(),
            Operations,
            wrapperBody: null);
    }

    /// <summary>The configured operations, in registration order.</summary>
    public IReadOnlyList<HostOperation> Operations { get; }

    /// <summary>
    /// True when any configured operation is asynchronous. Such a configuration
    /// requires the asynchronous entry points (<see cref="KatLangEngine.RunAsync"/>,
    /// <c>Evaluator.RunAsync</c>, and the async engine conveniences); synchronous entry
    /// points reject it with <see cref="InvalidOperationException"/> before evaluating
    /// anything.
    /// </summary>
    public bool ContainsAsynchronousOperations { get; }

    /// <summary>
    /// The runtime prelude with the host operations appended as ambient members.
    /// Reference-stable for the lifetime of this set, so runs sharing the set share
    /// declaration identities.
    /// </summary>
    internal Algorithm.User RuntimePreludeAlgorithm { get; }

    /// <summary>
    /// The signature-only semantic prelude (parameter detection / front-end lookup)
    /// with the host operations appended, mirroring the runtime prelude name-for-name.
    /// </summary>
    internal Algorithm.User SemanticPreludeAlgorithm { get; }

    /// <summary>
    /// Creates a validated set. Throws <see cref="ArgumentException"/> when two
    /// operations share a name; each operation's own name and parameter names were
    /// already validated by its factory.
    /// </summary>
    public static HostOperations Create(params HostOperation[] operations)
    {
        ArgumentNullException.ThrowIfNull(operations);

        var snapshot = new List<HostOperation>(operations.Length);
        var names = new HashSet<string>(StringComparer.Ordinal);
        foreach (var operation in operations)
        {
            ArgumentNullException.ThrowIfNull(operation, nameof(operations));
            if (!names.Add(operation.Name))
            {
                throw new ArgumentException(
                    $"Duplicate host operation name '{operation.Name}'.",
                    nameof(operations));
            }

            snapshot.Add(operation);
        }

        return new HostOperations(snapshot);
    }

    internal bool TryGetByNativeName(
        string nativeName,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out HostOperation? operation)
        => _operationsByNativeName.TryGetValue(nativeName, out operation);

    /// <summary>
    /// Appends one wrapper property per operation to a prelude built by
    /// <see cref="BuiltinRegistry"/>. The wrapper is the exact shape of a Math member:
    /// a parentless <see cref="Algorithm.User"/> whose parameters are the operation's
    /// declared parameters and whose only output row is the native-dispatch call
    /// (or no output at all for the signature-only semantic flavor). Wrappers are
    /// synthetic and carry no source spans, so they can never produce semantic sites.
    /// </summary>
    private static Algorithm.User CreateExtendedPrelude(
        Algorithm.User prelude,
        IReadOnlyList<HostOperation> operations,
        Func<HostOperation, Expr>? wrapperBody)
    {
        var properties = new List<Property>(prelude.Properties.Count + operations.Count);
        properties.AddRange(prelude.Properties);
        foreach (var operation in operations)
        {
            properties.Add(new Property(
                operation.Name,
                new Algorithm.User(
                    Parent: null,
                    Parameters: Algorithm.NormalParameters(operation.ParameterNames),
                    Opens: [],
                    Properties: [],
                    Output: wrapperBody is null ? [] : [wrapperBody(operation)]),
                IsPublic: true));
        }

        return prelude with { Properties = properties };
    }
}
