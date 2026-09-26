using System.Diagnostics.CodeAnalysis;

namespace KatLang;

/// <summary>
/// FE-3: the immutable parameter-pattern list implicit lifting stores as an owner's
/// <see cref="Algorithm.User.ParameterPatterns"/> — the SHARED SIGNATURE TEMPLATE of every owner
/// whose lifted signature has the same content, instead of one freshly copied list per owner.
///
/// <para><b>Shape, not declaration.</b> A template holds only immutable signature shape: the
/// ordered pattern records (nested mutable memberships are snapshotted once; immutable capture leaves are shared with the callee that
/// declared them) and facts derived from them. It holds no owner, activation, value, cache entry,
/// host result, random state, or cancellation state. The SEMANTIC parameter identity stays
/// owner-relative — <c>(owner declaration, slot)</c> — exactly as before FE-3, when K owners already
/// held the same lifted capture records in K separate lists: two owners sharing one template are
/// still two declarations (<see cref="Algorithm.Declaration"/>), bind in their own activations, and
/// are never collapsed. Sharing the LIST is sound because a list's identity carries nothing an
/// owner-specific consumer may key on; every memo keyed by a pattern-list instance derives only
/// content facts from it.</para>
///
/// <para><b>Two forms, depth at most one.</b> A FLAT template stores every pattern. A COMPOSED
/// owner signature is an owner-local head (the owner's own patterns, a small delta) followed by
/// one FLAT shared tail template (the lifted signature many owners share): its storage and every
/// fact derived from it cost the head, never the tail. A tail is never itself composed.</para>
///
/// <para><b>No mutation route.</b> Only <see cref="IReadOnlyList{T}"/> is implemented, so a
/// template shared by many owners cannot be changed through any of them (the baseline's per-owner
/// <c>List</c> could be down-cast and mutated). Facts are computed on first use and published
/// atomically; they are pure functions of the immutable content, so concurrent readers of a
/// retained parse result observe the same values.</para>
///
/// <para><b>Lifetime.</b> Templates are created by one resolution run
/// (<see cref="ImplicitSignatureTemplateInterner"/>) and live exactly as long as the elaborated
/// tree that references them; there is no static registry.</para>
/// </summary>
internal sealed class ImplicitSignatureTemplate : IReadOnlyList<ParameterPattern>
{
    private readonly ParameterPattern[] _items;
    private readonly ImplicitSignatureTemplate? _tail;
    private TemplateFacts? _facts;

    private ImplicitSignatureTemplate(ParameterPattern[] items, ImplicitSignatureTemplate? tail)
    {
        System.Diagnostics.Debug.Assert(tail is null || tail._tail is null, "A tail template is always flat.");
        _items = items;
        _tail = tail;
        Count = items.Length + (tail?.Count ?? 0);
    }

    /// <summary>A flat template over a freshly built array whose ownership transfers here.</summary>
    internal static ImplicitSignatureTemplate Flat(ParameterPattern[] items) => new(items, tail: null);

    /// <summary>
    /// An owner signature: <paramref name="head"/> (the owner's own patterns, copied) followed by the
    /// flat shared <paramref name="tail"/>. The caller guarantees the head's capture names are
    /// disjoint from the tail's, so first-occurrence facts compose without a scan of the tail.
    /// </summary>
    internal static ImplicitSignatureTemplate Compose(IReadOnlyList<ParameterPattern> head, ImplicitSignatureTemplate tail)
    {
        if (head.Count == 0)
            return tail;
        // Extending a composed signature copies only its local delta, never its flat tail.
        return tail._tail is { } shared
            ? new([.. head, .. tail._items], shared)
            : new([.. head], tail);
    }

    public int Count { get; }

    /// <summary>The owner-local head of a composed signature (the whole template when flat).</summary>
    internal IReadOnlyList<ParameterPattern> Head => _items;

    /// <summary>The flat shared tail of a composed signature, or null for a flat template.</summary>
    internal ImplicitSignatureTemplate? Tail => _tail;

    /// <summary>True for a composed owner signature (an owner-local head over a shared tail).</summary>
    internal bool IsComposed => _tail is not null;

    public ParameterPattern this[int index]
        => (uint)index < (uint)_items.Length
            ? _items[index]
            : _tail is { } tail
                ? tail[index - _items.Length]
                : throw new ArgumentOutOfRangeException(nameof(index));

    public IEnumerator<ParameterPattern> GetEnumerator()
    {
        foreach (var item in _items)
            yield return item;
        if (_tail is { } tail)
        {
            foreach (var item in tail._items)
                yield return item;
        }
    }

    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();

    /// <summary>The template's content facts, computed once (shared by every owner of the template).</summary>
    internal TemplateFacts Facts
    {
        get
        {
            var facts = Volatile.Read(ref _facts);
            if (facts is not null)
                return facts;
            facts = new TemplateFacts(this);
            return Interlocked.CompareExchange(ref _facts, facts, null) ?? facts;
        }
    }

    /// <summary>
    /// Content facts of one template: the flattened captures and names in order, the name SET,
    /// first-occurrence lookup by name, and the top-level collecting shape. A flat template's
    /// facts cost its width once; a composed signature's facts cost its head and reuse the tail's.
    /// </summary>
    internal sealed class TemplateFacts
    {
        private readonly ParameterPattern[] _headPatterns;
        private readonly ParameterDeclaration[] _headCaptures;
        private readonly Dictionary<string, ParameterDeclaration> _headFirstCapture;
        private readonly TemplateFacts? _tail;

        internal TemplateFacts(ImplicitSignatureTemplate template)
        {
            _headPatterns = template._items;
            _tail = template._tail?.Facts;
            _headCaptures = [.. ParameterPattern.FlattenCaptures(template._items)];
            _headFirstCapture = new Dictionary<string, ParameterDeclaration>(_headCaptures.Length, StringComparer.Ordinal);
            foreach (var capture in _headCaptures)
                _headFirstCapture.TryAdd(capture.Name, capture);
            CaptureCount = _headCaptures.Length + (_tail?.CaptureCount ?? 0);
            var headCollecting = 0;
            foreach (var pattern in template._items)
            {
                if (pattern is CaptureParameterPattern { Kind: ParameterKind.Collecting })
                    headCollecting++;
            }

            TopLevelCollectingCount = headCollecting + (_tail?.TopLevelCollectingCount ?? 0);
            HasEmptyGroup = Array.Exists(_headPatterns, ContainsEmptyGroup) || (_tail?.HasEmptyGroup ?? false);
            HasRecoveryPlaceholder = Array.Exists(_headCaptures, static capture => capture.IsRecoveryPlaceholder)
                || (_tail?.HasRecoveryPlaceholder ?? false);
            Captures = _tail is null ? _headCaptures : new ConcatReadOnlyList<ParameterDeclaration>(_headCaptures, _tail.Captures);
            var headNames = new string[_headCaptures.Length];
            for (var i = 0; i < headNames.Length; i++)
                headNames[i] = _headCaptures[i].Name;
            Names = _tail is null ? headNames : new ConcatReadOnlyList<string>(headNames, _tail.Names);
            NameSet = _tail is null
                ? new NameSetView(_headFirstCapture, tail: null)
                : new NameSetView(_headFirstCapture, _tail.NameSet);
        }

        /// <summary>The number of captures (Lean: <c>(patterns.flatMap captures).length</c>).</summary>
        public int CaptureCount { get; }

        /// <summary>Top-level collecting captures (the binder's movable collector count).</summary>
        public int TopLevelCollectingCount { get; }

        /// <summary>Whether lifting must remove an empty structural group, at any nesting level.</summary>
        public bool HasEmptyGroup { get; }

        private static bool ContainsEmptyGroup(ParameterPattern pattern)
            => pattern is SequenceValueParameterPattern group
                && (group.Items.Count == 0 || group.Items.Any(ContainsEmptyGroup));

        /// <summary>Whether a capture is a parser recovery placeholder (editor metadata displays it as <c>?</c>).</summary>
        public bool HasRecoveryPlaceholder { get; }

        /// <summary>The flattened capture declarations, left to right, duplicates included.</summary>
        public IReadOnlyList<ParameterDeclaration> Captures { get; }

        /// <summary>The flattened capture names, left to right, duplicates included.</summary>
        public IReadOnlyList<string> Names { get; }

        /// <summary>The capture names as a set (read-only; shared by every owner of the template).</summary>
        public IReadOnlySet<string> NameSet { get; }

        /// <summary>The FIRST capture declaring <paramref name="name"/> (first occurrence wins).</summary>
        public bool TryGetFirstCapture(string name, [NotNullWhen(true)] out ParameterDeclaration? capture)
        {
            if (_headFirstCapture.TryGetValue(name, out capture))
                return true;
            if (_tail is not null)
                return _tail.TryGetFirstCapture(name, out capture);
            capture = null;
            return false;
        }

        /// <summary>
        /// The first-occurrence binding kind of each name — the forwarding SOURCE kinds of an owner
        /// whose signature this is (the resolver's <c>BuildSourceBindingKinds</c>), as a read-only view.
        /// </summary>
        public IReadOnlyDictionary<string, ParameterKind> BindingKinds
        {
            get
            {
                var view = Volatile.Read(ref _bindingKinds);
                if (view is not null)
                    return view;
                view = new BindingKindView(this);
                return Interlocked.CompareExchange(ref _bindingKinds, view, null) ?? view;
            }
        }

        private BindingKindView? _bindingKinds;

        /// <summary>
        /// The flat <see cref="CallableParameter"/> list of a signature over this template with the
        /// given parameter source (the signature's <c>Parameters</c>), built once per source and shared
        /// by every owner's signature; a composed signature builds only its head's parameters.
        /// </summary>
        public IReadOnlyList<CallableParameter> CallableParameters(CallableParameterSource source)
        {
            var slots = Volatile.Read(ref _callableParameters);
            if (slots is null)
            {
                slots = new IReadOnlyList<CallableParameter>?[Enum.GetValues<CallableParameterSource>().Length];
                slots = Interlocked.CompareExchange(ref _callableParameters, slots, null) ?? slots;
            }

            var index = (int)source;
            var computed = Volatile.Read(ref slots[index]);
            if (computed is not null)
                return computed;
            var head = CallableSignature.CreateParameters(_headPatterns, source).ToArray();
            computed = _tail is null ? head : new ConcatReadOnlyList<CallableParameter>(head, _tail.CallableParameters(source));
            return Interlocked.CompareExchange(ref slots[index], computed, null) ?? computed;
        }

        private IReadOnlyList<CallableParameter>?[]? _callableParameters;
    }

    /// <summary>
    /// A read-only name set over a head map and an optional (disjoint) tail set. A composed
    /// signature's set exposes its shared <see cref="Tail"/> so a consumer can decide a question
    /// about the tail once for every owner of the template and test only the owner's head.
    /// </summary>
    internal sealed class NameSetView(Dictionary<string, ParameterDeclaration> head, IReadOnlySet<string>? tail) : IReadOnlySet<string>
    {
        /// <summary>The shared tail template's name set of a composed signature, or null for a flat one.</summary>
        public IReadOnlySet<string>? Tail => tail;

        public int Count => head.Count + (tail?.Count ?? 0);

        public bool Contains(string item) => head.ContainsKey(item) || (tail?.Contains(item) ?? false);

        public IEnumerator<string> GetEnumerator()
        {
            foreach (var name in head.Keys)
                yield return name;
            if (tail is not null)
            {
                foreach (var name in tail)
                    yield return name;
            }
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();

        public bool IsProperSubsetOf(IEnumerable<string> other) => ToSet().IsProperSubsetOf(other);
        public bool IsProperSupersetOf(IEnumerable<string> other) => ToSet().IsProperSupersetOf(other);
        public bool IsSubsetOf(IEnumerable<string> other) => ToSet().IsSubsetOf(other);
        public bool IsSupersetOf(IEnumerable<string> other) => ToSet().IsSupersetOf(other);
        public bool Overlaps(IEnumerable<string> other) => other.Any(Contains);
        public bool SetEquals(IEnumerable<string> other) => ToSet().SetEquals(other);

        private HashSet<string> ToSet() => new(this, StringComparer.Ordinal);
    }

    /// <summary>First-occurrence binding kinds of a template, read through its facts.</summary>
    private sealed class BindingKindView(TemplateFacts facts) : IReadOnlyDictionary<string, ParameterKind>
    {
        public ParameterKind this[string key]
            => facts.TryGetFirstCapture(key, out var capture) ? capture.Kind : throw new KeyNotFoundException(key);

        public IEnumerable<string> Keys => facts.NameSet;

        public IEnumerable<ParameterKind> Values => Keys.Select(key => this[key]);

        public int Count => facts.NameSet.Count;

        public bool ContainsKey(string key) => facts.NameSet.Contains(key);

        public bool TryGetValue(string key, out ParameterKind value)
        {
            if (facts.TryGetFirstCapture(key, out var capture))
            {
                value = capture.Kind;
                return true;
            }

            value = default;
            return false;
        }

        public IEnumerator<KeyValuePair<string, ParameterKind>> GetEnumerator()
        {
            foreach (var key in Keys)
                yield return new(key, this[key]);
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }
}

/// <summary>An O(1)-indexed read-only view of <c>head ++ tail</c> (both immutable).</summary>
internal sealed class ConcatReadOnlyList<T>(IReadOnlyList<T> head, IReadOnlyList<T> tail) : IReadOnlyList<T>
{
    public int Count { get; } = head.Count + tail.Count;

    public T this[int index]
        => index < head.Count ? head[index] : tail[index - head.Count];

    public IEnumerator<T> GetEnumerator()
    {
        foreach (var item in head)
            yield return item;
        foreach (var item in tail)
            yield return item;
    }

    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
}

/// <summary>
/// FE-3: the run-local source of shared signature templates for ONE resolution run (created with
/// the run, garbage with it — never static). Flat templates are interned by EXACT content: the
/// ordered sequence of pattern RECORD references, so two derivations of the same lifted signature
/// share one template while two signatures with equal spellings but different declarations (other
/// capture records, other order, other grouping) never do.
/// </summary>
internal sealed class ImplicitSignatureTemplateInterner(FrontEndTraversalObservations? observations)
{
    private readonly Dictionary<ContentKey, ImplicitSignatureTemplate> _flat = new();
    private readonly Dictionary<ContentKey, ImplicitSignatureTemplate?> _liftedTails = new();
    private readonly Dictionary<SequenceValueParameterPattern, SequenceValueParameterPattern> _groups = new(ReferenceEqualityComparer.Instance);

    // Public host patterns retain caller-owned lists. Freeze nested membership once per
    // resolution before a shared template can cache facts about it; preserve record metadata.
    internal ParameterPattern Freeze(ParameterPattern pattern)
    {
        if (pattern is not SequenceValueParameterPattern group)
            return pattern;
        if (!_groups.TryGetValue(group, out var frozen))
        {
            frozen = group with { Items = Array.AsReadOnly(group.Items.Select(Freeze).ToArray()) };
            _groups.Add(group, frozen);
            _groups.Add(frozen, frozen);
        }
        return frozen;
    }

    /// <summary>The flat template with exactly <paramref name="patterns"/>' content (interned).</summary>
    public ImplicitSignatureTemplate InternFlat(IReadOnlyList<ParameterPattern> patterns)
    {
        if (patterns is ImplicitSignatureTemplate { IsComposed: false } flat)
            return flat;
        var items = patterns.Select(Freeze).ToArray();
        var key = new ContentKey(items);
        if (!_flat.TryGetValue(key, out var template))
        {
            template = ImplicitSignatureTemplate.Flat(items);
            _flat.Add(key, template);
            observations?.RecordSignatureTemplateBuilt(items.Length);
        }

        return template;
    }

    /// <summary>
    /// The lifted tail of an ordered dependency list, memoized by the dependencies' pattern-list
    /// REFERENCES (the caller's per-owner inputs are applied afterwards): <paramref name="merge"/>
    /// runs once per distinct dependency sequence, however many owners lift it.
    /// </summary>
    public ImplicitSignatureTemplate? LiftedTail(
        IReadOnlyList<IReadOnlyList<ParameterPattern>> dependencies,
        Func<IReadOnlyList<IReadOnlyList<ParameterPattern>>, IReadOnlyList<ParameterPattern>> merge)
    {
        // A template with unique captures and no empty groups is already the exact
        // first-occurrence merge. Host-built empty groups are removed by that merge.
        // Keep its composed head/tail when another owner forwards that signature.
        if (dependencies.Count == 1 && dependencies[0] is ImplicitSignatureTemplate template
            && template.Facts.CaptureCount == template.Facts.NameSet.Count
            && !template.Facts.HasEmptyGroup)
            return template;
        var key = new ContentKey([.. dependencies]);
        if (!_liftedTails.TryGetValue(key, out var tail))
        {
            var merged = merge(dependencies);
            tail = merged.Count == 0 ? null : InternFlat(merged);
            _liftedTails.Add(key, tail);
        }

        return tail;
    }

    /// <summary>Exact content key: an ordered sequence of references, compared by reference.</summary>
    private readonly struct ContentKey : IEquatable<ContentKey>
    {
        private readonly object[] _items;
        private readonly int _hash;

        public ContentKey(object[] items)
        {
            _items = items;
            var hash = new HashCode();
            foreach (var item in items)
                hash.Add(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(item));
            _hash = hash.ToHashCode();
        }

        public bool Equals(ContentKey other)
        {
            if (_hash != other._hash || _items.Length != other._items.Length)
                return false;
            for (var i = 0; i < _items.Length; i++)
            {
                if (!ReferenceEquals(_items[i], other._items[i]))
                    return false;
            }

            return true;
        }

        public override bool Equals(object? obj) => obj is ContentKey other && Equals(other);

        public override int GetHashCode() => _hash;
    }
}
