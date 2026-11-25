namespace KatLang;

/// <summary>
/// The predictor of code-link format 1 (<c>docs/design/code-link-format.md</c> § The model): it
/// gives the probability that the next bit of a program's bytes is 1, and learns from each bit.
/// It mixes seven context models (the bytes before, up to six of them, and the current word) and
/// a match model in the logistic domain, and it starts from the state that reading the frozen
/// primer (<c>code-link-primer-1.txt</c>) leaves, so a short program is cheap from its first
/// byte.
///
/// <para>Every step is integer arithmetic with wrapping unsigned 32-bit hashing, and every
/// constant here is part of format 1: changing any of them, or the primer, changes every link,
/// so a change is a NEW format, made only by owner decision, never as part of another change.
/// The fixtures in <c>dotnet/tests/KatLang.Tests/CodeLinks/Fixtures/</c> pin the results.</para>
///
/// <para>An instance is single-threaded state. The primed state is built once per process and
/// never changes; each encoding or decoding works on its own copy
/// (<see cref="StartPrimed"/>).</para>
/// </summary>
internal sealed class CodeLinkModel
{
    /// <summary>The manifest name of the embedded primer of format 1.</summary>
    internal const string PrimerResourceName = "KatLang.CodeLinks.code-link-primer-1.txt";

    private const int TableBits = 17;
    private const int ContextCount = 7;
    private const int InputCount = ContextCount + 2;
    private const int WeightSets = 6 * 8;
    private const int MatchBits = 16;
    private const int MatchContexts = 64;
    private const int CountLimit = 60;
    private const int MatchCountLimit = 255;
    private const int MinimumMatch = 5;
    private const int MatchVerifyLimit = 32;
    private const int MaxMatchLength = 65_535;
    private const int InitialWeight = 19_661;
    private const int InitialProbability = 32_768;
    private const int InitialMatchProbability = 49_152;
    private const int RateShift = 10;
    private const int WeightLimit = 1 << 22;
    private const int Bias = 256;

    private static readonly int[] s_rates = CreateRates();

    // The points of SquashPoints. Squash reads them once per coded bit, so they are an array: in
    // debuggable (Debug-build) code the JIT calls RuntimeHelpers.CreateSpan instead of expanding
    // it, and a ReadOnlySpan property over constant data then allocates on every read, 72 bytes
    // per bit. Initialized before s_stretch, which squashes every stretch value.
    private static readonly short[] s_squashPoints =
    [
        1, 2, 2, 3, 4, 5, 6, 8, 10, 13, 17, 21, 27, 35, 45, 58, 74, 94, 120, 153, 194, 246, 311, 391,
        488, 606, 747, 912, 1102, 1314, 1546, 1793, 2048, 2303, 2550, 2782, 2994, 3184, 3349, 3490,
        3608, 3705, 3785, 3850, 3902, 3943, 3976, 4002, 4022, 4038, 4051, 4061, 4069, 4075, 4079,
        4083, 4086, 4088, 4090, 4091, 4092, 4093, 4094, 4094, 4095,
    ];

    private static readonly short[] s_stretch = CreateStretch();
    private static readonly Lazy<byte[]> s_primer = new(ReadPrimer);
    private static readonly Lazy<CodeLinkModel> s_primed = new(CreatePrimed);

    private readonly ushort[] _probabilities;
    private readonly byte[] _counts;
    private readonly int[] _weights;
    private readonly ushort[] _matchProbabilities;
    private readonly byte[] _matchCounts;
    private readonly int[] _matchTable;
    private readonly uint[] _contexts = new uint[ContextCount];
    private readonly int[] _slots = new int[ContextCount];
    private readonly int[] _inputs = new int[InputCount];
    private byte[] _history;
    private int _position;
    private int _partial = 1;
    private int _bitIndex;
    private uint _word;
    private int _matchPointer;
    private int _matchLength;
    private int _expectedBit = -1;
    private int _matchContext;
    private int _weightSet;
    private int _probability;

    private CodeLinkModel(int capacity)
    {
        _probabilities = new ushort[ContextCount << TableBits];
        _probabilities.AsSpan().Fill(InitialProbability);
        _counts = new byte[ContextCount << TableBits];
        _weights = new int[WeightSets * InputCount];
        _weights.AsSpan().Fill(InitialWeight);
        _matchProbabilities = new ushort[MatchContexts];
        _matchProbabilities.AsSpan().Fill(InitialMatchProbability);
        _matchCounts = new byte[MatchContexts];
        _matchTable = new int[1 << MatchBits];
        _history = new byte[Math.Max(capacity, 16)];
        ComputeContexts();
    }

    private CodeLinkModel(CodeLinkModel state, int capacity)
    {
        _probabilities = (ushort[])state._probabilities.Clone();
        _counts = (byte[])state._counts.Clone();
        _weights = (int[])state._weights.Clone();
        _matchProbabilities = (ushort[])state._matchProbabilities.Clone();
        _matchCounts = (byte[])state._matchCounts.Clone();
        _matchTable = (int[])state._matchTable.Clone();
        state._contexts.CopyTo(_contexts, 0);
        _history = new byte[state._position + Math.Max(capacity, 16)];
        state._history.AsSpan(0, state._position).CopyTo(_history);
        _position = state._position;
        _partial = state._partial;
        _bitIndex = state._bitIndex;
        _word = state._word;
        _matchPointer = state._matchPointer;
        _matchLength = state._matchLength;
    }

    /// <summary>The bytes of the frozen primer of format 1.</summary>
    internal static ReadOnlySpan<byte> Primer => s_primer.Value;

    /// <summary>
    /// A model in the primed state, for one encoding or decoding of about
    /// <paramref name="capacity"/> bytes: a copy of the process-wide primed state, which
    /// nothing ever changes.
    /// </summary>
    internal static CodeLinkModel StartPrimed(int capacity) => new(s_primed.Value, capacity);

    /// <summary>The probability that the next bit is 1, in 1..4095 of 4096.</summary>
    internal int Predict()
    {
        var partial = unchecked((uint)_partial * 0x27D4EB2Fu);
        var maxOrder = 0;
        for (var i = 0; i < ContextCount; i++)
        {
            var slot = (i << TableBits) | (int)(Mix(_contexts[i] ^ partial) >> (32 - TableBits));
            _slots[i] = slot;
            _inputs[i] = s_stretch[_probabilities[slot] >> 4];
            if (i is >= 1 and <= 5 && _counts[slot] > 0)
                maxOrder = i;
        }

        _expectedBit = -1;
        _inputs[ContextCount] = 0;
        if (_matchLength > 0)
        {
            int expected = _history[_matchPointer];
            if (((expected | 256) >> (8 - _bitIndex)) == _partial)
            {
                _expectedBit = (expected >> (7 - _bitIndex)) & 1;
                _matchContext = Math.Min(_matchLength, MatchContexts - 1);
                int stretch = s_stretch[_matchProbabilities[_matchContext] >> 4];
                _inputs[ContextCount] = _expectedBit != 0 ? stretch : -stretch;
            }
            else
            {
                _matchLength = 0;
            }
        }

        _inputs[ContextCount + 1] = Bias;
        _weightSet = (maxOrder * 8 + _bitIndex) * InputCount;
        long dot = 0;
        for (var i = 0; i < InputCount; i++)
            dot += (long)_weights[_weightSet + i] * _inputs[i];

        _probability = Squash((int)(dot >> 16));
        return _probability;
    }

    /// <summary>Learns the bit <paramref name="bit"/> (0 or 1) that followed the last <see cref="Predict"/>.</summary>
    internal void Update(int bit)
    {
        var error = (bit << 12) - _probability;
        for (var i = 0; i < InputCount; i++)
        {
            var weight = _weights[_weightSet + i] + ((_inputs[i] * error) >> RateShift);
            _weights[_weightSet + i] = Math.Clamp(weight, -WeightLimit, WeightLimit);
        }

        var target = bit != 0 ? 65_535 : 0;
        for (var i = 0; i < ContextCount; i++)
        {
            var slot = _slots[i];
            int count = _counts[slot];
            int probability = _probabilities[slot];
            _probabilities[slot] = (ushort)(probability + (((target - probability) * s_rates[count]) >> 15));
            if (count < CountLimit)
                _counts[slot] = (byte)(count + 1);
        }

        if (_expectedBit >= 0)
        {
            var hit = bit == _expectedBit;
            int count = _matchCounts[_matchContext];
            int probability = _matchProbabilities[_matchContext];
            _matchProbabilities[_matchContext] = (ushort)(probability + ((((hit ? 65_535 : 0) - probability) * s_rates[count]) >> 15));
            if (count < MatchCountLimit)
                _matchCounts[_matchContext] = (byte)(count + 1);
            if (!hit)
                _matchLength = 0;
        }

        _partial = (_partial << 1) | bit;
        if (++_bitIndex == 8)
            EndByte((byte)(_partial & 0xFF));
    }

    /// <summary>
    /// The logistic function on the stretch domain (ln(p / (1 − p)) × 256, −2047..2047) as a
    /// probability in 1..4095 of 4096: linear interpolation between the 65 points of
    /// <see cref="SquashPoints"/>.
    /// </summary>
    internal static int Squash(int stretch)
    {
        var d = Math.Clamp(stretch, -2047, 2047) + 2048;
        var points = s_squashPoints;
        var p = (points[d >> 6] * (64 - (d & 63)) + points[(d >> 6) + 1] * (d & 63) + 32) >> 6;
        return Math.Clamp(p, 1, 4095);
    }

    /// <summary>The inverse of <see cref="Squash"/> for a 12-bit probability.</summary>
    internal static int Stretch(int probability) => s_stretch[probability];

    /// <summary>
    /// <c>round(4096 / (1 + e^(−(i − 32) / 4)))</c> clamped to 1..4095, for i = 0..64: the
    /// logistic function at stretch 64 (i − 32). Written out, not computed, because a
    /// platform's <c>exp</c> may round differently.
    /// </summary>
    internal static ReadOnlySpan<short> SquashPoints => s_squashPoints;

    private void EndByte(byte value)
    {
        if (_position == _history.Length)
            Array.Resize(ref _history, _history.Length * 2);

        _history[_position++] = value;
        _partial = 1;
        _bitIndex = 0;

        if (_matchLength > 0)
        {
            _matchPointer++;
            if (_matchLength < MaxMatchLength)
                _matchLength++;
        }

        if (_position >= MinimumMatch)
        {
            uint hash = 0;
            for (var k = 1; k <= MinimumMatch; k++)
                hash = Step(hash, _history[_position - k], 16 + k);

            var entry = (int)(hash >> (32 - MatchBits));
            if (_matchLength == 0)
            {
                var candidate = _matchTable[entry];
                if (candidate > 0)
                {
                    var length = 0;
                    while (length < MatchVerifyLimit
                        && candidate - 1 - length >= 0
                        && _history[candidate - 1 - length] == _history[_position - 1 - length])
                    {
                        length++;
                    }

                    if (length >= MinimumMatch)
                    {
                        _matchLength = length;
                        _matchPointer = candidate;
                    }
                }
            }

            _matchTable[entry] = _position;
        }

        var isWordByte = value is (>= (byte)'0' and <= (byte)'9') or (>= (byte)'A' and <= (byte)'Z')
            or (>= (byte)'a' and <= (byte)'z') or (byte)'_' or >= 0x80;
        _word = isWordByte ? unchecked(((_word ^ value) * 0x01000193u) | 1u) : 0u;
        ComputeContexts();
    }

    private void ComputeContexts()
    {
        _contexts[0] = 0;
        var hash = Step(0, Back(1), 1);
        _contexts[1] = hash;
        hash = Step(hash, Back(2), 2);
        _contexts[2] = hash;
        hash = Step(hash, Back(3), 3);
        _contexts[3] = hash;
        hash = Step(hash, Back(4), 4);
        _contexts[4] = hash;
        _contexts[5] = Step(Step(hash, Back(5), 5), Back(6), 6);
        _contexts[6] = _word == 0 ? Step(0x7777, Back(1), 7) : Step(_word, 0, 8);
    }

    private int Back(int distance) => _position >= distance ? _history[_position - distance] : 0;

    private void Train(ReadOnlySpan<byte> bytes)
    {
        foreach (var value in bytes)
        {
            for (var i = 7; i >= 0; i--)
            {
                Predict();
                Update((value >> i) & 1);
            }
        }
    }

    /// <summary>The MurmurHash3 32-bit finalizer.</summary>
    private static uint Mix(uint x)
    {
        unchecked
        {
            x ^= x >> 16;
            x *= 0x85EBCA6Bu;
            x ^= x >> 13;
            x *= 0xC2B2AE35u;
            x ^= x >> 16;
            return x;
        }
    }

    private static uint Step(uint hash, int value, int position)
        => Mix(unchecked(hash + (uint)(value + 1) * 0x9E3779B1u + (uint)position * 1_048_576u));

    /// <summary>The adaptation rate of a count n: 65536 / (2n + 3), applied as a 15-bit fraction.</summary>
    private static int[] CreateRates()
    {
        var rates = new int[MatchCountLimit + 1];
        for (var n = 0; n < rates.Length; n++)
            rates[n] = 65_536 / (2 * n + 3);
        return rates;
    }

    private static short[] CreateStretch()
    {
        var table = new short[4096];
        var p = 0;
        for (var d = -2047; d <= 2047; d++)
        {
            var value = Squash(d);
            while (p <= value)
                table[p++] = (short)d;
        }

        while (p < table.Length)
            table[p++] = 2047;
        return table;
    }

    private static byte[] ReadPrimer()
    {
        using var stream = typeof(CodeLinkModel).Assembly.GetManifestResourceStream(PrimerResourceName)
            ?? throw new InvalidOperationException($"The KatLang assembly has no embedded resource '{PrimerResourceName}'.");
        var bytes = new byte[stream.Length];
        stream.ReadExactly(bytes);
        return bytes;
    }

    private static CodeLinkModel CreatePrimed()
    {
        var primer = s_primer.Value;
        var model = new CodeLinkModel(primer.Length);
        model.Train(primer);
        return model;
    }
}
