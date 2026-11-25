using System.Diagnostics;
using System.Numerics;
using System.Text;

namespace KatLang;

/// <summary>
/// Code-link format 1 (<c>docs/design/code-link-format.md</c>): a program's link is
/// <c>#1/&lt;payload&gt;</c>, and its payload the digits of one arithmetic-coded stream, each
/// digit a character of base64url (<see cref="Alphabet"/>). The stream holds the
/// number of bytes of the program's WTF-8 form, those bytes with the probabilities of
/// <see cref="CodeLinkModel"/>, and a 12-bit check value. Every step is integer arithmetic, so
/// every implementation of the specification makes the same payload.
///
/// <para>A new format is the owner's decision, never a side effect of another change: it gets
/// the next number, <see cref="CodeLink.Encode"/> writes it, and reading keeps every earlier
/// format so old links keep opening.</para>
/// </summary>
internal static class CodeLinkFormat
{
    /// <summary>The number of this format, which its links carry before their payload.</summary>
    internal const int Number = 1;

    /// <summary>The digits of a payload, by value: base64url (RFC 4648 § 5).</summary>
    internal const string Alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";

    /// <summary>The most bytes a program can have in WTF-8: three for each UTF-16 code unit.</summary>
    internal const int MaxBytes = 3 * CodeLink.MaxSourceLength;

    // The coder's registers hold 30 bits, five digits.
    private const int Top = 0x3FFF_FFFF;
    private const int EvenOdds = 2048;
    private const int CheckBits = 12;
    private const int CheckMask = (1 << CheckBits) - 1;

    // ⌊log₂ MaxBytes⌋: fifteen zeros announce a length of at least 2^15 = 32,768 bytes; sixteen,
    // at least 65,536, more than any program can have (MaxBytes is 60,000).
    internal const int MaxLengthZeros = 15;

    private static readonly uint[] s_crcTable = CreateCrcTable();

    /// <summary>The payload of <paramref name="source"/>, a nonempty program of any length.</summary>
    internal static string Encode(string source) => Stream(Wtf8.Encode(source));

    /// <summary>
    /// The value of the payload character <paramref name="character"/>, or −1 when it is not a
    /// digit.
    /// </summary>
    internal static int DigitOf(char character) => character switch
    {
        >= 'A' and <= 'Z' => character - 'A',
        >= 'a' and <= 'z' => character - 'a' + 26,
        >= '0' and <= '9' => character - '0' + 52,
        '-' => 62,
        '_' => 63,
        _ => -1,
    };

    /// <summary>
    /// Reads the stream of a format-1 payload: <paramref name="payload"/> holds one or more
    /// digits and nothing else. The checks are made in the stream's order, and the
    /// first that fails decides the refusal: the length field (a length over
    /// <see cref="MaxBytes"/> is <see cref="CodeLinkRefusal.SourceTooLong"/>), each byte (one
    /// that is not valid WTF-8 is <see cref="CodeLinkRefusal.Damaged"/>, and more than
    /// <see cref="CodeLink.MaxSourceLength"/> code units are
    /// <see cref="CodeLinkRefusal.SourceTooLong"/>), then the check value. A check mismatch is
    /// <see cref="CodeLinkRefusal.Damaged"/>. At any bit, the reader also gives that refusal
    /// if the coder shifts more times than the payload has digits. Last, the
    /// program's own payload must be <paramref name="payload"/> itself
    /// (<see cref="CodeLinkRefusal.NotCanonical"/>).
    ///
    /// <para>The work is linear in the length the stream announces, which is at most
    /// <see cref="MaxBytes"/>, and reading stops at the first byte that is not valid WTF-8 or
    /// that takes the program past <see cref="CodeLink.MaxSourceLength"/> code units.</para>
    /// </summary>
    internal static CodeLinkDecoding Read(string payload)
    {
        Debug.Assert(payload.Length > 0);
        var reader = new DigitReader(payload);

        var zeros = 0;
        int bit;
        while ((bit = reader.Code(EvenOdds)) == 0)
        {
            if (++zeros > MaxLengthZeros)
                return Refuse(CodeLinkRefusal.SourceTooLong);
        }

        if (bit < 0)
            return Refuse(CodeLinkRefusal.Damaged);

        var length = 1;
        for (var i = 0; i < zeros; i++)
        {
            bit = reader.Code(EvenOdds);
            if (bit < 0)
                return Refuse(CodeLinkRefusal.Damaged);
            length = length * 2 + bit;
        }

        if (length > MaxBytes)
            return Refuse(CodeLinkRefusal.SourceTooLong);

        var model = CodeLinkModel.StartPrimed(length);
        var bytes = new byte[length];
        // A code unit takes at least one byte, and the program is refused as soon as it has more
        // than MaxSourceLength of them (two more at most, from one four-byte sequence).
        var text = new Wtf8.Reader(Math.Min(length, CodeLink.MaxSourceLength) + 2);
        for (var k = 0; k < length; k++)
        {
            var value = 0;
            for (var i = 0; i < 8; i++)
            {
                bit = reader.Code(model.Predict());
                if (bit < 0)
                    return Refuse(CodeLinkRefusal.Damaged);
                model.Update(bit);
                value = (value << 1) | bit;
            }

            bytes[k] = (byte)value;
            if (!text.Push((byte)value))
                return Refuse(CodeLinkRefusal.Damaged);
            if (text.Length > CodeLink.MaxSourceLength)
                return Refuse(CodeLinkRefusal.SourceTooLong);
        }

        if (!text.IsComplete)
            return Refuse(CodeLinkRefusal.Damaged);

        var check = 0;
        for (var i = 0; i < CheckBits; i++)
        {
            bit = reader.Code(EvenOdds);
            if (bit < 0)
                return Refuse(CodeLinkRefusal.Damaged);
            check = (check << 1) | bit;
        }

        if (check != (int)(Crc32(bytes) & CheckMask))
            return Refuse(CodeLinkRefusal.Damaged);

        // WHY ACCEPTANCE IS EXACT: the stream is decoded by the encoder's own steps, so the program
        // read is the one whose payload agrees with this one wherever the decoder looked; what
        // the decoder cannot see (digits it reads as zeros past the end, extra digits, a longer
        // flush, a surrogate pair written as two three-byte sequences) leaves a payload that is
        // not the program's own. One program has one payload, and it is the only one accepted.
        var source = text.ToString();
        if (!string.Equals(Encode(source), payload, StringComparison.Ordinal))
            return Refuse(CodeLinkRefusal.NotCanonical);

        return new CodeLinkDecoding.Program(source);
    }

    /// <summary>CRC-32 (ISO-HDLC: zlib, PNG, Ethernet) of <paramref name="bytes"/>.</summary>
    internal static uint Crc32(ReadOnlySpan<byte> bytes)
    {
        var crc = 0xFFFF_FFFFu;
        foreach (var value in bytes)
            crc = s_crcTable[(crc ^ value) & 0xFF] ^ (crc >> 8);
        return ~crc;
    }

    /// <summary>The payload of the bytes <paramref name="bytes"/>, one or more of them.</summary>
    private static string Stream(byte[] bytes)
    {
        Debug.Assert(bytes.Length > 0);
        var model = CodeLinkModel.StartPrimed(bytes.Length);
        var writer = new DigitWriter(Math.Min(bytes.Length + 16, CodeLink.MaxPayloadLength + 1));

        var length = bytes.Length;
        var zeros = BitOperations.Log2((uint)length);
        for (var i = 0; i < zeros; i++)
            writer.Code(0, EvenOdds);
        for (var i = zeros; i >= 0; i--)
            writer.Code((length >> i) & 1, EvenOdds);

        foreach (var value in bytes)
        {
            for (var i = 7; i >= 0; i--)
            {
                var bit = (value >> i) & 1;
                writer.Code(bit, model.Predict());
                model.Update(bit);
            }
        }

        var check = (int)(Crc32(bytes) & CheckMask);
        for (var i = CheckBits - 1; i >= 0; i--)
            writer.Code((check >> i) & 1, EvenOdds);

        return writer.Finish();
    }

    private static CodeLinkDecoding.Refused Refuse(CodeLinkRefusal reason) => new(reason);

    private static uint[] CreateCrcTable()
    {
        var table = new uint[256];
        for (var n = 0u; n < 256; n++)
        {
            var c = n;
            for (var k = 0; k < 8; k++)
                c = (c & 1) != 0 ? 0xEDB8_8320u ^ (c >> 1) : c >> 1;
            table[n] = c;
        }

        return table;
    }

    /// <summary>
    /// The arithmetic encoder: a carryless binary coder on a 30-bit interval [low, high] that
    /// writes a digit whenever both ends agree on their top six bits, and at the end the
    /// shortest digits whose value, followed by zero digits, lies in the interval.
    /// </summary>
    private sealed class DigitWriter(int capacity)
    {
        private readonly StringBuilder _text = new(capacity);
        private int _low;
        private int _high = Top;

        /// <summary>Codes <paramref name="bit"/>, whose probability of being 1 is <paramref name="probabilityOfOne"/> of 4096.</summary>
        public void Code(int bit, int probabilityOfOne)
        {
            var middle = _low + (int)(((long)(_high - _low) * probabilityOfOne) >> 12);
            if (bit != 0)
                _high = middle;
            else
                _low = middle + 1;

            while ((_low >> 24) == (_high >> 24))
            {
                _text.Append(Alphabet[_high >> 24]);
                _low = (_low << 6) & Top;
                _high = ((_high << 6) & Top) | 63;
            }
        }

        public string Finish()
        {
            for (var digits = 0; digits <= 5; digits++)
            {
                var unit = 1L << (6 * (5 - digits));
                var value = (_low + unit - 1) / unit * unit;
                if (value <= _high)
                {
                    for (var i = 0; i < digits; i++)
                        _text.Append(Alphabet[(int)(value >> (24 - 6 * i)) & 63]);
                    return _text.ToString();
                }
            }

            throw new UnreachableException("Five digits always name a value in the interval.");
        }
    }

    /// <summary>
    /// The arithmetic decoder: the encoder's steps on the payload's digits, read as zeros past
    /// its end. A canonical payload has at least as many digits as the encoder wrote while
    /// coding, so a stream that needs more is refused at once.
    /// </summary>
    private sealed class DigitReader
    {
        private readonly string _payload;
        private readonly int _digitCount;
        private int _next;
        private int _shifts;
        private int _low;
        private int _high = Top;
        private int _value;

        public DigitReader(string payload)
        {
            _payload = payload;
            _digitCount = payload.Length;
            for (var k = 0; k < 5; k++)
                _value = (_value << 6) | ReadDigit();
        }

        /// <summary>The next bit, or −1 when the stream needs more digits than the payload has.</summary>
        public int Code(int probabilityOfOne)
        {
            var middle = _low + (int)(((long)(_high - _low) * probabilityOfOne) >> 12);
            var bit = _value <= middle ? 1 : 0;
            if (bit != 0)
                _high = middle;
            else
                _low = middle + 1;

            while ((_low >> 24) == (_high >> 24))
            {
                if (++_shifts > _digitCount)
                    return -1;
                _low = (_low << 6) & Top;
                _high = ((_high << 6) & Top) | 63;
                _value = ((_value << 6) & Top) | ReadDigit();
            }

            return bit;
        }

        private int ReadDigit() => _next < _payload.Length ? DigitOf(_payload[_next++]) : 0;
    }
}

/// <summary>
/// WTF-8: UTF-8 extended to surrogate code points, so that every UTF-16 string has one byte
/// form. A surrogate pair is one supplementary code point (four bytes); any other surrogate is
/// a code point of its own (three bytes, <c>ED A0..BF xx</c>).
/// </summary>
internal static class Wtf8
{
    /// <summary>The WTF-8 bytes of <paramref name="text"/>.</summary>
    internal static byte[] Encode(string text)
    {
        var count = 0;
        for (var i = 0; i < text.Length; i++)
        {
            int unit = text[i];
            if (unit < 0x80)
                count += 1;
            else if (unit < 0x800)
                count += 2;
            else if (IsPairAt(text, i))
            {
                count += 4;
                i++;
            }
            else
                count += 3;
        }

        var bytes = new byte[count];
        var at = 0;
        for (var i = 0; i < text.Length; i++)
        {
            int codePoint = text[i];
            if (IsPairAt(text, i))
            {
                codePoint = char.ConvertToUtf32(text[i], text[i + 1]);
                i++;
            }

            if (codePoint < 0x80)
            {
                bytes[at++] = (byte)codePoint;
            }
            else if (codePoint < 0x800)
            {
                bytes[at++] = (byte)(0xC0 | (codePoint >> 6));
                bytes[at++] = (byte)(0x80 | (codePoint & 0x3F));
            }
            else if (codePoint < 0x1_0000)
            {
                bytes[at++] = (byte)(0xE0 | (codePoint >> 12));
                bytes[at++] = (byte)(0x80 | ((codePoint >> 6) & 0x3F));
                bytes[at++] = (byte)(0x80 | (codePoint & 0x3F));
            }
            else
            {
                bytes[at++] = (byte)(0xF0 | (codePoint >> 18));
                bytes[at++] = (byte)(0x80 | ((codePoint >> 12) & 0x3F));
                bytes[at++] = (byte)(0x80 | ((codePoint >> 6) & 0x3F));
                bytes[at++] = (byte)(0x80 | (codePoint & 0x3F));
            }
        }

        Debug.Assert(at == count);
        return bytes;
    }

    private static bool IsPairAt(string text, int i)
        => char.IsHighSurrogate(text[i]) && i + 1 < text.Length && char.IsLowSurrogate(text[i + 1]);

    /// <summary>
    /// Reads WTF-8 a byte at a time, strictly: no overlong form, nothing above U+10FFFF, no
    /// stray continuation byte. Surrogate code points are read as single code units; a pair
    /// written as two of them reads as the pair, whose own WTF-8 form is the four-byte one.
    /// </summary>
    internal sealed class Reader(int capacity)
    {
        private readonly char[] _units = new char[capacity];
        private int _length;
        private int _needed;
        private int _codePoint;
        private int _lower = 0x80;
        private int _upper = 0xBF;

        /// <summary>The UTF-16 code units read so far.</summary>
        public int Length => _length;

        /// <summary>Whether no code point is half read.</summary>
        public bool IsComplete => _needed == 0;

        /// <summary>Reads <paramref name="value"/>, and is <c>false</c> when it cannot come next in WTF-8.</summary>
        public bool Push(byte value)
        {
            if (_needed == 0)
            {
                switch (value)
                {
                    case < 0x80:
                        _units[_length++] = (char)value;
                        return true;
                    case >= 0xC2 and <= 0xDF:
                        _needed = 1;
                        _codePoint = value & 0x1F;
                        return true;
                    case >= 0xE0 and <= 0xEF:
                        _needed = 2;
                        _codePoint = value & 0x0F;
                        if (value == 0xE0)
                            _lower = 0xA0;
                        return true;
                    case >= 0xF0 and <= 0xF4:
                        _needed = 3;
                        _codePoint = value & 0x07;
                        if (value == 0xF0)
                            _lower = 0x90;
                        else if (value == 0xF4)
                            _upper = 0x8F;
                        return true;
                    default:
                        return false;
                }
            }

            if (value < _lower || value > _upper)
                return false;

            _lower = 0x80;
            _upper = 0xBF;
            _codePoint = (_codePoint << 6) | (value & 0x3F);
            if (--_needed == 0)
            {
                if (_codePoint < 0x1_0000)
                {
                    _units[_length++] = (char)_codePoint;
                }
                else
                {
                    var offset = _codePoint - 0x1_0000;
                    _units[_length++] = (char)(0xD800 + (offset >> 10));
                    _units[_length++] = (char)(0xDC00 + (offset & 0x3FF));
                }
            }

            return true;
        }

        public override string ToString() => new(_units, 0, _length);
    }
}
