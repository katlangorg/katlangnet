// The output format, and the order in which this encoder emits it, are lz-string 1.5.0's
// (https://github.com/pieroxy/lz-string), used under the MIT License:
//
//   MIT License
//
//   Copyright (c) 2013 pieroxy
//
//   Permission is hereby granted, free of charge, to any person obtaining a copy
//   of this software and associated documentation files (the "Software"), to deal
//   in the Software without restriction, including without limitation the rights
//   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//   copies of the Software, and to permit persons to whom the Software is
//   furnished to do so, subject to the following conditions:
//
//   The above copyright notice and this permission notice shall be included in all
//   copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
//   SOFTWARE.

using System.Text;

namespace KatLang.CLI;

/// <summary>
/// lz-string 1.5.0's <c>compressToEncodedURIComponent</c>, the encoding of a KatLang code link's
/// payload: its <c>_compress</c> with 6 bits per character over the alphabet
/// <c>A–Z a–z 0–9 + - $</c>, producing exactly the characters the JavaScript does for every
/// string. The reference is the copy katlang.org serves, katlangweb's
/// <c>KatLangWeb/wwwroot/lib/lz-string/1.5.0/lz-string.js</c>; the tests pin this port to
/// payloads that copy produced.
///
/// <para>The input is a sequence of UTF-16 code units, as a JavaScript string is, and nothing in
/// it is interpreted: surrogates, unpaired or not, are code units like any other.</para>
///
/// <para><c>_compress</c> is LZW over a dictionary keyed by strings, compared code unit by code
/// unit (ordinally), as JavaScript property keys are. Every key it adds is <c>w + c</c>: the
/// phrase <c>w</c>, already a key, followed by one code unit <c>c</c>. A key is therefore
/// identified by its prefix's code and its last code unit, which is how this port keys it, so
/// each code unit costs one or two hash lookups and nothing is concatenated or copied: linear
/// time and memory, where string keys cost the length of the current phrase per code unit. The
/// two dictionaries agree key for key, with the one exception JavaScript itself makes (see
/// <see cref="UnstorableKey"/>).</para>
/// </summary>
internal static class LzString
{
    /// <summary><c>keyStrUriSafe</c>: the character of each 6-bit value.</summary>
    private const string UriSafeAlphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+-$";

    private const int BitsPerChar = 6;

    /// <summary>The reserved code before a code unit below 256, written in 8 bits.</summary>
    private const int CharacterIn8Bits = 0;

    /// <summary>The reserved code before a code unit of 256 or above, written in 16 bits.</summary>
    private const int CharacterIn16Bits = 1;

    /// <summary>The reserved code that ends the stream.</summary>
    private const int EndOfStream = 2;

    /// <summary>
    /// The one phrase <c>_compress</c> numbers but never stores. Its dictionary is a plain
    /// JavaScript object, and <c>context_dictionary["__proto__"] = context_dictSize++</c> assigns
    /// the object's prototype instead of adding a key: the setter ignores a number, so the code
    /// is used up (<c>context_dictSize</c> still advances) and <c>"__proto__"</c> never becomes a
    /// key. A source that repeats <c>__proto__</c> therefore keeps emitting it as
    /// <c>"__proto_"</c> and <c>"_"</c>. The decoder numbers the same entry and is never sent it,
    /// so the payload still decodes; this encoder reproduces the gap, or katlang.org's check that
    /// a payload re-encodes to itself would refuse its links.
    /// </summary>
    private const string UnstorableKey = "__proto__";

    /// <summary>
    /// The longest input encoded. The bound keeps every code, and the bit widths derived from
    /// them, far inside 32-bit arithmetic (as in JavaScript, whose bitwise operators work on
    /// 32-bit integers); a code link carries at most <see cref="CodeLink.MaxSourceLength"/>
    /// code units.
    /// </summary>
    internal const int MaxInputLength = 1 << 24;

    /// <summary>
    /// <c>LZString.compressToEncodedURIComponent(input)</c>: <c>"Q"</c> for the empty string,
    /// otherwise the input's payload, characters from <c>A–Z a–z 0–9 + -</c> (the alphabet's
    /// <c>$</c> is the 6-bit value 64 and never occurs).
    /// </summary>
    public static string CompressToEncodedUriComponent(string input)
    {
        ArgumentNullException.ThrowIfNull(input);
        ArgumentOutOfRangeException.ThrowIfGreaterThan(input.Length, MaxInputLength);

        return new Compressor(input).Compress();
    }

    /// <summary>
    /// One run of <c>_compress</c>. The field names follow its <c>context_</c> variables, and its
    /// steps keep their order: the order decides when the code width grows.
    /// </summary>
    private sealed class Compressor(string input)
    {
        /// <summary>
        /// <c>context_dictionary</c>: the code of each key. A key of one code unit <c>c</c> is
        /// stored as <c>c</c> itself, a key <c>w + c</c> as <c>(code of w) &lt;&lt; 16 | c</c>;
        /// codes start at 3, so the two kinds never collide.
        /// </summary>
        private readonly Dictionary<long, int> _dictionary = [];

        /// <summary><c>context_dictionaryToCreate</c>: code units added but not yet written out.</summary>
        private readonly HashSet<char> _dictionaryToCreate = [];

        /// <summary><c>context_data</c>: the payload so far.</summary>
        private readonly StringBuilder _data = new();

        /// <summary><c>context_enlargeIn</c>, starting at 2 to compensate for the first entry.</summary>
        private int _enlargeIn = 2;

        /// <summary><c>context_dictSize</c>: the next code.</summary>
        private int _dictSize = 3;

        /// <summary><c>context_numBits</c>: the width of every code written now.</summary>
        private int _numBits = 2;

        /// <summary><c>context_data_val</c>: the bits of the payload character being filled.</summary>
        private int _dataVal;

        /// <summary><c>context_data_position</c>: how many of those bits are filled.</summary>
        private int _dataPosition;

        public string Compress()
        {
            if (input.Length == 0)
                return Finish();

            // context_w is input[wStart..i), the longest key ending just before the code unit
            // being read, and w is its code; it is never empty once the first code unit is read.
            var w = AddCharacter(input[0]);
            var wStart = 0;

            for (var i = 1; i < input.Length; i++)
            {
                var c = input[i];
                AddCharacter(c);

                if (_dictionary.TryGetValue(PhraseKey(w, c), out var wc))
                {
                    w = wc;
                    continue;
                }

                WritePhrase(w, wStart, i);

                // Add wc to the dictionary.
                if (!IsUnstorableKey(wStart, i + 1))
                    _dictionary.Add(PhraseKey(w, c), _dictSize);

                _dictSize++;
                w = _dictionary[c];
                wStart = i;
            }

            // Output the code for w.
            WritePhrase(w, wStart, input.Length);
            return Finish();
        }

        /// <summary>
        /// Gives a code unit seen for the first time the next code and marks it to be written
        /// out (<c>context_dictionaryToCreate</c>); returns its code.
        /// </summary>
        private int AddCharacter(char c)
        {
            if (!_dictionary.TryGetValue(c, out var code))
            {
                code = _dictSize++;
                _dictionary.Add(c, code);
                _dictionaryToCreate.Add(c);
            }

            return code;
        }

        /// <summary>
        /// Writes the phrase <c>input[start..end)</c>, whose code is <paramref name="code"/>: a
        /// code unit not yet written out as its literal, which costs a code of its own, and any
        /// other phrase as its code.
        /// </summary>
        private void WritePhrase(int code, int start, int end)
        {
            if (end - start == 1 && _dictionaryToCreate.Remove(input[start]))
            {
                var unit = input[start];
                if (unit < 256)
                {
                    WriteBits(CharacterIn8Bits, _numBits);
                    WriteBits(unit, 8);
                }
                else
                {
                    WriteBits(CharacterIn16Bits, _numBits);
                    WriteBits(unit, 16);
                }

                CountCode();
            }
            else
            {
                WriteBits(code, _numBits);
            }

            CountCode();
        }

        /// <summary>
        /// <c>context_enlargeIn--</c>: once the codes of the current width are used up, every
        /// later code is one bit wider.
        /// </summary>
        private void CountCode()
        {
            if (--_enlargeIn == 0)
            {
                _enlargeIn = 1 << _numBits;
                _numBits++;
            }
        }

        /// <summary>
        /// Writes the low <paramref name="count"/> bits of <paramref name="value"/>, least
        /// significant first; each payload character takes six of them, the first as its most
        /// significant bit.
        /// </summary>
        private void WriteBits(int value, int count)
        {
            for (var i = 0; i < count; i++)
            {
                _dataVal = (_dataVal << 1) | (value & 1);
                if (_dataPosition == BitsPerChar - 1)
                {
                    _dataPosition = 0;
                    _data.Append(UriSafeAlphabet[_dataVal]);
                    _dataVal = 0;
                }
                else
                {
                    _dataPosition++;
                }

                value >>= 1;
            }
        }

        /// <summary>
        /// Marks the end of the stream and flushes the last character, padded with zero bits. A
        /// stream that ends on a character boundary still gets one more character, all zeros
        /// (<c>A</c>), as the JavaScript's flush loop writes it.
        /// </summary>
        private string Finish()
        {
            WriteBits(EndOfStream, _numBits);

            while (true)
            {
                _dataVal <<= 1;
                if (_dataPosition == BitsPerChar - 1)
                {
                    _data.Append(UriSafeAlphabet[_dataVal]);
                    return _data.ToString();
                }

                _dataPosition++;
            }
        }

        /// <summary>
        /// Whether the phrase <c>input[start..end)</c> is <see cref="UnstorableKey"/>, the key
        /// JavaScript's object dictionary cannot hold.
        /// </summary>
        private bool IsUnstorableKey(int start, int end)
            => end - start == UnstorableKey.Length
               && input.AsSpan(start, UnstorableKey.Length).SequenceEqual(UnstorableKey);

        private static long PhraseKey(int prefixCode, char c) => ((long)prefixCode << 16) | c;
    }
}
