using System.Text;
using System.Collections.Generic;

namespace KatLang
{
    public class Condition : Expression
    {
        public readonly IList<double> Values;

        public Condition(IEnumerable<double> values)
        {
            Values = new List<double>(values);
        }

        public override int GetHashCode()
        {
            var hash = 0;
            foreach (var val in Values)
            {
                hash ^= val.GetHashCode();
            }

            return hash;
        }

        public override bool Equals(object? obj)
        {
            if (obj is null)
            {
                return false;
            }
            if (ReferenceEquals(this, obj))
            {
                return true;
            }

            if (obj is Condition condition && Values.Count == condition.Values.Count)
            {
                for (var i = 0; i < Values.Count; i++)
                {
                    if (Values[i] != condition.Values[i])
                    {
                        return false;
                    }
                }
                return true;
            }
            return false;
        }

        public override string ToString()
        {
            var sb = new StringBuilder();

            foreach (var condition in Values)
            {
                if (sb.Length > 2)
                {
                    sb.Append(',');
                }
                sb.Append('#');
                sb.Append(condition);
            }

            return sb.ToString();
        }
    }

    public class ParameterWeightHolder
    {
        public string Name { get; set; }
        public int Weight { get; set; }

        public ParameterWeightHolder(ParameterExpression expression) : this(expression.Name, expression.GraceWeight) { }
        public ParameterWeightHolder(string name, int weight)
        {
            Name = name;
            Weight = weight;
        }
    }

    public struct TextPosition
    {
        public readonly int LineNumber;
        public readonly int Column;

        public TextPosition(int line, int column)
        {
            LineNumber = line;
            Column = column;
        }
    }

    public enum MarkerSeverity
    {
        Hint = 1,
        Info = 2,
        Warning = 4,
        Error = 8,
    }

    public class MarkerData
    {
        public MarkerData(string message, MarkerSeverity severity, int startLineNumber, int startColumn, int endLineNumber, int endColumn)
        {
            Message = message;
            Severity = severity;
            StartLine = startLineNumber;
            StartColumn = startColumn;
            EndLine = endLineNumber;
            EndColumn = endColumn;
        }

        public string Message { get; }

        public MarkerSeverity Severity { get; }

        public int StartColumn { get; }

        public int StartLine { get; }

        public int EndColumn { get; }

        public int EndLine { get; }
    }

    public class ParsingResult
    {
        public Expression Expression { get; }
        public List<MarkerData> Errors { get; }

        public ParsingResult(Expression expr, List<MarkerData> errors)
        {
            Expression = expr;
            Errors = errors;
        }
    }
}
