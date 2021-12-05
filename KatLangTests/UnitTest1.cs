using Microsoft.VisualStudio.TestTools.UnitTesting;
using KatLang;
using System.Linq;
using System.IO;
using System;

namespace KatLangTests
{
    [TestClass]
    public class UnitTest1
    {
        [TestMethod]
        public void EmptyKatCodeTest1()
        {
            var algorithm = Parser.Parse(null).Expression as AlgorithmExpression;

            Assert.AreEqual(0, algorithm.Expressions.Count);
            Assert.AreEqual(0, algorithm.Properties.Count);
        }

        [TestMethod]
        public void EmptyKatCodeTest2()
        {
            var source = "";
            var algorithm = Parser.Parse(source).Expression as AlgorithmExpression;

            Assert.AreEqual(0, algorithm.Expressions.Count);
            Assert.AreEqual(0, algorithm.Properties.Count);
        }

        [TestMethod]
        public void EmptyKatCodeTest3()
        {
            var source = " ";
            var algorithm = Parser.Parse(source).Expression as AlgorithmExpression;

            Assert.AreEqual(0, algorithm.Expressions.Count);
            Assert.AreEqual(0, algorithm.Properties.Count);
        }

        [TestMethod]
        public void ConstantTest()
        {
            var source = "6";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("6", result.Expression.ToString());
        }

        [TestMethod]
        public void NegativeConstantTest()
        {
            var source = "-5";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("-5", result.Expression.ToString());
        }

        [TestMethod]
        public void MinusMinusTest()
        {
            var source = "--5";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("5", result.Expression.ToString());
        }

        [TestMethod]
        public void NegativeArgumentTest()
        {
            var source = "sign(-5)";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("-1", result.Expression.ToString());
        }

        [TestMethod]
        public void BinaryMinusTest()
        {
            var source = "0-5";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("-5", result.Expression.ToString());
        }

        [TestMethod]
        public void BinaryMinusNegativeArgumentTest()
        {
            var source = "6--1";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("7", result.Expression.ToString());
        }

        [TestMethod]
        public void TestManySimpleOperations()
        {
            var source = "6-2+3";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("7", result.Expression.ToString());
        }

        [TestMethod]
        public void TestManyDivisions()
        {
            var source = "200 / 4 / 2";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("25", result.Expression.ToString());
        }

        [TestMethod]
        public void OpPriorityTest1()
        {
            var source = @"1+2*3";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("7", result.Expression.ToString());
        }

        [TestMethod]
        public void OpPriorityTest2()
        {
            var source = "(2 + 3) * 4";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("20", result.Expression.ToString());
        }

        [TestMethod]
        public void OpPriorityTest3()
        {
            var source = "2 + 3 ^ 2 * 3 + 4";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("33", result.Expression.ToString());
        }

        [TestMethod]
        public void OpPriorityTest4()
        {
            var source = @"
                f=a+1
                3+f(2)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("6", result.Expression.ToString());
        }

        [TestMethod]
        public void ParamListTest()
        {
            var source = "a+b, 1, 2";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("a+b,1,2", result.Expression.ToString());
        }

        [TestMethod]
        public void EmptyPropertyTest()
        {
            var source = "x=";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("", result.Expression.ToString());
        }

        [TestMethod]
        public void PropertyTest1()
        {
            var source = @"
                Value = 1.234
                Value
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("1.234", result.Expression.ToString());
        }

        [TestMethod]
        public void PropertyTest2()
        {
            var source = @"
                Value = 1.234
                Value(0)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("1.234", result.Expression.ToString());
        }

        [TestMethod]
        public void PropertyTest3()
        {
            var source = @"
                Value = (2 + 3) * 4
                Value
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("20", result.Expression.ToString());
        }

        [TestMethod]
        public void PropertyTest4()
        {
            var source = @"
                Func = (2 + 3) * x
                Func(4)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("20", result.Expression.ToString());
        }

        [TestMethod]
        public void PropertyTest5()
        {
            var source = @"
                Sum = a+b
                Sum(4,6)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("10", result.Expression.ToString());
        }

        [TestMethod]
        public void PropertyTest6()
        {
            var source = @"
                Func = sign(x)
                Func(-(-2+3))
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("-1", result.Expression.ToString());
        }

        [TestMethod]
        public void PropertyTest7()
        {
            var source = @"
                Func = sign(-x)
                Func (6)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("-1", result.Expression.ToString());
        }

        [TestMethod]
        public void PropertyTest8()
        {
            var source = @"
                Func = sign(x)
                Func(-4)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("-1", result.Expression.ToString());
        }

        [TestMethod]
        public void PropertyTest9()
        {
            var source = @"
                Func = round(1.23456, 2)
                Func
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("1.23", result.Expression.ToString());
        }

        [TestMethod]
        public void PropertyTest10()
        {
            var source = @"
                Func = round(x, 2)
                Func(1.23456)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("1.23", result.Expression.ToString());
        }

        [TestMethod]
        public void PropertyTest11()
        {
            var source = @"
                Func = x * round(1.23456, 2)
                Func(2)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2.46", result.Expression.ToString());
        }

        [TestMethod]
        public void PropertyTest12()
        {
            var source = @"
                Func = round(1.23456, 2 * x)
                Func(2)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("1.2346", result.Expression.ToString());
        }

        [TestMethod]
        public void PropertyTest13()
        {
            var source = @"
                Func = round(1 + x, 2)*y
                Func (0.123456, 2)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2.24", result.Expression.ToString());
        }

        [TestMethod]
        public void PropertyTest14()
        {
            var source = @"
                f=5
                #f()
            ";

            var result = Parser.Parse(source);
            Assert.AreEqual(1, result.Errors.Count);
        }

        [TestMethod]
        public void PropertyTest15()
        {
            //if brackets follows after some other construction than identifier, then it is considered as beginning of new expression.
            var source = @"
                Test=0<1
                (5)
            ";

            var result = Parser.Parse(source);
            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("5", result.Expression.ToString());
        }

        [TestMethod]
        public void UserFuncDoubleExecution()
        {
            var source = @"
                f=a
                f(1), f(2)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("1,2", result.Expression.ToString());
        }

        [TestMethod]
        public void NotTest1()
        {
            var source = "not(1)";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("0", result.Expression.ToString());
        }

        [TestMethod]
        public void NotTest2()
        {
            var source = "not(0)";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("1", result.Expression.ToString());
        }

        [TestMethod]
        public void NotTest3()
        {
            var source = "not(not(1))";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("1", result.Expression.ToString());
        }

        [TestMethod]
        public void InvalidExpressionTest()
        {
            var source = ";";
            var result = Parser.Parse(source);
            Assert.AreEqual(1, result.Errors.Count);
        }

        [TestMethod]
        public void InvalidExpressionTest2()
        {
            var source = "6=";
            var result = Parser.Parse(source);
            Assert.AreEqual(1, result.Errors.Count);
        }

        [TestMethod]
        public void InvalidExpressionTest3()
        {
            var source = "=";
            var result = Parser.Parse(source);
            Assert.AreEqual(1, result.Errors.Count);
        }

        [TestMethod]
        public void InvalidExpressionTest5()
        {
            var source = "1#2";
            var result = Parser.Parse(source);
            Assert.AreEqual(1, result.Errors.Count);
        }

        [TestMethod]
        public void InvalidExpressionTest6()
        {
            var source = "(2+3";
            var result = Parser.Parse(source);
            Assert.AreEqual(1, result.Errors.Count);
        }

        [TestMethod]
        public void IgnoranceOperatorTest1()
        {
            var source = "#a, 6";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("6", result.Expression.ToString());
        }

        [TestMethod]
        public void IgnoranceOperatorTest2()
        {
            var source = @"
                f = #a
                f(2)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("", result.Expression.ToString());
        }

        [TestMethod]
        public void IgnoranceOperatorTest3()
        {
            var source = @"
                f = #a, 3
                f(2)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("3", result.Expression.ToString());
        }

        [TestMethod]
        public void IgnoranceOperatorTest4()
        {
            var source = @"
                f = #a, #a
                f(2)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("", result.Expression.ToString());
        }

        [TestMethod]
        public void IgnoranceOperatorTest5()
        {
            var source = @"
                f = #a, #a, a
                f(2)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2", result.Expression.ToString());
        }

        [TestMethod]
        public void IgnoranceOperatorTest6()
        {
            var source = @"
                f = #a, a, a
                f(2)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2,2", result.Expression.ToString());
        }

        [TestMethod]
        public void IgnoranceOperatorTest7()
        {
            var source = @"
                f = #a, #a, 3
                f(2)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("3", result.Expression.ToString());
        }

        [TestMethod]
        public void IgnoranceOperatorTest8()
        {
            var source = @"
                (#a, #a), 6
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("6", result.Expression.ToString());
        }

        [TestMethod]
        public void IgnoranceOperatorTest9()
        {
            var source = @"
                (#a, a), 6
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("a,6", result.Expression.ToString());
        }

        [TestMethod]
        public void IgnoranceOperatorTest10()
        {
            var source = @"
                f = 6, #
                f(0, 7, 6, 5, 4, 3, 2, 1)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("6", result.Expression.ToString());
        }

        [TestMethod]
        public void IgnoranceOperatorTest11()
        {
            var source = @"
                f = 6, #a
                f
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("6", result.Expression.ToString());
        }

        [TestMethod]
        public void IgnoranceOperatorTest12()
        {
            var source = @"
                f = 6, #
                f
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("6", result.Expression.ToString());
        }

        [TestMethod]
        public void IgnoranceOperatorTest13()
        {
            var source = @"
                g = 2, #
                f = g, 1
                f(0)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2,1", result.Expression.ToString());
        }

        [TestMethod]
        public void IgnoranceOperatorTest14()
        {
            var source = @"
                g = 2, #, 3
                f = g, 1
                f(0)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2,3,1", result.Expression.ToString());
        }

        [TestMethod]
        public void IgnoranceOperatorTest15()
        {
            var source = @"
                g = 2, #, 3
                f = g(5), 1
                f(0)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2,3,1", result.Expression.ToString());
        }

        [TestMethod]
        public void ConditionalParameterTest1()
        {
            var source = @"
                If = #1, a
                If = #0, #a

                If(1, 2)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2", result.Expression.ToString());
        }

        [TestMethod]
        public void ConditionalParameterTest2()
        {
            var source = @"
                If = #1, a
                If = #0, #a

                If(0, 2)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("", result.Expression.ToString());
        }

        [TestMethod]
        public void ConditionalParameterTest3()
        {
            var source = @"
                If = #1, a
                If = #0, #a

                If(2, 3)
            ";
            var result = Parser.Parse(source);
            Assert.AreEqual(1, result.Errors.Count());
        }

        [TestMethod]
        public void ConditionalParameterTest4()
        {
            var source = @"
                If = #1, a
                If = #0, #a

                If(1, 2, 3)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2", result.Expression.ToString());
        }

        [TestMethod]
        public void ConditionalParameterTest5()
        {
            var source = @"
                If = #1, a
                If = #0, #a

                If(0, 2, 3)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("", result.Expression.ToString());
        }

        [TestMethod]
        public void ConditionalParameterTest6()
        {
            var source = @"
                else = #0, #a, b
                else = #, a, #b

                else(0, 2, 3)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("3", result.Expression.ToString());
        }

        [TestMethod]
        public void ConditionalParameterTest7()
        {
            var source = @"
                else = #0, #a, b
                else = #, a, #b

                else(1, 2, 3)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2", result.Expression.ToString());
        }

        [TestMethod]
        public void ConditionalParameterTest8()
        {
            var source = @"
                else = #0, #a, b
                else = #, a, #b

                else(0, 2, 3, 4)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("3", result.Expression.ToString());
        }

        [TestMethod]
        public void ConditionalParameterTest9()
        {
            var source = @"
                else = #0, #a, b
                else = #, a, #b

                else(1, 2, 3, 4)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2", result.Expression.ToString());
        }

        [TestMethod]
        public void ConditionalParameterTest10()
        {
            var source = @"
                else = #0, #a, b
                else = #, a, #b

                else(1, 2)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2", result.Expression.ToString());
        }

        [TestMethod]
        public void ConditionalParameterTest11()
        {
            var source = @"
                else = #0, #a, b
                else = #, a, #b

                else(0, 2)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("b", result.Expression.ToString());
        }

        [TestMethod]
        public void ComplexConditionalParameterTest1()
        {
            var source = @"
                else = #0, #a, b
                else = #, a, #b

                f = else(a>7, b, c)
                f(8, 3, 4)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("3", result.Expression.ToString());
        }

        [TestMethod]
        public void ComplexConditionalParameterTest2()
        {
            var source = @"
                else = #0, #a, b
                else = #, a, #b

                f = else(a>7, b, c)
                f(6, 3, 4)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("4", result.Expression.ToString());
        }

        [TestMethod]
        public void ComplexConditionalParameterTest3()
        {
            var source = @"
                else = #0, #a, b
                else = #, a, #b

                f = else(a>7, b, c)
                f(8, 3)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("3", result.Expression.ToString());
        }

        [TestMethod]
        public void ComplexConditionalParameterTest4()
        {
            var source = @"
                else = #0, #a, b
                else = #, a, #b

                f = else (a>7, b)
                f(8, 3)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("3", result.Expression.ToString());
        }

        [TestMethod]
        public void ComplexConditionalParameterTest5()
        {
            var source = @"
                else = #0, #a, b
                else = #, a, #b

                f = else(a>7, b)
                f(8)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("b", result.Expression.ToString());
        }

        [TestMethod]
        public void ComplexConditionalParameterTest6()
        {
            var source = @"
                else = #0, #a, b
                else = #, a, #b

                f = else(a>7)
                f(8)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("a", result.Expression.ToString());
        }

        [TestMethod]
        public void ComplexConditionalParameterTest7()
        {
            var source = @"
                else = #0, #a, b
                else = #, a, #b

                f = else(a>7, c, 6)
                f(8)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("c", result.Expression.ToString());
        }

        [TestMethod]
        public void ComplexConditionalParameterTest8()
        {
            var source = @"
                else = #0, #a, b
                else = #, a, #b

                f = else(a>7, c, d)
                f(8)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("c", result.Expression.ToString());
        }

        [TestMethod]
        public void ParametersInScopeTest1()
        {
            var source = @"
                f = (a + b) + (b + c)

                f(2,3,4)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("12", result.Expression.ToString());
        }

        [TestMethod]
        public void ParametersInScopeTest2()
        {
            var source = @"
                f = #a, #b, #c, (a + b) + (b + c)

                f(2, 3, 4, 5)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("12", result.Expression.ToString());
        }


        [TestMethod]
        public void AnonymousIdentityAlgorithmTest()
        {
            var source = "a(3)";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("a(3)", result.Expression.ToString());
        }

        [TestMethod]
        public void HigherFunctionTest1()
        {
            var source = @"
                f=k(6)
                f(a+1)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("f(a+1)", result.Expression.ToString());
        }

        [TestMethod]
        public void HigherFunctionTest2()
        {
            var source = @"
                f=k(6)
                f{a+1}
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("7", result.Expression.ToString());
        }

        [TestMethod]
        public void HigherFunctionTest3()
        {
            var source = @"
                f=k(6)
                f
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("k(6)", result.Expression.ToString());
        }

        [TestMethod]
        public void HigherFunctionTest4()
        {
            var source = @"
                f=k(6)
                f(1)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("1", result.Expression.ToString());
        }

        [TestMethod]
        public void HigherFunctionTest5()
        {
            var source = @"
                f=k(6)+k(7)
                f{a+1}
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("15", result.Expression.ToString());
        }

        [TestMethod]
        public void HigherFunctionTest6()
        {
            var source = @"
                f=a+1,b+1,c+1
                g=x+y+z
                g(f(1,2,3))
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("9", result.Expression.ToString());
        }

        [TestMethod]
        public void HigherFunctionTest7()
        {
            var source = @"
                g = a(5)
                f = g((b+10) + c)
                f(3)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("g(13+c)", result.Expression.ToString());
        }

        [TestMethod]
        public void HigherFunctionTest8()
        {
            var source = @"
                g = a(5)
                f = g(b+10) + c
                f(3)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("13+c", result.Expression.ToString());
        }

        [TestMethod]
        public void HigherFunctionTest9()
        {
            var source = @"
                g = a(5)
                f = g{b+10} + c
                f(3)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("18", result.Expression.ToString());
        }

        [TestMethod]
        public void HigherFunctionNoInfiniteLoopTest2()
        {
            var source = @"

                f=x+1
                f(f)

            ";

            var result = Parser.Parse(source);
            Assert.AreEqual(0, result.Errors.Count);

            //TODO: think if this is the best that can be done with f(f). Seems odd.
            Assert.AreEqual("f(x+1)", result.Expression.ToString());
            Assert.Inconclusive();
        }

        [TestMethod]
        public void ContentSelectorTest1()
        {
            var source = "(1,2,3,4):1";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2", result.Expression.ToString());
        }

        [TestMethod]
        public void ContentSelectorTest2()
        {
            var source = @"
                f=(1,2,3,4)
                f:1
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2", result.Expression.ToString());
        }

        [TestMethod]
        public void ContentSelectorTest3()
        {
            var source = @"
                f=a:b
                f((1,2,3,4),1)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2", result.Expression.ToString());
        }

        [TestMethod]
        public void ContentSelectorTest4()
        {
            var source = @"
                A=3
                A:0
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("3", result.Expression.ToString());
        }

        [TestMethod]
        public void ContentSelectorTest5()
        {
            var source = @"
                A=3
                A:x
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("3:x", result.Expression.ToString());
        }

        [TestMethod]
        public void ContentSelectorTest6()
        {
            //Tests if selection expression is cloned properly - it can be seen in repeated usage
            var source = @"
                Data=5,4,3,2,1
                Z=a+1, Data:a
                repeat(Z, 2, 0)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2,4", result.Expression.ToString());
        }

        [TestMethod]
        public void ContentSelectorTest7()
        {
            //Tests if binary expression is cloned properly - it can be seen in repeated usage
            var source = @"
                Data=5,4,3,2,1
                SumData=a+1, sum+Data:a
                repeat(SumData, Data.length, 0, 0):1
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("15", result.Expression.ToString());
        }

        [TestMethod]
        public void LoopTest1()
        {
            var source = @"
                f=n-1, n*result, n>1
                loop(f, 6, 1):1
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("720", result.Expression.ToString());
        }

        [TestMethod]
        public void LoopTest2()
        {
            var source = @"
                f=n-1, n*result, n>1
                loop(f, 6, 1):1
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("720", result.Expression.ToString());
        }

        [TestMethod]
        public void LoopTest3()
        {
            var source = @"
                f=n+1
                repeat(f, 0, 10)
            ";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("10", result.Expression.ToString());
        }

        [TestMethod]
        public void ManyAlgorithmResultTest1()
        {
            var source = "1+2 3+4";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("3\n7", result.Expression.ToString());
        }

        [TestMethod]
        public void ManyAlgorithmResultTest2()
        {
            var source = "1+2, 3+4";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("3\n7", result.Expression.ToString());
        }

        [TestMethod]
        public void ProjectEulerProblem1()
        {
            var source = @"
                Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n), n > 2
                Sum = loop(Algo, x, 0) : 1
                Sum(999)";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("233168", result.Expression.ToString());
        }

        [TestMethod]
        public void ProjectEulerProblem2()
        {
            var source = @"
                Algo = b, ~a + b, sum + if(b mod 2 == 0, b), b <= 4000000
                Sum = loop(Algo, 1, 2, 0) : 2
                Sum";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("4613732", result.Expression.ToString());
        }

        [TestMethod]
        public void OpenAlgorithmTest()
        {
            var fileName = "algorithm.kat";
            File.WriteAllText(fileName, "9+11");

            var source = @"
                A=open('algorithm.kat')
                B=10
                A+B";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("30", result.Expression.ToString());
        }

        [TestMethod]
        public void OpenPropertiesTest()
        {
            var fileName = "algorithm.kat";
            File.WriteAllText(fileName, "X=5 9+11");

            var source = @"
                A=open('algorithm.kat')
                B=10
                A+B";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("30", result.Expression.ToString());
        }

        [TestMethod]
        public void OpenPropertyAccessTest()
        {
            var fileName = "algorithm.kat";
            File.WriteAllText(fileName, "X=5 9+11");

            var source = @"
                A=open('algorithm.kat')
                A.X+10";

            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("15", result.Expression.ToString());
        }

        [TestMethod]
        public void OpenSelectorTest()
        {
            var fileName = "algorithm.kat";
            File.WriteAllText(fileName, "X=5 9+11 10 12");

            var source = @"
                A=open('algorithm.kat')
                A:1";

            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("10", result.Expression.ToString());
        }

        [TestMethod]
        public void LoadAlgorithmFromWeb()
        {
            var source = @"
                A=load('https://kat.blob.core.windows.net/examples/algorithm.kat')
                A.X+5";

            var result = Parser.Parse(source, Parser.DownloadCode);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("25", result.Expression.ToString());
        }

        [TestMethod]
        public void OpenAlgorithmFromWebNonExistent()
        {
            var source = @"
                A=load2('http')
                A.X+5";

            var result = Parser.Parse(source);

            Assert.AreEqual(1, result.Errors.Count);
        }

        [TestMethod]
        public void JoinAlgorithmFromWeb()
        {
            var source = @"
                join('https://kat.blob.core.windows.net/examples/algorithm.kat')
                X+5";

            var result = Parser.Parse(source, Parser.DownloadCode);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("25", result.Expression.ToString());
        }

        [TestMethod]
        public void LoadAndJoinAlgorithmFromWeb()
        {
            var source = @"
                A=load('https://kat.blob.core.windows.net/examples/algorithm.kat')
                join(A)
                X+5";

            var result = Parser.Parse(source, Parser.DownloadCode);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("25", result.Expression.ToString());
        }

        [TestMethod]
        public void ConditionalPropertyErrors()
        {
            var source = @"
Reverse = #0, 1
Reverse = #0, 2
Reverse = 0, 0
Reverse = 0, 1

Reverse(7)";

            var result = Parser.Parse(source);
            Assert.AreEqual(6, result.Errors.Count);
        }

        [TestMethod]
        public void OpenWrongAlgorithmTest1()
        {
            var source = "A=load('nonExistent.kat') A";
            var result = Parser.Parse(source);

            Assert.AreEqual(1, result.Errors.Count);
        }

        [TestMethod]
        public void OpenWrongAlgorithmTest2()
        {
            var fileName = "algorithm.kat";
            File.WriteAllText(fileName, ";");

            var source = "A=load('algorithm.kat') A";

            var result = Parser.Parse(source);

            Assert.AreEqual(1, result.Errors.Count);
        }

        [TestMethod]
        public void JoinWrongAlgorithmTest1()
        {
            var source = "join('nonExistent.kat')";
            var result = Parser.Parse(source);

            Assert.AreEqual(1, result.Errors.Count);
        }

        [TestMethod]
        public void JoinWrongAlgorithmTest2()
        {
            var fileName = "algorithm.kat";
            File.WriteAllText(fileName, ";");

            var source = "join('algorithm.kat')";
            var result = Parser.Parse(source);

            Assert.AreEqual(1, result.Errors.Count);
        }

        [TestMethod]
        public void PiTest1()
        {
            var source = "pi";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual(Math.PI.ToString(), result.Expression.ToString());
        }

        [TestMethod]
        public void PiTest2()
        {
            var source = "pi()";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual(Math.PI.ToString(), result.Expression.ToString());
        }

        [TestMethod]
        public void ExpTest1()
        {
            var source = "exp";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual(Math.E.ToString(), result.Expression.ToString());
        }

        [TestMethod]
        public void ExpTest2()
        {
            var source = "exp()";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual(Math.E.ToString(), result.Expression.ToString());
        }

        [TestMethod]
        public void PropertyExecutionTest()
        {
            var source = @"
Numbers={A=x B=3}
Numbers.A(6)";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("6", result.Expression.ToString());
        }

        [TestMethod]
        public void ExtensionPropertyTest1()
        {
            var source = "Add1=x+1 6.Add1";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("7", result.Expression.ToString());
        }

        [TestMethod]
        public void ExtensionPropertyTest2()
        {
            var source = "Add1=x+1 Number=6 Number.Add1";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("7", result.Expression.ToString());
        }

        [TestMethod]
        public void ExtensionPropertyTest3()
        {
            var source = "Add1=x+1 6.5.Add1";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("7.5", result.Expression.ToString());
        }

        [TestMethod]
        public void ExtensionPropertyTest4()
        {
            var source = "Numbers=(First=1 Second=2) Add=a+1 Numbers.First.Add";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2", result.Expression.ToString());
        }

        [TestMethod]
        public void ExtensionPropertyTest5()
        {
            var source = @"
Numbers=(First=1 Second=2)
Add=a+b
Numbers.First.Add(3)";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("4", result.Expression.ToString());
        }

        [TestMethod]
        public void ExtensionPropertyTest6()
        {
            var source = @"
Numbers = 3, 5, 9, 1, 0, 6
Add = a + 1, sum + Numbers:a
Sum = Add.repeat(Numbers.length, 0, 0):1
Sum";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("24", result.Expression.ToString());
        }

        [TestMethod]
        public void ExtensionPropertyTest7()
        {
            var source = @"
//Properties:
Algo = b, ~a + b, sum + if(b mod 2 == 0, b), b<10
Sum = Algo.loop(1, 2, 0) : 2
//Output:
Sum";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("10", result.Expression.ToString());
        }

        [TestMethod]
        public void ExtensionPropertyTest8()
        {
            var source = @"
Add1 = a + 1, b
Check = if(a < b, a, 0), b
Add1.Add1.Check.repeat(6, 0, 30)";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("12,30", result.Expression.ToString());
        }

        [TestMethod]
        public void ExtensionPropertyTest9()
        {
            var source = @"
Add = a+1, b, c
Check1 = if(a<b, (a, b), (b, a)); c
Check2 = a; if(b<c, (b, c), (c, b))
Algo = Add(a,b,c).Check1.Check2
Algo(1,2,3)";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2,2,3", result.Expression.ToString());
        }

        [TestMethod]
        public void ExtensionPropertyTest10()
        {
            var source = @"
Add = a+1, b, c
Check1 = if(a<b, (a, b), (b, a)); c
Check2 = a; if(b<c, (b, c), (c, b))
Add(3,2,3).Check1.Check2";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("2,3,4", result.Expression.ToString());
        }

        [TestMethod]
        public void ExtensionPropertyTest11()
        {
            var source = @"
K=a.t
K(2, {x+1})";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("3", result.Expression.ToString());
        }

        [TestMethod]
        public void ExtensionPropertyTest12()
        {
            var source = @"
K=a.~t
K({x+1}, 2)";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("3", result.Expression.ToString());
        }

        [TestMethod]
        public void AlgorithmCombinintTest()
        {
            //testing use of semicolon usage - it joins two or more algorithms into one.
            var source = @"
Check = if(x > 0, (x-1 y), (y-1 y-1))
Algo = Check(x, y); y > 0
Algo.loop(6, 6)";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("0,0,1", result.Expression.ToString());
        }

        [TestMethod]
        public void AlgorithmCombiningTest2()
        {
            //testing use of semicolon usage - it joins two or more algorithms into one.
            var source = @"
Check = if(x > 0, (x-1 y), (y-1 y-1))
Algo = combine(Check(x, y), y > 0)
Algo.loop(6, 6)";
            var result = Parser.Parse(source);

            Assert.AreEqual(0, result.Errors.Count);
            Assert.AreEqual("0,0,1", result.Expression.ToString());
        }






    }
}
