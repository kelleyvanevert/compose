#[macro_use]
extern crate pest_derive;

#[macro_use]
extern crate lazy_static;

use pest::{
    error::Error,
    iterators::{Pair, Pairs},
    pratt_parser::{Assoc, Op, PrattParser},
    Parser,
};
use std::fs;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct MyParser;

lazy_static! {
    static ref PRATT: PrattParser<Rule> = PrattParser::new()
        .op(Op::postfix(Rule::coerce))
        .op(Op::infix(Rule::add, Assoc::Left) | Op::infix(Rule::sub, Assoc::Left))
        .op(Op::infix(Rule::mul, Assoc::Left) | Op::infix(Rule::div, Assoc::Left))
        .op(Op::infix(Rule::pow, Assoc::Right))
        .op(Op::postfix(Rule::fac))
        .op(Op::prefix(Rule::pos) | Op::prefix(Rule::neg));
}

#[derive(Debug, PartialEq)]
enum Expr<'a> {
    Id(&'a str),
    SampleInput,
    EnvelopeInput,
    PatternInput,
    Number(f64),
    Factor(f64),
    Coercion(Box<Expr<'a>>, &'a str),
    Function(Vec<&'a str>, Box<Expr<'a>>),
    Block(Vec<Stmt<'a>>, Option<Box<Expr<'a>>>),
    Prefix(&'a str, Box<Expr<'a>>),
    Postfix(&'a str, Box<Expr<'a>>),
    Infix(&'a str, Box<Expr<'a>>, Box<Expr<'a>>),
}

#[derive(Debug, PartialEq)]
enum Stmt<'a> {
    Def(&'a str, Expr<'a>),
    Ret(Expr<'a>),
    Noop,
}

fn parse_into_expr<'a>(pair: Pair<'a, Rule>) -> Expr<'a> {
    match pair.as_rule() {
        Rule::expr => parse_pairs_into_expr(pair.into_inner()),
        Rule::id => Expr::Id(pair.as_str()),
        Rule::sample_input => Expr::SampleInput,
        Rule::envelope_input => Expr::EnvelopeInput,
        Rule::pattern_input => Expr::PatternInput,
        Rule::number => Expr::Number(pair.as_str().parse::<f64>().unwrap()),
        Rule::factor => Expr::Factor(pair.into_inner().as_str().parse::<f64>().unwrap()),
        Rule::function => {
            let mut inner = pair.into_inner();
            let params: Vec<&'a str> = inner
                .next()
                .unwrap()
                .into_inner()
                .map(|p| p.as_str())
                .collect();
            let expr = parse_into_expr(inner.next().unwrap());

            Expr::Function(params, Box::new(expr))
        }
        Rule::block => {
            let mut inner = pair.into_inner();
            let stmts: Vec<Stmt<'a>> = inner
                .next()
                .unwrap()
                .into_inner()
                .map(|p| parse_into_stmt(p))
                .collect();

            let maybe_expr = inner.next().map(parse_into_expr).map(|expr| Box::new(expr));

            Expr::Block(stmts, maybe_expr)
        }
        r => unreachable!("not an expr: {:?}", r),
    }
}

fn parse_pairs_into_expr<'a>(pairs: Pairs<'a, Rule>) -> Expr<'a> {
    PRATT
        .map_primary(parse_into_expr)
        .map_prefix(|op, rhs| Expr::Prefix(op.as_str(), Box::new(rhs)))
        .map_postfix(|lhs, op| match op.as_rule() {
            Rule::coerce => {
                let mut inner = op.into_inner();
                let typename = inner.next().unwrap().as_str();
                Expr::Coercion(Box::new(lhs), typename)
            }
            _ => Expr::Postfix(op.as_str(), Box::new(lhs)),
        })
        .map_infix(|lhs, op, rhs| Expr::Infix(op.as_str(), Box::new(lhs), Box::new(rhs)))
        .parse(
            pairs
                // hack
                .filter(|p| p.as_rule() != Rule::EOI),
        )
}

fn parse_into_stmt(pair: Pair<Rule>) -> Stmt {
    match pair.as_rule() {
        Rule::def => {
            let mut inner = pair.into_inner();
            let id = inner.next().unwrap().as_str();
            let expr = parse_into_expr(inner.next().unwrap());
            Stmt::Def(id, expr)
        }
        Rule::ret => Stmt::Ret(parse_into_expr(pair.into_inner().next().unwrap())),
        Rule::noop => Stmt::Noop,
        r => unreachable!("not a stmt: {:?}", r),
    }
}

#[allow(unused)]
fn parse_expression(input: &str) -> Result<Expr, Error<Rule>> {
    let pairs = MyParser::parse(Rule::entry_expression, input)?;

    Ok(parse_pairs_into_expr(pairs))
}

#[allow(unused)]
fn parse_statement(input: &str) -> Result<Stmt, Error<Rule>> {
    let mut pairs = MyParser::parse(Rule::entry_statement, input)?;
    let value = pairs.next().unwrap();

    Ok(parse_into_stmt(value))
}

#[test]
fn test_parse() {
    fn num(num: f64) -> Expr<'static> {
        Expr::Number(num)
    }

    fn factor(num: f64) -> Expr<'static> {
        Expr::Factor(num)
    }

    fn prefix<'a>(op: &'a str, a: Expr<'a>) -> Expr<'a> {
        Expr::Prefix(op, Box::new(a))
    }

    fn postfix<'a>(op: &'a str, a: Expr<'a>) -> Expr<'a> {
        Expr::Postfix(op, Box::new(a))
    }

    fn infix<'a>(op: &'a str, a: Expr<'a>, b: Expr<'a>) -> Expr<'a> {
        Expr::Infix(op, Box::new(a), Box::new(b))
    }

    fn coerce<'a>(a: Expr<'a>, typename: &'a str) -> Expr<'a> {
        Expr::Coercion(Box::new(a), typename)
    }

    fn func<'a>(params: Vec<&'a str>, a: Expr<'a>) -> Expr<'a> {
        Expr::Function(params, Box::new(a))
    }

    assert_eq!(parse_expression("hello"), Ok(Expr::Id("hello")));
    assert_eq!(parse_expression("  bla_"), Ok(Expr::Id("bla_")));
    assert_eq!(parse_expression(" bla_bla  "), Ok(Expr::Id("bla_bla")));

    assert!(matches!(parse_expression("hello 8"), Err(_)));

    assert!(matches!(parse_expression("_bla"), Err(_)));
    assert!(matches!(parse_expression("Bla"), Err(_)));

    assert_eq!(parse_expression("123"), Ok(num(123.0)));
    assert_eq!(parse_expression(" -123"), Ok(prefix("-", num(123.0))));
    assert_eq!(parse_expression("-123"), Ok(prefix("-", num(123.0))));
    assert_eq!(parse_expression(" +123"), Ok(prefix("+", num(123.0))));
    assert_eq!(parse_expression("+123"), Ok(prefix("+", num(123.0))));
    assert_eq!(parse_expression(" 123."), Ok(num(123.0)));
    assert_eq!(parse_expression(" 123.456"), Ok(num(123.456)));
    assert_eq!(parse_expression(".456"), Ok(num(0.456)));
    assert_eq!(parse_expression("0.456  "), Ok(num(0.456)));
    assert_eq!(parse_expression("0. "), Ok(num(0.0)));
    assert_eq!(parse_expression("-0."), Ok(prefix("-", num(0.0))));

    assert!(matches!(parse_expression("."), Err(_)));

    assert_eq!(parse_expression("(123 ) "), Ok(num(123.0)));

    assert_eq!(parse_expression("123f"), Ok(factor(123.0)));
    assert_eq!(parse_expression("123.f"), Ok(factor(123.0)));
    assert_eq!(parse_expression(" +123.f"), Ok(prefix("+", factor(123.0))));
    assert_eq!(parse_expression("+ 123.f"), Ok(prefix("+", factor(123.0))));
    assert_eq!(parse_expression("-123.f"), Ok(prefix("-", factor(123.0))));
    assert_eq!(parse_expression("123.456f"), Ok(factor(123.456)));
    assert_eq!(parse_expression(" .456f"), Ok(factor(0.456)));
    assert_eq!(parse_expression(" 0.456f "), Ok(factor(0.456)));
    assert_eq!(parse_expression(" 0.f"), Ok(factor(0.0)));
    assert_eq!(parse_expression("-0.f"), Ok(prefix("-", factor(0.0))));

    assert!(matches!(parse_expression("45 f"), Err(_)));

    assert_eq!(parse_expression("1+ 2"), Ok(infix("+", num(1.0), num(2.0))));

    assert_eq!(
        parse_expression("1+ 2* 3"),
        Ok(infix("+", num(1.0), infix("*", num(2.0), num(3.0))))
    );

    assert_eq!(
        parse_expression("(1+ 2)* 3"),
        Ok(infix("*", infix("+", num(1.0), num(2.0)), num(3.0)))
    );

    assert_eq!(
        parse_expression(" 123 as factor"),
        Ok(coerce(num(123.0), "factor"))
    );

    assert_eq!(
        parse_expression("(123  ) as factor"),
        Ok(coerce(num(123.0), "factor"))
    );

    assert_eq!(
        parse_expression("( 123 as factor  )"),
        Ok(coerce(num(123.0), "factor"))
    );

    assert_eq!(
        parse_expression("2 * 3 as factor"),
        Ok(coerce(infix("*", num(2.0), num(3.0)), "factor"))
    );

    assert_eq!(
        parse_expression("2 * (3 as factor)"),
        Ok(infix("*", num(2.0), coerce(num(3.0), "factor")))
    );

    assert_eq!(
        parse_expression("fn(s) s"),
        Ok(func(vec!["s"], Expr::Id("s")))
    );

    assert_eq!(
        parse_expression("fn ( s, kick , pa_ram, ) (23.0 + bla)"),
        Ok(func(
            vec!["s", "kick", "pa_ram"],
            infix("+", num(23.0), Expr::Id("bla"))
        ))
    );

    assert_eq!(
        parse_statement("let hello = 5f;"),
        Ok(Stmt::Def("hello", factor(5.0)))
    );

    assert_eq!(
        parse_expression("{ 123 }"),
        Ok(Expr::Block(vec![], Some(Box::new(num(123.0)))))
    );
    assert_eq!(
        parse_expression("{ ;123 }"),
        Ok(Expr::Block(vec![Stmt::Noop], Some(Box::new(num(123.0)))))
    );

    assert!(matches!(parse_expression("{ ;123 ; }"), Err(_)));

    assert_eq!(
        parse_expression("{ let v = 5; }"),
        Ok(Expr::Block(vec![Stmt::Def("v", num(5.0))], None))
    );
    assert_eq!(
        parse_expression("{ let v = 5 ;let h=8f; }"),
        Ok(Expr::Block(
            vec![Stmt::Def("v", num(5.0)), Stmt::Def("h", Expr::Factor(8.0))],
            None
        ))
    );
    assert_eq!(
        parse_expression("{ let v = 5 ;let h=8f;5.0 }"),
        Ok(Expr::Block(
            vec![Stmt::Def("v", num(5.0)), Stmt::Def("h", Expr::Factor(8.0))],
            Some(Box::new(num(5.0)))
        ))
    );

    assert_eq!(
        parse_expression(
            "fn (a, b) {
                let len = 1.1f;
                23.0
            }"
        ),
        Ok(func(
            vec!["a", "b"],
            Expr::Block(
                vec![Stmt::Def("len", factor(1.1)),],
                Some(Box::new(num(23.0)))
            )
        ))
    );

    assert_eq!(
        parse_expression(
            "fn (a, b) {
                let len = 1.1f;
                return 4;
                23.0
            }"
        ),
        Ok(func(
            vec!["a", "b"],
            Expr::Block(
                vec![Stmt::Def("len", factor(1.1)), Stmt::Ret(num(4.0)),],
                Some(Box::new(num(23.0)))
            )
        ))
    );
}

fn main() {
    println!("hello world");
}
