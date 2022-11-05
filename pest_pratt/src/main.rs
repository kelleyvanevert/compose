#[macro_use]
extern crate pest_derive;

use pest::{error::Error, iterators::Pair, Parser};
use std::fs;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct MyParser;

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
}

#[derive(Debug, PartialEq)]
enum Stmt<'a> {
    Def(&'a str, Expr<'a>),
    Ret(Expr<'a>),
}

fn parse_into_expr<'a>(pair: Pair<'a, Rule>) -> Expr<'a> {
    match pair.as_rule() {
        Rule::id => Expr::Id(pair.as_str()),
        Rule::sample_input => Expr::SampleInput,
        Rule::envelope_input => Expr::EnvelopeInput,
        Rule::pattern_input => Expr::PatternInput,
        Rule::number => Expr::Number(pair.as_str().parse::<f64>().unwrap()),
        Rule::factor => Expr::Factor(pair.into_inner().as_str().parse::<f64>().unwrap()),
        Rule::coercion => {
            let mut inner = pair.into_inner();
            let expr = parse_into_expr(inner.next().unwrap());
            let typename = inner.next().unwrap().as_str();

            Expr::Coercion(Box::new(expr), typename)
        }
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

fn parse_into_stmt(pair: Pair<Rule>) -> Stmt {
    match pair.as_rule() {
        Rule::def => {
            let mut inner = pair.into_inner();
            let id = inner.next().unwrap().as_str();
            let id = id.trim(); // WHAT
            let expr = parse_into_expr(inner.next().unwrap());
            Stmt::Def(id, expr)
        }
        Rule::ret => Stmt::Ret(parse_into_expr(pair.into_inner().next().unwrap())),
        r => unreachable!("not a stmt: {:?}", r),
    }
}

#[allow(unused)]
fn parse_expression(input: &str) -> Result<Expr, Error<Rule>> {
    let mut pairs = MyParser::parse(Rule::expression, input)?;
    let value = pairs.next().unwrap();

    Ok(parse_into_expr(value))
}

#[allow(unused)]
fn parse_statement(input: &str) -> Result<Stmt, Error<Rule>> {
    let mut pairs = MyParser::parse(Rule::statement, input)?;
    let value = pairs.next().unwrap();

    Ok(parse_into_stmt(value))
}

#[test]
fn test_parse() {
    assert_eq!(parse_expression("hello"), Ok(Expr::Id("hello")));
    assert_eq!(parse_expression("  bla_"), Ok(Expr::Id("bla_")));
    assert_eq!(parse_expression(" bla_bla  "), Ok(Expr::Id("bla_bla")));

    assert!(matches!(parse_expression("_bla"), Err(_)));
    assert!(matches!(parse_expression("Bla"), Err(_)));

    assert_eq!(parse_expression("123"), Ok(Expr::Number(123.0)));
    assert_eq!(parse_expression("+123"), Ok(Expr::Number(123.0)));
    assert_eq!(parse_expression(" -123"), Ok(Expr::Number(-123.0)));
    assert_eq!(parse_expression(" 123."), Ok(Expr::Number(123.0)));
    assert_eq!(parse_expression(" 123.456"), Ok(Expr::Number(123.456)));
    assert_eq!(parse_expression(".456"), Ok(Expr::Number(0.456)));
    assert_eq!(parse_expression("0.456  "), Ok(Expr::Number(0.456)));
    assert_eq!(parse_expression("0. "), Ok(Expr::Number(0.0)));
    assert_eq!(parse_expression("-0."), Ok(Expr::Number(0.0)));

    assert!(matches!(parse_expression("."), Err(_)));

    assert_eq!(parse_expression("(123 ) "), Ok(Expr::Number(123.0)));

    assert_eq!(parse_expression("123f"), Ok(Expr::Factor(123.0)));
    assert_eq!(parse_expression("123.f"), Ok(Expr::Factor(123.0)));
    assert_eq!(parse_expression(" +123.f"), Ok(Expr::Factor(123.0)));
    assert_eq!(parse_expression("-123.f"), Ok(Expr::Factor(-123.0)));
    assert_eq!(parse_expression("123.456f"), Ok(Expr::Factor(123.456)));
    assert_eq!(parse_expression(" .456f"), Ok(Expr::Factor(0.456)));
    assert_eq!(parse_expression(" 0.456f"), Ok(Expr::Factor(0.456)));
    assert_eq!(parse_expression(" 0.f"), Ok(Expr::Factor(0.0)));
    assert_eq!(parse_expression("-0.f"), Ok(Expr::Factor(0.0)));

    assert!(matches!(parse_expression("45 f"), Err(_)));

    assert_eq!(
        parse_expression(" 123 as factor"),
        Ok(Expr::Coercion(Box::new(Expr::Number(123.0)), "factor"))
    );
    assert_eq!(
        parse_expression("(123  ) as factor"),
        Ok(Expr::Coercion(Box::new(Expr::Number(123.0)), "factor"))
    );
    assert_eq!(
        parse_expression("( 123 as factor  )"),
        Ok(Expr::Coercion(Box::new(Expr::Number(123.0)), "factor"))
    );

    assert_eq!(
        parse_expression("fn(s) s"),
        Ok(Expr::Function(vec!["s"], Box::new(Expr::Id("s"))))
    );

    assert_eq!(
        parse_expression("fn ( s, kick , pa_ram, ) (23.0)"),
        Ok(Expr::Function(
            vec!["s", "kick", "pa_ram"],
            Box::new(Expr::Number(23.0))
        ))
    );

    assert_eq!(
        parse_statement("let hello = 5f;"),
        Ok(Stmt::Def("hello", Expr::Factor(5.0)))
    );

    assert_eq!(
        parse_expression("{ let v = 5; }"),
        Ok(Expr::Block(vec![Stmt::Def("v", Expr::Number(5.0))], None))
    );
    assert_eq!(
        parse_expression("{ let v = 5 ;let h=8f; }"),
        Ok(Expr::Block(
            vec![
                Stmt::Def("v", Expr::Number(5.0)),
                Stmt::Def("h", Expr::Factor(8.0))
            ],
            None
        ))
    );
    assert_eq!(
        parse_expression("{ let v = 5 ;let h=8f;5.0 }"),
        Ok(Expr::Block(
            vec![
                Stmt::Def("v", Expr::Number(5.0)),
                Stmt::Def("h", Expr::Factor(8.0))
            ],
            Some(Box::new(Expr::Number(5.0)))
        ))
    );

    assert_eq!(
        parse_expression(
            "fn (a, b) {
                let len = 1.1f;
                23.0
            }"
        ),
        Ok(Expr::Function(
            vec!["a", "b"],
            Box::new(Expr::Block(
                vec![Stmt::Def("len", Expr::Factor(1.1)),],
                Some(Box::new(Expr::Number(23.0)))
            ))
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
        Ok(Expr::Function(
            vec!["a", "b"],
            Box::new(Expr::Block(
                vec![
                    Stmt::Def("len", Expr::Factor(1.1)),
                    Stmt::Ret(Expr::Number(4.0)),
                ],
                Some(Box::new(Expr::Number(23.0)))
            ))
        ))
    );
}

fn main() {
    println!("{:?}", parse_expression("hello"));
}
