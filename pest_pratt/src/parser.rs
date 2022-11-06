use pest::{
    error::Error,
    iterators::{Pair, Pairs},
    pratt_parser::{Assoc, Op, PrattParser},
    Parser,
};

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct MyParser;

lazy_static! {
    static ref PRATT: PrattParser<Rule> = PrattParser::new()
        .op(Op::postfix(Rule::coerce))
        .op(Op::infix(Rule::seq, Assoc::Left))
        .op(Op::infix(Rule::add, Assoc::Left) | Op::infix(Rule::sub, Assoc::Left))
        .op(Op::infix(Rule::mul, Assoc::Left) | Op::infix(Rule::div, Assoc::Left))
        .op(Op::infix(Rule::pow, Assoc::Right))
        .op(Op::postfix(Rule::fac))
        .op(Op::prefix(Rule::pos) | Op::prefix(Rule::neg));
}

#[allow(unused)]
#[derive(Debug, PartialEq)]
pub enum Expr<'a> {
    Id(&'a str),
    Input {
        kind: &'a str,
        save: Option<&'a str>,
    },
    Number(f64),
    Factor(f64),
    Coercion(Box<Expr<'a>>, &'a str),
    Function(Vec<&'a str>, Box<Expr<'a>>),
    Block(Vec<Stmt<'a>>, Option<Box<Expr<'a>>>),
    Prefix(&'a str, Box<Expr<'a>>),
    Postfix(&'a str, Box<Expr<'a>>),
    Infix(&'a str, Box<Expr<'a>>, Box<Expr<'a>>),
}

#[allow(unused)]
#[derive(Debug, PartialEq)]
pub enum Stmt<'a> {
    Def(&'a str, Expr<'a>),
    Ret(Expr<'a>),
    Noop,
}

fn parse_into_expr<'a>(pair: Pair<'a, Rule>) -> Expr<'a> {
    match pair.as_rule() {
        Rule::expr => parse_pairs_into_expr(pair.into_inner()),
        Rule::id => Expr::Id(pair.as_str()),
        Rule::input => {
            let mut inner = pair.into_inner();
            let kind = match inner.next().unwrap().as_str().chars().next().unwrap() {
                'E' => "envelope",
                'S' => "sample",
                'P' => "pattern",
                'C' => "chord",
                _ => unreachable!(),
            };
            let save = inner
                .next()
                .map(|p| p.into_inner().next().unwrap().as_str());

            Expr::Input { kind, save }
        }
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
pub fn parse_expression(input: &str) -> Result<Expr, Error<Rule>> {
    let pairs = MyParser::parse(Rule::entry_expression, input)?;

    Ok(parse_pairs_into_expr(pairs))
}

#[allow(unused)]
pub fn parse_statement(input: &str) -> Result<Stmt, Error<Rule>> {
    let mut pairs = MyParser::parse(Rule::entry_statement, input)?;
    let value = pairs.next().unwrap();

    Ok(parse_into_stmt(value))
}

#[test]
fn test_parse() {
    fn id<'a>(id: &'a str) -> Expr<'a> {
        Expr::Id(id)
    }

    fn def<'a>(id: &'a str, a: Expr<'a>) -> Stmt<'a> {
        Stmt::Def(id, a)
    }

    fn ret<'a>(a: Expr<'a>) -> Stmt<'a> {
        Stmt::Ret(a)
    }

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

    fn block<'a>(stmts: Vec<Stmt<'a>>, ret: Option<Expr<'a>>) -> Expr<'a> {
        Expr::Block(stmts, ret.map(Box::new))
    }

    fn input<'a>(kind: &'a str, save: Option<&'a str>) -> Expr<'a> {
        Expr::Input { kind, save }
    }

    assert_eq!(parse_expression("E"), Ok(input("envelope", None)));
    assert_eq!(parse_expression("E@3"), Ok(input("envelope", Some("3"))));
    assert_eq!(parse_expression(" E@3 "), Ok(input("envelope", Some("3"))));
    assert!(matches!(parse_expression("E @3"), Err(_)));
    assert!(matches!(parse_expression("E@ 3"), Err(_)));
    assert!(matches!(parse_expression("E @ 3"), Err(_)));

    assert_eq!(parse_expression("hello"), Ok(id("hello")));
    assert_eq!(parse_expression("  bla_"), Ok(id("bla_")));
    assert_eq!(parse_expression(" bla_bla  "), Ok(id("bla_bla")));

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

    assert_eq!(parse_expression("123!"), Ok(postfix("!", num(123.0))));
    assert_eq!(
        parse_expression("123 as factor!"),
        Ok(postfix("!", coerce(num(123.0), "factor")))
    );
    assert_eq!(
        parse_expression("(123 as factor)!"),
        Ok(postfix("!", coerce(num(123.0), "factor")))
    );

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
        parse_expression("E++ 2"),
        Ok(infix("++", input("envelope", None), num(2.0)))
    );
    assert_eq!(
        parse_expression("E ++ 2 ++ P"),
        Ok(infix(
            "++",
            infix("++", input("envelope", None), num(2.0)),
            input("pattern", None)
        ))
    );
    assert_eq!(
        parse_expression("E ++ (2 ++ P)"),
        Ok(infix(
            "++",
            input("envelope", None),
            infix("++", num(2.0), input("pattern", None))
        ))
    );
    assert_eq!(
        parse_expression("E * 3f ++ 2 ++ P"),
        Ok(infix(
            "++",
            infix(
                "++",
                infix("*", input("envelope", None), factor(3.0)),
                num(2.0)
            ),
            input("pattern", None)
        ))
    );
    assert_eq!(
        parse_expression("E * 3f ++ 2 as pattern ++ P"),
        Ok(infix(
            "++",
            coerce(
                infix(
                    "++",
                    infix("*", input("envelope", None), factor(3.0)),
                    num(2.0)
                ),
                "pattern"
            ),
            input("pattern", None)
        ))
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

    assert_eq!(parse_expression("fn(s) s"), Ok(func(vec!["s"], id("s"))));

    assert_eq!(
        parse_expression("fn ( s, kick , pa_ram, ) (23.0 + bla)"),
        Ok(func(
            vec!["s", "kick", "pa_ram"],
            infix("+", num(23.0), id("bla"))
        ))
    );

    assert_eq!(
        parse_statement("let hello = 5f;"),
        Ok(def("hello", factor(5.0)))
    );

    assert_eq!(
        parse_expression("{ 123 }"),
        Ok(block(vec![], Some(num(123.0))))
    );
    assert_eq!(
        parse_expression("{ ;123 }"),
        Ok(block(vec![Stmt::Noop], Some(num(123.0))))
    );

    assert!(matches!(parse_expression("{ ;123 ; }"), Err(_)));

    assert_eq!(
        parse_expression("{ let v = 5; }"),
        Ok(block(vec![def("v", num(5.0))], None))
    );
    assert_eq!(
        parse_expression("{ let v = 5 ;let h=8f; }"),
        Ok(block(vec![def("v", num(5.0)), def("h", factor(8.0))], None))
    );
    assert_eq!(
        parse_expression("{ let v = 5 ;let h=8f;5.0 }"),
        Ok(block(
            vec![def("v", num(5.0)), def("h", factor(8.0))],
            Some(num(5.0))
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
            block(vec![def("len", factor(1.1)),], Some(num(23.0)))
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
            block(
                vec![def("len", factor(1.1)), ret(num(4.0)),],
                Some(num(23.0))
            )
        ))
    );

    assert_eq!(
        parse_statement(
            "let make_kick = fn (a, b) {
                let len = 1.1f;
                return 4 * S@23;
                23.0
            }; "
        ),
        Ok(def(
            "make_kick",
            func(
                vec!["a", "b"],
                block(
                    vec![
                        def("len", factor(1.1)),
                        ret(infix("*", num(4.0), input("sample", Some("23")))),
                    ],
                    Some(num(23.0))
                )
            )
        ))
    );
}
