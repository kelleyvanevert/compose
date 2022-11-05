use std::ops::Add;

use anyhow::{anyhow, Ok, Result};

pub struct Parser<'p, T>(Box<dyn Fn(&str) -> Result<(T, usize)> + 'p>);

impl<'p, A: 'p> Parser<'p, A> {
    #[allow(unused)]
    fn parse(&self, input: &str) -> Result<(A, usize)> {
        let p = self.0.as_ref();
        p(input)
    }

    #[allow(unused)]
    fn seq<B: 'p>(self, next: impl Into<Parser<'p, B>>) -> Parser<'p, (A, B)> {
        seq(self, next)
    }

    #[allow(unused)]
    fn map<B: 'p>(self, f: fn(A) -> B) -> Parser<'p, B> {
        map(self, f)
    }

    #[allow(unused)]
    fn skip<B: 'p>(self, next: impl Into<Parser<'p, B>>) -> Parser<'p, A> {
        skip(self, next)
    }
}

fn exact(str: &str) -> Parser<'static, String> {
    let str = str.to_owned();
    let cb = move |input: &str| {
        if input.starts_with(&str) {
            Ok((str.clone(), str.len()))
        } else {
            Err(anyhow!("could not parse"))
        }
    };
    Parser(Box::new(cb))
}

fn seq<'p, A: 'p, B: 'p>(
    pa: impl Into<Parser<'p, A>>,
    pb: impl Into<Parser<'p, B>>,
) -> Parser<'p, (A, B)> {
    let pa: Parser<'p, A> = pa.into();
    let pb: Parser<'p, B> = pb.into();

    Parser(Box::new(move |input: &str| match pa.parse(input) {
        Result::Ok((a, ai)) => match pb.parse(&input[ai..]) {
            Result::Ok((b, bi)) => Ok(((a, b), ai + bi)),
            _err => Err(anyhow!("could not parse")),
        },
        _err => Err(anyhow!("could not parse")),
    }))
}

fn map<'p, A: 'p, B: 'p>(pa: impl Into<Parser<'p, A>>, f: fn(A) -> B) -> Parser<'p, B> {
    let pa: Parser<'p, A> = pa.into();

    Parser(Box::new(move |input: &str| match pa.parse(input) {
        Result::Ok((a, ai)) => Ok((f(a), ai)),
        _err => Err(anyhow!("could not parse")),
    }))
}

fn skip<'p, A: 'p, B: 'p>(
    pa: impl Into<Parser<'p, A>>,
    pb: impl Into<Parser<'p, B>>,
) -> Parser<'p, A> {
    seq(pa, pb).map(|(a, _)| a)
}

impl<'p, A: 'p, B: 'p> Add<Parser<'p, B>> for Parser<'p, A> {
    type Output = Parser<'p, (A, B)>;

    fn add(self, next: Parser<'p, B>) -> Self::Output {
        seq(self, next)
    }
}

impl From<&str> for Parser<'_, String> {
    fn from(str: &str) -> Self {
        exact(str)
    }
}

impl From<String> for Parser<'_, String> {
    fn from(str: String) -> Self {
        exact(&str)
    }
}

fn main() {
    // let p = exact("hell".to_owned()).ne;
    // let q = exact("o world".to_owned());
    // let c = seq(p, q);

    let c = seq("he", "llo").skip(" ").map(|(a, b)| a + &b);
    // let c = exact("he").seq("llo").skip(exact(" ")).map(|(a, b)| a + &b);

    println!("{:?}", c.parse("hello world"));
}
