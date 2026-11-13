use lean_rust_kernel::{Error, Expr, Kernel, Kind, MAX_HEIGHT};

fn node(kind: Kind) -> Expr {
    Expr::new(kind).unwrap()
}

fn parse(input: &str) -> Expr {
    fn term(tokens: &mut std::str::SplitWhitespace<'_>) -> Expr {
        let token = tokens.next().expect("truncated oracle expression");
        node(match token {
            "a" => Kind::App(term(tokens), term(tokens)),
            "l" => Kind::Lam(term(tokens), term(tokens)),
            "p" => Kind::Pi(term(tokens), term(tokens)),
            "t" => Kind::Let(term(tokens), term(tokens), term(tokens)),
            _ if token.starts_with('v') => Kind::BVar(token[1..].parse().unwrap()),
            _ if token.starts_with('s') => Kind::Sort(token[1..].parse().unwrap()),
            _ => panic!("unknown oracle token: {token}"),
        })
    }
    let mut tokens = input.split_whitespace();
    let expr = term(&mut tokens);
    assert!(tokens.next().is_none(), "trailing oracle tokens");
    expr
}

// Structural equality independent of the evaluator. In particular it does
// not allow the WHNF result to pass by reducing extra redexes.
fn structural(left: &Expr, right: &Expr) -> bool {
    use Kind::*;
    match (left.kind(), right.kind()) {
        (BVar(i), BVar(j)) | (Sort(i), Sort(j)) => i == j,
        (App(a, b), App(c, d)) | (Lam(a, b), Lam(c, d)) | (Pi(a, b), Pi(c, d)) => {
            structural(a, c) && structural(b, d)
        }
        (Let(a, b, c), Let(d, e, f)) => structural(a, d) && structural(b, e) && structural(c, f),
        _ => false,
    }
}

#[test]
fn pinned_lean_oracle() {
    let kernel = Kernel::new(100_000);
    let mut count = 0;
    for row in include_str!("../oracle/cases.tsv").lines() {
        let fields: Vec<_> = row.split('\t').collect();
        match fields.as_slice() {
            ["eq", name, lean, rust, left, right] => {
                let expected = rust.parse().unwrap();
                assert_eq!(kernel.def_eq(&parse(left), &parse(right), 0), Ok(expected), "{name}");
                assert_eq!(*lean != *rust, name.ends_with("-outside-fragment"), "{name}");
            }
            ["whnf", name, input, expected] => {
                let actual = kernel.whnf(&parse(input), 0).unwrap();
                assert!(structural(&actual, &parse(expected)), "{name}");
            }
            ["inst", name, ambient, body, value, expected] => {
                let actual = kernel.instantiate(&parse(body), &parse(value), ambient.parse().unwrap()).unwrap();
                assert!(structural(&actual, &parse(expected)), "{name}");
            }
            _ => panic!("invalid oracle row: {row}"),
        }
        count += 1;
    }
    assert_eq!(count, 19);
}

struct Generator(u64);

impl Generator {
    fn next(&mut self) -> u32 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
        (self.0 >> 32) as u32
    }

    // Generate scoped expressions with terminating redexes. Applications use
    // a bound variable as head or a lambda that ignores its argument.
    fn term(&mut self, size: u32, scope: u32) -> Expr {
        if size == 0 {
            return node(if scope > 0 && self.next() % 2 == 0 {
                Kind::BVar(self.next() % scope)
            } else {
                Kind::Sort(self.next() % 4)
            });
        }
        let smaller = size - 1;
        node(match self.next() % 5 {
            0 => Kind::Lam(self.term(smaller, scope), self.term(smaller, scope + 1)),
            1 => Kind::Pi(self.term(smaller, scope), self.term(smaller, scope + 1)),
            2 => Kind::Let(parse("s1"), parse("s0"), self.term(smaller, scope + 1)),
            3 if scope > 0 => Kind::App(node(Kind::BVar(self.next() % scope)), self.term(smaller, scope)),
            _ => Kind::App(node(Kind::Lam(parse("s1"), parse("s0"))), self.term(smaller, scope)),
        })
    }
}

#[test]
fn generated_normalization_and_conversion_properties() {
    let kernel = Kernel::new(100_000);
    let mut generator = Generator(0xd57d_d6a1_2e2a_aa09);
    for index in 0..1024 {
        let ambient = index % 4;
        let term = generator.term(index % 7, ambient);
        let normal = kernel.normalize(&term, ambient).unwrap();
        assert!(structural(&normal, &kernel.normalize(&normal, ambient).unwrap()));
        assert_eq!(kernel.def_eq(&term, &normal, ambient), Ok(true));
        assert_eq!(kernel.def_eq(&normal, &term, ambient), Ok(true));
        let beta = node(Kind::App(parse("l s1 v0"), term));
        let zeta = node(Kind::Let(parse("s1"), beta.clone(), parse("v0")));
        assert_eq!(kernel.def_eq(&beta, &zeta, ambient), Ok(true));
        assert_eq!(kernel.def_eq(&zeta, &normal, ambient), Ok(true));
    }
}

#[test]
fn scope_validation_includes_unreduced_children() {
    let kernel = Kernel::new(100_000);
    for input in ["v0", "l v0 v0", "p v0 v0", "t s1 v0 v0", "t v0 s0 v0", "a l s1 s0 v0"] {
        let expr = parse(input);
        assert_eq!(kernel.whnf(&expr, 0).unwrap_err(), Error::OutOfScope, "{input}");
        assert_eq!(kernel.def_eq(&expr, &expr, 0), Err(Error::OutOfScope), "{input}");
    }
    assert_eq!(kernel.instantiate(&parse("v0"), &parse("v0"), 0).unwrap_err(), Error::OutOfScope);
}

#[test]
fn budget_height_and_overflow_fail_explicitly() {
    let kernel = Kernel::new(1000);
    let omega = parse("a l s1 a v0 v0 l s1 a v0 v0");
    assert_eq!(kernel.normalize(&omega, 0).unwrap_err(), Error::BudgetExhausted);
    assert_eq!(kernel.def_eq(&omega, &parse("s0"), 0), Err(Error::BudgetExhausted));
    let mut deep = parse("s0");
    for _ in 1..MAX_HEIGHT {
        deep = node(Kind::Lam(parse("s1"), deep));
    }
    assert_eq!(Expr::new(Kind::Lam(parse("s1"), deep)).unwrap_err(), Error::HeightLimit);
    let value = node(Kind::BVar(u32::MAX - 1));
    assert_eq!(
        kernel.instantiate(&parse("l s1 l s1 v2"), &value, u32::MAX).unwrap_err(),
        Error::IndexOverflow
    );
}

#[test]
fn shared_node_has_different_scope_at_different_depths() {
    let kernel = Kernel::new(1000);
    let shared = parse("v0");
    let binder = node(Kind::Lam(parse("s1"), shared.clone()));
    let body = node(Kind::App(shared, binder));
    let actual = kernel.instantiate(&body, &parse("s0"), 0).unwrap();
    assert!(structural(&actual, &parse("a s0 l s1 v0")));
}
