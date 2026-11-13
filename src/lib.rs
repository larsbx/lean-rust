#![forbid(unsafe_code)]
//! Bounded, syntactic beta/zeta conversion for a fragment of Lean expressions.

use std::sync::Arc;

pub const MAX_HEIGHT: u16 = 128;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    OutOfScope,
    HeightLimit,
    BudgetExhausted,
    IndexOverflow,
}

#[derive(Debug, Clone)]
pub struct Expr(Arc<Node>);

#[derive(Debug)]
struct Node {
    kind: Kind,
    height: u16,
}

#[derive(Debug)]
pub enum Kind {
    BVar(u32),
    /// A universe obtained by applying successor to zero this many times.
    Sort(u32),
    App(Expr, Expr),
    Lam(Expr, Expr),
    Pi(Expr, Expr),
    Let(Expr, Expr, Expr),
}

impl Expr {
    pub fn new(kind: Kind) -> Result<Self, Error> {
        use Kind::*;
        let child_height = match &kind {
            BVar(_) | Sort(_) => 0,
            App(a, b) | Lam(a, b) | Pi(a, b) => a.0.height.max(b.0.height),
            Let(ty, value, body) => ty.0.height.max(value.0.height).max(body.0.height),
        };
        let height = child_height + 1;
        if height > MAX_HEIGHT {
            return Err(Error::HeightLimit);
        }
        Ok(Self(Arc::new(Node { kind, height })))
    }

    pub fn kind(&self) -> &Kind {
        &self.0.kind
    }

    fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

/// Each operation gets a fresh work budget, charged per traversal or reduction step.
/// Exhaustion is an error and is never interpreted as inequality.
pub struct Kernel {
    steps: u64,
}

struct Work(u64);

impl Work {
    fn step(&mut self) -> Result<(), Error> {
        self.0 = self.0.checked_sub(1).ok_or(Error::BudgetExhausted)?;
        Ok(())
    }
}

impl Kernel {
    pub fn new(steps: u64) -> Self {
        Self { steps }
    }

    /// Remove one binder. The body is scoped in `ambient + 1`, the value in `ambient`.
    pub fn instantiate(&self, body: &Expr, value: &Expr, ambient: u32) -> Result<Expr, Error> {
        let mut work = Work(self.steps);
        validate(body, u64::from(ambient) + 1, &mut work)?;
        validate(value, u64::from(ambient), &mut work)?;
        instantiate(body, value, &mut work)
    }

    /// Reduce only at the head, following the function side of applications.
    pub fn whnf(&self, expr: &Expr, ambient: u32) -> Result<Expr, Error> {
        let mut work = Work(self.steps);
        validate(expr, u64::from(ambient), &mut work)?;
        whnf(expr, &mut work, 1)
    }

    pub fn normalize(&self, expr: &Expr, ambient: u32) -> Result<Expr, Error> {
        let mut work = Work(self.steps);
        validate(expr, u64::from(ambient), &mut work)?;
        normalize(expr, &mut work, 1)
    }

    /// Compare beta/zeta normal forms, ignoring binder names by construction.
    /// This is a syntactic conversion test and does not check expression types.
    pub fn def_eq(&self, left: &Expr, right: &Expr, ambient: u32) -> Result<bool, Error> {
        let mut work = Work(self.steps);
        validate(left, u64::from(ambient), &mut work)?;
        validate(right, u64::from(ambient), &mut work)?;
        if left.same_node(right) {
            return Ok(true);
        }
        let left = normalize(left, &mut work, 1)?;
        let right = normalize(right, &mut work, 1)?;
        equal(&left, &right, &mut work)
    }
}

/// Traverse immediate children. The domain, let type and let value sit outside
/// their binder. Pass the child's additional binder depth to the visitor.
fn map_children(
    expr: &Expr,
    mut visit: impl FnMut(&Expr, u32) -> Result<Expr, Error>,
) -> Result<Expr, Error> {
    use Kind::*;
    fn pair(
        expr: &Expr,
        left: &Expr,
        right: &Expr,
        right_depth: u32,
        visit: &mut impl FnMut(&Expr, u32) -> Result<Expr, Error>,
        build: impl FnOnce(Expr, Expr) -> Kind,
    ) -> Result<Expr, Error> {
        let new_left = visit(left, 0)?;
        let new_right = visit(right, right_depth)?;
        if new_left.same_node(left) && new_right.same_node(right) {
            return Ok(expr.clone());
        }
        Expr::new(build(new_left, new_right))
    }
    match expr.kind() {
        BVar(_) | Sort(_) => Ok(expr.clone()),
        App(f, x) => pair(expr, f, x, 0, &mut visit, App),
        Lam(ty, body) => pair(expr, ty, body, 1, &mut visit, Lam),
        Pi(ty, body) => pair(expr, ty, body, 1, &mut visit, Pi),
        Let(ty, value, body) => {
            let new_ty = visit(ty, 0)?;
            let new_value = visit(value, 0)?;
            let new_body = visit(body, 1)?;
            if new_ty.same_node(ty) && new_value.same_node(value) && new_body.same_node(body) {
                return Ok(expr.clone());
            }
            Expr::new(Let(new_ty, new_value, new_body))
        }
    }
}

fn validate(expr: &Expr, ambient: u64, work: &mut Work) -> Result<(), Error> {
    use Kind::*;
    work.step()?;
    match expr.kind() {
        BVar(i) if u64::from(*i) >= ambient => Err(Error::OutOfScope),
        BVar(_) | Sort(_) => Ok(()),
        App(f, x) => {
            validate(f, ambient, work)?;
            validate(x, ambient, work)
        }
        Lam(ty, body) | Pi(ty, body) => {
            validate(ty, ambient, work)?;
            validate(body, ambient + 1, work)
        }
        Let(ty, value, body) => {
            validate(ty, ambient, work)?;
            validate(value, ambient, work)?;
            validate(body, ambient + 1, work)
        }
    }
}

fn lift(expr: &Expr, amount: u32, cutoff: u32, work: &mut Work) -> Result<Expr, Error> {
    work.step()?;
    if amount == 0 {
        return Ok(expr.clone());
    }
    if let Kind::BVar(i) = expr.kind() {
        return if *i >= cutoff {
            Expr::new(Kind::BVar(i.checked_add(amount).ok_or(Error::IndexOverflow)?))
        } else {
            Ok(expr.clone())
        };
    }
    map_children(expr, |child, binders| lift(child, amount, cutoff + binders, work))
}

fn instantiate(body: &Expr, value: &Expr, work: &mut Work) -> Result<Expr, Error> {
    fn visit(expr: &Expr, value: &Expr, depth: u32, work: &mut Work) -> Result<Expr, Error> {
        work.step()?;
        if let Kind::BVar(i) = expr.kind() {
            return match i.cmp(&depth) {
                std::cmp::Ordering::Less => Ok(expr.clone()),
                std::cmp::Ordering::Equal => lift(value, depth, 0, work),
                std::cmp::Ordering::Greater => Expr::new(Kind::BVar(i - 1)),
            };
        }
        map_children(expr, |child, binders| visit(child, value, depth + binders, work))
    }
    visit(body, value, 0, work)
}

fn whnf(expr: &Expr, work: &mut Work, depth: u16) -> Result<Expr, Error> {
    if depth > MAX_HEIGHT {
        return Err(Error::HeightLimit);
    }
    let mut head = expr.clone();
    loop {
        work.step()?;
        match head.kind() {
            Kind::Let(_, value, body) => head = instantiate(body, value, work)?,
            Kind::App(f, x) => {
                let f_head = whnf(f, work, depth + 1)?;
                if let Kind::Lam(_, body) = f_head.kind() {
                    head = instantiate(body, x, work)?;
                } else if f_head.same_node(f) {
                    return Ok(head);
                } else {
                    return Expr::new(Kind::App(f_head, x.clone()));
                }
            }
            _ => return Ok(head),
        }
    }
}

fn normalize(expr: &Expr, work: &mut Work, depth: u16) -> Result<Expr, Error> {
    let head = whnf(expr, work, depth)?;
    map_children(&head, |child, _| normalize(child, work, depth + 1))
}

fn equal(left: &Expr, right: &Expr, work: &mut Work) -> Result<bool, Error> {
    use Kind::*;
    work.step()?;
    if left.same_node(right) {
        return Ok(true);
    }
    match (left.kind(), right.kind()) {
        (BVar(i), BVar(j)) | (Sort(i), Sort(j)) => Ok(i == j),
        (App(a, b), App(c, d)) | (Lam(a, b), Lam(c, d)) | (Pi(a, b), Pi(c, d)) => {
            Ok(equal(a, c, work)? && equal(b, d, work)?)
        }
        // The caller compares normal forms, which have no let nodes.
        _ => Ok(false),
    }
}
