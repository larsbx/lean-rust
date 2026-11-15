import Lean

open Lean

def sort (n : Nat) : Expr :=
  .sort (Nat.rec Level.zero (fun _ l => .succ l) n)

def lam (ty body : Expr) (name : Name := `x) : Expr :=
  .lam name ty body .default

def pi (ty body : Expr) : Expr := .forallE `x ty body .default
def letIn (ty value body : Expr) : Expr := .letE `x ty value body false
def v := Expr.bvar

partial def encode : Expr → String
  | .bvar n => s!"v{n}"
  | .sort l => "s" ++ toString (levelNumber l)
  | .app f x => s!"a {encode f} {encode x}"
  | .lam _ ty body _ => s!"l {encode ty} {encode body}"
  | .forallE _ ty body _ => s!"p {encode ty} {encode body}"
  | .letE _ ty value body _ => s!"t {encode ty} {encode value} {encode body}"
  | _ => panic! "expression outside oracle encoding"
where
  levelNumber : Level → Nat
    | .zero => 0
    | .succ l => levelNumber l + 1
    | _ => panic! "universe outside oracle encoding"

def checked (operation : String) (result : Except Kernel.Exception α) : IO α :=
  match result with
  | .ok result => pure result
  | .error _ => throw (IO.userError s!"Lean kernel failed: {operation}")

-- Both wrappers preserve the type of a term in the surrounding context.
def expand (ty : Expr) : Nat → Expr → Expr
  | 0, term => term
  | n + 1, term =>
    let previous := expand ty n term
    if n % 2 == 0 then .app (lam ty (v 0)) previous
    else letIn ty previous (v 0)

def bindTypes (ty : Expr) (depth : Nat) (body : Expr) : Expr :=
  Nat.rec body (fun _ inner => lam ty inner) depth

def conversionRow (env : Environment) (name : String) (left right : Expr)
    (expectedLean expectedRust : Bool) (requireSameType : Bool := false) : IO String := do
  let leftType ← checked name (Kernel.check env {} left)
  let rightType ← checked name (Kernel.check env {} right)
  let sameType ← checked name (Kernel.isDefEq env {} leftType rightType)
  if (expectedLean || requireSameType) && !sameType then
    throw (IO.userError s!"expected equal types: {name}")
  let actual ← checked name (Kernel.isDefEq env {} left right)
  unless actual == expectedLean do
    throw (IO.userError s!"unexpected conversion result: {name}: {actual}")
  pure (String.intercalate "\t"
    ["eq", name, toString actual, toString expectedRust, encode left, encode right])

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "expected output path")
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {}
  let prop := sort 0
  let ty := sort 1
  let id := lam ty (v 0)
  let fty := pi ty ty
  let pairs := [
    ("beta", .app id prop, prop, true, true),
    ("zeta", letIn ty prop (v 0), prop, true, true),
    ("alpha", lam ty (v 0) `left, lam ty (v 0) `right, true, true),
    ("beta-under-pi", pi ty (.app id (v 0)), pi ty (v 0), true, true),
    ("dependent-beta", .app (lam ty (lam (v 0) (v 0))) prop, lam prop (v 0), true, true),
    ("capture-under-lambda",
      lam ty (.app (lam ty (lam ty (v 1))) (v 0)),
      lam ty (lam ty (v 1)), true, true),
    ("shadowing", lam ty (lam ty (v 1)), lam ty (lam ty (v 0)), false, false),
    ("different-sorts", ty, sort 2, false, false),
    ("different-domains", lam ty (v 0), lam (sort 2) (v 0), false, false),
    ("eta-outside-fragment", lam fty (v 0), lam fty (lam ty (.app (v 1) (v 0))), true, false),
    ("proof-irrelevance-outside-fragment",
      lam prop (lam (v 0) (lam (v 1) (v 1))),
      lam prop (lam (v 0) (lam (v 1) (v 0))), true, false)
  ]
  let mut rows := #[]
  for (name, left, right, expectedLean, expectedRust) in pairs do
    rows := rows.push (← conversionRow env name left right expectedLean expectedRust)
  for depth in [2:10] do
    for steps in [1:7] do
      let name := s!"generated-{depth}-{steps}"
      let first := bindTypes ty depth (v (depth - 1))
      let last := bindTypes ty depth (v 0)
      let expandedFirst := bindTypes ty depth (expand ty steps (v (depth - 1)))
      let expandedLast := bindTypes ty depth (expand ty steps (v 0))
      rows := rows.push (← conversionRow env (name ++ "-first") expandedFirst first true true)
      rows := rows.push (← conversionRow env (name ++ "-last") last expandedLast true true)
      rows := rows.push (← conversionRow env (name ++ "-distinct") expandedFirst expandedLast false false true)
  let heads := [
    ("beta-head", .app id prop),
    ("zeta-head", letIn ty prop (v 0)),
    ("whnf-stops-under-lambda", lam ty (.app id (v 0))),
    ("let-in-function-position", .app (letIn fty id (v 0)) prop)
  ]
  for (name, input) in heads do
    let _ ← checked name (Kernel.check env {} input)
    let actual ← checked name (Kernel.whnf env {} input)
    rows := rows.push (String.intercalate "\t" ["whnf", name, encode input, encode actual])
  let instances := [
    ("lift-open-replacement", 1, lam ty (v 1), v 0),
    ("preserve-inner-and-decrement-outer", 1, pi (v 1) (.app (v 0) (v 2)), v 0),
    ("let-scopes", 2, letIn (v 0) (v 2) (.app (v 1) (v 0)), v 1),
    ("lift-cutoff", 1, lam ty (v 1), lam ty (.app (v 0) (v 1)))
  ]
  for (name, ambient, body, value) in instances do
    rows := rows.push (String.intercalate "\t"
      ["inst", name, toString ambient, encode body, encode value, encode (body.instantiate1 value)])
  IO.FS.writeFile output (String.intercalate "\n" rows.toList ++ "\n")
