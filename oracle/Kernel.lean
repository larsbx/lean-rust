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
    let _ ← checked name (Kernel.check env {} left)
    let _ ← checked name (Kernel.check env {} right)
    let actual ← checked name (Kernel.isDefEq env {} left right)
    unless actual == expectedLean do
      throw (IO.userError s!"unexpected conversion result: {name}: {actual}")
    rows := rows.push (String.intercalate "\t"
      ["eq", name, toString actual, toString expectedRust, encode left, encode right])
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
