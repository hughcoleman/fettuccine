import Mathlib.Tactic
import Fettuccine.Buchberger

open Lean Elab Tactic Meta

namespace GroebnerTactic

private partial def collectFromOrEq (x : Expr) (p : Expr) : MetaM (Option (List Expr)) := do
  let p ← withTransparency .reducible <| whnf p
  if p.isAppOf ``Or then
    let args := p.getAppArgs
    let lhs := args[args.size - 2]!
    let rhs := args[args.size - 1]!
    match (← collectFromOrEq x lhs), (← collectFromOrEq x rhs) with
    | some l₁, some l₂ =>
        return some (l₁ ++ l₂)
    | _, _ =>
        return none
  else if p.isAppOf ``Eq then
    let args := p.getAppArgs
    let lhs := args[args.size - 2]!
    let rhs := args[args.size - 1]!
    if lhs == x then
      return some [rhs]
    else if rhs == x then
      return some [lhs]
    else
      return none
  else if p.isConstOf ``False then
    return some []
  else
    return none

private def unfoldHeadDef (e : Expr) : MetaM Expr := do
  let e ← withTransparency .reducible <| whnf e
  match e.getAppFn with
  | Expr.const c lvls =>
      let ci ← getConstInfo c
      match ci.value? (allowOpaque := true) with
      | some body =>
          let body := body.instantiateLevelParams ci.levelParams lvls
          withTransparency .reducible <| whnf (mkAppN body e.getAppArgs)
      | none =>
          pure e
  | _ =>
      pure e

private partial def collectSetElements (s : Expr) : MetaM (List Expr) := do
  let s ← withTransparency .reducible <| whnf s
  if s.isAppOf ``Set.insert || s.isAppOf ``Insert.insert then
    let args := s.getAppArgs
    let elem := args[args.size - 2]!
    let rest := args[args.size - 1]!
    return elem :: (← collectSetElements rest)
  else if s.isAppOf ``Set.singleton || s.isAppOf ``Singleton.singleton then
    let args := s.getAppArgs
    return [args[args.size - 1]!]
  else if s.isAppOf ``EmptyCollection.emptyCollection then
    return []
  else
    match s with
    | Expr.lam _ _ body _ =>
        match (← collectFromOrEq (Expr.bvar 0) body) with
        | some xs =>
            return xs
        | none =>
            throwError
              "groebnerBasis: expected a finite set literal built from \
              Set.insert/singleton/empty, got:{indentExpr s}"
    | _ =>
        throwError
          "groebnerBasis: expected a finite set literal built from \
          Set.insert/singleton/empty, got:{indentExpr s}"

private def getIdealSpanSet (idealExpr : Expr) : MetaM Expr := do
  let idealExpr ← unfoldHeadDef idealExpr
  if idealExpr.isAppOf ``Ideal.span then
    let args := idealExpr.getAppArgs
    return args[args.size - 1]!
  else
    throwError
      "groebnerBasis: expected an ideal of the form Ideal.span ..., \
      got:{indentExpr idealExpr}"

end GroebnerTactic

/-!
# Groebner Tactic (Scaffold)

This file contains the first parsing scaffold for a `groebnerBasis` tactic.
The tactic currently accepts two identifiers:

* the name of an ideal term/hypothesis
* the name of a monomial order term/hypothesis

At this stage it only elaborates and validates that both inputs are parsable terms,
then emits an informational message.
-/

/--
`groebnerBasis I ord` parses and elaborates `I` and `ord` as terms.

Current behavior:
* unfolds and validates `I` has shape `Ideal.span (...)`
* extracts generators from a finite set literal
* computes `CMvPolynomial.buchbergerAlgorithm (ord := ord) gens 32`
* inserts the computed basis as local definition `G`
* inserts `hG : CMvPolynomial.IsGroebnerBasis₁ (ord := ord) I G` as a scaffolded proof term
-/
syntax (name := groebnerBasisTac) "groebnerBasis " ident term:max : tactic

elab_rules : tactic
  | `(tactic| groebnerBasis $idealName:ident $ordTerm) => do
      let idealExpr ← elabTerm idealName none
      let ordExpr ← elabTerm ordTerm none
      let idealTy ← inferType idealExpr
      let ordTy ← inferType ordExpr
      let setExpr ← GroebnerTactic.getIdealSpanSet idealExpr
      let gens := (← GroebnerTactic.collectSetElements setExpr).reverse
      if gens.isEmpty then
        throwError "groebnerBasis: extracted generator set is empty"
      let genTy ← inferType gens.head!
      let gensExpr ← mkListLit genTy gens
      let gbExpr ← mkAppM ``CMvPolynomial.buchbergerAlgorithm #[ordExpr, gensExpr, mkNatLit 32]
      let gbTy ← inferType gbExpr
      let goal ← getMainGoal
      let (gFVarId, goal') ← goal.note `G gbExpr (some gbTy)
      let (hGTy, goal'') ← goal'.withContext do
        let gExpr := mkFVar gFVarId
        let hGTy ← mkAppM ``CMvPolynomial.IsGroebnerBasis₁ #[ordExpr, idealExpr, gExpr]
        let hGProof ← mkSorry hGTy true
        let (_, goal'') ← goal'.note `hG hGProof (some hGTy)
        pure (hGTy, goal'')
      replaceMainGoal [goal'']
      logInfo m!"groebnerBasis parsed ideal `{idealName.getId}` : {idealTy}"
      logInfo m!"groebnerBasis parsed order : {ordTy}"
      logInfo m!"groebnerBasis inserted local `G : {gbTy}`"
      logInfo m!"groebnerBasis inserted local `hG : {hGTy}`"
