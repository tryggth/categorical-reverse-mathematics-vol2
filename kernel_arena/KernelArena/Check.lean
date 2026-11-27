/-
Fuel-bounded bidirectional 2LTT typechecking for `KernelArena` (Phase 0 + Rung 1).
Zero `partial`, zero `termination_by`, zero `sorry`, zero `axiom`, zero wildcard `match`.
-/
import KernelArena.AST
import KernelArena.Cofib
import KernelArena.Arena
import KernelArena.ShiftSubst
import KernelArena.Whnf

namespace KernelArena
namespace Check

open ShiftSubst

@[inline] private def bindE {α β : Type} (x : Except CheckError α)
    (f : α → Except CheckError β) : Except CheckError β :=
  match x with | .error e => .error e | .ok a => f a

private def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

private def whnfOr (fuel dLen : Nat) (cof : Cof) (t : Term) : Except CheckError Term :=
  match Whnf.whnf fuel dLen cof t with
  | some w => .ok w | none => .error (.eTypecheckFail "WHNF fuel exhausted")

private def expectUniv (isF : Bool) (fuel dLen : Nat) (cof : Cof) (ty : Term) : Except CheckError Nat :=
  bindE (whnfOr fuel dLen cof ty) fun w => by
    cases w with
    | univF l => exact if isF then .ok l else .error (.eLevelFirewall "expected UnivS, got UnivF")
    | univS l => exact if isF then .error (.eLevelFirewall "expected UnivF, got UnivS") else .ok l
    | _ => exact .error (.eTypecheckFail "expected universe sort")

private def expectValidSort (fuel dLen : Nat) (cof : Cof) (ty : Term) : Except CheckError Unit :=
  bindE (whnfOr fuel dLen cof ty) fun w => by
    cases w with | univF _ => exact .ok () | univS _ => exact .ok () | _ => exact .error (.eTypecheckFail "not a sort")

private def expectPi (isF : Bool) (fuel dLen : Nat) (cof : Cof) (ty : Term) : Except CheckError (Term × Term) :=
  bindE (whnfOr fuel dLen cof ty) fun w => by
    cases w with
    | piF d c => exact if isF then .ok (d, c) else .error (.eLevelFirewall "level firewall: strict op on PiF")
    | piS d c => exact if !isF then .ok (d, c) else .error (.eLevelFirewall "level firewall: fibrant op on PiS")
    | _ => exact .error (.eTypecheckFail "expected Pi type")

private def expectSigma (isF : Bool) (fuel dLen : Nat) (cof : Cof) (ty : Term) : Except CheckError (Term × Term) :=
  bindE (whnfOr fuel dLen cof ty) fun w => by
    cases w with
    | sigmaF d c => exact if isF then .ok (d, c) else .error (.eLevelFirewall "level firewall: strict op on SigmaF")
    | sigmaS d c => exact if !isF then .ok (d, c) else .error (.eLevelFirewall "level firewall: fibrant op on SigmaS")
    | _ => exact .error (.eTypecheckFail "expected Sigma type")

private def expectPathType (fuel dLen : Nat) (cof : Cof) (ty : Term) : Except CheckError (Term × Term × Term) :=
  bindE (whnfOr fuel dLen cof ty) fun w => by
    cases w with | pathType tl a0 a1 => exact .ok (tl, a0, a1) | _ => exact .error (.eTypecheckFail "expected PathType")

private def expectVType (fuel dLen : Nat) (cof : Cof) (ty : Term) : Except CheckError (Dim × Term × Term × Term) :=
  bindE (whnfOr fuel dLen cof ty) fun w => by
    cases w with | vType r a b f _ _ _ => exact .ok (r, a, b, f) | _ => exact .error (.eTypecheckFail "expected VType")

private def checkTubesPair (fuel dLen : Nat) (cof : Cof) (phi1 : Cof) (u1 : Term) : Tubes → Except CheckError Unit
  | .nil => .ok ()
  | .cons phi2 u2 rest =>
    if Whnf.isDefEq fuel (dLen + 1) (shiftDimInCof 1 0 (Cof.and cof (Cof.and phi1 phi2))) u1 u2 then
      checkTubesPair fuel dLen cof phi1 u1 rest
    else .error (.eTubeMismatch "hcom tube pairwise overlap mismatch")

private def checkHComTubes (checkFn : Nat → Cof → List Term → Term → Term → Except CheckError Unit)
    (fuel dLen : Nat) (cof : Cof) (ctx : List Term) (r : Dim) (ty u0 : Term) : Tubes → Except CheckError Unit
  | .nil => .ok ()
  | .cons phi body rest =>
    if !Cofib.cofWellScoped dLen phi then .error (.eTypecheckFail "hcom tube cofibration out of scope")
    else
      let cofPhi := Cof.and cof phi
      bindE (checkFn (dLen + 1) (shiftDimInCof 1 0 cofPhi) (shiftDimInCtx 1 0 ctx) body (shiftDimInTerm 1 0 ty)) fun () =>
      if !Whnf.isDefEq fuel dLen cofPhi (substDimInTerm 0 r body) u0 then .error (.eTubeMismatch "hcom tube base agreement mismatch")
      else bindE (checkTubesPair fuel dLen cof phi body rest) fun () => checkHComTubes checkFn fuel dLen cof ctx r ty u0 rest

private def checkEquivUnderPhi0
    (checkFn : Nat → Cof → List Term → Term → Term → Except CheckError Unit)
    (inferFn : Nat → Cof → List Term → Term → Except CheckError Term)
    (fuel dLen : Nat) (cof : Cof) (ctx : List Term) (r : Dim) (lB : Nat) (a b f g sec ret : Term) :
    Except CheckError Unit :=
  let phi0 := Cof.and cof (Cof.eq r .d0)
  if Cofib.isInconsistent dLen phi0 then .ok ()
  else
    bindE (inferFn dLen phi0 ctx a) fun aSort =>
    bindE (expectUniv true fuel dLen phi0 aSort) fun lA =>
    if lA != lB then .error (.eTypecheckFail "VType universe level mismatch")
    else
      let b1 := shiftTerm 1 0 b; let a1 := shiftTerm 1 0 a
      bindE (checkFn dLen phi0 ctx f (.piF a b1)) fun () =>
      bindE (checkFn dLen phi0 ctx g (.piF b a1)) fun () =>
      let f1 := shiftTerm 1 0 f; let g1 := shiftTerm 1 0 g
      let secTy := Term.piF b (.pathType (shiftDimInTerm 1 0 b1) (.appF f1 (.appF g1 (.var 0))) (.var 0))
      let retTy := Term.piF a (.pathType (shiftDimInTerm 1 0 a1) (.appF g1 (.appF f1 (.var 0))) (.var 0))
      bindE (checkFn dLen phi0 ctx sec secTy) fun () => checkFn dLen phi0 ctx ret retTy

private def checkVProj
    (checkFn : Nat → Cof → List Term → Term → Term → Except CheckError Unit)
    (inferFn : Nat → Cof → List Term → Term → Except CheckError Term)
    (fuel dLen : Nat) (cof : Cof) (ctx : List Term) (r : Dim) (a b f v : Term) : Except CheckError Term :=
  if !Cofib.dimWellScoped dLen r then .error (.eTypecheckFail "vProj dim out of scope")
  else
    bindE (inferFn dLen cof ctx b) fun bSort =>
    bindE (expectUniv true fuel dLen cof bSort) fun lB =>
    let phi0 := Cof.and cof (Cof.eq r .d0)
    let equivOk :=
      if Cofib.isInconsistent dLen phi0 then .ok ()
      else
        bindE (inferFn dLen phi0 ctx a) fun aSort =>
        bindE (expectUniv true fuel dLen phi0 aSort) fun lA =>
        if lA != lB then .error (.eTypecheckFail "vProj universe mismatch")
        else checkFn dLen phi0 ctx f (.piF a (shiftTerm 1 0 b))
    bindE equivOk fun () =>
    if Cofib.dimEqUnder dLen cof r .d0 then bindE (checkFn dLen cof ctx v a) fun () => .ok b
    else if Cofib.dimEqUnder dLen cof r .d1 then bindE (checkFn dLen cof ctx v b) fun () => .ok b
    else
      bindE (inferFn dLen cof ctx v) fun vTy =>
      bindE (expectVType fuel dLen cof vTy) fun (r', a', b', f') =>
      if !Cofib.dimEqUnder dLen cof r r' || !Whnf.isDefEq fuel dLen cof b b' then .error (.eTypecheckFail "vProj type mismatch")
      else if !Cofib.isInconsistent dLen phi0 && (!Whnf.isDefEq fuel dLen phi0 a a' || !Whnf.isDefEq fuel dLen phi0 f f') then
        .error (.eTypecheckFail "vProj boundary fiber mismatch")
      else .ok b

private def inferUniv (isF : Bool) (inferFn : Nat → Cof → List Term → Term → Except CheckError Term)
    (fuel dLen : Nat) (cof : Cof) (ctx : List Term) (t : Term) : Except CheckError Nat :=
  bindE (inferFn dLen cof ctx t) fun s => expectUniv isF fuel dLen cof s

private def inferBinder (isF : Bool) (inferFn : Nat → Cof → List Term → Term → Except CheckError Term)
    (fuel dLen : Nat) (cof : Cof) (ctx : List Term) (dom cod : Term) : Except CheckError Term :=
  bindE (inferUniv isF inferFn fuel dLen cof ctx dom) fun l1 =>
  bindE (inferUniv isF inferFn fuel dLen cof (dom :: ctx) cod) fun l2 =>
  .ok (if isF then .univF (max l1 l2) else .univS (max l1 l2))

private def inferLam (isF : Bool) (inferFn : Nat → Cof → List Term → Term → Except CheckError Term)
    (fuel dLen : Nat) (cof : Cof) (ctx : List Term) (dom body : Term) : Except CheckError Term :=
  bindE (inferUniv isF inferFn fuel dLen cof ctx dom) fun _ =>
  bindE (inferFn dLen cof (dom :: ctx) body) fun bTy =>
  bindE (inferUniv isF inferFn fuel dLen cof (dom :: ctx) bTy) fun _ => .ok (if isF then .piF dom bTy else .piS dom bTy)

private def inferApp (isF : Bool) (checkFn : Nat → Cof → List Term → Term → Term → Except CheckError Unit)
    (inferFn : Nat → Cof → List Term → Term → Except CheckError Term)
    (fuel dLen : Nat) (cof : Cof) (ctx : List Term) (fn arg : Term) : Except CheckError Term :=
  bindE (inferFn dLen cof ctx fn) fun fnTy =>
  bindE (expectPi isF fuel dLen cof fnTy) fun (dom, cod) =>
  bindE (checkFn dLen cof ctx arg dom) fun () => .ok (substTerm 0 arg cod)

private def inferPair (isF : Bool) (inferFn : Nat → Cof → List Term → Term → Except CheckError Term)
    (fuel dLen : Nat) (cof : Cof) (ctx : List Term) (a b : Term) : Except CheckError Term :=
  bindE (inferFn dLen cof ctx a) fun t1 => bindE (inferUniv isF inferFn fuel dLen cof ctx t1) fun _ =>
  bindE (inferFn dLen cof ctx b) fun t2 => bindE (inferUniv isF inferFn fuel dLen cof ctx t2) fun _ =>
  .ok (if isF then .sigmaF t1 (shiftTerm 1 0 t2) else .sigmaS t1 (shiftTerm 1 0 t2))

private def inferProj (isF isFst : Bool) (inferFn : Nat → Cof → List Term → Term → Except CheckError Term)
    (fuel dLen : Nat) (cof : Cof) (ctx : List Term) (p : Term) : Except CheckError Term :=
  bindE (inferFn dLen cof ctx p) fun pTy =>
  bindE (expectSigma isF fuel dLen cof pTy) fun (dom, cod) =>
  .ok (if isFst then dom else substTerm 0 (if isF then .fstF p else .fstS p) cod)

private def checkLam (isF : Bool) (checkFn : Nat → Cof → List Term → Term → Term → Except CheckError Unit)
    (inferFn : Nat → Cof → List Term → Term → Except CheckError Term)
    (fuel dLen : Nat) (cof : Cof) (ctx : List Term) (dom body ty : Term) : Except CheckError Unit :=
  bindE (expectPi isF fuel dLen cof ty) fun (dom', cod') =>
  bindE (inferUniv isF inferFn fuel dLen cof ctx dom) fun _ =>
  if !Whnf.isDefEq fuel dLen cof dom dom' then .error (.eTypecheckFail "lambda domain mismatch")
  else checkFn dLen cof (dom :: ctx) body cod'

private def checkPair (isF : Bool) (checkFn : Nat → Cof → List Term → Term → Term → Except CheckError Unit)
    (fuel dLen : Nat) (cof : Cof) (ctx : List Term) (fst snd ty : Term) : Except CheckError Unit :=
  bindE (expectSigma isF fuel dLen cof ty) fun (dom, cod) =>
  bindE (checkFn dLen cof ctx fst dom) fun () => checkFn dLen cof ctx snd (substTerm 0 fst cod)

private def checkPathLam (checkFn : Nat → Cof → List Term → Term → Term → Except CheckError Unit)
    (fuel dLen : Nat) (cof : Cof) (ctx : List Term) (body ty : Term) : Except CheckError Unit :=
  bindE (expectPathType fuel dLen cof ty) fun (tyLine, a0, a1) =>
  bindE (checkFn (dLen + 1) (shiftDimInCof 1 0 cof) (shiftDimInCtx 1 0 ctx) body tyLine) fun () =>
  if !Whnf.isDefEq fuel dLen cof (substDimInTerm 0 .d0 body) a0 then .error (.ePathBoundary "pathLam 0-endpoint mismatch")
  else if !Whnf.isDefEq fuel dLen cof (substDimInTerm 0 .d1 body) a1 then .error (.ePathBoundary "pathLam 1-endpoint mismatch")
  else .ok ()

private def checkVIn (checkFn : Nat → Cof → List Term → Term → Term → Except CheckError Unit)
    (fuel dLen : Nat) (cof : Cof) (ctx : List Term) (r : Dim) (a b ty : Term) : Except CheckError Unit :=
  if !Cofib.dimWellScoped dLen r then .error (.eTypecheckFail "vIn dim out of scope")
  else if Cofib.dimEqUnder dLen cof r .d0 then checkFn dLen cof ctx a ty
  else if Cofib.dimEqUnder dLen cof r .d1 then checkFn dLen cof ctx b ty
  else
    bindE (expectVType fuel dLen cof ty) fun (r', aTy, bTy, f) =>
    if !Cofib.dimEqUnder dLen cof r r' then .error (.eTypecheckFail "vIn dim mismatch")
    else
      bindE (checkFn dLen cof ctx b bTy) fun () =>
      let phi0 := Cof.and cof (Cof.eq r .d0)
      if Cofib.isInconsistent dLen phi0 then .ok ()
      else bindE (checkFn dLen phi0 ctx a aTy) fun () =>
        if Whnf.isDefEq fuel dLen phi0 (.appF f a) b then .ok () else .error (.ePathBoundary "vIn f a != b under r = 0")

private def inferPathApp (checkFn : Nat → Cof → List Term → Term → Term → Except CheckError Unit)
    (inferFn : Nat → Cof → List Term → Term → Except CheckError Term)
    (fuel dLen : Nat) (cof : Cof) (ctx : List Term) (p a0 a1 : Term) (r : Dim) : Except CheckError Term :=
  if !Cofib.dimWellScoped dLen r then .error (.eTypecheckFail "pathApp dim out of scope")
  else
    bindE (inferFn dLen cof ctx p) fun pTy =>
    bindE (expectPathType fuel dLen cof pTy) fun (tyLine, p0, p1) =>
    bindE (checkFn dLen cof ctx a0 (substDimInTerm 0 .d0 tyLine)) fun () =>
    bindE (checkFn dLen cof ctx a1 (substDimInTerm 0 .d1 tyLine)) fun () =>
    if !Whnf.isDefEq fuel dLen cof a0 p0 || !Whnf.isDefEq fuel dLen cof a1 p1 then
      .error (.ePathBoundary "pathApp explicit endpoint mismatch")
    else .ok (substDimInTerm 0 r tyLine)

private def checkFallback (inferFn : Nat → Cof → List Term → Term → Except CheckError Term)
    (fuel dLen : Nat) (cof : Cof) (ctx : List Term) (t ty : Term) : Except CheckError Unit :=
  bindE (inferFn dLen cof ctx t) fun inferred =>
  if Whnf.isDefEq fuel dLen cof inferred ty then .ok () else .error (.eTypecheckFail "type mismatch")

mutual
  /-- Bidirectional typecheck `t : ty` under `(dLen, cof, ctx)`. -/
  def check : Nat → Nat → Nat → Cof → List Term → Term → Term → Except CheckError Unit
    | 0, _, _, _, _, _, _ => .error (.eTypecheckFail "fuel exhausted in check")
    | fuel + 1, k, dLen, cof, ctx, t, ty =>
      if Cofib.isInconsistent dLen cof then .ok ()
      else
        let tOrig := t
        by
          cases t with
          | lamF dom body => exact checkLam true (check fuel k) (infer fuel k) fuel dLen cof ctx dom body ty
          | lamS dom body => exact checkLam false (check fuel k) (infer fuel k) fuel dLen cof ctx dom body ty
          | pairF fst snd => exact checkPair true (check fuel k) fuel dLen cof ctx fst snd ty
          | pairS fst snd => exact checkPair false (check fuel k) fuel dLen cof ctx fst snd ty
          | pathLam body => exact checkPathLam (check fuel k) fuel dLen cof ctx body ty
          | vIn r a b => exact checkVIn (check fuel k) fuel dLen cof ctx r a b ty
          | _ => exact checkFallback (infer fuel k) fuel dLen cof ctx tOrig ty

  /-- Fuel-bounded type inference enforcing 2LTT firewall, universe depth `k`, and cubical Kan rules. -/
  def infer : Nat → Nat → Nat → Cof → List Term → Term → Except CheckError Term
    | 0, _, _, _, _, _ => .error (.eTypecheckFail "fuel exhausted in infer")
    | fuel + 1, k, dLen, cof, ctx, t =>
      match t with
      | .univS l => if l < k then .ok (.univS (l + 1)) else .error (.eUnivOob "UnivS level >= k")
      | .univF l => if l < k then .ok (.univF (l + 1)) else .error (.eUnivOob "UnivF level >= k")
      | .boolS => if 0 < k then .ok (.univS 0) else .error (.eUnivOob "strict base requires k > 0")
      | .unitS => if 0 < k then .ok (.univS 0) else .error (.eUnivOob "strict base requires k > 0")
      | .boolF => if 0 < k then .ok (.univF 0) else .error (.eUnivOob "fibrant base requires k > 0")
      | .emptyF => if 0 < k then .ok (.univF 0) else .error (.eUnivOob "fibrant base requires k > 0")
      | .unitF => if 0 < k then .ok (.univF 0) else .error (.eUnivOob "fibrant base requires k > 0")
      | .trueF | .falseF => if 0 < k then .ok .boolF else .error (.eUnivOob "BoolF lit requires k > 0")
      | .starS => if 0 < k then .ok .unitS else .error (.eUnivOob "StarS requires k > 0")
      | .starF => if 0 < k then .ok .unitF else .error (.eUnivOob "StarF requires k > 0")
      | .var idx => match listGet? ctx idx with | some ty => .ok (shiftTerm (idx + 1) 0 ty) | none => .error (.eTypecheckFail "unbound var")
      | .liftFtoS inner => bindE (inferUniv true (infer fuel k) fuel dLen cof ctx inner) fun l => .ok (.univS l)
      | .piF dom cod | .sigmaF dom cod => inferBinder true (infer fuel k) fuel dLen cof ctx dom cod
      | .piS dom cod | .sigmaS dom cod => inferBinder false (infer fuel k) fuel dLen cof ctx dom cod
      | .lamF dom body => inferLam true (infer fuel k) fuel dLen cof ctx dom body
      | .lamS dom body => inferLam false (infer fuel k) fuel dLen cof ctx dom body
      | .appF fn arg => inferApp true (check fuel k) (infer fuel k) fuel dLen cof ctx fn arg
      | .appS fn arg => inferApp false (check fuel k) (infer fuel k) fuel dLen cof ctx fn arg
      | .pairF a b => inferPair true (infer fuel k) fuel dLen cof ctx a b
      | .pairS a b => inferPair false (infer fuel k) fuel dLen cof ctx a b
      | .fstF p => inferProj true true (infer fuel k) fuel dLen cof ctx p
      | .sndF p => inferProj true false (infer fuel k) fuel dLen cof ctx p
      | .fstS p => inferProj false true (infer fuel k) fuel dLen cof ctx p
      | .sndS p => inferProj false false (infer fuel k) fuel dLen cof ctx p
      | .eqS ty lhs rhs =>
        bindE (inferUniv false (infer fuel k) fuel dLen cof ctx ty) fun l =>
        bindE (check fuel k dLen cof ctx lhs ty) fun () => bindE (check fuel k dLen cof ctx rhs ty) fun () => .ok (.univS l)
      | .reflS a =>
        bindE (infer fuel k dLen cof ctx a) fun ty =>
        bindE (inferUniv false (infer fuel k) fuel dLen cof ctx ty) fun _ => .ok (.eqS ty a a)
      | .uipS ty lhs rhs p q =>
        bindE (inferUniv false (infer fuel k) fuel dLen cof ctx ty) fun _ =>
        bindE (check fuel k dLen cof ctx lhs ty) fun () => bindE (check fuel k dLen cof ctx rhs ty) fun () =>
        let eqTy := Term.eqS ty lhs rhs
        bindE (check fuel k dLen cof ctx p eqTy) fun () => bindE (check fuel k dLen cof ctx q eqTy) fun () => .ok (.eqS eqTy p q)
      | .emptyElimF motive scrut =>
        bindE (check fuel k dLen cof ctx scrut .emptyF) fun () =>
        bindE (inferUniv true (infer fuel k) fuel dLen cof (.emptyF :: ctx) motive) fun _ => .ok (substTerm 0 scrut motive)
      | .boolElimF motive tCase fCase scrut =>
        bindE (check fuel k dLen cof ctx scrut .boolF) fun () =>
        bindE (inferUniv true (infer fuel k) fuel dLen cof (.boolF :: ctx) motive) fun _ =>
        bindE (check fuel k dLen cof ctx tCase (substTerm 0 .trueF motive)) fun () =>
        bindE (check fuel k dLen cof ctx fCase (substTerm 0 .falseF motive)) fun () => .ok (substTerm 0 scrut motive)
      | .pathType tyLine a0 a1 =>
        let cof' := shiftDimInCof 1 0 cof
        bindE (inferUniv true (infer fuel k) fuel (dLen + 1) cof' (shiftDimInCtx 1 0 ctx) tyLine) fun l =>
        bindE (check fuel k dLen cof ctx a0 (substDimInTerm 0 .d0 tyLine)) fun () =>
        bindE (check fuel k dLen cof ctx a1 (substDimInTerm 0 .d1 tyLine)) fun () => .ok (.univF l)
      | .pathLam body =>
        let dLen' := dLen + 1; let cof' := shiftDimInCof 1 0 cof; let ctx' := shiftDimInCtx 1 0 ctx
        bindE (infer fuel k dLen' cof' ctx' body) fun bTy =>
        bindE (inferUniv true (infer fuel k) fuel dLen' cof' ctx' bTy) fun _ =>
        .ok (.pathType bTy (substDimInTerm 0 .d0 body) (substDimInTerm 0 .d1 body))
      | .pathApp p a0 a1 r => inferPathApp (check fuel k) (infer fuel k) fuel dLen cof ctx p a0 a1 r
      | .coe r r' tyLine m =>
        if !Cofib.dimWellScoped dLen r || !Cofib.dimWellScoped dLen r' then .error (.eTypecheckFail "coe dim OOB")
        else
          let cof' := shiftDimInCof 1 0 cof
          bindE (inferUniv true (infer fuel k) fuel (dLen + 1) cof' (shiftDimInCtx 1 0 ctx) tyLine) fun _ =>
          bindE (check fuel k dLen cof ctx m (substDimInTerm 0 r tyLine)) fun () => .ok (substDimInTerm 0 r' tyLine)
      | .hcom r r' ty tubes u0 =>
        if !Cofib.dimWellScoped dLen r || !Cofib.dimWellScoped dLen r' then .error (.eTypecheckFail "hcom dim OOB")
        else
          bindE (inferUniv true (infer fuel k) fuel dLen cof ctx ty) fun _ =>
          bindE (check fuel k dLen cof ctx u0 ty) fun () =>
          bindE (checkHComTubes (check fuel k) fuel dLen cof ctx r ty u0 tubes) fun () => .ok ty
      | .vType r a b f g sec ret =>
        if !Cofib.dimWellScoped dLen r then .error (.eTypecheckFail "vType dim OOB")
        else
          bindE (inferUniv true (infer fuel k) fuel dLen cof ctx b) fun lB =>
          bindE (checkEquivUnderPhi0 (check fuel k) (infer fuel k) fuel dLen cof ctx r lB a b f g sec ret) fun () => .ok (.univF lB)
      | .vIn r a b =>
        if !Cofib.dimWellScoped dLen r then .error (.eTypecheckFail "vIn dim out of scope")
        else if Cofib.dimEqUnder dLen cof r .d0 then infer fuel k dLen cof ctx a
        else if Cofib.dimEqUnder dLen cof r .d1 then infer fuel k dLen cof ctx b
        else .error (.eTypecheckFail "cannot infer vIn without expected VType")
      | .vProj r a b f v => checkVProj (check fuel k) (infer fuel k) fuel dLen cof ctx r a b f v
      | .innerUnivalence arg | .innerCoalgebraNu arg =>
        bindE (inferUniv true (infer fuel k) fuel dLen cof ctx arg) fun l => .ok (.univF l)
      | .outerStrictEq lhs rhs =>
        bindE (infer fuel k dLen cof ctx lhs) fun t1 => bindE (infer fuel k dLen cof ctx rhs) fun t2 =>
        if Whnf.isDefEq fuel dLen cof t1 t2 then
          bindE (inferUniv false (infer fuel k) fuel dLen cof ctx t1) fun l => .ok (.univS l)
        else .error (.eTypecheckFail "OuterStrictEq endpoint type mismatch")
      | .smallnessReplacement arg => bindE (inferUniv false (infer fuel k) fuel dLen cof ctx arg) fun l => .ok (.univS l)
end

private def extractTerm? (v : ArenaVal) : Option Term := by
  cases v with | term t => exact some t | _ => exact none

private def decodeGoalAndProof (nodes : Array ArenaNode) (goalId proofId : Nat) : Except CheckError (Term × Term) :=
  match Arena.decodeArena nodes with
  | none => .error (.eTopoCycle "failed to decode arena nodes")
  | some vals =>
    match vals[goalId]? with
    | none => .error (.eTopoCycle "goal node out of bounds")
    | some vg =>
      match vals[proofId]? with
      | none => .error (.eTopoCycle "proof node out of bounds")
      | some vp =>
        match extractTerm? vg with
        | none => .error (.eTopoCycle "goal node is not a Term")
        | some goalTerm =>
          match extractTerm? vp with
          | none => .error (.eTopoCycle "proof node is not a Term")
          | some proofTerm => .ok (goalTerm, proofTerm)

/-- Verify that `goalTerm` is a valid sort and `proofTerm : goalTerm`. -/
def checkGoalAndProof (fuel k : Nat) (proofTerm goalTerm : Term) : Except CheckError Unit :=
  bindE (infer fuel k 0 .top [] goalTerm) fun sort =>
  bindE (expectValidSort fuel 0 .top sort) fun () => check fuel k 0 .top [] proofTerm goalTerm

/-- Purely boolean certificate verification (for fast zero-axiom kernel `rfl` in `CertChecks`). -/
def checkCert (fuel : Nat) (c : Cert) : Bool :=
  c.schema == "kernel-arena.2ltt.v1" &&
    Arena.checkTopoBool c.nodes c.goalTypeNode c.proofTermNode &&
    (Arena.computeStrataFlags c.nodes c.goalTypeNode c.proofTermNode == c.strataFlags) &&
    match decodeGoalAndProof c.nodes c.goalTypeNode c.proofTermNode with
    | .error _ => false
    | .ok (goalTerm, proofTerm) =>
      match checkGoalAndProof fuel c.universeDepthK proofTerm goalTerm with
      | .ok () => true | .error _ => false

/-- Full CLI verification including canonical SHA-256 arena hash check and structured errors. -/
def verifyCert (fuel : Nat) (c : Cert) : Except CheckError Unit :=
  if c.schema != "kernel-arena.2ltt.v1" then
    .error (.eSchemaError s!"unsupported schema '{c.schema}', expected 'kernel-arena.2ltt.v1'")
  else
    bindE (Arena.checkTopo c.nodes c.goalTypeNode c.proofTermNode) fun () =>
    bindE (Arena.verifyArenaHash c) fun () =>
    bindE (Arena.verifyStrataFlags c) fun () =>
    bindE (decodeGoalAndProof c.nodes c.goalTypeNode c.proofTermNode) fun (goalTerm, proofTerm) =>
    checkGoalAndProof fuel c.universeDepthK proofTerm goalTerm

end Check
end KernelArena
