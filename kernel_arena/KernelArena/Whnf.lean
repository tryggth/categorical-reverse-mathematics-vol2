/-
Soundness-Safe Fuel-Bounded WHNF and Definitional Equality for Rung 1 Cartesian 2LTT.
Implements exact cSet reductions, Cartesian Pi/Sigma Kan coercion, and regularity-safe V-coercion.
Zero `partial`, zero `sorry`, zero `axiom`.
-/
import KernelArena.AST
import KernelArena.Cofib
import KernelArena.ShiftSubst

namespace KernelArena
namespace Whnf

open ShiftSubst

private def findSatisfiedTube (dLen : Nat) (cof : Cof) : Tubes → Option Term
  | .nil => none
  | .cons phi body rest =>
    if Cofib.entails dLen cof phi then some body
    else findSatisfiedTube dLen cof rest

private def isDiscreteFibrant (t : Term) : Bool := by
  cases t with
  | boolF => exact true
  | unitF => exact true
  | emptyF => exact true
  | _ => exact false

private def extractLamFBody (t : Term) : Option Term := by
  cases t with | lamF _ b => exact some b | _ => exact none

private def extractLamSBody (t : Term) : Option Term := by
  cases t with | lamS _ b => exact some b | _ => exact none

private def extractPairF (t : Term) : Option (Term × Term) := by
  cases t with | pairF a b => exact some (a, b) | _ => exact none

private def extractPairS (t : Term) : Option (Term × Term) := by
  cases t with | pairS a b => exact some (a, b) | _ => exact none

private def extractPathLamBody (t : Term) : Option Term := by
  cases t with | pathLam b => exact some b | _ => exact none

private def extractVInB (t : Term) : Option Term := by
  cases t with | vIn _ _ b => exact some b | _ => exact none

private def extractBoolLit (t : Term) : Option Bool := by
  cases t with | trueF => exact some true | falseF => exact some false | _ => exact none

private def coePiStep (rDim r'Dim : Dim) (dom cod m : Term) : Term :=
  let dom' := substDimInTerm 0 r'Dim dom
  let a1 := shiftTerm 1 0 dom
  let b1 := shiftTerm 1 1 cod
  let f1 := shiftTerm 1 0 m
  let argAtR := Term.coe r'Dim rDim a1 (.var 0)
  let appAtR := Term.appF f1 argAtR
  let xAtI := Term.coe (shiftDimInDim 1 0 r'Dim) (.dvar 0) (shiftDimInTerm 1 1 a1) (.var 0)
  let codLine := substTerm 0 xAtI b1
  .lamF dom' (.coe rDim r'Dim codLine appAtR)

private def coeSigmaStep (rDim r'Dim : Dim) (dom cod m : Term) : Term :=
  let fstP := Term.fstF m
  let sndP := Term.sndF m
  let newFst := Term.coe rDim r'Dim dom fstP
  let fstAtI := Term.coe (shiftDimInDim 1 0 rDim) (.dvar 0) (shiftDimInTerm 1 1 dom) (shiftDimInTerm 1 0 fstP)
  let sndLine := substTerm 0 fstAtI cod
  let newSnd := Term.coe rDim r'Dim sndLine sndP
  .pairF newFst newSnd

/-- Fuel-bounded weak head normal form reduction under `(dLen, cof)`. -/
def whnf : Nat → Nat → Cof → Term → Option Term
  | 0, _, _, _ => none
  | fuel + 1, dLen, cof, t =>
    match t with
    | .appF fn arg =>
      match whnf fuel dLen cof fn with
      | none => none
      | some fn' =>
        match extractLamFBody fn' with
        | some body => whnf fuel dLen cof (substTerm 0 arg body)
        | none => some (.appF fn' arg)
    | .appS fn arg =>
      match whnf fuel dLen cof fn with
      | none => none
      | some fn' =>
        match extractLamSBody fn' with
        | some body => whnf fuel dLen cof (substTerm 0 arg body)
        | none => some (.appS fn' arg)
    | .fstF p =>
      match whnf fuel dLen cof p with
      | none => none
      | some p' =>
        match extractPairF p' with
        | some (a, _) => whnf fuel dLen cof a
        | none => some (.fstF p')
    | .sndF p =>
      match whnf fuel dLen cof p with
      | none => none
      | some p' =>
        match extractPairF p' with
        | some (_, b) => whnf fuel dLen cof b
        | none => some (.sndF p')
    | .fstS p =>
      match whnf fuel dLen cof p with
      | none => none
      | some p' =>
        match extractPairS p' with
        | some (a, _) => whnf fuel dLen cof a
        | none => some (.fstS p')
    | .sndS p =>
      match whnf fuel dLen cof p with
      | none => none
      | some p' =>
        match extractPairS p' with
        | some (_, b) => whnf fuel dLen cof b
        | none => some (.sndS p')
    | .boolElimF motive tCase fCase scrut =>
      match whnf fuel dLen cof scrut with
      | none => none
      | some scrut' =>
        match extractBoolLit scrut' with
        | some true => whnf fuel dLen cof tCase
        | some false => whnf fuel dLen cof fCase
        | none => some (.boolElimF motive tCase fCase scrut')
    | .pathApp p a0 a1 r =>
      if Cofib.dimEqUnder dLen cof r .d0 then whnf fuel dLen cof a0
      else if Cofib.dimEqUnder dLen cof r .d1 then whnf fuel dLen cof a1
      else
        match whnf fuel dLen cof p with
        | none => none
        | some p' =>
          match extractPathLamBody p' with
          | some body => whnf fuel dLen cof (substDimInTerm 0 r body)
          | none => some (.pathApp p' a0 a1 r)
    | .vType r a b f g sec ret =>
      if Cofib.dimEqUnder dLen cof r .d0 then whnf fuel dLen cof a
      else if Cofib.dimEqUnder dLen cof r .d1 then whnf fuel dLen cof b
      else some (.vType r a b f g sec ret)
    | .vIn r a b =>
      if Cofib.dimEqUnder dLen cof r .d0 then whnf fuel dLen cof a
      else if Cofib.dimEqUnder dLen cof r .d1 then whnf fuel dLen cof b
      else some (.vIn r a b)
    | .vProj r a b f v =>
      if Cofib.dimEqUnder dLen cof r .d0 then whnf fuel dLen cof (.appF f v)
      else if Cofib.dimEqUnder dLen cof r .d1 then whnf fuel dLen cof v
      else
        match whnf fuel dLen cof v with
        | none => none
        | some v' =>
          match extractVInB v' with
          | some b' => whnf fuel dLen cof b'
          | none => some (.vProj r a b f v')
    | .hcom r r' ty tubes u0 =>
      if Cofib.dimEqUnder dLen cof r r' then whnf fuel dLen cof u0
      else
        match findSatisfiedTube dLen cof tubes with
        | some body => whnf fuel dLen cof (substDimInTerm 0 r' body)
        | none =>
          match tubes with
          | .nil =>
            match whnf fuel dLen cof ty with
            | none => none
            | some ty' =>
              if isDiscreteFibrant ty' then whnf fuel dLen cof u0
              else some (.hcom r r' ty' .nil u0)
          | .cons _ _ _ => some (.hcom r r' ty tubes u0)
    | .coe r r' tyLine m =>
      if Cofib.dimEqUnder dLen cof r r' then whnf fuel dLen cof m
      else
        match whnf fuel (dLen + 1) (shiftDimInCof 1 0 cof) tyLine with
        | none => none
        | some tyLine' =>
          let saved := tyLine'
          by
          cases tyLine' with
          | boolF => exact whnf fuel dLen cof m
          | unitF => exact whnf fuel dLen cof m
          | emptyF => exact whnf fuel dLen cof m
          | piF dom cod => exact some (coePiStep r r' dom cod m)
          | sigmaF dom cod => exact some (coeSigmaStep r r' dom cod m)
          | vType rV a b f g sec ret =>
            exact
              if beqDim rV (.dvar 0) && !dimOccursInTerm 0 a && !dimOccursInTerm 0 b &&
                 !dimOccursInTerm 0 f && !dimOccursInTerm 0 g then
                let a' := substDimInTerm 0 .d0 a
                let b' := substDimInTerm 0 .d0 b
                let f' := substDimInTerm 0 .d0 f
                let g' := substDimInTerm 0 .d0 g
                if Cofib.dimEqUnder dLen cof r .d0 && Cofib.dimEqUnder dLen cof r' .d1 then
                  whnf fuel dLen cof (.hcom .d0 .d1 b' .nil (.coe .d0 .d1 (shiftDimInTerm 1 0 b') (.appF f' m)))
                else if Cofib.dimEqUnder dLen cof r .d1 && Cofib.dimEqUnder dLen cof r' .d0 then
                  whnf fuel dLen cof (.hcom .d1 .d0 a' .nil (.coe .d1 .d0 (shiftDimInTerm 1 0 a') (.appF g' m)))
                else some (.coe r r' (.vType rV a b f g sec ret) m)
              else some (.coe r r' (.vType rV a b f g sec ret) m)
          | _ => exact some (.coe r r' saved m)
    | .univS l => some (.univS l)
    | .univF l => some (.univF l)
    | .boolS => some .boolS
    | .boolF => some .boolF
    | .trueF => some .trueF
    | .falseF => some .falseF
    | .var idx => some (.var idx)
    | .piS d c => some (.piS d c)
    | .piF d c => some (.piF d c)
    | .lamS d b => some (.lamS d b)
    | .lamF d b => some (.lamF d b)
    | .liftFtoS i => some (.liftFtoS i)
    | .innerUnivalence a => some (.innerUnivalence a)
    | .innerCoalgebraNu a => some (.innerCoalgebraNu a)
    | .outerStrictEq l r => some (.outerStrictEq l r)
    | .smallnessReplacement a => some (.smallnessReplacement a)
    | .unitS => some .unitS
    | .starS => some .starS
    | .sigmaS d c => some (.sigmaS d c)
    | .pairS a b => some (.pairS a b)
    | .eqS ty l r => some (.eqS ty l r)
    | .reflS a => some (.reflS a)
    | .uipS ty l r p q => some (.uipS ty l r p q)
    | .emptyF => some .emptyF
    | .emptyElimF m s => some (.emptyElimF m s)
    | .unitF => some .unitF
    | .starF => some .starF
    | .sigmaF d c => some (.sigmaF d c)
    | .pairF a b => some (.pairF a b)
    | .pathType ty a0 a1 => some (.pathType ty a0 a1)
    | .pathLam b => some (.pathLam b)

private def eqTubes (recEq : Nat → Cof → Term → Term → Bool) (dLen : Nat) (cof : Cof)
    (t1 t2 : Tubes) : Bool :=
  match t1 with
  | .nil =>
    match t2 with
    | .nil => true
    | .cons _ _ _ => false
  | .cons c1 b1 r1 =>
    match t2 with
    | .nil => false
    | .cons c2 b2 r2 =>
      Cofib.entails dLen (Cof.and cof c1) c2 && Cofib.entails dLen (Cof.and cof c2) c1 &&
        recEq (dLen + 1) (shiftDimInCof 1 0 (Cof.and cof c1)) b1 b2 &&
        eqTubes recEq dLen cof r1 r2

private def eqModHead (recEq : Nat → Cof → Term → Term → Bool) (dLen : Nat) (cof : Cof)
    (u1 u2 : Term) : Bool := by
  cases u1 with
  | univS l1 => cases u2 with | univS l2 => exact l1 == l2 | _ => exact false
  | univF l1 => cases u2 with | univF l2 => exact l1 == l2 | _ => exact false
  | boolS => cases u2 with | boolS => exact true | _ => exact false
  | boolF => cases u2 with | boolF => exact true | _ => exact false
  | trueF => cases u2 with | trueF => exact true | _ => exact false
  | falseF => cases u2 with | falseF => exact true | _ => exact false
  | var i1 => cases u2 with | var i2 => exact i1 == i2 | _ => exact false
  | piS d1 c1 => cases u2 with | piS d2 c2 => exact recEq dLen cof d1 d2 && recEq dLen cof c1 c2 | _ => exact false
  | piF d1 c1 => cases u2 with | piF d2 c2 => exact recEq dLen cof d1 d2 && recEq dLen cof c1 c2 | _ => exact false
  | lamS d1 b1 => cases u2 with | lamS d2 b2 => exact recEq dLen cof d1 d2 && recEq dLen cof b1 b2 | _ => exact false
  | lamF d1 b1 => cases u2 with | lamF d2 b2 => exact recEq dLen cof d1 d2 && recEq dLen cof b1 b2 | _ => exact false
  | appS f1 a1 => cases u2 with | appS f2 a2 => exact recEq dLen cof f1 f2 && recEq dLen cof a1 a2 | _ => exact false
  | appF f1 a1 => cases u2 with | appF f2 a2 => exact recEq dLen cof f1 f2 && recEq dLen cof a1 a2 | _ => exact false
  | liftFtoS x1 => cases u2 with | liftFtoS x2 => exact recEq dLen cof x1 x2 | _ => exact false
  | innerUnivalence x1 => cases u2 with | innerUnivalence x2 => exact recEq dLen cof x1 x2 | _ => exact false
  | innerCoalgebraNu x1 => cases u2 with | innerCoalgebraNu x2 => exact recEq dLen cof x1 x2 | _ => exact false
  | outerStrictEq l1 r1 => cases u2 with | outerStrictEq l2 r2 => exact recEq dLen cof l1 l2 && recEq dLen cof r1 r2 | _ => exact false
  | smallnessReplacement x1 => cases u2 with | smallnessReplacement x2 => exact recEq dLen cof x1 x2 | _ => exact false
  | unitS => cases u2 with | unitS => exact true | _ => exact false
  | starS => cases u2 with | starS => exact true | _ => exact false
  | sigmaS d1 c1 => cases u2 with | sigmaS d2 c2 => exact recEq dLen cof d1 d2 && recEq dLen cof c1 c2 | _ => exact false
  | pairS a1 b1 => cases u2 with | pairS a2 b2 => exact recEq dLen cof a1 a2 && recEq dLen cof b1 b2 | _ => exact false
  | fstS p1 => cases u2 with | fstS p2 => exact recEq dLen cof p1 p2 | _ => exact false
  | sndS p1 => cases u2 with | sndS p2 => exact recEq dLen cof p1 p2 | _ => exact false
  | eqS t1 l1 r1 => cases u2 with | eqS t2 l2 r2 => exact recEq dLen cof t1 t2 && recEq dLen cof l1 l2 && recEq dLen cof r1 r2 | _ => exact false
  | reflS a1 => cases u2 with | reflS a2 => exact recEq dLen cof a1 a2 | _ => exact false
  | uipS t1 l1 r1 p1 q1 => cases u2 with
    | uipS t2 l2 r2 p2 q2 =>
      exact recEq dLen cof t1 t2 && recEq dLen cof l1 l2 && recEq dLen cof r1 r2 &&
        recEq dLen cof p1 p2 && recEq dLen cof q1 q2
    | _ => exact false
  | emptyF => cases u2 with | emptyF => exact true | _ => exact false
  | emptyElimF m1 s1 => cases u2 with | emptyElimF m2 s2 => exact recEq dLen cof m1 m2 && recEq dLen cof s1 s2 | _ => exact false
  | unitF => cases u2 with | unitF => exact true | _ => exact false
  | starF => cases u2 with | starF => exact true | _ => exact false
  | boolElimF m1 t1 f1 s1 => cases u2 with
    | boolElimF m2 t2 f2 s2 =>
      exact recEq dLen cof m1 m2 && recEq dLen cof t1 t2 && recEq dLen cof f1 f2 && recEq dLen cof s1 s2
    | _ => exact false
  | sigmaF d1 c1 => cases u2 with | sigmaF d2 c2 => exact recEq dLen cof d1 d2 && recEq dLen cof c1 c2 | _ => exact false
  | pairF a1 b1 => cases u2 with | pairF a2 b2 => exact recEq dLen cof a1 a2 && recEq dLen cof b1 b2 | _ => exact false
  | fstF p1 => cases u2 with | fstF p2 => exact recEq dLen cof p1 p2 | _ => exact false
  | sndF p1 => cases u2 with | sndF p2 => exact recEq dLen cof p1 p2 | _ => exact false
  | pathType t1 a01 a11 => cases u2 with
    | pathType t2 a02 a12 =>
      exact recEq (dLen + 1) (shiftDimInCof 1 0 cof) t1 t2 && recEq dLen cof a01 a02 && recEq dLen cof a11 a12
    | _ => exact false
  | pathLam b1 => cases u2 with
    | pathLam b2 => exact recEq (dLen + 1) (shiftDimInCof 1 0 cof) b1 b2
    | _ => exact false
  | pathApp p1 a01 a11 r1 => cases u2 with
    | pathApp p2 a02 a12 r2 =>
      exact Cofib.dimEqUnder dLen cof r1 r2 && recEq dLen cof p1 p2 &&
        recEq dLen cof a01 a02 && recEq dLen cof a11 a12
    | _ => exact false
  | coe r1 r1' t1 m1 => cases u2 with
    | coe r2 r2' t2 m2 =>
      exact Cofib.dimEqUnder dLen cof r1 r2 && Cofib.dimEqUnder dLen cof r1' r2' &&
        recEq (dLen + 1) (shiftDimInCof 1 0 cof) t1 t2 && recEq dLen cof m1 m2
    | _ => exact false
  | hcom r1 r1' t1 tb1 u1 => cases u2 with
    | hcom r2 r2' t2 tb2 u2 =>
      exact Cofib.dimEqUnder dLen cof r1 r2 && Cofib.dimEqUnder dLen cof r1' r2' &&
        recEq dLen cof t1 t2 && eqTubes recEq dLen cof tb1 tb2 && recEq dLen cof u1 u2
    | _ => exact false
  | vType r1 a1 b1 f1 g1 s1 rt1 => cases u2 with
    | vType r2 a2 b2 f2 g2 s2 rt2 =>
      exact Cofib.dimEqUnder dLen cof r1 r2 && recEq dLen cof a1 a2 && recEq dLen cof b1 b2 &&
        recEq dLen cof f1 f2 && recEq dLen cof g1 g2 && recEq dLen cof s1 s2 && recEq dLen cof rt1 rt2
    | _ => exact false
  | vIn r1 a1 b1 => cases u2 with
    | vIn r2 a2 b2 =>
      exact Cofib.dimEqUnder dLen cof r1 r2 && recEq dLen cof a1 a2 && recEq dLen cof b1 b2
    | _ => exact false
  | vProj r1 a1 b1 f1 v1 => cases u2 with
    | vProj r2 a2 b2 f2 v2 =>
      exact Cofib.dimEqUnder dLen cof r1 r2 && recEq dLen cof a1 a2 && recEq dLen cof b1 b2 &&
        recEq dLen cof f1 f2 && recEq dLen cof v1 v2
    | _ => exact false

/-- Fuel-bounded definitional equality modulo WHNF and Cartesian cofibration `cof`. -/
def isDefEq : Nat → Nat → Cof → Term → Term → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, dLen, cof, t1, t2 =>
    if Cofib.isInconsistent dLen cof then true
    else if beqTerm t1 t2 then true
    else
      match whnf fuel dLen cof t1 with
      | none => false
      | some u1 =>
        match whnf fuel dLen cof t2 with
        | none => false
        | some u2 =>
          if beqTerm u1 u2 then true
          else eqModHead (isDefEq fuel) dLen cof u1 u2

end Whnf
end KernelArena
