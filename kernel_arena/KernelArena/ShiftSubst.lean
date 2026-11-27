/-
Pure structural de Bruijn shifting, substitution, and occurrence checks
for both term variables (`Term`) and Cartesian dimension variables (`Dim`/`Cof`/`Term`).
Zero `partial`, zero `sorry`, zero `axiom`.
-/
import KernelArena.AST

namespace KernelArena
namespace ShiftSubst

/-- Shift free dimension variables `≥ cutoff` by `d` in `Dim`. -/
def shiftDimInDim (d cutoff : Nat) : Dim → Dim
  | .d0 => .d0
  | .d1 => .d1
  | .dvar i => if i >= cutoff then .dvar (i + d) else .dvar i

/-- Substitute `s` for dimension variable `j` and shift higher dim vars down by 1. -/
def substDimInDim (j : Nat) (s : Dim) : Dim → Dim
  | .d0 => .d0
  | .d1 => .d1
  | .dvar i =>
    if i == j then shiftDimInDim j 0 s
    else if i > j then .dvar (i - 1)
    else .dvar i

/-- Shift free dimension variables `≥ cutoff` by `d` in `Cof`. -/
def shiftDimInCof (d cutoff : Nat) : Cof → Cof
  | .top => .top
  | .bot => .bot
  | .eq r1 r2 => .eq (shiftDimInDim d cutoff r1) (shiftDimInDim d cutoff r2)
  | .and c1 c2 => .and (shiftDimInCof d cutoff c1) (shiftDimInCof d cutoff c2)
  | .or c1 c2 => .or (shiftDimInCof d cutoff c1) (shiftDimInCof d cutoff c2)

/-- Substitute `s` for dimension variable `j` in `Cof`. -/
def substDimInCof (j : Nat) (s : Dim) : Cof → Cof
  | .top => .top
  | .bot => .bot
  | .eq r1 r2 => .eq (substDimInDim j s r1) (substDimInDim j s r2)
  | .and c1 c2 => .and (substDimInCof j s c1) (substDimInCof j s c2)
  | .or c1 c2 => .or (substDimInCof j s c1) (substDimInCof j s c2)

/-- Check if dimension variable `i` occurs free in `Dim`. -/
def dimOccursInDim (i : Nat) : Dim → Bool
  | .d0 => false
  | .d1 => false
  | .dvar k => k == i

/-- Check if dimension variable `i` occurs free in `Cof`. -/
def dimOccursInCof (i : Nat) : Cof → Bool
  | .top => false
  | .bot => false
  | .eq r1 r2 => dimOccursInDim i r1 || dimOccursInDim i r2
  | .and c1 c2 => dimOccursInCof i c1 || dimOccursInCof i c2
  | .or c1 c2 => dimOccursInCof i c1 || dimOccursInCof i c2

mutual
  /-- Shift free dimension variables `≥ cutoff` by `d` in `Term`. -/
  def shiftDimInTerm (d cutoff : Nat) : Term → Term
    | .univS l => .univS l
    | .univF l => .univF l
    | .boolS => .boolS
    | .boolF => .boolF
    | .trueF => .trueF
    | .falseF => .falseF
    | .var idx => .var idx
    | .piS dom cod => .piS (shiftDimInTerm d cutoff dom) (shiftDimInTerm d cutoff cod)
    | .piF dom cod => .piF (shiftDimInTerm d cutoff dom) (shiftDimInTerm d cutoff cod)
    | .lamS dom body => .lamS (shiftDimInTerm d cutoff dom) (shiftDimInTerm d cutoff body)
    | .lamF dom body => .lamF (shiftDimInTerm d cutoff dom) (shiftDimInTerm d cutoff body)
    | .appS fn arg => .appS (shiftDimInTerm d cutoff fn) (shiftDimInTerm d cutoff arg)
    | .appF fn arg => .appF (shiftDimInTerm d cutoff fn) (shiftDimInTerm d cutoff arg)
    | .liftFtoS i => .liftFtoS (shiftDimInTerm d cutoff i)
    | .innerUnivalence a => .innerUnivalence (shiftDimInTerm d cutoff a)
    | .innerCoalgebraNu a => .innerCoalgebraNu (shiftDimInTerm d cutoff a)
    | .outerStrictEq l r => .outerStrictEq (shiftDimInTerm d cutoff l) (shiftDimInTerm d cutoff r)
    | .smallnessReplacement a => .smallnessReplacement (shiftDimInTerm d cutoff a)
    | .unitS => .unitS
    | .starS => .starS
    | .sigmaS dom cod => .sigmaS (shiftDimInTerm d cutoff dom) (shiftDimInTerm d cutoff cod)
    | .pairS a b => .pairS (shiftDimInTerm d cutoff a) (shiftDimInTerm d cutoff b)
    | .fstS p => .fstS (shiftDimInTerm d cutoff p)
    | .sndS p => .sndS (shiftDimInTerm d cutoff p)
    | .eqS ty l r => .eqS (shiftDimInTerm d cutoff ty) (shiftDimInTerm d cutoff l) (shiftDimInTerm d cutoff r)
    | .reflS a => .reflS (shiftDimInTerm d cutoff a)
    | .uipS ty l r p q => .uipS (shiftDimInTerm d cutoff ty) (shiftDimInTerm d cutoff l)
        (shiftDimInTerm d cutoff r) (shiftDimInTerm d cutoff p) (shiftDimInTerm d cutoff q)
    | .emptyF => .emptyF
    | .emptyElimF m s => .emptyElimF (shiftDimInTerm d cutoff m) (shiftDimInTerm d cutoff s)
    | .unitF => .unitF
    | .starF => .starF
    | .boolElimF m t f s => .boolElimF (shiftDimInTerm d cutoff m) (shiftDimInTerm d cutoff t)
        (shiftDimInTerm d cutoff f) (shiftDimInTerm d cutoff s)
    | .sigmaF dom cod => .sigmaF (shiftDimInTerm d cutoff dom) (shiftDimInTerm d cutoff cod)
    | .pairF a b => .pairF (shiftDimInTerm d cutoff a) (shiftDimInTerm d cutoff b)
    | .fstF p => .fstF (shiftDimInTerm d cutoff p)
    | .sndF p => .sndF (shiftDimInTerm d cutoff p)
    | .pathType ty a0 a1 =>
      .pathType (shiftDimInTerm d (cutoff + 1) ty) (shiftDimInTerm d cutoff a0) (shiftDimInTerm d cutoff a1)
    | .pathLam body => .pathLam (shiftDimInTerm d (cutoff + 1) body)
    | .pathApp p a0 a1 r =>
      .pathApp (shiftDimInTerm d cutoff p) (shiftDimInTerm d cutoff a0)
        (shiftDimInTerm d cutoff a1) (shiftDimInDim d cutoff r)
    | .coe r r' ty m =>
      .coe (shiftDimInDim d cutoff r) (shiftDimInDim d cutoff r')
        (shiftDimInTerm d (cutoff + 1) ty) (shiftDimInTerm d cutoff m)
    | .hcom r r' ty tubes u0 =>
      .hcom (shiftDimInDim d cutoff r) (shiftDimInDim d cutoff r')
        (shiftDimInTerm d cutoff ty) (shiftDimInTubes d cutoff tubes) (shiftDimInTerm d cutoff u0)
    | .vType r a b f g sec ret =>
      .vType (shiftDimInDim d cutoff r) (shiftDimInTerm d cutoff a) (shiftDimInTerm d cutoff b)
        (shiftDimInTerm d cutoff f) (shiftDimInTerm d cutoff g)
        (shiftDimInTerm d cutoff sec) (shiftDimInTerm d cutoff ret)
    | .vIn r a b => .vIn (shiftDimInDim d cutoff r) (shiftDimInTerm d cutoff a) (shiftDimInTerm d cutoff b)
    | .vProj r a b f v =>
      .vProj (shiftDimInDim d cutoff r) (shiftDimInTerm d cutoff a) (shiftDimInTerm d cutoff b)
        (shiftDimInTerm d cutoff f) (shiftDimInTerm d cutoff v)

  def shiftDimInTubes (d cutoff : Nat) : Tubes → Tubes
    | .nil => .nil
    | .cons c b rest =>
      .cons (shiftDimInCof d cutoff c) (shiftDimInTerm d (cutoff + 1) b) (shiftDimInTubes d cutoff rest)
end

mutual
  /-- Substitute `s` for dimension variable `j` in `Term`. -/
  def substDimInTerm (j : Nat) (s : Dim) : Term → Term
    | .univS l => .univS l
    | .univF l => .univF l
    | .boolS => .boolS
    | .boolF => .boolF
    | .trueF => .trueF
    | .falseF => .falseF
    | .var idx => .var idx
    | .piS dom cod => .piS (substDimInTerm j s dom) (substDimInTerm j s cod)
    | .piF dom cod => .piF (substDimInTerm j s dom) (substDimInTerm j s cod)
    | .lamS dom body => .lamS (substDimInTerm j s dom) (substDimInTerm j s body)
    | .lamF dom body => .lamF (substDimInTerm j s dom) (substDimInTerm j s body)
    | .appS fn arg => .appS (substDimInTerm j s fn) (substDimInTerm j s arg)
    | .appF fn arg => .appF (substDimInTerm j s fn) (substDimInTerm j s arg)
    | .liftFtoS i => .liftFtoS (substDimInTerm j s i)
    | .innerUnivalence a => .innerUnivalence (substDimInTerm j s a)
    | .innerCoalgebraNu a => .innerCoalgebraNu (substDimInTerm j s a)
    | .outerStrictEq l r => .outerStrictEq (substDimInTerm j s l) (substDimInTerm j s r)
    | .smallnessReplacement a => .smallnessReplacement (substDimInTerm j s a)
    | .unitS => .unitS
    | .starS => .starS
    | .sigmaS dom cod => .sigmaS (substDimInTerm j s dom) (substDimInTerm j s cod)
    | .pairS a b => .pairS (substDimInTerm j s a) (substDimInTerm j s b)
    | .fstS p => .fstS (substDimInTerm j s p)
    | .sndS p => .sndS (substDimInTerm j s p)
    | .eqS ty l r => .eqS (substDimInTerm j s ty) (substDimInTerm j s l) (substDimInTerm j s r)
    | .reflS a => .reflS (substDimInTerm j s a)
    | .uipS ty l r p q => .uipS (substDimInTerm j s ty) (substDimInTerm j s l)
        (substDimInTerm j s r) (substDimInTerm j s p) (substDimInTerm j s q)
    | .emptyF => .emptyF
    | .emptyElimF m sc => .emptyElimF (substDimInTerm j s m) (substDimInTerm j s sc)
    | .unitF => .unitF
    | .starF => .starF
    | .boolElimF m t f sc => .boolElimF (substDimInTerm j s m) (substDimInTerm j s t)
        (substDimInTerm j s f) (substDimInTerm j s sc)
    | .sigmaF dom cod => .sigmaF (substDimInTerm j s dom) (substDimInTerm j s cod)
    | .pairF a b => .pairF (substDimInTerm j s a) (substDimInTerm j s b)
    | .fstF p => .fstF (substDimInTerm j s p)
    | .sndF p => .sndF (substDimInTerm j s p)
    | .pathType ty a0 a1 =>
      .pathType (substDimInTerm (j + 1) s ty) (substDimInTerm j s a0) (substDimInTerm j s a1)
    | .pathLam body => .pathLam (substDimInTerm (j + 1) s body)
    | .pathApp p a0 a1 r =>
      .pathApp (substDimInTerm j s p) (substDimInTerm j s a0)
        (substDimInTerm j s a1) (substDimInDim j s r)
    | .coe r r' ty m =>
      .coe (substDimInDim j s r) (substDimInDim j s r')
        (substDimInTerm (j + 1) s ty) (substDimInTerm j s m)
    | .hcom r r' ty tubes u0 =>
      .hcom (substDimInDim j s r) (substDimInDim j s r')
        (substDimInTerm j s ty) (substDimInTubes j s tubes) (substDimInTerm j s u0)
    | .vType r a b f g sec ret =>
      .vType (substDimInDim j s r) (substDimInTerm j s a) (substDimInTerm j s b)
        (substDimInTerm j s f) (substDimInTerm j s g)
        (substDimInTerm j s sec) (substDimInTerm j s ret)
    | .vIn r a b => .vIn (substDimInDim j s r) (substDimInTerm j s a) (substDimInTerm j s b)
    | .vProj r a b f v =>
      .vProj (substDimInDim j s r) (substDimInTerm j s a) (substDimInTerm j s b)
        (substDimInTerm j s f) (substDimInTerm j s v)

  def substDimInTubes (j : Nat) (s : Dim) : Tubes → Tubes
    | .nil => .nil
    | .cons c b rest =>
      .cons (substDimInCof j s c) (substDimInTerm (j + 1) s b) (substDimInTubes j s rest)
end

mutual
  /-- Check if dimension variable `i` occurs free in `Term`. -/
  def dimOccursInTerm (i : Nat) : Term → Bool
    | .univS _ => false
    | .univF _ => false
    | .boolS => false
    | .boolF => false
    | .trueF => false
    | .falseF => false
    | .var _ => false
    | .piS d c => dimOccursInTerm i d || dimOccursInTerm i c
    | .piF d c => dimOccursInTerm i d || dimOccursInTerm i c
    | .lamS d b => dimOccursInTerm i d || dimOccursInTerm i b
    | .lamF d b => dimOccursInTerm i d || dimOccursInTerm i b
    | .appS f a => dimOccursInTerm i f || dimOccursInTerm i a
    | .appF f a => dimOccursInTerm i f || dimOccursInTerm i a
    | .liftFtoS x => dimOccursInTerm i x
    | .innerUnivalence x => dimOccursInTerm i x
    | .innerCoalgebraNu x => dimOccursInTerm i x
    | .outerStrictEq l r => dimOccursInTerm i l || dimOccursInTerm i r
    | .smallnessReplacement x => dimOccursInTerm i x
    | .unitS => false
    | .starS => false
    | .sigmaS d c => dimOccursInTerm i d || dimOccursInTerm i c
    | .pairS a b => dimOccursInTerm i a || dimOccursInTerm i b
    | .fstS p => dimOccursInTerm i p
    | .sndS p => dimOccursInTerm i p
    | .eqS t l r => dimOccursInTerm i t || dimOccursInTerm i l || dimOccursInTerm i r
    | .reflS a => dimOccursInTerm i a
    | .uipS t l r p q =>
      dimOccursInTerm i t || dimOccursInTerm i l || dimOccursInTerm i r ||
      dimOccursInTerm i p || dimOccursInTerm i q
    | .emptyF => false
    | .emptyElimF m s => dimOccursInTerm i m || dimOccursInTerm i s
    | .unitF => false
    | .starF => false
    | .boolElimF m t f s =>
      dimOccursInTerm i m || dimOccursInTerm i t || dimOccursInTerm i f || dimOccursInTerm i s
    | .sigmaF d c => dimOccursInTerm i d || dimOccursInTerm i c
    | .pairF a b => dimOccursInTerm i a || dimOccursInTerm i b
    | .fstF p => dimOccursInTerm i p
    | .sndF p => dimOccursInTerm i p
    | .pathType ty a0 a1 =>
      dimOccursInTerm (i + 1) ty || dimOccursInTerm i a0 || dimOccursInTerm i a1
    | .pathLam b => dimOccursInTerm (i + 1) b
    | .pathApp p a0 a1 r =>
      dimOccursInTerm i p || dimOccursInTerm i a0 || dimOccursInTerm i a1 || dimOccursInDim i r
    | .coe r r' ty m =>
      dimOccursInDim i r || dimOccursInDim i r' || dimOccursInTerm (i + 1) ty || dimOccursInTerm i m
    | .hcom r r' ty tubes u0 =>
      dimOccursInDim i r || dimOccursInDim i r' || dimOccursInTerm i ty ||
      dimOccursInTubes i tubes || dimOccursInTerm i u0
    | .vType r a b f g sec ret =>
      dimOccursInDim i r || dimOccursInTerm i a || dimOccursInTerm i b ||
      dimOccursInTerm i f || dimOccursInTerm i g || dimOccursInTerm i sec || dimOccursInTerm i ret
    | .vIn r a b => dimOccursInDim i r || dimOccursInTerm i a || dimOccursInTerm i b
    | .vProj r a b f v =>
      dimOccursInDim i r || dimOccursInTerm i a || dimOccursInTerm i b ||
      dimOccursInTerm i f || dimOccursInTerm i v

  def dimOccursInTubes (i : Nat) : Tubes → Bool
    | .nil => false
    | .cons c b rest => dimOccursInCof i c || dimOccursInTerm (i + 1) b || dimOccursInTubes i rest
end

mutual
  /-- Shift free term de Bruijn indices `≥ cutoff` by `d`. -/
  def shiftTerm (d cutoff : Nat) : Term → Term
    | .univS l => .univS l
    | .univF l => .univF l
    | .boolS => .boolS
    | .boolF => .boolF
    | .trueF => .trueF
    | .falseF => .falseF
    | .var idx => if idx >= cutoff then .var (idx + d) else .var idx
    | .piS dom cod => .piS (shiftTerm d cutoff dom) (shiftTerm d (cutoff + 1) cod)
    | .piF dom cod => .piF (shiftTerm d cutoff dom) (shiftTerm d (cutoff + 1) cod)
    | .lamS dom body => .lamS (shiftTerm d cutoff dom) (shiftTerm d (cutoff + 1) body)
    | .lamF dom body => .lamF (shiftTerm d cutoff dom) (shiftTerm d (cutoff + 1) body)
    | .appS fn arg => .appS (shiftTerm d cutoff fn) (shiftTerm d cutoff arg)
    | .appF fn arg => .appF (shiftTerm d cutoff fn) (shiftTerm d cutoff arg)
    | .liftFtoS i => .liftFtoS (shiftTerm d cutoff i)
    | .innerUnivalence a => .innerUnivalence (shiftTerm d cutoff a)
    | .innerCoalgebraNu a => .innerCoalgebraNu (shiftTerm d cutoff a)
    | .outerStrictEq l r => .outerStrictEq (shiftTerm d cutoff l) (shiftTerm d cutoff r)
    | .smallnessReplacement a => .smallnessReplacement (shiftTerm d cutoff a)
    | .unitS => .unitS
    | .starS => .starS
    | .sigmaS dom cod => .sigmaS (shiftTerm d cutoff dom) (shiftTerm d (cutoff + 1) cod)
    | .pairS a b => .pairS (shiftTerm d cutoff a) (shiftTerm d cutoff b)
    | .fstS p => .fstS (shiftTerm d cutoff p)
    | .sndS p => .sndS (shiftTerm d cutoff p)
    | .eqS ty l r => .eqS (shiftTerm d cutoff ty) (shiftTerm d cutoff l) (shiftTerm d cutoff r)
    | .reflS a => .reflS (shiftTerm d cutoff a)
    | .uipS ty l r p q => .uipS (shiftTerm d cutoff ty) (shiftTerm d cutoff l)
        (shiftTerm d cutoff r) (shiftTerm d cutoff p) (shiftTerm d cutoff q)
    | .emptyF => .emptyF
    | .emptyElimF m s => .emptyElimF (shiftTerm d (cutoff + 1) m) (shiftTerm d cutoff s)
    | .unitF => .unitF
    | .starF => .starF
    | .boolElimF m t f s => .boolElimF (shiftTerm d (cutoff + 1) m) (shiftTerm d cutoff t)
        (shiftTerm d cutoff f) (shiftTerm d cutoff s)
    | .sigmaF dom cod => .sigmaF (shiftTerm d cutoff dom) (shiftTerm d (cutoff + 1) cod)
    | .pairF a b => .pairF (shiftTerm d cutoff a) (shiftTerm d cutoff b)
    | .fstF p => .fstF (shiftTerm d cutoff p)
    | .sndF p => .sndF (shiftTerm d cutoff p)
    | .pathType ty a0 a1 => .pathType (shiftTerm d cutoff ty) (shiftTerm d cutoff a0) (shiftTerm d cutoff a1)
    | .pathLam b => .pathLam (shiftTerm d cutoff b)
    | .pathApp p a0 a1 r => .pathApp (shiftTerm d cutoff p) (shiftTerm d cutoff a0) (shiftTerm d cutoff a1) r
    | .coe r r' ty m => .coe r r' (shiftTerm d cutoff ty) (shiftTerm d cutoff m)
    | .hcom r r' ty tubes u0 =>
      .hcom r r' (shiftTerm d cutoff ty) (shiftTubesTerm d cutoff tubes) (shiftTerm d cutoff u0)
    | .vType r a b f g sec ret =>
      .vType r (shiftTerm d cutoff a) (shiftTerm d cutoff b) (shiftTerm d cutoff f)
        (shiftTerm d cutoff g) (shiftTerm d cutoff sec) (shiftTerm d cutoff ret)
    | .vIn r a b => .vIn r (shiftTerm d cutoff a) (shiftTerm d cutoff b)
    | .vProj r a b f v =>
      .vProj r (shiftTerm d cutoff a) (shiftTerm d cutoff b) (shiftTerm d cutoff f) (shiftTerm d cutoff v)

  def shiftTubesTerm (d cutoff : Nat) : Tubes → Tubes
    | .nil => .nil
    | .cons c b rest => .cons c (shiftTerm d cutoff b) (shiftTubesTerm d cutoff rest)
end

mutual
  /-- Substitute `s` for de Bruijn term variable `j` and shift higher indices down by 1. -/
  def substTerm (j : Nat) (s : Term) : Term → Term
    | .univS l => .univS l
    | .univF l => .univF l
    | .boolS => .boolS
    | .boolF => .boolF
    | .trueF => .trueF
    | .falseF => .falseF
    | .var idx =>
      if idx == j then shiftTerm j 0 s
      else if idx > j then .var (idx - 1)
      else .var idx
    | .piS dom cod => .piS (substTerm j s dom) (substTerm (j + 1) s cod)
    | .piF dom cod => .piF (substTerm j s dom) (substTerm (j + 1) s cod)
    | .lamS dom body => .lamS (substTerm j s dom) (substTerm (j + 1) s body)
    | .lamF dom body => .lamF (substTerm j s dom) (substTerm (j + 1) s body)
    | .appS fn arg => .appS (substTerm j s fn) (substTerm j s arg)
    | .appF fn arg => .appF (substTerm j s fn) (substTerm j s arg)
    | .liftFtoS i => .liftFtoS (substTerm j s i)
    | .innerUnivalence a => .innerUnivalence (substTerm j s a)
    | .innerCoalgebraNu a => .innerCoalgebraNu (substTerm j s a)
    | .outerStrictEq l r => .outerStrictEq (substTerm j s l) (substTerm j s r)
    | .smallnessReplacement a => .smallnessReplacement (substTerm j s a)
    | .unitS => .unitS
    | .starS => .starS
    | .sigmaS dom cod => .sigmaS (substTerm j s dom) (substTerm (j + 1) s cod)
    | .pairS a b => .pairS (substTerm j s a) (substTerm j s b)
    | .fstS p => .fstS (substTerm j s p)
    | .sndS p => .sndS (substTerm j s p)
    | .eqS ty l r => .eqS (substTerm j s ty) (substTerm j s l) (substTerm j s r)
    | .reflS a => .reflS (substTerm j s a)
    | .uipS ty l r p q => .uipS (substTerm j s ty) (substTerm j s l)
        (substTerm j s r) (substTerm j s p) (substTerm j s q)
    | .emptyF => .emptyF
    | .emptyElimF m sc => .emptyElimF (substTerm (j + 1) s m) (substTerm j s sc)
    | .unitF => .unitF
    | .starF => .starF
    | .boolElimF m t f sc => .boolElimF (substTerm (j + 1) s m) (substTerm j s t)
        (substTerm j s f) (substTerm j s sc)
    | .sigmaF dom cod => .sigmaF (substTerm j s dom) (substTerm (j + 1) s cod)
    | .pairF a b => .pairF (substTerm j s a) (substTerm j s b)
    | .fstF p => .fstF (substTerm j s p)
    | .sndF p => .sndF (substTerm j s p)
    | .pathType ty a0 a1 =>
      .pathType (substTerm j (shiftDimInTerm 1 0 s) ty) (substTerm j s a0) (substTerm j s a1)
    | .pathLam b => .pathLam (substTerm j (shiftDimInTerm 1 0 s) b)
    | .pathApp p a0 a1 r => .pathApp (substTerm j s p) (substTerm j s a0) (substTerm j s a1) r
    | .coe r r' ty m => .coe r r' (substTerm j (shiftDimInTerm 1 0 s) ty) (substTerm j s m)
    | .hcom r r' ty tubes u0 =>
      .hcom r r' (substTerm j s ty) (substTubesTerm j (shiftDimInTerm 1 0 s) tubes) (substTerm j s u0)
    | .vType r a b f g sec ret =>
      .vType r (substTerm j s a) (substTerm j s b) (substTerm j s f)
        (substTerm j s g) (substTerm j s sec) (substTerm j s ret)
    | .vIn r a b => .vIn r (substTerm j s a) (substTerm j s b)
    | .vProj r a b f v =>
      .vProj r (substTerm j s a) (substTerm j s b) (substTerm j s f) (substTerm j s v)

  def substTubesTerm (j : Nat) (s : Term) : Tubes → Tubes
    | .nil => .nil
    | .cons c b rest => .cons c (substTerm j s b) (substTubesTerm j s rest)
end

/-- Shift free dimension variables in a term context list when entering a dimension binder. -/
def shiftDimInCtx (d cutoff : Nat) : List Term → List Term
  | [] => []
  | ty :: rest => shiftDimInTerm d cutoff ty :: shiftDimInCtx d cutoff rest

end ShiftSubst
end KernelArena
