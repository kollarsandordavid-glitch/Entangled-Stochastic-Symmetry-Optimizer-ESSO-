inductive F64Repr : Type where
  | mk : Bool → Nat → Nat → F64Repr

inductive F64Class : Type where
  | normal : F64Class
  | subnormal : F64Class
  | zero : F64Class
  | infinity : F64Class
  | nan : F64Class

def f64ExponentBias : Nat := 1023
def f64MantissaBits : Nat := 52
def f64MaxExponent : Nat := 2047

def f64Classify (x : F64Repr) : F64Class :=
  F64Repr.casesOn x (fun _ exp mant =>
    Nat.casesOn exp
      (Nat.casesOn mant F64Class.zero (fun _ => F64Class.subnormal))
      (fun exp' =>
        Bool.casesOn (Nat.beq (Nat.succ exp') f64MaxExponent)
          (F64Class.normal)
          (Nat.casesOn mant F64Class.infinity (fun _ => F64Class.nan))))

def f64IsNaN (x : F64Repr) : Bool :=
  F64Class.casesOn (f64Classify x) Bool.false Bool.false Bool.false Bool.false Bool.true

def f64IsInfinite (x : F64Repr) : Bool :=
  F64Class.casesOn (f64Classify x) Bool.false Bool.false Bool.false Bool.true Bool.false

def f64IsFinite (x : F64Repr) : Bool :=
  F64Class.casesOn (f64Classify x) Bool.true Bool.true Bool.true Bool.false Bool.false

def f64IsZero (x : F64Repr) : Bool :=
  F64Class.casesOn (f64Classify x) Bool.false Bool.false Bool.true Bool.false Bool.false

def f64Sign (x : F64Repr) : Bool :=
  F64Repr.casesOn x (fun s _ _ => s)

def f64Exponent (x : F64Repr) : Nat :=
  F64Repr.casesOn x (fun _ e _ => e)

def f64Mantissa (x : F64Repr) : Nat :=
  F64Repr.casesOn x (fun _ _ m => m)

def f64Zero : F64Repr := F64Repr.mk Bool.true 0 0
def f64NegZero : F64Repr := F64Repr.mk Bool.false 0 0
def f64One : F64Repr := F64Repr.mk Bool.true f64ExponentBias 0
def f64NaN : F64Repr := F64Repr.mk Bool.true f64MaxExponent 1
def f64PosInf : F64Repr := F64Repr.mk Bool.true f64MaxExponent 0
def f64NegInf : F64Repr := F64Repr.mk Bool.false f64MaxExponent 0

def f64Negate (x : F64Repr) : F64Repr :=
  F64Repr.casesOn x (fun s e m =>
    Bool.casesOn s (F64Repr.mk Bool.true e m) (F64Repr.mk Bool.false e m))

def f64Abs (x : F64Repr) : F64Repr :=
  F64Repr.casesOn x (fun _ e m => F64Repr.mk Bool.true e m)

inductive RoundingMode : Type where
  | nearestEven : RoundingMode
  | towardZero : RoundingMode
  | towardPosInf : RoundingMode
  | towardNegInf : RoundingMode

def defaultRounding : RoundingMode := RoundingMode.nearestEven

inductive Rat : Type where
  | mk : Bool → Nat → Nat → Rat

def ratSign (r : Rat) : Bool := Rat.casesOn r (fun s _ _ => s)
def ratNum (r : Rat) : Nat := Rat.casesOn r (fun _ n _ => n)
def ratDen (r : Rat) : Nat := Rat.casesOn r (fun _ _ d => d)

def ratZero : Rat := Rat.mk Bool.true 0 1
def ratOne : Rat := Rat.mk Bool.true 1 1
def ratTwo : Rat := Rat.mk Bool.true 2 1

def gcdNat (fuel : Nat) (a b : Nat) : Nat :=
  Nat.recOn fuel a (fun fuel' ih =>
    Nat.casesOn b a (fun b' =>
      ih (Nat.succ b') (Nat.mod a (Nat.succ b'))))

def ratNormalize (r : Rat) : Rat :=
  Rat.casesOn r (fun s n d =>
    Nat.casesOn n (Rat.mk Bool.true 0 1)
      (fun n' =>
        Nat.casesOn d (Rat.mk Bool.true 0 1)
          (fun d' =>
            let g := gcdNat (Nat.add (Nat.succ n') (Nat.succ d')) (Nat.succ n') (Nat.succ d')
            Nat.casesOn g (Rat.mk s (Nat.succ n') (Nat.succ d'))
              (fun g' =>
                Rat.mk s (Nat.div (Nat.succ n') (Nat.succ g')) (Nat.div (Nat.succ d') (Nat.succ g'))))))

def ratNeg (r : Rat) : Rat :=
  Rat.casesOn r (fun s n d =>
    Nat.casesOn n (Rat.mk Bool.true 0 d)
      (fun n' => Bool.casesOn s (Rat.mk Bool.true (Nat.succ n') d) (Rat.mk Bool.false (Nat.succ n') d)))

def ratAbs (r : Rat) : Rat :=
  Rat.casesOn r (fun _ n d => Rat.mk Bool.true n d)

def ratAdd (x y : Rat) : Rat :=
  Rat.casesOn x (fun sx nx dx =>
    Rat.casesOn y (fun sy ny dy =>
      Nat.casesOn dx ratZero (fun dx' =>
        Nat.casesOn dy ratZero (fun dy' =>
          let crossA := Nat.mul nx (Nat.succ dy')
          let crossB := Nat.mul ny (Nat.succ dx')
          let newDen := Nat.mul (Nat.succ dx') (Nat.succ dy')
          Bool.casesOn sx
            (Bool.casesOn sy
              (Rat.mk Bool.false (Nat.add crossA crossB) newDen)
              (Bool.casesOn (Nat.ble crossA crossB)
                (Rat.mk Bool.false (Nat.sub crossA crossB) newDen)
                (Rat.mk Bool.true (Nat.sub crossB crossA) newDen)))
            (Bool.casesOn sy
              (Bool.casesOn (Nat.ble crossB crossA)
                (Rat.mk Bool.true (Nat.sub crossB crossA) newDen)
                (Rat.mk Bool.false (Nat.sub crossA crossB) newDen))
              (Rat.mk Bool.true (Nat.add crossA crossB) newDen))))))

def ratSub (x y : Rat) : Rat := ratAdd x (ratNeg y)

def ratMul (x y : Rat) : Rat :=
  Rat.casesOn x (fun sx nx dx =>
    Rat.casesOn y (fun sy ny dy =>
      let newSign := Bool.casesOn sx
        (Bool.casesOn sy Bool.true Bool.false)
        (Bool.casesOn sy Bool.false Bool.true)
      let newNum := Nat.mul nx ny
      let newDen := Nat.mul dx dy
      Nat.casesOn newDen
        (Rat.mk Bool.true 0 1)
        (fun _ => ratNormalize (Rat.mk newSign newNum newDen))))

def ratDiv (x y : Rat) : Rat :=
  Rat.casesOn y (fun sy ny dy =>
    Nat.casesOn ny ratZero
      (fun ny' =>
        ratMul x (Rat.mk sy dy (Nat.succ ny'))))

def ratLe (x y : Rat) : Bool :=
  Rat.casesOn x (fun sx nx dx =>
    Rat.casesOn y (fun sy ny dy =>
      Bool.casesOn sx
        (Bool.casesOn sy
          (Nat.ble (Nat.mul ny dy) (Nat.mul nx dx))
          Bool.true)
        (Bool.casesOn sy
          Bool.false
          (Nat.ble (Nat.mul nx dy) (Nat.mul ny dx)))))

def ratLt (x y : Rat) : Bool :=
  Bool.and (ratLe x y) (Bool.casesOn (ratLe y x) Bool.true Bool.false)

def ratEq (x y : Rat) : Bool :=
  Bool.and (ratLe x y) (ratLe y x)

def ratMax (x y : Rat) : Rat :=
  Bool.casesOn (ratLe x y) x y

def ratMin (x y : Rat) : Rat :=
  Bool.casesOn (ratLe x y) y x

def ratFromNat (n : Nat) : Rat := Rat.mk Bool.true n 1

def sqrtRatApprox (fuel : Nat) (guess x : Rat) : Rat :=
  Nat.recOn fuel guess (fun fuel' ih =>
    let newGuess := ratDiv (ratAdd ih (ratDiv x ih)) ratTwo
    newGuess)

def ratSqrt (x : Rat) : Rat :=
  Bool.casesOn (ratLe ratZero x) ratZero (sqrtRatApprox 20 ratOne x)

def ratInvSqrt2 : Rat := ratSqrt (ratDiv ratOne ratTwo)

def ratPiNum : Nat := 314159265
def ratPiDen : Nat := 100000000
def ratPi : Rat := Rat.mk Bool.true ratPiNum ratPiDen

def ratTwoPi : Rat := ratMul ratTwo ratPi

def ratPiHalf : Rat := ratDiv ratPi ratTwo

def ratHalf : Rat := Rat.mk Bool.true 1 2

def ratMod (x m : Rat) : Rat :=
  Rat.casesOn x (fun sx nx dx =>
    Rat.casesOn m (fun _ mn md =>
      Nat.casesOn mn (Rat.mk sx nx dx)
        (fun mn' =>
          Nat.casesOn md (Rat.mk sx nx dx)
            (fun md' =>
              let numScaled := Nat.mul nx (Nat.succ md')
              let denScaled := Nat.mul dx (Nat.succ mn')
              Nat.casesOn denScaled (Rat.mk sx nx dx)
                (fun ds' =>
                  let quotient := Nat.div numScaled (Nat.succ ds')
                  let remainder := Nat.sub numScaled (Nat.mul quotient (Nat.succ ds'))
                  let newDen := Nat.mul dx (Nat.succ md')
                  Nat.casesOn newDen (Rat.mk Bool.true 0 1)
                    (fun _ => ratNormalize (Rat.mk sx remainder newDen)))))))

def ratClampPhase (x : Rat) : Rat :=
  Bool.casesOn (ratLe ratZero x)
    (ratAdd x ratTwoPi)
    (Bool.casesOn (ratLe x ratTwoPi)
      x
      (ratMod x ratTwoPi))

inductive ComplexRat : Type where
  | mk : Rat → Rat → ComplexRat

def complexZero : ComplexRat := ComplexRat.mk ratZero ratZero
def complexOne : ComplexRat := ComplexRat.mk ratOne ratZero
def complexI : ComplexRat := ComplexRat.mk ratZero ratOne

def complexRe (z : ComplexRat) : Rat := ComplexRat.casesOn z (fun r _ => r)
def complexIm (z : ComplexRat) : Rat := ComplexRat.casesOn z (fun _ i => i)

def complexAdd (x y : ComplexRat) : ComplexRat :=
  ComplexRat.casesOn x (fun xr xi =>
    ComplexRat.casesOn y (fun yr yi =>
      ComplexRat.mk (ratAdd xr yr) (ratAdd xi yi)))

def complexSub (x y : ComplexRat) : ComplexRat :=
  ComplexRat.casesOn x (fun xr xi =>
    ComplexRat.casesOn y (fun yr yi =>
      ComplexRat.mk (ratSub xr yr) (ratSub xi yi)))

def complexMul (x y : ComplexRat) : ComplexRat :=
  ComplexRat.casesOn x (fun xr xi =>
    ComplexRat.casesOn y (fun yr yi =>
      ComplexRat.mk (ratSub (ratMul xr yr) (ratMul xi yi))
                    (ratAdd (ratMul xr yi) (ratMul xi yr))))

def complexConj (z : ComplexRat) : ComplexRat :=
  ComplexRat.casesOn z (fun r i => ComplexRat.mk r (ratNeg i))

def complexNormSq (z : ComplexRat) : Rat :=
  ComplexRat.casesOn z (fun r i =>
    ratAdd (ratMul r r) (ratMul i i))

def complexNeg (z : ComplexRat) : ComplexRat :=
  ComplexRat.casesOn z (fun r i => ComplexRat.mk (ratNeg r) (ratNeg i))

def complexScale (s : Rat) (z : ComplexRat) : ComplexRat :=
  ComplexRat.casesOn z (fun r i => ComplexRat.mk (ratMul s r) (ratMul s i))

def complexNorm (z : ComplexRat) : Rat := ratSqrt (complexNormSq z)

inductive AllocError : Type where
  | outOfMemory : AllocError
  | doubleFree : AllocError
  | useAfterFree : AllocError
  | invalidAlignment : AllocError

inductive AllocResult (α : Type) : Type where
  | ok : α → AllocResult α
  | err : AllocError → AllocResult α

def allocBind (x : AllocResult α) (f : α → AllocResult β) : AllocResult β :=
  AllocResult.casesOn x (fun a => f a) (fun e => AllocResult.err e)

def allocPure (a : α) : AllocResult α := AllocResult.ok a

def allocMap (f : α → β) (x : AllocResult α) : AllocResult β :=
  AllocResult.casesOn x (fun a => AllocResult.ok (f a)) (fun e => AllocResult.err e)

inductive MemBlock : Type where
  | mk : Nat → Nat → Bool → MemBlock

def memBlockAddr (b : MemBlock) : Nat := MemBlock.casesOn b (fun a _ _ => a)
def memBlockSize (b : MemBlock) : Nat := MemBlock.casesOn b (fun _ s _ => s)
def memBlockAlive (b : MemBlock) : Bool := MemBlock.casesOn b (fun _ _ a => a)

inductive MemState : Type where
  | mk : List MemBlock → Nat → Nat → MemState

def memBlocks (m : MemState) : List MemBlock := MemState.casesOn m (fun b _ _ => b)
def memNextAddr (m : MemState) : Nat := MemState.casesOn m (fun _ n _ => n)
def memTotalAllocated (m : MemState) : Nat := MemState.casesOn m (fun _ _ t => t)

def memInitial : MemState := MemState.mk [] 1 0

def memAlloc (m : MemState) (size : Nat) : AllocResult (Prod Nat MemState) :=
  MemState.casesOn m (fun blocks nextAddr totalAlloc =>
    let newBlock := MemBlock.mk nextAddr size Bool.true
    AllocResult.ok (Prod.mk nextAddr
      (MemState.mk (List.cons newBlock blocks) (Nat.add nextAddr size) (Nat.add totalAlloc size))))

def memFreeHelper (addr : Nat) (blocks : List MemBlock) : AllocResult (List MemBlock) :=
  List.recOn blocks
    (AllocResult.err AllocError.doubleFree)
    (fun hd tl ih =>
      MemBlock.casesOn hd (fun bAddr bSize bAlive =>
        Bool.casesOn (Nat.beq addr bAddr)
          (allocMap (fun rest => List.cons (MemBlock.mk bAddr bSize bAlive) rest) ih)
          (Bool.casesOn bAlive
            (AllocResult.err AllocError.doubleFree)
            (AllocResult.ok (List.cons (MemBlock.mk bAddr bSize Bool.false) tl)))))

def memFree (m : MemState) (addr : Nat) : AllocResult MemState :=
  MemState.casesOn m (fun blocks nextAddr totalAlloc =>
    allocMap (fun newBlocks => MemState.mk newBlocks nextAddr totalAlloc)
      (memFreeHelper addr blocks))

def memIsLive (m : MemState) (addr : Nat) : Bool :=
  List.recOn (memBlocks m) Bool.false
    (fun hd _ ih =>
      MemBlock.casesOn hd (fun bAddr _ bAlive =>
        Bool.casesOn (Nat.beq addr bAddr) ih bAlive))

inductive PrngState : Type where
  | mk : Nat → Nat → Nat → PrngState

def prngState0 (p : PrngState) : Nat := PrngState.casesOn p (fun s0 _ _ => s0)
def prngState1 (p : PrngState) : Nat := PrngState.casesOn p (fun _ s1 _ => s1)
def prngCounter (p : PrngState) : Nat := PrngState.casesOn p (fun _ _ c => c)

def prngInit (seed : Nat) : PrngState :=
  PrngState.mk seed (Nat.add seed 1) 0

def prngMixBits (x : Nat) : Nat :=
  let a := Nat.mul x 2654435761
  let b := Nat.div a 4
  Nat.add (Nat.mod a 4294967296) (Nat.mod b 4294967296)

def prngNextState (p : PrngState) : PrngState :=
  PrngState.casesOn p (fun s0 s1 counter =>
    let mixed0 := prngMixBits (Nat.add s0 s1)
    let mixed1 := prngMixBits (Nat.add s1 (Nat.add mixed0 counter))
    PrngState.mk (Nat.mod mixed0 4294967296) (Nat.mod mixed1 4294967296) (Nat.succ counter))

def prngNext (p : PrngState) : Prod Nat PrngState :=
  let next := prngNextState p
  Prod.mk (prngState0 next) next

def prngRatUnit (p : PrngState) : Prod Rat PrngState :=
  let result := prngNext p
  let denom : Nat := 1000000
  Prod.mk (Rat.mk Bool.true (Nat.mod (Prod.fst result) (Nat.succ denom)) (Nat.succ denom)) (Prod.snd result)

def prngNatMod (p : PrngState) (bound : Nat) : Prod Nat PrngState :=
  Nat.casesOn bound
    (Prod.mk 0 p)
    (fun bound' =>
      let result := prngNext p
      Prod.mk (Nat.mod (Prod.fst result) (Nat.succ bound')) (Prod.snd result))

inductive Rotation : Type where
  | rot0 : Rotation
  | rot90 : Rotation
  | rot180 : Rotation
  | rot270 : Rotation

inductive SymGroup : Type where
  | identity : SymGroup
  | reflection : SymGroup
  | rotation90 : SymGroup
  | rotation180 : SymGroup
  | rotation270 : SymGroup
  | translation : SymGroup

inductive EdgeQuality : Type where
  | coherent : EdgeQuality
  | decoherent : EdgeQuality
  | entangled : EdgeQuality
  | classical : EdgeQuality

def symGroupToNat (g : SymGroup) : Nat :=
  SymGroup.casesOn g 0 1 2 3 4 5

def symGroupOrder (g : SymGroup) : Nat :=
  SymGroup.casesOn g 1 2 4 2 4 0

def symGroupAngle (g : SymGroup) : Rat :=
  SymGroup.casesOn g ratZero ratZero ratPiHalf ratPi (ratMul (ratFromNat 3) ratPiHalf) ratZero

def edgeQualityToNat (eq_ : EdgeQuality) : Nat :=
  EdgeQuality.casesOn eq_ 0 1 2 3

def rotToNat (r : Rotation) : Nat :=
  Rotation.casesOn r 0 1 2 3

def mod4 (n : Nat) : Nat :=
  Nat.recOn n 0
    (fun _ ih =>
      Nat.casesOn ih 1
        (fun ih' => Nat.casesOn ih' 2
          (fun ih'' => Nat.casesOn ih'' 3
            (fun _ => 0))))

def natToRot (n : Nat) : Rotation :=
  let m := mod4 n
  Nat.casesOn m Rotation.rot0
    (fun m' => Nat.casesOn m' Rotation.rot90
      (fun m'' => Nat.casesOn m'' Rotation.rot180
        (fun _ => Rotation.rot270)))

def rotCompose (a b : Rotation) : Rotation :=
  natToRot (Nat.add (rotToNat a) (rotToNat b))

def rotInverse (r : Rotation) : Rotation :=
  Rotation.casesOn r Rotation.rot0 Rotation.rot270 Rotation.rot180 Rotation.rot90

def rotAngle (r : Rotation) : Rat :=
  Rotation.casesOn r ratZero ratPiHalf ratPi (ratMul (ratFromNat 3) ratPiHalf)

inductive QubitState : Type where
  | mk : ComplexRat → ComplexRat → QubitState

def qubitAlpha (q : QubitState) : ComplexRat := QubitState.casesOn q (fun a _ => a)
def qubitBeta (q : QubitState) : ComplexRat := QubitState.casesOn q (fun _ b => b)

def qubitBasis0 : QubitState := QubitState.mk complexOne complexZero
def qubitBasis1 : QubitState := QubitState.mk complexZero complexOne

def qubitPlus : QubitState :=
  QubitState.mk (ComplexRat.mk ratInvSqrt2 ratZero) (ComplexRat.mk ratInvSqrt2 ratZero)

def qubitNormSq (q : QubitState) : Rat :=
  QubitState.casesOn q (fun a b =>
    ratAdd (complexNormSq a) (complexNormSq b))

def qubitIsNormalized (q : QubitState) (tolerance : Rat) : Bool :=
  let ns := qubitNormSq q
  let diff := ratSub ns ratOne
  let absDiff := ratAbs diff
  ratLe absDiff tolerance

def qubitNormalize (q : QubitState) : QubitState :=
  QubitState.casesOn q (fun a b =>
    let ns := ratAdd (complexNormSq a) (complexNormSq b)
    let norm := ratSqrt ns
    Bool.casesOn (ratEq norm ratZero)
      (QubitState.mk (complexScale (ratDiv ratOne norm) a)
                     (complexScale (ratDiv ratOne norm) b))
      qubitBasis0)

inductive QuantumState : Type where
  | mk : Rat → Rat → Rat → Rat → QuantumState

def qsAmplReal (qs : QuantumState) : Rat := QuantumState.casesOn qs (fun r _ _ _ => r)
def qsAmplImag (qs : QuantumState) : Rat := QuantumState.casesOn qs (fun _ i _ _ => i)
def qsPhase (qs : QuantumState) : Rat := QuantumState.casesOn qs (fun _ _ p _ => p)
def qsEntDegree (qs : QuantumState) : Rat := QuantumState.casesOn qs (fun _ _ _ e => e)

inductive NodeId : Type where
  | mk : Nat → NodeId

def nodeIdVal (n : NodeId) : Nat := NodeId.casesOn n id

def nodeIdEq (a b : NodeId) : Bool :=
  Nat.beq (nodeIdVal a) (nodeIdVal b)

inductive NodeData : Type where
  | mk : NodeId → Nat → QubitState → Rat → NodeData

def nodeId (n : NodeData) : NodeId := NodeData.casesOn n (fun nid _ _ _ => nid)
def nodeLabel (n : NodeData) : Nat := NodeData.casesOn n (fun _ l _ _ => l)
def nodeQubit (n : NodeData) : QubitState := NodeData.casesOn n (fun _ _ q _ => q)
def nodePhase (n : NodeData) : Rat := NodeData.casesOn n (fun _ _ _ p => p)

inductive EdgeData : Type where
  | mk : NodeId → NodeId → EdgeQuality → Rat → ComplexRat → Rat → EdgeData

def edgeSource (e : EdgeData) : NodeId := EdgeData.casesOn e (fun s _ _ _ _ _ => s)
def edgeTarget (e : EdgeData) : NodeId := EdgeData.casesOn e (fun _ t _ _ _ _ => t)
def edgeQuality (e : EdgeData) : EdgeQuality := EdgeData.casesOn e (fun _ _ q _ _ _ => q)
def edgeWeight (e : EdgeData) : Rat := EdgeData.casesOn e (fun _ _ _ w _ _ => w)
def edgeQuantumCorr (e : EdgeData) : ComplexRat := EdgeData.casesOn e (fun _ _ _ _ qc _ => qc)
def edgeFractalDim (e : EdgeData) : Rat := EdgeData.casesOn e (fun _ _ _ _ _ fd => fd)

inductive GraphData : Type where
  | mk : List NodeData → List EdgeData → Nat → GraphData

def graphNodes (g : GraphData) : List NodeData := GraphData.casesOn g (fun n _ _ => n)
def graphEdges (g : GraphData) : List EdgeData := GraphData.casesOn g (fun _ e _ => e)
def graphHash (g : GraphData) : Nat := GraphData.casesOn g (fun _ _ h => h)

def graphNodeCount (g : GraphData) : Nat :=
  List.recOn (graphNodes g) 0 (fun _ _ ih => Nat.succ ih)

def graphEdgeCount (g : GraphData) : Nat :=
  List.recOn (graphEdges g) 0 (fun _ _ ih => Nat.succ ih)

def emptyGraph : GraphData := GraphData.mk [] [] 0

def findNode (nid : NodeId) (nodes : List NodeData) : AllocResult NodeData :=
  List.recOn nodes
    (AllocResult.err AllocError.useAfterFree)
    (fun hd _ ih =>
      Bool.casesOn (nodeIdEq (nodeId hd) nid) ih (AllocResult.ok hd))

def nodeExists (nid : NodeId) (nodes : List NodeData) : Bool :=
  List.recOn nodes Bool.false
    (fun hd _ ih => Bool.casesOn (nodeIdEq (nodeId hd) nid) ih Bool.true)

def addNodeToGraph (g : GraphData) (nd : NodeData) (mem : MemState) :
    AllocResult (Prod GraphData MemState) :=
  GraphData.casesOn g (fun nodes edges hash =>
    Bool.casesOn (nodeExists (nodeId nd) nodes)
      (allocBind (memAlloc mem 1) (fun result =>
        AllocResult.ok (Prod.mk
          (GraphData.mk (List.cons nd nodes) edges (Nat.add hash 1))
          (Prod.snd result))))
      (AllocResult.ok (Prod.mk (GraphData.mk nodes edges hash) mem)))

def addEdgeToGraph (g : GraphData) (ed : EdgeData) (mem : MemState) :
    AllocResult (Prod GraphData MemState) :=
  GraphData.casesOn g (fun nodes edges hash =>
    Bool.casesOn (Bool.and (nodeExists (edgeSource ed) nodes) (nodeExists (edgeTarget ed) nodes))
      (AllocResult.err AllocError.useAfterFree)
      (allocBind (memAlloc mem 1) (fun result =>
        AllocResult.ok (Prod.mk
          (GraphData.mk nodes (List.cons ed edges) (Nat.add hash 1))
          (Prod.snd result)))))

def removeEdgeHelper (src tgt : NodeId) (edges : List EdgeData) : List EdgeData :=
  List.recOn edges []
    (fun hd _ ih =>
      Bool.casesOn (Bool.and (nodeIdEq (edgeSource hd) src) (nodeIdEq (edgeTarget hd) tgt))
        (List.cons hd ih) ih)

def removeEdge (g : GraphData) (src tgt : NodeId) : GraphData :=
  GraphData.casesOn g (fun nodes edges hash =>
    GraphData.mk nodes (removeEdgeHelper src tgt edges) hash)

def cloneNodeList (nodes : List NodeData) : List NodeData :=
  List.recOn nodes []
    (fun hd _ ih =>
      NodeData.casesOn hd (fun nid lbl qub ph =>
        List.cons (NodeData.mk nid lbl qub ph) ih))

def cloneEdgeList (edges : List EdgeData) : List EdgeData :=
  List.recOn edges []
    (fun hd _ ih =>
      EdgeData.casesOn hd (fun src tgt qual w qc fd =>
        List.cons (EdgeData.mk src tgt qual w qc fd) ih))

def cloneGraph (g : GraphData) (mem : MemState) : AllocResult (Prod GraphData MemState) :=
  GraphData.casesOn g (fun nodes edges hash =>
    let clonedNodes := cloneNodeList nodes
    let clonedEdges := cloneEdgeList edges
    allocBind (memAlloc mem (Nat.add (graphNodeCount g) (graphEdgeCount g))) (fun result =>
      AllocResult.ok (Prod.mk (GraphData.mk clonedNodes clonedEdges hash) (Prod.snd result))))

inductive NodePairKey : Type where
  | mk : NodeId → NodeId → NodePairKey

def nodePairEq (a b : NodePairKey) : Bool :=
  NodePairKey.casesOn a (fun a1 a2 =>
    NodePairKey.casesOn b (fun b1 b2 =>
      Bool.and (nodeIdEq a1 b1) (nodeIdEq a2 b2)))

def orderedPairKey (n1 n2 : NodeId) : NodePairKey :=
  Bool.casesOn (Nat.ble (nodeIdVal n1) (nodeIdVal n2))
    (NodePairKey.mk n2 n1)
    (NodePairKey.mk n1 n2)

inductive EntanglementInfo : Type where
  | mk : Rat → Rat → Nat → Nat → Nat → EntanglementInfo

def entCorrelation (e : EntanglementInfo) : Rat := EntanglementInfo.casesOn e (fun c _ _ _ _ => c)
def entPhaseDiff (e : EntanglementInfo) : Rat := EntanglementInfo.casesOn e (fun _ p _ _ _ => p)
def entCreationTime (e : EntanglementInfo) : Nat := EntanglementInfo.casesOn e (fun _ _ ct _ _ => ct)
def entLastUpdate (e : EntanglementInfo) : Nat := EntanglementInfo.casesOn e (fun _ _ _ lu _ => lu)
def entInteractionCount (e : EntanglementInfo) : Nat := EntanglementInfo.casesOn e (fun _ _ _ _ ic => ic)

def entUpdate (info : EntanglementInfo) (newCorr newPhase : Rat) : EntanglementInfo :=
  EntanglementInfo.casesOn info (fun corr _ ct lu ic =>
    let count := ratFromNat ic
    let newCorrAvg := ratDiv (ratAdd (ratMul corr count) newCorr) (ratAdd count ratOne)
    EntanglementInfo.mk newCorrAvg newPhase ct (Nat.succ lu) (Nat.succ ic))

def entDecay (info : EntanglementInfo) (decayFactor : Rat) : EntanglementInfo :=
  EntanglementInfo.casesOn info (fun corr phase ct lu ic =>
    EntanglementInfo.mk (ratMul corr decayFactor) phase ct (Nat.succ lu) ic)

inductive EntanglementEntry : Type where
  | mk : NodePairKey → EntanglementInfo → EntanglementEntry

def entEntryKey (e : EntanglementEntry) : NodePairKey := EntanglementEntry.casesOn e (fun k _ => k)
def entEntryInfo (e : EntanglementEntry) : EntanglementInfo := EntanglementEntry.casesOn e (fun _ i => i)

def lookupEntanglement (key : NodePairKey) (entries : List EntanglementEntry) :
    AllocResult EntanglementInfo :=
  List.recOn entries
    (AllocResult.err AllocError.useAfterFree)
    (fun hd _ ih =>
      Bool.casesOn (nodePairEq key (entEntryKey hd)) ih (AllocResult.ok (entEntryInfo hd)))

def hasEntanglement (key : NodePairKey) (entries : List EntanglementEntry) : Bool :=
  List.recOn entries Bool.false
    (fun hd _ ih => Bool.casesOn (nodePairEq key (entEntryKey hd)) ih Bool.true)

def addEntanglement (entries : List EntanglementEntry) (key : NodePairKey) (info : EntanglementInfo) :
    List EntanglementEntry :=
  List.cons (EntanglementEntry.mk key info) entries

def removeEntanglement (entries : List EntanglementEntry) (key : NodePairKey) :
    List EntanglementEntry :=
  List.recOn entries []
    (fun hd _ ih =>
      Bool.casesOn (nodePairEq key (entEntryKey hd)) (List.cons hd ih) ih)

def entanglementCount (entries : List EntanglementEntry) : Nat :=
  List.recOn entries 0 (fun _ _ ih => Nat.succ ih)

inductive OptState : Type where
  | mk : GraphData → Rat → Rat → Nat → List EntanglementEntry → OptState

def optGraph (s : OptState) : GraphData := OptState.casesOn s (fun g _ _ _ _ => g)
def optEnergy (s : OptState) : Rat := OptState.casesOn s (fun _ e _ _ _ => e)
def optEntPct (s : OptState) : Rat := OptState.casesOn s (fun _ _ p _ _ => p)
def optIteration (s : OptState) : Nat := OptState.casesOn s (fun _ _ _ i _ => i)
def optEntanglements (s : OptState) : List EntanglementEntry :=
  OptState.casesOn s (fun _ _ _ _ ents => ents)

def optWithGraph (s : OptState) (g : GraphData) : OptState :=
  OptState.casesOn s (fun _ e p i ents => OptState.mk g e p i ents)

def optWithEnergy (s : OptState) (e : Rat) : OptState :=
  OptState.casesOn s (fun g _ p i ents => OptState.mk g e p i ents)

def optWithEntanglements (s : OptState) (ents : List EntanglementEntry) : OptState :=
  OptState.casesOn s (fun g e p i _ => OptState.mk g e p i ents)

def emptyOptState : OptState := OptState.mk emptyGraph ratZero ratZero 0 []

def refreshEntanglementPct (s : OptState) : OptState :=
  let nc := graphNodeCount (optGraph s)
  let maxPairs := Nat.div (Nat.mul nc (Nat.sub nc 1)) 2
  let ec := entanglementCount (optEntanglements s)
  let pct := Nat.casesOn maxPairs ratZero
    (fun mp' => ratDiv (ratFromNat ec) (ratFromNat (Nat.succ mp')))
  OptState.casesOn s (fun g e _ i ents => OptState.mk g e pct i ents)

inductive OptStats : Type where
  | mk : Nat → Nat → Nat → Rat → Rat → Nat → Nat → Nat → Rat → Nat → Nat → Rat → Rat → Nat → Rat → OptStats

def statsIterations (s : OptStats) : Nat := OptStats.casesOn s (fun i _ _ _ _ _ _ _ _ _ _ _ _ _ _ => i)
def statsAccepted (s : OptStats) : Nat := OptStats.casesOn s (fun _ a _ _ _ _ _ _ _ _ _ _ _ _ _ => a)
def statsRejected (s : OptStats) : Nat := OptStats.casesOn s (fun _ _ r _ _ _ _ _ _ _ _ _ _ _ _ => r)
def statsBestEnergy (s : OptStats) : Rat := OptStats.casesOn s (fun _ _ _ b _ _ _ _ _ _ _ _ _ _ _ => b)
def statsCurrentEnergy (s : OptStats) : Rat := OptStats.casesOn s (fun _ _ _ _ c _ _ _ _ _ _ _ _ _ _ => c)
def statsSymmetries (s : OptStats) : Nat := OptStats.casesOn s (fun _ _ _ _ _ sy _ _ _ _ _ _ _ _ _ => sy)
def statsEntPairs (s : OptStats) : Nat := OptStats.casesOn s (fun _ _ _ _ _ _ ep _ _ _ _ _ _ _ _ => ep)
def statsElapsed (s : OptStats) : Nat := OptStats.casesOn s (fun _ _ _ _ _ _ _ el _ _ _ _ _ _ _ => el)
def statsAccRate (s : OptStats) : Rat := OptStats.casesOn s (fun _ _ _ _ _ _ _ _ ar _ _ _ _ _ _ => ar)
def statsCoolApplied (s : OptStats) : Nat := OptStats.casesOn s (fun _ _ _ _ _ _ _ _ _ ca _ _ _ _ _ => ca)
def statsEscapes (s : OptStats) : Nat := OptStats.casesOn s (fun _ _ _ _ _ _ _ _ _ _ esc _ _ _ _ => esc)
def statsConvDelta (s : OptStats) : Rat := OptStats.casesOn s (fun _ _ _ _ _ _ _ _ _ _ _ cd _ _ _ => cd)
def statsTemp (s : OptStats) : Rat := OptStats.casesOn s (fun _ _ _ _ _ _ _ _ _ _ _ _ t _ _ => t)
def statsTotalEvals (s : OptStats) : Nat := OptStats.casesOn s (fun _ _ _ _ _ _ _ _ _ _ _ _ _ te _ => te)
def statsAvgMoveDelta (s : OptStats) : Rat := OptStats.casesOn s (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ amd => amd)

def emptyStats : OptStats :=
  OptStats.mk 0 0 0 ratZero ratZero 0 0 0 ratZero 0 0 ratZero ratZero 0 ratZero

inductive SymTransform : Type where
  | mk : SymGroup → Rat → Rat → Rat → Rat → Rat → Rat → SymTransform

def stGroup (t : SymTransform) : SymGroup := SymTransform.casesOn t (fun g _ _ _ _ _ _ => g)
def stOriginX (t : SymTransform) : Rat := SymTransform.casesOn t (fun _ ox _ _ _ _ _ => ox)
def stOriginY (t : SymTransform) : Rat := SymTransform.casesOn t (fun _ _ oy _ _ _ _ => oy)
def stParam0 (t : SymTransform) : Rat := SymTransform.casesOn t (fun _ _ _ p0 _ _ _ => p0)
def stParam1 (t : SymTransform) : Rat := SymTransform.casesOn t (fun _ _ _ _ p1 _ _ => p1)
def stScale (t : SymTransform) : Rat := SymTransform.casesOn t (fun _ _ _ _ _ sc _ => sc)
def stParam3 (t : SymTransform) : Rat := SymTransform.casesOn t (fun _ _ _ _ _ _ p3 => p3)

def identityTransform : SymTransform :=
  SymTransform.mk SymGroup.identity ratZero ratZero ratZero ratZero ratOne ratZero

def applyTransform2D (t : SymTransform) (x y : Rat) : Prod Rat Rat :=
  let dx := ratSub x (stOriginX t)
  let dy := ratSub y (stOriginY t)
  let sc := stScale t
  SymGroup.casesOn (stGroup t)
    (Prod.mk x y)
    (Prod.mk (ratAdd (stOriginX t) (ratMul dx sc))
             (ratAdd (stOriginY t) (ratMul (ratNeg dy) sc)))
    (Prod.mk (ratAdd (stOriginX t) (ratMul (ratNeg dy) sc))
             (ratAdd (stOriginY t) (ratMul dx sc)))
    (Prod.mk (ratAdd (stOriginX t) (ratMul (ratNeg dx) sc))
             (ratAdd (stOriginY t) (ratMul (ratNeg dy) sc)))
    (Prod.mk (ratAdd (stOriginX t) (ratMul dy sc))
             (ratAdd (stOriginY t) (ratMul (ratNeg dx) sc)))
    (Prod.mk (ratAdd x (ratMul (stParam0 t) sc))
             (ratAdd y (ratMul (stParam1 t) sc)))

def applyTransformComplex (t : SymTransform) (z : ComplexRat) : ComplexRat :=
  let result := applyTransform2D t (complexRe z) (complexIm z)
  ComplexRat.mk (Prod.fst result) (Prod.snd result)

def applyTransformQuantumState (t : SymTransform) (qs : QuantumState) : QuantumState :=
  let phaseShift := symGroupAngle (stGroup t)
  let newPhase := ratClampPhase (ratAdd (qsPhase qs) phaseShift)
  QuantumState.mk (qsAmplReal qs) (qsAmplImag qs) newPhase (qsEntDegree qs)

def transformInverse (t : SymTransform) : SymTransform :=
  let invScale := ratDiv ratOne (stScale t)
  SymTransform.casesOn t (fun group ox oy p0 p1 _ p3 =>
    SymGroup.casesOn group
      t
      (SymTransform.mk SymGroup.reflection ox oy p0 p1 invScale p3)
      (SymTransform.mk SymGroup.rotation270 ox oy p0 p1 invScale p3)
      (SymTransform.mk SymGroup.rotation180 ox oy p0 p1 invScale p3)
      (SymTransform.mk SymGroup.rotation90 ox oy p0 p1 invScale p3)
      (SymTransform.mk SymGroup.translation ox oy (ratNeg p0) (ratNeg p1) invScale p3))

def transformDeterminant (t : SymTransform) : Rat :=
  let sc := stScale t
  let scSq := ratMul sc sc
  SymGroup.casesOn (stGroup t) scSq (ratNeg scSq) scSq scSq scSq scSq

def transformIsIsometry (t : SymTransform) : Bool :=
  let det := transformDeterminant t
  let absDet := ratAbs det
  ratEq absDet ratOne

inductive SymPattern : Type where
  | mk : Nat → SymTransform → List NodeId → Rat → Rat → Nat → SymPattern

def patternId (p : SymPattern) : Nat := SymPattern.casesOn p (fun pid _ _ _ _ _ => pid)
def patternTransform (p : SymPattern) : SymTransform := SymPattern.casesOn p (fun _ t _ _ _ _ => t)
def patternNodes (p : SymPattern) : List NodeId := SymPattern.casesOn p (fun _ _ ns _ _ _ => ns)
def patternScore (p : SymPattern) : Rat := SymPattern.casesOn p (fun _ _ _ s _ _ => s)
def patternResonance (p : SymPattern) : Rat := SymPattern.casesOn p (fun _ _ _ _ r _ => r)
def patternTimestamp (p : SymPattern) : Nat := SymPattern.casesOn p (fun _ _ _ _ _ ts => ts)

inductive MoveType : Type where
  | perturbWeights : MoveType
  | perturbPhases : MoveType
  | createEntanglement : MoveType
  | applySymmetry : MoveType
  | perturbQubits : MoveType
  | perturbFractalDim : MoveType
  | toggleEdge : MoveType

def moveTypeToNat (m : MoveType) : Nat :=
  MoveType.casesOn m 0 1 2 3 4 5 6

def natToMoveType (n : Nat) : MoveType :=
  let m := Nat.mod n 7
  Nat.casesOn m MoveType.perturbWeights
    (fun r => Nat.casesOn r MoveType.perturbPhases
      (fun r' => Nat.casesOn r' MoveType.createEntanglement
        (fun r'' => Nat.casesOn r'' MoveType.applySymmetry
          (fun r''' => Nat.casesOn r''' MoveType.perturbQubits
            (fun r'''' => Nat.casesOn r'''' MoveType.perturbFractalDim
              (fun _ => MoveType.toggleEdge))))))

inductive UndoEntry : Type where
  | savedEdgeWeight : NodeId → NodeId → Rat → Rat → UndoEntry
  | savedNodeState : NodeId → Rat → ComplexRat → ComplexRat → UndoEntry
  | addedEntanglement : NodePairKey → UndoEntry
  | savedGraph : GraphData → UndoEntry

inductive UndoLog : Type where
  | mk : MoveType → List UndoEntry → UndoLog

def undoMoveType (log : UndoLog) : MoveType := UndoLog.casesOn log (fun mt _ => mt)
def undoEntries (log : UndoLog) : List UndoEntry := UndoLog.casesOn log (fun _ es => es)

def emptyUndoLog : UndoLog := UndoLog.mk MoveType.perturbWeights []

def undoEntryCount (log : UndoLog) : Nat :=
  List.recOn (undoEntries log) 0 (fun _ _ ih => Nat.succ ih)

inductive OptimizerConfig : Type where
  | mk : Rat → Rat → Rat → Nat → Rat → Rat → Nat → Rat → Bool → OptimizerConfig

def cfgInitialTemp (c : OptimizerConfig) : Rat := OptimizerConfig.casesOn c (fun it _ _ _ _ _ _ _ _ => it)
def cfgCoolingRate (c : OptimizerConfig) : Rat := OptimizerConfig.casesOn c (fun _ cr _ _ _ _ _ _ _ => cr)
def cfgCurrentTemp (c : OptimizerConfig) : Rat := OptimizerConfig.casesOn c (fun _ _ ct _ _ _ _ _ _ => ct)
def cfgMaxIter (c : OptimizerConfig) : Nat := OptimizerConfig.casesOn c (fun _ _ _ mi _ _ _ _ _ => mi)
def cfgMinTemp (c : OptimizerConfig) : Rat := OptimizerConfig.casesOn c (fun _ _ _ _ mt _ _ _ _ => mt)
def cfgReheat (c : OptimizerConfig) : Rat := OptimizerConfig.casesOn c (fun _ _ _ _ _ rh _ _ _ => rh)
def cfgSymInterval (c : OptimizerConfig) : Nat := OptimizerConfig.casesOn c (fun _ _ _ _ _ _ si _ _ => si)
def cfgConvergence (c : OptimizerConfig) : Rat := OptimizerConfig.casesOn c (fun _ _ _ _ _ _ _ cv _ => cv)
def cfgAdaptive (c : OptimizerConfig) : Bool := OptimizerConfig.casesOn c (fun _ _ _ _ _ _ _ _ ad => ad)

def defaultConfig : OptimizerConfig :=
  OptimizerConfig.mk
    (ratFromNat 100)
    (Rat.mk Bool.true 95 100)
    (ratFromNat 100)
    10000
    (Rat.mk Bool.true 1 1000)
    (ratFromNat 2)
    50
    (Rat.mk Bool.true 1 100000000)
    Bool.true

inductive FullOptimizerState : Type where
  | mk : OptimizerConfig → OptState → OptState → List SymPattern → List SymTransform →
         OptStats → List Rat → List Rat → Nat → PrngState → MemState → FullOptimizerState

def fosConfig (f : FullOptimizerState) : OptimizerConfig :=
  FullOptimizerState.casesOn f (fun c _ _ _ _ _ _ _ _ _ _ => c)
def fosCurrent (f : FullOptimizerState) : OptState :=
  FullOptimizerState.casesOn f (fun _ cur _ _ _ _ _ _ _ _ _ => cur)
def fosBest (f : FullOptimizerState) : OptState :=
  FullOptimizerState.casesOn f (fun _ _ best _ _ _ _ _ _ _ _ => best)
def fosPatterns (f : FullOptimizerState) : List SymPattern :=
  FullOptimizerState.casesOn f (fun _ _ _ pats _ _ _ _ _ _ _ => pats)
def fosTransforms (f : FullOptimizerState) : List SymTransform :=
  FullOptimizerState.casesOn f (fun _ _ _ _ trans _ _ _ _ _ _ => trans)
def fosStats (f : FullOptimizerState) : OptStats :=
  FullOptimizerState.casesOn f (fun _ _ _ _ _ stats _ _ _ _ _ => stats)
def fosEnergyHist (f : FullOptimizerState) : List Rat :=
  FullOptimizerState.casesOn f (fun _ _ _ _ _ _ eh _ _ _ _ => eh)
def fosTempHist (f : FullOptimizerState) : List Rat :=
  FullOptimizerState.casesOn f (fun _ _ _ _ _ _ _ th _ _ _ => th)
def fosIteration (f : FullOptimizerState) : Nat :=
  FullOptimizerState.casesOn f (fun _ _ _ _ _ _ _ _ it _ _ => it)
def fosPrng (f : FullOptimizerState) : PrngState :=
  FullOptimizerState.casesOn f (fun _ _ _ _ _ _ _ _ _ prng _ => prng)
def fosMem (f : FullOptimizerState) : MemState :=
  FullOptimizerState.casesOn f (fun _ _ _ _ _ _ _ _ _ _ mem => mem)

def computeDefaultEnergy (g : GraphData) : Rat :=
  let nodeEnergy := List.recOn (graphNodes g) ratZero
    (fun hd _ ih =>
      NodeData.casesOn hd (fun _ _ q p =>
        ratAdd ih (ratAdd p (ratAdd (complexNormSq (qubitAlpha q)) (complexNormSq (qubitBeta q))))))
  let edgeEnergy := List.recOn (graphEdges g) ratZero
    (fun hd _ ih =>
      EdgeData.casesOn hd (fun _ _ _ w qc fd =>
        ratAdd ih (ratAdd (ratMul w fd) (complexNormSq qc))))
  ratAdd nodeEnergy edgeEnergy

def computeConnectivityEnergy (g : GraphData) : Rat :=
  let nc := graphNodeCount g
  let ec := graphEdgeCount g
  let maxEdges := Nat.mul nc (Nat.sub nc 1)
  Nat.casesOn maxEdges ratZero
    (fun me' => ratSub ratOne (ratDiv (ratFromNat ec) (ratFromNat (Nat.succ me'))))

def computeCoherenceEnergy (g : GraphData) : Rat :=
  let nodeCoherence := List.recOn (graphNodes g) ratZero
    (fun hd _ ih =>
      NodeData.casesOn hd (fun _ _ q _ =>
        ratAdd ih (ratDiv (ratAdd (complexNormSq (qubitAlpha q)) (complexNormSq (qubitBeta q)))
                          ratTwo)))
  let edgeCorrelation := List.recOn (graphEdges g) ratZero
    (fun hd _ ih =>
      EdgeData.casesOn hd (fun _ _ _ _ qc _ => ratAdd ih (complexNormSq qc)))
  ratAdd nodeCoherence edgeCorrelation

def computeFractalDimEnergy (g : GraphData) : Rat :=
  let totalDim := List.recOn (graphEdges g) ratZero
    (fun hd _ ih =>
      EdgeData.casesOn hd (fun _ _ _ _ _ fd => ratAdd ih fd))
  let ec := graphEdgeCount g
  Nat.casesOn ec ratZero
    (fun ec' =>
      let avgDim := ratDiv totalDim (ratFromNat (Nat.succ ec'))
      let target := Rat.mk Bool.true 3 2
      ratAbs (ratSub avgDim target))

def coolTemperature (temp rate minTemp : Rat) : Rat :=
  let newTemp := ratMul temp rate
  Bool.casesOn (ratLe newTemp minTemp) newTemp minTemp

def adaptiveCoolTemperature (temp rate minTemp acceptRate : Rat) : Rat :=
  let adjustedRate :=
    Bool.casesOn (ratLe (Rat.mk Bool.true 6 10) acceptRate)
      (Bool.casesOn (ratLe acceptRate (Rat.mk Bool.true 2 10))
        rate
        (ratMul rate (Rat.mk Bool.true 102 100)))
      (ratMul rate (Rat.mk Bool.true 98 100))
  let clampedRate := ratMin (Rat.mk Bool.true 999 1000) (ratMax (Rat.mk Bool.true 1 1000) adjustedRate)
  let newTemp := ratMul temp clampedRate
  Bool.casesOn (ratLe newTemp minTemp) newTemp minTemp

def perturbWeight (w : Rat) (delta : Rat) : Rat :=
  ratMax ratZero (ratMin ratOne (ratAdd w delta))

def perturbPhase (phase delta : Rat) : Rat :=
  ratClampPhase (ratAdd phase delta)

def normalizeQubit (a b : ComplexRat) : QubitState :=
  let ns := ratAdd (complexNormSq a) (complexNormSq b)
  let norm := ratSqrt ns
  Bool.casesOn (ratEq norm ratZero)
    (QubitState.mk (complexScale (ratDiv ratOne norm) a)
                   (complexScale (ratDiv ratOne norm) b))
    qubitBasis0

def updateNodePhase (nodes : List NodeData) (nid : NodeId) (newPhase : Rat) : List NodeData :=
  List.recOn nodes []
    (fun hd _ ih =>
      NodeData.casesOn hd (fun id_ lbl qub ph =>
        Bool.casesOn (nodeIdEq id_ nid)
          (List.cons (NodeData.mk id_ lbl qub ph) ih)
          (List.cons (NodeData.mk id_ lbl qub newPhase) ih)))

def updateNodeQubit (nodes : List NodeData) (nid : NodeId) (newQ : QubitState) : List NodeData :=
  List.recOn nodes []
    (fun hd _ ih =>
      NodeData.casesOn hd (fun id_ lbl _ ph =>
        Bool.casesOn (nodeIdEq id_ nid)
          (List.cons (NodeData.mk id_ lbl (nodeQubit hd) ph) ih)
          (List.cons (NodeData.mk id_ lbl newQ ph) ih)))

def updateEdgeWeight (edges : List EdgeData) (src tgt : NodeId) (newW : Rat) : List EdgeData :=
  List.recOn edges []
    (fun hd _ ih =>
      EdgeData.casesOn hd (fun s t q _ qc fd =>
        Bool.casesOn (Bool.and (nodeIdEq s src) (nodeIdEq t tgt))
          (List.cons (EdgeData.mk s t q (edgeWeight hd) qc fd) ih)
          (List.cons (EdgeData.mk s t q newW qc fd) ih)))

def updateEdgeFractalDim (edges : List EdgeData) (src tgt : NodeId) (newFd : Rat) : List EdgeData :=
  List.recOn edges []
    (fun hd _ ih =>
      EdgeData.casesOn hd (fun s t q w qc _ =>
        Bool.casesOn (Bool.and (nodeIdEq s src) (nodeIdEq t tgt))
          (List.cons (EdgeData.mk s t q w qc (edgeFractalDim hd)) ih)
          (List.cons (EdgeData.mk s t q w qc newFd) ih)))

def applyMoveType0 (state : OptState) (prng : PrngState) (temp : Rat) :
    Prod (Prod OptState UndoLog) PrngState :=
  let g := optGraph state
  let edges := graphEdges g
  let savedEntries := List.recOn edges ([] : List UndoEntry)
    (fun hd _ ih =>
      EdgeData.casesOn hd (fun src tgt _ w _ fd =>
        List.cons (UndoEntry.savedEdgeWeight src tgt w fd) ih))
  let prngResult := prngRatUnit prng
  let delta := ratSub (Prod.fst prngResult) ratHalf
  let scaledDelta := ratMul delta (ratMul temp (Rat.mk Bool.true 1 10))
  let newEdges := List.recOn edges ([] : List EdgeData)
    (fun hd _ ih =>
      EdgeData.casesOn hd (fun src tgt qual w qc fd =>
        List.cons (EdgeData.mk src tgt qual (perturbWeight w scaledDelta) qc fd) ih))
  let newGraph := GraphData.mk (graphNodes g) newEdges (graphHash g)
  let newState := optWithGraph state newGraph
  let log := UndoLog.mk MoveType.perturbWeights savedEntries
  Prod.mk (Prod.mk newState log) (Prod.snd prngResult)

def applyMoveType1 (state : OptState) (prng : PrngState) (temp : Rat) :
    Prod (Prod OptState UndoLog) PrngState :=
  let g := optGraph state
  let nodes := graphNodes g
  let savedEntries := List.recOn nodes ([] : List UndoEntry)
    (fun hd _ ih =>
      NodeData.casesOn hd (fun nid _ qub ph =>
        List.cons (UndoEntry.savedNodeState nid ph (qubitAlpha qub) (qubitBeta qub)) ih))
  let prngResult := prngRatUnit prng
  let delta := ratMul (ratSub (Prod.fst prngResult) ratHalf) (ratMul temp (Rat.mk Bool.true 2 10))
  let newNodes := List.recOn nodes ([] : List NodeData)
    (fun hd _ ih =>
      NodeData.casesOn hd (fun nid lbl qub ph =>
        List.cons (NodeData.mk nid lbl qub (perturbPhase ph delta)) ih))
  let newGraph := GraphData.mk newNodes (graphEdges g) (graphHash g)
  let newState := optWithGraph state newGraph
  let log := UndoLog.mk MoveType.perturbPhases savedEntries
  Prod.mk (Prod.mk newState log) (Prod.snd prngResult)

def applyMoveType2 (state : OptState) (prng : PrngState) :
    Prod (Prod OptState UndoLog) PrngState :=
  let nc := graphNodeCount (optGraph state)
  Nat.casesOn nc
    (Prod.mk (Prod.mk state emptyUndoLog) prng)
    (fun nc' =>
      Nat.casesOn nc'
        (Prod.mk (Prod.mk state emptyUndoLog) prng)
        (fun _ =>
          let r1 := prngNatMod prng (Nat.succ (Nat.succ nc'))
          let r2 := prngNatMod (Prod.snd r1) (Nat.succ (Nat.succ nc'))
          let n1 := NodeId.mk (Prod.fst r1)
          let n2 := NodeId.mk (Prod.fst r2)
          let key := orderedPairKey n1 n2
          Bool.casesOn (hasEntanglement key (optEntanglements state))
            (let r3 := prngRatUnit (Prod.snd r2)
             let corr := ratAdd ratHalf (ratMul (Prod.fst r3) ratHalf)
             let info := EntanglementInfo.mk corr ratZero 0 0 1
             let newEnts := addEntanglement (optEntanglements state) key info
             let newState := optWithEntanglements state newEnts
             let log := UndoLog.mk MoveType.createEntanglement [UndoEntry.addedEntanglement key]
             Prod.mk (Prod.mk newState log) (Prod.snd r3))
            (Prod.mk (Prod.mk state emptyUndoLog) (Prod.snd r2))))

def applyMoveType3 (state : OptState) (prng : PrngState) (transforms : List SymTransform) :
    Prod (Prod OptState UndoLog) PrngState :=
  List.recOn transforms
    (Prod.mk (Prod.mk state emptyUndoLog) prng)
    (fun firstT _ _ =>
      let g := optGraph state
      let nodes := graphNodes g
      let savedEntries := List.recOn nodes ([] : List UndoEntry)
        (fun hd _ ih =>
          NodeData.casesOn hd (fun nid _ qub ph =>
            List.cons (UndoEntry.savedNodeState nid ph (qubitAlpha qub) (qubitBeta qub)) ih))
      let qs := QuantumState.mk ratOne ratZero ratZero ratZero
      let transformed := applyTransformQuantumState firstT qs
      let newNodes := List.recOn nodes ([] : List NodeData)
        (fun hd _ ih =>
          NodeData.casesOn hd (fun nid lbl qub _ =>
            List.cons (NodeData.mk nid lbl qub (qsPhase transformed)) ih))
      let newGraph := GraphData.mk newNodes (graphEdges g) (graphHash g)
      let newState := optWithGraph state newGraph
      let log := UndoLog.mk MoveType.applySymmetry savedEntries
      Prod.mk (Prod.mk newState log) prng)

def applyMoveType4 (state : OptState) (prng : PrngState) (temp : Rat) :
    Prod (Prod OptState UndoLog) PrngState :=
  let g := optGraph state
  let nodes := graphNodes g
  let savedEntries := List.recOn nodes ([] : List UndoEntry)
    (fun hd _ ih =>
      NodeData.casesOn hd (fun nid _ qub ph =>
        List.cons (UndoEntry.savedNodeState nid ph (qubitAlpha qub) (qubitBeta qub)) ih))
  let perturbation := ratMul temp (Rat.mk Bool.true 5 100)
  let r1 := prngRatUnit prng
  let r2 := prngRatUnit (Prod.snd r1)
  let newNodes := List.recOn nodes ([] : List NodeData)
    (fun hd _ ih =>
      NodeData.casesOn hd (fun nid lbl qub ph =>
        let newAlpha := complexAdd (qubitAlpha qub) (ComplexRat.mk perturbation ratZero)
        let newBeta := complexAdd (qubitBeta qub) (ComplexRat.mk ratZero perturbation)
        let newQ := normalizeQubit newAlpha newBeta
        List.cons (NodeData.mk nid lbl newQ ph) ih))
  let newGraph := GraphData.mk newNodes (graphEdges g) (graphHash g)
  let newState := optWithGraph state newGraph
  let log := UndoLog.mk MoveType.perturbQubits savedEntries
  Prod.mk (Prod.mk newState log) (Prod.snd r2)

def applyMoveType5 (state : OptState) (prng : PrngState) (temp : Rat) :
    Prod (Prod OptState UndoLog) PrngState :=
  let g := optGraph state
  let edges := graphEdges g
  let savedEntries := List.recOn edges ([] : List UndoEntry)
    (fun hd _ ih =>
      EdgeData.casesOn hd (fun src tgt _ w _ fd =>
        List.cons (UndoEntry.savedEdgeWeight src tgt w fd) ih))
  let r1 := prngRatUnit prng
  let delta := ratMul (ratSub (Prod.fst r1) ratHalf) (ratMul temp (Rat.mk Bool.true 2 100))
  let newEdges := List.recOn edges ([] : List EdgeData)
    (fun hd _ ih =>
      EdgeData.casesOn hd (fun src tgt qual w qc fd =>
        let newFd := ratMax ratZero (ratMin (ratFromNat 3) (ratAdd fd delta))
        List.cons (EdgeData.mk src tgt qual w qc newFd) ih))
  let newGraph := GraphData.mk (graphNodes g) newEdges (graphHash g)
  let newState := optWithGraph state newGraph
  let log := UndoLog.mk MoveType.perturbFractalDim savedEntries
  Prod.mk (Prod.mk newState log) (Prod.snd r1)

def applyMoveType6 (state : OptState) (prng : PrngState) (mem : MemState) :
    Prod (Prod (Prod OptState UndoLog) PrngState) MemState :=
  let g := optGraph state
  let savedGraphEntry := UndoEntry.savedGraph g
  let nc := graphNodeCount g
  Nat.casesOn nc
    (Prod.mk (Prod.mk (Prod.mk state (UndoLog.mk MoveType.toggleEdge [savedGraphEntry])) prng) mem)
    (fun nc' =>
      Nat.casesOn nc'
        (Prod.mk (Prod.mk (Prod.mk state (UndoLog.mk MoveType.toggleEdge [savedGraphEntry])) prng) mem)
        (fun _ =>
          let r1 := prngNatMod prng (Nat.succ (Nat.succ nc'))
          let r2 := prngNatMod (Prod.snd r1) (Nat.succ (Nat.succ nc'))
          let n1 := NodeId.mk (Prod.fst r1)
          let n2 := NodeId.mk (Prod.fst r2)
          let edgeEx := List.recOn (graphEdges g) Bool.false
            (fun hd _ ih =>
              EdgeData.casesOn hd (fun src tgt _ _ _ _ =>
                Bool.casesOn (Bool.and (nodeIdEq src n1) (nodeIdEq tgt n2)) ih Bool.true))
          Bool.casesOn edgeEx
            (let r3 := prngRatUnit (Prod.snd r2)
             let w := Prod.fst r3
             let newEdge := EdgeData.mk n1 n2 EdgeQuality.coherent w complexZero (Rat.mk Bool.true 3 2)
             let newGraph := GraphData.mk (graphNodes g)
               (List.cons newEdge (graphEdges g)) (Nat.add (graphHash g) 1)
             let newState := optWithGraph state newGraph
             Prod.mk (Prod.mk (Prod.mk newState (UndoLog.mk MoveType.toggleEdge [savedGraphEntry])) (Prod.snd r3)) mem)
            (let newGraph := removeEdge g n1 n2
             let newState := optWithGraph state newGraph
             Prod.mk (Prod.mk (Prod.mk newState (UndoLog.mk MoveType.toggleEdge [savedGraphEntry])) (Prod.snd r2)) mem)))

def restoreEdgeWeights (edges : List EdgeData) (saved : List UndoEntry) : List EdgeData :=
  List.recOn saved edges
    (fun hd _ ih =>
      UndoEntry.casesOn hd
        (fun src tgt oldW oldFd =>
          updateEdgeWeight (updateEdgeFractalDim ih src tgt oldFd) src tgt oldW)
        (fun _ _ _ _ => ih)
        (fun _ => ih)
        (fun _ => ih))

def restoreNodeStates (nodes : List NodeData) (saved : List UndoEntry) : List NodeData :=
  List.recOn saved nodes
    (fun hd _ ih =>
      UndoEntry.casesOn hd
        (fun _ _ _ _ => ih)
        (fun nid oldPhase oldAlpha oldBeta =>
          List.recOn ih []
            (fun nd _ rest =>
              NodeData.casesOn nd (fun id_ lbl _ _ =>
                Bool.casesOn (nodeIdEq id_ nid)
                  (List.cons nd rest)
                  (List.cons (NodeData.mk id_ lbl (QubitState.mk oldAlpha oldBeta) oldPhase) rest))))
        (fun _ => ih)
        (fun _ => ih))

def undoMove (state : OptState) (log : UndoLog) : OptState :=
  UndoLog.casesOn log (fun mt entries =>
    MoveType.casesOn mt
      (let g := optGraph state
       let restoredEdges := restoreEdgeWeights (graphEdges g) entries
       optWithGraph state (GraphData.mk (graphNodes g) restoredEdges (graphHash g)))
      (let g := optGraph state
       let restoredNodes := restoreNodeStates (graphNodes g) entries
       optWithGraph state (GraphData.mk restoredNodes (graphEdges g) (graphHash g)))
      (let restoredEnts := List.recOn entries (optEntanglements state)
         (fun hd _ ih =>
           UndoEntry.casesOn hd
             (fun _ _ _ _ => ih)
             (fun _ _ _ _ => ih)
             (fun key => removeEntanglement ih key)
             (fun _ => ih))
       optWithEntanglements state restoredEnts)
      (let g := optGraph state
       let restoredNodes := restoreNodeStates (graphNodes g) entries
       optWithGraph state (GraphData.mk restoredNodes (graphEdges g) (graphHash g)))
      (let g := optGraph state
       let restoredNodes := restoreNodeStates (graphNodes g) entries
       optWithGraph state (GraphData.mk restoredNodes (graphEdges g) (graphHash g)))
      (let g := optGraph state
       let restoredEdges := restoreEdgeWeights (graphEdges g) entries
       optWithGraph state (GraphData.mk (graphNodes g) restoredEdges (graphHash g)))
      (List.recOn entries state
         (fun hd _ _ =>
           UndoEntry.casesOn hd
             (fun _ _ _ _ => state)
             (fun _ _ _ _ => state)
             (fun _ => state)
             (fun savedG => optWithGraph state savedG))))

def acceptMoveDecision (deltaEnergy temp : Rat) (prng : PrngState) : Prod Bool PrngState :=
  Bool.casesOn (ratLt deltaEnergy ratZero)
    (Bool.casesOn (ratEq deltaEnergy ratZero)
      (let r := prngRatUnit prng
       let expArg := ratNeg (ratDiv deltaEnergy temp)
       let threshold := ratDiv ratOne (ratAdd ratOne expArg)
       let accepted := ratLt (Prod.fst r) threshold
       Prod.mk accepted (Prod.snd r))
      (Prod.mk Bool.true prng))
    (Prod.mk Bool.true prng)

def detectSymmetries (g : GraphData) : List SymTransform :=
  let nodes := graphNodes g
  let nc := graphNodeCount g
  let cx := Nat.casesOn nc ratZero
    (fun nc' =>
      ratDiv (List.recOn nodes ratZero
        (fun hd _ ih =>
          NodeData.casesOn hd (fun _ _ q _ =>
            ratAdd ih (complexRe (qubitAlpha q)))))
        (ratFromNat (Nat.succ nc')))
  let cy := Nat.casesOn nc ratZero
    (fun nc' =>
      ratDiv (List.recOn nodes ratZero
        (fun hd _ ih =>
          NodeData.casesOn hd (fun _ _ q _ =>
            ratAdd ih (complexIm (qubitAlpha q)))))
        (ratFromNat (Nat.succ nc')))
  let identityT := SymTransform.mk SymGroup.identity cx cy ratZero ratZero ratOne ratZero
  let reflT := SymTransform.mk SymGroup.reflection cx cy ratZero ratZero ratOne ratZero
  let rot180T := SymTransform.mk SymGroup.rotation180 cx cy ratZero ratZero ratOne ratZero
  List.cons identityT (List.cons reflT (List.cons rot180T []))

def updateEntanglementMap (ents : List EntanglementEntry) (decayFactor : Rat) :
    List EntanglementEntry :=
  List.recOn ents []
    (fun hd _ ih =>
      EntanglementEntry.casesOn hd (fun key info =>
        let decayed := entDecay info decayFactor
        Bool.casesOn (ratLe (entCorrelation decayed) (Rat.mk Bool.true 1 100))
          (List.cons (EntanglementEntry.mk key decayed) ih)
          ih))

def updateStatsAcceptance (s : OptStats) : OptStats :=
  OptStats.casesOn s (fun iters acc rej best curr sym ent elapsed _ cool esc conv temp evals avgd =>
    let total := Nat.add acc rej
    let newRate := Nat.casesOn total ratZero
      (fun total' => ratDiv (ratFromNat acc) (ratFromNat (Nat.succ total')))
    OptStats.mk iters acc rej best curr sym ent elapsed newRate cool esc conv temp evals avgd)

def averageEntanglement (ents : List EntanglementEntry) : Rat :=
  let count := entanglementCount ents
  Nat.casesOn count ratZero
    (fun count' =>
      let total := List.recOn ents ratZero
        (fun hd _ ih =>
          EntanglementEntry.casesOn hd (fun _ info =>
            ratAdd ih (entCorrelation info)))
      ratDiv total (ratFromNat (Nat.succ count')))

def minNat (a b : Nat) : Nat :=
  Nat.recOn a 0
    (fun a' _ => Nat.casesOn b 0 (fun b' => Nat.succ (minNat a' b')))

def maxNat (a b : Nat) : Nat :=
  Nat.recOn a b
    (fun a' _ => Nat.casesOn b (Nat.succ a') (fun b' => Nat.succ (maxNat a' b')))

def listLengthGeneric (l : List α) : Nat :=
  List.recOn l 0 (fun _ _ ih => Nat.succ ih)

def listAppendGeneric (l1 l2 : List α) : List α :=
  List.recOn l1 l2 (fun hd _ ih => List.cons hd ih)

theorem rot_identity_left : ∀ (r : Rotation), Eq (rotCompose Rotation.rot0 r) r :=
  fun r => Rotation.casesOn r (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _)

theorem rot_identity_right : ∀ (r : Rotation), Eq (rotCompose r Rotation.rot0) r :=
  fun r => Rotation.casesOn r (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _)

theorem rot_inverse_left : ∀ (r : Rotation), Eq (rotCompose (rotInverse r) r) Rotation.rot0 :=
  fun r => Rotation.casesOn r (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _)

theorem rot_inverse_right : ∀ (r : Rotation), Eq (rotCompose r (rotInverse r)) Rotation.rot0 :=
  fun r => Rotation.casesOn r (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _)

theorem rot_assoc : ∀ (a b c : Rotation),
    Eq (rotCompose (rotCompose a b) c) (rotCompose a (rotCompose b c)) :=
  fun a b c =>
    Rotation.casesOn a
      (Rotation.casesOn b
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _)))
      (Rotation.casesOn b
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _)))
      (Rotation.casesOn b
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _)))
      (Rotation.casesOn b
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))
        (Rotation.casesOn c (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _)))

theorem rot_compose_comm : ∀ (a b : Rotation), Eq (rotCompose a b) (rotCompose b a) :=
  fun a b =>
    Rotation.casesOn a
      (Rotation.casesOn b (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))
      (Rotation.casesOn b (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))
      (Rotation.casesOn b (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))
      (Rotation.casesOn b (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _))

theorem rot_inverse_involution : ∀ (r : Rotation), Eq (rotInverse (rotInverse r)) r :=
  fun r => Rotation.casesOn r (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _)

theorem rotToNat_natToRot_roundtrip : ∀ (r : Rotation), Eq (natToRot (rotToNat r)) r :=
  fun r => Rotation.casesOn r (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _)

theorem rot_compose_table_00 : Eq (rotCompose Rotation.rot0 Rotation.rot0) Rotation.rot0 := Eq.refl _
theorem rot_compose_table_01 : Eq (rotCompose Rotation.rot0 Rotation.rot90) Rotation.rot90 := Eq.refl _
theorem rot_compose_table_02 : Eq (rotCompose Rotation.rot0 Rotation.rot180) Rotation.rot180 := Eq.refl _
theorem rot_compose_table_03 : Eq (rotCompose Rotation.rot0 Rotation.rot270) Rotation.rot270 := Eq.refl _
theorem rot_compose_table_10 : Eq (rotCompose Rotation.rot90 Rotation.rot0) Rotation.rot90 := Eq.refl _
theorem rot_compose_table_11 : Eq (rotCompose Rotation.rot90 Rotation.rot90) Rotation.rot180 := Eq.refl _
theorem rot_compose_table_12 : Eq (rotCompose Rotation.rot90 Rotation.rot180) Rotation.rot270 := Eq.refl _
theorem rot_compose_table_13 : Eq (rotCompose Rotation.rot90 Rotation.rot270) Rotation.rot0 := Eq.refl _
theorem rot_compose_table_20 : Eq (rotCompose Rotation.rot180 Rotation.rot0) Rotation.rot180 := Eq.refl _
theorem rot_compose_table_21 : Eq (rotCompose Rotation.rot180 Rotation.rot90) Rotation.rot270 := Eq.refl _
theorem rot_compose_table_22 : Eq (rotCompose Rotation.rot180 Rotation.rot180) Rotation.rot0 := Eq.refl _
theorem rot_compose_table_23 : Eq (rotCompose Rotation.rot180 Rotation.rot270) Rotation.rot90 := Eq.refl _
theorem rot_compose_table_30 : Eq (rotCompose Rotation.rot270 Rotation.rot0) Rotation.rot270 := Eq.refl _
theorem rot_compose_table_31 : Eq (rotCompose Rotation.rot270 Rotation.rot90) Rotation.rot0 := Eq.refl _
theorem rot_compose_table_32 : Eq (rotCompose Rotation.rot270 Rotation.rot180) Rotation.rot90 := Eq.refl _
theorem rot_compose_table_33 : Eq (rotCompose Rotation.rot270 Rotation.rot270) Rotation.rot180 := Eq.refl _

theorem rot_compose_inverse_unique : ∀ (a b : Rotation),
    Eq (rotCompose a b) Rotation.rot0 → Eq b (rotInverse a) :=
  fun a b =>
    Rotation.casesOn a
      (Rotation.casesOn b (fun _ => Eq.refl _) (fun h => False.elim (Rotation.noConfusion h))
        (fun h => False.elim (Rotation.noConfusion h)) (fun h => False.elim (Rotation.noConfusion h)))
      (Rotation.casesOn b (fun h => False.elim (Rotation.noConfusion h))
        (fun h => False.elim (Rotation.noConfusion h)) (fun h => False.elim (Rotation.noConfusion h))
        (fun _ => Eq.refl _))
      (Rotation.casesOn b (fun h => False.elim (Rotation.noConfusion h))
        (fun h => False.elim (Rotation.noConfusion h)) (fun _ => Eq.refl _)
        (fun h => False.elim (Rotation.noConfusion h)))
      (Rotation.casesOn b (fun h => False.elim (Rotation.noConfusion h))
        (fun _ => Eq.refl _) (fun h => False.elim (Rotation.noConfusion h))
        (fun h => False.elim (Rotation.noConfusion h)))

theorem rot_order_rot180_is_2 :
    And (Not (Eq Rotation.rot180 Rotation.rot0))
        (Eq (rotCompose Rotation.rot180 Rotation.rot180) Rotation.rot0) :=
  And.intro (fun h => Rotation.noConfusion h) (Eq.refl _)

theorem rot_order_rot90_is_4 :
    And (Not (Eq (rotCompose Rotation.rot90 Rotation.rot90) Rotation.rot0))
        (Eq (rotCompose (rotCompose (rotCompose Rotation.rot90 Rotation.rot90) Rotation.rot90) Rotation.rot90) Rotation.rot0) :=
  And.intro (fun h => Rotation.noConfusion h) (Eq.refl _)

theorem rot_closure : ∀ (a b : Rotation),
    Or (Eq (rotCompose a b) Rotation.rot0)
       (Or (Eq (rotCompose a b) Rotation.rot90)
           (Or (Eq (rotCompose a b) Rotation.rot180)
               (Eq (rotCompose a b) Rotation.rot270))) :=
  fun a b =>
    Rotation.casesOn a
      (Rotation.casesOn b (Or.inl (Eq.refl _)) (Or.inr (Or.inl (Eq.refl _)))
        (Or.inr (Or.inr (Or.inl (Eq.refl _)))) (Or.inr (Or.inr (Or.inr (Eq.refl _)))))
      (Rotation.casesOn b (Or.inr (Or.inl (Eq.refl _))) (Or.inr (Or.inr (Or.inl (Eq.refl _))))
        (Or.inr (Or.inr (Or.inr (Eq.refl _)))) (Or.inl (Eq.refl _)))
      (Rotation.casesOn b (Or.inr (Or.inr (Or.inl (Eq.refl _)))) (Or.inr (Or.inr (Or.inr (Eq.refl _))))
        (Or.inl (Eq.refl _)) (Or.inr (Or.inl (Eq.refl _))))
      (Rotation.casesOn b (Or.inr (Or.inr (Or.inr (Eq.refl _)))) (Or.inl (Eq.refl _))
        (Or.inr (Or.inl (Eq.refl _))) (Or.inr (Or.inr (Or.inl (Eq.refl _)))))

theorem rot_cancel_left : ∀ (a b c : Rotation),
    Eq (rotCompose a b) (rotCompose a c) → Eq b c :=
  fun a b c h =>
    let inv_a := rotInverse a
    let step1 := congrArg (rotCompose inv_a) h
    let lhs : Eq (rotCompose (rotCompose inv_a a) b) b :=
      Eq.trans (congrArg (fun x => rotCompose x b) (rot_inverse_left a)) (rot_identity_left b)
    let rhs : Eq (rotCompose (rotCompose inv_a a) c) c :=
      Eq.trans (congrArg (fun x => rotCompose x c) (rot_inverse_left a)) (rot_identity_left c)
    Eq.trans (Eq.symm lhs)
      (Eq.trans (Eq.symm (rot_assoc inv_a a b))
        (Eq.trans step1 (Eq.trans (rot_assoc inv_a a c) rhs)))

theorem nat_sub_le : ∀ (a b : Nat), Nat.le (Nat.sub a b) a :=
  fun a => Nat.recOn a
    (fun b => Nat.casesOn b (Nat.le_refl 0) (fun _ => Nat.le_refl 0))
    (fun a' ih b => Nat.casesOn b (Nat.le_refl (Nat.succ a')) (fun b' => Nat.le_step (ih b')))

theorem nat_add_zero_left : ∀ (n : Nat), Eq (Nat.add 0 n) n :=
  fun n => Nat.recOn n (Eq.refl 0) (fun n' ih => congrArg Nat.succ ih)

theorem nat_succ_add : ∀ (a b : Nat), Eq (Nat.add (Nat.succ a) b) (Nat.succ (Nat.add a b)) :=
  fun a b => Nat.recOn b (Eq.refl _) (fun b' ih => congrArg Nat.succ ih)

theorem nat_add_comm : ∀ (a b : Nat), Eq (Nat.add a b) (Nat.add b a) :=
  fun a b => Nat.recOn b
    (Eq.symm (nat_add_zero_left a))
    (fun b' ih => Eq.trans (congrArg Nat.succ ih) (Eq.symm (nat_succ_add b' a)))

theorem nat_add_assoc : ∀ (a b c : Nat), Eq (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c)) :=
  fun a b c => Nat.recOn c (Eq.refl _) (fun c' ih => congrArg Nat.succ ih)

theorem nat_le_add_right : ∀ (a b : Nat), Nat.le a (Nat.add a b) :=
  fun a b => Nat.recOn b (Nat.le_refl a) (fun _ ih => Nat.le_step ih)

theorem nat_le_add_left : ∀ (a b : Nat), Nat.le b (Nat.add a b) :=
  fun a b => Eq.subst (nat_add_comm a b) (nat_le_add_right b a)

theorem nat_add_le_mono_left : ∀ (a b c : Nat), Nat.le b c → Nat.le (Nat.add a b) (Nat.add a c) :=
  fun a b c h => Nat.recOn a
    (Eq.subst (Eq.symm (nat_add_zero_left c)) (Eq.subst (Eq.symm (nat_add_zero_left b)) h))
    (fun a' ih => Eq.subst (Eq.symm (nat_succ_add a' c))
      (Eq.subst (Eq.symm (nat_succ_add a' b)) (Nat.succ_le_succ ih)))

theorem nat_mul_zero_left : ∀ (n : Nat), Eq (Nat.mul 0 n) 0 :=
  fun n => Nat.recOn n (Eq.refl 0) (fun n' ih => ih)

theorem nat_sub_self : ∀ (a : Nat), Eq (Nat.sub a a) 0 :=
  fun a => Nat.recOn a (Eq.refl 0) (fun a' ih => ih)

theorem mod4_values : And (Eq (mod4 0) 0) (And (Eq (mod4 1) 1) (And (Eq (mod4 2) 2) (Eq (mod4 3) 3))) :=
  And.intro (Eq.refl _) (And.intro (Eq.refl _) (And.intro (Eq.refl _) (Eq.refl _)))

theorem mod4_period : Eq (mod4 4) 0 := Eq.refl _

theorem rotToNat_bounded : ∀ (r : Rotation), Nat.lt (rotToNat r) 4 :=
  fun r => Rotation.casesOn r
    (Nat.succ_le_succ (Nat.zero_le 3))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 2)))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.le_refl 0)))))

theorem minNat_le_left : ∀ (a b : Nat), Nat.le (minNat a b) a :=
  fun a => Nat.recOn a (fun _ => Nat.le_refl 0)
    (fun a' ih b => Nat.casesOn b (Nat.zero_le (Nat.succ a')) (fun b' => Nat.succ_le_succ (ih b')))

theorem minNat_le_right : ∀ (a b : Nat), Nat.le (minNat a b) b :=
  fun a => Nat.recOn a (fun b => Nat.zero_le b)
    (fun a' ih b => Nat.casesOn b (Nat.le_refl 0) (fun b' => Nat.succ_le_succ (ih b')))

theorem minNat_comm : ∀ (a b : Nat), Eq (minNat a b) (minNat b a) :=
  fun a => Nat.recOn a
    (fun b => Nat.casesOn b (Eq.refl 0) (fun _ => Eq.refl 0))
    (fun a' ih b => Nat.casesOn b (Eq.refl 0) (fun b' => congrArg Nat.succ (ih b')))

theorem minNat_idem : ∀ (a : Nat), Eq (minNat a a) a :=
  fun a => Nat.recOn a (Eq.refl 0) (fun a' ih => congrArg Nat.succ ih)

theorem minNat_assoc : ∀ (a b c : Nat), Eq (minNat (minNat a b) c) (minNat a (minNat b c)) :=
  fun a => Nat.recOn a (fun _ _ => Eq.refl 0)
    (fun a' ih b c =>
      Nat.casesOn b (Nat.casesOn c (Eq.refl 0) (fun _ => Eq.refl 0))
        (fun b' => Nat.casesOn c (Eq.refl 0) (fun c' => congrArg Nat.succ (ih b' c'))))

theorem maxNat_ge_left : ∀ (a b : Nat), Nat.le a (maxNat a b) :=
  fun a => Nat.recOn a (fun b => Nat.zero_le (maxNat 0 b))
    (fun a' ih b => Nat.casesOn b (Nat.le_refl (Nat.succ a')) (fun b' => Nat.succ_le_succ (ih b')))

theorem maxNat_ge_right : ∀ (a b : Nat), Nat.le b (maxNat a b) :=
  fun a => Nat.recOn a (fun b => Nat.le_refl b)
    (fun a' ih b => Nat.casesOn b (Nat.zero_le (Nat.succ a')) (fun b' => Nat.succ_le_succ (ih b')))

theorem maxNat_comm : ∀ (a b : Nat), Eq (maxNat a b) (maxNat b a) :=
  fun a => Nat.recOn a
    (fun b => Nat.casesOn b (Eq.refl 0) (fun _ => Eq.refl _))
    (fun a' ih b => Nat.casesOn b (Eq.refl _) (fun b' => congrArg Nat.succ (ih b')))

theorem maxNat_idem : ∀ (a : Nat), Eq (maxNat a a) a :=
  fun a => Nat.recOn a (Eq.refl 0) (fun a' ih => congrArg Nat.succ ih)

theorem emptyGraph_nodeCount : Eq (graphNodeCount emptyGraph) 0 := Eq.refl 0
theorem emptyGraph_edgeCount : Eq (graphEdgeCount emptyGraph) 0 := Eq.refl 0
theorem emptyOptState_energy : Eq (optEnergy emptyOptState) ratZero := Eq.refl _
theorem emptyOptState_entCount : Eq (entanglementCount (optEntanglements emptyOptState)) 0 := Eq.refl 0

def edgeWeightBounded (w : Rat) : Prop :=
  And (Eq (ratLe ratZero w) Bool.true) (Eq (ratLe w ratOne) Bool.true)

def phaseBounded (p : Rat) : Prop :=
  And (Eq (ratLe ratZero p) Bool.true) (Eq (ratLe p ratTwoPi) Bool.true)

def graphWeightsInvariant (g : GraphData) : Prop :=
  List.recOn (graphEdges g) True
    (fun hd _ ih => And (edgeWeightBounded (edgeWeight hd)) ih)

def graphPhasesInvariant (g : GraphData) : Prop :=
  List.recOn (graphNodes g) True
    (fun hd _ ih => And (phaseBounded (nodePhase hd)) ih)

def optStateInvariant (s : OptState) : Prop :=
  And (graphWeightsInvariant (optGraph s))
      (And (graphPhasesInvariant (optGraph s))
           (Nat.le 0 (entanglementCount (optEntanglements s))))

theorem emptyOptState_invariant : optStateInvariant emptyOptState :=
  And.intro True.intro (And.intro True.intro (Nat.le_refl 0))

theorem perturbWeight_clamps_zero : ∀ (w delta : Rat),
    Eq (ratLe ratZero (perturbWeight w delta)) Bool.true :=
  fun _ _ => Eq.refl _

theorem perturbWeight_clamps_one : ∀ (w delta : Rat),
    Eq (ratLe (perturbWeight w delta) ratOne) Bool.true :=
  fun _ _ => Eq.refl _

def statsInvariant (s : OptStats) : Prop :=
  And (Nat.le (statsAccepted s) (Nat.add (statsAccepted s) (statsRejected s)))
      (Nat.le 0 (statsIterations s))

theorem emptyStats_invariant : statsInvariant emptyStats :=
  And.intro (Nat.le_refl 0) (Nat.le_refl 0)

theorem statsInvariant_accept : ∀ (acc rej : Nat), Nat.le acc (Nat.add acc rej) :=
  fun acc rej => nat_le_add_right acc rej

def totalMovesInvariant (acc rej iter : Nat) : Prop := Eq (Nat.add acc rej) iter

theorem totalMoves_init : totalMovesInvariant 0 0 0 := Eq.refl 0

theorem totalMoves_accept : ∀ (acc rej iter : Nat),
    totalMovesInvariant acc rej iter → totalMovesInvariant (Nat.succ acc) rej (Nat.succ iter) :=
  fun _ _ _ h => congrArg Nat.succ h

theorem totalMoves_reject : ∀ (acc rej iter : Nat),
    totalMovesInvariant acc rej iter → totalMovesInvariant acc (Nat.succ rej) (Nat.succ iter) :=
  fun _ _ _ h => Eq.trans (Eq.refl _) (congrArg Nat.succ h)

def configValid (c : OptimizerConfig) : Prop :=
  And (Nat.le 1 (cfgMaxIter c))
      (And (Eq (ratLe ratZero (cfgInitialTemp c)) Bool.true)
           (And (Eq (ratLe ratZero (cfgCoolingRate c)) Bool.true)
                (Eq (ratLe (cfgCoolingRate c) ratOne) Bool.true)))

theorem defaultConfig_valid : configValid defaultConfig :=
  And.intro (Nat.succ_le_succ (Nat.zero_le 9999))
    (And.intro (Eq.refl _) (And.intro (Eq.refl _) (Eq.refl _)))

def optimizerProgress (iteration maxIter : Nat) : Prop := Nat.le iteration maxIter

theorem optimizerProgress_start : ∀ (m : Nat), optimizerProgress 0 m :=
  fun m => Nat.zero_le m

theorem optimizerProgress_step : ∀ (i m : Nat),
    optimizerProgress i m → Nat.lt i m → optimizerProgress (Nat.succ i) m :=
  fun _ _ _ h => h

def entanglementBound (entCount nodeCount : Nat) : Prop :=
  Nat.le entCount (Nat.mul nodeCount nodeCount)

theorem entanglement_bound_empty : entanglementBound 0 0 := Nat.le_refl 0

theorem entanglement_bound_growth : ∀ (e n : Nat),
    entanglementBound e n → entanglementBound e (Nat.succ n) :=
  fun e n h => Nat.le_trans h (nat_le_add_right (Nat.mul n n) (Nat.add n (Nat.add n 1)))

def memSafety (m : MemState) : Prop :=
  And (Nat.le 1 (memNextAddr m)) (Nat.le 0 (memTotalAllocated m))

theorem memInitial_safe : memSafety memInitial :=
  And.intro (Nat.succ_le_succ (Nat.zero_le 0)) (Nat.le_refl 0)

theorem memAlloc_preserves_safety : ∀ (blocks : List MemBlock) (nextAddr totalAlloc size : Nat),
    Nat.le 1 nextAddr →
    Nat.le 1 (Nat.add nextAddr size) :=
  fun _ nextAddr _ _ h => Nat.le_trans h (nat_le_add_right nextAddr _)

def allocResultIsOk (r : AllocResult α) : Bool :=
  AllocResult.casesOn r (fun _ => Bool.true) (fun _ => Bool.false)

theorem allocPure_isOk : ∀ (a : α), Eq (allocResultIsOk (allocPure a)) Bool.true :=
  fun _ => Eq.refl _

def prngDeterministic (p1 p2 : PrngState) : Prop :=
  Eq (prngState0 p1) (prngState0 p2) →
  Eq (prngState1 p1) (prngState1 p2) →
  Eq (prngCounter p1) (prngCounter p2) →
  Eq (Prod.fst (prngNext p1)) (Prod.fst (prngNext p2))

theorem prng_deterministic : ∀ (p : PrngState), prngDeterministic p p :=
  fun _ _ _ _ => Eq.refl _

theorem prng_counter_increases : ∀ (p : PrngState),
    Eq (prngCounter (Prod.snd (prngNext p))) (Nat.succ (prngCounter p)) :=
  fun p => PrngState.casesOn p (fun _ _ _ => Eq.refl _)

theorem cloneNodeList_preserves_length : ∀ (nodes : List NodeData),
    Eq (listLengthGeneric (cloneNodeList nodes)) (listLengthGeneric nodes) :=
  fun nodes =>
    List.recOn nodes (Eq.refl 0)
      (fun hd _ ih => NodeData.casesOn hd (fun _ _ _ _ => congrArg Nat.succ ih))

theorem cloneEdgeList_preserves_length : ∀ (edges : List EdgeData),
    Eq (listLengthGeneric (cloneEdgeList edges)) (listLengthGeneric edges) :=
  fun edges =>
    List.recOn edges (Eq.refl 0)
      (fun hd _ ih => EdgeData.casesOn hd (fun _ _ _ _ _ _ => congrArg Nat.succ ih))

def graphIsomorphic (g1 g2 : GraphData) : Prop :=
  And (Eq (graphNodeCount g1) (graphNodeCount g2))
      (And (Eq (graphEdgeCount g1) (graphEdgeCount g2))
           (Eq (graphHash g1) (graphHash g2)))

theorem cloneGraph_isomorphic : ∀ (nodes : List NodeData) (edges : List EdgeData) (hash : Nat),
    graphIsomorphic (GraphData.mk nodes edges hash)
                    (GraphData.mk (cloneNodeList nodes) (cloneEdgeList edges) hash) :=
  fun nodes edges hash =>
    And.intro
      (Eq.symm (cloneNodeList_preserves_length nodes))
      (And.intro (Eq.symm (cloneEdgeList_preserves_length edges)) (Eq.refl hash))

theorem addNode_increases_count : ∀ (nodes : List NodeData) (edges : List EdgeData) (hash : Nat) (nd : NodeData),
    Eq (graphNodeCount (GraphData.mk (List.cons nd nodes) edges hash))
       (Nat.succ (graphNodeCount (GraphData.mk nodes edges hash))) :=
  fun _ _ _ _ => Eq.refl _

theorem removeEdge_count_le : ∀ (src tgt : NodeId) (edges : List EdgeData),
    Nat.le (listLengthGeneric (removeEdgeHelper src tgt edges)) (listLengthGeneric edges) :=
  fun src tgt edges =>
    List.recOn edges (Nat.le_refl 0)
      (fun hd _ ih =>
        EdgeData.casesOn hd (fun s t _ _ _ _ =>
          Bool.casesOn (Bool.and (nodeIdEq s src) (nodeIdEq t tgt))
            (Nat.succ_le_succ ih) (Nat.le_step ih)))

theorem entanglementCount_add : ∀ (ents : List EntanglementEntry) (key : NodePairKey) (info : EntanglementInfo),
    Eq (entanglementCount (addEntanglement ents key info)) (Nat.succ (entanglementCount ents)) :=
  fun _ _ _ => Eq.refl _

theorem entanglementCount_remove_le : ∀ (ents : List EntanglementEntry) (key : NodePairKey),
    Nat.le (entanglementCount (removeEntanglement ents key)) (entanglementCount ents) :=
  fun ents key =>
    List.recOn ents (Nat.le_refl 0)
      (fun hd _ ih =>
        EntanglementEntry.casesOn hd (fun k _ =>
          Bool.casesOn (nodePairEq key k) (Nat.succ_le_succ ih) (Nat.le_step ih)))

theorem hasEntanglement_nil : ∀ (k : NodePairKey), Eq (hasEntanglement k []) Bool.false :=
  fun _ => Eq.refl _

theorem nodeIdEq_refl : ∀ (n : NodeId), Eq (nodeIdEq n n) Bool.true :=
  fun n => NodeId.casesOn n (fun _ => Eq.refl _)

theorem nodePairEq_refl : ∀ (p : NodePairKey), Eq (nodePairEq p p) Bool.true :=
  fun p => NodePairKey.casesOn p (fun n1 n2 =>
    NodeId.casesOn n1 (fun _ => NodeId.casesOn n2 (fun _ => Eq.refl _)))

theorem undoType6_restores_graph : ∀ (s : OptState) (savedG : GraphData),
    Eq (optGraph (undoMove s (UndoLog.mk MoveType.toggleEdge [UndoEntry.savedGraph savedG]))) savedG :=
  fun _ _ => Eq.refl _

theorem undoType0_preserves_node_count : ∀ (s : OptState) (entries : List UndoEntry),
    Eq (graphNodeCount (optGraph (undoMove s (UndoLog.mk MoveType.perturbWeights entries))))
       (graphNodeCount (optGraph s)) :=
  fun _ _ => Eq.refl _

theorem undoType1_preserves_edge_count : ∀ (s : OptState) (entries : List UndoEntry),
    Eq (graphEdgeCount (optGraph (undoMove s (UndoLog.mk MoveType.perturbPhases entries))))
       (graphEdgeCount (optGraph s)) :=
  fun _ _ => Eq.refl _

theorem undoType2_reduces_entanglement : ∀ (s : OptState) (key : NodePairKey),
    Nat.le (entanglementCount (optEntanglements (undoMove s (UndoLog.mk MoveType.createEntanglement [UndoEntry.addedEntanglement key]))))
           (entanglementCount (optEntanglements s)) :=
  fun s key => entanglementCount_remove_le (optEntanglements s) key

theorem undoType3_preserves_node_count : ∀ (s : OptState) (entries : List UndoEntry),
    Eq (graphNodeCount (optGraph (undoMove s (UndoLog.mk MoveType.applySymmetry entries))))
       (graphNodeCount (optGraph s)) :=
  fun _ _ => Eq.refl _

theorem undoType4_preserves_node_count : ∀ (s : OptState) (entries : List UndoEntry),
    Eq (graphNodeCount (optGraph (undoMove s (UndoLog.mk MoveType.perturbQubits entries))))
       (graphNodeCount (optGraph s)) :=
  fun _ _ => Eq.refl _

theorem undoType5_preserves_node_count : ∀ (s : OptState) (entries : List UndoEntry),
    Eq (graphNodeCount (optGraph (undoMove s (UndoLog.mk MoveType.perturbFractalDim entries))))
       (graphNodeCount (optGraph s)) :=
  fun _ _ => Eq.refl _

def allMovesPreserveStructure (s : OptState) : Prop :=
  And (∀ (entries : List UndoEntry),
    Eq (graphNodeCount (optGraph (undoMove s (UndoLog.mk MoveType.perturbWeights entries))))
       (graphNodeCount (optGraph s)))
  (And (∀ (entries : List UndoEntry),
    Eq (graphEdgeCount (optGraph (undoMove s (UndoLog.mk MoveType.perturbPhases entries))))
       (graphEdgeCount (optGraph s)))
  (And (∀ (key : NodePairKey),
    Nat.le (entanglementCount (optEntanglements (undoMove s (UndoLog.mk MoveType.createEntanglement [UndoEntry.addedEntanglement key]))))
           (entanglementCount (optEntanglements s)))
  (And (∀ (entries : List UndoEntry),
    Eq (graphNodeCount (optGraph (undoMove s (UndoLog.mk MoveType.applySymmetry entries))))
       (graphNodeCount (optGraph s)))
  (And (∀ (entries : List UndoEntry),
    Eq (graphNodeCount (optGraph (undoMove s (UndoLog.mk MoveType.perturbQubits entries))))
       (graphNodeCount (optGraph s)))
  (And (∀ (entries : List UndoEntry),
    Eq (graphNodeCount (optGraph (undoMove s (UndoLog.mk MoveType.perturbFractalDim entries))))
       (graphNodeCount (optGraph s)))
  (∀ (savedG : GraphData),
    Eq (optGraph (undoMove s (UndoLog.mk MoveType.toggleEdge [UndoEntry.savedGraph savedG]))) savedG))))))

theorem allMoves_preserve : ∀ (s : OptState), allMovesPreserveStructure s :=
  fun s =>
    And.intro (fun entries => undoType0_preserves_node_count s entries)
    (And.intro (fun entries => undoType1_preserves_edge_count s entries)
    (And.intro (fun key => undoType2_reduces_entanglement s key)
    (And.intro (fun entries => undoType3_preserves_node_count s entries)
    (And.intro (fun entries => undoType4_preserves_node_count s entries)
    (And.intro (fun entries => undoType5_preserves_node_count s entries)
    (fun savedG => undoType6_restores_graph s savedG))))))

theorem moveTypeToNat_bounded : ∀ (m : MoveType), Nat.lt (moveTypeToNat m) 7 :=
  fun m => MoveType.casesOn m
    (Nat.succ_le_succ (Nat.zero_le 6))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 5)))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 4))))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 3)))))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 2))))))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1)))))))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.le_refl 0))))))))

theorem symGroupToNat_bounded : ∀ (g : SymGroup), Nat.lt (symGroupToNat g) 6 :=
  fun g => SymGroup.casesOn g
    (Nat.succ_le_succ (Nat.zero_le 5))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 4)))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 3))))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 2)))))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))))))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.le_refl 0)))))))

theorem edgeQualityToNat_bounded : ∀ (e : EdgeQuality), Nat.lt (edgeQualityToNat e) 4 :=
  fun e => EdgeQuality.casesOn e
    (Nat.succ_le_succ (Nat.zero_le 3))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 2)))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))))
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.le_refl 0)))))

theorem identityTransform_preserves_point : ∀ (x y : Rat),
    Eq (applyTransform2D identityTransform x y) (Prod.mk x y) :=
  fun _ _ => Eq.refl _

theorem rotation90_inverse_is_270 :
    Eq (stGroup (transformInverse (SymTransform.mk SymGroup.rotation90 ratZero ratZero ratZero ratZero ratOne ratZero)))
       SymGroup.rotation270 := Eq.refl _

theorem rotation180_inverse_is_180 :
    Eq (stGroup (transformInverse (SymTransform.mk SymGroup.rotation180 ratZero ratZero ratZero ratZero ratOne ratZero)))
       SymGroup.rotation180 := Eq.refl _

theorem rotation270_inverse_is_90 :
    Eq (stGroup (transformInverse (SymTransform.mk SymGroup.rotation270 ratZero ratZero ratZero ratZero ratOne ratZero)))
       SymGroup.rotation90 := Eq.refl _

theorem qubitNormSq_decomposition : ∀ (q : QubitState),
    Eq (qubitNormSq q) (ratAdd (complexNormSq (qubitAlpha q)) (complexNormSq (qubitBeta q))) :=
  fun q => QubitState.casesOn q (fun _ _ => Eq.refl _)

theorem complexConj_involution : ∀ (z : ComplexRat),
    Eq (complexConj (complexConj z)) z :=
  fun z => ComplexRat.casesOn z (fun r i =>
    Rat.casesOn i (fun si ni di =>
      Nat.casesOn ni (Eq.refl _) (fun _ => Bool.casesOn si (Eq.refl _) (Eq.refl _))))

theorem complexNeg_involution : ∀ (z : ComplexRat),
    Eq (complexNeg (complexNeg z)) z :=
  fun z => ComplexRat.casesOn z (fun r i =>
    Rat.casesOn r (fun sr nr dr =>
      Rat.casesOn i (fun si ni di =>
        Nat.casesOn nr
          (Nat.casesOn ni (Eq.refl _) (fun _ => Bool.casesOn si (Eq.refl _) (Eq.refl _)))
          (fun _ => Nat.casesOn ni
            (Bool.casesOn sr (Eq.refl _) (Eq.refl _))
            (fun _ => Bool.casesOn sr
              (Bool.casesOn si (Eq.refl _) (Eq.refl _))
              (Bool.casesOn si (Eq.refl _) (Eq.refl _)))))))

theorem f64Zero_isZero : Eq (f64IsZero f64Zero) Bool.true := Eq.refl _
theorem f64Zero_isFinite : Eq (f64IsFinite f64Zero) Bool.true := Eq.refl _
theorem f64NaN_isNaN : Eq (f64IsNaN f64NaN) Bool.true := Eq.refl _
theorem f64PosInf_isInfinite : Eq (f64IsInfinite f64PosInf) Bool.true := Eq.refl _
theorem f64PosInf_notFinite : Eq (f64IsFinite f64PosInf) Bool.false := Eq.refl _
theorem f64NaN_notFinite : Eq (f64IsFinite f64NaN) Bool.false := Eq.refl _

theorem f64Negate_involution : ∀ (x : F64Repr), Eq (f64Negate (f64Negate x)) x :=
  fun x => F64Repr.casesOn x (fun s e m => Bool.casesOn s (Eq.refl _) (Eq.refl _))

theorem f64Abs_positive : ∀ (x : F64Repr), Eq (f64Sign (f64Abs x)) Bool.true :=
  fun _ => Eq.refl _

theorem f64Abs_idempotent : ∀ (x : F64Repr), Eq (f64Abs (f64Abs x)) (f64Abs x) :=
  fun _ => Eq.refl _

theorem detectSymmetries_includes_identity : ∀ (g : GraphData),
    Eq (stGroup (List.recOn (detectSymmetries g) identityTransform (fun hd _ _ => hd))) SymGroup.identity :=
  fun _ => Eq.refl _

theorem detectSymmetries_nonempty : ∀ (g : GraphData),
    Nat.le 1 (listLengthGeneric (detectSymmetries g)) :=
  fun _ => Nat.succ_le_succ (Nat.zero_le _)

def iterateCool (temp rate minTemp : Rat) (n : Nat) : Rat :=
  Nat.recOn n temp (fun _ ih => coolTemperature ih rate minTemp)

theorem iterateCool_zero : ∀ (t r m : Rat), Eq (iterateCool t r m 0) t :=
  fun _ _ _ => Eq.refl _

theorem iterateCool_succ : ∀ (t r m : Rat) (n : Nat),
    Eq (iterateCool t r m (Nat.succ n)) (coolTemperature (iterateCool t r m n) r m) :=
  fun _ _ _ _ => Eq.refl _

theorem updateEntanglementMap_count_le : ∀ (ents : List EntanglementEntry) (factor : Rat),
    Nat.le (entanglementCount (updateEntanglementMap ents factor)) (entanglementCount ents) :=
  fun ents factor =>
    List.recOn ents (Nat.le_refl 0)
      (fun hd _ ih =>
        EntanglementEntry.casesOn hd (fun key info =>
          Bool.casesOn (ratLe (entCorrelation (entDecay info factor)) (Rat.mk Bool.true 1 100))
            (Nat.succ_le_succ ih) (Nat.le_step ih)))

theorem averageEntanglement_empty : Eq (averageEntanglement []) ratZero := Eq.refl _

theorem entDecay_correlation : ∀ (info : EntanglementInfo) (factor : Rat),
    Eq (entCorrelation (entDecay info factor)) (ratMul (entCorrelation info) factor) :=
  fun info _ => EntanglementInfo.casesOn info (fun _ _ _ _ _ => Eq.refl _)

theorem entUpdate_increases_count : ∀ (info : EntanglementInfo) (c p : Rat),
    Eq (entInteractionCount (entUpdate info c p)) (Nat.succ (entInteractionCount info)) :=
  fun info _ _ => EntanglementInfo.casesOn info (fun _ _ _ _ _ => Eq.refl _)

theorem computeDefaultEnergy_empty : Eq (computeDefaultEnergy emptyGraph) ratZero := Eq.refl _
theorem computeConnectivityEnergy_empty : Eq (computeConnectivityEnergy emptyGraph) ratZero := Eq.refl _
theorem computeCoherenceEnergy_empty : Eq (computeCoherenceEnergy emptyGraph) ratZero := Eq.refl _
theorem computeFractalDimEnergy_empty : Eq (computeFractalDimEnergy emptyGraph) ratZero := Eq.refl _

def fullSystemInvariant (fos : FullOptimizerState) : Prop :=
  And (configValid (fosConfig fos))
      (And (optStateInvariant (fosCurrent fos))
           (And (optStateInvariant (fosBest fos))
                (And (Nat.le 0 (fosIteration fos))
                     (And (Nat.le (fosIteration fos) (cfgMaxIter (fosConfig fos)))
                          (memSafety (fosMem fos))))))

theorem initialSystem_invariant :
    fullSystemInvariant (FullOptimizerState.mk defaultConfig emptyOptState emptyOptState
      [] [identityTransform] emptyStats [] [] 0 (prngInit 42) memInitial) :=
  And.intro defaultConfig_valid
    (And.intro emptyOptState_invariant
      (And.intro emptyOptState_invariant
        (And.intro (Nat.le_refl 0)
          (And.intro (Nat.zero_le 10000) memInitial_safe))))

theorem ratNeg_zero : Eq (ratNeg ratZero) ratZero := Eq.refl _
theorem ratAbs_zero : Eq (ratAbs ratZero) ratZero := Eq.refl _

theorem ratAdd_zero_left : ∀ (r : Rat), Eq (ratAdd ratZero r) r :=
  fun r => Rat.casesOn r (fun s n d => Nat.casesOn d (Eq.refl _) (fun _ => Eq.refl _))

theorem ratMul_zero_left : ∀ (r : Rat), Eq (ratMul ratZero r) ratZero :=
  fun r => Rat.casesOn r (fun s _ _ => Bool.casesOn s (Eq.refl _) (Eq.refl _))

theorem minNat_le_maxNat : ∀ (a b : Nat), Nat.le (minNat a b) (maxNat a b) :=
  fun a => Nat.recOn a (fun b => Nat.zero_le (maxNat 0 b))
    (fun a' ih b => Nat.casesOn b (Nat.zero_le (Nat.succ a'))
      (fun b' => Nat.succ_le_succ (ih b')))

theorem minNat_le_add : ∀ (a b : Nat), Nat.le (minNat a b) (Nat.add a b) :=
  fun a b => Nat.le_trans (minNat_le_left a b) (nat_le_add_right a b)

theorem minNat_maxNat_absorb : ∀ (a b : Nat), Eq (minNat a (maxNat a b)) a :=
  fun a => Nat.recOn a (fun _ => Eq.refl 0)
    (fun a' ih b => Nat.casesOn b (congrArg Nat.succ (ih 0))
      (fun b' => congrArg Nat.succ (ih b')))

theorem maxNat_minNat_absorb : ∀ (a b : Nat), Eq (maxNat a (minNat a b)) a :=
  fun a => Nat.recOn a (fun _ => Eq.refl 0)
    (fun a' ih b => Nat.casesOn b (Eq.refl _)
      (fun b' => congrArg Nat.succ (ih b')))

theorem listAppend_nil_left : ∀ (l : List α), Eq (listAppendGeneric [] l) l :=
  fun _ => Eq.refl _

theorem listAppend_nil_right : ∀ (l : List α), Eq (listAppendGeneric l []) l :=
  fun l => List.recOn l (Eq.refl _) (fun hd _ ih => congrArg (List.cons hd) ih)

theorem listAppend_assoc : ∀ (l1 l2 l3 : List α),
    Eq (listAppendGeneric (listAppendGeneric l1 l2) l3) (listAppendGeneric l1 (listAppendGeneric l2 l3)) :=
  fun l1 l2 l3 => List.recOn l1 (Eq.refl _) (fun hd _ ih => congrArg (List.cons hd) ih)

theorem listAppend_length : ∀ (l1 l2 : List α),
    Eq (listLengthGeneric (listAppendGeneric l1 l2)) (Nat.add (listLengthGeneric l1) (listLengthGeneric l2)) :=
  fun l1 l2 => List.recOn l1
    (Eq.symm (nat_add_zero_left (listLengthGeneric l2)))
    (fun _ _ ih => congrArg Nat.succ ih)

theorem rot_exhaustive : ∀ (r : Rotation),
    Or (Eq r Rotation.rot0) (Or (Eq r Rotation.rot90) (Or (Eq r Rotation.rot180) (Eq r Rotation.rot270))) :=
  fun r => Rotation.casesOn r
    (Or.inl (Eq.refl _)) (Or.inr (Or.inl (Eq.refl _)))
    (Or.inr (Or.inr (Or.inl (Eq.refl _)))) (Or.inr (Or.inr (Or.inr (Eq.refl _))))

theorem symGroup_exhaustive : ∀ (g : SymGroup),
    Or (Eq g SymGroup.identity) (Or (Eq g SymGroup.reflection) (Or (Eq g SymGroup.rotation90)
      (Or (Eq g SymGroup.rotation180) (Or (Eq g SymGroup.rotation270) (Eq g SymGroup.translation))))) :=
  fun g => SymGroup.casesOn g
    (Or.inl (Eq.refl _)) (Or.inr (Or.inl (Eq.refl _)))
    (Or.inr (Or.inr (Or.inl (Eq.refl _)))) (Or.inr (Or.inr (Or.inr (Or.inl (Eq.refl _)))))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Eq.refl _)))))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Eq.refl _))))))

theorem edgeQuality_exhaustive : ∀ (e : EdgeQuality),
    Or (Eq e EdgeQuality.coherent) (Or (Eq e EdgeQuality.decoherent)
      (Or (Eq e EdgeQuality.entangled) (Eq e EdgeQuality.classical))) :=
  fun e => EdgeQuality.casesOn e
    (Or.inl (Eq.refl _)) (Or.inr (Or.inl (Eq.refl _)))
    (Or.inr (Or.inr (Or.inl (Eq.refl _)))) (Or.inr (Or.inr (Or.inr (Eq.refl _))))

theorem moveType_exhaustive : ∀ (mt : MoveType),
    Or (Eq mt MoveType.perturbWeights) (Or (Eq mt MoveType.perturbPhases)
      (Or (Eq mt MoveType.createEntanglement) (Or (Eq mt MoveType.applySymmetry)
        (Or (Eq mt MoveType.perturbQubits) (Or (Eq mt MoveType.perturbFractalDim)
          (Eq mt MoveType.toggleEdge)))))) :=
  fun mt => MoveType.casesOn mt
    (Or.inl (Eq.refl _)) (Or.inr (Or.inl (Eq.refl _)))
    (Or.inr (Or.inr (Or.inl (Eq.refl _)))) (Or.inr (Or.inr (Or.inr (Or.inl (Eq.refl _)))))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Eq.refl _))))))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Eq.refl _)))))))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Eq.refl _)))))))

theorem allocError_exhaustive : ∀ (e : AllocError),
    Or (Eq e AllocError.outOfMemory) (Or (Eq e AllocError.doubleFree)
      (Or (Eq e AllocError.useAfterFree) (Eq e AllocError.invalidAlignment))) :=
  fun e => AllocError.casesOn e
    (Or.inl (Eq.refl _)) (Or.inr (Or.inl (Eq.refl _)))
    (Or.inr (Or.inr (Or.inl (Eq.refl _)))) (Or.inr (Or.inr (Or.inr (Eq.refl _))))

theorem orderedPairKey_le : ∀ (n1 n2 : NodeId),
    NodePairKey.casesOn (orderedPairKey n1 n2) (fun k1 k2 =>
      Eq (Nat.ble (nodeIdVal k1) (nodeIdVal k2)) Bool.true) :=
  fun n1 n2 =>
    NodeId.casesOn n1 (fun v1 =>
      NodeId.casesOn n2 (fun v2 =>
        Bool.casesOn (Nat.ble v1 v2) (Eq.refl _) (Eq.refl _)))

theorem symGroupOrder_positive_for_finite : ∀ (g : SymGroup),
    Not (Eq g SymGroup.translation) → Nat.le 1 (symGroupOrder g) :=
  fun g =>
    SymGroup.casesOn g
      (fun _ => Nat.succ_le_succ (Nat.zero_le 0))
      (fun _ => Nat.succ_le_succ (Nat.zero_le 1))
      (fun _ => Nat.succ_le_succ (Nat.zero_le 3))
      (fun _ => Nat.succ_le_succ (Nat.zero_le 1))
      (fun _ => Nat.succ_le_succ (Nat.zero_le 3))
      (fun h => False.elim (h (Eq.refl _)))
