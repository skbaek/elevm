import Elevm.Types
import Elevm.EC
import Elevm.Hash

abbrev AccessList : Type := List (Adr × List B256)

instance : ToString AccessList := ⟨@List.toString _ _⟩

abbrev State : Type := Lean.RBMap Adr Acct compare

def State.toStrings (w : State) : List String :=
  let kvs := w.toArray.toList
  let kvToStrings : Adr × Acct → List String :=
    fun x => Acct.toStrings ("0x" ++ x.fst.toHex.dropZeroes) x.snd
  fork "STATE" (kvs.map kvToStrings)

def AccessItem.toStrings : (Adr × List B256) → List String
  | ⟨a, ks⟩ => fork a.toHex <| ks.map <| fun k => [k.toHex]

def AccessList.toStrings (al : AccessList) : List String :=
    fork "ACCESS LIST" <| al.map <| AccessItem.toStrings

-- class Authorization
structure Auth : Type where
  chainId : B64
  address : Adr
  nonce : B64
  yParity : Nat
  r : B256
  s : B256

inductive TxType : Type
  -- Legacy (including EIP-155)
  | zero
    (gasPrice : Nat)
    (receiver : Option Adr)
  -- EIP-2930
  | one
    (chainId : B64)
    (gasPrice : Nat)
    (receiver : Option Adr)
    (accessList : AccessList)
  -- EIP-1559
  | two
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (receiver : Option Adr)
    (accessList : AccessList)
  -- EIP-4844
  | three
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (receiver : Adr)
    (accessList : AccessList)
    (maxBlobFee : Nat)
    (blobHashes : List B256)
  | four
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (receiver : Adr)
    (accessList : AccessList)
    (auths : List Auth)

structure Withdrawal : Type where
  (globalIndex : B64)
  (validatorIndex : B64)
  (recipient : Adr)
  (amount : B256)

structure Header : Type where
  parentHash : B256
  ommersHash : B256
  coinbase : Adr
  stateRoot : B256
  txsRoot : B256
  receiptRoot : B256
  bloom : B8L
  difficulty : Nat
  number : Nat
  gasLimit : Nat
  gasUsed : Nat
  timestamp : Nat
  extraData : B8L
  prevRandao : B256
  nonce : B64
  baseFeePerGas : Nat
  withdrawalsRoot : B256
  blobGasUsed : Nat
  excessBlobGas : Nat
  parentBeaconBlockRoot : B256
  requestsHash : Option B256

def Header.toStrings (header : Header) : List String :=
  fork "header" [
    [s!"parent hash : {header.parentHash}"],
    [s!"ommers hash : {header.ommersHash}"],
    [s!"coinbase : {header.coinbase}"],
    [s!"stateRoot : {header.stateRoot}"],
    [s!"transactions root : {header.txsRoot}"],
    [s!"receipt root : {header.receiptRoot}"],
    [s!"bloom : {header.bloom.toHex}"],
    [s!"difficulty : {header.difficulty}"],
    [s!"number : {header.number}"],
    [s!"gas limit : {header.gasLimit}"],
    [s!"gas used : {header.gasUsed}"],
    [s!"timestamp : {header.timestamp}"],
    [s!"extra data : {header.extraData.toHex}"],
    [s!"prevRandao : {header.prevRandao}"],
    [s!"nonce : {header.nonce}"],
    [s!"base fee per gas : {header.baseFeePerGas}"],
    [s!"withdrawals root : {header.withdrawalsRoot}"],
    [s!"blob gas used : {header.blobGasUsed}"],
    [s!"excess blob gas : {header.excessBlobGas}"],
    [s!"parent beacon block root : {header.parentBeaconBlockRoot}"],
    [s!"requests Hash : {header.requestsHash}"],
  ]

instance : ToString Header := ⟨String.joinln ∘ Header.toStrings⟩

def Header.toBLT (header : Header) : BLT :=
  BLT.list <| [
    BLT.b8s header.parentHash.toB8L,
    BLT.b8s header.ommersHash.toB8L,
    BLT.b8s header.coinbase.toB8L,
    BLT.b8s header.stateRoot.toB8L,
    BLT.b8s header.txsRoot.toB8L,
    BLT.b8s header.receiptRoot.toB8L,
    BLT.b8s header.bloom,
    BLT.b8s header.difficulty.toB8L,
    BLT.b8s header.number.toB8L,
    BLT.b8s header.gasLimit.toB8L,
    BLT.b8s header.gasUsed.toB8L,
    BLT.b8s header.timestamp.toB8L,
    BLT.b8s header.extraData,
    BLT.b8s header.prevRandao.toB8L,
    BLT.b8s header.nonce.toB8L,
    BLT.b8s header.baseFeePerGas.toB8L,
    BLT.b8s header.withdrawalsRoot.toB8L,
    BLT.b8s header.blobGasUsed.toB8L,
    BLT.b8s header.excessBlobGas.toB8L,
    BLT.b8s header.parentBeaconBlockRoot.toB8L
  ] ++
    match header.requestsHash with
    | none => []
    | some rh => [BLT.b8s rh.toB8L]

structure Tx : Type where
  (nonce : B64)
  (gas : Nat)
    (value : Nat)
  (data : B8L)
  (v : Nat)
  (r : B8L)
  (s : B8L)
  (type : TxType)

structure Block : Type where
  header : Header
  txs : List (B8L ⊕ Tx)
  ommers : List Header
  wds : List Withdrawal

structure BlockChain : Type where
  blocks : List Block
  state : State
  chainId : B64

def TxType.receiver? : TxType → Option Adr
  | .zero _ receiver => receiver
  | .one _ _ receiver _ => receiver
  | .two _ _ _ receiver _ => receiver
  | .three _ _ _ receiver _ _ _ => some receiver
  | .four _ _ _ receiver _ _ => some receiver

def TxType.accessList : TxType → AccessList
  | .zero _ _ => []
  | .one _ _ _ al => al
  | .two _ _ _ _ al => al
  | .three _ _ _ _ al _ _ => al
  | .four _ _ _ _ al _ => al

def Tx.accessList (tx : Tx) : AccessList := tx.type.accessList

def Tx.auths (tx : Tx) : List Auth :=
  match tx.type with
  | .four _ _ _ _ _ auths => auths
  | _ => []

def B8L.sig (bs : B8L) : B8L := List.dropWhile (· = 0) bs

def AccessList.toBLT (al : AccessList) : BLT :=
  let aux : Adr × List B256 → BLT
  | ⟨adr, words⟩ =>
    .list [.b8s adr.toB8L, .list (words.map (.b8s ∘ B256.toB8L))]
  .list (al.map aux)

def Auth.toBLT (auth : Auth) : BLT :=
  .list [
    .b8s auth.chainId.toB8L.sig,
    .b8s <| auth.address.toB8L,
    .b8s auth.nonce.toNat.toB8L,
    .b8s auth.yParity.toB8L,
    .b8s auth.r.toB8L,
    .b8s auth.s.toB8L,
  ]

def Tx.toBLT (tx : Tx) : BLT :=
  match tx.type with
  | .zero gasPrice receiver =>
    .list [
      .b8s tx.nonce.toNat.toB8L,
      .b8s gasPrice.toB8L,
      .b8s tx.gas.toB8L,
      .b8s <| receiver.rec [] Adr.toB8L,
      .b8s tx.value.toB8L,
      .b8s tx.data,
      .b8s tx.v.toB8L,
      .b8s (trimZero tx.r),
      .b8s (trimZero tx.s),
    ]
  | .one chainId gasPrice receiver accessList =>
    .list [
      .b8s chainId.toB8L.sig,
      .b8s tx.nonce.toNat.toB8L,
      .b8s gasPrice.toB8L,
      .b8s tx.gas.toB8L,
      .b8s <| receiver.rec [] Adr.toB8L,
      .b8s tx.value.toB8L,
      .b8s tx.data,
      accessList.toBLT,
      .b8s tx.v.toB8L,
      .b8s (trimZero tx.r),
      .b8s (trimZero tx.s)
    ]
  | .two chainId maxPriorityFee maxFee receiver accessList =>
    .list [
      .b8s chainId.toB8L.sig,
      .b8s tx.nonce.toNat.toB8L,
      .b8s maxPriorityFee.toB8L,
      .b8s maxFee.toB8L,
      .b8s tx.gas.toB8L,
      .b8s <| receiver.rec [] Adr.toB8L,
      .b8s tx.value.toB8L,
      .b8s tx.data,
      accessList.toBLT,
      .b8s tx.v.toB8L,
      .b8s (trimZero tx.r),
      .b8s (trimZero tx.s)
    ]
  | .three chainId maxPriorityFee maxFee receiver accessList maxBlobFee blobHashes =>
    .list [
      .b8s chainId.toB8L.sig,
      .b8s tx.nonce.toNat.toB8L,
      .b8s maxPriorityFee.toB8L,
      .b8s maxFee.toB8L,
      .b8s tx.gas.toB8L,
      .b8s receiver.toB8L,
      .b8s tx.value.toB8L,
      .b8s tx.data,
      accessList.toBLT,
      .b8s maxBlobFee.toB8L,
      .list <| blobHashes.map <| .b8s ∘ B256.toB8L,
      .b8s tx.v.toB8L,
      .b8s (trimZero tx.r),
      .b8s (trimZero tx.s)
    ]
  | .four chainId maxPriorityFee maxFee receiver accessList auths =>
    .list [
      .b8s chainId.toB8L.sig,
      .b8s tx.nonce.toNat.toB8L,
      .b8s maxPriorityFee.toB8L,
      .b8s maxFee.toB8L,
      .b8s tx.gas.toB8L,
      .b8s receiver.toB8L,
      .b8s tx.value.toB8L,
      .b8s tx.data,
      accessList.toBLT,
      .list <| auths.map <| Auth.toBLT,
      .b8s tx.v.toB8L,
      .b8s (trimZero tx.r),
      .b8s (trimZero tx.s)
    ]

def Auth.toStrings (auth : Auth) : List String :=
  fork
    "auth"
    [
      [s!"chain ID : {auth.chainId}"],
      [s!"address : {auth.address}"],
      [s!"nonce : {auth.nonce.toHex}"],
      [s!"y parity : {auth.yParity}"],
      [s!"r : {auth.r.toHex}"],
      [s!"s : {auth.s.toHex}"]
    ]

def Auths.toStrings (al : List Auth) : List String :=
    fork "auth list" <| al.map <| Auth.toStrings

def TxType.toStrings : TxType → List String
  | zero
    (gasPrice : Nat)
    (receiver : Option Adr) =>
    fork "Type-0" [
      [s!"gas price : {gasPrice.repr}"],
      [s!"receiver : {toString receiver}"]
    ]
  | one
    (chainId : B64)
    (gasPrice : Nat)
    (receiver : Option Adr)
    (accessList : AccessList) =>
    fork "Type-1" [
      [s!"chain ID : {chainId}"],
      [s!"gas price : {gasPrice.repr}"],
      [s!"receiver : {toString receiver}"],
      accessList.toStrings
    ]
  | two
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (receiver : Option Adr)
    (accessList : AccessList) =>
    fork "Type-2" [
      [s!"chain ID : {chainId}"],
      [s!"max priority fee : {maxPriorityFee.repr}"],
      [s!"max fee : {maxFee.repr}"],
      [s!"receiver : {toString receiver}"],
      accessList.toStrings
    ]
  | three
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (receiver : Adr)
    (accessList : AccessList)
    (maxBlobFee : Nat)
    (blobHashes : List B256) =>
    fork "Type-3" [
      [s!"chain ID : {chainId}"],
      [s!"max priority fee : {maxPriorityFee.repr}"],
      [s!"max fee : {maxFee.repr}"],
      [s!"receiver : {toString receiver}"],
      accessList.toStrings,
      [s!"max blob fee : {maxBlobFee.repr}"],
      fork "blob hashes" (blobHashes.map <| fun bh => [bh.toHex])
    ]
  | four
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (receiver : Adr)
    (accessList : AccessList)
    (auths : List Auth) =>
    fork "Type-4" [
      [s!"chain ID : {chainId}"],
      [s!"max priority fee : {maxPriorityFee.repr}"],
      [s!"max fee : {maxFee.repr}"],
      [s!"receiver : {toString receiver}"],
      accessList.toStrings,
      Auths.toStrings auths
    ]

instance : ToString TxType := ⟨String.joinln ∘ TxType.toStrings⟩

def Tx.toStrings (tx : Tx) : List String :=
  fork "tx" [
    [s!"nonce : {tx.nonce.toHex}"],
    [s!"gas limit : {tx.gas}"],
    [s!"value : {tx.value.repr}"],
    [s!"calldata : {tx.data.toHex}"],
    [s!"v : {tx.v}"],
    [s!"r : {tx.r.toHex}"],
    [s!"s : {tx.s.toHex}"],
    tx.type.toStrings
  ]

instance : ToString Tx := ⟨String.joinln ∘ Tx.toStrings⟩

def B8LOrTxToBLT : B8L ⊕ Tx → BLT
  | .inl bs => BLT.b8s bs
  | .inr tx => tx.toBLT

def Withdrawal.toBLT (wd : Withdrawal) : BLT :=
  BLT.list [
    BLT.b8s wd.globalIndex.toB8L.sig,
    BLT.b8s wd.validatorIndex.toB8L.sig,
    BLT.b8s wd.recipient.toB8L,
    BLT.b8s wd.amount.toB8L.sig
  ]

def Block.toBLT (block : Block) : BLT :=
  let txBLTs : List BLT := block.txs.map B8LOrTxToBLT
  .list [
    Header.toBLT block.header,
    .list txBLTs,
    .list <| block.ommers.map Header.toBLT,
    .list <| block.wds.map Withdrawal.toBLT
  ]

def TxType.gasPrice (baseFee : Nat) : TxType → Nat
  | .zero gp _ => gp
  | .one _ gp _ _ => gp
  | .two _ mpf mf _ _ => min mf (baseFee + mpf)
  | .three _ mpf mf _ _ _ _ => min mf (baseFee + mpf)
  | .four _ mpf mf _ _ _ => min mf (baseFee + mpf)

def TxType.blobHashes : TxType → List B256
  | .zero _ _ => []
  | .one _ _ _ _ => []
  | .two _ _ _ _ _ => []
  | .three _ _ _ _ _ _ bhs => bhs
  | .four _ _ _ _ _ _ => []

def Tx.blobHashes (tx : Tx) : List B256 := tx.type.blobHashes

def BLT.toB256 : BLT → Option B256
  | .b8s bs => some bs.toB256P
  | _ => none

-- nibbles-to-bytes maps
abbrev NTB := Lean.RBMap (List B8) (List B8) (@List.compare _ ⟨B8.compareLows⟩)

def NTB.toStrings (s : NTB) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : B8L × B8L → List String :=
    λ nb => [s!"{B4L.toHex (nb.fst.map B8.lows)} : {nb.snd.toHex}"]
  fork "NTB" (kvs.map kvToStrings)

def hpAux : B8L → (Option B8 × B8L)
  | [] => ⟨none, []⟩
  | n :: ns =>
    match hpAux ns with
    | ⟨none, bs⟩ => ⟨some n, bs⟩
    | ⟨some m, bs⟩ => ⟨none, ((n <<< 4) ||| m.lows) :: bs⟩

def hp (ns : B8L) (t : Bool) : B8L :=
  match hpAux ns with
  | ⟨none, bs⟩ => (cond t (0x20) 0) :: bs
  | ⟨some n, bs⟩ => ((cond t 0x30 0x10) ||| n.lows) :: bs

def commonPrefixCore : B8L → B8L → B8L
  | [], _ => []
  | _, [] => []
  | n :: ns, n' :: ns' =>
    if n = n' then n :: commonPrefixCore ns ns'
    else []

def commonPrefix (n : B8) (ns : B8L) : List B8L → Option B8L
  | [] => some (n :: ns)
  | ns' :: nss =>
    match commonPrefixCore (n :: ns) ns' with
    | [] => none
    | (n' :: ns'') => commonPrefix n' ns'' nss

def NTB.empty : NTB := Lean.RBMap.empty

def sansPrefix : B8L → B8L → Option B8L
  | [], ns => some ns
  | _, [] => none
  | n :: ns, n' :: ns' =>
    if n = n' then sansPrefix ns ns' else none

def insertSansPrefix (pfx : B8L) (m : NTB) (ns : B8L) (bs : B8L) : Option NTB := do
  (m.insert · bs) <$> sansPrefix pfx ns

def NTB.factor (m : NTB) : Option (B8L × NTB) := do
  let ((n :: ns) :: nss) ← some (m.toList.map Prod.fst) | none
  let pfx ← commonPrefix n ns nss
  let m' ← Lean.RBMap.foldM (insertSansPrefix pfx) NTB.empty m
  some ⟨pfx, m'⟩

structure NTBs : Type where
  (x0 : NTB) (x1 : NTB) (x2 : NTB) (x3 : NTB)
  (x4 : NTB) (x5 : NTB) (x6 : NTB) (x7 : NTB)
  (x8 : NTB) (x9 : NTB) (xA : NTB) (xB : NTB)
  (xC : NTB) (xD : NTB) (xE : NTB) (xF : NTB)

def NTBs.empty : NTBs :=
  ⟨ .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty ⟩

def NTBs.update (js : NTBs) (f : NTB → NTB) (k : B8) : NTBs :=
  match k.toBools with
  | ⟨_, _, _, _, 0, 0, 0, 0⟩ => { js with x0 := f js.x0}
  | ⟨_, _, _, _, 0, 0, 0, 1⟩ => { js with x1 := f js.x1}
  | ⟨_, _, _, _, 0, 0, 1, 0⟩ => { js with x2 := f js.x2}
  | ⟨_, _, _, _, 0, 0, 1, 1⟩ => { js with x3 := f js.x3}
  | ⟨_, _, _, _, 0, 1, 0, 0⟩ => { js with x4 := f js.x4}
  | ⟨_, _, _, _, 0, 1, 0, 1⟩ => { js with x5 := f js.x5}
  | ⟨_, _, _, _, 0, 1, 1, 0⟩ => { js with x6 := f js.x6}
  | ⟨_, _, _, _, 0, 1, 1, 1⟩ => { js with x7 := f js.x7}
  | ⟨_, _, _, _, 1, 0, 0, 0⟩ => { js with x8 := f js.x8}
  | ⟨_, _, _, _, 1, 0, 0, 1⟩ => { js with x9 := f js.x9}
  | ⟨_, _, _, _, 1, 0, 1, 0⟩ => { js with xA := f js.xA}
  | ⟨_, _, _, _, 1, 0, 1, 1⟩ => { js with xB := f js.xB}
  | ⟨_, _, _, _, 1, 1, 0, 0⟩ => { js with xC := f js.xC}
  | ⟨_, _, _, _, 1, 1, 0, 1⟩ => { js with xD := f js.xD}
  | ⟨_, _, _, _, 1, 1, 1, 0⟩ => { js with xE := f js.xE}
  | ⟨_, _, _, _, 1, 1, 1, 1⟩ => { js with xF := f js.xF}

def NTBs.insert (js : NTBs) : B8L → B8L → NTBs
  | [], _ => js
  | n :: ns, bs => js.update (Lean.RBMap.insert · ns bs) n

mutual

  def nodeComp : Nat → NTB → BLT
    | 0, _ => .b8s []
    | k + 1, j =>
      if j.isEmpty
      then .b8s []
      else let r := structComp k j
           if r.toB8L.length < 32
           then r
           else .b8s <| r.toB8L.keccak.toB8L

  def structComp : Nat → NTB → BLT
    | 0, _ => .b8s []
    | k + 1, j =>
      if j.isEmpty
            then .b8s []       else if j.isSingleton
           then match j.toList with
                | [(k, v)] => .list [.b8s (hp k 1), .b8s v]
                | _ => .b8s []            else match j.factor with
                | none =>
                  let js := Lean.RBMap.fold NTBs.insert NTBs.empty j
                  .list [ nodeComp k js.x0, nodeComp k js.x1, nodeComp k js.x2,
                          nodeComp k js.x3, nodeComp k js.x4, nodeComp k js.x5,
                          nodeComp k js.x6, nodeComp k js.x7, nodeComp k js.x8,
                          nodeComp k js.x9, nodeComp k js.xA, nodeComp k js.xB,
                          nodeComp k js.xC, nodeComp k js.xD, nodeComp k js.xE,
                          nodeComp k js.xF, .b8s (j.findD [] []) ]
                | some (pfx, j') => .list [.b8s (hp pfx 0), nodeComp k j']

end

def NTB.maxKeyLength (j : NTB) : Nat :=
  (j.toList.map (List.length ∘ Prod.fst)).maxD 0

def collapse (j : NTB) : BLT := structComp (2 * (j.maxKeyLength + 1)) j

def trie (j : NTB) : B256 :=
  B8L.keccak <| (collapse j).toB8L

def B256.toBLT (w : B256) : BLT := .b8s w.toB8L

def Stor.toNTB (s : Stor) : NTB :=
  let f : NTB → B256 → B256 → NTB :=
    λ j k v =>
      j.insert
        k.keccak.toB4s
        ((BLT.toB8L <| .b8s <| B8L.sig <| v.toB8L))
  Lean.RBMap.fold f NTB.empty s

def B256.zerocount (x : B256) : Nat → Nat
  | 0 => 0
  | k + 1 => if x = 0 then k + 1 else B256.zerocount (x >>> 8) k

def B256.bytecount (x : B256) : Nat := 32 - (B256.zerocount x 32)

def toKeyVal (pr : Adr × Acct) : B8L × B8L :=
  let ad := pr.fst
  let ac := pr.snd
  ⟨
    ad.toB8L.keccak.toB4s,
    let val' :=
      BLT.toB8L <| .list [
        .b8s (ac.nonce.toB8L.sig),
        .b8s (ac.bal.toB8L.sig),
        B256.toBLT (trie ac.stor.toNTB),
        B256.toBLT <| (B8L.keccak ac.code.toList)
      ]
    val'
  ⟩

-- values --

def gHigh : Nat := 10
def gJumpdest : Nat := 1
def txCreateCost : Nat := 32000
def gasInitCodeWordCost : Nat := 2
def gBase : Nat := 2
def gasCopy : Nat := 3
def gReturnDataCopy : Nat := 3
def gMemory : Nat := 3
def gKeccak256 : Nat := 30
def gasKeccak256Word : Nat := 6
def gVerylow : Nat := 3
def gLow : Nat := 5
def gMid : Nat := 8
def gExp : Nat := 10
def gExpbyte : Nat := 50
def gasColdSload : Nat := 2100
def gasStorageSet : Nat := 20000
def rSClear : Nat := 4800
def gBlockhash : Nat := 20
def gasCodeDeposit : Nat := 200
def gasCreate : Nat := 32000
def gHashopcode : Nat := 3
def gasPerBlob : Nat := 2 ^ 17
def gasStorageUpdate := 5000
def gasEcrecover : Nat := 3000
def maxCodeSize : Nat := 24576 -- 0x00006000
def maxInitcodeSize : Nat := 49152 -- 0x0000C000
def gNewAccount : Nat := 25000
def gasSelfDestructNewAccount : Nat := 25000
def gasCallValue : Nat := 9000
def gCallStipend : Nat := 2300
def gasWarmAccess : Nat := 100
def gasColdAccountAccess : Nat := 2600
def gasSelfDestruct : Nat := 5000
def gLog : Nat := 375
def gLogdata : Nat := 8
def gLogtopic : Nat := 375
def depositContractAddress : Adr :=
  0x00000000219ab540356cbb839cbe05303d7705fa
def depositEventSignatureHash : B256 :=
  0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5
def depositEventLength : Nat := 576
def pubkeyOffset : Nat := 160
def amountOffset : Nat := 320
def signatureOffset : Nat := 384
def indexOffset : Nat := 512
def withdrawalCredentialsOffset := 256
def pubkeySize : Nat := 48
def amountSize : Nat := 8
def indexSize : Nat := 8
def signatureSize : Nat := 96
def withdrawalCredentialsSize : Nat := 32
def txAccessListAddressCost : Nat := 2400
def txAccessListStorageKeyCost : Nat := 1900
def floorCalldataCost : Nat := 10
def standardCallDataTokenCost : Nat := 4
def depositRequestType : B8L := [0]
def withdrawalRequestType : B8L := [1]
def consolidationRequestType : B8L := [2]
def withdrawalRequestPredeployAddress : Adr := 0x00000961Ef480Eb55e80D19ad83579A64c007002
def consolidationRequestPredeployAddress : Adr := 0x0000BBdDc7CE488642fb579F8B00f3a590007251
def historyStorageAddress : Adr := 0x0000F90827F1C53a10cb7A02335B175320002935
def emptyOmmerHash : B256 := (BLT.list []).toB8L.keccak
def setCodeTxMagic : B8L := [0x05]
def beaconRootsAddress : Adr := 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02
def systemAddress : Adr := 0xfffffffffffffffffffffffffffffffffffffffe
def systemTransactionGas : Nat := 30000000
def maxInitCodeSize : Nat := maxCodeSize * 2
def maxBlobGasPerBlock : Nat := 1179648
def versionedHashVersionKzg : B8 := 0x01
def eoaDelegationMarker : B8L := [0xEF, 0x01, 0x00]
def blobBaseFeeUpdateFraction : Nat := 3338477
def gasBlake2PerRound : Nat := 1
def eoaDelegatedCodeLength : Nat := 23
def targetBlobGasPerBlock : Nat := 0x60000 -- U64(393216)
def elasticityMultiplier : Nat := 2
def gasLimitAdjustmentFactor : Nat := 1024
def gasLimitMinimum : Nat := 5000
def baseFeeMaxChangeDenominator := 8
def perEmptyAccountCost := 25000
def perAuthBaseCost := 12500
def txBaseCost : Nat := 21000
def lengthPerPair : Nat := 160
def g1MaxDiscount : Nat := 519
def g2MaxDiscount : Nat := 524

def g1KDiscount : List Nat :=
  [
    1000, 949, 848, 797, 764, 750, 738, 728,
    719, 712, 705, 698, 692, 687, 682, 677,
    673, 669, 665, 661, 658, 654, 651, 648,
    645, 642, 640, 637, 635, 632, 630, 627,
    625, 623, 621, 619, 617, 615, 613, 611,
    609, 608, 606, 604, 603, 601, 599, 598,
    596, 595, 593, 592, 591, 589, 588, 586,
    585, 584, 582, 581, 580, 579, 577, 576,
    575, 574, 573, 572, 570, 569, 568, 567,
    566, 565, 564, 563, 562, 561, 560, 559,
    558, 557, 556, 555, 554, 553, 552, 551,
    550, 549, 548, 547, 547, 546, 545, 544,
    543, 542, 541, 540, 540, 539, 538, 537,
    536, 536, 535, 534, 533, 532, 532, 531,
    530, 529, 528, 528, 527, 526, 525, 525,
    524, 523, 522, 522, 521, 520, 520, 519,
  ]

def g2KDiscount : List Nat :=
  [
    1000, 1000, 923, 884, 855, 832, 812, 796,
    782, 770, 759, 749, 740, 732, 724, 717,
    711, 704, 699, 693, 688, 683, 679, 674,
    670, 666, 663, 659, 655, 652, 649, 646,
    643, 640, 637, 634, 632, 629, 627, 624,
    622, 620, 618, 615, 613, 611, 609, 607,
    606, 604, 602, 600, 598, 597, 595, 593,
    592, 590, 589, 587, 586, 584, 583, 582,
    580, 579, 578, 576, 575, 574, 573, 571,
    570, 569, 568, 567, 566, 565, 563, 562,
    561, 560, 559, 558, 557, 556, 555, 554,
    553, 552, 552, 551, 550, 549, 548, 547,
    546, 545, 545, 544, 543, 542, 541, 541,
    540, 539, 538, 537, 537, 536, 535, 535,
    534, 533, 532, 532, 531, 530, 530, 529,
    528, 528, 527, 526, 526, 525, 524, 524
  ]

def initCodeCost (len : Nat) : Nat :=
  gasInitCodeWordCost * (ceilDiv len 32)

instance {a b : Adr} : Decidable (a = b) := by
  cases a; cases b; simp; apply instDecidableAnd

instance : Hashable Adr := ⟨Adr.low⟩
instance : Hashable (Adr × B256) := ⟨λ x => x.1.low⟩

abbrev AdrSet : Type := @Std.HashSet Adr _ _
abbrev KeySet : Type := @Std.HashSet (Adr × B256) _ _

abbrev Tra : Type := Lean.RBMap Adr Stor compare

def Sta : Type := Array B256 × Nat

instance : Inhabited Sta := ⟨⟨.empty, 0⟩⟩

def calculateMemoryGasCost (memSize : Nat) : Nat :=
  let memWordSize := ceilDiv memSize 32
  let linearCost := gMemory * memWordSize
  let quadraticCost := (memWordSize ^ 2) / 512
  linearCost + quadraticCost

structure Mem : Type where
  data : Array B8
  size : Nat

def Mem.empty : Mem := ⟨.empty, 0⟩

structure Log : Type where
  (address : Adr)
  (topics : List B256)
  (data : B8L)

-- class Benvironment
structure Benv : Type where
  chainId : B64
  state : State
  origState : State
  createdAccounts : AdrSet
  blockGasLimit : Nat
  blockHashes: List B256
  coinbase : Adr
  number : Nat
  baseFeePerGas : Nat
  time : B256
  prevRandao : B256
  excessBlobGas : Nat
  parentBeaconBlockRoot : B256

-- class TransactionEnvironment
structure Tenv : Type where
    origin: Adr
    gasPrice: Nat
    gas: Nat
    accessListAddresses: AdrSet
    accessListStorageKeys: KeySet
    transientStorage: Tra
    blobVersionedHashes: List B256
    auths : List Auth
    indexInBlock : Option Nat
    txHash: Option B256

-- class Message
structure Msg : Type where
  benv: Benv
  tenv: Tenv
  caller: Adr
  target: Option Adr
  currentTarget: Adr
  gas: Nat
  value: B256
  data: B8L
  codeAddress: Option Adr
  code: ByteArray
  depth: Nat
  shouldTransferValue: Bool
  isStatic: Bool
  accessedAddresses: AdrSet
  accessedStorageKeys: KeySet
  disablePrecompiles : Bool

def hasErrorType (err errType : String) : Bool :=
  err = errType || String.isPrefixOf (errType ++ " : ") err

abbrev isExceptionalHalt (err : String) : Prop :=
  List.any [
    "StackUnderflowError",
    "StackOverflowError",
    "OutOfGasError",
    "InvalidOpcode",
    "InvalidJumpDestError",
    "StackDepthLimitError",
    "WriteInStaticContext",
    "OutOfBoundsRead",
    "InvalidParameter",
    "InvalidContractPrefix",
    "AddressCollision",
    "KZGProofError"
  ] (hasErrorType err)

def isInvalidTransaction (err : String) : Bool :=
  List.any [
    "InvalidTransaction",
    "InsufficientBalanceError",
    "NonceMismatchError",
    "GasUsedExceedsLimitError",
    "InvalidSenderError",
    "BlobGasLimitExceededError",
    "NoBlobDataError",
    "InvalidSignatureError",
    "TransactionTypeError",
    "TransactionTypeContractCreationError",
    "InsufficientMaxFeePerBlobGasError",
    "InsufficientMaxFeePerGasError",
    "InvalidBlobVersionedHashError",
    "PriorityFeeGreaterThanMaxFeeError",
    "EmptyAuthorizationListError"
  ] (hasErrorType err)

def isEthereumException (err : String) : Bool :=
  hasErrorType err "InvalidBlock" ||
  isInvalidTransaction err

def isRlpException (err : String) : Bool :=
  List.any ["EncodingError", "DecodingError"] (hasErrorType err)

structure Evm : Type where
  pc : Nat
  stack: List B256
  memory: Mem
  code: ByteArray
  gas_left: Nat
  logs: List Log
  refund_counter: Int
  msg: Msg
  output: B8L
  accountsToDelete: AdrSet
  return_data: B8L
  error: Option String
  accessedAddresses: AdrSet
  accessedStorageKeys: KeySet

def Stack.toStrings (stack : List B256) : List String :=
  fork "STACK" [
    ["-------------------------- STACK TOP ---------------------------"] ++
    stack.map B256.toHex ++
    ["------------------------- STACK BOTTOM -------------------------"]
  ]

def Mem.toStrings (mem : Mem) : List String :=
  fork "MEM" [
    String.chunks 64 <| B8L.toHex mem.data.toList
  ]

def mkSingleton {ξ : Type u} : ξ → List ξ
  | x => [x]

def Log.toStrings (l : Log) : List String :=
  fork "log" [
    [s!"address : {l.address.toHex}"],
    fork "topics" (l.topics.map (mkSingleton ∘ B256.toHex)),
    fork "data" [String.chunks 64 l.data.toHex]
  ]

def Tra.toStrings (tra : Tra) : List String :=
  fork "TRANSIENT STORAGE" <| tra.toList.map <|
    fun kv =>
      fork kv.fst.toHex <| kv.snd.toList.map <|
        mkSingleton ∘ fun kv' => s!"{kv'.fst.toHex} : {B256.toHex kv'.snd}"

def Msg.toStrings (msg : Msg) : List String  :=
  fork "MESSAGE" [
    [s!"caller : {msg.caller.toHex}"],
    [s!"target : {(msg.target.rec "NONE" Adr.toHex : String)}"],
    [s!"current target : {msg.currentTarget.toHex}"],
    [s!"gas : {msg.gas}"],
    [s!"value : {msg.value.toHex}"],
    [s!"data : {msg.data.toHex}"],
    [s!"code address : {(msg.codeAddress.rec "None" Adr.toHex : String)}"],
    fork "CODE" [String.chunks 64 <| B8L.toHex msg.code.toList],
    [s!"depth : {msg.depth}"],
    [s!"should transfer value : {msg.shouldTransferValue}"],
    [s!"is static : {msg.isStatic}"],
    fork "ACCESSED ADDRESSES"
      (msg.accessedAddresses.toList.map (mkSingleton ∘ Adr.toHex)),
    fork "ACCESSED STORAGE KEYS"
      (msg.accessedStorageKeys.toList.map (fun kv => [s!"{kv.fst.toHex} : {B256.toHex kv.snd}"]))
  ]

def Benv.toStrings (benv : Benv) : List String :=
  fork "BLOCK ENVIRONMENT" [
    [s!"CHAIN ID : {benv.chainId}"],
    fork "STATE" [State.toStrings benv.state],
    [s!"BLOCK GAS LIMIT : {benv.blockGasLimit}"],
    fork "BLOCK HASHES" (benv.blockHashes.map (mkSingleton ∘ B256.toHex)),
    [s!"COINBASE : {benv.coinbase}"],
    [s!"BASE FEE PER GAS : {benv.baseFeePerGas}"],
    [s!"TIME : {benv.time.toHex}"],
    [s!"PREVRANDAO : {benv.prevRandao.toHex}"],
    [s!"EXCESS BLOB GAS : {benv.excessBlobGas}"],
    [s!"PARENT BEACON BLOCK ROOT : {benv.parentBeaconBlockRoot.toHex}"]
  ]

def Evm.toStrings (evm : Evm) : List String :=
  fork "EVM" [
    [s!"PC : {evm.pc}"],
    Stack.toStrings evm.stack,
    Mem.toStrings evm.memory,
    [s!"CODE : {B8L.toHex evm.code.toList}"],
    [s!"GAS LEFT : {evm.gas_left}"],
    fork "LOGS" (evm.logs.map Log.toStrings),
    [s!"REFUND COUNTER : {evm.refund_counter}"],
    Msg.toStrings evm.msg,
    [s!"output : {evm.output.toHex}"],
    fork "ACCOUNTS TO DELETE"
      (evm.accountsToDelete.toList.map (mkSingleton ∘ Adr.toHex)),
    [s!"return data : {evm.return_data.toHex}"],
    fork "ACCESSED ADDRESSES"
      (evm.accessedAddresses.toList.map (mkSingleton ∘ Adr.toHex)),
    fork "ACCESSED STORAGE KEYS"
      (evm.accessedStorageKeys.toList.map (fun kv => [s!"{kv.fst.toHex} : {B256.toHex kv.snd}"]))
  ]

abbrev Adr.isPrecomp (a : Adr) : Prop :=
  1 ≤ a.toNat ∧ a.toNat ≤ 17

def safeSub {ξ} [Sub ξ] [LE ξ] [DecidableLE ξ] (x y : ξ) : Option ξ :=
  if y ≤ x then some (x - y) else none

def chargeGas (cost : Nat) (evm : Evm) : Except (Evm × String) Evm := do
  match safeSub evm.gas_left cost with
  | none => .error ⟨evm, "OutOfGasError"⟩
  | some gas => .ok {evm with gas_left := gas}

def B256.toAdr : B256 → Adr
  | ⟨⟨_, x⟩, ⟨y, z⟩⟩ => {high := x.toUInt32, mid := y, low := z}

def Adr.toB256 (a : Adr) : B256 :=
  ⟨⟨0, a.high.toUInt64⟩ , ⟨a.mid, a.low⟩⟩

inductive Ninst : Type
  | reg : Rinst → Ninst
  | exec : Xinst → Ninst
  | push : ∀ bs : B8L, bs.length ≤ 32 → Ninst

-- inductive Ninst : Type
--   | reg : Rinst → Ninst
--   | exec : Xinst → Ninst
--   | push : B256 → Nat → Ninst

def Ninst.toOpString : Ninst → String
  | reg o => Rinst.toString o
  | exec o => Xinst.toString o
  -- | push bs _ => "PUSH0"
  | push bs _ => "PUSH" ++ bs.length.repr

-- def Ninst.toString : Ninst → String
--   | reg o => Rinst.toString o
--   | exec o => Xinst.toString o
--   | push _ 0 => "PUSH0"
--   | push x len => "PUSH" ++ len.repr ++ " 0x" ++ x.toHex.dropZeroes

def Ninst.toString : Ninst → String
  | reg o => Rinst.toString o
  | exec o => Xinst.toString o
  | push [] _ => "PUSH0"
  | push bs _ => "PUSH" ++ bs.length.repr ++ " " ++ B8L.toHex bs

instance : ToString Ninst := ⟨Ninst.toString⟩
instance : Repr Ninst := ⟨λ i _ => i.toString⟩

inductive Inst : Type
  | last : Linst → Inst
  | next : Ninst → Inst
  | jump : Jinst → Inst

def Evm.getInst (evm : Evm) : Option Inst :=
  if evm.pc < evm.code.size
  then
    let b : B8 := evm.code.get! evm.pc
    (b.toRinst <&> (.next ∘ .reg)) <|>
    (b.toXinst <&> (.next ∘ .exec)) <|>
    (b.toJinst <&> .jump) <|>
    (b.toLinst <&> .last) <|>
    (
      let bn := b.toNat
      if h_bn : 95 ≤ bn ∧ bn ≤ 127 then
        let bs : B8L := evm.code.sliceD (evm.pc + 1) (bn - 95) 0
        let h_bs : bs.length ≤ 32 := by
          simp [bs, ByteArray.length_sliceD, h_bn.right]
        some <| .next <| .push bs h_bs
      else
        none
    )
  else
    some (.last .stop)

-- def Evm.getInst (evm : Evm) : Option Inst :=
--   let aux (code : ByteArray) (pc len off : Nat) : B8 :=
--     if off < len
--     then code.get! ((pc + len) - off)
--     else 0
--   if evm.pc < evm.code.size
--   then
--     let b : B8 := evm.code.get! evm.pc
--     (b.toRinst <&> (.next ∘ .reg)) <|>
--     (b.toXinst <&> (.next ∘ .exec)) <|>
--     (b.toJinst <&> .jump) <|>
--     (b.toLinst <&> .last) <|>
--     (
--       let bn := b.toNat
--       if 95 ≤ bn ∧ bn ≤ 127
--       then let len := bn - 95
--            let x : B256 :=
--              B8s.toB256
--                (aux evm.code evm.pc len 31)
--                (aux evm.code evm.pc len 30)
--                (aux evm.code evm.pc len 29)
--                (aux evm.code evm.pc len 28)
--                (aux evm.code evm.pc len 27)
--                (aux evm.code evm.pc len 26)
--                (aux evm.code evm.pc len 25)
--                (aux evm.code evm.pc len 24)
--                (aux evm.code evm.pc len 23)
--                (aux evm.code evm.pc len 22)
--                (aux evm.code evm.pc len 21)
--                (aux evm.code evm.pc len 20)
--                (aux evm.code evm.pc len 19)
--                (aux evm.code evm.pc len 18)
--                (aux evm.code evm.pc len 17)
--                (aux evm.code evm.pc len 16)
--                (aux evm.code evm.pc len 15)
--                (aux evm.code evm.pc len 14)
--                (aux evm.code evm.pc len 13)
--                (aux evm.code evm.pc len 12)
--                (aux evm.code evm.pc len 11)
--                (aux evm.code evm.pc len 10)
--                (aux evm.code evm.pc len  9)
--                (aux evm.code evm.pc len  8)
--                (aux evm.code evm.pc len  7)
--                (aux evm.code evm.pc len  6)
--                (aux evm.code evm.pc len  5)
--                (aux evm.code evm.pc len  4)
--                (aux evm.code evm.pc len  3)
--                (aux evm.code evm.pc len  2)
--                (aux evm.code evm.pc len  1)
--                (aux evm.code evm.pc len  0)
--            some (.next <| .push x len)
--       else none
--     )
--   else
--     some (.last .stop)

def fakeExpAux (num den i : Nat) : Nat → Nat → Nat
  | _, 0 => panic! "error : recursion limit reached for fake exponentiation"
  | 0, _ => 0
  | numAcc, lim + 1 =>
    let numAcc' := (numAcc * num) / (den * i)
    numAcc + fakeExpAux num den (i + 1) numAcc' lim

def fakeExp (fac num den : Nat) : Nat :=
  let lim := (max (fac * num) <| num * num) + 2
  let out := fakeExpAux num den 1 (fac * den) lim
  out / den

def calculate_blob_gas_price (excessBlobGas : Nat) : Nat :=
  fakeExp 1 excessBlobGas blobBaseFeeUpdateFraction

def Evm.push (x : B256) (evm : Evm) : Except (Evm × String) Evm := do
  .assert
    (evm.stack.length < 1024)
    ⟨evm, "StackOverflowError"⟩
  .ok {evm with stack := x :: evm.stack}

def Evm.pop (evm : Evm) : Except (Evm × String) (B256 × Evm) := do
  match evm.stack with
  | [] => .error ⟨evm, "StackUnderflowError"⟩
  | x :: xs => .ok ⟨x, {evm with stack := xs}⟩

-- stackTop & pop' is used because we canno do
--
--   let mut ⟨x, evm⟩ ← evm.pop
--
-- because the new evm must be returned separately for the 'mut' keyword

-- todo : check if using stackTop & pop' actually improves performance
-- for tests involving heavy repetitions of static calls

def Evm.stackTop (evm : Evm) : Except (Evm × String) B256 := do
  match evm.stack with
  | [] => .error ⟨evm, "StackUnderflowError"⟩
  | x :: _ => .ok x

def Evm.pop' (evm : Evm) : Except (Evm × String) Evm := do
  match evm.stack with
  | [] => .error ⟨evm, "StackUnderflowError"⟩
  | _ :: xs => .ok {evm with stack := xs}

def Prod.mapFst {α₁ : Type u₁} {α₂ : Type u₂} {β : Type v} (f : α₁ → α₂) : α₁ × β → α₂ × β :=
  Prod.map f id

def Evm.popToNat (evm : Evm) : Except (Evm × String) (Nat × Evm) :=
  evm.pop <&> Prod.mapFst B256.toNat

def Evm.popN (evm : Evm) : Nat → Except (Evm × String) (List B256 × Evm)
  | 0 => .ok ⟨[], evm⟩
  | n + 1 => do
    let ⟨x, evm⟩ ← evm.pop
    let ⟨xs, evm⟩ ← evm.popN n
    .ok ⟨x :: xs, evm⟩

abbrev Execution : Type := Except (Evm × String) Evm

def Evm.incrPc (evm : Evm) : Execution :=
  .ok {evm with pc := evm.pc + 1}

def pushItem (x : B256) (c : Nat) (evm : Evm) : Execution := do
  chargeGas c evm >>= Evm.push x >>= Evm.incrPc

def access_cost (x : Adr) (a : AdrSet) : Nat :=
  if x ∈ a then gasWarmAccess else gasColdAccountAccess

def addAccessedAddress (evm : Evm) (a : Adr) : Evm :=
  {evm with accessedAddresses := evm.accessedAddresses.insert a}

def addAccessedStorageKey (evm : Evm) (a : Adr) (k : B256) : Evm :=
  {evm with accessedStorageKeys := evm.accessedStorageKeys.insert ⟨a, k⟩}

def add_account_to_delete (evm : Evm) (a : Adr) : Evm :=
  {evm with accountsToDelete := evm.accountsToDelete.insert a}

def add_created_account (benv : Benv) (adr : Adr) : Benv :=
  {benv with createdAccounts := benv.createdAccounts.insert adr}

def Acct.empty : Acct :=
  {
    nonce := 0
    bal := 0
    stor := .empty
    code := ByteArray.mk #[]
  }

def Acct.Erasable (ac : Acct) : Prop :=
  ac.nonce = 0 ∧
  ac.bal = 0 ∧
  ac.stor.isEmpty = .true ∧
  ac.code.size = 0

instance {ac : Acct} : Decidable ac.Erasable := instDecidableAnd

def State.get (w : State) (a : Adr) : Acct := (w.find? a).getD .empty

def State.set (w : State) (a : Adr) (ac : Acct) : State :=
  if ac.Erasable then w.erase a else w.insert a ac

def Acct.Empty (a : Acct) : Prop :=
  a.code.size = 0 ∧ a.nonce = 0 ∧ a.bal = 0

instance {a : Acct} : Decidable a.Empty := by
 apply instDecidableAnd

def destroyAccount (w : State) (a : Adr) : State := w.erase a

abbrev AccountExists (wor : State) (adr : Adr) : Prop :=
  let acct := wor.get adr
  ¬ (acct.Empty ∧ acct.stor.isEmpty)

-- dedicated function for 'destroying touched empty accounts' is
-- not necessary for this implementation, as all functions for
-- modifying world state are designed to immediately destroy any
-- account if it becomes empty as a result of the modification

def Tra.set (τ : Tra) (a : Adr) (s : Stor) : Tra :=
  if s.isEmpty then τ.erase a else τ.insert a s

def State.setCode (ω : State) (a : Adr) (cd : ByteArray) : State :=
  let ac := ω.get a
  ω.set a {ac with code := cd}

def Evm.getOrigAcct (evm : Evm) (a : Adr) : Acct :=
  evm.msg.benv.origState.get a

def Evm.getAcct (evm : Evm) (a : Adr) : Acct :=
  evm.msg.benv.state.get a

-- def Benv.setAcct (benv : Benv) (a : Adr) (ac : Acct) : Benv :=
--   {benv with state := benv.state.set a ac}
--
-- def Msg.setAcct (msg : Msg) (a : Adr) (ac : Acct) : Msg :=
--   {msg with benv := msg.benv.setAcct a ac}
--
-- def Evm.setAcct (evm : Evm) (a : Adr) (ac : Acct) : Evm :=
--   {evm with msg := evm.msg.setAcct a ac}

def Evm.getBal (evm : Evm) (a : Adr) : B256 := (evm.getAcct a).bal
def Evm.getCode (evm : Evm) (a : Adr) : ByteArray := (evm.getAcct a).code
def Evm.getStorVal (evm : Evm) (adr : Adr) (key : B256) : B256 :=
  (evm.getAcct adr).stor.findD key 0

def Stor.set (s : Stor) (k v : B256) : Stor :=
  if v = 0 then s.erase k else s.insert k v

def State.setStorVal (wor : State) (adr : Adr) (key val : B256) : State :=
  let acct : Acct := wor.get adr
  wor.set adr {acct with stor := acct.stor.set key val}

def Benv.setStorVal (benv : Benv) (adr : Adr) (key val : B256) : Benv :=
  {benv with state := benv.state.setStorVal adr key val}

def Msg.setStorVal (msg : Msg) (adr : Adr) (key val : B256) : Msg :=
 {msg with benv := msg.benv.setStorVal adr key val}

def Evm.setStorVal (evm : Evm) (adr : Adr) (key val : B256) : Evm :=
  {evm with msg := evm.msg.setStorVal adr key val}

def Tra.setStorVal (tra : Tra) (adr : Adr) (key val : B256) : Tra :=
  let stor : Stor := tra.findD adr .empty
  tra.set adr <| stor.set key val

def Tenv.setTransVal (tenv : Tenv) (adr : Adr) (key val : B256) : Tenv :=
  {tenv with transientStorage := tenv.transientStorage.setStorVal adr key val}

def Msg.setTransVal (msg : Msg) (adr : Adr) (key val : B256) : Msg :=
  {msg with tenv := msg.tenv.setTransVal adr key val}

def Evm.setTransVal (evm : Evm) (adr : Adr) (key val : B256) : Evm :=
  {evm with msg := evm.msg.setTransVal adr key val}

def Evm.getOrigStorVal (evm : Evm) (adr : Adr) (key : B256) : B256 :=
  (evm.getOrigAcct adr).stor.findD key 0

def Evm.getTransVal (evm : Evm) (adr : Adr) (key : B256) : B256 :=
  (evm.msg.tenv.transientStorage.findD adr .empty).findD key 0

def memExtSize
  (current_size access_index access_size : Nat) : Nat :=
  if access_size = 0
  then current_size
  else
    32 *
    ( max
        (ceilDiv current_size 32)
        (ceilDiv (access_index + access_size) 32) )

def memExtsSize : Nat → List (Nat × Nat) → Nat
  | initSize, [] => initSize
  | initSize, ⟨accessIndex, accessSize⟩ :: pairs =>
    let expSize := memExtSize initSize accessIndex accessSize
    memExtsSize expSize pairs

def Evm.extCost (evm : Evm) (pairs : List (Nat × Nat)) : Nat :=
  let extSize := memExtsSize evm.memory.size pairs
  calculateMemoryGasCost extSize - calculateMemoryGasCost evm.memory.size

def ceil32 (n : Nat) : Nat :=
  match n % 32 with
  | 0 => n
  | m@(_ + 1) => n + 32 - m

def Mem.write (μ : Mem) (n : ℕ) : B8L → Mem
  | [] => μ
  | xs@(_ :: _) =>
    if n + xs.length ≤ μ.size
    then
      if n + xs.length ≤ μ.data.size
      then
        ⟨Array.writeD μ.data n xs, μ.size⟩
      else
        let blank : Array B8 := Array.replicate (n + xs.length) 0x00
        ⟨Array.writeD (Array.copyD μ.data blank) n xs, μ.size⟩

    else
      let newSize := ceil32 (n + xs.length)
      let blank : Array B8 := Array.replicate newSize 0x00
      ⟨Array.writeD (Array.copyD μ.data blank) n xs, newSize⟩

def Mem.extend (μ : Mem) (index size : Nat) : Mem :=
  ⟨μ.data, memExtSize μ.size index size⟩

def Mem.extends (μ : Mem) (pairs : List (Nat × Nat)) : Mem :=
  ⟨μ.data, memExtsSize μ.size pairs⟩

def Mem.read (μ : Mem) (index size : ℕ) : B8L × Mem :=
  ⟨μ.data.sliceD index size 0, μ.extend index size⟩

def Dead (w : State) (a : Adr) : Prop :=
  match w.find? a with
  | none => True
  | some x => x.Empty

def Evm.memWrite (evm : Evm) (idx : Nat) (val : B8L) : Evm :=
  {evm with memory := evm.memory.write idx val}

def Evm.memRead (evm : Evm) (index size : Nat) : B8L × Evm :=
  let ⟨val, mem⟩ := evm.memory.read index size
  ⟨val, {evm with memory := mem}⟩

def Evm.memExtends (evm : Evm) (pairs : List (Nat × Nat)) : Evm :=
  let mem := evm.memory.extends pairs
  {evm with memory := mem}

def Evm.addLog (evm : Evm) (log : Log) : Evm :=
  {evm with logs := evm.logs ++ [log]}

def applyUnary (f : B256 → B256) (cost : Nat) (evm : Evm) : Execution := do
  let ⟨x, evm⟩ ← evm.pop
  pushItem (f x) cost evm

def applyBinary (f : B256 → B256 → B256)
  (cost : Nat) (evm : Evm) : Execution := do
  let ⟨x, evm⟩ ← evm.pop
  let ⟨y, evm⟩ ← evm.pop
  pushItem (f x y) cost evm

def applyTernary (f : B256 → B256 → B256 → B256)
  (cost : Nat) (evm : Evm) : Execution := do
  let ⟨x, evm⟩ ← evm.pop
  let ⟨y, evm⟩ ← evm.pop
  let ⟨z, evm⟩ ← evm.pop
  pushItem (f x y z) cost evm

def List.swap : List ξ → Nat → Option (List ξ)
  | [], _ => none
  | x :: xs, k => do
    let y ← xs[k]?
    let ys := xs.set k x
    .some (y :: ys)

def Evm.contract (evm : Evm) : Adr := evm.msg.currentTarget

def Evm.assertDynamic (evm : Evm) : Except (Evm × String) Unit :=
  Except.assert (!evm.msg.isStatic) ⟨evm, s!"WriteInStaticContext"⟩

def Rinst.run (evm : Evm) : Rinst → Execution
  | .address => pushItem evm.contract.toB256 gBase evm
  | .basefee => pushItem evm.msg.benv.baseFeePerGas.toB256 gBase evm
  | .blobhash => do
    let ⟨x, evm⟩ ← evm.pop
    let y : B256 := evm.msg.tenv.blobVersionedHashes.getD x.toNat 0
    chargeGas gHashopcode evm >>= Evm.push y >>= Evm.incrPc
  | .blobbasefee => do
    let fee := calculate_blob_gas_price evm.msg.benv.excessBlobGas
    pushItem fee.toB256 gBase evm
  | .balance => do
    let ⟨x, evm⟩ ← evm.pop
    let a := x.toAdr
    let evm ←
      if a ∈ evm.accessedAddresses
      then chargeGas gasWarmAccess evm
      else chargeGas gasColdAccountAccess (addAccessedAddress evm a)
    evm.push (evm.getBal a) >>= Evm.incrPc
  | .origin => pushItem evm.msg.tenv.origin.toB256 gBase evm
  | .caller => pushItem evm.msg.caller.toB256 gBase evm
  | .callvalue => pushItem evm.msg.value gBase evm
  | .calldataload => do
    let ⟨start_index, evm⟩ ← evm.pop
    let evm ← chargeGas gVerylow evm
    let value := B8L.toB256P <| evm.msg.data.sliceD start_index.toNat 32 0
    evm.push value >>= Evm.incrPc
  | .calldatasize => pushItem evm.msg.data.length.toB256 gBase evm
  | .calldatacopy => do
    let ⟨memory_start_index, evm⟩ ← evm.popToNat
    let ⟨data_start_index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := gasCopy * words
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) evm
    let value := evm.msg.data.sliceD data_start_index size 0
    let evm := evm.memWrite memory_start_index value
    evm.incrPc
  | .codesize => pushItem evm.msg.code.size.toB256 gBase evm
  | .codecopy => do
    let ⟨memory_start_index, evm⟩ ← evm.popToNat
    let ⟨code_start_index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := gasCopy * words
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) evm
    let value := evm.code.sliceD code_start_index size (Linst.toB8 .stop)
    .ok {
      evm with
      pc := evm.pc + 1
      memory := evm.memory.write memory_start_index value
    }
  | .gasprice => pushItem evm.msg.tenv.gasPrice.toB256 gBase evm
  | .extcodesize => do
    let ⟨address_word, evm⟩ ← evm.pop
    let address := address_word.toAdr
    let evm ←
      if address ∈ evm.accessedAddresses
      then chargeGas gasWarmAccess evm
      else chargeGas gasColdAccountAccess (addAccessedAddress evm address)
    let codesize := (evm.getCode address).size.toB256
    evm.push codesize >>= Evm.incrPc
  | .extcodecopy => do
    let ⟨address_word, evm⟩ ← evm.pop
    let address : Adr := address_word.toAdr
    let ⟨memory_start_index, evm⟩ ← evm.popToNat
    let ⟨code_start_index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := gasCopy * words
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ←
      if address ∈ evm.accessedAddresses
      then chargeGas (gasWarmAccess + copy_gas_cost + extend_memory_cost) evm
      else
        chargeGas
          (gasColdAccountAccess + copy_gas_cost + extend_memory_cost)
          (addAccessedAddress evm address)
    let code := evm.getCode address
    let value := code.sliceD code_start_index size (Linst.toB8 .stop)
    .ok {
      evm with
      pc := evm.pc + 1
      memory := evm.memory.write memory_start_index value
    }
  | .retdatasize => pushItem evm.return_data.length.toB256 gBase evm
  | .retdatacopy => do
    let ⟨memory_start_index, evm⟩ ← evm.popToNat
    let ⟨return_data_start_index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := gReturnDataCopy * words
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) evm

    if (evm.return_data.length < return_data_start_index + size) then
      .error ⟨evm, "OutOfBoundsRead"⟩

    let value :=
      evm.return_data.sliceD return_data_start_index size 0
    .ok {
      evm with
      pc := evm.pc + 1
      memory := evm.memory.write memory_start_index value
    }
  | .extcodehash => do
    let ⟨address_word, evm⟩ ← evm.pop
    let address : Adr := address_word.toAdr
    let evm ←
      if address ∈ evm.accessedAddresses
      then chargeGas gasWarmAccess evm
      else chargeGas gasColdAccountAccess (addAccessedAddress evm address)
    let account := evm.getAcct address
    let codehash : B256 :=
      if account.Empty
      then 0
      else ByteArray.keccak 0 account.code.size account.code
    evm.push codehash >>= Evm.incrPc
  | .selfbalance => pushItem (evm.getBal evm.contract) gLow evm
  | .chainid => pushItem evm.msg.benv.chainId.toB256 gBase evm
  | .number => pushItem evm.msg.benv.number.toB256 gBase evm
  | .timestamp => pushItem evm.msg.benv.time gBase evm
  | .gaslimit => pushItem evm.msg.benv.blockGasLimit.toB256 gBase evm
  | .prevrandao => pushItem evm.msg.benv.prevRandao gBase evm
  | .coinbase => pushItem evm.msg.benv.coinbase.toB256 gBase evm
  | .msize => pushItem evm.memory.size.toB256 gBase evm
  | .mload => do
    let ⟨start_index, evm⟩ ← evm.popToNat
    let extend_memory_cost := evm.extCost [⟨start_index, 32⟩]
    let evm ← chargeGas (gVerylow + extend_memory_cost) evm
    let ⟨value, evm⟩  := evm.memRead start_index 32
    evm.push (B8L.toB256P value) >>= Evm.incrPc
  | .mstore => do
    let start_index ← evm.stackTop <&> B256.toNat
    let mut evm ← evm.pop'
    let value ← evm.stackTop
    evm ← evm.pop'
    let extend_memory_cost := evm.extCost [⟨start_index, 32⟩]
    evm ← chargeGas (gVerylow + extend_memory_cost) evm
    evm := evm.memWrite start_index value.toB8L
    evm.incrPc
  | .mstore8 => do
    let ⟨start_index, evm⟩ ← evm.popToNat
    let ⟨value, evm⟩ ← evm.pop
    let extend_memory_cost := evm.extCost [⟨start_index, 1⟩]
    let evm ← chargeGas (gVerylow + extend_memory_cost) evm
    let evm := evm.memWrite start_index [value.2.2.toUInt8]
    Evm.incrPc evm
  | .gas => do
    let evm ← chargeGas gBase evm
    evm.push evm.gas_left.toB256 >>= Evm.incrPc
  | .eq => applyBinary .eq_check gVerylow evm
  | .lt => applyBinary .lt_check gVerylow evm
  | .gt => applyBinary .gt_check gVerylow evm
  | .slt => applyBinary .slt_check gVerylow evm
  | .sgt => applyBinary .sgt_check gVerylow evm
  | .iszero => applyUnary (.eq_check · 0) gVerylow evm
  | .not => applyUnary (~~~ ·) gVerylow evm
  | .and => applyBinary B256.and gVerylow evm
  | .or => applyBinary B256.or gVerylow evm
  | .xor => applyBinary B256.xor gVerylow evm
  | .signextend => applyBinary B256.signext gLow evm
  | .pop => (evm.pop <&> Prod.snd) >>= chargeGas gBase >>= Evm.incrPc
  | .byte =>
    applyBinary (λ x y => (List.getD y.toB8L x.toNat 0).toB256) gVerylow evm
  | .shl => applyBinary (fun x y => y <<< x.toNat) gVerylow evm
  | .shr => applyBinary (fun x y => y >>> x.toNat) gVerylow evm
  | .sar => applyBinary (fun x y => B256.arithShiftRight y x.toNat) gVerylow evm
  | .kec => do
    let ⟨memory_start_index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let words := ceilDiv size 32
    let word_gas_cost := gasKeccak256Word * words
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ← chargeGas (gKeccak256 + word_gas_cost + extend_memory_cost) evm
    let ⟨arg, evm⟩ := evm.memRead memory_start_index size
    evm.push arg.keccak >>= Evm.incrPc
  | .sub => applyBinary (· - ·) gVerylow evm
  | .mul => applyBinary (· * ·) gLow evm
  | .exp => do
    let ⟨base, evm⟩ ← evm.pop
    let ⟨exponent, evm⟩ ← evm.pop
    let evm ← chargeGas (gExp + (gExpbyte * exponent.bytecount)) evm
    evm.push (B256.bexp base exponent) >>= Evm.incrPc
  | .div => applyBinary (· / ·) gLow evm
  | .sdiv => applyBinary B256.sdiv gLow evm
  | .mod => applyBinary (· % ·) gLow evm
  | .smod => applyBinary B256.smod gLow evm
  | .add => applyBinary (· + ·) gVerylow evm
  | .addmod => applyTernary B256.addmod gMid evm
  | .mulmod => applyTernary B256.mulmod gMid evm
  | .swap n => do
    let evm ← chargeGas gVerylow evm
    match List.swap evm.stack n with
    | none => .error ⟨evm, "StackUnderflowError"⟩
    | some stack =>
      .ok {
        evm with
        pc := evm.pc + 1
        stack := stack
      }
  | .dup n => do
    let evm ← chargeGas gVerylow evm
    match evm.stack[n]? with
    | none => .error ⟨evm, "StackUnderflowError"⟩
    | some word => evm.push word >>= Evm.incrPc
  | .sload => do
    let ⟨key, evm⟩ ← evm.pop
    let ct := evm.contract
    let evm ←
      if ⟨ct, key⟩ ∈ evm.accessedStorageKeys
      then chargeGas gasWarmAccess evm
      else
        chargeGas gasColdSload
          (addAccessedStorageKey evm ct key)
    evm.push (evm.getStorVal ct key) >>= Evm.incrPc
  | .tload => do
    let ⟨key, evm⟩ ← evm.pop
    pushItem (evm.getTransVal evm.contract key) gasWarmAccess evm
  | .pc => pushItem evm.pc.toB256 gBase evm
  | .sstore => do
    let ⟨key, evm⟩ ← evm.pop
    let ⟨new_value, evm⟩ ← evm.pop
    let mut evm : Evm := evm
    .assert
      (gCallStipend < evm.gas_left)
      ⟨evm, "OutOfGasError"⟩
    let ct := evm.contract
    let original_value := evm.getOrigStorVal ct key
    let current_value := evm.getStorVal ct key
    let mut gas_cost := 0
    if ⟨ct, key⟩ ∉ evm.accessedStorageKeys
      then
        evm := addAccessedStorageKey evm ct key
        gas_cost := gas_cost + gasColdSload
    if original_value = current_value ∧ current_value ≠ new_value
      then
        if original_value = 0
        then gas_cost := gas_cost + gasStorageSet
        else gas_cost := gas_cost + (gasStorageUpdate - gasColdSload)
      else gas_cost := gas_cost + gasWarmAccess
    if current_value ≠ new_value
    then
      if original_value ≠ 0 ∧ current_value ≠ 0 ∧ new_value = 0
        then evm := {evm with refund_counter := evm.refund_counter + rSClear}
      if original_value ≠ 0 ∧ current_value = 0
        then evm := {evm with refund_counter := evm.refund_counter - rSClear}
      if original_value = new_value
        then
          if original_value = 0
          then
            evm := {
              evm with
              refund_counter := evm.refund_counter + (gasStorageSet - gasWarmAccess)
            }
          else
            evm := {
              evm with
              refund_counter :=
                evm.refund_counter + (gasStorageUpdate - gasColdSload - gasWarmAccess)
            }
    evm ← chargeGas gas_cost evm
    evm.assertDynamic
    (evm.setStorVal evm.contract key new_value).incrPc
  | .tstore => do
    let ⟨key, evm⟩ ← evm.pop
    let ⟨new_value, evm⟩ ← evm.pop
    let evm ← chargeGas gasWarmAccess evm
    evm.assertDynamic
    (evm.setTransVal evm.contract key new_value).incrPc
  | .mcopy => do
    let ⟨destination, evm⟩ ← evm.popToNat
    let ⟨source, evm⟩ ← evm.popToNat
    let ⟨length, evm⟩ ← evm.popToNat
    let words := ceilDiv length 32
    let copy_gas_cost := gasCopy * words
    let extend_memory_cost :=
      evm.extCost [⟨source, length⟩, ⟨destination, length⟩]
    let evm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) evm
    let ⟨value, evm⟩ := evm.memRead source length
    (evm.memWrite destination value).incrPc
  | .log n => do
    let ⟨memory_start_index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let ⟨topics, evm⟩ ← evm.popN n
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ←
      chargeGas
        (gLog + (gLogdata * size) + (gLogtopic * n) + extend_memory_cost)
        evm
    evm.assertDynamic
    let ⟨data, evm⟩ := evm.memRead memory_start_index size
    let log : Log := ⟨evm.contract, topics, data⟩
    (evm.addLog log).incrPc
  | .blockhash => do
    let ⟨blockNumberWord, evm⟩ ← evm.pop
    let blockNumber := blockNumberWord.toNat
    let evm ← chargeGas gBlockhash evm
    let maxBlockNumber := blockNumber + 256
    let hash : B256 :=
      if evm.msg.benv.number ≤ blockNumber ∨ maxBlockNumber < evm.msg.benv.number
      then 0
      else
        evm.msg.benv.blockHashes.getD
          (evm.msg.benv.blockHashes.length - (evm.msg.benv.number - blockNumber))
          0
    evm.push hash >>= Evm.incrPc

instance : Inhabited Benv := ⟨
  {
    chainId := 0
    state := .empty
    origState := .empty
    createdAccounts := .emptyWithCapacity
    blockGasLimit := 0
    blockHashes := []
    coinbase := 0
    number := 0
    baseFeePerGas := 0
    time := 0
    prevRandao := 0
    excessBlobGas := 0
    parentBeaconBlockRoot := 0
  }
⟩

instance : Inhabited Tenv := ⟨
  {
    origin := 0
    gasPrice := 0
    gas := 0
    accessListAddresses := .emptyWithCapacity
    accessListStorageKeys := .emptyWithCapacity
    transientStorage := .empty
    blobVersionedHashes := []
    auths := []
    indexInBlock := none
    txHash := none
  }
⟩

instance : Inhabited Msg :=
  ⟨
    {
      benv := default
      tenv := default
      caller := 0
      target := .none
      currentTarget := 0
      gas := 0
      value := 0
      data := []
      codeAddress := .none
      code := .empty
      depth := 0
      shouldTransferValue := false
      isStatic := false
      accessedAddresses := .emptyWithCapacity
      accessedStorageKeys := .emptyWithCapacity
      disablePrecompiles := false
    }
  ⟩

instance : Inhabited Evm := ⟨
  {
    pc := 0
    stack := []
    memory := ⟨.empty, 0⟩
    code := .empty
    gas_left := 0
    logs := []
    refund_counter := 0
    msg := default
    output := []
    accountsToDelete := .emptyWithCapacity
    return_data := []
    error := .none
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := .emptyWithCapacity
  }
⟩

instance : Inhabited Execution := ⟨.ok default⟩

def noPushBefore (cd : ByteArray) : Nat → Nat → Bool
  | 0, _ => true
  | _, 0 => true
  | k + 1, m + 1 =>
    if k < cd.size
    then let b := cd.get! k
         if (b < (0x7F - m.toUInt8) || 0x7F < b)
         then noPushBefore cd k m
         else if noPushBefore cd k 32
              then false
              else noPushBefore cd k m
    else noPushBefore cd k m

def jumpable (cd : ByteArray) (k : Nat) : Bool :=
  if cd.get! k = (Jinst.toB8 .jumpdest)
  then noPushBefore cd k 32
  else false

def Jinst.run (evm : Evm) : Jinst → Execution
  | .jumpdest => chargeGas gJumpdest evm >>= Evm.incrPc
  | .jump => do
    let ⟨jump_dest, evm⟩ ← evm.pop
    let evm ← chargeGas gMid evm
    .assert
      (jumpable evm.code jump_dest.toNat)
      ⟨evm, "InvalidJumpDestError"⟩
    .ok {evm with pc := jump_dest.toNat}
  | .jumpi => do
    let ⟨dest, evm⟩ ← evm.pop
    let ⟨cond, evm⟩ ← evm.pop
    let evm ← chargeGas gHigh evm
    let pc ←
      if cond = 0
      then .ok <| evm.pc + 1
      else
        .assert
          (jumpable evm.code dest.toNat)
          ⟨evm, "InvalidJumpDestError"⟩
        .ok dest.toNat
    .ok {evm with pc := pc}

def State.subBal (wor : State) (adr : Adr) (val : B256) : Option State :=
  let acct := wor.get adr
  if acct.bal < val
  then .none
  else wor.set adr {acct with bal := acct.bal - val}

def State.addBal (wor : State) (adr : Adr) (val : B256) : State :=
  let acct := wor.get adr
  wor.set adr {acct with bal := acct.bal + val}

def State.setBal (wor : State) (adr : Adr) (val : B256) : State :=
  let acct := wor.get adr
  wor.set adr {acct with bal := val}

def Benv.setBal (benv : Benv) (adr : Adr) (val : B256) : Benv :=
  {benv with state := benv.state.setBal adr val}

def Benv.subBal (benv : Benv) (adr : Adr) (val : B256) : Option Benv := do
  let wor ← benv.state.subBal adr val
  some {benv with state := wor}

def Benv.addBal (benv : Benv) (adr : Adr) (val : B256) : Benv :=
  {benv with state := benv.state.addBal adr val}

def Msg.setBal (msg : Msg) (adr : Adr) (val : B256) : Msg :=
  {msg with benv := msg.benv.setBal adr val}

def Evm.setBal (evm : Evm) (adr : Adr) (val : B256) : Evm :=
  {evm with msg := evm.msg.setBal adr val}

def Msg.subBal (msg : Msg) (adr : Adr) (val : B256) : Option Msg := do
  let benv ← msg.benv.subBal adr val
  some {msg with benv := benv}

def Evm.subBal (evm : Evm) (adr : Adr) (val : B256) : Option Evm := do
  let msg ← evm.msg.subBal adr val
  some {evm with msg := msg}

def Msg.addBal (msg : Msg) (adr : Adr) (val : B256) : Msg :=
  {msg with benv := msg.benv.addBal adr val}

def Evm.addBal (evm : Evm) (adr : Adr) (val : B256) : Evm :=
  {evm with msg := evm.msg.addBal adr val}

def Linst.run (evm : Evm) : Linst → Execution
  | .stop => .ok {evm with pc := evm.pc + 1}
  | .rev => do
    let ⟨memory_start_index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ← chargeGas extend_memory_cost evm
    let ⟨output, evm⟩ := evm.memRead memory_start_index size
    let evm := {evm with output := output}
    .error ⟨evm, "Revert"⟩
  | .ret => do
    let ⟨index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let cost := evm.extCost [⟨index, size⟩]
    let evm ← chargeGas cost evm
    let ⟨output, evm⟩ := evm.memRead index size
    .ok {evm with output := output}
  | .dest => do
    let donor := evm.contract
    let ⟨donee, evm⟩ ← evm.pop <&> Prod.mapFst B256.toAdr
    let donorBal := (evm.getAcct evm.contract).bal
    let mut gas_cost := gasSelfDestruct
    let mut evm := evm
    if donee ∉ evm.accessedAddresses
      then
        evm := addAccessedAddress evm donee
        gas_cost := gas_cost + gasColdAccountAccess
    if (evm.getAcct donee).Empty ∧ donorBal ≠ 0
      then gas_cost := gas_cost + gasSelfDestructNewAccount
    evm ← chargeGas gas_cost evm
    evm.assertDynamic
    evm ←
      (evm.subBal donor donorBal).toExcept
        ⟨evm, "ERROR : InsufficientBalanceError"⟩
    evm := evm.addBal donee donorBal
    if donor ∈ evm.msg.benv.createdAccounts
      then evm := add_account_to_delete (evm.setBal donor 0) donor
    .ok evm

def except64th (n : Nat) : Nat := n - (n / 64)

def calculate_msg_call_gas
  (value gas gas_left memory_cost extra_gas : Nat)
  (cs : Nat := gCallStipend) : Nat × Nat :=
  let call_stipend : Nat := if value = 0 then 0 else cs
  if gas_left < extra_gas + memory_cost
  then ⟨gas + extra_gas, gas + call_stipend⟩
  else
    let gas' := min gas (except64th (gas_left - memory_cost - extra_gas))
    ⟨gas' + extra_gas, gas' + call_stipend⟩

def incorporateChildOnError (parent child : Evm) (returnData : B8L) : Evm :=
  {
    parent with
    gas_left := parent.gas_left + child.gas_left
    msg := {
      parent.msg with
      benv := child.msg.benv
      tenv := child.msg.tenv
    },
    return_data := returnData
  }

def incorporateChildOnSuccess (parent child : Evm) (returnData : B8L) : Evm :=
  {
    parent with
    gas_left := parent.gas_left + child.gas_left
    msg := {
      parent.msg with
      benv := child.msg.benv
      tenv := child.msg.tenv
    },
    logs := parent.logs ++ child.logs
    -- logs := parent.logs ++ child.logs
    refund_counter := parent.refund_counter + child.refund_counter
    accountsToDelete := parent.accountsToDelete.union child.accountsToDelete
    return_data := returnData
    accessedAddresses := parent.accessedAddresses.union child.accessedAddresses
    accessedStorageKeys := parent.accessedStorageKeys.union child.accessedStorageKeys
  }

def compute_contract_address (sender : Adr) (nonce : B64) : Adr :=
  let LA : B8L :=
    BLT.toB8L <| .list [.b8s sender.toB8L, .b8s nonce.toB8L.sig]
  (B8L.keccak LA).toAdr

def create2NewAddress
  (sender : Adr) (salt : B256) (initCode : B8L): Adr :=
  let LA : B8L :=
    (0xFF : B8) :: (sender.toB8L ++ salt.toB8L ++ initCode.keccak.toB8L)
  (B8L.keccak LA).toAdr

def State.incrNonce (w : State) (a : Adr) : State :=
  let ac := w.get a
  let ac' : Acct := {ac with nonce := ac.nonce + 1}
  w.set a ac'

def Msg.incrNonce (msg : Msg) (adr : Adr) : Msg :=
  {
    msg with
    benv := {
      msg.benv with
      state := msg.benv.state.incrNonce adr
    }
  }

def Evm.incrNonce (evm : Evm) (adr : Adr) : Evm :=
  {evm with msg := evm.msg.incrNonce adr}

def Benv.incrNonce (benv : Benv) (adr : Adr) : Benv :=
  {benv with state := benv.state.incrNonce adr}

def State.setStor (w : State) (a : Adr) (s : Stor) : State :=
  let ac := (w.get a)
  w.set a {ac with stor := s}

def Benv.setStor (benv : Benv) (adr : Adr) (stor : Stor) : Benv :=
  {benv with state := benv.state.setStor adr stor}

-- def Evm.setBenv (evm : Evm) (benv : Benv) : Evm :=
--   {evm with msg := {evm.msg with benv := benv}}
--
-- def Msg.setStor (msg : Msg) (adr : Adr) (stor : Stor) : Msg :=
--   {msg with benv := msg.benv.setStor adr stor}

def Msg.setCode (msg : Msg) (adr : Adr) (code : ByteArray) : Msg :=
  {msg with benv := {msg.benv with state := msg.benv.state.setCode adr code}}

def Evm.setCode (evm : Evm) (adr : Adr) (code : ByteArray) : Evm :=
  {evm with msg := evm.msg.setCode adr code}

def Evm.rollback (evm : Evm) (wor : State) (tra : Tra) : Evm :=
  {
    evm with
    msg := {
      evm.msg with
      benv := {
        evm.msg.benv with
        state := wor
      },
      tenv := {
        evm.msg.tenv with
        transientStorage := tra
      }
    }
  }

def liftToExecution (evm : Evm)
  (f : Except (Benv × Tenv × String) Evm) : Execution := do
  match f with
  | .error ⟨benv, tenv, ex⟩ =>
    let evm' := {
      evm with
      msg := {
        evm.msg with
        benv := benv
        tenv := tenv
      }
    }
    .error ⟨evm', ex⟩
  | .ok evm => .ok evm

def executeEcrecover (evm : Evm) : Execution := do
  let data := evm.msg.data
  let evm ← chargeGas gasEcrecover evm
  let h := B8L.toB256P <| data.sliceD 0 32 (0x00 : B8)
  let (some v : Option Bool) ←
    .ok
      ( match (B8L.toB256P <| data.sliceD 32 32 (0x00 : B8)) with
        | 0x1B => some false
        | 0x1C => some true
        | _ => .none ) | .ok evm
  let r := B8L.toB256P <| data.sliceD 64 32 (0x00 : B8)
  let s := B8L.toB256P <| data.sliceD 96 32 (0x00 : B8)
  if r = 0 ∨ s = 0 ∨
     r ≥ secp256k1.curveOrder.toB256 ∨
     s ≥ secp256k1.curveOrder.toB256 then
    .ok evm
  else
    match secp256k1.recover h v r s with
    | .none => .ok evm
    | some adr => .ok {evm with output := adr.toB256.toB8L}

def executeSha256 (evm : Evm) : Execution := do
  let data := evm.msg.data
  let cost : Nat := 60 + (12 * (ceilDiv data.length 32))
  let mut evm ← chargeGas cost evm
  .ok {evm with output := (B8L.sha256 data).toB8L}

def executeRipemd160 (evm : Evm) : Execution := do
  let data : B8L := evm.msg.data
  let cost : Nat := 600 + (120 * (ceilDiv data.length 32))
  let evm ← chargeGas cost evm
  let hash : B8L := data.ripemd160
  let output : B8L := B256.toB8L <| (B8L.toB256P <| hash)
  .ok {evm with output := output}

def executeId (evm : Evm) : Execution := do
  let data := evm.msg.data
  let cost := 15 + (3 * (ceilDiv data.length 32))
  let evm ← chargeGas cost evm
  .ok {evm with output := data}

def B8L.sliceToNat (data : B8L) (start : Nat) (length : Nat) : Nat :=
  match data.drop start with
  | [] => 0
  | tail@(_ :: _)=>
    if tail.length < length
    then
      if tail.all (· = 0)
      then 0
      else B8L.toNat <| tail.takeD length (0 : B8)
    else B8L.toNat <| tail.take length

-- def complexity
def modexpComplexity
  (baseLength modulusLength : Nat) : Nat :=
  let maxLength := max baseLength modulusLength
  let words := ceilDiv maxLength 8
  words ^ 2

-- def iterations
def modexpIterations (expLength : Nat) (expHead : Nat) : Nat :=
  let bitsPart : Nat := (Nat.log2 expHead)
  let count :=
    if expLength ≤ 32
    then
      if expHead = 0
      then 0
      else
        bitsPart
    else
      let lengthPart := 8 * (expLength - 32)
      lengthPart + bitsPart

  max count 1

-- def gas_cost
def modexpGascost
  (baseLength modulusLength expLength expHead : Nat) : Nat :=
  let mulComplexity := modexpComplexity baseLength modulusLength
  let iterationCount := modexpIterations expLength expHead
  let cost := (mulComplexity * iterationCount) / 3
  max 200 cost

def executeModexp (evm : Evm) : Execution := do
  let data := evm.msg.data
  let baseLength : Nat := B8L.sliceToNat data 0 32
  let expLength : Nat := B8L.sliceToNat data 32 32
  let modulusLength : Nat := B8L.sliceToNat data 64 32
  let expHead : Nat := B8L.sliceToNat data (96 + baseLength) (min 32 expLength)
  let cost : Nat := modexpGascost baseLength modulusLength expLength expHead
  let evm ← chargeGas cost evm
  if baseLength = 0 ∧ modulusLength = 0
    then return {evm with output := []}
  let base : Nat := B8L.sliceToNat data 96 baseLength
  let exp : Nat := B8L.sliceToNat data (96 + baseLength) expLength
  let modulus : Nat := B8L.sliceToNat data (96 + baseLength + expLength) modulusLength
  let output :=
    if modulus = 0
    then List.replicate modulusLength (0x00 : B8)
    else (Nat.powMod base exp modulus).toB8L.pack modulusLength
  .ok {evm with output := output}

def executeEcadd (evm : Evm) : Execution := do
  let data := evm.msg.data
  let evm ← chargeGas 150 evm
  let x0 : Nat := B8L.toNat <| data.sliceD 0 32 (0 : B8)
  let y0 : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
  let x1 : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)
  let y1 : Nat := B8L.toNat <| data.sliceD 96 32 (0 : B8)

  .assert
    ( x0 < altBn128Prime ∧ y0 < altBn128Prime ∧
      x1 < altBn128Prime ∧ x1 < altBn128Prime )
    ⟨evm, "OutOfGasError"⟩

  let p0 ← (BNP.mk? x0 y0).toExcept ⟨evm, "OutOfGasError"⟩
  let p1 ← (BNP.mk? x1 y1).toExcept ⟨evm, "OutOfGasError"⟩

  .ok {evm with output := BNP.toB8L (p0 + p1)}

def executeEcmul (evm : Evm) : Execution := do
  let data := evm.msg.data
  let evm ← chargeGas 6000 evm
  let x : Nat := B8L.toNat <| data.sliceD 0 32 (0 : B8)
  let y : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
  let n : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)

  .assert
    (x < altBn128Prime ∧ y < altBn128Prime)
    ⟨evm, "OutOfGasError"⟩
  let p ← (BNP.mk? x y).toExcept ⟨evm, "OutOfGasError"⟩

  .ok {evm with output := BNP.toB8L (p * n)}

-- structure Blake2 : Type where
--   w: B64
--   mask_bits: B64
--   -- word_format: String
--   R1: B64
--   R2: B64
--   R3: B64
--   R4: B64
--
-- def blake2b : Blake2 :=
--   {
--     w := 64,
--     mask_bits := 0xFFFFFFFFFFFFFFFF
--     -- word_format := "Q",
--     R1 := 32,
--     R2 := 24,
--     R3 := 16,
--     R4 := 63
--   }

def b2R1 : B64 := 32
def b2R2 : B64 := 24
def b2R3 : B64 := 16
def b2R4 : B64 := 63
def b2MaskBits : B64 := 0xFFFFFFFFFFFFFFFF

def blake2IV : List B64 :=
  [
    0x6A09E667F3BCC908,
    0xBB67AE8584CAA73B,
    0x3C6EF372FE94F82B,
    0xA54FF53A5F1D36F1,
    0x510E527FADE682D1,
    0x9B05688C2B3E6C1F,
    0x1F83D9ABFB41BD6B,
    0x5BE0CD19137E2179
  ]

def blake2MixTable : Array (Array Nat) :=
  #[
    #[0, 4, 8, 12],
    #[1, 5, 9, 13],
    #[2, 6, 10, 14],
    #[3, 7, 11, 15],
    #[0, 5, 10, 15],
    #[1, 6, 11, 12],
    #[2, 7, 8, 13],
    #[3, 4, 9, 14]
  ]

def blake2Sigma : Array (Array Nat) :=
  #[
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]
  ]

-- def spit_le_to_uint
def spit_le_to_B64 (data: B8L) : Nat → Nat → List B64
  | _, 0 => []
  | start, num_words + 1 =>
    let wordBytes := data.sliceD start 8 (0x00 : B8)
    let word := B8L.toB64P wordBytes.reverse
    word :: spit_le_to_B64 data (start + 8) num_words

-- def get_blake2_parameters
def getBlake2Parameters (data : B8L) :
  Nat × List B64 × List B64 × B64 × B64 × Nat :=
  let rounds := B8L.sliceToNat data 0 4
  let h := spit_le_to_B64 data 4 8
  let m := spit_le_to_B64 data 68 16
  let t := spit_le_to_B64 data 196 2
  let f := B8L.toNat <| data.drop 212
  ⟨rounds, h, m, t.getD 0 0, t.getD 1 0, f⟩

def b2wR1 : B64 := 32
def b2wR2 : B64 := 40
def b2wR3 : B64 := 48
def b2wR4 : B64 := 1

-- def G
def Blake2.g (v : Array B64) (a b c d : Nat) (x y : B64) : Array B64 :=
  let na : B64 := ((v[a]!) + (v[b]!) + x)
  let v := v.set! a na
  let shiftArg : B64 := (v[d]! ^^^ na)
  let nd : B64 := ((shiftArg >>> b2R1) ^^^ (shiftArg <<< b2wR1)) -- % b2.maxWord
  let v := v.set! d nd
  let nc := (v[c]! + nd) -- % b2.maxWord
  let v := v.set! c nc
  let shiftArg : B64 := (v[b]! ^^^ v[c]!)
  let nb := ((shiftArg >>> b2R2) ^^^ (shiftArg <<< b2wR2)) -- % b2maxWord
  let v := v.set! b nb
  let na := (v[a]! + nb + y) -- % b2maxWord
  let v := v.set! a na
  let shiftArg : B64 := (v[d]! ^^^ v[a]!)
  let nd := ((shiftArg >>> b2R3) ^^^ (shiftArg <<< b2wR3)) -- % b2maxWord
  let v := v.set! d nd
  let nc := (v[c]! + nd) -- % b2maxWord
  let v := v.set! c nc
  let shiftArg : B64 := (v[b]! ^^^ nc)
  let v := v.set! b <| ((shiftArg >>> b2R4) ^^^ (shiftArg <<< b2wR4)) -- % b2.maxWord
  v

def traceId {ξ : Type} (msg : String) (x : ξ) :=
  dbg_trace msg ; x

def iterRangeTrace (max : Nat) {ξ : Type} (k : Nat) (f : Nat → ξ → ξ) (x : ξ) : ξ :=
  let rec aux : Nat → Nat → ξ → ξ
    | _, 0, x => x
    | m, n + 1, x =>
      let i := m - (n + 1)
      let x' := traceId s!"{i} / {max}" (f i x)
      aux m n x' --<| f i x
  aux k k x

def iterRange {ξ : Type} (k : Nat) (f : Nat → ξ → ξ) (x : ξ) : ξ :=
  let rec aux : Nat → Nat → ξ → ξ
    | _, 0, x => x
    | m, n + 1, x =>
      let i := m - (n + 1)
      aux m n <| f i x
  aux k k x


-- compress
def bCompress (numRounds : Nat)
  (h m : List B64) (t0 t1 : B64) (f : Bool) : Option B8L := do
  let v14 : B64 := blake2IV.getD 6 0
  let v : List B64 :=
    h.take 8 ++
    (blake2IV).take 4 ++ [
      .xor t0 (blake2IV.getD 4 0),
      .xor t1 (blake2IV.getD 5 0),
      if f then .xor v14 b2MaskBits else v14,
      (blake2IV.getD 7 0),
      0
    ]

  let innerFun (s : Array Nat) (i : Nat) (v : Array B64) : Array B64 :=
    Blake2.g v
      ((blake2MixTable[i]!)[0]!)
      ((blake2MixTable[i]!)[1]!)
      ((blake2MixTable[i]!)[2]!)
      ((blake2MixTable[i]!)[3]!)
      m[s[i * 2]!]!
      m[s[(i * 2) + 1]!]!

  let outerFun (r : Nat) (v : Array B64) : Array B64 :=
    let s : Array Nat := blake2Sigma[r % blake2Sigma.size]!
    iterRange 8 (innerFun s) v

  let arr := iterRangeTrace numRounds numRounds outerFun ⟨v⟩
  let v := arr.toList
  let resultMsgWords :=
    (List.range 8).map <| fun i => h[i]! ^^^ v[i]! ^^^ v[(i + 8)]!
  List.flatten <| resultMsgWords.map (fun n => n.toB8L.reverse.takeD 8 (0x00 : B8))

-- blake2f
def executeBlake2F (evm : Evm) : Execution := do
  let data := evm.msg.data
  .assert (data.length = 213) ⟨evm, "InvalidParameter"⟩
  let ⟨rounds, h, m, t0, t1, fn⟩ := getBlake2Parameters data
  let evm ← chargeGas (gasBlake2PerRound * rounds) evm
  let f ←
    match fn with
    | 0 => .ok false
    | 1 => .ok true
    | _ => .error ⟨evm, "InvalidParameter"⟩
  let output ← (bCompress rounds h m t0 t1 f).toExcept ⟨evm, "bCompress failed"⟩
  .ok {evm with output := output}

def executePointEval (evm : Evm) : Execution := do
  let data := evm.msg.data
  .assert (data.length = 192) ⟨evm, "KZGProofError"⟩
  .error ⟨evm, "UNIMP : executePointEval"⟩

def gasBlsG1Mul : Nat := 12000
def gasBlsG1Map : Nat := 5500
def gasBlsG2Add : Nat := 600
def gasBlsG2Mul : Nat := 22500
def gasBlsG2Map : Nat := 23800

-- bls12_g1_add
def executeBls12G1Add (evm : Evm) : Execution := do
  let data := evm.msg.data
  .assert (data.length = 256) ⟨evm, "InvalidParameter"⟩
  .error ⟨evm, "BLS12 G1 Add not implemented yet"⟩

-- bls12_g1_msm
def executeBls12G1Msm (evm : Evm) : Execution := do
  let data := evm.msg.data
  if data.length = 0 ∨ data.length % lengthPerPair ≠ 0 then
    .error ⟨evm, s!"InvalidParameter : {data.length} is not a valid input lnegth"⟩
  let k := data.length / lengthPerPair
  let discount :=
    List.getD g1KDiscount (k - 1) g1MaxDiscount
  let gasCost := (k * gasBlsG1Mul * discount) / 1000
  let mut evm ← chargeGas gasCost evm
  .error ⟨evm, "BLS12 G1 msm not implemented yet"⟩

-- bls12_g2_add
def executeBls12G2Add (evm : Evm) : Execution := do
  let data := evm.msg.data
  if data.length ≠ 512 then
    .error ⟨evm, "InvalidParameter"⟩
  let mut evm ← chargeGas gasBlsG2Add evm
  .error ⟨evm, "BLS12 G2 add not implemented yet"⟩

-- def bls12_g2_msm
def executeBls12G2Msm (evm : Evm) : Execution := do
  let data := evm.msg.data
  if data.length = 0 ∨ data.length % lengthPerPair ≠ 0 then
    .error ⟨evm, s!"InvalidParameter : {data.length} is not a valid input lnegth"⟩
  let k := data.length / lengthPerPair
  let discount :=
    List.getD g2KDiscount (k - 1) g2MaxDiscount
  let gasCost := (k * gasBlsG2Mul * discount) / 1000
  let mut evm ← chargeGas gasCost evm
  .error ⟨evm, "BLS12 G2 msm not implemented yet"⟩

-- def bls12_pairing(evm: Evm) -> None:
def executeBls12Pairing (evm : Evm) : Execution := do
  let data := evm.msg.data
  if data.length = 0 ∨ data.length % 384 ≠ 0 then
    .error ⟨evm, s!"InvalidParameter : {data.length} is not a valid input lnegth"⟩
  let k := data.length / 384
  let gasCost := (32600 * k + 37700)
  let mut evm ← chargeGas gasCost evm
  .error ⟨evm, "BLS12 pairing not implemented yet"⟩

-- def bls12_map_fp_to_g1(evm: Evm) -> None:
def executeBls12MapFpToG1 (evm : Evm) : Execution := do
  let data := evm.msg.data
  if data.length ≠ 64 then
    .error ⟨evm, "InvalidParameter"⟩
  let mut evm ← chargeGas gasBlsG1Map evm
  .error ⟨evm, "BLS12 map FP-to-G1 Msm not implemented yet"⟩

def catchWithOOG {ξ : Type U} (evm : Evm) (cond : String → Bool) :
  Except String ξ → Except (Evm × String) ξ
  | .ok v => .ok v
  | .error e =>
    if cond e then
      .error ⟨evm, "OutOfGasError"⟩
    else
      .error ⟨evm, e⟩

-- def bytes_to_g1(data: Bytes) -> Point3D[FQ]:
def B8L.toExStrBNP (data : B8L) : Except String BNP := do
  if data.length ≠ 64 then
    .error "InvalidParameter : input should be 64 bytes long"
  let x := data.sliceToNat 0 32
  let y := data.sliceToNat 32 32
  if x >= altBn128Prime then
    .error "InvalidParameter : invalid field element"
  if y >= altBn128Prime then
    .error "InvalidParameter : invalid field element"
  (EllipticCurve.mk? (FinField.ofNat x) (FinField.ofNat y)).toExcept
    "InvalidParameter : point is not on curve"

-- def bytes_to_g2(data: Bytes) -> Point3D[FQ2]:
def B8L.toExStrBNP2 (data : B8L) : Except String BNP2 := do
  if data.length ≠ 128 then
    .error "InvalidParameter : input should be 128 bytes long"
  let x0 := data.sliceToNat 0 32
  let x1 := data.sliceToNat 32 32
  let y0 := data.sliceToNat 64 32
  let y1 := data.sliceToNat 96 32
  if (
    x0 ≥ altBn128Prime ∨
    x1 ≥ altBn128Prime ∨
    y0 ≥ altBn128Prime ∨
    y1 ≥ altBn128Prime
  ) then
    .error "InvalidParameter : invalid field element"
  (EllipticCurve.mk? (BNF2.mk x0 x1) (BNF2.mk y0 y1)).toExcept
    "InvalidParameter : point is not on curve"

-- def bls12_map_fp2_to_g2(evm: Evm) -> None:
def executeBls12MapFp2ToG2 (evm : Evm) : Execution := do
  let data := evm.msg.data
  .assert (data.length = 128) ⟨evm, "InvalidParameter"⟩
  let mut evm ← chargeGas gasBlsG2Map evm
  .error ⟨evm, "main logic of BLS12 map FP2-to_G2 not implemented yet"⟩

def executePairingCheck (evm : Evm) : Execution := do
  let data := evm.msg.data
  let evm ← chargeGas ((34000 * (data.length / 192)) + 45000) evm
  .assert (data.length % 192 = 0) ⟨evm, "OutOfGasError"⟩
  let mut result : BNF12 := 1
  for i in List.range (data.length / 192) do
    let p : BNP ←
      catchWithOOG evm (hasErrorType · "InvalidParameter") <|
        B8L.toExStrBNP (data.slice! (i * 192) 64)
    let q : BNP2 ←
      catchWithOOG evm (hasErrorType · "InvalidParameter") <|
        B8L.toExStrBNP2 (data.slice! (i * 192 + 64) 128)
    .assert (p * altBn128CurveOrder = ⟨0, 0⟩) ⟨evm, "OutOfGasError"⟩
    .assert (q * altBn128CurveOrder = ⟨0, 0⟩) ⟨evm, "OutOfGasError"⟩
    let pairResult ← (pairing q p).toExcept ⟨evm, "ValueError"⟩
    result := result * pairResult
  let output : B8L :=
    if result = 1
    then (1 : Nat).toB256.toB8L
    else (0 : Nat).toB256.toB8L
  .ok {evm with output := output}

def executePrecomp (evm : Evm) : Adr → Execution
  | 0x1 => executeEcrecover evm
  | 0x2 => executeSha256 evm
  | 0x3 => executeRipemd160 evm
  | 0x4 => executeId evm
  | 0x5 => executeModexp evm
  | 0x6 => executeEcadd evm
  | 0x7 => executeEcmul evm
  | 0x8 => executePairingCheck evm
  | 0x9 => executeBlake2F evm
  | 0xA => executePointEval evm
  | 0xB => executeBls12G1Add evm
  | 0xC => executeBls12G1Msm evm
  | 0xD => executeBls12G2Add evm
  | 0xE => executeBls12G2Msm evm
  | 0xF => executeBls12Pairing evm
  | 0x10 => executeBls12MapFpToG1 evm
  | 0x11 => executeBls12MapFp2ToG2 evm
  | n => .error ⟨evm, s!"ERROR : precompiled contract {n} does not exist"⟩

def Inst.toOpString : Inst → String
  | .next n => n.toOpString
  | .jump j => j.toString
  | .last l => l.toString

def Inst.toString : Inst → String
  | .next n => n.toString
  | .jump j => j.toString
  | .last l => l.toString

def State.getStor (w : State) (a : Adr) : Stor := (w.get a).stor
def State.getNonce (w : State) (a : Adr) : B64 := (w.get a).nonce
def State.getCode (w : State) (a : Adr) : ByteArray := (w.get a).code

instance : ToString Log := ⟨String.joinln ∘ Log.toStrings⟩

def List.toStringSingleQuote {ξ : Type u} [inst : ToString ξ] : List ξ → String
  | [] => "[]"
  | [x] => "['" ++ toString x ++ "']"
  | x::xs => xs.foldl (· ++ ", '" ++ toString · ++ "'") ("['" ++ toString x ++ "'") |>.push ']'

def stepString (evm : Evm) (i : Inst) : String :=
  "step(" ++
    s!"pc({evm.pc}), " ++
    s!"gas({evm.gas_left}), " ++
    s!"op(\"{i.toOpString}\"), " ++
    s!"depth({evm.msg.depth}), " ++
    s!"{List.toStringSingleQuote <| evm.stack.map (fun x => "0x" ++ x.toHex.dropZeroes)}" ++
  ")."

def showStep (vb : Bool) (evm : Evm) (i : Inst) : Except (Evm × String) Unit :=
  if vb
  then do
    .print (stepString evm i)
    .ok ()
  else .ok ()

def showLim (lim : Nat) (evm : Evm) : Except (EVM × String) Unit := do
  if lim % 100000 = 0 then
    .print s!"Recursion limit = {lim}, gas left = {evm.gas_left}"

def isValidDelegation (code: ByteArray) : Prop :=
  code.size = eoaDelegatedCodeLength ∧
  code.sliceD 0 3 (0 : B8) = eoaDelegationMarker

instance {code} : Decidable (isValidDelegation code) := instDecidableAnd

-- get_delegated_code_address
def getDelegatedCodeAddress (code : ByteArray) : Option Adr :=
  if isValidDelegation code
  then
    let adrBytes := code.sliceD eoaDelegationMarker.length 20 (0 : B8)
    adrBytes.toAdr?
  else none

instance : Inhabited Adr := ⟨0⟩

-- access_delegation
def accessDelegation (evm : Evm) (adr : Adr) :
  Bool × Adr × ByteArray × Nat × Evm :=
  let state := evm.msg.benv.state
  let code := state.getCode adr
  if isValidDelegation code
  then
    let adr :=
      (code.sliceD eoaDelegationMarker.length 20 (0 : B8)).toAdr?.get!
    let accessGasCost := access_cost adr evm.accessedAddresses
    let evm := addAccessedAddress evm adr
    let code := state.getCode adr
    ⟨true, adr, code, accessGasCost, evm⟩
  else ⟨false, adr, code, 0, evm⟩

mutual

  def executeCode (vb : Bool) (msg : Msg) :
    Nat → Except (Benv × Tenv × String) Evm
    | 0 => .error ⟨msg.benv, msg.tenv, "RecursionLimit"⟩
    | lim + 1 => do
      let evm : Evm := {
        pc := 0
        stack := []
        memory := .empty
        code := msg.code
        gas_left := msg.gas
        logs := []
        refund_counter := 0
        msg := msg
        output := []
        accountsToDelete := .emptyWithCapacity
        return_data := []
        error := .none
        accessedAddresses := msg.accessedAddresses
        accessedStorageKeys := msg.accessedStorageKeys
      }
      let isPrecomp : Bool :=
        match msg.codeAddress with
        | .none => false
        | .some adr => adr.isPrecomp
      let result : Execution :=
        if isPrecomp
        then
          executePrecomp evm (msg.codeAddress.getD 0)
        else exec vb lim evm
      match result with
      | .ok evm => .ok evm
      | .error ⟨evm, err⟩ =>
        if isExceptionalHalt err
        then .ok {evm with gas_left := 0, output := [], error := some err}
        else
          if err = "Revert"
          then .ok {evm with error := some "Revert"}
          else .error ⟨evm.msg.benv, evm.msg.tenv, err⟩
  termination_by lim => lim

  def processMsg (vb : Bool) (msg : Msg) :
    Nat → Except (Benv × Tenv × String) Evm
    | 0 => .error ⟨msg.benv, msg.tenv, "RecursionLimit"⟩
    | lim + 1 => do
      .assert
        (msg.depth ≤ 1024)
        ⟨msg.benv, msg.tenv, "StackDepthLimitError"⟩
      let benv ←
        if msg.shouldTransferValue
        then
          let benv ←
            (msg.benv.subBal msg.caller msg.value).toExcept
              ⟨msg.benv, msg.tenv, "AssertionError"⟩
          .ok <| benv.addBal msg.currentTarget msg.value
        else .ok msg.benv
      let mut evm ← executeCode vb {msg with benv := benv} lim
      if evm.error.isSome
        then evm := evm.rollback msg.benv.state msg.tenv.transientStorage
      .ok evm
  termination_by lim => lim

  def processCreateMessage (vb : Bool) (msg : Msg) :
    Nat → Except (Benv × Tenv × String) Evm
    | 0 => .error ⟨msg.benv, msg.tenv, "RecursionLimit"⟩
    | lim + 1 => do
      let init_state := msg.benv.state
      let init_tra := msg.tenv.transientStorage
      let adr := msg.currentTarget
      let mut benv := msg.benv.setStor adr .empty
      benv := add_created_account benv adr
      benv := benv.incrNonce adr
      let evm ← processMsg vb {msg with benv := benv} lim
      if evm.error.isNone
      then
        let contractCode := evm.output
        let contractCodeGas := contractCode.length * gasCodeDeposit
        let result : Execution :=
          match contractCode with
          | 0xEF :: _ => .error ⟨evm, "InvalidContractPrefix"⟩
          | _ => do
            let evm ← chargeGas contractCodeGas evm
            if maxCodeSize < contractCode.length
            then .error ⟨evm, "OutOfGasError"⟩
            else .ok evm
        match result with
        | .ok evm => .ok <| evm.setCode adr <| .mk <| .mk contractCode
        | .error (evm, err) =>
          if isExceptionalHalt err
          then
            let evm := evm.rollback init_state init_tra
            .ok {evm with gas_left := 0, output := [], error := .some err}
          else .error ⟨evm.msg.benv, evm.msg.tenv, err⟩
      else .ok <| evm.rollback init_state init_tra
  termination_by lim => lim

  def genericCreate
    (vb : Bool)
    (evm : Evm)
    (endowment : B256)
    (newAddress : Adr)
    (memoryIndex : Nat)
    (memorySize : Nat) : Nat → Execution
    | 0 => .error ⟨evm, "RecursionLimit"⟩
    | lim + 1 => do
      let calldata := evm.memory.data.sliceD memoryIndex memorySize 0
      .assert
        (memorySize ≤ maxInitcodeSize)
        ⟨evm, "OutOfGasError"⟩
      let mut evm := addAccessedAddress evm newAddress
      let createMsgGas := except64th evm.gas_left
      evm := {evm with gas_left := evm.gas_left - createMsgGas}
      evm.assertDynamic
      evm := {evm with return_data := []}
      let sender := evm.msg.benv.state.get evm.contract
      let .false ←
        .ok (
          (
            sender.bal < endowment ∨
            sender.nonce = B64.max ∨
            evm.msg.depth + 1 > 1024
          ) : Bool
        ) | ({evm with gas_left := evm.gas_left + createMsgGas}.push 0)
      evm := evm.incrNonce evm.contract
      let .false ←
        .ok (
          let target := evm.msg.benv.state.get newAddress
          (
            target.nonce ≠ (0 : B64) ∨
            target.code.size ≠ 0 ∨
            target.stor.size ≠ 0
          ) : Bool
        ) | evm.push 0
      let childMsg : Msg := {
        benv := evm.msg.benv
        tenv := evm.msg.tenv
        caller := evm.contract
        target := .none
        gas := createMsgGas
        value := endowment
        data := []
        code := .mk <| .mk calldata
        currentTarget := newAddress
        depth := evm.msg.depth + 1
        codeAddress := .none
        shouldTransferValue := true
        isStatic := false
        accessedAddresses := evm.accessedAddresses
        accessedStorageKeys := evm.accessedStorageKeys
        disablePrecompiles := false
      }
      let child ← liftToExecution evm <| processCreateMessage vb childMsg lim
      if child.error.isSome
      then (incorporateChildOnError evm child child.output).push 0
      else (incorporateChildOnSuccess evm child []).push child.contract.toB256
  termination_by lim => lim

  def generic_call
    (vb : Bool)
    (evm: Evm)
    (gas: Nat)
    (value: B256)
    (caller: Adr)
    (target: Adr)
    (codeAddress: Adr)
    (shouldTransferValue: Bool)
    (isStaticcall: Bool)
    (input_index:  Nat)
    (input_size:   Nat)
    (output_index: Nat)
    (output_size:  Nat)
    (code : ByteArray)
    (disablePrecompiles: Bool) : Nat → Execution
    | 0 => .error ⟨evm, "RecursionLimit"⟩
    | lim + 1 => do
      let mut evm := {evm with return_data := []}
      let .false ← .ok ((evm.msg.depth + 1 > 1024) : Bool)
        | ({evm with gas_left := evm.gas_left + gas}).push 0
      let calldata := evm.memory.data.sliceD input_index input_size 0
      let childMsg : Msg := {
        benv := evm.msg.benv
        tenv := evm.msg.tenv
        caller := caller
        target := target
        gas := gas
        currentTarget := target
        value := value
        data := calldata
        codeAddress := codeAddress
        code := code
        depth := evm.msg.depth + 1
        shouldTransferValue := shouldTransferValue
        isStatic := isStaticcall || evm.msg.isStatic
        accessedAddresses := evm.accessedAddresses
        accessedStorageKeys := evm.accessedStorageKeys
        disablePrecompiles := disablePrecompiles
      }
      let child ← liftToExecution evm <| processMsg vb childMsg lim
      evm ←
        if child.error.isSome
        then (incorporateChildOnError evm child child.output).push 0
        else (incorporateChildOnSuccess evm child child.output).push 1
      let actualOutput := child.output.take output_size
      evm := evm.memWrite output_index actualOutput
      .ok evm
  termination_by lim => lim

  def Ninst.run (vb : Bool) (evm : Evm) : Ninst → Nat → Execution
    | .push xs _, _ => do
      let evm ← chargeGas (if xs.length = 0 then gBase else gVerylow) evm
      let evm ← evm.push xs.toB256P
      .ok {evm with pc := evm.pc + xs.length + 1}
    --| .push x len, _ => do
    --  let evm ← chargeGas (if len = 0 then gBase else gVerylow) evm
    --  let evm ← evm.push x
    --  .ok {evm with pc := evm.pc + len + 1}
    | .reg r, _ => r.run evm
    | .exec _, 0 => .error ⟨evm, "RecursionLimit"⟩
    | .exec .create, lim + 1 => do
      let ⟨endowment, evm⟩ ← evm.pop
      let ⟨memory_index, evm⟩ ← evm.popToNat
      let ⟨memory_size, evm⟩ ← evm.popToNat
      let extend_cost := evm.extCost [⟨memory_index, memory_size⟩]
      let initCodeCost := gasInitCodeWordCost * (ceilDiv memory_size 32)
      let evm ← chargeGas (gasCreate + extend_cost + initCodeCost) evm
      let evm := evm.memExtends [⟨memory_index, memory_size⟩]
      let newAddress :=
        compute_contract_address
          evm.contract
          (evm.msg.benv.state.get evm.contract).nonce
      let evm ←
        genericCreate
          vb
          evm
          endowment
          newAddress
          memory_index
          memory_size
          lim
      evm.incrPc
    | .exec .create2, lim + 1 => do
      let ⟨endowment, evm⟩ ← evm.pop
      let ⟨memory_index, evm⟩ ← evm.popToNat
      let ⟨memory_size, evm⟩ ← evm.popToNat
      let ⟨salt, evm⟩ ← evm.pop
      let extend_cost := evm.extCost [⟨memory_index, memory_size⟩]
      let initCodeHashCost :=
        gasKeccak256Word * ceilDiv memory_size 32
      let initCodeCost :=
        gasInitCodeWordCost * (ceilDiv memory_size 32)
      let evm ←
        chargeGas
          (gasCreate + initCodeHashCost + extend_cost + initCodeCost)
          evm
      let evm := evm.memExtends [⟨memory_index, memory_size⟩]
      let newAddress :=
        create2NewAddress
          evm.contract
          salt
          (evm.memory.data.sliceD memory_index memory_size 0)
      let evm ←
        genericCreate
          vb
          evm
          endowment
          newAddress
          memory_index
          memory_size
          lim
      evm.incrPc
    | .exec .call, lim + 1 => do
      let ⟨gas, evm⟩ ← evm.pop
      let ⟨callee, evm⟩ ← evm.pop <&> Prod.mapFst B256.toAdr
      let ⟨value, evm⟩ ← evm.pop
      let ⟨input_index, evm⟩ ← evm.popToNat
      let ⟨input_size, evm⟩ ← evm.popToNat
      let ⟨output_index, evm⟩ ← evm.popToNat
      let ⟨output_size, evm⟩ ← evm.popToNat
      let extend_cost :=
        evm.extCost [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]
      let mut access_cost := access_cost callee evm.accessedAddresses
      let evm := addAccessedAddress evm callee
      let ⟨disablePrecompiles, _, code, delegatedAccessGasCost, evm⟩ :=
        accessDelegation evm callee
      access_cost := access_cost + delegatedAccessGasCost
      let create_cost :=
        if (¬ (evm.getAcct callee).Empty) ∨ value = 0
        then 0
        else gNewAccount
      let transfer_cost := if value = 0 then 0 else gasCallValue
      let ⟨msg_call_cost, msg_call_stipend⟩ :=
        calculate_msg_call_gas
          value.toNat
          gas.toNat
          evm.gas_left
          extend_cost
          (access_cost + create_cost + transfer_cost)
      let evm ← chargeGas (msg_call_cost + extend_cost) evm
      .assert (!evm.msg.isStatic ∨ value = 0) ⟨evm, "WriteInStaticContext"⟩
      let evm :=
        evm.memExtends
          [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]
      let senderBal := (evm.getAcct evm.contract).bal
      let evm ←
        if senderBal < value
        then
          let evm ← evm.push 0
          .ok {
            evm with
            return_data := []
            gas_left := evm.gas_left + msg_call_stipend
          }
        else
          generic_call
            vb
            evm
            msg_call_stipend
            value
            evm.contract
            callee
            callee
            true
            false
            input_index
            input_size
            output_index
            output_size
            code
            disablePrecompiles
            lim
      evm.incrPc
    | .exec .callcode, lim + 1 => do
      let ⟨gas, evm⟩ ← evm.pop
      let ⟨codeAddress, evm⟩ ← evm.pop <&> Prod.mapFst B256.toAdr
      let ⟨value, evm⟩ ← evm.pop
      let ⟨input_index, evm⟩ ← evm.popToNat
      let ⟨input_size, evm⟩ ← evm.popToNat
      let ⟨output_index, evm⟩ ← evm.popToNat
      let ⟨output_size, evm⟩ ← evm.popToNat
      let target := evm.contract
      let extend_cost :=
        evm.extCost [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]
      let mut access_cost := access_cost codeAddress evm.accessedAddresses
      let evm := addAccessedAddress evm codeAddress
      let ⟨disablePrecompiles, codeAddress, code, delegatedAccessGasCost, evm⟩ :=
        accessDelegation evm codeAddress
      access_cost := access_cost + delegatedAccessGasCost
      let transfer_cost := if value = 0 then 0 else gasCallValue
      let ⟨msg_call_cost, msg_call_stipend⟩ :=
        calculate_msg_call_gas
          value.toNat
          gas.toNat
          evm.gas_left
          extend_cost
          (access_cost + transfer_cost)
      let evm ← chargeGas (msg_call_cost + extend_cost) evm
      let evm :=
        evm.memExtends
          [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]
      let senderBal := (evm.getAcct evm.contract).bal
      let evm ←
        if senderBal < value
        then
          let evm ← evm.push 0
          .ok {
            evm with
            return_data := []
            gas_left := evm.gas_left + msg_call_stipend
          }
        else
          generic_call
            vb
            evm
            msg_call_stipend
            value
            evm.contract
            target
            codeAddress
            true
            false
            input_index
            input_size
            output_index
            output_size
            code
            disablePrecompiles
            lim
      evm.incrPc
    | .exec .delcall, lim + 1 => do
      let ⟨gas, evm⟩ ← evm.pop
      let ⟨codeAddress, evm⟩ ← evm.pop <&> Prod.mapFst B256.toAdr
      let ⟨input_index, evm⟩ ← evm.popToNat
      let ⟨input_size, evm⟩ ← evm.popToNat
      let ⟨output_index, evm⟩ ← evm.popToNat
      let ⟨output_size, evm⟩ ← evm.popToNat
      let extend_cost :=
        evm.extCost [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]
      let mut access_cost := access_cost codeAddress evm.accessedAddresses
      let evm := addAccessedAddress evm codeAddress
      let ⟨disablePrecompiles, codeAddress, code, delegatedAccessGasCost, evm⟩ :=
        accessDelegation evm codeAddress
      access_cost := access_cost + delegatedAccessGasCost
      let ⟨msg_call_cost, msg_call_stipend⟩ :=
        calculate_msg_call_gas
          0
          gas.toNat
          evm.gas_left
          extend_cost
          access_cost
      let evm ← chargeGas (msg_call_cost + extend_cost) evm
      let evm :=
        evm.memExtends
          [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]
      let evm ←
        generic_call
          vb
          evm
          msg_call_stipend
          evm.msg.value
          evm.msg.caller
          evm.contract
          codeAddress
          false
          false
          input_index
          input_size
          output_index
          output_size
          code
          disablePrecompiles
          lim
      evm.incrPc
    | .exec .statcall, lim + 1 => do
      let gas ← evm.stackTop
      let mut evm ← evm.pop'
      let target ← evm.stackTop <&> B256.toAdr
      evm ← evm.pop'
      let input_index ← evm.stackTop <&> B256.toNat
      evm ← evm.pop'
      let input_size ← evm.stackTop <&> B256.toNat
      evm ← evm.pop'
      let output_index ← evm.stackTop <&> B256.toNat
      evm ← evm.pop'
      let output_size ← evm.stackTop <&> B256.toNat
      evm ← evm.pop'
      let extend_cost :=
        evm.extCost [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]
      let mut access_cost := access_cost target evm.accessedAddresses
      evm := addAccessedAddress evm target
      let ⟨disablePrecompiles, _, code, delegatedAccessGasCost, evm'⟩ :=
        accessDelegation evm target
      evm := evm'
      access_cost := access_cost + delegatedAccessGasCost
      let ⟨msg_call_cost, msg_call_stipend⟩ :=
        calculate_msg_call_gas
          0
          gas.toNat
          evm.gas_left
          extend_cost
          access_cost
      evm ← chargeGas (msg_call_cost + extend_cost) evm
      evm :=
        evm.memExtends
          [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]
      evm ←
        generic_call
          vb
          evm
          msg_call_stipend
          0
          evm.contract
          target
          target
          true
          true
          input_index
          input_size
          output_index
          output_size
          code
          disablePrecompiles
          lim
      evm.incrPc
  termination_by _ lim => lim

  def exec : Bool → Nat → Evm → Execution
    | _, 0, evm =>
      .error ⟨evm, "RecursionLimit"⟩
    | vb, lim + 1, evm => do
      let mut evm := evm
      -- showLim lim evm
      let i ← (evm.getInst).toExcept ⟨evm, "InvalidOpcode"⟩
      showStep vb evm i
      match i with
      | .next n =>
         evm ← n.run vb evm lim
         exec vb lim evm
      | .jump j =>
        evm ← j.run evm
        exec vb lim evm
      | .last l => l.run evm
  termination_by _ lim _ => lim

end

instance {w a} : Decidable (Dead w a) := by
  simp [Dead]
  cases (Lean.RBMap.find? w a)
  · simp; apply instDecidableTrue
  · simp [Acct.Empty]; apply instDecidableAnd

def State.code (w : State) (a : Adr) : ByteArray :=
  match w.find? a with
  | none => ByteArray.mk #[]
  | some x => x.code

def KeySet.toStrings (ks : KeySet) : List String :=
  let f : (Adr × B256) → List String :=
    fun | ⟨a, x⟩ => [s!"{a.toHex} : {x.toHex}"]
  fork "KeySet" <| ks.toList.map f

instance : ToString KeySet := ⟨λ ks => String.joinln <| ks.toStrings⟩

def Sta.toStringsCore (xs : Array B256) : Nat → List String
  | 0 => []
  | n + 1 => ("0x" ++ (xs.getD n 0).toHex) :: Sta.toStringsCore xs n

def Sta.toStrings : Sta → List String
  | ⟨xs, n⟩ => Sta.toStringsCore xs n

def Sta.toString (s : Sta) : String := String.joinln s.toStrings

instance : ToString Sta := ⟨Sta.toString⟩

def correctBlobHashVersion (h : B256) : Prop :=
  h.toB8V[0] = 0x01

instance : DecidablePred correctBlobHashVersion := by
  intro h; simp [correctBlobHashVersion]; infer_instance

def Log.toBLT (l : Log) : BLT :=
  .list [
    .b8s l.address.toB8L,
    .list (l.topics.map B256.toBLT),
    .b8s l.data
  ]

def List.putIndex {ξ : Type u} (xs : List ξ) : List (Nat × ξ) :=
  let rec aux : Nat → List ξ → List (Nat × ξ)
    | _, [] => []
    | k, x :: xs => (k, x) :: aux (k + 1) xs
  aux 0 xs

inductive ExpectedWorldState : Type
  | wor : State → ExpectedWorldState
  | root : B256 → ExpectedWorldState

structure Test where
  (name : String)
  (info : Lean.Json)
  (blocks : Lean.Json)
  (gbh : Lean.Json)
  (grlp : Lean.Json)
  (lbh : Lean.Json)
  (network : Lean.Json)
  (pre : Lean.Json)
  (post : ExpectedWorldState)
  (sealEngine : Lean.Json)

def Test.toStrings (t : Test) : List String :=
  fork "test" [
    [s!"test name : {t.name}"],
    fork "info" [t.info.toStrings],
    fork "blocks" [t.blocks.toStrings],
    fork "genesisBlockHeader" [t.gbh.toStrings],
    fork "genesisRLP" [t.grlp.toStrings],
    fork "lastblockhash" [t.lbh.toStrings],
    fork "network" [t.network.toStrings],
    fork "pre" [t.pre.toStrings],
    --[s!"postRoot {t.postRoot.toHex}"],
    fork "sealEngine" [t.sealEngine.toStrings]
  ]

instance : ToString Test := ⟨String.joinln ∘ Test.toStrings⟩

def B8L.toByteArray (xs : B8L) : ByteArray := .mk <| .mk xs

instance : ToString State := ⟨String.joinln ∘ State.toStrings⟩
instance : ToString BLT := ⟨String.joinln ∘ BLT.toStrings⟩

def toKeyVal' (pr : B8L × B8L) : B8L × B8L :=
  let ad := pr.fst
  let ac := pr.snd
  ⟨B8L.toB4s ad, ac⟩

def receiptRoot (w : List (B8L × B8L)) : B256 :=
  let keyVals : List (B8L × B8L) := (List.map toKeyVal' w)
  let finalNTB : NTB := Lean.RBMap.fromList keyVals _
  trie finalNTB

def addIndexToBloom (hash : B8L) (index : Nat) (bloom : B8L) : B8L :=
  let bitToSet : B16 :=
    (B8s.toB16 (hash.getD index 0) (hash.getD (index + 1) 0)) &&& (0x07FF : B16)
  let bitIndex : B16 := 0x07FF - bitToSet
  let byteIndex : Nat := (bitIndex / 8).toNat
  let bitValue : B8 := 0x01 <<< (0x07 - (bitIndex.lows &&& 0x07))
  let origValue : B8 := bloom.getD byteIndex 0
  bloom.set byteIndex (origValue ||| bitValue)

def addEntryToBloom (bloom : B8L) (entry : B8L) : B8L :=
  let hash := (B8L.keccak entry).toB8L
  addIndexToBloom hash 4 <|
  addIndexToBloom hash 2 <|
  addIndexToBloom hash 0 bloom

def addLogToBloom (bloom : B8L) (log : Log) : B8L :=
  let bloom' := addEntryToBloom bloom log.address.toB8L
  List.foldl addEntryToBloom bloom' (log.topics.map B256.toB8L)

def logsBloom (l : List Log) : B8L :=
  List.foldl addLogToBloom (List.replicate 256 0x00) l

def Withdrawal.toStrings (wd : Withdrawal) : List String :=
  fork "withdrawal" [
    [s!"global index : 0x{wd.globalIndex.toHex}"],
    [s!"validator index : 0x{wd.validatorIndex.toHex}"],
    [s!"recipient : 0x{wd.recipient.toHex}"],
    [s!"amount : 0x{wd.amount.toHex}"]
  ]

instance : ToString Withdrawal := ⟨String.joinln ∘ Withdrawal.toStrings⟩

def BLT.toExStrHeader : BLT → Except String Header
  | .list (
      .b8s parentHash ::
      .b8s ommersHash ::
      .b8s coinbase ::
      .b8s stateRoot ::
      .b8s txsRoot ::
      .b8s receiptRoot ::
      .b8s bloom ::
      .b8s difficulty ::
      .b8s number ::
      .b8s gasLimit ::
      .b8s gasUsed ::
      .b8s timestamp ::
      .b8s extraData ::
      .b8s prevRandao ::
      .b8s nonce ::
      .b8s baseFeePerGas ::
      .b8s withdrawalsRoot ::
      .b8s blobGasUsed ::
      .b8s excessBlobGas ::
      .b8s parentBeaconBlockRoot ::
      tail
    ) => do
      let parentHash ← parentHash.toB256?.toExcept "parentHash to B256 conversion failed"
      let ommersHash ← ommersHash.toB256?.toExcept "ommersHash to B256 conversion failed"
      let coinbase ← coinbase.toAdr?.toExcept "coinbase to Adr conversion failed"
      let stateRoot ← stateRoot.toB256?.toExcept "stateRoot to B256 conversion failed"
      let txsRoot ← txsRoot.toB256?.toExcept "txsRoot to B256 conversion failed"
      let receiptRoot ← receiptRoot.toB256?.toExcept "receiptRoot to B256 conversion failed"
      let difficulty := difficulty.toNat
      let number := number.toNat
      let gasLimit := gasLimit.toNat
      let gasUsed := gasUsed.toNat
      let timestamp := timestamp.toNat
      let prevRandao ← prevRandao.toB256?.toExcept "prevRandao to B256 conversion failed"
      let nonce ← nonce.toB64?.toExcept "nonce to B64 conversion failed"
      let baseFeePerGas := baseFeePerGas.toNat
      let withdrawalsRoot ← withdrawalsRoot.toB256?.toExcept "withdrawalsRoot to B256 conversion failed"
      let blobGasUsed := blobGasUsed.toNat
      let excessBlobGas := excessBlobGas.toNat
      let previousBeaconBlockRoot ← parentBeaconBlockRoot.toB256?.toExcept "parentBeaconBlockRoot to B256 conversion failed"
      let requestsHash : Option B256 ←
        match tail with
        | [] => .ok none
        | [.b8s requestsHash] => requestsHash.toB256?.toExcept "requestsHash conversion failed"
        | _ => .error "BLT to Header conversion failed, incorrect list length"
      .ok {
        parentHash := parentHash
        ommersHash := ommersHash
        coinbase := coinbase
        stateRoot := stateRoot
        txsRoot := txsRoot
        receiptRoot := receiptRoot
        bloom := bloom
        difficulty := difficulty
        number := number
        gasLimit := gasLimit
        gasUsed := gasUsed
        timestamp := timestamp
        extraData := extraData
        prevRandao := prevRandao
        nonce := nonce
        baseFeePerGas := baseFeePerGas
        withdrawalsRoot := withdrawalsRoot
        blobGasUsed := blobGasUsed
        excessBlobGas := excessBlobGas
        parentBeaconBlockRoot := previousBeaconBlockRoot
        requestsHash := requestsHash
      }
  | _ =>
    .error "BLT to Header conversion failed, expected a list"

def Block.toStrings (block : Block) : List String :=
  let aux : B8L ⊕ Tx → List String
    | .inl xs => fork "Encoded Tx" [String.chunks 80 xs.toHex]
    | .inr tx => tx.toStrings
  fork "BLOCK" [
    Header.toStrings block.header,
    fork "TXS" <| block.txs.map aux,
    fork "OMMERS" <| block.ommers.map Header.toStrings,
    fork "WDS" <| block.wds.map Withdrawal.toStrings
  ]

instance : ToString Block := ⟨String.joinln ∘ Block.toStrings⟩

def calculateExcessBlobGas (parentHeader : Header) : Nat :=
  let parentBlobGas : Nat :=
    parentHeader.excessBlobGas + parentHeader.blobGasUsed
  parentBlobGas - targetBlobGasPerBlock

abbrev checkGasLimit (gasLimit parentGasLimit : Nat) : Prop :=
  let maxAdjustmentDelta := parentGasLimit / gasLimitAdjustmentFactor
  gasLimit < parentGasLimit + maxAdjustmentDelta ∧
  parentGasLimit - maxAdjustmentDelta < gasLimit ∧
  gasLimitMinimum ≤ gasLimit

def calculateBaseFeePerGas
  (blockGasLimit parentGasLimit parentGasUsed parentBaseFeePerGas : Nat) :
  Except String Nat := do
  let parentGasTarget := parentGasLimit / elasticityMultiplier
  .assert
    (checkGasLimit blockGasLimit parentGasLimit)
    "InvalidBlock"
  if parentGasUsed = parentGasTarget
  then .ok parentBaseFeePerGas
  else
    if parentGasUsed > parentGasTarget
    then
      let gasUsedDelta := parentGasUsed - parentGasTarget
      let parentFeeGasDelta := parentBaseFeePerGas * gasUsedDelta
      let targetFeeGasDelta := parentFeeGasDelta / parentGasTarget
      let baseFeePerGasDelta :=
        max (targetFeeGasDelta / baseFeeMaxChangeDenominator) 1
      .ok <| parentBaseFeePerGas + baseFeePerGasDelta
    else
      let gasUsedDelta := parentGasTarget - parentGasUsed
      let parentFeeGasDelta := parentBaseFeePerGas * gasUsedDelta
      let targetFeeGasDelta := parentFeeGasDelta / parentGasTarget
      let baseFeePerGasDelta :=
        targetFeeGasDelta / baseFeeMaxChangeDenominator
      .ok <| parentBaseFeePerGas - baseFeePerGasDelta

def validateHeader (chain : BlockChain) (header : Header) :
  Except String Unit := do
  let parent ← chain.blocks.getLast?.toExcept "No parent block found"
  let expectedBaseFeePerGas ←
    calculateBaseFeePerGas
      header.gasLimit
      parent.header.gasLimit
      parent.header.gasUsed
      parent.header.baseFeePerGas
  let blockParentHash := (Header.toBLT parent.header).toB8L.keccak
  if header.excessBlobGas ≠ calculateExcessBlobGas parent.header then do
    .error "InvalidBlock : ExcessBlobGas does not match expected value"
  if header.gasUsed > header.gasLimit then do
    .error s!"InvalidBlock : gas used = {header.gasUsed} > gas limit = {header.gasLimit}"
  if expectedBaseFeePerGas ≠ header.baseFeePerGas then do
    .error "InvalidBlock : BaseFeePerGas does not match expected value"
  if header.timestamp ≤ parent.header.timestamp then do
    .error "InvalidBlock : Timestamp does not match expected value"
  if header.number ≠ parent.header.number + 1 then do
    .error "InvalidBlock : number does not match expected value"
  if header.extraData.length > 32 then do
    .error "InvalidBlock : ExtraData exceeds 32 bytes"
  if header.difficulty ≠ 0 then do
    .error "InvalidBlock : Difficulty does not match expected value"
  if header.nonce ≠ 0 then do
    .error "InvalidBlock : nonce does not match expected value"
  if header.ommersHash ≠ emptyOmmerHash then do
    .error s!"InvalidBlock : expected ommers hash = {emptyOmmerHash}, computed ommers hash"
  if header.parentHash ≠ blockParentHash then do
    .error "InvalidBlock : parentHash does not match expected value"

structure MsgCallOutput : Type where
  gasLeft : Nat
  refundCounter : Int
  logs : List Log
  accountsToDelete : AdrSet
  error: Option String
  returnData : B8L

def Except.bimap
  {ε : Type u0} {δ : Type u1} {ξ : Type u2} {υ : Type u3}
  (f : ε → δ) (g : ξ → υ) : Except ε ξ → Except δ υ
  | .error e => .error <| f e
  | .ok x => .ok <| g x

def accountHasCodeOrNonce (state : State) (adr : Adr) : Bool :=
  state.getNonce adr > 0 || !(state.getCode adr).isEmpty

def accountHasStorage (state : State) (adr : Adr) : Bool :=
  !(state.getStor adr).isEmpty

def Tx.signingHash (tx : Tx) : Option B256 :=
  match tx.type with
  | .zero gasPrice receiver =>
    if tx.v = 27 || tx.v = 28
    then
      -- signing_hash_pre155
      some <|
        B8L.keccak <|
          BLT.toB8L <|
            .list [
              .b8s tx.nonce.toB8L.sig,
              .b8s gasPrice.toB8L,
              .b8s tx.gas.toB8L,
              .b8s ((receiver <&> Adr.toB8L).getD []),
              .b8s tx.value.toB8L,
              .b8s tx.data
            ]
    else do
      -- signing_hash155
      let chainId : Nat := (tx.v - 35) / 2
      some <|
        B8L.keccak <|
          BLT.toB8L <|
            .list [
              .b8s tx.nonce.toB8L.sig,
              .b8s gasPrice.toB8L,
              .b8s tx.gas.toB8L,
              .b8s ((receiver <&> Adr.toB8L).getD []),
              .b8s tx.value.toB8L,
              .b8s tx.data,
              .b8s chainId.toB8L,
              .b8s [],
              .b8s []
            ]
  -- def signing_hash2930
  | .one chainId gasPrice receiver accessList =>
    B8L.keccak <|
      .cons (0x01 : B8) <|
        BLT.toB8L <|
          .list [
            .b8s chainId.toB8L.sig,
            .b8s tx.nonce.toB8L.sig,
            .b8s gasPrice.toB8L,
            .b8s tx.gas.toB8L,
            .b8s ((receiver <&> Adr.toB8L).getD []),
            .b8s tx.value.toB8L,
            .b8s tx.data,
            accessList.toBLT
          ]
  -- signing_hash1559
  | .two chainId maxPriorityFee maxFee receiver accessList =>
    B8L.keccak <|
      .cons (0x02 : B8) <|
        BLT.toB8L <|
          .list [
            .b8s chainId.toB8L.sig,
            .b8s tx.nonce.toB8L.sig,
            .b8s maxPriorityFee.toB8L,
            .b8s maxFee.toB8L,
            .b8s tx.gas.toB8L,
            .b8s ((receiver <&> Adr.toB8L).getD []),
            .b8s tx.value.toB8L,
            .b8s tx.data,
            accessList.toBLT
          ]
  -- def signing_hash4844
  | .three chainId maxPriorityFee maxFee receiver accessList maxBlobFee blobHashes =>
    B8L.keccak <|
      .cons (0x03 : B8) <|
        BLT.toB8L <|
          .list [
            .b8s chainId.toB8L.sig,
            .b8s tx.nonce.toB8L.sig,
            .b8s maxPriorityFee.toB8L,
            .b8s maxFee.toB8L,
            .b8s tx.gas.toB8L,
            .b8s receiver.toB8L,
            .b8s tx.value.toB8L,
            .b8s tx.data,
            accessList.toBLT,
            .b8s maxBlobFee.toB8L,
            .list <| blobHashes.map <| .b8s ∘ B256.toB8L
          ]
  | .four chainId maxPriorityFee maxFee receiver accessList auths =>
    B8L.keccak <|
      .cons (0x04 : B8) <|
        BLT.toB8L <|
          .list [
            .b8s chainId.toB8L.sig,
            .b8s tx.nonce.toB8L.sig,
            .b8s maxPriorityFee.toB8L,
            .b8s maxFee.toB8L,
            .b8s tx.gas.toB8L,
            .b8s receiver.toB8L,
            .b8s tx.value.toB8L,
            .b8s tx.data,
            accessList.toBLT,
            .list <| auths.map Auth.toBLT
          ]

-- recover_sender
def recoverSender (chain_id: B64) (tx: Tx) : Except String Adr := do
  let r := tx.r.toB256P
  let s := tx.s.toB256P
  if (r = 0 ∨ secp256k1.curveOrder.toB256 ≤ r) then
    .error "InvalidSignatureError : bad r"
  if (s = 0 ∨ secp256k1.curveOrder.toB256 / 2 < s) then
    .error "InvalidSignatureError : bad s"
  let v := tx.v
  let signingHash ←
    tx.signingHash.toExcept "InvalidSignatureError : signing hash is None"
  match tx.type with
  | .zero _ _ =>
    if v = 27 ∨ v = 28
    then
      (secp256k1.recover signingHash (v - 27).toBool r s).toExcept
        "sender recovery failed"
    else
      let chain_id_x2 := (chain_id.toNat) * (2)
      .assert (v = 35 + chain_id_x2 ∨ v = 36 + chain_id_x2) "InvalidSignatureError : bad v"
      (secp256k1.recover signingHash (v - 35 - chain_id_x2).toBool r s).toExcept
        "sender recovery failed"
  | _ =>
    .assert (v < 2) "InvalidSignatureError"
    (secp256k1.recover signingHash v.toBool r s).toExcept "sender recovery failed"

-- recover_authority
def recoverAuthority (auth : Auth) : Except String Adr := do
  let yParity := auth.yParity
  let r := auth.r
  let s := auth.s
  if (
    1 < yParity ∨
    r = 0 ∨  secp256k1.curveOrder.toB256 ≤ r ∨
    s = 0 ∨ (secp256k1.curveOrder.toB256 / 2) < s
  ) then
    .error "InvalidSignatureError"
  let signingHash : B256 :=
    B8L.keccak <|
      List.append setCodeTxMagic <|
        BLT.toB8L <| .list [
          .b8s auth.chainId.toB8L.sig,
          .b8s auth.address.toB8L,
          .b8s auth.nonce.toB8L.sig
        ]
  (secp256k1.recover signingHash yParity.toBool r s ).toExcept "sender recovery failed"

def setDelegation (msg : Msg) : Except String (Msg × B256) := do
  let mut refundCounter : B256 := 0
  let mut msg := msg
  for auth in msg.tenv.auths do
    if auth.chainId != msg.benv.chainId && auth.chainId != 0 then
      continue
    if auth.nonce = B64.max then
      continue
    let authority : Adr ←
      match recoverAuthority auth with
      | .error err =>
        if err = "InvalidSignatureError" then
          continue
        else
          .error err
      | .ok adr => .ok adr
    msg := {msg with accessedAddresses := msg.accessedAddresses.insert authority}
    let authorityAccount : Acct :=
      msg.benv.state.get authority
    let authorityCode : ByteArray := authorityAccount.code
    if ¬ (authorityCode.isEmpty ∧ isValidDelegation authorityCode) then
      continue
    if authorityAccount.nonce != auth.nonce then
      continue
    if AccountExists msg.benv.state authority then
      refundCounter :=
        refundCounter + (perEmptyAccountCost - perAuthBaseCost).toB256
    let codeToSet : ByteArray :=
      if auth.address = 0 then
        .empty
      else
        (eoaDelegationMarker ++ auth.address.toB8L).toByteArray
    msg := msg.setCode authority codeToSet
    msg := msg.incrNonce authority
  msg ←
    match msg.codeAddress with
    | none =>
      .error "InvalidBlock : Invalid type 4 transaction: no target"
    | some ca =>
      .ok {
        msg with
        code := msg.benv.state.getCode ca
      }
  .ok ⟨msg, refundCounter⟩

def processMessageCall (vb : Bool) (msg : Msg) :
  Except String (State × MsgCallOutput) := do
  let benv := msg.benv
  let mut msg : Msg := msg
  let mut refundCounter : Nat := 0
  let mut evm : Evm := default
  if msg.target.isNone then
    let isCollision : Bool :=
      accountHasCodeOrNonce benv.state msg.currentTarget || accountHasStorage benv.state msg.currentTarget
    if isCollision then
      return ⟨benv.state, ⟨0, 0, [], .emptyWithCapacity, "AddressCollision", []⟩⟩
    else
      evm ← Except.bimap (Prod.snd ∘ Prod.snd) id <| processCreateMessage vb msg (msg.gas + 50)
  else
    if !msg.tenv.auths.isEmpty then
      let ⟨msg', setDelegationValue⟩ ← setDelegation msg
      msg := msg'
      refundCounter := refundCounter + setDelegationValue.toNat
    match getDelegatedCodeAddress msg.code with
    | none => .ok ()
    | some dca =>
      msg :=
        {
          msg with
          disablePrecompiles := true,
          accessedAddresses := msg.accessedAddresses.insert dca,
          code := benv.state.getCode dca,
          codeAddress := some dca
        }
    evm ← Except.bimap (Prod.snd ∘ Prod.snd) id <| processMsg vb msg (msg.gas + 50)
  let mut logs : List Log := []
  let mut accountsToDelete : AdrSet := .emptyWithCapacity
  if evm.error.isNone then
    logs := evm.logs
    accountsToDelete := evm.accountsToDelete
    let evmRc ← (Int.toNat? evm.refund_counter).toExcept "ERROR : refund counter is negative"
    refundCounter := refundCounter + evmRc
--return MsgCallOutput
  .ok ⟨
    evm.msg.benv.state,
    {
      gasLeft := evm.gas_left,
      refundCounter := refundCounter
      logs := logs,
      accountsToDelete := accountsToDelete,
      error := evm.error,
      returnData := evm.output
    }
  ⟩

def Tx.isTypeThree (tx : Tx) : Bool :=
  match tx.type with
  | .three _ _ _ _ _ _ _ => true
  | _ => false

def Tx.isTypeFour (tx : Tx) : Bool :=
  match tx.type with
  | .four _ _ _ _ _ _ => true
  | _ => false

-- calculate_total_blob_gas
def calculateTotalBlobGas (tx: Tx) : Nat :=
  match tx.type with
  | .three _ _ _ _ _ _ blobHashes => gasPerBlob * blobHashes.length
  | _ => 0

structure Receipt : Type where
  succeeded : Bool
  gasUsed : Nat
  bloom : B8L
  logs : List Log

structure BlockOutput : Type where
  blockGasUsed : Nat
  transactionsTrie : Lean.RBMap B8L Tx compare
  receiptsTrie : Lean.RBMap B8L (Fin 5 × Receipt) compare
  receiptKeys : List B8L
  blockLogs : List Log
  withdrawalsTrie : Lean.RBMap B8L Withdrawal compare
  blobGasUsed : Nat
  requests : List B8L

-- check_transaction
def checkTransaction (benv : Benv) (blockOut : BlockOutput) (tx : Tx) :
  Except String (Adr × Nat × List B256 × Nat) := do
  let gasAvailable := benv.blockGasLimit - blockOut.blockGasUsed
  let blobGasAvailable := maxBlobGasPerBlock - blockOut.blobGasUsed
  if tx.gas > gasAvailable then
    .error "GasUsedExceedsLimitError : gas used exceeds limit"
  let txBlobGasUsed := calculateTotalBlobGas tx
  if txBlobGasUsed > blobGasAvailable then
    .error s!"BlobGasLimitExceededError : blob gas used = {txBlobGasUsed}, blob gas available = {blobGasAvailable}"
  let senderAddress ← recoverSender benv.chainId tx
  let senderAccount := benv.state.get senderAddress
  let mut effectiveGasPrice := 0
  let mut maxGasFee := 0
  let selector : Nat ⊕ (Nat × Nat) :=
    match tx.type with
    | .zero gasPrice _ => .inl gasPrice
    | .one _ gasPrice _ _ => .inl gasPrice
    | .two _ maxPriorityFee maxFee _ _ => .inr (maxPriorityFee, maxFee)
    | .three _ maxPriorityFee maxFee _ _ _ _ => .inr (maxPriorityFee, maxFee)
    | .four _ maxPriorityFee maxFee _ _ _ => .inr (maxPriorityFee, maxFee)
  match selector with
  | .inr (maxPriorityFee, maxFee) =>
    if maxFee < maxPriorityFee then
      .error "PriorityFeeGreaterThanMaxFeeError : priority fee greater than max fee"
    if maxFee < benv.baseFeePerGas then
      .error "InsufficientMaxFeePerGasError"
    let priorityFeePerGas := min maxPriorityFee (maxFee - benv.baseFeePerGas)
    effectiveGasPrice := priorityFeePerGas + benv.baseFeePerGas
    maxGasFee := tx.gas * maxFee
  | .inl gasPrice =>
    if gasPrice < benv.baseFeePerGas then
      .error "InvalidBlock : gas price below base fee"
    effectiveGasPrice := gasPrice
    maxGasFee := tx.gas * gasPrice
  let mut blobVersionedHashes : List B256 := []
  match tx.type with
  | .three _ _ _ _ _ maxBlobFee blobHashes =>
    if blobHashes.isEmpty then
      .error "NoBlobDataError : no blob data in transaction"
    if List.any blobHashes (λ bvh => bvh.toB8V.head ≠ versionedHashVersionKzg) then
      .error "InvalidBlobVersionedHashError : invalid blob versioned hash"
    let blobGasPrice := calculate_blob_gas_price benv.excessBlobGas
    if maxBlobFee < blobGasPrice then
      .error "InsufficientMaxFeePerBlobGasError : insufficient max fee per blob gas"
    maxGasFee := maxGasFee + calculateTotalBlobGas tx * maxBlobFee
    blobVersionedHashes := blobHashes
  | _ => .ok ()
  if tx.isTypeThree ∨ tx.isTypeFour then
    if tx.type.receiver?.isNone then
      .error "TransactionTypeContractCreationError : receiver is none for type 3 or 4 tx"
  match tx.type with
  | .four _ _ _ _ _ [] =>
    .error "EmptyAuthorizationListError : empty authorization list"
  | _ => .ok ()
    if senderAccount.nonce > tx.nonce then
      .error "NonceMismatchError : nonce too low"
    else if senderAccount.nonce < tx.nonce then
      .error "NonceMismatchError : nonce too high"
    if senderAccount.bal.toNat < maxGasFee + tx.value then
      .error s!"InsufficientBalanceError : sender balance ({senderAccount.bal.toNat}) < max gas fee ({maxGasFee}) + tx value ({tx.value})"
    if ¬ (senderAccount.code.isEmpty ∨ isValidDelegation senderAccount.code) then
      .error "InvalidSenderError : not EOA"
    .ok ⟨
      senderAddress,
      effectiveGasPrice,
      blobVersionedHashes,
      txBlobGasUsed
    ⟩

def calculateIntrinsicCost (tx: Tx) : Nat × Nat :=
  let tokensInCalldata : Nat :=
    (tx.data.map <| fun x => if x = 0 then 1 else 4).sum
  let callDataFloorGasCost : Nat :=
    tokensInCalldata * floorCalldataCost + txBaseCost
  let dataCost : Nat :=
    tokensInCalldata * standardCallDataTokenCost
  let createCost : Nat :=
      match tx.type.receiver? with
      | none => txCreateCost + initCodeCost (tx.data).length
      | some _ => 0
  let accessListCost : Nat :=
    let accessList :=
      match tx.type with
      | .zero _ _ => []
      | .one _ _ _ accessList => accessList
      | .two _ _ _ _ accessList => accessList
      | .three _ _ _ _ accessList _ _ => accessList
      | .four _ _ _ _ accessList _ => accessList
    let accessItemCost : (Adr × List B256) → Nat
      | ⟨_, keys⟩ =>
        txAccessListAddressCost + keys.length * txAccessListStorageKeyCost
    (accessList.map accessItemCost).sum
  let authCost : Nat :=
    match tx.type with
    | .four _ _ _ _ _ auths => perEmptyAccountCost * auths.length
    | _ => 0
  ⟨
    txBaseCost + dataCost + createCost + accessListCost + authCost,
    callDataFloorGasCost
  ⟩

-- validate_transaction
def validateTransaction (tx : Tx) : Except String (Nat × Nat) := do
  let ⟨intrinsicGas, callDataFloorGasCost⟩ := calculateIntrinsicCost tx
  if max intrinsicGas callDataFloorGasCost > tx.gas
    then .error "InvalidTransaction : Insufficient gas"
  if tx.nonce = B64.max
    then .error "InvalidTransaction : Nonce too high"
  if tx.type.receiver?.isNone && tx.data.length > maxInitcodeSize
    then .error "InvalidTransaction : Code size too large"
  .ok ⟨intrinsicGas, callDataFloorGasCost⟩

def prepareMessage (benv: Benv) (tenv: Tenv) (tx: Tx) :
  Except String Msg := do
  let ⟨currentTarget, msgData, code, codeAddress⟩ :
    Adr × B8L × ByteArray × Option Adr :=
    match tx.type.receiver? with
    | none => ⟨
        compute_contract_address
          tenv.origin
          (benv.state.getNonce tenv.origin - 1),
        [],
        .mk (.mk tx.data),
        none
      ⟩
    | some target => ⟨
        target,
        tx.data,
        benv.state.getCode target,
        target
      ⟩
  let accessedAddresses : AdrSet :=
    tenv.accessListAddresses.insertMany
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, tenv.origin, currentTarget]
  .ok {
    benv := benv,
    tenv := tenv,
    caller := tenv.origin,
    target := tx.type.receiver?,
    gas := tenv.gas,
    value := tx.value.toB256,
    data := msgData,
    code := code,
    depth := 0,
    currentTarget := currentTarget,
    codeAddress := codeAddress
    shouldTransferValue := true,
    isStatic := false,
    accessedAddresses := accessedAddresses,
    accessedStorageKeys := tenv.accessListStorageKeys,
    disablePrecompiles := false
  }

-- calculate_total_blob_gas
def calculate_total_blob_gas (tx: Tx) : Nat :=
  match tx.type with
  | .three _ _ _ _ _ _ blobHashes => gasPerBlob * blobHashes.length
  | _ => 0

-- calculate_data_fee
def calculate_data_fee (excess_blob_gas: Nat) (tx: Tx) : Nat :=
  calculate_total_blob_gas tx * calculate_blob_gas_price excess_blob_gas

def getTxHash (tx : Tx) : B256 := tx.toBLT.toB8L.keccak

def Receipt.toStrings (r : Receipt) : List String :=
  fork "RECEIPT" [
    [s!"SUCCEEDED: {r.succeeded}"],
    [s!"GAS USED: {r.gasUsed}"],
    fork "BLOOM" [r.bloom.toHex.chunks 64],
    fork "LOGS" (r.logs.map Log.toStrings)
  ]

instance : ToString Receipt where
  toString := String.joinln ∘ Receipt.toStrings

def Receipt.toBLT (r : Receipt) : BLT :=
  .list [
    .b8s (if r.succeeded then [0x01] else []),
    .b8s r.gasUsed.toB8LPack,
    .b8s r.bloom,
    .list (r.logs.map Log.toBLT)
  ]

-- make_receipt
def makeReceipt
  (tx: Tx)
  (error: Option String)
  (gasUsed: Nat)
  (logs: List Log) : Fin 5 × Receipt :=
  let receipt : Receipt := {
    succeeded := error.isNone,
    gasUsed := gasUsed,
    bloom := logsBloom logs,
    logs := logs
  }
  let head : Fin 5 :=
    match tx.type with
    | .zero _ _ => 0
    | .one _ _ _ _ => 1
    | .two _ _ _ _ _ => 2
    | .three _ _ _ _ _ _ _ => 3
    | .four _ _ _ _ _ _ => 4
  ⟨head, receipt⟩

def BlockOutput.init : BlockOutput :=
  {
    blockGasUsed := 0
    transactionsTrie := .empty
    receiptsTrie := .empty
    receiptKeys := []
    blockLogs := []
    withdrawalsTrie := .empty
    blobGasUsed := 0
    requests := []
  }

-- process_transaction
def processTransaction
  (vb : Bool) (benv: Benv) (bout : BlockOutput)
  (tx: Tx) (index : Nat) : Except String (State × BlockOutput) := do
  let transactionsTrie : Lean.RBMap B8L Tx compare :=
    bout.transactionsTrie.insert (BLT.b8s index.toB8L).toB8L tx
  let bout := {bout with transactionsTrie := transactionsTrie}
  let ⟨intrinsicGas, calldataFloorGasCost⟩ ← validateTransaction tx
  let ⟨
    sender,
    effectiveGasPrice,
    blobVersionedHashes,
    txBlobGasUsed
  ⟩ ← checkTransaction benv bout tx
  let blobGasFee :=
    if tx.isTypeThree
    then calculate_data_fee benv.excessBlobGas tx
    else 0
  let effectiveGasFee := tx.gas * effectiveGasPrice
  let gas := tx.gas - intrinsicGas
  let mut state : State := benv.state.incrNonce sender
  state ← (state.subBal sender (effectiveGasFee + blobGasFee).toB256).toExcept
    "ERROR : balance underflow"
  let preaccessedAddresses : AdrSet :=
    .ofList (benv.coinbase :: tx.accessList.map Prod.fst)
  let preaccessedStorageKeys : KeySet :=
    .ofList (tx.accessList.map <| λ ⟨adr, keys⟩ => keys.map (⟨adr, ·⟩)).flatten
  let tenv : Tenv := {
    origin := sender
    gasPrice := effectiveGasPrice
    gas := gas
    accessListAddresses := preaccessedAddresses
    accessListStorageKeys := preaccessedStorageKeys
    transientStorage := .empty
    blobVersionedHashes := blobVersionedHashes
    auths := tx.auths
    indexInBlock := index
    txHash := getTxHash tx
  }
  let msg ← prepareMessage {benv with state := state} tenv tx
  let ⟨state', txOutput⟩ ← processMessageCall vb msg
  state := state'
  let txGasUsedBeforeRefund := tx.gas - txOutput.gasLeft
  let refundCounter : Nat ←
    (Int.toNat? txOutput.refundCounter).toExcept "ERROR : refund counter is negative"
  let mut txGasRefund : Nat :=
    min (txGasUsedBeforeRefund / 5) refundCounter
  let txGasUsedAfterRefund : Nat :=
    max (txGasUsedBeforeRefund - txGasRefund) calldataFloorGasCost
  let txGasLeft :=
    tx.gas - txGasUsedAfterRefund
  let gasRefundAmount : Nat :=
    txGasLeft * effectiveGasPrice
  let priorityFeePerGas := effectiveGasPrice - benv.baseFeePerGas
  let transactionFee := txGasUsedAfterRefund * priorityFeePerGas
  state := state.addBal sender gasRefundAmount.toB256
  state := state.addBal benv.coinbase transactionFee.toB256
  for adr in txOutput.accountsToDelete do
    state := destroyAccount state adr
  let mut bout := {
    bout with
    blockGasUsed := bout.blockGasUsed + txGasUsedAfterRefund,
    blobGasUsed := bout.blobGasUsed + txBlobGasUsed
  }
  let receipt :=
    makeReceipt tx txOutput.error bout.blockGasUsed txOutput.logs
  let receiptKey : B8L := BLT.toB8L <| .b8s index.toB8L
  bout := {
    bout with
    receiptKeys := bout.receiptKeys ++ [receiptKey]
    receiptsTrie :=
      bout.receiptsTrie.insert receiptKey receipt
    blockLogs := bout.blockLogs ++ txOutput.logs
  }
  .ok ⟨state, bout⟩

-- def process_withdrawal
def processWithdrawals
  (benv : Benv) (bout : BlockOutput) (wds : List Withdrawal) : State × BlockOutput :=
  let trie : Lean.RBMap B8L Withdrawal compare :=
    List.foldl (λ acc ⟨i, wd⟩ =>
      acc.insert (BLT.toB8L <| .b8s i.toB8L) wd) bout.withdrawalsTrie wds.putIndex
  let state :=
    List.foldl (λ acc wd => acc.addBal wd.recipient (wd.amount * (10 ^ 9).toB256)) benv.state wds
  ⟨state, {bout with withdrawalsTrie := trie}⟩

def BLT.toAccessItem : BLT → Option (Adr × List B256)
  | .list [.b8s ar, .list ksr] => do
    let a ← B8L.toAdr? ar
    let ks ← List.mapM toB256 ksr
    pure ⟨a, ks⟩
  | _ => none

def BLT.toAccessList : BLT → Option AccessList
  | .list rs => List.mapM toAccessItem rs
  | _ => none

def B8L.toExStrTx : B8L → Except String Tx
  | [] => .error "error : cannot decode empty transaction BLT"
  | x :: xs =>
    match x, B8L.toBLT? xs with
    | 0x01, BLT.list [
        .b8s chainId,
        .b8s nonce,
        .b8s gasPrice,
        .b8s gas,
        .b8s receiver,
        .b8s value,
        .b8s data,
        accessList,
        .b8s yParity,
        .b8s r,
        .b8s s
      ] => do .ok {
          nonce := nonce.toB64P,
          gas := gas.toNat,
          value := value.toNat,
          data := data,
          v := yParity.toNat,
          r := (r.reverse.takeD 32 0).reverse,
          s := (s.reverse.takeD 32 0).reverse,
          type :=
            .one
              chainId.toB64P
              gasPrice.toNat
              receiver.toAdr?
              (← accessList.toAccessList.toExcept "cannot decode access list")
        }
    | 0x02, BLT.list [
        .b8s chainId,
        .b8s nonce,
        .b8s maxPriorityFee,
        .b8s maxFee,
        .b8s gas,
        .b8s receiver,
        .b8s value,
        .b8s data,
        accessList,
        .b8s yParity,
        .b8s r,
        .b8s s
      ] => do .ok {
        nonce := nonce.toB64P,
        gas := gas.toNat,
        value := value.toNat,
        data := data,
        v := yParity.toNat,
        r := (r.reverse.takeD 32 0).reverse,
        s := (s.reverse.takeD 32 0).reverse,
        type :=
          .two
            chainId.toB64P
            maxPriorityFee.toNat
            maxFee.toNat
            receiver.toAdr?
            (← accessList.toAccessList.toExcept "cannot decode access list")
      }
    | 0x03, BLT.list [
        .b8s chainId,
        .b8s nonce,
        .b8s maxPriorityFee,
        .b8s maxFee,
        .b8s gas,
        .b8s receiver,
        .b8s value,
        .b8s data,
        accessList,
        .b8s maxBlobFee,
        .list blobHashes,
        .b8s yParity,
        .b8s r,
        .b8s s
      ] => do .ok {
        nonce := nonce.toB64P,
        gas := gas.toNat,
        value := value.toNat,
        data := data,
        v := yParity.toNat,
        r := (r.reverse.takeD 32 0).reverse,
        s := (s.reverse.takeD 32 0).reverse,
        type :=
          .three
            chainId.toB64P
            maxPriorityFee.toNat
            maxFee.toNat
            (← receiver.toAdr?.toExcept "DecodingError")
            (← accessList.toAccessList.toExcept "cannot decode access list")
            maxBlobFee.toNat
            (← List.mapM (λ r => r.toB256.toExcept "cannot decode blob hash") blobHashes)
      }
    | x, _ => .error s!"ERROR : type-{x} txs do not exist, decoding failed"

def decodeTx : B8L ⊕ Tx → Except String Tx
  | .inl xs => xs.toExStrTx
  | .inr tx => .ok tx

-- process_system_transaction
def processSystemTransaction (vb : Bool) (benv : Benv)
  (target : Adr) (code : ByteArray) (data : B8L) :
  Except String (State × MsgCallOutput) := do
  let txEnv : Tenv := {
    origin := systemAddress,
    gasPrice := benv.baseFeePerGas,
    gas := systemTransactionGas,
    accessListAddresses := .emptyWithCapacity
    accessListStorageKeys := .emptyWithCapacity
    transientStorage := .empty,
    blobVersionedHashes := [],
    auths := [],
    indexInBlock := none,
    txHash := none
  }
  let systemTxMsg : Msg := {
    benv := benv,
    tenv := txEnv,
    caller := systemAddress,
    target := target,
    gas := systemTransactionGas,
    value := 0,
    data := data,
    code := code,
    depth := 0,
    currentTarget := target,
    codeAddress := target,
    shouldTransferValue := false,
    isStatic := false,
    accessedAddresses := .emptyWithCapacity,
    accessedStorageKeys := .emptyWithCapacity,
    disablePrecompiles := false
  }
  processMessageCall vb systemTxMsg

def extractDepositData (data : B8L) : Except String B8L := do
  if data.length != depositEventLength then
    .error "InvalidBlock : Invalid deposit event data length"
  if data.sliceToNat 0 32 ≠ pubkeyOffset then
    .error "InvalidBlock : Invalid pubkey offset in deposit log"
  if data.sliceToNat 32 32 ≠ withdrawalCredentialsOffset then
    .error "InvalidBlock : Invalid withdrawal credentials offset in deposit log"
  if data.sliceToNat 64 32 ≠ amountOffset then
    .error "InvalidBlock : Invalid amount offset in deposit log"
  if data.sliceToNat 96 32 ≠ signatureOffset then
    .error "InvalidBlock : Invalid signature offset in deposit log"
  if data.sliceToNat 128 32 ≠ indexOffset then
    .error "InvalidBlock : Invalid index offset in deposit log"
  if data.sliceToNat pubkeyOffset 32 ≠ pubkeySize then
    .error "InvalidBlock : Invalid pubkey size in deposit log"
  let pubkey : B8L := data.slice! (pubkeyOffset + 32) pubkeySize
  if data.sliceToNat withdrawalCredentialsOffset 32 ≠ withdrawalCredentialsSize then
    .error "InvalidBlock : Invalid withdrawal credentials size in deposit log"
  let withdrawalCredentials : B8L :=
    data.slice! (withdrawalCredentialsOffset + 32) withdrawalCredentialsSize
  if data.sliceToNat amountOffset 32 ≠ amountSize then
    .error "InvalidBlock : Invalid amount size in deposit log"
  let amount : B8L := data.slice! (amountOffset + 32) amountSize
  if data.sliceToNat signatureOffset 32 ≠ signatureSize then
    .error "InvalidBlock : Invalid signature size in deposit log"
  let signature : B8L := data.slice! (signatureOffset + 32) signatureSize
  if data.sliceToNat indexOffset 32 ≠ indexSize then
    .error "InvalidBlock : Invalid index size in deposit log"
  let index : B8L := data.slice! (indexOffset + 32) indexSize
  .ok (pubkey ++ withdrawalCredentials ++ amount ++ signature ++ index)

-- parse_deposit_requests
def parseDepositRequests
  (bout : BlockOutput) : Except String B8L := do
  let mut depositRequests : B8L := []
  for key in bout.receiptKeys do
    let ⟨_, receipt⟩  ←
      (bout.receiptsTrie.find? key).toExcept "ERROR : receipt not found"
    for log in receipt.logs do
      if (
        log.address = depositContractAddress ∧
        log.topics[0]? = some depositEventSignatureHash
      ) then
        let request ← extractDepositData log.data
        depositRequests := depositRequests ++ request
  .ok depositRequests

def processUncheckedSystemTransaction
  (vb : Bool) (benv : Benv) (target : Adr) (data : B8L) :
  Except String (State × MsgCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  processSystemTransaction vb benv target systemContractCode data

def processCheckedSystemTransaction
  (vb : Bool) (benv : Benv) (target : Adr) (data : B8L) :
  Except String (State × MsgCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  if systemContractCode.isEmpty then
    .error s!"InvalidBlock : System contract address {target.toHex} does not contain code"
  let ⟨state, systemTxOutput⟩ ←
    processSystemTransaction vb benv target systemContractCode data
  if systemTxOutput.error.isSome then
    .error s!"InvalidBlock : System contract ({target.toHex}) call failed: {systemTxOutput.error.get!}"
  .ok ⟨state, systemTxOutput⟩

def processGeneralPurposeRequests
  (vb : Bool) (benv : Benv) (bout : BlockOutput) :
  Except String (State × BlockOutput) := do
  let depositRequests ← parseDepositRequests bout
  let mut requestsFromExecution : List B8L := bout.requests
  if depositRequests.length > 0 then
    requestsFromExecution :=
      requestsFromExecution ++ [depositRequestType ++ depositRequests]
  let ⟨state, withdrawalOutput⟩  ←
    processCheckedSystemTransaction vb benv
      withdrawalRequestPredeployAddress
      []
  let benv := {benv with state := state}
  if withdrawalOutput.returnData.length > 0 then
    requestsFromExecution :=
      requestsFromExecution ++ [withdrawalRequestType ++ withdrawalOutput.returnData]
  let ⟨state, consolidationOutput⟩  ←
    processCheckedSystemTransaction vb benv
      consolidationRequestPredeployAddress
      []
  if consolidationOutput.returnData.length > 0 then
    requestsFromExecution :=
      requestsFromExecution ++ [consolidationRequestType ++ consolidationOutput.returnData]
  .ok ⟨state, {bout with requests := requestsFromExecution}⟩

def applyBody
  (vb : Bool) (benv : Benv) (txs : List (B8L ⊕ Tx)) (wds : List Withdrawal) :
  Except String (State × BlockOutput) := do
  let mut bout := BlockOutput.init
  cprint vb "\n================================ BEACON ROOTS TX ================================\n"
  let ⟨state, _⟩ ←
    processUncheckedSystemTransaction false benv
      beaconRootsAddress
      benv.parentBeaconBlockRoot.toB8L
  let mut benv : Benv := {benv with state := state}
  cprint vb "\n================================ HISTORY STORAGE TX ================================\n"
  let lastHash ←
     benv.blockHashes.getLast?.toExcept "ERROR : block hashes is empty"
  let ⟨state, _⟩ ←
    processUncheckedSystemTransaction false benv
      historyStorageAddress
      lastHash.toB8L
  benv := {benv with state := state}
  cprint vb "\n================================ TEST TXS ================================\n"
  for ⟨i, tx⟩ in (← txs.mapM decodeTx).putIndex do
    let ⟨state, bout'⟩ ← processTransaction vb benv bout tx i
    benv := {benv with state := state}
    bout := bout'
  cprint vb s!"\nSTATE AFTER TEST TXS :"
  cprint vb s!"{benv.state}"
  cprint vb "\n================================ PROCESS WITHDRAWALS ================================\n"
  let ⟨state, bout'⟩ :=
    processWithdrawals benv bout wds
  benv := {benv with state := state}
  bout := bout'
  cprint vb "\n================================ PROCESS GENERAL PURPOSE REQUESTS ================================\n"
  processGeneralPurposeRequests vb benv bout

-- get_last256_block_hashes
def getLast256BlockHashes (chain : BlockChain) : List B256 :=
  match chain.blocks.reverse.take 255 with
  | [] => []
  | block :: blocks =>
    let hash : B256 := (Header.toBLT block.header).toB8L.keccak
    let hashes : List B256 :=
      blocks.map <| fun x => x.header.parentHash
    (hash :: hashes).reverse

def computeRequestsHash (requests : List B8L) : B256 :=
  let hashes := requests.map (fun r => r.keccak.toB8L)
  B8L.sha256 <| List.flatten hashes

def State.root (w : State) : B256 :=
  let keyVals := (List.map toKeyVal w.toList)
  let finalNTB : NTB := Lean.RBMap.fromList keyVals _
  trie finalNTB

-- state_transition
def state_transition (vb : Bool) (chain : BlockChain) (block : Block) :
  Except String BlockChain := do
  validateHeader chain block.header
  if ¬block.ommers.isEmpty then do
    .error "InvalidBlock"
  let benv : Benv := {
    chainId := chain.chainId,
    state := chain.state,
    origState := chain.state,
    createdAccounts := .emptyWithCapacity,
    blockGasLimit := block.header.gasLimit,
    blockHashes := getLast256BlockHashes chain,
    coinbase := block.header.coinbase,
    number := block.header.number,
    baseFeePerGas := block.header.baseFeePerGas,
    time := block.header.timestamp.toB256,
    prevRandao := block.header.prevRandao,
    excessBlobGas := block.header.excessBlobGas,
    parentBeaconBlockRoot := block.header.parentBeaconBlockRoot
  }
  let ⟨state, bout⟩ ← applyBody vb benv block.txs block.wds
  let blockStateRoot : B256 := state.root
  let transactionsRoot : B256 ← do
    let transactionsAux (arg : B8L × Tx) : (B8L × B8L) :=
      let txPrefix : B8L :=
        match arg.snd.type with
        | .zero _ _ => []
        | .one _ _ _ _ => [0x01]
        | .two _ _ _ _ _ => [0x02]
        | .three _ _ _ _ _ _ _ => [0x03]
        | .four _ _ _ _ _ _ => [0x04]
      ⟨arg.fst.toB4s, txPrefix ++ arg.snd.toBLT.toB8L⟩
    let temp := List.map transactionsAux bout.transactionsTrie.toList
    .ok <| trie <| Lean.RBMap.fromList temp _
  let receiptRoot : B256 :=
    let receiptAux : (B8L × Fin 5 × Receipt) → (B8L × B8L)
      | ⟨key, type, receipt⟩ =>
        ⟨key.toB4s, type.val.toB8L ++ receipt.toBLT.toB8L⟩
                let temp := (List.map receiptAux bout.receiptsTrie.toList)
    trie <| Lean.RBMap.fromList temp _
  let block_logs_bloom := logsBloom bout.blockLogs
  let withdrawalsRoot : B256 :=
    let withdrawalsAux (arg : B8L × Withdrawal) : B8L × B8L :=
      ⟨arg.fst.toB4s, arg.snd.toBLT.toB8L⟩
    let temp := (List.map withdrawalsAux bout.withdrawalsTrie.toList)
    trie <| Lean.RBMap.fromList temp _
  let requestsHash := computeRequestsHash bout.requests
  if bout.blockGasUsed ≠ block.header.gasUsed then
    .error s!"InvalidBlock : computed block gas used = {bout.blockGasUsed} ≠ expected block gas used = {block.header.gasUsed}"
  if transactionsRoot ≠ block.header.txsRoot then
    .error s!"InvalidBlock : computed transactions root = {transactionsRoot} ≠ expected transactions root = {block.header.txsRoot}"
  if blockStateRoot ≠ block.header.stateRoot then
    .error "InvalidBlock : state root mismatch"
  if receiptRoot ≠ block.header.receiptRoot then
    .error "InvalidBlock : receipt root mismatch"
  if block_logs_bloom ≠ block.header.bloom then
    .error "InvalidBlock : bloom mismatch"
  if withdrawalsRoot ≠ block.header.withdrawalsRoot then
    .error "InvalidBlock : withdrawals root mismatch"
  if bout.blobGasUsed ≠ block.header.blobGasUsed then
    .error "InvalidBlock : blob gas used mismatch"
  if some requestsHash ≠ block.header.requestsHash then
    .error s!"InvalidBlock : expected requests hash = {block.header.requestsHash}, computed requests hash = {requestsHash}"
  .ok {
    state := state
    blocks := (block :: chain.blocks.reverse.take 254).reverse
    chainId := chain.chainId
  }

def BLT.toExStrWithdrawal : BLT → Except String Withdrawal
  | .list [
      .b8s globalIndex,
      .b8s validatorIndex,
      .b8s recipient,
      .b8s amount
    ] => do
    let globalIndex := globalIndex.toB64P
    let validatorIndex := validatorIndex.toB64P
    let recipient ← recipient.toAdr?.toExcept "error : invalid recipient address"
    let amount := amount.toB256P
    .ok {
      globalIndex := globalIndex,
      validatorIndex := validatorIndex,
      recipient := recipient,
      amount := amount
    }
  | _ => .error "error : invalid withdrawal BLT format"

def BLT.toExStrTx : BLT → Except String Tx
  | .list [
      .b8s nonce,
      .b8s gasPrice,
      .b8s gas,
      .b8s receiver,
      .b8s value,
      .b8s data,
      .b8s v,
      .b8s r,
      .b8s s
    ] => .ok {
      nonce := nonce.toB64P,
      gas := gas.toNat
      value := value.toNat,
      data := data,
      v := v.toNat,
      r := r,
      s := s,
      type := .zero gasPrice.toNat receiver.toAdr?
    }
  | .list _ => .error "error : invalid transaction BLT format"
  | .b8s xs => xs.toExStrTx

def BLT.toExStrBlock : BLT → Except String Block
  | BLT.list [
      HeaderBLT,
      .list TxBLTs,
      .list OmmerBLTs,
      .list WithdrawalBLTs
    ] => do
    let header ← HeaderBLT.toExStrHeader
    let aux : BLT → Except String (B8L ⊕ Tx)
      | blt@(.list _) => blt.toExStrTx <&> .inr
      | .b8s xs => .ok <| .inl xs
    let txs ← List.mapM aux TxBLTs
    let ommers ← List.mapM BLT.toExStrHeader OmmerBLTs
    let withdrawals ← List.mapM BLT.toExStrWithdrawal WithdrawalBLTs
    .ok {
      header := header,
      txs := txs,
      ommers := ommers,
      wds := withdrawals
    }
  | _ => .error "error : invalid block BLT format"

/-
rlpToBlock is equivalent to json_to_block from execution-specs.
why does it accept the RLP bytes as input, and not the whole JSON?
the justification is that json_to_block expects the RLP bytes to be
always available, and always uses *only* the RLP bytes to obtain the
block, ignoring everything else in the JSON (the code path that deals
with nonexistent RLP bytes exists, but is unreachable). its return
type also omits the RLP bytes, since this is identical to the input.
-/
def rlpToBlock (rlp : B8L) : Except String (Block × B256) := do
  let block_blt ← (B8L.toBLT? rlp).toExcept "error : cannot decode block from rlp"
  let block ← block_blt.toExStrBlock
  .ok ⟨block, (Header.toBLT block.header).toB8L.keccak⟩

def addBlockToChain (vb : Bool) (chain : BlockChain) (blockRlp : B8L) :
  Except String (BlockChain ⊕ String) := do
  let ⟨block, blockHeaderHash⟩ ← rlpToBlock blockRlp
  cprint vb "\nSTATE BEFORE TRANSITION :"
  cprint vb s!"{chain.state}"
  if (Header.toBLT block.header).toB8L.keccak ≠ blockHeaderHash then do
    .error "ERROR : incorrect block header hash"
  let rlp' := block.toBLT.toB8L
  if blockRlp ≠ rlp' then do
    .error "ERROR : incorrect block rlp"
  let chain ←
    match state_transition vb chain block with
    | .error err => return (.inr err)
    | .ok chain => .ok chain
  cprint vb s!"\nSTATE AFTER TRANSITION :"
  cprint vb s!"{chain.state}"
  .ok (.inl chain)
