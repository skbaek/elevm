import Elevm.Types
import Elevm.EC
import Elevm.Hash

abbrev AccessList : Type := List (Adr × List B256)

instance : ToString AccessList := ⟨@List.toString _ _⟩

abbrev State : Type := Std.TreeMap Adr Acct compare

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
  | .b8s bs => some bs.toB256
  | _ => none

-- nibbles-to-bytes maps
abbrev NTB := Std.TreeMap (List B8) (List B8) (@List.compare _ ⟨B8.compareLows⟩)

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

def NTB.empty : NTB := Std.TreeMap.empty

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
  let m' ← Std.TreeMap.foldlM (insertSansPrefix pfx) NTB.empty m
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
  | n :: ns, bs => js.update (Std.TreeMap.insert · ns bs) n

def Std.TreeMap.isSingleton {K V : Type} (cmp : K → K → Ordering)
    (m : Std.TreeMap K V cmp) : Bool :=
  m.size = 1

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
                  let js := Std.TreeMap.foldl NTBs.insert NTBs.empty j
                  .list [ nodeComp k js.x0, nodeComp k js.x1, nodeComp k js.x2,
                          nodeComp k js.x3, nodeComp k js.x4, nodeComp k js.x5,
                          nodeComp k js.x6, nodeComp k js.x7, nodeComp k js.x8,
                          nodeComp k js.x9, nodeComp k js.xA, nodeComp k js.xB,
                          nodeComp k js.xC, nodeComp k js.xD, nodeComp k js.xE,
                          nodeComp k js.xF, .b8s (j.getD [] []) ]
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
  Std.TreeMap.foldl f NTB.empty s

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
  rw [Prod.ext_iff]; apply instDecidableAnd

instance : Hashable Adr := ⟨fun x => x.2.2⟩
instance : Hashable (Adr × B256) := ⟨λ x => x.1.2.2⟩

abbrev AdrSet : Type := @Std.HashSet Adr _ _
abbrev KeySet : Type := @Std.HashSet (Adr × B256) _ _

abbrev Tra : Type := Std.TreeMap Adr Stor compare

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

structure BenvStat : Type where
  chainId : B64
  origState : State
  blockGasLimit : Nat
  blockHashes: List B256
  coinbase : Adr
  number : Nat
  baseFeePerGas : Nat
  time : B256
  prevRandao : B256
  excessBlobGas : Nat
  parentBeaconBlockRoot : B256

-- class Benvironment
structure Benv : Type where
  state : State
  createdAccounts : AdrSet
  stat : BenvStat

structure TenvStat : Type where
  origin: Adr
  gasPrice: Nat
  gas: Nat
  accessListAddresses: AdrSet
  accessListStorageKeys: KeySet
  blobVersionedHashes: List B256
  auths : List Auth
  indexInBlock : Option Nat
  txHash: Option B256

-- class TransactionEnvironment
structure Tenv : Type where
  transientStorage: Tra
  stat : TenvStat

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

def Msg.withBenv (msg : Msg) (benv : Benv) : Msg :=
  {msg with benv := benv}

def Benv.withState (benv : Benv) (st : State) : Benv :=
  {benv with state := st}

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

@[ext]
structure Devm : Type where
  stack : List B256
  memory : Mem
  gasLeft : Nat
  logs : List Log
  refundCounter : Int
  output : B8L
  accountsToDelete : AdrSet
  returnData : B8L
  error : Option String
  accessedAddresses : AdrSet
  accessedStorageKeys : KeySet
  state : State
  createdAccounts : AdrSet
  transientStorage : Tra

structure Sevm : Type where
  caller : Adr
  target : Option Adr
  currentTarget : Adr
  gas : Nat
  value : B256
  data : B8L
  codeAddress : Option Adr
  code : ByteArray
  depth : Nat
  shouldTransferValue : Bool
  isStatic : Bool
  disablePrecompiles : Bool
  benvStat : BenvStat
  tenvStat : TenvStat

@[ext]
structure Evm : Type where
  pc : Nat
  sta : Sevm
  dyna : Devm

def Devm.withStack (devm : Devm) (stack : List B256) : Devm := {devm with stack := stack}
def Devm.withMemory (devm : Devm) (memory : Mem) : Devm := {devm with memory := memory}
def Devm.withGasLeft (devm : Devm) (gasLeft : Nat) : Devm := {devm with gasLeft := gasLeft}
def Devm.withLogs (devm : Devm) (logs : List Log) : Devm := {devm with logs := logs}
def Devm.withRefundCounter (devm : Devm) (refundCounter : Int) : Devm := {devm with refundCounter := refundCounter}
def Devm.withOutput (devm : Devm) (output : B8L) : Devm := {devm with output := output}
def Devm.withAccountsToDelete (devm : Devm) (accountsToDelete : AdrSet) : Devm := {devm with accountsToDelete := accountsToDelete}
def Devm.withReturnData (devm : Devm) (returnData : B8L) : Devm := {devm with returnData := returnData}
def Devm.withError (devm : Devm) (error : Option String) : Devm := {devm with error := error}
def Devm.withAccessedAddresses (devm : Devm) (accessedAddresses : AdrSet) : Devm := {devm with accessedAddresses := accessedAddresses}
def Devm.withAccessedStorageKeys (devm : Devm) (accessedStorageKeys : KeySet) : Devm := {devm with accessedStorageKeys := accessedStorageKeys}
def Devm.withState (devm : Devm) (state : State) : Devm := {devm with state := state}

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

def BenvStat.toStrings (bs : BenvStat) : List String :=
  fork "BLOCK ENVIRONMENT" [
    [s!"CHAIN ID : {bs.chainId}"],
    [s!"BLOCK GAS LIMIT : {bs.blockGasLimit}"],
    fork "BLOCK HASHES" (bs.blockHashes.map (mkSingleton ∘ B256.toHex)),
    [s!"COINBASE : {bs.coinbase}"],
    [s!"BASE FEE PER GAS : {bs.baseFeePerGas}"],
    [s!"TIME : {bs.time.toHex}"],
    [s!"PREVRANDAO : {bs.prevRandao.toHex}"],
    [s!"EXCESS BLOB GAS : {bs.excessBlobGas}"],
    [s!"PARENT BEACON BLOCK ROOT : {bs.parentBeaconBlockRoot.toHex}"]
  ]

def Benv.toStrings (benv : Benv) : List String :=
  fork "BLOCK ENVIRONMENT" [
    fork "STATE" [State.toStrings benv.state],
    fork "STAT" [benv.stat.toStrings]
  ]

def Evm.toStrings (evm : Evm) : List String :=
  fork "EVM" [
    [s!"PC : {evm.pc}"],
    Stack.toStrings evm.dyna.stack,
    Mem.toStrings evm.dyna.memory,
    [s!"CODE : {B8L.toHex evm.sta.code.toList}"],
    [s!"GAS LEFT : {evm.dyna.gasLeft}"],
    fork "LOGS" (evm.dyna.logs.map Log.toStrings),
    [s!"REFUND COUNTER : {evm.dyna.refundCounter}"],
    ["MSG : *print unimplemented*"], --Msg.toStrings evm.msg,
    [s!"output : {evm.dyna.output.toHex}"],
    fork "ACCOUNTS TO DELETE"
      (evm.dyna.accountsToDelete.toList.map (mkSingleton ∘ Adr.toHex)),
    [s!"return data : {evm.dyna.returnData.toHex}"],
    fork "ACCESSED ADDRESSES"
      (evm.dyna.accessedAddresses.toList.map (mkSingleton ∘ Adr.toHex)),
    fork "ACCESSED STORAGE KEYS"
      (evm.dyna.accessedStorageKeys.toList.map (fun kv => [s!"{kv.fst.toHex} : {B256.toHex kv.snd}"]))
  ]

abbrev Adr.isPrecomp (a : Adr) : Prop :=
  1 ≤ a.toNat ∧ a.toNat ≤ 17

def safeSub {ξ} [Sub ξ] [LE ξ] [DecidableLE ξ] (x y : ξ) : Option ξ :=
  if y ≤ x then some (x - y) else none

abbrev Execution : Type := Except (String × Devm) Devm

def chargeGas (cost : Nat) (devm : Devm) : Execution := do
  match safeSub devm.gasLeft cost with
  | none => .error ⟨"OutOfGasError", devm⟩
  | some gas => .ok {devm with gasLeft := gas}

inductive Ninst : Type
  | reg : Rinst → Ninst
  | exec : Xinst → Ninst
  | push : ∀ bs : B8L, bs.length ≤ 32 → Ninst

def Ninst.toOpString : Ninst → String
  | reg o => Rinst.toString o
  | exec o => Xinst.toString o
  | push bs _ => "PUSH" ++ bs.length.repr

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

inductive InstType
  | R | X | J | L | P

def B8.toInstType (b : B8) : InstType :=
  match b.highs with
  | 0x00 => if b.lows = 0x00 then .L else .R
  | 0x05 =>
    match b.lows with
    | 0x06 => .J
    | 0x07 => .J
    | 0x0B => .J
    | 0x0F => .P
    | _ => .R
  | 0x06 => .P
  | 0x07 => .P
  | 0x0F =>
    match b.lows with
    | 0x03 => .L
    | 0x0D => .L
    | 0x0F => .L
    | _ => .X
  | _ => .R

lemma Nat.hi_le (a b : Nat) : a ↿ b ≤ a := by
  rw [hi, shiftLeft_eq, shiftRight_eq_div_pow]
  apply Nat.div_mul_le_self

lemma B8.shl_highs_or_lows_eq_self (x : B8) : (x.highs <<< 4) ||| x.lows = x := by
  apply UInt8.toNat_inj.mp
  unfold B8.lows
  rw [UInt8.toNat_or]
  rw [UInt8.toNat_and]
  have rw : UInt8.toNat 15 = 15 := by rfl
  rw [rw]; clear rw
  rw [Nat.and_two_pow_sub_one_eq_mod _ 4]
  have hh := Nat.hi_or_lo
  rw [UInt8.toNat_shiftLeft]
  unfold B8.highs
  rw [UInt8.toNat_shiftRight]
  have rw : (UInt8.toNat 4 % 8) = 4 := by rfl
  rw [rw]; clear rw
  have hh := Nat.hi_le x.toNat 4
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt _ (UInt8.toNat_lt x))]
  · apply Nat.hi_or_lo
  · apply Nat.hi_le

lemma B8.lt_of_highs_lt_highs (x y : B8) (lt : x.highs < y.highs) : x < y := by
  rw [UInt8.lt_iff_toNat_lt]
  have lt' : x.toNat < (x.toNat ↿ 4) + 16 := by
    conv => lhs; rw [← Nat.hi_or_lo x.toNat 4]; rfl
    rw [← @Nat.add_eq_or 4]
    · rw [Nat.add_lt_add_iff_left]; apply Nat.lo_lt
    · apply Nat.two_pow_dvd_shl
    · apply Nat.lo_lt
  have le : (x.toNat ↿ 4) + 16 ≤ (y.toNat ↿ 4) := by
    simp only [Nat.hi]
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    have rw : 16 = 2 ^ 4 := by rfl
    conv => lhs; arg 2; rw [rw]; rfl
    clear rw;
    rw [← Nat.succ_mul (x.toNat >>> 4) (2 ^ 4)]
    rw [Nat.mul_le_mul_right_iff (by omega)]
    apply Nat.succ_le_of_lt lt
  have le' : (y.toNat ↿ 4) ≤ y.toNat := Nat.hi_le _ _
  apply Nat.lt_of_lt_of_le lt' <| Nat.le_trans le le'

lemma le_of_toInstType_eq_p (b : B8) (h : b.toInstType = .P) :
    b.toNat ≤ 127 := by
  apply Nat.le_of_lt_succ
  apply (@UInt8.lt_iff_toNat_lt b 0x80).mp
  apply B8.lt_of_highs_lt_highs
  simp [B8.toInstType] at h; split at h
  · split at h <;> cases h
  · rename (B8.highs _ =  _) => heq; rw [heq]
    apply (@UInt8.lt_iff_toNat_lt 5 8).mpr; simp
  · rename (B8.highs _ =  _) => heq; rw [heq]
    apply (@UInt8.lt_iff_toNat_lt 6 8).mpr; simp
  · rename (B8.highs _ =  _) => heq; rw [heq]
    apply (@UInt8.lt_iff_toNat_lt 7 8).mpr; simp
  · split at h <;> cases h
  · cases h

def ByteArray.getInst (code : ByteArray) (pc : Nat) : Option Inst :=
  if pc < code.size
  then
    let b : B8 := code.get! pc
    match h : b.toInstType with
    | .R => b.toRinst <&> (.next ∘ .reg)
    | .X => b.toXinst <&> (.next ∘ .exec)
    | .J => b.toJinst <&> .jump
    | .L => b.toLinst <&> .last
    | .P =>
      let le := le_of_toInstType_eq_p b h
      let bs : B8L := code.sliceD (pc + 1) (b.toNat - 95) 0
      let le' : bs.length ≤ 32 := by
        simp [bs, ByteArray.length_sliceD, le]
      some <| .next <| .push bs le'
  else
    some (.last .stop)

def Evm.getInst (evm : Evm) : Option Inst :=
  ByteArray.getInst evm.sta.code evm.pc

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

def Devm.push (x : B256) (devm : Devm) : Execution := do
  .assert
    (devm.stack.length < 1024)
    ⟨"StackOverflowError", devm⟩
  .ok {devm with stack := x :: devm.stack}

def Devm.pop (devm : Devm) : Except (String × Devm) (B256 × Devm) := do
  match devm.stack with
  | [] => .error ⟨"StackUnderflowError", devm⟩
  | x :: xs => .ok ⟨x, {devm with stack := xs}⟩

def Prod.mapFst {α₁ : Type u₁} {α₂ : Type u₂} {β : Type v} (f : α₁ → α₂) : α₁ × β → α₂ × β :=
  Prod.map f id

def Devm.popToNat (devm : Devm) : Except (String × Devm) (Nat × Devm) :=
  devm.pop <&> Prod.mapFst B256.toNat

def Devm.popToAdr (devm : Devm) : Except (String × Devm) (Adr × Devm) :=
  devm.pop <&> Prod.mapFst B256.toAdr

def Devm.popN (devm : Devm) : Nat → Except (String × Devm) (List B256 × Devm)
  | 0 => .ok ⟨[], devm⟩
  | n + 1 => do
    let ⟨x, devm'⟩ ← devm.pop
    let ⟨xs, devm''⟩ ← devm'.popN n
    .ok ⟨x :: xs, devm''⟩

def pushItem (x : B256) (c : Nat) (devm : Devm) : Execution := do
  chargeGas c devm >>= Devm.push x -->>= Evm.incrPc

def access_cost (x : Adr) (a : AdrSet) : Nat :=
  if x ∈ a then gasWarmAccess else gasColdAccountAccess

def addAccessedAddress (devm : Devm) (a : Adr) : Devm :=
  devm.withAccessedAddresses (devm.accessedAddresses.insert a)

def addAccessedStorageKey (devm : Devm) (a : Adr) (k : B256) : Devm :=
  devm.withAccessedStorageKeys (devm.accessedStorageKeys.insert ⟨a, k⟩)

def addAccountToDelete (devm : Devm) (a : Adr) : Devm :=
  devm.withAccountsToDelete (devm.accountsToDelete.insert a)

def addCreatedAccount (benv : Benv) (adr : Adr) : Benv :=
  {benv with createdAccounts := benv.createdAccounts.insert adr}

def Acct.nil : Acct :=
  {
    nonce := 0
    bal := 0
    stor := .empty
    code := ByteArray.mk #[]
  }

lemma Std.TreeMap.eq_empty_iff_isEmpty {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} :
    t = Std.TreeMap.empty ↔ t.isEmpty = true := by
  refine' ⟨_, eq_empty_of_isEmpty⟩; intro h; cases h; rfl

instance {stor : Stor} : Decidable (stor = .empty) := by
  simp only [Stor.empty]; rw [Std.TreeMap.eq_empty_iff_isEmpty]; infer_instance

instance {ac : Acct} : Decidable (ac = .nil) := by
  rw [Acct.ext_iff, Acct.nil]; apply instDecidableAnd

def State.get (w : State) (a : Adr) : Acct :=
  w.getD a .nil

def State.set (w : State) (a : Adr) (ac : Acct) : State :=
  if ac = .nil then w.erase a else w.insert a ac

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

def getOrigAcct (sevm : Sevm) (a : Adr) : Acct :=
  sevm.benvStat.origState.get a

def Devm.getAcct (devm : Devm) (a : Adr) : Acct :=
  devm.state.get a

def Devm.getBal (devm : Devm) (a : Adr) : B256 := (devm.getAcct a).bal
def Devm.getCode (devm : Devm) (a : Adr) : ByteArray := (devm.getAcct a).code
def Devm.getStorVal (devm : Devm) (adr : Adr) (key : B256) : B256 :=
  (devm.getAcct adr).stor.get key

def Stor.set (s : Stor) (k v : B256) : Stor :=
  if v = 0 then s.erase k else s.insert k v

def State.setStorVal (wor : State) (adr : Adr) (key val : B256) : State :=
  let acct : Acct := wor.get adr
  wor.set adr {acct with stor := acct.stor.set key val}

def Benv.setStorVal (benv : Benv) (adr : Adr) (key val : B256) : Benv :=
  {benv with state := benv.state.setStorVal adr key val}

def Devm.setStorVal (devm : Devm) (adr : Adr) (key val : B256) : Devm :=
  --devm.withBenv (devm.benv.setStorVal adr key val)
  {devm with state := devm.state.setStorVal adr key val}

def Tra.setStorVal (tra : Tra) (adr : Adr) (key val : B256) : Tra :=
  let stor : Stor := tra.getD adr .empty
  tra.set adr <| stor.set key val

def Tenv.setTransVal (tenv : Tenv) (adr : Adr) (key val : B256) : Tenv :=
  {tenv with transientStorage := tenv.transientStorage.setStorVal adr key val}

def Devm.setTransVal (devm : Devm) (adr : Adr) (key val : B256) : Devm :=
  {devm with transientStorage := devm.transientStorage.setStorVal adr key val}

def getOrigStorVal (sevm : Sevm) (adr : Adr) (key : B256) : B256 :=
  (getOrigAcct sevm adr).stor.get key

def Devm.getTransVal (devm : Devm) (adr : Adr) (key : B256) : B256 :=
  (devm.transientStorage.getD adr .empty).get key

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

def Devm.extCost (devm : Devm) (pairs : List (Nat × Nat)) : Nat :=
  let extSize := memExtsSize devm.memory.size pairs
  calculateMemoryGasCost extSize - calculateMemoryGasCost devm.memory.size

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
  match w[a]? with
  | none => True
  | some x => x.Empty

def Devm.memWrite (devm : Devm) (idx : Nat) (val : B8L) : Devm :=
  devm.withMemory <| devm.memory.write idx val

def Devm.memRead (devm : Devm) (index size : Nat) : B8L × Devm :=
  let ⟨val, mem⟩ := devm.memory.read index size
  ⟨val, devm.withMemory mem⟩

def Devm.memExtends (devm : Devm) (pairs : List (Nat × Nat)) : Devm :=
  devm.withMemory <| devm.memory.extends pairs

def Devm.addLog (devm : Devm) (log : Log) : Devm :=
  devm.withLogs <| devm.logs ++ [log]

def applyUnary (f : B256 → B256) (cost : Nat) (devm : Devm) : Execution := do
  let ⟨x, devm'⟩ ← devm.pop
  pushItem (f x) cost devm'

def applyBinary (f : B256 → B256 → B256)
  (cost : Nat) (devm : Devm) : Execution := do
  let ⟨x, devm'⟩ ← devm.pop
  let ⟨y, devm''⟩ ← devm'.pop
  pushItem (f x y) cost devm''

def applyTernary (f : B256 → B256 → B256 → B256)
  (cost : Nat) (devm : Devm) : Execution := do
  let ⟨x, devm'⟩ ← devm.pop
  let ⟨y, devm''⟩ ← devm'.pop
  let ⟨z, devm'''⟩ ← devm''.pop
  pushItem (f x y z) cost devm'''

def List.swap {ξ} : List ξ → Nat → Option (List ξ)
  | [], _ => none
  | x :: xs, k => do
    let y ← xs[k]?
    let ys := xs.set k x
    .some (y :: ys)

def Evm.contract (evm : Evm) : Adr := evm.sta.currentTarget

def assertDynamic (sevm : Sevm) (devm : Devm) : Except (String × Devm) Unit :=
  Except.assert (!sevm.isStatic) ⟨s!"WriteInStaticContext", devm⟩

def sstore_new_refund_counter (new_value : B256)
    (original_value : B256) (current_value : B256) (rc : Int) : Int :=
  if current_value ≠ new_value then
    let rc' :=
      if original_value ≠ 0 ∧ current_value ≠ 0 ∧ new_value = 0 then
        rc + rSClear
      else
        rc
    let rc'' :=
      if original_value ≠ 0 ∧ current_value = 0 then
        rc' - rSClear
      else
        rc'
    if original_value = new_value then
      if original_value = 0 then
        rc'' + (gasStorageSet - gasWarmAccess)
      else
        rc'' + (gasStorageUpdate - gasColdSload - gasWarmAccess)
    else
      rc''
  else rc

def Rinst.runCore
  (pc : Nat)
  (devm : Devm)
  (sevm : Sevm) : Rinst → Execution
  | .address => pushItem sevm.currentTarget.toB256 gBase devm
  | .basefee => pushItem sevm.benvStat.baseFeePerGas.toB256 gBase devm
  | .blobhash => do
    let ⟨x, devm⟩ ← devm.pop
    let y : B256 := sevm.tenvStat.blobVersionedHashes.getD x.toNat 0
    chargeGas gHashopcode devm >>= Devm.push y
  | .blobbasefee => do
    let fee := calculate_blob_gas_price sevm.benvStat.excessBlobGas
    pushItem fee.toB256 gBase devm
  | .balance => do
    let ⟨x, devm⟩ ← devm.pop
    let a := x.toAdr
    let devm' ←
      if a ∈ devm.accessedAddresses
      then chargeGas gasWarmAccess devm
      else chargeGas gasColdAccountAccess (addAccessedAddress devm a)
    devm'.push (devm'.getBal a)
  | .origin => pushItem sevm.tenvStat.origin.toB256 gBase devm
  | .caller => pushItem sevm.caller.toB256 gBase devm
  | .callvalue => pushItem sevm.value gBase devm
  | .calldataload => do
    let ⟨start_index, devm⟩ ← devm.pop
    let devm' ← chargeGas gVerylow devm
    let value := B8L.toB256 <| sevm.data.sliceD start_index.toNat 32 0
    devm'.push value
  | .calldatasize => pushItem sevm.data.length.toB256 gBase devm
  | .calldatacopy => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨data_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := gasCopy * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) devm
    let value := sevm.data.sliceD data_start_index size 0
    .ok <| devm.memWrite memory_start_index value
  | .codesize => pushItem sevm.code.size.toB256 gBase devm
  | .codecopy => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨code_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := gasCopy * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) devm
    let value := sevm.code.sliceD code_start_index size (Linst.toB8 .stop)
    .ok {devm with memory := devm.memory.write memory_start_index value}
  | .gasprice => pushItem sevm.tenvStat.gasPrice.toB256 gBase devm
  | .extcodesize => do
    let ⟨adr, devm⟩ ← devm.popToAdr
    let devm ←
      if adr ∈ devm.accessedAddresses
      then chargeGas gasWarmAccess devm
      else chargeGas gasColdAccountAccess (addAccessedAddress devm adr)
    let codesize := (devm.getCode adr).size.toB256
    devm.push codesize
  | .extcodecopy => do
    let ⟨adr, devm⟩ ← devm.popToAdr
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨code_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := gasCopy * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ←
      if adr ∈ devm.accessedAddresses
      then chargeGas (gasWarmAccess + copy_gas_cost + extend_memory_cost) devm
      else
        chargeGas
          (gasColdAccountAccess + copy_gas_cost + extend_memory_cost)
          (addAccessedAddress devm adr)
    let code := devm.getCode adr
    let value := code.sliceD code_start_index size (Linst.toB8 .stop)
    .ok {
      devm with
      memory := devm.memory.write memory_start_index value
    }
  | .retdatasize => pushItem devm.returnData.length.toB256 gBase devm
  | .retdatacopy => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨return_data_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := gReturnDataCopy * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) devm
    if (devm.returnData.length < return_data_start_index + size) then
      .error ⟨"OutOfBoundsRead", devm⟩
    let value :=
      devm.returnData.sliceD return_data_start_index size 0
    .ok {
      devm with
      memory := devm.memory.write memory_start_index value
    }
  | .extcodehash => do
    let ⟨adr, devm⟩ ← devm.popToAdr
    let devm ←
      if adr ∈ devm.accessedAddresses then
        chargeGas gasWarmAccess devm
      else
        chargeGas gasColdAccountAccess (addAccessedAddress devm adr)
    let account := devm.getAcct adr
    let codehash : B256 :=
      if account.Empty then 0
      else ByteArray.keccak 0 account.code.size account.code
    devm.push codehash
  | .selfbalance => pushItem (devm.getBal sevm.currentTarget) gLow devm
  | .chainid => pushItem sevm.benvStat.chainId.toB256 gBase devm
  | .number => pushItem sevm.benvStat.number.toB256 gBase devm
  | .timestamp => pushItem sevm.benvStat.time gBase devm
  | .gaslimit => pushItem sevm.benvStat.blockGasLimit.toB256 gBase devm
  | .prevrandao => pushItem sevm.benvStat.prevRandao gBase devm
  | .coinbase => pushItem sevm.benvStat.coinbase.toB256 gBase devm
  | .msize => pushItem devm.memory.size.toB256 gBase devm
  | .mload => do
    let ⟨start_index, devm⟩ ← devm.popToNat
    let extend_memory_cost := devm.extCost [⟨start_index, 32⟩]
    let devm ← chargeGas (gVerylow + extend_memory_cost) devm
    let ⟨value, devm⟩ := devm.memRead start_index 32
    devm.push (B8L.toB256 value)
  | .mstore => do
    let ⟨start_index, devm⟩ ← devm.popToNat
    let ⟨value, devm⟩ ← devm.pop
    let extend_memory_cost := devm.extCost [⟨start_index, 32⟩]
    let devm ← chargeGas (gVerylow + extend_memory_cost) devm
    .ok <| devm.memWrite start_index value.toB8L
  | .mstore8 => do
    let ⟨start_index, devm⟩ ← devm.popToNat
    let ⟨value, devm⟩ ← devm.pop
    let extend_memory_cost := devm.extCost [⟨start_index, 1⟩]
    let devm ← chargeGas (gVerylow + extend_memory_cost) devm
    .ok <| devm.memWrite start_index [value.2.2.toUInt8]
  | .gas => do
    let devm ← chargeGas gBase devm
    devm.push devm.gasLeft.toB256
  | .eq => applyBinary .eq_check gVerylow devm
  | .lt => applyBinary .lt_check gVerylow devm
  | .gt => applyBinary .gt_check gVerylow devm
  | .slt => applyBinary .slt_check gVerylow devm
  | .sgt => applyBinary .sgt_check gVerylow devm
  | .iszero => applyUnary (.eq_check · 0) gVerylow devm
  | .not => applyUnary (~~~ ·) gVerylow devm
  | .and => applyBinary B256.and gVerylow devm
  | .or => applyBinary B256.or gVerylow devm
  | .xor => applyBinary B256.xor gVerylow devm
  | .signextend => applyBinary B256.signext gLow devm
  | .pop => (devm.pop <&> Prod.snd) >>= chargeGas gBase
  | .byte =>
    applyBinary (λ x y => (List.getD y.toB8L x.toNat 0).toB256) gVerylow devm
  | .shl => applyBinary (fun x y => y <<< x.toNat) gVerylow devm
  | .shr => applyBinary (fun x y => y >>> x.toNat) gVerylow devm
  | .sar => applyBinary (fun x y => B256.arithShiftRight y x.toNat) gVerylow devm
  | .kec => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let word_gas_cost := gasKeccak256Word * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas (gKeccak256 + word_gas_cost + extend_memory_cost) devm
    let ⟨arg, devm⟩ := devm.memRead memory_start_index size
    devm.push arg.keccak
  | .sub => applyBinary (· - ·) gVerylow devm
  | .mul => applyBinary (· * ·) gLow devm
  | .exp => do
    let ⟨base, devm⟩ ← devm.pop
    let ⟨exponent, devm⟩ ← devm.pop
    let devm ← chargeGas (gExp + (gExpbyte * exponent.bytecount)) devm
    devm.push (B256.bexp base exponent)
  | .div => applyBinary (· / ·) gLow devm
  | .sdiv => applyBinary B256.sdiv gLow devm
  | .mod => applyBinary (· % ·) gLow devm
  | .smod => applyBinary B256.smod gLow devm
  | .add => applyBinary (· + ·) gVerylow devm
  | .addmod => applyTernary B256.addmod gMid devm
  | .mulmod => applyTernary B256.mulmod gMid devm
  | .swap n => do
    let devm ← chargeGas gVerylow devm
    match List.swap devm.stack n with
    | none => .error ⟨"StackUnderflowError", devm⟩
    | some stack => .ok {devm with stack := stack}
  | .dup n => do
    let devm ← chargeGas gVerylow devm
    match devm.stack[n]? with
    | none => .error ⟨"StackUnderflowError", devm⟩
    | some word => devm.push word
  | .sload => do
    let ⟨key, devm⟩ ← devm.pop
    let ct := sevm.currentTarget
    let devm ←
      if ⟨ct, key⟩ ∈ devm.accessedStorageKeys then
        chargeGas gasWarmAccess devm
      else
        chargeGas gasColdSload
          (addAccessedStorageKey devm ct key)
    devm.push (devm.getStorVal ct key)
  | .tload => do
    let ⟨key, devm⟩ ← devm.pop
    pushItem (devm.getTransVal sevm.currentTarget key) gasWarmAccess devm
  | .pc => pushItem pc.toB256 gBase devm
  | .sstore => do
    let ⟨key, devm1⟩ ← devm.pop
    let ⟨new_value, devm2⟩ ← devm1.pop
    .assert
      (gCallStipend < devm2.gasLeft)
      ⟨"OutOfGasError", devm2⟩
    let ct := sevm.currentTarget
    let original_value := getOrigStorVal sevm ct key
    let current_value := devm2.getStorVal ct key
    let ⟨devm3, gasCost2⟩ ← .ok <|
      if ⟨ct, key⟩ ∉ devm2.accessedStorageKeys then
        ( ⟨ addAccessedStorageKey devm2 ct key,
            gasColdSload ⟩ : Devm × Nat )
      else
        ⟨devm2, 0⟩
    let gasCost3 ← .ok <|
      if original_value = current_value ∧ current_value ≠ new_value then
        if original_value = 0 then
          gasCost2 + gasStorageSet
        else
          gasCost2 + (gasStorageUpdate - gasColdSload)
      else
        gasCost2 + gasWarmAccess
    let devm4 ← .ok <|
      { devm3 with
        refundCounter :=
          sstore_new_refund_counter
            new_value
            original_value
            current_value
            devm3.refundCounter }
    let devm5 ← chargeGas gasCost3 devm4
    assertDynamic sevm devm5
    .ok (devm5.setStorVal sevm.currentTarget key new_value)
  | .tstore => do
    let ⟨key, devm⟩ ← devm.pop
    let ⟨new_value, devm⟩ ← devm.pop
    let devm ← chargeGas gasWarmAccess devm
    assertDynamic sevm devm
    .ok (devm.setTransVal sevm.currentTarget key new_value)
  | .mcopy => do
    let ⟨destination, devm⟩ ← devm.popToNat
    let ⟨source, devm⟩ ← devm.popToNat
    let ⟨length, devm⟩ ← devm.popToNat
    let words := ceilDiv length 32
    let copy_gas_cost := gasCopy * words
    let extend_memory_cost :=
      devm.extCost [⟨source, length⟩, ⟨destination, length⟩]
    let devm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) devm
    let ⟨value, devm⟩ := devm.memRead source length
    .ok (devm.memWrite destination value)
  | .log n => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let ⟨topics, devm⟩ ← devm.popN n
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ←
      chargeGas
        (gLog + (gLogdata * size) + (gLogtopic * n) + extend_memory_cost)
        devm
    assertDynamic sevm devm
    let ⟨data, devm⟩ := devm.memRead memory_start_index size
    let log : Log := ⟨sevm.currentTarget, topics, data⟩
    .ok (devm.addLog log)
  | .blockhash => do
    let ⟨blockNumberWord, devm⟩ ← devm.pop
    let blockNumber := blockNumberWord.toNat
    let devm ← chargeGas gBlockhash devm
    let maxBlockNumber := blockNumber + 256
    let hash : B256 :=
      if sevm.benvStat.number ≤ blockNumber ∨ maxBlockNumber < sevm.benvStat.number
      then 0
      else
        sevm.benvStat.blockHashes.getD
          (sevm.benvStat.blockHashes.length - (sevm.benvStat.number - blockNumber))
          0
    devm.push hash

def Rinst.run (evm : Evm) := Rinst.runCore evm.pc evm.dyna evm.sta

instance : Inhabited BenvStat := ⟨
  {
    chainId := 0
    origState := .empty
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
instance : Inhabited Benv := ⟨
  {
    state := .empty
    createdAccounts := .emptyWithCapacity
    stat := default
  }
⟩

instance : Inhabited TenvStat := ⟨
  {
    origin := 0
    gasPrice := 0
    gas := 0
    accessListAddresses := .emptyWithCapacity
    accessListStorageKeys := .emptyWithCapacity
    blobVersionedHashes := []
    auths := []
    indexInBlock := none
    txHash := none
  }
⟩
instance : Inhabited Tenv := ⟨
  {
    transientStorage := .empty
    stat := default
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
      depth := 1024
      shouldTransferValue := false
      isStatic := false
      accessedAddresses := .emptyWithCapacity
      accessedStorageKeys := .emptyWithCapacity
      disablePrecompiles := false
    }
  ⟩

instance : Inhabited Devm := ⟨
  {
    stack := []
    memory := ⟨.empty, 0⟩
    gasLeft := 0
    logs := []
    refundCounter := 0
    output := []
    accountsToDelete := .emptyWithCapacity
    returnData := []
    error := .none
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := .emptyWithCapacity
    state := .empty
    createdAccounts := .emptyWithCapacity
    transientStorage := default
  }
⟩


instance : Inhabited Sevm := ⟨
  {
    caller := 0
    target := .none
    currentTarget := 0
    gas := 0
    value := 0
    data := []
    codeAddress := .none
    code := .empty
    depth := 1024
    shouldTransferValue := false
    isStatic := false
    disablePrecompiles := false
    benvStat := default
    tenvStat := default
  }
⟩

instance : Inhabited Evm := ⟨
  {
    pc := 0
    sta := default
    dyna := default
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

def Jinst.runCore (pc : Nat) (devm : Devm) (sevm : Sevm) :
    Jinst → Except (String × Devm) (Nat × Devm)
  | .jumpdest => do
    let devm' ← chargeGas gJumpdest devm
    .ok ⟨pc + 1, devm'⟩
  | .jump => do
    let ⟨jump_dest, devm'⟩ ← devm.pop
    let devm'' ← chargeGas gMid devm'
    .assert
      (jumpable sevm.code jump_dest.toNat)
      ⟨"InvalidJumpDestError", devm''⟩
    .ok ⟨jump_dest.toNat, devm''⟩
  | .jumpi => do
    let ⟨dest, devm'⟩ ← devm.pop
    let ⟨cond, devm''⟩ ← devm'.pop
    let devm''' ← chargeGas gHigh devm''
    let pc' : Nat ←
      if cond = 0
      then .ok <| pc + 1
      else
        .assert
          (jumpable sevm.code dest.toNat)
          ⟨"InvalidJumpDestError", devm'''⟩
        .ok dest.toNat
    .ok ⟨pc', devm'''⟩

def Jinst.run (evm : Evm) (j : Jinst) : Except (String × Devm) (Nat × Devm) :=
  Jinst.runCore evm.pc evm.dyna evm.sta j

def State.bal (w : State) (a : Adr) : B256 := (w.get a).bal

def State.setBal (st : State) (adr : Adr) (val : B256) : State :=
  -- let acct := wor.get adr
  --wor.set adr {acct with bal := val}
  st.set adr <| (st.get adr).withBal val

def State.addBal (st : State) (adr : Adr) (val : B256) : State :=
  -- let acct := wor.get adr
  -- wor.set adr {acct with bal := acct.bal + val}
  st.setBal adr <| (st.bal adr + val)


def State.subBal (st : State) (adr : Adr) (val : B256) : Option State :=
  -- let acct := wor.get adr
  -- if acct.bal < val
  -- else wor.set adr {acct with bal := acct.bal - val}
  if st.bal adr < val
  then .none
  else st.setBal adr (st.bal adr - val)

def Benv.setBal (benv : Benv) (adr : Adr) (val : B256) : Benv :=
  {benv with state := benv.state.setBal adr val}

def Benv.subBal (benv : Benv) (adr : Adr) (val : B256) : Option Benv := do
  let wor ← benv.state.subBal adr val
  some <| benv.withState wor

def Benv.addBal (benv : Benv) (adr : Adr) (val : B256) : Benv :=
  benv.withState (benv.state.addBal adr val)

-- def Msg.setBal (msg : Msg) (adr : Adr) (val : B256) : Msg :=
--   {msg with benv := msg.benv.setBal adr val}

def Devm.setBal (devm : Devm) (adr : Adr) (val : B256) : Devm :=
  --{devm with benv := devm.benv.setBal adr val}
  {devm with state := devm.state.setBal adr val}

-- def Msg.subBal (msg : Msg) (adr : Adr) (val : B256) : Option Msg := do
--   let benv ← msg.benv.subBal adr val
--   some {msg with benv := benv}

def Devm.subBal (devm : Devm) (adr : Adr) (val : B256) : Option Devm := do
  -- let benv ← devm.benv.subBal adr val
  -- some {devm with benv := benv}
  let state ← devm.state.subBal adr val
  some <| devm.withState state

--def Msg.addBal (msg : Msg) (adr : Adr) (val : B256) : Msg :=
--  {msg with benv := msg.benv.addBal adr val}

def Devm.addBal (devm : Devm) (adr : Adr) (val : B256) : Devm :=
  --{devm with benv := devm.benv.addBal adr val}
  devm.withState (devm.state.addBal adr val)

def Linst.run (sevm : Sevm) (devm : Devm) :
    Linst → Except (String × Devm) Devm
  | .stop => .ok devm
  | .rev => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas extend_memory_cost devm
    let ⟨output, devm⟩ := devm.memRead memory_start_index size
    let devm := {devm with output := output}
    .error ⟨"Revert", devm⟩
  | .ret => do
    let ⟨index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let cost := devm.extCost [⟨index, size⟩]
    let devm ← chargeGas cost devm
    let ⟨output, devm⟩ := devm.memRead index size
    .ok {devm with output := output}
  | .dest => do
    let donor := sevm.currentTarget
    let ⟨donee, devm1⟩ ← devm.popToAdr
    let donorBal ← .ok (devm1.getAcct sevm.currentTarget).bal
    let ⟨devm2, gasCost2⟩ ← .ok <|
      if donee ∉ devm1.accessedAddresses
        then
          ( ⟨ addAccessedAddress devm1 donee,
              gasSelfDestruct + gasColdAccountAccess ⟩ : Devm × Nat )
        else
          ⟨devm1, gasSelfDestruct⟩
    let gasCost3 ← .ok <|
      if (devm2.getAcct donee).Empty ∧ donorBal ≠ 0 then
        gasCost2 + gasSelfDestructNewAccount
      else
        gasCost2
    let devm3 ← chargeGas gasCost3 devm2
    assertDynamic sevm devm3
    let devm4 ←
      (devm3.subBal donor donorBal).toExcept
        ⟨"ERROR : InsufficientBalanceError", devm3⟩
    let devm5 ← .ok <| devm4.addBal donee donorBal
    if donor ∈ devm5.createdAccounts then
      .ok (addAccountToDelete (devm5.setBal donor 0) donor)
    else
      .ok devm5

def except64th (n : Nat) : Nat := n - (n / 64)

def calculateMsgCallGas
  (value gas gas_left memory_cost extra_gas : Nat)
  (cs : Nat := gCallStipend) : Nat × Nat :=
  let call_stipend : Nat := if value = 0 then 0 else cs
  if gas_left < extra_gas + memory_cost
  then ⟨gas + extra_gas, gas + call_stipend⟩
  else
    let gas' := min gas (except64th (gas_left - memory_cost - extra_gas))
    ⟨gas' + extra_gas, gas' + call_stipend⟩

def incorporateChildOnError (parent child : Devm) (returnData : B8L) : Devm :=
  {
    parent with
    gasLeft := parent.gasLeft + child.gasLeft
    state := child.state
    createdAccounts := child.createdAccounts
    transientStorage := child.transientStorage
    returnData := returnData
  }

def incorporateChildOnSuccess (parent child : Devm) (returnData : B8L) : Devm :=
  {
    parent with
    gasLeft := parent.gasLeft + child.gasLeft
    state := child.state
    createdAccounts := child.createdAccounts
    transientStorage := child.transientStorage
    logs := parent.logs ++ child.logs
    refundCounter := parent.refundCounter + child.refundCounter
    accountsToDelete := parent.accountsToDelete.union child.accountsToDelete
    returnData := returnData
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

def Devm.incrNonce (devm : Devm) (adr : Adr) : Devm :=
  {devm with state := devm.state.incrNonce adr}

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

def Devm.setCode (devm : Devm) (adr : Adr) (code : ByteArray) : Devm :=
  --{devm with benv := {devm.benv with state := devm.benv.state.setCode adr code}}
  {devm with state := devm.state.setCode adr code}

def Devm.rollback (devm : Devm) (wor : State) (tra : Tra) : Devm :=
  {
    devm with
    state := wor,
    transientStorage := tra
  }

def liftToExecution (devm : Devm)
  (f : Except (String × State × AdrSet × Tra) Devm) : Execution := do
  match f with
  | .error ⟨err, state, createdAccounts, tra⟩ =>
    let devm' := {
      devm with
      state := state
      createdAccounts := createdAccounts
      transientStorage := tra
    }
    .error ⟨err, devm'⟩
  | .ok devm' => .ok devm'

inductive PrecompResult
| error (msg : String) (cost : Nat)
| ok (cost : Nat) (output : B8L)

def PrecompResult.chargeGas (cost : Nat) (evm : Evm)
    (pr : Unit → PrecompResult) : PrecompResult :=
  if cost ≤ evm.dyna.gasLeft then pr () else .error "OutOfGasError" 0

def executeEcrecover (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  PrecompResult.chargeGas gasEcrecover evm fun () =>
    let h := B8L.toB256 <| data.sliceD 0 32 (0x00 : B8)
    let v_opt := match (B8L.toB256 <| data.sliceD 32 32 (0x00 : B8)) with
                 | 0x1B => some false
                 | 0x1C => some true
                 | _ => none
    match v_opt with
    | none => .ok gasEcrecover []
    | some v =>
      let r := B8L.toB256 <| data.sliceD 64 32 (0x00 : B8)
      let s := B8L.toB256 <| data.sliceD 96 32 (0x00 : B8)
      if r = 0 ∨ s = 0 ∨
         r ≥ secp256k1.curveOrder.toB256 ∨
         s ≥ secp256k1.curveOrder.toB256 then
        .ok gasEcrecover []
      else
        match secp256k1.recover h v r s with
        | .none => .ok gasEcrecover []
        | some adr => .ok gasEcrecover adr.toB256.toB8L

def executeSha256 (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  let cost : Nat := 60 + (12 * (ceilDiv data.length 32))
  PrecompResult.chargeGas cost evm fun () => .ok cost (B8L.sha256 data).toB8L

def executeRipemd160 (evm : Evm) : PrecompResult :=
  let data : B8L := evm.sta.data
  let cost : Nat := 600 + (120 * (ceilDiv data.length 32))
  PrecompResult.chargeGas cost evm fun () =>
    let hash : B8L := data.ripemd160
    let output : B8L := B256.toB8L <| (B8L.toB256 <| hash)
    .ok cost output

def executeId (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  let cost := 15 + (3 * (ceilDiv data.length 32))
  PrecompResult.chargeGas cost evm fun () => .ok cost data

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

def executeModexp (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  let baseLength : Nat := B8L.sliceToNat data 0 32
  let expLength : Nat := B8L.sliceToNat data 32 32
  let modulusLength : Nat := B8L.sliceToNat data 64 32
  let expHead : Nat := B8L.sliceToNat data (96 + baseLength) (min 32 expLength)
  let cost : Nat := modexpGascost baseLength modulusLength expLength expHead
  PrecompResult.chargeGas cost evm fun () =>
    if baseLength = 0 ∧ modulusLength = 0 then .ok cost []
    else
      let base : Nat := B8L.sliceToNat data 96 baseLength
      let exp : Nat := B8L.sliceToNat data (96 + baseLength) expLength
      let modulus : Nat := B8L.sliceToNat data (96 + baseLength + expLength) modulusLength
      let output :=
        if modulus = 0 then List.replicate modulusLength (0x00 : B8)
        else (Nat.powMod base exp modulus).toB8L.pack modulusLength
      .ok cost output

def executeEcadd (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  PrecompResult.chargeGas 150 evm fun () =>
    let x0 : Nat := B8L.toNat <| data.sliceD 0 32 (0 : B8)
    let y0 : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
    let x1 : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)
    let y1 : Nat := B8L.toNat <| data.sliceD 96 32 (0 : B8)
    if ¬ (x0 < altBn128Prime ∧ y0 < altBn128Prime ∧ x1 < altBn128Prime ∧ x1 < altBn128Prime) then
      .error "OutOfGasError" 150
    else
      match BNP.mk? x0 y0 with
      | none => .error "OutOfGasError" 150
      | some p0 =>
        match BNP.mk? x1 y1 with
        | none => .error "OutOfGasError" 150
        | some p1 => .ok 150 (BNP.toB8L (p0 + p1))

def executeEcmul (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  PrecompResult.chargeGas 6000 evm fun () =>
    let x : Nat := B8L.toNat <| data.sliceD 0 32 (0 : B8)
    let y : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
    let n : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)
    if ¬ (x < altBn128Prime ∧ y < altBn128Prime) then
      .error "OutOfGasError" 6000
    else
      match BNP.mk? x y with
      | none => .error "OutOfGasError" 6000
      | some p => .ok 6000 (BNP.toB8L (p * n))

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
def spit_le_to_B64 (data : B8L) : Nat → Nat → List B64
  | _, 0 => []
  | start, num_words + 1 =>
    let wordBytes := data.sliceD start 8 (0x00 : B8)
    let word := B8L.toB64 wordBytes.reverse
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
def executeBlake2F (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 213 then .error "InvalidParameter" 0
  else
    let ⟨rounds, h, m, t0, t1, fn⟩ := getBlake2Parameters data
    let cost := gasBlake2PerRound * rounds
    PrecompResult.chargeGas cost evm fun () =>
      match fn with
      | 0 =>
        match bCompress rounds h m t0 t1 false with
        | some output => .ok cost output
        | none => .error "bCompress failed" cost
      | 1 =>
        match bCompress rounds h m t0 t1 true with
        | some output => .ok cost output
        | none => .error "bCompress failed" cost
      | _ => .error "InvalidParameter" cost

def executePointEval (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 192 then .error "KZGProofError" 0
  else .error "UNIMP : executePointEval" 0

def gasBlsG1Mul : Nat := 12000
def gasBlsG1Map : Nat := 5500
def gasBlsG2Add : Nat := 600
def gasBlsG2Mul : Nat := 22500
def gasBlsG2Map : Nat := 23800

-- bls12_g1_add
def executeBls12G1Add (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 256 then .error "InvalidParameter" 0
  else .error "BLS12 G1 Add not implemented yet" 0

-- bls12_g1_msm
def executeBls12G1Msm (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length = 0 ∨ data.length % lengthPerPair ≠ 0 then
    .error s!"InvalidParameter : {data.length} is not a valid input lnegth" 0
  else
    let k := data.length / lengthPerPair
    let discount := List.getD g1KDiscount (k - 1) g1MaxDiscount
    let gasCost := (k * gasBlsG1Mul * discount) / 1000
    PrecompResult.chargeGas gasCost evm fun () =>
      .error "BLS12 G1 msm not implemented yet" gasCost

-- bls12_g2_add
def executeBls12G2Add (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 512 then .error "InvalidParameter" 0
  else
    PrecompResult.chargeGas gasBlsG2Add evm fun () =>
      .error "BLS12 G2 add not implemented yet" gasBlsG2Add

-- def bls12_g2_msm
def executeBls12G2Msm (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length = 0 ∨ data.length % lengthPerPair ≠ 0 then
    .error s!"InvalidParameter : {data.length} is not a valid input length" 0
  else
    let k := data.length / lengthPerPair
    let discount := List.getD g2KDiscount (k - 1) g2MaxDiscount
    let gasCost := (k * gasBlsG2Mul * discount) / 1000
    PrecompResult.chargeGas gasCost evm fun () =>
      .error "BLS12 G2 msm not implemented yet" gasCost

-- def bls12_pairing(evm : Evm) -> None :
def executeBls12Pairing (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length = 0 ∨ data.length % 384 ≠ 0 then
    .error s!"InvalidParameter : {data.length} is not a valid input length" 0
  else
    let k := data.length / 384
    let gasCost := (32600 * k + 37700)
    PrecompResult.chargeGas gasCost evm fun () =>
      .error "BLS12 pairing not implemented yet" gasCost

-- def bls12_map_fp_to_g1(evm : Evm) -> None :
def executeBls12MapFpToG1 (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 64 then .error "InvalidParameter" 0
  else
    PrecompResult.chargeGas gasBlsG1Map evm fun () =>
      .error "BLS12 map FP-to-G1 Msm not implemented yet" gasBlsG1Map

def catchWithOOG {ξ : Type U} (devm : Devm) (cond : String → Bool) :
  Except String ξ → Except (String × Devm) ξ
  | .ok v => .ok v
  | .error e =>
    if cond e then
      .error ⟨"OutOfGasError", devm⟩
    else
      .error ⟨e, devm⟩

-- def bytes_to_g1(data : Bytes) -> Point3D[FQ]:
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

-- def bytes_to_g2(data : Bytes) -> Point3D[FQ2]:
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

def catchWithOOGPrecomp {ξ} (cost : Nat) (cond : String → Bool) :
  Except String ξ → Except (String × Nat) ξ
  | .ok v => .ok v
  | .error e => if cond e then .error ⟨"OutOfGasError", cost⟩ else .error ⟨e, cost⟩

-- def bls12_map_fp2_to_g2(evm : Evm) -> None :
def executeBls12MapFp2ToG2 (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 128 then .error "InvalidParameter" 0
  else
    PrecompResult.chargeGas gasBlsG2Map evm fun () =>
      .error "main logic of BLS12 map FP2-to_G2 not implemented yet" gasBlsG2Map

def executePairingCheckInner (data : B8L) (cost : Nat) :
    Except (String × Nat) (Nat × B8L) := do
  if data.length % 192 ≠ 0 then throw ⟨"OutOfGasError", cost⟩
  let mut result : BNF12 := 1
  for i in List.range (data.length / 192) do
    let p : BNP ←
      catchWithOOGPrecomp cost (hasErrorType · "InvalidParameter") <|
        B8L.toExStrBNP (data.slice! (i * 192) 64)
    let q : BNP2 ←
      catchWithOOGPrecomp cost (hasErrorType · "InvalidParameter") <|
        B8L.toExStrBNP2 (data.slice! (i * 192 + 64) 128)
    if p * altBn128CurveOrder ≠ ⟨0, 0⟩ then throw ⟨"OutOfGasError", cost⟩
    if q * altBn128CurveOrder ≠ ⟨0, 0⟩ then throw ⟨"OutOfGasError", cost⟩
    let pairResult ← match pairing q p with
                     | some v => pure v
                     | none => throw ⟨"ValueError", cost⟩
    result := result * pairResult
  let output : B8L := if result = 1 then (1 : Nat).toB256.toB8L else (0 : Nat).toB256.toB8L
  pure (cost, output)

def executePairingCheck (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  let cost := (34000 * (data.length / 192)) + 45000
  PrecompResult.chargeGas cost evm fun () =>
    -- let inner : Except (String × Nat) (Nat × B8L) := do
    --   if data.length % 192 ≠ 0 then throw ⟨"OutOfGasError", cost⟩
    --   let mut result : BNF12 := 1
    --   for i in List.range (data.length / 192) do
    --     let p : BNP ←
    --       catchWithOOGPrecomp cost (hasErrorType · "InvalidParameter") <|
    --         B8L.toExStrBNP (data.slice! (i * 192) 64)
    --     let q : BNP2 ←
    --       catchWithOOGPrecomp cost (hasErrorType · "InvalidParameter") <|
    --         B8L.toExStrBNP2 (data.slice! (i * 192 + 64) 128)
    --     if p * altBn128CurveOrder ≠ ⟨0, 0⟩ then throw ⟨"OutOfGasError", cost⟩
    --     if q * altBn128CurveOrder ≠ ⟨0, 0⟩ then throw ⟨"OutOfGasError", cost⟩
    --     let pairResult ← match pairing q p with
    --                      | some v => pure v
    --                      | none => throw ⟨"ValueError", cost⟩
    --     result := result * pairResult
    --   let output : B8L := if result = 1 then (1 : Nat).toB256.toB8L else (0 : Nat).toB256.toB8L
    --   pure (cost, output)
    let inner := executePairingCheckInner data cost
    match inner with
    | .ok ⟨cost, output⟩ => .ok cost output
    | .error ⟨msg, cost⟩ => .error msg cost

def precompileRun (evm : Evm) : Adr → PrecompResult
  | 1 => executeEcrecover evm -- 0x1
  | 2 => executeSha256 evm -- 0x2
  | 3 => executeRipemd160 evm -- 0x3
  | 4 => executeId evm -- 0x4
  | 5 => executeModexp evm -- 0x5
  | 6 => executeEcadd evm -- 0x6
  | 7 => executeEcmul evm -- 0x7
  | 8 => executePairingCheck evm --  0x8
  | 9 => executeBlake2F evm -- 0x9
  | 10 => executePointEval evm -- 0xA
  | 11 => executeBls12G1Add evm --  0xB
  | 12 => executeBls12G1Msm evm --  0xC
  | 13 => executeBls12G2Add evm --  0xD
  | 14 => executeBls12G2Msm evm --  0xE
  | 15 => executeBls12Pairing evm -- 0xF
  | 16 => executeBls12MapFpToG1 evm -- 0x10
  | 17 => executeBls12MapFp2ToG2 evm -- 0x11
  | n => .error s!"ERROR : precompiled contract {n} does not exist" 0

def applyPrecompResult (evm : Evm) (res : PrecompResult) : Execution :=
  match res with
  | .error msg cost => .error ⟨msg, { evm.dyna with gasLeft := evm.dyna.gasLeft - cost }⟩
  | .ok cost output => .ok { evm.dyna with gasLeft := evm.dyna.gasLeft - cost, output := output }

def executePrecomp (evm : Evm) (adr : Adr) : Execution :=
  applyPrecompResult evm (precompileRun evm adr)

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
    s!"gas({evm.dyna.gasLeft}), " ++
    s!"op(\"{i.toOpString}\"), " ++
    s!"depth({evm.sta.depth}), " ++
    s!"{List.toStringSingleQuote <| evm.dyna.stack.map (fun x => "0x" ++ x.toHex.dropZeroes)}" ++
  ")."

def showStep (evm : Evm) (i : Inst) : Except (Evm × String) Unit :=
  if verbose ()
  then do
    .print (stepString evm i)
    .ok ()
  else .ok ()

def showLim (lim : Nat) (evm : Evm) : Except (Evm × String) Unit := do
  if lim % 100000 = 0 then
    .print s!"Recursion limit = {lim}, gas left = {evm.dyna.gasLeft}"

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
def accessDelegation (devm : Devm) (adr : Adr) :
  Bool × Adr × ByteArray × Nat × Devm :=
  let state := devm.state
  let code := state.getCode adr
  if isValidDelegation code
  then
    let adr :=
      (code.sliceD eoaDelegationMarker.length 20 (0 : B8)).toAdr?.get!
    let accessGasCost := access_cost adr devm.accessedAddresses
    let devm := addAccessedAddress devm adr
    let code := state.getCode adr
    ⟨true, adr, code, accessGasCost, devm⟩
  else ⟨false, adr, code, 0, devm⟩

def processCreateMessage.msg (msg : Msg) : Msg :=
  let adr := msg.currentTarget
  let benv := msg.benv.setStor adr .empty
  let benv := addCreatedAccount benv adr
  let benv := benv.incrNonce adr
  msg.withBenv benv

def processCreateMessage.chargeCodeGas (devm : Devm) : Execution :=
  let contractCode := devm.output
  let contractCodeGas := contractCode.length * gasCodeDeposit
  match contractCode with
  | 0xEF :: _ => .error ⟨"InvalidContractPrefix", devm⟩
  | _ => do
    let devm ← chargeGas contractCodeGas devm
    if maxCodeSize < contractCode.length
    then .error ⟨"OutOfGasError", devm⟩
    else .ok devm

def processCreateMessage.exceptionalHalt
    (devm : Devm) (err : String) (st : State) (tra : Tra) : Devm :=
  {devm.rollback st tra with gasLeft := 0, output := [], error := .some err}

def initSevm (msg : Msg) : Sevm :=
  {
    caller := msg.caller
    target := msg.target
    currentTarget := msg.currentTarget
    gas := msg.gas
    value := msg.value
    data := msg.data
    codeAddress := msg.codeAddress
    code := msg.code
    depth := msg.depth
    shouldTransferValue := msg.shouldTransferValue
    isStatic := msg.isStatic
    disablePrecompiles := msg.disablePrecompiles
    benvStat := msg.benv.stat
    tenvStat := msg.tenv.stat
  }

def initDevm (msg : Msg) : Devm :=
  {
    stack := []
    memory := .empty
    gasLeft := msg.gas
    logs := []
    refundCounter := 0
    output := []
    accountsToDelete := .emptyWithCapacity
    returnData := []
    error := .none
    accessedAddresses := msg.accessedAddresses
    accessedStorageKeys := msg.accessedStorageKeys
    state := msg.benv.state
    createdAccounts := msg.benv.createdAccounts
    transientStorage := msg.tenv.transientStorage
  }

def initEvm (msg : Msg) : Evm :=
  {
    pc := 0
    sta := initSevm msg
    dyna := initDevm msg
  }

def Msg.benvAfterTransfer (msg : Msg) :
    Except (String × State × AdrSet × Tra) Benv :=
  if msg.shouldTransferValue then do
    let benv ←
      (msg.benv.subBal msg.caller msg.value).toExcept
        ⟨"AssertionError", msg.benv.state, msg.benv.createdAccounts, msg.tenv.transientStorage⟩
    .ok <| benv.addBal msg.currentTarget msg.value
  else
    .ok msg.benv

def executeCode.handleError :
    Execution → Except (String × State × AdrSet × Tra) Devm
  | .ok evm => .ok evm
  | .error ⟨err, evm⟩ =>
    if isExceptionalHalt err
    then .ok {evm with gasLeft := 0, output := [], error := some err}
    else
      if err = "Revert"
      then .ok {evm with error := some "Revert"}
      else .error ⟨err, evm.state, evm.createdAccounts, evm.transientStorage⟩

def Execution.withPc (pc : Nat) (exn : Execution) :
     Except (String × Devm) (Nat × Devm) := do
  let devm ← exn
  .ok ⟨pc, devm⟩

def Ninst.size : Ninst → Nat
  | reg _ => 1
  | exec _ => 1
  | push xs _ => xs.length + 1

-- the message passed to the sub-call performed by a call-type instruction.
-- factored out as a named definition to prevent context blowup in proofs.
def callMsg
    (sevm: Sevm)
    (evm1: Devm)
    (gas: Nat)
    (value: B256)
    (caller: Adr)
    (target: Adr)
    (codeAddress: Adr)
    (shouldTransferValue: Bool)
    (isStaticcall: Bool)
    (calldata: B8L)
    (code : ByteArray)
    (disablePrecompiles: Bool) : Msg :=
  {
    benv := {state := evm1.state, createdAccounts := evm1.createdAccounts, stat := sevm.benvStat}
    tenv := {transientStorage := evm1.transientStorage, stat := sevm.tenvStat}
    caller := caller
    target := target
    gas := gas
    currentTarget := target
    value := value
    data := calldata
    codeAddress := codeAddress
    code := code
    depth := sevm.depth - 1
    shouldTransferValue := shouldTransferValue
    isStatic := isStaticcall || sevm.isStatic
    accessedAddresses := evm1.accessedAddresses
    accessedStorageKeys := evm1.accessedStorageKeys
    disablePrecompiles := disablePrecompiles
  }

mutual

  def executeCode (msg : Msg) :
    Nat → Except (String × State × AdrSet × Tra) Devm
    | 0 =>
      .error ⟨
        "RecursionLimit",
        msg.benv.state,
        msg.benv.createdAccounts,
        msg.tenv.transientStorage
      ⟩
    | lim + 1 => do
      let evm : Evm := initEvm msg
      match msg.codeAddress with
      | .none =>
        executeCode.handleError <| exec evm lim
      | .some adr =>
        if adr.isPrecomp then
          executeCode.handleError <| executePrecomp evm adr
        else
          executeCode.handleError <| exec evm lim
  termination_by lim => lim

  def processMessage (msg : Msg) :
    Nat → Except (String × State × AdrSet × Tra) Devm
    | 0 =>
      .error ⟨
        "RecursionLimit",
        msg.benv.state,
        msg.benv.createdAccounts,
        msg.tenv.transientStorage
      ⟩
    | lim + 1 => do
      /- In the original reference python implementation, there is a test here that
         checks the msg.depth value, and fails with a "stack depth limit error" if
         it is larger than 1024. However, due to the way processMessage is defined
         and used, there is no way msg.depth ever has a value larger than 1024, and
         the error reporting is a dead code path that never will never get used, so
         it is omitted here.  -/
      let benv ← msg.benvAfterTransfer
      let evm ← executeCode (msg.withBenv benv) lim
      if evm.error.isSome then
        .ok <| evm.rollback msg.benv.state msg.tenv.transientStorage
      else
        .ok evm
  termination_by lim => lim

  def processCreateMessage (msg : Msg) :
    Nat → Except (String × State × AdrSet × Tra) Devm
    | 0 => .error ⟨"RecursionLimit", msg.benv.state, msg.benv.createdAccounts, msg.tenv.transientStorage⟩
    | lim + 1 => do
      let evm ← processMessage (processCreateMessage.msg msg) lim
      if evm.error.isNone then
        match processCreateMessage.chargeCodeGas evm with
        | .ok evm => .ok <| evm.setCode msg.currentTarget ⟨⟨evm.output⟩⟩
        | .error ⟨err, evm⟩ =>
          if isExceptionalHalt err
          then
            .ok <|
              processCreateMessage.exceptionalHalt evm err
                msg.benv.state
                msg.tenv.transientStorage
          else
            .error ⟨err, evm.state, evm.createdAccounts, evm.transientStorage⟩
      else
        .ok <| evm.rollback msg.benv.state msg.tenv.transientStorage
  termination_by lim => lim

  def genericCreate
    (sevm : Sevm)
    (devm : Devm)
    (endowment : B256)
    (newAddress : Adr)
    (memoryIndex : Nat)
    (memorySize : Nat) : Nat → Execution
    | 0 => .error ⟨"RecursionLimit", devm⟩
    | lim + 1 => do
      let calldata ← .ok <| devm.memory.data.sliceD memoryIndex memorySize 0
      .assert
        (memorySize ≤ maxInitCodeSize)
        ⟨"OutOfGasError", devm⟩
      let devm1 ← .ok <| addAccessedAddress devm newAddress
      let createMsgGas ← .ok <| except64th devm1.gasLeft
      let devm2 ← .ok <| {devm1 with gasLeft := devm1.gasLeft - createMsgGas}
      assertDynamic sevm devm2
      let devm3 ← .ok <| {devm2 with returnData := []}
      let sender ← .ok <| devm3.state.get sevm.currentTarget
      if ( sender.bal < endowment ∨
           sender.nonce = B64.max ∨
           sevm.depth = 0 ) then
        return (← {devm3 with gasLeft := devm3.gasLeft + createMsgGas}.push 0)
      let devm4 ← .ok <| devm3.incrNonce sevm.currentTarget
      if
        ( let target := devm4.state.get newAddress
          target.nonce ≠ (0 : B64) ∨
          target.code.size ≠ 0 ∨
          target.stor.size ≠ 0 ) then
        return (← devm4.push 0)
      let childMsg : Msg ← .ok <| {
        benv := Benv.mk devm4.state devm4.createdAccounts sevm.benvStat
        tenv := {transientStorage := devm4.transientStorage, stat := sevm.tenvStat} --devm4.tenv
        caller := sevm.currentTarget
        target := .none
        gas := createMsgGas
        value := endowment
        data := []
        code := .mk <| .mk calldata
        currentTarget := newAddress
        depth := sevm.depth - 1
        codeAddress := .none
        shouldTransferValue := true
        isStatic := false
        accessedAddresses := devm4.accessedAddresses
        accessedStorageKeys := devm4.accessedStorageKeys
        disablePrecompiles := false
      }
      let child ← liftToExecution devm4 <| processCreateMessage childMsg lim
      if child.error.isSome then
        (incorporateChildOnError devm4 child child.output).push 0
      else
        (incorporateChildOnSuccess devm4 child []).push newAddress.toB256
  termination_by lim => lim

  def genericCall
    (sevm: Sevm)
    (devm: Devm)
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
    | 0 => .error ⟨"RecursionLimit", devm⟩
    | lim + 1 => do
      let evm1 ← .ok (devm.withReturnData [])
      if (sevm.depth = 0) then
        return (← (evm1.withGasLeft (evm1.gasLeft + gas)).push 0)
      let calldata ← .ok <| evm1.memory.data.sliceD input_index input_size 0
      let (childMsg : Msg) ← .ok <|
        callMsg sevm evm1 gas value caller target codeAddress
          shouldTransferValue isStaticcall calldata code disablePrecompiles
      let child ← liftToExecution evm1 <| processMessage childMsg lim
      let actualOutput := child.output.take output_size
      if child.error.isSome then
        let evm2 ← (incorporateChildOnError evm1 child child.output).push 0
        .ok <| evm2.memWrite output_index actualOutput
      else
        let evm2 ← (incorporateChildOnSuccess evm1 child child.output).push 1
        .ok <| evm2.memWrite output_index actualOutput
  termination_by lim => lim

  def Xinst.run (sevm : Sevm) (devm : Devm) :
      Xinst → Nat → Execution
    |  _, 0 => .error ⟨"RecursionLimit", devm⟩
    | .create, lim + 1 => do
      let ⟨endowment, devm1⟩ ← devm.pop
      let ⟨memoryIndex, devm2⟩ ← devm1.popToNat
      let ⟨memorySize, devm3⟩ ← devm2.popToNat
      let extendCost ← .ok <| devm3.extCost [⟨memoryIndex, memorySize⟩]
      let initCodeCost ← .ok <| gasInitCodeWordCost * (ceilDiv memorySize 32)
      let devm4 ← chargeGas (gasCreate + extendCost + initCodeCost) devm3
      let devm5 ← .ok <| devm4.memExtends [⟨memoryIndex, memorySize⟩]
      let newAddress ← .ok <|
        compute_contract_address
          sevm.currentTarget
          (devm5.state.get sevm.currentTarget).nonce
      genericCreate
        sevm
        devm5
        endowment
        newAddress
        memoryIndex
        memorySize
        lim
    | .create2, lim + 1 => do
      let ⟨endowment, devm1⟩ ← devm.pop
      let ⟨memoryIndex, devm2⟩ ← devm1.popToNat
      let ⟨memorySize, devm3⟩ ← devm2.popToNat
      let ⟨salt, devm4⟩ ← devm3.pop
      let extendCost ← .ok <| devm4.extCost [⟨memoryIndex, memorySize⟩]
      let initCodeHashCost ← .ok <|
        gasKeccak256Word * ceilDiv memorySize 32
      let initCodeCost ← .ok <|
        gasInitCodeWordCost * (ceilDiv memorySize 32)
      let devm5 ←
        chargeGas
          (gasCreate + initCodeHashCost + extendCost + initCodeCost)
          devm4
      let devm6 ← .ok <| devm5.memExtends [⟨memoryIndex, memorySize⟩]
      let newAddress ← .ok <|
        create2NewAddress
          sevm.currentTarget
          salt
          (devm6.memory.data.sliceD memoryIndex memorySize 0)
      genericCreate
        sevm
        devm6
        endowment
        newAddress
        memoryIndex
        memorySize
        lim
    | .call, lim + 1 => do
      let ⟨gas, devm1⟩ ← devm.pop
      let ⟨callee, devm2⟩ ← devm1.popToAdr
      let ⟨value, devm3⟩ ← devm2.pop
      let ⟨inputIndex, devm4⟩ ← devm3.popToNat
      let ⟨inputSize, devm5⟩ ← devm4.popToNat
      let ⟨outputIndex, devm6⟩ ← devm5.popToNat
      let ⟨outputSize, devm7⟩ ← devm6.popToNat
      let extendCost ← .ok <|
        devm7.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let preAccessCost ← .ok <| access_cost callee devm7.accessedAddresses
      let devm8 ← .ok <| addAccessedAddress devm7 callee
      let ⟨disablePrecompiles, _, code, delegatedAccessGasCost, devm9⟩ ← .ok <|
        accessDelegation devm8 callee
      let accessCost ← .ok <| preAccessCost + delegatedAccessGasCost
      let createCost ← .ok <|
        if (¬ (devm9.getAcct callee).Empty) ∨ value = 0
        then 0
        else gNewAccount
      let transferCost ← .ok <| if value = 0 then 0 else gasCallValue
      let ⟨msgCallCost, msgCallStipend⟩ ← .ok <|
        calculateMsgCallGas
          value.toNat
          gas.toNat
          devm9.gasLeft
          extendCost
          (accessCost + createCost + transferCost)
      let devm10 ← chargeGas (msgCallCost + extendCost) devm9
      .assert (!sevm.isStatic ∨ value = 0) ⟨"WriteInStaticContext", devm10⟩
      let devm11 ← .ok <|
        devm10.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let senderBal ← .ok <| (devm11.getAcct sevm.currentTarget).bal
      if senderBal < value then
        let devm12 ← devm11.push 0
        .ok ((devm12.withReturnData []).withGasLeft (devm12.gasLeft + msgCallStipend))
      else
        genericCall
          sevm
          devm11
          msgCallStipend
          value
          sevm.currentTarget
          callee
          callee
          true
          false
          inputIndex
          inputSize
          outputIndex
          outputSize
          code
          disablePrecompiles
          lim
    | .callcode, lim + 1 => do
      let ⟨gas, devm1⟩ ← devm.pop
      let ⟨codeAddress, devm2⟩ ← devm1.popToAdr
      let ⟨value, devm3⟩ ← devm2.pop
      let ⟨inputIndex, devm4⟩ ← devm3.popToNat
      let ⟨inputSize, devm5⟩ ← devm4.popToNat
      let ⟨outputIndex, devm6⟩ ← devm5.popToNat
      let ⟨outputSize, devm7⟩ ← devm6.popToNat
      let extendCost ← .ok <|
        devm7.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let preAccessCost ← .ok <| access_cost codeAddress devm7.accessedAddresses
      let devm8 ← .ok <| addAccessedAddress devm7 codeAddress
      let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm9⟩ ← .ok <|
        accessDelegation devm8 codeAddress
      let accessCost ← .ok <| preAccessCost + delegatedAccessGasCost
      let transferCost ← .ok <| if value = 0 then 0 else gasCallValue
      let ⟨msgCallCost, msgCallStipend⟩ ← .ok <|
        calculateMsgCallGas
          value.toNat
          gas.toNat
          devm9.gasLeft
          extendCost
          (accessCost + transferCost)
      let devm10 ← chargeGas (msgCallCost + extendCost) devm9
      let devm11 ← .ok <|
        devm10.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let senderBal ← .ok (devm11.getAcct sevm.currentTarget).bal
      if senderBal < value
      then
        let devm12 ← devm11.push 0
        .ok {
          devm12 with
          returnData := []
          gasLeft := devm12.gasLeft + msgCallStipend
        }
      else
        genericCall
          sevm
          devm11
          msgCallStipend
          value
          sevm.currentTarget
          sevm.currentTarget
          newCodeAddress
          true
          false
          inputIndex
          inputSize
          outputIndex
          outputSize
          code
          disablePrecompiles
          lim
    | .delcall, lim + 1 => do
      let ⟨gas, devm1⟩ ← devm.pop
      let ⟨codeAddress, devm2⟩ ← devm1.popToAdr
      let ⟨inputIndex, devm3⟩ ← devm2.popToNat
      let ⟨inputSize, devm4⟩ ← devm3.popToNat
      let ⟨outputIndex, devm5⟩ ← devm4.popToNat
      let ⟨outputSize, devm6⟩ ← devm5.popToNat
      let extendCost ← .ok <|
        devm6.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let preAccessCost ← .ok <| access_cost codeAddress devm6.accessedAddresses
      let devm7 ← .ok <| addAccessedAddress devm6 codeAddress
      let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm8⟩ ← .ok <|
        accessDelegation devm7 codeAddress
      let accessCost ← .ok <| preAccessCost + delegatedAccessGasCost
      let ⟨msgCallCost, msgCallStipend⟩ ← .ok <|
        calculateMsgCallGas
          0
          gas.toNat
          devm8.gasLeft
          extendCost
          accessCost
      let devm9 ← chargeGas (msgCallCost + extendCost) devm8
      let devm10 ← .ok <|
        devm9.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      genericCall
        sevm
        devm10
        msgCallStipend
        sevm.value
        sevm.caller
        sevm.currentTarget
        newCodeAddress
        false
        false
        inputIndex
        inputSize
        outputIndex
        outputSize
        code
        disablePrecompiles
        lim
    | .statcall, lim + 1 => do
      let ⟨gas, devm1⟩ ← devm.pop
      let ⟨target, devm2⟩ ← devm1.popToAdr
      let ⟨inputIndex, devm3⟩ ← devm2.popToNat
      let ⟨inputSize, devm4⟩ ← devm3.popToNat
      let ⟨outputIndex, devm5⟩ ← devm4.popToNat
      let ⟨outputSize, devm6⟩ ← devm5.popToNat
      let extendCost ← .ok <|
        devm6.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let preAccessCost ← .ok <| access_cost target devm6.accessedAddresses
      let devm7 ← .ok <| addAccessedAddress devm6 target
      let ⟨disablePrecompiles, _, code, delegatedAccessGasCost, devm8⟩ ←
        .ok <| accessDelegation devm7 target
      let accessCost ← .ok <| preAccessCost + delegatedAccessGasCost
      let ⟨msgCallCost, msgCallStipend⟩ ← .ok <|
        calculateMsgCallGas
          0
          gas.toNat
          devm8.gasLeft
          extendCost
          accessCost
      let devm9 ← chargeGas (msgCallCost + extendCost) devm8
      let devm10 ← .ok <|
        devm9.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      genericCall
        sevm
        devm10
        msgCallStipend
        0
        sevm.currentTarget
        target
        target
        true
        true
        inputIndex
        inputSize
        outputIndex
        outputSize
        code
        disablePrecompiles
        lim
  termination_by _ lim => lim

  def Ninst.run (evm : Evm) :
      --Ninst → Nat → Except (String × Devm) (Nat × Devm)
      Ninst → Nat → Execution
    | .push xs _, _ => do
      let evm' ← chargeGas (if xs = [] then gBase else gVerylow) evm.dyna
      -- (evm'.push xs.toB256).withPc (evm.pc + xs.length + 1)
      evm'.push xs.toB256 --).withPc (evm.pc + xs.length + 1)
    | .reg r, _ =>
      --(r.run evm).withPc (evm.pc + 1)
      r.run evm
    | .exec _, 0 => .error ⟨"RecursionLimit", evm.dyna⟩
    | .exec x, lim + 1 =>
      -- (Xinst.run evm.sta evm.dyna x lim).withPc (evm.pc + 1)
      Xinst.run evm.sta evm.dyna x lim
  termination_by _ lim => lim

  def exec : Evm → Nat → Execution
    | evm, 0 =>
      .error ⟨"RecursionLimit", evm.dyna⟩
    | evm, lim + 1 => do
      -- let mut evm := evm
      -- showLim lim evm
      let i ← (evm.getInst).toExcept ⟨"InvalidOpcode", evm.dyna⟩
      -- showStep evm i
      match i with
      | .next n =>
        let devm ← n.run evm lim
        exec ⟨evm.pc + n.size, evm.sta, devm⟩ lim
      | .jump j =>
        let ⟨pc, devm⟩ ← j.run evm
        exec ⟨pc, evm.sta, devm⟩ lim
      | .last l => l.run evm.sta evm.dyna
  termination_by _ lim => lim

end

instance {w a} : Decidable (Dead w a) := by
  simp [Dead]
  cases w[a]?
  · simp; apply instDecidableTrue
  · simp [Acct.Empty]; apply instDecidableAnd

def State.code (w : State) (a : Adr) : ByteArray :=
  match w[a]? with
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


def correctBlobHashVersion (h : B256) : Prop :=
  h.toB8L[0]! = 0x01

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
  let finalNTB : NTB := Std.TreeMap.ofList keyVals _
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
  let r := tx.r.toB256
  let s := tx.s.toB256
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
  for auth in msg.tenv.stat.auths do
    if auth.chainId != msg.benv.stat.chainId && auth.chainId != 0 then
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

def processMessageCall.create (msg : Msg) :
  Except String (State × MsgCallOutput) := do
  let benv := msg.benv
  let isCollision : Bool :=
    accountHasCodeOrNonce benv.state msg.currentTarget || accountHasStorage benv.state msg.currentTarget
  if isCollision then
    return ⟨benv.state, ⟨0, 0, [], .emptyWithCapacity, "AddressCollision", []⟩⟩
  else
    let evm ← Except.bimap Prod.fst id <| processCreateMessage msg (msg.gas + 50)
    let logs := if evm.error.isNone then evm.logs else []
    let accountsToDelete := if evm.error.isNone then evm.accountsToDelete else .emptyWithCapacity
    let refundCounter ←
      if evm.error.isNone then
       (Int.toNat? evm.refundCounter).toExcept "ERROR : refund counter is negative"
      else
        .ok 0
    .ok ⟨
      evm.state,
      {
        gasLeft := evm.gasLeft,
        refundCounter := refundCounter
        logs := logs,
        accountsToDelete := accountsToDelete,
        error := evm.error,
        returnData := evm.output
      }
    ⟩

def processMessageCall.call (msg : Msg) :
  Except String (State × MsgCallOutput) := do
  let (⟨msgDelegation, refundDelegation⟩ : Msg × Nat) ←
    if msg.tenv.stat.auths.isEmpty then
      .ok (⟨msg, 0⟩ : Msg × Nat)
    else do
      let ⟨msgDelegation, setDelegationValue⟩ ← setDelegation msg
      .ok ⟨msgDelegation, setDelegationValue.toNat⟩
  let msgPc :=
    match getDelegatedCodeAddress msgDelegation.code with
    | none => msgDelegation
    | some dca =>
      {
        msgDelegation with
        disablePrecompiles := true,
        accessedAddresses := msgDelegation.accessedAddresses.insert dca,
        code := msg.benv.state.getCode dca,
        codeAddress := some dca
      }
  let evm ← Except.bimap Prod.fst id <| processMessage msgPc (msgPc.gas + 50)
  let refundProcessMessage ←
    if evm.error.isNone then
      (Int.toNat? evm.refundCounter).toExcept "ERROR : refund counter is negative"
    else
      .ok 0
  let logs := if evm.error.isNone then evm.logs else []
  let accountsToDelete := if evm.error.isNone then evm.accountsToDelete else .emptyWithCapacity
  .ok ⟨
    evm.state,
    {
      gasLeft := evm.gasLeft,
      refundCounter := refundDelegation + refundProcessMessage
      logs := logs,
      accountsToDelete := accountsToDelete,
      error := evm.error,
      returnData := evm.output
    }
  ⟩

def processMessageCall (msg : Msg) :
    Except String (State × MsgCallOutput) := do
  if msg.target.isNone then
    processMessageCall.create msg
  else
    processMessageCall.call msg

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
  transactionsTrie : Std.TreeMap B8L Tx compare
  receiptsTrie : Std.TreeMap B8L (Fin 5 × Receipt) compare
  receiptKeys : List B8L
  blockLogs : List Log
  withdrawalsTrie : Std.TreeMap B8L Withdrawal compare
  blobGasUsed : Nat
  requests : List B8L

-- check_transaction
def checkTransaction (benv : Benv) (blockOut : BlockOutput) (tx : Tx) :
  Except String (Adr × Nat × List B256 × Nat) := do
  let gasAvailable := benv.stat.blockGasLimit - blockOut.blockGasUsed
  let blobGasAvailable := maxBlobGasPerBlock - blockOut.blobGasUsed
  if tx.gas > gasAvailable then
    .error "GasUsedExceedsLimitError : gas used exceeds limit"
  let txBlobGasUsed := calculateTotalBlobGas tx
  if txBlobGasUsed > blobGasAvailable then
    .error s!"BlobGasLimitExceededError : blob gas used = {txBlobGasUsed}, blob gas available = {blobGasAvailable}"
  let senderAddress ← recoverSender benv.stat.chainId tx
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
    if maxFee < benv.stat.baseFeePerGas then
      .error "InsufficientMaxFeePerGasError"
    let priorityFeePerGas := min maxPriorityFee (maxFee - benv.stat.baseFeePerGas)
    effectiveGasPrice := priorityFeePerGas + benv.stat.baseFeePerGas
    maxGasFee := tx.gas * maxFee
  | .inl gasPrice =>
    if gasPrice < benv.stat.baseFeePerGas then
      .error "InvalidBlock : gas price below base fee"
    effectiveGasPrice := gasPrice
    maxGasFee := tx.gas * gasPrice
  let mut blobVersionedHashes : List B256 := []
  match tx.type with
  | .three _ _ _ _ _ maxBlobFee blobHashes =>
    if blobHashes.isEmpty then
      .error "NoBlobDataError : no blob data in transaction"
    if List.any blobHashes (λ bvh => bvh.toB8L[0]! ≠ versionedHashVersionKzg) then
      .error "InvalidBlobVersionedHashError : invalid blob versioned hash"
    let blobGasPrice := calculate_blob_gas_price benv.stat.excessBlobGas
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
  if tx.type.receiver?.isNone && tx.data.length > maxInitCodeSize
    then .error "InvalidTransaction : Code size too large"
  .ok ⟨intrinsicGas, callDataFloorGasCost⟩

def prepareMessage (benv: Benv) (tenv: Tenv) (tx: Tx) :
  Except String Msg := do
  let ⟨currentTarget, msgData, code, codeAddress⟩ :
    Adr × B8L × ByteArray × Option Adr :=
    match tx.type.receiver? with
    | none => ⟨
        compute_contract_address
          tenv.stat.origin
          (benv.state.getNonce tenv.stat.origin - 1),
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
    tenv.stat.accessListAddresses.insertMany
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, tenv.stat.origin, currentTarget]
  .ok {
    benv := benv,
    tenv := tenv,
    caller := tenv.stat.origin,
    target := tx.type.receiver?,
    gas := tenv.stat.gas,
    value := tx.value.toB256,
    data := msgData,
    code := code,
    depth := 1024,
    currentTarget := currentTarget,
    codeAddress := codeAddress
    shouldTransferValue := true,
    isStatic := false,
    accessedAddresses := accessedAddresses,
    accessedStorageKeys := tenv.stat.accessListStorageKeys,
    disablePrecompiles := false
  }

-- calculate_data_fee
def calculate_data_fee (excess_blob_gas: Nat) (tx: Tx) : Nat :=
  calculateTotalBlobGas tx * calculate_blob_gas_price excess_blob_gas

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
  (benv: Benv) (bout : BlockOutput)
  (tx: Tx) (index : Nat) : Except String (State × BlockOutput) := do
  let transactionsTrie : Std.TreeMap B8L Tx compare :=
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
    then calculate_data_fee benv.stat.excessBlobGas tx
    else 0
  let effectiveGasFee := tx.gas * effectiveGasPrice
  let gas := tx.gas - intrinsicGas
  let mut state : State := benv.state.incrNonce sender
  state ← (state.subBal sender (effectiveGasFee + blobGasFee).toB256).toExcept
    "ERROR : balance underflow"
  let preaccessedAddresses : AdrSet :=
    .ofList (benv.stat.coinbase :: tx.accessList.map Prod.fst)
  let preaccessedStorageKeys : KeySet :=
    .ofList (tx.accessList.map <| λ ⟨adr, keys⟩ => keys.map (⟨adr, ·⟩)).flatten
  let tenv : Tenv := {
    transientStorage := .empty
    stat := {
      origin := sender
      gasPrice := effectiveGasPrice
      gas := gas
      accessListAddresses := preaccessedAddresses
      accessListStorageKeys := preaccessedStorageKeys
      blobVersionedHashes := blobVersionedHashes
      auths := tx.auths
      indexInBlock := index
      txHash := getTxHash tx
    }
  }
  let msg ← prepareMessage {benv with state := state} tenv tx
  let ⟨state', txOutput⟩ ← processMessageCall msg
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
  let priorityFeePerGas := effectiveGasPrice - benv.stat.baseFeePerGas
  let transactionFee := txGasUsedAfterRefund * priorityFeePerGas
  state := state.addBal sender gasRefundAmount.toB256
  state := state.addBal benv.stat.coinbase transactionFee.toB256
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

def BlockOutput.withWithdrawalsTrie
    (bo : BlockOutput) (tr : Std.TreeMap B8L Withdrawal compare) : BlockOutput :=
  {bo with withdrawalsTrie := tr}

def processWithdrawalsTrie (tr : Std.TreeMap B8L Withdrawal compare)
    (wds : List Withdrawal) : Std.TreeMap B8L Withdrawal compare :=
  List.foldl
    (λ acc ⟨i, wd⟩ => acc.insert (BLT.toB8L <| .b8s i.toB8L) wd)
    tr
    wds.putIndex

def processWithdrawalsState (st : State) (wds : List Withdrawal) : State :=
  List.foldl
    (λ acc wd => acc.addBal wd.recipient (wd.amount * (10 ^ 9).toB256))
    st
    wds

-- def process_withdrawal
def processWithdrawals
  (benv : Benv) (bout : BlockOutput) (wds : List Withdrawal) : State × BlockOutput :=
  let trie := processWithdrawalsTrie bout.withdrawalsTrie wds
  let state := processWithdrawalsState benv.state wds
  ⟨state, bout.withWithdrawalsTrie trie⟩

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
          nonce := nonce.toB64,
          gas := gas.toNat,
          value := value.toNat,
          data := data,
          v := yParity.toNat,
          r := (r.reverse.takeD 32 0).reverse,
          s := (s.reverse.takeD 32 0).reverse,
          type :=
            .one
              chainId.toB64
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
        nonce := nonce.toB64,
        gas := gas.toNat,
        value := value.toNat,
        data := data,
        v := yParity.toNat,
        r := (r.reverse.takeD 32 0).reverse,
        s := (s.reverse.takeD 32 0).reverse,
        type :=
          .two
            chainId.toB64
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
        nonce := nonce.toB64,
        gas := gas.toNat,
        value := value.toNat,
        data := data,
        v := yParity.toNat,
        r := (r.reverse.takeD 32 0).reverse,
        s := (s.reverse.takeD 32 0).reverse,
        type :=
          .three
            chainId.toB64
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


def processSystemTransactionTenv (benv : Benv) : Tenv :=
  {
    transientStorage := .empty,
    stat := {
      origin := systemAddress,
      gasPrice := benv.stat.baseFeePerGas,
      gas := systemTransactionGas,
      accessListAddresses := .emptyWithCapacity
      accessListStorageKeys := .emptyWithCapacity
      blobVersionedHashes := [],
      auths := [],
      indexInBlock := none,
      txHash := none
    }
  }

def processSystemTransactionMsg (benv : Benv) (tenv : Tenv)
    (target : Adr) (data : B8L) (code : ByteArray) : Msg :=
  {
    benv := benv,
    tenv := tenv,
    caller := systemAddress,
    target := target,
    gas := systemTransactionGas,
    value := 0,
    data := data,
    code := code,
    depth := 1024,
    currentTarget := target,
    codeAddress := target,
    shouldTransferValue := false,
    isStatic := false,
    accessedAddresses := .emptyWithCapacity,
    accessedStorageKeys := .emptyWithCapacity,
    disablePrecompiles := false
  }

-- process_system_transaction
def processSystemTransaction (benv : Benv)
  (target : Adr) (code : ByteArray) (data : B8L) :
  Except String (State × MsgCallOutput) := do
  let txEnv : Tenv := processSystemTransactionTenv benv
  let systemTxMsg : Msg :=
    processSystemTransactionMsg benv txEnv target data code
  processMessageCall systemTxMsg

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
      bout.receiptsTrie[key]?.toExcept "ERROR : receipt not found"
    for log in receipt.logs do
      if (
        log.address = depositContractAddress ∧
        log.topics[0]? = some depositEventSignatureHash
      ) then
        let request ← extractDepositData log.data
        depositRequests := depositRequests ++ request
  .ok depositRequests

def processUncheckedSystemTransaction
  (benv : Benv) (target : Adr) (data : B8L) :
  Except String (State × MsgCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  processSystemTransaction benv target systemContractCode data

def processCheckedSystemTransaction
  (benv : Benv) (target : Adr) (data : B8L) :
  Except String (State × MsgCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  if systemContractCode.isEmpty then
    .error s!"InvalidBlock : System contract address {target.toHex} does not contain code"
  let ⟨state, systemTxOutput⟩ ←
    processSystemTransaction benv target systemContractCode data
  if systemTxOutput.error.isSome then
    .error s!"InvalidBlock : System contract ({target.toHex}) call failed: {systemTxOutput.error.get!}"
  .ok ⟨state, systemTxOutput⟩

def processGeneralPurposeRequests
  (benv : Benv) (bout : BlockOutput) :
  Except String (State × BlockOutput) := do
  let depositRequests ← parseDepositRequests bout
  let mut requestsFromExecution : List B8L := bout.requests
  if depositRequests.length > 0 then
    requestsFromExecution :=
      requestsFromExecution ++ [depositRequestType ++ depositRequests]
  let ⟨state, withdrawalOutput⟩  ←
    processCheckedSystemTransaction benv
      withdrawalRequestPredeployAddress
      []
  let benv := {benv with state := state}
  if withdrawalOutput.returnData.length > 0 then
    requestsFromExecution :=
      requestsFromExecution ++ [withdrawalRequestType ++ withdrawalOutput.returnData]
  let ⟨state, consolidationOutput⟩  ←
    processCheckedSystemTransaction benv
      consolidationRequestPredeployAddress
      []
  if consolidationOutput.returnData.length > 0 then
    requestsFromExecution :=
      requestsFromExecution ++ [consolidationRequestType ++ consolidationOutput.returnData]
  .ok ⟨state, {bout with requests := requestsFromExecution}⟩

def applyTransactions :
    List (Nat × Tx) → Benv → BlockOutput → Except String (Benv × BlockOutput)
  | [], benv, bout => .ok (benv, bout)
  | ⟨i, tx⟩ :: txis, benv , bout => do
    let ⟨st, bout'⟩ ← processTransaction benv bout tx i
    applyTransactions txis (benv.withState st) bout'

def applyBody
  (benv : Benv) (txs : List (B8L ⊕ Tx)) (wds : List Withdrawal) :
  Except String (State × BlockOutput) := do
  cprint "\n================================ BEACON ROOTS TX ================================\n"
  let ⟨stBeacon, _⟩ ←
    processUncheckedSystemTransaction benv
      beaconRootsAddress
      benv.stat.parentBeaconBlockRoot.toB8L
  let benvBeacon : Benv := benv.withState stBeacon
  cprint "\n================================ HISTORY STORAGE TX ================================\n"
  let lastHash ←
     benvBeacon.stat.blockHashes.getLast?.toExcept "ERROR : block hashes is empty"
  let ⟨stHistory, _⟩ ←
    processUncheckedSystemTransaction benvBeacon
      historyStorageAddress
      lastHash.toB8L
  let benvHistory := benvBeacon.withState stHistory
  cprint "\n================================ MAIN TXS ================================\n"
  let ⟨benvTxs, boutTxs⟩ ←
    applyTransactions (← txs.mapM decodeTx).putIndex benvHistory .init
  cprint s!"\nSTATE AFTER TEST TXS :"
  cprint s!"{benvTxs.state}"
  cprint "\n================================ PROCESS WITHDRAWALS ================================\n"
  let ⟨stWds, boutWds⟩ :=
    processWithdrawals benvTxs boutTxs wds
  cprint "\n================================ PROCESS GENERAL PURPOSE REQUESTS ================================\n"
  processGeneralPurposeRequests (benvTxs.withState stWds) boutWds

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
  let finalNTB : NTB := Std.TreeMap.ofList keyVals _
  trie finalNTB

def stateTransitionChecks (bout : BlockOutput) (header : Header)
    (transactionsRoot blockStateRoot receiptRoot : B256)
    (blockLogsBloom : B8L) (withdrawalsRoot requestsHash : B256) :
    Except String Unit := do
  if bout.blockGasUsed ≠ header.gasUsed then
    .error s!"InvalidBlock : computed block gas used = {bout.blockGasUsed} ≠ expected block gas used = {header.gasUsed}"
  if transactionsRoot ≠ header.txsRoot then
    .error s!"InvalidBlock : computed transactions root = {transactionsRoot} ≠ expected transactions root = {header.txsRoot}"
  if blockStateRoot ≠ header.stateRoot then
    .error "InvalidBlock : state root mismatch"
  if receiptRoot ≠ header.receiptRoot then
    .error "InvalidBlock : receipt root mismatch"
  if blockLogsBloom ≠ header.bloom then
    .error "InvalidBlock : bloom mismatch"
  if withdrawalsRoot ≠ header.withdrawalsRoot then
    .error "InvalidBlock : withdrawals root mismatch"
  if bout.blobGasUsed ≠ header.blobGasUsed then
    .error "InvalidBlock : blob gas used mismatch"
  if some requestsHash ≠ header.requestsHash then
    .error s!"InvalidBlock : expected requests hash = {header.requestsHash}, computed requests hash = {requestsHash}"

def initBenvStat (chain : BlockChain) (header : Header) : BenvStat :=
  {
    chainId := chain.chainId,
    origState := chain.state,
    blockGasLimit := header.gasLimit,
    blockHashes := getLast256BlockHashes chain,
    coinbase := header.coinbase,
    number := header.number,
    baseFeePerGas := header.baseFeePerGas,
    time := header.timestamp.toB256,
    prevRandao := header.prevRandao,
    excessBlobGas := header.excessBlobGas,
    parentBeaconBlockRoot := header.parentBeaconBlockRoot
  }

def initBenv (chain : BlockChain) (header : Header) : Benv :=
  {
    state := chain.state,
    createdAccounts := .emptyWithCapacity,
    stat := initBenvStat chain header
  }

def getTransactionsRoot (bout : BlockOutput) : B256 :=
  let aux (arg : B8L × Tx) : (B8L × B8L) :=
    let txPrefix : B8L :=
      match arg.snd.type with
      | .zero _ _ => []
      | .one _ _ _ _ => [0x01]
      | .two _ _ _ _ _ => [0x02]
      | .three _ _ _ _ _ _ _ => [0x03]
      | .four _ _ _ _ _ _ => [0x04]
    ⟨arg.fst.toB4s, txPrefix ++ arg.snd.toBLT.toB8L⟩
  trie <| Std.TreeMap.ofList (List.map aux bout.transactionsTrie.toList) _

def getReceiptRoot (bout : BlockOutput) : B256 :=
  let aux : (B8L × Fin 5 × Receipt) → (B8L × B8L)
    | ⟨key, type, receipt⟩ => ⟨key.toB4s, type.val.toB8L ++ receipt.toBLT.toB8L⟩
  trie <| Std.TreeMap.ofList (List.map aux bout.receiptsTrie.toList) _

def getWithdrawalsRoot (bout : BlockOutput) : B256 :=
  let aux (arg : B8L × Withdrawal) : B8L × B8L :=
    ⟨arg.fst.toB4s, arg.snd.toBLT.toB8L⟩
  trie <| Std.TreeMap.ofList (List.map aux bout.withdrawalsTrie.toList) _

def stateTransitionOmmersCheck (ommers : List Header) : Except String Unit := do
  if ¬ommers.isEmpty then do
    .error "InvalidBlock"

def appendBlock (blks : List Block) (blk : Block) : List Block :=
  (blk :: blks.reverse.take 254).reverse

def stateTransition (ch : BlockChain) (block : Block) :
  Except String BlockChain := do
  validateHeader ch block.header
  stateTransitionOmmersCheck block.ommers
  let benv : Benv := initBenv ch block.header
  let ⟨st, bout⟩ ← applyBody benv block.txs block.wds
  let blockStateRoot : B256 := st.root
  let transactionsRoot : B256 := getTransactionsRoot bout
  let receiptRoot : B256 := getReceiptRoot bout
  let blockLogsBloom : B8L := logsBloom bout.blockLogs
  let withdrawalsRoot : B256 := getWithdrawalsRoot bout
  let requestsHash := computeRequestsHash bout.requests
  stateTransitionChecks bout block.header
    transactionsRoot blockStateRoot receiptRoot
    blockLogsBloom withdrawalsRoot requestsHash
  .ok ⟨appendBlock ch.blocks block, st, ch.chainId⟩

def BLT.toExStrWithdrawal : BLT → Except String Withdrawal
  | .list [
      .b8s globalIndex,
      .b8s validatorIndex,
      .b8s recipient,
      .b8s amount
    ] => do
    let globalIndex := globalIndex.toB64
    let validatorIndex := validatorIndex.toB64
    let recipient ← recipient.toAdr?.toExcept "error : invalid recipient address"
    let amount := amount.toB256
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
      nonce := nonce.toB64,
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

def addBlockToChain (chain : BlockChain) (blockRlp : B8L) :
  Except String (BlockChain ⊕ String) := do
  let ⟨block, blockHeaderHash⟩ ← rlpToBlock blockRlp
  cprint "\nSTATE BEFORE TRANSITION :"
  cprint s!"{chain.state}"
  if (Header.toBLT block.header).toB8L.keccak ≠ blockHeaderHash then do
    .error "ERROR : incorrect block header hash"
  let rlp' := block.toBLT.toB8L
  if blockRlp ≠ rlp' then do
    .error "ERROR : incorrect block rlp"
  let chain ←
    match stateTransition chain block with
    | .error err => return (.inr err)
    | .ok chain => .ok chain
  cprint s!"\nSTATE AFTER TRANSITION :"
  cprint s!"{chain.state}"
  .ok (.inl chain)
