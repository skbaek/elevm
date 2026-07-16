-- FixtureException.lean : the canonical vocabulary of official fixture
-- exception identities, and the fail-closed matcher built on it.
--
-- This module is fixture-runner infrastructure, not EVM semantics: it is
-- imported by `Main.lean` only, and deliberately not from the `Elevm` library
-- root, so that no proof client depends on it.
--
-- A fixture's `expectException` is a `|`-separated set of *allowed* official
-- exception identities. The runner must parse that set, classify the actual
-- error as exactly one canonical identity, and accept only set membership.
-- Everything here therefore fails closed: unknown expected identities, unknown
-- actual errors, and broad categories such as a bare `InvalidBlock` are
-- failures, never successes. There is deliberately no `contains`, no suffix
-- match, and no "any RLP error is good enough" fallback -- those are what let a
-- block be rejected for the wrong reason and still be scored as a pass.

import Elevm.Execution

/-- One official exception identity from the Prague fixture corpus.

The corpus vocabulary was generated from the fixtures rather than assumed: at
the time of writing the selected Prague cases contain 296 expected-invalid
blocks, 38 distinct `expectException` strings, and exactly these 35 individual
identities, spanning the `BlockException` and `TransactionException`
namespaces. `FixtureException.all` and the `#guard`s below pin those counts, so
corpus drift shows up as a build failure rather than as a silently accepted
unknown token. -/
inductive FixtureException where
  -- BlockException.*
  | blockExtraDataTooBig
  | blockGasLimitTooBig
  | blockGasUsedOverflow
  | blockImportImpossibleDifficultyOverParis
  | blockImportImpossibleUnclesOverParis
  | blockInvalidBaseFeePerGas
  | blockInvalidBlockNumber
  | blockInvalidBlockTimestampOlderThanParent
  | blockInvalidGasLimit
  | blockInvalidGasUsed
  | blockInvalidLogBloom
  | blockInvalidReceiptsRoot
  | blockInvalidStateRoot
  | blockInvalidTransactionsRoot
  | blockInvalidWithdrawalsRoot
  | blockRlpInvalidFieldOverflow64
  | blockRlpStructuresEncoding
  | blockRlpWithdrawalsNotRead
  | blockUnknownParent
  | blockUnknownParentZero
  -- TransactionException.*
  | txGasLimitPriceProductOverflow
  | txGasAllowanceExceeded
  | txInitcodeSizeExceeded
  | txInsufficientAccountFunds
  | txInsufficientMaxFeePerGas
  | txIntrinsicGasTooLow
  | txNonceIsMax
  | txNonceMismatchTooHigh
  | txNonceMismatchTooLow
  | txPriorityGreaterThanMaxFeePerGas
  | txSenderNotEoa
  | txType3TxBlobCountExceeded
  | txType3TxContractCreation
  | txType3TxInvalidBlobVersionedHash
  | txType3TxZeroBlobs
deriving DecidableEq, BEq, Repr, Inhabited

namespace FixtureException

/-- Every identity in the vocabulary. The single source of truth for the
round-trip, coverage, and injectivity checks below. -/
def all : List FixtureException :=
  [ blockExtraDataTooBig,
    blockGasLimitTooBig,
    blockGasUsedOverflow,
    blockImportImpossibleDifficultyOverParis,
    blockImportImpossibleUnclesOverParis,
    blockInvalidBaseFeePerGas,
    blockInvalidBlockNumber,
    blockInvalidBlockTimestampOlderThanParent,
    blockInvalidGasLimit,
    blockInvalidGasUsed,
    blockInvalidLogBloom,
    blockInvalidReceiptsRoot,
    blockInvalidStateRoot,
    blockInvalidTransactionsRoot,
    blockInvalidWithdrawalsRoot,
    blockRlpInvalidFieldOverflow64,
    blockRlpStructuresEncoding,
    blockRlpWithdrawalsNotRead,
    blockUnknownParent,
    blockUnknownParentZero,
    txGasLimitPriceProductOverflow,
    txGasAllowanceExceeded,
    txInitcodeSizeExceeded,
    txInsufficientAccountFunds,
    txInsufficientMaxFeePerGas,
    txIntrinsicGasTooLow,
    txNonceIsMax,
    txNonceMismatchTooHigh,
    txNonceMismatchTooLow,
    txPriorityGreaterThanMaxFeePerGas,
    txSenderNotEoa,
    txType3TxBlobCountExceeded,
    txType3TxContractCreation,
    txType3TxInvalidBlobVersionedHash,
    txType3TxZeroBlobs ]

/-- The canonical spelling of an identity: byte-for-byte the token the fixtures
use. -/
def toString : FixtureException → String
  | blockExtraDataTooBig => "BlockException.EXTRA_DATA_TOO_BIG"
  | blockGasLimitTooBig => "BlockException.GASLIMIT_TOO_BIG"
  | blockGasUsedOverflow => "BlockException.GAS_USED_OVERFLOW"
  | blockImportImpossibleDifficultyOverParis =>
    "BlockException.IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS"
  | blockImportImpossibleUnclesOverParis =>
    "BlockException.IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS"
  | blockInvalidBaseFeePerGas => "BlockException.INVALID_BASEFEE_PER_GAS"
  | blockInvalidBlockNumber => "BlockException.INVALID_BLOCK_NUMBER"
  | blockInvalidBlockTimestampOlderThanParent =>
    "BlockException.INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT"
  | blockInvalidGasLimit => "BlockException.INVALID_GASLIMIT"
  | blockInvalidGasUsed => "BlockException.INVALID_GAS_USED"
  | blockInvalidLogBloom => "BlockException.INVALID_LOG_BLOOM"
  | blockInvalidReceiptsRoot => "BlockException.INVALID_RECEIPTS_ROOT"
  | blockInvalidStateRoot => "BlockException.INVALID_STATE_ROOT"
  | blockInvalidTransactionsRoot => "BlockException.INVALID_TRANSACTIONS_ROOT"
  | blockInvalidWithdrawalsRoot => "BlockException.INVALID_WITHDRAWALS_ROOT"
  | blockRlpInvalidFieldOverflow64 => "BlockException.RLP_INVALID_FIELD_OVERFLOW_64"
  | blockRlpStructuresEncoding => "BlockException.RLP_STRUCTURES_ENCODING"
  | blockRlpWithdrawalsNotRead => "BlockException.RLP_WITHDRAWALS_NOT_READ"
  | blockUnknownParent => "BlockException.UNKNOWN_PARENT"
  | blockUnknownParentZero => "BlockException.UNKNOWN_PARENT_ZERO"
  | txGasLimitPriceProductOverflow =>
    "TransactionException.GASLIMIT_PRICE_PRODUCT_OVERFLOW"
  | txGasAllowanceExceeded => "TransactionException.GAS_ALLOWANCE_EXCEEDED"
  | txInitcodeSizeExceeded => "TransactionException.INITCODE_SIZE_EXCEEDED"
  | txInsufficientAccountFunds => "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS"
  | txInsufficientMaxFeePerGas => "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS"
  | txIntrinsicGasTooLow => "TransactionException.INTRINSIC_GAS_TOO_LOW"
  | txNonceIsMax => "TransactionException.NONCE_IS_MAX"
  | txNonceMismatchTooHigh => "TransactionException.NONCE_MISMATCH_TOO_HIGH"
  | txNonceMismatchTooLow => "TransactionException.NONCE_MISMATCH_TOO_LOW"
  | txPriorityGreaterThanMaxFeePerGas =>
    "TransactionException.PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS"
  | txSenderNotEoa => "TransactionException.SENDER_NOT_EOA"
  | txType3TxBlobCountExceeded => "TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED"
  | txType3TxContractCreation => "TransactionException.TYPE_3_TX_CONTRACT_CREATION"
  | txType3TxInvalidBlobVersionedHash =>
    "TransactionException.TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH"
  | txType3TxZeroBlobs => "TransactionException.TYPE_3_TX_ZERO_BLOBS"

instance : ToString FixtureException := ⟨toString⟩

/-- Exact inverse of `toString`. Exact means exact: no trimming, no case
folding, no prefix acceptance. An unrecognized token is `none`, which every
caller must treat as a failure. -/
def ofString? (s : String) : Option FixtureException :=
  all.find? (fun e => e.toString = s)

/-- The delimiter separating the alternatives of an `expectException` set. -/
def delimiter : String := "|"

/-- Parse a fixture `expectException` string into the nonempty set of allowed
identities.

`String.splitOn` always yields at least one token, and every token must resolve
to a canonical identity, so a successful parse is nonempty by construction.
Tokens are matched exactly, which is what rejects whitespace variants
(`"A | B"`), and empty tokens are rejected, which is what rejects a stray
`"A||B"` or a leading/trailing delimiter. Repeated identities are collapsed:
this is a set, and `"A|A"` names the same one-element set as `"A"`. -/
def parseExpectation (s : String) : Except String (List FixtureException) := do
  let toks := s.splitOn delimiter
  let es ←
    toks.mapM fun tok =>
      if tok.isEmpty then
        .error
          s!"empty alternative in expectException {repr s} \
             (stray or duplicated {repr delimiter} delimiter)"
      else
        match ofString? tok with
        | some e => .ok e
        | none => .error s!"unknown expected exception identity {repr tok} in {repr s}"
  .ok es.eraseDups

/-- A registered route from an actual internal error to the one canonical
identity it means.

The `String` is an error *tag*: it matches an actual error either exactly, or
as a prefix ending at the fixed `" : "` delimiter, so a producer may keep
detailed internal text after the tag. This is `hasErrorType`, the same
convention the rest of the executable already uses. -/
abbrev ActualRoute : Type := String × FixtureException

/-- Classify an actual error using an explicit route table.

Recognizes *only* explicitly registered exact messages or tag-prefixes; there is
no substring, suffix, or category fallback. An unregistered error is `none` and
must fail the fixture rather than be waved through. -/
def classifyWith (routes : List ActualRoute) (err : String) : Option FixtureException :=
  (routes.find? (fun r => hasErrorType err r.fst)).map Prod.snd

/-- The routes from ELeVM's actual errors to canonical identities.

Deliberately empty at this step. Registering a route is a claim that a specific
producer raises a specific official identity, and most producers are still
ambiguous: they raise bare `"InvalidBlock"` or share one internal string between
two official identities. Making the producers precise, and filling this table
under a coverage check, is the later strict-decoding and classification work.
Until then an empty table means `classify` recognizes nothing, which is the
fail-closed direction -- the old oracle stays wired, so no fixture's
classification depends on this yet. -/
def actualRoutes : List ActualRoute := []

/-- Classify an actual error against the registered routes. -/
def classify (err : String) : Option FixtureException :=
  classifyWith actualRoutes err

/-- The matcher: succeed only when the one identity classified from the actual
error is a member of the parsed expected set. (`matches` itself is a reserved
token in Lean, hence the name.) -/
def matchesSet (expected : List FixtureException) (actual : String) : Bool :=
  match classify actual with
  | none => false
  | some a => expected.contains a

/-- The string-level matcher, with the diagnostics the runner needs on failure:
both the raw actual error and its canonical reading (or the fact that it has
none). Returns the matched identity so a caller can report *which* alternative
was hit. -/
def matchesExpectation (expected actual : String) : Except String FixtureException := do
  let es ← parseExpectation expected
  match classify actual with
  | none =>
    .error s!"unknown actual error {repr actual} : it maps to no canonical \
              exception identity, expected one of {es.map toString}"
  | some a =>
    if es.contains a then
      .ok a
    else
      .error s!"exception mismatch : actual {repr actual} is {a.toString}, \
                expected one of {es.map toString}"

end FixtureException

----------------- FIXTURE VOCABULARY REGRESSION CHECKS ------------------

open FixtureException

-- The vocabulary is exactly the generated Prague inventory: 35 identities.
#guard all.length = 35

-- `toString` is injective, so no two identities collapse to one token.
#guard (all.map toString).eraseDups.length = 35

-- `toString`/`ofString?` round trip on all 35, in both directions.
#guard all.all (fun e => ofString? e.toString == some e)
#guard all.all (fun e => (ofString? e.toString).all (fun e' => e'.toString == e.toString))

-- `Except` has no `BEq`, so parse results are compared through these two
-- helpers rather than `==`.
private def parsesTo (s : String) (es : List FixtureException) : Bool :=
  match parseExpectation s with
  | .ok es' => es' == es
  | .error _ => false

private def parseRejects (s : String) : Bool := (parseExpectation s).toOption.isNone

-- Every identity's own spelling parses as the one-element set naming it. This
-- covers all 31 singleton `expectException` strings in the inventory.
#guard all.all (fun e => parsesTo e.toString [e])

-- `ofString?` is exact: near misses are unknown tokens, not near matches.
#guard (ofString? "BlockException.EXTRA_DATA_TOO_BIG").isSome
#guard (ofString? "EXTRA_DATA_TOO_BIG").isNone                       -- bare, unqualified
#guard (ofString? "BlockException.EXTRA_DATA_TOO_BIG ").isNone       -- trailing space
#guard (ofString? " BlockException.EXTRA_DATA_TOO_BIG").isNone       -- leading space
#guard (ofString? "blockexception.extra_data_too_big").isNone        -- case folded
#guard (ofString? "BlockException.EXTRA_DATA_TOO_BIG_X").isNone      -- longer
#guard (ofString? "BlockException.EXTRA_DATA_TOO_BI").isNone         -- truncated
#guard (ofString? "BlockException").isNone                           -- namespace only
#guard (ofString? "InvalidBlock").isNone                             -- old broad category
#guard (ofString? "").isNone

-- The seven composite expectation strings in the generated inventory, each
-- parsing to the exact set it names.
#guard parsesTo
  "BlockException.RLP_STRUCTURES_ENCODING|BlockException.RLP_INVALID_FIELD_OVERFLOW_64"
  [blockRlpStructuresEncoding, blockRlpInvalidFieldOverflow64]
#guard parsesTo
  "BlockException.RLP_STRUCTURES_ENCODING|BlockException.RLP_WITHDRAWALS_NOT_READ"
  [blockRlpStructuresEncoding, blockRlpWithdrawalsNotRead]
#guard parsesTo
  "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS|TransactionException.GASLIMIT_PRICE_PRODUCT_OVERFLOW"
  [txInsufficientAccountFunds, txGasLimitPriceProductOverflow]
#guard parsesTo
  "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS|TransactionException.INTRINSIC_GAS_TOO_LOW"
  [txInsufficientAccountFunds, txIntrinsicGasTooLow]
#guard parsesTo
  "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS|TransactionException.GAS_ALLOWANCE_EXCEEDED"
  [txInsufficientMaxFeePerGas, txGasAllowanceExceeded]
#guard parsesTo
  "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS|TransactionException.INSUFFICIENT_ACCOUNT_FUNDS"
  [txInsufficientMaxFeePerGas, txInsufficientAccountFunds]
#guard parsesTo
  "TransactionException.SENDER_NOT_EOA|TransactionException.INSUFFICIENT_ACCOUNT_FUNDS"
  [txSenderNotEoa, txInsufficientAccountFunds]

-- Order is preserved and duplicates collapse: the parse is a set.
#guard parsesTo "TransactionException.NONCE_IS_MAX|TransactionException.NONCE_IS_MAX"
  [txNonceIsMax]

-- Every distinct `expectException` string in the generated Prague inventory,
-- with its plan-writing-time occurrence count. 296 expected-invalid blocks
-- across 38 strings; the whole table must parse, and its identities must be
-- exactly the 35 in `all` -- no unused constructor, no unroutable token.
def fixtureInventory : List String :=
  [ "BlockException.EXTRA_DATA_TOO_BIG",                                                                    -- 3
    "BlockException.GASLIMIT_TOO_BIG",                                                                      -- 1
    "BlockException.GAS_USED_OVERFLOW",                                                                     -- 1
    "BlockException.IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS",                                               -- 1
    "BlockException.IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS",                                                   -- 66
    "BlockException.INVALID_BASEFEE_PER_GAS",                                                               -- 2
    "BlockException.INVALID_BLOCK_NUMBER",                                                                  -- 2
    "BlockException.INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT",                                             -- 7
    "BlockException.INVALID_GASLIMIT",                                                                      -- 10
    "BlockException.INVALID_GAS_USED",                                                                      -- 1
    "BlockException.INVALID_LOG_BLOOM",                                                                     -- 1
    "BlockException.INVALID_RECEIPTS_ROOT",                                                                 -- 1
    "BlockException.INVALID_STATE_ROOT",                                                                    -- 2
    "BlockException.INVALID_TRANSACTIONS_ROOT",                                                             -- 1
    "BlockException.INVALID_WITHDRAWALS_ROOT",                                                              -- 2
    "BlockException.RLP_STRUCTURES_ENCODING|BlockException.RLP_INVALID_FIELD_OVERFLOW_64",                  -- 4
    "BlockException.RLP_STRUCTURES_ENCODING|BlockException.RLP_WITHDRAWALS_NOT_READ",                       -- 1
    "BlockException.UNKNOWN_PARENT",                                                                        -- 1
    "BlockException.UNKNOWN_PARENT_ZERO",                                                                   -- 1
    "TransactionException.GAS_ALLOWANCE_EXCEEDED",                                                          -- 5
    "TransactionException.INITCODE_SIZE_EXCEEDED",                                                          -- 1
    "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS",                                                      -- 68
    "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS|TransactionException.GASLIMIT_PRICE_PRODUCT_OVERFLOW", -- 1
    "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS|TransactionException.INTRINSIC_GAS_TOO_LOW",           -- 49
    "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS",                                                    -- 7
    "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS|TransactionException.GAS_ALLOWANCE_EXCEEDED",        -- 1
    "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS|TransactionException.INSUFFICIENT_ACCOUNT_FUNDS",    -- 3
    "TransactionException.INTRINSIC_GAS_TOO_LOW",                                                           -- 30
    "TransactionException.NONCE_IS_MAX",                                                                    -- 2
    "TransactionException.NONCE_MISMATCH_TOO_HIGH",                                                         -- 1
    "TransactionException.NONCE_MISMATCH_TOO_LOW",                                                          -- 1
    "TransactionException.PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS",                                           -- 7
    "TransactionException.SENDER_NOT_EOA",                                                                  -- 7
    "TransactionException.SENDER_NOT_EOA|TransactionException.INSUFFICIENT_ACCOUNT_FUNDS",                  -- 1
    "TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED",                                                   -- 1
    "TransactionException.TYPE_3_TX_CONTRACT_CREATION",                                                     -- 1
    "TransactionException.TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH",                                           -- 1
    "TransactionException.TYPE_3_TX_ZERO_BLOBS" ]                                                           -- 1

#guard fixtureInventory.length = 38
#guard fixtureInventory.eraseDups.length = 38
#guard fixtureInventory.all (fun s => (parseExpectation s).toOption.isSome)

-- Both coverage directions: every identity is reachable from the corpus, and
-- the corpus mentions nothing outside the vocabulary. The second direction
-- holds because parsing succeeded above; the first is the real check, and it
-- fails loudly if a constructor is added that the fixtures never name.
#guard
  (fixtureInventory.flatMap
    (fun s => ((parseExpectation s).toOption.getD []))).eraseDups.length = 35

-- Malformed expectation strings are rejected, not repaired.
#guard parseRejects ""                                                     -- no alternatives
#guard parseRejects "|"                                                    -- two empty tokens
#guard parseRejects "BlockException.INVALID_GASLIMIT|"                     -- trailing delimiter
#guard parseRejects "|BlockException.INVALID_GASLIMIT"                     -- leading delimiter
#guard parseRejects
  "BlockException.INVALID_GASLIMIT||BlockException.GASLIMIT_TOO_BIG"       -- duplicated delimiter
#guard parseRejects
  "BlockException.INVALID_GASLIMIT | BlockException.GASLIMIT_TOO_BIG"      -- whitespace variant
#guard parseRejects "BlockException.INVALID_GASLIMIT|NotAnIdentity"        -- one unknown token
#guard parseRejects "InvalidBlock"                                         -- old broad category
#guard parseRejects "BlockException.INVALID_GASLIMIT|InvalidBlock"

-- The classifier's route semantics, exercised against a synthetic table: the
-- real `actualRoutes` is still empty by design.
private def sampleRoutes : List ActualRoute :=
  [ ("InvalidGasLimitAbsolute", blockGasLimitTooBig),
    ("InvalidGasLimitAdjustment", blockInvalidGasLimit) ]

-- An exact message, and a tag-prefix ending at the fixed " : " delimiter.
#guard classifyWith sampleRoutes "InvalidGasLimitAbsolute" == some blockGasLimitTooBig
#guard classifyWith sampleRoutes "InvalidGasLimitAbsolute : gasLimit = 2^63"
  == some blockGasLimitTooBig
#guard classifyWith sampleRoutes "InvalidGasLimitAdjustment : delta too large"
  == some blockInvalidGasLimit

-- A registered tag is not a substring or suffix matcher, and the delimiter is
-- fixed: only " : " opens the detail text.
#guard (classifyWith sampleRoutes "InvalidGasLimitAbsolute: gasLimit").isNone
#guard (classifyWith sampleRoutes "InvalidGasLimitAbsoluteX").isNone
#guard (classifyWith sampleRoutes "Error: InvalidGasLimitAbsolute").isNone
#guard (classifyWith sampleRoutes "wrapped InvalidGasLimitAbsolute : detail").isNone
#guard (classifyWith sampleRoutes "").isNone

-- Unregistered errors do not classify. In particular the old broad strings the
-- current oracle accepts must never become an identity by themselves.
#guard (classifyWith sampleRoutes "InvalidBlock").isNone
#guard (classifyWith sampleRoutes "InvalidBlock : some detail").isNone
#guard (classifyWith sampleRoutes "InvalidTransaction").isNone
#guard (classifyWith sampleRoutes "DecodingError : unexpected list length").isNone
#guard (classifyWith sampleRoutes "EncodingError").isNone

-- `actualRoutes` is empty at this step, so `classify` recognizes nothing and
-- `matches` is uniformly false: this module is not yet authoritative.
#guard actualRoutes.isEmpty
#guard (classify "InvalidBlock").isNone
#guard (classify "InvalidGasLimitAbsolute").isNone

-- The matcher is set membership on the one classified identity -- never
-- "some failure occurred". Shown against the synthetic table so the semantics
-- are pinned before `actualRoutes` is filled in.
private def matchesWith (routes : List ActualRoute)
  (expected : List FixtureException) (actual : String) : Bool :=
  match classifyWith routes actual with
  | none => false
  | some a => expected.contains a

#guard matchesWith sampleRoutes [blockGasLimitTooBig] "InvalidGasLimitAbsolute"
#guard matchesWith sampleRoutes [blockInvalidGasLimit, blockGasLimitTooBig]
  "InvalidGasLimitAbsolute : detail"
-- The right kind of failure, but not the expected identity: still a failure.
#guard ¬ matchesWith sampleRoutes [blockInvalidGasLimit] "InvalidGasLimitAbsolute"
-- An unclassifiable error never matches, no matter how broad the expected set.
#guard ¬ matchesWith sampleRoutes all "InvalidBlock"
#guard ¬ matchesWith sampleRoutes all "InvalidBlock : gas limit is wrong"
-- An empty expected set matches nothing; `parseExpectation` cannot produce one.
#guard ¬ matchesWith sampleRoutes [] "InvalidGasLimitAbsolute"

-- With the real (empty) route table, nothing matches yet.
#guard ¬ matchesSet all "InvalidGasLimitAbsolute"

-- `matchesExpectation` fails closed on every channel: unknown expected token,
-- unknown actual error, and a classified-but-unexpected identity.
#guard (matchesExpectation "NotAnIdentity" "InvalidGasLimitAbsolute").toOption.isNone
#guard (matchesExpectation "BlockException.GASLIMIT_TOO_BIG" "InvalidBlock").toOption.isNone
#guard (matchesExpectation "BlockException.GASLIMIT_TOO_BIG" "").toOption.isNone
