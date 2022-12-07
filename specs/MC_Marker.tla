---------- MODULE MC_Marker ----------

EXTENDS FiniteSets, typedefs_marker

\* @type: Set(ADDR);
UserAddrs == {"user1", "user2"}
\* @type: Set(DENOM);
DENOMS == { "hotdogcoin", "coldcatcoin", "nhash" }

VARIABLE
  \* @type: Set(MARKER);
  markers,
  \* @type: DENOM -> Str;
  markerStatus,
  \* @type: <<ADDR, DENOM>> -> Int;
  accounts,
  \* @type: Set(GRANTZ);
  grantz,
  \* @type: TX;
  tx,
  \* @type: Int;
  tx_no,
  \* @type: Bool;
  tx_fail

INSTANCE Marker

TX_WITH_AMOUNT == {
    "add-marker", "mint-marker", "burn-marker",
    "transfer-marker", "withdraw-marker", "grantz-marker"
}

\* a view to enumerate all transactions
TxView == tx.type

\* a view that contains some interesting combinations
TxMidView ==
    IF tx.type \in TX_WITH_AMOUNT
    THEN <<tx.type, tx.amount = 0, tx.amount > 100000, tx.amount > 100000000>>
    ELSE <<tx.type, FALSE, FALSE, FALSE>>
    
\* a rich view to enumerate interesting transactions
RichView ==
    <<
        IF tx.type \in TX_WITH_AMOUNT
        THEN <<tx.type, tx.amount > 0, tx.amount > 1000, tx.amount > 1000000>>
        ELSE <<tx.type, FALSE, FALSE, FALSE>>,
        IF tx.type = "add-marker"
        THEN <<tx.fail, tx.isSupplyFixed, tx.isAllowGovernance, tx.markerType>>
        ELSE <<tx.fail, FALSE, FALSE, "">>
    >>

InvFalse == FALSE
TxFail == tx_no < 9 \/ tx_fail
TxNoFailAfter(k) == ~(tx_no >= k /\ tx_fail)
TxFailAfter(k) == ~(tx_no >= k /\ ~tx_fail)

TxNoFail3 == TxNoFailAfter(3)
TxNoFail4 == TxNoFailAfter(4)
TxNoFail5 == TxNoFailAfter(5)
TxNoFail6 == TxNoFailAfter(6)
TxNoFail7 == TxNoFailAfter(7)
TxNoFail8 == TxNoFailAfter(8)
TxNoFail9 == TxNoFailAfter(9)
TxNoFail10 == TxNoFailAfter(10)
TxNoFail11 == TxNoFailAfter(11)
TxNoFail12 == TxNoFailAfter(12)
TxNoFail13 == TxNoFailAfter(13)
TxNoFail14 == TxNoFailAfter(14)

TxFail3 == TxFailAfter(3)
TxFail4 == TxFailAfter(4)
TxFail5 == TxFailAfter(5)
TxFail6 == TxFailAfter(6)
TxFail7 == TxFailAfter(7)
TxFail8 == TxFailAfter(8)
TxFail9 == TxFailAfter(9)
TxFail10 == TxFailAfter(10)
TxFail11 == TxFailAfter(11)
TxFail12 == TxFailAfter(12)
TxFail13 == TxFailAfter(13)
TxFail14 == TxFailAfter(14)

\* a counterexample to this invariant leads to a state
\* where a marker is minted. Use it to produce a mint tx.
NoMint ==
  tx.type /= "mint-marker"

\* A counterexample to this invariant leads to a state
\* where we cancel a marker. Use it to produce a destroy tx.
NoDestroy ==
  tx.type /= "destroy-marker"

\* a counterexample to this invariant leads to a state
\* where we have a marker that backs 'nhash'
NoActiveHashMarker ==
  LET Example ==
    \E m \in markers:
       /\ m.denom = "nhash"
       /\ m.amount = MAX_TOTAL_SUPPLY - 1000
       /\ m.isSupplyFixed
       /\ markerStatus["nhash"] = "ACTIVE"
  IN
  ~Example

\* A counterexample to this invariant leads to a state
\* where we activate a marker that has zero supply,
\* while the minting access is given to the marker itself.
\* See IF-PROVENANCE-04.
NoFinalizeWhenMarkerHasMinting ==
  LET Example ==
    /\ markerStatus["hotdogcoin"] = "FINALIZED"
    /\ \E m \in markers:
         /\ m.denom = "hotdogcoin"
         /\ m.markerType = "COIN"
         /\ m.amount = 0
         /\ m.isSupplyFixed
         /\ "mint" \in m.accessControl["hotdogcoin"]
  IN
  ~Example

\* A counterexample to this invariant leads to a state
\* where we activate a marker that has too many coins
\* and produce panic when trying to mint one more coin.
\* See IF-PROVENANCE-01.
NoActiveOverUint ==
  LET Example ==
    /\ tx.type = "mint-marker"
    /\ tx.denom = "coldcatcoin"
    /\ markerStatus["coldcatcoin"] = "ACTIVE"
    /\ \E m \in markers:
         /\ m.denom = "coldcatcoin"
         /\ m.markerType = "COIN"
         /\ m.amount >= 2^64 + 999
         /\ m.isSupplyFixed
         /\ { "mint", "burn" } \subseteq m.accessControl["user1"]
  IN
  ~Example

\* A counterexample to this invariant leads to a state
\* where we activate a marker that has too many coins
\* and produce panic when trying to mint one more coin.
\* See IF-PROVENANCE-01.
NoActiveMaxSupply ==
  LET Example ==
    /\ tx.type = "mint-marker"
    /\ markerStatus["coldcatcoin"] = "ACTIVE"
    /\ tx.denom = "coldcatcoin"
    /\ \E m \in markers:
         /\ m.denom = "coldcatcoin"
         /\ m.markerType = "COIN"
         /\ m.amount > MAX_TOTAL_SUPPLY + 999
         /\ m.amount < 2^64
         /\ m.isSupplyFixed
         /\ { "mint", "burn" } \subseteq m.accessControl["user1"]
  IN
  ~Example

\* A counterexample to this invariant leads to a state
\* where we activate a marker that has too many coins
\* and produce panic when trying to mint one more coin.
\* See IF-PROVENANCE-01.
\* In this case, tx.fail = TRUE.
NoMintingOverUint ==
  LET Example ==
    /\ tx.type \in { "mint-marker", "burn-marker" }
    /\ markerStatus["coldcatcoin"] = "ACTIVE"
    /\ \E m \in markers:
         /\ m.denom = "coldcatcoin"
         /\ m.markerType = "COIN"
         /\ m.amount = 1
         /\ tx.amount = 2^(256 - 60) - 1
         /\ m.isSupplyFixed
         /\ (IF tx.type = "mint-marker" THEN "mint" ELSE "burn")
                \in m.accessControl["user1"]
  IN
  ~Example

\* A counterexample to this invariant leads to a state
\* where we activate a marker that no one can manage.
\* This invariant is violated.
\* See IF-PROVENANCE-02.
NoOrphanedMarker ==
  LET Example ==
    /\ tx.type = "activate-marker"
    /\ tx.denom = "coldcatcoin"
    /\ \E m \in markers:
         /\ m.denom = "coldcatcoin"
         /\ m.markerType = "COIN"
         /\ \A a \in DOMAIN m.accessControl:
            m.accessControl[a] = {}
  IN
  ~Example

\* A counterexample to this invariant leads to a state
\* where we activate a marker that no one can manage.
\* This invariant is violated. We think it should not.
\* See IF-PROVENANCE-03.
NoRevokeSelfWhenZero ==
  LET Example ==
    /\ tx.type = "revoke-marker"
    /\ tx.denom = "hotdogcoin"
    /\ markerStatus["hotdogcoin"] = "ACTIVE"
    /\ \E m \in markers:
         /\ m.denom = "hotdogcoin"
         /\ m.markerType = "COIN"
         /\ ~m.isAllowGovernance
         /\ m.amount = 0
         /\ m.amount < MAX_TOTAL_SUPPLY
         /\ m.isSupplyFixed
         /\ \A a \in DOMAIN m.accessControl:
            a = tx.address \/ m.accessControl[a] = {}
  IN
  ~Example

\* A counterexample to this invariant leads to a state
\* where we delete a marker without having permission to delete.
\* This invariant holds true.
NoDeleteWithoutPermissions ==
  LET Example ==
    /\ tx.type = "delete-marker"
    /\ \E m \in markers:
        \* the account was once active
        /\ accounts[m.denom, m.denom] > 0
        /\ m.denom = tx.denom
        /\ m.accessControl[tx.user] = {}
  IN
  ~Example

\* A counterexample to this invariant leads to a state
\* where we transfer all coins from the marker account.
\* This invariant is violated.
NoWithdraw ==
  LET denom == "hotdogcoin" IN
  LET Example ==
    /\ tx.type = "withdraw-marker"
    /\ tx.denom = denom
    /\ markerStatus[denom] = "ACTIVE"
  IN
  ~Example

\* A counterexample to this invariant leads to a state
\* where we transfer some coins from the marker account.
\* This invariant is violated.
NoTransfer ==
  LET denom == "hotdogcoin" IN
  LET Example ==
    /\ tx.type = "transfer-marker"
    /\ tx.denom = denom
    /\ markerStatus[denom] = "ACTIVE"
  IN
  ~Example

\* A counterexample to this invariant leads to a state
\* where we transfer all coins from the marker account.
\* This invariant is violated.
NoDepletingMarker ==
  LET denom == "hotdogcoin" IN
  LET Example ==
    /\ tx.type = "transfer-marker"
    /\ tx.denom = denom
    /\ accounts[denom, denom] = 0
    /\ markerStatus[denom] = "ACTIVE"
  IN
  ~Example

\* Use the following transition predicate for the property above.
NextTransferNoFail ==
    /\ NextNoFail
    /\ tx'.type \in {
        "add-marker", "finalize-marker", "activate-marker",
        "grant-marker", "withdraw-marker",
        "grantz-marker", "transfer-marker"
       }

\* A counterexample to this invariant leads to a state
\* where the manager is allowed to delete the marker.
\* This invariant is violated.
NoDeleteByManager ==
  LET Example ==
    /\ tx.type = "delete-marker"
    /\ \E m \in markers:
        /\ m.denom = tx.denom
        /\ m.accessControl[tx.user] = {}
        /\ m.manager = tx.user
  IN
  ~Example

\* A counterexample to this invariant leads to a state
\* where a marker is created twice under different ownership.
\* This invariant is violated.
\* @type: Seq(STATE) => Bool;
NoRecyclingMarkers(trace) ==
  LET Example ==
    \E i, j \in DOMAIN trace:
      /\ i /= j
      /\ LET tx_i == trace[i].tx
             tx_j == trace[j].tx
         IN
         /\ tx_i.type = "add-marker"
         /\ tx_j.type = "add-marker"
         /\ tx_i.denom = tx_j.denom
         /\ tx_i.user /= tx_j.user
         /\ ~tx_i.fail
         /\ ~tx_j.fail
  IN
  ~Example

\* A counterexample to this invariant leads to a state
\* where a marker is deleted and it burns other coins too.
\* This invariant is violated.
NoBurningOtherCoins ==
  LET Example ==
    /\ tx'.type = "delete-marker"
    /\ tx'.denom = "hotdogcoin"
    /\ ~tx'.fail
    \* the marker account holds all coins of another marker
    /\ markerStatus["coldcatcoin"] = "ACTIVE"
    /\ LET ts == TotalSupply("coldcatcoin") IN
        /\ ts > 0
        /\ accounts["hotdogcoin", "coldcatcoin"] = ts
  IN
  ~Example

====================
