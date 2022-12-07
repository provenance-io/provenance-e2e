---------------------------------- MODULE Marker ------------------------------
(*
  This specification reconstructs the protcol that operates on markers.
  The main purpose of this specification is to produce CLI tests
  for the `marker` module. Although this specification captures
  many marker transactions precisely (as we can see from positive
  and negative tests), it may be incomplete.
  Use it for testing purposes only.
 *)

EXTENDS Integers, Apalache, typedefs_marker

CONSTANT
  \* available user addresses
  \* @type: Set(ADDR);
  UserAddrs,
  \* available denominations
  \* @type: Set(DENOM);
  DENOMS

VARIABLE
  \* markers in the system
  \* @type: Set(MARKER);
  markers,
  \* marker statuses
  \* @type: DENOM -> Str;
  markerStatus,
  \* bank accounts, including marker accounts
  \* @type: <<ADDR, DENOM>> -> Int;
  accounts,
  \* authz authorization
  \* @type: Set(GRANTZ);
  grantz,
  \* transaction to execute
  \* @type: TX;
  tx,
  \* transaction sequence number
  \* @type: Int;
  tx_no,
  \* is it expected to fail
  \* @type: Bool;
  tx_fail

\* available coin types
MARKER_TYPES == { "COIN", "RESTRICTED" }

\* available marker statuses
MARKER_STATUSES == { "UNSPECIFIED", "PROPOSED",
                     "FINALIZED", "ACTIVE", "CANCELLED" }
\* permissions that can be given to a user
PERMISSIONS == { "mint", "burn", "deposit",
                 "withdraw", "delete", "admin", "transfer" }

\* as in markers, we use the denomination name as an address
ACCOUNT_ADDRS == UserAddrs \union DENOMS

\* maximum supply for a marker
MAX_TOTAL_SUPPLY == 100000000000

\* initial supply of hash on the user accounts
INIT_HASH == 100000000000000000000

(******************** AUXILLIARY OPERATORS *******************************)

\* Calculate the total coin supply across the accounts.
\*
\* @type: DENOM => Int;
TotalSupply(denom) ==
  LET Add(sum, a) == sum + accounts[a, denom] IN
  ApaFoldSet(Add, 0, ACCOUNT_ADDRS)

\* Increase total supply for a denomination.
\*
\* @type: (Int, DENOM) => Bool;
IncreaseSupply(offset, denom) ==
  LET inCirculation == TotalSupply(denom) IN
  LET total == inCirculation + offset IN
  IF total > MAX_TOTAL_SUPPLY
  \* this arm should be unreachable, except that it does in the code :-)
  THEN UNCHANGED <<accounts, markers>>
  ELSE  /\ accounts' = [ accounts EXCEPT ![denom, denom] = @ + offset ]
        /\ \/ \E m \in markers:
            /\ m.denom = denom
            /\ m.isSupplyFixed
            \* top up fixed supply
            /\ LET nm == [ m EXCEPT !.amount = total ] IN
               markers' = (markers \union {nm}) \ {m}
           \/ /\ \A m \in markers: (m.denom = denom => ~m.isSupplyFixed)
              \* keep the marker unchanged
              /\ UNCHANGED markers

\* Decrease total supply for a denomination.
\*
\* @type: (Int, DENOM) => Bool;
DecreaseSupply(offset, denom) ==
  LET inCirculation == TotalSupply(denom) IN
  LET total == inCirculation - offset IN
  /\ accounts' = [ accounts EXCEPT ![denom, denom] = @ - offset ]
  /\ \/ \E m \in markers:
          /\ m.denom = denom
          /\ m.isSupplyFixed
          \* top up fixed supply
          /\ LET nm == [ m EXCEPT !.amount = total ] IN
               markers' = (markers \union {nm}) \ {m}
     \/ /\ \A m \in markers: (m.denom = denom => ~m.isSupplyFixed)
        \* keep the marker unchanged
        /\ UNCHANGED markers

\* Does a user have access to a marker?
\*
\* @type: (MARKER, ADDR, ACCESS) => Bool;
HasPermission(mrkr, user, access) ==
    LET ps == mrkr.accessControl IN
    /\ user \in DOMAIN ps
    /\ access \in ps[user]

(******************* ACTIONS ***************************************)

\* Initialize the protocol.
Init ==
  /\ markers = {}
  /\ markerStatus = [ d \in DENOMS |-> "UNSPECIFIED" ]
  /\ accounts = [ <<a, d>> \in ACCOUNT_ADDRS \X DENOMS |->
                  IF a \in UserAddrs /\ d = "nhash" THEN INIT_HASH ELSE 0 ]
  /\ grantz = {}
  /\ tx_no = 0
  /\ tx = [type |-> "init", fail |-> FALSE]
  /\ tx_fail = FALSE

\* Propose a new marker.
\*
\* @type: (ADDR, Int, DENOM, Str, Bool, Bool) => Bool;
AddMarker(user, amount, denom, markerType, isSupplyFixed, isAllowGovernance) ==
  LET fail ==
    \/ denom = "nhash" \* we should not be able to add 'nhash'
    \/ amount < 0
    \/ \E m \in markers: m.denom = denom
    \* the marker already exists
    \/ markerStatus[denom] /= "UNSPECIFIED"
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ tx' = [
    type                |-> "add-marker",
    user                |-> user,
    amount              |-> amount,
    denom               |-> denom,
    markerType          |-> markerType,
    isSupplyFixed       |-> isSupplyFixed,
    isAllowGovernance   |-> isAllowGovernance,
    fail                |-> fail
    ]
  /\ markerStatus' = [ markerStatus EXCEPT ![denom] = "PROPOSED" ]
  /\ LET \* @type: MARKER;
         newMarker == [
            amount              |-> amount,
            denom               |-> denom,
            manager             |-> user,
            accessControl       |-> [ a \in ACCOUNT_ADDRS |-> {} ],
            markerType          |-> markerType,
            isSupplyFixed       |-> isSupplyFixed,
            isAllowGovernance   |-> isAllowGovernance
         ]
     IN
     markers' = markers \union { newMarker }
  /\ UNCHANGED <<accounts, grantz>>

\* Finalize a proposed marker.
\*
\* @type: (ADDR, DENOM) => Bool;
FinalizeMarker(user, denom) ==
  LET fail ==
    \/ markerStatus[denom] /= "PROPOSED"
    \/ \E m \in markers:
        /\ m.denom = denom
        /\\/ m.manager /= user
           \* Manager finalizes a zero-supply token without mint rights.
           \* There is a special rule about this in Provenance.
          \//\ m.amount = 0
            /\ \A a \in DOMAIN m.accessControl:
                  "mint" \notin m.accessControl[a]
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ tx' = [
        type    |-> "finalize-marker",
        user    |-> user,
        denom   |-> denom,
        fail    |-> fail
    ]
  /\ markerStatus' = [ markerStatus EXCEPT ![denom] = "FINALIZED" ]
  /\ UNCHANGED <<markers, accounts, grantz>>

\* Activate a finalized marker.
\*
\* @type: (ADDR, DENOM) => Bool;
ActivateMarker(user, denom) ==
  LET fail ==
    \/ markerStatus[denom] /= "FINALIZED"
    \/  LET denomSupply == TotalSupply(denom) IN
        \E m \in markers:
          /\ m.denom = denom
          /\\/ m.manager /= user
             \* fail, if the requested marker supply is below the existing one
            \/ m.amount < denomSupply
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ tx' = [
        type    |-> "activate-marker",
        user    |-> user,
        denom   |-> denom,
        fail    |-> fail
    ]
  /\ markerStatus' = [ markerStatus EXCEPT ![denom] = "ACTIVE" ]
  \* Adjust the supply by minting coins.
  \* Note that the implementation mints the difference
  \* between requested supply and supply across all accounts.
  \* We do not do it here, as we start in a predefined initial state,
  \* where no coins except 'nhash' exist.
  /\ \E m \in markers:
       /\ m.denom = denom
       /\  LET toMint == m.amount IN
           accounts' = [ accounts EXCEPT ![denom, denom] = toMint ]
       \* set manager to ""
       /\  LET nm == [ m EXCEPT !.manager = "" ] IN
           markers' = (markers \union { nm }) \ { m }
  /\ UNCHANGED grantz

\* Cancel an active marker.
\*
\* @type: (ADDR, DENOM) => Bool;
CancelMarker(user, denom) ==
  LET status == markerStatus[denom] IN
  LET fail ==
    \/ status \notin { "PROPOSED", "FINALIZED", "ACTIVE" }
    \* all coins should belong to the marker account
    \/ \E a \in ACCOUNT_ADDRS:
         accounts[a, denom] > 0 /\ a /= denom
    \/ \E m \in markers:
         /\ m.denom = denom
         /\\//\ status = "PROPOSED"
             /\ m.manager /= user
           \//\ status /= "PROPOSED"
             /\ ~HasPermission(m, user, "delete")

  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ tx' = [
        type    |-> "cancel-marker",
        user    |-> user,
        denom   |-> denom,
        fail    |-> fail
    ]
  /\ markerStatus' = [ markerStatus EXCEPT ![denom] = "CANCELLED" ]
  /\ UNCHANGED <<markers, accounts, grantz>>

\* Delete a cancelled marker.
\*
\* @type: (ADDR, DENOM) => Bool;
DeleteMarker(user, denom) ==
  LET status == markerStatus[denom] IN
  LET fail ==
    \/ status /= "CANCELLED"
    \* all coins should belong to the marker account
    \/ \E a \in ACCOUNT_ADDRS:
         accounts[a, denom] > 0 /\ a /= denom
    \* the user should have the necessary permissions
    \/ \E m \in markers:
         /\ m.denom = denom
         /\ m.manager /= user
         /\ ~HasPermission(m, user, "delete")
    \* the marker holds coins of another denomination
    \/ \E otherDenom \in DENOMS:
         otherDenom /= denom /\ accounts[denom, otherDenom] > 0
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ tx' = [
        type    |-> "delete-marker",
        user    |-> user,
        denom   |-> denom,
        fail    |-> fail
    ]
  /\ markerStatus' = [ markerStatus EXCEPT ![denom] = "UNSPECIFIED" ]
  /\ \E m \in markers:
       /\ m.denom = denom
       \* a destroyed marker gets deleted in abci.go:BeginBlock
       /\ markers' = markers \ { m }
  /\ UNCHANGED <<accounts, grantz>>

\* Grant access rights to a user.
\*
\* @type: (ADDR, ADDR, DENOM, ACCESS) => Bool;
AddAccess(user, address, denom, access) ==
  LET status == markerStatus[denom] IN
  LET fail ==
    \/ status \notin { "PROPOSED", "FINALIZED", "ACTIVE" }
    \/ \E m \in markers:
         /\ m.denom = denom
         /\\/ IF status = "PROPOSED"
             THEN m.manager /= user
             ELSE ~HasPermission(m, user, "admin")
           \* the same access cannot be granted twice
           \/ HasPermission(m, address, access)
           \/ access = "transfer" /\ m.markerType = "COIN"
           \* the marker itself cannot be assigned an address
           \/ address = denom
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ tx' = [
        type    |-> "grant-marker",
        user    |-> user,
        address |-> address,
        access  |-> access,
        denom   |-> denom,
        fail    |-> fail
    ]
  /\ \E m \in markers:
      /\ m.denom = denom
      /\  LET nm == [ m EXCEPT !.accessControl[address] = @ \union {access} ] IN
          markers' = (markers \ { m }) \union { nm }
  /\ UNCHANGED <<accounts, markerStatus, grantz>>

\* Remove access rights from a user.
\*
\* @type: (ADDR, ADDR, DENOM) => Bool;
RemoveAccess(user, address, denom) ==
  LET status == markerStatus[denom] IN
  LET fail ==
    \/ status \notin { "PROPOSED", "FINALIZED", "ACTIVE" }
    \/ \E m \in markers:
         /\m.denom = denom
         /\\/ IF status = "PROPOSED"
              THEN m.manager /= user
              ELSE ~HasPermission(m, user, "admin")
           \* cannot revoke the mint permission on a zero-supply token
           \/ /\ status = "FINALIZED"
              /\ m.amount = 0
              /\ \A a \in DOMAIN m.accessControl:
                   a /= address => "mint" \notin m.accessControl[a]
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ tx' = [
        type    |-> "revoke-marker",
        user    |-> user,
        address |-> address,
        denom   |-> denom,
        fail    |-> fail
    ]
  /\ \E m \in markers:
      /\ m.denom = denom
      /\  LET nm == [ m EXCEPT !.accessControl[address] = {} ] IN
          markers' = (markers  \ { m }) \union { nm }
  /\ UNCHANGED <<accounts, markerStatus, grantz>>

\* Mint coins for a marker.
\*
\* @type: (ADDR, Int, DENOM) => Bool;
MintMarker(user, amount, denom) ==
  LET fail ==
    \/ amount <= 0
    \/ markerStatus[denom] \notin { "PROPOSED", "FINALIZED", "ACTIVE" }
    \/ TotalSupply(denom) + amount > MAX_TOTAL_SUPPLY
    \/ \E m \in markers:
         /\ m.denom = denom
         /\ ~HasPermission(m, user, "mint")
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ tx' = [
        type    |-> "mint-marker",
        user    |-> user,
        amount  |-> amount,
        denom   |-> denom,
        fail    |-> fail
    ]
  /\ IF markerStatus[denom] = "ACTIVE"
     THEN \* mint coins, optionally updating the marker
          IncreaseSupply(amount, denom)
     ELSE \* update the requested supply without minting coins
        /\ \E m \in markers:
            /\ m.denom = denom
            /\  LET nm == [ m EXCEPT !.amount = @ + amount ] IN
                markers' = (markers \ { m }) \union { nm }
        /\ UNCHANGED accounts
  /\ UNCHANGED <<markerStatus, grantz>>

\* Burn coins for a marker.
\*
\* @type: (ADDR, Int, DENOM) => Bool;
BurnMarker(user, amount, denom) ==
  LET fail ==
    \/ amount <= 0
    \/ markerStatus[denom] \notin { "PROPOSED", "FINALIZED", "ACTIVE" }
    \/  LET denomSupply == TotalSupply(denom) IN
        \E m \in markers:
          /\ m.denom = denom
          /\\/ ~HasPermission(m, user, "burn")
            \/ accounts[denom, denom] < amount
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ tx' = [
        type    |-> "burn-marker",
        user    |-> user,
        amount  |-> amount,
        denom   |-> denom,
        fail    |-> fail
    ]
  /\ IF markerStatus[denom] = "ACTIVE"
     THEN \* mint coins, optionally updating the marker
          DecreaseSupply(amount, denom)
     ELSE \* update the requested supply without burning coins
        /\ \E m \in markers:
            /\ m.denom = denom
            /\  LET nm == [ m EXCEPT !.amount = @ - amount ] IN
                markers' = (markers \ { m }) \union { nm }
        /\ UNCHANGED accounts
  /\ UNCHANGED <<markerStatus, grantz>>

\* Withdraw coins from a marker account.
\*
\* @type: (ADDR, ADDR, Int, DENOM) => Bool;
WithdrawMarker(user, to, amount, denom) ==
  LET fail ==
    \/ amount <= 0
    \/ markerStatus[denom] /= "ACTIVE"
    \/ \E m \in markers:
        /\ m.denom = denom
        /\\/ ~HasPermission(m, user, "withdraw")
          \/ accounts[denom, denom] < amount
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ tx' = [
        type    |-> "withdraw-marker",
        user    |-> user,
        to      |-> to,
        amount  |-> amount,
        denom   |-> denom,
        fail    |-> fail
    ]
  /\ accounts' = [ accounts EXCEPT
        ![denom, denom] = @ - amount,
        ![to, denom] = @ + amount
    ]
  /\ UNCHANGED <<markers, markerStatus, grantz>>

\* Transfer coins from one account on another.
\*
\* @type: (ADDR, ADDR, ADDR, Int, DENOM) => Bool;
TransferMarker(user, from, to, amount, denom) ==
  LET fail ==
    \/ amount <= 0
    \/ markerStatus[denom] \notin { "FINALIZED", "ACTIVE" }
    \/ \A z \in grantz:
        \/ z.grantee /= user
        \/ z.granter /= from
        \/ z.denom /= denom
        \/ z.limit < amount
    \/ \E m \in markers:
        /\ m.denom = denom
        /\\/ m.markerType /= "RESTRICTED"
          \/ ~HasPermission(m, user, "transfer")
          \/ accounts[from, denom] < amount
    \* v1.7.1 does not fail here, see IF-PROVENANCE-13
    \/ /\ to \in DENOMS
       /\ markerStatus[to] = "UNSPECIFIED"
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ tx' = [
        type    |-> "transfer-marker",
        user    |-> user,
        from    |-> from,
        to      |-> to,
        amount  |-> amount,
        denom   |-> denom,
        fail    |-> fail
    ]
  /\ IF from = to
     THEN UNCHANGED accounts
     ELSE accounts' = [ accounts EXCEPT
            ![from, denom] = @ - amount,
            ![to, denom] = @ + amount
          ]
  \* update the authz limits
  /\ \E z \in grantz:
      LET newLimit == z.limit - amount IN
      IF newLimit > 0
      THEN LET nz == [ z EXCEPT !.limit = @ - amount ] IN
            grantz' = (grantz \ { z }) \union { nz }
      ELSE  grantz' = grantz \ { z }
  /\ UNCHANGED <<markers, markerStatus>>

\* Authorize one address to transfer on behalf of another address.
\*
\* @type: (ADDR, ADDR, Int, DENOM) => Bool;
GrantzMarker(user, to, amount, denom) ==
  LET fail ==
    \/ amount <= 0
    \/ user = to
  IN
  \* The following condition is not in the code.
  \* But we add it to make model checking faster.
  /\ markerStatus[denom] = "ACTIVE"
  /\ tx_fail' = (tx_fail \/ fail)
  /\ tx' = [
        type    |-> "grantz-marker",
        user    |-> user,
        to      |-> to,
        amount  |-> amount,
        denom   |-> denom,
        fail    |-> fail
    ]
  \* introdu an authz authorization with a limit
  /\  LET z == [ granter    |-> user,
                 grantee    |-> to,
                 limit      |-> amount,
                 denom      |-> denom ]
      IN
      grantz' = grantz \union { z }
  /\ UNCHANGED <<accounts, markers, markerStatus>>

\* Revoke an authorization that was created with GrantzMarker.
\*
\* @type: (ADDR, ADDR) => Bool;
RevokezMarker(user, to) ==
  LET fail == FALSE IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ tx' = [
        type    |-> "revokez-marker",
        user    |-> user,
        to      |-> to,
        fail    |-> fail
    ]
  \* the following condition is to improve model checking
  /\ \E rec \in grantz:
      /\ rec.granter = user
      /\ rec.grantee = to
  /\ grantz' = { z \in grantz: z.granter /= user \/ z.grantee /= to }
  /\ UNCHANGED <<accounts, markers, markerStatus>>

\* All available protocol transitions
Next ==
  /\ tx_no' = tx_no + 1
  /\ ~tx_fail   \* no previous transaction has failed
  /\\E user \in UserAddrs:
    \/\E amount \in Int:
      \E denom \in DENOMS:
      \E markerType \in MARKER_TYPES:
      \E isSupplyFixed, isAllowGovernance \in BOOLEAN:
        AddMarker(user, amount, denom, markerType,
                  isSupplyFixed, isAllowGovernance)
    \/\E denom \in DENOMS:
        \/ FinalizeMarker(user, denom)
        \/ ActivateMarker(user, denom)
        \/ CancelMarker(user, denom)
        \/ DeleteMarker(user, denom)
        \/ \E address \in ACCOUNT_ADDRS:
           \/ RemoveAccess(user, address, denom)
           \/ \E access \in PERMISSIONS:
               AddAccess(user, address, denom, access)
        \/ \E amount \in Int:
            \/ MintMarker(user, amount, denom)
            \/ BurnMarker(user, amount, denom)
        \/ \E to \in ACCOUNT_ADDRS:
           \E amount \in Int:
            WithdrawMarker(user, to, amount, denom)
        \/ \E from, to \in ACCOUNT_ADDRS:
           \E amount \in Int:
            TransferMarker(user, from, to, amount, denom)
    \/ \E to \in ACCOUNT_ADDRS:
         \/ RevokezMarker(user, to)
         \/ \E denom \in DENOMS:
            \E amount \in Int:
              GrantzMarker(user, to, amount, denom)

\* Protocol transitions, assuming that no transation fails.
NextNoFail ==
    /\ Next
    /\ ~tx_fail'

===============================================================================
