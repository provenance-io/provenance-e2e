---------- MODULE MC_MarkerTransfer ----------
(*
 * This module is tuned towards exploring transfer transactions.
 * We assume that all boilerplate transactions are done and
 * explore only coin transfers. By fixing the initial sequence
 * of transactions, we let the model checker try longer executions.
 *)
EXTENDS Sequences, MC_Marker

VARIABLES
    \* @type: Seq(Str);
    future

InitFuture ==
    /\ Init
    \* the ritual of activating a marker and doing one transfer
    /\ future = <<"add-marker", "grant-marker", "grant-marker", "grant-marker",
        "finalize-marker", "activate-marker", "grantz-marker", "withdraw-marker",
        "transfer-marker">>

NextFuture ==
    /\ Next
    /\  IF Len(future) > 0
        THEN LET expected_type == Head(future) IN
            /\ tx'.type = expected_type
            /\ future' = Tail(future)
        ELSE UNCHANGED future

==============================================
