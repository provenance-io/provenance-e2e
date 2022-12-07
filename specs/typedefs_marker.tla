--------------------------- MODULE typedefs_marker ----------------------------

(*
 @typeAlias: ADDR = Str;
 @typeAlias: DENOM = Str;
 @typeAlias: ACCESS = Str;
 @typeAlias: MARKER = [
   amount: Int,
   denom: Str,
   manager: ADDR,
   accessControl: ADDR -> Set(ACCESS),
   markerType: Str,
   isSupplyFixed: Bool,
   isAllowGovernance: Bool
 ];
 @typeAlias: TX = [
   type: Str,
   fail: Bool,
   user: ADDR,
   address: ADDR,
   from: ADDR,
   to: ADDR,
   amount: Int,
   denom: DENOM,
   access: ACCESS,
   markerType: Str,
   isSupplyFixed: Bool,
   isAllowGovernance: Bool
 ];
 @typeAlias: GRANTZ = [
   granter: ADDR,
   grantee: ADDR,
   limit: Int,
   denom: DENOM
 ];
 @typeAlias: STATE = [
   markers: Set(MARKER),
   markerStatus: DENOM -> Str,
   accounts: <<ADDR, DENOM>> -> Int,
   grantz: Set(GRANTZ),
   tx: TX,
   tx_no: Int,
   tx_fail: Bool
 ];
 *)
typedefs_marker_alias == TRUE
===============================================================================
