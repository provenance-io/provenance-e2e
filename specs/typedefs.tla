---------- MODULE typedefs ----------
(*
   @typeAlias: ADDR = Str;
   @typeAlias: SRC = Str;
   @typeAlias: PARTY = Str;
   @typeAlias: DEFTYPE = Str;
   @typeAlias: DESC = Str;
   @typeAlias: CONTRACTSPEC = 
   [
    id: ADDR,
    desc: DESC,
    owners: Set(ADDR),
    parties: Set(PARTY),
    source: SRC,
    classname: Str
   ];
   @typeAlias: SCOPESPEC = 
   [
    id: ADDR,
    desc: DESC,
    owners: Set(ADDR),
    parties: Set(PARTY),
    cspecs: Set(ADDR)
   ];
   @typeAlias: SCOPE =
   [
    id: ADDR,
    sspecId: ADDR,
    owners: Set(ADDR),
    dataAccess: Set(ADDR),
    valueOwnerAddress: ADDR
   ];
   @typeAlias: INSPEC = [name: Str, typeName: Str, source: SRC];   
   @typeAlias: RECORDSPEC = 
   [
    id: ADDR,
    name: Str,
    inputSpecs: Set(INSPEC),
    typeName: Str,
    resultType: DEFTYPE,
    parties: Set(PARTY)
   ];
   @typeAlias: STATUS = Str;
   @typeAlias: INPUT = [name: Str, source: SRC, typeName: Str, status: STATUS];
   @typeAlias: OUTPUT = [hash: Str, status: STATUS];
   @typeAlias: RECORDID = <<Str, ADDR>>;
   @typeAlias: PROCESS = [name: Str, id: ADDR, method: Str];
   @typeAlias: RECORDPARTY = [addr: ADDR, party:PARTY];
   @typeAlias: RECORD = 
   [
    scopeId: ADDR,
    rspecId: ADDR,
    name: Str,
    process: PROCESS,
    inputs: Set(INPUT),
    outputs: Set(OUTPUT),
    recParties: Set(RECORDPARTY),
    cspecId: ADDR,
    sessionId: ADDR
   ];
   @typeAlias: TX =
   [
    type: Str,
    user: ADDR,
    scopeId: ADDR,
    sspecId: ADDR,
    cspecId: ADDR,
    rspecId: ADDR,
    sessionId: ADDR,
    owners: Set(ADDR),
    parties: Set(PARTY),
    recParties: Set(RECORDPARTY),
    source: SRC,
    desc: DESC,
    classname: Str,
    dataAccess: Set(ADDR),
    valueOwnerAddress: ADDR,
    cspecs: Set(ADDR),
    name: Str,
    inputSpecs: Set(INSPEC),
    typeName: Str,
    resultType: DEFTYPE,
    inputs: Set(INPUT),
    outputs: Set(OUTPUT),
    fail: Bool
   ];
   @typeAlias: STATE = [
    contractSpecs: Set(CONTRACTSPEC),
    scopeSpecs: Set(SCOPESPEC),
    scopes: Set(SCOPE),
    recordSpecs: Set(RECORDSPEC),
    records: Set(RECORD),
    tx: TX,
    tx_no: Int,
    tx_fail: Bool
   ];
*)
MetadataTypeAliases == TRUE

====================
