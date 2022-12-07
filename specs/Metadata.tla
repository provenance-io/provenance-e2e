---------- MODULE Metadata ----------

EXTENDS Integers, typedefs

CONSTANT 
  \* @type: Set(ADDR);
  ContractSpecAddrs,
  \* @type: Set(ADDR);
  ScopeSpecAddrs,
  \* @type: Set(ADDR);
  ScopeAddrs,
  \* @type: Set(ADDR);
  RecordSpecAddrs,
  \* @type: Set(DESC);
  Descriptions,
  \* @type: Set(ADDR);
  UserAddrs,
  \* @type: Set(Str);
  Hashes,
  \* @type: Set(Str);
  ClassNames,
  \* @type: Set(Str);
  RecordNames,
  \* @type: Set(Str);
  TypeNames,
  \* @type: Set(Str);
  InputNames,
  \* @type: Set(Str);
  ProcessNames,
  \* @type: Set(Str);
  MethodNames,
  \* @type: Str -> Str;
  RecSpecCtrSpecPairing,
  \* @type: <<Str,Str>> -> Str;
  CSpecAndNameToRSpec

VARIABLE
  \* @type: Set(CONTRACTSPEC);
  contractSpecs,
  \* @type: Set(SCOPESPEC);
  scopeSpecs,
  \* @type: Set(SCOPE);
  scopes,
  \* @type: Set(RECORDSPEC);
  recordSpecs,
  \* @type: Set(RECORD);
  records,
  \* @type: TX;
  tx,
  \* @type: Int;
  tx_no,
  \* @type: Bool;
  tx_fail

\* @type: () => <<Set(CONTRACTSPEC),Set(SCOPESPEC), Set(SCOPE), Set(RECORDSPEC), Set(RECORD)>>;
vars == <<contractSpecs, scopeSpecs, scopes, recordSpecs, records>>
\* @type: () => <<Set(SCOPESPEC),Set(SCOPE), Set(RECORDSPEC), Set(RECORD)>>;
varsNoCspecs == <<scopeSpecs, scopes, recordSpecs, records>>
\* @type: () => <<Set(CONTRACTSPEC),Set(SCOPE), Set(RECORDSPEC), Set(RECORD)>>;
varsNoSspecs == <<contractSpecs, scopes, recordSpecs, records>>
\* @type: () => <<Set(CONTRACTSPEC),Set(SCOPESPEC), Set(RECORDSPEC), Set(RECORD)>>;
varsNoScopes == <<contractSpecs, scopeSpecs, recordSpecs, records>>
\* @type: () => <<Set(CONTRACTSPEC),Set(SCOPESPEC), Set(SCOPE), Set(RECORD)>>;
varsNoRspecs == <<contractSpecs, scopeSpecs, scopes, records>>
\* @type: () => <<Set(CONTRACTSPEC),Set(SCOPESPEC), Set(SCOPE), Set(RECORDSPEC)>>;
varsNoRecords == <<contractSpecs, scopeSpecs, scopes, recordSpecs>>

Parties == {
  "UNSPECIFIED", \* what can this party do?
  "ORIGINATOR",
  "SERVICER",
  "INVESTOR",
  "CUSTODIAN",
  "OWNER",
  "AFFILIATE",
  "OMNIBUS",
  "PROVENANCE"
}

\* @type: Set(RECORDPARTY);
RecParties == 
  [ 
    addr: UserAddrs,
    party: Parties
  ]

DefinitionType == {
  "UNSPECIFIED",
  "PROPOSED",
  "RECORD",
  "RECORD_LIST"
}

InputStatuses == {
  "UNKNOWN",
  "PROPOSED",
  "RECORD"
}

OutputStatuses == {
  "UNSPECIFIED",
  "PASS",
  "SKIP",
  "FAIL"
}

Sources == UserAddrs \union Hashes
\* @type: Set(INSPEC);
InputSpecs ==
  [
    name: InputNames,
    typeName: TypeNames,
    source: Sources
  ]

\* @type: Set(INPUT);
Inputs == 
  [
    name: InputNames,
    typeName: TypeNames,
    source: Sources,
    status: InputStatuses
  ]

\* @type: Set(OUTPUT);
Outputs == 
  [
    hash: Hashes,
    status: OutputStatuses
  ]

\* @type: Set(PROCESS);
Processes ==
  [
    name: ProcessNames,
    id: Sources,
    method: MethodNames
  ]

\* Possibly extends later
SessionAddrs == ContractSpecAddrs

\*********************
\* Optimizations for testing

RestrictedUserAddrs == { "user1" }
RestrictedParties == {"OWNER"}
\* @type: Set(RECORDPARTY);
RestrictedRecParties == 
  [ 
    addr: RestrictedUserAddrs, 
    party: RestrictedParties 
  ]
RestrictedDefinitionType == DefinitionType
RestrictedInputStatuses == InputStatuses
RestrictedOutputStatuses == OutputStatuses 
RestrictedSources == RestrictedUserAddrs \union Hashes
\* @type: Set(INSPEC);
RestrictedInputSpecs ==
  [
    name: InputNames,
    typeName: TypeNames,
    source: RestrictedSources
  ]

\* @type: Set(INPUT);
RestrictedInputs == 
  [
    name: InputNames,
    typeName: TypeNames,
    source: RestrictedSources,
    status: {"PROPOSED"}
  ]
RestrictedOutputs == Outputs
\* @type: Set(PROCESS);
RestrictedProcesses ==
  [
    name: ProcessNames,
    id: RestrictedSources,
    method: MethodNames
  ]


AllTx == {
  "write-contract-specification",
  "remove-contract-specification",
  "write-scope-specification",
  "remove-scope-specification",
  "add-contract-spec-to-scope-spec",
  "remove-contract-spec-from-scope-spec",
  "write-scope",
  "remove-scope",
  "scope-data-access add",
  "scope-data-access remove",
  "scope-owners add",
  "scope-owners remove",
  "write-record-specification",
  "remove-record-specification",
  "write-record",
  "remove-record"
}

AllowedTx == AllTx

\*********************



Init == 
  /\ contractSpecs = {}
  /\ scopeSpecs = {}
  /\ scopes = {}
  /\ recordSpecs = {}
  /\ records = {}
  /\ tx_no = 0
  /\ tx = [type |-> "init", fail |-> FALSE]
  /\ tx_fail = FALSE

\* record IDs are uniquely defined by scope id and name
\* @type: (RECORD) => RECORDID;
RecordId(record) == << record.name, record.scopeId >>
\* @type: () => Set(RECORDID);
RecordAddrs == RecordNames \X ScopeAddrs

\* @type: () => Set(ADDR);
ActiveContractSpecIds == { cs.id : cs \in contractSpecs }
\* @type: () => Set(ADDR);
ActiveScopeSpecIds == { ss.id : ss \in scopeSpecs }
\* @type: () => Set(ADDR);
ActiveScopeIds == { s.id : s \in scopes }
\* @type: () => Set(ADDR);
ActiveRecordSpecIds == { rs.id : rs \in recordSpecs }
\* @type: () => Set(RECORDID);
ActiveRecordIds == { RecordId(r) : r \in records }

\* @type: (ADDR) => Bool;
IsActiveContractSpecId(cspecId) == cspecId \in ActiveContractSpecIds
\* @type: (ADDR) => Bool;
IsActiveScopeSpecId(sspecId) == sspecId \in ActiveScopeSpecIds
\* @type: (ADDR) => Bool;
IsActiveScopeId(sId) == sId \in ActiveScopeIds
\* @type: (ADDR) => Bool;
IsActiveRecordSpecId(rspecId) == rspecId \in ActiveRecordSpecIds
\* @type: (RECORDID) => Bool;
IsActiveRecordId(rId) == rId \in ActiveRecordIds

\* @type: (ADDR) => Bool;
IsValidContractSpecId(cspecId) == cspecId \in ContractSpecAddrs
\* @type: (CONTRACTSPEC) => Bool;
IsValidContractSpec(cspec) ==
  /\ IsValidContractSpecId(cspec.id)
  /\ cspec.owners /= {}
  /\ cspec.parties /= {}
  /\ "UNSPECIFIED" \notin cspec.parties
  /\ cspec.source \in UserAddrs

\* @type: (ADDR) => Bool;
IsValidScopeSpecId(sspecId) == sspecId \in ScopeSpecAddrs
\* @type: (SCOPESPEC) => Bool;
IsValidScopeSpec(sspec) == 
  /\ IsValidScopeSpecId(sspec.id)
  /\ sspec.owners /= {}
  /\ sspec.parties /= {}
  /\ "UNSPECIFIED" \notin sspec.parties
  /\ sspec.cspecs /= {}
\* @type: (ADDR) => Bool;
IsValidScopeId(sId) == sId \in ScopeAddrs
\* @type: (SCOPE) => Bool;
IsValidScope(scope) ==
  /\ IsValidScopeId(scope.id)
  /\ scope.owners /= {}
  /\ scope.dataAccess /= {}
\* @type: (ADDR) => Bool;
IsValidRecordSpecId(rspecId) == rspecId \in RecordSpecAddrs
\* @type: (RECORDSPEC) => Bool;
IsValidRecordSpec(rspec) ==
  /\ IsValidRecordSpecId(rspec.id)
  /\ rspec.inputSpecs /= {}
  /\ rspec.parties /= {}
  /\ "UNSPECIFIED" \notin rspec.parties
  /\ rspec.resultType /= "UNSPECIFIED"
IsValidRecordId(rId) == rId \in RecordAddrs
\* @type: (INPUT) => Bool;
IsValidRecordInput(input) ==
  /\ input.status /= "UNKNOWN"
  /\ input.source \in Hashes <=> input.status = "PROPOSED"
  \* /\ IsValidRecordId(input.source) \* problem: record IDs are bad for us
\* @type: (OUTPUT) => Bool;
IsValidRecordOutput(output) ==
  /\ output.status /= "UNSPECIFIED"
\* @type: (RECORD) => Bool;
IsValidRecord(record) ==
  /\ IsValidRecordId(RecordId(record))
  /\ record.inputs /= {}
  /\ \A input \in record.inputs: IsValidRecordInput(input)
  /\ record.outputs /= {}
  /\ \A output \in record.outputs: IsValidRecordOutput(output)
  /\ record.recParties /= {}
  /\ \A rp \in record.recParties: rp.party /= "UNSPECIFIED"

\* @type: (ADDR, CONTRACTSPEC) => Bool;
WriteContractSpec(user, cspec) == 
  LET fail ==
     \/ ~IsValidContractSpec(cspec) 
     \/ IsActiveContractSpecId(cspec.id)
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ contractSpecs' = contractSpecs \union {cspec}
  /\ tx' = [
        type      |-> "write-contract-specification",
        cspecId   |-> cspec.id,
        user      |-> user,
        owners    |-> cspec.owners,
        parties   |-> cspec.parties,
        source    |-> cspec.source,
        desc      |-> cspec.desc,
        classname |-> cspec.classname,
        fail      |-> fail
     ]
  /\ UNCHANGED varsNoCspecs

\* @type: (ADDR, ADDR) => Bool;
RemoveContractSpec(user, cspecId) == 
  LET UserIsOwner == 
    \E cs \in contractSpecs:
            \/ cspecId = cs.id
            \/ cs.owners = {user}
  IN
  LET InUse == 
    { ss \in scopeSpecs: cspecId \in ss.cspecs } /= {}
  IN
  LET fail ==
      \/ ~IsValidContractSpecId(cspecId)
      \/ ~IsActiveContractSpecId(cspecId)
      \/ ~UserIsOwner    
      \/ InUse
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ contractSpecs' = { cs \in contractSpecs: cs.id /= cspecId }
  /\ recordSpecs' = { rs \in recordSpecs: RecSpecCtrSpecPairing[rs.id] /= cspecId } \* remove associated rspecs
  /\ tx' = [
         type       |-> "remove-contract-specification",
         user       |-> user,
         cspecId    |-> cspecId,
         fail       |-> fail
     ]   
  /\ UNCHANGED <<contractSpecs, scopeSpecs, scopes, records>>

\* @type: (ADDR, SCOPESPEC) => Bool;
WriteScopeSpec(user, sspec) == 
  LET AllCSpecsActive == 
    \A cspecId \in sspec.cspecs: IsActiveContractSpecId(cspecId)
  IN
  LET fail == 
    \/ ~IsValidScopeSpec(sspec) 
    \/ IsActiveScopeSpecId(sspec.id)
    \/ ~AllCSpecsActive
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ scopeSpecs' = scopeSpecs \union {sspec}
  /\ tx' = [
    type    |-> "write-scope-specification",
    user    |-> user, 
    sspecId |-> sspec.id,
    owners  |-> sspec.owners,
    parties |-> sspec.parties,
    desc    |-> sspec.desc,
    cspecs  |-> sspec.cspecs,
    fail    |-> fail
    ]
  /\ UNCHANGED varsNoSspecs

\* @type: (ADDR, ADDR) => Bool;
RemoveScopeSpec(user, sspecId) == 
  LET UserIsOwner == 
    \E ss \in scopeSpecs:
            \/ sspecId = ss.id
            \/ ss.owners = {user}
  IN
  LET InUse == 
    \E scope \in scopes:
      scope.sspecId = sspecId
  IN
  LET fail == 
    \/ ~IsValidScopeSpecId(sspecId)
    \/ ~IsActiveScopeSpecId(sspecId)
    \/ ~UserIsOwner
    \/ InUse
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ scopeSpecs' = { ss \in scopeSpecs: ss.id /= sspecId }
  /\ tx' = [
      type    |-> "remove-scope-specification",
      user    |-> user,
      sspecId |-> sspecId,
      fail    |-> fail
    ]
  /\ UNCHANGED varsNoSspecs

\* @type: (ADDR,ADDR,ADDR) => Bool;
AddContractSpecToScopeSpec(user, cspecId, sspecId) == 
  LET CSpecAlreadyAdded ==
    \E sspec \in scopeSpecs:
      /\ sspec.id = sspecId
      /\ cspecId \in sspec.cspecs
  IN
  LET fail ==
    \/ ~IsValidContractSpecId(cspecId)
    \/ ~IsActiveContractSpecId(cspecId)
    \/ ~IsValidScopeSpecId(sspecId)
    \/ ~IsActiveScopeSpecId(sspecId)
    \/ CSpecAlreadyAdded
  IN
  /\ tx_fail' = (tx_fail \/ fail)      
  /\ scopeSpecs' =
    {
      IF sspec.id = sspecId
      THEN [sspec EXCEPT !.cspecs = @ \union {cspecId}]
      ELSE sspec
      : sspec \in scopeSpecs
    }
  /\ tx' = [
    type    |-> "add-contract-spec-to-scope-spec",
    user    |-> user,
    sspecId |-> sspecId,
    cspecId |-> cspecId,
    fail    |-> fail
    ]
  /\ UNCHANGED varsNoSspecs 

\* @type: (ADDR,ADDR,ADDR) => Bool;
RemoveContractSpecFromScopeSpec(user, cspecId, sspecId) == 
  LET CSpecNotPresent == 
    \E sspec \in scopeSpecs:
      /\ sspec.id = sspecId
      /\ cspecId \notin sspec.cspecs
  IN
  LET fail ==
    \/ ~IsValidContractSpecId(cspecId)
    \/ ~IsActiveContractSpecId(cspecId)
    \/ ~IsValidScopeSpecId(sspecId)
    \/ ~IsActiveScopeSpecId(sspecId)
    \/ CSpecNotPresent
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ scopeSpecs' = 
    {
      IF sspec.id = sspecId
      THEN [sspec EXCEPT !.cspecs = @ \ {cspecId}]
      ELSE sspec
      : sspec \in scopeSpecs
    }
  /\ tx' = [
    type    |-> "remove-contract-spec-from-scope-spec",
    user    |-> user,
    sspecId |-> sspecId,
    cspecId |-> cspecId,
    fail    |-> fail
    ]
  /\ UNCHANGED varsNoSspecs 

\* @type: (ADDR, SCOPE) => Bool;
WriteScope(user, scope) ==
  LET fail == 
    \/ ~IsValidScope(scope) 
    \/ IsActiveScopeId(scope.id)
    \/ ~IsActiveScopeSpecId(scope.sspecId)
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ scopes' = scopes \union {scope}
  /\ tx' = [
    type              |-> "write-scope",
    user              |-> user,
    scopeId           |-> scope.id,
    sspecId           |-> scope.sspecId,
    owners            |-> scope.owners,
    dataAccess        |-> scope.dataAccess,
    valueOwnerAddress |-> scope.valueOwnerAddress,
    fail              |-> fail
    ]
  /\ UNCHANGED varsNoScopes

\* @type: (ADDR, ADDR) => Bool;
RemoveScope(user, scopeId) == 
  LET isOwner == 
    \E scope \in scopes:
      /\ scope.scopeId = scopeId
      /\ user \in scope.owners
  IN 
  LET fail == 
    \/ ~IsValidScopeId(scopeId)
    \/ ~IsActiveScopeId(scopeId)
    \/ ~isOwner
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ scopes' = { s \in scopes: s.id /= scopeId }
  /\ tx' = [
      type    |-> "remove-scope",
      user    |-> user,
      scopeId |-> scopeId,
      fail    |-> fail
    ]
  /\ UNCHANGED varsNoScopes

\* @type: (ADDR, ADDR, Set(ADDR)) => Bool;
AddScopeDataAccess(user, scopeId, dataAccess) == 
  LET DataAccessToAddNotNew ==
    \E scope \in scopes:
      /\ scope.id = scopeId
      /\ scope.dataAccess \intersect dataAccess /= {}
  IN
  LET fail ==
    \/ ~IsValidScopeId(scopeId)
    \/ ~IsActiveScopeId(scopeId)
    \/ dataAccess = {}
    \/ DataAccessToAddNotNew
  IN
  /\ tx_fail' = (tx_fail \/ fail)      
  /\ scopes' = {
      IF scope.id = scopeId
      THEN [scope EXCEPT !.dataAccess = @ \union dataAccess]
      ELSE scope
      : scope \in scopes
    }
  /\ tx' = [
    type       |-> "scope-data-access add",
    user       |-> user,
    scopeId    |-> scopeId,
    dataAccess |-> dataAccess,
    fail       |-> fail
    ]
  /\ UNCHANGED varsNoScopes 

\* @type: (ADDR, ADDR, Set(ADDR)) => Bool;
RemoveScopeDataAccess(user, scopeId, dataAccess) == 
  LET DataAccessNotPresent ==
    \E scope \in scopes:
      /\ scope.id = scopeId
      /\ \E da \in dataAccess:
        da \notin scope.dataAccess
  IN
  LET fail ==
    \/ ~IsValidScopeId(scopeId)
    \/ ~IsActiveScopeId(scopeId)
    \/ dataAccess = {}
    \/ DataAccessNotPresent
  IN
  /\ tx_fail' = (tx_fail \/ fail)      
  /\ scopes' = {
      IF scope.id = scopeId
      THEN [scope EXCEPT !.dataAccess = @ \ dataAccess]
      ELSE scope
      : scope \in scopes
    }
  /\ tx' = [
    type       |-> "scope-data-access remove",
    user       |-> user,
    scopeId    |-> scopeId,
    dataAccess |-> dataAccess,
    fail       |-> fail
    ]
  /\ UNCHANGED varsNoScopes 

\* @type: (ADDR, ADDR, Set(ADDR)) => Bool;
AddScopeOwners(user, scopeId, owners) == 
  LET OwnersToAddNotNew ==
    \E scope \in scopes:
      /\ scope.id = scopeId
      /\ scope.owners \intersect owners /= {}
  IN
  LET fail ==
    \/ ~IsValidScopeId(scopeId)
    \/ ~IsActiveScopeId(scopeId)
    \/ owners = {}
    \/ OwnersToAddNotNew
  IN
  /\ tx_fail' = (tx_fail \/ fail)      
  /\ scopes' = {
      IF scope.id = scopeId
      THEN [scope EXCEPT !.owners = @ \union owners]
      ELSE scope
      : scope \in scopes
    }
  /\ tx' = [
    type    |-> "scope-owners add",
    user    |-> user,
    scopeId |-> scopeId,
    owners  |-> owners,
    fail    |-> fail
    ]
  /\ UNCHANGED varsNoScopes 

\* @type: (ADDR, ADDR, Set(ADDR)) => Bool;
RemoveScopeOwners(user, scopeId, owners) == 
  LET OwnersNotPresent ==
    \E scope \in scopes:
      /\ scope.id = scopeId
      /\ \E owner \in owners:
        owner \notin scope.owners
  IN
  LET RemoveLast == 
    \E scope \in scopes:
      /\ scope.id = scopeId
      /\ scope.owners \ owners = {}
  IN
  LET fail ==
    \/ ~IsValidScopeId(scopeId)
    \/ ~IsActiveScopeId(scopeId)
    \/ owners = {}
    \/ OwnersNotPresent
    \/ RemoveLast
  IN
  /\ tx_fail' = (tx_fail \/ fail)      
  /\ scopes' = {
      IF scope.id = scopeId
      THEN [scope EXCEPT !.owners = @ \ owners]
      ELSE scope
      : scope \in scopes
    }
  /\ tx' = [
    type    |-> "scope-owners remove",
    user    |-> user,
    scopeId |-> scopeId,
    owners  |-> owners,
    fail    |-> fail
    ]
  /\ UNCHANGED varsNoScopes 

\* @type: (ADDR, RECORDSPEC) => Bool;
WriteRecordSpec(user, rspec) ==
  LET cspecPairId == RecSpecCtrSpecPairing[rspec.id]
  IN
  LET MatchesName == 
    CSpecAndNameToRSpec[cspecPairId, rspec.name] = rspec.id
  IN
  LET isCSpecOwner == \E cspec \in contractSpecs:
    /\ cspec.id = cspecPairId
    /\ cspec.owners = {user}
  IN 
  LET fail ==
     \/ ~IsValidRecordSpec(rspec) 
     \/ ~IsActiveContractSpecId(cspecPairId)
     \/ IsActiveRecordSpecId(rspec.id)
     \/ ~isCSpecOwner
     \/ ~MatchesName
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ recordSpecs' = recordSpecs \union {rspec}
  /\ tx' = [
        type       |-> "write-record-specification",
        user       |-> user,
        rspecId    |-> rspec.id,
        name       |-> rspec.name,
        inputSpecs |-> rspec.inputSpecs,
        typeName   |-> rspec.typeName,
        resultType |-> rspec.resultType,
        parties    |-> rspec.parties,
        fail       |-> fail
     ]
  /\ UNCHANGED varsNoRspecs

\* @type: (ADDR, ADDR) => Bool;
RemoveRecordSpec(user, rspecId) == 
  LET cspecPairId == RecSpecCtrSpecPairing[rspecId]
  IN
  LET isCSpecOwner == \E cspec \in contractSpecs:
    /\ cspec.id = cspecPairId
    /\ cspec.owners = {user}
  IN 
  LET fail == 
    \/ ~IsValidRecordSpecId(rspecId)
    \/ ~IsActiveRecordSpecId(rspecId)
    \/ ~isCSpecOwner
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ recordSpecs' = { rs \in recordSpecs: rs.id /= rspecId }
  /\ tx' = [
      type    |-> "remove-record-specification",
      user    |-> user,
      rspecId |-> rspecId,
      fail    |-> fail
    ]
  /\ UNCHANGED varsNoRspecs

\* @type: (ADDR, RECORD) => Bool;
WriteRecord(user, record) == 
  LET RecIdCorrectForCSpecAndName == 
    record.rspecId = CSpecAndNameToRSpec[record.cspecId, record.name]
  IN
  LET SpecAndRecordInputsMatch == 
    \E rspec \in recordSpecs:
      /\ rspec.id = record.rspecId
      /\ rspec.name = record.name
      /\ LET
            \*@type: Set(<<Str,Str,Str>>);
            InputTups == { <<input.name, input.typeName, input.source>>: input \in record.inputs }
            \*@type: Set(<<Str,Str,Str>>);
            InputSpecTups == { <<inputSpec.name, inputSpec.typeName, inputSpec.source>>: inputSpec \in rspec.inputSpecs }
          IN InputTups = InputSpecTups
  IN
  LET OwnsCS ==
    \E cs \in contractSpecs:
      /\ cs.id = record.cspecId
      /\ cs.owners = {user}
  IN
  LET cspecIdInSSpec == 
    \E scope \in scopes:
      /\ scope.id = record.scopeId
      /\ \E sspec \in scopeSpecs:
        /\ sspec.id = scope.sspecId
        /\ record.cspecId \in sspec.cspecs
  IN
  LET ValidParties == \* (we forcve singluar owner)
    /\ \A party \in record.recParties: party.addr = user
    /\ \E party \in record.recParties: party.party = "OWNER"
  IN
  LET fail ==
     \/ ~IsValidRecord(record) 
     \/ IsActiveRecordId(RecordId(record))
     \/ ~IsActiveScopeId(record.scopeId)
     \/ ~IsActiveRecordSpecId(record.rspecId)
     \/ ~IsActiveContractSpecId(record.cspecId)
     \/ ~SpecAndRecordInputsMatch
     \/ ~ValidParties
     \/ ~OwnsCS
     \/ ~RecIdCorrectForCSpecAndName
     \/ ~cspecIdInSSpec
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ records' = records \union {record}
  /\ tx' = [
        type       |-> "write-record",
        user       |-> user,
        scopeId    |-> record.scopeId,
        rspecId    |-> record.rspecId,
        name       |-> record.name,
        process    |-> record.process,
        inputs     |-> record.inputs,
        outputs    |-> record.outputs,
        recParties |-> record.recParties,
        cspecId    |-> record.cspecId,
        sessionId  |-> record.sessionId,
        fail       |-> fail
     ]
  /\ UNCHANGED varsNoRecords

\* @type: (ADDR, RECORDID) => Bool;
RemoveRecord(user, rId) == 
  LET fail == 
    \/ ~IsValidRecordId(rId)
    \/ ~IsActiveRecordId(rId)
  IN
  /\ tx_fail' = (tx_fail \/ fail)
  /\ records' = { r \in records: RecordId(r) /= rId }
  /\ tx' = [
      type     |-> "remove-record",
      user     |-> user,
      name     |-> rId[1],
      scopeId  |-> rId[2],
      fail     |-> fail
    ]
  /\ UNCHANGED varsNoRecords

Next == 
  /\ tx_no' = tx_no + 1
  /\ \E user \in RestrictedUserAddrs:
    \* CONTRACT SPECS
    \/ \E cspecId \in ContractSpecAddrs:
       \E desc \in Descriptions:
       \E owners \in SUBSET RestrictedUserAddrs:
       \E parties \in SUBSET RestrictedParties:
       \E src \in RestrictedSources:
       \E classname \in ClassNames:
          WriteContractSpec(user, [
            id        |-> cspecId,
            desc      |-> desc,
            owners    |-> owners,
            parties   |-> parties,
            source    |-> src,
            classname |-> classname
          ])
    \/ \E cspecId \in ContractSpecAddrs: 
          RemoveContractSpec(user, cspecId)
    \* SCOPE SPECS
    \/ \E sspecId \in ScopeSpecAddrs:
       \E desc \in Descriptions:
       \E owners \in SUBSET RestrictedUserAddrs:
       \E parties \in SUBSET RestrictedParties:
       \E cspecs \in SUBSET ContractSpecAddrs:
          WriteScopeSpec(user, [
            id      |-> sspecId,
            desc    |-> desc,
            owners  |-> owners,
            parties |-> parties,
            cspecs  |-> cspecs
          ])
    \/ \E sspecId \in ScopeSpecAddrs:
          RemoveScopeSpec(user, sspecId)
    \/ \E sspecId \in ScopeSpecAddrs:
       \E cspecId \in ContractSpecAddrs:
          \/ AddContractSpecToScopeSpec(user, cspecId, sspecId)
          \/ RemoveContractSpecFromScopeSpec(user, cspecId, sspecId)
    \* SCOPES
    \/ \E scopeId \in ScopeAddrs:
       \E sspecId \in ScopeSpecAddrs:
       \E owners \in SUBSET RestrictedUserAddrs:
       \E dataAccess \in SUBSET RestrictedUserAddrs:
       \E valueOwnerAddress \in RestrictedUserAddrs:
          WriteScope(user, [
            id                |-> scopeId,
            sspecId           |-> sspecId,
            owners            |-> owners,
            dataAccess        |-> dataAccess,
            valueOwnerAddress |-> valueOwnerAddress
          ])
    \/ \E scopeId \in ScopeAddrs:
          RemoveScope(user, scopeId)
    \/ \E scopeId \in ScopeAddrs:
       \E dataAccess \in SUBSET RestrictedUserAddrs:
          \/ AddScopeDataAccess(user, scopeId, dataAccess)
          \/ RemoveScopeDataAccess(user, scopeId, dataAccess)
    \/ \E scopeId \in ScopeAddrs:
       \E owners \in SUBSET RestrictedUserAddrs:
          \/ AddScopeOwners(user, scopeId, owners)
          \/ RemoveScopeOwners(user, scopeId, owners)
    \* RECORD SPECS
    \/ \E rspecId \in RecordSpecAddrs:
       \E name \in RecordNames:
       \* \E inputSpecs \in SUBSET InputSpecs:
       \E inputSpecs \in InputSpecs:
       \E typeName \in TypeNames:
       \E resultType \in RestrictedDefinitionType:
       \E parties \in SUBSET RestrictedParties:
          WriteRecordSpec(user, [
            id         |-> rspecId,
            name       |-> name,
            inputSpecs |-> {inputSpecs},
            typeName   |-> typeName,
            resultType |-> resultType,
            parties    |-> parties
          ])
    \/ \E rspecId \in RecordSpecAddrs:
          RemoveRecordSpec(user, rspecId)
    \* RECORDS
    \/ \E scopeId \in ScopeAddrs:
       \E rspecId \in RecordSpecAddrs:
       \E name \in RecordNames:
       \E process \in RestrictedProcesses:
       \* \E inputs \in SUBSET RestrictedInputs:
       \* \E outputs \in SUBSET RestrictedOutputs:
       \* \E recParties \in SUBSET RestrictedRecParties:
       \E inputs \in RestrictedInputs:
       \E outputs \in RestrictedOutputs:
       \E recParties \in RestrictedRecParties:
       \E cspecId \in ContractSpecAddrs:
       \E sessionId \in SessionAddrs:
          WriteRecord(user, [
            scopeId    |-> scopeId,
            rspecId    |-> rspecId,
            name       |-> name,
            process    |-> process,
            inputs     |-> {inputs},
            outputs    |-> {outputs},
            recParties |-> {recParties},
            cspecId    |-> cspecId,
            sessionId  |-> sessionId
          ])
    \/ \E rId \in RecordAddrs:
          RemoveRecord(user, rId)
  /\ tx'.type \in AllowedTx


====================
