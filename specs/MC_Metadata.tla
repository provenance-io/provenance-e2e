---------- MODULE MC_Metadata ----------

EXTENDS FiniteSets, typedefs

\* @type: Set(ADDR);
ContractSpecAddrs == {"contractspec1"}
\* ContractSpecAddrs == {"contractspec1", "contractspec2", "contractspec3"}
\* @type: Set(ADDR);
ScopeSpecAddrs == {"scopespec1", "scopespec2", "scopespec3"}
\* @type: Set(ADDR);
ScopeAddrs == {"scope1", "scope2", "scope3"}
\* @type: Set(ADDR);
RecordSpecAddrs == {
  "recordspec11", "recordspec12", "recordspec13",
  "recordspec21", "recordspec22", "recordspec23"
  }
\* @type: Set(DESC);
Descriptions == {"A","B","C"}
\* @type: Set(ADDR);
UserAddrs == {"user1", "user2"}
\* @type: Set(Str);
Hashes == { "hash1", "hash2" }
\* @type: Set(Str);
ClassNames == {"class1", "class2"}  
\* @type: Set(Str);
RecordNames == {"recordName1", "recordName2"}  
\* @type: Set(Str);
TypeNames == {"type1", "type2", "type3"}
\* @type: Set(Str);
InputNames == {"input1", "input2", "input3"}
\* @type: Set(Str);
ProcessNames == {"process1", "process2", "process3"}
\* @type: Set(Str);
MethodNames == {"foo", "bar", "baz"}
\* @type: Str -> Str;
RecSpecCtrSpecPairing ==
    [ addrUsr \in RecordSpecAddrs |->  
        CASE addrUsr = "recordspec11" -> "contractspec1"
        []   addrUsr = "recordspec12" -> "contractspec2"
        []   addrUsr = "recordspec13" -> "contractspec3"
        []   addrUsr = "recordspec21" -> "contractspec1"
        []   addrUsr = "recordspec22" -> "contractspec2"
        [] OTHER -> "contractspec3"
    ]
\* @type: <<Str,Str>> -> Str;
CSpecAndNameToRSpec == 
    [ addrUsr \in ContractSpecAddrs \X RecordNames |->  
        CASE addrUsr = <<"contractspec1", "recordName1">> -> "recordspec11"
        []   addrUsr = <<"contractspec2", "recordName1">> -> "recordspec12"
        []   addrUsr = <<"contractspec3", "recordName1">> -> "recordspec13"
        []   addrUsr = <<"contractspec1", "recordName2">> -> "recordspec21"
        []   addrUsr = <<"contractspec2", "recordName2">> -> "recordspec22"
        [] OTHER -> "recordspec23"
    ]


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

INSTANCE Metadata

TxTypeView == tx.type

InvFalse == FALSE
TxFail == tx_no > 3 => tx_fail
TxNoFail == ~TxFail
ExistsContractSpecWithNoOwners == tx_no > 3 => \E cs \in contractSpecs: cs.owners = {}
ExistsContractSpecWithNoParties == tx_no > 3 => \E cs \in contractSpecs: cs.parties = {}

\* a transaction is added and then removed
\*
\* @type: Seq(STATE) => Bool;
AddThenRemove(trace) ==
    LET Example ==
    /\ \A i \in DOMAIN trace:
        LET tx_i == trace[i].tx IN
        /\ tx_i.type \in { "write-contract-specification", "write-scope-specification" }
            => Cardinality(tx_i.owners) = 1
        /\ ~tx_i.fail
    /\ \E i, j \in DOMAIN trace:
        /\ i < j
        /\ LET tx_i == trace[i].tx
               tx_j == trace[j].tx
           IN 
            /\ tx_i.type = "write-contract-specification"
            /\ tx_j.type = "remove-contract-specification"
            /\ tx_i.cspecId = tx_j.cspecId
    IN
    ~Example

\* a contract spec/scope spec interation
\*
\* @type: Seq(STATE) => Bool;
AddThenRemoveCtr(trace) ==
    LET Example ==
    /\ \A i \in DOMAIN trace:
        LET tx_i == trace[i].tx IN
        /\ tx_i.type \in { 
            "write-contract-specification", 
            "write-scope-specification"
            }
            => Cardinality(tx_i.owners) = 1
        /\  tx_i.type \in { 
                "init",
                "write-contract-specification", 
                "write-scope-specification",
                "add-contract-spec-to-scope-spec", 
                "remove-contract-spec-from-scope-spec" 
            }
        /\ ~tx_i.fail
    /\ \E i, j \in DOMAIN trace:
        /\ i < j
        /\ LET tx_i == trace[i].tx
               tx_j == trace[j].tx
           IN 
            /\ tx_i.type = "add-contract-spec-to-scope-spec"
            /\ tx_j.type = "remove-contract-spec-from-scope-spec"
            /\ tx_i.cspecId = tx_j.cspecId
            /\ tx_i.sspecId = tx_j.sspecId
    IN
    ~Example


\* a scope is created in a scope spec, but the scope spec is deleted 
\* @type: () => Bool;
OrphanedScope ==
    LET Example ==
        /\ ~tx_fail
        /\ \E scopeSpec \in scopeSpecs:
            /\ tx'.type = "remove-scope-specification"
            /\ tx'.sspecId = scopeSpec.id
            /\ Cardinality(scopeSpec.owners) = 1
            /\ \E scope \in scopes':
                scope.sspecId = scopeSpec.id

    IN ~Example

\* a record is created in a record spec, but the record spec is deleted 
\* @type: () => Bool;
OrphanedRecord ==
    LET Example ==
        /\ ~tx_fail
        /\ \E recSpec \in recordSpecs:
            /\ tx'.type = "remove-record-specification"
            /\ tx'.rspecId = recSpec.id
            /\ \E record \in records':
                record.rspecId = recSpec.id

    IN ~Example

\* a scope is created in a scope spec, but the scope spec is deleted 
\* @type: Seq(STATE) => Bool;
OrphanedScopeTrace(trace) ==
    LET Example ==
    /\ \A i \in DOMAIN trace:
        LET tx_i == trace[i].tx IN
        /\ tx_i.type \in { 
            "write-contract-specification", 
            "write-scope-specification",
            "write-scope"
            }
            => Cardinality(tx_i.owners) = 1
        /\  tx_i.type \in { 
                "init",
                "write-contract-specification", 
                "write-scope-specification",
                "write-scope",
                "remove-scope-specification"
            }
        /\ ~tx_i.fail
    /\ \E i, j \in DOMAIN trace:
        /\ i < j
        /\ LET tx_i == trace[i].tx
               tx_j == trace[j].tx
               (*@type: Set(SCOPE);*)jscopes == trace[j].scopes
           IN 
            /\ tx_i.type = "write-scope"
            /\ tx_j.type = "remove-scope-specification"
            /\ tx_i.sspecId = tx_j.sspecId
            /\ tx_i.scopeId \in { s.scopeId : s \in jscopes}
    IN
    ~Example

\* a scope spec is cleared of all contract specs
\* @type: () => Bool;
ContractlessScopeSpec ==
    LET Example ==
        /\ ~tx_fail
        /\ \E ss \in scopeSpecs:
            /\ ss.cspecs = {}
    IN
    ~Example 

\* a scope is cleared of all data access
\* @type: () => Bool;
InaccessibleScope ==
    LET Example ==
        /\ ~tx_fail
        /\ \E scope \in scopes:
            /\ scope.dataAccess = {}
    IN
    ~Example 

\* a scope is cleared of all data access
\* @type: () => Bool;
UnownedScope ==
    LET Example ==
        /\ ~tx_fail
        /\ \E scope \in scopes:
            /\ scope.owners = {}
    IN
    ~Example 

LateFail ==
  LET Example == 
    /\ tx_no = 9 /\ ~tx_fail
    /\ tx_fail'
  IN ~Example

\* @type: () => Bool;
NoFail ==
  LET Example == 
    /\ ~tx_fail
    /\ tx_no = 10
  IN
  ~Example 

====================
