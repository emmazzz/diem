(function() {var implementors = {};
implementors["backup_cli"] = [{"text":"impl Ord for EpochEndingBackupMeta","synthetic":false,"types":[]},{"text":"impl Ord for StateSnapshotBackupMeta","synthetic":false,"types":[]},{"text":"impl Ord for TransactionBackupMeta","synthetic":false,"types":[]}];
implementors["boogie_backend"] = [{"text":"impl Ord for ModelValue","synthetic":false,"types":[]}];
implementors["borrow_graph"] = [{"text":"impl Ord for RefID","synthetic":false,"types":[]}];
implementors["bytecode"] = [{"text":"impl Ord for AbsStructType","synthetic":false,"types":[]},{"text":"impl Ord for Addr","synthetic":false,"types":[]},{"text":"impl Ord for GlobalKey","synthetic":false,"types":[]},{"text":"impl Ord for Root","synthetic":false,"types":[]},{"text":"impl Ord for Offset","synthetic":false,"types":[]},{"text":"impl Ord for AccessPath","synthetic":false,"types":[]},{"text":"impl Ord for EdgeDomain","synthetic":false,"types":[]},{"text":"impl&lt;Elem:&nbsp;Ord + Clone + Sized&gt; Ord for SetDomain&lt;Elem&gt;","synthetic":false,"types":[]},{"text":"impl&lt;K:&nbsp;Ord, V:&nbsp;Ord + AbstractDomain&gt; Ord for MapDomain&lt;K, V&gt;","synthetic":false,"types":[]},{"text":"impl&lt;State:&nbsp;Ord + Clone&gt; Ord for BlockState&lt;State&gt;","synthetic":false,"types":[]},{"text":"impl Ord for FunctionVariant","synthetic":false,"types":[]},{"text":"impl Ord for Def","synthetic":false,"types":[]},{"text":"impl Ord for Label","synthetic":false,"types":[]},{"text":"impl Ord for AttrId","synthetic":false,"types":[]},{"text":"impl Ord for SpecBlockId","synthetic":false,"types":[]},{"text":"impl Ord for AssignKind","synthetic":false,"types":[]},{"text":"impl Ord for Constant","synthetic":false,"types":[]},{"text":"impl Ord for BorrowNode","synthetic":false,"types":[]},{"text":"impl Ord for StrongEdge","synthetic":false,"types":[]},{"text":"impl Ord for PropKind","synthetic":false,"types":[]}];
implementors["diem_config"] = [{"text":"impl Ord for PeerRole","synthetic":false,"types":[]},{"text":"impl Ord for NetworkId","synthetic":false,"types":[]}];
implementors["diem_crypto"] = [{"text":"impl Ord for HashValue","synthetic":false,"types":[]},{"text":"impl Ord for PublicKey","synthetic":false,"types":[]}];
implementors["diem_jellyfish_merkle"] = [{"text":"impl Ord for NodeKey","synthetic":false,"types":[]},{"text":"impl Ord for StaleNodeIndex","synthetic":false,"types":[]}];
implementors["diem_logger"] = [{"text":"impl Ord for LevelFilter","synthetic":false,"types":[]},{"text":"impl Ord for Key","synthetic":false,"types":[]},{"text":"impl Ord for Level","synthetic":false,"types":[]}];
implementors["diem_nibble"] = [{"text":"impl Ord for Nibble","synthetic":false,"types":[]}];
implementors["diem_types"] = [{"text":"impl Ord for AccessPath","synthetic":false,"types":[]},{"text":"impl Ord for Path","synthetic":false,"types":[]},{"text":"impl Ord for EventKey","synthetic":false,"types":[]},{"text":"impl Ord for MempoolStatus","synthetic":false,"types":[]},{"text":"impl Ord for MempoolStatusCode","synthetic":false,"types":[]},{"text":"impl Ord for AuthenticationKey","synthetic":false,"types":[]},{"text":"impl Ord for GovernanceRole","synthetic":false,"types":[]}];
implementors["functional_tests"] = [{"text":"impl Ord for Stage","synthetic":false,"types":[]}];
implementors["ir_to_bytecode"] = [{"text":"impl Ord for InternalCompilerError","synthetic":false,"types":[]}];
implementors["ir_to_bytecode_syntax"] = [{"text":"impl&lt;L:&nbsp;Ord, E:&nbsp;Ord&gt; Ord for ParseError&lt;L, E&gt;","synthetic":false,"types":[]}];
implementors["move_core_types"] = [{"text":"impl Ord for AccountAddress","synthetic":false,"types":[]},{"text":"impl Ord for Identifier","synthetic":false,"types":[]},{"text":"impl Ord for IdentStr","synthetic":false,"types":[]},{"text":"impl Ord for TypeTag","synthetic":false,"types":[]},{"text":"impl Ord for StructTag","synthetic":false,"types":[]},{"text":"impl Ord for ResourceKey","synthetic":false,"types":[]},{"text":"impl Ord for ModuleId","synthetic":false,"types":[]},{"text":"impl Ord for VMStatus","synthetic":false,"types":[]},{"text":"impl Ord for KeptVMStatus","synthetic":false,"types":[]},{"text":"impl Ord for AbortLocation","synthetic":false,"types":[]},{"text":"impl Ord for StatusCode","synthetic":false,"types":[]}];
implementors["move_coverage"] = [{"text":"impl Ord for AbstractSegment","synthetic":false,"types":[]}];
implementors["move_ir_types"] = [{"text":"impl Ord for ModuleName","synthetic":false,"types":[]},{"text":"impl Ord for QualifiedModuleIdent","synthetic":false,"types":[]},{"text":"impl Ord for ModuleIdent","synthetic":false,"types":[]},{"text":"impl Ord for Var_","synthetic":false,"types":[]},{"text":"impl Ord for Ability","synthetic":false,"types":[]},{"text":"impl Ord for QualifiedStructIdent","synthetic":false,"types":[]},{"text":"impl Ord for Field_","synthetic":false,"types":[]},{"text":"impl Ord for StructName","synthetic":false,"types":[]},{"text":"impl Ord for ConstantName","synthetic":false,"types":[]},{"text":"impl Ord for FunctionName","synthetic":false,"types":[]},{"text":"impl Ord for BlockLabel","synthetic":false,"types":[]},{"text":"impl Ord for NopLabel","synthetic":false,"types":[]},{"text":"impl Ord for Loc","synthetic":false,"types":[]},{"text":"impl&lt;T:&nbsp;Ord&gt; Ord for Spanned&lt;T&gt;","synthetic":false,"types":[]}];
implementors["move_lang"] = [{"text":"impl Ord for SpecId","synthetic":false,"types":[]},{"text":"impl Ord for AbilitySet","synthetic":false,"types":[]},{"text":"impl Ord for TypeName_","synthetic":false,"types":[]},{"text":"impl Ord for BaseType_","synthetic":false,"types":[]},{"text":"impl Ord for Label","synthetic":false,"types":[]},{"text":"impl Ord for BuiltinTypeName_","synthetic":false,"types":[]},{"text":"impl Ord for TypeName_","synthetic":false,"types":[]},{"text":"impl Ord for TParamID","synthetic":false,"types":[]},{"text":"impl Ord for TParam","synthetic":false,"types":[]},{"text":"impl Ord for TVar","synthetic":false,"types":[]},{"text":"impl Ord for ModuleName","synthetic":false,"types":[]},{"text":"impl Ord for Field","synthetic":false,"types":[]},{"text":"impl Ord for StructName","synthetic":false,"types":[]},{"text":"impl Ord for FunctionName","synthetic":false,"types":[]},{"text":"impl Ord for ConstantName","synthetic":false,"types":[]},{"text":"impl Ord for Ability_","synthetic":false,"types":[]},{"text":"impl Ord for Var","synthetic":false,"types":[]},{"text":"impl Ord for ModuleIdent","synthetic":false,"types":[]},{"text":"impl&lt;K:&nbsp;TName, V:&nbsp;Ord&gt; Ord for UniqueMap&lt;K, V&gt;","synthetic":false,"types":[]},{"text":"impl&lt;T:&nbsp;TName&gt; Ord for UniqueSet&lt;T&gt;","synthetic":false,"types":[]},{"text":"impl Ord for Address","synthetic":false,"types":[]},{"text":"impl Ord for Pass","synthetic":false,"types":[]}];
implementors["move_model"] = [{"text":"impl Ord for SpecBlockTarget","synthetic":false,"types":[]},{"text":"impl Ord for ModuleName","synthetic":false,"types":[]},{"text":"impl Ord for QualifiedSymbol","synthetic":false,"types":[]},{"text":"impl Ord for Loc","synthetic":false,"types":[]},{"text":"impl Ord for ModuleId","synthetic":false,"types":[]},{"text":"impl Ord for NamedConstantId","synthetic":false,"types":[]},{"text":"impl Ord for StructId","synthetic":false,"types":[]},{"text":"impl Ord for FieldId","synthetic":false,"types":[]},{"text":"impl Ord for FunId","synthetic":false,"types":[]},{"text":"impl Ord for SchemaId","synthetic":false,"types":[]},{"text":"impl Ord for SpecFunId","synthetic":false,"types":[]},{"text":"impl Ord for SpecVarId","synthetic":false,"types":[]},{"text":"impl Ord for NodeId","synthetic":false,"types":[]},{"text":"impl Ord for GlobalId","synthetic":false,"types":[]},{"text":"impl&lt;Id:&nbsp;Ord&gt; Ord for QualifiedId&lt;Id&gt;","synthetic":false,"types":[]},{"text":"impl Ord for TypeParameter","synthetic":false,"types":[]},{"text":"impl Ord for TypeConstraint","synthetic":false,"types":[]},{"text":"impl Ord for Symbol","synthetic":false,"types":[]},{"text":"impl Ord for Type","synthetic":false,"types":[]},{"text":"impl Ord for PrimitiveType","synthetic":false,"types":[]}];
implementors["move_vm_types"] = [{"text":"impl Ord for NativeCostIndex","synthetic":false,"types":[]},{"text":"impl Ord for StructType","synthetic":false,"types":[]},{"text":"impl Ord for Type","synthetic":false,"types":[]}];
implementors["network"] = [{"text":"impl Ord for DiscoverySource","synthetic":false,"types":[]},{"text":"impl Ord for MessagingProtocolVersion","synthetic":false,"types":[]}];
implementors["short_hex_str"] = [{"text":"impl Ord for ShortHexStr","synthetic":false,"types":[]}];
implementors["vm"] = [{"text":"impl Ord for Location","synthetic":false,"types":[]},{"text":"impl Ord for VMError","synthetic":false,"types":[]},{"text":"impl Ord for ModuleHandleIndex","synthetic":false,"types":[]},{"text":"impl Ord for StructHandleIndex","synthetic":false,"types":[]},{"text":"impl Ord for FunctionHandleIndex","synthetic":false,"types":[]},{"text":"impl Ord for FieldHandleIndex","synthetic":false,"types":[]},{"text":"impl Ord for StructDefInstantiationIndex","synthetic":false,"types":[]},{"text":"impl Ord for FunctionInstantiationIndex","synthetic":false,"types":[]},{"text":"impl Ord for FieldInstantiationIndex","synthetic":false,"types":[]},{"text":"impl Ord for IdentifierIndex","synthetic":false,"types":[]},{"text":"impl Ord for AddressIdentifierIndex","synthetic":false,"types":[]},{"text":"impl Ord for ConstantPoolIndex","synthetic":false,"types":[]},{"text":"impl Ord for SignatureIndex","synthetic":false,"types":[]},{"text":"impl Ord for StructDefinitionIndex","synthetic":false,"types":[]},{"text":"impl Ord for FunctionDefinitionIndex","synthetic":false,"types":[]},{"text":"impl Ord for ModuleHandle","synthetic":false,"types":[]},{"text":"impl Ord for StructHandle","synthetic":false,"types":[]},{"text":"impl Ord for Ability","synthetic":false,"types":[]},{"text":"impl Ord for AbilitySet","synthetic":false,"types":[]},{"text":"impl Ord for SignatureToken","synthetic":false,"types":[]},{"text":"impl Ord for Type","synthetic":false,"types":[]},{"text":"impl Ord for FunctionSignature","synthetic":false,"types":[]},{"text":"impl Ord for IndexKind","synthetic":false,"types":[]},{"text":"impl Ord for SignatureTokenKind","synthetic":false,"types":[]}];
implementors["x_core"] = [{"text":"impl&lt;T:&nbsp;Ord&gt; Ord for DebugIgnore&lt;T&gt;","synthetic":false,"types":[]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()