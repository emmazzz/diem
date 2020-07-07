
// ** prelude from <inline-prelude>

// ================================================================================
// Notation

// This files contains a Handlebars Rust template for the prover's Boogie prelude.
// The template language constructs allow the prelude to adjust the actual content
// to multiple options. We only use a few selected template constructs which are
// mostly self-explaining. See the handlebars crate documentation for more information.
//
// The object passed in as context for templates is the struct cli::Options and its
// sub-structs.

// ================================================================================
// Domains

// Debug tracking
// --------------

// Debug tracking is used to inject information used for model analysis. The generated code emits statements
// like this:
//
//     assume $DebugTrackLocal(file_id, byte_index, var_idx, $Value);
//
// While those tracking assumptions are trivially true for the provers logic, the solver (at least Z3)
// will construct a function mapping which appears in the model, e.g.:
//
//     $DebugTrackLocal -> {
//         1 440 0 (Vector (ValueArray |T@[Int]$Value!val!0| 0)) -> true
//         1 533 1 ($Integer 1) -> true
//         ...
//         else -> true
//     }
//
// This information can then be read out from the model.


// Tracks debug information for a parameter, local or a return parameter. Return parameter indices start at
// the overall number of locals (including parameters).
function $DebugTrackLocal(file_id: int, byte_index:  int, var_idx: int, $Value: $Value) : bool {
  true
}

// Tracks at which location a function was aborted.
function $DebugTrackAbort(file_id: int, byte_index: int) : bool {
  true
}

// Tracks the $Value of a specification (sub-)expression.
function $DebugTrackExp(module_id: int, node_id: int, $Value: $Value) : $Value { $Value }


// Path type
// ---------

type {:datatype} $Path;
function {:constructor} $Path(p: [int]int, size: int): $Path;
const $EmptyPath: $Path;
axiom size#$Path($EmptyPath) == 0;

function {:inline} $path_index_at(p: $Path, i: int): int {
    p#$Path(p)[i]
}

// Type Values
// -----------

type $TypeName;
type $FieldName = int;
type $LocalName;
type {:datatype} $TypeValue;
function {:constructor} $BooleanType() : $TypeValue;
function {:constructor} $IntegerType() : $TypeValue;
function {:constructor} $AddressType() : $TypeValue;
function {:constructor} $StrType() : $TypeValue;
function {:constructor} $VectorType(t: $TypeValue) : $TypeValue;
function {:constructor} $StructType(name: $TypeName, ps: $TypeValueArray, ts: $TypeValueArray) : $TypeValue;
function {:constructor} $TypeType(): $TypeValue;
function {:constructor} $ErrorType() : $TypeValue;

function {:inline} $DefaultTypeValue() : $TypeValue { $ErrorType() }
function {:builtin "MapConst"} $MapConstTypeValue(tv: $TypeValue): [int]$TypeValue;

type {:datatype} $TypeValueArray;
function {:constructor} $TypeValueArray(v: [int]$TypeValue, l: int): $TypeValueArray;
const $EmptyTypeValueArray: $TypeValueArray;
axiom l#$TypeValueArray($EmptyTypeValueArray) == 0;
axiom v#$TypeValueArray($EmptyTypeValueArray) == $MapConstTypeValue($DefaultTypeValue());


// Values
// ------

type {:datatype} $Value;

const $MAX_U8: int;
axiom $MAX_U8 == 255;
const $MAX_U64: int;
axiom $MAX_U64 == 18446744073709551615;
const $MAX_U128: int;
axiom $MAX_U128 == 340282366920938463463374607431768211455;

function {:constructor} $Boolean(b: bool): $Value;
function {:constructor} $Integer(i: int): $Value;
function {:constructor} $Address(a: int): $Value;
function {:constructor} $Vector(v: $ValueArray): $Value; // used to both represent move Struct and Vector
function {:constructor} $Range(lb: $Value, ub: $Value): $Value;
function {:constructor} $Type(t: $TypeValue): $Value;
function {:constructor} $Error(): $Value;

function {:inline} $DefaultValue(): $Value { $Error() }
function {:builtin "MapConst"} $MapConstValue(v: $Value): [int]$Value;

function {:inline} $IsValidU8(v: $Value): bool {
  is#$Integer(v) && i#$Integer(v) >= 0 && i#$Integer(v) <= $MAX_U8
}

function {:inline} $IsValidU8Vector(vec: $Value): bool {
  $Vector_is_well_formed(vec)
  && (forall i: int :: {$select_vector(vec, i)} 0 <= i && i < $vlen(vec) ==> $IsValidU8($select_vector(vec, i)))
}

function {:inline} $IsValidU64(v: $Value): bool {
  is#$Integer(v) && i#$Integer(v) >= 0 && i#$Integer(v) <= $MAX_U64
}

function {:inline} $IsValidU128(v: $Value): bool {
  is#$Integer(v) && i#$Integer(v) >= 0 && i#$Integer(v) <= $MAX_U128
}

function {:inline} $IsValidNum(v: $Value): bool {
  is#$Integer(v)
}


// Value Array
// -----------





// This is the implementation of $ValueArray using integer maps

type {:datatype} $ValueArray;

function {:constructor} $ValueArray(v: [int]$Value, l: int): $ValueArray;

function $EmptyValueArray(): $ValueArray;
axiom l#$ValueArray($EmptyValueArray()) == 0;
axiom v#$ValueArray($EmptyValueArray()) == $MapConstValue($Error());

function {:inline} $ReadValueArray(a: $ValueArray, i: int): $Value {
    (
        v#$ValueArray(a)[i]
    )
}

function {:inline} $LenValueArray(a: $ValueArray): int {
    (
        l#$ValueArray(a)
    )
}

function {:inline} $RemoveValueArray(a: $ValueArray): $ValueArray {
    (
        var l := l#$ValueArray(a) - 1;
        $ValueArray(
            (lambda i: int ::
                if i >= 0 && i < l then v#$ValueArray(a)[i] else $DefaultValue()),
            l
        )
    )
}

function {:inline} $RemoveIndexValueArray(a: $ValueArray, i: int): $ValueArray {
    (
        var l := l#$ValueArray(a) - 1;
        $ValueArray(
            (lambda j: int ::
                if j >= 0 && j < l then
                    if j < i then v#$ValueArray(a)[j] else v#$ValueArray(a)[j+1]
                else $DefaultValue()),
            l
        )
    )
}

function {:inline} $ConcatValueArray(a1: $ValueArray, a2: $ValueArray): $ValueArray {
    (
        var l1, l2 := l#$ValueArray(a1), l#$ValueArray(a2);
        $ValueArray(
            (lambda i: int ::
                if i >= 0 && i < l1 + l2 then
                    if i < l1 then v#$ValueArray(a1)[i] else v#$ValueArray(a2)[i - l1]
                else
                    $DefaultValue()),
            l1 + l2)
    )
}

function {:inline} $ReverseValueArray(a: $ValueArray): $ValueArray {
    (
        var l := l#$ValueArray(a);
        $ValueArray(
            (lambda i: int :: if 0 <= i && i < l then v#$ValueArray(a)[l - i - 1] else $DefaultValue()),
            l
        )
    )
}

function {:inline} $SliceValueArray(a: $ValueArray, i: int, j: int): $ValueArray { // return the sliced vector of a for the range [i, j)
    $ValueArray((lambda k:int :: if 0 <= k && k < j-i then v#$ValueArray(a)[i+k] else $DefaultValue()), (if j-i < 0 then 0 else j-i))
}

function {:inline} $ExtendValueArray(a: $ValueArray, elem: $Value): $ValueArray {
    (var len := l#$ValueArray(a);
     $ValueArray(v#$ValueArray(a)[len := elem], len + 1))
}

function {:inline} $UpdateValueArray(a: $ValueArray, i: int, elem: $Value): $ValueArray {
    $ValueArray(v#$ValueArray(a)[i := elem], l#$ValueArray(a))
}

function {:inline} $SwapValueArray(a: $ValueArray, i: int, j: int): $ValueArray {
    $ValueArray(v#$ValueArray(a)[i := v#$ValueArray(a)[j]][j := v#$ValueArray(a)[i]], l#$ValueArray(a))
}

function {:inline} $IsEmpty(a: $ValueArray): bool {
    l#$ValueArray(a) == 0
}

// All invalid elements of array are DefaultValue. This is useful in specialized
// cases. This is used to defined normalization for $Vector
function {:inline} $IsNormalizedValueArray(a: $ValueArray, len: int): bool {
    (forall i: int :: i < 0 || i >= len ==> v#$ValueArray(a)[i] == $DefaultValue())
}


 //end of backend.vector_using_sequences


// Stratified Functions on Values
// ------------------------------

// TODO: templatize this or move it back to the translator. For now we
//   prefer to handcode this so its easier to evolve the model independent of the
//   translator.

const $StratificationDepth: int;
axiom $StratificationDepth == 4;



// Generate a stratified version of IsEqual for depth of 4.

function  $IsEqual_stratified(v1: $Value, v2: $Value): bool {
    (v1 == v2) ||
    (is#$Vector(v1) &&
     is#$Vector(v2) &&
     $vlen(v1) == $vlen(v2) &&
     (forall i: int :: 0 <= i && i < $vlen(v1) ==> $IsEqual_level1($select_vector(v1,i), $select_vector(v2,i))))
}

function  $IsEqual_level1(v1: $Value, v2: $Value): bool {
    (v1 == v2) ||
    (is#$Vector(v1) &&
     is#$Vector(v2) &&
     $vlen(v1) == $vlen(v2) &&
     (forall i: int :: 0 <= i && i < $vlen(v1) ==> $IsEqual_level2($select_vector(v1,i), $select_vector(v2,i))))
}

function  $IsEqual_level2(v1: $Value, v2: $Value): bool {
    (v1 == v2) ||
    (is#$Vector(v1) &&
     is#$Vector(v2) &&
     $vlen(v1) == $vlen(v2) &&
     (forall i: int :: 0 <= i && i < $vlen(v1) ==> $IsEqual_level3($select_vector(v1,i), $select_vector(v2,i))))
}

function {:inline} $IsEqual_level3(v1: $Value, v2: $Value): bool {
    v1 == v2
}


function {:inline} $IsEqual(v1: $Value, v2: $Value): bool {
    $IsEqual_stratified(v1, v2)
}



// Generate stratified ReadValue for the depth of 4.


function  $ReadValue_stratified(p: $Path, v: $Value) : $Value {
    if (0 == size#$Path(p)) then
        v
    else
        $ReadValue_level1(p, $select_vector(v,$path_index_at(p, 0)))
}

function  $ReadValue_level1(p: $Path, v: $Value) : $Value {
    if (1 == size#$Path(p)) then
        v
    else
        $ReadValue_level2(p, $select_vector(v,$path_index_at(p, 1)))
}

function  $ReadValue_level2(p: $Path, v: $Value) : $Value {
    if (2 == size#$Path(p)) then
        v
    else
        $ReadValue_level3(p, $select_vector(v,$path_index_at(p, 2)))
}

function {:inline} $ReadValue_level3(p: $Path, v: $Value): $Value {
    v
}


function {:inline} $ReadValue(p: $Path, v: $Value): $Value {
    $ReadValue_stratified(p, v)
}

// Generate stratified $UpdateValue for the depth of 4.


function  $UpdateValue_stratified(p: $Path, offset: int, v: $Value, new_v: $Value): $Value {
    (var poffset := offset + 0;
    if (poffset == size#$Path(p)) then
        new_v
    else
        $update_vector(v, $path_index_at(p, poffset),
                       $UpdateValue_level1(p, offset, $select_vector(v,$path_index_at(p, poffset)), new_v)))
}

function  $UpdateValue_level1(p: $Path, offset: int, v: $Value, new_v: $Value): $Value {
    (var poffset := offset + 1;
    if (poffset == size#$Path(p)) then
        new_v
    else
        $update_vector(v, $path_index_at(p, poffset),
                       $UpdateValue_level2(p, offset, $select_vector(v,$path_index_at(p, poffset)), new_v)))
}

function  $UpdateValue_level2(p: $Path, offset: int, v: $Value, new_v: $Value): $Value {
    (var poffset := offset + 2;
    if (poffset == size#$Path(p)) then
        new_v
    else
        $update_vector(v, $path_index_at(p, poffset),
                       $UpdateValue_level3(p, offset, $select_vector(v,$path_index_at(p, poffset)), new_v)))
}

function {:inline} $UpdateValue_level3(p: $Path, offset: int, v: $Value, new_v: $Value): $Value {
    new_v
}


function {:inline} $UpdateValue(p: $Path, offset: int, v: $Value, new_v: $Value): $Value {
    $UpdateValue_stratified(p, offset, v, new_v)
}

// Generate stratified $IsPathPrefix for the depth of 4.


function  $IsPathPrefix_stratified(p1: $Path, p2: $Path): bool {
    if (0 == size#$Path(p1)) then
        true
    else if (p#$Path(p1)[0] == p#$Path(p2)[0]) then
        $IsPathPrefix_level1(p1, p2)
    else
        false
}

function  $IsPathPrefix_level1(p1: $Path, p2: $Path): bool {
    if (1 == size#$Path(p1)) then
        true
    else if (p#$Path(p1)[1] == p#$Path(p2)[1]) then
        $IsPathPrefix_level2(p1, p2)
    else
        false
}

function  $IsPathPrefix_level2(p1: $Path, p2: $Path): bool {
    if (2 == size#$Path(p1)) then
        true
    else if (p#$Path(p1)[2] == p#$Path(p2)[2]) then
        $IsPathPrefix_level3(p1, p2)
    else
        false
}

function {:inline} $IsPathPrefix_level3(p1: $Path, p2: $Path): bool {
    true
}


function {:inline} $IsPathPrefix(p1: $Path, p2: $Path): bool {
    $IsPathPrefix_stratified(p1, p2)
}

// Generate stratified $ConcatPath for the depth of 4.


function  $ConcatPath_stratified(p1: $Path, p2: $Path): $Path {
    if (0 == size#$Path(p2)) then
        p1
    else
        $ConcatPath_level1($Path(p#$Path(p1)[size#$Path(p1) := p#$Path(p2)[0]], size#$Path(p1) + 1), p2)
}

function  $ConcatPath_level1(p1: $Path, p2: $Path): $Path {
    if (1 == size#$Path(p2)) then
        p1
    else
        $ConcatPath_level2($Path(p#$Path(p1)[size#$Path(p1) := p#$Path(p2)[1]], size#$Path(p1) + 1), p2)
}

function  $ConcatPath_level2(p1: $Path, p2: $Path): $Path {
    if (2 == size#$Path(p2)) then
        p1
    else
        $ConcatPath_level3($Path(p#$Path(p1)[size#$Path(p1) := p#$Path(p2)[2]], size#$Path(p1) + 1), p2)
}

function {:inline} $ConcatPath_level3(p1: $Path, p2: $Path): $Path {
    p1
}


function {:inline} $ConcatPath(p1: $Path, p2: $Path): $Path {
    $ConcatPath_stratified(p1, p2)
}

// Vector related functions on Values
// ----------------------------------

function {:inline} $vlen(v: $Value): int {
    $LenValueArray(v#$Vector(v))
}

// Check that all invalid elements of vector are DefaultValue
function {:inline} $is_normalized_vector(v: $Value): bool {
    $IsNormalizedValueArray(v#$Vector(v), $vlen(v))
}

// Sometimes, we need the length as a Value, not an int.
function {:inline} $vlen_value(v: $Value): $Value {
    $Integer($vlen(v))
}
function {:inline} $mk_vector(): $Value {
    $Vector($EmptyValueArray())
}
function {:inline} $push_back_vector(v: $Value, elem: $Value): $Value {
    $Vector($ExtendValueArray(v#$Vector(v), elem))
}
function {:inline} $pop_back_vector(v: $Value): $Value {
    $Vector($RemoveValueArray(v#$Vector(v)))
}
function {:inline} $append_vector(v1: $Value, v2: $Value): $Value {
    $Vector($ConcatValueArray(v#$Vector(v1), v#$Vector(v2)))
}
function {:inline} $reverse_vector(v: $Value): $Value {
    $Vector($ReverseValueArray(v#$Vector(v)))
}
function {:inline} $update_vector(v: $Value, i: int, elem: $Value): $Value {
    $Vector($UpdateValueArray(v#$Vector(v), i, elem))
}
// $update_vector_by_value requires index to be a Value, not int.
function {:inline} $update_vector_by_value(v: $Value, i: $Value, elem: $Value): $Value {
    $Vector($UpdateValueArray(v#$Vector(v), i#$Integer(i), elem))
}
function {:inline} $select_vector(v: $Value, i: int) : $Value {
    $ReadValueArray(v#$Vector(v), i)
}
// $select_vector_by_value requires index to be a Value, not int.
function {:inline} $select_vector_by_value(v: $Value, i: $Value) : $Value {
    $select_vector(v, i#$Integer(i))
}
function {:inline} $swap_vector(v: $Value, i: int, j: int): $Value {
    $Vector($SwapValueArray(v#$Vector(v), i, j))
}
function {:inline} $slice_vector(v: $Value, r: $Value) : $Value {
    $Vector($SliceValueArray(v#$Vector(v), i#$Integer(lb#$Range(r)), i#$Integer(ub#$Range(r))))
}
function {:inline} $InVectorRange(v: $Value, i: int): bool {
    i >= 0 && i < $vlen(v)
}
function {:inline} $remove_vector(v: $Value, i:int): $Value {
    $Vector($RemoveIndexValueArray(v#$Vector(v), i))
}
function {:inline} $contains_vector(v: $Value, e: $Value): bool {
    (exists i:int :: 0 <= i && i < $vlen(v) && $IsEqual($select_vector(v,i), e))
}

function {:inline} $InRange(r: $Value, i: int): bool {
   i#$Integer(lb#$Range(r)) <= i && i < i#$Integer(ub#$Range(r))
}


// ============================================================================================
// Memory

type {:datatype} $Location;
function {:constructor} $Global(t: $TypeValue, a: int): $Location;
function {:constructor} $Local(i: int): $Location;
function {:constructor} $Param(i: int): $Location;

type {:datatype} $Reference;
function {:constructor} $Reference(l: $Location, p: $Path, v: $Value): $Reference;
const $DefaultReference: $Reference;

type {:datatype} $Memory;
function {:constructor} $Memory(domain: [$Location]bool, contents: [$Location]$Value): $Memory;

function $Memory__is_well_formed(m: $Memory): bool;

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [$Location]bool;
function {:builtin "MapConst"} $ConstMemoryContent(v: $Value): [$Location]$Value;

const $EmptyMemory: $Memory;
axiom domain#$Memory($EmptyMemory) == $ConstMemoryDomain(false);
axiom contents#$Memory($EmptyMemory) == $ConstMemoryContent($DefaultValue());

var $m: $Memory;
var $abort_flag: bool;

procedure {:inline 1} $InitVerification() {
  // Set abort_flag to false
  $abort_flag := false;
}

// ============================================================================================
// Specifications

// TODO: unify some of this with instruction procedures to avoid duplication

// Tests whether resource exists.
function {:inline} $ResourceExistsRaw(m: $Memory, resource: $TypeValue, addr: int): bool {
    domain#$Memory(m)[$Global(resource, addr)]
}
function {:inline} $ResourceExists(m: $Memory, resource: $TypeValue, address: $Value): $Value {
    $Boolean($ResourceExistsRaw(m, resource, a#$Address(address)))
}

// Obtains Value of given resource.
function {:inline} $ResourceValue(m: $Memory, resource: $TypeValue, address: $Value): $Value {
  contents#$Memory(m)[$Global(resource, a#$Address(address))]
}

// Applies a field selection to a Value.
function {:inline} $SelectField(val: $Value, field: $FieldName): $Value { //breaks abstracts, we don't know $Fieldname = int
    $select_vector(val, field)
}

// Dereferences a reference.
function {:inline} $Dereference(ref: $Reference): $Value {
    v#$Reference(ref)
}

// Check whether sender account exists.
function {:inline} $ExistsTxnSenderAccount(m: $Memory, txn: $Transaction): bool {
   domain#$Memory(m)[$Global($LibraAccount_T_type_value(), sender#$Transaction(txn))]
}

function {:inline} $TxnSender(txn: $Transaction): $Value {
    $Address(sender#$Transaction(txn))
}

// Forward declaration of type Value of LibraAccount. This is declared so we can define
// $ExistsTxnSenderAccount and $LibraAccount_save_account
const unique $LibraAccount_T: $TypeName;
function $LibraAccount_T_type_value(): $TypeValue;
axiom is#$StructType($LibraAccount_T_type_value()) && name#$StructType($LibraAccount_T_type_value()) == $LibraAccount_T;
function $LibraAccount_Balance_type_value(tv: $TypeValue): $TypeValue;

// ============================================================================================
// Instructions

procedure {:inline 1} $Exists(address: $Value, t: $TypeValue) returns (dst: $Value)
free requires is#$Address(address);
{
    dst := $ResourceExists($m, t, address);
}

procedure {:inline 1} $MoveToRaw(ta: $TypeValue, a: int, v: $Value)
{
    var l: $Location;

    l := $Global(ta, a);
    if ($ResourceExistsRaw($m, ta, a)) {
        $abort_flag := true;
        return;
    }
    $m := $Memory(domain#$Memory($m)[l := true], contents#$Memory($m)[l := v]);
}

procedure {:inline 1} $MoveTo(ta: $TypeValue, v: $Value, signer: $Value)
{
    var addr: $Value;

    call addr := $Signer_borrow_address(signer);
    call $MoveToRaw(ta, a#$Address(addr), v);
}

procedure {:inline 1} $MoveToSender(ta: $TypeValue, v: $Value)
{
    call $MoveToRaw(ta, sender#$Transaction($txn), v);
}

procedure {:inline 1} $MoveFrom(address: $Value, ta: $TypeValue) returns (dst: $Value)
free requires is#$Address(address);
{
    var a: int;
    var l: $Location;
    a := a#$Address(address);
    l := $Global(ta, a);
    if (!$ResourceExistsRaw($m, ta, a)) {
        $abort_flag := true;
        return;
    }
    dst := contents#$Memory($m)[l];
    $m := $Memory(domain#$Memory($m)[l := false], contents#$Memory($m)[l := $DefaultValue()]);
}

procedure {:inline 1} $BorrowGlobal(address: $Value, ta: $TypeValue) returns (dst: $Reference)
free requires is#$Address(address);
{
    var a: int;
    var l: $Location;
    a := a#$Address(address);
    l := $Global(ta, a);
    if (!$ResourceExistsRaw($m, ta, a)) {
        $abort_flag := true;
        return;
    }
    dst := $Reference(l, $EmptyPath, contents#$Memory($m)[l]);
}

procedure {:inline 1} $BorrowLoc(l: int, v: $Value) returns (dst: $Reference)
{
    dst := $Reference($Local(l), $EmptyPath, v);
}

procedure {:inline 1} $BorrowField(src: $Reference, f: $FieldName) returns (dst: $Reference)
{
    var p: $Path;
    var size: int;

    p := p#$Reference(src);
    size := size#$Path(p);
    p := $Path(p#$Path(p)[size := f], size+1);
    dst := $Reference(l#$Reference(src), p, $select_vector(v#$Reference(src), f)); //breaks abstraction
}

procedure {:inline 1} $GetGlobal(address: $Value, ta: $TypeValue) returns (dst: $Value)
free requires is#$Address(address);
{
    var r: $Reference;

    call r := $BorrowGlobal(address, ta);
    call dst := $ReadRef(r);
}

procedure {:inline 1} $GetFieldFromReference(src: $Reference, f: $FieldName) returns (dst: $Value)
{
    var r: $Reference;

    call r := $BorrowField(src, f);
    call dst := $ReadRef(r);
}

procedure {:inline 1} $GetFieldFromValue(src: $Value, f: $FieldName) returns (dst: $Value)
{
    dst := $select_vector(src, f); //breaks abstraction
}

procedure {:inline 1} $WriteRef(to: $Reference, new_v: $Value) returns (to': $Reference)
{
    to' := $Reference(l#$Reference(to), p#$Reference(to), new_v);
}

procedure {:inline 1} $ReadRef(from: $Reference) returns (v: $Value)
{
    v := v#$Reference(from);
}

procedure {:inline 1} $CopyOrMoveRef(local: $Reference) returns (dst: $Reference)
{
    dst := local;
}

procedure {:inline 1} $CopyOrMoveValue(local: $Value) returns (dst: $Value)
{
    dst := local;
}

procedure {:inline 1} $WritebackToGlobal(src: $Reference)
{
    var l: $Location;
    var v: $Value;

    l := l#$Reference(src);
    if (is#$Global(l)) {
        v := $UpdateValue(p#$Reference(src), 0, contents#$Memory($m)[l], v#$Reference(src));
        $m := $Memory(domain#$Memory($m), contents#$Memory($m)[l := v]);
    }
}

procedure {:inline 1} $WritebackToValue(src: $Reference, idx: int, vdst: $Value) returns (vdst': $Value)
{
    if (l#$Reference(src) == $Local(idx)) {
        vdst' := $UpdateValue(p#$Reference(src), 0, vdst, v#$Reference(src));
    } else {
        vdst' := vdst;
    }
}

procedure {:inline 1} $WritebackToReference(src: $Reference, dst: $Reference) returns (dst': $Reference)
{
    var srcPath, dstPath: $Path;

    srcPath := p#$Reference(src);
    dstPath := p#$Reference(dst);
    if (l#$Reference(dst) == l#$Reference(src) && size#$Path(dstPath) <= size#$Path(srcPath) && $IsPathPrefix(dstPath, srcPath)) {
        dst' := $Reference(
                    l#$Reference(dst),
                    dstPath,
                    $UpdateValue(srcPath, size#$Path(dstPath), v#$Reference(dst), v#$Reference(src)));
    } else {
        dst' := dst;
    }
}

procedure {:inline 1} $Splice1(idx1: int, src1: $Reference, dst: $Reference) returns (dst': $Reference) {
    assume l#$Reference(dst) == $Local(idx1);
    dst' := $Reference(l#$Reference(dst), $ConcatPath(p#$Reference(src1), p#$Reference(dst)), v#$Reference(dst));
}

procedure {:inline 1} $CastU8(src: $Value) returns (dst: $Value)
free requires is#$Integer(src);
{
    if (i#$Integer(src) > $MAX_U8) {
        $abort_flag := true;
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU64(src: $Value) returns (dst: $Value)
free requires is#$Integer(src);
{
    if (i#$Integer(src) > $MAX_U64) {
        $abort_flag := true;
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU128(src: $Value) returns (dst: $Value)
free requires is#$Integer(src);
{
    if (i#$Integer(src) > $MAX_U128) {
        $abort_flag := true;
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: $Value, src2: $Value) returns (dst: $Value)
free requires $IsValidU8(src1) && $IsValidU8(src2);
{
    if (i#$Integer(src1) + i#$Integer(src2) > $MAX_U8) {
        $abort_flag := true;
        return;
    }
    dst := $Integer(i#$Integer(src1) + i#$Integer(src2));
}

procedure {:inline 1} $AddU64(src1: $Value, src2: $Value) returns (dst: $Value)
free requires $IsValidU64(src1) && $IsValidU64(src2);
{
    if (i#$Integer(src1) + i#$Integer(src2) > $MAX_U64) {
        $abort_flag := true;
        return;
    }
    dst := $Integer(i#$Integer(src1) + i#$Integer(src2));
}

procedure {:inline 1} $AddU64_unchecked(src1: $Value, src2: $Value) returns (dst: $Value)
free requires $IsValidU64(src1) && $IsValidU64(src2);
{
    dst := $Integer(i#$Integer(src1) + i#$Integer(src2));
}

procedure {:inline 1} $AddU128(src1: $Value, src2: $Value) returns (dst: $Value)
free requires $IsValidU128(src1) && $IsValidU128(src2);
{
    if (i#$Integer(src1) + i#$Integer(src2) > $MAX_U128) {
        $abort_flag := true;
        return;
    }
    dst := $Integer(i#$Integer(src1) + i#$Integer(src2));
}

procedure {:inline 1} $AddU128_unchecked(src1: $Value, src2: $Value) returns (dst: $Value)
free requires $IsValidU128(src1) && $IsValidU128(src2);
{
    dst := $Integer(i#$Integer(src1) + i#$Integer(src2));
}

procedure {:inline 1} $Sub(src1: $Value, src2: $Value) returns (dst: $Value)
free requires is#$Integer(src1) && is#$Integer(src2);
{
    if (i#$Integer(src1) < i#$Integer(src2)) {
        $abort_flag := true;
        return;
    }
    dst := $Integer(i#$Integer(src1) - i#$Integer(src2));
}

// This deals only with narrow special cases. Src2 must be constant
// 32 or 64, which is what we use now.  Obviously, it could be extended
// to src2 == any integer Value from 0..127.
// Left them out for brevity
function $power_of_2(power: $Value): int {
    (var p := i#$Integer(power);
     if p == 32 then 4294967296
     else if p == 64 then 18446744073709551616
     // Value is undefined, otherwise.
     else -1
     )
}

procedure {:inline 1} $Shl(src1: $Value, src2: $Value) returns (dst: $Value)
requires is#$Integer(src1) && is#$Integer(src2);
{
    var po2: int;
    po2 := $power_of_2(src2);
    assert po2 >= 1;   // po2 < 0 if src2 not 32 or 63
    dst := $Integer(i#$Integer(src2) * po2);
}

procedure {:inline 1} $Shr(src1: $Value, src2: $Value) returns (dst: $Value)
requires is#$Integer(src1) && is#$Integer(src2);
{
    var po2: int;
    po2 := $power_of_2(src2);
    assert po2 >= 1;   // po2 < 0 if src2 not 32 or 63
    dst := $Integer(i#$Integer(src2) div po2);
}

procedure {:inline 1} $MulU8(src1: $Value, src2: $Value) returns (dst: $Value)
free requires $IsValidU8(src1) && $IsValidU8(src2);
{
    if (i#$Integer(src1) * i#$Integer(src2) > $MAX_U8) {
        $abort_flag := true;
        return;
    }
    dst := $Integer(i#$Integer(src1) * i#$Integer(src2));
}

procedure {:inline 1} $MulU64(src1: $Value, src2: $Value) returns (dst: $Value)
free requires $IsValidU64(src1) && $IsValidU64(src2);
{
    if (i#$Integer(src1) * i#$Integer(src2) > $MAX_U64) {
        $abort_flag := true;
        return;
    }
    dst := $Integer(i#$Integer(src1) * i#$Integer(src2));
}

procedure {:inline 1} $MulU128(src1: $Value, src2: $Value) returns (dst: $Value)
free requires $IsValidU128(src1) && $IsValidU128(src2);
{
    if (i#$Integer(src1) * i#$Integer(src2) > $MAX_U128) {
        $abort_flag := true;
        return;
    }
    dst := $Integer(i#$Integer(src1) * i#$Integer(src2));
}

procedure {:inline 1} $Div(src1: $Value, src2: $Value) returns (dst: $Value)
free requires is#$Integer(src1) && is#$Integer(src2);
{
    if (i#$Integer(src2) == 0) {
        $abort_flag := true;
        return;
    }
    dst := $Integer(i#$Integer(src1) div i#$Integer(src2));
}

procedure {:inline 1} $Mod(src1: $Value, src2: $Value) returns (dst: $Value)
free requires is#$Integer(src1) && is#$Integer(src2);
{
    if (i#$Integer(src2) == 0) {
        $abort_flag := true;
        return;
    }
    dst := $Integer(i#$Integer(src1) mod i#$Integer(src2));
}

procedure {:inline 1} $ArithBinaryUnimplemented(src1: $Value, src2: $Value) returns (dst: $Value);
free requires is#$Integer(src1) && is#$Integer(src2);
ensures is#$Integer(dst);

procedure {:inline 1} $Lt(src1: $Value, src2: $Value) returns (dst: $Value)
free requires is#$Integer(src1) && is#$Integer(src2);
{
    dst := $Boolean(i#$Integer(src1) < i#$Integer(src2));
}

procedure {:inline 1} $Gt(src1: $Value, src2: $Value) returns (dst: $Value)
free requires is#$Integer(src1) && is#$Integer(src2);
{
    dst := $Boolean(i#$Integer(src1) > i#$Integer(src2));
}

procedure {:inline 1} $Le(src1: $Value, src2: $Value) returns (dst: $Value)
free requires is#$Integer(src1) && is#$Integer(src2);
{
    dst := $Boolean(i#$Integer(src1) <= i#$Integer(src2));
}

procedure {:inline 1} $Ge(src1: $Value, src2: $Value) returns (dst: $Value)
free requires is#$Integer(src1) && is#$Integer(src2);
{
    dst := $Boolean(i#$Integer(src1) >= i#$Integer(src2));
}

procedure {:inline 1} $And(src1: $Value, src2: $Value) returns (dst: $Value)
free requires is#$Boolean(src1) && is#$Boolean(src2);
{
    dst := $Boolean(b#$Boolean(src1) && b#$Boolean(src2));
}

procedure {:inline 1} $Or(src1: $Value, src2: $Value) returns (dst: $Value)
free requires is#$Boolean(src1) && is#$Boolean(src2);
{
    dst := $Boolean(b#$Boolean(src1) || b#$Boolean(src2));
}

procedure {:inline 1} $Not(src: $Value) returns (dst: $Value)
free requires is#$Boolean(src);
{
    dst := $Boolean(!b#$Boolean(src));
}

// Pack and Unpack are auto-generated for each type T


// Transaction
// -----------

type {:datatype} $Transaction;
var $txn: $Transaction;
function {:constructor} $Transaction(sender: int) : $Transaction;


// ==================================================================================
// Native Vector Type

function {:inline} $Vector_type_value(tv: $TypeValue): $TypeValue {
    $VectorType(tv)
}



// This is uses the implementation of $ValueArray using integer maps
function {:inline} $Vector_is_well_formed(v: $Value): bool {
    is#$Vector(v) &&
    (
        var va := v#$Vector(v);
        (
            var l := l#$ValueArray(va);
            0 <= l && l <= $MAX_U64 &&
            (forall x: int :: {v#$ValueArray(va)[x]} x < 0 || x >= l ==> v#$ValueArray(va)[x] == $DefaultValue())
        )
    )
}



procedure {:inline 1} $Vector_empty(ta: $TypeValue) returns (v: $Value) {
    v := $mk_vector();
}

procedure {:inline 1} $Vector_is_empty(ta: $TypeValue, v: $Value) returns (b: $Value) {
    assume is#$Vector(v);
    b := $Boolean($vlen(v) == 0);
}

procedure {:inline 1} $Vector_push_back(ta: $TypeValue, v: $Value, val: $Value) returns (v': $Value) {
    assume is#$Vector(v);
    v' := $push_back_vector(v, val);
}

procedure {:inline 1} $Vector_pop_back(ta: $TypeValue, v: $Value) returns (e: $Value, v': $Value) {
    var len: int;
    assume is#$Vector(v);
    len := $vlen(v);
    if (len == 0) {
        $abort_flag := true;
        return;
    }
    e := $select_vector(v, len-1);
    v' := $pop_back_vector(v);
}

procedure {:inline 1} $Vector_append(ta: $TypeValue, v: $Value, other: $Value) returns (v': $Value) {
    assume is#$Vector(v);
    assume is#$Vector(other);
    v' := $append_vector(v, other);
}

procedure {:inline 1} $Vector_reverse(ta: $TypeValue, v: $Value) returns (v': $Value) {
    assume is#$Vector(v);
    v' := $reverse_vector(v);
}

procedure {:inline 1} $Vector_length(ta: $TypeValue, v: $Value) returns (l: $Value) {
    assume is#$Vector(v);
    l := $Integer($vlen(v));
}

procedure {:inline 1} $Vector_borrow(ta: $TypeValue, src: $Value, i: $Value) returns (dst: $Value) {
    var i_ind: int;

    assume is#$Vector(src);
    assume is#$Integer(i);
    i_ind := i#$Integer(i);
    if (i_ind < 0 || i_ind >= $vlen(src)) {
        $abort_flag := true;
        return;
    }
    dst := $select_vector(src, i_ind);
}

procedure {:inline 1} $Vector_borrow_mut(ta: $TypeValue, v: $Value, index: $Value) returns (dst: $Reference, v': $Value)
free requires is#$Integer(index);
{
    var i_ind: int;

    i_ind := i#$Integer(index);
    assume is#$Vector(v);
    if (i_ind < 0 || i_ind >= $vlen(v)) {
        $abort_flag := true;
        return;
    }
    dst := $Reference($Local(0), $Path(p#$Path($EmptyPath)[0 := i_ind], 1), $select_vector(v, i_ind));
    v' := v;
}

procedure {:inline 1} $Vector_destroy_empty(ta: $TypeValue, v: $Value) {
    if ($vlen(v) != 0) {
      $abort_flag := true;
    }
}

procedure {:inline 1} $Vector_swap(ta: $TypeValue, v: $Value, i: $Value, j: $Value) returns (v': $Value)
free requires is#$Integer(i) && is#$Integer(j);
{
    var i_ind: int;
    var j_ind: int;
    assume is#$Vector(v);
    i_ind := i#$Integer(i);
    j_ind := i#$Integer(j);
    if (i_ind >= $vlen(v) || j_ind >= $vlen(v) || i_ind < 0 || j_ind < 0) {
        $abort_flag := true;
        return;
    }
    v' := $swap_vector(v, i_ind, j_ind);
}

procedure {:inline 1} $Vector_remove(ta: $TypeValue, v: $Value, i: $Value) returns (e: $Value, v': $Value)
free requires is#$Integer(i);
{
    var i_ind: int;

    assume is#$Vector(v);
    i_ind := i#$Integer(i);
    if (i_ind < 0 || i_ind >= $vlen(v)) {
        $abort_flag := true;
        return;
    }
    e := $select_vector(v, i_ind);
    v' := $remove_vector(v, i_ind);
}

procedure {:inline 1} $Vector_swap_remove(ta: $TypeValue, v: $Value, i: $Value) returns (e: $Value, v': $Value)
free requires is#$Integer(i);
{
    var i_ind: int;
    var len: int;

    assume is#$Vector(v);
    i_ind := i#$Integer(i);
    len := $vlen(v);
    if (i_ind < 0 || i_ind >= len) {
        $abort_flag := true;
        return;
    }
    e := $select_vector(v, i_ind);
    v' := $pop_back_vector($swap_vector(v, i_ind, len-1));
}

procedure {:inline 1} $Vector_contains(ta: $TypeValue, v: $Value, e: $Value) returns (res: $Value)  {
    assume is#$Vector(v);
    res := $Boolean($contains_vector(v, e));
}

// FIXME: This procedure sometimes (not always) make the test (performance_200511) very slow (> 10 mins) or hang
// although this is not used in the test script (performance_200511). The test finishes in 20 secs when it works fine.
procedure {:inline 1} $Vector_index_of(ta: $TypeValue, v: $Value, e: $Value) returns (res1: $Value, res2: $Value);
requires is#$Vector(v);
ensures is#$Boolean(res1);
ensures is#$Integer(res2);
ensures 0 <= i#$Integer(res2) && i#$Integer(res2) < $vlen(v);
ensures res1 == $Boolean($contains_vector(v, e));
ensures b#$Boolean(res1) ==> $IsEqual($select_vector(v,i#$Integer(res2)), e);
ensures b#$Boolean(res1) ==> (forall i:int :: 0<=i && i<i#$Integer(res2) ==> !$IsEqual($select_vector(v,i), e));
ensures !b#$Boolean(res1) ==> i#$Integer(res2) == 0;

// FIXME: This alternative definition has the same issue as the other one above.
// TODO: Delete this when unnecessary
//procedure {:inline 1} $Vector_index_of(ta: $TypeValue, v: $Value, e: $Value) returns (res1: $Value, res2: $Value) {
//    var b: bool;
//    var i: int;
//    assume is#$Vector(v);
//    b := $contains_vector(v, e);
//    if (b) {
//        havoc i;
//        assume 0 <= i && i < $vlen(v);
//        assume $IsEqual($select_vector(v,i), e);
//        assume (forall j:int :: 0<=j && j<i ==> !$IsEqual($select_vector(v,j), e));
//    }
//    else {
//        i := 0;
//    }
//    res1 := $Boolean(b);
//    res2 := $Integer(i);
//}

// ==================================================================================
// Native hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function {:inline} $Hash_sha2($m: $Memory, $txn: $Transaction, val: $Value): $Value {
    $Hash_sha2_core(val)
}

function $Hash_sha2_core(val: $Value): $Value;

// This says that Hash_sha2 respects isEquals (this would be automatic if we had an
// extensional theory of arrays and used ==, which has the substitution property
// for functions).
axiom (forall v1,v2: $Value :: $Vector_is_well_formed(v1) && $Vector_is_well_formed(v2)
       && $IsEqual(v1, v2) ==> $IsEqual($Hash_sha2_core(v1), $Hash_sha2_core(v2)));

// This says that Hash_sha2 is an injection
axiom (forall v1,v2: $Value :: $Vector_is_well_formed(v1) && $Vector_is_well_formed(v2)
        && $IsEqual($Hash_sha2_core(v1), $Hash_sha2_core(v2)) ==> $IsEqual(v1, v2));

// This procedure has no body. We want Boogie to just use its requires
// and ensures properties when verifying code that calls it.
procedure $Hash_sha2_256(val: $Value) returns (res: $Value);
// It will still work without this, but this helps verifier find more reasonable counterexamples.
free requires $IsValidU8Vector(val);
ensures res == $Hash_sha2_core(val);     // returns Hash_sha2 Value
ensures $IsValidU8Vector(res);    // result is a legal vector of U8s.
ensures $vlen(res) == 32;               // result is 32 bytes.

// similarly for Hash_sha3
function {:inline} $Hash_sha3($m: $Memory, $txn: $Transaction, val: $Value): $Value {
    $Hash_sha3_core(val)
}
function $Hash_sha3_core(val: $Value): $Value;

axiom (forall v1,v2: $Value :: $Vector_is_well_formed(v1) && $Vector_is_well_formed(v2)
       && $IsEqual(v1, v2) ==> $IsEqual($Hash_sha3_core(v1), $Hash_sha3_core(v2)));

axiom (forall v1,v2: $Value :: $Vector_is_well_formed(v1) && $Vector_is_well_formed(v2)
        && $IsEqual($Hash_sha3_core(v1), $Hash_sha3_core(v2)) ==> $IsEqual(v1, v2));

procedure $Hash_sha3_256(val: $Value) returns (res: $Value);
ensures res == $Hash_sha3_core(val);     // returns Hash_sha3 Value
ensures $IsValidU8Vector(res);    // result is a legal vector of U8s.
ensures $vlen(res) == 32;               // result is 32 bytes.

// ==================================================================================
// Native libra_account

// TODO: this function clashes with a similar version in older libraries. This is solved by a hack where the
// translator appends _OLD to the name when encountering this. The hack shall be removed once old library
// sources are not longer used.
procedure {:inline 1} $LibraAccount_save_account_OLD(ta: $TypeValue, balance: $Value, account: $Value, addr: $Value) {
    var a: int;
    var t_T: $TypeValue;
    var l_T: $Location;
    var t_Balance: $TypeValue;
    var l_Balance: $Location;

    a := a#$Address(addr);
    t_T := $LibraAccount_T_type_value();
    if ($ResourceExistsRaw($m, t_T, a)) {
        $abort_flag := true;
        return;
    }

    t_Balance := $LibraAccount_Balance_type_value(ta);
    if ($ResourceExistsRaw($m, t_Balance, a)) {
        $abort_flag := true;
        return;
    }

    l_T := $Global(t_T, a);
    l_Balance := $Global(t_Balance, a);
    $m := $Memory(domain#$Memory($m)[l_T := true][l_Balance := true], contents#$Memory($m)[l_T := account][l_Balance := balance]);
}

procedure {:inline 1} $LibraAccount_save_account(
       t_Token: $TypeValue, t_AT: $TypeValue, account_type: $Value, balance: $Value,
       account: $Value, event_generator: $Value, addr: $Value) {
    // TODO: implement this
    assert false;
}

procedure {:inline 1} $LibraAccount_create_signer(
  addr: $Value
) returns (signer: $Value) {
    // A signer is currently identical to an address.
    signer := addr;
}

procedure {:inline 1} $LibraAccount_destroy_signer(
  signer: $Value
) {
  return;
}

procedure {:inline 1} $LibraAccount_write_to_event_store(ta: $TypeValue, guid: $Value, count: $Value, msg: $Value) {
    // TODO: this is used in old library sources, remove it once those sources are not longer used in tests.
    // This function is modeled as a no-op because the actual side effect of this native function is not observable from the Move side.
}

procedure {:inline 1} $Event_write_to_event_store(ta: $TypeValue, guid: $Value, count: $Value, msg: $Value) {
    // This function is modeled as a no-op because the actual side effect of this native function is not observable from the Move side.
}

// ==================================================================================
// Native Signer

procedure {:inline 1} $Signer_borrow_address(signer: $Value) returns (res: $Value)
    free requires is#$Address(signer);
{
    res := signer;
}

// TODO: implement the below methods
// ==================================================================================
// Native signature

// TODO: implement the below methods. See issue #4666.

procedure {:inline 1} $Signature_ed25519_validate_pubkey(public_key: $Value) returns (res: $Value) {
    res := $Boolean(true);
}

procedure {:inline 1} $Signature_ed25519_verify(signature: $Value, public_key: $Value, message: $Value) returns (res: $Value) {
    res := $Boolean(true);
}

procedure {:inline 1} Signature_ed25519_threshold_verify(bitmap: $Value, signature: $Value, public_key: $Value, message: $Value) returns (res: $Value) {
    assert false; // Signature_ed25519_threshold_verify not implemented
}

// ==================================================================================
// Native LCS::serialize

// native define serialize<MoveValue>(v: &MoveValue): vector<u8>;

// Serialize is modeled as an uninterpreted function, with an additional
// axiom to say it's an injection.

function {:inline} $LCS_serialize($m: $Memory, $txn: $Transaction, ta: $TypeValue, v: $Value): $Value {
    $LCS_serialize_core(v)
}

function $LCS_serialize_core(v: $Value): $Value;
function $LCS_serialize_core_inv(v: $Value): $Value;
// Needed only because IsEqual(v1, v2) is weaker than v1 == v2 in case there is a vector nested inside v1 or v2.
axiom (forall v1, v2: $Value :: $IsEqual(v1, v2) ==> $LCS_serialize_core(v1) == $LCS_serialize_core(v2));
// Injectivity
axiom (forall v: $Value :: $LCS_serialize_core_inv($LCS_serialize_core(v)) == v);

// This says that serialize returns a non-empty vec<u8>

axiom (forall v: $Value :: ( var r := $LCS_serialize_core(v); $IsValidU8Vector(r) && $vlen(r) > 0 &&
                            $vlen(r) <= 4 ));


// Serialized addresses should have the same length
const $serialized_address_len: int;
axiom (forall v: $Value :: (var r := $LCS_serialize_core(v); is#$Address(v) ==> $vlen(r) == $serialized_address_len));

procedure $LCS_to_bytes(ta: $TypeValue, v: $Value) returns (res: $Value);
ensures res == $LCS_serialize($m, $txn, ta, v);
ensures $IsValidU8Vector(res);    // result is a legal vector of U8s.

// ==================================================================================
// Native Signer::spec_address_of

function {:inline} $Signer_spec_address_of($m: $Memory, $txn: $Transaction, signer: $Value): $Value
{
    // A signer is currently identical to an address.
    signer
}

// ==================================================================================
// FixedPoint32 intrinsic functions

procedure $FixedPoint32_multiply_u64(num: $Value, multiplier: $Value) returns (res: $Value);
ensures $IsValidU64(res);

procedure $FixedPoint32_divide_u64(num: $Value, multiplier: $Value) returns (res: $Value);
ensures $IsValidU64(res);

procedure $FixedPoint32_create_from_rational(numerator: $Value, denominator: $Value) returns (res: $Value);
// The predicate in the following line is equivalent to $FixedPoint32_FixedPoint32_is_well_formed(res),
// but written this way to avoid the forward declaration.
ensures $Vector_is_well_formed(res) && $vlen(res) == 1 && $IsValidU64($SelectField(res, 0));

// ==================================================================================
// Mocked out Event module

procedure {:inline 1} $Event_new_event_handle(t: $TypeValue, signer: $Value) returns (res: $Value) {
}

procedure {:inline 1} $Event_publish_generator(account: $Value) {
}

procedure {:inline 1} $Event_emit_event(t: $TypeValue, handler: $Value, msg: $Value) returns (res: $Value) {
    res := handler;
}



// ** spec vars of module FixedPoint32



// ** spec funs of module FixedPoint32



// ** structs of module FixedPoint32

const unique $FixedPoint32_FixedPoint32: $TypeName;
const $FixedPoint32_FixedPoint32_value: $FieldName;
axiom $FixedPoint32_FixedPoint32_value == 0;
function $FixedPoint32_FixedPoint32_type_value(): $TypeValue {
    $StructType($FixedPoint32_FixedPoint32, $TypeValueArray($MapConstTypeValue($DefaultTypeValue()), 0), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $IntegerType()], 1))
}
function {:inline} $FixedPoint32_FixedPoint32_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $IsValidU64($SelectField($this, $FixedPoint32_FixedPoint32_value))
}
function {:inline} $FixedPoint32_FixedPoint32_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $IsValidU64($SelectField($this, $FixedPoint32_FixedPoint32_value))
}

procedure {:inline 1} $FixedPoint32_FixedPoint32_pack($file_id: int, $byte_index: int, $var_idx: int, value: $Value) returns ($struct: $Value)
{
    assume $IsValidU64(value);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := value], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $FixedPoint32_FixedPoint32_unpack($struct: $Value) returns (value: $Value)
{
    assume is#$Vector($struct);
    value := $SelectField($struct, $FixedPoint32_FixedPoint32_value);
    assume $IsValidU64(value);
}



// ** functions of module FixedPoint32

procedure {:inline 1} $FixedPoint32_create_from_raw_value_def(value: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $IntegerType()
    var $t2: $Value; // $FixedPoint32_FixedPoint32_type_value()
    var $t3: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(6, 2977, 0, value); }

    // bytecode translation starts here
    // $t3 := move(value)
    call $tmp := $CopyOrMoveValue(value);
    $t3 := $tmp;

    // $t2 := pack FixedPoint32::FixedPoint32($t3)
    call $tmp := $FixedPoint32_FixedPoint32_pack(0, 0, 0, $t3);
    $t2 := $tmp;

    // return $t2
    $ret0 := $t2;
    if (true) { assume $DebugTrackLocal(6, 3046, 4, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $FixedPoint32_create_from_raw_value(value: $Value) returns ($ret0: $Value)
free requires $IsValidU64(value);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($Boolean(false))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(false)))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($ret0, $Vector($ExtendValueArray($EmptyValueArray(), value))))));
{
    call $ret0 := $FixedPoint32_create_from_raw_value_def(value);
}

procedure {:inline 1} $FixedPoint32_get_raw_value_def(num: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $FixedPoint32_FixedPoint32_type_value()
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $IntegerType()
    var $t4: $Value; // $FixedPoint32_FixedPoint32_type_value()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(6, 3257, 0, num); }

    // bytecode translation starts here
    // $t4 := move(num)
    call $tmp := $CopyOrMoveValue(num);
    $t4 := $tmp;

    // $t1 := copy($t4)
    call $tmp := $CopyOrMoveValue($t4);
    $t1 := $tmp;

    // $t2 := get_field<FixedPoint32::FixedPoint32>.value($t1)
    call $tmp := $GetFieldFromValue($t1, $FixedPoint32_FixedPoint32_value);
    assume $IsValidU64($tmp);
    $t2 := $tmp;

    // $t3 := move($t2)
    call $tmp := $CopyOrMoveValue($t2);
    $t3 := $tmp;

    // return $t3
    $ret0 := $t3;
    if (true) { assume $DebugTrackLocal(6, 3316, 5, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $FixedPoint32_get_raw_value(num: $Value) returns ($ret0: $Value)
free requires $FixedPoint32_FixedPoint32_is_well_formed(num);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($Boolean(false))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(false)))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($ret0, $SelectField(num, $FixedPoint32_FixedPoint32_value)))));
{
    call $ret0 := $FixedPoint32_get_raw_value_def(num);
}



// ** spec vars of module Vector



// ** spec funs of module Vector

function {:inline} $Vector_spec_contains($tv0: $TypeValue, v: $Value, e: $Value): $Value {
    $Boolean((var $range_1 := v; (exists $i_0: int :: $InVectorRange($range_1, $i_0) && (var x := $select_vector($range_1, $i_0); b#$Boolean($Boolean($IsEqual(x, e)))))))
}

function {:inline} $Vector_eq_push_back($tv0: $TypeValue, v1: $Value, v2: $Value, e: $Value): $Value {
    $Boolean(b#$Boolean($Boolean(b#$Boolean($Boolean($IsEqual($vlen_value(v1), $Integer(i#$Integer($vlen_value(v2)) + i#$Integer($Integer(1)))))) && b#$Boolean($Boolean($IsEqual($select_vector_by_value(v1, $Integer(i#$Integer($vlen_value(v1)) - i#$Integer($Integer(1)))), e))))) && b#$Boolean($Boolean($IsEqual($slice_vector(v1, $Range($Integer(0), $Integer(i#$Integer($vlen_value(v1)) - i#$Integer($Integer(1))))), $slice_vector(v2, $Range($Integer(0), $vlen_value(v2)))))))
}

function {:inline} $Vector_eq_append($tv0: $TypeValue, v: $Value, v1: $Value, v2: $Value): $Value {
    $Boolean(b#$Boolean($Boolean(b#$Boolean($Boolean($IsEqual($vlen_value(v), $Integer(i#$Integer($vlen_value(v1)) + i#$Integer($vlen_value(v2)))))) && b#$Boolean($Boolean($IsEqual($slice_vector(v, $Range($Integer(0), $vlen_value(v1))), v1))))) && b#$Boolean($Boolean($IsEqual($slice_vector(v, $Range($vlen_value(v1), $vlen_value(v))), v2))))
}

function {:inline} $Vector_eq_pop_front($tv0: $TypeValue, v1: $Value, v2: $Value): $Value {
    $Boolean(b#$Boolean($Boolean($IsEqual($Integer(i#$Integer($vlen_value(v1)) + i#$Integer($Integer(1))), $vlen_value(v2)))) && b#$Boolean($Boolean($IsEqual(v1, $slice_vector(v2, $Range($Integer(1), $vlen_value(v2)))))))
}



// ** structs of module Vector



// ** functions of module Vector

procedure {:inline 1} $Vector_singleton_def($tv0: $TypeValue, e: $Value) returns ($ret0: $Value){
    // declare local variables
    var v: $Value; // $Vector_type_value($tv0)
    var $t2: $Value; // $Vector_type_value($tv0)
    var $t3: $Reference; // ReferenceType($Vector_type_value($tv0))
    var $t4: $Value; // $tv0
    var $t5: $Value; // $Vector_type_value($tv0)
    var $t6: $Value; // $tv0
    var $t7: $Value; // $Vector_type_value($tv0)
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(17, 1206, 0, e); }

    // bytecode translation starts here
    // $t6 := move(e)
    call $tmp := $CopyOrMoveValue(e);
    $t6 := $tmp;

    // $t2 := Vector::empty<#0>()
    call $t2 := $Vector_empty($tv0);
    if ($abort_flag) {
      assume $DebugTrackAbort(17, 136);
      goto Abort;
    }
    assume $Vector_is_well_formed($t2);


    // v := $t2
    call $tmp := $CopyOrMoveValue($t2);
    v := $tmp;
    if (true) { assume $DebugTrackLocal(17, 1279, 1, $tmp); }

    // $t3 := borrow_local(v)
    call $t3 := $BorrowLoc(1, v);
    assume $Vector_is_well_formed($Dereference($t3));

    // UnpackRef($t3)

    // PackRef($t3)

    // $t7 := read_ref($t3)
    call $tmp := $ReadRef($t3);
    assume $Vector_is_well_formed($tmp);
    $t7 := $tmp;

    // $t7 := Vector::push_back<#0>($t7, $t6)
    call $t7 := $Vector_push_back($tv0, $t7, $t6);
    if ($abort_flag) {
      assume $DebugTrackAbort(17, 499);
      goto Abort;
    }
    assume $Vector_is_well_formed($t7);


    // write_ref($t3, $t7)
    call $t3 := $WriteRef($t3, $t7);

    // LocalRoot(v) <- $t3
    call v := $WritebackToValue($t3, 1, v);

    // UnpackRef($t3)

    // PackRef($t3)

    // return v
    $ret0 := v;
    if (true) { assume $DebugTrackLocal(17, 1330, 8, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Vector_singleton($tv0: $TypeValue, e: $Value) returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $ret0 := $Vector_singleton_def($tv0, e);
}



// ** spec vars of module Signer



// ** spec funs of module Signer



// ** structs of module Signer



// ** functions of module Signer

procedure {:inline 1} $Signer_address_of_def(s: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $AddressType()
    var $t2: $Value; // $AddressType()
    var $t3: $Value; // $AddressType()
    var $t4: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(16, 407, 0, s); }

    // bytecode translation starts here
    // $t4 := move(s)
    call $tmp := $CopyOrMoveValue(s);
    $t4 := $tmp;

    // $t1 := move($t4)
    call $tmp := $CopyOrMoveValue($t4);
    $t1 := $tmp;

    // $t2 := Signer::borrow_address($t1)
    call $t2 := $Signer_borrow_address($t1);
    if ($abort_flag) {
      assume $DebugTrackAbort(16, 324);
      goto Abort;
    }
    assume is#$Address($t2);


    // $t3 := move($t2)
    call $tmp := $CopyOrMoveValue($t2);
    $t3 := $tmp;

    // return $t3
    $ret0 := $t3;
    if (true) { assume $DebugTrackLocal(16, 460, 5, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Signer_address_of(s: $Value) returns ($ret0: $Value)
free requires is#$Address(s);
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $ret0 := $Signer_address_of_def(s);
}



// ** spec vars of module LCS



// ** spec funs of module LCS



// ** structs of module LCS



// ** functions of module LCS



// ** spec vars of module Event



// ** spec funs of module Event



// ** structs of module Event

const unique $Event_EventHandle: $TypeName;
const $Event_EventHandle_counter: $FieldName;
axiom $Event_EventHandle_counter == 0;
const $Event_EventHandle_guid: $FieldName;
axiom $Event_EventHandle_guid == 1;
function $Event_EventHandle_type_value($tv0: $TypeValue): $TypeValue {
    $StructType($Event_EventHandle, $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $tv0], 1), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $IntegerType()][1 := $Vector_type_value($IntegerType())], 2))
}
function {:inline} $Event_EventHandle_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 2
      && $IsValidU64($SelectField($this, $Event_EventHandle_counter))
      && $Vector_is_well_formed($SelectField($this, $Event_EventHandle_guid)) && (forall $$0: int :: {$select_vector($SelectField($this, $Event_EventHandle_guid),$$0)} $$0 >= 0 && $$0 < $vlen($SelectField($this, $Event_EventHandle_guid)) ==> $IsValidU8($select_vector($SelectField($this, $Event_EventHandle_guid),$$0)))
}
function {:inline} $Event_EventHandle_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 2
      && $IsValidU64($SelectField($this, $Event_EventHandle_counter))
      && $Vector_is_well_formed($SelectField($this, $Event_EventHandle_guid)) && (forall $$0: int :: {$select_vector($SelectField($this, $Event_EventHandle_guid),$$0)} $$0 >= 0 && $$0 < $vlen($SelectField($this, $Event_EventHandle_guid)) ==> $IsValidU8($select_vector($SelectField($this, $Event_EventHandle_guid),$$0)))
}

axiom (forall m: $Memory, a: $Value, $tv0: $TypeValue :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $Event_EventHandle_is_well_formed($ResourceValue(m, $Event_EventHandle_type_value($tv0), a))
);

procedure {:inline 1} $Event_EventHandle_pack($file_id: int, $byte_index: int, $var_idx: int, $tv0: $TypeValue, counter: $Value, guid: $Value) returns ($struct: $Value)
{
    assume $IsValidU64(counter);
    assume $Vector_is_well_formed(guid) && (forall $$0: int :: {$select_vector(guid,$$0)} $$0 >= 0 && $$0 < $vlen(guid) ==> $IsValidU8($select_vector(guid,$$0)));
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := counter][1 := guid], 2));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $Event_EventHandle_unpack($tv0: $TypeValue, $struct: $Value) returns (counter: $Value, guid: $Value)
{
    assume is#$Vector($struct);
    counter := $SelectField($struct, $Event_EventHandle_counter);
    assume $IsValidU64(counter);
    guid := $SelectField($struct, $Event_EventHandle_guid);
    assume $Vector_is_well_formed(guid) && (forall $$0: int :: {$select_vector(guid,$$0)} $$0 >= 0 && $$0 < $vlen(guid) ==> $IsValidU8($select_vector(guid,$$0)));
}

const unique $Event_EventHandleGenerator: $TypeName;
const $Event_EventHandleGenerator_counter: $FieldName;
axiom $Event_EventHandleGenerator_counter == 0;
const $Event_EventHandleGenerator_addr: $FieldName;
axiom $Event_EventHandleGenerator_addr == 1;
function $Event_EventHandleGenerator_type_value(): $TypeValue {
    $StructType($Event_EventHandleGenerator, $TypeValueArray($MapConstTypeValue($DefaultTypeValue()), 0), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $IntegerType()][1 := $AddressType()], 2))
}
function {:inline} $Event_EventHandleGenerator_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 2
      && $IsValidU64($SelectField($this, $Event_EventHandleGenerator_counter))
      && is#$Address($SelectField($this, $Event_EventHandleGenerator_addr))
}
function {:inline} $Event_EventHandleGenerator_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 2
      && $IsValidU64($SelectField($this, $Event_EventHandleGenerator_counter))
      && is#$Address($SelectField($this, $Event_EventHandleGenerator_addr))
}

axiom (forall m: $Memory, a: $Value :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $Event_EventHandleGenerator_is_well_formed($ResourceValue(m, $Event_EventHandleGenerator_type_value(), a))
);

procedure {:inline 1} $Event_EventHandleGenerator_pack($file_id: int, $byte_index: int, $var_idx: int, counter: $Value, addr: $Value) returns ($struct: $Value)
{
    assume $IsValidU64(counter);
    assume is#$Address(addr);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := counter][1 := addr], 2));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $Event_EventHandleGenerator_unpack($struct: $Value) returns (counter: $Value, addr: $Value)
{
    assume is#$Vector($struct);
    counter := $SelectField($struct, $Event_EventHandleGenerator_counter);
    assume $IsValidU64(counter);
    addr := $SelectField($struct, $Event_EventHandleGenerator_addr);
    assume is#$Address(addr);
}



// ** functions of module Event



// ** spec vars of module CoreAddresses



// ** spec funs of module CoreAddresses

function {:inline} $CoreAddresses_SPEC_LIBRA_ROOT_ADDRESS(): $Value {
    $Address(173345816)
}

function {:inline} $CoreAddresses_SPEC_CURRENCY_INFO_ADDRESS(): $Value {
    $Address(173345816)
}

function {:inline} $CoreAddresses_SPEC_TREASURY_COMPLIANCE_ADDRESS(): $Value {
    $Address(186537453)
}

function {:inline} $CoreAddresses_SPEC_VM_RESERVED_ADDRESS(): $Value {
    $Address(0)
}



// ** structs of module CoreAddresses



// ** functions of module CoreAddresses

procedure {:inline 1} $CoreAddresses_CURRENCY_INFO_ADDRESS_def() returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := 0xa550c18
    $tmp := $Address(173345816);
    $t0 := $tmp;

    // return $t0
    $ret0 := $t0;
    if (true) { assume $DebugTrackLocal(4, 890, 1, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $CoreAddresses_CURRENCY_INFO_ADDRESS() returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $ret0 := $CoreAddresses_CURRENCY_INFO_ADDRESS_def();
}

procedure {:inline 1} $CoreAddresses_LIBRA_ROOT_ADDRESS_def() returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := 0xa550c18
    $tmp := $Address(173345816);
    $t0 := $tmp;

    // return $t0
    $ret0 := $t0;
    if (true) { assume $DebugTrackLocal(4, 330, 1, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $CoreAddresses_LIBRA_ROOT_ADDRESS() returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $ret0 := $CoreAddresses_LIBRA_ROOT_ADDRESS_def();
}

procedure {:inline 1} $CoreAddresses_TREASURY_COMPLIANCE_ADDRESS_def() returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := 0xb1e55ed
    $tmp := $Address(186537453);
    $t0 := $tmp;

    // return $t0
    $ret0 := $t0;
    if (true) { assume $DebugTrackLocal(4, 1358, 1, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $CoreAddresses_TREASURY_COMPLIANCE_ADDRESS() returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $ret0 := $CoreAddresses_TREASURY_COMPLIANCE_ADDRESS_def();
}

procedure {:inline 1} $CoreAddresses_VM_RESERVED_ADDRESS_def() returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := 0x0
    $tmp := $Address(0);
    $t0 := $tmp;

    // return $t0
    $ret0 := $t0;
    if (true) { assume $DebugTrackLocal(4, 1894, 1, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $CoreAddresses_VM_RESERVED_ADDRESS() returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $ret0 := $CoreAddresses_VM_RESERVED_ADDRESS_def();
}



// ** spec vars of module LibraTimestamp



// ** spec funs of module LibraTimestamp

function {:inline} $LibraTimestamp_spec_is_genesis($m: $Memory, $txn: $Transaction): $Value {
    $Boolean(!b#$Boolean($ResourceExists($m, $LibraTimestamp_TimeHasStarted_type_value(), $CoreAddresses_SPEC_LIBRA_ROOT_ADDRESS())))
}

function {:inline} $LibraTimestamp_spec_is_not_initialized($m: $Memory, $txn: $Transaction): $Value {
    $Boolean(b#$Boolean($Boolean(!b#$Boolean($LibraTimestamp_root_ctm_initialized($m, $txn)))) || b#$Boolean($Boolean($IsEqual($LibraTimestamp_spec_now_microseconds($m, $txn), $Integer(0)))))
}

function {:inline} $LibraTimestamp_root_ctm_initialized($m: $Memory, $txn: $Transaction): $Value {
    $ResourceExists($m, $LibraTimestamp_CurrentTimeMicroseconds_type_value(), $CoreAddresses_SPEC_LIBRA_ROOT_ADDRESS())
}

function {:inline} $LibraTimestamp_spec_now_microseconds($m: $Memory, $txn: $Transaction): $Value {
    $SelectField($ResourceValue($m, $LibraTimestamp_CurrentTimeMicroseconds_type_value(), $CoreAddresses_SPEC_LIBRA_ROOT_ADDRESS()), $LibraTimestamp_CurrentTimeMicroseconds_microseconds)
}



// ** structs of module LibraTimestamp

const unique $LibraTimestamp_CurrentTimeMicroseconds: $TypeName;
const $LibraTimestamp_CurrentTimeMicroseconds_microseconds: $FieldName;
axiom $LibraTimestamp_CurrentTimeMicroseconds_microseconds == 0;
function $LibraTimestamp_CurrentTimeMicroseconds_type_value(): $TypeValue {
    $StructType($LibraTimestamp_CurrentTimeMicroseconds, $TypeValueArray($MapConstTypeValue($DefaultTypeValue()), 0), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $IntegerType()], 1))
}
function {:inline} $LibraTimestamp_CurrentTimeMicroseconds_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $IsValidU64($SelectField($this, $LibraTimestamp_CurrentTimeMicroseconds_microseconds))
}
function {:inline} $LibraTimestamp_CurrentTimeMicroseconds_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $IsValidU64($SelectField($this, $LibraTimestamp_CurrentTimeMicroseconds_microseconds))
}

axiom (forall m: $Memory, a: $Value :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $LibraTimestamp_CurrentTimeMicroseconds_is_well_formed($ResourceValue(m, $LibraTimestamp_CurrentTimeMicroseconds_type_value(), a))
);

procedure {:inline 1} $LibraTimestamp_CurrentTimeMicroseconds_pack($file_id: int, $byte_index: int, $var_idx: int, microseconds: $Value) returns ($struct: $Value)
{
    assume $IsValidU64(microseconds);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := microseconds], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $LibraTimestamp_CurrentTimeMicroseconds_unpack($struct: $Value) returns (microseconds: $Value)
{
    assume is#$Vector($struct);
    microseconds := $SelectField($struct, $LibraTimestamp_CurrentTimeMicroseconds_microseconds);
    assume $IsValidU64(microseconds);
}

const unique $LibraTimestamp_TimeHasStarted: $TypeName;
const $LibraTimestamp_TimeHasStarted_dummy_field: $FieldName;
axiom $LibraTimestamp_TimeHasStarted_dummy_field == 0;
function $LibraTimestamp_TimeHasStarted_type_value(): $TypeValue {
    $StructType($LibraTimestamp_TimeHasStarted, $TypeValueArray($MapConstTypeValue($DefaultTypeValue()), 0), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $BooleanType()], 1))
}
function {:inline} $LibraTimestamp_TimeHasStarted_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && is#$Boolean($SelectField($this, $LibraTimestamp_TimeHasStarted_dummy_field))
}
function {:inline} $LibraTimestamp_TimeHasStarted_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && is#$Boolean($SelectField($this, $LibraTimestamp_TimeHasStarted_dummy_field))
}

axiom (forall m: $Memory, a: $Value :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $LibraTimestamp_TimeHasStarted_is_well_formed($ResourceValue(m, $LibraTimestamp_TimeHasStarted_type_value(), a))
);

procedure {:inline 1} $LibraTimestamp_TimeHasStarted_pack($file_id: int, $byte_index: int, $var_idx: int, dummy_field: $Value) returns ($struct: $Value)
{
    assume is#$Boolean(dummy_field);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := dummy_field], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $LibraTimestamp_TimeHasStarted_unpack($struct: $Value) returns (dummy_field: $Value)
{
    assume is#$Vector($struct);
    dummy_field := $SelectField($struct, $LibraTimestamp_TimeHasStarted_dummy_field);
    assume is#$Boolean(dummy_field);
}



// ** functions of module LibraTimestamp

procedure {:inline 1} $LibraTimestamp_assert_is_genesis_def() returns (){
    // declare local variables
    var $t0: $Value; // $BooleanType()
    var $t1: $Value; // $IntegerType()
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t2 := LibraTimestamp::is_genesis()
    call $t2 := $LibraTimestamp_is_genesis();
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 3650);
      goto Abort;
    }
    assume is#$Boolean($t2);


    // $t0 := $t2
    call $tmp := $CopyOrMoveValue($t2);
    $t0 := $tmp;
    if (true) { assume $DebugTrackLocal(12, 4119, 0, $tmp); }

    // if ($t0) goto L0 else goto L1
    $tmp := $t0;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t4 := 0
    $tmp := $Integer(0);
    $t4 := $tmp;

    // abort($t4)
    if (true) { assume $DebugTrackAbort(12, 4119); }
    goto Abort;

    // L0:
L0:

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraTimestamp_assert_is_genesis() returns ()
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn))))) ==> b#$Boolean($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> b#$Boolean($LibraTimestamp_root_ctm_initialized($m, $txn)))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> b#$Boolean($Boolean(i#$Integer(old($LibraTimestamp_spec_now_microseconds($m, $txn))) <= i#$Integer($LibraTimestamp_spec_now_microseconds($m, $txn)))))));
{
    call $LibraTimestamp_assert_is_genesis_def();
}

procedure {:inline 1} $LibraTimestamp_initialize_def(association: $Value) returns (){
    // declare local variables
    var timer: $Value; // $LibraTimestamp_CurrentTimeMicroseconds_type_value()
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $IntegerType()
    var $t4: $Value; // $AddressType()
    var $t5: $Value; // $AddressType()
    var $t6: $Value; // $AddressType()
    var $t7: $Value; // $BooleanType()
    var $t8: $Value; // $BooleanType()
    var $t9: $Value; // $AddressType()
    var $t10: $Value; // $IntegerType()
    var $t11: $Value; // $AddressType()
    var $t12: $Value; // $IntegerType()
    var $t13: $Value; // $LibraTimestamp_CurrentTimeMicroseconds_type_value()
    var $t14: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(12, 1066, 0, association); }

    // bytecode translation starts here
    // $t14 := move(association)
    call $tmp := $CopyOrMoveValue(association);
    $t14 := $tmp;

    // $t4 := copy($t14)
    call $tmp := $CopyOrMoveValue($t14);
    $t4 := $tmp;

    // $t5 := Signer::address_of($t4)
    call $t5 := $Signer_address_of($t4);
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 1211);
      goto Abort;
    }
    assume is#$Address($t5);


    // $t6 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t6 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 1253);
      goto Abort;
    }
    assume is#$Address($t6);


    // $t7 := ==($t5, $t6)
    $tmp := $Boolean($IsEqual($t5, $t6));
    $t7 := $tmp;

    // $t2 := $t7
    call $tmp := $CopyOrMoveValue($t7);
    $t2 := $tmp;
    if (true) { assume $DebugTrackLocal(12, 1196, 2, $tmp); }

    // if ($t2) goto L0 else goto L1
    $tmp := $t2;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t9 := move($t14)
    call $tmp := $CopyOrMoveValue($t14);
    $t9 := $tmp;

    // destroy($t9)

    // $t10 := 1
    $tmp := $Integer(1);
    $t10 := $tmp;

    // abort($t10)
    if (true) { assume $DebugTrackAbort(12, 1196); }
    goto Abort;

    // L0:
L0:

    // $t11 := move($t14)
    call $tmp := $CopyOrMoveValue($t14);
    $t11 := $tmp;

    // $t12 := 0
    $tmp := $Integer(0);
    $t12 := $tmp;

    // $t13 := pack LibraTimestamp::CurrentTimeMicroseconds($t12)
    call $tmp := $LibraTimestamp_CurrentTimeMicroseconds_pack(0, 0, 0, $t12);
    $t13 := $tmp;

    // move_to<LibraTimestamp::CurrentTimeMicroseconds>($t13, $t11)
    call $MoveTo($LibraTimestamp_CurrentTimeMicroseconds_type_value(), $t13, $t11);
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 1424);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraTimestamp_initialize(association: $Value) returns ()
free requires is#$Address(association);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($Boolean(!$IsEqual($Signer_spec_address_of($m, $txn, association), $CoreAddresses_SPEC_LIBRA_ROOT_ADDRESS())))) ==> $abort_flag;
free ensures b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(!$IsEqual($Signer_spec_address_of($m, $txn, association), $CoreAddresses_SPEC_LIBRA_ROOT_ADDRESS())))))
    || b#$Boolean(old(($LibraTimestamp_root_ctm_initialized($m, $txn)))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn))))) ==> b#$Boolean($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> b#$Boolean($LibraTimestamp_root_ctm_initialized($m, $txn)))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> b#$Boolean($Boolean(i#$Integer(old($LibraTimestamp_spec_now_microseconds($m, $txn))) <= i#$Integer($LibraTimestamp_spec_now_microseconds($m, $txn)))))));
free ensures !$abort_flag ==> (b#$Boolean($LibraTimestamp_root_ctm_initialized($m, $txn)));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($LibraTimestamp_spec_now_microseconds($m, $txn), $Integer(0)))));
{
    call $LibraTimestamp_initialize_def(association);
}

procedure {:inline 1} $LibraTimestamp_is_genesis_def() returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $AddressType()
    var $t1: $Value; // $BooleanType()
    var $t2: $Value; // $BooleanType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t0 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 3718);
      goto Abort;
    }
    assume is#$Address($t0);


    // $t1 := exists<LibraTimestamp::TimeHasStarted>($t0)
    call $tmp := $Exists($t0, $LibraTimestamp_TimeHasStarted_type_value());
    $t1 := $tmp;

    // $t2 := !($t1)
    call $tmp := $Not($t1);
    $t2 := $tmp;

    // return $t2
    $ret0 := $t2;
    if (true) { assume $DebugTrackLocal(12, 3679, 3, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $LibraTimestamp_is_genesis() returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($Boolean(false))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(false)))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn))))) ==> b#$Boolean($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> b#$Boolean($LibraTimestamp_root_ctm_initialized($m, $txn)))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> b#$Boolean($Boolean(i#$Integer(old($LibraTimestamp_spec_now_microseconds($m, $txn))) <= i#$Integer($LibraTimestamp_spec_now_microseconds($m, $txn)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($ret0, $LibraTimestamp_spec_is_genesis($m, $txn)))));
{
    call $ret0 := $LibraTimestamp_is_genesis_def();
}

procedure {:inline 1} $LibraTimestamp_is_not_initialized_def() returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $BooleanType()
    var $t1: $Value; // $AddressType()
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $BooleanType()
    var $t5: $Value; // $IntegerType()
    var $t6: $Value; // $IntegerType()
    var $t7: $Value; // $BooleanType()
    var $t8: $Value; // $BooleanType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t1 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t1 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 3962);
      goto Abort;
    }
    assume is#$Address($t1);


    // $t2 := exists<LibraTimestamp::CurrentTimeMicroseconds>($t1)
    call $tmp := $Exists($t1, $LibraTimestamp_CurrentTimeMicroseconds_type_value());
    $t2 := $tmp;

    // $t3 := !($t2)
    call $tmp := $Not($t2);
    $t3 := $tmp;

    // if ($t3) goto L0 else goto L1
    $tmp := $t3;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // goto L2
    goto L2;

    // L0:
L0:

    // $t4 := true
    $tmp := $Boolean(true);
    $t4 := $tmp;

    // $t0 := $t4
    call $tmp := $CopyOrMoveValue($t4);
    $t0 := $tmp;
    if (true) { assume $DebugTrackLocal(12, 3914, 0, $tmp); }

    // goto L3
    goto L3;

    // L2:
L2:

    // $t5 := LibraTimestamp::now_microseconds()
    call $t5 := $LibraTimestamp_now_microseconds();
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 3396);
      goto Abort;
    }
    assume $IsValidU64($t5);


    // $t6 := 0
    $tmp := $Integer(0);
    $t6 := $tmp;

    // $t7 := ==($t5, $t6)
    $tmp := $Boolean($IsEqual($t5, $t6));
    $t7 := $tmp;

    // $t0 := $t7
    call $tmp := $CopyOrMoveValue($t7);
    $t0 := $tmp;
    if (true) { assume $DebugTrackLocal(12, 3914, 0, $tmp); }

    // goto L3
    goto L3;

    // L3:
L3:

    // return $t0
    $ret0 := $t0;
    if (true) { assume $DebugTrackLocal(12, 3914, 9, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $LibraTimestamp_is_not_initialized() returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($Boolean(false))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(false)))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn))))) ==> b#$Boolean($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> b#$Boolean($LibraTimestamp_root_ctm_initialized($m, $txn)))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> b#$Boolean($Boolean(i#$Integer(old($LibraTimestamp_spec_now_microseconds($m, $txn))) <= i#$Integer($LibraTimestamp_spec_now_microseconds($m, $txn)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($ret0, $LibraTimestamp_spec_is_not_initialized($m, $txn)))));
{
    call $ret0 := $LibraTimestamp_is_not_initialized_def();
}

procedure {:inline 1} $LibraTimestamp_now_microseconds_def() returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $AddressType()
    var $t1: $Value; // $LibraTimestamp_CurrentTimeMicroseconds_type_value()
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t0 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 3517);
      goto Abort;
    }
    assume is#$Address($t0);


    // $t1 := get_global<LibraTimestamp::CurrentTimeMicroseconds>($t0)
    call $tmp := $GetGlobal($t0, $LibraTimestamp_CurrentTimeMicroseconds_type_value());
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 3463);
      goto Abort;
    }
    assume $LibraTimestamp_CurrentTimeMicroseconds_is_well_formed($tmp);
    $t1 := $tmp;

    // $t2 := get_field<LibraTimestamp::CurrentTimeMicroseconds>.microseconds($t1)
    call $tmp := $GetFieldFromValue($t1, $LibraTimestamp_CurrentTimeMicroseconds_microseconds);
    assume $IsValidU64($tmp);
    $t2 := $tmp;

    // $t3 := move($t2)
    call $tmp := $CopyOrMoveValue($t2);
    $t3 := $tmp;

    // return $t3
    $ret0 := $t3;
    if (true) { assume $DebugTrackLocal(12, 3463, 4, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $LibraTimestamp_now_microseconds() returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($Boolean(!b#$Boolean($ResourceExists($m, $LibraTimestamp_CurrentTimeMicroseconds_type_value(), $CoreAddresses_SPEC_LIBRA_ROOT_ADDRESS()))))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(!b#$Boolean($ResourceExists($m, $LibraTimestamp_CurrentTimeMicroseconds_type_value(), $CoreAddresses_SPEC_LIBRA_ROOT_ADDRESS())))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn))))) ==> b#$Boolean($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> b#$Boolean($LibraTimestamp_root_ctm_initialized($m, $txn)))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> b#$Boolean($Boolean(i#$Integer(old($LibraTimestamp_spec_now_microseconds($m, $txn))) <= i#$Integer($LibraTimestamp_spec_now_microseconds($m, $txn)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($ret0, $LibraTimestamp_spec_now_microseconds($m, $txn)))));
{
    call $ret0 := $LibraTimestamp_now_microseconds_def();
}

procedure {:inline 1} $LibraTimestamp_reset_time_has_started_for_test_def() returns (){
    // declare local variables
    var $t0: $Value; // $AddressType()
    var $t1: $Value; // $LibraTimestamp_TimeHasStarted_type_value()
    var $t2: $Value; // $BooleanType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t0 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 2365);
      goto Abort;
    }
    assume is#$Address($t0);


    // $t1 := move_from<LibraTimestamp::TimeHasStarted>($t0)
    call $tmp := $MoveFrom($t0, $LibraTimestamp_TimeHasStarted_type_value());
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 2324);
      goto Abort;
    }
    assume $LibraTimestamp_TimeHasStarted_is_well_formed($tmp);
    $t1 := $tmp;

    // $t2 := unpack LibraTimestamp::TimeHasStarted($t1)
    call $t2 := $LibraTimestamp_TimeHasStarted_unpack($t1);
    $t2 := $t2;

    // destroy($t2)

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraTimestamp_reset_time_has_started_for_test() returns ()
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> b#$Boolean($Boolean(i#$Integer(old($LibraTimestamp_spec_now_microseconds($m, $txn))) <= i#$Integer($LibraTimestamp_spec_now_microseconds($m, $txn)))))));
{
    call $LibraTimestamp_reset_time_has_started_for_test_def();
}

procedure {:inline 1} $LibraTimestamp_set_time_has_started_def(association: $Value) returns (){
    // declare local variables
    var $t1: $Value; // $BooleanType()
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $IntegerType()
    var $t5: $Value; // $BooleanType()
    var $t6: $Value; // $AddressType()
    var $t7: $Value; // $AddressType()
    var $t8: $Value; // $AddressType()
    var $t9: $Value; // $BooleanType()
    var $t10: $Value; // $BooleanType()
    var $t11: $Value; // $AddressType()
    var $t12: $Value; // $IntegerType()
    var $t13: $Value; // $AddressType()
    var $t14: $Value; // $BooleanType()
    var $t15: $Value; // $IntegerType()
    var $t16: $Value; // $IntegerType()
    var $t17: $Value; // $BooleanType()
    var $t18: $Value; // $BooleanType()
    var $t19: $Value; // $BooleanType()
    var $t20: $Value; // $BooleanType()
    var $t21: $Value; // $AddressType()
    var $t22: $Value; // $IntegerType()
    var $t23: $Value; // $AddressType()
    var $t24: $Value; // $BooleanType()
    var $t25: $Value; // $LibraTimestamp_TimeHasStarted_type_value()
    var $t26: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(12, 1564, 0, association); }

    // bytecode translation starts here
    // $t26 := move(association)
    call $tmp := $CopyOrMoveValue(association);
    $t26 := $tmp;

    // $t6 := copy($t26)
    call $tmp := $CopyOrMoveValue($t26);
    $t6 := $tmp;

    // $t7 := Signer::address_of($t6)
    call $t7 := $Signer_address_of($t6);
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 1676);
      goto Abort;
    }
    assume is#$Address($t7);


    // $t8 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t8 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 1718);
      goto Abort;
    }
    assume is#$Address($t8);


    // $t9 := ==($t7, $t8)
    $tmp := $Boolean($IsEqual($t7, $t8));
    $t9 := $tmp;

    // $t1 := $t9
    call $tmp := $CopyOrMoveValue($t9);
    $t1 := $tmp;
    if (true) { assume $DebugTrackLocal(12, 1661, 1, $tmp); }

    // if ($t1) goto L0 else goto L1
    $tmp := $t1;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t11 := move($t26)
    call $tmp := $CopyOrMoveValue($t26);
    $t11 := $tmp;

    // destroy($t11)

    // $t12 := 1
    $tmp := $Integer(1);
    $t12 := $tmp;

    // abort($t12)
    if (true) { assume $DebugTrackAbort(12, 1661); }
    goto Abort;

    // L0:
L0:

    // $t13 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t13 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 1872);
      goto Abort;
    }
    assume is#$Address($t13);


    // $t14 := exists<LibraTimestamp::CurrentTimeMicroseconds>($t13)
    call $tmp := $Exists($t13, $LibraTimestamp_CurrentTimeMicroseconds_type_value());
    $t14 := $tmp;

    // if ($t14) goto L2 else goto L3
    $tmp := $t14;
    if (b#$Boolean($tmp)) { goto L2; } else { goto L3; }

    // L3:
L3:

    // goto L4
    goto L4;

    // L2:
L2:

    // $t15 := LibraTimestamp::now_microseconds()
    call $t15 := $LibraTimestamp_now_microseconds();
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 3396);
      goto Abort;
    }
    assume $IsValidU64($t15);


    // $t16 := 0
    $tmp := $Integer(0);
    $t16 := $tmp;

    // $t17 := ==($t15, $t16)
    $tmp := $Boolean($IsEqual($t15, $t16));
    $t17 := $tmp;

    // $t5 := $t17
    call $tmp := $CopyOrMoveValue($t17);
    $t5 := $tmp;
    if (true) { assume $DebugTrackLocal(12, 1825, 5, $tmp); }

    // goto L5
    goto L5;

    // L4:
L4:

    // $t18 := false
    $tmp := $Boolean(false);
    $t18 := $tmp;

    // $t5 := $t18
    call $tmp := $CopyOrMoveValue($t18);
    $t5 := $tmp;
    if (true) { assume $DebugTrackLocal(12, 1825, 5, $tmp); }

    // goto L5
    goto L5;

    // L5:
L5:

    // $t3 := $t5
    call $tmp := $CopyOrMoveValue($t5);
    $t3 := $tmp;
    if (true) { assume $DebugTrackLocal(12, 1805, 3, $tmp); }

    // if ($t3) goto L6 else goto L7
    $tmp := $t3;
    if (b#$Boolean($tmp)) { goto L6; } else { goto L7; }

    // L7:
L7:

    // $t21 := move($t26)
    call $tmp := $CopyOrMoveValue($t26);
    $t21 := $tmp;

    // destroy($t21)

    // $t22 := 2
    $tmp := $Integer(2);
    $t22 := $tmp;

    // abort($t22)
    if (true) { assume $DebugTrackAbort(12, 1805); }
    goto Abort;

    // L6:
L6:

    // $t23 := move($t26)
    call $tmp := $CopyOrMoveValue($t26);
    $t23 := $tmp;

    // $t24 := false
    $tmp := $Boolean(false);
    $t24 := $tmp;

    // $t25 := pack LibraTimestamp::TimeHasStarted($t24)
    call $tmp := $LibraTimestamp_TimeHasStarted_pack(0, 0, 0, $t24);
    $t25 := $tmp;

    // move_to<LibraTimestamp::TimeHasStarted>($t25, $t23)
    call $MoveTo($LibraTimestamp_TimeHasStarted_type_value(), $t25, $t23);
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 1955);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraTimestamp_set_time_has_started(association: $Value) returns ()
free requires is#$Address(association);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($Boolean(!$IsEqual($Signer_spec_address_of($m, $txn, association), $CoreAddresses_SPEC_LIBRA_ROOT_ADDRESS())))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn))))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean(!b#$Boolean($LibraTimestamp_root_ctm_initialized($m, $txn))))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean(!$IsEqual($LibraTimestamp_spec_now_microseconds($m, $txn), $Integer(0))))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(!$IsEqual($Signer_spec_address_of($m, $txn, association), $CoreAddresses_SPEC_LIBRA_ROOT_ADDRESS())))))
    || b#$Boolean(old(($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn))))))
    || b#$Boolean(old(($Boolean(!b#$Boolean($LibraTimestamp_root_ctm_initialized($m, $txn))))))
    || b#$Boolean(old(($Boolean(!$IsEqual($LibraTimestamp_spec_now_microseconds($m, $txn), $Integer(0)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn))))) ==> b#$Boolean($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> b#$Boolean($LibraTimestamp_root_ctm_initialized($m, $txn)))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> b#$Boolean($Boolean(i#$Integer(old($LibraTimestamp_spec_now_microseconds($m, $txn))) <= i#$Integer($LibraTimestamp_spec_now_microseconds($m, $txn)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn)))));
{
    call $LibraTimestamp_set_time_has_started_def(association);
}

procedure {:inline 1} $LibraTimestamp_update_global_time_def(account: $Value, proposer: $Value, timestamp: $Value) returns (){
    // declare local variables
    var global_timer: $Reference; // ReferenceType($LibraTimestamp_CurrentTimeMicroseconds_type_value())
    var $t4: $Value; // $BooleanType()
    var $t5: $Value; // $IntegerType()
    var $t6: $Value; // $BooleanType()
    var $t7: $Value; // $IntegerType()
    var $t8: $Value; // $BooleanType()
    var $t9: $Value; // $IntegerType()
    var $t10: $Value; // $AddressType()
    var $t11: $Value; // $AddressType()
    var $t12: $Value; // $AddressType()
    var $t13: $Value; // $BooleanType()
    var $t14: $Value; // $BooleanType()
    var $t15: $Value; // $IntegerType()
    var $t16: $Value; // $AddressType()
    var $t17: $Reference; // ReferenceType($LibraTimestamp_CurrentTimeMicroseconds_type_value())
    var $t18: $Value; // $AddressType()
    var $t19: $Value; // $AddressType()
    var $t20: $Value; // $BooleanType()
    var $t21: $Value; // $IntegerType()
    var $t22: $Reference; // ReferenceType($LibraTimestamp_CurrentTimeMicroseconds_type_value())
    var $t23: $Value; // $IntegerType()
    var $t24: $Value; // $IntegerType()
    var $t25: $Value; // $BooleanType()
    var $t26: $Value; // $BooleanType()
    var $t27: $Reference; // ReferenceType($LibraTimestamp_CurrentTimeMicroseconds_type_value())
    var $t28: $Value; // $IntegerType()
    var $t29: $Reference; // ReferenceType($LibraTimestamp_CurrentTimeMicroseconds_type_value())
    var $t30: $Value; // $IntegerType()
    var $t31: $Value; // $IntegerType()
    var $t32: $Value; // $IntegerType()
    var $t33: $Value; // $BooleanType()
    var $t34: $Value; // $BooleanType()
    var $t35: $Reference; // ReferenceType($LibraTimestamp_CurrentTimeMicroseconds_type_value())
    var $t36: $Value; // $IntegerType()
    var $t37: $Value; // $IntegerType()
    var $t38: $Reference; // ReferenceType($LibraTimestamp_CurrentTimeMicroseconds_type_value())
    var $t39: $Reference; // ReferenceType($IntegerType())
    var $t40: $Value; // $AddressType()
    var $t41: $Value; // $AddressType()
    var $t42: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(12, 2514, 0, account); }
    if (true) { assume $DebugTrackLocal(12, 2514, 1, proposer); }
    if (true) { assume $DebugTrackLocal(12, 2514, 2, timestamp); }

    // bytecode translation starts here
    // $t40 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t40 := $tmp;

    // $t41 := move(proposer)
    call $tmp := $CopyOrMoveValue(proposer);
    $t41 := $tmp;

    // $t42 := move(timestamp)
    call $tmp := $CopyOrMoveValue(timestamp);
    $t42 := $tmp;

    // $t10 := move($t40)
    call $tmp := $CopyOrMoveValue($t40);
    $t10 := $tmp;

    // $t11 := Signer::address_of($t10)
    call $t11 := $Signer_address_of($t10);
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 2738);
      goto Abort;
    }
    assume is#$Address($t11);


    // $t12 := CoreAddresses::VM_RESERVED_ADDRESS()
    call $t12 := $CoreAddresses_VM_RESERVED_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 2776);
      goto Abort;
    }
    assume is#$Address($t12);


    // $t13 := ==($t11, $t12)
    $tmp := $Boolean($IsEqual($t11, $t12));
    $t13 := $tmp;

    // $t4 := $t13
    call $tmp := $CopyOrMoveValue($t13);
    $t4 := $tmp;
    if (true) { assume $DebugTrackLocal(12, 2723, 4, $tmp); }

    // if ($t4) goto L0 else goto L1
    $tmp := $t4;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t15 := 33
    $tmp := $Integer(33);
    $t15 := $tmp;

    // abort($t15)
    if (true) { assume $DebugTrackAbort(12, 2723); }
    goto Abort;

    // L0:
L0:

    // $t16 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t16 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 2890);
      goto Abort;
    }
    assume is#$Address($t16);


    // $t17 := borrow_global<LibraTimestamp::CurrentTimeMicroseconds>($t16)
    call $t17 := $BorrowGlobal($t16, $LibraTimestamp_CurrentTimeMicroseconds_type_value());
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 2832);
      goto Abort;
    }
    assume $LibraTimestamp_CurrentTimeMicroseconds_is_well_formed($Dereference($t17));

    // UnpackRef($t17)

    // global_timer := $t17
    call global_timer := $CopyOrMoveRef($t17);
    if (true) { assume $DebugTrackLocal(12, 2817, 3, $Dereference(global_timer)); }

    // $t19 := CoreAddresses::VM_RESERVED_ADDRESS()
    call $t19 := $CoreAddresses_VM_RESERVED_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(12, 2952);
      goto Abort;
    }
    assume is#$Address($t19);


    // $t20 := ==($t41, $t19)
    $tmp := $Boolean($IsEqual($t41, $t19));
    $t20 := $tmp;

    // if ($t20) goto L2 else goto L3
    $tmp := $t20;
    if (b#$Boolean($tmp)) { goto L2; } else { goto L3; }

    // L3:
L3:

    // goto L4
    goto L4;

    // L2:
L2:

    // $t22 := copy(global_timer)
    call $t22 := $CopyOrMoveRef(global_timer);

    // $t23 := get_field<LibraTimestamp::CurrentTimeMicroseconds>.microseconds($t22)
    call $tmp := $GetFieldFromReference($t22, $LibraTimestamp_CurrentTimeMicroseconds_microseconds);
    assume $IsValidU64($tmp);
    $t23 := $tmp;

    // Reference(global_timer) <- $t22
    call global_timer := $WritebackToReference($t22, global_timer);

    // $t24 := move($t23)
    call $tmp := $CopyOrMoveValue($t23);
    $t24 := $tmp;

    // $t25 := ==($t42, $t24)
    $tmp := $Boolean($IsEqual($t42, $t24));
    $t25 := $tmp;

    // $t6 := $t25
    call $tmp := $CopyOrMoveValue($t25);
    $t6 := $tmp;
    if (true) { assume $DebugTrackLocal(12, 3070, 6, $tmp); }

    // if ($t6) goto L5 else goto L6
    $tmp := $t6;
    if (b#$Boolean($tmp)) { goto L5; } else { goto L6; }

    // L6:
L6:

    // $t27 := move(global_timer)
    call $t27 := $CopyOrMoveRef(global_timer);

    // destroy($t27)

    // LibraTimestamp::CurrentTimeMicroseconds <- $t27
    call $WritebackToGlobal($t27);

    // PackRef($t27)

    // $t28 := 5001
    $tmp := $Integer(5001);
    $t28 := $tmp;

    // abort($t28)
    if (true) { assume $DebugTrackAbort(12, 3070); }
    goto Abort;

    // L5:
L5:

    // goto L7
    goto L7;

    // L4:
L4:

    // $t29 := copy(global_timer)
    call $t29 := $CopyOrMoveRef(global_timer);

    // $t30 := get_field<LibraTimestamp::CurrentTimeMicroseconds>.microseconds($t29)
    call $tmp := $GetFieldFromReference($t29, $LibraTimestamp_CurrentTimeMicroseconds_microseconds);
    assume $IsValidU64($tmp);
    $t30 := $tmp;

    // Reference(global_timer) <- $t29
    call global_timer := $WritebackToReference($t29, global_timer);

    // $t31 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t31 := $tmp;

    // $t33 := <($t31, $t42)
    call $tmp := $Lt($t31, $t42);
    $t33 := $tmp;

    // $t8 := $t33
    call $tmp := $CopyOrMoveValue($t33);
    $t8 := $tmp;
    if (true) { assume $DebugTrackLocal(12, 3200, 8, $tmp); }

    // if ($t8) goto L7 else goto L8
    $tmp := $t8;
    if (b#$Boolean($tmp)) { goto L7; } else { goto L8; }

    // L8:
L8:

    // $t35 := move(global_timer)
    call $t35 := $CopyOrMoveRef(global_timer);

    // destroy($t35)

    // LibraTimestamp::CurrentTimeMicroseconds <- $t35
    call $WritebackToGlobal($t35);

    // PackRef($t35)

    // $t36 := 5001
    $tmp := $Integer(5001);
    $t36 := $tmp;

    // abort($t36)
    if (true) { assume $DebugTrackAbort(12, 3200); }
    goto Abort;

    // L7:
L7:

    // $t38 := move(global_timer)
    call $t38 := $CopyOrMoveRef(global_timer);

    // $t39 := borrow_field<LibraTimestamp::CurrentTimeMicroseconds>.microseconds($t38)
    call $t39 := $BorrowField($t38, $LibraTimestamp_CurrentTimeMicroseconds_microseconds);
    assume $IsValidU64($Dereference($t39));

    // LibraTimestamp::CurrentTimeMicroseconds <- $t38
    call $WritebackToGlobal($t38);

    // UnpackRef($t39)

    // write_ref($t39, $t42)
    call $t39 := $WriteRef($t39, $t42);
    if (true) { assume $DebugTrackLocal(12, 3272, 3, $Dereference(global_timer)); }

    // LibraTimestamp::CurrentTimeMicroseconds <- $t39
    call $WritebackToGlobal($t39);

    // Reference($t38) <- $t39
    call $t38 := $WritebackToReference($t39, $t38);

    // PackRef($t38)

    // PackRef($t39)

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraTimestamp_update_global_time(account: $Value, proposer: $Value, timestamp: $Value) returns ()
free requires is#$Address(account);
free requires is#$Address(proposer);
free requires $IsValidU64(timestamp);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($Boolean(!$IsEqual($Signer_spec_address_of($m, $txn, account), $CoreAddresses_SPEC_VM_RESERVED_ADDRESS())))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean(!b#$Boolean($LibraTimestamp_root_ctm_initialized($m, $txn))))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean(b#$Boolean($Boolean($IsEqual(proposer, $CoreAddresses_SPEC_VM_RESERVED_ADDRESS()))) && b#$Boolean($Boolean(!$IsEqual(timestamp, $LibraTimestamp_spec_now_microseconds($m, $txn))))))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean(b#$Boolean($Boolean(!$IsEqual(proposer, $CoreAddresses_SPEC_VM_RESERVED_ADDRESS()))) && b#$Boolean($Boolean(!b#$Boolean($Boolean(i#$Integer(timestamp) > i#$Integer($LibraTimestamp_spec_now_microseconds($m, $txn))))))))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(!$IsEqual($Signer_spec_address_of($m, $txn, account), $CoreAddresses_SPEC_VM_RESERVED_ADDRESS())))))
    || b#$Boolean(old(($Boolean(!b#$Boolean($LibraTimestamp_root_ctm_initialized($m, $txn))))))
    || b#$Boolean(old(($Boolean(b#$Boolean($Boolean($IsEqual(proposer, $CoreAddresses_SPEC_VM_RESERVED_ADDRESS()))) && b#$Boolean($Boolean(!$IsEqual(timestamp, $LibraTimestamp_spec_now_microseconds($m, $txn))))))))
    || b#$Boolean(old(($Boolean(b#$Boolean($Boolean(!$IsEqual(proposer, $CoreAddresses_SPEC_VM_RESERVED_ADDRESS()))) && b#$Boolean($Boolean(!b#$Boolean($Boolean(i#$Integer(timestamp) > i#$Integer($LibraTimestamp_spec_now_microseconds($m, $txn)))))))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn))))) ==> b#$Boolean($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> b#$Boolean($LibraTimestamp_root_ctm_initialized($m, $txn)))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($LibraTimestamp_root_ctm_initialized($m, $txn))) ==> b#$Boolean($Boolean(i#$Integer(old($LibraTimestamp_spec_now_microseconds($m, $txn))) <= i#$Integer($LibraTimestamp_spec_now_microseconds($m, $txn)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($LibraTimestamp_spec_now_microseconds($m, $txn), timestamp))));
{
    call $LibraTimestamp_update_global_time_def(account, proposer, timestamp);
}



// ** spec vars of module Roles



// ** spec funs of module Roles

function {:inline} $Roles_spec_get_role_id($m: $Memory, $txn: $Transaction, account: $Value): $Value {
    (var addr := $Signer_spec_address_of($m, $txn, account); $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))
}

function {:inline} $Roles_spec_has_role_id($m: $Memory, $txn: $Transaction, account: $Value, role_id: $Value): $Value {
    (var addr := $Signer_spec_address_of($m, $txn, account); $Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id), role_id)))))
}

function {:inline} $Roles_SPEC_LIBRA_ROOT_ROLE_ID(): $Value {
    $Integer(0)
}

function {:inline} $Roles_SPEC_TREASURY_COMPLIANCE_ROLE_ID(): $Value {
    $Integer(1)
}

function {:inline} $Roles_SPEC_DESIGNATED_DEALER_ROLE_ID(): $Value {
    $Integer(2)
}

function {:inline} $Roles_SPEC_VALIDATOR_ROLE_ID(): $Value {
    $Integer(3)
}

function {:inline} $Roles_SPEC_VALIDATOR_OPERATOR_ROLE_ID(): $Value {
    $Integer(4)
}

function {:inline} $Roles_SPEC_PARENT_VASP_ROLE_ID(): $Value {
    $Integer(5)
}

function {:inline} $Roles_SPEC_CHILD_VASP_ROLE_ID(): $Value {
    $Integer(6)
}

function {:inline} $Roles_SPEC_UNHOSTED_ROLE_ID(): $Value {
    $Integer(7)
}

function {:inline} $Roles_spec_has_libra_root_role($m: $Memory, $txn: $Transaction, account: $Value): $Value {
    $Roles_spec_has_role_id($m, $txn, account, $Roles_SPEC_LIBRA_ROOT_ROLE_ID())
}

function {:inline} $Roles_spec_has_treasury_compliance_role($m: $Memory, $txn: $Transaction, account: $Value): $Value {
    $Roles_spec_has_role_id($m, $txn, account, $Roles_SPEC_TREASURY_COMPLIANCE_ROLE_ID())
}

function {:inline} $Roles_spec_has_designated_dealer_role($m: $Memory, $txn: $Transaction, account: $Value): $Value {
    $Roles_spec_has_role_id($m, $txn, account, $Roles_SPEC_DESIGNATED_DEALER_ROLE_ID())
}

function {:inline} $Roles_spec_has_validator_role($m: $Memory, $txn: $Transaction, account: $Value): $Value {
    $Roles_spec_has_role_id($m, $txn, account, $Roles_SPEC_VALIDATOR_ROLE_ID())
}

function {:inline} $Roles_spec_has_validator_operator_role($m: $Memory, $txn: $Transaction, account: $Value): $Value {
    $Roles_spec_has_role_id($m, $txn, account, $Roles_SPEC_VALIDATOR_OPERATOR_ROLE_ID())
}

function {:inline} $Roles_spec_has_parent_VASP_role($m: $Memory, $txn: $Transaction, account: $Value): $Value {
    $Roles_spec_has_role_id($m, $txn, account, $Roles_SPEC_PARENT_VASP_ROLE_ID())
}

function {:inline} $Roles_spec_has_child_VASP_role($m: $Memory, $txn: $Transaction, account: $Value): $Value {
    $Roles_spec_has_role_id($m, $txn, account, $Roles_SPEC_CHILD_VASP_ROLE_ID())
}

function {:inline} $Roles_spec_has_unhosted_role($m: $Memory, $txn: $Transaction, account: $Value): $Value {
    $Roles_spec_has_role_id($m, $txn, account, $Roles_SPEC_UNHOSTED_ROLE_ID())
}

function {:inline} $Roles_spec_has_register_new_currency_privilege($m: $Memory, $txn: $Transaction, account: $Value): $Value {
    $Roles_spec_has_treasury_compliance_role($m, $txn, account)
}

function {:inline} $Roles_spec_has_update_dual_attestation_threshold_privilege($m: $Memory, $txn: $Transaction, account: $Value): $Value {
    $Roles_spec_has_treasury_compliance_role($m, $txn, account)
}

function {:inline} $Roles_spec_has_on_chain_config_privilege($m: $Memory, $txn: $Transaction, account: $Value): $Value {
    $Roles_spec_has_treasury_compliance_role($m, $txn, account)
}



// ** structs of module Roles

const unique $Roles_Privilege: $TypeName;
const $Roles_Privilege_witness: $FieldName;
axiom $Roles_Privilege_witness == 0;
const $Roles_Privilege_is_extracted: $FieldName;
axiom $Roles_Privilege_is_extracted == 1;
function $Roles_Privilege_type_value($tv0: $TypeValue): $TypeValue {
    $StructType($Roles_Privilege, $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $tv0], 1), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $tv0][1 := $BooleanType()], 2))
}
function {:inline} $Roles_Privilege_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 2
      && is#$Boolean($SelectField($this, $Roles_Privilege_is_extracted))
}
function {:inline} $Roles_Privilege_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 2
      && is#$Boolean($SelectField($this, $Roles_Privilege_is_extracted))
}

axiom (forall m: $Memory, a: $Value, $tv0: $TypeValue :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $Roles_Privilege_is_well_formed($ResourceValue(m, $Roles_Privilege_type_value($tv0), a))
);

procedure {:inline 1} $Roles_Privilege_pack($file_id: int, $byte_index: int, $var_idx: int, $tv0: $TypeValue, witness: $Value, is_extracted: $Value) returns ($struct: $Value)
{
    assume is#$Boolean(is_extracted);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := witness][1 := is_extracted], 2));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $Roles_Privilege_unpack($tv0: $TypeValue, $struct: $Value) returns (witness: $Value, is_extracted: $Value)
{
    assume is#$Vector($struct);
    witness := $SelectField($struct, $Roles_Privilege_witness);
    is_extracted := $SelectField($struct, $Roles_Privilege_is_extracted);
    assume is#$Boolean(is_extracted);
}

const unique $Roles_RoleId: $TypeName;
const $Roles_RoleId_role_id: $FieldName;
axiom $Roles_RoleId_role_id == 0;
function $Roles_RoleId_type_value(): $TypeValue {
    $StructType($Roles_RoleId, $TypeValueArray($MapConstTypeValue($DefaultTypeValue()), 0), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $IntegerType()], 1))
}
function {:inline} $Roles_RoleId_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $IsValidU64($SelectField($this, $Roles_RoleId_role_id))
}
function {:inline} $Roles_RoleId_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $IsValidU64($SelectField($this, $Roles_RoleId_role_id))
}

axiom (forall m: $Memory, a: $Value :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $Roles_RoleId_is_well_formed($ResourceValue(m, $Roles_RoleId_type_value(), a))
);

procedure {:inline 1} $Roles_RoleId_pack($file_id: int, $byte_index: int, $var_idx: int, role_id: $Value) returns ($struct: $Value)
{
    assume $IsValidU64(role_id);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := role_id], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $Roles_RoleId_unpack($struct: $Value) returns (role_id: $Value)
{
    assume is#$Vector($struct);
    role_id := $SelectField($struct, $Roles_RoleId_role_id);
    assume $IsValidU64(role_id);
}



// ** functions of module Roles

procedure {:inline 1} $Roles_CHILD_VASP_ROLE_ID_def() returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := 6
    $tmp := $Integer(6);
    $t0 := $tmp;

    // return $t0
    $ret0 := $t0;
    if (true) { assume $DebugTrackLocal(15, 1193, 1, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_CHILD_VASP_ROLE_ID() returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_CHILD_VASP_ROLE_ID_def();
}

procedure {:inline 1} $Roles_DESIGNATED_DEALER_ROLE_ID_def() returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := 2
    $tmp := $Integer(2);
    $t0 := $tmp;

    // return $t0
    $ret0 := $t0;
    if (true) { assume $DebugTrackLocal(15, 1025, 1, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_DESIGNATED_DEALER_ROLE_ID() returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_DESIGNATED_DEALER_ROLE_ID_def();
}

procedure {:inline 1} $Roles_LIBRA_ROOT_ROLE_ID_def() returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := 0
    $tmp := $Integer(0);
    $t0 := $tmp;

    // return $t0
    $ret0 := $t0;
    if (true) { assume $DebugTrackLocal(15, 929, 1, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_LIBRA_ROOT_ROLE_ID() returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_LIBRA_ROOT_ROLE_ID_def();
}

procedure {:inline 1} $Roles_PARENT_VASP_ROLE_ID_def() returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := 5
    $tmp := $Integer(5);
    $t0 := $tmp;

    // return $t0
    $ret0 := $t0;
    if (true) { assume $DebugTrackLocal(15, 1153, 1, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_PARENT_VASP_ROLE_ID() returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_PARENT_VASP_ROLE_ID_def();
}

procedure {:inline 1} $Roles_TREASURY_COMPLIANCE_ROLE_ID_def() returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := 1
    $tmp := $Integer(1);
    $t0 := $tmp;

    // return $t0
    $ret0 := $t0;
    if (true) { assume $DebugTrackLocal(15, 978, 1, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_TREASURY_COMPLIANCE_ROLE_ID() returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_TREASURY_COMPLIANCE_ROLE_ID_def();
}

procedure {:inline 1} $Roles_UNHOSTED_ROLE_ID_def() returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := 7
    $tmp := $Integer(7);
    $t0 := $tmp;

    // return $t0
    $ret0 := $t0;
    if (true) { assume $DebugTrackLocal(15, 1231, 1, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_UNHOSTED_ROLE_ID() returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_UNHOSTED_ROLE_ID_def();
}

procedure {:inline 1} $Roles_VALIDATOR_OPERATOR_ROLE_ID_def() returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := 4
    $tmp := $Integer(4);
    $t0 := $tmp;

    // return $t0
    $ret0 := $t0;
    if (true) { assume $DebugTrackLocal(15, 1112, 1, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_VALIDATOR_OPERATOR_ROLE_ID() returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_VALIDATOR_OPERATOR_ROLE_ID_def();
}

procedure {:inline 1} $Roles_VALIDATOR_ROLE_ID_def() returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := 3
    $tmp := $Integer(3);
    $t0 := $tmp;

    // return $t0
    $ret0 := $t0;
    if (true) { assume $DebugTrackLocal(15, 1064, 1, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_VALIDATOR_ROLE_ID() returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_VALIDATOR_ROLE_ID_def();
}

procedure {:inline 1} $Roles_add_privilege_to_account_association_root_role_def($tv0: $TypeValue, account: $Value, witness: $Value) returns (){
    // declare local variables
    var account_role: $Value; // $Roles_RoleId_type_value()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $IntegerType()
    var $t5: $Value; // $AddressType()
    var $t6: $Value; // $AddressType()
    var $t7: $Value; // $Roles_RoleId_type_value()
    var $t8: $Value; // $Roles_RoleId_type_value()
    var $t9: $Value; // $IntegerType()
    var $t10: $Value; // $IntegerType()
    var $t11: $Value; // $IntegerType()
    var $t12: $Value; // $BooleanType()
    var $t13: $Value; // $BooleanType()
    var $t14: $Value; // $AddressType()
    var $t15: $Value; // $IntegerType()
    var $t16: $Value; // $AddressType()
    var $t17: $Value; // $tv0
    var $t18: $Value; // $BooleanType()
    var $t19: $Value; // $Roles_Privilege_type_value($tv0)
    var $t20: $Value; // $AddressType()
    var $t21: $Value; // $tv0
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 2385, 0, account); }
    if (true) { assume $DebugTrackLocal(15, 2385, 1, witness); }

    // bytecode translation starts here
    // $t20 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t20 := $tmp;

    // $t21 := move(witness)
    call $tmp := $CopyOrMoveValue(witness);
    $t21 := $tmp;

    // $t5 := copy($t20)
    call $tmp := $CopyOrMoveValue($t20);
    $t5 := $tmp;

    // $t6 := Signer::address_of($t5)
    call $t6 := $Signer_address_of($t5);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 2571);
      goto Abort;
    }
    assume is#$Address($t6);


    // $t7 := get_global<Roles::RoleId>($t6)
    call $tmp := $GetGlobal($t6, $Roles_RoleId_type_value());
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 2541);
      goto Abort;
    }
    assume $Roles_RoleId_is_well_formed($tmp);
    $t7 := $tmp;

    // account_role := $t7
    call $tmp := $CopyOrMoveValue($t7);
    account_role := $tmp;
    if (true) { assume $DebugTrackLocal(15, 2526, 2, $tmp); }

    // $t8 := move(account_role)
    call $tmp := $CopyOrMoveValue(account_role);
    $t8 := $tmp;

    // $t9 := get_field<Roles::RoleId>.role_id($t8)
    call $tmp := $GetFieldFromValue($t8, $Roles_RoleId_role_id);
    assume $IsValidU64($tmp);
    $t9 := $tmp;

    // $t10 := move($t9)
    call $tmp := $CopyOrMoveValue($t9);
    $t10 := $tmp;

    // $t11 := Roles::LIBRA_ROOT_ROLE_ID()
    call $t11 := $Roles_LIBRA_ROOT_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 901);
      goto Abort;
    }
    assume $IsValidU64($t11);


    // $t12 := ==($t10, $t11)
    $tmp := $Boolean($IsEqual($t10, $t11));
    $t12 := $tmp;

    // $t3 := $t12
    call $tmp := $CopyOrMoveValue($t12);
    $t3 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 2601, 3, $tmp); }

    // if ($t3) goto L0 else goto L1
    $tmp := $t3;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t14 := move($t20)
    call $tmp := $CopyOrMoveValue($t20);
    $t14 := $tmp;

    // destroy($t14)

    // $t15 := 0
    $tmp := $Integer(0);
    $t15 := $tmp;

    // abort($t15)
    if (true) { assume $DebugTrackAbort(15, 2601); }
    goto Abort;

    // L0:
L0:

    // $t16 := move($t20)
    call $tmp := $CopyOrMoveValue($t20);
    $t16 := $tmp;

    // $t18 := false
    $tmp := $Boolean(false);
    $t18 := $tmp;

    // $t19 := pack Roles::Privilege<#0>($t21, $t18)
    call $tmp := $Roles_Privilege_pack(0, 0, 0, $tv0, $t21, $t18);
    $t19 := $tmp;

    // move_to<Roles::Privilege<#0>>($t19, $t16)
    call $MoveTo($Roles_Privilege_type_value($tv0), $t19, $t16);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 2666);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $Roles_add_privilege_to_account_association_root_role($tv0: $TypeValue, account: $Value, witness: $Value) returns ()
free requires is#$Address(account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $Roles_add_privilege_to_account_association_root_role_def($tv0, account, witness);
}

procedure {:inline 1} $Roles_grant_root_association_role_def(association: $Value) returns (){
    // declare local variables
    var owner_address: $Value; // $AddressType()
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $IntegerType()
    var $t4: $Value; // $AddressType()
    var $t5: $Value; // $AddressType()
    var $t6: $Value; // $AddressType()
    var $t7: $Value; // $AddressType()
    var $t8: $Value; // $BooleanType()
    var $t9: $Value; // $BooleanType()
    var $t10: $Value; // $AddressType()
    var $t11: $Value; // $IntegerType()
    var $t12: $Value; // $AddressType()
    var $t13: $Value; // $IntegerType()
    var $t14: $Value; // $Roles_RoleId_type_value()
    var $t15: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 3191, 0, association); }

    // bytecode translation starts here
    // $t15 := move(association)
    call $tmp := $CopyOrMoveValue(association);
    $t15 := $tmp;

    // LibraTimestamp::assert_is_genesis()
    call $LibraTimestamp_assert_is_genesis();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 3293);
      goto Abort;
    }

    // $t4 := copy($t15)
    call $tmp := $CopyOrMoveValue($t15);
    $t4 := $tmp;

    // $t5 := Signer::address_of($t4)
    call $t5 := $Signer_address_of($t4);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 3350);
      goto Abort;
    }
    assume is#$Address($t5);


    // owner_address := $t5
    call $tmp := $CopyOrMoveValue($t5);
    owner_address := $tmp;
    if (true) { assume $DebugTrackLocal(15, 3326, 1, $tmp); }

    // $t7 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t7 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 3422);
      goto Abort;
    }
    assume is#$Address($t7);


    // $t8 := ==(owner_address, $t7)
    $tmp := $Boolean($IsEqual(owner_address, $t7));
    $t8 := $tmp;

    // $t2 := $t8
    call $tmp := $CopyOrMoveValue($t8);
    $t2 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 3383, 2, $tmp); }

    // if ($t2) goto L0 else goto L1
    $tmp := $t2;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t10 := move($t15)
    call $tmp := $CopyOrMoveValue($t15);
    $t10 := $tmp;

    // destroy($t10)

    // $t11 := 0
    $tmp := $Integer(0);
    $t11 := $tmp;

    // abort($t11)
    if (true) { assume $DebugTrackAbort(15, 3383); }
    goto Abort;

    // L0:
L0:

    // $t12 := move($t15)
    call $tmp := $CopyOrMoveValue($t15);
    $t12 := $tmp;

    // $t13 := Roles::LIBRA_ROOT_ROLE_ID()
    call $t13 := $Roles_LIBRA_ROOT_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 901);
      goto Abort;
    }
    assume $IsValidU64($t13);


    // $t14 := pack Roles::RoleId($t13)
    call $tmp := $Roles_RoleId_pack(0, 0, 0, $t13);
    $t14 := $tmp;

    // move_to<Roles::RoleId>($t14, $t12)
    call $MoveTo($Roles_RoleId_type_value(), $t14, $t12);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 3514);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $Roles_grant_root_association_role(association: $Value) returns ()
free requires is#$Address(association);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $Roles_grant_root_association_role_def(association);
}

procedure {:inline 1} $Roles_grant_treasury_compliance_role_def(treasury_compliance_account: $Value, lr_account: $Value) returns (){
    // declare local variables
    var owner_address: $Value; // $AddressType()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $IntegerType()
    var $t5: $Value; // $BooleanType()
    var $t6: $Value; // $IntegerType()
    var $t7: $Value; // $AddressType()
    var $t8: $Value; // $BooleanType()
    var $t9: $Value; // $BooleanType()
    var $t10: $Value; // $AddressType()
    var $t11: $Value; // $IntegerType()
    var $t12: $Value; // $AddressType()
    var $t13: $Value; // $AddressType()
    var $t14: $Value; // $AddressType()
    var $t15: $Value; // $AddressType()
    var $t16: $Value; // $BooleanType()
    var $t17: $Value; // $BooleanType()
    var $t18: $Value; // $AddressType()
    var $t19: $Value; // $IntegerType()
    var $t20: $Value; // $AddressType()
    var $t21: $Value; // $IntegerType()
    var $t22: $Value; // $Roles_RoleId_type_value()
    var $t23: $Value; // $AddressType()
    var $t24: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 3758, 0, treasury_compliance_account); }
    if (true) { assume $DebugTrackLocal(15, 3758, 1, lr_account); }

    // bytecode translation starts here
    // $t23 := move(treasury_compliance_account)
    call $tmp := $CopyOrMoveValue(treasury_compliance_account);
    $t23 := $tmp;

    // $t24 := move(lr_account)
    call $tmp := $CopyOrMoveValue(lr_account);
    $t24 := $tmp;

    // LibraTimestamp::assert_is_genesis()
    call $LibraTimestamp_assert_is_genesis();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 3924);
      goto Abort;
    }

    // $t7 := move($t24)
    call $tmp := $CopyOrMoveValue($t24);
    $t7 := $tmp;

    // $t8 := Roles::has_libra_root_role($t7)
    call $t8 := $Roles_has_libra_root_role($t7);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 8974);
      goto Abort;
    }
    assume is#$Boolean($t8);


    // $t3 := $t8
    call $tmp := $CopyOrMoveValue($t8);
    $t3 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 3953, 3, $tmp); }

    // if ($t3) goto L0 else goto L1
    $tmp := $t3;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t10 := move($t23)
    call $tmp := $CopyOrMoveValue($t23);
    $t10 := $tmp;

    // destroy($t10)

    // $t11 := 999
    $tmp := $Integer(999);
    $t11 := $tmp;

    // abort($t11)
    if (true) { assume $DebugTrackAbort(15, 3953); }
    goto Abort;

    // L0:
L0:

    // $t12 := copy($t23)
    call $tmp := $CopyOrMoveValue($t23);
    $t12 := $tmp;

    // $t13 := Signer::address_of($t12)
    call $t13 := $Signer_address_of($t12);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 4035);
      goto Abort;
    }
    assume is#$Address($t13);


    // owner_address := $t13
    call $tmp := $CopyOrMoveValue($t13);
    owner_address := $tmp;
    if (true) { assume $DebugTrackLocal(15, 4011, 2, $tmp); }

    // $t15 := CoreAddresses::TREASURY_COMPLIANCE_ADDRESS()
    call $t15 := $CoreAddresses_TREASURY_COMPLIANCE_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 4123);
      goto Abort;
    }
    assume is#$Address($t15);


    // $t16 := ==(owner_address, $t15)
    $tmp := $Boolean($IsEqual(owner_address, $t15));
    $t16 := $tmp;

    // $t5 := $t16
    call $tmp := $CopyOrMoveValue($t16);
    $t5 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 4084, 5, $tmp); }

    // if ($t5) goto L2 else goto L3
    $tmp := $t5;
    if (b#$Boolean($tmp)) { goto L2; } else { goto L3; }

    // L3:
L3:

    // $t18 := move($t23)
    call $tmp := $CopyOrMoveValue($t23);
    $t18 := $tmp;

    // destroy($t18)

    // $t19 := 0
    $tmp := $Integer(0);
    $t19 := $tmp;

    // abort($t19)
    if (true) { assume $DebugTrackAbort(15, 4084); }
    goto Abort;

    // L2:
L2:

    // $t20 := move($t23)
    call $tmp := $CopyOrMoveValue($t23);
    $t20 := $tmp;

    // $t21 := Roles::TREASURY_COMPLIANCE_ROLE_ID()
    call $t21 := $Roles_TREASURY_COMPLIANCE_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 941);
      goto Abort;
    }
    assume $IsValidU64($t21);


    // $t22 := pack Roles::RoleId($t21)
    call $tmp := $Roles_RoleId_pack(0, 0, 0, $t21);
    $t22 := $tmp;

    // move_to<Roles::RoleId>($t22, $t20)
    call $MoveTo($Roles_RoleId_type_value(), $t22, $t20);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 4230);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $Roles_grant_treasury_compliance_role(treasury_compliance_account: $Value, lr_account: $Value) returns ()
free requires is#$Address(treasury_compliance_account);
free requires is#$Address(lr_account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $Roles_grant_treasury_compliance_role_def(treasury_compliance_account, lr_account);
}

procedure {:inline 1} $Roles_has_child_VASP_role_def(account: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $AddressType()
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 9803, 0, account); }

    // bytecode translation starts here
    // $t4 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t4 := $tmp;

    // $t1 := move($t4)
    call $tmp := $CopyOrMoveValue($t4);
    $t1 := $tmp;

    // $t2 := Roles::CHILD_VASP_ROLE_ID()
    call $t2 := $Roles_CHILD_VASP_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 1165);
      goto Abort;
    }
    assume $IsValidU64($t2);


    // $t3 := Roles::has_role($t1, $t2)
    call $t3 := $Roles_has_role($t1, $t2);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 8751);
      goto Abort;
    }
    assume is#$Boolean($t3);


    // return $t3
    $ret0 := $t3;
    if (true) { assume $DebugTrackLocal(15, 9884, 5, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_has_child_VASP_role(account: $Value) returns ($ret0: $Value)
free requires is#$Address(account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_has_child_VASP_role_def(account);
}

procedure {:inline 1} $Roles_has_designated_dealer_role_def(account: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $AddressType()
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 9245, 0, account); }

    // bytecode translation starts here
    // $t4 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t4 := $tmp;

    // $t1 := move($t4)
    call $tmp := $CopyOrMoveValue($t4);
    $t1 := $tmp;

    // $t2 := Roles::DESIGNATED_DEALER_ROLE_ID()
    call $t2 := $Roles_DESIGNATED_DEALER_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 990);
      goto Abort;
    }
    assume $IsValidU64($t2);


    // $t3 := Roles::has_role($t1, $t2)
    call $t3 := $Roles_has_role($t1, $t2);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 8751);
      goto Abort;
    }
    assume is#$Boolean($t3);


    // return $t3
    $ret0 := $t3;
    if (true) { assume $DebugTrackLocal(15, 9333, 5, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_has_designated_dealer_role(account: $Value) returns ($ret0: $Value)
free requires is#$Address(account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_has_designated_dealer_role_def(account);
}

procedure {:inline 1} $Roles_has_libra_root_role_def(account: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $AddressType()
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 8963, 0, account); }

    // bytecode translation starts here
    // $t4 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t4 := $tmp;

    // $t1 := move($t4)
    call $tmp := $CopyOrMoveValue($t4);
    $t1 := $tmp;

    // $t2 := Roles::LIBRA_ROOT_ROLE_ID()
    call $t2 := $Roles_LIBRA_ROOT_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 901);
      goto Abort;
    }
    assume $IsValidU64($t2);


    // $t3 := Roles::has_role($t1, $t2)
    call $t3 := $Roles_has_role($t1, $t2);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 8751);
      goto Abort;
    }
    assume is#$Boolean($t3);


    // return $t3
    $ret0 := $t3;
    if (true) { assume $DebugTrackLocal(15, 9044, 5, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_has_libra_root_role(account: $Value) returns ($ret0: $Value)
free requires is#$Address(account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_has_libra_root_role_def(account);
}

procedure {:inline 1} $Roles_has_on_chain_config_privilege_def(account: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $AddressType()
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 10369, 0, account); }

    // bytecode translation starts here
    // $t3 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t3 := $tmp;

    // $t1 := move($t3)
    call $tmp := $CopyOrMoveValue($t3);
    $t1 := $tmp;

    // $t2 := Roles::has_libra_root_role($t1)
    call $t2 := $Roles_has_libra_root_role($t1);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 8974);
      goto Abort;
    }
    assume is#$Boolean($t2);


    // return $t2
    $ret0 := $t2;
    if (true) { assume $DebugTrackLocal(15, 10461, 4, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_has_on_chain_config_privilege(account: $Value) returns ($ret0: $Value)
free requires is#$Address(account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_has_on_chain_config_privilege_def(account);
}

procedure {:inline 1} $Roles_has_parent_VASP_role_def(account: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $AddressType()
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 9669, 0, account); }

    // bytecode translation starts here
    // $t4 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t4 := $tmp;

    // $t1 := move($t4)
    call $tmp := $CopyOrMoveValue($t4);
    $t1 := $tmp;

    // $t2 := Roles::PARENT_VASP_ROLE_ID()
    call $t2 := $Roles_PARENT_VASP_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 1124);
      goto Abort;
    }
    assume $IsValidU64($t2);


    // $t3 := Roles::has_role($t1, $t2)
    call $t3 := $Roles_has_role($t1, $t2);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 8751);
      goto Abort;
    }
    assume is#$Boolean($t3);


    // return $t3
    $ret0 := $t3;
    if (true) { assume $DebugTrackLocal(15, 9751, 5, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_has_parent_VASP_role(account: $Value) returns ($ret0: $Value)
free requires is#$Address(account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_has_parent_VASP_role_def(account);
}

procedure {:inline 1} $Roles_has_register_new_currency_privilege_def(account: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $AddressType()
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 10063, 0, account); }

    // bytecode translation starts here
    // $t3 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t3 := $tmp;

    // $t1 := move($t3)
    call $tmp := $CopyOrMoveValue($t3);
    $t1 := $tmp;

    // $t2 := Roles::has_treasury_compliance_role($t1)
    call $t2 := $Roles_has_treasury_compliance_role($t1);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 9106);
      goto Abort;
    }
    assume is#$Boolean($t2);


    // return $t2
    $ret0 := $t2;
    if (true) { assume $DebugTrackLocal(15, 10161, 4, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_has_register_new_currency_privilege(account: $Value) returns ($ret0: $Value)
free requires is#$Address(account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_has_register_new_currency_privilege_def(account);
}

procedure {:inline 1} $Roles_has_role_def(account: $Value, role_id: $Value) returns ($ret0: $Value){
    // declare local variables
    var addr: $Value; // $AddressType()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $AddressType()
    var $t5: $Value; // $AddressType()
    var $t6: $Value; // $AddressType()
    var $t7: $Value; // $BooleanType()
    var $t8: $Value; // $AddressType()
    var $t9: $Value; // $Roles_RoleId_type_value()
    var $t10: $Value; // $IntegerType()
    var $t11: $Value; // $IntegerType()
    var $t12: $Value; // $IntegerType()
    var $t13: $Value; // $BooleanType()
    var $t14: $Value; // $BooleanType()
    var $t15: $Value; // $BooleanType()
    var $t16: $Value; // $AddressType()
    var $t17: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 8740, 0, account); }
    if (true) { assume $DebugTrackLocal(15, 8740, 1, role_id); }

    // bytecode translation starts here
    // $t16 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t16 := $tmp;

    // $t17 := move(role_id)
    call $tmp := $CopyOrMoveValue(role_id);
    $t17 := $tmp;

    // $t4 := move($t16)
    call $tmp := $CopyOrMoveValue($t16);
    $t4 := $tmp;

    // $t5 := Signer::address_of($t4)
    call $t5 := $Signer_address_of($t4);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 8842);
      goto Abort;
    }
    assume is#$Address($t5);


    // addr := $t5
    call $tmp := $CopyOrMoveValue($t5);
    addr := $tmp;
    if (true) { assume $DebugTrackLocal(15, 8827, 2, $tmp); }

    // $t7 := exists<Roles::RoleId>(addr)
    call $tmp := $Exists(addr, $Roles_RoleId_type_value());
    $t7 := $tmp;

    // if ($t7) goto L0 else goto L1
    $tmp := $t7;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // goto L2
    goto L2;

    // L0:
L0:

    // $t9 := get_global<Roles::RoleId>(addr)
    call $tmp := $GetGlobal(addr, $Roles_RoleId_type_value());
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 8905);
      goto Abort;
    }
    assume $Roles_RoleId_is_well_formed($tmp);
    $t9 := $tmp;

    // $t10 := get_field<Roles::RoleId>.role_id($t9)
    call $tmp := $GetFieldFromValue($t9, $Roles_RoleId_role_id);
    assume $IsValidU64($tmp);
    $t10 := $tmp;

    // $t11 := move($t10)
    call $tmp := $CopyOrMoveValue($t10);
    $t11 := $tmp;

    // $t13 := ==($t11, $t17)
    $tmp := $Boolean($IsEqual($t11, $t17));
    $t13 := $tmp;

    // $t3 := $t13
    call $tmp := $CopyOrMoveValue($t13);
    $t3 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 8870, 3, $tmp); }

    // goto L3
    goto L3;

    // L2:
L2:

    // $t14 := false
    $tmp := $Boolean(false);
    $t14 := $tmp;

    // $t3 := $t14
    call $tmp := $CopyOrMoveValue($t14);
    $t3 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 8870, 3, $tmp); }

    // goto L3
    goto L3;

    // L3:
L3:

    // return $t3
    $ret0 := $t3;
    if (true) { assume $DebugTrackLocal(15, 8870, 18, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_has_role(account: $Value, role_id: $Value) returns ($ret0: $Value)
free requires is#$Address(account);
free requires $IsValidU64(role_id);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_has_role_def(account, role_id);
}

procedure {:inline 1} $Roles_has_treasury_compliance_role_def(account: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $AddressType()
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 9095, 0, account); }

    // bytecode translation starts here
    // $t4 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t4 := $tmp;

    // $t1 := move($t4)
    call $tmp := $CopyOrMoveValue($t4);
    $t1 := $tmp;

    // $t2 := Roles::TREASURY_COMPLIANCE_ROLE_ID()
    call $t2 := $Roles_TREASURY_COMPLIANCE_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 941);
      goto Abort;
    }
    assume $IsValidU64($t2);


    // $t3 := Roles::has_role($t1, $t2)
    call $t3 := $Roles_has_role($t1, $t2);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 8751);
      goto Abort;
    }
    assume is#$Boolean($t3);


    // return $t3
    $ret0 := $t3;
    if (true) { assume $DebugTrackLocal(15, 9185, 5, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_has_treasury_compliance_role(account: $Value) returns ($ret0: $Value)
free requires is#$Address(account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_has_treasury_compliance_role_def(account);
}

procedure {:inline 1} $Roles_has_unhosted_role_def(account: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $AddressType()
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 9935, 0, account); }

    // bytecode translation starts here
    // $t4 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t4 := $tmp;

    // $t1 := move($t4)
    call $tmp := $CopyOrMoveValue($t4);
    $t1 := $tmp;

    // $t2 := Roles::UNHOSTED_ROLE_ID()
    call $t2 := $Roles_UNHOSTED_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 1205);
      goto Abort;
    }
    assume $IsValidU64($t2);


    // $t3 := Roles::has_role($t1, $t2)
    call $t3 := $Roles_has_role($t1, $t2);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 8751);
      goto Abort;
    }
    assume is#$Boolean($t3);


    // return $t3
    $ret0 := $t3;
    if (true) { assume $DebugTrackLocal(15, 10014, 5, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_has_unhosted_role(account: $Value) returns ($ret0: $Value)
free requires is#$Address(account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_has_unhosted_role_def(account);
}

procedure {:inline 1} $Roles_has_update_dual_attestation_threshold_privilege_def(account: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $AddressType()
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 10210, 0, account); }

    // bytecode translation starts here
    // $t3 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t3 := $tmp;

    // $t1 := move($t3)
    call $tmp := $CopyOrMoveValue($t3);
    $t1 := $tmp;

    // $t2 := Roles::has_treasury_compliance_role($t1)
    call $t2 := $Roles_has_treasury_compliance_role($t1);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 9106);
      goto Abort;
    }
    assume is#$Boolean($t2);


    // return $t2
    $ret0 := $t2;
    if (true) { assume $DebugTrackLocal(15, 10320, 4, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_has_update_dual_attestation_threshold_privilege(account: $Value) returns ($ret0: $Value)
free requires is#$Address(account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_has_update_dual_attestation_threshold_privilege_def(account);
}

procedure {:inline 1} $Roles_has_validator_operator_role_def(account: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $AddressType()
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 9521, 0, account); }

    // bytecode translation starts here
    // $t4 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t4 := $tmp;

    // $t1 := move($t4)
    call $tmp := $CopyOrMoveValue($t4);
    $t1 := $tmp;

    // $t2 := Roles::VALIDATOR_OPERATOR_ROLE_ID()
    call $t2 := $Roles_VALIDATOR_OPERATOR_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 1076);
      goto Abort;
    }
    assume $IsValidU64($t2);


    // $t3 := Roles::has_role($t1, $t2)
    call $t3 := $Roles_has_role($t1, $t2);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 8751);
      goto Abort;
    }
    assume is#$Boolean($t3);


    // return $t3
    $ret0 := $t3;
    if (true) { assume $DebugTrackLocal(15, 9610, 5, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_has_validator_operator_role(account: $Value) returns ($ret0: $Value)
free requires is#$Address(account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_has_validator_operator_role_def(account);
}

procedure {:inline 1} $Roles_has_validator_role_def(account: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $AddressType()
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 9391, 0, account); }

    // bytecode translation starts here
    // $t4 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t4 := $tmp;

    // $t1 := move($t4)
    call $tmp := $CopyOrMoveValue($t4);
    $t1 := $tmp;

    // $t2 := Roles::VALIDATOR_ROLE_ID()
    call $t2 := $Roles_VALIDATOR_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 1037);
      goto Abort;
    }
    assume $IsValidU64($t2);


    // $t3 := Roles::has_role($t1, $t2)
    call $t3 := $Roles_has_role($t1, $t2);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 8751);
      goto Abort;
    }
    assume is#$Boolean($t3);


    // return $t3
    $ret0 := $t3;
    if (true) { assume $DebugTrackLocal(15, 9471, 5, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Roles_has_validator_role(account: $Value) returns ($ret0: $Value)
free requires is#$Address(account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $ret0 := $Roles_has_validator_role_def(account);
}

procedure {:inline 1} $Roles_new_child_vasp_role_def(creating_account: $Value, new_account: $Value) returns (){
    // declare local variables
    var calling_role: $Value; // $Roles_RoleId_type_value()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $IntegerType()
    var $t5: $Value; // $BooleanType()
    var $t6: $Value; // $IntegerType()
    var $t7: $Value; // $AddressType()
    var $t8: $Value; // $AddressType()
    var $t9: $Value; // $Roles_RoleId_type_value()
    var $t10: $Value; // $AddressType()
    var $t11: $Value; // $AddressType()
    var $t12: $Value; // $BooleanType()
    var $t13: $Value; // $BooleanType()
    var $t14: $Value; // $BooleanType()
    var $t15: $Value; // $AddressType()
    var $t16: $Value; // $Roles_RoleId_type_value()
    var $t17: $Value; // $IntegerType()
    var $t18: $Value; // $Roles_RoleId_type_value()
    var $t19: $Value; // $IntegerType()
    var $t20: $Value; // $IntegerType()
    var $t21: $Value; // $IntegerType()
    var $t22: $Value; // $BooleanType()
    var $t23: $Value; // $BooleanType()
    var $t24: $Value; // $AddressType()
    var $t25: $Value; // $IntegerType()
    var $t26: $Value; // $AddressType()
    var $t27: $Value; // $IntegerType()
    var $t28: $Value; // $Roles_RoleId_type_value()
    var $t29: $Value; // $AddressType()
    var $t30: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 7135, 0, creating_account); }
    if (true) { assume $DebugTrackLocal(15, 7135, 1, new_account); }

    // bytecode translation starts here
    // $t29 := move(creating_account)
    call $tmp := $CopyOrMoveValue(creating_account);
    $t29 := $tmp;

    // $t30 := move(new_account)
    call $tmp := $CopyOrMoveValue(new_account);
    $t30 := $tmp;

    // $t7 := move($t29)
    call $tmp := $CopyOrMoveValue($t29);
    $t7 := $tmp;

    // $t8 := Signer::address_of($t7)
    call $t8 := $Signer_address_of($t7);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 7313);
      goto Abort;
    }
    assume is#$Address($t8);


    // $t9 := get_global<Roles::RoleId>($t8)
    call $tmp := $GetGlobal($t8, $Roles_RoleId_type_value());
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 7283);
      goto Abort;
    }
    assume $Roles_RoleId_is_well_formed($tmp);
    $t9 := $tmp;

    // calling_role := $t9
    call $tmp := $CopyOrMoveValue($t9);
    calling_role := $tmp;
    if (true) { assume $DebugTrackLocal(15, 7268, 2, $tmp); }

    // $t10 := copy($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t10 := $tmp;

    // $t11 := Signer::address_of($t10)
    call $t11 := $Signer_address_of($t10);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 7456);
      goto Abort;
    }
    assume is#$Address($t11);


    // $t12 := exists<Roles::RoleId>($t11)
    call $tmp := $Exists($t11, $Roles_RoleId_type_value());
    $t12 := $tmp;

    // $t13 := !($t12)
    call $tmp := $Not($t12);
    $t13 := $tmp;

    // $t3 := $t13
    call $tmp := $CopyOrMoveValue($t13);
    $t3 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 7425, 3, $tmp); }

    // if ($t3) goto L0 else goto L1
    $tmp := $t3;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t15 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t15 := $tmp;

    // destroy($t15)

    // $t16 := move(calling_role)
    call $tmp := $CopyOrMoveValue(calling_role);
    $t16 := $tmp;

    // destroy($t16)

    // $t17 := 1
    $tmp := $Integer(1);
    $t17 := $tmp;

    // abort($t17)
    if (true) { assume $DebugTrackAbort(15, 7425); }
    goto Abort;

    // L0:
L0:

    // $t18 := move(calling_role)
    call $tmp := $CopyOrMoveValue(calling_role);
    $t18 := $tmp;

    // $t19 := get_field<Roles::RoleId>.role_id($t18)
    call $tmp := $GetFieldFromValue($t18, $Roles_RoleId_role_id);
    assume $IsValidU64($tmp);
    $t19 := $tmp;

    // $t20 := move($t19)
    call $tmp := $CopyOrMoveValue($t19);
    $t20 := $tmp;

    // $t21 := Roles::PARENT_VASP_ROLE_ID()
    call $t21 := $Roles_PARENT_VASP_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 1124);
      goto Abort;
    }
    assume $IsValidU64($t21);


    // $t22 := ==($t20, $t21)
    $tmp := $Boolean($IsEqual($t20, $t21));
    $t22 := $tmp;

    // $t5 := $t22
    call $tmp := $CopyOrMoveValue($t22);
    $t5 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 7494, 5, $tmp); }

    // if ($t5) goto L2 else goto L3
    $tmp := $t5;
    if (b#$Boolean($tmp)) { goto L2; } else { goto L3; }

    // L3:
L3:

    // $t24 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t24 := $tmp;

    // destroy($t24)

    // $t25 := 0
    $tmp := $Integer(0);
    $t25 := $tmp;

    // abort($t25)
    if (true) { assume $DebugTrackAbort(15, 7494); }
    goto Abort;

    // L2:
L2:

    // $t26 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t26 := $tmp;

    // $t27 := Roles::CHILD_VASP_ROLE_ID()
    call $t27 := $Roles_CHILD_VASP_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 1165);
      goto Abort;
    }
    assume $IsValidU64($t27);


    // $t28 := pack Roles::RoleId($t27)
    call $tmp := $Roles_RoleId_pack(0, 0, 0, $t27);
    $t28 := $tmp;

    // move_to<Roles::RoleId>($t28, $t26)
    call $MoveTo($Roles_RoleId_type_value(), $t28, $t26);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 7560);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $Roles_new_child_vasp_role(creating_account: $Value, new_account: $Value) returns ()
free requires is#$Address(creating_account);
free requires is#$Address(new_account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $Roles_new_child_vasp_role_def(creating_account, new_account);
}

procedure {:inline 1} $Roles_new_designated_dealer_role_def(creating_account: $Value, new_account: $Value) returns (){
    // declare local variables
    var calling_role: $Value; // $Roles_RoleId_type_value()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $IntegerType()
    var $t5: $Value; // $BooleanType()
    var $t6: $Value; // $IntegerType()
    var $t7: $Value; // $AddressType()
    var $t8: $Value; // $AddressType()
    var $t9: $Value; // $Roles_RoleId_type_value()
    var $t10: $Value; // $AddressType()
    var $t11: $Value; // $AddressType()
    var $t12: $Value; // $BooleanType()
    var $t13: $Value; // $BooleanType()
    var $t14: $Value; // $BooleanType()
    var $t15: $Value; // $AddressType()
    var $t16: $Value; // $Roles_RoleId_type_value()
    var $t17: $Value; // $IntegerType()
    var $t18: $Value; // $Roles_RoleId_type_value()
    var $t19: $Value; // $IntegerType()
    var $t20: $Value; // $IntegerType()
    var $t21: $Value; // $IntegerType()
    var $t22: $Value; // $BooleanType()
    var $t23: $Value; // $BooleanType()
    var $t24: $Value; // $AddressType()
    var $t25: $Value; // $IntegerType()
    var $t26: $Value; // $AddressType()
    var $t27: $Value; // $IntegerType()
    var $t28: $Value; // $Roles_RoleId_type_value()
    var $t29: $Value; // $AddressType()
    var $t30: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 4652, 0, creating_account); }
    if (true) { assume $DebugTrackLocal(15, 4652, 1, new_account); }

    // bytecode translation starts here
    // $t29 := move(creating_account)
    call $tmp := $CopyOrMoveValue(creating_account);
    $t29 := $tmp;

    // $t30 := move(new_account)
    call $tmp := $CopyOrMoveValue(new_account);
    $t30 := $tmp;

    // $t7 := move($t29)
    call $tmp := $CopyOrMoveValue($t29);
    $t7 := $tmp;

    // $t8 := Signer::address_of($t7)
    call $t8 := $Signer_address_of($t7);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 4837);
      goto Abort;
    }
    assume is#$Address($t8);


    // $t9 := get_global<Roles::RoleId>($t8)
    call $tmp := $GetGlobal($t8, $Roles_RoleId_type_value());
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 4807);
      goto Abort;
    }
    assume $Roles_RoleId_is_well_formed($tmp);
    $t9 := $tmp;

    // calling_role := $t9
    call $tmp := $CopyOrMoveValue($t9);
    calling_role := $tmp;
    if (true) { assume $DebugTrackLocal(15, 4792, 2, $tmp); }

    // $t10 := copy($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t10 := $tmp;

    // $t11 := Signer::address_of($t10)
    call $t11 := $Signer_address_of($t10);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 4980);
      goto Abort;
    }
    assume is#$Address($t11);


    // $t12 := exists<Roles::RoleId>($t11)
    call $tmp := $Exists($t11, $Roles_RoleId_type_value());
    $t12 := $tmp;

    // $t13 := !($t12)
    call $tmp := $Not($t12);
    $t13 := $tmp;

    // $t3 := $t13
    call $tmp := $CopyOrMoveValue($t13);
    $t3 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 4949, 3, $tmp); }

    // if ($t3) goto L0 else goto L1
    $tmp := $t3;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t15 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t15 := $tmp;

    // destroy($t15)

    // $t16 := move(calling_role)
    call $tmp := $CopyOrMoveValue(calling_role);
    $t16 := $tmp;

    // destroy($t16)

    // $t17 := 1
    $tmp := $Integer(1);
    $t17 := $tmp;

    // abort($t17)
    if (true) { assume $DebugTrackAbort(15, 4949); }
    goto Abort;

    // L0:
L0:

    // $t18 := move(calling_role)
    call $tmp := $CopyOrMoveValue(calling_role);
    $t18 := $tmp;

    // $t19 := get_field<Roles::RoleId>.role_id($t18)
    call $tmp := $GetFieldFromValue($t18, $Roles_RoleId_role_id);
    assume $IsValidU64($tmp);
    $t19 := $tmp;

    // $t20 := move($t19)
    call $tmp := $CopyOrMoveValue($t19);
    $t20 := $tmp;

    // $t21 := Roles::TREASURY_COMPLIANCE_ROLE_ID()
    call $t21 := $Roles_TREASURY_COMPLIANCE_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 941);
      goto Abort;
    }
    assume $IsValidU64($t21);


    // $t22 := ==($t20, $t21)
    $tmp := $Boolean($IsEqual($t20, $t21));
    $t22 := $tmp;

    // $t5 := $t22
    call $tmp := $CopyOrMoveValue($t22);
    $t5 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 5018, 5, $tmp); }

    // if ($t5) goto L2 else goto L3
    $tmp := $t5;
    if (b#$Boolean($tmp)) { goto L2; } else { goto L3; }

    // L3:
L3:

    // $t24 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t24 := $tmp;

    // destroy($t24)

    // $t25 := 0
    $tmp := $Integer(0);
    $t25 := $tmp;

    // abort($t25)
    if (true) { assume $DebugTrackAbort(15, 5018); }
    goto Abort;

    // L2:
L2:

    // $t26 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t26 := $tmp;

    // $t27 := Roles::DESIGNATED_DEALER_ROLE_ID()
    call $t27 := $Roles_DESIGNATED_DEALER_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 990);
      goto Abort;
    }
    assume $IsValidU64($t27);


    // $t28 := pack Roles::RoleId($t27)
    call $tmp := $Roles_RoleId_pack(0, 0, 0, $t27);
    $t28 := $tmp;

    // move_to<Roles::RoleId>($t28, $t26)
    call $MoveTo($Roles_RoleId_type_value(), $t28, $t26);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 5092);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $Roles_new_designated_dealer_role(creating_account: $Value, new_account: $Value) returns ()
free requires is#$Address(creating_account);
free requires is#$Address(new_account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $Roles_new_designated_dealer_role_def(creating_account, new_account);
}

procedure {:inline 1} $Roles_new_parent_vasp_role_def(creating_account: $Value, new_account: $Value) returns (){
    // declare local variables
    var calling_role: $Value; // $Roles_RoleId_type_value()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $IntegerType()
    var $t5: $Value; // $BooleanType()
    var $t6: $Value; // $IntegerType()
    var $t7: $Value; // $AddressType()
    var $t8: $Value; // $AddressType()
    var $t9: $Value; // $Roles_RoleId_type_value()
    var $t10: $Value; // $AddressType()
    var $t11: $Value; // $AddressType()
    var $t12: $Value; // $BooleanType()
    var $t13: $Value; // $BooleanType()
    var $t14: $Value; // $BooleanType()
    var $t15: $Value; // $AddressType()
    var $t16: $Value; // $Roles_RoleId_type_value()
    var $t17: $Value; // $IntegerType()
    var $t18: $Value; // $Roles_RoleId_type_value()
    var $t19: $Value; // $IntegerType()
    var $t20: $Value; // $IntegerType()
    var $t21: $Value; // $IntegerType()
    var $t22: $Value; // $BooleanType()
    var $t23: $Value; // $BooleanType()
    var $t24: $Value; // $AddressType()
    var $t25: $Value; // $IntegerType()
    var $t26: $Value; // $AddressType()
    var $t27: $Value; // $IntegerType()
    var $t28: $Value; // $Roles_RoleId_type_value()
    var $t29: $Value; // $AddressType()
    var $t30: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 6524, 0, creating_account); }
    if (true) { assume $DebugTrackLocal(15, 6524, 1, new_account); }

    // bytecode translation starts here
    // $t29 := move(creating_account)
    call $tmp := $CopyOrMoveValue(creating_account);
    $t29 := $tmp;

    // $t30 := move(new_account)
    call $tmp := $CopyOrMoveValue(new_account);
    $t30 := $tmp;

    // $t7 := move($t29)
    call $tmp := $CopyOrMoveValue($t29);
    $t7 := $tmp;

    // $t8 := Signer::address_of($t7)
    call $t8 := $Signer_address_of($t7);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 6703);
      goto Abort;
    }
    assume is#$Address($t8);


    // $t9 := get_global<Roles::RoleId>($t8)
    call $tmp := $GetGlobal($t8, $Roles_RoleId_type_value());
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 6673);
      goto Abort;
    }
    assume $Roles_RoleId_is_well_formed($tmp);
    $t9 := $tmp;

    // calling_role := $t9
    call $tmp := $CopyOrMoveValue($t9);
    calling_role := $tmp;
    if (true) { assume $DebugTrackLocal(15, 6658, 2, $tmp); }

    // $t10 := copy($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t10 := $tmp;

    // $t11 := Signer::address_of($t10)
    call $t11 := $Signer_address_of($t10);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 6846);
      goto Abort;
    }
    assume is#$Address($t11);


    // $t12 := exists<Roles::RoleId>($t11)
    call $tmp := $Exists($t11, $Roles_RoleId_type_value());
    $t12 := $tmp;

    // $t13 := !($t12)
    call $tmp := $Not($t12);
    $t13 := $tmp;

    // $t3 := $t13
    call $tmp := $CopyOrMoveValue($t13);
    $t3 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 6815, 3, $tmp); }

    // if ($t3) goto L0 else goto L1
    $tmp := $t3;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t15 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t15 := $tmp;

    // destroy($t15)

    // $t16 := move(calling_role)
    call $tmp := $CopyOrMoveValue(calling_role);
    $t16 := $tmp;

    // destroy($t16)

    // $t17 := 1
    $tmp := $Integer(1);
    $t17 := $tmp;

    // abort($t17)
    if (true) { assume $DebugTrackAbort(15, 6815); }
    goto Abort;

    // L0:
L0:

    // $t18 := move(calling_role)
    call $tmp := $CopyOrMoveValue(calling_role);
    $t18 := $tmp;

    // $t19 := get_field<Roles::RoleId>.role_id($t18)
    call $tmp := $GetFieldFromValue($t18, $Roles_RoleId_role_id);
    assume $IsValidU64($tmp);
    $t19 := $tmp;

    // $t20 := move($t19)
    call $tmp := $CopyOrMoveValue($t19);
    $t20 := $tmp;

    // $t21 := Roles::LIBRA_ROOT_ROLE_ID()
    call $t21 := $Roles_LIBRA_ROOT_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 901);
      goto Abort;
    }
    assume $IsValidU64($t21);


    // $t22 := ==($t20, $t21)
    $tmp := $Boolean($IsEqual($t20, $t21));
    $t22 := $tmp;

    // $t5 := $t22
    call $tmp := $CopyOrMoveValue($t22);
    $t5 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 6884, 5, $tmp); }

    // if ($t5) goto L2 else goto L3
    $tmp := $t5;
    if (b#$Boolean($tmp)) { goto L2; } else { goto L3; }

    // L3:
L3:

    // $t24 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t24 := $tmp;

    // destroy($t24)

    // $t25 := 0
    $tmp := $Integer(0);
    $t25 := $tmp;

    // abort($t25)
    if (true) { assume $DebugTrackAbort(15, 6884); }
    goto Abort;

    // L2:
L2:

    // $t26 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t26 := $tmp;

    // $t27 := Roles::PARENT_VASP_ROLE_ID()
    call $t27 := $Roles_PARENT_VASP_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 1124);
      goto Abort;
    }
    assume $IsValidU64($t27);


    // $t28 := pack Roles::RoleId($t27)
    call $tmp := $Roles_RoleId_pack(0, 0, 0, $t27);
    $t28 := $tmp;

    // move_to<Roles::RoleId>($t28, $t26)
    call $MoveTo($Roles_RoleId_type_value(), $t28, $t26);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 6949);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $Roles_new_parent_vasp_role(creating_account: $Value, new_account: $Value) returns ()
free requires is#$Address(creating_account);
free requires is#$Address(new_account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $Roles_new_parent_vasp_role_def(creating_account, new_account);
}

procedure {:inline 1} $Roles_new_unhosted_role_def(_creating_account: $Value, new_account: $Value) returns (){
    // declare local variables
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $IntegerType()
    var $t4: $Value; // $AddressType()
    var $t5: $Value; // $AddressType()
    var $t6: $Value; // $BooleanType()
    var $t7: $Value; // $BooleanType()
    var $t8: $Value; // $BooleanType()
    var $t9: $Value; // $AddressType()
    var $t10: $Value; // $IntegerType()
    var $t11: $Value; // $AddressType()
    var $t12: $Value; // $IntegerType()
    var $t13: $Value; // $Roles_RoleId_type_value()
    var $t14: $Value; // $AddressType()
    var $t15: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 7789, 0, _creating_account); }
    if (true) { assume $DebugTrackLocal(15, 7789, 1, new_account); }

    // bytecode translation starts here
    // $t14 := move(_creating_account)
    call $tmp := $CopyOrMoveValue(_creating_account);
    $t14 := $tmp;

    // $t15 := move(new_account)
    call $tmp := $CopyOrMoveValue(new_account);
    $t15 := $tmp;

    // $t4 := copy($t15)
    call $tmp := $CopyOrMoveValue($t15);
    $t4 := $tmp;

    // $t5 := Signer::address_of($t4)
    call $t5 := $Signer_address_of($t4);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 7982);
      goto Abort;
    }
    assume is#$Address($t5);


    // $t6 := exists<Roles::RoleId>($t5)
    call $tmp := $Exists($t5, $Roles_RoleId_type_value());
    $t6 := $tmp;

    // $t7 := !($t6)
    call $tmp := $Not($t6);
    $t7 := $tmp;

    // $t2 := $t7
    call $tmp := $CopyOrMoveValue($t7);
    $t2 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 7951, 2, $tmp); }

    // if ($t2) goto L0 else goto L1
    $tmp := $t2;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t9 := move($t15)
    call $tmp := $CopyOrMoveValue($t15);
    $t9 := $tmp;

    // destroy($t9)

    // $t10 := 1
    $tmp := $Integer(1);
    $t10 := $tmp;

    // abort($t10)
    if (true) { assume $DebugTrackAbort(15, 7951); }
    goto Abort;

    // L0:
L0:

    // $t11 := move($t15)
    call $tmp := $CopyOrMoveValue($t15);
    $t11 := $tmp;

    // $t12 := Roles::UNHOSTED_ROLE_ID()
    call $t12 := $Roles_UNHOSTED_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 1205);
      goto Abort;
    }
    assume $IsValidU64($t12);


    // $t13 := pack Roles::RoleId($t12)
    call $tmp := $Roles_RoleId_pack(0, 0, 0, $t12);
    $t13 := $tmp;

    // move_to<Roles::RoleId>($t13, $t11)
    call $MoveTo($Roles_RoleId_type_value(), $t13, $t11);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 8020);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $Roles_new_unhosted_role(_creating_account: $Value, new_account: $Value) returns ()
free requires is#$Address(_creating_account);
free requires is#$Address(new_account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $Roles_new_unhosted_role_def(_creating_account, new_account);
}

procedure {:inline 1} $Roles_new_validator_operator_role_def(creating_account: $Value, new_account: $Value) returns (){
    // declare local variables
    var calling_role: $Value; // $Roles_RoleId_type_value()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $IntegerType()
    var $t5: $Value; // $BooleanType()
    var $t6: $Value; // $IntegerType()
    var $t7: $Value; // $AddressType()
    var $t8: $Value; // $AddressType()
    var $t9: $Value; // $Roles_RoleId_type_value()
    var $t10: $Value; // $AddressType()
    var $t11: $Value; // $AddressType()
    var $t12: $Value; // $BooleanType()
    var $t13: $Value; // $BooleanType()
    var $t14: $Value; // $BooleanType()
    var $t15: $Value; // $AddressType()
    var $t16: $Value; // $Roles_RoleId_type_value()
    var $t17: $Value; // $IntegerType()
    var $t18: $Value; // $Roles_RoleId_type_value()
    var $t19: $Value; // $IntegerType()
    var $t20: $Value; // $IntegerType()
    var $t21: $Value; // $IntegerType()
    var $t22: $Value; // $BooleanType()
    var $t23: $Value; // $BooleanType()
    var $t24: $Value; // $AddressType()
    var $t25: $Value; // $IntegerType()
    var $t26: $Value; // $AddressType()
    var $t27: $Value; // $IntegerType()
    var $t28: $Value; // $Roles_RoleId_type_value()
    var $t29: $Value; // $AddressType()
    var $t30: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 5892, 0, creating_account); }
    if (true) { assume $DebugTrackLocal(15, 5892, 1, new_account); }

    // bytecode translation starts here
    // $t29 := move(creating_account)
    call $tmp := $CopyOrMoveValue(creating_account);
    $t29 := $tmp;

    // $t30 := move(new_account)
    call $tmp := $CopyOrMoveValue(new_account);
    $t30 := $tmp;

    // $t7 := move($t29)
    call $tmp := $CopyOrMoveValue($t29);
    $t7 := $tmp;

    // $t8 := Signer::address_of($t7)
    call $t8 := $Signer_address_of($t7);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 6078);
      goto Abort;
    }
    assume is#$Address($t8);


    // $t9 := get_global<Roles::RoleId>($t8)
    call $tmp := $GetGlobal($t8, $Roles_RoleId_type_value());
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 6048);
      goto Abort;
    }
    assume $Roles_RoleId_is_well_formed($tmp);
    $t9 := $tmp;

    // calling_role := $t9
    call $tmp := $CopyOrMoveValue($t9);
    calling_role := $tmp;
    if (true) { assume $DebugTrackLocal(15, 6033, 2, $tmp); }

    // $t10 := copy($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t10 := $tmp;

    // $t11 := Signer::address_of($t10)
    call $t11 := $Signer_address_of($t10);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 6221);
      goto Abort;
    }
    assume is#$Address($t11);


    // $t12 := exists<Roles::RoleId>($t11)
    call $tmp := $Exists($t11, $Roles_RoleId_type_value());
    $t12 := $tmp;

    // $t13 := !($t12)
    call $tmp := $Not($t12);
    $t13 := $tmp;

    // $t3 := $t13
    call $tmp := $CopyOrMoveValue($t13);
    $t3 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 6190, 3, $tmp); }

    // if ($t3) goto L0 else goto L1
    $tmp := $t3;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t15 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t15 := $tmp;

    // destroy($t15)

    // $t16 := move(calling_role)
    call $tmp := $CopyOrMoveValue(calling_role);
    $t16 := $tmp;

    // destroy($t16)

    // $t17 := 1
    $tmp := $Integer(1);
    $t17 := $tmp;

    // abort($t17)
    if (true) { assume $DebugTrackAbort(15, 6190); }
    goto Abort;

    // L0:
L0:

    // $t18 := move(calling_role)
    call $tmp := $CopyOrMoveValue(calling_role);
    $t18 := $tmp;

    // $t19 := get_field<Roles::RoleId>.role_id($t18)
    call $tmp := $GetFieldFromValue($t18, $Roles_RoleId_role_id);
    assume $IsValidU64($tmp);
    $t19 := $tmp;

    // $t20 := move($t19)
    call $tmp := $CopyOrMoveValue($t19);
    $t20 := $tmp;

    // $t21 := Roles::LIBRA_ROOT_ROLE_ID()
    call $t21 := $Roles_LIBRA_ROOT_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 901);
      goto Abort;
    }
    assume $IsValidU64($t21);


    // $t22 := ==($t20, $t21)
    $tmp := $Boolean($IsEqual($t20, $t21));
    $t22 := $tmp;

    // $t5 := $t22
    call $tmp := $CopyOrMoveValue($t22);
    $t5 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 6259, 5, $tmp); }

    // if ($t5) goto L2 else goto L3
    $tmp := $t5;
    if (b#$Boolean($tmp)) { goto L2; } else { goto L3; }

    // L3:
L3:

    // $t24 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t24 := $tmp;

    // destroy($t24)

    // $t25 := 0
    $tmp := $Integer(0);
    $t25 := $tmp;

    // abort($t25)
    if (true) { assume $DebugTrackAbort(15, 6259); }
    goto Abort;

    // L2:
L2:

    // $t26 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t26 := $tmp;

    // $t27 := Roles::VALIDATOR_OPERATOR_ROLE_ID()
    call $t27 := $Roles_VALIDATOR_OPERATOR_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 1076);
      goto Abort;
    }
    assume $IsValidU64($t27);


    // $t28 := pack Roles::RoleId($t27)
    call $tmp := $Roles_RoleId_pack(0, 0, 0, $t27);
    $t28 := $tmp;

    // move_to<Roles::RoleId>($t28, $t26)
    call $MoveTo($Roles_RoleId_type_value(), $t28, $t26);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 6324);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $Roles_new_validator_operator_role(creating_account: $Value, new_account: $Value) returns ()
free requires is#$Address(creating_account);
free requires is#$Address(new_account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $Roles_new_validator_operator_role_def(creating_account, new_account);
}

procedure {:inline 1} $Roles_new_validator_role_def(creating_account: $Value, new_account: $Value) returns (){
    // declare local variables
    var calling_role: $Value; // $Roles_RoleId_type_value()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $IntegerType()
    var $t5: $Value; // $BooleanType()
    var $t6: $Value; // $IntegerType()
    var $t7: $Value; // $AddressType()
    var $t8: $Value; // $AddressType()
    var $t9: $Value; // $Roles_RoleId_type_value()
    var $t10: $Value; // $AddressType()
    var $t11: $Value; // $AddressType()
    var $t12: $Value; // $BooleanType()
    var $t13: $Value; // $BooleanType()
    var $t14: $Value; // $BooleanType()
    var $t15: $Value; // $AddressType()
    var $t16: $Value; // $Roles_RoleId_type_value()
    var $t17: $Value; // $IntegerType()
    var $t18: $Value; // $Roles_RoleId_type_value()
    var $t19: $Value; // $IntegerType()
    var $t20: $Value; // $IntegerType()
    var $t21: $Value; // $IntegerType()
    var $t22: $Value; // $BooleanType()
    var $t23: $Value; // $BooleanType()
    var $t24: $Value; // $AddressType()
    var $t25: $Value; // $IntegerType()
    var $t26: $Value; // $AddressType()
    var $t27: $Value; // $IntegerType()
    var $t28: $Value; // $Roles_RoleId_type_value()
    var $t29: $Value; // $AddressType()
    var $t30: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(15, 5281, 0, creating_account); }
    if (true) { assume $DebugTrackLocal(15, 5281, 1, new_account); }

    // bytecode translation starts here
    // $t29 := move(creating_account)
    call $tmp := $CopyOrMoveValue(creating_account);
    $t29 := $tmp;

    // $t30 := move(new_account)
    call $tmp := $CopyOrMoveValue(new_account);
    $t30 := $tmp;

    // $t7 := move($t29)
    call $tmp := $CopyOrMoveValue($t29);
    $t7 := $tmp;

    // $t8 := Signer::address_of($t7)
    call $t8 := $Signer_address_of($t7);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 5457);
      goto Abort;
    }
    assume is#$Address($t8);


    // $t9 := get_global<Roles::RoleId>($t8)
    call $tmp := $GetGlobal($t8, $Roles_RoleId_type_value());
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 5427);
      goto Abort;
    }
    assume $Roles_RoleId_is_well_formed($tmp);
    $t9 := $tmp;

    // calling_role := $t9
    call $tmp := $CopyOrMoveValue($t9);
    calling_role := $tmp;
    if (true) { assume $DebugTrackLocal(15, 5412, 2, $tmp); }

    // $t10 := copy($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t10 := $tmp;

    // $t11 := Signer::address_of($t10)
    call $t11 := $Signer_address_of($t10);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 5600);
      goto Abort;
    }
    assume is#$Address($t11);


    // $t12 := exists<Roles::RoleId>($t11)
    call $tmp := $Exists($t11, $Roles_RoleId_type_value());
    $t12 := $tmp;

    // $t13 := !($t12)
    call $tmp := $Not($t12);
    $t13 := $tmp;

    // $t3 := $t13
    call $tmp := $CopyOrMoveValue($t13);
    $t3 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 5569, 3, $tmp); }

    // if ($t3) goto L0 else goto L1
    $tmp := $t3;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t15 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t15 := $tmp;

    // destroy($t15)

    // $t16 := move(calling_role)
    call $tmp := $CopyOrMoveValue(calling_role);
    $t16 := $tmp;

    // destroy($t16)

    // $t17 := 1
    $tmp := $Integer(1);
    $t17 := $tmp;

    // abort($t17)
    if (true) { assume $DebugTrackAbort(15, 5569); }
    goto Abort;

    // L0:
L0:

    // $t18 := move(calling_role)
    call $tmp := $CopyOrMoveValue(calling_role);
    $t18 := $tmp;

    // $t19 := get_field<Roles::RoleId>.role_id($t18)
    call $tmp := $GetFieldFromValue($t18, $Roles_RoleId_role_id);
    assume $IsValidU64($tmp);
    $t19 := $tmp;

    // $t20 := move($t19)
    call $tmp := $CopyOrMoveValue($t19);
    $t20 := $tmp;

    // $t21 := Roles::LIBRA_ROOT_ROLE_ID()
    call $t21 := $Roles_LIBRA_ROOT_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 901);
      goto Abort;
    }
    assume $IsValidU64($t21);


    // $t22 := ==($t20, $t21)
    $tmp := $Boolean($IsEqual($t20, $t21));
    $t22 := $tmp;

    // $t5 := $t22
    call $tmp := $CopyOrMoveValue($t22);
    $t5 := $tmp;
    if (true) { assume $DebugTrackLocal(15, 5638, 5, $tmp); }

    // if ($t5) goto L2 else goto L3
    $tmp := $t5;
    if (b#$Boolean($tmp)) { goto L2; } else { goto L3; }

    // L3:
L3:

    // $t24 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t24 := $tmp;

    // destroy($t24)

    // $t25 := 0
    $tmp := $Integer(0);
    $t25 := $tmp;

    // abort($t25)
    if (true) { assume $DebugTrackAbort(15, 5638); }
    goto Abort;

    // L2:
L2:

    // $t26 := move($t30)
    call $tmp := $CopyOrMoveValue($t30);
    $t26 := $tmp;

    // $t27 := Roles::VALIDATOR_ROLE_ID()
    call $t27 := $Roles_VALIDATOR_ROLE_ID();
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 1037);
      goto Abort;
    }
    assume $IsValidU64($t27);


    // $t28 := pack Roles::RoleId($t27)
    call $tmp := $Roles_RoleId_pack(0, 0, 0, $t27);
    $t28 := $tmp;

    // move_to<Roles::RoleId>($t28, $t26)
    call $MoveTo($Roles_RoleId_type_value(), $t28, $t26);
    if ($abort_flag) {
      assume $DebugTrackAbort(15, 5703);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $Roles_new_validator_role(creating_account: $Value, new_account: $Value) returns ()
free requires is#$Address(creating_account);
free requires is#$Address(new_account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Roles_RoleId_type_value(), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Roles_RoleId_type_value(), addr)) && b#$Boolean($Boolean($IsEqual(old($SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id)), $SelectField($ResourceValue($m, $Roles_RoleId_type_value(), addr), $Roles_RoleId_role_id))))))))))));
{
    call $Roles_new_validator_role_def(creating_account, new_account);
}



// ** spec vars of module Offer



// ** spec funs of module Offer

function {:inline} $Offer_is_allowed_recipient($m: $Memory, $txn: $Transaction, $tv0: $TypeValue, offer_addr: $Value, recipient: $Value): $Value {
    $Boolean(b#$Boolean($Boolean($IsEqual(recipient, $SelectField($ResourceValue($m, $Offer_Offer_type_value($tv0), offer_addr), $Offer_Offer_for)))) || b#$Boolean($Boolean($IsEqual(recipient, offer_addr))))
}



// ** structs of module Offer

const unique $Offer_Offer: $TypeName;
const $Offer_Offer_offered: $FieldName;
axiom $Offer_Offer_offered == 0;
const $Offer_Offer_for: $FieldName;
axiom $Offer_Offer_for == 1;
function $Offer_Offer_type_value($tv0: $TypeValue): $TypeValue {
    $StructType($Offer_Offer, $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $tv0], 1), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $tv0][1 := $AddressType()], 2))
}
function {:inline} $Offer_Offer_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 2
      && is#$Address($SelectField($this, $Offer_Offer_for))
}
function {:inline} $Offer_Offer_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 2
      && is#$Address($SelectField($this, $Offer_Offer_for))
}

axiom (forall m: $Memory, a: $Value, $tv0: $TypeValue :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $Offer_Offer_is_well_formed($ResourceValue(m, $Offer_Offer_type_value($tv0), a))
);

procedure {:inline 1} $Offer_Offer_pack($file_id: int, $byte_index: int, $var_idx: int, $tv0: $TypeValue, offered: $Value, for: $Value) returns ($struct: $Value)
{
    assume is#$Address(for);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := offered][1 := for], 2));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $Offer_Offer_unpack($tv0: $TypeValue, $struct: $Value) returns (offered: $Value, for: $Value)
{
    assume is#$Vector($struct);
    offered := $SelectField($struct, $Offer_Offer_offered);
    for := $SelectField($struct, $Offer_Offer_for);
    assume is#$Address(for);
}



// ** functions of module Offer

procedure {:inline 1} $Offer_address_of_def($tv0: $TypeValue, offer_address: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $AddressType()
    var $t2: $Value; // $Offer_Offer_type_value($tv0)
    var $t3: $Value; // $AddressType()
    var $t4: $Value; // $AddressType()
    var $t5: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(13, 1473, 0, offer_address); }

    // bytecode translation starts here
    // $t5 := move(offer_address)
    call $tmp := $CopyOrMoveValue(offer_address);
    $t5 := $tmp;

    // $t2 := get_global<Offer::Offer<#0>>($t5)
    call $tmp := $GetGlobal($t5, $Offer_Offer_type_value($tv0));
    if ($abort_flag) {
      assume $DebugTrackAbort(13, 1558);
      goto Abort;
    }
    assume $Offer_Offer_is_well_formed($tmp);
    $t2 := $tmp;

    // $t3 := get_field<Offer::Offer<#0>>.for($t2)
    call $tmp := $GetFieldFromValue($t2, $Offer_Offer_for);
    assume is#$Address($tmp);
    $t3 := $tmp;

    // $t4 := move($t3)
    call $tmp := $CopyOrMoveValue($t3);
    $t4 := $tmp;

    // return $t4
    $ret0 := $t4;
    if (true) { assume $DebugTrackLocal(13, 1558, 6, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Offer_address_of($tv0: $TypeValue, offer_address: $Value) returns ($ret0: $Value)
free requires is#$Address(offer_address);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($Boolean(!b#$Boolean($ResourceExists($m, $Offer_Offer_type_value($tv0), offer_address))))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(!b#$Boolean($ResourceExists($m, $Offer_Offer_type_value($tv0), offer_address)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall ty: $Value :: is#$Type(ty) ==> b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean($Boolean(!b#$Boolean(old($ResourceExists($m, $Offer_Offer_type_value(t#$Type(ty)), addr))))) ==> b#$Boolean($Boolean(!b#$Boolean($ResourceExists($m, $Offer_Offer_type_value(t#$Type(ty)), addr)))))))))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall ty: $Value :: is#$Type(ty) ==> b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Offer_Offer_type_value(t#$Type(ty)), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Offer_Offer_type_value(t#$Type(ty)), addr)) && b#$Boolean($Boolean($IsEqual($ResourceValue($m, $Offer_Offer_type_value(t#$Type(ty)), addr), old($ResourceValue($m, $Offer_Offer_type_value(t#$Type(ty)), addr))))))))))))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($ret0, $SelectField($ResourceValue($m, $Offer_Offer_type_value($tv0), offer_address), $Offer_Offer_for)))));
{
    call $ret0 := $Offer_address_of_def($tv0, offer_address);
}

procedure {:inline 1} $Offer_create_def($tv0: $TypeValue, account: $Value, offered: $Value, for: $Value) returns (){
    // declare local variables
    var $t3: $Value; // $AddressType()
    var $t4: $Value; // $tv0
    var $t5: $Value; // $AddressType()
    var $t6: $Value; // $Offer_Offer_type_value($tv0)
    var $t7: $Value; // $AddressType()
    var $t8: $Value; // $tv0
    var $t9: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(13, 459, 0, account); }
    if (true) { assume $DebugTrackLocal(13, 459, 1, offered); }
    if (true) { assume $DebugTrackLocal(13, 459, 2, for); }

    // bytecode translation starts here
    // $t7 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t7 := $tmp;

    // $t8 := move(offered)
    call $tmp := $CopyOrMoveValue(offered);
    $t8 := $tmp;

    // $t9 := move(for)
    call $tmp := $CopyOrMoveValue(for);
    $t9 := $tmp;

    // $t3 := move($t7)
    call $tmp := $CopyOrMoveValue($t7);
    $t3 := $tmp;

    // $t6 := pack Offer::Offer<#0>($t8, $t9)
    call $tmp := $Offer_Offer_pack(0, 0, 0, $tv0, $t8, $t9);
    $t6 := $tmp;

    // move_to<Offer::Offer<#0>>($t6, $t3)
    call $MoveTo($Offer_Offer_type_value($tv0), $t6, $t3);
    if ($abort_flag) {
      assume $DebugTrackAbort(13, 542);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $Offer_create($tv0: $TypeValue, account: $Value, offered: $Value, for: $Value) returns ()
free requires is#$Address(account);
free requires is#$Address(for);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($ResourceExists($m, $Offer_Offer_type_value($tv0), $Signer_spec_address_of($m, $txn, account)))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($ResourceExists($m, $Offer_Offer_type_value($tv0), $Signer_spec_address_of($m, $txn, account))))));
free ensures !$abort_flag ==> (b#$Boolean($ResourceExists($m, $Offer_Offer_type_value($tv0), $Signer_spec_address_of($m, $txn, account))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($ResourceValue($m, $Offer_Offer_type_value($tv0), $Signer_spec_address_of($m, $txn, account)), $Vector($ExtendValueArray($ExtendValueArray($EmptyValueArray(), offered), for))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall ty: $Value :: is#$Type(ty) ==> b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Offer_Offer_type_value(t#$Type(ty)), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Offer_Offer_type_value(t#$Type(ty)), addr)) && b#$Boolean($Boolean($IsEqual($ResourceValue($m, $Offer_Offer_type_value(t#$Type(ty)), addr), old($ResourceValue($m, $Offer_Offer_type_value(t#$Type(ty)), addr))))))))))))))));
{
    call $Offer_create_def($tv0, account, offered, for);
}

procedure {:inline 1} $Offer_exists_at_def($tv0: $TypeValue, offer_address: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $AddressType()
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(13, 1251, 0, offer_address); }

    // bytecode translation starts here
    // $t3 := move(offer_address)
    call $tmp := $CopyOrMoveValue(offer_address);
    $t3 := $tmp;

    // $t2 := exists<Offer::Offer<#0>>($t3)
    call $tmp := $Exists($t3, $Offer_Offer_type_value($tv0));
    $t2 := $tmp;

    // return $t2
    $ret0 := $t2;
    if (true) { assume $DebugTrackLocal(13, 1317, 4, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Offer_exists_at($tv0: $TypeValue, offer_address: $Value) returns ($ret0: $Value)
free requires is#$Address(offer_address);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall ty: $Value :: is#$Type(ty) ==> b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean($Boolean(!b#$Boolean(old($ResourceExists($m, $Offer_Offer_type_value(t#$Type(ty)), addr))))) ==> b#$Boolean($Boolean(!b#$Boolean($ResourceExists($m, $Offer_Offer_type_value(t#$Type(ty)), addr)))))))))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall ty: $Value :: is#$Type(ty) ==> b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Offer_Offer_type_value(t#$Type(ty)), addr))) ==> b#$Boolean($Boolean(b#$Boolean($ResourceExists($m, $Offer_Offer_type_value(t#$Type(ty)), addr)) && b#$Boolean($Boolean($IsEqual($ResourceValue($m, $Offer_Offer_type_value(t#$Type(ty)), addr), old($ResourceValue($m, $Offer_Offer_type_value(t#$Type(ty)), addr))))))))))))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($ret0, $ResourceExists($m, $Offer_Offer_type_value($tv0), offer_address)))));
{
    call $ret0 := $Offer_exists_at_def($tv0, offer_address);
}

procedure {:inline 1} $Offer_redeem_def($tv0: $TypeValue, account: $Value, offer_address: $Value) returns ($ret0: $Value){
    // declare local variables
    var for: $Value; // $AddressType()
    var offered: $Value; // $tv0
    var sender: $Value; // $AddressType()
    var $t5: $Value; // $BooleanType()
    var $t6: $Value; // $IntegerType()
    var $t7: $Value; // $BooleanType()
    var $t8: $Value; // $AddressType()
    var $t9: $Value; // $Offer_Offer_type_value($tv0)
    var $t10: $Value; // $tv0
    var $t11: $Value; // $AddressType()
    var $t12: $Value; // $AddressType()
    var $t13: $Value; // $AddressType()
    var $t14: $Value; // $AddressType()
    var $t15: $Value; // $AddressType()
    var $t16: $Value; // $BooleanType()
    var $t17: $Value; // $BooleanType()
    var $t18: $Value; // $AddressType()
    var $t19: $Value; // $AddressType()
    var $t20: $Value; // $BooleanType()
    var $t21: $Value; // $BooleanType()
    var $t22: $Value; // $BooleanType()
    var $t23: $Value; // $IntegerType()
    var $t24: $Value; // $tv0
    var $t25: $Value; // $AddressType()
    var $t26: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(13, 833, 0, account); }
    if (true) { assume $DebugTrackLocal(13, 833, 1, offer_address); }

    // bytecode translation starts here
    // $t25 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t25 := $tmp;

    // $t26 := move(offer_address)
    call $tmp := $CopyOrMoveValue(offer_address);
    $t26 := $tmp;

    // $t9 := move_from<Offer::Offer<#0>>($t26)
    call $tmp := $MoveFrom($t26, $Offer_Offer_type_value($tv0));
    if ($abort_flag) {
      assume $DebugTrackAbort(13, 970);
      goto Abort;
    }
    assume $Offer_Offer_is_well_formed($tmp);
    $t9 := $tmp;

    // ($t10, $t11) := unpack Offer::Offer<#0>($t9)
    call $t10, $t11 := $Offer_Offer_unpack($tv0, $t9);
    $t10 := $t10;
    $t11 := $t11;

    // for := $t11
    call $tmp := $CopyOrMoveValue($t11);
    for := $tmp;
    if (true) { assume $DebugTrackLocal(13, 962, 2, $tmp); }

    // offered := $t10
    call $tmp := $CopyOrMoveValue($t10);
    offered := $tmp;
    if (true) { assume $DebugTrackLocal(13, 953, 3, $tmp); }

    // $t12 := move($t25)
    call $tmp := $CopyOrMoveValue($t25);
    $t12 := $tmp;

    // $t13 := Signer::address_of($t12)
    call $t13 := $Signer_address_of($t12);
    if ($abort_flag) {
      assume $DebugTrackAbort(13, 1037);
      goto Abort;
    }
    assume is#$Address($t13);


    // sender := $t13
    call $tmp := $CopyOrMoveValue($t13);
    sender := $tmp;
    if (true) { assume $DebugTrackLocal(13, 1020, 4, $tmp); }

    // $t16 := ==(sender, for)
    $tmp := $Boolean($IsEqual(sender, for));
    $t16 := $tmp;

    // if ($t16) goto L0 else goto L1
    $tmp := $t16;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // goto L2
    goto L2;

    // L0:
L0:

    // $t17 := true
    $tmp := $Boolean(true);
    $t17 := $tmp;

    // $t7 := $t17
    call $tmp := $CopyOrMoveValue($t17);
    $t7 := $tmp;
    if (true) { assume $DebugTrackLocal(13, 1110, 7, $tmp); }

    // goto L3
    goto L3;

    // L2:
L2:

    // $t20 := ==(sender, $t26)
    $tmp := $Boolean($IsEqual(sender, $t26));
    $t20 := $tmp;

    // $t7 := $t20
    call $tmp := $CopyOrMoveValue($t20);
    $t7 := $tmp;
    if (true) { assume $DebugTrackLocal(13, 1110, 7, $tmp); }

    // goto L3
    goto L3;

    // L3:
L3:

    // $t5 := $t7
    call $tmp := $CopyOrMoveValue($t7);
    $t5 := $tmp;
    if (true) { assume $DebugTrackLocal(13, 1103, 5, $tmp); }

    // if ($t5) goto L4 else goto L5
    $tmp := $t5;
    if (b#$Boolean($tmp)) { goto L4; } else { goto L5; }

    // L5:
L5:

    // $t23 := 11
    $tmp := $Integer(11);
    $t23 := $tmp;

    // abort($t23)
    if (true) { assume $DebugTrackAbort(13, 1103); }
    goto Abort;

    // L4:
L4:

    // return offered
    $ret0 := offered;
    if (true) { assume $DebugTrackLocal(13, 1161, 27, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Offer_redeem($tv0: $TypeValue, account: $Value, offer_address: $Value) returns ($ret0: $Value)
free requires is#$Address(account);
free requires is#$Address(offer_address);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($Boolean(!b#$Boolean($ResourceExists($m, $Offer_Offer_type_value($tv0), offer_address))))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean(!b#$Boolean($Offer_is_allowed_recipient($m, $txn, $tv0, offer_address, $Signer_spec_address_of($m, $txn, account)))))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(!b#$Boolean($ResourceExists($m, $Offer_Offer_type_value($tv0), offer_address))))))
    || b#$Boolean(old(($Boolean(!b#$Boolean($Offer_is_allowed_recipient($m, $txn, $tv0, offer_address, $Signer_spec_address_of($m, $txn, account))))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean((forall ty: $Value :: is#$Type(ty) ==> b#$Boolean($Boolean((forall addr: $Value :: is#$Address(addr) ==> b#$Boolean($Boolean(b#$Boolean($Boolean(!b#$Boolean(old($ResourceExists($m, $Offer_Offer_type_value(t#$Type(ty)), addr))))) ==> b#$Boolean($Boolean(!b#$Boolean($ResourceExists($m, $Offer_Offer_type_value(t#$Type(ty)), addr)))))))))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean(old($ResourceExists($m, $Offer_Offer_type_value($tv0), offer_address))) && b#$Boolean($Boolean(!b#$Boolean($ResourceExists($m, $Offer_Offer_type_value($tv0), offer_address)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($ret0, old($SelectField($ResourceValue($m, $Offer_Offer_type_value($tv0), offer_address), $Offer_Offer_offered))))));
{
    call $ret0 := $Offer_redeem_def($tv0, account, offer_address);
}



// ** spec vars of module LibraConfig



// ** spec funs of module LibraConfig

function {:inline} $LibraConfig_spec_has_config($m: $Memory, $txn: $Transaction): $Value {
    $ResourceExists($m, $LibraConfig_Configuration_type_value(), $CoreAddresses_SPEC_LIBRA_ROOT_ADDRESS())
}

function {:inline} $LibraConfig_spec_get($m: $Memory, $txn: $Transaction, $tv0: $TypeValue): $Value {
    $SelectField($ResourceValue($m, $LibraConfig_LibraConfig_type_value($tv0), $CoreAddresses_SPEC_LIBRA_ROOT_ADDRESS()), $LibraConfig_LibraConfig_payload)
}

function {:inline} $LibraConfig_spec_is_published($m: $Memory, $txn: $Transaction, $tv0: $TypeValue): $Value {
    $ResourceExists($m, $LibraConfig_LibraConfig_type_value($tv0), $CoreAddresses_SPEC_LIBRA_ROOT_ADDRESS())
}

function {:inline} $LibraConfig_spec_has_on_chain_config_privilege($m: $Memory, $txn: $Transaction, account: $Value): $Value {
    $Roles_spec_has_libra_root_role($m, $txn, account)
}



// ** structs of module LibraConfig

const unique $LibraConfig_LibraConfig: $TypeName;
const $LibraConfig_LibraConfig_payload: $FieldName;
axiom $LibraConfig_LibraConfig_payload == 0;
function $LibraConfig_LibraConfig_type_value($tv0: $TypeValue): $TypeValue {
    $StructType($LibraConfig_LibraConfig, $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $tv0], 1), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $tv0], 1))
}
function {:inline} $LibraConfig_LibraConfig_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
}
function {:inline} $LibraConfig_LibraConfig_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
}

axiom (forall m: $Memory, a: $Value, $tv0: $TypeValue :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $LibraConfig_LibraConfig_is_well_formed($ResourceValue(m, $LibraConfig_LibraConfig_type_value($tv0), a))
);

procedure {:inline 1} $LibraConfig_LibraConfig_pack($file_id: int, $byte_index: int, $var_idx: int, $tv0: $TypeValue, payload: $Value) returns ($struct: $Value)
{
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := payload], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $LibraConfig_LibraConfig_unpack($tv0: $TypeValue, $struct: $Value) returns (payload: $Value)
{
    assume is#$Vector($struct);
    payload := $SelectField($struct, $LibraConfig_LibraConfig_payload);
}

const unique $LibraConfig_Configuration: $TypeName;
const $LibraConfig_Configuration_epoch: $FieldName;
axiom $LibraConfig_Configuration_epoch == 0;
const $LibraConfig_Configuration_last_reconfiguration_time: $FieldName;
axiom $LibraConfig_Configuration_last_reconfiguration_time == 1;
const $LibraConfig_Configuration_events: $FieldName;
axiom $LibraConfig_Configuration_events == 2;
function $LibraConfig_Configuration_type_value(): $TypeValue {
    $StructType($LibraConfig_Configuration, $TypeValueArray($MapConstTypeValue($DefaultTypeValue()), 0), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $IntegerType()][1 := $IntegerType()][2 := $Event_EventHandle_type_value($LibraConfig_NewEpochEvent_type_value())], 3))
}
function {:inline} $LibraConfig_Configuration_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 3
      && $IsValidU64($SelectField($this, $LibraConfig_Configuration_epoch))
      && $IsValidU64($SelectField($this, $LibraConfig_Configuration_last_reconfiguration_time))
      && $Event_EventHandle_is_well_formed_types($SelectField($this, $LibraConfig_Configuration_events))
}
function {:inline} $LibraConfig_Configuration_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 3
      && $IsValidU64($SelectField($this, $LibraConfig_Configuration_epoch))
      && $IsValidU64($SelectField($this, $LibraConfig_Configuration_last_reconfiguration_time))
      && $Event_EventHandle_is_well_formed($SelectField($this, $LibraConfig_Configuration_events))
}

axiom (forall m: $Memory, a: $Value :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $LibraConfig_Configuration_is_well_formed($ResourceValue(m, $LibraConfig_Configuration_type_value(), a))
);

procedure {:inline 1} $LibraConfig_Configuration_pack($file_id: int, $byte_index: int, $var_idx: int, epoch: $Value, last_reconfiguration_time: $Value, events: $Value) returns ($struct: $Value)
{
    assume $IsValidU64(epoch);
    assume $IsValidU64(last_reconfiguration_time);
    assume $Event_EventHandle_is_well_formed(events);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := epoch][1 := last_reconfiguration_time][2 := events], 3));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $LibraConfig_Configuration_unpack($struct: $Value) returns (epoch: $Value, last_reconfiguration_time: $Value, events: $Value)
{
    assume is#$Vector($struct);
    epoch := $SelectField($struct, $LibraConfig_Configuration_epoch);
    assume $IsValidU64(epoch);
    last_reconfiguration_time := $SelectField($struct, $LibraConfig_Configuration_last_reconfiguration_time);
    assume $IsValidU64(last_reconfiguration_time);
    events := $SelectField($struct, $LibraConfig_Configuration_events);
    assume $Event_EventHandle_is_well_formed(events);
}

const unique $LibraConfig_ModifyConfigCapability: $TypeName;
const $LibraConfig_ModifyConfigCapability_dummy_field: $FieldName;
axiom $LibraConfig_ModifyConfigCapability_dummy_field == 0;
function $LibraConfig_ModifyConfigCapability_type_value($tv0: $TypeValue): $TypeValue {
    $StructType($LibraConfig_ModifyConfigCapability, $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $tv0], 1), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $BooleanType()], 1))
}
function {:inline} $LibraConfig_ModifyConfigCapability_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && is#$Boolean($SelectField($this, $LibraConfig_ModifyConfigCapability_dummy_field))
}
function {:inline} $LibraConfig_ModifyConfigCapability_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && is#$Boolean($SelectField($this, $LibraConfig_ModifyConfigCapability_dummy_field))
}

axiom (forall m: $Memory, a: $Value, $tv0: $TypeValue :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $LibraConfig_ModifyConfigCapability_is_well_formed($ResourceValue(m, $LibraConfig_ModifyConfigCapability_type_value($tv0), a))
);

procedure {:inline 1} $LibraConfig_ModifyConfigCapability_pack($file_id: int, $byte_index: int, $var_idx: int, $tv0: $TypeValue, dummy_field: $Value) returns ($struct: $Value)
{
    assume is#$Boolean(dummy_field);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := dummy_field], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $LibraConfig_ModifyConfigCapability_unpack($tv0: $TypeValue, $struct: $Value) returns (dummy_field: $Value)
{
    assume is#$Vector($struct);
    dummy_field := $SelectField($struct, $LibraConfig_ModifyConfigCapability_dummy_field);
    assume is#$Boolean(dummy_field);
}

const unique $LibraConfig_NewEpochEvent: $TypeName;
const $LibraConfig_NewEpochEvent_epoch: $FieldName;
axiom $LibraConfig_NewEpochEvent_epoch == 0;
function $LibraConfig_NewEpochEvent_type_value(): $TypeValue {
    $StructType($LibraConfig_NewEpochEvent, $TypeValueArray($MapConstTypeValue($DefaultTypeValue()), 0), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $IntegerType()], 1))
}
function {:inline} $LibraConfig_NewEpochEvent_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $IsValidU64($SelectField($this, $LibraConfig_NewEpochEvent_epoch))
}
function {:inline} $LibraConfig_NewEpochEvent_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $IsValidU64($SelectField($this, $LibraConfig_NewEpochEvent_epoch))
}

procedure {:inline 1} $LibraConfig_NewEpochEvent_pack($file_id: int, $byte_index: int, $var_idx: int, epoch: $Value) returns ($struct: $Value)
{
    assume $IsValidU64(epoch);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := epoch], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $LibraConfig_NewEpochEvent_unpack($struct: $Value) returns (epoch: $Value)
{
    assume is#$Vector($struct);
    epoch := $SelectField($struct, $LibraConfig_NewEpochEvent_epoch);
    assume $IsValidU64(epoch);
}



// ** functions of module LibraConfig

procedure {:inline 1} $LibraConfig_initialize_def(config_account: $Value) returns (){
    // declare local variables
    var $t1: $Value; // $BooleanType()
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $AddressType()
    var $t4: $Value; // $AddressType()
    var $t5: $Value; // $AddressType()
    var $t6: $Value; // $BooleanType()
    var $t7: $Value; // $BooleanType()
    var $t8: $Value; // $AddressType()
    var $t9: $Value; // $IntegerType()
    var $t10: $Value; // $AddressType()
    var $t11: $Value; // $IntegerType()
    var $t12: $Value; // $IntegerType()
    var $t13: $Value; // $AddressType()
    var $t14: $Value; // $Event_EventHandle_type_value($LibraConfig_NewEpochEvent_type_value())
    var $t15: $Value; // $LibraConfig_Configuration_type_value()
    var $t16: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(11, 888, 0, config_account); }

    // bytecode translation starts here
    // $t16 := move(config_account)
    call $tmp := $CopyOrMoveValue(config_account);
    $t16 := $tmp;

    // $t3 := copy($t16)
    call $tmp := $CopyOrMoveValue($t16);
    $t3 := $tmp;

    // $t4 := Signer::address_of($t3)
    call $t4 := $Signer_address_of($t3);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 1009);
      goto Abort;
    }
    assume is#$Address($t4);


    // $t5 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t5 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 1054);
      goto Abort;
    }
    assume is#$Address($t5);


    // $t6 := ==($t4, $t5)
    $tmp := $Boolean($IsEqual($t4, $t5));
    $t6 := $tmp;

    // $t1 := $t6
    call $tmp := $CopyOrMoveValue($t6);
    $t1 := $tmp;
    if (true) { assume $DebugTrackLocal(11, 994, 1, $tmp); }

    // if ($t1) goto L0 else goto L1
    $tmp := $t1;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t8 := move($t16)
    call $tmp := $CopyOrMoveValue($t16);
    $t8 := $tmp;

    // destroy($t8)

    // $t9 := 1
    $tmp := $Integer(1);
    $t9 := $tmp;

    // abort($t9)
    if (true) { assume $DebugTrackAbort(11, 994); }
    goto Abort;

    // L0:
L0:

    // $t10 := copy($t16)
    call $tmp := $CopyOrMoveValue($t16);
    $t10 := $tmp;

    // $t11 := 0
    $tmp := $Integer(0);
    $t11 := $tmp;

    // $t12 := 0
    $tmp := $Integer(0);
    $t12 := $tmp;

    // $t13 := move($t16)
    call $tmp := $CopyOrMoveValue($t16);
    $t13 := $tmp;

    // $t14 := Event::new_event_handle<LibraConfig::NewEpochEvent>($t13)
    call $t14 := $Event_new_event_handle($LibraConfig_NewEpochEvent_type_value(), $t13);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 1271);
      goto Abort;
    }
    assume $Event_EventHandle_is_well_formed($t14);


    // $t15 := pack LibraConfig::Configuration($t11, $t12, $t14)
    call $tmp := $LibraConfig_Configuration_pack(0, 0, 0, $t11, $t12, $t14);
    $t15 := $tmp;

    // move_to<LibraConfig::Configuration>($t15, $t10)
    call $MoveTo($LibraConfig_Configuration_type_value(), $t15, $t10);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 1088);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraConfig_initialize(config_account: $Value) returns ()
free requires is#$Address(config_account);
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $LibraConfig_initialize_def(config_account);
}

procedure {:inline 1} $LibraConfig_claim_delegated_modify_config_def($tv0: $TypeValue, account: $Value, offer_address: $Value) returns (){
    // declare local variables
    var $t2: $Value; // $AddressType()
    var $t3: $Value; // $AddressType()
    var $t4: $Value; // $AddressType()
    var $t5: $Value; // $LibraConfig_ModifyConfigCapability_type_value($tv0)
    var $t6: $Value; // $AddressType()
    var $t7: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(11, 5931, 0, account); }
    if (true) { assume $DebugTrackLocal(11, 5931, 1, offer_address); }

    // bytecode translation starts here
    // $t6 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t6 := $tmp;

    // $t7 := move(offer_address)
    call $tmp := $CopyOrMoveValue(offer_address);
    $t7 := $tmp;

    // $t2 := copy($t6)
    call $tmp := $CopyOrMoveValue($t6);
    $t2 := $tmp;

    // $t3 := move($t6)
    call $tmp := $CopyOrMoveValue($t6);
    $t3 := $tmp;

    // $t5 := Offer::redeem<LibraConfig::ModifyConfigCapability<#0>>($t3, $t7)
    call $t5 := $Offer_redeem($LibraConfig_ModifyConfigCapability_type_value($tv0), $t3, $t7);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 6056);
      goto Abort;
    }
    assume $LibraConfig_ModifyConfigCapability_is_well_formed($t5);


    // move_to<LibraConfig::ModifyConfigCapability<#0>>($t5, $t2)
    call $MoveTo($LibraConfig_ModifyConfigCapability_type_value($tv0), $t5, $t2);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 6032);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraConfig_claim_delegated_modify_config($tv0: $TypeValue, account: $Value, offer_address: $Value) returns ()
free requires is#$Address(account);
free requires is#$Address(offer_address);
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $LibraConfig_claim_delegated_modify_config_def($tv0, account, offer_address);
}

procedure {:inline 1} $LibraConfig_emit_reconfiguration_event_def() returns (){
    // declare local variables
    var config_ref: $Reference; // ReferenceType($LibraConfig_Configuration_type_value())
    var $t1: $Value; // $AddressType()
    var $t2: $Reference; // ReferenceType($LibraConfig_Configuration_type_value())
    var $t3: $Reference; // ReferenceType($LibraConfig_Configuration_type_value())
    var $t4: $Value; // $IntegerType()
    var $t5: $Value; // $IntegerType()
    var $t6: $Value; // $IntegerType()
    var $t7: $Value; // $IntegerType()
    var $t8: $Reference; // ReferenceType($LibraConfig_Configuration_type_value())
    var $t9: $Reference; // ReferenceType($IntegerType())
    var $t10: $Reference; // ReferenceType($LibraConfig_Configuration_type_value())
    var $t11: $Reference; // ReferenceType($Event_EventHandle_type_value($LibraConfig_NewEpochEvent_type_value()))
    var $t12: $Reference; // ReferenceType($LibraConfig_Configuration_type_value())
    var $t13: $Value; // $IntegerType()
    var $t14: $Value; // $IntegerType()
    var $t15: $Value; // $LibraConfig_NewEpochEvent_type_value()
    var $t16: $Value; // $Event_EventHandle_type_value($LibraConfig_NewEpochEvent_type_value())
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t1 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t1 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 8233);
      goto Abort;
    }
    assume is#$Address($t1);


    // $t2 := borrow_global<LibraConfig::Configuration>($t1)
    call $t2 := $BorrowGlobal($t1, $LibraConfig_Configuration_type_value());
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 8185);
      goto Abort;
    }
    assume $LibraConfig_Configuration_is_well_formed($Dereference($t2));

    // UnpackRef($t2)

    // config_ref := $t2
    call config_ref := $CopyOrMoveRef($t2);
    if (true) { assume $DebugTrackLocal(11, 8172, 0, $Dereference(config_ref)); }

    // $t3 := copy(config_ref)
    call $t3 := $CopyOrMoveRef(config_ref);

    // $t4 := get_field<LibraConfig::Configuration>.epoch($t3)
    call $tmp := $GetFieldFromReference($t3, $LibraConfig_Configuration_epoch);
    assume $IsValidU64($tmp);
    $t4 := $tmp;

    // Reference(config_ref) <- $t3
    call config_ref := $WritebackToReference($t3, config_ref);

    // $t5 := move($t4)
    call $tmp := $CopyOrMoveValue($t4);
    $t5 := $tmp;

    // $t6 := 1
    $tmp := $Integer(1);
    $t6 := $tmp;

    // $t7 := +($t5, $t6)
    call $tmp := $AddU64($t5, $t6);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 8300);
      goto Abort;
    }
    $t7 := $tmp;

    // $t8 := copy(config_ref)
    call $t8 := $CopyOrMoveRef(config_ref);

    // $t9 := borrow_field<LibraConfig::Configuration>.epoch($t8)
    call $t9 := $BorrowField($t8, $LibraConfig_Configuration_epoch);
    assume $IsValidU64($Dereference($t9));

    // Reference(config_ref) <- $t8
    call config_ref := $WritebackToReference($t8, config_ref);

    // UnpackRef($t9)

    // write_ref($t9, $t7)
    call $t9 := $WriteRef($t9, $t7);
    if (true) { assume $DebugTrackLocal(11, 8264, 0, $Dereference(config_ref)); }

    // Reference(config_ref) <- $t9
    call config_ref := $WritebackToReference($t9, config_ref);

    // Reference($t8) <- $t9
    call $t8 := $WritebackToReference($t9, $t8);

    // PackRef($t9)

    // $t10 := copy(config_ref)
    call $t10 := $CopyOrMoveRef(config_ref);

    // $t11 := borrow_field<LibraConfig::Configuration>.events($t10)
    call $t11 := $BorrowField($t10, $LibraConfig_Configuration_events);
    assume $Event_EventHandle_is_well_formed_types($Dereference($t11));

    // Reference(config_ref) <- $t10
    call config_ref := $WritebackToReference($t10, config_ref);

    // UnpackRef($t11)

    // $t12 := move(config_ref)
    call $t12 := $CopyOrMoveRef(config_ref);

    // $t13 := get_field<LibraConfig::Configuration>.epoch($t12)
    call $tmp := $GetFieldFromReference($t12, $LibraConfig_Configuration_epoch);
    assume $IsValidU64($tmp);
    $t13 := $tmp;

    // LibraConfig::Configuration <- $t12
    call $WritebackToGlobal($t12);

    // $t14 := move($t13)
    call $tmp := $CopyOrMoveValue($t13);
    $t14 := $tmp;

    // $t15 := pack LibraConfig::NewEpochEvent($t14)
    call $tmp := $LibraConfig_NewEpochEvent_pack(0, 0, 0, $t14);
    $t15 := $tmp;

    // PackRef($t11)

    // $t16 := read_ref($t11)
    call $tmp := $ReadRef($t11);
    assume $Event_EventHandle_is_well_formed($tmp);
    $t16 := $tmp;

    // $t16 := Event::emit_event<LibraConfig::NewEpochEvent>($t16, $t15)
    call $t16 := $Event_emit_event($LibraConfig_NewEpochEvent_type_value(), $t16, $t15);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 8321);
      goto Abort;
    }
    assume $Event_EventHandle_is_well_formed($t16);


    // write_ref($t11, $t16)
    call $t11 := $WriteRef($t11, $t16);
    if (true) { assume $DebugTrackLocal(11, 8102, 0, $Dereference(config_ref)); }

    // LibraConfig::Configuration <- $t11
    call $WritebackToGlobal($t11);

    // Reference($t10) <- $t11
    call $t10 := $WritebackToReference($t11, $t10);

    // Reference($t12) <- $t11
    call $t12 := $WritebackToReference($t11, $t12);

    // UnpackRef($t11)

    // PackRef($t11)

    // PackRef($t12)

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraConfig_emit_reconfiguration_event() returns ()
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $LibraConfig_emit_reconfiguration_event_def();
}

procedure {:inline 1} $LibraConfig_get_def($tv0: $TypeValue) returns ($ret0: $Value){
    // declare local variables
    var addr: $Value; // $AddressType()
    var $t1: $Value; // $BooleanType()
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $AddressType()
    var $t4: $Value; // $AddressType()
    var $t5: $Value; // $BooleanType()
    var $t6: $Value; // $BooleanType()
    var $t7: $Value; // $IntegerType()
    var $t8: $Value; // $AddressType()
    var $t9: $Value; // $LibraConfig_LibraConfig_type_value($tv0)
    var $t10: $Value; // $tv0
    var $t11: $Value; // $tv0
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t3 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t3 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 1513);
      goto Abort;
    }
    assume is#$Address($t3);


    // addr := $t3
    call $tmp := $CopyOrMoveValue($t3);
    addr := $tmp;
    if (true) { assume $DebugTrackLocal(11, 1491, 0, $tmp); }

    // $t5 := exists<LibraConfig::LibraConfig<#0>>(addr)
    call $tmp := $Exists(addr, $LibraConfig_LibraConfig_type_value($tv0));
    $t5 := $tmp;

    // $t1 := $t5
    call $tmp := $CopyOrMoveValue($t5);
    $t1 := $tmp;
    if (true) { assume $DebugTrackLocal(11, 1543, 1, $tmp); }

    // if ($t1) goto L0 else goto L1
    $tmp := $t1;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t7 := 24
    $tmp := $Integer(24);
    $t7 := $tmp;

    // abort($t7)
    if (true) { assume $DebugTrackAbort(11, 1543); }
    goto Abort;

    // L0:
L0:

    // $t9 := get_global<LibraConfig::LibraConfig<#0>>(addr)
    call $tmp := $GetGlobal(addr, $LibraConfig_LibraConfig_type_value($tv0));
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 1600);
      goto Abort;
    }
    assume $LibraConfig_LibraConfig_is_well_formed($tmp);
    $t9 := $tmp;

    // $t10 := get_field<LibraConfig::LibraConfig<#0>>.payload($t9)
    call $tmp := $GetFieldFromValue($t9, $LibraConfig_LibraConfig_payload);
    $t10 := $tmp;

    // $t11 := move($t10)
    call $tmp := $CopyOrMoveValue($t10);
    $t11 := $tmp;

    // return $t11
    $ret0 := $t11;
    if (true) { assume $DebugTrackLocal(11, 1598, 12, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $LibraConfig_get($tv0: $TypeValue) returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $ret0 := $LibraConfig_get_def($tv0);
}

procedure {:inline 1} $LibraConfig_publish_new_config_def($tv0: $TypeValue, config_account: $Value, payload: $Value) returns (){
    // declare local variables
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $IntegerType()
    var $t4: $Value; // $BooleanType()
    var $t5: $Value; // $IntegerType()
    var $t6: $Value; // $AddressType()
    var $t7: $Value; // $BooleanType()
    var $t8: $Value; // $BooleanType()
    var $t9: $Value; // $AddressType()
    var $t10: $Value; // $IntegerType()
    var $t11: $Value; // $AddressType()
    var $t12: $Value; // $AddressType()
    var $t13: $Value; // $AddressType()
    var $t14: $Value; // $BooleanType()
    var $t15: $Value; // $BooleanType()
    var $t16: $Value; // $AddressType()
    var $t17: $Value; // $IntegerType()
    var $t18: $Value; // $AddressType()
    var $t19: $Value; // $BooleanType()
    var $t20: $Value; // $LibraConfig_ModifyConfigCapability_type_value($tv0)
    var $t21: $Value; // $AddressType()
    var $t22: $Value; // $tv0
    var $t23: $Value; // $LibraConfig_LibraConfig_type_value($tv0)
    var $t24: $Value; // $AddressType()
    var $t25: $Value; // $tv0
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(11, 4226, 0, config_account); }
    if (true) { assume $DebugTrackLocal(11, 4226, 1, payload); }

    // bytecode translation starts here
    // $t24 := move(config_account)
    call $tmp := $CopyOrMoveValue(config_account);
    $t24 := $tmp;

    // $t25 := move(payload)
    call $tmp := $CopyOrMoveValue(payload);
    $t25 := $tmp;

    // $t6 := copy($t24)
    call $tmp := $CopyOrMoveValue($t24);
    $t6 := $tmp;

    // $t7 := Roles::has_on_chain_config_privilege($t6)
    call $t7 := $Roles_has_on_chain_config_privilege($t6);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 4390);
      goto Abort;
    }
    assume is#$Boolean($t7);


    // $t2 := $t7
    call $tmp := $CopyOrMoveValue($t7);
    $t2 := $tmp;
    if (true) { assume $DebugTrackLocal(11, 4376, 2, $tmp); }

    // if ($t2) goto L0 else goto L1
    $tmp := $t2;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t9 := move($t24)
    call $tmp := $CopyOrMoveValue($t24);
    $t9 := $tmp;

    // destroy($t9)

    // $t10 := 919416
    $tmp := $Integer(919416);
    $t10 := $tmp;

    // abort($t10)
    if (true) { assume $DebugTrackAbort(11, 4376); }
    goto Abort;

    // L0:
L0:

    // $t11 := copy($t24)
    call $tmp := $CopyOrMoveValue($t24);
    $t11 := $tmp;

    // $t12 := Signer::address_of($t11)
    call $t12 := $Signer_address_of($t11);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 4469);
      goto Abort;
    }
    assume is#$Address($t12);


    // $t13 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t13 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 4514);
      goto Abort;
    }
    assume is#$Address($t13);


    // $t14 := ==($t12, $t13)
    $tmp := $Boolean($IsEqual($t12, $t13));
    $t14 := $tmp;

    // $t4 := $t14
    call $tmp := $CopyOrMoveValue($t14);
    $t4 := $tmp;
    if (true) { assume $DebugTrackLocal(11, 4454, 4, $tmp); }

    // if ($t4) goto L2 else goto L3
    $tmp := $t4;
    if (b#$Boolean($tmp)) { goto L2; } else { goto L3; }

    // L3:
L3:

    // $t16 := move($t24)
    call $tmp := $CopyOrMoveValue($t24);
    $t16 := $tmp;

    // destroy($t16)

    // $t17 := 1
    $tmp := $Integer(1);
    $t17 := $tmp;

    // abort($t17)
    if (true) { assume $DebugTrackAbort(11, 4454); }
    goto Abort;

    // L2:
L2:

    // $t18 := copy($t24)
    call $tmp := $CopyOrMoveValue($t24);
    $t18 := $tmp;

    // $t19 := false
    $tmp := $Boolean(false);
    $t19 := $tmp;

    // $t20 := pack LibraConfig::ModifyConfigCapability<#0>($t19)
    call $tmp := $LibraConfig_ModifyConfigCapability_pack(0, 0, 0, $tv0, $t19);
    $t20 := $tmp;

    // move_to<LibraConfig::ModifyConfigCapability<#0>>($t20, $t18)
    call $MoveTo($LibraConfig_ModifyConfigCapability_type_value($tv0), $t20, $t18);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 4548);
      goto Abort;
    }

    // $t21 := move($t24)
    call $tmp := $CopyOrMoveValue($t24);
    $t21 := $tmp;

    // $t23 := pack LibraConfig::LibraConfig<#0>($t25)
    call $tmp := $LibraConfig_LibraConfig_pack(0, 0, 0, $tv0, $t25);
    $t23 := $tmp;

    // move_to<LibraConfig::LibraConfig<#0>>($t23, $t21)
    call $MoveTo($LibraConfig_LibraConfig_type_value($tv0), $t23, $t21);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 4616);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraConfig_publish_new_config($tv0: $TypeValue, config_account: $Value, payload: $Value) returns ()
free requires is#$Address(config_account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean(old($Boolean(!b#$Boolean($LibraConfig_spec_is_published($m, $txn, $tv0))))));
free ensures !$abort_flag ==> (b#$Boolean($LibraConfig_spec_is_published($m, $txn, $tv0)));
{
    call $LibraConfig_publish_new_config_def($tv0, config_account, payload);
}

procedure {:inline 1} $LibraConfig_publish_new_config_with_capability_def($tv0: $TypeValue, config_account: $Value, payload: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $IntegerType()
    var $t4: $Value; // $BooleanType()
    var $t5: $Value; // $IntegerType()
    var $t6: $Value; // $AddressType()
    var $t7: $Value; // $BooleanType()
    var $t8: $Value; // $BooleanType()
    var $t9: $Value; // $AddressType()
    var $t10: $Value; // $IntegerType()
    var $t11: $Value; // $AddressType()
    var $t12: $Value; // $AddressType()
    var $t13: $Value; // $AddressType()
    var $t14: $Value; // $BooleanType()
    var $t15: $Value; // $BooleanType()
    var $t16: $Value; // $AddressType()
    var $t17: $Value; // $IntegerType()
    var $t18: $Value; // $AddressType()
    var $t19: $Value; // $tv0
    var $t20: $Value; // $LibraConfig_LibraConfig_type_value($tv0)
    var $t21: $Value; // $BooleanType()
    var $t22: $Value; // $LibraConfig_ModifyConfigCapability_type_value($tv0)
    var $t23: $Value; // $AddressType()
    var $t24: $Value; // $tv0
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(11, 2931, 0, config_account); }
    if (true) { assume $DebugTrackLocal(11, 2931, 1, payload); }

    // bytecode translation starts here
    // $t23 := move(config_account)
    call $tmp := $CopyOrMoveValue(config_account);
    $t23 := $tmp;

    // $t24 := move(payload)
    call $tmp := $CopyOrMoveValue(payload);
    $t24 := $tmp;

    // $t6 := copy($t23)
    call $tmp := $CopyOrMoveValue($t23);
    $t6 := $tmp;

    // $t7 := Roles::has_on_chain_config_privilege($t6)
    call $t7 := $Roles_has_on_chain_config_privilege($t6);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 3144);
      goto Abort;
    }
    assume is#$Boolean($t7);


    // $t2 := $t7
    call $tmp := $CopyOrMoveValue($t7);
    $t2 := $tmp;
    if (true) { assume $DebugTrackLocal(11, 3130, 2, $tmp); }

    // if ($t2) goto L0 else goto L1
    $tmp := $t2;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t9 := move($t23)
    call $tmp := $CopyOrMoveValue($t23);
    $t9 := $tmp;

    // destroy($t9)

    // $t10 := 919414
    $tmp := $Integer(919414);
    $t10 := $tmp;

    // abort($t10)
    if (true) { assume $DebugTrackAbort(11, 3130); }
    goto Abort;

    // L0:
L0:

    // $t11 := copy($t23)
    call $tmp := $CopyOrMoveValue($t23);
    $t11 := $tmp;

    // $t12 := Signer::address_of($t11)
    call $t12 := $Signer_address_of($t11);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 3223);
      goto Abort;
    }
    assume is#$Address($t12);


    // $t13 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t13 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 3268);
      goto Abort;
    }
    assume is#$Address($t13);


    // $t14 := ==($t12, $t13)
    $tmp := $Boolean($IsEqual($t12, $t13));
    $t14 := $tmp;

    // $t4 := $t14
    call $tmp := $CopyOrMoveValue($t14);
    $t4 := $tmp;
    if (true) { assume $DebugTrackLocal(11, 3208, 4, $tmp); }

    // if ($t4) goto L2 else goto L3
    $tmp := $t4;
    if (b#$Boolean($tmp)) { goto L2; } else { goto L3; }

    // L3:
L3:

    // $t16 := move($t23)
    call $tmp := $CopyOrMoveValue($t23);
    $t16 := $tmp;

    // destroy($t16)

    // $t17 := 1
    $tmp := $Integer(1);
    $t17 := $tmp;

    // abort($t17)
    if (true) { assume $DebugTrackAbort(11, 3208); }
    goto Abort;

    // L2:
L2:

    // $t18 := move($t23)
    call $tmp := $CopyOrMoveValue($t23);
    $t18 := $tmp;

    // $t20 := pack LibraConfig::LibraConfig<#0>($t24)
    call $tmp := $LibraConfig_LibraConfig_pack(0, 0, 0, $tv0, $t24);
    $t20 := $tmp;

    // move_to<LibraConfig::LibraConfig<#0>>($t20, $t18)
    call $MoveTo($LibraConfig_LibraConfig_type_value($tv0), $t20, $t18);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 3302);
      goto Abort;
    }

    // $t21 := false
    $tmp := $Boolean(false);
    $t21 := $tmp;

    // $t22 := pack LibraConfig::ModifyConfigCapability<#0>($t21)
    call $tmp := $LibraConfig_ModifyConfigCapability_pack(0, 0, 0, $tv0, $t21);
    $t22 := $tmp;

    // return $t22
    $ret0 := $t22;
    if (true) { assume $DebugTrackLocal(11, 3628, 25, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $LibraConfig_publish_new_config_with_capability($tv0: $TypeValue, config_account: $Value, payload: $Value) returns ($ret0: $Value)
free requires is#$Address(config_account);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean(old($Boolean(!b#$Boolean($LibraConfig_spec_is_published($m, $txn, $tv0))))));
free ensures !$abort_flag ==> (b#$Boolean($LibraConfig_spec_is_published($m, $txn, $tv0)));
{
    call $ret0 := $LibraConfig_publish_new_config_with_capability_def($tv0, config_account, payload);
}

procedure {:inline 1} $LibraConfig_publish_new_config_with_delegate_def($tv0: $TypeValue, config_account: $Value, payload: $Value, delegate: $Value) returns (){
    // declare local variables
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $IntegerType()
    var $t5: $Value; // $BooleanType()
    var $t6: $Value; // $IntegerType()
    var $t7: $Value; // $AddressType()
    var $t8: $Value; // $BooleanType()
    var $t9: $Value; // $BooleanType()
    var $t10: $Value; // $AddressType()
    var $t11: $Value; // $IntegerType()
    var $t12: $Value; // $AddressType()
    var $t13: $Value; // $AddressType()
    var $t14: $Value; // $AddressType()
    var $t15: $Value; // $BooleanType()
    var $t16: $Value; // $BooleanType()
    var $t17: $Value; // $AddressType()
    var $t18: $Value; // $IntegerType()
    var $t19: $Value; // $AddressType()
    var $t20: $Value; // $BooleanType()
    var $t21: $Value; // $LibraConfig_ModifyConfigCapability_type_value($tv0)
    var $t22: $Value; // $AddressType()
    var $t23: $Value; // $AddressType()
    var $t24: $Value; // $tv0
    var $t25: $Value; // $LibraConfig_LibraConfig_type_value($tv0)
    var $t26: $Value; // $AddressType()
    var $t27: $Value; // $tv0
    var $t28: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(11, 5060, 0, config_account); }
    if (true) { assume $DebugTrackLocal(11, 5060, 1, payload); }
    if (true) { assume $DebugTrackLocal(11, 5060, 2, delegate); }

    // bytecode translation starts here
    // $t26 := move(config_account)
    call $tmp := $CopyOrMoveValue(config_account);
    $t26 := $tmp;

    // $t27 := move(payload)
    call $tmp := $CopyOrMoveValue(payload);
    $t27 := $tmp;

    // $t28 := move(delegate)
    call $tmp := $CopyOrMoveValue(delegate);
    $t28 := $tmp;

    // $t7 := copy($t26)
    call $tmp := $CopyOrMoveValue($t26);
    $t7 := $tmp;

    // $t8 := Roles::has_on_chain_config_privilege($t7)
    call $t8 := $Roles_has_on_chain_config_privilege($t7);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 5266);
      goto Abort;
    }
    assume is#$Boolean($t8);


    // $t3 := $t8
    call $tmp := $CopyOrMoveValue($t8);
    $t3 := $tmp;
    if (true) { assume $DebugTrackLocal(11, 5252, 3, $tmp); }

    // if ($t3) goto L0 else goto L1
    $tmp := $t3;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t10 := move($t26)
    call $tmp := $CopyOrMoveValue($t26);
    $t10 := $tmp;

    // destroy($t10)

    // $t11 := 919417
    $tmp := $Integer(919417);
    $t11 := $tmp;

    // abort($t11)
    if (true) { assume $DebugTrackAbort(11, 5252); }
    goto Abort;

    // L0:
L0:

    // $t12 := copy($t26)
    call $tmp := $CopyOrMoveValue($t26);
    $t12 := $tmp;

    // $t13 := Signer::address_of($t12)
    call $t13 := $Signer_address_of($t12);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 5345);
      goto Abort;
    }
    assume is#$Address($t13);


    // $t14 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t14 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 5390);
      goto Abort;
    }
    assume is#$Address($t14);


    // $t15 := ==($t13, $t14)
    $tmp := $Boolean($IsEqual($t13, $t14));
    $t15 := $tmp;

    // $t5 := $t15
    call $tmp := $CopyOrMoveValue($t15);
    $t5 := $tmp;
    if (true) { assume $DebugTrackLocal(11, 5330, 5, $tmp); }

    // if ($t5) goto L2 else goto L3
    $tmp := $t5;
    if (b#$Boolean($tmp)) { goto L2; } else { goto L3; }

    // L3:
L3:

    // $t17 := move($t26)
    call $tmp := $CopyOrMoveValue($t26);
    $t17 := $tmp;

    // destroy($t17)

    // $t18 := 1
    $tmp := $Integer(1);
    $t18 := $tmp;

    // abort($t18)
    if (true) { assume $DebugTrackAbort(11, 5330); }
    goto Abort;

    // L2:
L2:

    // $t19 := copy($t26)
    call $tmp := $CopyOrMoveValue($t26);
    $t19 := $tmp;

    // $t20 := false
    $tmp := $Boolean(false);
    $t20 := $tmp;

    // $t21 := pack LibraConfig::ModifyConfigCapability<#0>($t20)
    call $tmp := $LibraConfig_ModifyConfigCapability_pack(0, 0, 0, $tv0, $t20);
    $t21 := $tmp;

    // Offer::create<LibraConfig::ModifyConfigCapability<#0>>($t19, $t21, $t28)
    call $Offer_create($LibraConfig_ModifyConfigCapability_type_value($tv0), $t19, $t21, $t28);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 5431);
      goto Abort;
    }

    // $t23 := move($t26)
    call $tmp := $CopyOrMoveValue($t26);
    $t23 := $tmp;

    // $t25 := pack LibraConfig::LibraConfig<#0>($t27)
    call $tmp := $LibraConfig_LibraConfig_pack(0, 0, 0, $tv0, $t27);
    $t25 := $tmp;

    // move_to<LibraConfig::LibraConfig<#0>>($t25, $t23)
    call $MoveTo($LibraConfig_LibraConfig_type_value($tv0), $t25, $t23);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 5507);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraConfig_publish_new_config_with_delegate($tv0: $TypeValue, config_account: $Value, payload: $Value, delegate: $Value) returns ()
free requires is#$Address(config_account);
free requires is#$Address(delegate);
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $LibraConfig_publish_new_config_with_delegate_def($tv0, config_account, payload, delegate);
}

procedure {:inline 1} $LibraConfig_publish_new_treasury_compliance_config_def($tv0: $TypeValue, config_account: $Value, tc_account: $Value, payload: $Value) returns (){
    // declare local variables
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $IntegerType()
    var $t5: $Value; // $AddressType()
    var $t6: $Value; // $BooleanType()
    var $t7: $Value; // $BooleanType()
    var $t8: $Value; // $AddressType()
    var $t9: $Value; // $AddressType()
    var $t10: $Value; // $IntegerType()
    var $t11: $Value; // $AddressType()
    var $t12: $Value; // $tv0
    var $t13: $Value; // $LibraConfig_LibraConfig_type_value($tv0)
    var $t14: $Value; // $AddressType()
    var $t15: $Value; // $BooleanType()
    var $t16: $Value; // $LibraConfig_ModifyConfigCapability_type_value($tv0)
    var $t17: $Value; // $AddressType()
    var $t18: $Value; // $AddressType()
    var $t19: $Value; // $tv0
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(11, 3741, 0, config_account); }
    if (true) { assume $DebugTrackLocal(11, 3741, 1, tc_account); }
    if (true) { assume $DebugTrackLocal(11, 3741, 2, payload); }

    // bytecode translation starts here
    // $t17 := move(config_account)
    call $tmp := $CopyOrMoveValue(config_account);
    $t17 := $tmp;

    // $t18 := move(tc_account)
    call $tmp := $CopyOrMoveValue(tc_account);
    $t18 := $tmp;

    // $t19 := move(payload)
    call $tmp := $CopyOrMoveValue(payload);
    $t19 := $tmp;

    // $t5 := copy($t17)
    call $tmp := $CopyOrMoveValue($t17);
    $t5 := $tmp;

    // $t6 := Roles::has_on_chain_config_privilege($t5)
    call $t6 := $Roles_has_on_chain_config_privilege($t5);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 3955);
      goto Abort;
    }
    assume is#$Boolean($t6);


    // $t3 := $t6
    call $tmp := $CopyOrMoveValue($t6);
    $t3 := $tmp;
    if (true) { assume $DebugTrackLocal(11, 3941, 3, $tmp); }

    // if ($t3) goto L0 else goto L1
    $tmp := $t3;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t8 := move($t18)
    call $tmp := $CopyOrMoveValue($t18);
    $t8 := $tmp;

    // destroy($t8)

    // $t9 := move($t17)
    call $tmp := $CopyOrMoveValue($t17);
    $t9 := $tmp;

    // destroy($t9)

    // $t10 := 919415
    $tmp := $Integer(919415);
    $t10 := $tmp;

    // abort($t10)
    if (true) { assume $DebugTrackAbort(11, 3941); }
    goto Abort;

    // L0:
L0:

    // $t11 := move($t17)
    call $tmp := $CopyOrMoveValue($t17);
    $t11 := $tmp;

    // $t13 := pack LibraConfig::LibraConfig<#0>($t19)
    call $tmp := $LibraConfig_LibraConfig_pack(0, 0, 0, $tv0, $t19);
    $t13 := $tmp;

    // move_to<LibraConfig::LibraConfig<#0>>($t13, $t11)
    call $MoveTo($LibraConfig_LibraConfig_type_value($tv0), $t13, $t11);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 4019);
      goto Abort;
    }

    // $t14 := move($t18)
    call $tmp := $CopyOrMoveValue($t18);
    $t14 := $tmp;

    // $t15 := false
    $tmp := $Boolean(false);
    $t15 := $tmp;

    // $t16 := pack LibraConfig::ModifyConfigCapability<#0>($t15)
    call $tmp := $LibraConfig_ModifyConfigCapability_pack(0, 0, 0, $tv0, $t15);
    $t16 := $tmp;

    // move_to<LibraConfig::ModifyConfigCapability<#0>>($t16, $t14)
    call $MoveTo($LibraConfig_ModifyConfigCapability_type_value($tv0), $t16, $t14);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 4077);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraConfig_publish_new_treasury_compliance_config($tv0: $TypeValue, config_account: $Value, tc_account: $Value, payload: $Value) returns ()
free requires is#$Address(config_account);
free requires is#$Address(tc_account);
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $LibraConfig_publish_new_treasury_compliance_config_def($tv0, config_account, tc_account, payload);
}

procedure {:inline 1} $LibraConfig_reconfigure_def(lr_account: $Value) returns (){
    // declare local variables
    var $t1: $Value; // $BooleanType()
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $AddressType()
    var $t4: $Value; // $BooleanType()
    var $t5: $Value; // $BooleanType()
    var $t6: $Value; // $IntegerType()
    var $t7: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(11, 6131, 0, lr_account); }

    // bytecode translation starts here
    // $t7 := move(lr_account)
    call $tmp := $CopyOrMoveValue(lr_account);
    $t7 := $tmp;

    // $t3 := move($t7)
    call $tmp := $CopyOrMoveValue($t7);
    $t3 := $tmp;

    // $t4 := Roles::has_libra_root_role($t3)
    call $t4 := $Roles_has_libra_root_role($t3);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 6338);
      goto Abort;
    }
    assume is#$Boolean($t4);


    // $t1 := $t4
    call $tmp := $CopyOrMoveValue($t4);
    $t1 := $tmp;
    if (true) { assume $DebugTrackLocal(11, 6324, 1, $tmp); }

    // if ($t1) goto L0 else goto L1
    $tmp := $t1;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t6 := 919418
    $tmp := $Integer(919418);
    $t6 := $tmp;

    // abort($t6)
    if (true) { assume $DebugTrackAbort(11, 6324); }
    goto Abort;

    // L0:
L0:

    // LibraConfig::reconfigure_()
    call $LibraConfig_reconfigure_();
    assume $abort_flag == false;

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraConfig_reconfigure(lr_account: $Value) returns ()
free requires is#$Address(lr_account);
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $LibraConfig_reconfigure_def(lr_account);
}

procedure {:inline 1} $LibraConfig_reconfigure__def() returns (){
    // declare local variables
    var config_ref: $Reference; // ReferenceType($LibraConfig_Configuration_type_value())
    var current_block_time: $Value; // $IntegerType()
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $IntegerType()
    var $t4: $Value; // $BooleanType()
    var $t5: $Value; // $AddressType()
    var $t6: $Reference; // ReferenceType($LibraConfig_Configuration_type_value())
    var $t7: $Value; // $IntegerType()
    var $t8: $Value; // $IntegerType()
    var $t9: $Reference; // ReferenceType($LibraConfig_Configuration_type_value())
    var $t10: $Value; // $IntegerType()
    var $t11: $Value; // $IntegerType()
    var $t12: $Value; // $BooleanType()
    var $t13: $Value; // $BooleanType()
    var $t14: $Reference; // ReferenceType($LibraConfig_Configuration_type_value())
    var $t15: $Value; // $IntegerType()
    var $t16: $Value; // $IntegerType()
    var $t17: $Reference; // ReferenceType($LibraConfig_Configuration_type_value())
    var $t18: $Reference; // ReferenceType($IntegerType())
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t4 := LibraTimestamp::is_not_initialized()
    call $t4 := $LibraTimestamp_is_not_initialized();
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 6589);
      goto Abort;
    }
    assume is#$Boolean($t4);


    // if ($t4) goto L0 else goto L1
    $tmp := $t4;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // goto L2
    goto L2;

    // L0:
L0:

    // return ()
    return;

    // L2:
L2:

    // $t5 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t5 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 6717);
      goto Abort;
    }
    assume is#$Address($t5);


    // $t6 := borrow_global<LibraConfig::Configuration>($t5)
    call $t6 := $BorrowGlobal($t5, $LibraConfig_Configuration_type_value());
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 6669);
      goto Abort;
    }
    assume $LibraConfig_Configuration_is_well_formed($Dereference($t6));

    // UnpackRef($t6)

    // config_ref := $t6
    call config_ref := $CopyOrMoveRef($t6);
    if (true) { assume $DebugTrackLocal(11, 6656, 0, $Dereference(config_ref)); }

    // $t7 := LibraTimestamp::now_microseconds()
    call $t7 := $LibraTimestamp_now_microseconds();
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 6991);
      goto Abort;
    }
    assume $IsValidU64($t7);


    // current_block_time := $t7
    call $tmp := $CopyOrMoveValue($t7);
    current_block_time := $tmp;
    if (true) { assume $DebugTrackLocal(11, 6954, 1, $tmp); }

    // $t9 := copy(config_ref)
    call $t9 := $CopyOrMoveRef(config_ref);

    // $t10 := get_field<LibraConfig::Configuration>.last_reconfiguration_time($t9)
    call $tmp := $GetFieldFromReference($t9, $LibraConfig_Configuration_last_reconfiguration_time);
    assume $IsValidU64($tmp);
    $t10 := $tmp;

    // Reference(config_ref) <- $t9
    call config_ref := $WritebackToReference($t9, config_ref);

    // $t11 := move($t10)
    call $tmp := $CopyOrMoveValue($t10);
    $t11 := $tmp;

    // $t12 := >(current_block_time, $t11)
    call $tmp := $Gt(current_block_time, $t11);
    $t12 := $tmp;

    // $t2 := $t12
    call $tmp := $CopyOrMoveValue($t12);
    $t2 := $tmp;
    if (true) { assume $DebugTrackLocal(11, 7018, 2, $tmp); }

    // if ($t2) goto L3 else goto L4
    $tmp := $t2;
    if (b#$Boolean($tmp)) { goto L3; } else { goto L4; }

    // L4:
L4:

    // $t14 := move(config_ref)
    call $t14 := $CopyOrMoveRef(config_ref);

    // destroy($t14)

    // LibraConfig::Configuration <- $t14
    call $WritebackToGlobal($t14);

    // PackRef($t14)

    // $t15 := 23
    $tmp := $Integer(23);
    $t15 := $tmp;

    // abort($t15)
    if (true) { assume $DebugTrackAbort(11, 7018); }
    goto Abort;

    // L3:
L3:

    // $t17 := move(config_ref)
    call $t17 := $CopyOrMoveRef(config_ref);

    // $t18 := borrow_field<LibraConfig::Configuration>.last_reconfiguration_time($t17)
    call $t18 := $BorrowField($t17, $LibraConfig_Configuration_last_reconfiguration_time);
    assume $IsValidU64($Dereference($t18));

    // LibraConfig::Configuration <- $t17
    call $WritebackToGlobal($t17);

    // UnpackRef($t18)

    // write_ref($t18, current_block_time)
    call $t18 := $WriteRef($t18, current_block_time);
    if (true) { assume $DebugTrackLocal(11, 7096, 0, $Dereference(config_ref)); }

    // LibraConfig::Configuration <- $t18
    call $WritebackToGlobal($t18);

    // Reference($t17) <- $t18
    call $t17 := $WritebackToReference($t18, $t17);

    // PackRef($t17)

    // PackRef($t18)

    // LibraConfig::emit_reconfiguration_event()
    call $LibraConfig_emit_reconfiguration_event();
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 8106);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraConfig_reconfigure_() returns ()
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $LibraConfig_reconfigure__def();
}

procedure {:inline 1} $LibraConfig_set_def($tv0: $TypeValue, account: $Value, payload: $Value) returns (){
    // declare local variables
    var addr: $Value; // $AddressType()
    var config: $Reference; // ReferenceType($LibraConfig_LibraConfig_type_value($tv0))
    var signer_address: $Value; // $AddressType()
    var $t5: $Value; // $BooleanType()
    var $t6: $Value; // $IntegerType()
    var $t7: $Value; // $BooleanType()
    var $t8: $Value; // $IntegerType()
    var $t9: $Value; // $AddressType()
    var $t10: $Value; // $AddressType()
    var $t11: $Value; // $BooleanType()
    var $t12: $Value; // $BooleanType()
    var $t13: $Value; // $AddressType()
    var $t14: $Value; // $IntegerType()
    var $t15: $Value; // $AddressType()
    var $t16: $Value; // $AddressType()
    var $t17: $Value; // $AddressType()
    var $t18: $Value; // $BooleanType()
    var $t19: $Value; // $BooleanType()
    var $t20: $Value; // $IntegerType()
    var $t21: $Value; // $AddressType()
    var $t22: $Reference; // ReferenceType($LibraConfig_LibraConfig_type_value($tv0))
    var $t23: $Value; // $tv0
    var $t24: $Reference; // ReferenceType($LibraConfig_LibraConfig_type_value($tv0))
    var $t25: $Reference; // ReferenceType($tv0)
    var $t26: $Value; // $AddressType()
    var $t27: $Value; // $tv0
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(11, 1794, 0, account); }
    if (true) { assume $DebugTrackLocal(11, 1794, 1, payload); }

    // bytecode translation starts here
    // $t26 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t26 := $tmp;

    // $t27 := move(payload)
    call $tmp := $CopyOrMoveValue(payload);
    $t27 := $tmp;

    // $t9 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t9 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 1934);
      goto Abort;
    }
    assume is#$Address($t9);


    // addr := $t9
    call $tmp := $CopyOrMoveValue($t9);
    addr := $tmp;
    if (true) { assume $DebugTrackLocal(11, 1912, 2, $tmp); }

    // $t11 := exists<LibraConfig::LibraConfig<#0>>(addr)
    call $tmp := $Exists(addr, $LibraConfig_LibraConfig_type_value($tv0));
    $t11 := $tmp;

    // $t5 := $t11
    call $tmp := $CopyOrMoveValue($t11);
    $t5 := $tmp;
    if (true) { assume $DebugTrackLocal(11, 1964, 5, $tmp); }

    // if ($t5) goto L0 else goto L1
    $tmp := $t5;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t13 := move($t26)
    call $tmp := $CopyOrMoveValue($t26);
    $t13 := $tmp;

    // destroy($t13)

    // $t14 := 24
    $tmp := $Integer(24);
    $t14 := $tmp;

    // abort($t14)
    if (true) { assume $DebugTrackAbort(11, 1964); }
    goto Abort;

    // L0:
L0:

    // $t15 := move($t26)
    call $tmp := $CopyOrMoveValue($t26);
    $t15 := $tmp;

    // $t16 := Signer::address_of($t15)
    call $t16 := $Signer_address_of($t15);
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 2048);
      goto Abort;
    }
    assume is#$Address($t16);


    // signer_address := $t16
    call $tmp := $CopyOrMoveValue($t16);
    signer_address := $tmp;
    if (true) { assume $DebugTrackLocal(11, 2023, 4, $tmp); }

    // $t18 := exists<LibraConfig::ModifyConfigCapability<#0>>(signer_address)
    call $tmp := $Exists(signer_address, $LibraConfig_ModifyConfigCapability_type_value($tv0));
    $t18 := $tmp;

    // $t7 := $t18
    call $tmp := $CopyOrMoveValue($t18);
    $t7 := $tmp;
    if (true) { assume $DebugTrackLocal(11, 2077, 7, $tmp); }

    // if ($t7) goto L2 else goto L3
    $tmp := $t7;
    if (b#$Boolean($tmp)) { goto L2; } else { goto L3; }

    // L3:
L3:

    // $t20 := 24
    $tmp := $Integer(24);
    $t20 := $tmp;

    // abort($t20)
    if (true) { assume $DebugTrackAbort(11, 2077); }
    goto Abort;

    // L2:
L2:

    // $t22 := borrow_global<LibraConfig::LibraConfig<#0>>(addr)
    call $t22 := $BorrowGlobal(addr, $LibraConfig_LibraConfig_type_value($tv0));
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 2167);
      goto Abort;
    }
    assume $LibraConfig_LibraConfig_is_well_formed($Dereference($t22));

    // UnpackRef($t22)

    // config := $t22
    call config := $CopyOrMoveRef($t22);
    if (true) { assume $DebugTrackLocal(11, 2158, 3, $Dereference(config)); }

    // $t24 := move(config)
    call $t24 := $CopyOrMoveRef(config);

    // $t25 := borrow_field<LibraConfig::LibraConfig<#0>>.payload($t24)
    call $t25 := $BorrowField($t24, $LibraConfig_LibraConfig_payload);

    // LibraConfig::LibraConfig <- $t24
    call $WritebackToGlobal($t24);

    // UnpackRef($t25)

    // write_ref($t25, $t27)
    call $t25 := $WriteRef($t25, $t27);
    if (true) { assume $DebugTrackLocal(11, 2221, 3, $Dereference(config)); }

    // LibraConfig::LibraConfig <- $t25
    call $WritebackToGlobal($t25);

    // Reference($t24) <- $t25
    call $t24 := $WritebackToReference($t25, $t24);

    // PackRef($t24)

    // PackRef($t25)

    // LibraConfig::reconfigure_()
    call $LibraConfig_reconfigure_();
    assume $abort_flag == false;

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraConfig_set($tv0: $TypeValue, account: $Value, payload: $Value) returns ()
free requires is#$Address(account);
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $LibraConfig_set_def($tv0, account, payload);
}

procedure {:inline 1} $LibraConfig_set_with_capability_def($tv0: $TypeValue, _cap: $Value, payload: $Value) returns (){
    // declare local variables
    var addr: $Value; // $AddressType()
    var config: $Reference; // ReferenceType($LibraConfig_LibraConfig_type_value($tv0))
    var $t4: $Value; // $BooleanType()
    var $t5: $Value; // $IntegerType()
    var $t6: $Value; // $AddressType()
    var $t7: $Value; // $AddressType()
    var $t8: $Value; // $BooleanType()
    var $t9: $Value; // $BooleanType()
    var $t10: $Value; // $IntegerType()
    var $t11: $Value; // $AddressType()
    var $t12: $Reference; // ReferenceType($LibraConfig_LibraConfig_type_value($tv0))
    var $t13: $Value; // $tv0
    var $t14: $Reference; // ReferenceType($LibraConfig_LibraConfig_type_value($tv0))
    var $t15: $Reference; // ReferenceType($tv0)
    var $t16: $Value; // $LibraConfig_ModifyConfigCapability_type_value($tv0)
    var $t17: $Value; // $tv0
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(11, 2354, 0, _cap); }
    if (true) { assume $DebugTrackLocal(11, 2354, 1, payload); }

    // bytecode translation starts here
    // $t16 := move(_cap)
    call $tmp := $CopyOrMoveValue(_cap);
    $t16 := $tmp;

    // $t17 := move(payload)
    call $tmp := $CopyOrMoveValue(payload);
    $t17 := $tmp;

    // $t6 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t6 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 2553);
      goto Abort;
    }
    assume is#$Address($t6);


    // addr := $t6
    call $tmp := $CopyOrMoveValue($t6);
    addr := $tmp;
    if (true) { assume $DebugTrackLocal(11, 2531, 2, $tmp); }

    // $t8 := exists<LibraConfig::LibraConfig<#0>>(addr)
    call $tmp := $Exists(addr, $LibraConfig_LibraConfig_type_value($tv0));
    $t8 := $tmp;

    // $t4 := $t8
    call $tmp := $CopyOrMoveValue($t8);
    $t4 := $tmp;
    if (true) { assume $DebugTrackLocal(11, 2583, 4, $tmp); }

    // if ($t4) goto L0 else goto L1
    $tmp := $t4;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t10 := 24
    $tmp := $Integer(24);
    $t10 := $tmp;

    // abort($t10)
    if (true) { assume $DebugTrackAbort(11, 2583); }
    goto Abort;

    // L0:
L0:

    // $t12 := borrow_global<LibraConfig::LibraConfig<#0>>(addr)
    call $t12 := $BorrowGlobal(addr, $LibraConfig_LibraConfig_type_value($tv0));
    if ($abort_flag) {
      assume $DebugTrackAbort(11, 2651);
      goto Abort;
    }
    assume $LibraConfig_LibraConfig_is_well_formed($Dereference($t12));

    // UnpackRef($t12)

    // config := $t12
    call config := $CopyOrMoveRef($t12);
    if (true) { assume $DebugTrackLocal(11, 2642, 3, $Dereference(config)); }

    // $t14 := move(config)
    call $t14 := $CopyOrMoveRef(config);

    // $t15 := borrow_field<LibraConfig::LibraConfig<#0>>.payload($t14)
    call $t15 := $BorrowField($t14, $LibraConfig_LibraConfig_payload);

    // LibraConfig::LibraConfig <- $t14
    call $WritebackToGlobal($t14);

    // UnpackRef($t15)

    // write_ref($t15, $t17)
    call $t15 := $WriteRef($t15, $t17);
    if (true) { assume $DebugTrackLocal(11, 2705, 3, $Dereference(config)); }

    // LibraConfig::LibraConfig <- $t15
    call $WritebackToGlobal($t15);

    // Reference($t14) <- $t15
    call $t14 := $WritebackToReference($t15, $t14);

    // PackRef($t14)

    // PackRef($t15)

    // LibraConfig::reconfigure_()
    call $LibraConfig_reconfigure_();
    assume $abort_flag == false;

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraConfig_set_with_capability($tv0: $TypeValue, _cap: $Value, payload: $Value) returns ()
free requires $LibraConfig_ModifyConfigCapability_is_well_formed(_cap);
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $LibraConfig_set_with_capability_def($tv0, _cap, payload);
}



// ** spec vars of module RegisteredCurrencies



// ** spec funs of module RegisteredCurrencies

function {:inline} $RegisteredCurrencies_get_currency_codes($m: $Memory, $txn: $Transaction): $Value {
    $SelectField($LibraConfig_spec_get($m, $txn, $RegisteredCurrencies_RegisteredCurrencies_type_value()), $RegisteredCurrencies_RegisteredCurrencies_currency_codes)
}



// ** structs of module RegisteredCurrencies

const unique $RegisteredCurrencies_RegisteredCurrencies: $TypeName;
const $RegisteredCurrencies_RegisteredCurrencies_currency_codes: $FieldName;
axiom $RegisteredCurrencies_RegisteredCurrencies_currency_codes == 0;
function $RegisteredCurrencies_RegisteredCurrencies_type_value(): $TypeValue {
    $StructType($RegisteredCurrencies_RegisteredCurrencies, $TypeValueArray($MapConstTypeValue($DefaultTypeValue()), 0), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $Vector_type_value($Vector_type_value($IntegerType()))], 1))
}
function {:inline} $RegisteredCurrencies_RegisteredCurrencies_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $Vector_is_well_formed($SelectField($this, $RegisteredCurrencies_RegisteredCurrencies_currency_codes)) && (forall $$0: int :: {$select_vector($SelectField($this, $RegisteredCurrencies_RegisteredCurrencies_currency_codes),$$0)} $$0 >= 0 && $$0 < $vlen($SelectField($this, $RegisteredCurrencies_RegisteredCurrencies_currency_codes)) ==> $Vector_is_well_formed($select_vector($SelectField($this, $RegisteredCurrencies_RegisteredCurrencies_currency_codes),$$0)) && (forall $$1: int :: {$select_vector($select_vector($SelectField($this, $RegisteredCurrencies_RegisteredCurrencies_currency_codes),$$0),$$1)} $$1 >= 0 && $$1 < $vlen($select_vector($SelectField($this, $RegisteredCurrencies_RegisteredCurrencies_currency_codes),$$0)) ==> $IsValidU8($select_vector($select_vector($SelectField($this, $RegisteredCurrencies_RegisteredCurrencies_currency_codes),$$0),$$1))))
}
function {:inline} $RegisteredCurrencies_RegisteredCurrencies_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $Vector_is_well_formed($SelectField($this, $RegisteredCurrencies_RegisteredCurrencies_currency_codes)) && (forall $$0: int :: {$select_vector($SelectField($this, $RegisteredCurrencies_RegisteredCurrencies_currency_codes),$$0)} $$0 >= 0 && $$0 < $vlen($SelectField($this, $RegisteredCurrencies_RegisteredCurrencies_currency_codes)) ==> $Vector_is_well_formed($select_vector($SelectField($this, $RegisteredCurrencies_RegisteredCurrencies_currency_codes),$$0)) && (forall $$1: int :: {$select_vector($select_vector($SelectField($this, $RegisteredCurrencies_RegisteredCurrencies_currency_codes),$$0),$$1)} $$1 >= 0 && $$1 < $vlen($select_vector($SelectField($this, $RegisteredCurrencies_RegisteredCurrencies_currency_codes),$$0)) ==> $IsValidU8($select_vector($select_vector($SelectField($this, $RegisteredCurrencies_RegisteredCurrencies_currency_codes),$$0),$$1))))
}

procedure {:inline 1} $RegisteredCurrencies_RegisteredCurrencies_pack($file_id: int, $byte_index: int, $var_idx: int, currency_codes: $Value) returns ($struct: $Value)
{
    assume $Vector_is_well_formed(currency_codes) && (forall $$0: int :: {$select_vector(currency_codes,$$0)} $$0 >= 0 && $$0 < $vlen(currency_codes) ==> $Vector_is_well_formed($select_vector(currency_codes,$$0)) && (forall $$1: int :: {$select_vector($select_vector(currency_codes,$$0),$$1)} $$1 >= 0 && $$1 < $vlen($select_vector(currency_codes,$$0)) ==> $IsValidU8($select_vector($select_vector(currency_codes,$$0),$$1))));
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := currency_codes], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $RegisteredCurrencies_RegisteredCurrencies_unpack($struct: $Value) returns (currency_codes: $Value)
{
    assume is#$Vector($struct);
    currency_codes := $SelectField($struct, $RegisteredCurrencies_RegisteredCurrencies_currency_codes);
    assume $Vector_is_well_formed(currency_codes) && (forall $$0: int :: {$select_vector(currency_codes,$$0)} $$0 >= 0 && $$0 < $vlen(currency_codes) ==> $Vector_is_well_formed($select_vector(currency_codes,$$0)) && (forall $$1: int :: {$select_vector($select_vector(currency_codes,$$0),$$1)} $$1 >= 0 && $$1 < $vlen($select_vector(currency_codes,$$0)) ==> $IsValidU8($select_vector($select_vector(currency_codes,$$0),$$1))));
}

const unique $RegisteredCurrencies_RegistrationCapability: $TypeName;
const $RegisteredCurrencies_RegistrationCapability_cap: $FieldName;
axiom $RegisteredCurrencies_RegistrationCapability_cap == 0;
function $RegisteredCurrencies_RegistrationCapability_type_value(): $TypeValue {
    $StructType($RegisteredCurrencies_RegistrationCapability, $TypeValueArray($MapConstTypeValue($DefaultTypeValue()), 0), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $LibraConfig_ModifyConfigCapability_type_value($RegisteredCurrencies_RegisteredCurrencies_type_value())], 1))
}
function {:inline} $RegisteredCurrencies_RegistrationCapability_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $LibraConfig_ModifyConfigCapability_is_well_formed_types($SelectField($this, $RegisteredCurrencies_RegistrationCapability_cap))
}
function {:inline} $RegisteredCurrencies_RegistrationCapability_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $LibraConfig_ModifyConfigCapability_is_well_formed($SelectField($this, $RegisteredCurrencies_RegistrationCapability_cap))
}

axiom (forall m: $Memory, a: $Value :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $RegisteredCurrencies_RegistrationCapability_is_well_formed($ResourceValue(m, $RegisteredCurrencies_RegistrationCapability_type_value(), a))
);

procedure {:inline 1} $RegisteredCurrencies_RegistrationCapability_pack($file_id: int, $byte_index: int, $var_idx: int, cap: $Value) returns ($struct: $Value)
{
    assume $LibraConfig_ModifyConfigCapability_is_well_formed(cap);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := cap], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $RegisteredCurrencies_RegistrationCapability_unpack($struct: $Value) returns (cap: $Value)
{
    assume is#$Vector($struct);
    cap := $SelectField($struct, $RegisteredCurrencies_RegistrationCapability_cap);
    assume $LibraConfig_ModifyConfigCapability_is_well_formed(cap);
}



// ** functions of module RegisteredCurrencies

procedure {:inline 1} $RegisteredCurrencies_initialize_def(config_account: $Value) returns ($ret0: $Value){
    // declare local variables
    var cap: $Value; // $LibraConfig_ModifyConfigCapability_type_value($RegisteredCurrencies_RegisteredCurrencies_type_value())
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $IntegerType()
    var $t4: $Value; // $AddressType()
    var $t5: $Value; // $AddressType()
    var $t6: $Value; // $AddressType()
    var $t7: $Value; // $BooleanType()
    var $t8: $Value; // $BooleanType()
    var $t9: $Value; // $AddressType()
    var $t10: $Value; // $IntegerType()
    var $t11: $Value; // $AddressType()
    var $t12: $Value; // $Vector_type_value($Vector_type_value($IntegerType()))
    var $t13: $Value; // $RegisteredCurrencies_RegisteredCurrencies_type_value()
    var $t14: $Value; // $LibraConfig_ModifyConfigCapability_type_value($RegisteredCurrencies_RegisteredCurrencies_type_value())
    var $t15: $Value; // $LibraConfig_ModifyConfigCapability_type_value($RegisteredCurrencies_RegisteredCurrencies_type_value())
    var $t16: $Value; // $RegisteredCurrencies_RegistrationCapability_type_value()
    var $t17: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(14, 820, 0, config_account); }

    // bytecode translation starts here
    // $t17 := move(config_account)
    call $tmp := $CopyOrMoveValue(config_account);
    $t17 := $tmp;

    // LibraTimestamp::assert_is_genesis()
    call $LibraTimestamp_assert_is_genesis();
    if ($abort_flag) {
      assume $DebugTrackAbort(14, 199);
      goto Abort;
    }

    // $t4 := copy($t17)
    call $tmp := $CopyOrMoveValue($t17);
    $t4 := $tmp;

    // $t5 := Signer::address_of($t4)
    call $t5 := $Signer_address_of($t4);
    if ($abort_flag) {
      assume $DebugTrackAbort(14, 974);
      goto Abort;
    }
    assume is#$Address($t5);


    // $t6 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t6 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(14, 1019);
      goto Abort;
    }
    assume is#$Address($t6);


    // $t7 := ==($t5, $t6)
    $tmp := $Boolean($IsEqual($t5, $t6));
    $t7 := $tmp;

    // $t2 := $t7
    call $tmp := $CopyOrMoveValue($t7);
    $t2 := $tmp;
    if (true) { assume $DebugTrackLocal(14, 946, 2, $tmp); }

    // if ($t2) goto L0 else goto L1
    $tmp := $t2;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t9 := move($t17)
    call $tmp := $CopyOrMoveValue($t17);
    $t9 := $tmp;

    // destroy($t9)

    // $t10 := 0
    $tmp := $Integer(0);
    $t10 := $tmp;

    // abort($t10)
    if (true) { assume $DebugTrackAbort(14, 946); }
    goto Abort;

    // L0:
L0:

    // $t11 := move($t17)
    call $tmp := $CopyOrMoveValue($t17);
    $t11 := $tmp;

    // $t12 := Vector::empty<vector<u8>>()
    call $t12 := $Vector_empty($Vector_type_value($IntegerType()));
    if ($abort_flag) {
      assume $DebugTrackAbort(14, 1220);
      goto Abort;
    }
    assume $Vector_is_well_formed($t12) && (forall $$0: int :: {$select_vector($t12,$$0)} $$0 >= 0 && $$0 < $vlen($t12) ==> $Vector_is_well_formed($select_vector($t12,$$0)) && (forall $$1: int :: {$select_vector($select_vector($t12,$$0),$$1)} $$1 >= 0 && $$1 < $vlen($select_vector($t12,$$0)) ==> $IsValidU8($select_vector($select_vector($t12,$$0),$$1))));


    // $t13 := pack RegisteredCurrencies::RegisteredCurrencies($t12)
    call $tmp := $RegisteredCurrencies_RegisteredCurrencies_pack(0, 0, 0, $t12);
    $t13 := $tmp;

    // $t14 := LibraConfig::publish_new_config_with_capability<RegisteredCurrencies::RegisteredCurrencies>($t11, $t13)
    call $t14 := $LibraConfig_publish_new_config_with_capability($RegisteredCurrencies_RegisteredCurrencies_type_value(), $t11, $t13);
    if ($abort_flag) {
      assume $DebugTrackAbort(14, 1097);
      goto Abort;
    }
    assume $LibraConfig_ModifyConfigCapability_is_well_formed($t14);


    // cap := $t14
    call $tmp := $CopyOrMoveValue($t14);
    cap := $tmp;
    if (true) { assume $DebugTrackLocal(14, 1078, 1, $tmp); }

    // $t16 := pack RegisteredCurrencies::RegistrationCapability(cap)
    call $tmp := $RegisteredCurrencies_RegistrationCapability_pack(0, 0, 0, cap);
    $t16 := $tmp;

    // return $t16
    $ret0 := $t16;
    if (true) { assume $DebugTrackLocal(14, 1250, 18, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $RegisteredCurrencies_initialize(config_account: $Value) returns ($ret0: $Value)
free requires is#$Address(config_account);
requires $ExistsTxnSenderAccount($m, $txn);
requires b#$Boolean($Boolean(b#$Boolean($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn)))) ==> b#$Boolean($LibraConfig_spec_is_published($m, $txn, $RegisteredCurrencies_RegisteredCurrencies_type_value()))))
    || b#$Boolean($Boolean(!$IsEqual($Signer_spec_address_of($m, $txn, config_account), $CoreAddresses_SPEC_LIBRA_ROOT_ADDRESS())))
    || b#$Boolean($LibraConfig_spec_is_published($m, $txn, $RegisteredCurrencies_RegisteredCurrencies_type_value()))
    || b#$Boolean($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn))));
free ensures b#$Boolean(old($Boolean(!$IsEqual($Signer_spec_address_of($m, $txn, config_account), $CoreAddresses_SPEC_LIBRA_ROOT_ADDRESS())))) ==> $abort_flag;
free ensures b#$Boolean(old($LibraConfig_spec_is_published($m, $txn, $RegisteredCurrencies_RegisteredCurrencies_type_value()))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn))))) ==> $abort_flag;
free ensures !$abort_flag ==> (b#$Boolean($LibraConfig_spec_is_published($m, $txn, $RegisteredCurrencies_RegisteredCurrencies_type_value())));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($vlen_value($RegisteredCurrencies_get_currency_codes($m, $txn)), $Integer(0)))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn)))) ==> b#$Boolean($LibraConfig_spec_is_published($m, $txn, $RegisteredCurrencies_RegisteredCurrencies_type_value())))));
{
    call $ret0 := $RegisteredCurrencies_initialize_def(config_account);
}

procedure {:inline 1} $RegisteredCurrencies_add_currency_code_def(currency_code: $Value, cap: $Value) returns (){
    // declare local variables
    var config: $Value; // $RegisteredCurrencies_RegisteredCurrencies_type_value()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $IntegerType()
    var $t5: $Value; // $RegisteredCurrencies_RegisteredCurrencies_type_value()
    var $t6: $Value; // $RegisteredCurrencies_RegisteredCurrencies_type_value()
    var $t7: $Value; // $Vector_type_value($Vector_type_value($IntegerType()))
    var $t8: $Value; // $Vector_type_value($IntegerType())
    var $t9: $Value; // $BooleanType()
    var $t10: $Value; // $BooleanType()
    var $t11: $Value; // $BooleanType()
    var $t12: $Value; // $RegisteredCurrencies_RegistrationCapability_type_value()
    var $t13: $Value; // $IntegerType()
    var $t14: $Reference; // ReferenceType($RegisteredCurrencies_RegisteredCurrencies_type_value())
    var $t15: $Reference; // ReferenceType($Vector_type_value($Vector_type_value($IntegerType())))
    var $t16: $Value; // $Vector_type_value($IntegerType())
    var $t17: $Value; // $RegisteredCurrencies_RegistrationCapability_type_value()
    var $t18: $Value; // $LibraConfig_ModifyConfigCapability_type_value($RegisteredCurrencies_RegisteredCurrencies_type_value())
    var $t19: $Value; // $RegisteredCurrencies_RegisteredCurrencies_type_value()
    var $t20: $Value; // $Vector_type_value($IntegerType())
    var $t21: $Value; // $RegisteredCurrencies_RegistrationCapability_type_value()
    var $t22: $Value; // $Vector_type_value($Vector_type_value($IntegerType()))
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(14, 2052, 0, currency_code); }
    if (true) { assume $DebugTrackLocal(14, 2052, 1, cap); }

    // bytecode translation starts here
    // $t20 := move(currency_code)
    call $tmp := $CopyOrMoveValue(currency_code);
    $t20 := $tmp;

    // $t21 := move(cap)
    call $tmp := $CopyOrMoveValue(cap);
    $t21 := $tmp;

    // $t5 := LibraConfig::get<RegisteredCurrencies::RegisteredCurrencies>()
    call $t5 := $LibraConfig_get($RegisteredCurrencies_RegisteredCurrencies_type_value());
    if ($abort_flag) {
      assume $DebugTrackAbort(14, 2197);
      goto Abort;
    }
    assume $RegisteredCurrencies_RegisteredCurrencies_is_well_formed($t5);


    // config := $t5
    call $tmp := $CopyOrMoveValue($t5);
    config := $tmp;
    if (true) { assume $DebugTrackLocal(14, 2175, 2, $tmp); }

    // $t6 := copy(config)
    call $tmp := $CopyOrMoveValue(config);
    $t6 := $tmp;

    // $t7 := get_field<RegisteredCurrencies::RegisteredCurrencies>.currency_codes($t6)
    call $tmp := $GetFieldFromValue($t6, $RegisteredCurrencies_RegisteredCurrencies_currency_codes);
    assume $Vector_is_well_formed($tmp) && (forall $$0: int :: {$select_vector($tmp,$$0)} $$0 >= 0 && $$0 < $vlen($tmp) ==> $Vector_is_well_formed($select_vector($tmp,$$0)) && (forall $$1: int :: {$select_vector($select_vector($tmp,$$0),$$1)} $$1 >= 0 && $$1 < $vlen($select_vector($tmp,$$0)) ==> $IsValidU8($select_vector($select_vector($tmp,$$0),$$1))));
    $t7 := $tmp;

    // $t8 := copy($t20)
    call $tmp := $CopyOrMoveValue($t20);
    $t8 := $tmp;

    // $t9 := Vector::contains<vector<u8>>($t7, $t8)
    call $t9 := $Vector_contains($Vector_type_value($IntegerType()), $t7, $t8);
    if ($abort_flag) {
      assume $DebugTrackAbort(14, 2263);
      goto Abort;
    }
    assume is#$Boolean($t9);


    // $t10 := !($t9)
    call $tmp := $Not($t9);
    $t10 := $tmp;

    // $t3 := $t10
    call $tmp := $CopyOrMoveValue($t10);
    $t3 := $tmp;
    if (true) { assume $DebugTrackLocal(14, 2234, 3, $tmp); }

    // if ($t3) goto L0 else goto L1
    $tmp := $t3;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t12 := move($t21)
    call $tmp := $CopyOrMoveValue($t21);
    $t12 := $tmp;

    // destroy($t12)

    // $t13 := 1
    $tmp := $Integer(1);
    $t13 := $tmp;

    // abort($t13)
    if (true) { assume $DebugTrackAbort(14, 2234); }
    goto Abort;

    // L0:
L0:

    // $t14 := borrow_local(config)
    call $t14 := $BorrowLoc(2, config);
    assume $RegisteredCurrencies_RegisteredCurrencies_is_well_formed($Dereference($t14));

    // UnpackRef($t14)

    // $t15 := borrow_field<RegisteredCurrencies::RegisteredCurrencies>.currency_codes($t14)
    call $t15 := $BorrowField($t14, $RegisteredCurrencies_RegisteredCurrencies_currency_codes);
    assume $Vector_is_well_formed($Dereference($t15)) && (forall $$1: int :: {$select_vector($Dereference($t15),$$1)} $$1 >= 0 && $$1 < $vlen($Dereference($t15)) ==> $Vector_is_well_formed($select_vector($Dereference($t15),$$1)) && (forall $$2: int :: {$select_vector($select_vector($Dereference($t15),$$1),$$2)} $$2 >= 0 && $$2 < $vlen($select_vector($Dereference($t15),$$1)) ==> $IsValidU8($select_vector($select_vector($Dereference($t15),$$1),$$2))));

    // LocalRoot(config) <- $t14
    call config := $WritebackToValue($t14, 2, config);

    // UnpackRef($t15)

    // PackRef($t15)

    // $t22 := read_ref($t15)
    call $tmp := $ReadRef($t15);
    assume $Vector_is_well_formed($tmp) && (forall $$0: int :: {$select_vector($tmp,$$0)} $$0 >= 0 && $$0 < $vlen($tmp) ==> $Vector_is_well_formed($select_vector($tmp,$$0)) && (forall $$1: int :: {$select_vector($select_vector($tmp,$$0),$$1)} $$1 >= 0 && $$1 < $vlen($select_vector($tmp,$$0)) ==> $IsValidU8($select_vector($select_vector($tmp,$$0),$$1))));
    $t22 := $tmp;

    // $t22 := Vector::push_back<vector<u8>>($t22, $t20)
    call $t22 := $Vector_push_back($Vector_type_value($IntegerType()), $t22, $t20);
    if ($abort_flag) {
      assume $DebugTrackAbort(14, 2354);
      goto Abort;
    }
    assume $Vector_is_well_formed($t22) && (forall $$0: int :: {$select_vector($t22,$$0)} $$0 >= 0 && $$0 < $vlen($t22) ==> $Vector_is_well_formed($select_vector($t22,$$0)) && (forall $$1: int :: {$select_vector($select_vector($t22,$$0),$$1)} $$1 >= 0 && $$1 < $vlen($select_vector($t22,$$0)) ==> $IsValidU8($select_vector($select_vector($t22,$$0),$$1))));


    // write_ref($t15, $t22)
    call $t15 := $WriteRef($t15, $t22);

    // LocalRoot(config) <- $t15
    call config := $WritebackToValue($t15, 2, config);

    // Reference($t14) <- $t15
    call $t14 := $WritebackToReference($t15, $t14);

    // UnpackRef($t15)

    // PackRef($t14)

    // PackRef($t15)

    // $t17 := move($t21)
    call $tmp := $CopyOrMoveValue($t21);
    $t17 := $tmp;

    // $t18 := get_field<RegisteredCurrencies::RegistrationCapability>.cap($t17)
    call $tmp := $GetFieldFromValue($t17, $RegisteredCurrencies_RegistrationCapability_cap);
    assume $LibraConfig_ModifyConfigCapability_is_well_formed($tmp);
    $t18 := $tmp;

    // LibraConfig::set_with_capability<RegisteredCurrencies::RegisteredCurrencies>($t18, config)
    call $LibraConfig_set_with_capability($RegisteredCurrencies_RegisteredCurrencies_type_value(), $t18, config);
    if ($abort_flag) {
      assume $DebugTrackAbort(14, 2429);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $RegisteredCurrencies_add_currency_code(currency_code: $Value, cap: $Value) returns ()
free requires $Vector_is_well_formed(currency_code) && (forall $$0: int :: {$select_vector(currency_code,$$0)} $$0 >= 0 && $$0 < $vlen(currency_code) ==> $IsValidU8($select_vector(currency_code,$$0)));
free requires $RegisteredCurrencies_RegistrationCapability_is_well_formed(cap);
requires $ExistsTxnSenderAccount($m, $txn);
requires b#$Boolean($Boolean(b#$Boolean($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn)))) ==> b#$Boolean($LibraConfig_spec_is_published($m, $txn, $RegisteredCurrencies_RegisteredCurrencies_type_value()))))
    || b#$Boolean($Boolean(!b#$Boolean($LibraConfig_spec_is_published($m, $txn, $RegisteredCurrencies_RegisteredCurrencies_type_value()))))
    || b#$Boolean($Vector_spec_contains($Vector_type_value($IntegerType()), $SelectField($LibraConfig_spec_get($m, $txn, $RegisteredCurrencies_RegisteredCurrencies_type_value()), $RegisteredCurrencies_RegisteredCurrencies_currency_codes), currency_code));
free ensures b#$Boolean(old($Boolean(!b#$Boolean($LibraConfig_spec_is_published($m, $txn, $RegisteredCurrencies_RegisteredCurrencies_type_value()))))) ==> $abort_flag;
free ensures b#$Boolean(old($Vector_spec_contains($Vector_type_value($IntegerType()), $SelectField($LibraConfig_spec_get($m, $txn, $RegisteredCurrencies_RegisteredCurrencies_type_value()), $RegisteredCurrencies_RegisteredCurrencies_currency_codes), currency_code))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(!b#$Boolean($LibraConfig_spec_is_published($m, $txn, $RegisteredCurrencies_RegisteredCurrencies_type_value()))))))
    || b#$Boolean(old(($Vector_spec_contains($Vector_type_value($IntegerType()), $SelectField($LibraConfig_spec_get($m, $txn, $RegisteredCurrencies_RegisteredCurrencies_type_value()), $RegisteredCurrencies_RegisteredCurrencies_currency_codes), currency_code)))));
free ensures !$abort_flag ==> (b#$Boolean($Vector_eq_push_back($Vector_type_value($IntegerType()), $RegisteredCurrencies_get_currency_codes($m, $txn), old($RegisteredCurrencies_get_currency_codes($m, $txn)), currency_code)));
free ensures !$abort_flag ==> (b#$Boolean($Boolean(b#$Boolean($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn)))) ==> b#$Boolean($LibraConfig_spec_is_published($m, $txn, $RegisteredCurrencies_RegisteredCurrencies_type_value())))));
{
    call $RegisteredCurrencies_add_currency_code_def(currency_code, cap);
}



// ** spec vars of module Libra

var $Libra_sum_of_coin_values : [$TypeValue]$Value where (forall $tv0: $TypeValue :: $IsValidNum($Libra_sum_of_coin_values[$tv0]));


// ** spec funs of module Libra

function {:inline} $Libra_spec_is_currency($m: $Memory, $txn: $Transaction, $tv0: $TypeValue): $Value {
    $ResourceExists($m, $Libra_CurrencyInfo_type_value($tv0), $CoreAddresses_SPEC_CURRENCY_INFO_ADDRESS())
}

function {:inline} $Libra_spec_currency_info($m: $Memory, $txn: $Transaction, $tv0: $TypeValue): $Value {
    $ResourceValue($m, $Libra_CurrencyInfo_type_value($tv0), $CoreAddresses_SPEC_CURRENCY_INFO_ADDRESS())
}



// ** structs of module Libra

const unique $Libra_Libra: $TypeName;
const $Libra_Libra_value: $FieldName;
axiom $Libra_Libra_value == 0;
function $Libra_Libra_type_value($tv0: $TypeValue): $TypeValue {
    $StructType($Libra_Libra, $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $tv0], 1), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $IntegerType()], 1))
}
function {:inline} $Libra_Libra_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $IsValidU64($SelectField($this, $Libra_Libra_value))
}
function {:inline} $Libra_Libra_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $IsValidU64($SelectField($this, $Libra_Libra_value))
}

axiom (forall m: $Memory, a: $Value, $tv0: $TypeValue :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $Libra_Libra_is_well_formed($ResourceValue(m, $Libra_Libra_type_value($tv0), a))
);

procedure {:inline 1} $Libra_Libra_before_update_inv($tv0: $TypeValue, $before: $Value) {
    $Libra_sum_of_coin_values := $Libra_sum_of_coin_values[$tv0 := $Integer(i#$Integer($Libra_sum_of_coin_values[$tv0]) - i#$Integer($SelectField($before, $Libra_Libra_value)))];
}

procedure {:inline 1} $Libra_Libra_after_update_inv($tv0: $TypeValue, $after: $Value) {
    $Libra_sum_of_coin_values := $Libra_sum_of_coin_values[$tv0 := $Integer(i#$Integer($Libra_sum_of_coin_values[$tv0]) + i#$Integer($SelectField($after, $Libra_Libra_value)))];
}

procedure {:inline 1} $Libra_Libra_pack($file_id: int, $byte_index: int, $var_idx: int, $tv0: $TypeValue, value: $Value) returns ($struct: $Value)
{
    assume $IsValidU64(value);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := value], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
    $Libra_sum_of_coin_values := $Libra_sum_of_coin_values[$tv0 := $Integer(i#$Integer($Libra_sum_of_coin_values[$tv0]) + i#$Integer($SelectField($struct, $Libra_Libra_value)))];
}

procedure {:inline 1} $Libra_Libra_unpack($tv0: $TypeValue, $struct: $Value) returns (value: $Value)
{
    assume is#$Vector($struct);
    value := $SelectField($struct, $Libra_Libra_value);
    assume $IsValidU64(value);
    $Libra_sum_of_coin_values := $Libra_sum_of_coin_values[$tv0 := $Integer(i#$Integer($Libra_sum_of_coin_values[$tv0]) - i#$Integer($SelectField($struct, $Libra_Libra_value)))];
}

const unique $Libra_BurnCapability: $TypeName;
const $Libra_BurnCapability_dummy_field: $FieldName;
axiom $Libra_BurnCapability_dummy_field == 0;
function $Libra_BurnCapability_type_value($tv0: $TypeValue): $TypeValue {
    $StructType($Libra_BurnCapability, $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $tv0], 1), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $BooleanType()], 1))
}
function {:inline} $Libra_BurnCapability_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && is#$Boolean($SelectField($this, $Libra_BurnCapability_dummy_field))
}
function {:inline} $Libra_BurnCapability_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && is#$Boolean($SelectField($this, $Libra_BurnCapability_dummy_field))
}

axiom (forall m: $Memory, a: $Value, $tv0: $TypeValue :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $Libra_BurnCapability_is_well_formed($ResourceValue(m, $Libra_BurnCapability_type_value($tv0), a))
);

procedure {:inline 1} $Libra_BurnCapability_pack($file_id: int, $byte_index: int, $var_idx: int, $tv0: $TypeValue, dummy_field: $Value) returns ($struct: $Value)
{
    assume is#$Boolean(dummy_field);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := dummy_field], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $Libra_BurnCapability_unpack($tv0: $TypeValue, $struct: $Value) returns (dummy_field: $Value)
{
    assume is#$Vector($struct);
    dummy_field := $SelectField($struct, $Libra_BurnCapability_dummy_field);
    assume is#$Boolean(dummy_field);
}

const unique $Libra_CurrencyInfo: $TypeName;
const $Libra_CurrencyInfo_total_value: $FieldName;
axiom $Libra_CurrencyInfo_total_value == 0;
const $Libra_CurrencyInfo_preburn_value: $FieldName;
axiom $Libra_CurrencyInfo_preburn_value == 1;
const $Libra_CurrencyInfo_is_synthetic: $FieldName;
axiom $Libra_CurrencyInfo_is_synthetic == 2;
const $Libra_CurrencyInfo_scaling_factor: $FieldName;
axiom $Libra_CurrencyInfo_scaling_factor == 3;
const $Libra_CurrencyInfo_fractional_part: $FieldName;
axiom $Libra_CurrencyInfo_fractional_part == 4;
const $Libra_CurrencyInfo_currency_code: $FieldName;
axiom $Libra_CurrencyInfo_currency_code == 5;
const $Libra_CurrencyInfo_can_mint: $FieldName;
axiom $Libra_CurrencyInfo_can_mint == 6;
function $Libra_CurrencyInfo_type_value($tv0: $TypeValue): $TypeValue {
    $StructType($Libra_CurrencyInfo, $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $tv0], 1), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $IntegerType()][1 := $IntegerType()][2 := $BooleanType()][3 := $IntegerType()][4 := $IntegerType()][5 := $Vector_type_value($IntegerType())][6 := $BooleanType()], 7))
}
function {:inline} $Libra_CurrencyInfo_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 7
      && $IsValidU128($SelectField($this, $Libra_CurrencyInfo_total_value))
      && $IsValidU64($SelectField($this, $Libra_CurrencyInfo_preburn_value))
      && is#$Boolean($SelectField($this, $Libra_CurrencyInfo_is_synthetic))
      && $IsValidU64($SelectField($this, $Libra_CurrencyInfo_scaling_factor))
      && $IsValidU64($SelectField($this, $Libra_CurrencyInfo_fractional_part))
      && $Vector_is_well_formed($SelectField($this, $Libra_CurrencyInfo_currency_code)) && (forall $$0: int :: {$select_vector($SelectField($this, $Libra_CurrencyInfo_currency_code),$$0)} $$0 >= 0 && $$0 < $vlen($SelectField($this, $Libra_CurrencyInfo_currency_code)) ==> $IsValidU8($select_vector($SelectField($this, $Libra_CurrencyInfo_currency_code),$$0)))
      && is#$Boolean($SelectField($this, $Libra_CurrencyInfo_can_mint))
}
function {:inline} $Libra_CurrencyInfo_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 7
      && $IsValidU128($SelectField($this, $Libra_CurrencyInfo_total_value))
      && $IsValidU64($SelectField($this, $Libra_CurrencyInfo_preburn_value))
      && is#$Boolean($SelectField($this, $Libra_CurrencyInfo_is_synthetic))
      && $IsValidU64($SelectField($this, $Libra_CurrencyInfo_scaling_factor))
      && $IsValidU64($SelectField($this, $Libra_CurrencyInfo_fractional_part))
      && $Vector_is_well_formed($SelectField($this, $Libra_CurrencyInfo_currency_code)) && (forall $$0: int :: {$select_vector($SelectField($this, $Libra_CurrencyInfo_currency_code),$$0)} $$0 >= 0 && $$0 < $vlen($SelectField($this, $Libra_CurrencyInfo_currency_code)) ==> $IsValidU8($select_vector($SelectField($this, $Libra_CurrencyInfo_currency_code),$$0)))
      && is#$Boolean($SelectField($this, $Libra_CurrencyInfo_can_mint))
}

axiom (forall m: $Memory, a: $Value, $tv0: $TypeValue :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $Libra_CurrencyInfo_is_well_formed($ResourceValue(m, $Libra_CurrencyInfo_type_value($tv0), a))
);

procedure {:inline 1} $Libra_CurrencyInfo_pack($file_id: int, $byte_index: int, $var_idx: int, $tv0: $TypeValue, total_value: $Value, preburn_value: $Value, is_synthetic: $Value, scaling_factor: $Value, fractional_part: $Value, currency_code: $Value, can_mint: $Value) returns ($struct: $Value)
{
    assume $IsValidU128(total_value);
    assume $IsValidU64(preburn_value);
    assume is#$Boolean(is_synthetic);
    assume $IsValidU64(scaling_factor);
    assume $IsValidU64(fractional_part);
    assume $Vector_is_well_formed(currency_code) && (forall $$0: int :: {$select_vector(currency_code,$$0)} $$0 >= 0 && $$0 < $vlen(currency_code) ==> $IsValidU8($select_vector(currency_code,$$0)));
    assume is#$Boolean(can_mint);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := total_value][1 := preburn_value][2 := is_synthetic][3 := scaling_factor][4 := fractional_part][5 := currency_code][6 := can_mint], 7));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $Libra_CurrencyInfo_unpack($tv0: $TypeValue, $struct: $Value) returns (total_value: $Value, preburn_value: $Value, is_synthetic: $Value, scaling_factor: $Value, fractional_part: $Value, currency_code: $Value, can_mint: $Value)
{
    assume is#$Vector($struct);
    total_value := $SelectField($struct, $Libra_CurrencyInfo_total_value);
    assume $IsValidU128(total_value);
    preburn_value := $SelectField($struct, $Libra_CurrencyInfo_preburn_value);
    assume $IsValidU64(preburn_value);
    is_synthetic := $SelectField($struct, $Libra_CurrencyInfo_is_synthetic);
    assume is#$Boolean(is_synthetic);
    scaling_factor := $SelectField($struct, $Libra_CurrencyInfo_scaling_factor);
    assume $IsValidU64(scaling_factor);
    fractional_part := $SelectField($struct, $Libra_CurrencyInfo_fractional_part);
    assume $IsValidU64(fractional_part);
    currency_code := $SelectField($struct, $Libra_CurrencyInfo_currency_code);
    assume $Vector_is_well_formed(currency_code) && (forall $$0: int :: {$select_vector(currency_code,$$0)} $$0 >= 0 && $$0 < $vlen(currency_code) ==> $IsValidU8($select_vector(currency_code,$$0)));
    can_mint := $SelectField($struct, $Libra_CurrencyInfo_can_mint);
    assume is#$Boolean(can_mint);
}

const unique $Libra_CurrencyRegistrationCapability: $TypeName;
const $Libra_CurrencyRegistrationCapability_cap: $FieldName;
axiom $Libra_CurrencyRegistrationCapability_cap == 0;
function $Libra_CurrencyRegistrationCapability_type_value(): $TypeValue {
    $StructType($Libra_CurrencyRegistrationCapability, $TypeValueArray($MapConstTypeValue($DefaultTypeValue()), 0), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $RegisteredCurrencies_RegistrationCapability_type_value()], 1))
}
function {:inline} $Libra_CurrencyRegistrationCapability_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $RegisteredCurrencies_RegistrationCapability_is_well_formed_types($SelectField($this, $Libra_CurrencyRegistrationCapability_cap))
}
function {:inline} $Libra_CurrencyRegistrationCapability_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $RegisteredCurrencies_RegistrationCapability_is_well_formed($SelectField($this, $Libra_CurrencyRegistrationCapability_cap))
}

axiom (forall m: $Memory, a: $Value :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $Libra_CurrencyRegistrationCapability_is_well_formed($ResourceValue(m, $Libra_CurrencyRegistrationCapability_type_value(), a))
);

procedure {:inline 1} $Libra_CurrencyRegistrationCapability_pack($file_id: int, $byte_index: int, $var_idx: int, cap: $Value) returns ($struct: $Value)
{
    assume $RegisteredCurrencies_RegistrationCapability_is_well_formed(cap);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := cap], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $Libra_CurrencyRegistrationCapability_unpack($struct: $Value) returns (cap: $Value)
{
    assume is#$Vector($struct);
    cap := $SelectField($struct, $Libra_CurrencyRegistrationCapability_cap);
    assume $RegisteredCurrencies_RegistrationCapability_is_well_formed(cap);
}

const unique $Libra_MintCapability: $TypeName;
const $Libra_MintCapability_dummy_field: $FieldName;
axiom $Libra_MintCapability_dummy_field == 0;
function $Libra_MintCapability_type_value($tv0: $TypeValue): $TypeValue {
    $StructType($Libra_MintCapability, $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $tv0], 1), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $BooleanType()], 1))
}
function {:inline} $Libra_MintCapability_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && is#$Boolean($SelectField($this, $Libra_MintCapability_dummy_field))
}
function {:inline} $Libra_MintCapability_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && is#$Boolean($SelectField($this, $Libra_MintCapability_dummy_field))
}

axiom (forall m: $Memory, a: $Value, $tv0: $TypeValue :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $Libra_MintCapability_is_well_formed($ResourceValue(m, $Libra_MintCapability_type_value($tv0), a))
);

procedure {:inline 1} $Libra_MintCapability_pack($file_id: int, $byte_index: int, $var_idx: int, $tv0: $TypeValue, dummy_field: $Value) returns ($struct: $Value)
{
    assume is#$Boolean(dummy_field);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := dummy_field], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $Libra_MintCapability_unpack($tv0: $TypeValue, $struct: $Value) returns (dummy_field: $Value)
{
    assume is#$Vector($struct);
    dummy_field := $SelectField($struct, $Libra_MintCapability_dummy_field);
    assume is#$Boolean(dummy_field);
}

const unique $Libra_Preburn: $TypeName;
const $Libra_Preburn_requests: $FieldName;
axiom $Libra_Preburn_requests == 0;
function $Libra_Preburn_type_value($tv0: $TypeValue): $TypeValue {
    $StructType($Libra_Preburn, $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $tv0], 1), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $Vector_type_value($Libra_Libra_type_value($tv0))], 1))
}
function {:inline} $Libra_Preburn_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $Vector_is_well_formed($SelectField($this, $Libra_Preburn_requests)) && (forall $$0: int :: {$select_vector($SelectField($this, $Libra_Preburn_requests),$$0)} $$0 >= 0 && $$0 < $vlen($SelectField($this, $Libra_Preburn_requests)) ==> $Libra_Libra_is_well_formed_types($select_vector($SelectField($this, $Libra_Preburn_requests),$$0)))
}
function {:inline} $Libra_Preburn_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $Vector_is_well_formed($SelectField($this, $Libra_Preburn_requests)) && (forall $$0: int :: {$select_vector($SelectField($this, $Libra_Preburn_requests),$$0)} $$0 >= 0 && $$0 < $vlen($SelectField($this, $Libra_Preburn_requests)) ==> $Libra_Libra_is_well_formed($select_vector($SelectField($this, $Libra_Preburn_requests),$$0)))
}

axiom (forall m: $Memory, a: $Value, $tv0: $TypeValue :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $Libra_Preburn_is_well_formed($ResourceValue(m, $Libra_Preburn_type_value($tv0), a))
);

procedure {:inline 1} $Libra_Preburn_pack($file_id: int, $byte_index: int, $var_idx: int, $tv0: $TypeValue, requests: $Value) returns ($struct: $Value)
{
    assume $Vector_is_well_formed(requests) && (forall $$0: int :: {$select_vector(requests,$$0)} $$0 >= 0 && $$0 < $vlen(requests) ==> $Libra_Libra_is_well_formed($select_vector(requests,$$0)));
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := requests], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $Libra_Preburn_unpack($tv0: $TypeValue, $struct: $Value) returns (requests: $Value)
{
    assume is#$Vector($struct);
    requests := $SelectField($struct, $Libra_Preburn_requests);
    assume $Vector_is_well_formed(requests) && (forall $$0: int :: {$select_vector(requests,$$0)} $$0 >= 0 && $$0 < $vlen(requests) ==> $Libra_Libra_is_well_formed($select_vector(requests,$$0)));
}

const unique $Libra_RegisterNewCurrency: $TypeName;
const $Libra_RegisterNewCurrency_dummy_field: $FieldName;
axiom $Libra_RegisterNewCurrency_dummy_field == 0;
function $Libra_RegisterNewCurrency_type_value(): $TypeValue {
    $StructType($Libra_RegisterNewCurrency, $TypeValueArray($MapConstTypeValue($DefaultTypeValue()), 0), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $BooleanType()], 1))
}
function {:inline} $Libra_RegisterNewCurrency_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && is#$Boolean($SelectField($this, $Libra_RegisterNewCurrency_dummy_field))
}
function {:inline} $Libra_RegisterNewCurrency_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && is#$Boolean($SelectField($this, $Libra_RegisterNewCurrency_dummy_field))
}

axiom (forall m: $Memory, a: $Value :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $Libra_RegisterNewCurrency_is_well_formed($ResourceValue(m, $Libra_RegisterNewCurrency_type_value(), a))
);

procedure {:inline 1} $Libra_RegisterNewCurrency_pack($file_id: int, $byte_index: int, $var_idx: int, dummy_field: $Value) returns ($struct: $Value)
{
    assume is#$Boolean(dummy_field);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := dummy_field], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $Libra_RegisterNewCurrency_unpack($struct: $Value) returns (dummy_field: $Value)
{
    assume is#$Vector($struct);
    dummy_field := $SelectField($struct, $Libra_RegisterNewCurrency_dummy_field);
    assume is#$Boolean(dummy_field);
}



// ** functions of module Libra

procedure {:inline 1} $Libra_value_def($tv0: $TypeValue, coin: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t1: $Value; // $Libra_Libra_type_value($tv0)
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $IntegerType()
    var $t4: $Value; // $Libra_Libra_type_value($tv0)
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(9, 11901, 0, coin); }

    // bytecode translation starts here
    // $t4 := move(coin)
    call $tmp := $CopyOrMoveValue(coin);
    $t4 := $tmp;

    // $t1 := move($t4)
    call $tmp := $CopyOrMoveValue($t4);
    $t1 := $tmp;

    // $t2 := get_field<Libra::Libra<#0>>.value($t1)
    call $tmp := $GetFieldFromValue($t1, $Libra_Libra_value);
    assume $IsValidU64($tmp);
    $t2 := $tmp;

    // $t3 := move($t2)
    call $tmp := $CopyOrMoveValue($t2);
    $t3 := $tmp;

    // return $t3
    $ret0 := $t3;
    if (true) { assume $DebugTrackLocal(9, 11967, 5, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Libra_value($tv0: $TypeValue, coin: $Value) returns ($ret0: $Value)
free requires $Libra_Libra_is_well_formed(coin);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($Libra_sum_of_coin_values[$tv0], old($Libra_sum_of_coin_values[$tv0])))));
{
    call $ret0 := $Libra_value_def($tv0, coin);
}

procedure {:inline 1} $Libra_initialize_def(config_account: $Value) returns (){
    // declare local variables
    var cap: $Value; // $RegisteredCurrencies_RegistrationCapability_type_value()
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $IntegerType()
    var $t4: $Value; // $AddressType()
    var $t5: $Value; // $AddressType()
    var $t6: $Value; // $AddressType()
    var $t7: $Value; // $BooleanType()
    var $t8: $Value; // $BooleanType()
    var $t9: $Value; // $AddressType()
    var $t10: $Value; // $IntegerType()
    var $t11: $Value; // $AddressType()
    var $t12: $Value; // $RegisteredCurrencies_RegistrationCapability_type_value()
    var $t13: $Value; // $AddressType()
    var $t14: $Value; // $RegisteredCurrencies_RegistrationCapability_type_value()
    var $t15: $Value; // $Libra_CurrencyRegistrationCapability_type_value()
    var $t16: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(9, 5060, 0, config_account); }

    // bytecode translation starts here
    // $t16 := move(config_account)
    call $tmp := $CopyOrMoveValue(config_account);
    $t16 := $tmp;

    // LibraTimestamp::assert_is_genesis()
    call $LibraTimestamp_assert_is_genesis();
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 5148);
      goto Abort;
    }

    // $t4 := copy($t16)
    call $tmp := $CopyOrMoveValue($t16);
    $t4 := $tmp;

    // $t5 := Signer::address_of($t4)
    call $t5 := $Signer_address_of($t4);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 5239);
      goto Abort;
    }
    assume is#$Address($t5);


    // $t6 := CoreAddresses::LIBRA_ROOT_ADDRESS()
    call $t6 := $CoreAddresses_LIBRA_ROOT_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 5284);
      goto Abort;
    }
    assume is#$Address($t6);


    // $t7 := ==($t5, $t6)
    $tmp := $Boolean($IsEqual($t5, $t6));
    $t7 := $tmp;

    // $t2 := $t7
    call $tmp := $CopyOrMoveValue($t7);
    $t2 := $tmp;
    if (true) { assume $DebugTrackLocal(9, 5211, 2, $tmp); }

    // if ($t2) goto L0 else goto L1
    $tmp := $t2;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t9 := move($t16)
    call $tmp := $CopyOrMoveValue($t16);
    $t9 := $tmp;

    // destroy($t9)

    // $t10 := 0
    $tmp := $Integer(0);
    $t10 := $tmp;

    // abort($t10)
    if (true) { assume $DebugTrackAbort(9, 5211); }
    goto Abort;

    // L0:
L0:

    // $t11 := copy($t16)
    call $tmp := $CopyOrMoveValue($t16);
    $t11 := $tmp;

    // $t12 := RegisteredCurrencies::initialize($t11)
    assume b#$Boolean($Boolean(b#$Boolean($Boolean(!b#$Boolean($LibraTimestamp_spec_is_genesis($m, $txn)))) ==> b#$Boolean($LibraConfig_spec_is_published($m, $txn, $RegisteredCurrencies_RegisteredCurrencies_type_value()))));
    call $t12 := $RegisteredCurrencies_initialize($t11);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 5371);
      goto Abort;
    }
    assume $RegisteredCurrencies_RegistrationCapability_is_well_formed($t12);


    // cap := $t12
    call $tmp := $CopyOrMoveValue($t12);
    cap := $tmp;
    if (true) { assume $DebugTrackLocal(9, 5343, 1, $tmp); }

    // $t13 := move($t16)
    call $tmp := $CopyOrMoveValue($t16);
    $t13 := $tmp;

    // $t15 := pack Libra::CurrencyRegistrationCapability(cap)
    call $tmp := $Libra_CurrencyRegistrationCapability_pack(0, 0, 0, cap);
    $t15 := $tmp;

    // move_to<Libra::CurrencyRegistrationCapability>($t15, $t13)
    call $MoveTo($Libra_CurrencyRegistrationCapability_type_value(), $t15, $t13);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 5407);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $Libra_initialize(config_account: $Value) returns ()
free requires is#$Address(config_account);
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $Libra_initialize_def(config_account);
}

procedure {:inline 1} $Libra_assert_is_currency_def($tv0: $TypeValue) returns (){
    // declare local variables
    var $t0: $Value; // $BooleanType()
    var $t1: $Value; // $IntegerType()
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t2 := Libra::is_currency<#0>()
    call $t2 := $Libra_is_currency($tv0);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 13268);
      goto Abort;
    }
    assume is#$Boolean($t2);


    // $t0 := $t2
    call $tmp := $CopyOrMoveValue($t2);
    $t0 := $tmp;
    if (true) { assume $DebugTrackLocal(9, 13678, 0, $tmp); }

    // if ($t0) goto L0 else goto L1
    $tmp := $t0;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t4 := 1
    $tmp := $Integer(1);
    $t4 := $tmp;

    // abort($t4)
    if (true) { assume $DebugTrackAbort(9, 13678); }
    goto Abort;

    // L0:
L0:

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $Libra_assert_is_currency($tv0: $TypeValue) returns ()
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($Libra_sum_of_coin_values[$tv0], old($Libra_sum_of_coin_values[$tv0])))));
{
    call $Libra_assert_is_currency_def($tv0);
}

procedure {:inline 1} $Libra_burn_def($tv0: $TypeValue, account: $Value, preburn_address: $Value) returns (){
    // declare local variables
    var $t2: $Value; // $AddressType()
    var $t3: $Value; // $AddressType()
    var $t4: $Value; // $AddressType()
    var $t5: $Value; // $Libra_BurnCapability_type_value($tv0)
    var $t6: $Value; // $AddressType()
    var $t7: $Value; // $AddressType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(9, 6389, 0, account); }
    if (true) { assume $DebugTrackLocal(9, 6389, 1, preburn_address); }

    // bytecode translation starts here
    // $t6 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t6 := $tmp;

    // $t7 := move(preburn_address)
    call $tmp := $CopyOrMoveValue(preburn_address);
    $t7 := $tmp;

    // $t3 := move($t6)
    call $tmp := $CopyOrMoveValue($t6);
    $t3 := $tmp;

    // $t4 := Signer::address_of($t3)
    call $t4 := $Signer_address_of($t3);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 6649);
      goto Abort;
    }
    assume is#$Address($t4);


    // $t5 := get_global<Libra::BurnCapability<#0>>($t4)
    call $tmp := $GetGlobal($t4, $Libra_BurnCapability_type_value($tv0));
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 6601);
      goto Abort;
    }
    assume $Libra_BurnCapability_is_well_formed($tmp);
    $t5 := $tmp;

    // Libra::burn_with_capability<#0>($t7, $t5)
    call $Libra_burn_with_capability($tv0, $t7, $t5);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 8657);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $Libra_burn($tv0: $TypeValue, account: $Value, preburn_address: $Value) returns ()
free requires is#$Address(account);
free requires is#$Address(preburn_address);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($Libra_sum_of_coin_values[$tv0], old($Libra_sum_of_coin_values[$tv0])))));
{
    call $Libra_burn_def($tv0, account, preburn_address);
}

procedure {:inline 1} $Libra_burn_with_capability_def($tv0: $TypeValue, preburn_address: $Value, capability: $Value) returns (){
    // declare local variables
    var $t2: $Value; // $AddressType()
    var $t3: $Reference; // ReferenceType($Libra_Preburn_type_value($tv0))
    var $t4: $Value; // $AddressType()
    var $t5: $Value; // $Libra_BurnCapability_type_value($tv0)
    var $t6: $Value; // $AddressType()
    var $t7: $Value; // $Libra_BurnCapability_type_value($tv0)
    var $t8: $Value; // $Libra_Preburn_type_value($tv0)
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(9, 8646, 0, preburn_address); }
    if (true) { assume $DebugTrackLocal(9, 8646, 1, capability); }

    // bytecode translation starts here
    // $t6 := move(preburn_address)
    call $tmp := $CopyOrMoveValue(preburn_address);
    $t6 := $tmp;

    // $t7 := move(capability)
    call $tmp := $CopyOrMoveValue(capability);
    $t7 := $tmp;

    // $t3 := borrow_global<Libra::Preburn<#0>>($t6)
    call $t3 := $BorrowGlobal($t6, $Libra_Preburn_type_value($tv0));
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 8913);
      goto Abort;
    }
    assume $Libra_Preburn_is_well_formed($Dereference($t3));

    // UnpackRef($t3)

    // $t5 := move($t7)
    call $tmp := $CopyOrMoveValue($t7);
    $t5 := $tmp;

    // PackRef($t3)

    // $t8 := read_ref($t3)
    call $tmp := $ReadRef($t3);
    assume $Libra_Preburn_is_well_formed($tmp);
    $t8 := $tmp;

    // $t8 := Libra::burn_with_resource_cap<#0>($t8, $t6, $t5)
    call $t8 := $Libra_burn_with_resource_cap($tv0, $t8, $t6, $t5);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 9906);
      goto Abort;
    }
    assume $Libra_Preburn_is_well_formed($t8);


    // write_ref($t3, $t8)
    call $t3 := $WriteRef($t3, $t8);

    // Libra::Preburn <- $t3
    call $WritebackToGlobal($t3);

    // UnpackRef($t3)

    // PackRef($t3)

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $Libra_burn_with_capability($tv0: $TypeValue, preburn_address: $Value, capability: $Value) returns ()
free requires is#$Address(preburn_address);
free requires $Libra_BurnCapability_is_well_formed(capability);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($Boolean(!b#$Boolean($ResourceExists($m, $Libra_Preburn_type_value($tv0), preburn_address))))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean(!b#$Boolean($Libra_spec_is_currency($m, $txn, $tv0))))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean($IsEqual($vlen_value($SelectField($ResourceValue($m, $Libra_Preburn_type_value($tv0), preburn_address), $Libra_Preburn_requests)), $Integer(0))))) ==> $abort_flag;
free ensures b#$Boolean(old((var i := $Libra_spec_currency_info($m, $txn, $tv0); $Boolean(b#$Boolean($Boolean(i#$Integer($SelectField(i, $Libra_CurrencyInfo_total_value)) < i#$Integer($SelectField($select_vector_by_value($SelectField($ResourceValue($m, $Libra_Preburn_type_value($tv0), preburn_address), $Libra_Preburn_requests), $Integer(0)), $Libra_Libra_value)))) || b#$Boolean($Boolean(i#$Integer($SelectField(i, $Libra_CurrencyInfo_preburn_value)) < i#$Integer($SelectField($select_vector_by_value($SelectField($ResourceValue($m, $Libra_Preburn_type_value($tv0), preburn_address), $Libra_Preburn_requests), $Integer(0)), $Libra_Libra_value)))))))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(!b#$Boolean($ResourceExists($m, $Libra_Preburn_type_value($tv0), preburn_address))))))
    || b#$Boolean(old(($Boolean(!b#$Boolean($Libra_spec_is_currency($m, $txn, $tv0))))))
    || b#$Boolean(old(($Boolean($IsEqual($vlen_value($SelectField($ResourceValue($m, $Libra_Preburn_type_value($tv0), preburn_address), $Libra_Preburn_requests)), $Integer(0))))))
    || b#$Boolean(old(((var i := $Libra_spec_currency_info($m, $txn, $tv0); $Boolean(b#$Boolean($Boolean(i#$Integer($SelectField(i, $Libra_CurrencyInfo_total_value)) < i#$Integer($SelectField($select_vector_by_value($SelectField($ResourceValue($m, $Libra_Preburn_type_value($tv0), preburn_address), $Libra_Preburn_requests), $Integer(0)), $Libra_Libra_value)))) || b#$Boolean($Boolean(i#$Integer($SelectField(i, $Libra_CurrencyInfo_preburn_value)) < i#$Integer($SelectField($select_vector_by_value($SelectField($ResourceValue($m, $Libra_Preburn_type_value($tv0), preburn_address), $Libra_Preburn_requests), $Integer(0)), $Libra_Libra_value))))))))));
free ensures !$abort_flag ==> (b#$Boolean($Vector_eq_pop_front($Libra_Libra_type_value($tv0), $SelectField($ResourceValue($m, $Libra_Preburn_type_value($tv0), preburn_address), $Libra_Preburn_requests), old($SelectField($ResourceValue($m, $Libra_Preburn_type_value($tv0), preburn_address), $Libra_Preburn_requests)))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_total_value), $Integer(i#$Integer(old($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_total_value))) - i#$Integer(old($SelectField($select_vector_by_value($SelectField($ResourceValue($m, $Libra_Preburn_type_value($tv0), preburn_address), $Libra_Preburn_requests), $Integer(0)), $Libra_Libra_value))))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_preburn_value), $Integer(i#$Integer(old($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_preburn_value))) - i#$Integer(old($SelectField($select_vector_by_value($SelectField($ResourceValue($m, $Libra_Preburn_type_value($tv0), preburn_address), $Libra_Preburn_requests), $Integer(0)), $Libra_Libra_value))))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($Libra_sum_of_coin_values[$tv0], old($Libra_sum_of_coin_values[$tv0])))));
{
    call $Libra_burn_with_capability_def($tv0, preburn_address, capability);
}

procedure {:inline 1} $Libra_burn_with_resource_cap_def($tv0: $TypeValue, preburn: $Value, _: $Value, _capability: $Value) returns ($ret0: $Value){
    // declare local variables
    var info: $Reference; // ReferenceType($Libra_CurrencyInfo_type_value($tv0))
    var value: $Value; // $IntegerType()
    var $t5: $Reference; // ReferenceType($Libra_Preburn_type_value($tv0))
    var $t6: $Reference; // ReferenceType($Vector_type_value($Libra_Libra_type_value($tv0)))
    var $t7: $Value; // $IntegerType()
    var $t8: $Value; // $Libra_Libra_type_value($tv0)
    var $t9: $Value; // $IntegerType()
    var $t10: $Value; // $AddressType()
    var $t11: $Reference; // ReferenceType($Libra_CurrencyInfo_type_value($tv0))
    var $t12: $Reference; // ReferenceType($Libra_CurrencyInfo_type_value($tv0))
    var $t13: $Value; // $IntegerType()
    var $t14: $Value; // $IntegerType()
    var $t15: $Value; // $IntegerType()
    var $t16: $Value; // $IntegerType()
    var $t17: $Value; // $IntegerType()
    var $t18: $Reference; // ReferenceType($Libra_CurrencyInfo_type_value($tv0))
    var $t19: $Reference; // ReferenceType($IntegerType())
    var $t20: $Reference; // ReferenceType($Libra_CurrencyInfo_type_value($tv0))
    var $t21: $Value; // $IntegerType()
    var $t22: $Value; // $IntegerType()
    var $t23: $Value; // $IntegerType()
    var $t24: $Value; // $IntegerType()
    var $t25: $Reference; // ReferenceType($Libra_CurrencyInfo_type_value($tv0))
    var $t26: $Reference; // ReferenceType($IntegerType())
    var $t27: $Value; // $Libra_Preburn_type_value($tv0)
    var $t28: $Reference; // ReferenceType($Libra_Preburn_type_value($tv0))
    var $t29: $Value; // $AddressType()
    var $t30: $Value; // $Libra_BurnCapability_type_value($tv0)
    var $t31: $Value; // $Vector_type_value($Libra_Libra_type_value($tv0))
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(9, 9895, 0, preburn); }
    if (true) { assume $DebugTrackLocal(9, 9895, 1, _); }
    if (true) { assume $DebugTrackLocal(9, 9895, 2, _capability); }

    // bytecode translation starts here
    // $t27 := move(preburn)
    call $tmp := $CopyOrMoveValue(preburn);
    $t27 := $tmp;

    // $t29 := move(_)
    call $tmp := $CopyOrMoveValue(_);
    $t29 := $tmp;

    // $t30 := move(_capability)
    call $tmp := $CopyOrMoveValue(_capability);
    $t30 := $tmp;

    // $t28 := borrow_local($t27)
    call $t28 := $BorrowLoc(27, $t27);
    assume $Libra_Preburn_is_well_formed($Dereference($t28));

    // UnpackRef($t28)

    // $t5 := move($t28)
    call $t5 := $CopyOrMoveRef($t28);

    // $t6 := borrow_field<Libra::Preburn<#0>>.requests($t5)
    call $t6 := $BorrowField($t5, $Libra_Preburn_requests);
    assume $Vector_is_well_formed($Dereference($t6)) && (forall $$1: int :: {$select_vector($Dereference($t6),$$1)} $$1 >= 0 && $$1 < $vlen($Dereference($t6)) ==> $Libra_Libra_is_well_formed_types($select_vector($Dereference($t6),$$1)));

    // LocalRoot($t27) <- $t5
    call $t27 := $WritebackToValue($t5, 27, $t27);

    // UnpackRef($t6)

    // $t7 := 0
    $tmp := $Integer(0);
    $t7 := $tmp;

    // PackRef($t6)

    // $t31 := read_ref($t6)
    call $tmp := $ReadRef($t6);
    assume $Vector_is_well_formed($tmp) && (forall $$0: int :: {$select_vector($tmp,$$0)} $$0 >= 0 && $$0 < $vlen($tmp) ==> $Libra_Libra_is_well_formed($select_vector($tmp,$$0)));
    $t31 := $tmp;

    // ($t8, $t31) := Vector::remove<Libra::Libra<#0>>($t31, $t7)
    call $t8, $t31 := $Vector_remove($Libra_Libra_type_value($tv0), $t31, $t7);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 10177);
      goto Abort;
    }
    assume $Libra_Libra_is_well_formed($t8);

    assume $Vector_is_well_formed($t31) && (forall $$0: int :: {$select_vector($t31,$$0)} $$0 >= 0 && $$0 < $vlen($t31) ==> $Libra_Libra_is_well_formed($select_vector($t31,$$0)));


    // write_ref($t6, $t31)
    call $t6 := $WriteRef($t6, $t31);
    if (true) { assume $DebugTrackLocal(9, 9895, 3, $Dereference(info)); }

    // LocalRoot($t27) <- $t6
    call $t27 := $WritebackToValue($t6, 27, $t27);

    // Reference($t5) <- $t6
    call $t5 := $WritebackToReference($t6, $t5);

    // UnpackRef($t6)

    // PackRef($t5)

    // PackRef($t6)

    // $t9 := unpack Libra::Libra<#0>($t8)
    call $t9 := $Libra_Libra_unpack($tv0, $t8);
    $t9 := $t9;

    // value := $t9
    call $tmp := $CopyOrMoveValue($t9);
    value := $tmp;
    if (true) { assume $DebugTrackLocal(9, 10159, 4, $tmp); }

    // $t10 := CoreAddresses::CURRENCY_INFO_ADDRESS()
    call $t10 := $CoreAddresses_CURRENCY_INFO_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 10320);
      goto Abort;
    }
    assume is#$Address($t10);


    // $t11 := borrow_global<Libra::CurrencyInfo<#0>>($t10)
    call $t11 := $BorrowGlobal($t10, $Libra_CurrencyInfo_type_value($tv0));
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 10263);
      goto Abort;
    }
    assume $Libra_CurrencyInfo_is_well_formed($Dereference($t11));

    // UnpackRef($t11)

    // info := $t11
    call info := $CopyOrMoveRef($t11);
    if (true) { assume $DebugTrackLocal(9, 10256, 3, $Dereference(info)); }

    // $t12 := copy(info)
    call $t12 := $CopyOrMoveRef(info);

    // $t13 := get_field<Libra::CurrencyInfo<#0>>.total_value($t12)
    call $tmp := $GetFieldFromReference($t12, $Libra_CurrencyInfo_total_value);
    assume $IsValidU128($tmp);
    $t13 := $tmp;

    // Reference(info) <- $t12
    call info := $WritebackToReference($t12, info);

    // $t14 := move($t13)
    call $tmp := $CopyOrMoveValue($t13);
    $t14 := $tmp;

    // $t16 := (u128)(value)
    call $tmp := $CastU128(value);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 10392);
      goto Abort;
    }
    $t16 := $tmp;

    // $t17 := -($t14, $t16)
    call $tmp := $Sub($t14, $t16);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 10390);
      goto Abort;
    }
    $t17 := $tmp;

    // $t18 := copy(info)
    call $t18 := $CopyOrMoveRef(info);

    // $t19 := borrow_field<Libra::CurrencyInfo<#0>>.total_value($t18)
    call $t19 := $BorrowField($t18, $Libra_CurrencyInfo_total_value);
    assume $IsValidU128($Dereference($t19));

    // Reference(info) <- $t18
    call info := $WritebackToReference($t18, info);

    // UnpackRef($t19)

    // write_ref($t19, $t17)
    call $t19 := $WriteRef($t19, $t17);
    if (true) { assume $DebugTrackLocal(9, 10354, 3, $Dereference(info)); }

    // Reference(info) <- $t19
    call info := $WritebackToReference($t19, info);

    // Reference($t18) <- $t19
    call $t18 := $WritebackToReference($t19, $t18);

    // PackRef($t19)

    // $t20 := copy(info)
    call $t20 := $CopyOrMoveRef(info);

    // $t21 := get_field<Libra::CurrencyInfo<#0>>.preburn_value($t20)
    call $tmp := $GetFieldFromReference($t20, $Libra_CurrencyInfo_preburn_value);
    assume $IsValidU64($tmp);
    $t21 := $tmp;

    // Reference(info) <- $t20
    call info := $WritebackToReference($t20, info);

    // $t22 := move($t21)
    call $tmp := $CopyOrMoveValue($t21);
    $t22 := $tmp;

    // $t24 := -($t22, value)
    call $tmp := $Sub($t22, value);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 10457);
      goto Abort;
    }
    $t24 := $tmp;

    // $t25 := move(info)
    call $t25 := $CopyOrMoveRef(info);

    // $t26 := borrow_field<Libra::CurrencyInfo<#0>>.preburn_value($t25)
    call $t26 := $BorrowField($t25, $Libra_CurrencyInfo_preburn_value);
    assume $IsValidU64($Dereference($t26));

    // Libra::CurrencyInfo <- $t25
    call $WritebackToGlobal($t25);

    // UnpackRef($t26)

    // write_ref($t26, $t24)
    call $t26 := $WriteRef($t26, $t24);
    if (true) { assume $DebugTrackLocal(9, 10417, 3, $Dereference(info)); }

    // Libra::CurrencyInfo <- $t26
    call $WritebackToGlobal($t26);

    // Reference($t25) <- $t26
    call $t25 := $WritebackToReference($t26, $t25);

    // PackRef($t25)

    // PackRef($t26)

    // return $t27
    $ret0 := $t27;
    if (true) { assume $DebugTrackLocal(9, 10464, 32, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Libra_burn_with_resource_cap($tv0: $TypeValue, preburn: $Value, _: $Value, _capability: $Value) returns ($ret0: $Value)
free requires $Libra_Preburn_is_well_formed(preburn);
free requires is#$Address(_);
free requires $Libra_BurnCapability_is_well_formed(_capability);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($Boolean(!b#$Boolean($Libra_spec_is_currency($m, $txn, $tv0))))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean($IsEqual($vlen_value($SelectField(preburn, $Libra_Preburn_requests)), $Integer(0))))) ==> $abort_flag;
free ensures b#$Boolean(old((var i := $Libra_spec_currency_info($m, $txn, $tv0); $Boolean(b#$Boolean($Boolean(i#$Integer($SelectField(i, $Libra_CurrencyInfo_total_value)) < i#$Integer($SelectField($select_vector_by_value($SelectField(preburn, $Libra_Preburn_requests), $Integer(0)), $Libra_Libra_value)))) || b#$Boolean($Boolean(i#$Integer($SelectField(i, $Libra_CurrencyInfo_preburn_value)) < i#$Integer($SelectField($select_vector_by_value($SelectField(preburn, $Libra_Preburn_requests), $Integer(0)), $Libra_Libra_value)))))))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(!b#$Boolean($Libra_spec_is_currency($m, $txn, $tv0))))))
    || b#$Boolean(old(($Boolean($IsEqual($vlen_value($SelectField(preburn, $Libra_Preburn_requests)), $Integer(0))))))
    || b#$Boolean(old(((var i := $Libra_spec_currency_info($m, $txn, $tv0); $Boolean(b#$Boolean($Boolean(i#$Integer($SelectField(i, $Libra_CurrencyInfo_total_value)) < i#$Integer($SelectField($select_vector_by_value($SelectField(preburn, $Libra_Preburn_requests), $Integer(0)), $Libra_Libra_value)))) || b#$Boolean($Boolean(i#$Integer($SelectField(i, $Libra_CurrencyInfo_preburn_value)) < i#$Integer($SelectField($select_vector_by_value($SelectField(preburn, $Libra_Preburn_requests), $Integer(0)), $Libra_Libra_value))))))))));
free ensures !$abort_flag ==> (b#$Boolean($Vector_eq_pop_front($Libra_Libra_type_value($tv0), $SelectField($ret0, $Libra_Preburn_requests), old($SelectField(preburn, $Libra_Preburn_requests)))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_total_value), $Integer(i#$Integer(old($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_total_value))) - i#$Integer(old($SelectField($select_vector_by_value($SelectField(preburn, $Libra_Preburn_requests), $Integer(0)), $Libra_Libra_value))))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_preburn_value), $Integer(i#$Integer(old($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_preburn_value))) - i#$Integer(old($SelectField($select_vector_by_value($SelectField(preburn, $Libra_Preburn_requests), $Integer(0)), $Libra_Libra_value))))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($Libra_sum_of_coin_values[$tv0], old($Libra_sum_of_coin_values[$tv0])))));
{
    call $ret0 := $Libra_burn_with_resource_cap_def($tv0, preburn, _, _capability);
}

procedure {:inline 1} $Libra_deposit_def($tv0: $TypeValue, coin: $Value, check: $Value) returns ($ret0: $Value){
    // declare local variables
    var value: $Value; // $IntegerType()
    var $t3: $Value; // $Libra_Libra_type_value($tv0)
    var $t4: $Value; // $IntegerType()
    var $t5: $Reference; // ReferenceType($Libra_Libra_type_value($tv0))
    var $t6: $Value; // $IntegerType()
    var $t7: $Value; // $IntegerType()
    var $t8: $Value; // $IntegerType()
    var $t9: $Value; // $IntegerType()
    var $t10: $Reference; // ReferenceType($Libra_Libra_type_value($tv0))
    var $t11: $Reference; // ReferenceType($IntegerType())
    var $t12: $Value; // $Libra_Libra_type_value($tv0)
    var $t13: $Reference; // ReferenceType($Libra_Libra_type_value($tv0))
    var $t14: $Value; // $Libra_Libra_type_value($tv0)
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(9, 12978, 0, coin); }
    if (true) { assume $DebugTrackLocal(9, 12978, 1, check); }

    // bytecode translation starts here
    // $t12 := move(coin)
    call $tmp := $CopyOrMoveValue(coin);
    $t12 := $tmp;

    // $t14 := move(check)
    call $tmp := $CopyOrMoveValue(check);
    $t14 := $tmp;

    // $t13 := borrow_local($t12)
    call $t13 := $BorrowLoc(12, $t12);
    assume $Libra_Libra_is_well_formed($Dereference($t13));

    // UnpackRef($t13)
    call $Libra_Libra_before_update_inv($tv0, $Dereference($t13));

    // $t4 := unpack Libra::Libra<#0>($t14)
    call $t4 := $Libra_Libra_unpack($tv0, $t14);
    $t4 := $t4;

    // value := $t4
    call $tmp := $CopyOrMoveValue($t4);
    value := $tmp;
    if (true) { assume $DebugTrackLocal(9, 13081, 2, $tmp); }

    // $t5 := copy($t13)
    call $t5 := $CopyOrMoveRef($t13);

    // $t6 := get_field<Libra::Libra<#0>>.value($t5)
    call $tmp := $GetFieldFromReference($t5, $Libra_Libra_value);
    assume $IsValidU64($tmp);
    $t6 := $tmp;

    // Reference($t13) <- $t5
    call $t13 := $WritebackToReference($t5, $t13);

    // $t7 := move($t6)
    call $tmp := $CopyOrMoveValue($t6);
    $t7 := $tmp;

    // $t9 := +($t7, value)
    call $tmp := $AddU64($t7, value);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 13130);
      goto Abort;
    }
    $t9 := $tmp;

    // $t10 := move($t13)
    call $t10 := $CopyOrMoveRef($t13);

    // $t11 := borrow_field<Libra::Libra<#0>>.value($t10)
    call $t11 := $BorrowField($t10, $Libra_Libra_value);
    assume $IsValidU64($Dereference($t11));

    // LocalRoot($t12) <- $t10
    call $t12 := $WritebackToValue($t10, 12, $t12);

    // UnpackRef($t11)

    // write_ref($t11, $t9)
    call $t11 := $WriteRef($t11, $t9);

    // LocalRoot($t12) <- $t11
    call $t12 := $WritebackToValue($t11, 12, $t12);

    // Reference($t10) <- $t11
    call $t10 := $WritebackToReference($t11, $t10);

    // PackRef($t10)
    call $Libra_Libra_after_update_inv($tv0, $Dereference($t10));

    // PackRef($t11)

    // return $t12
    $ret0 := $t12;
    if (true) { assume $DebugTrackLocal(9, 13137, 15, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Libra_deposit($tv0: $TypeValue, coin: $Value, check: $Value) returns ($ret0: $Value)
free requires $Libra_Libra_is_well_formed(coin);
free requires $Libra_Libra_is_well_formed(check);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($Libra_sum_of_coin_values[$tv0], old($Libra_sum_of_coin_values[$tv0])))));
{
    call $ret0 := $Libra_deposit_def($tv0, coin, check);
}

procedure {:inline 1} $Libra_is_currency_def($tv0: $TypeValue) returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $AddressType()
    var $t1: $Value; // $BooleanType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // $t0 := CoreAddresses::CURRENCY_INFO_ADDRESS()
    call $t0 := $CoreAddresses_CURRENCY_INFO_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 13354);
      goto Abort;
    }
    assume is#$Address($t0);


    // $t1 := exists<Libra::CurrencyInfo<#0>>($t0)
    call $tmp := $Exists($t0, $Libra_CurrencyInfo_type_value($tv0));
    $t1 := $tmp;

    // return $t1
    $ret0 := $t1;
    if (true) { assume $DebugTrackLocal(9, 13308, 2, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Libra_is_currency($tv0: $TypeValue) returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($Libra_sum_of_coin_values[$tv0], old($Libra_sum_of_coin_values[$tv0])))));
{
    call $ret0 := $Libra_is_currency_def($tv0);
}

procedure {:inline 1} $Libra_mint_def($tv0: $TypeValue, account: $Value, value: $Value) returns ($ret0: $Value){
    // declare local variables
    var $t2: $Value; // $IntegerType()
    var $t3: $Value; // $AddressType()
    var $t4: $Value; // $AddressType()
    var $t5: $Value; // $Libra_MintCapability_type_value($tv0)
    var $t6: $Value; // $Libra_Libra_type_value($tv0)
    var $t7: $Value; // $AddressType()
    var $t8: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(9, 5683, 0, account); }
    if (true) { assume $DebugTrackLocal(9, 5683, 1, value); }

    // bytecode translation starts here
    // $t7 := move(account)
    call $tmp := $CopyOrMoveValue(account);
    $t7 := $tmp;

    // $t8 := move(value)
    call $tmp := $CopyOrMoveValue(value);
    $t8 := $tmp;

    // $t3 := move($t7)
    call $tmp := $CopyOrMoveValue($t7);
    $t3 := $tmp;

    // $t4 := Signer::address_of($t3)
    call $t4 := $Signer_address_of($t3);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 5909);
      goto Abort;
    }
    assume is#$Address($t4);


    // $t5 := get_global<Libra::MintCapability<#0>>($t4)
    call $tmp := $GetGlobal($t4, $Libra_MintCapability_type_value($tv0));
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 5861);
      goto Abort;
    }
    assume $Libra_MintCapability_is_well_formed($tmp);
    $t5 := $tmp;

    // $t6 := Libra::mint_with_capability<#0>($t8, $t5)
    call $t6 := $Libra_mint_with_capability($tv0, $t8, $t5);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 6947);
      goto Abort;
    }
    assume $Libra_Libra_is_well_formed($t6);


    // return $t6
    $ret0 := $t6;
    if (true) { assume $DebugTrackLocal(9, 5808, 9, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Libra_mint($tv0: $TypeValue, account: $Value, value: $Value) returns ($ret0: $Value)
free requires is#$Address(account);
free requires $IsValidU64(value);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($Boolean(!b#$Boolean($ResourceExists($m, $Libra_MintCapability_type_value($tv0), $Signer_spec_address_of($m, $txn, account)))))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean(!b#$Boolean($Libra_spec_is_currency($m, $txn, $tv0))))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean(!b#$Boolean($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_can_mint))))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean(i#$Integer($Integer(i#$Integer($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_total_value)) + i#$Integer(value))) > i#$Integer($Integer($MAX_U128))))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(!b#$Boolean($ResourceExists($m, $Libra_MintCapability_type_value($tv0), $Signer_spec_address_of($m, $txn, account)))))))
    || b#$Boolean(old(($Boolean(!b#$Boolean($Libra_spec_is_currency($m, $txn, $tv0))))))
    || b#$Boolean(old(($Boolean(!b#$Boolean($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_can_mint))))))
    || b#$Boolean(old(($Boolean(i#$Integer($Integer(i#$Integer($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_total_value)) + i#$Integer(value))) > i#$Integer($Integer($MAX_U128)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_total_value), $Integer(i#$Integer(old($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_total_value))) + i#$Integer(value))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($SelectField($ret0, $Libra_Libra_value), value))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($Libra_sum_of_coin_values[$tv0], old($Libra_sum_of_coin_values[$tv0])))));
{
    call $ret0 := $Libra_mint_def($tv0, account, value);
}

procedure {:inline 1} $Libra_mint_with_capability_def($tv0: $TypeValue, value: $Value, _capability: $Value) returns ($ret0: $Value){
    // declare local variables
    var info: $Reference; // ReferenceType($Libra_CurrencyInfo_type_value($tv0))
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $IntegerType()
    var $t5: $Value; // $AddressType()
    var $t6: $Reference; // ReferenceType($Libra_CurrencyInfo_type_value($tv0))
    var $t7: $Reference; // ReferenceType($Libra_CurrencyInfo_type_value($tv0))
    var $t8: $Value; // $BooleanType()
    var $t9: $Value; // $BooleanType()
    var $t10: $Value; // $BooleanType()
    var $t11: $Reference; // ReferenceType($Libra_CurrencyInfo_type_value($tv0))
    var $t12: $Value; // $IntegerType()
    var $t13: $Reference; // ReferenceType($Libra_CurrencyInfo_type_value($tv0))
    var $t14: $Value; // $IntegerType()
    var $t15: $Value; // $IntegerType()
    var $t16: $Value; // $IntegerType()
    var $t17: $Value; // $IntegerType()
    var $t18: $Value; // $IntegerType()
    var $t19: $Reference; // ReferenceType($Libra_CurrencyInfo_type_value($tv0))
    var $t20: $Reference; // ReferenceType($IntegerType())
    var $t21: $Value; // $IntegerType()
    var $t22: $Value; // $Libra_Libra_type_value($tv0)
    var $t23: $Value; // $IntegerType()
    var $t24: $Value; // $Libra_MintCapability_type_value($tv0)
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(9, 6936, 0, value); }
    if (true) { assume $DebugTrackLocal(9, 6936, 1, _capability); }

    // bytecode translation starts here
    // $t23 := move(value)
    call $tmp := $CopyOrMoveValue(value);
    $t23 := $tmp;

    // $t24 := move(_capability)
    call $tmp := $CopyOrMoveValue(_capability);
    $t24 := $tmp;

    // Libra::assert_is_currency<#0>()
    call $Libra_assert_is_currency($tv0);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 13637);
      goto Abort;
    }

    // $t5 := CoreAddresses::CURRENCY_INFO_ADDRESS()
    call $t5 := $CoreAddresses_CURRENCY_INFO_ADDRESS();
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 7266);
      goto Abort;
    }
    assume is#$Address($t5);


    // $t6 := borrow_global<Libra::CurrencyInfo<#0>>($t5)
    call $t6 := $BorrowGlobal($t5, $Libra_CurrencyInfo_type_value($tv0));
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 7209);
      goto Abort;
    }
    assume $Libra_CurrencyInfo_is_well_formed($Dereference($t6));

    // UnpackRef($t6)

    // info := $t6
    call info := $CopyOrMoveRef($t6);
    if (true) { assume $DebugTrackLocal(9, 7202, 2, $Dereference(info)); }

    // $t7 := copy(info)
    call $t7 := $CopyOrMoveRef(info);

    // $t8 := get_field<Libra::CurrencyInfo<#0>>.can_mint($t7)
    call $tmp := $GetFieldFromReference($t7, $Libra_CurrencyInfo_can_mint);
    assume is#$Boolean($tmp);
    $t8 := $tmp;

    // Reference(info) <- $t7
    call info := $WritebackToReference($t7, info);

    // $t9 := move($t8)
    call $tmp := $CopyOrMoveValue($t8);
    $t9 := $tmp;

    // $t3 := $t9
    call $tmp := $CopyOrMoveValue($t9);
    $t3 := $tmp;
    if (true) { assume $DebugTrackLocal(9, 7300, 3, $tmp); }

    // if ($t3) goto L0 else goto L1
    $tmp := $t3;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t11 := move(info)
    call $t11 := $CopyOrMoveRef(info);

    // destroy($t11)

    // Libra::CurrencyInfo <- $t11
    call $WritebackToGlobal($t11);

    // PackRef($t11)

    // $t12 := 4
    $tmp := $Integer(4);
    $t12 := $tmp;

    // abort($t12)
    if (true) { assume $DebugTrackAbort(9, 7300); }
    goto Abort;

    // L0:
L0:

    // $t13 := copy(info)
    call $t13 := $CopyOrMoveRef(info);

    // $t14 := get_field<Libra::CurrencyInfo<#0>>.total_value($t13)
    call $tmp := $GetFieldFromReference($t13, $Libra_CurrencyInfo_total_value);
    assume $IsValidU128($tmp);
    $t14 := $tmp;

    // Reference(info) <- $t13
    call info := $WritebackToReference($t13, info);

    // $t15 := move($t14)
    call $tmp := $CopyOrMoveValue($t14);
    $t15 := $tmp;

    // $t17 := (u128)($t23)
    call $tmp := $CastU128($t23);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 7372);
      goto Abort;
    }
    $t17 := $tmp;

    // $t18 := +($t15, $t17)
    call $tmp := $AddU128($t15, $t17);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 7370);
      goto Abort;
    }
    $t18 := $tmp;

    // $t19 := move(info)
    call $t19 := $CopyOrMoveRef(info);

    // $t20 := borrow_field<Libra::CurrencyInfo<#0>>.total_value($t19)
    call $t20 := $BorrowField($t19, $Libra_CurrencyInfo_total_value);
    assume $IsValidU128($Dereference($t20));

    // Libra::CurrencyInfo <- $t19
    call $WritebackToGlobal($t19);

    // UnpackRef($t20)

    // write_ref($t20, $t18)
    call $t20 := $WriteRef($t20, $t18);
    if (true) { assume $DebugTrackLocal(9, 7334, 2, $Dereference(info)); }

    // Libra::CurrencyInfo <- $t20
    call $WritebackToGlobal($t20);

    // Reference($t19) <- $t20
    call $t19 := $WritebackToReference($t20, $t19);

    // PackRef($t19)

    // PackRef($t20)

    // $t22 := pack Libra::Libra<#0>($t23)
    call $tmp := $Libra_Libra_pack(0, 0, 0, $tv0, $t23);
    $t22 := $tmp;

    // return $t22
    $ret0 := $t22;
    if (true) { assume $DebugTrackLocal(9, 7398, 25, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Libra_mint_with_capability($tv0: $TypeValue, value: $Value, _capability: $Value) returns ($ret0: $Value)
free requires $IsValidU64(value);
free requires $Libra_MintCapability_is_well_formed(_capability);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($Boolean(!b#$Boolean($Libra_spec_is_currency($m, $txn, $tv0))))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean(!b#$Boolean($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_can_mint))))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean(i#$Integer($Integer(i#$Integer($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_total_value)) + i#$Integer(value))) > i#$Integer($Integer($MAX_U128))))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(!b#$Boolean($Libra_spec_is_currency($m, $txn, $tv0))))))
    || b#$Boolean(old(($Boolean(!b#$Boolean($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_can_mint))))))
    || b#$Boolean(old(($Boolean(i#$Integer($Integer(i#$Integer($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_total_value)) + i#$Integer(value))) > i#$Integer($Integer($MAX_U128)))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_total_value), $Integer(i#$Integer(old($SelectField($Libra_spec_currency_info($m, $txn, $tv0), $Libra_CurrencyInfo_total_value))) + i#$Integer(value))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($SelectField($ret0, $Libra_Libra_value), value))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($Libra_sum_of_coin_values[$tv0], old($Libra_sum_of_coin_values[$tv0])))));
{
    call $ret0 := $Libra_mint_with_capability_def($tv0, value, _capability);
}

procedure {:inline 1} $Libra_withdraw_def($tv0: $TypeValue, coin: $Value, amount: $Value) returns ($ret0: $Value, $ret1: $Value){
    // declare local variables
    var $t2: $Value; // $BooleanType()
    var $t3: $Value; // $IntegerType()
    var $t4: $Reference; // ReferenceType($Libra_Libra_type_value($tv0))
    var $t5: $Value; // $IntegerType()
    var $t6: $Value; // $IntegerType()
    var $t7: $Value; // $IntegerType()
    var $t8: $Value; // $BooleanType()
    var $t9: $Value; // $BooleanType()
    var $t10: $Reference; // ReferenceType($Libra_Libra_type_value($tv0))
    var $t11: $Value; // $IntegerType()
    var $t12: $Reference; // ReferenceType($Libra_Libra_type_value($tv0))
    var $t13: $Value; // $IntegerType()
    var $t14: $Value; // $IntegerType()
    var $t15: $Value; // $IntegerType()
    var $t16: $Value; // $IntegerType()
    var $t17: $Reference; // ReferenceType($Libra_Libra_type_value($tv0))
    var $t18: $Reference; // ReferenceType($IntegerType())
    var $t19: $Value; // $IntegerType()
    var $t20: $Value; // $Libra_Libra_type_value($tv0)
    var $t21: $Value; // $Libra_Libra_type_value($tv0)
    var $t22: $Reference; // ReferenceType($Libra_Libra_type_value($tv0))
    var $t23: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(9, 12359, 0, coin); }
    if (true) { assume $DebugTrackLocal(9, 12359, 1, amount); }

    // bytecode translation starts here
    // $t21 := move(coin)
    call $tmp := $CopyOrMoveValue(coin);
    $t21 := $tmp;

    // $t23 := move(amount)
    call $tmp := $CopyOrMoveValue(amount);
    $t23 := $tmp;

    // $t22 := borrow_local($t21)
    call $t22 := $BorrowLoc(21, $t21);
    assume $Libra_Libra_is_well_formed($Dereference($t22));

    // UnpackRef($t22)
    call $Libra_Libra_before_update_inv($tv0, $Dereference($t22));

    // $t4 := copy($t22)
    call $t4 := $CopyOrMoveRef($t22);

    // $t5 := get_field<Libra::Libra<#0>>.value($t4)
    call $tmp := $GetFieldFromReference($t4, $Libra_Libra_value);
    assume $IsValidU64($tmp);
    $t5 := $tmp;

    // Reference($t22) <- $t4
    call $t22 := $WritebackToReference($t4, $t22);

    // $t6 := move($t5)
    call $tmp := $CopyOrMoveValue($t5);
    $t6 := $tmp;

    // $t8 := >=($t6, $t23)
    call $tmp := $Ge($t6, $t23);
    $t8 := $tmp;

    // $t2 := $t8
    call $tmp := $CopyOrMoveValue($t8);
    $t2 := $tmp;
    if (true) { assume $DebugTrackLocal(9, 12518, 2, $tmp); }

    // if ($t2) goto L0 else goto L1
    $tmp := $t2;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t10 := move($t22)
    call $t10 := $CopyOrMoveRef($t22);

    // destroy($t10)

    // LocalRoot($t21) <- $t10
    call $t21 := $WritebackToValue($t10, 21, $t21);

    // PackRef($t10)
    call $Libra_Libra_after_update_inv($tv0, $Dereference($t10));

    // $t11 := 10
    $tmp := $Integer(10);
    $t11 := $tmp;

    // abort($t11)
    if (true) { assume $DebugTrackAbort(9, 12518); }
    goto Abort;

    // L0:
L0:

    // $t12 := copy($t22)
    call $t12 := $CopyOrMoveRef($t22);

    // $t13 := get_field<Libra::Libra<#0>>.value($t12)
    call $tmp := $GetFieldFromReference($t12, $Libra_Libra_value);
    assume $IsValidU64($tmp);
    $t13 := $tmp;

    // Reference($t22) <- $t12
    call $t22 := $WritebackToReference($t12, $t22);

    // $t14 := move($t13)
    call $tmp := $CopyOrMoveValue($t13);
    $t14 := $tmp;

    // $t16 := -($t14, $t23)
    call $tmp := $Sub($t14, $t23);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 12584);
      goto Abort;
    }
    $t16 := $tmp;

    // $t17 := move($t22)
    call $t17 := $CopyOrMoveRef($t22);

    // $t18 := borrow_field<Libra::Libra<#0>>.value($t17)
    call $t18 := $BorrowField($t17, $Libra_Libra_value);
    assume $IsValidU64($Dereference($t18));

    // LocalRoot($t21) <- $t17
    call $t21 := $WritebackToValue($t17, 21, $t21);

    // UnpackRef($t18)

    // write_ref($t18, $t16)
    call $t18 := $WriteRef($t18, $t16);

    // LocalRoot($t21) <- $t18
    call $t21 := $WritebackToValue($t18, 21, $t21);

    // Reference($t17) <- $t18
    call $t17 := $WritebackToReference($t18, $t17);

    // PackRef($t17)
    call $Libra_Libra_after_update_inv($tv0, $Dereference($t17));

    // PackRef($t18)

    // $t20 := pack Libra::Libra<#0>($t23)
    call $tmp := $Libra_Libra_pack(0, 0, 0, $tv0, $t23);
    $t20 := $tmp;

    // return ($t20, $t21)
    $ret0 := $t20;
    if (true) { assume $DebugTrackLocal(9, 12602, 24, $ret0); }
    $ret1 := $t21;
    if (true) { assume $DebugTrackLocal(9, 12602, 25, $ret1); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
    $ret1 := $DefaultValue();
}
procedure {:inline 1} $Libra_withdraw($tv0: $TypeValue, coin: $Value, amount: $Value) returns ($ret0: $Value, $ret1: $Value)
free requires $Libra_Libra_is_well_formed(coin);
free requires $IsValidU64(amount);
requires $ExistsTxnSenderAccount($m, $txn);
free ensures b#$Boolean(old($Boolean(i#$Integer($SelectField(coin, $Libra_Libra_value)) < i#$Integer(amount)))) ==> $abort_flag;
free ensures $abort_flag ==> (b#$Boolean(old(($Boolean(i#$Integer($SelectField(coin, $Libra_Libra_value)) < i#$Integer(amount))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($SelectField($ret1, $Libra_Libra_value), $Integer(i#$Integer(old($SelectField(coin, $Libra_Libra_value))) - i#$Integer(amount))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($SelectField($ret0, $Libra_Libra_value), amount))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($Libra_sum_of_coin_values[$tv0], old($Libra_sum_of_coin_values[$tv0])))));
{
    call $ret0, $ret1 := $Libra_withdraw_def($tv0, coin, amount);
}

procedure {:inline 1} $Libra_zero_def($tv0: $TypeValue) returns ($ret0: $Value){
    // declare local variables
    var $t0: $Value; // $IntegerType()
    var $t1: $Value; // $Libra_Libra_type_value($tv0)
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time

    // bytecode translation starts here
    // Libra::assert_is_currency<#0>()
    call $Libra_assert_is_currency($tv0);
    if ($abort_flag) {
      assume $DebugTrackAbort(9, 13637);
      goto Abort;
    }

    // $t0 := 0
    $tmp := $Integer(0);
    $t0 := $tmp;

    // $t1 := pack Libra::Libra<#0>($t0)
    call $tmp := $Libra_Libra_pack(0, 0, 0, $tv0, $t0);
    $t1 := $tmp;

    // return $t1
    $ret0 := $t1;
    if (true) { assume $DebugTrackLocal(9, 11705, 2, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $Libra_zero($tv0: $TypeValue) returns ($ret0: $Value)
requires $ExistsTxnSenderAccount($m, $txn);
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($Libra_sum_of_coin_values[$tv0], old($Libra_sum_of_coin_values[$tv0])))));
{
    call $ret0 := $Libra_zero_def($tv0);
}



// ** spec vars of module LibraAccount



// ** spec funs of module LibraAccount

function {:inline} $LibraAccount_balance_of($m: $Memory, $txn: $Transaction, $tv0: $TypeValue, addr: $Value): $Value {
    $SelectField($SelectField($ResourceValue($m, $LibraAccount_LibraAccount_type_value($tv0), addr), $LibraAccount_LibraAccount_balance), $Libra_Libra_value)
}



// ** structs of module LibraAccount

const unique $LibraAccount_LibraAccount: $TypeName;
const $LibraAccount_LibraAccount_balance: $FieldName;
axiom $LibraAccount_LibraAccount_balance == 0;
function $LibraAccount_LibraAccount_type_value($tv0: $TypeValue): $TypeValue {
    $StructType($LibraAccount_LibraAccount, $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $tv0], 1), $TypeValueArray($MapConstTypeValue($DefaultTypeValue())[0 := $Libra_Libra_type_value($tv0)], 1))
}
function {:inline} $LibraAccount_LibraAccount_is_well_formed_types($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $Libra_Libra_is_well_formed_types($SelectField($this, $LibraAccount_LibraAccount_balance))
}
function {:inline} $LibraAccount_LibraAccount_is_well_formed($this: $Value): bool {
    $Vector_is_well_formed($this)
    && $vlen($this) == 1
      && $Libra_Libra_is_well_formed($SelectField($this, $LibraAccount_LibraAccount_balance))
}

axiom (forall m: $Memory, a: $Value, $tv0: $TypeValue :: $Memory__is_well_formed(m) && is#$Address(a) ==>
    $LibraAccount_LibraAccount_is_well_formed($ResourceValue(m, $LibraAccount_LibraAccount_type_value($tv0), a))
);

procedure {:inline 1} $LibraAccount_LibraAccount_before_update_inv($tv0: $TypeValue, $before: $Value) {
    call $Libra_Libra_before_update_inv($tv0, $SelectField($before, $LibraAccount_LibraAccount_balance));
}

procedure {:inline 1} $LibraAccount_LibraAccount_after_update_inv($tv0: $TypeValue, $after: $Value) {
    call $Libra_Libra_after_update_inv($tv0, $SelectField($after, $LibraAccount_LibraAccount_balance));
}

procedure {:inline 1} $LibraAccount_LibraAccount_pack($file_id: int, $byte_index: int, $var_idx: int, $tv0: $TypeValue, balance: $Value) returns ($struct: $Value)
{
    assume $Libra_Libra_is_well_formed(balance);
    $struct := $Vector($ValueArray($MapConstValue($DefaultValue())[0 := balance], 1));
    if ($byte_index > 0) { assume $DebugTrackLocal($file_id, $byte_index, $var_idx, $struct); }
}

procedure {:inline 1} $LibraAccount_LibraAccount_unpack($tv0: $TypeValue, $struct: $Value) returns (balance: $Value)
{
    assume is#$Vector($struct);
    balance := $SelectField($struct, $LibraAccount_LibraAccount_balance);
    assume $Libra_Libra_is_well_formed(balance);
}



// ** functions of module LibraAccount

procedure {:inline 1} $LibraAccount_deposit_def($tv0: $TypeValue, payee: $Value, to_deposit: $Value) returns (){
    // declare local variables
    var deposit_value: $Value; // $IntegerType()
    var $t3: $Value; // $BooleanType()
    var $t4: $Value; // $IntegerType()
    var $t5: $Value; // $Libra_Libra_type_value($tv0)
    var $t6: $Value; // $IntegerType()
    var $t7: $Value; // $IntegerType()
    var $t8: $Value; // $IntegerType()
    var $t9: $Value; // $BooleanType()
    var $t10: $Value; // $BooleanType()
    var $t11: $Value; // $IntegerType()
    var $t12: $Value; // $AddressType()
    var $t13: $Reference; // ReferenceType($LibraAccount_LibraAccount_type_value($tv0))
    var $t14: $Reference; // ReferenceType($Libra_Libra_type_value($tv0))
    var $t15: $Value; // $Libra_Libra_type_value($tv0)
    var $t16: $Value; // $AddressType()
    var $t17: $Value; // $Libra_Libra_type_value($tv0)
    var $t18: $Value; // $Libra_Libra_type_value($tv0)
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(10, 391, 0, payee); }
    if (true) { assume $DebugTrackLocal(10, 391, 1, to_deposit); }

    // bytecode translation starts here
    // $t16 := move(payee)
    call $tmp := $CopyOrMoveValue(payee);
    $t16 := $tmp;

    // $t17 := move(to_deposit)
    call $tmp := $CopyOrMoveValue(to_deposit);
    $t17 := $tmp;

    // $t5 := copy($t17)
    call $tmp := $CopyOrMoveValue($t17);
    $t5 := $tmp;

    // $t6 := Libra::value<#0>($t5)
    call $t6 := $Libra_value($tv0, $t5);
    if ($abort_flag) {
      assume $DebugTrackAbort(10, 596);
      goto Abort;
    }
    assume $IsValidU64($t6);


    // deposit_value := $t6
    call $tmp := $CopyOrMoveValue($t6);
    deposit_value := $tmp;
    if (true) { assume $DebugTrackLocal(10, 573, 2, $tmp); }

    // $t8 := 0
    $tmp := $Integer(0);
    $t8 := $tmp;

    // $t9 := >(deposit_value, $t8)
    call $tmp := $Gt(deposit_value, $t8);
    $t9 := $tmp;

    // $t3 := $t9
    call $tmp := $CopyOrMoveValue($t9);
    $t3 := $tmp;
    if (true) { assume $DebugTrackLocal(10, 624, 3, $tmp); }

    // if ($t3) goto L0 else goto L1
    $tmp := $t3;
    if (b#$Boolean($tmp)) { goto L0; } else { goto L1; }

    // L1:
L1:

    // $t11 := 7
    $tmp := $Integer(7);
    $t11 := $tmp;

    // abort($t11)
    if (true) { assume $DebugTrackAbort(10, 624); }
    goto Abort;

    // L0:
L0:

    // $t13 := borrow_global<LibraAccount::LibraAccount<#0>>($t16)
    call $t13 := $BorrowGlobal($t16, $LibraAccount_LibraAccount_type_value($tv0));
    if ($abort_flag) {
      assume $DebugTrackAbort(10, 724);
      goto Abort;
    }
    assume $LibraAccount_LibraAccount_is_well_formed($Dereference($t13));

    // UnpackRef($t13)
    call $LibraAccount_LibraAccount_before_update_inv($tv0, $Dereference($t13));

    // $t14 := borrow_field<LibraAccount::LibraAccount<#0>>.balance($t13)
    call $t14 := $BorrowField($t13, $LibraAccount_LibraAccount_balance);
    assume $Libra_Libra_is_well_formed_types($Dereference($t14));

    // LibraAccount::LibraAccount <- $t13
    call $WritebackToGlobal($t13);

    // UnpackRef($t14)
    call $Libra_Libra_before_update_inv($tv0, $Dereference($t14));

    // PackRef($t14)
    call $Libra_Libra_after_update_inv($tv0, $Dereference($t14));

    // $t18 := read_ref($t14)
    call $tmp := $ReadRef($t14);
    assume $Libra_Libra_is_well_formed($tmp);
    $t18 := $tmp;

    // $t18 := Libra::deposit<#0>($t18, $t17)
    call $t18 := $Libra_deposit($tv0, $t18, $t17);
    if ($abort_flag) {
      assume $DebugTrackAbort(10, 711);
      goto Abort;
    }
    assume $Libra_Libra_is_well_formed($t18);


    // write_ref($t14, $t18)
    call $t14 := $WriteRef($t14, $t18);

    // LibraAccount::LibraAccount <- $t14
    call $WritebackToGlobal($t14);

    // Reference($t13) <- $t14
    call $t13 := $WritebackToReference($t14, $t13);

    // UnpackRef($t14)
    call $Libra_Libra_before_update_inv($tv0, $Dereference($t14));

    // PackRef($t13)
    call $LibraAccount_LibraAccount_after_update_inv($tv0, $Dereference($t13));

    // PackRef($t14)
    call $Libra_Libra_after_update_inv($tv0, $Dereference($t14));

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraAccount_deposit($tv0: $TypeValue, payee: $Value, to_deposit: $Value) returns ()
free requires is#$Address(payee);
free requires $Libra_Libra_is_well_formed(to_deposit);
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $LibraAccount_deposit_def($tv0, payee, to_deposit);
}

procedure {:inline 1} $LibraAccount_pay_from_def($tv0: $TypeValue, payer: $Value, payee: $Value, amount: $Value) returns (){
    // declare local variables
    var $t3: $Value; // $AddressType()
    var $t4: $Value; // $AddressType()
    var $t5: $Value; // $IntegerType()
    var $t6: $Value; // $Libra_Libra_type_value($tv0)
    var $t7: $Value; // $AddressType()
    var $t8: $Value; // $AddressType()
    var $t9: $Value; // $IntegerType()
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(10, 1302, 0, payer); }
    if (true) { assume $DebugTrackLocal(10, 1302, 1, payee); }
    if (true) { assume $DebugTrackLocal(10, 1302, 2, amount); }

    // bytecode translation starts here
    // $t7 := move(payer)
    call $tmp := $CopyOrMoveValue(payer);
    $t7 := $tmp;

    // $t8 := move(payee)
    call $tmp := $CopyOrMoveValue(payee);
    $t8 := $tmp;

    // $t9 := move(amount)
    call $tmp := $CopyOrMoveValue(amount);
    $t9 := $tmp;

    // $t6 := LibraAccount::withdraw_from<#0>($t7, $t9)
    call $t6 := $LibraAccount_withdraw_from($tv0, $t7, $t9);
    if ($abort_flag) {
      assume $DebugTrackAbort(10, 869);
      goto Abort;
    }
    assume $Libra_Libra_is_well_formed($t6);


    // LibraAccount::deposit<#0>($t8, $t6)
    call $LibraAccount_deposit($tv0, $t8, $t6);
    if ($abort_flag) {
      assume $DebugTrackAbort(10, 395);
      goto Abort;
    }

    // return ()
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
}
procedure {:inline 1} $LibraAccount_pay_from($tv0: $TypeValue, payer: $Value, payee: $Value, amount: $Value) returns ()
free requires is#$Address(payer);
free requires is#$Address(payee);
free requires $IsValidU64(amount);
requires $ExistsTxnSenderAccount($m, $txn);
requires b#$Boolean($Boolean(!$IsEqual(amount, $Integer(0))))
    || b#$Boolean($Boolean(!b#$Boolean($ResourceExists($m, $LibraAccount_LibraAccount_type_value($tv0), payer))))
    || b#$Boolean($Boolean(!b#$Boolean($ResourceExists($m, $LibraAccount_LibraAccount_type_value($tv0), payee))));
free ensures b#$Boolean(old($Boolean(!b#$Boolean($ResourceExists($m, $LibraAccount_LibraAccount_type_value($tv0), payer))))) ==> $abort_flag;
free ensures b#$Boolean(old($Boolean(!b#$Boolean($ResourceExists($m, $LibraAccount_LibraAccount_type_value($tv0), payee))))) ==> $abort_flag;
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($LibraAccount_balance_of($m, $txn, $tv0, payer), $Integer(i#$Integer(old($LibraAccount_balance_of($m, $txn, $tv0, payer))) - i#$Integer(amount))))));
free ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($LibraAccount_balance_of($m, $txn, $tv0, payee), $Integer(i#$Integer(old($LibraAccount_balance_of($m, $txn, $tv0, payee))) + i#$Integer(amount))))));
{
    call $LibraAccount_pay_from_def($tv0, payer, payee, amount);
}

procedure  $LibraAccount_pay_from_verify($tv0: $TypeValue, payer: $Value, payee: $Value, amount: $Value) returns ()
free requires is#$Address(payer);
free requires is#$Address(payee);
free requires $IsValidU64(amount);
requires $ExistsTxnSenderAccount($m, $txn);
requires b#$Boolean($Boolean(!$IsEqual(amount, $Integer(0))))
    || b#$Boolean($Boolean(!b#$Boolean($ResourceExists($m, $LibraAccount_LibraAccount_type_value($tv0), payer))))
    || b#$Boolean($Boolean(!b#$Boolean($ResourceExists($m, $LibraAccount_LibraAccount_type_value($tv0), payee))));
ensures b#$Boolean(old($Boolean(!b#$Boolean($ResourceExists($m, $LibraAccount_LibraAccount_type_value($tv0), payer))))) ==> $abort_flag;
ensures b#$Boolean(old($Boolean(!b#$Boolean($ResourceExists($m, $LibraAccount_LibraAccount_type_value($tv0), payee))))) ==> $abort_flag;
ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($LibraAccount_balance_of($m, $txn, $tv0, payer), $Integer(i#$Integer(old($LibraAccount_balance_of($m, $txn, $tv0, payer))) - i#$Integer(amount))))));
ensures !$abort_flag ==> (b#$Boolean($Boolean($IsEqual($LibraAccount_balance_of($m, $txn, $tv0, payee), $Integer(i#$Integer(old($LibraAccount_balance_of($m, $txn, $tv0, payee))) + i#$Integer(amount))))));
{
    call $InitVerification();
    assume $Memory__is_well_formed($m);
    assume $ExistsTxnSenderAccount($m, $txn);
    assume b#$Boolean($Boolean(!$IsEqual(amount, $Integer(0))));
    call $LibraAccount_pay_from_def($tv0, payer, payee, amount);
}

procedure {:inline 1} $LibraAccount_withdraw_from_def($tv0: $TypeValue, payer: $Value, amount: $Value) returns ($ret0: $Value){
    // declare local variables
    var account_balance: $Reference; // ReferenceType($LibraAccount_LibraAccount_type_value($tv0))
    var $t3: $Value; // $AddressType()
    var $t4: $Reference; // ReferenceType($LibraAccount_LibraAccount_type_value($tv0))
    var $t5: $Reference; // ReferenceType($LibraAccount_LibraAccount_type_value($tv0))
    var $t6: $Reference; // ReferenceType($Libra_Libra_type_value($tv0))
    var $t7: $Value; // $IntegerType()
    var $t8: $Value; // $Libra_Libra_type_value($tv0)
    var $t9: $Value; // $AddressType()
    var $t10: $Value; // $IntegerType()
    var $t11: $Value; // $Libra_Libra_type_value($tv0)
    var $tmp: $Value;
    var $saved_m: $Memory;

    // initialize function execution
    assume !$abort_flag;
    $saved_m := $m;

    // track values of parameters at entry time
    if (true) { assume $DebugTrackLocal(10, 865, 0, payer); }
    if (true) { assume $DebugTrackLocal(10, 865, 1, amount); }

    // bytecode translation starts here
    // $t9 := move(payer)
    call $tmp := $CopyOrMoveValue(payer);
    $t9 := $tmp;

    // $t10 := move(amount)
    call $tmp := $CopyOrMoveValue(amount);
    $t10 := $tmp;

    // $t4 := borrow_global<LibraAccount::LibraAccount<#0>>($t9)
    call $t4 := $BorrowGlobal($t9, $LibraAccount_LibraAccount_type_value($tv0));
    if ($abort_flag) {
      assume $DebugTrackAbort(10, 1060);
      goto Abort;
    }
    assume $LibraAccount_LibraAccount_is_well_formed($Dereference($t4));

    // UnpackRef($t4)
    call $LibraAccount_LibraAccount_before_update_inv($tv0, $Dereference($t4));

    // account_balance := $t4
    call account_balance := $CopyOrMoveRef($t4);
    if (true) { assume $DebugTrackLocal(10, 1042, 2, $Dereference(account_balance)); }

    // $t5 := move(account_balance)
    call $t5 := $CopyOrMoveRef(account_balance);

    // $t6 := borrow_field<LibraAccount::LibraAccount<#0>>.balance($t5)
    call $t6 := $BorrowField($t5, $LibraAccount_LibraAccount_balance);
    assume $Libra_Libra_is_well_formed_types($Dereference($t6));

    // LibraAccount::LibraAccount <- $t5
    call $WritebackToGlobal($t5);

    // UnpackRef($t6)
    call $Libra_Libra_before_update_inv($tv0, $Dereference($t6));

    // PackRef($t6)
    call $Libra_Libra_after_update_inv($tv0, $Dereference($t6));

    // $t11 := read_ref($t6)
    call $tmp := $ReadRef($t6);
    assume $Libra_Libra_is_well_formed($tmp);
    $t11 := $tmp;

    // ($t8, $t11) := Libra::withdraw<#0>($t11, $t10)
    call $t8, $t11 := $Libra_withdraw($tv0, $t11, $t10);
    if ($abort_flag) {
      assume $DebugTrackAbort(10, 1125);
      goto Abort;
    }
    assume $Libra_Libra_is_well_formed($t8);

    assume $Libra_Libra_is_well_formed($t11);


    // write_ref($t6, $t11)
    call $t6 := $WriteRef($t6, $t11);
    if (true) { assume $DebugTrackLocal(10, 865, 2, $Dereference(account_balance)); }

    // LibraAccount::LibraAccount <- $t6
    call $WritebackToGlobal($t6);

    // Reference($t5) <- $t6
    call $t5 := $WritebackToReference($t6, $t5);

    // UnpackRef($t6)
    call $Libra_Libra_before_update_inv($tv0, $Dereference($t6));

    // PackRef($t5)
    call $LibraAccount_LibraAccount_after_update_inv($tv0, $Dereference($t5));

    // PackRef($t6)
    call $Libra_Libra_after_update_inv($tv0, $Dereference($t6));

    // return $t8
    $ret0 := $t8;
    if (true) { assume $DebugTrackLocal(10, 1118, 12, $ret0); }
    return;

Abort:
    $abort_flag := true;
    $m := $saved_m;
    $ret0 := $DefaultValue();
}
procedure {:inline 1} $LibraAccount_withdraw_from($tv0: $TypeValue, payer: $Value, amount: $Value) returns ($ret0: $Value)
free requires is#$Address(payer);
free requires $IsValidU64(amount);
requires $ExistsTxnSenderAccount($m, $txn);
{
    call $ret0 := $LibraAccount_withdraw_from_def($tv0, payer, amount);
}
