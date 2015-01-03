// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out --gpuverify-entry-points %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtUnsatisfiableEntryRequires 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingRequires 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingEnsures 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtUnsatisfiableAssume 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtUnsatisfiableEnsures 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtUnsatisfiableAxiom 0

type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);



var {:source_name "A"} {:global} $$A: [bv32]bv32;

axiom {:array_info "$$A"} {:global} {:elem_width 32} {:source_name "A"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$A: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$A: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$A: bool;

const $arrayId$$A: arrayId;

axiom $arrayId$$A == 1bv2;

var {:source_name "dest"} {:global} $$dest: [bv32]bv32;

axiom {:array_info "$$dest"} {:global} {:elem_width 32} {:source_name "dest"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$dest: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$dest: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$dest: bool;

const $arrayId$$dest: arrayId;

axiom $arrayId$$dest == 2bv2;

type ptr = bv32;

type arrayId = bv2;

function {:inline true} MKPTR(base: arrayId, offset: bv32) : ptr
{
  base ++ offset[30:0]
}

function {:inline true} base#MKPTR(p: ptr) : arrayId
{
  p[32:30]
}

function {:inline true} offset#MKPTR(p: ptr) : bv32
{
  0bv2 ++ p[30:0]
}

const $arrayId$$null$: arrayId;

axiom $arrayId$$null$ == 0bv2;

const _WATCHED_OFFSET: bv32;

const {:group_id_x} group_id_x$1: bv32;

const {:group_id_x} group_id_x$2: bv32;

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:local_id_x} local_id_x$1: bv32;

const {:local_id_x} local_id_x$2: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

function {:bvbuiltin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:bvbuiltin "bvand"} BV32_AND(bv32, bv32) : bv32;

function {:bvbuiltin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

function {:bvbuiltin "bvshl"} BV32_SHL(bv32, bv32) : bv32;

function {:bvbuiltin "bvslt"} BV32_SLT(bv32, bv32) : bool;

function {:bvbuiltin "bvsub"} BV32_SUB(bv32, bv32) : bv32;

function {:bvbuiltin "bvuge"} BV32_UGE(bv32, bv32) : bool;

procedure {:source_name "prefix_sum"} {:kernel} $prefix_sum();
  requires !_READ_HAS_OCCURRED_$$A && !_WRITE_HAS_OCCURRED_$$A && !_ATOMIC_HAS_OCCURRED_$$A;
  requires !_READ_HAS_OCCURRED_$$dest && !_WRITE_HAS_OCCURRED_$$dest && !_ATOMIC_HAS_OCCURRED_$$dest;
  requires BV32_SGT(group_size_x, 0bv32);
  requires BV32_SGT(num_groups_x, 0bv32);
  requires BV32_SGE(group_id_x$1, 0bv32);
  requires BV32_SGE(group_id_x$2, 0bv32);
  requires BV32_SLT(group_id_x$1, num_groups_x);
  requires BV32_SLT(group_id_x$2, num_groups_x);
  requires BV32_SGE(local_id_x$1, 0bv32);
  requires BV32_SGE(local_id_x$2, 0bv32);
  requires BV32_SLT(local_id_x$1, group_size_x);
  requires BV32_SLT(local_id_x$2, group_size_x);
  requires BV32_SGT(group_size_y, 0bv32);
  requires BV32_SGT(num_groups_y, 0bv32);
  requires BV32_SGE(group_id_y$1, 0bv32);
  requires BV32_SGE(group_id_y$2, 0bv32);
  requires BV32_SLT(group_id_y$1, num_groups_y);
  requires BV32_SLT(group_id_y$2, num_groups_y);
  requires BV32_SGE(local_id_y$1, 0bv32);
  requires BV32_SGE(local_id_y$2, 0bv32);
  requires BV32_SLT(local_id_y$1, group_size_y);
  requires BV32_SLT(local_id_y$2, group_size_y);
  requires BV32_SGT(group_size_z, 0bv32);
  requires BV32_SGT(num_groups_z, 0bv32);
  requires BV32_SGE(group_id_z$1, 0bv32);
  requires BV32_SGE(group_id_z$2, 0bv32);
  requires BV32_SLT(group_id_z$1, num_groups_z);
  requires BV32_SLT(group_id_z$2, num_groups_z);
  requires BV32_SGE(local_id_z$1, 0bv32);
  requires BV32_SGE(local_id_z$2, 0bv32);
  requires BV32_SLT(local_id_z$1, group_size_z);
  requires BV32_SLT(local_id_z$2, group_size_z);
  requires group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> local_id_x$1 != local_id_x$2 || local_id_y$1 != local_id_y$2 || local_id_z$1 != local_id_z$2;
  modifies _READ_HAS_OCCURRED_$$dest, _READ_HAS_OCCURRED_$$A, _WRITE_HAS_OCCURRED_$$dest, _WRITE_READ_BENIGN_FLAG_$$dest, _WRITE_READ_BENIGN_FLAG_$$dest, _WRITE_HAS_OCCURRED_$$A, _WRITE_READ_BENIGN_FLAG_$$A, _WRITE_READ_BENIGN_FLAG_$$A, $$A, $$dest, _TRACKING;



implementation {:source_name "prefix_sum"} {:kernel} $prefix_sum()
{
  var $d.0: bv32;
  var $.01: ptr;
  var $.0: ptr;
  var v2$1: bool;
  var v2$2: bool;
  var v0$1: bv32;
  var v0$2: bv32;
  var v1: bool;
  var v3$1: bv32;
  var v3$2: bv32;
  var v4$1: bv32;
  var v4$2: bv32;
  var v5$1: bv32;
  var v5$2: bv32;
  var p0$1: bool;
  var p0$2: bool;
  var p1$1: bool;
  var p1$2: bool;
  var p2$1: bool;
  var p2$2: bool;
  var p3$1: bool;
  var p3$2: bool;
  var p4$1: bool;
  var p4$2: bool;
  var p5$1: bool;
  var p5$2: bool;
  var p6$1: bool;
  var p6$2: bool;
  var p7$1: bool;
  var p7$2: bool;
  var p8$1: bool;
  var p8$2: bool;
  var p9$1: bool;
  var p9$2: bool;
  var p10$1: bool;
  var p10$2: bool;
  var p11$1: bool;
  var p11$2: bool;
  var p12$1: bool;
  var p12$2: bool;
  var p13$1: bool;
  var p13$2: bool;
  var p14$1: bool;
  var p14$2: bool;
  var p15$1: bool;
  var p15$2: bool;
  var p16$1: bool;
  var p16$2: bool;
  var p17$1: bool;
  var p17$2: bool;
  var p18$1: bool;
  var p18$2: bool;
  var p19$1: bool;
  var p19$2: bool;
  var p20$1: bool;
  var p20$2: bool;
  var p21$1: bool;
  var p21$2: bool;


  $0:
    v0$1 := BV32_ADD(BV32_MUL(group_size_x, group_id_x$1), local_id_x$1);
    v0$2 := BV32_ADD(BV32_MUL(group_size_x, group_id_x$2), local_id_x$2);
    $d.0, $.01, $.0 := 0bv32, MKPTR($arrayId$$dest, 0bv32), MKPTR($arrayId$$A, 0bv32);
    assume {:captureState "loop_entry_state_0_0"} true;
    goto $1;

  $1:
    assume {:captureState "loop_head_state_0"} true;
    assert {:block_sourceloc} {:sourceloc_num 1} true;
    v1 := BV32_SLT($d.0, 3bv32);
    p0$1 := false;
    p0$2 := false;
    p1$1 := false;
    p1$2 := false;
    p2$1 := false;
    p2$2 := false;
    p3$1 := false;
    p3$2 := false;
    p4$1 := false;
    p4$2 := false;
    p5$1 := false;
    p5$2 := false;
    p6$1 := false;
    p6$2 := false;
    p7$1 := false;
    p7$2 := false;
    p8$1 := false;
    p8$2 := false;
    p9$1 := false;
    p9$2 := false;
    p10$1 := false;
    p10$2 := false;
    p11$1 := false;
    p11$2 := false;
    p12$1 := false;
    p12$2 := false;
    p13$1 := false;
    p13$2 := false;
    p14$1 := false;
    p14$2 := false;
    p15$1 := false;
    p15$2 := false;
    p16$1 := false;
    p16$2 := false;
    p17$1 := false;
    p17$2 := false;
    p18$1 := false;
    p18$2 := false;
    p19$1 := false;
    p19$2 := false;
    p20$1 := false;
    p20$2 := false;
    p21$1 := false;
    p21$2 := false;
    goto __partitioned_block_$truebb_0, $falsebb;

  $falsebb:
    assume {:partition} !v1 && !v1;
    return;

  __partitioned_block_$truebb_0:
    assume {:partition} v1 && v1;
    v2$1 := BV32_UGE(v0$1, BV32_SHL(1bv32, BV32_AND($d.0, 31bv32)));
    v2$2 := BV32_UGE(v0$2, BV32_SHL(1bv32, BV32_AND($d.0, 31bv32)));
    p0$1 := (if v2$1 then v2$1 else p0$1);
    p0$2 := (if v2$2 then v2$2 else p0$2);
    p13$1 := (if !v2$1 then !v2$1 else p13$1);
    p13$2 := (if !v2$2 then !v2$2 else p13$2);
    p1$1 := (if p0$1 && base#MKPTR($.0) == $arrayId$$dest then base#MKPTR($.0) == $arrayId$$dest else p1$1);
    p1$2 := (if p0$2 && base#MKPTR($.0) == $arrayId$$dest then base#MKPTR($.0) == $arrayId$$dest else p1$2);
    p2$1 := (if p0$1 && base#MKPTR($.0) != $arrayId$$dest then base#MKPTR($.0) != $arrayId$$dest else p2$1);
    p2$2 := (if p0$2 && base#MKPTR($.0) != $arrayId$$dest then base#MKPTR($.0) != $arrayId$$dest else p2$2);
    call {:sourceloc} {:sourceloc_num 4} _LOG_READ_$$dest(p1$1, BV32_ADD(offset#MKPTR($.0), BV32_SUB(v0$1, BV32_SHL(1bv32, BV32_AND($d.0, 31bv32)))), $$dest[BV32_ADD(offset#MKPTR($.0), BV32_SUB(v0$1, BV32_SHL(1bv32, BV32_AND($d.0, 31bv32))))]);
    assume {:do_not_predicate} {:check_id "check_state_9"} {:captureState "check_state_9"} {:sourceloc} {:sourceloc_num 4} true;
    call {:check_id "check_state_9"} {:sourceloc} {:sourceloc_num 4} _CHECK_READ_$$dest(p1$2, BV32_ADD(offset#MKPTR($.0), BV32_SUB(v0$2, BV32_SHL(1bv32, BV32_AND($d.0, 31bv32)))), $$dest[BV32_ADD(offset#MKPTR($.0), BV32_SUB(v0$2, BV32_SHL(1bv32, BV32_AND($d.0, 31bv32))))]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$dest"} true;
    v3$1 := (if p1$1 then $$dest[BV32_ADD(offset#MKPTR($.0), BV32_SUB(v0$1, BV32_SHL(1bv32, BV32_AND($d.0, 31bv32))))] else v3$1);
    v3$2 := (if p1$2 then $$dest[BV32_ADD(offset#MKPTR($.0), BV32_SUB(v0$2, BV32_SHL(1bv32, BV32_AND($d.0, 31bv32))))] else v3$2);
    p4$1 := (if p2$1 && base#MKPTR($.0) == $arrayId$$A then base#MKPTR($.0) == $arrayId$$A else p4$1);
    p4$2 := (if p2$2 && base#MKPTR($.0) == $arrayId$$A then base#MKPTR($.0) == $arrayId$$A else p4$2);
    p3$1 := (if p2$1 && base#MKPTR($.0) != $arrayId$$A then base#MKPTR($.0) != $arrayId$$A else p3$1);
    p3$2 := (if p2$2 && base#MKPTR($.0) != $arrayId$$A then base#MKPTR($.0) != $arrayId$$A else p3$2);
    assert {:bad_pointer_access} {:sourceloc_num 6} {:thread 1} p3$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 6} {:thread 2} p3$2 ==> false;
    call {:sourceloc} {:sourceloc_num 5} _LOG_READ_$$A(p4$1, BV32_ADD(offset#MKPTR($.0), BV32_SUB(v0$1, BV32_SHL(1bv32, BV32_AND($d.0, 31bv32)))), $$A[BV32_ADD(offset#MKPTR($.0), BV32_SUB(v0$1, BV32_SHL(1bv32, BV32_AND($d.0, 31bv32))))]);
    assume {:do_not_predicate} {:check_id "check_state_8"} {:captureState "check_state_8"} {:sourceloc} {:sourceloc_num 5} true;
    call {:check_id "check_state_8"} {:sourceloc} {:sourceloc_num 5} _CHECK_READ_$$A(p4$2, BV32_ADD(offset#MKPTR($.0), BV32_SUB(v0$2, BV32_SHL(1bv32, BV32_AND($d.0, 31bv32)))), $$A[BV32_ADD(offset#MKPTR($.0), BV32_SUB(v0$2, BV32_SHL(1bv32, BV32_AND($d.0, 31bv32))))]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    v3$1 := (if p4$1 then $$A[BV32_ADD(offset#MKPTR($.0), BV32_SUB(v0$1, BV32_SHL(1bv32, BV32_AND($d.0, 31bv32))))] else v3$1);
    v3$2 := (if p4$2 then $$A[BV32_ADD(offset#MKPTR($.0), BV32_SUB(v0$2, BV32_SHL(1bv32, BV32_AND($d.0, 31bv32))))] else v3$2);
    p5$1 := (if p0$1 && base#MKPTR($.0) == $arrayId$$dest then base#MKPTR($.0) == $arrayId$$dest else p5$1);
    p5$2 := (if p0$2 && base#MKPTR($.0) == $arrayId$$dest then base#MKPTR($.0) == $arrayId$$dest else p5$2);
    p6$1 := (if p0$1 && base#MKPTR($.0) != $arrayId$$dest then base#MKPTR($.0) != $arrayId$$dest else p6$1);
    p6$2 := (if p0$2 && base#MKPTR($.0) != $arrayId$$dest then base#MKPTR($.0) != $arrayId$$dest else p6$2);
    call {:sourceloc} {:sourceloc_num 7} _LOG_READ_$$dest(p5$1, BV32_ADD(offset#MKPTR($.0), v0$1), $$dest[BV32_ADD(offset#MKPTR($.0), v0$1)]);
    assume {:do_not_predicate} {:check_id "check_state_7"} {:captureState "check_state_7"} {:sourceloc} {:sourceloc_num 7} true;
    call {:check_id "check_state_7"} {:sourceloc} {:sourceloc_num 7} _CHECK_READ_$$dest(p5$2, BV32_ADD(offset#MKPTR($.0), v0$2), $$dest[BV32_ADD(offset#MKPTR($.0), v0$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$dest"} true;
    v4$1 := (if p5$1 then $$dest[BV32_ADD(offset#MKPTR($.0), v0$1)] else v4$1);
    v4$2 := (if p5$2 then $$dest[BV32_ADD(offset#MKPTR($.0), v0$2)] else v4$2);
    p8$1 := (if p6$1 && base#MKPTR($.0) == $arrayId$$A then base#MKPTR($.0) == $arrayId$$A else p8$1);
    p8$2 := (if p6$2 && base#MKPTR($.0) == $arrayId$$A then base#MKPTR($.0) == $arrayId$$A else p8$2);
    p7$1 := (if p6$1 && base#MKPTR($.0) != $arrayId$$A then base#MKPTR($.0) != $arrayId$$A else p7$1);
    p7$2 := (if p6$2 && base#MKPTR($.0) != $arrayId$$A then base#MKPTR($.0) != $arrayId$$A else p7$2);
    assert {:bad_pointer_access} {:sourceloc_num 9} {:thread 1} p7$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 9} {:thread 2} p7$2 ==> false;
    call {:sourceloc} {:sourceloc_num 8} _LOG_READ_$$A(p8$1, BV32_ADD(offset#MKPTR($.0), v0$1), $$A[BV32_ADD(offset#MKPTR($.0), v0$1)]);
    assume {:do_not_predicate} {:check_id "check_state_6"} {:captureState "check_state_6"} {:sourceloc} {:sourceloc_num 8} true;
    call {:check_id "check_state_6"} {:sourceloc} {:sourceloc_num 8} _CHECK_READ_$$A(p8$2, BV32_ADD(offset#MKPTR($.0), v0$2), $$A[BV32_ADD(offset#MKPTR($.0), v0$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    v4$1 := (if p8$1 then $$A[BV32_ADD(offset#MKPTR($.0), v0$1)] else v4$1);
    v4$2 := (if p8$2 then $$A[BV32_ADD(offset#MKPTR($.0), v0$2)] else v4$2);
    p9$1 := (if p0$1 && base#MKPTR($.01) == $arrayId$$dest then base#MKPTR($.01) == $arrayId$$dest else p9$1);
    p9$2 := (if p0$2 && base#MKPTR($.01) == $arrayId$$dest then base#MKPTR($.01) == $arrayId$$dest else p9$2);
    p10$1 := (if p0$1 && base#MKPTR($.01) != $arrayId$$dest then base#MKPTR($.01) != $arrayId$$dest else p10$1);
    p10$2 := (if p0$2 && base#MKPTR($.01) != $arrayId$$dest then base#MKPTR($.01) != $arrayId$$dest else p10$2);
    call {:sourceloc} {:sourceloc_num 10} _LOG_WRITE_$$dest(p9$1, BV32_ADD(offset#MKPTR($.01), v0$1), BV32_ADD(v3$1, v4$1), $$dest[BV32_ADD(offset#MKPTR($.01), v0$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$dest(p9$2, BV32_ADD(offset#MKPTR($.01), v0$2));
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 10} true;
    call {:check_id "check_state_5"} {:sourceloc} {:sourceloc_num 10} _CHECK_WRITE_$$dest(p9$2, BV32_ADD(offset#MKPTR($.01), v0$2), BV32_ADD(v3$2, v4$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$dest"} true;
    $$dest[BV32_ADD(offset#MKPTR($.01), v0$1)] := (if p9$1 then BV32_ADD(v3$1, v4$1) else $$dest[BV32_ADD(offset#MKPTR($.01), v0$1)]);
    $$dest[BV32_ADD(offset#MKPTR($.01), v0$2)] := (if p9$2 then BV32_ADD(v3$2, v4$2) else $$dest[BV32_ADD(offset#MKPTR($.01), v0$2)]);
    p12$1 := (if p10$1 && base#MKPTR($.01) == $arrayId$$A then base#MKPTR($.01) == $arrayId$$A else p12$1);
    p12$2 := (if p10$2 && base#MKPTR($.01) == $arrayId$$A then base#MKPTR($.01) == $arrayId$$A else p12$2);
    p11$1 := (if p10$1 && base#MKPTR($.01) != $arrayId$$A then base#MKPTR($.01) != $arrayId$$A else p11$1);
    p11$2 := (if p10$2 && base#MKPTR($.01) != $arrayId$$A then base#MKPTR($.01) != $arrayId$$A else p11$2);
    assert {:bad_pointer_access} {:sourceloc_num 12} {:thread 1} p11$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 12} {:thread 2} p11$2 ==> false;
    call {:sourceloc} {:sourceloc_num 11} _LOG_WRITE_$$A(p12$1, BV32_ADD(offset#MKPTR($.01), v0$1), BV32_ADD(v3$1, v4$1), $$A[BV32_ADD(offset#MKPTR($.01), v0$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(p12$2, BV32_ADD(offset#MKPTR($.01), v0$2));
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 11} true;
    call {:check_id "check_state_4"} {:sourceloc} {:sourceloc_num 11} _CHECK_WRITE_$$A(p12$2, BV32_ADD(offset#MKPTR($.01), v0$2), BV32_ADD(v3$2, v4$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    $$A[BV32_ADD(offset#MKPTR($.01), v0$1)] := (if p12$1 then BV32_ADD(v3$1, v4$1) else $$A[BV32_ADD(offset#MKPTR($.01), v0$1)]);
    $$A[BV32_ADD(offset#MKPTR($.01), v0$2)] := (if p12$2 then BV32_ADD(v3$2, v4$2) else $$A[BV32_ADD(offset#MKPTR($.01), v0$2)]);
    p14$1 := (if p13$1 && base#MKPTR($.0) == $arrayId$$dest then base#MKPTR($.0) == $arrayId$$dest else p14$1);
    p14$2 := (if p13$2 && base#MKPTR($.0) == $arrayId$$dest then base#MKPTR($.0) == $arrayId$$dest else p14$2);
    p15$1 := (if p13$1 && base#MKPTR($.0) != $arrayId$$dest then base#MKPTR($.0) != $arrayId$$dest else p15$1);
    p15$2 := (if p13$2 && base#MKPTR($.0) != $arrayId$$dest then base#MKPTR($.0) != $arrayId$$dest else p15$2);
    call {:sourceloc} {:sourceloc_num 14} _LOG_READ_$$dest(p14$1, BV32_ADD(offset#MKPTR($.0), v0$1), $$dest[BV32_ADD(offset#MKPTR($.0), v0$1)]);
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 14} true;
    call {:check_id "check_state_3"} {:sourceloc} {:sourceloc_num 14} _CHECK_READ_$$dest(p14$2, BV32_ADD(offset#MKPTR($.0), v0$2), $$dest[BV32_ADD(offset#MKPTR($.0), v0$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$dest"} true;
    v5$1 := (if p14$1 then $$dest[BV32_ADD(offset#MKPTR($.0), v0$1)] else v5$1);
    v5$2 := (if p14$2 then $$dest[BV32_ADD(offset#MKPTR($.0), v0$2)] else v5$2);
    p17$1 := (if p15$1 && base#MKPTR($.0) == $arrayId$$A then base#MKPTR($.0) == $arrayId$$A else p17$1);
    p17$2 := (if p15$2 && base#MKPTR($.0) == $arrayId$$A then base#MKPTR($.0) == $arrayId$$A else p17$2);
    p16$1 := (if p15$1 && base#MKPTR($.0) != $arrayId$$A then base#MKPTR($.0) != $arrayId$$A else p16$1);
    p16$2 := (if p15$2 && base#MKPTR($.0) != $arrayId$$A then base#MKPTR($.0) != $arrayId$$A else p16$2);
    assert {:bad_pointer_access} {:sourceloc_num 16} {:thread 1} p16$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 16} {:thread 2} p16$2 ==> false;
    call {:sourceloc} {:sourceloc_num 15} _LOG_READ_$$A(p17$1, BV32_ADD(offset#MKPTR($.0), v0$1), $$A[BV32_ADD(offset#MKPTR($.0), v0$1)]);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 15} true;
    call {:check_id "check_state_2"} {:sourceloc} {:sourceloc_num 15} _CHECK_READ_$$A(p17$2, BV32_ADD(offset#MKPTR($.0), v0$2), $$A[BV32_ADD(offset#MKPTR($.0), v0$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    v5$1 := (if p17$1 then $$A[BV32_ADD(offset#MKPTR($.0), v0$1)] else v5$1);
    v5$2 := (if p17$2 then $$A[BV32_ADD(offset#MKPTR($.0), v0$2)] else v5$2);
    p18$1 := (if p13$1 && base#MKPTR($.01) == $arrayId$$dest then base#MKPTR($.01) == $arrayId$$dest else p18$1);
    p18$2 := (if p13$2 && base#MKPTR($.01) == $arrayId$$dest then base#MKPTR($.01) == $arrayId$$dest else p18$2);
    p19$1 := (if p13$1 && base#MKPTR($.01) != $arrayId$$dest then base#MKPTR($.01) != $arrayId$$dest else p19$1);
    p19$2 := (if p13$2 && base#MKPTR($.01) != $arrayId$$dest then base#MKPTR($.01) != $arrayId$$dest else p19$2);
    call {:sourceloc} {:sourceloc_num 17} _LOG_WRITE_$$dest(p18$1, BV32_ADD(offset#MKPTR($.01), v0$1), v5$1, $$dest[BV32_ADD(offset#MKPTR($.01), v0$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$dest(p18$2, BV32_ADD(offset#MKPTR($.01), v0$2));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 17} true;
    call {:check_id "check_state_1"} {:sourceloc} {:sourceloc_num 17} _CHECK_WRITE_$$dest(p18$2, BV32_ADD(offset#MKPTR($.01), v0$2), v5$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$dest"} true;
    $$dest[BV32_ADD(offset#MKPTR($.01), v0$1)] := (if p18$1 then v5$1 else $$dest[BV32_ADD(offset#MKPTR($.01), v0$1)]);
    $$dest[BV32_ADD(offset#MKPTR($.01), v0$2)] := (if p18$2 then v5$2 else $$dest[BV32_ADD(offset#MKPTR($.01), v0$2)]);
    p21$1 := (if p19$1 && base#MKPTR($.01) == $arrayId$$A then base#MKPTR($.01) == $arrayId$$A else p21$1);
    p21$2 := (if p19$2 && base#MKPTR($.01) == $arrayId$$A then base#MKPTR($.01) == $arrayId$$A else p21$2);
    p20$1 := (if p19$1 && base#MKPTR($.01) != $arrayId$$A then base#MKPTR($.01) != $arrayId$$A else p20$1);
    p20$2 := (if p19$2 && base#MKPTR($.01) != $arrayId$$A then base#MKPTR($.01) != $arrayId$$A else p20$2);
    assert {:bad_pointer_access} {:sourceloc_num 19} {:thread 1} p20$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 19} {:thread 2} p20$2 ==> false;
    call {:sourceloc} {:sourceloc_num 18} _LOG_WRITE_$$A(p21$1, BV32_ADD(offset#MKPTR($.01), v0$1), v5$1, $$A[BV32_ADD(offset#MKPTR($.01), v0$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(p21$2, BV32_ADD(offset#MKPTR($.01), v0$2));
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 18} true;
    call {:check_id "check_state_0"} {:sourceloc} {:sourceloc_num 18} _CHECK_WRITE_$$A(p21$2, BV32_ADD(offset#MKPTR($.01), v0$2), v5$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    $$A[BV32_ADD(offset#MKPTR($.01), v0$1)] := (if p21$1 then v5$1 else $$A[BV32_ADD(offset#MKPTR($.01), v0$1)]);
    $$A[BV32_ADD(offset#MKPTR($.01), v0$2)] := (if p21$2 then v5$2 else $$A[BV32_ADD(offset#MKPTR($.01), v0$2)]);
    goto __partitioned_block_$truebb_1;

  __partitioned_block_$truebb_1:
    call {:sourceloc_num 21} $bugle_barrier_duplicated_0(0bv1, 1bv1);
    assert {:sourceloc_num 22} {:thread 1} (if MKPTR(base#MKPTR($.0), BV32_MUL(offset#MKPTR($.0), 4bv32)) != MKPTR(base#MKPTR($.01), BV32_MUL(offset#MKPTR($.01), 4bv32)) then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 22} {:thread 2} (if MKPTR(base#MKPTR($.0), BV32_MUL(offset#MKPTR($.0), 4bv32)) != MKPTR(base#MKPTR($.01), BV32_MUL(offset#MKPTR($.01), 4bv32)) then 1bv1 else 0bv1) != 0bv1;
    $d.0, $.01, $.0 := BV32_ADD($d.0, 1bv32), MKPTR(base#MKPTR($.0), offset#MKPTR($.0)), MKPTR(base#MKPTR($.01), offset#MKPTR($.01));
    assume {:captureState "loop_back_edge_state_0_0"} true;
    goto $1;
}



axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 8bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 1bv32 then 1bv1 else 0bv1) != 0bv1;

const {:local_id_y} local_id_y$1: bv32;

const {:local_id_y} local_id_y$2: bv32;

const {:local_id_z} local_id_z$1: bv32;

const {:local_id_z} local_id_z$2: bv32;

const {:group_id_y} group_id_y$1: bv32;

const {:group_id_y} group_id_y$2: bv32;

const {:group_id_z} group_id_z$1: bv32;

const {:group_id_z} group_id_z$2: bv32;

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_0($0: bv1, $1: bv1);
  requires $0 == 0bv1;
  requires $1 == 1bv1;
  modifies $$A, $$dest, _TRACKING;



const _WATCHED_VALUE_$$A: bv32;

procedure {:inline 1} _LOG_READ_$$A(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$A;



implementation {:inline 1} _LOG_READ_$$A(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$A := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A == _value then true else _READ_HAS_OCCURRED_$$A);
    return;
}



procedure _CHECK_READ_$$A(_P: bool, _offset: bv32, _value: bv32);
  requires {:source_name "A"} {:array "$$A"} {:race} {:write_read} !(_P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$A);
  requires {:source_name "A"} {:array "$$A"} {:race} {:atomic_read} !(_P && _ATOMIC_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset);



var _WRITE_READ_BENIGN_FLAG_$$A: bool;

procedure {:inline 1} _LOG_WRITE_$$A(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$A, _WRITE_READ_BENIGN_FLAG_$$A;



implementation {:inline 1} _LOG_WRITE_$$A(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$A := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A == _value then true else _WRITE_HAS_OCCURRED_$$A);
    _WRITE_READ_BENIGN_FLAG_$$A := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$A);
    return;
}



procedure _CHECK_WRITE_$$A(_P: bool, _offset: bv32, _value: bv32);
  requires {:source_name "A"} {:array "$$A"} {:race} {:write_write} !(_P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A != _value);
  requires {:source_name "A"} {:array "$$A"} {:race} {:read_write} !(_P && _READ_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A != _value);
  requires {:source_name "A"} {:array "$$A"} {:race} {:atomic_write} !(_P && _ATOMIC_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _LOG_ATOMIC_$$A(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$A;



implementation {:inline 1} _LOG_ATOMIC_$$A(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$A := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$A);
    return;
}



procedure _CHECK_ATOMIC_$$A(_P: bool, _offset: bv32);
  requires {:source_name "A"} {:array "$$A"} {:race} {:write_atomic} !(_P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset);
  requires {:source_name "A"} {:array "$$A"} {:race} {:read_atomic} !(_P && _READ_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$A;



implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$A := (if _P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$A);
    return;
}



const _WATCHED_VALUE_$$dest: bv32;

procedure {:inline 1} _LOG_READ_$$dest(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$dest;



implementation {:inline 1} _LOG_READ_$$dest(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$dest := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$dest == _value then true else _READ_HAS_OCCURRED_$$dest);
    return;
}



procedure _CHECK_READ_$$dest(_P: bool, _offset: bv32, _value: bv32);
  requires {:source_name "dest"} {:array "$$dest"} {:race} {:write_read} !(_P && _WRITE_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$dest);
  requires {:source_name "dest"} {:array "$$dest"} {:race} {:atomic_read} !(_P && _ATOMIC_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset);



var _WRITE_READ_BENIGN_FLAG_$$dest: bool;

procedure {:inline 1} _LOG_WRITE_$$dest(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$dest, _WRITE_READ_BENIGN_FLAG_$$dest;



implementation {:inline 1} _LOG_WRITE_$$dest(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$dest := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$dest == _value then true else _WRITE_HAS_OCCURRED_$$dest);
    _WRITE_READ_BENIGN_FLAG_$$dest := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$dest == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$dest);
    return;
}



procedure _CHECK_WRITE_$$dest(_P: bool, _offset: bv32, _value: bv32);
  requires {:source_name "dest"} {:array "$$dest"} {:race} {:write_write} !(_P && _WRITE_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$dest != _value);
  requires {:source_name "dest"} {:array "$$dest"} {:race} {:read_write} !(_P && _READ_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$dest != _value);
  requires {:source_name "dest"} {:array "$$dest"} {:race} {:atomic_write} !(_P && _ATOMIC_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _LOG_ATOMIC_$$dest(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$dest;



implementation {:inline 1} _LOG_ATOMIC_$$dest(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$dest := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$dest);
    return;
}



procedure _CHECK_ATOMIC_$$dest(_P: bool, _offset: bv32);
  requires {:source_name "dest"} {:array "$$dest"} {:race} {:write_atomic} !(_P && _WRITE_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset);
  requires {:source_name "dest"} {:array "$$dest"} {:race} {:read_atomic} !(_P && _READ_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$dest(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$dest;



implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$dest(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$dest := (if _P && _WRITE_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$dest);
    return;
}



var _TRACKING: bool;

implementation {:inline 1} $bugle_barrier_duplicated_0($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$A;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$A;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$A;
    goto anon1;

  anon1:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$dest;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$dest;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$dest;
    goto anon2;

  anon2:
    goto anon7_Then, anon7_Else;

  anon7_Else:
    assume {:partition} !(group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1));
    goto anon5;

  anon5:
    havoc _TRACKING;
    return;

  anon7_Then:
    assume {:partition} group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1);
    havoc $$A;
    goto anon4;

  anon4:
    havoc $$dest;
    goto anon5;

  anon6_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}



function {:bvbuiltin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:bvbuiltin "bvsge"} BV32_SGE(bv32, bv32) : bool;
