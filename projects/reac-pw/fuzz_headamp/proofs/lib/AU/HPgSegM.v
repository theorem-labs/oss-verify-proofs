(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgSegM.v at
   a working branch c91e5489711; the same layer for image B. The file it is made from Requires
   image A's record (lib/A/HPgImgA.v) and image A's segment machinery, so NOTHING is Required from it here: a
   lib/AU file must drag no image-A module in, because fuzz_role ports this layer. The pieces of that file whose
   text names no image - the bytes of the frame object x, the nan-boxed float predicate, the two answers, the
   fold invariants, the record's data and the saved-register list - are restated here, word for word, over
   lib/AU/HPgSeg.v's image-free machinery; they are the SAME model, not a second one, and a later move of them
   into an image-free file would replace both copies. Everything else is image B's own: B's register allocation,
   B's frame offsets and B's pcs differ from A's at every cut (image B is 32.7% renaming-equal to image A over
   this function, M03 37%), so each cut state, each sub-cut and each piece statement is measured on image B. B
   has one refusal entry where A has two, a rotated scan loop whose head carries the previous entry's answer, a
   fourth saved float register, a third binary32 bound and two soft-float calls A does not make. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): THE CUT STATES of the second half of the walk of
   LLVMFuzzerTestOneInput (0x80c40, 12860 bytes, 3215 instructions) - the second allocator call C2 0x82efc and
   its return C3 0x82f00, the third C4 0x82f34 / C5 0x82f38, the fourth C6 0x83900 / C7 0x83904, the copy split
   C8 0x83920, C9 0x83950 and the frame's retirement join J 0x83980 - and the statement of every piece the
   checking segment M03 (C5 -> C6) is split into. Statement text only: no function of a binary is proved here.
   The theorem at the end adds no walk: it chains the piece statements into lib/A/HPgCSpec.v's fixed segment
   contract headamp_check_contract and closes its two loops by induction on the loop index.
   Proves no function (kind: segment lemma).

   WHAT THIS FILE IS FOR. The walk is cut at the nine pcs of the plain walk of the same function, one at each
   allocator call and one at each allocator return (lib/A/HPgCSpec.v hi_c1 .. hi_c9 at lib/AU/HPgImgB.v's record
   headamp_himg_B). The five middle segments M01 / M02 / M03 / M04a / M04b are the fixed contracts
   headamp_build_contract, headamp_dup_contract, headamp_check_contract, headamp_first_contract and
   headamp_plain_contract; E01 (ENTRY -> C1) and X01 (C9 -> the return) are not contract texts, because each of
   them makes or ends blocks and the frame for locals. This file holds
   - the harness-level cut states at C2, C3, C4, C5, C6, C7, C8, C9 and at the retirement join J: what the
     chaining carries across the contracts (the harness's journal from its entry, the blocks live, the geometry,
     the thirteen saved words, the four float saves and the frame's flag-pointer cell), stated relative to the
     harness's entry state (hqu_hcx), as the other segments of the walk need them;
   - the statement of the three allocator steps C2 -> C3 (malloc(pod) 0x82efc), C4 -> C5 (malloc(out) 0x82f34)
     and C6 -> C7 (malloc(first) 0x83900), and of the two X01 pieces (C9 -> J: the four frees and res out of
     scope; J -> the return: the frame's retirement word, the release of its shadow and the epilogue);
   - the sub-cuts of M03 and the statement of each of its pieces, in continuation form: a piece lemma is
     `the segment's start facts -> <the continuations of its end cuts> -> <the continuation of its start cut>`,
     so that the pieces are proved in parallel and each proof sees only the STATEMENTS of the pieces its
     continuation goes to. The loop index is an argument of the head's continuation and never under the inner
     quantifier, so each loop closes by induction on that index;
   - one discharge lemma per UBSan trap family M03 reaches (24 branch sites to `unimp` 0x83a10 / 0x83a14, one of
     them in a block outside the piece set): the pointer sum, the signed 32-bit increment and decrement, the
     signed multiply, the entry-index bound, the cell-index bound, the key body's cursor and the two constants
     of the float-cast test.

   M03's shape (fuzz_headamp.c:330-350, measured over the function's CFG): it fills the out block with the guard
   byte, sets res to 0x5a, calls the parse on the pod (or on NULL by the harness's null flag), runs
   check_no_overrun, check_count and check_cells_valid, and, when pp->corrupt is 0, runs the inlined expect_of
   (fuzz_headamp.c:109-157) into the frame object x and then check_object, check_cells and, for rc >= 0,
   check_keys and check_refusal. expect_of is two nested loops: the pair loop (head 0x8314c, latch 0x836b4)
   whose body is one call of the inlined pod_next_pair (scan head 0x83190), the prefix test (the strncmp wrapper
   at 0x8329c), read_channel (the blanks loop 0x832e8 and the digits loop 0x83364), the strcmp chain (0x83418 /
   0x8342c / 0x83440), cell_value with the inlined pod_nearest (0x83490 .. 0x83690, six soft-float calls), the
   cell write (0x836e4) and the refusal fold (0x836a0).

   WHERE IMAGE B KEEPS A VALUE (image A's register in brackets, for the reader of the A twin). s0 = S the entry
   sp (`addi s0,sp,0x220` 0x80c8c), s1 = R the 32-aligned base of the real frame (0x80c90, 0x80c94;
   R + 0x220 <= S), s3 = (F >> 3) + K the frame's shadow base (0x80d04, 0x80d30) and s11 = K the runtime's
   shadow offset [A: s7], loaded through the GOT word 0x9c7f0 (0x80ca8, 0x80cb0), are fixed from 0x80c94 to the
   epilogue. The frame for locals F is a side-stack frame of class 4 (`addi a0,zero,0x3a0` 0x80cbc, the class-4
   call 0x80cc0); M03 reads and writes its last two objects, res (12 bytes at F+0x2a0) [A: F+0x180] and x
   (struct expect, 136 bytes at F+0x2c0) [A: F+0x1a0]. Inside M03 s4 = cap, s6 = out, s9 = rc and s10 = res are
   kept across every cut; s5 is F at the segment's head, then the String type 8 while the pair loop runs, then
   read_channel's channel; s2 is 3 cap at the head, then x, then the scan index, then the value; the pod lives
   in the real-frame cell R+0x158 and x in R+0x138. The pair loop keeps the entry table in t0 (pp + OFF_ENT), t1
   (+4), t3 and t4 (+8), its one's complement in t2, the params-struct word in t5 and its shadow address in t6,
   the two binary32 bounds of the inlined pod_nearest in fs1 (-1.0f) and fs2 (256.0f) and B'S OWN THIRD bound in
   fs3 (2^63 as binary32, for the pod.h:160 float-cast test), and the loop's constants in the real-frame cells
   R+0x98 (the n_ent granule's slow-path constant), R+0xa0 (the high word of -0.5L), R+0xa8 (0.5L), R+0xb0 and
   R+0xb8 (the binary128 constant -(2^63 + 1) of the same float-cast test), R+0xc0 (the one's complement of
   &x.cell[0]), R+0xc8 (&x.cell[0]), R+0xd0 (1000000), R+0x118 (the multiplier that turns an entry index into
   104 times it through `mulhu`), R+0x120 (&pp->n_ent), R+0x128 (the one's complement of &ent[0].body) and
   R+0x130 (the shadow address of &pp->n_ent). The parse's first argument is at R+0x140 and the out block's size
   at R+0x150. Image B does NOT reuse R+0x98 or R+0xa0 inside M03 (image A reuses both): B's scratch cells are
   R+0x88 and R+0x90.

   THE MODEL. The quantities a cut names are the shared model's (lib/Pod): the record in the pp block is a
   Model.pod_rec r, the answer of the parse is Pod/Headamp.v's parse_props on the pod bytes (Model.buf r) at the
   harness's cap, and what expect_of computes is Pod/Headamp.v's expect_model at the same cap. The pair loop's
   invariant is one equation on Pod/Headamp.v's ha_fold over the pairs Pod/Accessors.v's pairs_by leaves, and
   the frame object x holds, byte for byte, what the fold has written so far (hqu_x_open). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB HPgSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================= the pcs of the cuts =======================================
   The eight harness-level pcs of this half of the walk are headamp_himg_B's hi_c2 .. hi_c9; J and the return
   are the walk's own. *)
Definition HQU_C2 : Z := 0x82efc.   (* the `jal` of malloc(pod), a0 = len + (len == 0) from 0x82ef4 .. 0x82ef8 *)
Definition HQU_C3 : Z := 0x82f00.   (* `beqz a0` after it *)
Definition HQU_C4 : Z := 0x82f34.   (* the `jal` of malloc(out), a0 = 3 cap + 3 from 0x82f24 .. 0x82f30 *)
Definition HQU_C5 : Z := 0x82f38.   (* `beqz a0` after it *)
Definition HQU_C6 : Z := 0x83900.   (* the `jal` of malloc(first) *)
Definition HQU_C7 : Z := 0x83904.   (* `beqz a0` after it *)
Definition HQU_C8 : Z := 0x83920.   (* after the __asan_memcpy that fills first (jal 0x8391c, skipped at 0x8390c) *)
Definition HQU_C9 : Z := 0x83950.   (* `mv a0,s7` after check_plain returns, before the `jal` of free(first) *)
Definition HQU_J : Z := 0x83980.    (* `lui a0,0x45e03`: the frame's retirement word, after the four frees *)
Definition HQU_RET : Z := 0x83a04.  (* the `ret` the epilogue ends with (the return cut is at ra) *)
(* inside M03 *)
Definition HQU_X : Z := 0x82fdc.     (* pp->corrupt = 0: the frame object x comes into scope *)
Definition HQU_PAIR : Z := 0x8314c.  (* the pair loop's head (fuzz_headamp.c:119), the back edge's target *)
Definition HQU_SCAN : Z := 0x83190.  (* the inlined pod_next_pair's scan head (pod.h:134) *)
Definition HQU_KEY : Z := 0x83260.   (* a pair was found: its key is about to be compared with the prefix *)
Definition HQU_VAL : Z := 0x83490.   (* the key is a cell address: cell_value of the pair's value pod *)
Definition HQU_CELL : Z := 0x836e4.  (* the value is in range: the cap test and the cell write *)
Definition HQU_RF : Z := 0x836a0.    (* the refusal fold (fuzz_headamp.c:144-147), with a5 = the code *)
Definition HQU_LATCH : Z := 0x836b4. (* the pair loop's latch *)
Definition HQU_RC : Z := 0x83850.    (* the loop is done: x->rc := x->n, then the last four checks *)
Definition HQU_RCM : Z := 0x8385c.   (* its second entry: x->rc := -1 (the null flag or not a Props object) *)
Definition HQU_FIRST : Z := 0x838e4. (* the request of the first block (fuzz_headamp.c:350) *)

(* the frame for locals: class 4, 1024 bytes, its flag pointer in the last word (read at 0x8399c); the real
   frame below the entry sp S is 0x220 bytes (`addi sp,sp,-0x220` 0x80c40, `addi sp,sp,0x220` 0x83a00); the
   events of the whole run are four allocations and four frees *)
Definition HQU_CID : Z := 4.
Definition HQU_RSZ : Z := 0x220.
Definition HQU_FLAG : Z := 0x3f8.
Definition HQU_EV : Z := 8.
(* the two frame objects M03 writes (the frame description at 0x1b958) *)
Definition HQU_RES : Z := 0x2a0.
Definition HQU_XO : Z := 0x2c0.
(* the offsets of struct expect's fields (fuzz_headamp.c:56-62) *)
Definition HQU_X_CELL0 : Z := 4.
Definition HQU_X_N : Z := 0x7c.
(* the one's complement of a 64-bit value, as `not rd,rs` leaves it *)
Definition hqu_not (v : Z) : Z := -1 - v.
(* the multiplier at R+0x118 (`addi a5,zero,0xd` 0x830ac, `slli a5,a5,0x23` 0x830fc): `mulhu` of it with an
   entry index shifted up by 32 is 104 times that index (hqu_mul104_ok) *)
Definition HQU_MUL104 : Z := 0xd * 2 ^ 35.
(* the two binary32 bounds of the inlined pod_nearest, in fs1 and fs2 (`lui a7,0xbf800` 0x830b8 /
   `fmv.w.x fs1,a7` 0x830cc and `lui t0,0x43800` 0x830bc / `fmv.w.x fs2,t0` 0x830d4) *)
Definition HQU_F32_M1 : Z := 0xbf800000.
Definition HQU_F32_256 : Z := 0x43800000.
(* image B's third binary32 bound, 2^63 (`lui t1,0x5f000` 0x830c0, `fmv.w.x fs3,t1` 0x830e0), and the binary128
   constant -(2^63 + 1) in the real-frame cells R+0xb0 (high) and R+0xb8 (low) (0x830c8 / 0x83114 / 0x83118 and
   0x830c4 / 0x8310c / 0x83110): the two operands of the pod.h:160 float-cast test *)
Definition HQU_F32_2P63 : Z := 0x5f000000.
Definition HQU_C2HI : Z := 0xc03e000000000000.
Definition HQU_C2LO : Z := 2 ^ 49.
(* the high words of -0.5L and 0.5L, in R+0xa0 and R+0xa8 (0x830d8 / 0x83124 / 0x83128 and 0x830d0 / 0x8311c /
   0x83120), and read_channel's bound in R+0xd0 (0x830b4 / 0x83104 / 0x83108) *)
Definition HQU_MHALF_HI : Z := 0xbffe000000000000.
Definition HQU_HALF_HI : Z := 0x3ffe000000000000.
Definition HQU_RC_BIG : Z := 1000000.

Lemma hqu_pcs_himg :
  hi_c2 headamp_himg_B = HQU_C2 /\ hi_c3 headamp_himg_B = HQU_C3 /\ hi_c4 headamp_himg_B = HQU_C4 /\
  hi_c5 headamp_himg_B = HQU_C5 /\ hi_c6 headamp_himg_B = HQU_C6 /\ hi_c7 headamp_himg_B = HQU_C7 /\
  hi_c8 headamp_himg_B = HQU_C8 /\ hi_c9 headamp_himg_B = HQU_C9 /\
  hi_cid headamp_himg_B = HQU_CID /\ hi_rsz headamp_himg_B = HQU_RSZ.
Proof. repeat split; reflexivity. Qed.
Lemma hqu_offs_layout :
  Layout.OFF_ENT = 0x4014 /\ Layout.OFF_N_ENT = 0x4d14 /\ Layout.OFF_CORRUPT = 0x4d18 /\
  Layout.OFF_PARAMS_STRUCT = 0x4010 /\ Layout.OFF_IS_PROPS = 0x4008 /\ Layout.ENT_SIZE = 104 /\
  Layout.PP_SIZE = 19744.
Proof. repeat split; reflexivity. Qed.
Lemma hqu_mul104_ok : forall m, 0 <= m -> (m * 2 ^ 32 * HQU_MUL104) / 2 ^ 64 = 104 * m.
Proof.
intros m Hm. unfold HQU_MUL104.
assert (E : 2 ^ 32 * (13 * 2 ^ 35) = 104 * 2 ^ 64) by (vm_compute; reflexivity).
replace (m * 2 ^ 32 * (13 * 2 ^ 35)) with (m * (2 ^ 32 * (13 * 2 ^ 35))) by ring.
rewrite E. replace (m * (104 * 2 ^ 64)) with (104 * m * 2 ^ 64) by ring.
rewrite Z.div_mul by lia. reflexivity.
Qed.

(* ===== the bytes of the frame's shadow M03 passes through =====
   headamp_B_shA is the prologue's pattern (116 granules of the 0x3a0-byte frame, written by the 116 `sb` of
   0x80d34 .. 0x80f04); headamp_B_shB opens res's two granules 84 (0x00) and 85 (0x04) at 0x82f5c / 0x82f60;
   hqu_shX opens x's seventeen granules 88 .. 104 at 0x82fe0 .. 0x83020 and is the pattern of every cut between
   0x83020 and the stores at 0x838a0 .. 0x838e0 that close them again. *)
Definition hqu_shX : list Z :=
  firstn 88 headamp_B_shB ++ repeat 0 17 ++ skipn 105 headamp_B_shB.
Lemma hqu_shX_len : length hqu_shX = 116%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma hqu_shB_len : length headamp_B_shB = 116%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma hqu_shX_x : forall i, (88 <= i < 105)%nat -> nth i hqu_shX 0 = 0.
Proof.
intros i Hi.
assert (E : forall j, (j < 17)%nat -> nth (88 + j) hqu_shX 0 = 0).
{ intros j Hj. do 17 (destruct j as [|j]; [vm_compute; reflexivity|]). lia. }
replace i with (88 + (i - 88))%nat by lia. apply E. lia.
Qed.
(* outside x's granules hqu_shX is headamp_B_shB (the prologue's guards and res's two granules) *)
Lemma hqu_shX_out : forall i, ((i < 88)%nat \/ (105 <= i < 116)%nat) -> nth i hqu_shX 0 = nth i headamp_B_shB 0.
Proof.
intros i Hi. destruct Hi as [Hi|Hi].
- do 88 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
- assert (Hj : (i - 105 < 11)%nat) by lia. replace i with (105 + (i - 105))%nat by lia.
  set (j := (i - 105)%nat) in *. clearbody j.
  do 11 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.

(* ===== the bytes of the frame object x while the pair loop runs =====
   x->rc is still the memset's 0 (it is written at 0x8385c); the cells written so far, then the zero cells up to
   ten; then x->n = the number of cells, x->keys and x->refusal (Spec/HeadBytes.v ha_res_bytes). The same text
   as image A's hq_x_open: struct expect is the harness's, not an image's. *)
Definition hqu_x_open (cs : list cell) (keys rf : Z) : list byte :=
  repeat (Z_to_bv 8 0) 4 ++ x_cells_bytes cs ++
  repeat (Z_to_bv 8 0) (12 * (X_CELLS - length cs)) ++ ha_res_bytes (Z.of_nat (length cs)) keys rf.
Lemma hqu_x_open_len : forall cs keys rf, (length cs <= X_CELLS)%nat ->
  length (hqu_x_open cs keys rf) = 136%nat.
Proof.
intros cs keys rf H. unfold hqu_x_open, X_CELLS in *.
rewrite !length_app, !repeat_length, length_x_cells_bytes, length_ha_res_bytes. lia.
Qed.

(* the thirteen callee-saved words the prologue stores at [S - 0x68, S): ra at S - 8, s0 at S - 0x10, ..., s11
   at S - 0x68 (`sd ra,0x218(sp)` 0x80c48 .. `sd s11,0x1b8(sp)` 0x80c78 after `addi sp,sp,-0x220`) - the same
   thirteen registers in the same places as image A - and the frame's flag-pointer word *)
Definition hqu_saved_regs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition hqu_saves_L (regs0 : bvmap 5 word) : list (hd_loc * Z) :=
  map (fun j => (LCell XS (- 8 - 8 * Z.of_nat j), bv_unsigned (getr regs0 (nth j hqu_saved_regs 0%bv)))) (seq 0 13).
Definition hqu_cells (regs0 : bvmap 5 word) (fl : Z) : list (hd_loc * Z) :=
  hqu_saves_L regs0 ++ [(LCell (XF 0) HQU_FLAG, fl)].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* a float register holds a nan-boxed binary32 word *)
Definition hqu_fs (fx2 : YK11.FPState) (k v : Z) : Prop :=
  Sem.reg_get (@fp_regs fx2) (Z_to_bv 5 k) = Sem.nan_box (Z_to_bv 32 v).

(* the float registers M03 writes: fs0, fs1, fa0, fa4, fa5, fs2 and - image B only - fs3
   (f8, f9, f10, f14, f15, f18, f19), as headamp_check_contract's post names them *)
Definition HQU_FXK : list Z := [8; 9; 10; 14; 15; 18; 19].
Definition hqu_fxk (fx2 : YK11.FPState) : Prop := hd_fxk HQU_FXK fx fx2.

(* =====================================================================================================
   PART 1. The harness level: what the chaining carries across the contracts
   =====================================================================================================
   Every cut below is stated relative to the harness's ENTRY state (hqu_hcx) and its journal from there (hqu_j:
   no footprint, own = the frame for locals, k events). A cut states only what the chaining cannot derive: the
   static conjuncts of hd_seg_pre (arodata_okP, the registered globals' and the strings' shadow, the read-only cells,
   the guard word hd_guard_ok, rom_view) are re-derived at each contract's start from the symbols and the journal, and the frames and the
   block disjointness follow from the journal and the block list. What must survive from C1 to the return is
   carried here: the thirteen callee-saved words, the FOUR float saves at S - 0x70, S - 0x78, S - 0x80 and
   S - 0x88 (`fsd fs0,0x1b0(sp)` 0x80c7c .. `fsd fs3,0x198(sp)` 0x80c88; image A saves three), which the
   epilogue reads back (0x839f0 .. 0x839fc), and the frame's flag-pointer word at F + HQU_FLAG (the class-4
   frame law's last word; X01 stores 0 through it at 0x8399c .. 0x839a0). *)
Section h.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

Record hqu_hcx := HQUCx {
hu_ly : alayout; hu_S : astate; hu_W : world segs; hu_regs : bvmap 5 word; hu_mem : word -> option byte;
hu_md : Model; hu_p : Z; hu_n : Z; hu_pl : list byte }.

(* What every harness-level segment may use of the entry: HPgCSpec.hd_lib_pre_x without the parts only the
   final leaf reads (asink_none, the fd and fs facts, ameta_inv, the meter) and without its float clause, which
   X01, running at the float state M04b returns at, must not mention. *)
Definition hqu_base (hx : hqu_hcx) : Prop :=
afn_pre segs B LLVMF_STK (hu_ly hx) (hu_S hx) (hu_W hx) (hu_regs hx) (hu_mem hx) (hu_md hx) [] /\
raZ (hu_regs hx) = RA_LLVMF /\
getr (hu_regs hx) 10 = w64 (hu_p hx) /\ getr (hu_regs hx) 11 = w64 (hu_n hx) /\
((hu_n hx = 0 /\ hu_p hx = A_EMPTY) \/
 (0 < hu_n hx < 2 ^ 26 /\ In (hu_p hx, hu_n hx) (ablocks B (hu_ly hx) (hu_S hx)))) /\
hu_n hx = Z.of_nat (length (hu_pl hx)) /\
garr8 segs (mrestrict (w_H (hu_W hx)) (hu_mem hx)) (hu_p hx) (hd_zbytes (hu_pl hx)) /\
frames (hu_S hx) = [] /\ st_nev (hu_S hx) + EV_LIB <= EV_MAX /\
blocks_bytes (hu_S hx) + LIVE_LIB <= LIVE_MAX /\
arodata_okP segs RLO RHI B (aview segs (w_H (hu_W hx)) (hu_mem hx)).

Definition hqu_j (hx : hqu_hcx) (own : list (Z * Z)) (ly' : alayout) (S' : astate) (W' : world segs)
(mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal segs B LLVMF_STK (spZ (hu_regs hx)) [] (hu_ly hx) (hu_S hx) (hu_W hx) (hu_mem hx) (hu_md hx) own
  ly' S' W' mem' md' k.

(* The geometry: S the entry sp, R the 32-aligned base of the real frame (image B's is 0x220 bytes), F the
   class-4 frame at position pos (frame_addr reads only ly_F, which every journal's layout_le keeps, so one
   value serves every cut). *)
Definition hqu_geo (hx : hqu_hcx) (pos : Z) (e : hd_env) : Prop :=
e_S e = spZ (hu_regs hx) /\ e_R e = 32 * ((e_S e - HQU_RSZ) / 32) /\
e_F e = frame_addr (hu_ly hx) HQU_CID pos.

(* the four float saves: the epilogue reads them back, and no clause of the harness's post names a float
   register, so only their presence is carried *)
Definition hqu_fsaves (e : hd_env) (W' : world segs) (mem' : word -> option byte) (regs' : bvmap 5 word) : Prop :=
  exists v0 v1 v2 v3,
  hd_at segs (w_H W') mem' regs' e (LCell XS (- 0x70)) v0 /\
  hd_at segs (w_H W') mem' regs' e (LCell XS (- 0x78)) v1 /\
  hd_at segs (w_H W') mem' regs' e (LCell XS (- 0x80)) v2 /\
  hd_at segs (w_H W') mem' regs' e (LCell XS (- 0x88)) v3.
Definition hqu_kept (hx : hqu_hcx) (pos : Z) (e : hd_env) (W' : world segs) (mem' : word -> option byte)
(regs' : bvmap 5 word) : Prop :=
  Forall (fun f => hd_at segs (w_H W') mem' regs' e (fst f) (snd f))
    (hqu_cells (hu_regs hx) (flag_addr (hu_ly hx) HQU_CID pos)) /\
  hqu_fsaves e W' mem' regs'.

(* One shape for every harness-level cut: the journal with its event count, the blocks made since the entry and
   still live, sp / gp / tp, the geometry, the image's values at that pc, the frame's shadow, and the carried
   cells. *)
Definition hqu_at_cut (hx : hqu_hcx) (pos : Z) (e : hd_env) (k : Z) (bls : list (Z * Z))
(L : list (hd_loc * hd_x)) (sh : list Z)
(ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
: Prop :=
hqu_j hx [(HQU_CID, pos)] ly S W mem md k /\
Permutation (ablocks B ly S) (ablocks B (hu_ly hx) (hu_S hx) ++ bls) /\
Forall (fun b => ~ In b (ablocks B (hu_ly hx) (hu_S hx)) /\ fst b <> 0) bls /\
getr regs 2 = w64 (e_R e) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
hqu_geo hx pos e /\
hd_cut segs (w_H W) mem regs e L /\
hd_fsh segs (w_H W) mem (e_F e) sh /\
hqu_kept hx pos e W mem regs.

(* the blocks live at C2 (pp), at C3 .. C4 (and pod), at C5 .. C6 (and out) and at C7 .. C9 (and first) *)
Definition hqu_blocks1 (e : hd_env) : list (Z * Z) := [(e_pp e, Layout.PP_SIZE)].
Definition hqu_blocks3 (e : hd_env) : list (Z * Z) :=
  hqu_blocks1 e ++ [(e_pod e, e_len e)].
Definition hqu_blocks5 (e : hd_env) : list (Z * Z) :=
  hqu_blocks3 e ++ [(e_out e, 3 * (e_cap e + 1))].
Definition hqu_blocks7 (e : hd_env) : list (Z * Z) :=
  hqu_blocks5 e ++ [(e_first e, hd_xv e XRc3NZ)].

(* The record's data every cut from C4 on carries: the record r the pp block holds, the pod block's copy of its
   buffer, the bounds the allocator calls were made under, and the answer the parse gave. *)
Definition hqu_rec (e : hd_env) (r : Model.pod_rec) (W : world segs) (mem : word -> option byte) : Prop :=
Model.pod_rec_wf r /\ e_len e = Z.of_nat (length (Model.buf r)) /\ 8 <= e_len e <= 5440 /\
garr8 segs (mrestrict (w_H W) mem) (e_pp e) (hd_zbytes (Layout.pp_bytes r)) /\
garr8 segs (mrestrict (w_H W) mem) (e_pod e) (hd_zbytes (Model.buf r)) /\
e_pod e mod 16 = 0 /\ shadow_hull_vis (aview segs (w_H W) mem) (e_pod e) (e_len e) /\
amem_range (e_pod e) (e_len e + 8) /\
0 <= e_cap e <= 9 /\ 0 <= e_null e <= 1 /\
e_rc e = ans_rc (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e)).

(* ---------------- C2 0x82efc: the build is done, the pod block is about to be asked for ---------------- *)
Definition hqu_cut_C2 (hx : hqu_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
ly S W regs mem md : Prop :=
hqu_at_cut hx pos e 1 (hqu_blocks1 e) (hi_L2 headamp_himg_B) (hi_shA headamp_himg_B) ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
Model.pod_rec_wf r /\ e_len e = Z.of_nat (length (Model.buf r)) /\ 8 <= e_len e <= 5440 /\
garr8 segs (mrestrict (w_H W) mem) (e_pp e) (hd_zbytes (Layout.pp_bytes r)) /\
0 <= e_cap e <= 9 /\ 0 <= e_null e <= 1.

(* ---------------- C3 0x82f00: what M02 (headamp_dup_contract) starts from ---------------- *)
Definition hqu_cut_C3 (hx : hqu_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
ly S W regs mem md : Prop :=
hqu_at_cut hx pos e 2 (hqu_blocks3 e) (hi_L3 headamp_himg_B) (hi_shA headamp_himg_B) ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
Model.pod_rec_wf r /\ e_len e = Z.of_nat (length (Model.buf r)) /\ 8 <= e_len e <= 5440 /\
garr8 segs (mrestrict (w_H W) mem) (e_pp e) (hd_zbytes (Layout.pp_bytes r)) /\
e_pod e mod 16 = 0 /\ shadow_hull_vis (aview segs (w_H W) mem) (e_pod e) (e_len e) /\
amem_range (e_pod e) (e_len e + 8) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_pod e) (e_len e) /\
0 <= e_cap e <= 9 /\ 0 <= e_null e <= 1.

(* ---------------- C4 0x82f34: what M02 delivers, before the out block is asked for ---------------- *)
Definition hqu_cut_C4 (hx : hqu_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
ly S W regs mem md : Prop :=
hqu_at_cut hx pos e 2 (hqu_blocks3 e) (hi_L4 headamp_himg_B) (hi_shA headamp_himg_B) ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
hqu_rec e r W mem /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_pod e) (e_len e).

(* ---------------- C5 0x82f38: what the malloc(out) step delivers and M03 starts from ---------------- *)
Definition hqu_cut_C5 (hx : hqu_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec) (ev : Z)
ly S W regs mem md : Prop :=
hqu_at_cut hx pos e 3 (hqu_blocks5 e) (hi_L5 headamp_himg_B) (hi_shA headamp_himg_B) ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
hqu_rec e r W mem /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_pod e) (e_len e) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_out e) (3 * (e_cap e + 1)) /\
(e_pod e + e_len e <= e_out e \/ e_out e + 3 * (e_cap e + 1) <= e_pod e) /\
rd32 (aview segs (w_H W) mem) (as_errno B) ev.

(* ---------------- C6 0x83900: what headamp_check_contract delivers ---------------- *)
Definition hqu_cut_C6 (hx : hqu_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
ly S W regs mem md : Prop :=
hqu_at_cut hx pos e 3 (hqu_blocks5 e) (hi_L6 headamp_himg_B) (hi_shB headamp_himg_B) ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
hqu_rec e r W mem /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_pod e) (e_len e) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_out e) (3 * (e_cap e + 1)) /\
garr8 segs (mrestrict (w_H W) mem) (e_out e)
  (hd_zbytes (ha_cells_bytes (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))) /\
(exists ev, rd32 (aview segs (w_H W) mem) (as_errno B) ev).

(* ---------------- C7 0x83904: what M04a (headamp_first_contract) starts from ---------------- *)
Definition hqu_cut_C7 (hx : hqu_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
ly S W regs mem md : Prop :=
hqu_at_cut hx pos e 4 (hqu_blocks7 e) (hi_L7 headamp_himg_B) (hi_shB headamp_himg_B) ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
hqu_rec e r W mem /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_pod e) (e_len e) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_out e) (3 * (e_cap e + 1)) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_first e) (hd_xv e XRc3NZ) /\
garr8 segs (mrestrict (w_H W) mem) (e_out e)
  (hd_zbytes (ha_cells_bytes (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))) /\
(exists ev, rd32 (aview segs (w_H W) mem) (as_errno B) ev).

(* ---------------- C8 0x83920: the copy split, what M04b starts from ---------------- *)
Definition hqu_cut_C8 (hx : hqu_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
ly S W regs mem md : Prop :=
hqu_at_cut hx pos e 4 (hqu_blocks7 e) (hi_L8 headamp_himg_B) (hi_shB headamp_himg_B) ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
hqu_rec e r W mem /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_pod e) (e_len e) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_out e) (3 * (e_cap e + 1)) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_first e) (hd_xv e XRc3NZ) /\
garr8 segs (mrestrict (w_H W) mem) (e_first e)
  (hd_zbytes (ha_cells_bytes (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))) /\
(exists ev, rd32 (aview segs (w_H W) mem) (as_errno B) ev).

(* ---------------- C9 0x83950: what M04b delivers and X01 starts from ---------------- *)
Definition hqu_cut_C9 (hx : hqu_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env)
ly S W regs mem md : Prop :=
hqu_at_cut hx pos e 4 (hqu_blocks7 e) (hi_L9 headamp_himg_B) (hi_shB headamp_himg_B) ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
0 <= e_cap e <= 9 /\ 8 <= e_len e <= 5440.

(* ---------------- J 0x83980: the frame's retirement join ----------------
   The four blocks are freed (LIFO: first, out, pod, pp at 0x83954 .. 0x8396c) and res's two granules are back
   at 0xf8 (0x83974 .. 0x83978), so the frame's shadow is the prologue's again and the blocks are the entry's.
   s5 and s7 both hold F (s7 is read back from R+0x18 at 0x8397c). The event count is a parameter: the walk of
   E01 reaches this join on the `j` 0x80f0c of the early return with no event at all, which the harness's
   premise n < 2 ^ 26 makes dead. *)
Definition hqu_cut_J (hx : hqu_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (k : Z)
ly S W regs mem md : Prop :=
hqu_j hx [(HQU_CID, pos)] ly S W mem md k /\ 0 <= k <= HQU_EV /\
Permutation (ablocks B ly S) (ablocks B (hu_ly hx) (hu_S hx)) /\
getr regs 2 = w64 (e_R e) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
hqu_geo hx pos e /\
YK0o.frm_zero (@fp_csr fx2) /\
hd_cut segs (w_H W) mem regs e
  [(LReg 8, XS); (LReg 19, XShF); (LReg 21, XF 0); (LReg 23, XF 0)] /\
hd_fsh segs (w_H W) mem (e_F e) (hi_shA headamp_himg_B) /\
hqu_kept hx pos e W mem regs.

(* ---------------- the return: HPgCSpec.hd_lib_post_x's own clauses ---------------- *)
Definition hqu_ret (hx : hqu_hcx) : world segs -> config -> Prop :=
fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = @cfg_at fx' segs RA_LLVMF regs' mem' md' /\
YK0o.frm_zero (@fp_csr fx') /\
hqu_j hx [] ly' S' W' mem' md' k /\ k <= HQU_EV /\
aregs_preserved (hu_regs hx) regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B (hu_ly hx) (hu_S hx)).

(* ---------------- the three allocator steps ----------------
   Each is one `jal` of the malloc wrapper and the `beqz` that follows it; the returned block is new, the env
   gains it only at the return cut (the values at the call do not read it), and the callee keeps every
   callee-saved register, the frames and every byte outside its own stack window and the block it made. *)
Definition hqu_env_pod (e : hd_env) (pod : Z) : hd_env :=
  HDEnv (e_S e) (e_R e) (e_F e) (e_pp e) pod (e_out e) (e_first e) (e_len e) (e_cap e) (e_null e) (e_rc e)
        (e_src e) (e_left e).
Definition hqu_env_out (e : hd_env) (out : Z) : hd_env :=
  HDEnv (e_S e) (e_R e) (e_F e) (e_pp e) (e_pod e) out (e_first e) (e_len e) (e_cap e) (e_null e) (e_rc e)
        (e_src e) (e_left e).
Definition hqu_env_first (e : hd_env) (first : Z) : hd_env :=
  HDEnv (e_S e) (e_R e) (e_F e) (e_pp e) (e_pod e) (e_out e) first (e_len e) (e_cap e) (e_null e) (e_rc e)
        (e_src e) (e_left e).
(* XProps reads the pod block too (it is the parse's first argument), so it moves with XPod *)
Lemma hqu_env_pod_xv : forall e pod x, x <> XPod -> x <> XProps -> hd_xv (hqu_env_pod e pod) x = hd_xv e x.
Proof.
intros e pod x H H2. destruct x; cbn; try reflexivity;
  [exfalso; exact (H eq_refl) | exfalso; exact (H2 eq_refl)].
Qed.
Lemma hqu_env_out_xv : forall e out x, x <> XOut -> hd_xv (hqu_env_out e out) x = hd_xv e x.
Proof. intros e out x H. destruct x; cbn; try reflexivity. exfalso; exact (H eq_refl). Qed.
Lemma hqu_env_first_xv : forall e first x, x <> XFirst -> hd_xv (hqu_env_first e first) x = hd_xv e x.
Proof. intros e first x H. destruct x; cbn; try reflexivity. exfalso; exact (H eq_refl). Qed.

Definition hqu_at_C3 (hx : hqu_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
: world segs -> config -> Prop :=
fun W3 c3 => exists pod ly3 S3 regs3 mem3 md3,
c3 = @cfg_at fx2 segs HQU_C3 regs3 mem3 md3 /\
4096 <= pod /\ getr regs3 10 = w64 pod /\
(forall rr, acallee_saved rr -> getr regs3 (Z_to_bv 5 rr) = getr regs2 (Z_to_bv 5 rr)) /\
frames S3 = frames S2 /\
ablocks B ly3 S3 = ablocks B ly2 S2 ++ [(pod, e_len e)] /\
acall_kept segs B ly2 S2 W2 mem2 W3 mem3 (e_R e - ASTACK) (e_R e)
  (fun a => pod <= a < pod + req_size (e_len e)) /\
hqu_cut_C3 hx fx2 pos (hqu_env_pod e pod) r ly3 S3 W3 regs3 mem3 md3.

(* The errno cell's value at C5 is quantified: the allocator's contract (lib/Reusable/YG0d.v amalloc_realizes, its
   acall_post with ascratch) lets malloc change the errno cell, so no value read at C4 survives the call;
   headamp_check_contract, which C5 starts, takes the value universally. *)
Definition hqu_at_C5 (hx : hqu_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
(ly4 : alayout) (S4 : astate) (W4 : world segs) (regs4 : bvmap 5 word) (mem4 : word -> option byte)
: world segs -> config -> Prop :=
fun W5 c5 => exists out ev5 ly5 S5 regs5 mem5 md5,
c5 = @cfg_at fx2 segs HQU_C5 regs5 mem5 md5 /\
4096 <= out /\ getr regs5 10 = w64 out /\
(forall rr, acallee_saved rr -> getr regs5 (Z_to_bv 5 rr) = getr regs4 (Z_to_bv 5 rr)) /\
frames S5 = frames S4 /\
ablocks B ly5 S5 = ablocks B ly4 S4 ++ [(out, 3 * (e_cap e + 1))] /\
acall_kept segs B ly4 S4 W4 mem4 W5 mem5 (e_R e - ASTACK) (e_R e)
  (fun a => out <= a < out + req_size (3 * (e_cap e + 1))) /\
hqu_cut_C5 hx fx2 pos (hqu_env_out e out) r ev5 ly5 S5 W5 regs5 mem5 md5.

Definition hqu_at_C7 (hx : hqu_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
(ly6 : alayout) (S6 : astate) (W6 : world segs) (regs6 : bvmap 5 word) (mem6 : word -> option byte)
: world segs -> config -> Prop :=
fun W7 c7 => exists first ly7 S7 regs7 mem7 md7,
c7 = @cfg_at fx2 segs HQU_C7 regs7 mem7 md7 /\
4096 <= first /\ getr regs7 10 = w64 first /\
(forall rr, acallee_saved rr -> getr regs7 (Z_to_bv 5 rr) = getr regs6 (Z_to_bv 5 rr)) /\
frames S7 = frames S6 /\
ablocks B ly7 S7 = ablocks B ly6 S6 ++ [(first, hd_xv e XRc3NZ)] /\
acall_kept segs B ly6 S6 W6 mem6 W7 mem7 (e_R e - ASTACK) (e_R e)
  (fun a => first <= a < first + req_size (hd_xv e XRc3NZ)) /\
hqu_cut_C7 hx fx2 pos (hqu_env_first e first) r ly7 S7 W7 regs7 mem7 md7.

(* ---------------- the five statements of this half's harness-level pieces ---------------- *)
(* the allocator step C2 -> C3 (an M24 step: an allocator request between segments): a0 = len + (len == 0) from 0x82ef4 .. 0x82ef8 *)
Definition hqu_S_C23_stmt : Prop :=
forall (hx : hqu_hcx) (fx2 : YK11.FPState) pos e r ly2 S2 W2 regs2 mem2 md2,
hqu_base hx -> hqu_cut_C2 hx fx2 pos e r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQU_C2 regs2 mem2 md2) (hqu_at_C3 hx fx2 pos e r ly2 S2 W2 regs2 mem2).
(* the allocator step C4 -> C5 (an M24 step: an allocator request between segments): a0 = 3 cap + 3 from 0x82f24 .. 0x82f30 *)
Definition hqu_S_C45_stmt : Prop :=
forall (hx : hqu_hcx) (fx2 : YK11.FPState) pos e r ly4 S4 W4 regs4 mem4 md4,
hqu_base hx -> hqu_cut_C4 hx fx2 pos e r ly4 S4 W4 regs4 mem4 md4 ->
SRr segs W4 (@cfg_at fx2 segs HQU_C4 regs4 mem4 md4) (hqu_at_C5 hx fx2 pos e r ly4 S4 W4 regs4 mem4).
(* the allocator step C6 -> C7 (an M24 step: an allocator request between segments): a0 = 3 max(rc, 0) + (3 max(rc, 0) == 0) from 0x838e4 .. 0x838fc *)
Definition hqu_S_C67_stmt : Prop :=
forall (hx : hqu_hcx) (fx2 : YK11.FPState) pos e r ly6 S6 W6 regs6 mem6 md6,
hqu_base hx -> hqu_cut_C6 hx fx2 pos e r ly6 S6 W6 regs6 mem6 md6 ->
SRr segs W6 (@cfg_at fx2 segs HQU_C6 regs6 mem6 md6) (hqu_at_C7 hx fx2 pos e r ly6 S6 W6 regs6 mem6).
(* X01, part 1: free(first), free(out), free(pod), free(pp) and res out of scope *)
Definition hqu_S_X01f_stmt : Prop :=
forall (hx : hqu_hcx) (fx2 : YK11.FPState) pos e ly S W regs mem md,
hqu_base hx -> hqu_cut_C9 hx fx2 pos e ly S W regs mem md ->
SRr segs W (@cfg_at fx2 segs HQU_C9 regs mem md)
  (fun W' c' => exists ly' S' regs' mem' md' k,
   c' = @cfg_at fx2 segs HQU_J regs' mem' md' /\ hqu_cut_J hx fx2 pos e k ly' S' W' regs' mem' md').
(* X01, part 2: F[0] := 0x45e0360e, the class-4 release (the shadow fill at 0x83998 and the flag
   byte through F + HQU_FLAG at 0x8399c .. 0x839a0; the s7 = 0 arm with the call at 0x839b0 is dead), a0 := 0
   and the epilogue, which restores four float registers *)
Definition hqu_S_X01r_stmt : Prop :=
forall (hx : hqu_hcx) (fx2 : YK11.FPState) pos e k ly S W regs mem md,
hqu_base hx -> hqu_cut_J hx fx2 pos e k ly S W regs mem md ->
SRr segs W (@cfg_at fx2 segs HQU_J regs mem md) (hqu_ret hx).

End h.

(* =====================================================================================================
   PART 2. M03: the sub-cuts of headamp_check_contract's walk, from C5 0x82f38 to C6 0x83900
   =====================================================================================================
   A cut inside the segment is a predicate over the segment's fixed data (lib/AU/HPgSeg.v's hsu_scx: the
   harness's journal so far, the registers at the segment's first pc, the run's quantities and the frame's
   position) and the state at the cut. It states only POSITIVE facts; what a call leaves alone is not restated
   (the journal's own clauses and each callee's write-set post carry it between cuts), and the segment's start
   facts, which every piece lemma takes, carry the read-only data and the input. *)

(* M03's write set, as headamp_check_contract states it: the image's third range list (the frame objects res
   and x, their shadow granules and the real-frame cells [R, R+0x160)), the out block and the errno cell. *)
Definition hqu_E3 (cx : hsu_scx segs) : Z -> Prop :=
fun a => hd_inw (x_e segs cx) (hi_w3 headamp_himg_B) a \/
 (e_out (x_e segs cx) <= a < e_out (x_e segs cx) + 3 * (e_cap (x_e segs cx) + 1)) \/
 (as_errno B <= a < as_errno B + 4).

(* the answer the parse gave (the out block and res hold it, and e_rc is its rc) and the answer expect_of
   computes (x holds it from 0x8385c on) *)
Definition hqu_ans (cx : hsu_scx segs) (r : Model.pod_rec) : answer :=
  Headamp.parse_props (hd_props (e_null (x_e segs cx)) (Model.buf r)) (e_cap (x_e segs cx)).
Definition hqu_exp (cx : hsu_scx segs) (r : Model.pod_rec) : answer :=
  Headamp.expect_model (e_null (x_e segs cx) =? 1) (e_cap (x_e segs cx)) r.
Definition hqu_fin (cx : hsu_scx segs) (r : Model.pod_rec) : list cell * Z * Z :=
  (ans_cells (hqu_exp cx r), ans_keys (hqu_exp cx r), ans_rf (hqu_exp cx r)).

(* ---------------- what the pieces of M03 all take: headamp_check_contract's premises ----------------
   The conjuncts are the contract's, in its order (HPgCSpec.v headamp_check_contract), so that the segment's
   proof hands them over as they stand. *)
Definition hqu_start_M03 (cx : hsu_scx segs) (r : Model.pod_rec) (ev : Z) : Prop :=
hsu_pre segs B headamp_himg_B cx (hi_shA headamp_himg_B) /\
hd_cut segs (w_H (x_W segs cx)) (x_memc segs cx) (x_regs segs cx) (x_e segs cx) (hi_L5 headamp_himg_B) /\
Model.pod_rec_wf r /\ e_len (x_e segs cx) = Z.of_nat (length (Model.buf r)) /\
garr8 segs (mrestrict (w_H (x_W segs cx)) (x_memc segs cx)) (e_pp (x_e segs cx)) (hd_zbytes (Layout.pp_bytes r)) /\
garr8 segs (mrestrict (w_H (x_W segs cx)) (x_memc segs cx)) (e_pod (x_e segs cx)) (hd_zbytes (Model.buf r)) /\
hd_fresh_block (ablocks B (x_ly segs cx) (x_S segs cx)) (ablocks B (x_lyc segs cx) (x_Sc segs cx)) (e_pod (x_e segs cx)) (e_len (x_e segs cx)) /\
range_addressable (aview segs (w_H (x_W segs cx)) (x_memc segs cx)) SHADOW_OFF (e_pod (x_e segs cx)) (e_len (x_e segs cx)) /\
shadow_hull_vis (aview segs (w_H (x_W segs cx)) (x_memc segs cx)) (e_pod (x_e segs cx)) (e_len (x_e segs cx)) /\
amem_range (e_pod (x_e segs cx)) (e_len (x_e segs cx) + 8) /\ e_pod (x_e segs cx) mod 16 = 0 /\
hd_fresh_block (ablocks B (x_ly segs cx) (x_S segs cx)) (ablocks B (x_lyc segs cx) (x_Sc segs cx)) (e_out (x_e segs cx))
  (3 * (e_cap (x_e segs cx) + 1)) /\
range_addressable (aview segs (w_H (x_W segs cx)) (x_memc segs cx)) SHADOW_OFF (e_out (x_e segs cx)) (3 * (e_cap (x_e segs cx) + 1)) /\
(e_pod (x_e segs cx) + e_len (x_e segs cx) <= e_out (x_e segs cx) \/
 e_out (x_e segs cx) + 3 * (e_cap (x_e segs cx) + 1) <= e_pod (x_e segs cx)) /\
e_rc (x_e segs cx) = ans_rc (hqu_ans cx r) /\
rd32 (aview segs (w_H (x_W segs cx)) (x_memc segs cx)) (as_errno B) ev /\
YK0o.frm_zero (@fp_csr fx).

(* ---------------- what every cut inside M03 carries ----------------
   The segment's journal-and-frame part with M03's write set, the float registers M03 may have changed, the
   frame's shadow pattern at that cut, the read-only image (the soft-float callees of the value piece need it),
   the pp block and the pod block unchanged (both lie outside the write set), the out block holding the parse's
   cells, res holding the parse's result struct, and the errno cell readable. *)
Definition hqu_base3 (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (sh : list Z)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_core segs B MT cx (hqu_E3 cx) ly2 S2 W2 regs2 mem2 md2 /\
hqu_fxk fx2 /\
hsu_fsh_at segs cx W2 mem2 sh /\
rom_view segs W2 mem2 /\
hsu_pp_at segs cx W2 mem2 (Layout.pp_bytes r) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_pod (x_e segs cx)) (hd_zbytes (Model.buf r)) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_out (x_e segs cx))
  (hd_zbytes (ha_cells_bytes (ans_cells (hqu_ans cx r)))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e segs cx) + HQU_RES) (hd_zbytes (ans_res_bytes (hqu_ans cx r))) /\
(exists ev, rd32 (aview segs (w_H W2) mem2) (as_errno B) ev).

(* the registers fixed from the prologue to the epilogue, and the four M03 keeps at every inner cut
   (image B's s5 is NOT one of them: it is F at the segment's head, the String type while the loop runs and
   read_channel's channel inside the body) *)
Definition hqu_L_frame (cx : hsu_scx segs) : list (hd_loc * Z) :=
  [(LReg 8, e_S (x_e segs cx)); (LReg 9, e_R (x_e segs cx)); (LReg 19, shadow_addr (e_F (x_e segs cx)));
   (LReg 27, SHADOW_OFF)].
Definition hqu_L_seg (cx : hsu_scx segs) : list (hd_loc * Z) :=
  hqu_L_frame cx ++
  [(LReg 20, e_cap (x_e segs cx)); (LReg 22, e_out (x_e segs cx)); (LReg 25, e_rc (x_e segs cx));
   (LReg 26, e_F (x_e segs cx) + HQU_RES)].
(* the real-frame cells the pair loop and its body read, written once by 0x82f50 .. 0x83140 *)
Definition hqu_L_loopc (cx : hsu_scx segs) : list (hd_loc * Z) :=
  let e := x_e segs cx in
  [(LCell XR 0x18, e_F e); (LCell XR 0x48, e_F e);
   (LCell XR 0x98, (e_pp e + Layout.OFF_N_ENT) mod 8 + 3);
   (LCell XR 0xa0, HQU_MHALF_HI); (LCell XR 0xa8, HQU_HALF_HI);
   (LCell XR 0xb0, HQU_C2HI); (LCell XR 0xb8, HQU_C2LO);
   (LCell XR 0xc0, hqu_not (e_F e + HQU_XO + HQU_X_CELL0)); (LCell XR 0xc8, e_F e + HQU_XO + HQU_X_CELL0);
   (LCell XR 0xd0, HQU_RC_BIG);
   (LCell XR 0x118, HQU_MUL104); (LCell XR 0x120, e_pp e + Layout.OFF_N_ENT);
   (LCell XR 0x128, hqu_not (e_pp e + Layout.OFF_ENT + 8));
   (LCell XR 0x130, shadow_addr (e_pp e + Layout.OFF_N_ENT));
   (LCell XR 0x138, e_F e + HQU_XO);
   (LCell XR 0x140, hd_xv e XProps); (LCell XR 0x148, e_pp e);
   (LCell XR 0x150, 3 * e_cap e + 3); (LCell XR 0x158, e_pod e)].
(* the five registers the loop's head and its scan hold besides the loop's: the entry table's four addresses
   and the one's complement of the first (0x8312c .. 0x83148, reloaded by the latch at 0x836c8 .. 0x836d8) *)
Definition hqu_L_loopr (cx : hsu_scx segs) : list (hd_loc * Z) :=
  let pp := e_pp (x_e segs cx) in
  [(LReg 5, pp + Layout.OFF_ENT); (LReg 6, pp + Layout.OFF_ENT + 4); (LReg 7, hqu_not (pp + Layout.OFF_ENT));
   (LReg 28, pp + Layout.OFF_ENT + 8); (LReg 29, pp + Layout.OFF_ENT + 8)].
(* the params-struct word and its shadow address, in t5 and t6 from 0x8305c .. 0x83064 to the latch's test *)
Definition hqu_L_t56 (cx : hsu_scx segs) : list (hd_loc * Z) :=
  let pp := e_pp (x_e segs cx) in
  [(LReg 30, pp + Layout.OFF_PARAMS_STRUCT); (LReg 31, shadow_addr (pp + Layout.OFF_PARAMS_STRUCT))].
(* the cells the body of one pair writes and reads besides the loop's: the entry table spilled around the
   wrapper calls (0x8326c .. 0x83298) and the index of the next at *)
Definition hqu_L_body (cx : hsu_scx segs) (j : Z) : list (hd_loc * Z) :=
  let pp := e_pp (x_e segs cx) in
  [(LCell XR 0xd8, j);
   (LCell XR 0xe0, pp + Layout.OFF_ENT + 8); (LCell XR 0xe8, pp + Layout.OFF_ENT + 8);
   (LCell XR 0xf0, hqu_not (pp + Layout.OFF_ENT)); (LCell XR 0xf8, pp + Layout.OFF_ENT);
   (LCell XR 0x100, pp + Layout.OFF_ENT + 4);
   (LCell XR 0x108, shadow_addr (pp + Layout.OFF_PARAMS_STRUCT));
   (LCell XR 0x110, pp + Layout.OFF_PARAMS_STRUCT)].

(* the record's three tests the loop runs under, and its entry count *)
Definition hqu_live (cx : hsu_scx segs) (r : Model.pod_rec) : Prop :=
  e_null (x_e segs cx) = 0 /\ Model.corrupt r = false /\
  Model.is_props r = true /\ Model.params_struct r = true.
Definition hqu_nent (r : Model.pod_rec) : Z := Z.of_nat (length (Model.ents r)).

(* the pair loop's invariant: folding the pairs that start at index j over what x holds gives the answer
   expect_of ends with (Pod/Headamp.v ha_fold, Pod/Accessors.v pairs_by) *)
Definition hqu_fold_inv (cx : hsu_scx segs) (r : Model.pod_rec) (j : nat) (cs : list cell) (keys rf : Z) : Prop :=
  Headamp.ha_fold Headamp.expect_cell (e_cap (x_e segs cx))
    (Accessors.pairs_by Accessors.key_of (skipn j (Model.ents r)) None) cs keys rf = hqu_fin cx r.
(* the same, with the pair the body is working on in front of the list *)
Definition hqu_pair_inv (cx : hsu_scx segs) (r : Model.pod_rec) (m : nat) (k : list byte) (v : Model.ent)
(cs : list cell) (keys rf : Z) : Prop :=
  v = nth (S m) (Model.ents r) (Model.Ent 0 0 []) /\
  Headamp.ha_prefix k = true /\
  (S m < length (Model.ents r))%nat /\
  Headamp.ha_fold Headamp.expect_cell (e_cap (x_e segs cx))
    ((k, v) :: Accessors.pairs_by Accessors.key_of (skipn (S (S m)) (Model.ents r)) None) cs keys rf = hqu_fin cx r.

(* what x holds at a cut of the loop, and the two bounds the fold keeps (image B's x is at F + 0x2c0) *)
Definition hqu_x_at (cx : hsu_scx segs) (W2 : world segs) (mem2 : word -> option byte)
(cs : list cell) (keys rf : Z) : Prop :=
  garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e segs cx) + HQU_XO) (hd_zbytes (hqu_x_open cs keys rf)) /\
  (length cs <= X_CELLS)%nat /\ Z.of_nat (length cs) <= e_cap (x_e segs cx) /\
  Z.of_nat (length cs) <= keys /\ 0 <= keys < 2 ^ 31 - 1 /\
  (rf = Headamp.REFUSE_NONE \/ rf = Headamp.REFUSE_BAD_KEY \/ rf = Headamp.REFUSE_OUT_OF_RANGE).

(* ---------------- X 0x82fdc: pp->corrupt is 0, the frame object x is about to come into scope ----------------
   s5 = F, s7 = 1 - the null flag (the `beqz s7` at 0x83038 is the null test); s2 = 3 cap and s8 = &pp->corrupt
   are dead here (0x82fdc writes s2). *)
Definition hqu_cut_X (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hqu_base3 cx fx2 r (hi_shB headamp_himg_B) ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2
  (hqu_L_seg cx ++
   [(LReg 21, e_F (x_e segs cx)); (LReg 23, 1 - e_null (x_e segs cx));
    (LCell XR 0x8, e_pp (x_e segs cx) + Layout.OFF_IS_PROPS);
    (LCell XR 0x18, e_F (x_e segs cx)); (LCell XR 0x48, e_F (x_e segs cx));
    (LCell XR 0xe0, Z.shiftr (e_pp (x_e segs cx) + Layout.OFF_N_ENT) 3);
    (LCell XR 0x108, - 16381); (LCell XR 0x120, e_pp (x_e segs cx) + Layout.OFF_N_ENT);
    (LCell XR 0x140, hd_xv (x_e segs cx) XProps); (LCell XR 0x148, e_pp (x_e segs cx));
    (LCell XR 0x150, 3 * e_cap (x_e segs cx) + 3); (LCell XR 0x158, e_pod (x_e segs cx))]) /\
Model.corrupt r = false.

(* ---------------- PAIR 0x8314c: the pair loop's head at index i (fuzz_headamp.c:119) ----------------
   a2 = at, the scan's first entry index; x holds what the fold has written. The real-frame cells R+0xd8 ..
   R+0x110 are NOT part of this cut: the key piece writes them, so their value differs between the first turn
   and the later ones.
   IMAGE B READS n_ent HERE and tests it (`ld a0,0x130(s1)` 0x8314c, the shadow byte, `ld a0,0x120(s1)` /
   `lw a3,0(a0)` 0x83158 .. 0x8315c, `bge a2,a3` 0x83160 -> RC 0x83850), where image A's pair head 0x8307c has
   no such test. So this cut carries i <= n_ent, NOT i < n_ent: the latch hands it i = m + 2, which may equal
   n_ent, and the head itself decides. Its piece statement therefore takes hqu_from_RC, which image A's twin
   does not. *)
Definition hqu_cut_PAIR (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (i : nat)
(cs : list cell) (keys rf : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hqu_base3 cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2
  (hqu_L_seg cx ++ hqu_L_loopc cx ++ hqu_L_loopr cx ++ hqu_L_t56 cx ++
   [(LReg 12, Z.of_nat i); (LReg 21, 8)]) /\
hqu_fs fx2 9 HQU_F32_M1 /\ hqu_fs fx2 18 HQU_F32_256 /\ hqu_fs fx2 19 HQU_F32_2P63 /\
hqu_live cx r /\ 0 < hqu_nent r /\
(i <= length (Model.ents r))%nat /\
hqu_x_at cx W2 mem2 cs keys rf /\ hqu_fold_inv cx r i cs keys rf.

(* ---------------- SCAN 0x83190: pod_next_pair's scan head (pod.h:134) ----------------
   Image B rotates this loop: the head tests the PREVIOUS entry's answer in s7 before it examines entry m, so
   the head has two states at one pc. This one is the examining state (s7 = 0). a3 = n_ent, a4 = the loop's
   index bound (33, or the first entry index when that is larger - it is at most 32, so a4 is 33), s2 = a2 = m,
   s8 = 104 m and a5 = the one's complement of &ent[m].body. *)
Definition hqu_cut_SCAN (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(cs : list cell) (keys rf : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hqu_base3 cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2
  (hqu_L_seg cx ++ hqu_L_loopc cx ++ hqu_L_loopr cx ++ hqu_L_t56 cx ++
   [(LReg 21, 8); (LReg 23, 0);
    (LReg 12, Z.of_nat m); (LReg 18, Z.of_nat m); (LReg 24, Layout.ENT_SIZE * Z.of_nat m);
    (LReg 13, hqu_nent r); (LReg 14, Z.max 33 (Z.of_nat at0));
    (LReg 15, hqu_not (e_pp (x_e segs cx) + Layout.OFF_ENT + 8 + Layout.ENT_SIZE * Z.of_nat m))]) /\
hqu_fs fx2 9 HQU_F32_M1 /\ hqu_fs fx2 18 HQU_F32_256 /\ hqu_fs fx2 19 HQU_F32_2P63 /\
hqu_live cx r /\
(at0 <= m < length (Model.ents r))%nat /\
(forall q, (at0 <= q < m)%nat -> Accessors.key_of (nth q (Model.ents r) (Model.Ent 0 0 [])) = None) /\
hqu_x_at cx W2 mem2 cs keys rf /\ hqu_fold_inv cx r at0 cs keys rf.

(* ---------------- SCAN 0x83190, the leaving state: entry m was a key ----------------
   s7 = &ent[m].body <> 0, so the head's `bnez s7` goes to the key. The counters have already moved on:
   s2 = a2 = m + 1, s8 = 104 (m + 1). Entry m + 1 is inside the table, which is why the loop came back here
   instead of leaving at 0x83230: a key in the last entry makes no pair. *)
Definition hqu_cut_SCANF (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(k : list byte) (cs : list cell) (keys rf : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hqu_base3 cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2
  (hqu_L_seg cx ++ hqu_L_loopc cx ++ hqu_L_loopr cx ++ hqu_L_t56 cx ++
   [(LReg 21, 8);
    (LReg 23, e_pp (x_e segs cx) + Layout.OFF_ENT + 8 + Layout.ENT_SIZE * Z.of_nat m);
    (LReg 12, Z.of_nat m + 1); (LReg 18, Z.of_nat m + 1);
    (LReg 24, Layout.ENT_SIZE * (Z.of_nat m + 1));
    (LReg 13, hqu_nent r); (LReg 14, Z.max 33 (Z.of_nat at0));
    (LReg 15, hqu_not (e_pp (x_e segs cx) + Layout.OFF_ENT + 8 + Layout.ENT_SIZE * (Z.of_nat m + 1)))]) /\
hqu_fs fx2 9 HQU_F32_M1 /\ hqu_fs fx2 18 HQU_F32_256 /\ hqu_fs fx2 19 HQU_F32_2P63 /\
hqu_live cx r /\
(at0 <= m)%nat /\ (S m < length (Model.ents r))%nat /\
0 < e_pp (x_e segs cx) + Layout.OFF_ENT + 8 + Layout.ENT_SIZE * Z.of_nat m /\
(forall q, (at0 <= q < m)%nat -> Accessors.key_of (nth q (Model.ents r) (Model.Ent 0 0 [])) = None) /\
Accessors.key_of (nth m (Model.ents r) (Model.Ent 0 0 [])) = Some k /\
hqu_x_at cx W2 mem2 cs keys rf /\ hqu_fold_inv cx r at0 cs keys rf.

(* ---------------- KEY 0x83260: entry m is a key and entry m + 1 is its value ----------------
   s7 = the key's body address, a2 = s2 = m + 1 (the value entry's index) and s8 = 104 (m + 1). The strncmp
   wrapper is called at 0x8329c with the key's address, the harness's own literal and 13. *)
Definition hqu_cut_KEY (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(k : list byte) (cs : list cell) (keys rf : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hqu_base3 cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2
  (hqu_L_seg cx ++ hqu_L_loopc cx ++ hqu_L_loopr cx ++ hqu_L_t56 cx ++
   [(LReg 23, e_pp (x_e segs cx) + Layout.OFF_ENT + 8 + Layout.ENT_SIZE * Z.of_nat m);
    (LReg 12, Z.of_nat m + 1); (LReg 18, Z.of_nat m + 1);
    (LReg 24, Layout.ENT_SIZE * (Z.of_nat m + 1))]) /\
hqu_fs fx2 9 HQU_F32_M1 /\ hqu_fs fx2 18 HQU_F32_256 /\ hqu_fs fx2 19 HQU_F32_2P63 /\
hqu_live cx r /\
(at0 <= m)%nat /\ (S m < length (Model.ents r))%nat /\
0 < e_pp (x_e segs cx) + Layout.OFF_ENT + 8 + Layout.ENT_SIZE * Z.of_nat m /\
(forall q, (at0 <= q < m)%nat -> Accessors.key_of (nth q (Model.ents r) (Model.Ent 0 0 [])) = None) /\
Accessors.key_of (nth m (Model.ents r) (Model.Ent 0 0 [])) = Some k /\
hqu_x_at cx W2 mem2 cs keys rf /\ hqu_fold_inv cx r at0 cs keys rf.

(* ---------------- VAL 0x83490: the key is a cell address, cell_value of the pair's value pod ----------------
   x->keys is already one more; a6 = the param, s7 = the param's top value, s5 = the channel, a5 = the refusal
   code the value's tests give, s2 = m + 1 the value entry's index and s8 = 104 (m + 1). x's own bound is only
   |cs| <= keys + 1 here, so the cut keeps KEY's |cs| <= keys: the cell piece's LATCH (S (S m)) needs
   hqu_x_at (cs ++ [cell]) (keys + 1) rf (image A's twin, lib/A/HPgSegM.v). *)
Definition hqu_cut_VAL (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(k : list byte) (v : Model.ent) (ch p : Z) (cs : list cell) (keys rf : Z)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hqu_base3 cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2
  (hqu_L_seg cx ++ hqu_L_loopc cx ++ hqu_L_t56 cx ++ hqu_L_body cx (Z.of_nat m + 2) ++
   [(LReg 16, p); (LReg 23, if p =? Headamp.HA_SENS then Headamp.HA_SENS_MAX else 1);
    (LReg 21, ch); (LReg 15, Headamp.REFUSE_OUT_OF_RANGE);
    (LReg 18, Z.of_nat m + 1); (LReg 24, Layout.ENT_SIZE * (Z.of_nat m + 1))]) /\
hqu_fs fx2 9 HQU_F32_M1 /\ hqu_fs fx2 18 HQU_F32_256 /\ hqu_fs fx2 19 HQU_F32_2P63 /\
hqu_live cx r /\ (at0 <= m)%nat /\
Headamp.expect_key (skipn (length Headamp.HA_PREFIX) k) = Headamp.KCell ch p /\
hqu_pair_inv cx r m k v cs keys rf /\
Z.of_nat (length cs) <= keys /\
hqu_x_at cx W2 mem2 cs (keys + 1) rf.

(* ---------------- CELL 0x836e4: the value is in range, the cap test and the cell write ----------------
   s2 = the value, s5 = the channel, a6 = the param (reloaded from R+0x90 on the Int and Float paths). *)
Definition hqu_cut_CELL (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(k : list byte) (v : Model.ent) (ch p val : Z) (cs : list cell) (keys rf : Z)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hqu_base3 cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2
  (hqu_L_seg cx ++ hqu_L_loopc cx ++ hqu_L_t56 cx ++ hqu_L_body cx (Z.of_nat m + 2) ++
   [(LReg 18, val); (LReg 21, ch); (LReg 16, p)]) /\
hqu_fs fx2 9 HQU_F32_M1 /\ hqu_fs fx2 18 HQU_F32_256 /\ hqu_fs fx2 19 HQU_F32_2P63 /\
hqu_live cx r /\ (at0 <= m)%nat /\
Headamp.expect_cell k v = inr (ch, p, val) /\
Headamp.cell_valid (ch, p, val) /\
hqu_pair_inv cx r m k v cs keys rf /\
Z.of_nat (length cs) <= keys /\
hqu_x_at cx W2 mem2 cs (keys + 1) rf.

(* ---------------- RF 0x836a0: the refusal fold (fuzz_headamp.c:144-147) ----------------
   Image B has ONE entry, with the code in a5 (image A has two, 0x83454 and 0x83460): every site that refuses
   sets a5 (0x833c8, 0x8344c, 0x8347c, 0x8366c, 0x8368c) before it jumps here. *)
Definition hqu_cut_RF (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(k : list byte) (v : Model.ent) (bad : Z) (cs : list cell) (keys rf : Z)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hqu_base3 cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2
  (hqu_L_seg cx ++ hqu_L_loopc cx ++ hqu_L_t56 cx ++ hqu_L_body cx (Z.of_nat m + 2) ++
   [(LReg 15, bad)]) /\
hqu_fs fx2 9 HQU_F32_M1 /\ hqu_fs fx2 18 HQU_F32_256 /\ hqu_fs fx2 19 HQU_F32_2P63 /\
hqu_live cx r /\ (at0 <= m)%nat /\
Headamp.expect_cell k v = inl bad /\
(bad = Headamp.REFUSE_BAD_KEY \/ bad = Headamp.REFUSE_OUT_OF_RANGE) /\
hqu_pair_inv cx r m k v cs keys rf /\
hqu_x_at cx W2 mem2 cs (keys + 1) rf.

(* ---------------- LATCH 0x836b4: the pair loop's latch, with the next index j ----------------
   It reads the params-struct word through t5 / t6 again and reloads the entry table from R+0xe0 .. R+0x100.
   The latch tests the params-struct word ONLY: it hands the pair head the index R+0xd8 = j with no bound of
   its own (image B's pair head 0x8314c reads n_ent and tests it, image A's 0x8307c does not), so j is bounded
   HERE. Every way in gives j = m + 2 with m + 1 < n_ent (hqu_pair_inv), so j <= n_ent. *)
Definition hqu_cut_LATCH (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (j : nat)
(cs : list cell) (keys rf : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hqu_base3 cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2
  (hqu_L_seg cx ++ hqu_L_loopc cx ++ hqu_L_t56 cx ++ hqu_L_body cx (Z.of_nat j)) /\
hqu_fs fx2 9 HQU_F32_M1 /\ hqu_fs fx2 18 HQU_F32_256 /\ hqu_fs fx2 19 HQU_F32_2P63 /\
hqu_live cx r /\ 0 < hqu_nent r /\ (j <= length (Model.ents r))%nat /\
hqu_x_at cx W2 mem2 cs keys rf /\ hqu_fold_inv cx r j cs keys rf.

(* ---------------- RC 0x83850 and RCM 0x8385c: the loop is done ----------------
   At RC the answer's rc is the number of cells written (x->n, loaded into a3 at 0x83854, with x in s2 and F
   back in s5 at 0x83858); RCM is the entry the two early exits take with a3 = -1 and x already in s2. From RCM
   on x holds expect_of's answer, which the last four checks read. The frame's shadow still has x in scope: the
   stores at 0x838a0 .. 0x838e0 close it. *)
Definition hqu_cut_RC (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hqu_base3 cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2
  (hqu_L_seg cx ++
   [(LCell XR 0x18, e_F (x_e segs cx)); (LCell XR 0x48, e_F (x_e segs cx));
    (LCell XR 0x138, e_F (x_e segs cx) + HQU_XO);
    (LCell XR 0x140, hd_xv (x_e segs cx) XProps); (LCell XR 0x148, e_pp (x_e segs cx));
    (LCell XR 0x150, 3 * e_cap (x_e segs cx) + 3); (LCell XR 0x158, e_pod (x_e segs cx))]) /\
Model.corrupt r = false /\
ans_rc (hqu_exp cx r) = Z.of_nat (length (ans_cells (hqu_exp cx r))) /\
hqu_x_at cx W2 mem2 (ans_cells (hqu_exp cx r)) (ans_keys (hqu_exp cx r)) (ans_rf (hqu_exp cx r)).
Definition hqu_cut_RCM (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hqu_base3 cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2
  (hqu_L_seg cx ++
   [(LReg 13, ans_rc (hqu_exp cx r)); (LReg 18, e_F (x_e segs cx) + HQU_XO);
    (LReg 21, e_F (x_e segs cx));
    (LCell XR 0x18, e_F (x_e segs cx)); (LCell XR 0x48, e_F (x_e segs cx));
    (LCell XR 0x140, hd_xv (x_e segs cx) XProps); (LCell XR 0x148, e_pp (x_e segs cx));
    (LCell XR 0x150, 3 * e_cap (x_e segs cx) + 3); (LCell XR 0x158, e_pod (x_e segs cx))]) /\
Model.corrupt r = false /\
hqu_x_at cx W2 mem2 (ans_cells (hqu_exp cx r)) (ans_keys (hqu_exp cx r)) (ans_rf (hqu_exp cx r)).

(* ---------------- FIRST 0x838e4: the request of the first block (fuzz_headamp.c:350) ----------------
   Both ways into this cut reach it with x out of scope again: the corrupt record goes straight here from
   0x82fd8, and the checked one through the stores at 0x838a0 .. 0x838e0. *)
Definition hqu_cut_FIRST (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hqu_base3 cx fx2 r (hi_shB headamp_himg_B) ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx segs cx W2 mem2 regs2
  (hqu_L_frame cx ++
   [(LReg 20, e_cap (x_e segs cx)); (LReg 21, e_F (x_e segs cx)); (LReg 22, e_out (x_e segs cx));
    (LReg 25, e_rc (x_e segs cx));
    (LCell XR 0x18, e_F (x_e segs cx));
    (LCell XR 0x140, hd_xv (x_e segs cx) XProps); (LCell XR 0x148, e_pp (x_e segs cx));
    (LCell XR 0x150, 3 * e_cap (x_e segs cx) + 3); (LCell XR 0x158, e_pod (x_e segs cx))]).

(* ---------------- C6 0x83900: the checking segment is done ----------------
   This cut IS headamp_check_contract's post, at the pc its contract names (hi_c6 headamp_himg_B). *)
Definition hqu_cut_C6s (cx : hsu_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_core segs B MT cx (hqu_E3 cx) ly2 S2 W2 regs2 mem2 md2 /\
hqu_fxk fx2 /\
hd_cut segs (w_H W2) mem2 regs2 (x_e segs cx) (hi_L6 headamp_himg_B) /\
hsu_fsh_at segs cx W2 mem2 (hi_shB headamp_himg_B) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_out (x_e segs cx))
  (hd_zbytes (ha_cells_bytes (ans_cells (hqu_ans cx r)))) /\
(exists ev, rd32 (aview segs (w_H W2) mem2) (as_errno B) ev).

(* =====================================================================================================
   THE CONTINUATIONS: "from this cut, the rest of the walk realizes POST"
   =====================================================================================================
   One per cut, with the loop index as an argument and never under the inner quantifier, so that the latch of a
   loop can hand the head its next index and each closure is an induction on the index, not a circular
   hypothesis. POST is generic. Each cut of M03 reaches its pc at the run's own float state. *)
Section f.
Variable cx : hsu_scx segs.
Variable r : Model.pod_rec.
Variable POST : world segs -> config -> Prop.

Definition hqu_from_X : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2, hqu_cut_X cx fx2 r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQU_X regs2 mem2 md2) POST.
Definition hqu_from_PAIR (i : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf,
hqu_cut_PAIR cx fx2 r i cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQU_PAIR regs2 mem2 md2) POST.
Definition hqu_from_SCAN (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf,
hqu_cut_SCAN cx fx2 r at0 m cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQU_SCAN regs2 mem2 md2) POST.
Definition hqu_from_SCANF (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf,
hqu_cut_SCANF cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQU_SCAN regs2 mem2 md2) POST.
Definition hqu_from_KEY (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf,
hqu_cut_KEY cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQU_KEY regs2 mem2 md2) POST.
Definition hqu_from_VAL (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k v ch p cs keys rf,
hqu_cut_VAL cx fx2 r at0 m k v ch p cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQU_VAL regs2 mem2 md2) POST.
Definition hqu_from_CELL (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k v ch p val cs keys rf,
hqu_cut_CELL cx fx2 r at0 m k v ch p val cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQU_CELL regs2 mem2 md2) POST.
Definition hqu_from_RF (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k v bad cs keys rf,
hqu_cut_RF cx fx2 r at0 m k v bad cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQU_RF regs2 mem2 md2) POST.
Definition hqu_from_LATCH (j : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf,
hqu_cut_LATCH cx fx2 r j cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQU_LATCH regs2 mem2 md2) POST.
Definition hqu_from_RC : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2, hqu_cut_RC cx fx2 r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQU_RC regs2 mem2 md2) POST.
Definition hqu_from_RCM : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2, hqu_cut_RCM cx fx2 r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQU_RCM regs2 mem2 md2) POST.
Definition hqu_from_FIRST : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2, hqu_cut_FIRST cx fx2 r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQU_FIRST regs2 mem2 md2) POST.
Definition hqu_from_C6 : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2, hqu_cut_C6s cx fx2 r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQU_C6 regs2 mem2 md2) POST.
End f.

(* =====================================================================================================
   THE PIECE STATEMENTS, one per walk lane of M03 (twelve; image A has eleven, because image B's rotated
   scan head needs its own one-instruction piece and image B has one refusal entry where A has two)
   ===================================================================================================== *)
(* M3a, the head (C5 -> 0x82fdc / 0x838e4): the NULL test (dead), memset(out, 0xa5), res into scope and
   memset(res, 0x5a, 12), the parse, check_no_overrun, check_count, check_cells_valid and the corrupt test. *)
Definition hqu_piece_M3a_head_stmt : Prop :=
forall cx POST r ev,
hqu_start_M03 cx r ev -> hqu_from_X cx r POST -> hqu_from_FIRST cx r POST ->
SRr segs (x_W segs cx) (cfg_at segs (hi_c5 headamp_himg_B) (x_regs segs cx) (x_memc segs cx) (x_mdc segs cx)) POST.
(* M3a, the setup (0x82fdc -> 0x8314c / 0x83850 / 0x8385c): x into scope, memset(x, 0, 0x88), the null flag,
   is_props, params_struct and n_ent, then the loop's constants. *)
Definition hqu_piece_M3a_setup_stmt : Prop :=
forall cx POST r ev,
hqu_start_M03 cx r ev -> hqu_from_PAIR cx r POST 0 -> hqu_from_RC cx r POST -> hqu_from_RCM cx r POST ->
hqu_from_X cx r POST.
(* M3b, the pair loop's head (0x8314c -> 0x83190 / 0x83850): the n_ent read through its instrumented check
   and the scan's operand registers. *)
Definition hqu_piece_M3b_pair_stmt : Prop :=
forall cx POST r ev i,
hqu_start_M03 cx r ev -> hqu_from_SCAN cx r POST i i -> hqu_from_RC cx r POST ->
hqu_from_PAIR cx r POST i.
(* M3b, one turn of the scan (0x83190 -> 0x83190 / 0x83850): the entry's type, size and last body byte
   (pod.h:92), each read through an instrumented check. *)
Definition hqu_piece_M3b_scan_stmt : Prop :=
forall cx POST r ev at0 m,
hqu_start_M03 cx r ev -> hqu_from_SCAN cx r POST at0 (S m) -> hqu_from_SCANF cx r POST at0 m ->
hqu_from_RC cx r POST ->
hqu_from_SCAN cx r POST at0 m.
(* M3b, the scan head's leaving arm (0x83190 -> 0x83260): the `bnez s7` of the rotated loop. *)
Definition hqu_piece_M3b_scanf_stmt : Prop :=
forall cx POST r ev at0 m,
hqu_start_M03 cx r ev -> hqu_from_KEY cx r POST at0 m -> hqu_from_SCANF cx r POST at0 m.
(* M3b, the latch (0x836b4 -> 0x8314c / 0x83850). *)
Definition hqu_piece_M3b_latch_stmt : Prop :=
forall cx POST r ev j,
hqu_start_M03 cx r ev -> hqu_from_PAIR cx r POST j -> hqu_from_RC cx r POST ->
hqu_from_LATCH cx r POST j.
(* M3b, the refusal fold (0x836a0 -> 0x836b4). *)
Definition hqu_piece_M3b_refuse_stmt : Prop :=
forall cx POST r ev at0 m,
hqu_start_M03 cx r ev -> hqu_from_LATCH cx r POST (S (S m)) ->
hqu_from_RF cx r POST at0 m.
(* M3c, the key and the channel (0x83260 -> 0x83490 / 0x836a0 / 0x836b4 / 0x83850): the strncmp wrapper,
   x->keys++, read_channel's two loops, the '.' test and the strcmp chain. *)
Definition hqu_piece_M3c_key_stmt : Prop :=
forall cx POST r ev at0 m,
hqu_start_M03 cx r ev -> hqu_from_VAL cx r POST at0 m -> hqu_from_RF cx r POST at0 m ->
hqu_from_LATCH cx r POST (S (S m)) -> hqu_from_RC cx r POST ->
hqu_from_KEY cx r POST at0 m.
(* M3d, the value (0x83490 -> 0x836a0 / 0x836e4): pod_bool, pod_int, pod_float and the inlined pod_nearest
   with its six soft-float calls (image B makes two __gttf2 calls image A does not). *)
Definition hqu_piece_M3d_value_stmt : Prop :=
forall cx POST r ev at0 m,
hqu_start_M03 cx r ev -> hqu_from_CELL cx r POST at0 m -> hqu_from_RF cx r POST at0 m ->
hqu_from_VAL cx r POST at0 m.
(* M3e, the cell write (0x836e4 -> 0x836b4 / 0x83850): the cap break and the three instrumented stores. *)
Definition hqu_piece_M3e_cell_stmt : Prop :=
forall cx POST r ev at0 m,
hqu_start_M03 cx r ev -> hqu_from_LATCH cx r POST (S (S m)) -> hqu_from_RC cx r POST ->
hqu_from_CELL cx r POST at0 m.
(* M3e, x->rc and the last four checks (0x83850 / 0x8385c -> 0x838e4), then x out of scope. *)
Definition hqu_piece_M3e_rc_stmt : Prop :=
forall cx POST r ev,
hqu_start_M03 cx r ev -> hqu_from_FIRST cx r POST ->
hqu_from_RC cx r POST /\ hqu_from_RCM cx r POST.
(* M24, the first block's request (0x838e4 -> C6). *)
Definition hqu_piece_M24_first_stmt : Prop :=
forall cx POST r ev,
hqu_start_M03 cx r ev -> hqu_from_C6 cx r POST -> hqu_from_FIRST cx r POST.

(* =====================================================================================================
   THE UBSAN TRAP FAMILIES: what rules out each of M03's 24 branches to `unimp`
   =====================================================================================================
   `unimp` has no step, so every one of these branches must be shown NOT taken. The families, by the fact that
   rules them out (PLAN section 4.2's discharges), with the sites of each:
   - a pointer sum stays below 2 ^ 64 (0x82f98 out + 3 cap; 0x83198 &ent[at]; 0x831e0 the body's last byte;
     0x8349c the value entry; 0x83708 and 0x83744 the cell): the code tests the one's complement of the base
     against the offset, so hqu_t_ptr turns the sum's bound into the test's;
   - the same, as a `bgeu` against a negative literal (0x832d8, the key's 13 bytes): hqu_t_ptr_ge;
   - a signed 32-bit value is incremented (0x83264 at + 1, 0x832b8 x->keys + 1, 0x83678 t + 1) or decremented
     (0x8365c t - 1): hqu_t_addw, hqu_t_subw; hqu_t_keys reads the first of these off the cut;
   - a signed multiply does not overflow (0x833a0, read_channel's acc * 10, where `mulh` and an arithmetic
     shift of the low word are compared): hqu_t_mulw with hqu_t_mul_fits;
   - an entry index is below the table's bound 33 (0x83194, 0x83494): hqu_t_idx, with hqu_t_scan_idx reading
     the bound off the scan's cut;
   - a cell index is below 10 (0x836f4, 0x83730): hqu_t_cells;
   - the cursor stays inside the key's body (0x83310 by way of 0x8330c, 0x8334c, 0x833b4, 0x833e4, 0x833f0,
     0x83400): hqu_t_cursor, from the key entry's size bound;
   - the float-cast bounds (0x835ec against fs3 and 0x83604 against the binary128 constant of R+0xb0 / R+0xb8):
     hqu_t_fcast_consts identifies the two constants by their fields, which is what the soft-float contracts of
     the value piece compare against. *)

(* the one's complement as the walk meets it: `not rd,rs` leaves 2 ^ 64 - 1 - v for a 64-bit v *)
Lemma hqu_not_mod : forall v, 0 <= v < 2 ^ 64 -> hqu_not v mod 2 ^ 64 = 2 ^ 64 - 1 - v.
Proof.
intros v Hv. unfold hqu_not.
replace (-1 - v) with ((2 ^ 64 - 1 - v) + (-1) * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
(* the pointer family: the test is `offset <u complement of base`, which the sum's bound rules out *)
Lemma hqu_t_ptr : forall base n, 0 <= base < 2 ^ 64 -> 0 <= n -> base + n < 2 ^ 64 ->
  n <= hqu_not base mod 2 ^ 64.
Proof. intros base n Hb Hn Hs. rewrite hqu_not_mod by lia. lia. Qed.
(* its `bgeu` form, where the literal is written as a negative *)
Lemma hqu_t_ptr_ge : forall base n, 0 <= base < 2 ^ 64 -> 0 < n -> base + n < 2 ^ 64 ->
  base < (- n) mod 2 ^ 64.
Proof.
intros base n Hb Hn Hs.
replace (- n) with ((2 ^ 64 - n) + (-1) * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.
(* the signed 32-bit increment and decrement families *)
Lemma hqu_t_addw : forall v, - 2 ^ 31 <= v < 2 ^ 31 - 1 -> - 2 ^ 31 <= v + 1 < 2 ^ 31 /\ v < v + 1.
Proof. intros v Hv. lia. Qed.
Lemma hqu_t_subw : forall v, - 2 ^ 31 < v <= 2 ^ 31 - 1 -> - 2 ^ 31 <= v - 1 < 2 ^ 31 /\ v - 1 < v.
Proof. intros v Hv. lia. Qed.
(* the signed multiply family: when the product fits in 64 bits the high word of the 128-bit product is the
   arithmetic shift of the low word by 63, which is what the code compares *)
Lemma hqu_t_mulw : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> Z.shiftr x 64 = Z.shiftr x 63.
Proof.
intros x Hx. rewrite !Z.shiftr_div_pow2 by lia.
destruct (Z_lt_le_dec x 0) as [Hneg|Hpos].
- assert (H1 : x / 2 ^ 64 = -1).
  { replace x with ((x + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (H2 : x / 2 ^ 63 = -1).
  { replace x with ((x + 2 ^ 63) + (-1) * 2 ^ 63) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  rewrite H1, H2. reflexivity.
- rewrite (Z.div_small x (2 ^ 64)) by lia. rewrite (Z.div_small x (2 ^ 63)) by lia. reflexivity.
Qed.
Lemma hqu_t_mul_fits : forall a b, - HQU_RC_BIG <= a <= HQU_RC_BIG -> 0 <= b <= 10 ->
  - 2 ^ 63 <= a * b < 2 ^ 63.
Proof. intros a b Ha Hb. unfold HQU_RC_BIG in Ha. nia. Qed.
(* the entry-index family: the loop's bound register is 33 whenever the first entry index is at most 32 *)
Lemma hqu_t_idx : forall at0 m, (at0 <= 32)%nat -> (m < 33)%nat ->
  Z.max 33 (Z.of_nat at0) = 33 /\ Z.of_nat m <> Z.max 33 (Z.of_nat at0).
Proof. intros at0 m Ha Hm. split; lia. Qed.
(* the cell-index family: x holds at most X_CELLS cells and the cap is at most 9 *)
Lemma hqu_t_cells : forall cx W2 mem2 cs keys rf,
  hqu_x_at cx W2 mem2 cs keys rf -> e_cap (x_e segs cx) <= 9 ->
  0 <= Z.of_nat (length cs) <= 9 /\ Z.of_nat (length cs) < 10.
Proof.
intros cx W2 mem2 cs keys rf Hx Hcap.
destruct Hx as (_ & Hle & Hcs & _ & _ & _). unfold X_CELLS in Hle. lia.
Qed.
(* the x->keys family, read off the cut: the counter is below 2 ^ 31 - 1, so its increment does not overflow *)
Lemma hqu_t_keys : forall cx W2 mem2 cs keys rf,
  hqu_x_at cx W2 mem2 cs keys rf -> - 2 ^ 31 <= keys < 2 ^ 31 - 1 /\ keys < keys + 1.
Proof.
intros cx W2 mem2 cs keys rf Hx. destruct Hx as (_ & _ & _ & _ & Hk & _). lia.
Qed.
(* the cursor family: the key entry's body is at most 45 bytes, so every index read_channel forms is small *)
Lemma hqu_t_cursor : forall (v : Model.ent) (i : Z),
  Model.ent_wf v -> 0 <= i <= Model.e_size v -> 0 <= i <= 45 /\ i < 2 ^ 31.
Proof. intros v i Hw Hi. destruct Hw as (_ & _ & Hs). lia. Qed.
(* the scan's index bound, read off the cut *)
Lemma hqu_t_scan_idx : forall cx fx2 r at0 m cs keys rf ly2 S2 W2 regs2 mem2 md2,
Model.pod_rec_wf r ->
hqu_cut_SCAN cx fx2 r at0 m cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
(at0 <= 32)%nat /\ (m < 33)%nat.
Proof.
intros cx fx2 r at0 m cs keys rf ly2 S2 W2 regs2 mem2 md2 Hw HSC.
destruct HSC as (_ & _ & _ & _ & _ & _ & Hm & _ & _ & _).
destruct (Model.ents_wf r Hw) as [Hle _]. split; lia.
Qed.
(* the float-cast family: the two constants the test compares against, by their fields. 0x5f000000 is the
   binary32 2 ^ 63 (sign 0, exponent 190, significand 0); the pair (R+0xb0, R+0xb8) is the binary128
   -(2 ^ 63 + 1) (sign 1, exponent 16446, significand 2 ^ 49 of 112 bits). *)
Lemma hqu_t_fcast_consts :
  Z.shiftr HQU_F32_2P63 31 = 0 /\ Z.shiftr HQU_F32_2P63 23 mod 256 = 190 /\
  HQU_F32_2P63 mod 2 ^ 23 = 0 /\
  Z.shiftr HQU_C2HI 63 = 1 /\ Z.shiftr HQU_C2HI 48 mod 2 ^ 15 = 16446 /\
  HQU_C2HI mod 2 ^ 48 = 0 /\ HQU_C2LO = 2 ^ 49 /\
  HQU_F32_M1 = 0xbf800000 /\ HQU_F32_256 = 0x43800000.
Proof.
unfold HQU_F32_2P63, HQU_C2HI, HQU_C2LO, HQU_F32_M1, HQU_F32_256.
repeat split; vm_compute; reflexivity.
Qed.

(* =====================================================================================================
   THE SEAM: headamp_check_contract from the pieces
   =====================================================================================================
   The two loops close by induction on the loop index: the pair loop on 33 - i (a head state has
   i <= |ents r| <= 32) and the scan on 32 - m (a scan state has m < |ents r| <= 32); a key found at m hands
   the latch the index m + 2, so the outer induction hypothesis serves it. Nothing here walks an instruction. *)
(* A cut is taken apart by its own pattern, never by a `repeat ... destruct` over the context: a Section
   hypothesis cannot be cleared, so such a tactic does not end on one. *)
Lemma hqu_cut_PAIR_bound : forall cx fx2 r i cs keys rf ly2 S2 W2 regs2 mem2 md2,
Model.pod_rec_wf r ->
hqu_cut_PAIR cx fx2 r i cs keys rf ly2 S2 W2 regs2 mem2 md2 -> (i <= 32)%nat.
Proof.
intros cx fx2 r i cs keys rf ly2 S2 W2 regs2 mem2 md2 Hw HP.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & Hi & _ & _).
destruct (Model.ents_wf r Hw) as [Hle _]. lia.
Qed.

Lemma hqu_cut_SCAN_bound : forall cx fx2 r at0 m cs keys rf ly2 S2 W2 regs2 mem2 md2,
Model.pod_rec_wf r ->
hqu_cut_SCAN cx fx2 r at0 m cs keys rf ly2 S2 W2 regs2 mem2 md2 -> (m < 32)%nat /\ (at0 <= m)%nat.
Proof.
intros cx fx2 r at0 m cs keys rf ly2 S2 W2 regs2 mem2 md2 Hw HSC.
destruct HSC as (_ & _ & _ & _ & _ & _ & Hm & _ & _ & _).
destruct (Model.ents_wf r Hw) as [Hle _]. split; lia.
Qed.

Section m03.
Variable cx : hsu_scx segs.
Variable r : Model.pod_rec.
Variable POST : world segs -> config -> Prop.
Variable ev : Z.
Hypothesis HS : hqu_start_M03 cx r ev.
(* M3b *)
Hypothesis PM3b_pair : hqu_piece_M3b_pair_stmt.
Hypothesis PM3b_scan : hqu_piece_M3b_scan_stmt.
Hypothesis PM3b_scanf : hqu_piece_M3b_scanf_stmt.
Hypothesis PM3b_latch : hqu_piece_M3b_latch_stmt.
Hypothesis PM3b_refuse : hqu_piece_M3b_refuse_stmt.
(* M3c, M3d, M3e *)
Hypothesis PM3c_key : hqu_piece_M3c_key_stmt.
Hypothesis PM3d_value : hqu_piece_M3d_value_stmt.
Hypothesis PM3e_cell : hqu_piece_M3e_cell_stmt.
(* the cut the loop may leave to *)
Hypothesis HRC : hqu_from_RC cx r POST.

Lemma hqu_wf : Model.pod_rec_wf r.
Proof. pose proof HS as H0. destruct H0 as (_ & _ & H & _). exact H. Qed.

(* one turn of the pair loop's body, given the latch of the next turn *)
Lemma hqu_body_closed : forall at0 m,
hqu_from_LATCH cx r POST (S (S m)) -> hqu_from_KEY cx r POST at0 m.
Proof.
intros at0 m HL.
assert (HRF : hqu_from_RF cx r POST at0 m) by exact (PM3b_refuse cx POST r ev at0 m HS HL).
assert (HCELL : hqu_from_CELL cx r POST at0 m) by exact (PM3e_cell cx POST r ev at0 m HS HL HRC).
assert (HVAL : hqu_from_VAL cx r POST at0 m) by exact (PM3d_value cx POST r ev at0 m HS HCELL HRF).
exact (PM3c_key cx POST r ev at0 m HS HVAL HRF HL HRC).
Qed.

(* the scan, closed: from its head at any m, given the pair loop's heads above at0 *)
Lemma hqu_scan_closed : forall at0,
(forall j, (at0 < j)%nat -> hqu_from_PAIR cx r POST j) -> forall m, hqu_from_SCAN cx r POST at0 m.
Proof.
intros at0 HP.
assert (H : forall f m, (32 - m <= f)%nat -> hqu_from_SCAN cx r POST at0 m).
{ induction f as [|f IH]; intros m Hm.
  - intros fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf HSC. exfalso.
    destruct (hqu_cut_SCAN_bound cx fx2 r at0 m cs keys rf ly2 S2 W2 regs2 mem2 md2 hqu_wf HSC). lia.
  - destruct (Nat.lt_ge_cases m at0) as [Hlt|Hge].
    + intros fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf HSC. exfalso.
      destruct (hqu_cut_SCAN_bound cx fx2 r at0 m cs keys rf ly2 S2 W2 regs2 mem2 md2 hqu_wf HSC). lia.
    + assert (HL : hqu_from_LATCH cx r POST (S (S m)))
        by exact (PM3b_latch cx POST r ev (S (S m)) HS (HP (S (S m)) ltac:(lia)) HRC).
      assert (HF : hqu_from_SCANF cx r POST at0 m)
        by exact (PM3b_scanf cx POST r ev at0 m HS (hqu_body_closed at0 m HL)).
      exact (PM3b_scan cx POST r ev at0 m HS (IH (S m) ltac:(lia)) HF HRC). }
intros m. exact (H (32 - m)%nat m (le_n _)).
Qed.

(* the pair loop, closed: from its head at any i *)
Lemma hqu_pairs_closed : forall i, hqu_from_PAIR cx r POST i.
Proof.
assert (H : forall f i, (33 - i <= f)%nat -> hqu_from_PAIR cx r POST i).
{ induction f as [|f IH]; intros i Hi.
  - intros fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf HP. exfalso.
    pose proof (hqu_cut_PAIR_bound cx fx2 r i cs keys rf ly2 S2 W2 regs2 mem2 md2 hqu_wf HP). lia.
  - apply (PM3b_pair cx POST r ev i HS); [| exact HRC].
    apply (hqu_scan_closed i). intros j Hj. apply IH. lia. }
intros i. exact (H (33 - i)%nat i (le_n _)).
Qed.
End m03.

(* the contract itself, from the twelve piece statements *)
Section seam.
Hypothesis PM3a_head : hqu_piece_M3a_head_stmt.
Hypothesis PM3a_setup : hqu_piece_M3a_setup_stmt.
Hypothesis PM3b_pair : hqu_piece_M3b_pair_stmt.
Hypothesis PM3b_scan : hqu_piece_M3b_scan_stmt.
Hypothesis PM3b_scanf : hqu_piece_M3b_scanf_stmt.
Hypothesis PM3b_latch : hqu_piece_M3b_latch_stmt.
Hypothesis PM3b_refuse : hqu_piece_M3b_refuse_stmt.
Hypothesis PM3c_key : hqu_piece_M3c_key_stmt.
Hypothesis PM3d_value : hqu_piece_M3d_value_stmt.
Hypothesis PM3e_cell : hqu_piece_M3e_cell_stmt.
Hypothesis PM3e_rc : hqu_piece_M3e_rc_stmt.
Hypothesis PM24_first : hqu_piece_M24_first_stmt.

Theorem headamp_check_holds : forall RLO RHI : Z,
headamp_check_contract segs B MT headamp_himg_B RLO RHI.
Proof.
intros RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs e pos ev r
  HPRE HL5 Hwf Hlen Hpp Hpod Hfb Hra Hhull Hamem Hal Hfo Hrao Hap Hrc Herr Hfrm.
set (cx := {| x_STK := STK; x_sp0 := sp0; x_FP := FP; x_ly := ly; x_S := S; x_W0 := W0; x_mem0 := mem0;
  x_md0 := md0; x_own := own; x_k := k; x_regs := regs; x_lyc := lyc; x_Sc := Sc; x_W := W; x_memc := memc;
  x_mdc := mdc; x_RLO := RLO; x_RHI := RHI; x_e := e; x_pos := pos |} : hsu_scx segs).
assert (HS : hqu_start_M03 cx r ev).
{ split; [exact HPRE|]. split; [exact HL5|]. split; [exact Hwf|]. split; [exact Hlen|].
  split; [exact Hpp|]. split; [exact Hpod|]. split; [exact Hfb|]. split; [exact Hra|].
  split; [exact Hhull|]. split; [exact Hamem|]. split; [exact Hal|]. split; [exact Hfo|].
  split; [exact Hrao|]. split; [exact Hap|]. split; [exact Hrc|]. split; [exact Herr | exact Hfrm]. }
(* the contract's post, as the pieces' POST; M03's last cut is it *)
set (POST := hd_seg_post segs B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
  (hi_c6 headamp_himg_B) (hd_fxk HQU_FXK fx)
  (fun a => hd_inw e (hi_w3 headamp_himg_B) a \/ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) \/
            (as_errno B <= a < as_errno B + 4))
  (fun W2 regs2 mem2 =>
   hd_cut segs (w_H W2) mem2 regs2 e (hi_L6 headamp_himg_B) /\
   hd_fsh segs (w_H W2) mem2 (e_F e) (hi_shB headamp_himg_B) /\
   garr8 segs (mrestrict (w_H W2) mem2) (e_out e)
     (hd_zbytes (ha_cells_bytes (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))) /\
   (exists ev', rd32 (aview segs (w_H W2) mem2) (as_errno B) ev'))).
assert (HC6 : hqu_from_C6 cx r POST).
{ intros fx2 ly2 S2 W2 regs2 mem2 md2 HC.
  destruct HC as (Hcore & Hfxk & HL6 & Hfsh & Hout & Hev).
  destruct Hcore as (HJ & Hr234 & Hfr & Hperm & Hio & Hmo & Hmem).
  apply SRr_ret. exists fx2, ly2, S2, regs2, mem2, md2.
  split; [reflexivity|]. split; [exact Hfxk|]. split; [exact HJ|]. split; [exact Hr234|].
  split; [exact Hfr|]. split; [exact Hperm|]. split; [exact Hio|]. split; [exact Hmo|].
  split; [exact Hmem|]. split; [exact HL6|]. split; [exact Hfsh|]. split; [exact Hout | exact Hev]. }
assert (HFIRST : hqu_from_FIRST cx r POST) by exact (PM24_first cx POST r ev HS HC6).
destruct (PM3e_rc cx POST r ev HS HFIRST) as [HRC HRCM].
assert (HPAIR0 : hqu_from_PAIR cx r POST 0)
  by exact (hqu_pairs_closed cx r POST ev HS PM3b_pair PM3b_scan PM3b_scanf PM3b_latch PM3b_refuse PM3c_key
             PM3d_value PM3e_cell HRC 0%nat).
assert (HX : hqu_from_X cx r POST) by exact (PM3a_setup cx POST r ev HS HPAIR0 HRC HRCM).
exact (PM3a_head cx POST r ev HS HX HFIRST).
Qed.
End seam.

End d.
End c.
End b.

Print Assumptions headamp_check_holds.
