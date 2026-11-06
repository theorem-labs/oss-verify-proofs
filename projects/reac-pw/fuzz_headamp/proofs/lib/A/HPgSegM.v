(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): THE CUT STATES of the second half of the walk of LLVMFuzzerTestOneInput (0x80bc0,
   12924 bytes, 3231 instructions) - the third allocator return C5 0x82e98, the fourth C7 0x83744, the copy split
   C8 0x83764, C9 0x83794 and the frame's retirement join 0x837c4 - and the statement of every piece the checking
   segment M03 (C5 -> C6 0x83740) is split into. Statement text only: no function of a binary is proved here. The
   two theorems at the end add no walk: they chain the piece statements into lib/A/HPgCSpec.v's fixed segment
   contract headamp_check_contract and close its two loops by induction on the loop index.

   WHAT THIS FILE IS FOR. The walk is cut at the nine pcs of the plain walk of the same function, one at each
   allocator call and one at each allocator return (lib/A/HPgCSpec.v hi_c1 .. hi_c9 at lib/A/HPgImgA.v's record
   headamp_himg_A). The five middle segments M01 / M02 / M03 / M04a / M04b are the fixed contracts
   headamp_build_contract, headamp_dup_contract, headamp_check_contract, headamp_first_contract and
   headamp_plain_contract; E01 (ENTRY -> C1) and X01 (C9 -> the return) are not contract texts, because each of
   them makes or ends blocks and the frame for locals. This file holds
   - the harness-level cut states at C5, C6, C7, C8, C9 and at the retirement join J 0x837c4: what the chaining
     carries across the contracts (the harness's journal from its entry, the blocks live, the geometry, the
     thirteen saved words and the frame's flag-pointer cell), stated relative to the harness's entry state
     (hq_hcx), as the three other segments of the walk need them;
   - the statement of the allocator step C6 -> C7 (the `jal` of malloc(first) at 0x83740 and its return) and of
     the two X01 pieces (C9 -> J: the four frees; J -> the return: the frame's retirement word, the release of
     its shadow and the epilogue);
   - the sub-cuts of M03 and the statement of each of its pieces, in continuation form: a piece lemma is
     `the segment's start facts -> <the continuations of its end cuts> -> <the continuation of its start cut>`,
     so that the pieces are proved in parallel and each proof sees only the STATEMENTS of the pieces its
     continuation goes to. The loop index is an argument of the head's continuation and never under the inner
     quantifier, so each loop closes by induction on that index.

   M03's shape (fuzz_headamp.c:330-350, measured over the function's CFG): it fills the out block with the guard
   byte, sets res to 0x5a, calls the parse on the pod (or on NULL by the harness's null flag), runs
   check_no_overrun, check_count and check_cells_valid, and, when pp->corrupt is 0, runs the inlined expect_of
   (fuzz_headamp.c:109-157) into the frame object x and then check_object, check_cells and, for rc >= 0,
   check_keys and check_refusal. expect_of is two nested loops: the pair loop (head 0x8307c, latch 0x83474) whose
   body is one call of the inlined pod_next_pair (its scan head 0x830a0), the prefix test (the strncmp wrapper at
   0x83190), read_channel (the blanks loop 0x831c0 and the digits loop 0x83264), the strcmp chain
   (0x832e8 / 0x832fc / 0x83310), cell_value with the inlined pod_nearest (0x83364 .. 0x83544, five soft-float
   calls), the cell write (0x83548) and the refusal fold (0x83460).

   WHERE A VALUE LIVES. s0 = S the entry sp, s1 = R the 32-aligned base of the real frame (R + 0x1e0 <= S),
   s3 = (F >> 3) + K the frame's shadow base and s7 = K the runtime's shadow offset are fixed from 0x80c10 to the
   epilogue. The frame for locals F is a side-stack frame of class 4; M03 reads and writes its last two objects,
   res (12 bytes at F+0x180) and x (struct expect, 136 bytes at F+0x1a0). Inside M03 s6 = cap, s8 = out,
   s9 = pod, s10 = res and s11 = rc; the pair loop keeps the record's entry table in ra and t6 (pp+0x4014),
   n_ent in t2 and n_ent - 1 in t3, 104 in a7, the String type 8 in t4 and -1 in t5, the two binary32 bounds of
   pod_nearest in fs1 (-1.0f) and fs2 (256.0f), and the loop's constants in the real-frame cells R+0xa8 (the high
   word of -0.5L), R+0xb0 (0.5L), R+0xb8 (&x.cell[0]), R+0xc0 (1000000), R+0xe8 (&ent[0].size), R+0xf8 and
   R+0x100 (&ent[0].body), R+0x108 (x). The parse's first argument (pod, or 0 when the null flag is set) is at
   R+0x110 and the out block's size at R+0x118 from 0x82ea8 on.

   THE MODEL. The quantities a cut names are the shared model's (lib/Pod): the record in the pp block is a
   Model.pod_rec r, the answer of the parse is Pod/Headamp.v's parse_props on the pod bytes (Model.buf r) at the
   harness's cap, and what expect_of computes is Pod/Headamp.v's expect_model at the same cap. The pair loop's
   invariant is one equation on Pod/Headamp.v's ha_fold over the pairs Pod/Accessors.v's pairs_by leaves, and the
   frame object x holds, byte for byte, what the fold has written so far (hq_x_open).
   Proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgImgA HPgSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================= the pcs of the cuts =======================================
   The five harness-level pcs of this half of the walk are headamp_himg_A's hi_c5 .. hi_c9; J and the return are
   the walk's own. *)
Definition HQ_C5 : Z := 0x82e98.    (* `beqz a0` after the `jal` of malloc(out) 0x82e94 *)
Definition HQ_C6 : Z := 0x83740.    (* the `jal` of malloc(first) *)
Definition HQ_C7 : Z := 0x83744.    (* `beqz a0` after it *)
Definition HQ_C8 : Z := 0x83764.    (* after the __asan_memcpy that fills first (jal 0x83760) *)
Definition HQ_C9 : Z := 0x83794.    (* `mv a0,s2` after check_plain returns, before the `jal` of free(first) *)
Definition HQ_J : Z := 0x837c4.     (* `lui a0,0x45e03`: the frame's retirement word, after the four frees *)
(* inside M03 *)
Definition HQ_X : Z := 0x82f30.     (* pp->corrupt = 0: the frame object x comes into scope *)
Definition HQ_PAIR : Z := 0x8307c.  (* the pair loop's head (fuzz_headamp.c:119) *)
Definition HQ_SCAN : Z := 0x830a0.  (* the inlined pod_next_pair's scan head (pod.h:134) *)
Definition HQ_KEY : Z := 0x83168.   (* a pair was found: its key is about to be compared with the prefix *)
Definition HQ_VAL : Z := 0x83364.   (* the key is a cell address: cell_value of the pair's value pod *)
Definition HQ_CELL : Z := 0x83548.  (* the value is in range: the cap test and the cell write *)
Definition HQ_RFA : Z := 0x83454.   (* a refusal from cell_value: t2 and t6 are reloaded, t3 := OUT_OF_RANGE *)
Definition HQ_RF : Z := 0x83460.    (* the refusal fold (fuzz_headamp.c:144-147) with t3 = the code *)
Definition HQ_LATCH : Z := 0x83474. (* the pair loop's latch *)
Definition HQ_RC : Z := 0x83694.    (* the loop is done: x->rc := x->n, then the last four checks *)
Definition HQ_RCM : Z := 0x8369c.   (* its second entry: x->rc := -1 (the null flag or not a Props object) *)
Definition HQ_FIRST : Z := 0x83724. (* the request of the first block (fuzz_headamp.c:350) *)

(* the frame for locals: class 4 (`addi a0,zero,0x280` 0x80c38, the call at 0x80c3c), 1024 bytes, its flag
   pointer in the last word; the real frame below the entry sp S; the events of the whole run (four allocations
   and four frees) *)
Definition HQ_CID : Z := 4.
Definition HQ_RSZ : Z := 0x1e0.
Definition HQ_FLAG : Z := 0x3f8.
Definition HQ_EV : Z := 8.
(* the two frame objects M03 writes *)
Definition HQ_RES : Z := 0x180.
Definition HQ_XO : Z := 0x1a0.
(* the offsets of struct expect's fields (fuzz_headamp.c:56-62) *)
Definition HQ_X_CELL0 : Z := 4.
Definition HQ_X_N : Z := 0x7c.
(* the record's fields the pair loop reads (pod.h:77-86): ent[0] and n_ent inside the pp block *)
Definition HQ_ENT0 : Z := 0x4014.
Definition HQ_ENT_SZ : Z := 0x4018.
Definition HQ_ENT_BODY : Z := 0x401c.

Lemma hq_pcs_himg :
  hi_c5 headamp_himg_A = HQ_C5 /\ hi_c6 headamp_himg_A = HQ_C6 /\ hi_c7 headamp_himg_A = HQ_C7 /\
  hi_c8 headamp_himg_A = HQ_C8 /\ hi_c9 headamp_himg_A = HQ_C9 /\
  hi_cid headamp_himg_A = HQ_CID /\ hi_rsz headamp_himg_A = HQ_RSZ.
Proof. repeat split; reflexivity. Qed.
Lemma hq_offs_layout :
  HQ_ENT0 = Layout.OFF_ENT /\ HQ_ENT_SZ = Layout.OFF_ENT + 4 /\ HQ_ENT_BODY = Layout.OFF_ENT + 8 /\
  Layout.ENT_SIZE = 104.
Proof. repeat split; reflexivity. Qed.

(* The byte values of the frame's shadow M03 passes through. headamp_A_shA is the prologue's pattern (80
   granules of the 0x280-byte frame); headamp_A_shB opens res's two granules 0x30 (0x00) and 0x31 (0x04) at
   0x82eb8 / 0x82ebc; hq_shX opens x's seventeen granules 0x34 .. 0x44 at 0x82f38 .. 0x82f78 and is the pattern
   of every cut between 0x82f78 and the stores at 0x836dc .. 0x83720 that close them again. *)
Definition hq_shX : list Z :=
  firstn 52 headamp_A_shB ++ repeat 0 17 ++ skipn 69 headamp_A_shB.
Lemma hq_shX_len : length hq_shX = 80%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma hq_shB_len : length headamp_A_shB = 80%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma hq_shX_x : forall i, (52 <= i < 69)%nat -> nth i hq_shX 0 = 0.
Proof.
  intros i Hi.
  assert (E : forall j, (j < 17)%nat -> nth (52 + j) hq_shX 0 = 0).
  { intros j Hj. do 17 (destruct j as [|j]; [vm_compute; reflexivity|]). lia. }
  replace i with (52 + (i - 52))%nat by lia. apply E. lia.
Qed.
(* outside x's granules hq_shX is headamp_A_shB (the prologue's guards and res's two granules) *)
Lemma hq_shX_out : forall i, (i < 52)%nat \/ (69 <= i < 80)%nat -> nth i hq_shX 0 = nth i headamp_A_shB 0.
Proof.
  intros i Hi. destruct Hi as [Hi|Hi].
  - do 52 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
  - assert (Hj : (i - 69 < 11)%nat) by lia. replace i with (69 + (i - 69))%nat by lia.
    set (j := (i - 69)%nat) in *. clearbody j.
    do 11 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.

(* ===== the bytes of the frame object x while the pair loop runs =====
   x->rc is still the memset's 0 (it is written at 0x8369c); the cells written so far, then the zero cells up to
   ten; then x->n = the number of cells, x->keys and x->refusal (Spec/HeadBytes.v ha_res_bytes). *)
Definition hq_x_open (cs : list cell) (keys rf : Z) : list byte :=
  repeat (Z_to_bv 8 0) 4 ++ x_cells_bytes cs ++
  repeat (Z_to_bv 8 0) (12 * (X_CELLS - length cs)) ++ ha_res_bytes (Z.of_nat (length cs)) keys rf.
Lemma hq_x_open_len : forall cs keys rf, (length cs <= X_CELLS)%nat ->
  length (hq_x_open cs keys rf) = 136%nat.
Proof.
  intros cs keys rf H. unfold hq_x_open, X_CELLS in *.
  rewrite !length_app, !repeat_length, length_x_cells_bytes, length_ha_res_bytes. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* a float register holds a nan-boxed binary32 word: fs1 = -1.0f and fs2 = 256.0f, the two bounds of the inlined
   pod_nearest (`lui; fmv.w.x` 0x8301c / 0x83030 and 0x83020 / 0x83044) *)
Definition hq_fs (fx2 : YK11.FPState) (k v : Z) : Prop :=
  Sem.reg_get (@fp_regs fx2) (Z_to_bv 5 k) = Sem.nan_box (Z_to_bv 32 v).
Definition HQ_F32_M1 : Z := 0xbf800000.
Definition HQ_F32_256 : Z := 0x43800000.
(* the high words of -0.5L and 0.5L, in the real-frame cells R+0xa8 and R+0xb0 (0x83048 .. 0x83054) *)
Definition HQ_MHALF_HI : Z := 0xbffe000000000000.
Definition HQ_HALF_HI : Z := 0x3ffe000000000000.
(* read_channel's bound, in R+0xc0 (0x8303c, 0x83040) *)
Definition HQ_RC_BIG : Z := 1000000.

(* the float registers M03 may write, as headamp_check_contract's post names them: fs0, fs1, fa0, fa4, fa5, fs2,
   fs3 (f8, f9, f10, f14, f15, f18, f19; image A never writes fs3, image B's float-cast bound does) *)
Definition hq_fxk (fx2 : YK11.FPState) : Prop := hd_fxk [8; 9; 10; 14; 15; 18; 19] fx fx2.

(* =====================================================================================================
   PART 1. The harness level: what the chaining carries across the contracts
   =====================================================================================================
   Every cut below is stated relative to the harness's ENTRY state (hq_hcx) and its journal from there (hq_j:
   no footprint, own = the frame for locals, k events). A cut states only what the chaining cannot derive: the
   static conjuncts of hd_seg_pre (arodata_okP, the registered globals' and the strings' shadow, the read-only cells,
   the guard word hd_guard_ok, rom_view) are re-derived at each contract's start from the symbols and the journal, and the frames and the
   block disjointness follow from the journal and the block list. What must survive from C1 to the return is
   carried here: the thirteen callee-saved words the prologue stores at [S - 0x68, S) (ra at S - 8, s0 at
   S - 0x10, ..., s11 at S - 0x68: `sd ra,0x1d8(sp)` 0x80bc8 .. `sd s11,0x178(sp)` 0x80bf8 after
   `addi sp,sp,-0x1e0`), the three float saves at S - 0x70, S - 0x78 and S - 0x80 (`fsd fs0,0x170(sp)` 0x80bfc
   .. 0x80c04), which the epilogue reads back (`fld` 0x83834 .. 0x8383c), and the frame's flag-pointer word at
   F + 0x3f8 (the class-4 frame law's last word; X01 stores 0 through it at 0x837e0 .. 0x837e4). *)
Section h.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

Record hq_hcx := HQCx {
h_ly : alayout; h_S : astate; h_W : world segs; h_regs : bvmap 5 word; h_mem : word -> option byte; h_md : Model;
h_p : Z; h_n : Z; h_pl : list byte }.

(* What every harness-level segment may use of the entry: HPgCSpec.hd_lib_pre_x without the parts only the final
   leaf reads (asink_none, the fd and fs facts, ameta_inv, the meter) and without its float clause, which X01,
   running at the float state M04b returns at, must not mention. *)
Definition hq_base (hx : hq_hcx) : Prop :=
afn_pre segs B LLVMF_STK (h_ly hx) (h_S hx) (h_W hx) (h_regs hx) (h_mem hx) (h_md hx) [] /\
raZ (h_regs hx) = RA_LLVMF /\
getr (h_regs hx) 10 = w64 (h_p hx) /\ getr (h_regs hx) 11 = w64 (h_n hx) /\
((h_n hx = 0 /\ h_p hx = A_EMPTY) \/ (0 < h_n hx < 2 ^ 26 /\ In (h_p hx, h_n hx) (ablocks B (h_ly hx) (h_S hx)))) /\
h_n hx = Z.of_nat (length (h_pl hx)) /\
garr8 segs (mrestrict (w_H (h_W hx)) (h_mem hx)) (h_p hx) (hd_zbytes (h_pl hx)) /\
frames (h_S hx) = [] /\ st_nev (h_S hx) + EV_LIB <= EV_MAX /\ blocks_bytes (h_S hx) + LIVE_LIB <= LIVE_MAX /\
arodata_okP segs RLO RHI B (aview segs (w_H (h_W hx)) (h_mem hx)).

Definition hq_j (hx : hq_hcx) (own : list (Z * Z)) (ly' : alayout) (S' : astate) (W' : world segs)
(mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal segs B LLVMF_STK (spZ (h_regs hx)) [] (h_ly hx) (h_S hx) (h_W hx) (h_mem hx) (h_md hx) own
  ly' S' W' mem' md' k.

(* The geometry: S the entry sp, R the 32-aligned base of the real frame, F the class-4 frame at position pos
   (frame_addr reads only ly_F, which every journal's layout_le keeps, so one value serves every cut). *)
Definition hq_geo (hx : hq_hcx) (pos : Z) (e : hd_env) : Prop :=
e_S e = spZ (h_regs hx) /\ e_R e = 32 * ((e_S e - HQ_RSZ) / 32) /\ e_F e = frame_addr (h_ly hx) HQ_CID pos.

Definition hq_saved_regs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition hq_saves_L (regs0 : bvmap 5 word) : list (hd_loc * Z) :=
  map (fun j => (LCell XS (- 8 - 8 * Z.of_nat j), bv_unsigned (getr regs0 (nth j hq_saved_regs 0%bv)))) (seq 0 13).
Definition hq_cells (regs0 : bvmap 5 word) (fl : Z) : list (hd_loc * Z) :=
  hq_saves_L regs0 ++ [(LCell (XF 0) HQ_FLAG, fl)].
(* the three float saves: the epilogue reads them back, and no clause of the harness's post names a float
   register, so only their presence is carried *)
Definition hq_fsaves (e : hd_env) (W' : world segs) (mem' : word -> option byte) (regs' : bvmap 5 word) : Prop :=
  exists v0 v1 v2,
  hd_at segs (w_H W') mem' regs' e (LCell XS (- 0x70)) v0 /\
  hd_at segs (w_H W') mem' regs' e (LCell XS (- 0x78)) v1 /\
  hd_at segs (w_H W') mem' regs' e (LCell XS (- 0x80)) v2.
Definition hq_kept (hx : hq_hcx) (pos : Z) (e : hd_env) (W' : world segs) (mem' : word -> option byte)
(regs' : bvmap 5 word) : Prop :=
  Forall (fun f => hd_at segs (w_H W') mem' regs' e (fst f) (snd f))
    (hq_cells (h_regs hx) (flag_addr (h_ly hx) HQ_CID pos)) /\
  hq_fsaves e W' mem' regs'.

(* One shape for every harness-level cut: the journal with its event count, the blocks made since the entry and
   still live, sp / gp / tp, the geometry, the image's values at that pc, the frame's shadow, and the carried
   cells. *)
Definition hq_at_cut (hx : hq_hcx) (pos : Z) (e : hd_env) (k : Z) (bls : list (Z * Z))
(L : list (hd_loc * hd_x)) (sh : list Z)
(ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
: Prop :=
hq_j hx [(HQ_CID, pos)] ly S W mem md k /\
Permutation (ablocks B ly S) (ablocks B (h_ly hx) (h_S hx) ++ bls) /\
Forall (fun b => ~ In b (ablocks B (h_ly hx) (h_S hx)) /\ fst b <> 0) bls /\
getr regs 2 = w64 (e_R e) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
hq_geo hx pos e /\
hd_cut segs (w_H W) mem regs e L /\
hd_fsh segs (w_H W) mem (e_F e) sh /\
hq_kept hx pos e W mem regs.

(* the blocks live at C5 .. C6 (pp, pod, out) and at C7 .. C9 (and first) *)
Definition hq_blocks5 (e : hd_env) : list (Z * Z) :=
  [(e_pp e, Layout.PP_SIZE); (e_pod e, e_len e); (e_out e, 3 * (e_cap e + 1))].
Definition hq_blocks7 (e : hd_env) : list (Z * Z) := hq_blocks5 e ++ [(e_first e, hd_xv e XRc3NZ)].

(* The record's data every cut of this half carries: the record r the pp block holds, the pod block's copy of
   its buffer, the bounds the allocator calls were made under, and the answer the parse gave. *)
Definition hq_rec (e : hd_env) (r : Model.pod_rec) (W : world segs) (mem : word -> option byte) : Prop :=
Model.pod_rec_wf r /\ e_len e = Z.of_nat (length (Model.buf r)) /\ 8 <= e_len e <= 5440 /\
garr8 segs (mrestrict (w_H W) mem) (e_pp e) (hd_zbytes (Layout.pp_bytes r)) /\
garr8 segs (mrestrict (w_H W) mem) (e_pod e) (hd_zbytes (Model.buf r)) /\
e_pod e mod 16 = 0 /\ shadow_hull_vis (aview segs (w_H W) mem) (e_pod e) (e_len e) /\
amem_range (e_pod e) (e_len e + 8) /\
0 <= e_cap e <= 9 /\ 0 <= e_null e <= 1 /\
e_rc e = ans_rc (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e)).

(* ---------------- C5 0x82e98: what the malloc(out) step delivers and M03 starts from ---------------- *)
Definition hq_cut_C5 (hx : hq_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec) (ev : Z)
ly S W regs mem md : Prop :=
hq_at_cut hx pos e 3 (hq_blocks5 e) (hi_L5 headamp_himg_A) (hi_shA headamp_himg_A) ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
hq_rec e r W mem /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_pod e) (e_len e) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_out e) (3 * (e_cap e + 1)) /\
rd32 (aview segs (w_H W) mem) (as_errno B) ev.

(* ---------------- C6 0x83740: what headamp_check_contract delivers ---------------- *)
Definition hq_cut_C6 (hx : hq_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
ly S W regs mem md : Prop :=
hq_at_cut hx pos e 3 (hq_blocks5 e) (hi_L6 headamp_himg_A) (hi_shB headamp_himg_A) ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
hq_rec e r W mem /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_pod e) (e_len e) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_out e) (3 * (e_cap e + 1)) /\
garr8 segs (mrestrict (w_H W) mem) (e_out e)
  (hd_zbytes (ha_cells_bytes (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))) /\
(exists ev, rd32 (aview segs (w_H W) mem) (as_errno B) ev).

(* ---------------- C7 0x83744: what M04a (headamp_first_contract) starts from ---------------- *)
Definition hq_cut_C7 (hx : hq_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
ly S W regs mem md : Prop :=
hq_at_cut hx pos e 4 (hq_blocks7 e) (hi_L7 headamp_himg_A) (hi_shB headamp_himg_A) ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
hq_rec e r W mem /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_pod e) (e_len e) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_out e) (3 * (e_cap e + 1)) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_first e) (hd_xv e XRc3NZ) /\
garr8 segs (mrestrict (w_H W) mem) (e_out e)
  (hd_zbytes (ha_cells_bytes (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))) /\
(exists ev, rd32 (aview segs (w_H W) mem) (as_errno B) ev).

(* ---------------- the allocator step C6 -> C7: the `jal` of malloc(first) ----------------
   C6's values do not read XFirst, so the env gains the returned block only at C7 (hq_env_first). *)
Definition hq_env_first (e : hd_env) (first : Z) : hd_env :=
  HDEnv (e_S e) (e_R e) (e_F e) (e_pp e) (e_pod e) (e_out e) first (e_len e) (e_cap e) (e_null e) (e_rc e)
        (e_src e) (e_left e).
Lemma hq_env_first_xv : forall e first x, x <> XFirst -> hd_xv (hq_env_first e first) x = hd_xv e x.
Proof. intros e first x H. destruct x; cbn; try reflexivity. exfalso; exact (H eq_refl). Qed.

Definition hq_at_C7 (hx : hq_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
(ly6 : alayout) (S6 : astate) (W6 : world segs) (regs6 : bvmap 5 word) (mem6 : word -> option byte)
: world segs -> config -> Prop :=
fun W7 c7 => exists first ly7 S7 regs7 mem7 md7,
c7 = @cfg_at fx2 segs HQ_C7 regs7 mem7 md7 /\
4096 <= first /\ getr regs7 10 = w64 first /\
(forall rr, acallee_saved rr -> getr regs7 (Z_to_bv 5 rr) = getr regs6 (Z_to_bv 5 rr)) /\
frames S7 = frames S6 /\
ablocks B ly7 S7 = ablocks B ly6 S6 ++ [(first, hd_xv e XRc3NZ)] /\
acall_kept segs B ly6 S6 W6 mem6 W7 mem7 (e_R e - ASTACK) (e_R e)
  (fun a => first <= a < first + req_size (hd_xv e XRc3NZ)) /\
hq_cut_C7 hx fx2 pos (hq_env_first e first) r ly7 S7 W7 regs7 mem7 md7.

(* ---------------- C8 0x83764: the copy split, what M04b starts from ---------------- *)
Definition hq_cut_C8 (hx : hq_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
ly S W regs mem md : Prop :=
hq_at_cut hx pos e 4 (hq_blocks7 e) (hi_L8 headamp_himg_A) (hi_shB headamp_himg_A) ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
hq_rec e r W mem /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_pod e) (e_len e) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_out e) (3 * (e_cap e + 1)) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_first e) (hd_xv e XRc3NZ) /\
garr8 segs (mrestrict (w_H W) mem) (e_first e)
  (hd_zbytes (ha_cells_bytes (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))) /\
(exists ev, rd32 (aview segs (w_H W) mem) (as_errno B) ev).

(* ---------------- C9 0x83794: what M04b delivers and X01 starts from ---------------- *)
Definition hq_cut_C9 (hx : hq_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env)
ly S W regs mem md : Prop :=
hq_at_cut hx pos e 4 (hq_blocks7 e) (hi_L9 headamp_himg_A) (hi_shB headamp_himg_A) ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
0 <= e_cap e <= 9 /\ 8 <= e_len e <= 5440.

(* ---------------- J 0x837c4: the frame's retirement join ----------------
   The four blocks are freed (LIFO: first, out, pod, pp at 0x83798 .. 0x837b0) and res's two granules are back
   at 0xf8 (0x837b8 .. 0x837bc), so the frame's shadow is the prologue's again and the blocks are the entry's.
   s6 and s10 both hold F (s6 is read back from R+0x20 at 0x837c0). The event count is a parameter: the walk of
   E01 reaches this join on the `j` 0x80df8 of the early return with no event at all, which the harness's
   premise n < 2 ^ 26 makes dead. *)
Definition hq_cut_J (hx : hq_hcx) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (k : Z)
ly S W regs mem md : Prop :=
hq_j hx [(HQ_CID, pos)] ly S W mem md k /\ 0 <= k <= HQ_EV /\
Permutation (ablocks B ly S) (ablocks B (h_ly hx) (h_S hx)) /\
getr regs 2 = w64 (e_R e) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
hq_geo hx pos e /\
YK0o.frm_zero (@fp_csr fx2) /\
hd_cut segs (w_H W) mem regs e
  [(LReg 8, XS); (LReg 19, XShF); (LReg 22, XF 0); (LReg 26, XF 0)] /\
hd_fsh segs (w_H W) mem (e_F e) (hi_shA headamp_himg_A) /\
hq_kept hx pos e W mem regs.

(* ---------------- the return: HPgCSpec.hd_lib_post_x's own clauses ---------------- *)
Definition hq_ret (hx : hq_hcx) : world segs -> config -> Prop :=
fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = @cfg_at fx' segs RA_LLVMF regs' mem' md' /\
YK0o.frm_zero (@fp_csr fx') /\
hq_j hx [] ly' S' W' mem' md' k /\ k <= HQ_EV /\
aregs_preserved (h_regs hx) regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B (h_ly hx) (h_S hx)).

(* ---------------- the three statements of this half's harness-level pieces ---------------- *)
(* the allocator step C6 -> C7 (an M24 step: an allocator request between segments): a0 = 3 max(rc, 0) + (3 max(rc, 0) == 0) from 0x83724 .. 0x8373c *)
Definition hq_S_C67_stmt : Prop :=
forall (hx : hq_hcx) (fx2 : YK11.FPState) pos e r ly6 S6 W6 regs6 mem6 md6,
hq_base hx -> hq_cut_C6 hx fx2 pos e r ly6 S6 W6 regs6 mem6 md6 ->
SRr segs W6 (@cfg_at fx2 segs HQ_C6 regs6 mem6 md6) (hq_at_C7 hx fx2 pos e r ly6 S6 W6 regs6 mem6).
(* X01, part 1: free(first), free(out), free(pod), free(pp) and res out of scope *)
Definition hq_S_X01f_stmt : Prop :=
forall (hx : hq_hcx) (fx2 : YK11.FPState) pos e ly S W regs mem md,
hq_base hx -> hq_cut_C9 hx fx2 pos e ly S W regs mem md ->
SRr segs W (@cfg_at fx2 segs HQ_C9 regs mem md)
  (fun W' c' => exists ly' S' regs' mem' md' k,
   c' = @cfg_at fx2 segs HQ_J regs' mem' md' /\ hq_cut_J hx fx2 pos e k ly' S' W' regs' mem' md').
(* X01, part 2: F[0] := 0x45e0360e, the class-4 release (the shadow fill at 0x837dc and the flag
   byte through F + 0x3f8 at 0x837e0 .. 0x837e4; the s6 = 0 arm with the call at 0x837f4 is dead), a0 := 0 and
   the epilogue *)
Definition hq_S_X01r_stmt : Prop :=
forall (hx : hq_hcx) (fx2 : YK11.FPState) pos e k ly S W regs mem md,
hq_base hx -> hq_cut_J hx fx2 pos e k ly S W regs mem md ->
SRr segs W (@cfg_at fx2 segs HQ_J regs mem md) (hq_ret hx).

End h.

(* =====================================================================================================
   PART 2. M03: the sub-cuts of headamp_check_contract's walk, from C5 0x82e98 to C6 0x83740
   =====================================================================================================
   A cut inside the segment is a predicate over the segment's fixed data (HPgSeg.hs_scx: the harness's journal
   so far, the registers at the segment's first pc, the run's quantities and the frame's position) and the state
   at the cut. It states only POSITIVE facts; what a call leaves alone is not restated (the journal's own
   clauses and each callee's write-set post carry it between cuts), and the segment's start facts, which every
   piece lemma takes, carry the read-only data and the input. *)

(* M03's write set, as headamp_check_contract states it: the image's third range list (the frame objects res and
   x, their shadow granules and the real-frame cells [R, R+0x120)), the out block and the errno cell. *)
Definition hq_E3 (cx : hs_scx segs) : Z -> Prop :=
fun a => hd_inw (x_e segs cx) (hi_w3 headamp_himg_A) a \/
 (e_out (x_e segs cx) <= a < e_out (x_e segs cx) + 3 * (e_cap (x_e segs cx) + 1)) \/
 (as_errno B <= a < as_errno B + 4).

(* the answer the parse gave (the out block and res hold it, and e_rc is its rc) and the answer expect_of
   computes (x holds it from 0x8369c on) *)
Definition hq_ans (cx : hs_scx segs) (r : Model.pod_rec) : answer :=
  Headamp.parse_props (hd_props (e_null (x_e segs cx)) (Model.buf r)) (e_cap (x_e segs cx)).
Definition hq_exp (cx : hs_scx segs) (r : Model.pod_rec) : answer :=
  Headamp.expect_model (e_null (x_e segs cx) =? 1) (e_cap (x_e segs cx)) r.
Definition hq_fin (cx : hs_scx segs) (r : Model.pod_rec) : list cell * Z * Z :=
  (ans_cells (hq_exp cx r), ans_keys (hq_exp cx r), ans_rf (hq_exp cx r)).

(* ---------------- what the pieces of M03 all take: headamp_check_contract's premises ----------------
   The conjuncts are the contract's, in its order (HPgCSpec.v headamp_check_contract), so that the segment's
   proof hands them over as they stand. *)
Definition hq_start_M03 (cx : hs_scx segs) (r : Model.pod_rec) (ev : Z) : Prop :=
hs_pre segs B cx (hi_shA headamp_himg_A) /\
hd_cut segs (w_H (x_W segs cx)) (x_memc segs cx) (x_regs segs cx) (x_e segs cx) (hi_L5 headamp_himg_A) /\
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
e_rc (x_e segs cx) = ans_rc (hq_ans cx r) /\
rd32 (aview segs (w_H (x_W segs cx)) (x_memc segs cx)) (as_errno B) ev /\
YK0o.frm_zero (@fp_csr fx).

(* ---------------- what every cut inside M03 carries ----------------
   The segment's journal-and-frame part with M03's write set, the float registers M03 may have changed, the
   frame's shadow pattern at that cut, the read-only image (the soft-float callees of the value piece need it),
   the pp block and the pod block unchanged (both lie outside the write set), the out block holding the parse's
   cells, res holding the parse's result struct, and the errno cell readable. *)
Definition hq_base3 (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (sh : list Z)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_core segs B MT cx (hq_E3 cx) ly2 S2 W2 regs2 mem2 md2 /\
hq_fxk fx2 /\
hs_fsh_at segs cx W2 mem2 sh /\
rom_view segs W2 mem2 /\
hs_pp_at segs cx W2 mem2 (Layout.pp_bytes r) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_pod (x_e segs cx)) (hd_zbytes (Model.buf r)) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_out (x_e segs cx))
  (hd_zbytes (ha_cells_bytes (ans_cells (hq_ans cx r)))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e segs cx) + HQ_RES) (hd_zbytes (ans_res_bytes (hq_ans cx r))) /\
(exists ev, rd32 (aview segs (w_H W2) mem2) (as_errno B) ev).

(* the registers fixed from the prologue to the epilogue, and the five M03 keeps *)
Definition hq_L_frame (cx : hs_scx segs) : list (hd_loc * Z) :=
  [(LReg 8, e_S (x_e segs cx)); (LReg 9, e_R (x_e segs cx)); (LReg 19, shadow_addr (e_F (x_e segs cx)));
   (LReg 23, SHADOW_OFF)].
Definition hq_L_seg (cx : hs_scx segs) : list (hd_loc * Z) :=
  hq_L_frame cx ++
  [(LReg 22, e_cap (x_e segs cx)); (LReg 24, e_out (x_e segs cx)); (LReg 25, e_pod (x_e segs cx));
   (LReg 26, e_F (x_e segs cx) + HQ_RES); (LReg 27, e_rc (x_e segs cx))].
(* the real-frame cells the pair loop and its body read, written once by 0x82ea8 .. 0x83078 *)
Definition hq_L_loopc (cx : hs_scx segs) : list (hd_loc * Z) :=
  [(LCell XR 0x20, e_F (x_e segs cx)); (LCell XR 0x60, e_F (x_e segs cx));
   (LCell XR 0xa8, HQ_MHALF_HI); (LCell XR 0xb0, HQ_HALF_HI);
   (LCell XR 0xb8, e_F (x_e segs cx) + HQ_XO + HQ_X_CELL0); (LCell XR 0xc0, HQ_RC_BIG);
   (LCell XR 0xe8, e_pp (x_e segs cx) + HQ_ENT_SZ); (LCell XR 0xf0, e_pp (x_e segs cx));
   (LCell XR 0xf8, e_pp (x_e segs cx) + HQ_ENT_BODY); (LCell XR 0x100, e_pp (x_e segs cx) + HQ_ENT_BODY);
   (LCell XR 0x108, e_F (x_e segs cx) + HQ_XO);
   (LCell XR 0x110, hd_xv (x_e segs cx) XProps); (LCell XR 0x118, 3 * e_cap (x_e segs cx) + 3)].
(* the five registers the scan's turn holds besides the loop's: the entry table's five operand registers, which
   advance by 104 a turn, and the fixed 104 * at0 in a3 *)
Definition hq_L_scan (cx : hs_scx segs) (at0 m : nat) : list (hd_loc * Z) :=
  let pp := e_pp (x_e segs cx) in
  let d := 104 * (Z.of_nat m - Z.of_nat at0) in
  [(LReg 13, 104 * Z.of_nat at0);
   (LReg 11, pp + HQ_ENT_SZ + d); (LReg 12, pp + HQ_ENT_BODY + d); (LReg 16, pp + HQ_ENT_BODY + d);
   (LReg 14, pp + HQ_ENT0 + d); (LReg 15, pp + HQ_ENT0 + d);
   (LReg 20, Z.of_nat m); (LReg 21, Z.of_nat m + 1)].
(* the registers the loop's head, its scan and its latch hold: the entry table (in ra and t6), the String type
   and -1. a7 = 104 is live at the head and the latch only: the scan's turn writes it (0x830a0). *)
Definition hq_L_loopr (cx : hs_scx segs) : list (hd_loc * Z) :=
  [(LReg 1, e_pp (x_e segs cx) + HQ_ENT0); (LReg 31, e_pp (x_e segs cx) + HQ_ENT0);
   (LReg 29, 8); (LReg 30, -1)].

(* the record's three tests the loop runs under, and its entry count *)
Definition hq_live (cx : hs_scx segs) (r : Model.pod_rec) : Prop :=
  e_null (x_e segs cx) = 0 /\ Model.corrupt r = false /\
  Model.is_props r = true /\ Model.params_struct r = true.
Definition hq_nent (r : Model.pod_rec) : Z := Z.of_nat (length (Model.ents r)).

(* the pair loop's invariant: folding the pairs that start at index j over what x holds gives the answer
   expect_of ends with (Pod/Headamp.v ha_fold, Pod/Accessors.v pairs_by) *)
Definition hq_fold_inv (cx : hs_scx segs) (r : Model.pod_rec) (j : nat) (cs : list cell) (keys rf : Z) : Prop :=
  Headamp.ha_fold Headamp.expect_cell (e_cap (x_e segs cx))
    (Accessors.pairs_by Accessors.key_of (skipn j (Model.ents r)) None) cs keys rf = hq_fin cx r.
(* the same, with the pair the body is working on in front of the list *)
Definition hq_pair_inv (cx : hs_scx segs) (r : Model.pod_rec) (m : nat) (k : list byte) (v : Model.ent)
(cs : list cell) (keys rf : Z) : Prop :=
  v = nth (S m) (Model.ents r) (Model.Ent 0 0 []) /\
  Headamp.ha_prefix k = true /\
  (S m < length (Model.ents r))%nat /\
  Headamp.ha_fold Headamp.expect_cell (e_cap (x_e segs cx))
    ((k, v) :: Accessors.pairs_by Accessors.key_of (skipn (S (S m)) (Model.ents r)) None) cs keys rf = hq_fin cx r.

(* what x holds at a cut of the loop, and the two bounds the fold keeps *)
Definition hq_x_at (cx : hs_scx segs) (W2 : world segs) (mem2 : word -> option byte)
(cs : list cell) (keys rf : Z) : Prop :=
  garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e segs cx) + HQ_XO) (hd_zbytes (hq_x_open cs keys rf)) /\
  (length cs <= X_CELLS)%nat /\ Z.of_nat (length cs) <= e_cap (x_e segs cx) /\
  Z.of_nat (length cs) <= keys /\ 0 <= keys < 2 ^ 31 - 1 /\
  (rf = Headamp.REFUSE_NONE \/ rf = Headamp.REFUSE_BAD_KEY \/ rf = Headamp.REFUSE_OUT_OF_RANGE).

(* ---------------- X 0x82f30: pp->corrupt is 0, the frame object x is about to come into scope ----------------
   s5 = &pp->len, s8 = out, s9 = pod, s10 = res, s11 = rc; the cells the header left. *)
Definition hq_cut_X (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hq_base3 cx fx2 r (hi_shB headamp_himg_A) ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
  (hq_L_seg cx ++
   [(LReg 21, e_pp (x_e segs cx) + 0x4000);
    (LCell XR 0x20, e_F (x_e segs cx)); (LCell XR 0x40, e_null (x_e segs cx)); (LCell XR 0x60, e_F (x_e segs cx));
    (LCell XR 0x90, Z.shiftr (e_pp (x_e segs cx) + Layout.OFF_N_ENT) 3);
    (LCell XR 0xa0, e_pp (x_e segs cx) + Layout.OFF_N_ENT); (LCell XR 0xf0, e_pp (x_e segs cx));
    (LCell XR 0x110, hd_xv (x_e segs cx) XProps); (LCell XR 0x118, 3 * e_cap (x_e segs cx) + 3)]) /\
Model.corrupt r = false.

(* ---------------- PAIR 0x8307c: the pair loop's head at index i (fuzz_headamp.c:119) ----------------
   s5 = at, the scan's entry index; x holds what the fold has written. i < |ents r|: the head 0x8307c .. 0x8309c
   enters the scan at m = i with no test, and the scan reads entry m. *)
Definition hq_cut_PAIR (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (i : nat)
(cs : list cell) (keys rf : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hq_base3 cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
  (hq_L_seg cx ++ hq_L_loopc cx ++ hq_L_loopr cx ++
   [(LReg 17, 104); (LReg 21, Z.of_nat i); (LReg 7, hq_nent r); (LReg 28, hq_nent r - 1)]) /\
hq_fs fx2 9 HQ_F32_M1 /\ hq_fs fx2 18 HQ_F32_256 /\
hq_live cx r /\ 0 < hq_nent r /\
(i < length (Model.ents r))%nat /\
hq_x_at cx W2 mem2 cs keys rf /\ hq_fold_inv cx r i cs keys rf.

(* ---------------- SCAN 0x830a0: pod_next_pair's scan head, from at0, reading entry m (pod.h:134) ---------- *)
Definition hq_cut_SCAN (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(cs : list cell) (keys rf : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hq_base3 cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
  (hq_L_seg cx ++ hq_L_loopc cx ++ hq_L_loopr cx ++ hq_L_scan cx at0 m ++
   [(LReg 7, hq_nent r); (LReg 28, hq_nent r - 1)]) /\
hq_fs fx2 9 HQ_F32_M1 /\ hq_fs fx2 18 HQ_F32_256 /\
hq_live cx r /\
(at0 <= m < length (Model.ents r))%nat /\
(forall q, (at0 <= q < m)%nat -> Accessors.key_of (nth q (Model.ents r) (Model.Ent 0 0 [])) = None) /\
hq_x_at cx W2 mem2 cs keys rf /\ hq_fold_inv cx r at0 cs keys rf.

(* ---------------- KEY 0x83168: entry m is a key and entry m + 1 is its value ----------------
   s2 = the key's body address, s4 = m + 1 (pod_next_pair's answer), s5 = m + 2 (the next at). The strncmp
   wrapper is called at 0x83190 with this address, the harness's own literal and 13. *)
Definition hq_cut_KEY (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(k : list byte) (cs : list cell) (keys rf : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hq_base3 cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
  (hq_L_seg cx ++ hq_L_loopc cx ++
   [(LReg 1, e_pp (x_e segs cx) + HQ_ENT0); (LReg 31, e_pp (x_e segs cx) + HQ_ENT0); (LReg 30, -1);
    (LReg 7, hq_nent r); (LReg 28, hq_nent r - 1);
    (LReg 18, e_pp (x_e segs cx) + HQ_ENT_BODY + 104 * Z.of_nat m);
    (LReg 20, Z.of_nat m + 1); (LReg 21, Z.of_nat m + 2)]) /\
hq_fs fx2 9 HQ_F32_M1 /\ hq_fs fx2 18 HQ_F32_256 /\
hq_live cx r /\
(at0 <= m)%nat /\ (S m < length (Model.ents r))%nat /\
(forall q, (at0 <= q < m)%nat -> Accessors.key_of (nth q (Model.ents r) (Model.Ent 0 0 [])) = None) /\
Accessors.key_of (nth m (Model.ents r) (Model.Ent 0 0 [])) = Some k /\
hq_x_at cx W2 mem2 cs keys rf /\ hq_fold_inv cx r at0 cs keys rf.

(* the cells the body of one pair writes and reads besides the loop's: the key's parts, saved around the
   wrapper calls (0x83170 .. 0x8318c), and the channel and the param the key gave *)
Definition hq_L_body (cx : hs_scx segs) (r : Model.pod_rec) : list (hd_loc * Z) :=
  [(LCell XR 0xc8, e_pp (x_e segs cx) + HQ_ENT0); (LCell XR 0xd0, hq_nent r - 1);
   (LCell XR 0xd8, e_pp (x_e segs cx) + HQ_ENT0); (LCell XR 0xe0, hq_nent r)].

(* ---------------- VAL 0x83364: the key is a cell address, cell_value of the pair's value pod ----------------
   x->keys is already one more; a3 = param, s2 = the param's top value, R+0xa0 = the channel, s4 = m + 1 the
   value entry's index, t3 = OUT_OF_RANGE (the refusal the value's tests give). |cs| <= keys is KEY's bound,
   kept apart from x's (keys + 1): the cell write at CELL appends one cell under it. *)
Definition hq_cut_VAL (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(k : list byte) (v : Model.ent) (ch p : Z) (cs : list cell) (keys rf : Z)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hq_base3 cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
  (hq_L_seg cx ++ hq_L_loopc cx ++ hq_L_body cx r ++
   [(LReg 31, e_pp (x_e segs cx) + HQ_ENT0); (LReg 7, hq_nent r);
    (LReg 13, p); (LReg 18, if p =? Headamp.HA_SENS then Headamp.HA_SENS_MAX else 1);
    (LReg 20, Z.of_nat m + 1); (LReg 21, Z.of_nat m + 2); (LReg 28, Headamp.REFUSE_OUT_OF_RANGE);
    (LCell XR 0xa0, ch)]) /\
hq_fs fx2 9 HQ_F32_M1 /\ hq_fs fx2 18 HQ_F32_256 /\
hq_live cx r /\ (at0 <= m)%nat /\
Headamp.expect_key (skipn (length Headamp.HA_PREFIX) k) = Headamp.KCell ch p /\
hq_pair_inv cx r m k v cs keys rf /\
Z.of_nat (length cs) <= keys /\
hq_x_at cx W2 mem2 cs (keys + 1) rf.

(* ---------------- CELL 0x83548: the value is in range, the cap test and the cell write ----------------
   s4 = the value; R+0x98 = the param, R+0xa0 = the channel. *)
Definition hq_cut_CELL (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(k : list byte) (v : Model.ent) (ch p val : Z) (cs : list cell) (keys rf : Z)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hq_base3 cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
  (hq_L_seg cx ++ hq_L_loopc cx ++ hq_L_body cx r ++
   [(LReg 20, val); (LReg 21, Z.of_nat m + 2); (LCell XR 0x98, p); (LCell XR 0xa0, ch)]) /\
hq_fs fx2 9 HQ_F32_M1 /\ hq_fs fx2 18 HQ_F32_256 /\
hq_live cx r /\ (at0 <= m)%nat /\
Headamp.expect_cell k v = inr (ch, p, val) /\
Headamp.cell_valid (ch, p, val) /\
hq_pair_inv cx r m k v cs keys rf /\
Z.of_nat (length cs) <= keys /\
hq_x_at cx W2 mem2 cs (keys + 1) rf.

(* ---------------- RFA 0x83454 and RF 0x83460: the refusal fold (fuzz_headamp.c:144-147) ----------------
   RFA is the entry cell_value's tests take: it reloads t2 and t6 and sets t3 to OUT_OF_RANGE; RF is the fold
   itself, with t3 = the code. *)
Definition hq_cut_RF (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(k : list byte) (v : Model.ent) (bad : Z) (cs : list cell) (keys rf : Z)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hq_base3 cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
  (hq_L_seg cx ++ hq_L_loopc cx ++ hq_L_body cx r ++
   [(LReg 31, e_pp (x_e segs cx) + HQ_ENT0); (LReg 7, hq_nent r);
    (LReg 21, Z.of_nat m + 2); (LReg 28, bad)]) /\
hq_fs fx2 9 HQ_F32_M1 /\ hq_fs fx2 18 HQ_F32_256 /\
hq_live cx r /\ (at0 <= m)%nat /\
Headamp.expect_cell k v = inl bad /\
(bad = Headamp.REFUSE_BAD_KEY \/ bad = Headamp.REFUSE_OUT_OF_RANGE) /\
hq_pair_inv cx r m k v cs keys rf /\
hq_x_at cx W2 mem2 cs (keys + 1) rf.
Definition hq_cut_RFA (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (at0 m : nat)
(k : list byte) (v : Model.ent) (cs : list cell) (keys rf : Z)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hq_base3 cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
  (hq_L_seg cx ++ hq_L_loopc cx ++ hq_L_body cx r ++ [(LReg 21, Z.of_nat m + 2)]) /\
hq_fs fx2 9 HQ_F32_M1 /\ hq_fs fx2 18 HQ_F32_256 /\
hq_live cx r /\ (at0 <= m)%nat /\
Headamp.expect_cell k v = inl Headamp.REFUSE_OUT_OF_RANGE /\
hq_pair_inv cx r m k v cs keys rf /\
hq_x_at cx W2 mem2 cs (keys + 1) rf.

(* ---------------- LATCH 0x83474: the pair loop's latch, with the next index j ----------------
   j <= |ents r|: the latch's test `blt s5,t2` 0x83488 compares the 64-bit j with n_ent, so only this bound makes
   the head it jumps to (PAIR j) have j < |ents r|. *)
Definition hq_cut_LATCH (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec) (j : nat)
(cs : list cell) (keys rf : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hq_base3 cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
  (hq_L_seg cx ++ hq_L_loopc cx ++ hq_L_body cx r ++
   [(LReg 31, e_pp (x_e segs cx) + HQ_ENT0); (LReg 7, hq_nent r); (LReg 21, Z.of_nat j)]) /\
hq_fs fx2 9 HQ_F32_M1 /\ hq_fs fx2 18 HQ_F32_256 /\
hq_live cx r /\ 0 < hq_nent r /\ (j <= length (Model.ents r))%nat /\
hq_x_at cx W2 mem2 cs keys rf /\ hq_fold_inv cx r j cs keys rf.

(* ---------------- RC 0x83694 and RCM 0x8369c: the loop is done ----------------
   At RC the answer's rc is the number of cells written (x->n, loaded into a1 at 0x83698); RCM is the entry the
   two early exits take with a1 = -1. From RCM on x holds expect_of's answer, which the last four checks read.
   RCM has no R+0x108 cell: both early exits (`bnez` 0x82f94, `beqz` 0x82fb0) leave before `sd s2,264(s1)`
   0x82fb4, and from 0x8369c on x is in s2.
   The frame's shadow still has x in scope: the stores at 0x836dc .. 0x83720 close it. *)
Definition hq_cut_RC (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hq_base3 cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
  (hq_L_seg cx ++
   [(LCell XR 0x20, e_F (x_e segs cx)); (LCell XR 0x60, e_F (x_e segs cx)); (LCell XR 0xf0, e_pp (x_e segs cx));
    (LCell XR 0x108, e_F (x_e segs cx) + HQ_XO);
    (LCell XR 0x110, hd_xv (x_e segs cx) XProps); (LCell XR 0x118, 3 * e_cap (x_e segs cx) + 3)]) /\
Model.corrupt r = false /\
ans_rc (hq_exp cx r) = Z.of_nat (length (ans_cells (hq_exp cx r))) /\
hq_x_at cx W2 mem2 (ans_cells (hq_exp cx r)) (ans_keys (hq_exp cx r)) (ans_rf (hq_exp cx r)).
Definition hq_cut_RCM (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hq_base3 cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
  (hq_L_seg cx ++
   [(LReg 11, ans_rc (hq_exp cx r)); (LReg 18, e_F (x_e segs cx) + HQ_XO);
    (LCell XR 0x20, e_F (x_e segs cx)); (LCell XR 0x60, e_F (x_e segs cx)); (LCell XR 0xf0, e_pp (x_e segs cx));
    (LCell XR 0x110, hd_xv (x_e segs cx) XProps); (LCell XR 0x118, 3 * e_cap (x_e segs cx) + 3)]) /\
Model.corrupt r = false /\
hq_x_at cx W2 mem2 (ans_cells (hq_exp cx r)) (ans_keys (hq_exp cx r)) (ans_rf (hq_exp cx r)).

(* ---------------- FIRST 0x83724: the request of the first block (fuzz_headamp.c:350) ----------------
   Both ways into this cut reach it with x out of scope again: the corrupt record goes straight here from
   0x82f2c, and the checked one through the stores at 0x836dc .. 0x83720. *)
Definition hq_cut_FIRST (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hq_base3 cx fx2 r (hi_shB headamp_himg_A) ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx segs cx W2 mem2 regs2
  (hq_L_frame cx ++
   [(LReg 22, e_cap (x_e segs cx)); (LReg 24, e_out (x_e segs cx)); (LReg 25, e_pod (x_e segs cx));
    (LReg 27, e_rc (x_e segs cx));
    (LCell XR 0x20, e_F (x_e segs cx)); (LCell XR 0x60, e_F (x_e segs cx)); (LCell XR 0xf0, e_pp (x_e segs cx));
    (LCell XR 0x110, hd_xv (x_e segs cx) XProps); (LCell XR 0x118, 3 * e_cap (x_e segs cx) + 3)]).

(* ---------------- C6 0x83740: the checking segment is done ----------------
   This cut IS headamp_check_contract's post, at the pc its contract names (hi_c6 headamp_himg_A). *)
Definition hq_cut_C6s (cx : hs_scx segs) (fx2 : YK11.FPState) (r : Model.pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_core segs B MT cx (hq_E3 cx) ly2 S2 W2 regs2 mem2 md2 /\
hq_fxk fx2 /\
hd_cut segs (w_H W2) mem2 regs2 (x_e segs cx) (hi_L6 headamp_himg_A) /\
hs_fsh_at segs cx W2 mem2 (hi_shB headamp_himg_A) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_out (x_e segs cx))
  (hd_zbytes (ha_cells_bytes (ans_cells (hq_ans cx r)))) /\
(exists ev, rd32 (aview segs (w_H W2) mem2) (as_errno B) ev).

(* =====================================================================================================
   THE CONTINUATIONS: "from this cut, the rest of the walk realizes POST"
   =====================================================================================================
   One per cut, with the loop index as an argument and never under the inner quantifier, so that the latch of a
   loop can hand the head its next index and each closure is an induction on the index, not a circular
   hypothesis. POST is generic. Each cut of M03 reaches its pc at the run's own float state. *)
Section f.
Variable cx : hs_scx segs.
Variable r : Model.pod_rec.
Variable POST : world segs -> config -> Prop.

Definition hq_from_X : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2, hq_cut_X cx fx2 r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQ_X regs2 mem2 md2) POST.
Definition hq_from_PAIR (i : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf,
hq_cut_PAIR cx fx2 r i cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQ_PAIR regs2 mem2 md2) POST.
Definition hq_from_SCAN (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf,
hq_cut_SCAN cx fx2 r at0 m cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQ_SCAN regs2 mem2 md2) POST.
Definition hq_from_KEY (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf,
hq_cut_KEY cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQ_KEY regs2 mem2 md2) POST.
Definition hq_from_VAL (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k v ch p cs keys rf,
hq_cut_VAL cx fx2 r at0 m k v ch p cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQ_VAL regs2 mem2 md2) POST.
Definition hq_from_CELL (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k v ch p val cs keys rf,
hq_cut_CELL cx fx2 r at0 m k v ch p val cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQ_CELL regs2 mem2 md2) POST.
Definition hq_from_RF (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k v bad cs keys rf,
hq_cut_RF cx fx2 r at0 m k v bad cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQ_RF regs2 mem2 md2) POST.
Definition hq_from_RFA (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 k v cs keys rf,
hq_cut_RFA cx fx2 r at0 m k v cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQ_RFA regs2 mem2 md2) POST.
Definition hq_from_LATCH (j : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf,
hq_cut_LATCH cx fx2 r j cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQ_LATCH regs2 mem2 md2) POST.
Definition hq_from_RC : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2, hq_cut_RC cx fx2 r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQ_RC regs2 mem2 md2) POST.
Definition hq_from_RCM : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2, hq_cut_RCM cx fx2 r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQ_RCM regs2 mem2 md2) POST.
Definition hq_from_FIRST : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2, hq_cut_FIRST cx fx2 r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQ_FIRST regs2 mem2 md2) POST.
Definition hq_from_C6 : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2, hq_cut_C6s cx fx2 r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQ_C6 regs2 mem2 md2) POST.
End f.

(* =====================================================================================================
   THE PIECE STATEMENTS, one per walk lane of M03
   ===================================================================================================== *)
(* M3a, the head (C5 -> 0x82f30 / 0x83724): the NULL test (dead), memset(out, 0xa5), res into scope and
   memset(res, 0x5a, 12), the parse, check_no_overrun, check_count, check_cells_valid and the corrupt test. *)
Definition hq_piece_M3a_head_stmt : Prop :=
forall cx POST r ev,
hq_start_M03 cx r ev -> hq_from_X cx r POST -> hq_from_FIRST cx r POST ->
SRr segs (x_W segs cx) (cfg_at segs (hi_c5 headamp_himg_A) (x_regs segs cx) (x_memc segs cx) (x_mdc segs cx)) POST.
(* M3a, the setup (0x82f30 -> 0x8307c / 0x83694 / 0x8369c): x into scope, memset(x, 0, 0x88), the null flag,
   is_props, params_struct and n_ent, then the loop's constants. *)
Definition hq_piece_M3a_setup_stmt : Prop :=
forall cx POST r ev,
hq_start_M03 cx r ev -> hq_from_PAIR cx r POST 0 -> hq_from_RC cx r POST -> hq_from_RCM cx r POST ->
hq_from_X cx r POST.
(* M3b, the pair loop's head (0x8307c -> 0x830a0): the scan's five operand registers. *)
Definition hq_piece_M3b_pair_stmt : Prop :=
forall cx POST r ev i,
hq_start_M03 cx r ev -> hq_from_SCAN cx r POST i i -> hq_from_PAIR cx r POST i.
(* M3b, one turn of the scan (0x830a0 -> 0x830a0 / 0x83168 / 0x83694): the entry's type, size and last body
   byte (pod.h:92), each read through an instrumented check. *)
Definition hq_piece_M3b_scan_stmt : Prop :=
forall cx POST r ev at0 m,
hq_start_M03 cx r ev -> hq_from_SCAN cx r POST at0 (S m) -> hq_from_KEY cx r POST at0 m ->
hq_from_RC cx r POST ->
hq_from_SCAN cx r POST at0 m.
(* M3b, the latch (0x83474 -> 0x8307c / 0x83694). *)
Definition hq_piece_M3b_latch_stmt : Prop :=
forall cx POST r ev j,
hq_start_M03 cx r ev -> hq_from_PAIR cx r POST j -> hq_from_RC cx r POST ->
hq_from_LATCH cx r POST j.
(* M3b, the refusal fold (0x83454 / 0x83460 -> 0x83474). *)
Definition hq_piece_M3b_refuse_stmt : Prop :=
forall cx POST r ev at0 m,
hq_start_M03 cx r ev -> hq_from_LATCH cx r POST (S (S m)) ->
hq_from_RF cx r POST at0 m /\ hq_from_RFA cx r POST at0 m.
(* M3c, the key and the channel (0x83168 -> 0x83364 / 0x83460 / 0x83474 / 0x83694): the strncmp wrapper,
   x->keys++, read_channel's two loops, the '.' test and the strcmp chain. *)
Definition hq_piece_M3c_key_stmt : Prop :=
forall cx POST r ev at0 m,
hq_start_M03 cx r ev -> hq_from_VAL cx r POST at0 m -> hq_from_RF cx r POST at0 m ->
hq_from_LATCH cx r POST (S (S m)) -> hq_from_RC cx r POST ->
hq_from_KEY cx r POST at0 m.
(* M3d, the value (0x83364 -> 0x83454 / 0x83460 / 0x83548): pod_bool, pod_int, pod_float and the inlined
   pod_nearest with its five soft-float calls. *)
Definition hq_piece_M3d_value_stmt : Prop :=
forall cx POST r ev at0 m,
hq_start_M03 cx r ev -> hq_from_CELL cx r POST at0 m -> hq_from_RF cx r POST at0 m ->
hq_from_RFA cx r POST at0 m ->
hq_from_VAL cx r POST at0 m.
(* M3e, the cell write (0x83548 -> 0x83474 / 0x83694): the cap break and the three instrumented stores. *)
Definition hq_piece_M3e_cell_stmt : Prop :=
forall cx POST r ev at0 m,
hq_start_M03 cx r ev -> hq_from_LATCH cx r POST (S (S m)) -> hq_from_RC cx r POST ->
hq_from_CELL cx r POST at0 m.
(* M3e, x->rc and the last four checks (0x83694 / 0x8369c -> 0x83724), then x out of scope. *)
Definition hq_piece_M3e_rc_stmt : Prop :=
forall cx POST r ev,
hq_start_M03 cx r ev -> hq_from_FIRST cx r POST ->
hq_from_RC cx r POST /\ hq_from_RCM cx r POST.
(* M24, the first block's request (0x83724 -> C6). *)
Definition hq_piece_M24_first_stmt : Prop :=
forall cx POST r ev,
hq_start_M03 cx r ev -> hq_from_C6 cx r POST -> hq_from_FIRST cx r POST.

(* =====================================================================================================
   THE SEAM: headamp_check_contract from the pieces
   =====================================================================================================
   The two loops close by induction on the loop index: the pair loop on 33 - i (a head state has
   i < |ents r| <= 32) and the scan on 32 - m (a scan state has m < |ents r| <= 32); a key found at m hands the
   latch the index m + 2, so the outer induction hypothesis serves it. Nothing here walks an instruction. *)
(* A cut is taken apart by its own pattern, never by a `repeat ... destruct` over the context: a Section
   hypothesis cannot be cleared, so such a tactic does not end on one. *)
Lemma hq_cut_PAIR_bound : forall cx fx2 r i cs keys rf ly2 S2 W2 regs2 mem2 md2,
Model.pod_rec_wf r ->
hq_cut_PAIR cx fx2 r i cs keys rf ly2 S2 W2 regs2 mem2 md2 -> (i <= 32)%nat.
Proof.
intros cx fx2 r i cs keys rf ly2 S2 W2 regs2 mem2 md2 Hw HP.
destruct HP as (_ & _ & _ & _ & _ & _ & Hi & _ & _).
destruct (Model.ents_wf r Hw) as [Hle _]. lia.
Qed.

Lemma hq_cut_SCAN_bound : forall cx fx2 r at0 m cs keys rf ly2 S2 W2 regs2 mem2 md2,
Model.pod_rec_wf r ->
hq_cut_SCAN cx fx2 r at0 m cs keys rf ly2 S2 W2 regs2 mem2 md2 -> (m < 32)%nat /\ (at0 <= m)%nat.
Proof.
intros cx fx2 r at0 m cs keys rf ly2 S2 W2 regs2 mem2 md2 Hw HSC.
destruct HSC as (_ & _ & _ & _ & _ & Hm & _ & _ & _).
destruct (Model.ents_wf r Hw) as [Hle _]. split; lia.
Qed.

Section m03.
Variable cx : hs_scx segs.
Variable r : Model.pod_rec.
Variable POST : world segs -> config -> Prop.
Variable ev : Z.
Hypothesis HS : hq_start_M03 cx r ev.
(* M3b *)
Hypothesis PM3b_pair : hq_piece_M3b_pair_stmt.
Hypothesis PM3b_scan : hq_piece_M3b_scan_stmt.
Hypothesis PM3b_latch : hq_piece_M3b_latch_stmt.
Hypothesis PM3b_refuse : hq_piece_M3b_refuse_stmt.
(* M3c, M3d, M3e *)
Hypothesis PM3c_key : hq_piece_M3c_key_stmt.
Hypothesis PM3d_value : hq_piece_M3d_value_stmt.
Hypothesis PM3e_cell : hq_piece_M3e_cell_stmt.
(* the two cuts the loop may leave to *)
Hypothesis HRC : hq_from_RC cx r POST.

Lemma hq_wf : Model.pod_rec_wf r.
Proof. pose proof HS as H0. destruct H0 as (_ & _ & H & _). exact H. Qed.

(* one turn of the pair loop's body, given the latch of the next turn *)
Lemma hq_body_closed : forall at0 m,
hq_from_LATCH cx r POST (S (S m)) -> hq_from_KEY cx r POST at0 m.
Proof.
intros at0 m HL.
destruct (PM3b_refuse cx POST r ev at0 m HS HL) as [HRF HRFA].
assert (HCELL : hq_from_CELL cx r POST at0 m) by exact (PM3e_cell cx POST r ev at0 m HS HL HRC).
assert (HVAL : hq_from_VAL cx r POST at0 m)
  by exact (PM3d_value cx POST r ev at0 m HS HCELL HRF HRFA).
exact (PM3c_key cx POST r ev at0 m HS HVAL HRF HL HRC).
Qed.

(* the scan, closed: from its head at any m, given the pair loop's heads above at0 *)
Lemma hq_scan_closed : forall at0,
(forall j, (at0 < j)%nat -> hq_from_PAIR cx r POST j) -> forall m, hq_from_SCAN cx r POST at0 m.
Proof.
intros at0 HP.
assert (H : forall f m, (32 - m <= f)%nat -> hq_from_SCAN cx r POST at0 m).
{ induction f as [|f IH]; intros m Hm.
  - intros fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf HSC. exfalso.
    destruct (hq_cut_SCAN_bound cx fx2 r at0 m cs keys rf ly2 S2 W2 regs2 mem2 md2 hq_wf HSC). lia.
  - destruct (Nat.lt_ge_cases m at0) as [Hlt|Hge].
    + intros fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf HSC. exfalso.
      destruct (hq_cut_SCAN_bound cx fx2 r at0 m cs keys rf ly2 S2 W2 regs2 mem2 md2 hq_wf HSC). lia.
    + assert (HL : hq_from_LATCH cx r POST (S (S m)))
        by exact (PM3b_latch cx POST r ev (S (S m)) HS (HP (S (S m)) ltac:(lia)) HRC).
      exact (PM3b_scan cx POST r ev at0 m HS (IH (S m) ltac:(lia)) (hq_body_closed at0 m HL) HRC). }
intros m. exact (H (32 - m)%nat m (le_n _)).
Qed.

(* the pair loop, closed: from its head at any i *)
Lemma hq_pairs_closed : forall i, hq_from_PAIR cx r POST i.
Proof.
assert (H : forall f i, (33 - i <= f)%nat -> hq_from_PAIR cx r POST i).
{ induction f as [|f IH]; intros i Hi.
  - intros fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf HP. exfalso.
    pose proof (hq_cut_PAIR_bound cx fx2 r i cs keys rf ly2 S2 W2 regs2 mem2 md2 hq_wf HP). lia.
  - apply (PM3b_pair cx POST r ev i HS).
    apply (hq_scan_closed i). intros j Hj. apply IH. lia. }
intros i. exact (H (33 - i)%nat i (le_n _)).
Qed.
End m03.

(* the contract itself, from the eleven piece statements *)
Section seam.
Hypothesis PM3a_head : hq_piece_M3a_head_stmt.
Hypothesis PM3a_setup : hq_piece_M3a_setup_stmt.
Hypothesis PM3b_pair : hq_piece_M3b_pair_stmt.
Hypothesis PM3b_scan : hq_piece_M3b_scan_stmt.
Hypothesis PM3b_latch : hq_piece_M3b_latch_stmt.
Hypothesis PM3b_refuse : hq_piece_M3b_refuse_stmt.
Hypothesis PM3c_key : hq_piece_M3c_key_stmt.
Hypothesis PM3d_value : hq_piece_M3d_value_stmt.
Hypothesis PM3e_cell : hq_piece_M3e_cell_stmt.
Hypothesis PM3e_rc : hq_piece_M3e_rc_stmt.
Hypothesis PM24_first : hq_piece_M24_first_stmt.

Theorem headamp_check_holds : forall RLO RHI : Z,
headamp_check_contract segs B MT headamp_himg_A RLO RHI.
Proof.
intros RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs e pos ev r
  HPRE HL5 Hwf Hlen Hpp Hpod Hfb Hra Hhull Hamem Hal Hfo Hrao Hdj Hrc Herr Hfrm.
set (cx := {| x_STK := STK; x_sp0 := sp0; x_FP := FP; x_ly := ly; x_S := S; x_W0 := W0; x_mem0 := mem0;
  x_md0 := md0; x_own := own; x_k := k; x_regs := regs; x_lyc := lyc; x_Sc := Sc; x_W := W; x_memc := memc;
  x_mdc := mdc; x_RLO := RLO; x_RHI := RHI; x_e := e; x_pos := pos |} : hs_scx segs).
assert (HS : hq_start_M03 cx r ev).
{ split; [exact HPRE|]. split; [exact HL5|]. split; [exact Hwf|]. split; [exact Hlen|].
  split; [exact Hpp|]. split; [exact Hpod|]. split; [exact Hfb|]. split; [exact Hra|].
  split; [exact Hhull|]. split; [exact Hamem|]. split; [exact Hal|]. split; [exact Hfo|].
  split; [exact Hrao|]. split; [exact Hdj|]. split; [exact Hrc|]. split; [exact Herr | exact Hfrm]. }
(* the contract's post, as the pieces' POST; M03's last cut is it *)
set (POST := hd_seg_post segs B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
  (hi_c6 headamp_himg_A) (hd_fxk [8; 9; 10; 14; 15; 18; 19] fx)
  (fun a => hd_inw e (hi_w3 headamp_himg_A) a \/ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) \/
            (as_errno B <= a < as_errno B + 4))
  (fun W2 regs2 mem2 =>
   hd_cut segs (w_H W2) mem2 regs2 e (hi_L6 headamp_himg_A) /\
   hd_fsh segs (w_H W2) mem2 (e_F e) (hi_shB headamp_himg_A) /\
   garr8 segs (mrestrict (w_H W2) mem2) (e_out e)
     (hd_zbytes (ha_cells_bytes (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))) /\
   (exists ev', rd32 (aview segs (w_H W2) mem2) (as_errno B) ev'))).
assert (HC6 : hq_from_C6 cx r POST).
{ intros fx2 ly2 S2 W2 regs2 mem2 md2 HC.
  destruct HC as (Hcore & Hfxk & HL6 & Hfsh & Hout & Hev).
  destruct Hcore as (HJ & Hr234 & Hfr & Hperm & Hio & Hmo & Hmem).
  apply SRr_ret. exists fx2, ly2, S2, regs2, mem2, md2.
  split; [reflexivity|]. split; [exact Hfxk|]. split; [exact HJ|]. split; [exact Hr234|].
  split; [exact Hfr|]. split; [exact Hperm|]. split; [exact Hio|]. split; [exact Hmo|].
  split; [exact Hmem|]. split; [exact HL6|]. split; [exact Hfsh|]. split; [exact Hout | exact Hev]. }
assert (HFIRST : hq_from_FIRST cx r POST) by exact (PM24_first cx POST r ev HS HC6).
destruct (PM3e_rc cx POST r ev HS HFIRST) as [HRC HRCM].
assert (HPAIR0 : hq_from_PAIR cx r POST 0)
  by exact (hq_pairs_closed cx r POST ev HS PM3b_pair PM3b_scan PM3b_latch PM3b_refuse PM3c_key PM3d_value
             PM3e_cell HRC 0%nat).
assert (HX : hq_from_X cx r POST) by exact (PM3a_setup cx POST r ev HS HPAIR0 HRC HRCM).
exact (PM3a_head cx POST r ev HS HX HFIRST).
Qed.
End seam.

End d.
End c.
End b.

Print Assumptions headamp_check_holds.
