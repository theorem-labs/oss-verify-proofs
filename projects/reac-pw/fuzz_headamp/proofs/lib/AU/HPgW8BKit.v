(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropKit.v at a529a88a618 (the plumbing of
   the property loop's block lemmas: pa_chunk8, pa_keep, pa_kwr_ro, pa_run, pa_runb, pa_branch, pa_reg, pa_leaf),
   proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at a529a88a618 (kept_run) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v
   at a529a88a618 (its section g and its tactics: the (location, value) facts of a cut, the journal-and-frame step,
   the segment's write set, the first block's bounds and pod_put, the model of a shape-7 property, the start facts
   and the input at a cut) for reac-pw/fuzz_headamp's image B: rs_ / rl_ / rm_ -> hsu_ / hd_ / hm_, role's image A
   record and code -> fuzz_headamp.asan-ubsan's (lib/AU/Img0U.v rsegs, HPgImgB.headamp_himg_B: class-4 frame of
   1024 bytes, real frame of 0x220 bytes, write set [F+0x20, F+0x278) / 116 shadow bytes / [R, R+0x198)), the block
   post HPgSteps.hdu_blk_postE in place of pa_post, one table over the four pieces of image B. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropKit.v; 169 of its 212 lines of code are new or changed and 368 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the shared part of the
   piece W8 of the build (M01) of LLVMFuzzerTestOneInput 0x80c40, J 0x82618 -> C 0x81888 / CL 0x82a18 (pod.h:428-433,
   the piece statement lib/AU/HPgSeg.v hsu_piece_W8_stmt): the pcs, the code table, the post of a block of steps,
   and the statements of the blocks between the two calls, of the facts the cut J gives and of the piece's end.
   Proves no function (kind: segment lemma).

   THE CODE (0x82618 .. 0x8270c, 62 words; the calls leave it).
   A   J 0x82618 .. 0x82648: the instrumented check of the 8-byte load of pp->len through the shadow address the
       cut keeps in R+0x150 (`lbu`, `beqz` 0x82620), s5 := a3 (the cursor), s10 := t1 (what is left), len from
       s2 = &pp->len, the capacity test `bltu a1,a0` 0x8263c (len + 112 > 0x4000; dead, len <= 5384),
       a0 := s7 = pp, a1 := s4 = &e62, `jal` 0x82648 to pod_write_ent 0x84634 (ra = 0x8264c).
   C0  0x8264c, first (R+0x140) = 0: a0 := first, a1 := the pod index (R+0x158), `beqz a0` 0x82654 to 0x826c4,
       a0 := -8, to 0x826c8.
   C1  0x8264c, first = 1: the check of the 4-byte n_ent at pp + 0x4d14 (its shadow address from R+0xe0 plus s11,
       `lb`, `bnez` 0x82664 and again 0x82680 for the store), n_ent through R+0x120 (`lw`), the UBSan tests
       `bge` 0x82674 (n_ent + 1 does not overflow), `bltu` 0x82690 (n_ent < 33) and `bgeu` 0x826a4 (n_ent * 104
       below ~(pp + 0x4014), R+0xd8), the store of n_ent + 1, a0 := pp + 0x4014 + 104 n_ent (R+0xd0), a1 := s4,
       a2 := 104, `jal` 0x826bc to __asan_memcpy 0x51d8c (ra = 0x826c0).
   C2  0x826c0: a1 := the pod index (R+0x158), a0 := -8, to 0x826c8.
   E   0x826c8 .. 0x82700: lib/AU/HPgSteps.v hdu_scope_e62_out (e62's 13 shadow granules := 0xf8, a1 := a1 + 1,
       s7 := -8), to 0x82704.
   D   0x82704: a0 := cnt (R+0x128), `bne a1,a0` 0x82708 to C 0x81888, else `j` 0x8270c to CL 0x82a18.

   REGISTERS AND R-CELLS (image B; the role port renames these): s1 = R (x9), s2 = pp + 0x4000 (x18), s3 = the
   frame's shadow base (x19), s4 = &e62 = F + 0x210 (x20), s7 = pp (x23) at J and -8 at the end, s11 = K (x27),
   a3 = the cursor (x13) and t1 = what is left (x6) at J, s5 (x21) and s10 (x26) after A; R+0x150 the shadow
   address of pp + 0x4000, R+0x140 first, R+0x158 the pod index, R+0x128 cnt, R+0xe0 (pp + 0x4d14) >> 3,
   R+0x120 pp + 0x4d14, R+0xd8 ~(pp + 0x4014), R+0xd0 pp + 0x4014. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ======================================== the pcs and the code ======================================== *)
Definition HW8_J : Z := 0x82618.       (* the cut J, headamp_bld_B's bi_J *)
Definition HW8_PWE : Z := 0x84634.     (* pod_write_ent's entry *)
Definition HW8_RA1 : Z := 0x8264c.     (* the return address of the call 0x82648 *)
Definition HW8_MEMCPY : Z := 0x51d8c.  (* __asan_memcpy's entry *)
Definition HW8_RA2 : Z := 0x826c0.     (* the return address of the call 0x826bc *)
Definition HW8_SC0 : Z := 0x826c8.     (* the first scope-closing store, hdu_scope_e62_out's start *)
Definition HW8_SC1 : Z := 0x82704.     (* hdu_scope_e62_out's end *)
Definition HW8_C : Z := 0x81888.       (* the cut C, bi_C *)
Definition HW8_CL : Z := 0x82a18.      (* the cut CL, bi_CL *)
Lemma hw8_pcs : bi_J headamp_bld_B = HW8_J /\ bi_C headamp_bld_B = HW8_C /\ bi_CL headamp_bld_B = HW8_CL.
Proof. repeat split. Qed.

(* the 62 instruction words 0x82618 .. 0x8270c *)
Definition hw8_tbl : ctable := build_table rsegs HW8_J 62 TEmpty.
Lemma hw8_tbl_ok : table_ok rsegs hw8_tbl.
Proof. apply build_table_ok0. unfold HW8_J. lia. Qed.

(* the two return addresses are word-aligned code addresses *)
Lemma hw8_ret1 : YK0s.ret_ok (Z_to_bv 64 HW8_RA1).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma hw8_ret2 : YK0s.ret_ok (Z_to_bv 64 HW8_RA2).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

(* the frame's shadow at J (e62 in scope) and at the end (back to the prologue's) *)
Lemma hw8_PJ : hsu_PJ headamp_himg_B = hmu_sh false false false false false true false false.
Proof. vm_compute. reflexivity. Qed.
Lemma hw8_P0 : hsu_P0 headamp_himg_B = hmu_sh false false false false false false false false.
Proof. vm_compute. reflexivity. Qed.

(* the registers the piece keeps from J to its end: sp, gp, tp, s0, s1, s2, s3, s4, s6, s8, s9, s11 (s5 and s10 take
   a3 and t1, s7 and a1 are set again) *)
Definition hw8_keepF : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 25; 27]%bv.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================================== the post of a block of steps =====================================
   A block runs inside the harness's journal (the world, the layout and the state at the block's start), changes
   no register but those of clob and no byte of [0, 2^64) but those Wr names, and R says what it computed. *)
Definition hw8_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model)
(regs : bvmap 5 word) (pc : Z) (clob : list (bv 5)) (Wr : Z -> Prop)
(R : bvmap 5 word -> (word -> option byte) -> Prop) : world rsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc) mem' (seg_rom rsegs)) md' /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\ same_io mdc md' /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) memc a) /\
R regs' mem'.

(* ===================================== the four blocks of steps ===================================== *)
(* A: J -> pod_write_ent's entry. len = L <= 5384 kills the capacity test. *)
Definition hw8_blkA_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world rsegs) memc mdc k (regs : bvmap 5 word) (R pp L : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (pp, PP_SIZE) (ablocks B lyc Sc) ->
sp0 - STK <= R -> R + 0x220 <= sp0 ->
getr regs 9 = w64 R -> getr regs 18 = w64 (pp + 0x4000) -> getr regs 23 = w64 pp ->
getr regs 27 = w64 SHADOW_OFF ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (shadow_addr (pp + 0x4000) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 L ->
0 <= L <= 5384 ->
SRr rsegs W (cfg_at rsegs HW8_J regs memc mdc)
(hw8_post STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs HW8_PWE [1; 10; 11; 21; 26]%bv
  (fun _ => False)
  (fun regs' _ => getr regs' 1 = w64 HW8_RA1 /\ getr regs' 10 = w64 pp /\ getr regs' 11 = getr regs 20 /\
     getr regs' 21 = getr regs 13 /\ getr regs' 26 = getr regs 6)).

(* C0: the return of pod_write_ent -> the first scope-closing store, when first = 0 (no record copy) *)
Definition hw8_blkC0_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world rsegs) memc mdc k (regs : bvmap 5 word) (R kk : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
sp0 - STK <= R -> R + 0x220 <= sp0 ->
getr regs 9 = w64 R ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 kk ->
0 <= kk < 32 ->
SRr rsegs W (cfg_at rsegs HW8_RA1 regs memc mdc)
(hw8_post STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs HW8_SC0 [10; 11]%bv
  (fun _ => False)
  (fun regs' _ => getr regs' 10 = w64 (-8) /\ getr regs' 11 = w64 kk)).

(* C1: the return of pod_write_ent -> __asan_memcpy's entry, when first = 1: n_ent := n_ent + 1 and the
   arguments of the record copy pp->ent[n_ent] = e62 *)
Definition hw8_blkC1_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world rsegs) memc mdc k (regs : bvmap 5 word) (R pp kk : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (pp, PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, PP_SIZE) (ablocks B ly S) ->
sp0 - STK <= R -> R + 0x220 <= sp0 ->
getr regs 9 = w64 R -> getr regs 23 = w64 pp -> getr regs 27 = w64 SHADOW_OFF ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 1 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 kk ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (Z.shiftr (pp + 0x4d14) 3 mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x120) 8 ((pp + 0x4d14) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd8) 8 ((- pp - 0x4014 - 1) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd0) 8 ((pp + 0x4014) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4d14) 4 kk ->
0 <= kk < 32 ->
SRr rsegs W (cfg_at rsegs HW8_RA1 regs memc mdc)
(hw8_post STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs HW8_MEMCPY [1; 10; 11; 12]%bv
  (fun a => pp + 0x4d14 <= a < pp + 0x4d18)
  (fun regs' mem' => getr regs' 1 = w64 HW8_RA2 /\ getr regs' 10 = w64 (pp + 0x4014 + 104 * kk) /\
     getr regs' 11 = getr regs 20 /\ getr regs' 12 = w64 104 /\
     val_mem rsegs (mrestrict (w_H W) mem') (pp + 0x4d14) 4 (kk + 1))).

(* C2: the return of __asan_memcpy -> the first scope-closing store *)
Definition hw8_blkC2_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world rsegs) memc mdc k (regs : bvmap 5 word) (R kk : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
sp0 - STK <= R -> R + 0x220 <= sp0 ->
getr regs 9 = w64 R ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 kk ->
0 <= kk < 32 ->
SRr rsegs W (cfg_at rsegs HW8_RA2 regs memc mdc)
(hw8_post STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs HW8_SC0 [10; 11]%bv
  (fun _ => False)
  (fun regs' _ => getr regs' 10 = w64 (-8) /\ getr regs' 11 = w64 kk)).

(* D: the loop's test, to C when the pod index kk1 (already incremented) is not the count, else to CL *)
Definition hw8_blkD_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world rsegs) memc mdc k (regs : bvmap 5 word) (R kk1 cnt : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
sp0 - STK <= R -> R + 0x220 <= sp0 ->
getr regs 9 = w64 R -> getr regs 11 = w64 kk1 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x128) 8 cnt ->
0 <= kk1 <= 32 -> 0 <= cnt <= 32 ->
SRr rsegs W (cfg_at rsegs HW8_SC1 regs memc mdc)
(hw8_post STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs (if kk1 =? cnt then HW8_CL else HW8_C)
  [10]%bv (fun _ => False) (fun _ _ => True)).

(* ===================================== what the cut J gives =====================================
   The journal, the first block and the frame for locals at J, the registers and R-cells the blocks and the
   calls read, e62's bytes, the first block's image with its len and n_ent cells, the frame's shadow, the
   geometry the calls' premises ask for, and the model's bounds. *)
Definition hw8_J_facts_stmt : Prop :=
forall cx rest sh np ps cnt es rr r ed ly2 S2 W2 regs2 mem2 md2,
hsu_start_M01 rsegs B headamp_himg_B cx rest ->
hsu_cut_J rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r ed ly2 S2 W2 regs2 mem2 md2 ->
let e := x_e cx in
let R := e_R e in let F := e_F e in let pp := e_pp e in
let L := Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) in
let kk := Z.of_nat (length es) in
let fs := hsu_first ps in
let m := mrestrict (w_H W2) mem2 in
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem2 md2 (x_k cx) /\
st_nev (x_S cx) + x_k cx <= EV_MAX /\
In (pp, PP_SIZE) (ablocks B ly2 S2) /\ ~ In (pp, PP_SIZE) (ablocks B (x_ly cx) (x_S cx)) /\
In (4, x_pos cx) (x_own cx) /\ In (4, x_pos cx) (frames S2) /\ frame_addr ly2 4 (x_pos cx) = F /\
getr regs2 2 = w64 R /\ getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
getr regs2 9 = w64 R /\ getr regs2 18 = w64 (pp + 0x4000) /\ getr regs2 19 = w64 (shadow_addr F) /\
getr regs2 20 = w64 (F + 0x210) /\ getr regs2 23 = w64 pp /\ getr regs2 27 = w64 SHADOW_OFF /\
val_mem rsegs m (R + 0x150) 8 (shadow_addr (pp + 0x4000) mod 2 ^ 64) /\
val_mem rsegs m (R + 0x140) 8 fs /\ val_mem rsegs m (R + 0x158) 8 kk /\ val_mem rsegs m (R + 0x128) 8 cnt /\
val_mem rsegs m (R + 0xe0) 8 (Z.shiftr (pp + 0x4d14) 3 mod 2 ^ 64) /\
val_mem rsegs m (R + 0x120) 8 ((pp + 0x4d14) mod 2 ^ 64) /\
val_mem rsegs m (R + 0xd8) 8 ((- pp - 0x4014 - 1) mod 2 ^ 64) /\
val_mem rsegs m (R + 0xd0) 8 ((pp + 0x4014) mod 2 ^ 64) /\
hm_bytes rsegs (w_H W2) mem2 (F + 0x210) (ent_mem ed) /\
hm_bytes rsegs (w_H W2) mem2 pp (pc_image (PbCut sh ps (Some es))) /\
val_mem rsegs m (pp + 0x4000) 8 L /\
(fs = 1 -> val_mem rsegs m (pp + 0x4d14) 4 kk) /\
hd_fsh rsegs (w_H W2) mem2 F (hmu_sh false false false false false true false false) /\
pp mod 16 = 0 /\ in_app pp PP_SIZE /\ 4096 <= pp /\ pp + PP_SIZE <= alloc_ceiling /\
F mod 32 = 0 /\ in_app F 1024 /\ 4096 <= F /\ F + 1024 <= alloc_ceiling /\
(pp + PP_SIZE <= F \/ F + 1024 <= pp) /\
alloc_ceiling + T_SEG_STK <= R /\ R mod 32 = 0 /\ R + 0x220 <= x_sp0 cx /\
x_sp0 cx mod 16 = 0 /\ x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx - x_STK cx <= R - T_SEG_STK /\
0 <= L <= 5384 /\ L mod 8 = 0 /\ ent_wf ed /\
(length es < 32)%nat /\ kk < cnt /\ cnt <= 32 /\
(fs = 0 \/ fs = 1) /\ fs = Z.b2z (pc_first (PbCut sh ps (Some es))) /\
Forall (fun kv => pval_wf (snd kv)) ps /\ Forall ent_wf (all_ents ps) /\ Forall ent_wf es /\
(length ps <= 2)%nat.

(* ===================================== the piece's end =====================================
   From a state that keeps J's journal clauses, J's registers of hw8_keepF, has s5 / s10 = J's a3 / t1, a1 = the
   next pod index and s7 = -8, changed no byte outside the callees' stack, the first block and e62's 13 shadow
   granules, closed those granules (0xf8) and holds the image of the record with one more pod: the cut C (the next
   turn) or, when the count is reached, the cut CL. *)
Definition hw8_finish_stmt : Prop :=
forall cx POST rest i k ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r ed ly3 S3 W3 regs3 mem3 md3 (last : bool),
hsu_start_M01 rsegs B headamp_himg_B cx rest -> (length ps = i)%nat -> (length es = k)%nat ->
hsu_cut_J rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r ed ly2 S2 W2 regs2 mem2 md2 ->
hsu_from_C rsegs B MT headamp_himg_B headamp_bld_B cx POST rest i (S k) ->
hsu_from_CL rsegs B MT headamp_himg_B headamp_bld_B cx POST rest i ->
(Z.of_nat (S k) =? cnt) = last ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly3 S3 W3 mem3 md3 (x_k cx) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall r0 : bv 5, In r0 hw8_keepF -> getr regs3 r0 = getr regs2 r0) ->
getr regs3 21 = getr regs2 13 -> getr regs3 26 = getr regs2 6 ->
getr regs3 11 = w64 (Z.of_nat (S k)) -> getr regs3 23 = w64 (-8) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) ->
   ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + PP_SIZE) ->
   ~ (shadow_addr (e_F (x_e cx)) + 66 <= a < shadow_addr (e_F (x_e cx)) + 79) ->
   aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
(forall o, 66 <= o < 79 -> aview rsegs (w_H W3) mem3 (shadow_addr (e_F (x_e cx)) + o) = Some 248) ->
hm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx)) (pc_image (PbCut sh ps (Some (es ++ [ed])))) ->
SRr rsegs W3 (cfg_at rsegs (if last then HW8_CL else HW8_C) regs3 mem3 md3) POST.
End d.
End b.

Print Assumptions hw8_pcs.
Print Assumptions hw8_tbl_ok.
Print Assumptions hw8_ret1.
Print Assumptions hw8_ret2.
Print Assumptions hw8_PJ.
Print Assumptions hw8_P0.
