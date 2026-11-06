(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 361 of its 394 lines of code are new or changed and 257 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropSel.v at a529a88a6181 (the latch blocks
   pa_latch / pa_latch7) and the latch piece pa_piece_latch of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same
   commit, for reac-pw/fuzz_rate image A: rate's pcs and real-frame cells (i at R+0xf8, seen' at R+0xc8, np at
   R+0xd0); the latch's third entry 0x8252c (pa_latchi, from the Int-7 piece with i in a6) is new; the block post is
   lib/A/RtPgSteps.v rts_post; the cut lists are lib/A/RtPgSeg.v's. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address below is measured on its unstripped
   twin sha256 0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): the property loop's latch of
   LLVMFuzzerTestOneInput, from its three entries, as block lemmas over lib/A/RtPgPropKit.v, and the piece
   rs_piece_W4_latch_stmt (LATCH / LATCHI / LATCH7 -> N / P1) of lib/A/RtPgSeg.v. Proves no function (kind: segment
   lemma).
     0x82528 ld a6,0xf8(s1)   i            (LATCH, from the Struct's close)
     0x8252c ld s9,0xc8(s1)   seen'        (LATCHI, from the Int-7 piece: i already in a6)
     0x82530 addiw a6,a6,1    i + 1        (LATCH7, from the shape-7 piece: i in a6, seen' in s9)
     0x82534 ld a0,0xd0(s1)   np
     0x82538 beq a6,a0,0x826d4 (P1)
     0x8253c j 0x80e10 (N) *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSteps RtPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgSeg RtPgPropKit RtPgPropLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments, as lib/A/RtPgSteps.v names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

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
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Local Notation pa_post := (rts_post B MT).

(* what the latch computes, from each entry: a6 = i + 1, s9 = seen', a0 = np *)
Definition latch_R (i seen np : Z) (W2 : world rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
getr regs2 16 = w64 (i + 1) /\ getr regs2 25 = w64 seen /\ getr regs2 10 = w64 np.
Definition latch7_R (i np : Z) (W2 : world rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
getr regs2 16 = w64 (i + 1) /\ getr regs2 10 = w64 np.

(* ---- the latch 0x82528 -> N 0x80e10 / P1 0x826d4: i, seen' and np from their cells ---- *)
Definition latch_facts : facts :=
mkFacts [ (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 2 0); (34%nat, mkAF 0 1 0); (35%nat, mkAF 1 3 0) ] [] [].
Definition ss_latch : sstate :=
mkSS PA_LATCH sr_atoms
[ YP09.mkRegion (Some 9%nat) 0xc8 0x100 0 0
  [ YP09.mkChunk 0xc8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0xd0 (CVal 8 (SOff 35 0)); YP09.mkChunk 0xf8 (CVal 8 (SOff 33 0)) ] ]
None latch_facts.
Lemma pa_latch : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R i seen np : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> 0 <= R -> R + 0x100 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 i ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc8) 8 seen ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd0) 8 np ->
0 <= i -> i < np -> np <= 3 -> 0 <= seen <= 1 ->
SRr rsegs W (cfg_at rsegs PA_LATCH regs memc mdc)
(pa_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if i + 1 =? np then PA_P1 else PA_N)
[10; 16; 25]%bv (fun _ => False) (latch_R i seen np)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i seen np HJ H9 HR0 HR1 Vi Vs Vn Hi0 Hin Hn3 Hs.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
assert (E9 : bv_unsigned (ew (Ereg regs (pa_extra [i; seen; np])) 9) = R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E33 : ew (Ereg regs (pa_extra [i; seen; np])) 33 = Z_to_bv 64 i) by reflexivity.
assert (E34 : ew (Ereg regs (pa_extra [i; seen; np])) 34 = Z_to_bv 64 seen) by reflexivity.
assert (E35 : ew (Ereg regs (pa_extra [i; seen; np])) 35 = Z_to_bv 64 np) by reflexivity.
assert (HS : st_ok rsegs (Ereg regs (pa_extra [i; seen; np])) ss_latch (restrict (w_H W) (mkst regs (Z_to_bv 64 PA_LATCH) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor; (eapply pa_chunk8; [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; eassumption
      | lia | eassumption ]).
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [latch_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E33, E34, E35, pa_extra_K. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    repeat split; try lia; apply Z.mod_1_r. }
remember (Ereg regs (pa_extra [i; seen; np])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (pa_extra [i; seen; np])) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs PABx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
by (intros; reflexivity).
unfold cfg_at. change (w64 PA_LATCH) with (Z_to_bv 64 PA_LATCH).
(* 0x82528 .. 0x82534, stop at the beq 0x82538 *)
pa_runb. pa_keep pa_kwr_ro.
pa_branch Hc; rewrite branch_eq_U, !U_SOff, E33, E35, !unsigned_lit_small in Hc by lia;
rewrite !zcanon_id in Hc by (unfold M64; lia);
first [apply (proj1 (Z.eqb_eq _ _)) in Hc | apply (proj1 (Z.eqb_neq _ _)) in Hc].
- replace (if i + 1 =? np then PA_P1 else PA_N) with PA_P1 by (destruct (Z.eqb_spec (i + 1) np); [reflexivity | lia]).
  pa_run PA_P1. pa_keep pa_kwr_ro.
  pa_leaf (pa_extra [i; seen; np]).
  unfold latch_R. pa_reg (16%bv : bv 5). pa_reg (25%bv : bv 5). pa_reg (10%bv : bv 5).
  unfold w64. rewrite !denot_lit_U, !U_SOff, E33, E34, E35, !unsigned_lit_small by lia.
  rewrite !zcanon_id by (unfold M64; lia). rewrite !Z.add_0_r. auto.
- replace (if i + 1 =? np then PA_P1 else PA_N) with PA_N by (destruct (Z.eqb_spec (i + 1) np); [lia | reflexivity]).
  pa_run PA_N. pa_keep pa_kwr_ro.
  pa_leaf (pa_extra [i; seen; np]).
  unfold latch_R. pa_reg (16%bv : bv 5). pa_reg (25%bv : bv 5). pa_reg (10%bv : bv 5).
  unfold w64. rewrite !denot_lit_U, !U_SOff, E33, E34, E35, !unsigned_lit_small by lia.
  rewrite !zcanon_id by (unfold M64; lia). rewrite !Z.add_0_r. auto.
Qed.

(* ---- the latch's second entry 0x8252c (from the Int-7 piece: a6 = i already loaded); seen' and np from their
   cells ---- *)
Definition latchi_facts : facts :=
mkFacts [ (16%nat, mkAF 0 2 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 1 0); (34%nat, mkAF 1 3 0) ] [] [].
Definition ss_latchi : sstate :=
mkSS PA_LATCHI sr_atoms
[ YP09.mkRegion (Some 9%nat) 0xc8 0xd8 0 0
  [ YP09.mkChunk 0xc8 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xd0 (CVal 8 (SOff 34 0)) ] ]
None latchi_facts.
Lemma pa_latchi : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R i seen np : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 16 = w64 i -> 0 <= R -> R + 0x100 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc8) 8 seen ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd0) 8 np ->
0 <= i -> i < np -> np <= 3 -> 0 <= seen <= 1 ->
SRr rsegs W (cfg_at rsegs PA_LATCHI regs memc mdc)
(pa_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if i + 1 =? np then PA_P1 else PA_N)
[10; 16; 25]%bv (fun _ => False) (latch_R i seen np)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i seen np HJ H9 H16 HR0 HR1 Vs Vn Hi0 Hin Hn3 Hs.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
assert (E9 : bv_unsigned (ew (Ereg regs (pa_extra [seen; np])) 9) = R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E16 : ew (Ereg regs (pa_extra [seen; np])) 16 = Z_to_bv 64 i) by (rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl), H16; reflexivity).
assert (E33 : ew (Ereg regs (pa_extra [seen; np])) 33 = Z_to_bv 64 seen) by reflexivity.
assert (E34 : ew (Ereg regs (pa_extra [seen; np])) 34 = Z_to_bv 64 np) by reflexivity.
assert (HS : st_ok rsegs (Ereg regs (pa_extra [seen; np])) ss_latchi (restrict (w_H W) (mkst regs (Z_to_bv 64 PA_LATCHI) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor; (eapply pa_chunk8; [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; eassumption
      | lia | eassumption ]).
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [latchi_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E16, E33, E34, pa_extra_K. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    repeat split; try lia; apply Z.mod_1_r. }
remember (Ereg regs (pa_extra [seen; np])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (pa_extra [seen; np])) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs PABx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
by (intros; reflexivity).
unfold cfg_at. change (w64 PA_LATCHI) with (Z_to_bv 64 PA_LATCHI).
(* 0x8252c .. 0x82534, stop at the beq 0x82538 *)
pa_runb. pa_keep pa_kwr_ro.
pa_branch Hc; rewrite branch_eq_U, !U_SOff, E16, E34, !unsigned_lit_small in Hc by lia;
rewrite !zcanon_id in Hc by (unfold M64; lia);
first [apply (proj1 (Z.eqb_eq _ _)) in Hc | apply (proj1 (Z.eqb_neq _ _)) in Hc].
- replace (if i + 1 =? np then PA_P1 else PA_N) with PA_P1 by (destruct (Z.eqb_spec (i + 1) np); [reflexivity | lia]).
  pa_run PA_P1. pa_keep pa_kwr_ro.
  pa_leaf (pa_extra [seen; np]).
  unfold latch_R. pa_reg (16%bv : bv 5). pa_reg (25%bv : bv 5). pa_reg (10%bv : bv 5).
  unfold w64. rewrite !denot_lit_U, !U_SOff, E16, E33, E34, !unsigned_lit_small by lia.
  rewrite !zcanon_id by (unfold M64; lia). rewrite !Z.add_0_r. auto.
- replace (if i + 1 =? np then PA_P1 else PA_N) with PA_N by (destruct (Z.eqb_spec (i + 1) np); [lia | reflexivity]).
  pa_run PA_N. pa_keep pa_kwr_ro.
  pa_leaf (pa_extra [seen; np]).
  unfold latch_R. pa_reg (16%bv : bv 5). pa_reg (25%bv : bv 5). pa_reg (10%bv : bv 5).
  unfold w64. rewrite !denot_lit_U, !U_SOff, E16, E33, E34, !unsigned_lit_small by lia.
  rewrite !zcanon_id by (unfold M64; lia). rewrite !Z.add_0_r. auto.
Qed.

(* ---- the latch's third entry 0x82530 (from the shape-7 piece: a6 = i and s9 = seen' already in registers) ---- *)
Definition latch7_facts : facts :=
mkFacts [ (16%nat, mkAF 0 2 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 1 3 0) ] [] [].
Definition ss_latch7 : sstate :=
mkSS PA_LATCH7 sr_atoms
[ YP09.mkRegion (Some 9%nat) 0xd0 0xd8 0 0 [ YP09.mkChunk 0xd0 (CVal 8 (SOff 33 0)) ] ]
None latch7_facts.
Lemma pa_latch7 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R i np : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 16 = w64 i -> 0 <= R -> R + 0x100 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd0) 8 np ->
0 <= i -> i < np -> np <= 3 ->
SRr rsegs W (cfg_at rsegs PA_LATCH7 regs memc mdc)
(pa_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if i + 1 =? np then PA_P1 else PA_N)
[10; 16]%bv (fun _ => False) (latch7_R i np)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i np HJ H9 H16 HR0 HR1 Vn Hi0 Hin Hn3.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
assert (E9 : bv_unsigned (ew (Ereg regs (pa_extra [np])) 9) = R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E16 : ew (Ereg regs (pa_extra [np])) 16 = Z_to_bv 64 i) by (rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl), H16; reflexivity).
assert (E33 : ew (Ereg regs (pa_extra [np])) 33 = Z_to_bv 64 np) by reflexivity.
assert (HS : st_ok rsegs (Ereg regs (pa_extra [np])) ss_latch7 (restrict (w_H W) (mkst regs (Z_to_bv 64 PA_LATCH7) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor; (eapply pa_chunk8; [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; eassumption
      | lia | eassumption ]).
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [latch7_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E16, E33, pa_extra_K. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    repeat split; try lia; apply Z.mod_1_r. }
remember (Ereg regs (pa_extra [np])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (pa_extra [np])) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs PABx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
by (intros; reflexivity).
unfold cfg_at. change (w64 PA_LATCH7) with (Z_to_bv 64 PA_LATCH7).
pa_runb. pa_keep pa_kwr_ro.
pa_branch Hc; rewrite branch_eq_U, !U_SOff, E16, E33, !unsigned_lit_small in Hc by lia;
rewrite !zcanon_id in Hc by (unfold M64; lia);
first [apply (proj1 (Z.eqb_eq _ _)) in Hc | apply (proj1 (Z.eqb_neq _ _)) in Hc].
- replace (if i + 1 =? np then PA_P1 else PA_N) with PA_P1 by (destruct (Z.eqb_spec (i + 1) np); [reflexivity | lia]).
  pa_run PA_P1. pa_keep pa_kwr_ro.
  pa_leaf (pa_extra [np]).
  unfold latch7_R. pa_reg (16%bv : bv 5). pa_reg (10%bv : bv 5).
  unfold w64. rewrite !denot_lit_U, !U_SOff, E16, E33, !unsigned_lit_small by lia.
  rewrite !zcanon_id by (unfold M64; lia). rewrite !Z.add_0_r. auto.
- replace (if i + 1 =? np then PA_P1 else PA_N) with PA_N by (destruct (Z.eqb_spec (i + 1) np); [lia | reflexivity]).
  pa_run PA_N. pa_keep pa_kwr_ro.
  pa_leaf (pa_extra [np]).
  unfold latch7_R. pa_reg (16%bv : bv 5). pa_reg (10%bv : bv 5).
  unfold w64. rewrite !denot_lit_U, !U_SOff, E16, E33, !unsigned_lit_small by lia.
  rewrite !zcanon_id by (unfold M64; lia). rewrite !Z.add_0_r. auto.
Qed.

End d.
End b.

(* ================================ the latch piece: LATCH / LATCHI / LATCH7 -> N / P1 ================================ *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* the end of the latch from any entry: the block's post at regs3 / mem3 with every location of rs_L_LATCH kept, a6
   = |ps| and s9 = seen', into the head N (another property is due) or the builder's end P1 *)
Lemma pa_latch_end : forall cx POST rest i ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3,
q_len (x_e cx) = rt_len rest ->
rs_from_N rsegs B MT cx POST rest (S i) -> rs_from_P1 rsegs B MT cx POST rest ->
(length ps = S i)%nat ->
rs_latch_body rsegs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
rs_core rsegs B MT cx (rs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3 ->
rs_at rsegs (w_H W3) mem3 regs3 (x_e cx) (rs_L_LATCH rsegs cx sh np ps rest r) ->
rs_fsh_at rsegs cx W3 mem3 rs_P0 -> rs_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps None)) ->
getr regs3 16 = w64 (Z.of_nat (length ps) - 1 + 1) -> getr regs3 25 = w64 (rs_seen ps) ->
SRr rsegs W3 (mkCfg (mkst regs3 (w64 (if Z.of_nat (length ps) - 1 + 1 =? np then PA_P1 else PA_N)) mem3
  (seg_rom rsegs)) md3) POST.
Proof.
intros cx POST rest i ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3 Hlen0 HN HP1 Hlen Hb Hcore3 Hat3
  Hfsh3 Hpp3 R16 R25.
destruct Hb as (_ & _ & _ & Hin & Hsuf & Hwf & Hsh & Hnp & Hps & Hnp3 & Hloop).
destruct (Z.eqb_spec (Z.of_nat (length ps) - 1 + 1) np) as [Heq|Hne].
- change (mkCfg (mkst regs3 (w64 PA_P1) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_P1 regs3 mem3 md3).
  apply (HP1 ly3 S3 W3 regs3 mem3 md3 sh np ps r).
  split.
  + split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|].
    split; [exact Hwf|]. split; [exact Hlen0|]. split; [exact Hsh|]. split; [exact Hnp|]. split; [lia | exact Hloop].
  + pa_list; pa_from Hat3.
- change (mkCfg (mkst regs3 (w64 PA_N) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_N regs3 mem3 md3).
  apply (HN ly3 S3 W3 regs3 mem3 md3 sh np ps r Hlen).
  split; [exact Hcore3|]. split.
  + pa_list; first [pa_from Hat3 | idtac].
    * cbn [rt_at]. refine (eq_trans R16 _). f_equal. lia.
    * cbn [rt_at]. exact R25.
  + split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|]. split; [exact Hwf|].
    split; [exact Hsh|]. split; [exact Hnp|]. split; [lia|]. split; [exact Hnp3 | exact Hloop].
Qed.

Lemma pa_piece_latch : rs_piece_W4_latch_stmt rsegs B MT.
Proof using MTL LAWS.
unfold rs_piece_W4_latch_stmt. intros cx POST rest i Hst HN HP1.
destruct Hst as (Hpre & Hfsh0 & Hc1 & Hlen0 & Hin0).
pose proof (pa_R_bounds B cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof asan_consts as (C1 & _).
assert (Hseen : forall ps, 0 <= rs_seen ps <= 1) by (intros ps; unfold rs_seen; destruct (existsb _ _); cbn; lia).
(* what every entry leaves of the cut: the journal-and-frame part, the frame's shadow and the first block, for a
   block that writes nothing *)
assert (Hstep : forall ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3,
  rs_latch_body rsegs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly3 S3 W3 mem3 md3 (x_k cx) ->
  (forall r0 : Z, r0 = 2 \/ r0 = 3 \/ r0 = 4 -> getr regs3 (Z_to_bv 5 r0) = getr regs2 (Z_to_bv 5 r0)) ->
  frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3 /\
  rs_fsh_at rsegs cx W3 mem3 rs_P0 /\ rs_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps None))).
{ intros ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3 Hb HJ3 Hr3 Hfr Hperm Hio Hmo Hmem.
  pose proof Hb as (Hcore & Hfsh & Hpp & _).
  pose proof (pa_mem_all _ _ _ _ Hmem) as Hall.
  split; [|split].
  - refine (pa_core_step B MT MTL cx _ (fun _ => False) _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 Hr3 Hfr Hperm Hio Hmo Hmem _).
    intros a [].
  - unfold rs_fsh_at in *. eapply rtm_fsh_kept; [exact Hfsh|]. intros j Hj. apply Hall.
  - unfold rs_pp_at in *. eapply (rtm_bytes_kept rsegs); [exact Hpp|]. intros x Hx. apply Hall. }
split; [|split].
- (* LATCH 0x82528: i, seen' and np from their cells *)
  unfold rs_from_LATCH. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hlen Hcut.
  destruct Hcut as [Hb Hat]. pose proof Hb as (Hcore & _ & _ & _ & _ & _ & _ & _ & Hps & Hnp3 & _).
  unfold rs_at_cx in Hat.
  pa_take Hat (LReg 9) (q_R (x_e cx)) A9.
  pa_take Hat (LCell XR 0xf8) (Z.of_nat (length ps) - 1) Ai.
  pa_take Hat (LCell XR 0xc8) (rs_seen ps) As.
  pa_take Hat (LCell XR 0xd0) np An.
  pose proof (Hseen ps) as Hs.
  rewrite Z.mod_small in Ai, As, An by lia.
  pose proof Hcore as (HJ & _).
  eapply SRr_bind.
  { refine (pa_latch B MT MTL LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (q_R (x_e cx)) (Z.of_nat (length ps) - 1) (rs_seen ps) np
      HJ A9 _ _ Ai As An _ _ _ Hs); lia. }
  intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
  destruct HR as (R16 & R25 & R10).
  pose proof (pa_mem_all _ _ _ _ Hmem) as Hall.
  destruct (Hstep ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3 Hb HJ3
    ltac:(pa_regs234 Hkeep) Hfr Hperm Hio Hmo Hmem) as (Hcore3 & Hfsh3 & Hpp3).
  assert (Hat3 : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx) (rs_L_LATCH rsegs cx sh np ps rest r)).
  { eapply pa_at_move; [exact Hat|]. pa_kept Hkeep ltac:(apply Hall). }
  exact (pa_latch_end cx POST rest i ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3
    Hlen0 HN HP1 Hlen Hb Hcore3 Hat3 Hfsh3 Hpp3 R16 R25).
- (* LATCHI 0x8252c: i in a6; seen' and np from their cells *)
  unfold rs_from_LATCHI. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hlen Hcut.
  destruct Hcut as [Hb Hat]. pose proof Hb as (Hcore & _ & _ & _ & _ & _ & _ & _ & Hps & Hnp3 & _).
  unfold rs_at_cx in Hat.
  pa_take Hat (LReg 9) (q_R (x_e cx)) A9.
  pa_take Hat (LReg 16) (Z.of_nat (length ps) - 1) A16.
  pa_take Hat (LCell XR 0xc8) (rs_seen ps) As.
  pa_take Hat (LCell XR 0xd0) np An.
  pose proof (Hseen ps) as Hs.
  rewrite Z.mod_small in As, An by lia.
  pose proof Hcore as (HJ & _).
  eapply SRr_bind.
  { refine (pa_latchi B MT MTL LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (q_R (x_e cx)) (Z.of_nat (length ps) - 1) (rs_seen ps) np
      HJ A9 A16 _ _ As An _ _ _ Hs); lia. }
  intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
  destruct HR as (R16 & R25 & R10).
  pose proof (pa_mem_all _ _ _ _ Hmem) as Hall.
  destruct (Hstep ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3 Hb HJ3
    ltac:(pa_regs234 Hkeep) Hfr Hperm Hio Hmo Hmem) as (Hcore3 & Hfsh3 & Hpp3).
  assert (Hat' : rs_at rsegs (w_H W2) mem2 regs2 (x_e cx) (rs_L_LATCH rsegs cx sh np ps rest r)).
  { unfold rs_at in Hat |- *. apply Forall_app in Hat as [Hat _]. exact Hat. }
  assert (Hat3 : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx) (rs_L_LATCH rsegs cx sh np ps rest r)).
  { eapply pa_at_move; [exact Hat'|]. pa_kept Hkeep ltac:(apply Hall). }
  exact (pa_latch_end cx POST rest i ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3
    Hlen0 HN HP1 Hlen Hb Hcore3 Hat3 Hfsh3 Hpp3 R16 R25).
- (* LATCH7 0x82530: i in a6, seen' in s9; np from its cell *)
  unfold rs_from_LATCH7. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hlen Hcut.
  destruct Hcut as [Hb Hat]. pose proof Hb as (Hcore & _ & _ & _ & _ & _ & _ & _ & Hps & Hnp3 & _).
  unfold rs_at_cx in Hat.
  pa_take Hat (LReg 9) (q_R (x_e cx)) A9.
  pa_take Hat (LReg 16) (Z.of_nat (length ps) - 1) A16.
  pa_take Hat (LReg 25) (rs_seen ps) A25.
  pa_take Hat (LCell XR 0xd0) np An.
  rewrite Z.mod_small in An by lia.
  pose proof Hcore as (HJ & _).
  eapply SRr_bind.
  { refine (pa_latch7 B MT MTL LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (q_R (x_e cx)) (Z.of_nat (length ps) - 1) np
      HJ A9 A16 _ _ An _ _ _); lia. }
  intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
  destruct HR as (R16 & R10).
  pose proof (pa_mem_all _ _ _ _ Hmem) as Hall.
  destruct (Hstep ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3 Hb HJ3
    ltac:(pa_regs234 Hkeep) Hfr Hperm Hio Hmo Hmem) as (Hcore3 & Hfsh3 & Hpp3).
  (* rs_L_LATCH from the cut's list: seen' is in s9 here, and the latch block writes no cell, so R+0xf8 and R+0xc8
     are not facts of this cut; the end needs only s9 *)
  assert (Hat3 : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx)
    (rs_Rc rsegs cx ++ rs_Kc rsegs cx sh np ++ rs_Hc rsegs cx
     ++ [(LReg 22, shadow_addr (q_pp (x_e cx) + 0x4000)); (LReg 26, -0x4001); (LReg 25, rs_seen ps)]
     ++ rs_cur2 rsegs cx rest r)).
  { assert (Hat' : rs_at rsegs (w_H W2) mem2 regs2 (x_e cx)
      (rs_Rc rsegs cx ++ rs_Kc rsegs cx sh np ++ rs_Hc rsegs cx
       ++ [(LReg 22, shadow_addr (q_pp (x_e cx) + 0x4000)); (LReg 26, -0x4001); (LReg 25, rs_seen ps)]
       ++ rs_cur2 rsegs cx rest r)) by (pa_list; pa_from Hat).
    eapply pa_at_move; [exact Hat'|]. pa_kept Hkeep ltac:(apply Hall). }
  pose proof Hb as (_ & _ & _ & Hin & Hsuf & Hwf & Hsh & Hnp & _ & _ & Hloop).
  destruct (Z.eqb_spec (Z.of_nat (length ps) - 1 + 1) np) as [Heq|Hne].
  + change (mkCfg (mkst regs3 (w64 PA_P1) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_P1 regs3 mem3 md3).
    apply (HP1 ly3 S3 W3 regs3 mem3 md3 sh np ps r).
    split.
    * split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|].
      split; [exact Hwf|]. split; [exact Hlen0|]. split; [exact Hsh|]. split; [exact Hnp|]. split; [lia | exact Hloop].
    * pa_list; pa_from Hat3.
  + change (mkCfg (mkst regs3 (w64 PA_N) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_N regs3 mem3 md3).
    apply (HN ly3 S3 W3 regs3 mem3 md3 sh np ps r Hlen).
    split; [exact Hcore3|]. split.
    * pa_list; first [pa_from Hat3 | idtac].
      cbn [rt_at]. refine (eq_trans R16 _). f_equal. lia.
    * split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|]. split; [exact Hwf|].
      split; [exact Hsh|]. split; [exact Hnp|]. split; [lia|]. split; [exact Hnp3 | exact Hloop].
Qed.
End p.

Print Assumptions pa_piece_latch.
