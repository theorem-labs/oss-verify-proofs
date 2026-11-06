(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgSlots.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632 for fuzz_qdisc's image A) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks reac_role_cfg_apply_state 0x82ed4 against lib/A/RPgCSpec.v's rl_cfg_apply_state_specX on the concrete image lib/A/Img0.v rsegs, with the plumbing of lib/A/RPgCfgChanges.v; the plain walk it replaces is lib/Prog/reac_role_cfg_apply_state.v (a split on the beq). The leaf's post is RPgCSpec's rl_post (the float state fx kept, no extra bytes E); qdisc's region of the divisor constant, its arithmetic lemmas and its three branches are dropped. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgCfgApply.v, with its module paths changed; 120 of its 152 lines of code are new or changed and 25 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropSel.v at a529a88a618 for reac-pw/fuzz_headamp image A: every address relocated (role image A -> headamp image A); the property index is in a7 (role a6) and the latch's cells move by the plan's slot map (R+0xb8 -> R+0xd8, R+0x88 -> R+0xa8, R+0x90 -> R+0xb0); module paths. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on its unstripped
   twin sha256 b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a): the property loop's latch
   (0x82ac0 / 0x82ac8) of LLVMFuzzerTestOneInput, as block lemmas over lib/A/HPgPropKit.v.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgSteps HPgMem HPgPropKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Local Notation pa_post := (pa_post B MT).

(* ---- the latch 0x82ac0 -> N 0x812f4 / P1 0x82c6c ----
     0x82ac0 ld a7,0xd8(s1)   i
     0x82ac4 ld s9,0xa8(s1)   seen'
     0x82ac8 addiw a7,a7,1    i + 1
     0x82acc ld a0,0xb0(s1)   np
     0x82ad0 beq a7,a0,0x82c6c
     0x82ad4 j 0x812f4 *)
Definition latch_facts : facts :=
mkFacts [ (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 2 0); (34%nat, mkAF 0 1 0); (35%nat, mkAF 1 3 0) ] [] [].
Definition ss_latch : sstate :=
mkSS PA_LATCH sr_atoms
[ YP09.mkRegion (Some 9%nat) 0xa8 0xe0 0 0
  [ YP09.mkChunk 0xa8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0xb0 (CVal 8 (SOff 35 0)); YP09.mkChunk 0xd8 (CVal 8 (SOff 33 0)) ] ]
None latch_facts.
Definition latch_R (i seen np : Z) (W2 : world rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
getr regs2 17 = w64 (i + 1) /\ getr regs2 25 = w64 seen /\ getr regs2 10 = w64 np.
Lemma pa_latch : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R i seen np : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> 0 <= R -> R + 0x100 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd8) 8 i ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa8) 8 seen ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 np ->
0 <= i -> i < np -> np <= 3 -> 0 <= seen <= 1 ->
SRr rsegs W (cfg_at rsegs PA_LATCH regs memc mdc)
(pa_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if i + 1 =? np then PA_P1 else PA_N)
[10; 17; 25]%bv (fun _ => False) (latch_R i seen np)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i seen np HJ H9 HR0 HR1 Vi Vs Vn Hi0 Hin Hn3 Hs.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
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
(* 0x82ac0 .. 0x82acc, stop at the beq 0x82ad0 *)
pa_runb. pa_keep pa_kwr_ro.
pa_branch Hc; rewrite branch_eq_U, !U_SOff, E33, E35, !unsigned_lit_small in Hc by lia;
rewrite !zcanon_id in Hc by (unfold M64; lia);
first [apply (proj1 (Z.eqb_eq _ _)) in Hc | apply (proj1 (Z.eqb_neq _ _)) in Hc].
- replace (if i + 1 =? np then PA_P1 else PA_N) with PA_P1 by (destruct (Z.eqb_spec (i + 1) np); [reflexivity | lia]).
  pa_run PA_P1. pa_keep pa_kwr_ro.
  pa_leaf (pa_extra [i; seen; np]).
  unfold latch_R. pa_reg (17%bv : bv 5). pa_reg (25%bv : bv 5). pa_reg (10%bv : bv 5).
  unfold w64. rewrite !denot_lit_U, !U_SOff, E33, E34, E35, !unsigned_lit_small by lia.
  rewrite !zcanon_id by (unfold M64; lia). rewrite !Z.add_0_r. auto.
- replace (if i + 1 =? np then PA_P1 else PA_N) with PA_N by (destruct (Z.eqb_spec (i + 1) np); [lia | reflexivity]).
  pa_run PA_N. pa_keep pa_kwr_ro.
  pa_leaf (pa_extra [i; seen; np]).
  unfold latch_R. pa_reg (17%bv : bv 5). pa_reg (25%bv : bv 5). pa_reg (10%bv : bv 5).
  unfold w64. rewrite !denot_lit_U, !U_SOff, E33, E34, E35, !unsigned_lit_small by lia.
  rewrite !zcanon_id by (unfold M64; lia). rewrite !Z.add_0_r. auto.
Qed.

(* ---- the latch's second entry 0x82ac8 (from the shape-7 piece: a7 = i and s9 = seen' already in registers) ----
     0x82ac8 addiw a7,a7,1 / 0x82acc ld a0,0xb0(s1) / 0x82ad0 beq a7,a0,0x82c6c / 0x82ad4 j 0x812f4 *)
Definition latch7_facts : facts :=
mkFacts [ (17%nat, mkAF 0 2 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 1 3 0) ] [] [].
Definition ss_latch7 : sstate :=
mkSS PA_LATCH7 sr_atoms
[ YP09.mkRegion (Some 9%nat) 0xb0 0xb8 0 0 [ YP09.mkChunk 0xb0 (CVal 8 (SOff 33 0)) ] ]
None latch7_facts.
Definition latch7_R (i np : Z) (W2 : world rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
getr regs2 17 = w64 (i + 1) /\ getr regs2 10 = w64 np.
Lemma pa_latch7 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R i np : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 17 = w64 i -> 0 <= R -> R + 0x100 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 np ->
0 <= i -> i < np -> np <= 3 ->
SRr rsegs W (cfg_at rsegs PA_LATCH7 regs memc mdc)
(pa_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if i + 1 =? np then PA_P1 else PA_N)
[10; 17]%bv (fun _ => False) (latch7_R i np)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i np HJ H9 H17 HR0 HR1 Vn Hi0 Hin Hn3.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
assert (E9 : bv_unsigned (ew (Ereg regs (pa_extra [np])) 9) = R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E17 : ew (Ereg regs (pa_extra [np])) 17 = Z_to_bv 64 i) by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl), H17; reflexivity).
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
    rewrite E17, E33, pa_extra_K. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    repeat split; try lia; apply Z.mod_1_r. }
remember (Ereg regs (pa_extra [np])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (pa_extra [np])) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs PABx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
by (intros; reflexivity).
unfold cfg_at. change (w64 PA_LATCH7) with (Z_to_bv 64 PA_LATCH7).
pa_runb. pa_keep pa_kwr_ro.
pa_branch Hc; rewrite branch_eq_U, !U_SOff, E17, E33, !unsigned_lit_small in Hc by lia;
rewrite !zcanon_id in Hc by (unfold M64; lia);
first [apply (proj1 (Z.eqb_eq _ _)) in Hc | apply (proj1 (Z.eqb_neq _ _)) in Hc].
- replace (if i + 1 =? np then PA_P1 else PA_N) with PA_P1 by (destruct (Z.eqb_spec (i + 1) np); [reflexivity | lia]).
  pa_run PA_P1. pa_keep pa_kwr_ro.
  pa_leaf (pa_extra [np]).
  unfold latch7_R. pa_reg (17%bv : bv 5). pa_reg (10%bv : bv 5).
  unfold w64. rewrite !denot_lit_U, !U_SOff, E17, E33, !unsigned_lit_small by lia.
  rewrite !zcanon_id by (unfold M64; lia). rewrite !Z.add_0_r. auto.
- replace (if i + 1 =? np then PA_P1 else PA_N) with PA_N by (destruct (Z.eqb_spec (i + 1) np); [lia | reflexivity]).
  pa_run PA_N. pa_keep pa_kwr_ro.
  pa_leaf (pa_extra [np]).
  unfold latch7_R. pa_reg (17%bv : bv 5). pa_reg (10%bv : bv 5).
  unfold w64. rewrite !denot_lit_U, !U_SOff, E17, E33, !unsigned_lit_small by lia.
  rewrite !zcanon_id by (unfold M64; lia). rewrite !Z.add_0_r. auto.
Qed.

End d.
End b.
