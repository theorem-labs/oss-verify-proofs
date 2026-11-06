(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropSel.v at a529a88a618 (pa_latch7, as
   hbp_latch) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a618 (pa_piece_latch's LATCH7 half, as
   hbp_piece_latch) for reac-pw/fuzz_headamp's image B: one latch entry (image B has one), t0 / a3 / a7 / s2 / s4 in
   place of role's a6 / R+0xb8 / R+0x88 / s9, np at R+0x100 in place of R+0x90, the cut states of lib/AU/HPgSeg.v. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropLatch.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropSel.v at a529a88a618 (pa_latch7, as
   hbp_latch) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a618 (pa_piece_latch's LATCH7 half, as
   hbp_piece_latch) for reac-pw/fuzz_headamp's image B: one latch entry (image B has one), t0 / a3 / a7 / s2 / s4 in
   place of role's a6 / R+0xb8 / R+0x88 / s9, np at R+0x100 in place of R+0x90, the cut states of lib/AU/HPgSeg.v. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on its
   unstripped twin sha256 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the property loop's
   latch of LLVMFuzzerTestOneInput (0x80c40), LATCH 0x82ae4 -> N 0x81494 / P1 0x82bf0, as the block lemma hbp_latch
   and the piece lemma hbp_piece_latch : HPgSeg.hsu_piece_W4_latch_stmt at headamp_himg_B / headamp_bld_B.
   Proves no function (kind: segment lemma).
     0x82ae4 addiw t0,t0,1     i + 1            (t0 = i at LATCH)
     0x82ae8 mv s2,a7          the cursor       (a7 at LATCH, s2 at N)
     0x82aec mv s4,a3          seen             (a3 at LATCH, s4 at N)
     0x82af0 ld a0,0x100(s1)   np               (R+0x100)
     0x82af4 beq t0,a0,0x82bf0                  -> P1
     0x82af8 j 0x81494                          -> N
   REGISTERS AND CELLS (for a port by a register / slot map): reads t0, a7, a3, s1, R+0x100; writes t0, s2, s4, a0;
   no store. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgMem HPgSeg HPgPropKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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

(* ---- the block LATCH 0x82ae4 -> N 0x81494 / P1 0x82bf0: env slot 33 = np (the cell R+0x100) ---- *)
Definition hbp_latch_facts : facts :=
mkFacts [ (5%nat, mkAF 0 2 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 1 3 0) ] [] [].
Definition hbp_ss_latch : sstate :=
mkSS HBP_LATCH sr_atoms
[ YP09.mkRegion (Some 9%nat) 0x100 0x108 0 0 [ YP09.mkChunk 0x100 (CVal 8 (SOff 33 0)) ] ]
None hbp_latch_facts.
Definition hbp_latch_R (i seen cur np : Z) (W2 : world rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
: Prop :=
getr regs2 5 = w64 (i + 1) /\ getr regs2 18 = w64 cur /\ getr regs2 20 = w64 seen /\ getr regs2 10 = w64 np.
Lemma hbp_latch : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R i seen cur np : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 5 = w64 i -> getr regs 13 = w64 seen -> getr regs 17 = w64 cur ->
0 <= R -> R + 0x108 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 np ->
0 <= i -> i < np -> np <= 3 -> 0 <= seen <= 1 -> 0 <= cur <= 2 ^ 63 ->
SRr rsegs W (cfg_at rsegs HBP_LATCH regs memc mdc)
(hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
 (if i + 1 =? np then HBP_P1 else HBP_N) [5; 10; 18; 20]%bv (fun _ => False) (hbp_latch_R i seen cur np)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i seen cur np
  HJ H9 H5 H13 H17 HR0 HR1 Vn Hi0 Hin Hn3 Hs Hc0.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
assert (E9 : bv_unsigned (ew (Ereg regs (hbp_extra [np])) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E5 : ew (Ereg regs (hbp_extra [np])) 5 = Z_to_bv 64 i)
  by (rewrite (ew_Ereg_nat regs _ 5 5%bv eq_refl), H5; reflexivity).
assert (E13 : ew (Ereg regs (hbp_extra [np])) 13 = Z_to_bv 64 seen)
  by (rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl), H13; reflexivity).
assert (E17 : ew (Ereg regs (hbp_extra [np])) 17 = Z_to_bv 64 cur)
  by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl), H17; reflexivity).
assert (E33 : ew (Ereg regs (hbp_extra [np])) 33 = Z_to_bv 64 np) by reflexivity.
assert (HS : st_ok rsegs (Ereg regs (hbp_extra [np])) hbp_ss_latch
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HBP_LATCH) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor; (eapply hbp_chunk8; [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; eassumption
      | lia | eassumption ]).
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [hbp_latch_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E5, E33, hbp_extra_K. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    repeat split; try lia; apply Z.mod_1_r. }
remember (Ereg regs (hbp_extra [np])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (hbp_extra [np])) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs HBPBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
by (intros; reflexivity).
unfold cfg_at. change (w64 HBP_LATCH) with (Z_to_bv 64 HBP_LATCH).
(* 0x82ae4 .. 0x82af0, stop at the beq 0x82af4 *)
hbp_runb. hbp_keep hbp_kwr_ro.
hbp_branch Hc; rewrite branch_eq_U, !U_SOff, E5, E33, !unsigned_lit_small in Hc by lia;
rewrite !zcanon_id in Hc by (unfold M64; lia);
first [apply (proj1 (Z.eqb_eq _ _)) in Hc | apply (proj1 (Z.eqb_neq _ _)) in Hc].
- replace (if i + 1 =? np then HBP_P1 else HBP_N) with HBP_P1
    by (destruct (Z.eqb_spec (i + 1) np); [reflexivity | lia]).
  hbp_run HBP_P1. hbp_keep hbp_kwr_ro.
  hbp_leaf (hbp_extra [np]).
  unfold hbp_latch_R. hbp_reg (5%bv : bv 5). hbp_reg (18%bv : bv 5). hbp_reg (20%bv : bv 5). hbp_reg (10%bv : bv 5).
  unfold w64. rewrite !denot_lit_U, !U_SOff, E5, E13, E17, E33, !unsigned_lit_small by lia.
  rewrite !zcanon_id by (unfold M64; lia). rewrite !Z.add_0_r. auto.
- replace (if i + 1 =? np then HBP_P1 else HBP_N) with HBP_N
    by (destruct (Z.eqb_spec (i + 1) np); [lia | reflexivity]).
  hbp_run HBP_N. hbp_keep hbp_kwr_ro.
  hbp_leaf (hbp_extra [np]).
  unfold hbp_latch_R. hbp_reg (5%bv : bv 5). hbp_reg (18%bv : bv 5). hbp_reg (20%bv : bv 5). hbp_reg (10%bv : bv 5).
  unfold w64. rewrite !denot_lit_U, !U_SOff, E5, E13, E17, E33, !unsigned_lit_small by lia.
  rewrite !zcanon_id by (unfold M64; lia). rewrite !Z.add_0_r. auto.
Qed.

(* ================================ the piece: LATCH -> N / P1 ================================ *)
Lemma hbp_piece_latch : hsu_piece_W4_latch_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof using MTL LAWS.
unfold hsu_piece_W4_latch_stmt. intros cx POST rest i Hst HN HP1.
destruct Hst as (Hpre & Hc1 & Hlen0 & Hin0).
pose proof (hbp_R_bounds B cx _ Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof asan_consts as (C1 & _).
unfold hsu_from_LATCH. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hlen Hcut.
destruct Hcut as (Hcore & Hfsh & Hpp & Hin & Hsuf & Hwf & Hsh & Hnp & Hps & Hnp3 & Hloop & Hat).
pose proof Hin as (Hleft & _ & _ & _ & _ & Hsrc0 & Hsrcn & _).
pose proof Hsuf as (j & Hj & Er).
assert (Lr : length r = (length rest - j)%nat) by (rewrite Er; apply length_skipn).
assert (Hcur : hsu_cur rsegs cx rest r = e_src (x_e cx) + Z.of_nat j) by (unfold hsu_cur; rewrite Lr; lia).
unfold hsu_at_cx in Hat.
hbp_take Hat (LReg 9) (e_R (x_e cx)) A9.
hbp_take Hat (LReg 5) (Z.of_nat (length ps) - 1) A5.
hbp_take Hat (LReg 13) (hsu_seen ps) A13.
hbp_take Hat (LReg 17) (hsu_cur rsegs cx rest r) A17.
hbp_take Hat (LCell XR 0x100) np An.
assert (Hseen : 0 <= hsu_seen ps <= 1) by (unfold hsu_seen; destruct (existsb _ _); cbn; lia).
rewrite Z.mod_small in An by lia.
pose proof Hcore as (HJ & _).
assert (HRlo : 0 <= e_R (x_e cx)) by lia.
assert (HRhi : e_R (x_e cx) + 0x108 <= 2 ^ 64) by lia.
assert (Hi0 : 0 <= Z.of_nat (length ps) - 1) by lia.
assert (Hilt : Z.of_nat (length ps) - 1 < np) by lia.
assert (Hcur63 : 0 <= hsu_cur rsegs cx rest r <= 2 ^ 63) by (rewrite Hcur; lia).
eapply SRr_bind.
{ exact (hbp_latch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (Z.of_nat (length ps) - 1)
    (hsu_seen ps) (hsu_cur rsegs cx rest r) np HJ A9 A5 A13 A17 HRlo HRhi An Hi0 Hilt Hnp3 Hseen Hcur63). }
intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
destruct HR as (R5 & R18 & R20 & R10).
pose proof (hbp_mem_all _ _ _ _ Hmem) as Hall.
assert (Hat3 : hsu_at rsegs (w_H W3) mem3 regs3 (x_e cx)
  (hsu_Rc1 rsegs cx ++ hsu_Kc rsegs cx sh np ++
   [(LReg 17, hsu_cur rsegs cx rest r); (LReg 28, Z.of_nat (length r))])).
{ assert (Hat' : hsu_at rsegs (w_H W2) mem2 regs2 (x_e cx)
    (hsu_Rc1 rsegs cx ++ hsu_Kc rsegs cx sh np ++
     [(LReg 17, hsu_cur rsegs cx rest r); (LReg 28, Z.of_nat (length r))])) by (hbp_list; hbp_from Hat).
  eapply hbp_at_move; [exact Hat'|]. hbp_kept Hkeep ltac:(apply Hall). }
assert (Hcore3 : hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (hbp_core_step B MT MTL cx _ (fun _ => False) _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 _ Hfr Hperm Hio Hmo Hmem _);
  [hbp_regs234 Hkeep | intros a []]. }
assert (Hfsh3 : hsu_fsh_at rsegs cx W3 mem3 (hsu_P0 headamp_himg_B)).
{ unfold hsu_fsh_at in *. eapply (hm_fsh_kept rsegs); [exact Hfsh|]. intros jj Hjj. apply Hall. }
assert (Hpp3 : hsu_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps None))).
{ unfold hsu_pp_at in *.
  eapply (hm_bytes_kept rsegs _ _ _ _ _ (pc_image (PbCut sh ps None))); [exact Hpp|].
  intros x Hx. apply Hall. }
destruct (Z.eqb_spec (Z.of_nat (length ps) - 1 + 1) np) as [Heq|Hne].
- replace (Z.of_nat (length ps) - 1 + 1 =? np) with true by (symmetry; apply Z.eqb_eq; exact Heq).
  change (mkCfg (mkst regs3 (w64 HBP_P1) mem3 (seg_rom rsegs)) md3)
    with (cfg_at rsegs (bi_P1 headamp_bld_B) regs3 mem3 md3).
  apply (HP1 ly3 S3 W3 regs3 mem3 md3 sh np ps r).
  split.
  + split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|].
    split; [exact Hwf|]. split; [exact Hlen0|]. split; [exact Hsh|]. split; [exact Hnp|]. split; [lia | exact Hloop].
  + hbp_list; hbp_from Hat3.
- replace (Z.of_nat (length ps) - 1 + 1 =? np) with false by (symmetry; apply Z.eqb_neq; exact Hne).
  change (mkCfg (mkst regs3 (w64 HBP_N) mem3 (seg_rom rsegs)) md3)
    with (cfg_at rsegs (bi_N headamp_bld_B) regs3 mem3 md3).
  apply (HN ly3 S3 W3 regs3 mem3 md3 sh np ps r Hlen).
  split; [exact Hcore3|]. split.
  + hbp_list; first [hbp_from Hat3 | idtac].
    * cbn [hd_at]. refine (eq_trans R5 _). f_equal. lia.
    * cbn [hd_at]. exact R20.
    * cbn [hd_at]. exact R18.
  + split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|]. split; [exact Hwf|].
    split; [exact Hsh|]. split; [exact Hnp|]. split; [lia|]. split; [exact Hnp3 | exact Hloop].
Qed.

End d.
End b.

Print Assumptions hbp_latch.
Print Assumptions hbp_piece_latch.
