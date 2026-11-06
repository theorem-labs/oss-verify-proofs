(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths, module names and numbers changed; 131 of its 179 lines of code are new or changed and 3292 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YA0q YCbm YK06 YI0m YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i YXcalls YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd YCbf YCj1 YCja YCjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacFrameCleanLen.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_classify_c disco_table_c hunt_c reac_disco_table_observe_c reac_frame_clean_len_c reac_hunt_observe_c
HuntObsFacts HuntObsLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacHuntObserveCore.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing}.
Context {PW : PAWinImg lib_both3_0_listing}.
Context {PV : PAObjVal lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis ASM1 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TCOS : treac_disco_classify_on_segment_spec B.
Hypothesis TOBS : treac_disco_table_observe_spec B.
Hypothesis HRO : YRo.tfib_ro_unowned B.
#[local] Notation EHO := (@ReacHuntObserveCore.EHO rc PI).

Lemma ho_entry : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs : bvmap 5 word) (h n hb hn : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 h ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_HUNT_OBSERVE_STK -> spZ regs <= sp0 ->
  In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn ->
  0 < h -> h mod 8 = 0 -> 0 <= n <= 8 ->
  val_mem SEGS (mrestrict (w_H W) memc) (h + 384) 4 n ->
  st_ok_pi SEGS VAL (EHO regs n (as_uar_cell B)) ss_ho
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_both3_reac_hunt_observe)) memc (seg_rom SEGS))) /\
  sh_ok SEGS HOBx ho_SH (EHO regs n (as_uar_cell B)) (mrestrict (w_H W) memc).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs h n hb hn
HJ H10 Hal16 Hwin Hsp Hin Hhb Hhe Hh0 Hh8 Hn HV.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfr : REAC_HUNT_OBSERVE_STK = REAC_HUNT_OBSERVE_FRAME + CLS_STK) by reflexivity.
assert (Hcls : 0 <= CLS_STK)
by (unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK; lia).
assert (Hfr0 : REAC_HUNT_OBSERVE_FRAME = 176) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc hb hn HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ hb hn HAR Hin) as Hbimg.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
rewrite restrict_mkst_fx.
set (E := EHO regs n (as_uar_cell B)).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regs (ho_extra n (as_uar_cell B))) m)
by (intros m Hm; subst E; unfold EHO; apply Eimg_low; exact Hm).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 h)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E59 : ew E 59 = Z_to_bv 64 (as_uar_cell B)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 27)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (subst E; unfold EHO; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (subst E; unfold EHO; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (subst E; unfold EHO; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 0)) as VR0. pose proof (pa_val_range (A_OBJ 1)) as VR1.
pose proof (pa_val_range (A_OBJ 12)) as VR12.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
split.
- unfold ss_ho, ho_regions. apply pa_entry_st_ok_full.
  + subst E. unfold EHO. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, ho_hregion.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp, Hfr0.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 59 0) (as_uar_cell B));
      [cbn [sv_denot]; rewrite E59, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
    * rewrite (VB 59%nat (as_uar_cell B) E59) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
    * rewrite (VB 10%nat h E10) by lia.
      split; [lia|]. split; [lia|]. split.
      -- intros o Ho. apply (apresent_writable SEGS). apply (fun Hq => proj1 (Hbpres (h + o) Hq)). lia.
      -- constructor; [|constructor].
         apply (chunk_ok_val SEGS E _ h 384 4 (SOff 33 0) n);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         change (N.to_nat 4) with 4%nat. exact HV.
  + apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, ho_hregion, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat h E10) by lia. rewrite (VB 59%nat (as_uar_cell B) E59) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia.
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia.
    cbn [base_val]. rewrite Usp, Hfr0.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with Hx : _ /\ _ |- _ => destruct Hx as [? ?] end.
    repeat split; first [ assumption | (apply or_comm; assumption) | lia ].
  + unfold ho_atoms0. split; [|split; exact I]. cbn [f_atoms atoms_ok].
    unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, E33, E59, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB, YImgTop.IMG_LO, YImgTop.IMG_TOP. repeat split; first [exact I | lia].
- unfold ho_SH, sh_ok. apply Forall_cons; [|apply Forall_nil].
  assert (HU10 : U E (SOff 10 0) = h) by (shent_U_norm; reflexivity).
  assert (HUB : U E HOBx = SHADOW_OFF) by (unfold HOBx; shent_U_norm; unfold SB, SHADOW_OFF; reflexivity).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HU10, HUB. split.
  + replace (h + 0) with h by lia. replace (480 - 0) with 480 by lia.
    apply (range_addressable_of_block SEGS B LAWS lyc Sc W memc mdc hb hn h 480 HAR Hin); lia.
  + intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia.
Qed.

End h.
End f.
End d.
