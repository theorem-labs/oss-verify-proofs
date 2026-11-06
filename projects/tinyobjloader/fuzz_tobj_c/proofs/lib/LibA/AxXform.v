(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "sobj"; "ss_facts"; "valuation"; "ss_objs"; "sprop"; "holds"; "obj_hi_of"; "obj_lo_of"; "smatch"; "ss_next"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "@Corelib.Init.Datatypes"; "option"; "list"; "nat"; "Some"; "bool"; "None"; "length"; "S"; "app"; "prod"; "true"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axform1"; "apply_axforms"; "apply_axformsS"; "apply_axformsS_p"; "apply_axforms_ref"; "apply_axform1_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "mk_pf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "rebase_obj_at"; "merge_objs_at"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform.X"; "drop_obj_at"; "@Stdlib.Lists.List"; "nth_error"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObjFast"; "merge_objs_at_p"; "rebase_obj_at_p"; "split_obj_at_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA"; "mk_pf_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast"; "unbase_obj_at_p"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymObj SymEntail SymCFG Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymDigFast SymObjFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase XformFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Inductive axform :=
| AXSplit (i : nat) (mid : sv)
| AXMerge (i : nat)
| AXRebase (i : nat)
| AXUnbase (i : nat) (c0 : Z)
| AXSelect (idxs : list nat).

Definition apply_axform1 (S : sstate) (x : axform) : option sstate := ltac2:(tb__ "0|2|
S1eSfS0A1M0Lx;Vx;S11SbS32VS;R2R1A3Lmid;Li;S11S31VS;R1A2Li;S11S30VS;R1A2Li;S11S28S33VS;R2R1A3Lc0;Li;S10S11A1S13G0L_;S2cS15S1S4VS;A1M1A2R1A2S12S0S27VS;S2aG1R1A2A2A2S14S0A1X13x2Lidxs;X1ex5").

Fixpoint apply_axformsS (S : sstate) (xs : list axform) : option sstate :=
  match xs with
  | [] => Some S
  | x :: r => match apply_axform1 S x with Some S' => apply_axformsS S' r | None => None end
  end.

Definition apply_axforms_ref (A : axst) (xs : list axform) : option axst := ltac2:(tb__ "0|0|
SfS0A1SfScA1Lx;S21SdVA;A1Vxs;A2S0S12ScSeVA;R1A2A2LS';S14ScA1Xfx2").

Definition apply_axform1_p (pf : pfacts) (S : sstate) (x : axform) : option sstate := ltac2:(tb__ "0|2|
S1eSfS0A1M0Lx;Vx;S11SbS3bVpf;VS;R2R1A4Lmid;Li;S11S39Vpf;VS;R1A3Li;S11S3aVpf;VS;R1A3Li;S11S28S3dVpf;VS;R2R1A4Lc0;Li;S10S11A1S13G0L_;S2cS15S1S4VS;A1M1A2R1A2S12S0S27VS;S2aG1R1A2A2A2S14S0A1X13x2Lidxs;X1ex5").
Lemma apply_axform1_p_eq : ltac2:(tb__ "0|0|
S0S1eS1aSfS0A1S24S2bS2R2A1A1R2R1A3S1fR2R1A2A3Fx;FS;").
Proof.
  intros S [i mid|i|i|i c0|idxs]; cbn [apply_axform1_p apply_axform1];
    [apply split_obj_at_p_eq | apply merge_objs_at_p_eq | apply rebase_obj_at_p_eq | apply unbase_obj_at_p_eq | reflexivity].
Qed.
Lemma apply_axform1_keeps_facts : ltac2:(tb__ "0|0|
S0S1eS0S1aSfS0A1S1fR3R2A2S12S0R1A2A3S1aS10S5A1S2R2A1S2R4A1A3F_;FS';Fx;FS;").
Proof.
  intros S [i mid|i|i|i c0|idxs] S' H; cbn [apply_axform1] in H.
  - exact (split_obj_at_facts _ _ _ _ H).
  - exact (merge_objs_at_facts _ _ _ H).
  - exact (rebase_obj_at_facts _ _ _ H).
  - exact (proj1 (unbase_facts _ _ _ _ H)).
  - destruct (select_ok _ _); [|discriminate]. injection H as <-. reflexivity.
Qed.
Fixpoint apply_axformsS_p (pf : pfacts) (S : sstate) (xs : list axform) : option sstate :=
  match xs with
  | [] => Some S
  | x :: r => match apply_axform1_p pf S x with Some S' => apply_axformsS_p pf S' r | None => None end
  end.
Lemma apply_axformsS_p_eq : ltac2:(tb__ "0|0|
S10S1eA1S0S1aSfS0A1S22S2bS2R1A1A1R1R2A3S21R1R2A2A3FS;Fxs;").
Proof.
  induction xs as [|x r IH]; intros S; cbn [apply_axformsS_p apply_axformsS]; [reflexivity|].
  rewrite apply_axform1_p_eq. destruct (apply_axform1 S x) as [S'|] eqn:E; [|reflexivity].
  rewrite <- (apply_axform1_keeps_facts _ _ _ E). apply IH.
Qed.
Definition apply_axforms (A : axst) (xs : list axform) : option axst := ltac2:(tb__ "0|1|
SfS0A1SfScA1Lx;S22S3cS2SdVA;A1M0A1A1G0Vxs;A3S0S12ScSeVA;R1A2A2LS';S14ScA1Xfx2").
Lemma apply_axforms_ref_eq : ltac2:(tb__ "0|0|
ScS10S1eA1S1aSfScA1S20R2R1A2S23R2R1A2A3Fxs;FA;").
Proof. intros A xs. unfold apply_axforms, apply_axforms_ref. rewrite DigFastA.mk_pf_f_eq, apply_axformsS_p_eq. reflexivity. Qed.

Section X.
Variable segs : list Segment.

Lemma ax_setS_setS : ltac2:(tb__ "0|0|
ScS0S0S1aScSeSeR3R2A2R1A2SeR3R1A2A3FS';FS;FA;").
Proof. intros [a b c] S S'. reflexivity. Qed.
Lemma ax_setS_id : ltac2:(tb__ "0|0|
ScS1aScSeR1SdR1A1A2R1A3FA;").
Proof. intros [a b c]. reflexivity. Qed.

Lemma SPA_rebase : ltac2:(tb__ "0|0|
S1dS3ScS11S0S10S26Q40A1A1S25S1aSfS0A1S30SdR5A1R4A2S12S0R3A2A3S1cVsegs;R8R6R7R3R2A6S1cVsegs;R9SeR7R5A2R8R4R3A6F_;F_;Fw;Ftp;FS';Fi;FA;Frho;FJ;").
Proof using .
  intros J rho A i S' tp [tr [ms md]] Hrb [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (smatch_rebase segs rho (ax_S A) i S' _ Hrb Hsm) as Hsm'.
  unfold rebase_obj_at in Hrb.
  destruct (nth_error (ss_objs (ax_S A)) i) as [o|] eqn:Hn; [|discriminate].
  destruct (rebase_obj (ss_facts (ax_S A)) o) as [o'|] eqn:Ho; [|discriminate]. injection Hrb as <-.
  assert (Hin_o : In o (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn).
  pose proof (smatch_facts segs _ _ _ Hsm) as Hfacts.
  destruct (rebase_obj_shape _ _ _ Ho) as (a & c0 & Hbase & Hsh2).
  cbn zeta in Hsh2. destruct (itv (ss_facts (ax_S A)) a) as [l h] eqn:Hitv.
  destruct Hsh2 as (Hlh & Hl & Hh & Slo & Shi & Scells & NA & Eo').
  assert (Hb : bv_unsigned (eval rho (ob_base o)) = bv_unsigned (eval rho a) + snorm c0).
  { rewrite Hbase. apply (rebase_base_val rho (ss_facts (ax_S A)) a c0 Hfacts). rewrite Hitv. repeat split; assumption. }
  pose proof (shift_ok_sound rho _ _ _ Hfacts Slo) as Elo.
  pose proof (shift_ok_sound rho _ _ _ Hfacts Shi) as Ehi.
  assert (Hrange : obj_range rho o' = obj_range rho o).
  { rewrite Eo'. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite Elo, Ehi, Hb. f_equal; lia. }
  split; [exact Hsm'|]. split; [exact HMI|]. split; [unfold axwf in Hwf |- *; cbn; exact Hwf|]. split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  cbn [set_objs ss_objs]. intros o2 x Ho2 Hx. apply in_app_or in Ho2 as [Ho2|[<-|Ho2]].
  - exists o2. split; [eapply In_firstn_In; exact Ho2 | exact Hx].
  - exists o. split; [exact Hin_o|]. rewrite <- Hrange. exact Hx.
  - exists o2. split; [eapply In_skipn_In; exact Ho2 | exact Hx].
Qed.

Lemma SPA_unbase : ltac2:(tb__ "0|0|
S1dS3ScS11S28S0S10S26Q40A1A1S25S1aSfS0A1S33SdR6A1R5R4A3S12S0R3A2A3S1cVsegs;R9R7R8R3R2A6S1cVsegs;RaSeR8R5A2R9R4R3A6F_;F_;Fw;Ftp;FS';Fc0;Fi;FA;Frho;FJ;").
Proof using .
  intros J rho A i c0 S' tp [tr [ms md]] Hub [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (smatch_unbase segs rho (ax_S A) i c0 S' _ Hub Hsm) as Hsm'.
  unfold unbase_obj_at in Hub.
  destruct (nth_error (ss_objs (ax_S A)) i) as [o|] eqn:Hn; [|discriminate].
  destruct (unbase_obj (ss_facts (ax_S A)) o c0) as [o'|] eqn:Ho; [|discriminate]. injection Hub as <-.
  assert (Hin_o : In o (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn).
  pose proof (smatch_facts segs _ _ _ Hsm) as Hfacts.
  pose proof (unbase_obj_shape _ _ _ _ Ho) as Hsh2. cbn zeta in Hsh2.
  destruct (itv (ss_facts (ax_S A)) (ob_base o)) as [l h] eqn:Hitv.
  destruct Hsh2 as (Hlh & Hl & Hh & Slo & Shi & Scells & NA & Eo').
  pose proof (shift_ok_sound rho _ _ _ Hfacts Slo) as Elo.
  pose proof (shift_ok_sound rho _ _ _ Hfacts Shi) as Ehi.
  assert (Hb : bv_unsigned (eval rho (mk_addk (ob_base o) c0)) = bv_unsigned (eval rho (ob_base o)) + snorm c0).
  { pose proof (itv_sound rho (ss_facts (ax_S A)) (ob_base o) Hfacts) as IT. rewrite Hitv in IT. unfold in_itv in IT. cbn in IT.
    rewrite mk_addk_sound, bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
    rewrite Zplus_mod_idemp_r. rewrite <- Zplus_mod_idemp_r, <- (snorm_mod c0), Zplus_mod_idemp_r. apply Z.mod_small.
    pose proof (bv_unsigned_in_range _ (eval rho (ob_base o))) as UR. rewrite two64 in UR. lia. }
  assert (Hrange : obj_range rho o' = obj_range rho o).
  { rewrite Eo'. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite Elo, Ehi, Hb. f_equal; lia. }
  split; [exact Hsm'|]. split; [exact HMI|]. split; [unfold axwf in Hwf |- *; cbn; exact Hwf|]. split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  cbn [set_objs ss_objs]. intros o2 x Ho2 Hx. apply in_app_or in Ho2 as [Ho2|[<-|Ho2]].
  - exists o2. split; [eapply In_firstn_In; exact Ho2 | exact Hx].
  - exists o. split; [exact Hin_o|]. rewrite <- Hrange. exact Hx.
  - exists o2. split; [eapply In_skipn_In; exact Ho2 | exact Hx].
Qed.

Lemma SPA_select : ltac2:(tb__ "0|1|
S1dS3ScS10S11A1S10S26Q40A1A1S25S1aS13S2cS15S1S4SdR4A1A1A2R3A2S19A3S1cVsegs;R7R5R6R3R2A6S1cVsegs;R8SeR6S27SdR6A1M0S2aS4G0A1R5A2A2A2R7R4R3A6F_;F_;Fw;Ftp;Fidxs;FA;Frho;FJ;").
Proof using .
  intros J rho A idxs tp [tr [ms md]] Hok [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  unfold select_ok in Hok. apply andb_prop in Hok as [Hok Hcov]. apply andb_prop in Hok as [Hnd Hlt].
  assert (Hlt' : forall i, In i idxs -> (i < length (ss_objs (ax_S A)))%nat).
  { intros i Hi. pose proof (proj1 (forallb_forall _ _) Hlt i Hi) as X. apply Nat.ltb_lt in X. exact X. }
  assert (Hcov' : forall i, (i < length (ss_objs (ax_S A)))%nat -> In i idxs).
  { intros i Hi. apply memN_In'. apply (proj1 (forallb_forall _ _) Hcov i). apply in_seq. lia. }
  pose proof (smatch_select segs rho (ax_S A) idxs _ Hsm Hnd Hlt' Hcov') as Hsm'.
  split; [exact Hsm'|]. split; [exact HMI|]. split; [unfold axwf in Hwf |- *; cbn; exact Hwf|]. split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  cbn [set_objs ss_objs]. intros o2 x Ho2 Hx. exists o2. split; [|exact Hx]. eapply select_In; [exact Ho2 | exact Hlt'].
Qed.

Lemma SPA_axform1 : ltac2:(tb__ "0|0|
S1dS3ScS1eS0S10S26Q40A1A1S25S1aSfS0A1S1fSdR5A1R4A2S12S0R3A2A3S1cVsegs;R8R6R7R3R2A6S1cVsegs;R9SeR7R5A2R8R4R3A6F_;F_;Fw;Ftp;FS';Fx;FA;Frho;FJ;").
Proof using .
  intros J rho A x S' tp w H HS. destruct x as [i mid|i|i|i c0|idxs]; cbn [apply_axform1] in H.
  - eapply SPA_split; eauto.
  - eapply SPA_merge; eauto.
  - eapply SPA_rebase; eauto.
  - eapply SPA_unbase; eauto.
  - destruct (select_ok (length (ss_objs (ax_S A))) idxs) eqn:E; [|discriminate]. injection H as <-.
    apply SPA_select; assumption.
Qed.

Theorem SPA_axforms_ref : ltac2:(tb__ "0|0|
S1dS10S1eA1S3ScScS10S26Q40A1A1S25S1aSfScA1S23R4R6A2S12ScR3A2A3S1cVsegs;R8R5R6R3R2A6S1cVsegs;R9R5R7R4R3A6F_;F_;Fw;Ftp;FA';FA;Frho;Fxs;FJ;").
Proof using .
  intros J xs. unfold apply_axforms_ref.
  assert (G : forall rho A S0 A' tp w,
    match apply_axformsS S0 xs with Some S' => Some (ax_setS A S') | None => None end = Some A' ->
    SPA segs J (ax_setS A S0) rho tp w -> SPA segs J A' rho tp w).
  { induction xs as [|x r IH]; intros rho A S0 A' tp w H HS; cbn [apply_axformsS] in H.
    - injection H as <-. exact HS.
    - destruct (apply_axform1 S0 x) as [S1|] eqn:E1; [|discriminate].
      apply (IH rho A S1 A' tp w H). rewrite <- (ax_setS_setS A S0 S1).
      eapply SPA_axform1; [|exact HS]. cbn. exact E1. }
  intros rho A A' tp w H HS. apply (G rho A (ax_S A) A' tp w H). rewrite ax_setS_id. exact HS.
Qed.

Theorem SPA_axforms : ltac2:(tb__ "0|0|
S1dS10S1eA1S3ScScS10S26Q40A1A1S25S1aSfScA1S20R4R6A2S12ScR3A2A3S1cVsegs;R8R5R6R3R2A6S1cVsegs;R9R5R7R4R3A6F_;F_;Fw;Ftp;FA';FA;Frho;Fxs;FJ;").
Proof using .
  intros J xs rho A A' tp w H. rewrite apply_axforms_ref_eq in H. exact (SPA_axforms_ref J xs rho A A' tp w H).
Qed.

Lemma apply_axform1_facts : ltac2:(tb__ "0|0|
S0S1eS0S1aSfS0A1S1fR3R2A2S12S0R1A2A3S1bS1aS10S5A1S2R2A1S2R4A1A3S1aS29SaR2A1SaR4A1A3A2F_;FS';Fx;FS;").
Proof.
  intros S x S' H. destruct x as [i mid|i|i|i c0|idxs]; cbn [apply_axform1] in H.
  - unfold split_obj_at in H. destruct (nth_error (ss_objs S) i); [|discriminate].
    destruct (sv_below (ss_next S) mid && in_bounds (ss_facts S) (ob_lo s) (ob_hi s) mid 0)%bool; [|discriminate].
    destruct (obj_split s mid) as [[o1 o2]|]; [|discriminate]. injection H as <-. split; reflexivity.
  - unfold merge_objs_at in H. destruct (nth_error (ss_objs S) i); [|discriminate]. destruct (nth_error (ss_objs S) (Datatypes.S i)); [|discriminate].
    destruct (sitv (ss_facts S) (ob_lo s)) as [[? ?]|]; [|discriminate]. destruct (sitv (ss_facts S) (ob_hi s0)) as [[? ?]|]; [|discriminate].
    destruct (_ <? _); [|discriminate]. destruct (obj_merge s s0); [|discriminate]. injection H as <-. split; reflexivity.
  - unfold rebase_obj_at in H. destruct (nth_error (ss_objs S) i); [|discriminate]. destruct (rebase_obj (ss_facts S) s); [|discriminate].
    injection H as <-. split; reflexivity.
  - apply unbase_facts in H. exact H.
  - destruct (select_ok (length (ss_objs S)) idxs); [|discriminate]. injection H as <-. split; reflexivity.
Qed.

Definition drop_obj_at (S : sstate) (i : nat) : sstate := ltac2:(tb__ "0|1|
S27VS;S17S1S2eS1Vi;S4VS;A1M0A3S2fS1S16Vi;A1G0A3A3A2").

Lemma smatch_drop_empty : ltac2:(tb__ "0|0|
S3S0S11S1S18S10S38A1S37A2S1aSfS1A1S35S1S4R4A1R3A3S12S1R2A2A3S2dS5S6R6A1S2R5A1A3S36S7R7R4A2S8R7R4A2A2F_;S9Vsegs;R7R6R3A4S9Vsegs;R8S34R7R6A2R4A4F_;F_;F_;Fw;Fo;Fi;FS;Frho;").
Proof using .
  intros rho S i o [tr [ms md]] Hn Hemp Hsm.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *. specialize (Hemp Hfacts).
  pose proof (nth_error_split3 _ _ _ Hn) as EQ.
  destruct Hmem as (Hall & Hpd & Hfr).
  unfold smatch, drop_obj_at. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { pose proof (swf_objs_replace S _ o _ [] Hwf EQ eq_refl) as W. cbn [app] in W. rewrite <- app_nil_l with (l := skipn (Datatypes.S i) (ss_objs S)) . exact W. }
  repeat (split; [assumption|]). split; [|exact Hfacts].
  split; [|split].
  - rewrite EQ in Hall. apply Forall_app in Hall as [A B]. inversion B; subst. apply Forall_app. auto.
  - apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd. rewrite EQ in Hpd. rewrite !map_app in Hpd |- *. cbn in Hpd.
    apply pdr_app_inv in Hpd as (P1 & P2 & P3). cbn in P2. destruct P2 as [_ P2].
    apply pdr_app; [exact P1 | exact P2 |]. intros r1 r2 H1 H2. apply P3; [exact H1 | cbn; auto].
  - intros a Hout. apply Hfr. rewrite EQ. unfold outside_all in Hout |- *. rewrite Forall_app in Hout |- *. destruct Hout as [A B].
    split; [exact A|]. constructor; [|exact B]. cbn zeta. unfold obj_range. cbn [fst snd]. lia.
Qed.

Lemma SPA_drop_empty : ltac2:(tb__ "0|0|
S1dS3ScS11S1S10S26Q40A1A1S25S1aSfS1A1S35S1S4SdR5A1A1R4A3S12S1R3A2A3S2dS5S6R7A1S2SdR6A1A1A3S36S7R8R5A2S8R8R5A2A2F_;S1cVsegs;R9R7R8R4R3A6S1cVsegs;RaSeR8S34SdR8A1R7A2A2R9R5R4A6F_;F_;F_;Fw;Ftp;Fo;Fi;FA;Frho;FJ;").
Proof using .
  intros J rho A i o tp [tr [ms md]] Hn Hemp [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (smatch_drop_empty rho (ax_S A) i o _ Hn Hemp Hsm) as Hsm'.
  split; [exact Hsm'|]. split; [exact HMI|]. split; [unfold axwf in Hwf |- *; cbn; exact Hwf|]. split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  cbn [drop_obj_at set_objs ss_objs]. intros o2 x Ho2 Hx. exists o2. split; [|exact Hx].
  apply in_app_or in Ho2 as [Ho2|Ho2]; [eapply In_firstn_In; exact Ho2 | eapply In_skipn_In; exact Ho2].
Qed.

End X.
