(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 258 of its 293 lines of code are new or changed and 34 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI0m.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3u.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow DiscoSyms DiscoList DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve ReacDiscoTableObserve_C.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacDiscoTableObserve_M.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve_X.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve_K2.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_observe_c reac_disco_table_observe.
Module DTC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table_c.
Module RDOC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe_c.
Module RDO := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe.
Module TM := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog.ReacDiscoTableObserve_M.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Ltac tobs_regq3 HS HR0 :=
  eapply (k2_reg_same_pi _ _ _ _ _ _ _ _ _ HS HR0);
  [ vm_compute; reflexivity | vm_compute; reflexivity | tobs_ag ].
Lemma seg_K3 : forall c, SegK4 B c -> SegK3 B c.
Proof.
intros c HK regs1 m1 md1 r HP HM H18 H19 H12 HFnd.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63.
pose proof (tp_s0 _ _ HP) as Hs0. pose proof (tp_s63 _ _ HP) as Hs63.
pose proof (tp_Tl _ _ HP) as HTl. pose proof (tp_Gl _ _ HP) as HGl.
pose proof (tp_T1 _ _ HP) as HT1. unfold DTC.tbl_T1 in HT1.
pose proof (proj1 HFnd) as Hrn.
assert (Hr : 0 <= r < 8) by lia.
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
destruct (TM.stage_len (tT c) (tG c) (tow c) (tnow c) r HTl HGl Hr) as (_ & _ & _ & HLD & HLE & _).
pose proof (tobs_env_img c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) as HEI.
pose proof (tobs_regs_ok c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r
  (tm_s0 _ _ _ _ _ _ HM) (tm_s5 _ _ _ _ _ _ HM) (tm_s6 _ _ _ _ _ _ HM) (tm_s8 _ _ _ _ _ _ HM)
  ltac:(lia) ltac:(lia)) as HR0.
assert (B8 : base_val (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) (Some 8%nat) = tt c).
{ cbn [base_val].
  rewrite (tobs_env_reg c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r 8 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM).
  apply unsigned_lit_small. lia. }
assert (B19 : base_val (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) (Some 19%nat) = tt c + 48 * r).
{ cbn [base_val].
  rewrite (tobs_env_reg c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r 19 19%bv eq_refl), H19.
  unfold w64. apply unsigned_lit_small. lia. }
assert (HdG : ed (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) 1 = tG c) by reflexivity.
assert (HdE : ed (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) 2
              = TM.ent (RDO.kD (tT c) (tG c) (tnow c) r) r) by reflexivity.
assert (HdT : ed (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) 0
              = RDO.kD (tT c) (tG c) (tnow c) r) by reflexivity.
assert (Hfam : DTC.u_at (TM.ent (RDO.kD (tT c) (tG c) (tnow c) r) r) 15 1 = RDOC.fam_of (tT c) r).
{ rewrite (TM.u_at_ent (RDO.kD (tT c) (tG c) (tnow c) r) r 15 1 HLD Hr ltac:(lia) ltac:(cbn; lia)).
  destruct (TM.stage_reads (tT c) (tG c) (tow c) (tnow c) r HTl HGl Hr) as (_ & _ & _ & _ & _ & SR & _).
  rewrite SR. reflexivity. }
destruct (tobs_enter B c regs1 m1 md1 (RDO.kD (tT c) (tG c) (tnow c) r) 0x5310 true r 0 HP HM
  ltac:(left; reflexivity) ltac:(rewrite H18; f_equal; lia)
  ltac:(intros _; split; [exact Hr | exact H19])) as [HS SHOK].
unfold cfgB.
paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x5358.
{ lazymatch goal with |- awr_ok ?Ex _ _ _ _ _ _ _ _ =>
    apply (tobs_awr_ent B c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r Ex);
      [ tobs_ag | exact HP | exact B8 | exact B19 | exact Hr ] end. }
lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
  assert (HFa : frame_of (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) (tobs_regions true 0)
    (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) (ms_mem msx))) by exact HFr;
  assert (HGa : mem_grows (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) (ms_mem msx))) by exact HG
end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TBspan.
- (* the sighting's fam byte is zero: no update of the entry *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (HAb : env_agree 64 (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
  rewrite branch_eq_U, U_data1, (ed_at_agree _ _ 1 (tG c) HAb HdG) in Hc.
  rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  assert (HcF : RDO.cF (tT c) (tG c) r = false)
    by (unfold RDO.cF, DTC.s_fam; rewrite Hc; reflexivity).
  assert (HkED : RDO.kE (tT c) (tG c) (tnow c) r = RDO.kD (tT c) (tG c) (tnow c) r)
    by (unfold RDO.kE; rewrite HcF; reflexivity).
  assert (Htf4 : tf4 c r = tf3 c r) by (unfold tf4; rewrite HcF; apply orb_false_r).
  clear HAb.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x5358.
  { lazymatch goal with |- awr_ok ?Ex _ _ _ _ _ _ _ _ =>
      apply (tobs_awr_ent B c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r Ex);
        [ tobs_ag | exact HP | exact B8 | exact B19 | exact Hr ] end. }
  lazymatch type of HFr with frame_of ?Ex _ _ _ =>
    assert (HAr : env_agree 64 (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (HAs : env_agree 64 (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HregH. cbn [ms_mem restrict] in HregH.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as HregE. cbn [ms_mem restrict] in HregE.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := ?mdx |} _ =>
    assert (HM2 : tobs_m B c (ms_regs msx) (ms_mem msx) mdx (RDO.kD (tT c) (tG c) (tnow c) r))
  end.
  { eapply (tobs_exit_ent B LAWS c regs1 m1 md1 (RDO.kD (tT c) (tG c) (tnow c) r) _ _ _ _
      (RDO.kD (tT c) (tG c) (tnow c) r) r HP HM Hr H19).
    - eapply (frame_of_trans _ (tobs_regions true 0) (tobs_regions true 0));
        [reflexivity | exact HFa |].
      eapply (frame_of_agree_skel 64 _ _ (tobs_regions true 0) (tobs_regions true 0));
        [ exact HAr | vm_compute; reflexivity | vm_compute; reflexivity | exact HFr ].
    - eapply mem_grows_trans; [exact HGa | exact HG].
    - exact HJ.
    - exact HregH.
    - exact (bv_at_agree _ _ 8%nat _ HAs eq_refl B8).
    - exact (ed_at_agree _ _ 0 _ HAs HdT).
    - exact HLD.
    - intros i Hi Hni. reflexivity.
    - apply (tobs_ent_bytes_id c (RDO.kD (tT c) (tG c) (tnow c) r) r _ _ Hr HLD HregE).
      + exact (bv_at_agree _ _ 19%nat _ HAs eq_refl B19).
      + exact (ed_at_agree _ _ 2 _ HAs HdE).
    - intros q Hq. cbn in Hq.
      repeat (destruct Hq as [<- | Hq]; [tobs_regq3 HS HR0 |]). destruct Hq. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
    assert (S18 : YK11.getr (ms_regs msx) 18 = w64 (ts c)) by (rewrite <- H18; tobs_regq3 HS HR0) end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
    assert (S19 : YK11.getr (ms_regs msx) 19 = w64 (tt c + 48 * r)) by (rewrite <- H19; tobs_regq3 HS HR0) end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
    assert (S12 : YK11.getr (ms_regs msx) 12 = w64 (Z.b2z (tf4 c r)))
      by (rewrite Htf4, <- H12; tobs_regq3 HS HR0) end.
  pmkst HS.
  exact (HK _ _ _ r HP ltac:(rewrite HkED; exact HM2) S18 S19 S12 HFnd).
- (* the sighting's fam byte is non-zero *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (HAb : env_agree 64 (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
  rewrite branch_eq_U, U_data1, (ed_at_agree _ _ 1 (tG c) HAb HdG) in Hc.
  rewrite U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  clear HAb.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x5358.
  { lazymatch goal with |- awr_ok ?Ex _ _ _ _ _ _ _ _ =>
      apply (tobs_awr_ent B c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r Ex);
        [ tobs_ag | exact HP | exact B8 | exact B19 | exact Hr ] end. }
  lazymatch type of HFr with frame_of ?Ex _ _ _ =>
    assert (HAr : env_agree 64 (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
    assert (HFb : frame_of (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) (tobs_regions true 0)
      (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) (ms_mem msx)));
    [ | assert (HGb : mem_grows (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) (ms_mem msx)))
          by (eapply mem_grows_trans; [exact HGa | exact HG]) ]
  end.
  { eapply (frame_of_trans _ (tobs_regions true 0) (tobs_regions true 0));
      [reflexivity | exact HFa |].
    eapply (frame_of_agree_skel 64 _ _ (tobs_regions true 0) (tobs_regions true 0));
      [ exact HAr | vm_compute; reflexivity | vm_compute; reflexivity | exact HFr ]. }
  clear HF HFr HG HFa HGa HAr.
  psrr_branch_tok RUN BR HS SHOK TBspan.
  + (* the entry's fam byte already agrees: no update *)
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (HAb : env_agree 64 (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
    rewrite branch_eq_U, !U_data1, (ed_at_agree _ _ 2 _ HAb HdE),
      (ed_at_agree _ _ 1 (tG c) HAb HdG), Hfam in Hc0.
    apply Z.eqb_eq in Hc0.
    assert (HcF : RDO.cF (tT c) (tG c) r = false)
      by (unfold RDO.cF, DTC.s_fam; rewrite Hc0, Z.eqb_refl; cbn [negb]; apply andb_false_r).
    assert (HkED : RDO.kE (tT c) (tG c) (tnow c) r = RDO.kD (tT c) (tG c) (tnow c) r)
      by (unfold RDO.kE; rewrite HcF; reflexivity).
    assert (Htf4 : tf4 c r = tf3 c r) by (unfold tf4; rewrite HcF; apply orb_false_r).
    clear HAb.
    paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x5358.
    { lazymatch goal with |- awr_ok ?Ex _ _ _ _ _ _ _ _ =>
        apply (tobs_awr_ent B c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r Ex);
          [ tobs_ag | exact HP | exact B8 | exact B19 | exact Hr ] end. }
    lazymatch type of HFr with frame_of ?Ex _ _ _ =>
      assert (HAr : env_agree 64 (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (HAs : env_agree 64 (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HregH. cbn [ms_mem restrict] in HregH.
    pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as HregE. cbn [ms_mem restrict] in HregE.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := ?mdx |} _ =>
      assert (HM2 : tobs_m B c (ms_regs msx) (ms_mem msx) mdx (RDO.kD (tT c) (tG c) (tnow c) r))
    end.
    { eapply (tobs_exit_ent B LAWS c regs1 m1 md1 (RDO.kD (tT c) (tG c) (tnow c) r) _ _ _ _
        (RDO.kD (tT c) (tG c) (tnow c) r) r HP HM Hr H19).
      - eapply (frame_of_trans _ (tobs_regions true 0) (tobs_regions true 0));
          [reflexivity | exact HFb |].
        eapply (frame_of_agree_skel 64 _ _ (tobs_regions true 0) (tobs_regions true 0));
          [ exact HAr | vm_compute; reflexivity | vm_compute; reflexivity | exact HFr ].
      - eapply mem_grows_trans; [exact HGb | exact HG].
      - exact HJ.
      - exact HregH.
      - exact (bv_at_agree _ _ 8%nat _ HAs eq_refl B8).
      - exact (ed_at_agree _ _ 0 _ HAs HdT).
      - exact HLD.
      - intros i Hi Hni. reflexivity.
      - apply (tobs_ent_bytes_id c (RDO.kD (tT c) (tG c) (tnow c) r) r _ _ Hr HLD HregE).
        + exact (bv_at_agree _ _ 19%nat _ HAs eq_refl B19).
        + exact (ed_at_agree _ _ 2 _ HAs HdE).
      - intros q Hq. cbn in Hq.
        repeat (destruct Hq as [<- | Hq]; [tobs_regq3 HS HR0 |]). destruct Hq. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
      assert (S18 : YK11.getr (ms_regs msx) 18 = w64 (ts c)) by (rewrite <- H18; tobs_regq3 HS HR0) end.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
      assert (S19 : YK11.getr (ms_regs msx) 19 = w64 (tt c + 48 * r)) by (rewrite <- H19; tobs_regq3 HS HR0) end.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
      assert (S12 : YK11.getr (ms_regs msx) 12 = w64 (Z.b2z (tf4 c r)))
        by (rewrite Htf4, <- H12; tobs_regq3 HS HR0) end.
    pmkst HS.
    exact (HK _ _ _ r HP ltac:(rewrite HkED; exact HM2) S18 S19 S12 HFnd).
  + (* the entry's fam byte differs: the store *)
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (HAb : env_agree 64 (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
    rewrite branch_eq_U, !U_data1, (ed_at_agree _ _ 2 _ HAb HdE),
      (ed_at_agree _ _ 1 (tG c) HAb HdG), Hfam in Hc0.
    apply Z.eqb_neq in Hc0.
    assert (HcF : RDO.cF (tT c) (tG c) r = true).
    { unfold RDO.cF, DTC.s_fam. apply andb_true_intro.
      split; apply negb_true_iff; apply Z.eqb_neq; [exact Hc | exact Hc0]. }
    assert (HentE : TM.ent (RDO.kE (tT c) (tG c) (tnow c) r) r
                    = DTC.upd (TM.ent (RDO.kD (tT c) (tG c) (tnow c) r) r) 15 (DTC.sub (tG c) 15 1))
      by (rewrite (TM.ent_kE (tT c) (tG c) (tnow c) r HTl HGl Hr), HcF; reflexivity).
    assert (Htf4 : tf4 c r = true) by (unfold tf4; rewrite HcF; apply orb_true_r).
    clear HAb.
    paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x5358.
    { lazymatch goal with |- awr_ok ?Ex _ _ _ _ _ _ _ _ =>
        apply (tobs_awr_ent B c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r Ex);
          [ tobs_ag | exact HP | exact B8 | exact B19 | exact Hr ] end. }
    lazymatch type of HFr with frame_of ?Ex _ _ _ =>
      assert (HAr : env_agree 64 (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (HAs : env_agree 64 (tobs_env c regs1 (RDO.kD (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HregH. cbn [ms_mem restrict] in HregH.
    pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as HregE. cbn [ms_mem restrict] in HregE.
    prreg HS (12%bv : bv 5) Q12.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := ?mdx |} _ =>
      assert (HM2 : tobs_m B c (ms_regs msx) (ms_mem msx) mdx (RDO.kE (tT c) (tG c) (tnow c) r))
    end.
    { eapply (tobs_exit_ent B LAWS c regs1 m1 md1 (RDO.kD (tT c) (tG c) (tnow c) r) _ _ _ _
        (RDO.kE (tT c) (tG c) (tnow c) r) r HP HM Hr H19).
      - eapply (frame_of_trans _ (tobs_regions true 0) (tobs_regions true 0));
          [reflexivity | exact HFb |].
        eapply (frame_of_agree_skel 64 _ _ (tobs_regions true 0) (tobs_regions true 0));
          [ exact HAr | vm_compute; reflexivity | vm_compute; reflexivity | exact HFr ].
      - eapply mem_grows_trans; [exact HGb | exact HG].
      - exact HJ.
      - exact HregH.
      - exact (bv_at_agree _ _ 8%nat _ HAs eq_refl B8).
      - exact (ed_at_agree _ _ 0 _ HAs HdT).
      - exact HLE.
      - intros i Hi Hni.
        destruct (TM.stage_out (tT c) (tG c) (tow c) (tnow c) r i HTl HGl Hr ltac:(lia) ltac:(lia))
          as (_ & _ & _ & OD & OE & _).
        rewrite OE, OD. reflexivity.
      - apply (tobs_ent_bytes_st c (RDO.kD (tT c) (tG c) (tnow c) r) (RDO.kE (tT c) (tG c) (tnow c) r) r
          _ _ _ 15 Hr HLD HLE ltac:(left; reflexivity) HregE).
        + exact (bv_at_agree _ _ 19%nat _ HAs eq_refl B19).
        + exact (ed_at_agree _ _ 2 _ HAs HdE).
        + exact HGl.
        + cbn [sv_denot]. rewrite dw1_eq, (ed_at_agree _ _ 1 (tG c) HAs HdG). reflexivity.
        + exact HentE.
      - intros q Hq. cbn in Hq.
        repeat (destruct Hq as [<- | Hq]; [tobs_regq3 HS HR0 |]). destruct Hq. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
      assert (S18 : YK11.getr (ms_regs msx) 18 = w64 (ts c)) by (rewrite <- H18; tobs_regq3 HS HR0) end.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
      assert (S19 : YK11.getr (ms_regs msx) 19 = w64 (tt c + 48 * r)) by (rewrite <- H19; tobs_regq3 HS HR0) end.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
      assert (S12 : YK11.getr (ms_regs msx) 12 = w64 (Z.b2z (tf4 c r)));
      [ rewrite Htf4; cbn [Z.b2z]; unfold w64; exact Q12 | ] end.
    pmkst HS.
    exact (HK _ _ _ r HP HM2 S18 S19 S12 HFnd).
Qed.
End h.
End f.
End d.
