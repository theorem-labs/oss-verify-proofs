(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 172 of its 207 lines of code are new or changed and 34 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve_X ReacDiscoTableObserve_Q.
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
Lemma tq_n_br : forall (n : Z), 0 <= n <= 8 ->
  branch_taken BC_LT (Z_to_bv 64 n) (Z_to_bv 64 8) = (n <? 8).
Proof. intros n Hn. cbn [branch_taken]. apply bv_lts_small; lia. Qed.
Lemma tq_ov_br : forall E (T : list byte), ed E 0 = T ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SData 0 388 4))) (sv_denot E (SLit 0)) = (DTC.ov_of T =? 0).
Proof.
intros E T Hed. rewrite branch_eq_U, U_lit by lia. rewrite U_SExt. cbv iota.
pose proof (data_word_range E 0 388 4 ltac:(cbn; lia)) as R.
unfold U. cbn [sv_denot]. rewrite unsigned_lit_small by (cbn in R; lia).
change (data_word E 0 388 4) with (DTC.u_at (ed E 0) 388 4) in *. rewrite Hed in *.
change (2 ^ (8 * Z.of_N 4) - 1) with (2 ^ 32 - 1) in R. change (2 ^ Z.of_N 32) with (2 ^ 32).
unfold DTC.ov_of, DTC.s32_at. rewrite (Z.mod_small (DTC.u_at T 388 4) (2 ^ 32)) by lia.
unfold zcanon, M64, bv_swrap. change (bv_wrap 32 ?x) with (x mod 2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
pose proof (Z.mod_pos_bound (DTC.u_at T 388 4 + 2 ^ 31) (2 ^ 32) ltac:(lia)) as Hm.
set (s := (DTC.u_at T 388 4 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) in *.
destruct (Z.eq_dec s 0) as [E0 | N0].
- rewrite E0. reflexivity.
- rewrite (proj2 (Z.eqb_neq s 0) N0). apply Z.eqb_neq. intros Hs.
  destruct (Z_lt_le_dec s 0) as [Hl | Hg].
  + rewrite <- (Z_mod_plus_full s 1 (2 ^ 64)) in Hs. rewrite Z.mod_small in Hs by lia. lia.
  + rewrite Z.mod_small in Hs by lia. lia.
Qed.
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
Ltac tq_rg HS HR0 c regs1 Tc l RG :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (RG : forall q : Z, In q l -> YK11.getr (ms_regs msx) (Z_to_bv 5 q) = YK11.getr regs1 (Z_to_bv 5 q))
  by (intros q Hq; cbn in Hq;
      repeat (destruct Hq as [<- | Hq];
        [ eapply (tobs_reg_same c regs1 Tc 0 _ _ _ _ _ HS HR0);
          [ vm_compute; reflexivity | vm_compute; reflexivity
          | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity] ] |]);
      destruct Hq) end.
Ltac tq_exit HMx HP B8 HFr HG HJ Tc' HTl' :=
  lazymatch type of HMx with tobs_m _ ?c ?r1 ?mm1 ?d1 ?Tc =>
  lazymatch type of HFr with frame_of ?Ex _ _ _ =>
  lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm2 ?d2 _ =>
  apply (tobs_exit_run B LAWS c r1 mm1 d1 Tc Ex false 0 0 _ mm2 d2 Tc' HP HMx B8
    ltac:(discriminate) HFr HG HJ HTl') end end end.
Lemma seg_none : forall c, SegNew B c -> SegSeq B c -> SegRet B c -> SegNone B c.
Proof.
intros c HNew HSeq HRet regs1 m1 md1 HP HM H18 H23 Hno.
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
pose proof (tp_Tl _ _ HP) as HTl. pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63.
pose proof (tp_T1 _ _ HP) as HT1. unfold DTC.tbl_T1 in HT1.
assert (B8 : base_val (tobs_env c regs1 (tT c) 0) (Some 8%nat) = tt c).
{ cbn [base_val]. rewrite (tobs_env_reg c regs1 (tT c) 0 8 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM).
  apply unsigned_lit_small. lia. }
pose proof (tobs_regs_ok c regs1 (tT c) 0 (tm_s0 _ _ _ _ _ _ HM) (tm_s5 _ _ _ _ _ _ HM) (tm_s6 _ _ _ _ _ _ HM)
  (tm_s8 _ _ _ _ _ _ HM) ltac:(lia) ltac:(lia)) as HR0.
pose proof (tobs_env_img c regs1 (tT c) 0) as HEI.
assert (H18' : YK11.getr regs1 18 = w64 (ts c - 0)) by (rewrite H18; f_equal; lia).
assert (HL1 : length (DTC.upd (tT c) 388 (Z_to_le_bytes 4 1)) = 400%nat)
  by (rewrite RDO.upd_len; [exact HTl | lia | rewrite tq_le_len, HTl; cbn; lia]).
destruct (tobs_enter B c regs1 m1 md1 (tT c) 0x53c4 false 0 0 HP HM ltac:(left; reflexivity) H18'
  ltac:(discriminate)) as [HS SHOK].
unfold cfgB.
paj_run_tok RUN HS HJ SHOK TBspan.
{ exact (tobs_awr B c _ false 0 0 HP B8 ltac:(discriminate)). }
tq_rg HS HR0 c regs1 (tT c) [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 27] RGA.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as Hreg. cbn [ms_mem restrict] in Hreg.
assert (HMA : tobs_m B c (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) (tT c)).
{ tq_exit HM HP B8 HFr HG HJ (tT c) HTl.
  - intros; reflexivity.
  - intros i Hi. exact (tq_hdr_same _ _ (tT c) (tt c) Hreg eq_refl B8 i Hi).
  - discriminate.
  - intros q Hq. apply RGA. cbn in Hq |- *. tauto. }
clear Hreg HFr HG.
rename ms into msA. rename mat into matA.
psrr_branch_tok RUN BR HS SHOK TBspan.
- assert (Hn8 : DTC.n_of (tT c) < 8).
  { cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite (tobs_env_reg c regs1 (tT c) 0 23 23%bv eq_refl), H23 in Hc.
    unfold w64 in Hc. rewrite unsigned_lit_small, Z.add_0_r in Hc by lia. rewrite tq_n_br in Hc by lia.
    apply Z.ltb_lt. exact Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x53f0.
  { exact (tobs_awr B c _ false 0 0 HP B8 ltac:(discriminate)). }
  rewrite ?wvb_collapse in HJ.
  pmkst HS.
  tq_rg HS HR0 c regs1 (tT c) [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 27] RG.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as Hreg. cbn [ms_mem restrict] in Hreg.
  assert (HM2 : tobs_m B c (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) (tT c)).
  { tq_exit HMA HP B8 HFr HG HJ (tT c) HTl.
    - intros; reflexivity.
    - intros i Hi. exact (tq_hdr_same _ _ (tT c) (tt c) Hreg eq_refl B8 i Hi).
    - discriminate.
    - intros q Hq. cbn in Hq. rewrite (RG q ltac:(cbn; lia)), (RGA q ltac:(cbn; lia)). reflexivity. }
  exact (HNew (ms_regs ms) (ms_mem ms) _ HP HM2 (eq_trans (RG 18 ltac:(cbn; lia)) H18)
    (eq_trans (RG 23 ltac:(cbn; lia)) H23) Hno Hn8).
- assert (Hn8 : 8 <= DTC.n_of (tT c)).
  { cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite (tobs_env_reg c regs1 (tT c) 0 23 23%bv eq_refl), H23 in Hc.
    unfold w64 in Hc. rewrite unsigned_lit_small, Z.add_0_r in Hc by lia. rewrite tq_n_br in Hc by lia.
    apply Z.ltb_ge. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK TBspan.
  { exact (tobs_awr B c _ false 0 0 HP B8 ltac:(discriminate)). }
  rewrite ?wvb_collapse in HJ.
  tq_rg HS HR0 c regs1 (tT c) [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 27] RGB.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as Hreg. cbn [ms_mem restrict] in Hreg.
  assert (HMB : tobs_m B c (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) (tT c)).
  { tq_exit HMA HP B8 HFr HG HJ (tT c) HTl.
    - intros; reflexivity.
    - intros i Hi. exact (tq_hdr_same _ _ (tT c) (tt c) Hreg eq_refl B8 i Hi).
    - discriminate.
    - intros q Hq. cbn in Hq. rewrite (RGB q ltac:(cbn; lia)), (RGA q ltac:(cbn; lia)). reflexivity. }
  clear Hreg HFr HG.
  rename ms into msB. rename mat into matB.
  psrr_branch_tok RUN BR HS SHOK TBspan.
  + rewrite (tq_ov_br _ (tT c)) in Hc; [|reflexivity].
    apply Z.eqb_eq in Hc. rename Hc into Hov.
    paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x55d0.
    { exact (tobs_awr B c _ false 0 0 HP B8 ltac:(discriminate)). }
    rewrite ?wvb_collapse in HJ.
    pmkst HS.
    tq_rg HS HR0 c regs1 (tT c) [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 27] RG.
    prreg HS (10%bv : bv 5) R10.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as Hreg. cbn [ms_mem restrict] in Hreg.
    assert (HM3 : tobs_m B c (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1)
      (DTC.upd (tT c) 388 (Z_to_le_bytes 4 1))).
    { tq_exit HMB HP B8 HFr HG HJ (DTC.upd (tT c) 388 (Z_to_le_bytes 4 1)) HL1.
      - intros i Hi Hn _. apply TM.upd_nth_out; rewrite ?tq_le_len; lia.
      - intros i Hi. apply (tq_hdr_store _ _ _ 388 1 (tT c) (tt c) Hreg (or_introl eq_refl) HTl eq_refl B8);
          [reflexivity | exact Hi].
      - discriminate.
      - intros q Hq. cbn in Hq. rewrite (RG q ltac:(cbn; lia)), (RGB q ltac:(cbn; lia)). reflexivity. }
    assert (Hmod : RDOC.observe_model (tT c) (tG c) (tow c) (tnow c)
      (DTC.upd (DTC.upd (tT c) 388 (Z_to_le_bytes 4 1)) 392
        (Z_to_le_bytes 4 (DTC.seq_of (DTC.upd (tT c) 388 (Z_to_le_bytes 4 1)) + 1))) 0).
    { pose proof (TM.model_full (tT c) (tG c) (tow c) (tnow c) Hno ltac:(lia)) as HMF.
      unfold RDOC.observe_full in HMF. rewrite (proj2 (Z.eqb_eq _ _) Hov) in HMF. cbn [fst snd] in HMF.
      assert (Hsq : DTC.seq_of (DTC.upd (tT c) 388 (Z_to_le_bytes 4 1)) = DTC.seq_of (tT c)).
      { unfold DTC.seq_of, DTC.u_at. rewrite RDO.sub_upd_other by (rewrite ?tq_le_len, ?HTl; cbn; lia). reflexivity. }
      rewrite Hsq. exact HMF. }
    exact (HSeq (ms_regs ms) (ms_mem ms) _ _ 0 0 HP HM3 ltac:(left; reflexivity)
      (eq_trans (RG 18 ltac:(cbn; lia)) H18') R10 Hmod).
  + rewrite (tq_ov_br _ (tT c)) in Hc; [|reflexivity].
    apply Z.eqb_neq in Hc. rename Hc into Hov.
    paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x55f0.
    { exact (tobs_awr B c _ false 0 0 HP B8 ltac:(discriminate)). }
    rewrite ?wvb_collapse in HJ.
    pmkst HS.
    tq_rg HS HR0 c regs1 (tT c) [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 27] RG.
    prreg HS (10%bv : bv 5) R10.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as Hreg. cbn [ms_mem restrict] in Hreg.
    assert (HM3 : tobs_m B c (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) (tT c)).
    { tq_exit HMB HP B8 HFr HG HJ (tT c) HTl.
      - intros; reflexivity.
      - intros i Hi. exact (tq_hdr_same _ _ (tT c) (tt c) Hreg eq_refl B8 i Hi).
      - discriminate.
      - intros q Hq. cbn in Hq. rewrite (RG q ltac:(cbn; lia)), (RGB q ltac:(cbn; lia)). reflexivity. }
    assert (Hmod : RDOC.observe_model (tT c) (tG c) (tow c) (tnow c) (tT c) 0).
    { pose proof (TM.model_full (tT c) (tG c) (tow c) (tnow c) Hno ltac:(lia)) as HMF.
      unfold RDOC.observe_full in HMF. rewrite (proj2 (Z.eqb_neq _ _) Hov) in HMF. cbn [fst snd] in HMF.
      exact HMF. }
    exact (HRet (ms_regs ms) (ms_mem ms) _ _ 0 0 HP HM3 ltac:(left; reflexivity)
      (eq_trans (RG 18 ltac:(cbn; lia)) H18') R10 Hmod).
Qed.
End h.
End f.
End d.
