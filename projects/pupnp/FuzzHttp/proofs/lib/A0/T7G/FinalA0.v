(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Agree Ceiling RunWord InitStack Nodes.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Realize CeilP.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import ShapeP0.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsAsan A0Img MainEntry A0Handoff ShapeAlg SpinAlg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ BridgeLZ NodesLZ NodesLZSound.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import A0LZ AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS SeamA0 A0Prog TopA0 ShapeInst.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Printf_lib F_printf_iface Stdio_iface F_printf_diag Exit RDriverA_kit RDriverA_ctx RDriverA_main RDriverA_iface RF_mainA_A MainA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7G Require Import GlueKit GlueA0_T GlueA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require IcptICS.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require PZDef.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7G Require GluePZ.
Import ListNotations.
Open Scope Z_scope.

Lemma srz_of_top : forall c T, Realize.realizes asegs c T -> SpinAlg.srealizes asegs c T.
Proof.
  intros c T H. induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exact (SpinAlg.srz_node asegs c I evs nx T i0 Hnode IH).
  - exact (SpinAlg.srz_halt asegs c Hh).
  - exact (SpinAlg.srz_conseq asegs c T T' IH Heq).
Qed.

Lemma hmain_K_A0 : forall inp en ms mo, A0Handoff.H_MAIN_A0 inp en ms mo ->
  hmain_model_facts inp mo /\ exists mo', meq mo mo' /\ minv mo' /\ m_halted mo' = None.
Proof.
  intros inp en ms mo HM. unfold A0Handoff.H_MAIN_A0 in HM.
  destruct (a0_main_lz en inp ms mo HM) as (w & V & m & LZ). cbv zeta in LZ. destruct LZ as (HF & _ & _ & _ & _ & AM).
  split.
  - constructor; [exact (am_fds _ _ _ _ AM)| exact (am_fs _ _ _ _ AM)| exact (am_halted _ _ _ _ AM)|].
    destruct (am_tid _ _ _ _ AM) as [NN _]. destruct (m_tid mo) as [t|]; [exists t; reflexivity| contradiction].
  - exists (strip_vm (perase (a0_P0 V) mo)).
    pose proof (lf_minv _ _ _ _ _ HF) as (M & _). pose proof (lf_halt _ _ _ _ _ HF) as Hh.
    split; [unfold meq; rewrite m_fds_strip_vm, m_fs_strip_vm, m_fds_perase, m_fs_perase; split; reflexivity|].
    split; [exact M| rewrite m_halted_strip_vm, m_halted_perase; exact Hh].
Qed.

Section FinalA0.

  Local Notation PZ := PZDef.PZ.
  Local Notation PZ_agree := GluePZ.PZ_agree.
  Local Notation PZ_INIT := GluePZ.PZ_INIT.

  Hypothesis INST : forall (HC : HasCeiling) (HG : HasGuard) (V : nat -> Z) inp en ms mo,
    valid_input inp -> valid_entry imgA0 en inp -> alloc_ceiling = LO (en_sp en) -> amain_at_V V en inp ms mo ->
    exists (FI : fs_if) (AI : am_if FI),
      (forall lo hi, a0_static lo hi -> am_static FI AI lo hi)
      /\ am_contracts FI AI (JA FI AI)
      /\ fuzz_one_stmtA FI AI (JA FI AI) PZ
      /\ alloc_init_stmt FI AI V (en_sp en) (in_fs inp) mo.

  #[using="INST"] Theorem main_A0 : MAIN A0Handoff.H_MAIN_A0 RSVA.
  Proof.
    intros inp en c VI VE AM. unfold at_main, A0Handoff.H_MAIN_A0 in AM.
    destruct (amain_at_split _ _ _ _ AM) as [V AMV].
    assert (VSP : valid_sp (en_sp en)).
    { pose proof (valid_input_va_size _ VI) as Hsv48. destruct en as [sp brk mb dr]. rewrite (valid_entry_sv48 _ _ _ Hsv48) in VE. cbn [imgA0] in VE. cbn. exact (proj1 VE). }
    set (HC := CeilP.ceilP (en_sp en) VSP).
    set (HG := run_guard (Z_to_bv 64 (V 45%nat)) (Z_to_bv 64 0)).
    assert (CEIL : @alloc_ceiling HC = LO (en_sp en)) by (unfold LO; exact (CeilP.ceilP_eq (en_sp en) VSP)).
    destruct (INST HC HG V inp en (cfg_ms c) (cfg_model c) VI VE CEIL AMV) as (FI & AI & AMS & AC & FZ & AINIT).
    destruct (IcptICS.ics_all HC) as (MCI & MSI & SNI & RDF & RDB & FWF & FWB & VPF & VPB & VFF & VFB & FPS & FP4 & FPB & DT).
    pose proof (@main_realizesA HC HG FI AI PZ (@H_MAIN_G HG V (en_sp en) (in_fs inp) (cfg_model c)) AMS AC MCI MSI SNI RDF RDB FWF FWB VPF VPB VFF VFB FPS FP4 FPB DT PZ_agree FZ
                  (@glue_A0 HC HG FI AI PZ V (en_sp en) (in_fs inp) (cfg_model c) AINIT PZ_INIT)) as M.
    apply (M inp en c VI VE). unfold at_main, H_MAIN_HC, H_MAIN_G. split; [split; [split; [exact AMV|] | repeat split] | exact CEIL].
    destruct AMV as (w & m & Hms & _ & _ & HMF & _).
    pose proof (proj1 (Forall_app _ _ _) HMF) as [HMFc _].
    mf V m HMFc (MRo (ZLit 6318512) 8 (ZV 45)) G.
    rewrite Hms. cbn [ms_mem MS]. unfold ssp_guard. exact G.
  Qed.
End FinalA0.

Section Closed.
  Local Notation PZ := PZDef.PZ.
  Hypothesis INST : forall (HC : HasCeiling) (HG : HasGuard) (V : nat -> Z) inp en ms mo,
    valid_input inp -> valid_entry imgA0 en inp -> alloc_ceiling = LO (en_sp en) -> amain_at_V V en inp ms mo ->
    exists (FI : fs_if) (AI : am_if FI),
      (forall lo hi, a0_static lo hi -> am_static FI AI lo hi)
      /\ am_contracts FI AI (JA FI AI)
      /\ fuzz_one_stmtA FI AI (JA FI AI) PZ
      /\ alloc_init_stmt FI AI V (en_sp en) (in_fs inp) mo.

  #[using="INST"] Theorem fuzzhttp_asan_error_free_final : strong_universal_error_free_T_scfg ACFG imgP0 imgA0.
  Proof.
    refine (fuzzhttp_asan_error_free_of A0Handoff.H_MAIN_A0 RSVA (fun segs c T => SpinAlg.srealizes segs c T) _ _ _ _ _ (main_A0 INST)
              (shape_of_hmain A0Handoff.H_MAIN_A0 RSVA hmain_K_A0)).
    - intros segs c T T' H E. exact (SpinAlg.srz_conseq segs c T T' H E).
    - intros segs c T H. induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
        [exact (SpinAlg.srz_node segs c I evs nx T i0 Hnode IH)| exact (SpinAlg.srz_halt segs c Hh)| exact (SpinAlg.srz_conseq segs c T T' IH Heq)].
    - intros segs c T H tr. exact (SpinAlg.srealizes_obs_iff segs c T H tr).
    - intros segs c T H. exact (SpinAlg.srealizes_no_error segs c T H).
    - intros inp en VI VE Tm TN HM. exact (a0_handoff inp en VI VE Tm TN HM).
  Qed.
End Closed.
