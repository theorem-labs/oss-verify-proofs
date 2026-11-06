(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Ceiling VmGap.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct BackingAlgebra MainExport MainFactsAsan A0Img MainEntry A0Handoff A0LZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ BridgeLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout PEnv LJ APrim ASec AQuar AHeap AHeap2 AHeapInit AHeapInst AVaOf ALinkPg ALinkVm ALink AFsEnv AFakeRep AFakeInst AFakeInit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAI Require Import ALinkInit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS SeamA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZACB Require Import ACInstB.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7G Require Import GlueKit GlueAllocKit GlueAllocLay GlueAllocEnv GlueAllocRep GlueAllocFs GlueAllocDepot GlueAllocBase.
Import ListNotations.
Open Scope Z_scope.

Section Run.
Context {HC : HasCeiling}.
Variables (V : nat -> Z) (sp : word) (fs : Fs.Fs) (mo : Model).
Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
Hypothesis AM : amodel V sp fs mo.
Hypothesis PSP : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = bv_unsigned sp.
Hypothesis CEILsp : alloc_ceiling = bv_unsigned sp - 8388608.
Hypothesis SP184 : bv_unsigned sp + 184 <= 2^47.

#[using="sp PSP CEILsp"] Lemma CEIL_V : alloc_ceiling = 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608.
Proof. rewrite CEILsp, <- PSP. reflexivity. Qed.

Definition AO_run : alayout_ok (AL_of V) := alayout_ok_of V HP CEIL_V.
Definition FI_run : fs_if := FI_B (AL_of V) AO_run.
Definition Bs_run : vmbase := Bs_of V mo.
#[using="sp CEILsp SP184"] Lemma SP0S_run : alloc_ceiling + 2^23 + 184 <= 2^47.
Proof. rewrite CEILsp. change (2^23) with 8388608. lia. Qed.
#[using="Type"] Lemma FSEI_run : forall m, thread_env (al_thread (AL_of V)) m ->
  fs_tls_env (at_thr (al_thread (AL_of V))) A0_DTV A0_TLSB (al_dtls (AL_of V)) (al_fsb (AL_of V)) m -> FSENV FI_run m.
Proof. intros m TE FT. split; assumption. Qed.
Definition AI_run : am_if FI_run := AI_B (AL_of V) (E_of V) FI_run Bs_run AO_run eq_refl SP0S_run FSEI_run.

#[using="fs AM"] Theorem AC_run : am_contracts FI_run AI_run (JA FI_run AI_run).
Proof.
  destruct (space_facts V HP) as (_ & _ & SAL). destruct (vb_consts V mo) as (VS & VU & VG & VN).
  exact (AC_B (AL_of V) (E_of V) FI_run Bs_run AO_run eq_refl SP0S_run (base_ok_of V sp fs mo HP AM CEILsp) VS SAL ltac:(cbn; lia) FSEI_run
           (reg_base V sp fs mo HP AM) (parr_base V sp fs mo HP AM) VU VG VN).
Qed.

#[using="Type"] Lemma AMS_run : forall lo hi, a0_static lo hi -> am_static FI_run AI_run lo hi.  Proof. intros lo hi H. exact H. Qed.
#[using="Type"] Lemma ASL_run : forall lo hi, am_static FI_run AI_run lo hi -> a0_static lo hi.  Proof. intros lo hi H. exact H. Qed.

#[using="fs AM"] Theorem alloc_init_run : forall (w : bool) (m : mem),
  Forall (mfact_ok asegs V (mrestrict (a0_H0 V mo) m)) (asan_mem_facts ++ asan_mem_facts_w w) ->
  (forall x : word, ashadow (bv_unsigned x) -> a0_H0 V mo x = false -> mrestrict (a0_H0 V mo) m x <> None) ->
  exists (s : aps FI_run AI_run) (st : fsstate FI_run),
    RHEAP_A FI_run AI_run s [] (mrestrict (a0_H0 V mo) m) /\ RFAKE FI_run st (mrestrict (a0_H0 V mo) m)
    /\ am_ghost FI_run AI_run s = (a0_H0 V mo, a0_P0 V)
    /\ fs_live FI_run st = [] /\ am_nsec FI_run AI_run s = 0
    /\ am_vm FI_run AI_run s (m_vm (perase (a0_P0 V) mo)).
Proof.
  intros w m HMw SHV. set (mr := mrestrict (a0_H0 V mo) m) in *.
  pose proof (proj1 (Forall_app _ _ _) HMw) as [HM _].
  destruct (depot_side w) as (ND0 & TB0 & LH0).
  destruct (RHEAP_B_init (AL_of V) (E_of V) (a0_H0 V mo) (a0_P0 V) [depot_h w] (depot_tot w) mr AO_run
              (RPRIM_of V AO_run mr HM) (RSEC_of V AO_run mr HM) (poison_env_init V mr HM) (thread_env_init V mr HM)
              ltac:(intros x XB HX; apply SHV; [unfold in_shadow_band in XB; unfold ashadow; lia| exact HX])
              (quar_gq_init V mr HM) (quar_tq_init V mr HM) (quar_mtx_init V mr HM) (quar_env_init V mr HM)
              (RDEPOT_init V mr w HMw) ND0 TB0 LH0
              (thread_env2_init V mr HM) (hooks_env_init V mr HM) (trace_env_init V mr HM) (alloc_env_init V mr HM) (ia_cells_init V mr HM)
              (fs_tls_env_init V AO_run mr HM)) as (HR & GH & NS).
  exists (bs0 (a0_H0 V mo) (a0_P0 V) [depot_h w] (depot_tot w)), fst0.
  split; [exact HR|]. split; [exact (RFAKE_init V AO_run mr HM)|]. split; [exact GH|]. split; [reflexivity|]. split; [exact NS|].
  cbn [am_vm AI_run AI_B]. apply LINKvm_of_LINK.
  exact (link_init V sp fs mo AM CEILsp (al_space (AL_of V))).
Qed.
End Run.
