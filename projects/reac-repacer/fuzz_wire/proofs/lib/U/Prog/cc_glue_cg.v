(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_wire: the cut-free (SRcf) twins of lib/U/Prog/cc_glue.v's four run lemmas (ccg_run_fp,
   ccg_runA, ccg_runQ, ccg_runN), as libreac/fuzz_decode's released lib/U/Prog/crt_glue_cg.v (25e3d17bdb5) has them
   for crt_glue.v; the proofs are cc_glue.v's with evt_SR_canon / kb_run replaced by evt_SRcf_canon / kb_run_cf. The
   rest of cc_glue.v (the list lemmas and the frame invariant cc_mid with its lemmas) never mentions SR, so the cf walk
   of check_copy (check_copy_cg.v) uses it as it is. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Contract KindBGlue Img0 SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require MState Mem Frame Exec Regs6ss RegisterBridge
Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import cc_glue LLVMFuzzerTestOneInput_cfb.
Import ListNotations.
Local Open Scope Z_scope.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.

Lemma ccg_run_fp_cf : forall regs pc mem md
    (K : bvmap 5 word -> bvmap 5 word -> word -> bv 32 -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt (ms_segs B) (fun ms => exists R F pc' fc mem',
      ms = MState.MS R F pc' fc None mem' (seg_rom (ms_segs B)) /\ K R F pc' fc mem')
    (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom (ms_segs B))) ->
  (forall R F pc' fc mem' regs', K R F pc' fc mem' -> (forall r, getr regs' r = getr R r) ->
     SRcf B (mkCfg (@mkst (mkFP F fc) regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md K P Hh Hl HE HK.
  eapply (evt_SRcf_canon B (mkst regs pc mem (seg_rom (ms_segs B))) _ md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & (R & F & pc' & fc & mem' & -> & HKR) & Heq).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ _ _ regs' HKR). apply kb_getr_eqv. exact HR.
Qed.

Lemma ccg_runA_cf : ms_segs B = rsegs -> forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs Q (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall ms, Q ms -> ms_svc_pending ms = None /\ ms_resv ms = None /\ ms_fregs ms = fp_regs /\
     ms_fcsr ms = fp_csr /\ ms_rom ms = seg_rom rsegs) ->
  (forall ms regs', Q ms -> (forall r, getr regs' r = getr (ms_regs ms) r) ->
     SRcf B (mkCfg (mkst regs' (ms_pc_val ms) (ms_mem ms) (seg_rom (ms_segs B))) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros HS regs pc mem md Q P Hh Hl HE HQ HK. rewrite <- HS in HE, HQ.
  apply (kb_run_cf B regs pc mem md
    (fun R pc' mem' => Q (MState.MS R fp_regs pc' fp_csr None mem' (seg_rom (ms_segs B)))) P Hh Hl).
  - eapply Exec.evt_mono; [exact HE|]. intros ms Hms. destruct (HQ ms Hms) as (E1 & E2 & E3 & E4 & E5).
    assert (Ems : ms = MState.MS (ms_regs ms) fp_regs (ms_pc_val ms) fp_csr None (ms_mem ms) (seg_rom (ms_segs B)))
      by (destruct ms as [r f p sv rv fc m ro]; cbn in E1, E2, E3, E4, E5; subst; reflexivity).
    exists (ms_regs ms), (ms_pc_val ms), (ms_mem ms). split; [exact Ems | rewrite <- Ems; exact Hms].
  - intros R pc' mem' regs' HR Hg. exact (HK _ regs' HR Hg).
Qed.

Lemma ccg_runQ_cf : ms_segs B = rsegs -> forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs Q (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall ms, Q ms -> ms_svc_pending ms = None /\ ms_resv ms = None /\ ms_rom ms = seg_rom rsegs) ->
  (forall ms regs', Q ms -> (forall r, getr regs' r = getr (ms_regs ms) r) ->
     SRcf B (mkCfg (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (ms_pc_val ms) (ms_mem ms)
       (seg_rom (ms_segs B))) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros HS regs pc mem md Q P Hh Hl HE HQ HK. rewrite <- HS in HE, HQ.
  apply (ccg_run_fp_cf regs pc mem md
    (fun R F pc' fc mem' => Q (MState.MS R F pc' fc None mem' (seg_rom (ms_segs B)))) P Hh Hl).
  - eapply Exec.evt_mono; [exact HE|]. intros ms Hms. destruct (HQ ms Hms) as (E1 & E2 & E3).
    assert (Ems : ms = MState.MS (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) None (ms_mem ms)
      (seg_rom (ms_segs B))) by (destruct ms as [r f p sv rv fc m ro]; cbn in E1, E2, E3; subst; reflexivity).
    exists (ms_regs ms), (ms_fregs ms), (ms_pc_val ms), (ms_fcsr ms), (ms_mem ms).
    split; [exact Ems | rewrite <- Ems; exact Hms].
  - intros R F pc' fc mem' regs' HR Hg. exact (HK _ regs' HR Hg).
Qed.

Lemma ccg_runN_cf : ms_segs B = rsegs -> forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (rmk regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> ms_svc_pending ms = None /\ ms_resv ms = None /\ ms_rom ms = seg_rom rsegs) ->
  (forall ms s0 regs', Q s0 -> ms_rel rsegs ms s0 -> ro_same rsegs mem (ms_mem ms) ->
     (forall r, getr regs' r = getr (ms_regs s0) r) ->
     SRcf B (mkCfg (@mkst (mkFP (ms_fregs s0) (ms_fcsr s0)) regs' (ms_pc_val s0) (ms_mem ms)
       (seg_rom (ms_segs B))) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros HS regs pc mem md Q P Hh Hl Hro HE HQ HK.
  apply (ccg_runQ_cf HS regs pc mem md (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s))
    P Hh Hl).
  - exact (evt_normalize rsegs Q (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs) ccg_wx Hro HE).
  - intros ms (s0 & HQs & Hrel & _). destruct (HQ s0 HQs) as (E1 & E2 & E3).
    destruct Hrel as (_ & _ & _ & Es & Er & _ & Eo & _). rewrite Es, Er, Eo. auto.
  - intros ms regs' (s0 & HQs & Hrel & Hsame) Hg.
    pose proof Hrel as (Er & Ef & Ep & _ & _ & Ec & _).
    rewrite Ef, Ep, Ec. apply (HK ms s0 regs' HQs Hrel Hsame). intros r. rewrite Hg, Er. reflexivity.
Qed.

End G.
