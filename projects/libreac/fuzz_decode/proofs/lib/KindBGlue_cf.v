From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0i YK15 YM06 YM06_cf YO0d YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Contract KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require MState Exec Regs6ss RegisterBridge.
Import ListNotations.
Local Open Scope Z_scope.

(* Cut-free (SR_cfv) twins of Contract.evt_SR_canon and KindBGlue.kb_run: an instruction run without system calls
   reaches no budget refusal and keeps the model. *)

Section K.
Context {fx : YK11.FPState}.

Lemma evt_SR_cfv : forall segs ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q ms -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', Q ms' -> SR_cfv segs (mkCfg ms' md) P) -> SR_cfv segs (mkCfg ms md) P.
Proof using.
  intros segs ms Q md P [final [Hs HQ]] Hh Hl K.
  exact (SR_cfv_msteps segs ms final md P Hh Hl (lib_msteps_frame segs ms final Hs) (K final HQ)).
Qed.

Lemma evt_SR_cfv_canon : forall segs ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SR_cfv segs (mkCfg ms' md) P) ->
  SR_cfv segs (mkCfg ms md) P.
Proof using.
  intros segs ms Q md P H Hh Hl K.
  exact (evt_SR_cfv segs ms _ md P (RegisterBridge.canonical_contract_transport segs Q ms H) Hh Hl K).
Qed.

Variable B : malloc_syms.
Let segs := ms_segs B.

Lemma kb_run_cf : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt segs (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom segs) /\ K R pc' mem')
    (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom segs)) ->
  (forall R pc' mem' regs', K R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     SR_cfv segs (mkCfg (mkst regs' pc' mem' (seg_rom segs)) md) P) ->
  SR_cfv segs (mkCfg (mkst regs pc mem (seg_rom segs)) md) P.
Proof using.
  intros regs pc mem md K P Hh Hl HE HK.
  eapply (evt_SR_cfv_canon segs (mkst regs pc mem (seg_rom segs)) _ md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & (R & pc' & mem' & -> & HKR) & Heq).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' HKR). apply kb_getr_eqv. exact HR.
Qed.
End K.
