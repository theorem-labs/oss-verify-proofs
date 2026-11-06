(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHWH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHWH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1lV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Lemma sstep_cfg_nonalloc : forall segs ms mo evs st,
(forall x8, ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos) ->
sstep segs (mkCfg ms mo) evs st -> sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs st.
Proof.
intros segs ms mo evs st Hna H.
assert (NS : forall x8 eff, ms_svc_pending ms = Some x8 ->
~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) mo eff).
{ intros x8 eff Hx. apply spurious_refusal_family_on. unfold injected_family_off.
destruct (injected_arm (bv_unsigned (in_sysno (sys_input segs ms x8)))) as [a|] eqn:E; [|reflexivity].
destruct (ia_family a) eqn:F; try reflexivity.
exfalso. exact (Hna x8 Hx (alloc_family_dispatched _ _ E F)). }
inversion H; subst.
- eapply sstep_cfg_instr; eassumption.
- eapply sstep_cfg_instr_fault; eassumption.
- eapply sstep_cfg_instr_unmodeled; eassumption.
- eapply sstep_cfg_syscall; try eassumption. apply NS. assumption.
- eapply sstep_cfg_syscall_materialization_fault; try eassumption. apply NS. assumption.
- eapply sstep_cfg_exit; eassumption.
- eapply sstep_cfg_killed; eassumption.
- eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

Section AdequacyA.

Variable node : Type.
Variable segs : list Segment.
Variable L : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base L segs.

Variable at_node : node -> machine_state -> Prop.

Variable nstep_raw : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit_raw : node -> Model -> word -> Model -> Prop.

Variable nsafe : node -> Model -> Prop.

Variable xinv : Model -> Prop.

Variable is_spin : node -> bool.

Variable rvar : node -> resp -> resp -> Prop.
Hypothesis rvar_refl : forall n r, rvar n r r.

Variable jinv : Model -> (word -> option byte) -> Prop.
Hypothesis jinv_stable : forall mo mo' m m',
vmeq mo mo' -> (forall a, hidden L mo a = true -> m' a = m a) -> jinv mo m -> jinv mo' m'.

Definition cinv (ms : machine_state) (mo : Model) : Prop := xinv mo /\ lv_inv L mo /\ jinv mo (ms_mem ms).

Definition nstepA (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
exists mo1, drift L mo mo1 /\ nstep_raw n mo1 rsp mo' evs.
Definition nexitA (n : node) (mo : Model) (code : word) (mo' : Model) : Prop :=
exists mo1, drift L mo mo1 /\ nexit_raw n mo1 code mo'.

Record node_soundA : Prop := {

nsA_spin_at : forall n msr, is_spin n = true -> at_node n msr ->
ms_svc_pending msr = None /\
RiscvSemantics.step_accesses segs msr = MachineOk (@mkAccessReport machine_state msr []);
nsA_spin_raw : forall n, is_spin n = true ->
(forall mo rsp mo' evs, ~ nstep_raw n mo rsp mo' evs) /\ (forall mo c mo', ~ nexit_raw n mo c mo');

nsA_complete : forall n ms mo evs X, is_spin n = false ->
at_node n (msview L mo ms) -> m_halted mo = None -> cinv ms mo -> nsafe n mo ->
sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs X ->
(exists rsp ms' mo', X = SNext (mkCfg ms' mo') /\ msview L mo' ms' = nret (msview L mo ms) rsp /\
nstep_raw n mo rsp mo' evs /\ cinv ms' mo' /\ m_halted mo' = None)
\/ (exists code mo', X = SNext (mkCfg ms mo') /\ nexit_raw n mo code mo' /\
evs = [ExitEv code (m_fs mo')] /\ m_halted mo' = Some code);

nsA_sound : forall n ms mo rsp mo' evs, is_spin n = false ->
at_node n (msview L mo ms) -> m_halted mo = None -> cinv ms mo -> nsafe n mo ->
nstep_raw n mo rsp mo' evs ->
exists ms' mo2 rsp2, sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs (SNext (mkCfg ms' mo2)) /\
msview L mo2 ms' = nret (msview L mo ms) rsp2 /\
nstep_raw n mo rsp2 mo2 evs /\ msim mo' mo2 /\ rvar n rsp rsp2 /\ m_halted mo2 = None;
nsA_exit : forall n ms mo code mo', is_spin n = false ->
at_node n (msview L mo ms) -> m_halted mo = None -> cinv ms mo -> nsafe n mo ->
nexit_raw n mo code mo' ->
m_halted mo' = Some code /\ sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo'));
nsA_progress : forall n ms mo, is_spin n = false ->
at_node n (msview L mo ms) -> m_halted mo = None -> cinv ms mo -> nsafe n mo ->
(exists rsp mo' evs, nstep_raw n mo rsp mo' evs) \/ (exists code mo', nexit_raw n mo code mo');

nsA_msim : forall n moA moB rsp mo' evs, msim moA moB -> nstep_raw n moA rsp mo' evs ->
exists mo'b, nstep_raw n moB rsp mo'b evs /\ msim mo' mo'b;
nsA_msim_exit : forall n moA moB code mo', msim moA moB -> nexit_raw n moA code mo' ->
exists mo'b, nexit_raw n moB code mo'b /\ msim mo' mo'b;

nsA_xinv_drift : forall mo mo', drift L mo mo' -> xinv mo -> xinv mo';
nsA_safe_drift : forall n mo mo', drift L mo mo' -> nsafe n mo -> nsafe n mo'
}.

Fixpoint tset {R} (t : itree node R) (mo : Model) : TSet :=
match t with
| Ret _ => t_nil
| Vis n k => fun tr =>
tr = []
\/ (exists mo1 rsp mo' evs, drift L mo mo1 /\ nstep_raw n mo1 rsp mo' evs /\ t_emit evs (tset (k rsp) mo') tr)
\/ (exists mo1 code mo', drift L mo mo1 /\ nexit_raw n mo1 code mo' /\ is_prefix tr [ExitEv code (m_fs mo')])
end.

Fixpoint tobliv {R} (t : itree node R) : Prop :=
match t with
| Ret _ => True
| Vis n k => (forall r r', rvar n r r' -> k r = k r') /\ (forall r, tobliv (k r))
end.

Lemma t_emit_mono : forall evs (T T' : TSet) tr, (forall tr, T tr -> T' tr) -> t_emit evs T tr -> t_emit evs T' tr.
Proof.
intros evs T T' tr H [Hp|(tr' & -> & HT)]; [left; exact Hp|]. right. exists tr'. split; [reflexivity| apply H, HT].
Qed.

Section Sound.
Hypothesis NS : node_soundA.

Lemma cinv_drift : forall ms ms' mo mo', drift L mo mo' ->
(forall a, hidden L mo a = true -> ms_mem ms' a = ms_mem ms a) -> cinv ms mo -> cinv ms' mo'.
Proof.
intros ms ms' mo mo' Hd Hm (HX & HI & HJ). split; [exact (nsA_xinv_drift NS _ _ Hd HX)|].
split; [exact (lv_inv_drift L _ _ HI Hd)|]. eapply jinv_stable; [eapply drift_vmeq; exact Hd| exact Hm| exact HJ].
Qed.

Import Exc.

End Sound.

Inductive tset_ind {R} : itree node R -> Model -> list event -> Prop :=
| ti_nil : forall t mo, tset_ind t mo []
| ti_part : forall n k mo mo1 rsp mo' evs tr,
drift L mo mo1 -> nstep_raw n mo1 rsp mo' evs -> is_prefix tr evs -> tset_ind (Vis n k) mo tr
| ti_step : forall n k mo mo1 rsp mo' evs tr,
drift L mo mo1 -> nstep_raw n mo1 rsp mo' evs -> tset_ind (k rsp) mo' tr -> tset_ind (Vis n k) mo (evs ++ tr)
| ti_exit : forall n (k : resp -> itree node R) mo mo1 code mo' tr,
drift L mo mo1 -> nexit_raw n mo1 code mo' -> is_prefix tr [ExitEv code (m_fs mo')] -> tset_ind (Vis n k) mo tr.

Fixpoint tset0 {R} (t : itree node R) (mo : Model) : TSet :=
match t with
| Ret _ => t_nil
| Vis n k => fun tr =>
tr = []
\/ (exists rsp mo' evs, nstep_raw n mo rsp mo' evs /\ t_emit evs (tset0 (k rsp) mo') tr)
\/ (exists code mo', nexit_raw n mo code mo' /\ is_prefix tr [ExitEv code (m_fs mo')])
end.

Section Sound0.
Hypothesis NS : node_soundA.

End Sound0.

End AdequacyA.

Arguments cinv L xinv jinv ms mo /.
Arguments tobliv {node} rvar {R} t.
Arguments nstepA {node} L nstep_raw n mo rsp mo' evs /.
Arguments nexitA {node} L nexit_raw n mo code mo' /.
Arguments tset {node} L nstep_raw nexit_raw {R} t mo tr.
Arguments tset0 {node} nstep_raw nexit_raw {R} t mo tr.
