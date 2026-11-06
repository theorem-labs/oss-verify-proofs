(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs StepSoundBase StepSoundAlu StepSoundMem Acc StepAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAcc.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step ValP StepB StepA StepM StepAcc.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module StepS.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Theorem sound_all : forall i fi, case_stmt segs OPS i fi.
Proof.
  intros i fi. destruct fi.
  - apply sound_ILui. - apply sound_IAuipc. - apply sound_IJal. - apply sound_IJalr. - apply sound_IBranch.
  - apply sound_ILoad. - apply sound_IStore. - apply sound_IOpImm. - apply sound_IOp. - apply sound_IOpImm32.
  - apply sound_IOp32. - apply sound_IMul. - apply sound_IMul32. - apply sound_IFence. - apply sound_IEcall.
  - apply sound_ILr. - apply sound_ISc. - apply sound_IAmo. - apply sound_IFLoad. - apply sound_IFStore.
  - apply sound_IFmv. - apply sound_IFcvtDS. - apply sound_IFcvtSD. - apply sound_IOther.
Qed.

Theorem step_sound : forall E st ms model it st',
  itab_ok segs it -> st_ok segs OPS E st ms model -> step segs it st = SOk st' ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_ok segs OPS E st' ms' model.
Proof.
  intros E st ms model it st' Hit HS Hstep.
  unfold step in Hstep.
  destruct (PrimInt63.ltb (s_pc st) bit62i) eqn:Hpc; [|discriminate].
  destruct (IMap.find (s_pc st) it) as [fi|] eqn:Hfind; [|discriminate].
  destruct (exec segs fi st) as [st1|why] eqn:Hx; [|discriminate]. injection Hstep as Hst1. subst st1.
  destruct (itab_find segs it (s_pc st) fi Hit Hfind) as (w & Hfetch & [[He Hfi] | (He & i & Hdec & Hof)]).
  - subst fi. cbn in Hx. discriminate.
  - rewrite <- (so_pc _ _ _ _ _ _ HS) in Hfetch.
    rewrite (step_exec segs ms w i Hfetch He Hdec).
    destruct (sound_all i fi E st ms model st' HS Hpc Hof Hx) as (c & m' & Hi & HS').
    rewrite Hi. exists (ms_upd ms c m'). split; [reflexivity | exact HS'].
Qed.

Theorem step_sound_a : forall E st ms model it st',
  itab_ok segs it -> st_ok segs OPS E st ms model -> step segs it st = SOk st' ->
  exists ms' model', Run.mi_account_step segs ms model = MachineOk (ms', model') /\ st_ok segs OPS E st' ms' model'.
Proof.
  intros E st ms model it st' Hit HS Hstep.
  unfold step in Hstep.
  destruct (PrimInt63.ltb (s_pc st) bit62i) eqn:Hpc; [|discriminate].
  destruct (IMap.find (s_pc st) it) as [fi|] eqn:Hfind; [|discriminate].
  destruct (exec segs fi st) as [st1|why] eqn:Hx; [|discriminate]. injection Hstep as Hst1. subst st1.
  destruct (itab_find segs it (s_pc st) fi Hit Hfind) as (w & Hfetch & [[He Hfi] | (He & i & Hdec & Hof)]).
  - subst fi. cbn in Hx. discriminate.
  - rewrite <- (so_pc _ _ _ _ _ _ HS) in Hfetch.
    destruct (sound_all i fi E st ms model st' HS Hpc Hof Hx) as (c & m' & Hi & HS').
    unfold interp_eff in Hi.
    destruct (interp_eff_accesses segs (Sem.exec (Z_to_bv 64 4) i (core_of ms)) (ms_mem ms)) as [report| |] eqn:HR;
      cbn [drop_access_report] in Hi; try discriminate.
    injection Hi as Hv.
    pose proof (exec_acc segs OPS i fi E st ms model st' report HS Hof Hx HR) as RNG.
    pose proof (exec_ops segs fi st st' Hx) as OPSEQ.
    pose proof (so_ops _ _ _ _ _ _ HS') as HO. rewrite OPSEQ in HO. apply (proj1 (ops_hold_insts OPS E _ _ _)) in HO.
    destruct (op_acc OPS (insts E (s_ops st)) (ms_mem (ms_upd ms c m')) model (@accessed_ranges _ report)
                (so_mf _ _ _ _ _ _ HS) HO) as (mo' & HM & HMI & HO').
    { intros a n j Hin Hj. apply (so_cover _ _ _ _ _ _ HS).
      exact (proj1 (Forall_forall _ _) RNG (a, n) Hin j Hj). }
    exists (ms_upd ms c m'), mo'. split.
    + unfold Run.mi_account_step, step_accesses. unfold ms_pc. rewrite Hfetch.
      unfold decode_exec_accesses. rewrite He, Hdec.
      unfold core_of in HR. rewrite HR.
      destruct report as [[c0 m0] acc]. cbn [access_value] in Hv. injection Hv as -> ->.
      cbn [access_value accessed_ranges] in *. rewrite HM. reflexivity.
    + destruct HS' as [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19].
      constructor; try assumption.
      rewrite OPSEQ. apply (proj2 (ops_hold_insts OPS E _ _ _)). exact HO'.
Qed.

Definition stop_keeps (why : stop) : bool :=
  match why with KStopPc | KEcall | KBranch _ _ _ _ | KFuel => true | _ => false end.

Lemma step1_sound : forall E st ms model it stops st',
  itab_ok segs it -> st_ok segs OPS E st ms model -> step1 segs it stops st = SOk st' ->
  exists ms' model', asteps segs ms model ms' model' /\ st_ok segs OPS E st' ms' model'.
Proof.
  intros E st ms model it stops st' Hit HS H. unfold step1 in H.
  destruct (in_stops (s_pc st) stops); [discriminate|].
  destruct (step_sound_a E st ms model it st' Hit HS H) as (ms' & mo' & Hs & HS').
  exists ms', mo'. split; [|exact HS'].
  exact (asteps_one segs ms model ms' mo' (so_svc _ _ _ _ _ _ HS) Hs).
Qed.

Lemma step1_stop : forall it stops st why st', step1 segs it stops st = SStop why st' -> st' = st.
Proof.
  intros it stops st why st' H. unfold step1, step in H.
  destruct (in_stops (s_pc st) stops); [congruence|].
  destruct (PrimInt63.ltb (s_pc st) bit62i); [|congruence].
  destruct (IMap.find (s_pc st) it) as [fi|]; [|congruence].
  destruct (exec segs fi st); congruence.
Qed.

Lemma runP_sound : forall p E st ms model it stops,
  itab_ok segs it -> st_ok segs OPS E st ms model ->
  match runP segs p it stops st with
  | SOk st' => exists ms' model', asteps segs ms model ms' model' /\ st_ok segs OPS E st' ms' model'
  | SStop why st' => exists ms' model', asteps segs ms model ms' model' /\ st_ok segs OPS E st' ms' model'
  end.
Proof.
  induction p as [q IH|q IH|]; intros E st ms model it stops Hit HS; cbn [runP].
  - pose proof (IH E st ms model it stops Hit HS) as H1.
    destruct (runP segs q it stops st) as [st1|why st1]; [|exact H1].
    destruct H1 as (ms1 & mo1 & Hm1 & HS1).
    pose proof (IH E st1 ms1 mo1 it stops Hit HS1) as H2.
    destruct (runP segs q it stops st1) as [st2|why st2].
    + destruct H2 as (ms2 & mo2 & Hm2 & HS2).
      destruct (step1 segs it stops st2) as [st3|why st3] eqn:Hs.
      * destruct (step1_sound E st2 ms2 mo2 it stops st3 Hit HS2 Hs) as (ms3 & mo3 & Hm3 & HS3).
        exists ms3, mo3. split; [|exact HS3].
        eapply asteps_trans; [exact Hm1|]. eapply asteps_trans; [exact Hm2|exact Hm3].
      * apply step1_stop in Hs; subst st3. exists ms2, mo2. split; [eapply asteps_trans; [exact Hm1|exact Hm2] | exact HS2].
    + destruct H2 as (ms2 & mo2 & Hm2 & HS2). exists ms2, mo2. split; [eapply asteps_trans; [exact Hm1|exact Hm2] | exact HS2].
  - pose proof (IH E st ms model it stops Hit HS) as H1.
    destruct (runP segs q it stops st) as [st1|why st1]; [|exact H1].
    destruct H1 as (ms1 & mo1 & Hm1 & HS1).
    pose proof (IH E st1 ms1 mo1 it stops Hit HS1) as H2.
    destruct (runP segs q it stops st1) as [st2|why st2];
      destruct H2 as (ms2 & mo2 & Hm2 & HS2); exists ms2, mo2; split; try exact HS2;
      (eapply asteps_trans; [exact Hm1|exact Hm2]).
  - destruct (step1 segs it stops st) as [st'|why st'] eqn:Hs.
    + exact (step1_sound E st ms model it stops st' Hit HS Hs).
    + apply step1_stop in Hs. subst st'. exists ms, model. split; [apply ast_refl | exact HS].
Qed.

Theorem run_sound : forall E st ms model it stops why st',
  itab_ok segs it -> st_ok segs OPS E st ms model ->
  run segs it stops st = SStop why st' ->
  exists ms' model', asteps segs ms model ms' model' /\ st_ok segs OPS E st' ms' model'.
Proof.
  intros E st ms model it stops why st' Hit HS. unfold run.
  pose proof (runP_sound (2^40)%positive E st ms model it stops Hit HS) as H.
  set (r := runP segs _ it stops st) in H |- *. clearbody r.
  destruct r as [s1|w1 s1]; intros Hr.
  - injection Hr as E1 E2. rewrite <- E2. exact H.
  - injection Hr as E1 E2. rewrite <- E2. exact H.
Qed.

End WithSegs.
End StepS.
