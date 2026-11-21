(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Glue/Nodes.v: the ecall, set_tid_address and exit nodes restated over BudgetWit.Rzb.rzb, each with its budget check *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (node_set_tid refutes the allocation numbers by search, 215 being one of them now; fx_node_set_tid_b reads the third field of FX.State.mfacts, the far-end reader; rzb_silent_all takes RomBase.sys_rob after node_ok, which fx_node_set_tid_b proves by RomBase.sys_rob_memfree and memfree_96). *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs StepSoundBase StepSound PlanSound Acc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit Require Import Rzb PlanSoundB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require RomBase.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS PlanSB FXN.
Open Scope Z_scope.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module FXNB.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Lemma step_ecall : forall ms w,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true ->
  RiscvSemantics.step segs ms = MachineOk (pend ms (ms_reg ms 17)).
Proof.
  intros ms w Hf He.
  unfold RiscvSemantics.step, step_accesses. unfold ms_pc. rewrite Hf.
  unfold drop_access_report, decode_exec_accesses. rewrite He. reflexivity.
Qed.

Lemma so_reg_get : forall E T ms model r,
  st_ok segs OPS E T ms model -> r5_eqb r X0 = false ->
  reg_get (ms_regs ms) (reg_of_r5 r) = den E (getr T r).
Proof.
  intros E T ms model r HS Hr.
  pose proof (so_regs _ _ _ _ _ _ HS r) as H. unfold rget in H. cbn [c_regs] in H.
  rewrite is_x0_reg_of_r5, Hr in H. exact H.
Qed.

Lemma so_a7 : forall E T ms model, st_ok segs OPS E T ms model -> ms_reg ms 17 = den E (getr T X17).
Proof. intros E T ms model HS. exact (so_reg_get E T ms model X17 HS eq_refl). Qed.
Lemma so_a0 : forall E T ms model, st_ok segs OPS E T ms model -> ms_gpr ms 0 = den E (getr T X10).
Proof. intros E T ms model HS. exact (so_reg_get E T ms model X10 HS eq_refl). Qed.
Lemma so_a1 : forall E T ms model, st_ok segs OPS E T ms model -> ms_gpr ms 1 = den E (getr T X11).
Proof. intros E T ms model HS. exact (so_reg_get E T ms model X11 HS eq_refl). Qed.
Lemma so_a2 : forall E T ms model, st_ok segs OPS E T ms model -> ms_gpr ms 2 = den E (getr T X12).
Proof. intros E T ms model HS. exact (so_reg_get E T ms model X12 HS eq_refl). Qed.
Lemma so_a3 : forall E T ms model, st_ok segs OPS E T ms model -> ms_gpr ms 3 = den E (getr T X13).
Proof. intros E T ms model HS. exact (so_reg_get E T ms model X13 HS eq_refl). Qed.
Lemma so_a4 : forall E T ms model, st_ok segs OPS E T ms model -> ms_gpr ms 4 = den E (getr T X14).
Proof. intros E T ms model HS. exact (so_reg_get E T ms model X14 HS eq_refl). Qed.
Lemma so_a5 : forall E T ms model, st_ok segs OPS E T ms model -> ms_gpr ms 5 = den E (getr T X15).
Proof. intros E T ms model HS. exact (so_reg_get E T ms model X15 HS eq_refl). Qed.

Lemma ecall_pend : forall E T ms model,
  st_ok segs OPS E T ms model -> ecall_at segs (s_pc T) ->
  RiscvSemantics.step segs ms = MachineOk (pend ms (den E (getr T X17))).
Proof.
  intros E T ms model HS (w & Hf & He).
  rewrite <- (so_pc _ _ _ _ _ _ HS) in Hf.
  rewrite (step_ecall ms w Hf He). rewrite (so_a7 E T ms model HS). reflexivity.
Qed.

Lemma rzb_pend : forall E T ms model K,
  st_ok segs OPS E T ms model -> ecall_at segs (s_pc T) ->
  rzb segs (mkCfg (pend ms (den E (getr T X17))) model) K ->
  rzb segs (mkCfg ms model) K.
Proof.
  intros E T ms model K HS Hat Hk.

  pose proof (ecall_pend E T ms model HS Hat) as Hst. destruct Hat as (w & Hf & He).
  rewrite <- (so_pc _ _ _ _ _ _ HS) in Hf.
  eapply (rzb_astep segs); [exact (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) | exact (so_svc _ _ _ _ _ _ HS)
                  | exact (Acc.account_step_ecall segs ms w _ model Hf He Hst) | exact Hk].
Qed.

Lemma asteps_plain : forall ms mo ms' mo', m_vm_lazy mo = [] -> ShapeAcc.asteps segs ms mo ms' mo' -> mo' = mo.
Proof.
  intros ms mo ms' mo' Hl H. induction H as [ms mo | ms mo ms1 mo1 ms2 mo2 Hsvc Hstep Hms IH]; [reflexivity|].
  rewrite (mi_account_step_no_lazy segs ms mo Hl) in Hstep.
  destruct (RiscvSemantics.step segs ms); try discriminate. injection Hstep as _ <-. exact (IH Hl).
Qed.

Lemma sys_acc : forall E os' (m' : word -> option byte) model' acc,
  op_minv OPS model' -> ops_hold OPS E os' m' model' ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> op_cov OPS (insts E os') (bv_unsigned a + j)) ->
  materialize_model_accesses model' acc = Some (matz model' acc) /\ op_minv OPS (matz model' acc) /\
  ops_hold OPS E os' m' (matz model' acc).
Proof.
  intros E os' m' model' acc Hmi Hops Hcov.
  destruct (op_acc OPS (insts E os') m' model' acc Hmi (proj1 (ops_hold_insts OPS E os' m' model') Hops) Hcov) as (mo2 & Hm & Hmi2 & Hops2).
  unfold matz. rewrite Hm. split; [reflexivity|]. split; [exact Hmi2|]. exact (proj2 (ops_hold_insts OPS E os' m' mo2) Hops2).
Qed.

Lemma matz_nil : forall mo, op_minv OPS mo -> materialize_model_accesses mo [] = Some (matz mo []).
Proof.
  intros mo Hmi. destruct (op_acc OPS [] (fun _ => None) mo [] Hmi (Forall_nil _)) as (mo2 & Hm & _).
  - intros a n j [].
  - unfold matz. rewrite Hm. reflexivity.
Qed.

Lemma mat_nil : forall mo, materialize_model_accesses mo [] = Some mo.
Proof. intros mo. unfold materialize_model_accesses, materialize_accesses. cbn. destruct mo as [fd [maps lz mat] io fs proc lim tm]; reflexivity. Qed.

Lemma cov_keep : forall E os os' a,
  (forall o, In o os -> (exists z, op_cov1 OPS (op_id o) (map (den E) (op_args o)) z) -> In o os') ->
  op_cov OPS (insts E os) a -> op_cov OPS (insts E os') a.
Proof.
  intros E os os' a Hk [C0|C1]; [left; exact C0| right].
  unfold insts in *. apply Exists_exists in C1 as (oi & Hin & Hc). apply in_map_iff in Hin as (o & <- & Ho). cbn [fst snd] in Hc.
  apply Exists_exists. exists (op_id o, map (den E) (op_args o)). split; [|exact Hc].
  apply in_map_iff. exists o. split; [reflexivity|]. apply (Hk o Ho). exists a. exact Hc.
Qed.

Lemma account_step_mat : forall ms mo ms' mo',
  mi_account_step segs ms mo = MachineOk (ms', mo') -> exists acc, materialize_model_accesses mo acc = Some mo'.
Proof.
  intros ms mo ms' mo' H. unfold mi_account_step in H.
  destruct (step_accesses segs ms) as [report| |]; try discriminate.
  destruct (materialize_model_accesses mo (@accessed_ranges _ report)) as [mo1|] eqn:M; [|discriminate].
  injection H as _ <-. exists (@accessed_ranges _ report). exact M.
Qed.

Lemma asteps_stable : forall MI ms mo ms' mo', mstable MI -> ShapeAcc.asteps segs ms mo ms' mo' -> MI mo -> MI mo'.
Proof.
  intros MI ms mo ms' mo' HMI H. induction H as [ms mo | ms mo ms1 mo1 ms2 mo2 Hsvc Hstep Hms IH]; intros Hmo; [exact Hmo|].
  destruct (account_step_mat _ _ _ _ Hstep) as [acc M]. exact (IH (HMI _ _ _ Hmo M)).
Qed.

Lemma mat_fds : forall mo acc mo', materialize_model_accesses mo acc = Some mo' -> m_fds mo' = m_fds mo.
Proof. intros mo acc mo' M. destruct (materialize_model_accesses_frame _ _ _ M) as (F & _). unfold m_fds. rewrite F. reflexivity. Qed.

Lemma st_ok_model : forall E T ms mo mo',
  st_ok segs OPS E T ms mo -> op_minv OPS mo' -> ops_hold OPS E (s_ops T) (ms_mem ms) mo' -> st_ok segs OPS E T ms mo'.
Proof. intros E T ms mo mo' [] Hmi Hops. split; assumption. Qed.

Lemma rzb_silent_all : forall c (I : Type) (nx : I -> config) (i0 : I) (K : TSet),
  node_ok segs c I (fun _ => []) nx -> RomBase.sys_rob segs c ->
  budget_ok segs c ->
  (forall i, rzb segs (nx i) K) ->
  rzb segs c K.
Proof.
  intros c I nx i0 K Hnode Hrob Hb Hk.
  apply (rzb_conseq segs c (t_alt (fun _ : I => t_emit [] K))).
  - apply (rzb_node segs c I (fun _ => []) nx (fun _ => K) i0 Hnode Hrob Hb). exact Hk.
  - assert (HK0 : K []) by (eapply rzb_nonempty; exact (Hk i0)).
    intros tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq K HK0 tr) Hi).
    + intros H. exists i0. exact (proj2 (t_emit_nil_eq K HK0 tr) H).
Qed.

End WithSegs.
Section WithSegs3.
Variable segs : list Segment.
Variable OPS : optable.

Hypothesis PL : plain_table OPS.

Lemma node_set_tid : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96 -> m_tid model = None ->
  node_ok segs (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Htid.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs ms x8)) = 96) by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hlazy' : forall t, m_vm_lazy (with_tid t model) = []) by (intros t; exact Hlazy).
  apply two_sided_lift.
  { apply (step_nonspur_nonalloc segs ms model x8 Hsvc). rewrite Hno. unfold alloc_mark_sysnos.
    (* 215 entered [Run.alloc_mark_sysnos] at index 1, so a pattern with a fixed
       number of branches names the wrong syscalls.  Refute by search, the idiom
       Glue/Nodes.v:451 and Common/ShapeAlg.v:21 already use. *)
    intros Hin; repeat (destruct Hin as [H|Hin]; [discriminate H|]); destruct Hin. }
  split.
  - intros [t Ht]. cbn [proj1_sig].
    rewrite <- (apply_effect_ret_only ms t).
    apply (sstep_syscall segs ms model x8 (mkEffect t [] []) (with_tid t model) (with_tid t model) []);
      [exact Hh | exact Hsvc | exact (set_tid_dispatch_ok _ _ _ Hno' Htid Ht)
      | rewrite m_halted_with_tid; exact Hh
      | apply materialize_model_accesses_no_lazy; apply Hlazy' ].
  - intros e st Hss. inversion Hss; subst;
      try congruence;
      match goal with
      | Hsv : ms_svc_pending ms = Some ?y |- _ =>
          assert (Ey : y = x8) by congruence; subst y
      end.
    +
      match goal with Hsp : syscall_spec _ _ (Ok ?eff ?m' ?evs) |- _ =>
        destruct (set_tid_dispatch_ok_inv _ _ _ _ _ Hno' Htid Hsp) as (t & Ht & -> & -> & ->) end.
      match goal with Hm : materialize_model_accesses _ _ = Some ?m'' |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy' t)) in Hm; injection Hm as <- end.
      exists (exist _ t Ht). split; [reflexivity|]. cbn [proj1_sig]. rewrite apply_effect_ret_only. reflexivity.
    +
      match goal with Hsp : syscall_spec _ _ (Ok ?eff ?m' ?evs) |- _ =>
        destruct (set_tid_dispatch_ok_inv _ _ _ _ _ Hno' Htid Hsp) as (t & Ht & -> & -> & ->) end.
      match goal with Hm : materialize_model_accesses _ _ = None |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy' t)) in Hm; discriminate Hm end.
    +
      match goal with Hsp : syscall_spec _ _ (Ok ?eff ?m' ?evs) |- _ =>
        destruct (set_tid_dispatch_ok_inv _ _ _ _ _ Hno' Htid Hsp) as (t & Ht & -> & -> & ->) end.
      match goal with Hm : m_halted (with_tid _ _) = Some _ |- _ => rewrite m_halted_with_tid in Hm; congruence end.
    +
      match goal with Hsp : syscall_spec _ _ (Ok ?eff ?m' ?evs) |- _ =>
        destruct (set_tid_dispatch_ok_inv _ _ _ _ _ Hno' Htid Hsp) as (t & Ht & -> & -> & ->) end.
      match goal with Hm : m_killed (with_tid _ _) = Some _ |- _ =>
        rewrite m_killed_with_tid, (m_killed_of_m_halted_none _ Hh) in Hm; discriminate Hm end.
    +
      exfalso. eapply set_tid_dispatch_no_unmodeled; [exact Hno' | exact Htid | eassumption].
Qed.

Lemma env_set_ext : forall E n w, env_ext n E (env_set E n w).
Proof.
  intros E n w. split; [reflexivity|]. intros k Hk. cbn [env_set ev eg]. split; [|reflexivity].
  destruct (PrimInt63.eqb k n) eqn:Hkn; [|reflexivity].
  apply Uint63.eqb_correct in Hkn. subst. lia.
Qed.

Lemma env_set_same : forall E n w, ev (env_set E n w) n = w.
Proof. intros. cbn [env_set ev]. rewrite Uint63.eqb_refl. reflexivity. Qed.

Theorem fx_node_set_tid_b : forall T T',
  post_set_tid T = Some T' ->
  (forall E mem model tid, ops_hold OPS E (s_ops T) mem model -> ops_hold OPS E (s_ops T) mem (with_tid tid model)) ->
  forall (K : TSet) E ms model,
    st_ok segs OPS E T ms model -> ecall_at segs (s_pc T) -> m_tid model = None ->
    (forall E' ms' model' tid,
        env_ext (s_next T) E E' -> st_ok segs OPS E' T' ms' model' ->
        0 < bv_unsigned tid < PID_MAX_ENVELOPE -> model' = with_tid tid model ->
        rzb segs (mkCfg ms' model') K) ->
    rzb segs (mkCfg ms model) K.
Proof.
  intros T T' Hpost Hpure K E ms model HS Hat Htid Hk.
  unfold post_set_tid in Hpost.
  destruct (getr T X17) as [no| | | | | | | | | |] eqn:H17; try discriminate.
  destruct (weqb no (wlit 96) && PrimInt63.ltb (s_pc T) bit62i && PrimInt63.ltb 0 (s_next T) && svars_below (s_next T) T) eqn:Hc;
    [|discriminate].
  injection Hpost as HT'.
  apply andb_prop in Hc as [Hc Hsv]. apply andb_prop in Hc as [Hc Hn]. apply andb_prop in Hc as [Hno Hpc].
  apply weqb_eq in Hno. subst no.
  assert (Hx8 : den E (getr T X17) = Z_to_bv 64 96) by (rewrite H17; reflexivity).
  assert (H96 : bv_unsigned (den E (getr T X17)) = 96) by (rewrite Hx8; reflexivity).
  eapply rzb_pend; [exact HS | exact Hat |].
  (* [FX.State.mfacts] gained [mf_reader] at the revision (the write path reads
     the far-end reader), so it is three fields now, not two. *)
  pose proof (plain_mf OPS _ PL (so_mf _ _ _ _ _ _ HS)) as [Hh Hlazy Hrdr].
  assert (Hrob : RomBase.sys_rob segs (mkCfg (pend ms (den E (getr T X17))) model)).
  { apply (RomBase.sys_rob_memfree segs (pend ms (den E (getr T X17))) model (den E (getr T X17)) eq_refl).
    rewrite H96. exact RomBase.memfree_96. }
  apply (rzb_silent_all segs _ tid_I _ (exist _ (Z_to_bv 64 1) tid1_ok) K
           (node_set_tid (pend ms (den E (getr T X17))) model _ Hh Hlazy eq_refl H96 Htid)
           Hrob
           (budget_ok_num segs (pend ms (den E (getr T X17))) model _ 96 eq_refl H96 eq_refl)).
  intros [t Ht]. cbn [proj1_sig].
  change (advance_past_svc (set_gpr0 (pend ms (den E (getr T X17))) t)) with (svc_post ms (den E (getr T X17)) t).
  apply (Hk (env_set E (s_next T) t) _ _ t (env_set_ext E (s_next T) t)); [|exact Ht|reflexivity].
  subst T'.
  assert (HS' : st_ok segs OPS (env_set E (s_next T) t) T ms model).
  { apply (st_ok_env segs OPS (s_next T) E); [apply env_set_ext| |exact Hsv|exact HS].
    apply Uint63.ltb_spec in Hn. exact Hn. }
  apply (st_ok_svc_return segs OPS _ T ms model); try assumption.
  - cbn [den]. rewrite env_set_same, wbv_wzero. apply bv_add_0_r. reflexivity.
  - constructor; [|constructor]. cbn [fact_holds]. rewrite env_set_same, !wlit_ok.
    change (to_Z 1%uint63) with 1. change (to_Z tid_max) with 4194303. unfold PID_MAX_ENVELOPE in Ht. lia.
  - apply (plain_minv OPS _ PL). split;
      [rewrite m_halted_with_tid; exact Hh | exact Hlazy | exact Hrdr].
  - apply Hpure. exact (so_ops _ _ _ _ _ _ HS').
Qed.

Lemma bv_and_255_small : forall (x : word), bv_unsigned x < 256 -> bv_and x (Z_to_bv 64 255) = x.
Proof.
  intros x Hx. apply bv_eq. rewrite bv_and_unsigned, Z_to_bv_small by (unfold bv_modulus; lia).
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  apply Z.mod_small. pose proof (bv_unsigned_in_range _ x). lia.
Qed.

Theorem fx_node_exit_b : forall T c,
  exit_code T = Some c ->
  forall E ms model,
    st_ok segs OPS E T ms model -> ecall_at segs (s_pc T) ->
    rzb segs (mkCfg ms model) (t_exit (wbv c) (m_fs model)).
Proof.
  intros T c Hcode E ms model HS Hat.
  unfold exit_code in Hcode.
  destruct (getr T X17) as [no| | | | | | | | | |] eqn:H17; try discriminate.
  destruct (getr T X10) as [c0| | | | | | | | | |] eqn:H10; try discriminate.
  destruct ((weqb no (wlit 93) || weqb no (wlit 94)) && wltu c0 (wlit 256)) eqn:Hc; [|discriminate].
  injection Hcode as ->.
  apply andb_prop in Hc as [Hno Hlt].
  eapply rzb_pend; [exact HS | exact Hat |].
  pose proof (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) as Hh.
  assert (Ha0 : ms_gpr (pend ms (den E (getr T X17))) 0 = wbv c).
  { rewrite pend_gpr, (so_a0 segs OPS E T ms model HS), H10. reflexivity. }
  assert (Hsmall : bv_unsigned (wbv c) < 256).
  { rewrite wbv_unsigned. pose proof (wltu_w2Z c (wlit 256)) as W. rewrite Hlt, wlit_ok in W.
    change (to_Z 256%uint63) with 256 in W. symmetry in W. apply Z.ltb_lt in W. exact W. }
  rewrite <- (bv_and_255_small (wbv c) Hsmall), <- Ha0.
  apply (rzb_exit segs (pend ms (den E (getr T X17))) model (den E (getr T X17)) Hh eq_refl).
  rewrite H17. unfold is_exit_no. cbn [den].
  destruct (weqb no (wlit 93)) eqn:E93.
  - left. apply weqb_eq in E93. subst. reflexivity.
  - right. cbn in Hno. apply weqb_eq in Hno. subst. reflexivity.
Qed.

End WithSegs3.
End FXNB.
