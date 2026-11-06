(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs StepSoundBase StepSound PlanSound Acc.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module FXN.

Definition pend (ms : machine_state) (x8 : word) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := Some x8; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.

Definition svc_post (ms : machine_state) (x8 ret : word) : machine_state :=
  advance_past_svc (set_gpr0 (pend ms x8) ret).

Lemma pend_gpr : forall ms x8 i, ms_gpr (pend ms x8) i = ms_gpr ms i.
Proof. reflexivity. Qed.
Lemma pend_mem : forall ms x8, ms_mem (pend ms x8) = ms_mem ms.
Proof. reflexivity. Qed.
Lemma pend_svc : forall ms x8, ms_svc_pending (pend ms x8) = Some x8.
Proof. reflexivity. Qed.

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

Lemma rz_pend : forall E T ms model K,
  st_ok segs OPS E T ms model -> ecall_at segs (s_pc T) ->
  realizes segs (mkCfg (pend ms (den E (getr T X17))) model) K ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros E T ms model K HS Hat Hk.

  pose proof (ecall_pend E T ms model HS Hat) as Hst. destruct Hat as (w & Hf & He).
  rewrite <- (so_pc _ _ _ _ _ _ HS) in Hf.
  eapply (ShapeAcc.rz_astep segs); [exact (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) | exact (so_svc _ _ _ _ _ _ HS)
                  | exact (Acc.account_step_ecall segs ms w _ model Hf He Hst) | exact Hk].
Qed.

Lemma asteps_plain : forall ms mo ms' mo', m_vm_lazy mo = [] -> ShapeAcc.asteps segs ms mo ms' mo' -> mo' = mo.
Proof.
  intros ms mo ms' mo' Hl H. induction H as [ms mo | ms mo ms1 mo1 ms2 mo2 Hsvc Hstep Hms IH]; [reflexivity|].
  rewrite (mi_account_step_no_lazy segs ms mo Hl) in Hstep.
  destruct (RiscvSemantics.step segs ms); try discriminate. injection Hstep as _ <-. exact (IH Hl).
Qed.

Definition matz (mo : Model) (acc : list (word * nat)) : Model :=
  match materialize_model_accesses mo acc with Some x => x | None => mo end.

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

Definition mstable (MI : Model -> Prop) : Prop :=
  forall mo acc mo', MI mo -> materialize_model_accesses mo acc = Some mo' -> MI mo'.

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

Lemma rz_silent_all : forall c (I : Type) (nx : I -> config) (i0 : I) (K : TSet),
  node_ok segs c I (fun _ => []) nx ->
  (forall i, realizes segs (nx i) K) ->
  realizes segs c K.
Proof.
  intros c I nx i0 K Hnode Hk.
  apply (rz_conseq segs c (t_alt (fun _ : I => t_emit [] K))).
  - apply (rz_node segs c I (fun _ => []) nx (fun _ => K) i0 Hnode). exact Hk.
  - assert (HK0 : K []) by (eapply realizes_nonempty; exact (Hk i0)).
    intros tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq K HK0 tr) Hi).
    + intros H. exists i0. exact (proj2 (t_emit_nil_eq K HK0 tr) H).
Qed.

End WithSegs.

Fixpoint slot_vars_below (n : int) (s : slot) : bool :=
  match s with [] => true | c :: s' => vars_below n (c_v c) && slot_vars_below n s' end.

Definition region_vars_below (n : int) (r : region) : bool :=
  vars_below n (rg_hi r) && IMap.forallb (fun _ gr => slot_vars_below n (g_cells gr)) (rg_cells r).

Definition fact_vars_below (n : int) (f : fact) : bool :=
  match f with
  | FRange k _ _ | FAlign k _ => PrimInt63.ltb k n
  | FULt a b | FULe a b | FEq a b | FNe a b | FSLt a b | FSLe a b => vars_below n a && vars_below n b
  end.

Definition resv_vars_below (n : int) (rv : sresv) : bool :=
  match rv with RAddr a => vars_below n a | _ => true end.

Definition rf_allb {A} (p : A -> bool) (x : rf A) : bool := forallb p (rf_to_list x).

Definition svars_below (n : int) (st : sstate) : bool :=
  rf_allb (vars_below n) (s_rf st) && rf_allb (vars_below n) (s_ff st) && resv_vars_below n (s_resv st)
  && IMap.forallb (fun k r => PrimInt63.ltb k n && region_vars_below n r) (s_regs st)
  && forallb (fact_vars_below n) (s_facts st)
  && forallb (fun o => forallb (vars_below n) (op_args o)) (s_ops st).

Lemma rf_allb_get : forall A (p : A -> bool) x, rf_allb p x = true -> forall r, p (rf_get x r) = true.
Proof.
  intros A p x H r. unfold rf_allb, rf_to_list in H.
  repeat (apply andb_prop in H; destruct H as [? H]).
  destruct r; cbn [rf_get]; assumption.
Qed.

Lemma forallb_In : forall A (p : A -> bool) l x, forallb p l = true -> In x l -> p x = true.
Proof. intros A p l x H Hin. rewrite forallb_forall in H. exact (H x Hin). Qed.

Lemma slot_vars_below_In : forall n s c, slot_vars_below n s = true -> In c s -> vars_below n (c_v c) = true.
Proof.
  induction s as [|c0 s IH]; intros c H Hin; [destruct Hin|].
  cbn [slot_vars_below] in H. apply andb_prop in H as [H1 H2].
  destruct Hin as [<-|Hin]; [exact H1 | exact (IH c H2 Hin)].
Qed.

Lemma den_env_below : forall n E E' v, env_ext n E E' -> vars_below n v = true -> den E' v = den E v.
Proof.
  intros n E E' v [Hb Hk]. induction v; intros Hv; cbn [vars_below] in Hv; cbn [den];
    repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end.
  - reflexivity.
  - apply Uint63.ltb_spec in Hv. rewrite (proj1 (Hk _ Hv)). reflexivity.
  - rewrite IHv1, IHv2 by assumption. reflexivity.
  - rewrite IHv1, IHv2 by assumption. reflexivity.
  - rewrite IHv1, IHv2 by assumption. reflexivity.
  - rewrite IHv1, IHv2 by assumption. reflexivity.
  - rewrite IHv by assumption. reflexivity.
  - rewrite IHv1, IHv2 by assumption. reflexivity.
  - rewrite IHv by assumption. rewrite Hb. reflexivity.
  - apply Uint63.ltb_spec in Hv. rewrite (proj2 (Hk _ Hv)). reflexivity.
  - rewrite IHv by assumption. reflexivity.
Qed.

Lemma env_ext_refl' : forall n E, env_ext n E E.
Proof. intros n E. split; [reflexivity|]. intros; split; reflexivity. Qed.

Lemma env_ext_trans' : forall n n' E E' E'', to_Z n <= to_Z n' -> env_ext n E E' -> env_ext n' E' E'' -> env_ext n E E''.
Proof.
  intros n n' E E' E'' Hle [Hb1 H1] [Hb2 H2]. split; [congruence|].
  intros k Hk. destruct (H1 k Hk) as [A1 B1]. destruct (H2 k ltac:(lia)) as [A2 B2]. split; congruence.
Qed.

Section EnvChange.
Variable segs : list Segment.
Variable OPS : optable.
Variables (n : int) (E E' : env).
Hypothesis HX : env_ext n E E'.

Let Hden : forall v, vars_below n v = true -> den E' v = den E v :=
  fun v Hv => den_env_below n E E' v HX Hv.

Lemma ev_env : forall k, PrimInt63.ltb k n = true -> ev E' k = ev E k.
Proof. intros k Hk. apply (proj1 (proj2 HX k (proj1 (Uint63.ltb_spec _ _) Hk))). Qed.
Lemma eg_env : forall k, PrimInt63.ltb k n = true -> eg E' k = eg E k.
Proof. intros k Hk. apply (proj2 (proj2 HX k (proj1 (Uint63.ltb_spec _ _) Hk))). Qed.

Lemma fact_holds_env : forall f, fact_vars_below n f = true -> fact_holds E f -> fact_holds E' f.
Proof.
  intros f Hf H. destruct f; cbn [fact_vars_below] in Hf; cbn [fact_holds] in *;
    try (apply andb_prop in Hf as [Ha Hb]; rewrite (Hden _ Ha), (Hden _ Hb); exact H);
    rewrite (ev_env _ Hf); exact H.
Qed.

Lemma hiZ_env : forall r, region_vars_below n r = true -> hiZ E' r = hiZ E r.
Proof. intros r Hr. apply andb_prop in Hr as [Hh _]. unfold hiZ. rewrite (Hden _ Hh). reflexivity. Qed.

Lemma bg_byte_env : forall k r o, PrimInt63.ltb k n = true -> bg_byte segs E' k r o = bg_byte segs E k r o.
Proof.
  intros k r o Hk. unfold bg_byte. destruct (rg_bg r); try reflexivity.
  - rewrite (eg_env _ Hk). reflexivity.
  - rewrite (proj1 HX). reflexivity.
Qed.

Lemma region_ok_env : forall priv m k r,
  PrimInt63.ltb k n = true -> region_vars_below n r = true ->
  region_ok segs priv E m k r -> region_ok segs priv E' m k r.
Proof.
  intros priv m k r Hk Hr HR.
  pose proof (hiZ_env r Hr) as Hhi. apply andb_prop in Hr as [Hh Hc].
  destruct HR as [Rbst Rrange Rvalid Rcells Rin Rbg].
  assert (Hcv : forall g gr c, IMap.find g (rg_cells r) = Some gr -> In c (g_cells gr) -> den E' (c_v c) = den E (c_v c)).
  { intros g gr c Hg Hin. apply Hden. eapply slot_vars_below_In; [|exact Hin].
    exact (proj1 (IMap.forallb_spec _ _ Rbst) Hc g gr Hg). }
  split.
  - exact Rbst.
  - rewrite (ev_env _ Hk), Hhi. exact Rrange.
  - rewrite (ev_env _ Hk), Hhi. exact Rvalid.
  - intros g gr Hg. rewrite (ev_env _ Hk). destruct (Rcells g gr Hg) as [Hs Hf]. split; [exact Hs|].
    apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hf c Hin) as [H1 [H2 [H3 H4]]].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    intros i Hi. rewrite (Hcv g gr c Hg Hin). exact (H4 i Hi).
  - rewrite Hhi. exact Rin.
  - intros o H1 H2 H3. rewrite (bg_byte_env k r o Hk), (ev_env _ Hk). apply Rbg; [rewrite <- Hhi; exact H1 | exact H2 | exact H3].
Qed.

Definition regs_vars_below (R : IMap.t region) : bool :=
  IMap.forallb (fun k r => PrimInt63.ltb k n && region_vars_below n r) R.

Lemma regs_env_find : forall R k r, IMap.bst R -> regs_vars_below R = true -> IMap.find k R = Some r ->
  ev E' k = ev E k /\ hiZ E' r = hiZ E r /\ PrimInt63.ltb k n = true /\ region_vars_below n r = true.
Proof.
  intros R k r Hb HR Hf. pose proof (proj1 (IMap.forallb_spec _ _ Hb) HR k r Hf) as H.
  apply andb_prop in H as [Hk Hr]. split; [exact (ev_env _ Hk)|]. split; [exact (hiZ_env _ Hr)|]. split; assumption.
Qed.

Lemma in_based_env : forall R a, IMap.bst R -> regs_vars_below R = true -> (in_based E' R a <-> in_based E R a).
Proof.
  intros R a Hb HR. split; intros (k & r & Hf & Hk & Ha); exists k, r;
    destruct (regs_env_find R k r Hb HR Hf) as (He & Hh & _); rewrite ?He, ?Hh in *; repeat split; try assumption; try lia.
Qed.

Theorem st_ok_env : forall st ms model,
  0 < to_Z n -> svars_below n st = true ->
  st_ok segs OPS E st ms model -> st_ok segs OPS E' st ms model.
Proof.
  intros st ms model Hn Hsv HS.
  unfold svars_below in Hsv.
  apply andb_prop in Hsv as [Hsv Hops]. apply andb_prop in Hsv as [Hsv Hfs]. apply andb_prop in Hsv as [Hsv HR].
  apply andb_prop in Hsv as [Hsv Hrv]. apply andb_prop in Hsv as [Hrf Hff].
  destruct HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops' Hapart Hmf Hcov].
  assert (Hargs : forall o, In o (s_ops st) -> map (den E') (op_args o) = map (den E) (op_args o)).
  { intros o Ho. apply map_ext_in. intros a Ha. apply Hden.
    exact (forallb_In _ _ _ a (forallb_In _ _ _ o Hops Ho) Ha). }
  split; try assumption.
  - intros r. rewrite (Hden _ (rf_allb_get _ _ _ Hrf r)). exact (Hregs r).
  - intros r. rewrite (Hden _ (rf_allb_get _ _ _ Hff r)). exact (Hfregs r).
  - destruct (s_resv st) as [|a|]; cbn [resv_ok resv_vars_below] in *; [exact Hresv| |exact Hresv].
    rewrite (Hden _ Hrv). exact Hresv.
  - rewrite <- Hz. apply ev_env. apply Uint63.ltb_spec. change (to_Z 0%uint63) with 0. exact Hn.
  - intros k r Hf. destruct (regs_env_find _ k r Hbst HR Hf) as (_ & _ & Hk & Hr).
    apply region_ok_env; [exact Hk | exact Hr | exact (Hreg k r Hf)].
  - intros k1 r1 k2 r2 H1 H2 Hne Hk1 Hk2 W a.
    destruct (regs_env_find _ k1 r1 Hbst HR H1) as (-> & -> & _).
    destruct (regs_env_find _ k2 r2 Hbst HR H2) as (-> & -> & _).
    exact (Hdisj k1 r1 k2 r2 H1 H2 Hne Hk1 Hk2 W a).
  - apply Forall_forall. intros f Hf. apply fact_holds_env; [exact (forallb_In _ _ _ f Hfs Hf)|].
    exact (proj1 (Forall_forall _ _) Hfacts f Hf).
  - unfold ops_hold in *. apply Forall_forall. intros o Ho. rewrite (Hargs o Ho).
    exact (proj1 (Forall_forall _ _) Hops' o Ho).
  - unfold ops_apart in *. apply Forall_forall. intros o Ho a Ha. rewrite (Hargs o Ho) in Ha.
    rewrite (in_based_env _ a Hbst HR). exact (proj1 (Forall_forall _ _) Hapart o Ho a Ha).
  -
    intros a Ha.
    assert (HI : insts E' (s_ops st) = insts E (s_ops st)).
    { unfold insts. apply map_ext_in. intros o Ho. rewrite (Hargs o Ho). reflexivity. }
    rewrite HI. apply Hcov. destruct Ha as [Ha|Ha]; [left; exact (proj1 (in_based_env _ a Hbst HR) Ha) | right; exact Ha].
Qed.

End EnvChange.

Definition svc_ret (T : sstate) (v : sv) (fs' : list fact) (n' : int) : sstate :=
  SS (PrimInt63.add (s_pc T) 4%uint63) (rf_set (s_rf T) X10 v) (s_ff T) (s_resv T) (s_regs T)
     (fs' ++ s_facts T) (s_ops T) (s_priv T) n'.

Lemma reg10 : (10%bv : bv 5) = reg_of_r5 X10.
Proof. apply bv_eq. reflexivity. Qed.

Lemma svc_post_eq : forall ms x8 ret,
  svc_post ms x8 ret = ms_upd ms (rset (reg_of_r5 X10) ret (with_pc (ms_pc_val ms + Z_to_bv 64 4)%bv (core_of ms))) (ms_mem ms).
Proof. intros. unfold svc_post, advance_past_svc, set_gpr0, set_reg. rewrite reg10. reflexivity. Qed.

Section WithSegs2.
Variable segs : list Segment.
Variable OPS : optable.

Lemma st_ok_svc_return : forall E T ms model model' x8 ret v fs' n',
  st_ok segs OPS E T ms model ->
  PrimInt63.ltb (s_pc T) bit62i = true ->
  den E v = ret ->
  Forall (fact_holds E) fs' ->
  op_minv OPS model' ->
  ops_hold OPS E (s_ops T) (ms_mem ms) model' ->
  st_ok segs OPS E (svc_ret T v fs' n') (svc_post ms x8 ret) model'.
Proof.
  intros E T ms model model' x8 ret v fs' n' HS Hpc Hv Hfs Hmf Hops.
  pose proof (st_ok_reg_pc segs OPS E T ms model X10 v ret (PrimInt63.add (s_pc T) 4%uint63) HS Hv) as H1.
  rewrite (pc4_ok (s_pc T) Hpc), <- (so_pc _ _ _ _ _ _ HS) in H1. rewrite <- (svc_post_eq ms x8 ret) in H1.
  destruct H1 as [Hpc' Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops' Hapart Hmf0 Hcov0].
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv svc_ret setpc setr] in *; try assumption.
  unfold facts_hold. apply Forall_app. split; assumption.
Qed.

End WithSegs2.

Lemma syscall_spec_96 : forall i m o,
  bv_unsigned (in_sysno i) = 96 -> (syscall_spec i m o <-> set_tid_address_spec i m o).
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma set_tid_dispatch_ok : forall i m tid,
  bv_unsigned (in_sysno i) = 96 -> m_tid m = None -> 0 < bv_unsigned tid < PID_MAX_ENVELOPE ->
  syscall_spec i m (Ok (mkEffect tid [] []) (with_tid tid m) []).
Proof.
  intros i m tid Hno Htid Hr. apply (proj2 (syscall_spec_96 i m _ Hno)).
  unfold set_tid_address_spec. apply (proj2 (bind_get_model _ i m _)). rewrite Htid.
  unfold bind, choose, set_tid, modify, ret_only, pure.
  exists tid, m, [], []. split; [exists tid; split; [exact Hr|reflexivity]|].
  split; [|reflexivity]. exists tt, (with_tid tid m), [], []. repeat split; reflexivity.
Qed.

Lemma set_tid_dispatch_ok_inv : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 96 -> m_tid m = None -> syscall_spec i m (Ok eff m' evs) ->
  exists tid, 0 < bv_unsigned tid < PID_MAX_ENVELOPE /\ eff = mkEffect tid [] [] /\ m' = with_tid tid m /\ evs = [].
Proof.
  intros i m eff m' evs Hno Htid H. apply (proj1 (syscall_spec_96 i m _ Hno)) in H.
  unfold set_tid_address_spec in H. apply (proj1 (bind_get_model _ i m _)) in H. cbv beta in H. rewrite Htid in H.
  unfold bind, choose, set_tid, modify, ret_only, pure in H.
  destruct H as (x & m1 & evs1 & evs2 & (t & Ht & E1) & (u & m2 & evs3 & evs4 & E2 & E3 & E4) & E5).
  injection E1 as A1 A2 A3. injection E2 as B1 B2 B3. injection E3 as C1 C2 C3. subst.
  exists t. repeat split; try reflexivity; lia.
Qed.

Lemma set_tid_dispatch_no_unmodeled : forall i m,
  bv_unsigned (in_sysno i) = 96 -> m_tid m = None -> ~ syscall_spec i m Unmodeled.
Proof.
  intros i m Hno Htid H. apply (proj1 (syscall_spec_96 i m _ Hno)) in H.
  unfold set_tid_address_spec in H. apply (proj1 (bind_get_model _ i m _)) in H. cbv beta in H. rewrite Htid in H.
  unfold bind, choose, set_tid, modify, ret_only, pure in H.
  sys_destruct; discriminate.
Qed.

Lemma apply_effect_ret_only : forall ms r, apply_effect ms (mkEffect r [] []) = set_gpr0 ms r.
Proof. intros ms r. reflexivity. Qed.

Definition tid_I : Type := { t : word | 0 < bv_unsigned t < PID_MAX_ENVELOPE }.

Lemma tid1_ok : 0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE.
Proof. unfold PID_MAX_ENVELOPE. rewrite Z_to_bv_small; [lia|]. unfold bv_modulus. lia. Qed.

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
    intros [H|[H|[H|[H|[]]]]]; discriminate H. }
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

Definition env_set (E : env) (n : int) (w : word) : env :=
  Env (fun k => if PrimInt63.eqb k n then w else ev E k) (eb E) (eg E).

Lemma env_set_ext : forall E n w, env_ext n E (env_set E n w).
Proof.
  intros E n w. split; [reflexivity|]. intros k Hk. cbn [env_set ev eg]. split; [|reflexivity].
  destruct (PrimInt63.eqb k n) eqn:Hkn; [|reflexivity].
  apply Uint63.eqb_correct in Hkn. subst. lia.
Qed.

Lemma env_set_same : forall E n w, ev (env_set E n w) n = w.
Proof. intros. cbn [env_set ev]. rewrite Uint63.eqb_refl. reflexivity. Qed.

Definition tid_max : int := 4194303%uint63.

Definition post_set_tid (T : sstate) : option sstate :=
  let n := s_next T in
  match getr T X17 with
  | VL no =>
      if weqb no (wlit 96%uint63) && PrimInt63.ltb (s_pc T) bit62i && PrimInt63.ltb 0%uint63 n && svars_below n T
      then Some (svc_ret T (VP n wzero) [FRange n (wlit 1%uint63) (wlit tid_max)] (PrimInt63.add n 1%uint63))
      else None
  | _ => None
  end.

Theorem fx_node_set_tid : forall T T',
  post_set_tid T = Some T' ->
  (forall E mem model tid, ops_hold OPS E (s_ops T) mem model -> ops_hold OPS E (s_ops T) mem (with_tid tid model)) ->
  forall (K : TSet) E ms model,
    st_ok segs OPS E T ms model -> ecall_at segs (s_pc T) -> m_tid model = None ->
    (forall E' ms' model' tid,
        env_ext (s_next T) E E' -> st_ok segs OPS E' T' ms' model' ->
        0 < bv_unsigned tid < PID_MAX_ENVELOPE -> model' = with_tid tid model ->
        realizes segs (mkCfg ms' model') K) ->
    realizes segs (mkCfg ms model) K.
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
  eapply rz_pend; [exact HS | exact Hat |].
  pose proof (plain_mf OPS _ PL (so_mf _ _ _ _ _ _ HS)) as [Hh Hlazy].
  apply (rz_silent_all segs _ tid_I _ (exist _ (Z_to_bv 64 1) tid1_ok) K
           (node_set_tid (pend ms (den E (getr T X17))) model _ Hh Hlazy eq_refl H96 Htid)).
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
  - apply (plain_minv OPS _ PL). split; [rewrite m_halted_with_tid; exact Hh | exact Hlazy].
  - apply Hpure. exact (so_ops _ _ _ _ _ _ HS').
Qed.

Definition exit_code (T : sstate) : option w64 :=
  match getr T X17, getr T X10 with
  | VL no, VL c => if (weqb no (wlit 93%uint63) || weqb no (wlit 94%uint63)) && wltu c (wlit 256%uint63) then Some c else None
  | _, _ => None
  end.

Lemma bv_and_255_small : forall (x : word), bv_unsigned x < 256 -> bv_and x (Z_to_bv 64 255) = x.
Proof.
  intros x Hx. apply bv_eq. rewrite bv_and_unsigned, Z_to_bv_small by (unfold bv_modulus; lia).
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  apply Z.mod_small. pose proof (bv_unsigned_in_range _ x). lia.
Qed.

Theorem fx_node_exit : forall T c,
  exit_code T = Some c ->
  forall E ms model,
    st_ok segs OPS E T ms model -> ecall_at segs (s_pc T) ->
    realizes segs (mkCfg ms model) (t_exit (wbv c) (m_fs model)).
Proof.
  intros T c Hcode E ms model HS Hat.
  unfold exit_code in Hcode.
  destruct (getr T X17) as [no| | | | | | | | | |] eqn:H17; try discriminate.
  destruct (getr T X10) as [c0| | | | | | | | | |] eqn:H10; try discriminate.
  destruct ((weqb no (wlit 93) || weqb no (wlit 94)) && wltu c0 (wlit 256)) eqn:Hc; [|discriminate].
  injection Hcode as ->.
  apply andb_prop in Hc as [Hno Hlt].
  eapply rz_pend; [exact HS | exact Hat |].
  pose proof (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) as Hh.
  assert (Ha0 : ms_gpr (pend ms (den E (getr T X17))) 0 = wbv c).
  { rewrite pend_gpr, (so_a0 segs OPS E T ms model HS), H10. reflexivity. }
  assert (Hsmall : bv_unsigned (wbv c) < 256).
  { rewrite wbv_unsigned. pose proof (wltu_w2Z c (wlit 256)) as W. rewrite Hlt, wlit_ok in W.
    change (to_Z 256%uint63) with 256 in W. symmetry in W. apply Z.ltb_lt in W. exact W. }
  rewrite <- (bv_and_255_small (wbv c) Hsmall), <- Ha0.
  apply (rz_exit segs (pend ms (den E (getr T X17))) model (den E (getr T X17)) Hh eq_refl).
  rewrite H17. unfold is_exit_no. cbn [den].
  destruct (weqb no (wlit 93)) eqn:E93.
  - left. apply weqb_eq in E93. subst. reflexivity.
  - right. cbn in Hno. apply weqb_eq in Hno. subst. reflexivity.
Qed.

End WithSegs3.

End FXN.
