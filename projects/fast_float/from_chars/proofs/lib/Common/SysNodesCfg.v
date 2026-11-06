(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec SeqExec ShapeSet RealizesCfg.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Pend.
Context {fx : FPState}.

Definition epend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    (x8 : word) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
     ms_svc_pending := Some x8; ms_resv := None; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

#[using="Type"] Lemma step_ecall_epend : forall segs regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom)
  = MachineOk (epend regs pc mem rom (getr regs 17)).
Proof. LiaFast.lf_pins LiaFast.u0. intros. unfold epend. eapply step_ecall; eassumption. Qed.

#[using="Type"] Lemma ms_gpr_epend : forall regs pc mem rom x8 (k : nat), (k <= 5)%nat ->
  ms_gpr (epend regs pc mem rom x8) k = getr regs (Z_to_bv 5 (10 + Z.of_nat k)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom x8 k Hk. unfold ms_gpr. cbn [ms_regs epend].
  symmetry. apply getr_nz. intro E. apply (f_equal bv_unsigned) in E.
  rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32%Z in E.
  rewrite Z.mod_small in E by lia. change (bv_unsigned (0 : reg)) with 0%Z in E. lia.
Qed.

#[using="Type"] Lemma in_arg_epend : forall segs regs pc mem rom x8 (k : nat), (k <= 5)%nat ->
  in_arg (sys_input segs (epend regs pc mem rom x8) x8) k
  = getr regs (Z_to_bv 5 (10 + Z.of_nat k)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom x8 k Hk. rewrite <- (ms_gpr_epend regs pc mem rom x8 k Hk).
  unfold in_arg, sys_input, syscall_args. cbn [in_args].
  destruct k as [|[|[|[|[|[|k]]]]]]; try lia; reflexivity.
Qed.

#[using="Type"] Lemma in_arg0_epend : forall segs regs pc mem rom x8,
  in_arg (sys_input segs (epend regs pc mem rom x8) x8) 0 = getr regs 10.
Proof. LiaFast.lf_pins LiaFast.u0. intros. rewrite in_arg_epend by lia. f_equal. Qed.
#[using="Type"] Lemma in_arg1_epend : forall segs regs pc mem rom x8,
  in_arg (sys_input segs (epend regs pc mem rom x8) x8) 1 = getr regs 11.
Proof. LiaFast.lf_pins LiaFast.u0. intros. rewrite in_arg_epend by lia. f_equal. Qed.
#[using="Type"] Lemma in_arg2_epend : forall segs regs pc mem rom x8,
  in_arg (sys_input segs (epend regs pc mem rom x8) x8) 2 = getr regs 12.
Proof. LiaFast.lf_pins LiaFast.u0. intros. rewrite in_arg_epend by lia. f_equal. Qed.
#[using="Type"] Lemma in_arg3_epend : forall segs regs pc mem rom x8,
  in_arg (sys_input segs (epend regs pc mem rom x8) x8) 3 = getr regs 13.
Proof. LiaFast.lf_pins LiaFast.u0. intros. rewrite in_arg_epend by lia. f_equal. Qed.

#[using="Type"] Lemma in_sysno_epend : forall segs regs pc mem rom x8,
  in_sysno (sys_input segs (epend regs pc mem rom x8) x8) = x8.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

(* [comment removed for export] *)
Definition mrb (segs : list Segment) (mem : word -> option byte) : word -> option byte :=
  fun a => match mem a with Some b => Some b | None => seg_rom segs a end.

#[using="Type"] Lemma in_mem_epend : forall segs regs pc mem x8,
  in_mem (sys_input segs (epend regs pc mem (seg_rom segs) x8) x8) = mrb segs mem.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma in_wmem_epend : forall segs regs pc mem rom x8,
  in_wmem (sys_input segs (epend regs pc mem rom x8) x8) = wview segs mem.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma adv_epend_ret : forall regs pc mem rom x8 r ci,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [] [] ci))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom x8 r ci. unfold epend.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_zeros apply_unmaps apply_copies].
  unfold mkst, regupd. rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma adv_epend_write : forall regs pc mem rom x8 r buf bs ci,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [(buf, bs)] [] [] [] ci))
  = mkst (regupd regs 10 r) (v_addi pc 4) (wbytes mem buf bs) rom.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom x8 r buf bs ci. unfold epend.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_zeros apply_unmaps apply_copies].
  rewrite write_to_mem_wbytes.
  unfold mkst, regupd. rewrite b_npc4. reflexivity.
Qed.

End Pend.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma not_spurious_uninjected : forall cfg i model eff,
  injected_arm (bv_unsigned (in_sysno i)) = None ->
  ~ spurious_refusal_cfg cfg i model eff.
Proof.
  intros cfg i model eff Hn. apply spurious_refusal_family_on.
  unfold injected_family_off. rewrite Hn. reflexivity.
Qed.

Lemma not_spurious_fs : forall cfg i model eff,
  sc_fs cfg = true -> bv_unsigned (in_sysno i) = 56%Z ->
  ~ spurious_refusal_cfg cfg i model eff.
Proof.
  intros cfg i model eff Hfs Hno. apply spurious_refusal_family_on.
  unfold injected_family_off. rewrite Hno. cbn. rewrite Hfs. reflexivity.
Qed.

Lemma t_alt_const_nil : forall (I : Type) (i0 : I) (T : TSet),
  T [] -> t_eq (t_alt (fun _ : I => t_emit [] T)) T.
Proof.
  intros I i0 T H0 tr. split.
  - intros [_ Hi]. exact (proj1 (t_emit_nil_eq T H0 tr) Hi).
  - intros Hi. exists i0. exact (proj2 (t_emit_nil_eq T H0 tr) Hi).
Qed.

Section Generic.
Context {fx : FPState}.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_ecall : forall regs pc mem rom model w T,
  m_halted model = None -> m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes_cfg segs cfg (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  realizes_cfg segs cfg (mkCfg (mkst regs pc mem rom) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom model w T Hh Hl HF HE H.
  eapply rzc_step; [exact Hh | exact Hl | reflexivity | | exact H].
  exact (step_ecall_epend segs regs pc mem rom w HF HE).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_sys : forall ms model x8 (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (EV : I -> list event) (T : I -> TSet) (i0 : I),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall j, syscall_spec (sys_input segs ms x8) model (Ok (E j) (M j) (EV j))) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     exists j, eff = E j /\ m' = M j /\ evs = EV j) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff) ->
  (forall j, m_halted (M j) = None) ->
  (forall j, m_vm_lazy (M j) = []) ->
  (forall j, realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms (E j))) (M j)) (T j)) ->
  realizes_cfg segs cfg (mkCfg ms model) (t_alt (fun j => t_emit (EV j) (T j))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model x8 I E M EV T i0 Hh Hsvc Hcomp Hsound Hnu Hns HhM HlM HK.
  apply (rzc_node segs cfg (mkCfg ms model) I EV
           (fun j => mkCfg (advance_past_svc (apply_effect ms (E j))) (M j)) T i0); [| exact HK].
  apply (node_sys_cfg_nl segs cfg ms model x8 I E M EV Hh Hsvc Hcomp); try assumption.
  - intros j. apply Hns.
  - intros eff m' evs Hs _. exact (Hsound eff m' evs Hs).
  - intros eff m' evs Hs. destruct (Hsound eff m' evs Hs) as (j & _ & -> & _). apply HhM.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_sys_det : forall ms model x8 eff m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff m' []) ->
  (forall eff1 m1 evs1, syscall_spec (sys_input segs ms x8) model (Ok eff1 m1 evs1) ->
     eff1 = eff /\ m1 = m' /\ evs1 = []) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff1, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff1) ->
  m_halted m' = None -> m_vm_lazy m' = [] ->
  realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms eff)) m') T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model x8 eff m' T Hh Hsvc Hc Hs Hnu Hns HhM HlM HK.
  eapply rzc_conseq.
  - apply (rzc_sys ms model x8 unit (fun _ => eff) (fun _ => m') (fun _ => []) (fun _ => T) tt);
      try assumption.
    + intros j. exact Hc.
    + intros eff1 m1 evs1 H. exists tt. exact (Hs _ _ _ H).
    + intros j. exact HhM.
    + intros j. exact HlM.
    + intros j. exact HK.
  - apply t_alt_const_nil; [exact tt|]. exact (realizes_cfg_nonempty segs cfg _ _ HK).
Qed.

End Generic.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Exit Fork.

Lemma syscall_spec_no : forall i m o (no : Z) (a : SpecArm),
  bv_unsigned (in_sysno i) = no -> lookup_arm spec_table no = Some a ->
  syscall_spec i m o <-> sa_spec a i m o.
Proof.
  intros i m o no a Hno Ha. unfold syscall_spec, dispatch. rewrite Hno, Ha. reflexivity.
Qed.

Lemma set_tid_fresh_ok : forall i m eff m' evs,
  m_tid m = None ->
  set_tid_address_spec i m (Ok eff m' evs) <->
  exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z
            /\ eff = mkEffect t [] [] /\ m' = with_tid t m /\ evs = [].
Proof.
  intros i m eff m' evs Htid. unfold set_tid_address_spec.
  rewrite bind_get_model. rewrite Htid.
  unfold set_tid, ret_only, bind, choose, modify, pure. split.
  - intros H. sys_destruct.
    match goal with |- exists t, _ /\ mkEffect ?x [] [] = _ /\ _ => exists x end.
    repeat split; try assumption; reflexivity.
  - intros (t & Ht & -> & -> & ->).
    exists t, m, [], []. split; [exists t; split; [exact Ht | reflexivity]|]. split; [|reflexivity].
    exists tt, (with_tid t m), [], []. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma set_tid_fresh_unmodeled : forall i m,
  m_tid m = None -> ~ set_tid_address_spec i m Unmodeled.
Proof.
  intros i m Htid H. unfold set_tid_address_spec in H.
  rewrite bind_get_model in H. rewrite Htid in H.
  unfold set_tid, ret_only, bind, choose, modify, pure in H. sys_destruct.
Qed.

Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. intros t m. destruct m; reflexivity. Qed.
Lemma with_tid_lazy : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m.
Proof. intros t m. destruct m; reflexivity. Qed.
Lemma with_tid_fs : forall t m, m_fs (with_tid t m) = m_fs m.
Proof. intros t m. destruct m; reflexivity. Qed.
Lemma with_tid_fds : forall t m, m_fds (with_tid t m) = m_fds m.
Proof. intros t m. destruct m; reflexivity. Qed.

Section Kernel.
Context {fx : FPState}.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_set_tid : forall regs (pc : word) mem rom model w T,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     realizes_cfg segs cfg (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) T) ->
  realizes_cfg segs cfg (mkCfg (mkst regs pc mem rom) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom model w T HF HE Hh Hlazy H17 Htid Hk.
  eapply rzc_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  set (x8 := getr regs 17).
  assert (Hno : bv_unsigned (in_sysno (sys_input segs ms x8)) = 96%Z) by (cbn; unfold x8; rewrite H17; reflexivity).
  assert (Hsp : forall o, syscall_spec (sys_input segs ms x8) model o
                          <-> set_tid_address_spec (sys_input segs ms x8) model o)
    by (intro o; exact (syscall_spec_no _ _ _ 96 _ Hno eq_refl)).
  set (I := {t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z}).
  assert (i0 : I) by (exists (Z_to_bv 64 1); split; vm_compute; reflexivity).
  eapply rzc_conseq.
  - apply (rzc_sys segs cfg ms model x8 I (fun j => mkEffect (proj1_sig j) [] [])
             (fun j => with_tid (proj1_sig j) model) (fun _ => []) (fun _ => T) i0);
      [exact Hh | reflexivity | | | | | | | ].
    + intros [t Ht]. apply Hsp. apply set_tid_fresh_ok; [exact Htid|]. exists t. auto.
    + intros eff m' evs Hs. apply Hsp in Hs. apply set_tid_fresh_ok in Hs as (t & Ht & -> & -> & ->); [|exact Htid].
      exists (exist _ t Ht). auto.
    + intros Hs. apply Hsp in Hs. exact (set_tid_fresh_unmodeled _ _ Htid Hs).
    + intros eff. apply not_spurious_uninjected. rewrite Hno. reflexivity.
    + intros j. rewrite with_tid_halted. exact Hh.
    + intros j. rewrite with_tid_lazy. exact Hlazy.
    + intros [t Ht]. cbn [proj1_sig]. unfold ms. rewrite adv_epend_ret. apply Hk. exact Ht.
  - apply t_alt_const_nil; [exact i0|].
    destruct i0 as [t Ht]. exact (realizes_cfg_nonempty segs cfg _ _ (Hk t Ht)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_exit_at : forall regs (pc : word) mem rom model w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 93 \/ getr regs 17 = Z_to_bv 64 94) ->
  realizes_cfg segs cfg (mkCfg (mkst regs pc mem rom) model)
    (t_exit (bv_and (getr regs 10) (Z_to_bv 64 255)) (m_fs model)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom model w HF HE Hh Hlazy H17.
  eapply rzc_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  replace (getr regs 10) with (ms_gpr (epend regs pc mem rom (getr regs 17)) 0)
    by (rewrite ms_gpr_epend by lia; f_equal).
  apply (rzc_exit segs cfg _ model (getr regs 17)); [exact Hh | reflexivity |].
  unfold exit_sysno. destruct H17 as [H|H]; rewrite H; [left|right]; reflexivity.
Qed.

End Kernel.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.

Lemma u64_lit : forall z, (0 <= z < 2^64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^64)%Z. apply Z.mod_small. exact Hz.
Qed.

Lemma bind_input {A} (k : SyscallInput -> Sys A) : forall i m o,
  bind input k i m o <-> k i i m o.
Proof.
  intros i m o. unfold bind, input. destruct o as [x m2 evs|]; split.
  - intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3).
    injection H1 as -> -> ->. cbn in H3. subst evs. exact H2.
  - intros H. exists i, m, [], evs. split; [reflexivity|].
    split; [exact H | reflexivity].
  - intros [H | (x0 & m1 & evs1 & H1 & H2)]; [discriminate|].
    injection H1 as -> -> ->. exact H2.
  - intros H. right. exists i, m, []. split; [reflexivity | exact H].
Qed.

Lemma record_copyins_ok_iff : forall reads spec i m eff m' evs,
  record_copyins reads spec i m (Ok eff m' evs) <->
  exists eff0, spec i m (Ok eff0 m' evs) /\ eff = with_copyins (reads ++ eff_copyins eff0) eff0.
Proof.
  intros reads spec i m eff m' evs. unfold record_copyins, bind, pure. split.
  - intros (x & m1 & evs1 & evs2 & H1 & H2 & H3). injection H2; intros; subst.
    exists x. rewrite app_nil_r. split; [exact H1 | reflexivity].
  - intros (eff0 & H & ->). exists eff0, m', evs, []. rewrite app_nil_r. auto.
Qed.

Lemma record_copyins_unmodeled_iff : forall reads spec i m,
  record_copyins reads spec i m Unmodeled <-> spec i m Unmodeled.
Proof.
  intros reads spec i m. unfold record_copyins, bind, pure. split.
  - intros [H | (x & m1 & evs1 & _ & H)]; [exact H | discriminate].
  - intros H. left. exact H.
Qed.

Lemma err_ret_ok_iff : forall e i m eff m' evs,
  err_ret e i m (Ok eff m' evs) <-> eff = mkEffect (errno_ret e) [] [] /\ m' = m /\ evs = [].
Proof.
  intros. unfold err_ret, ret_only, pure. split.
  - intros H. injection H as -> -> ->. auto.
  - intros (-> & -> & ->). reflexivity.
Qed.

Lemma err_ret_unmodeled : forall e i m, ~ err_ret e i m Unmodeled.
Proof. intros e i m H. unfold err_ret, ret_only, pure in H. discriminate H. Qed.

Lemma with_fds_halted : forall f m, m_halted (with_fds f m) = m_halted m.
Proof. intros f m. destruct m; reflexivity. Qed.
Lemma with_fds_lazy : forall f m, m_vm_lazy (with_fds f m) = m_vm_lazy m.
Proof. intros f m. destruct m; reflexivity. Qed.
Lemma with_fds_fs : forall f m, m_fs (with_fds f m) = m_fs m.
Proof. intros f m. destruct m; reflexivity. Qed.
Lemma with_fds_fds : forall f m, m_fds (with_fds f m) = f.
Proof. intros f m. destruct m; reflexivity. Qed.

(* [comment removed for export] *)
Lemma open_result_ok_iff : forall m mk i eff m' evs,
  open_result_spec m mk i m (Ok eff m' evs) <->
  ((exists e, In e openat_errnos /\ eff = mkEffect (errno_ret e) [] [] /\ m' = m /\ evs = [])
   \/ (fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None
       /\ eff = mkEffect (alloc_fd (m_fds m)) [] [] /\ m' = mk (alloc_fd (m_fds m)) m /\ evs = [])).
Proof.
  intros m mk i eff m' evs. unfold open_result_spec, alt.
  unfold errno_from, lowest_fd, err_ret, ret_only, bind, choose, modify, pure. split.
  - intros [H | H]; sys_destruct.
    + left. eexists. split; [eassumption|]. auto.
    + right. split; [assumption|]. auto.
  - intros [(e & He & -> & -> & ->) | (Hfree & -> & -> & ->)].
    + left. exists e, m, [], []. split; [exists e; auto|]. auto.
    + right. exists (alloc_fd (m_fds m)), m, [], []. split; [exists (alloc_fd (m_fds m)); auto|].
      split; [|reflexivity].
      exists tt, (mk (alloc_fd (m_fds m)) m), [], []. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma open_result_unmodeled : forall m mk i, ~ open_result_spec m mk i m Unmodeled.
Proof.
  intros m mk i H. unfold open_result_spec, alt in H.
  unfold errno_from, lowest_fd, err_ret, ret_only, bind, choose, modify, pure in H.
  destruct H as [H | H]; sys_destruct.
Qed.

(* [comment removed for export] *)
Lemma openat_rd_reduce : forall dirfd pathp flags p i m o,
  dirfd = AT_FDCWD32 ->
  Z.ldiff (bv_unsigned flags) open_ignored_flags = 0%Z ->
  read_cstr (in_mem i) pathp = CstrOk p ->
  path_eqb p [] = false -> path_has_slash p = false ->
  (openat_spec dirfd pathp flags i m o <->
   record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] (openat_read_spec p m) i m o).
Proof.
  intros dirfd pathp flags p i m o Hd Hfl Hc Hne Hsl.
  unfold openat_spec. rewrite bind_input.
  assert (E : forall o', openat_core_spec dirfd pathp flags i m o' <-> openat_read_spec p m i m o').
  { intro o'. unfold openat_core_spec. rewrite bind_input, bind_get_model.
    rewrite (modeled_open_flags_rd flags Hfl). cbn [negb].
    unfold openat_body_spec. rewrite Hc, Hne, Hd, bv_eqb_refl. cbn [negb].
    unfold openat_resolved_spec. rewrite Hsl. cbv zeta. rewrite Hfl. reflexivity. }
  destruct o as [eff m' evs|].
  - rewrite !record_copyins_ok_iff. split; intros (eff0 & H & ->); exists eff0; split; try reflexivity; apply E; exact H.
  - rewrite !record_copyins_unmodeled_iff. apply E.
Qed.

(* [comment removed for export] *)
Lemma openat_toolong_reduce : forall dirfd pathp flags i m o,
  Z.ldiff (bv_unsigned flags) open_ignored_flags = 0%Z ->
  read_cstr (in_mem i) pathp = CstrTooLong ->
  (openat_spec dirfd pathp flags i m o <->
   record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] (err_ret ENAMETOOLONG) i m o).
Proof.
  intros dirfd pathp flags i m o Hfl Hc.
  unfold openat_spec. rewrite bind_input.
  assert (E : forall o', openat_core_spec dirfd pathp flags i m o' <-> err_ret ENAMETOOLONG i m o').
  { intro o'. unfold openat_core_spec. rewrite bind_input, bind_get_model.
    rewrite (modeled_open_flags_rd flags Hfl). cbn [negb].
    unfold openat_body_spec. rewrite Hc. reflexivity. }
  destruct o as [eff m' evs|].
  - rewrite !record_copyins_ok_iff. split; intros (eff0 & H & ->); exists eff0; split; try reflexivity; apply E; exact H.
  - rewrite !record_copyins_unmodeled_iff. apply E.
Qed.

Lemma openat_empty_reduce : forall dirfd pathp flags i m o,
  Z.ldiff (bv_unsigned flags) open_ignored_flags = 0%Z ->
  read_cstr (in_mem i) pathp = CstrOk [] ->
  (openat_spec dirfd pathp flags i m o <->
   record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] (err_ret ENOENT) i m o).
Proof.
  intros dirfd pathp flags i m o Hfl Hc.
  unfold openat_spec. rewrite bind_input.
  assert (E : forall o', openat_core_spec dirfd pathp flags i m o' <-> err_ret ENOENT i m o').
  { intro o'. unfold openat_core_spec. rewrite bind_input, bind_get_model.
    rewrite (modeled_open_flags_rd flags Hfl). cbn [negb].
    unfold openat_body_spec. rewrite Hc. reflexivity. }
  destruct o as [eff m' evs|].
  - rewrite !record_copyins_ok_iff. split; intros (eff0 & H & ->); exists eff0; split; try reflexivity; apply E; exact H.
  - rewrite !record_copyins_unmodeled_iff. apply E.
Qed.

Lemma syscall_spec_56 : forall i m o,
  bv_unsigned (in_sysno i) = 56%Z ->
  syscall_spec i m o <-> openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o H. exact (syscall_spec_no i m o 56 _ H eq_refl). Qed.
Lemma syscall_spec_57 : forall i m o,
  bv_unsigned (in_sysno i) = 57%Z ->
  syscall_spec i m o <-> close_spec (fd32 (in_arg i 0)) i m o.
Proof. intros i m o H. exact (syscall_spec_no i m o 57 _ H eq_refl). Qed.
Lemma syscall_spec_63 : forall i m o,
  bv_unsigned (in_sysno i) = 63%Z ->
  syscall_spec i m o <-> read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o H. exact (syscall_spec_no i m o 63 _ H eq_refl). Qed.
Lemma syscall_spec_66 : forall i m o,
  bv_unsigned (in_sysno i) = 66%Z ->
  syscall_spec i m o <-> writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o H. exact (syscall_spec_no i m o 66 _ H eq_refl). Qed.
Lemma syscall_spec_29 : forall i m o,
  bv_unsigned (in_sysno i) = 29%Z ->
  syscall_spec i m o <-> ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i m o.
Proof. intros i m o H. exact (syscall_spec_no i m o 29 _ H eq_refl). Qed.

(* [comment removed for export] *)
Definition ret_ci (r : word) (ci : list (word * nat)) : SyscallEffect := mkEffectU r [] [] [] [] ci.

Lemma with_copyins_ret : forall ci r, with_copyins ci (mkEffect r [] []) = ret_ci r ci.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_alt_sum_nil : forall (IA : Type) (ia : IA) (A B : TSet),
  A [] -> B [] ->
  t_eq (t_alt (fun j : IA + unit => t_emit [] (match j with inl _ => A | inr _ => B end))) (t_alt2 A B).
Proof.
  intros IA ia A B HA HB tr. unfold t_alt, t_alt2. split.
  - intros [[a|[]] H]; [left; exact (proj1 (t_emit_nil_eq A HA tr) H)
                       | right; exact (proj1 (t_emit_nil_eq B HB tr) H)].
  - intros [H|H]; [exists (inl ia); exact (proj2 (t_emit_nil_eq A HA tr) H)
                  | exists (inr tt); exact (proj2 (t_emit_nil_eq B HB tr) H)].
Qed.

Section FsNodes.
Context {fx : FPState}.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Local Abbreviation PEND regs pc mem := (epend regs pc mem (seg_rom segs) (getr regs 17)).

#[using="Type"] Lemma in_sysno_pend : forall regs pc mem (no : Z),
  getr regs 17 = Z_to_bv 64 no -> (0 <= no < 2^64)%Z ->
  bv_unsigned (in_sysno (sys_input segs (PEND regs pc mem) (getr regs 17))) = no.
Proof. LiaFast.lf_pins LiaFast.u0. intros regs pc mem no H Hr. cbn [in_sysno sys_input]. rewrite H. apply u64_lit. exact Hr. Qed.

Section Open.
Hypothesis Hfs : sc_fs cfg = true.

(* [comment removed for export] *)
#[using="Hfs"] Lemma rzc_openat_can_open : forall regs pc mem model p (ent : FdEntry) A B,
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 56 ->
  fd32 (getr regs 10) = AT_FDCWD32 ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  read_cstr (mrb segs mem) (getr regs 11) = CstrOk p ->
  path_eqb p [] = false -> path_has_slash p = false ->
  (forall o, openat_read_spec p model (sys_input segs (PEND regs pc mem) (getr regs 17)) model o <->
             open_result_spec model (fun fd => with_fds (fd_insert (m_fds model) fd ent))
               (sys_input segs (PEND regs pc mem) (getr regs 17)) model o) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     realizes_cfg segs cfg (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) A) ->
  realizes_cfg segs cfg
    (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem (seg_rom segs))
           (with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model)) ent) model)) B ->
  realizes_cfg segs cfg (mkCfg (PEND regs pc mem) model) (t_alt2 A B).
Proof. LiaFast.lf_pins (fun (Hfs : LiaFast.U) => LiaFast.u0).
  intros regs pc mem model p ent A B Hh Hlz H17 Hd Hfl Hc Hne Hsl Hres Hfree HA HB.
  set (i := sys_input segs (PEND regs pc mem) (getr regs 17)).
  assert (A0 : in_arg i 0 = getr regs 10) by apply in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply in_arg2_epend.
  assert (Hno : bv_unsigned (in_sysno i) = 56%Z) by (apply in_sysno_pend; [exact H17 | lia]).
  set (ci := [(getr regs 11, cstr_access_len_aux (mrb segs mem) (getr regs 11) path_max)]).
  assert (Hsp : forall o, syscall_spec i model o <-> record_copyins ci (open_result_spec model
                  (fun fd => with_fds (fd_insert (m_fds model) fd ent))) i model o).
  { intro o. rewrite (syscall_spec_56 i model o Hno).
    rewrite (A0), (A1), (A2).
    rewrite (openat_rd_reduce (fd32 (getr regs 10)) (getr regs 11) (getr regs 12) p i model o Hd Hfl
               ltac:(exact Hc) Hne Hsl).
    change (in_mem i) with (mrb segs mem). fold ci.
    destruct o as [eff m' evs|].
    - rewrite !record_copyins_ok_iff. split; intros (eff0 & H & ->); exists eff0; split; try reflexivity; apply Hres; exact H.
    - rewrite !record_copyins_unmodeled_iff. apply Hres. }
  set (I := ({e : Z | In e openat_errnos} + unit)%type).
  assert (ia : {e : Z | In e openat_errnos}) by (exists ENOMEM; left; reflexivity).
  eapply rzc_conseq.
  - apply (rzc_sys segs cfg (PEND regs pc mem) model (getr regs 17) I
             (fun j => match j with inl e => ret_ci (errno_ret (proj1_sig e)) ci
                                  | inr _ => ret_ci (alloc_fd (m_fds model)) ci end)
             (fun j => match j with inl _ => model
                                  | inr _ => with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model)) ent) model end)
             (fun _ => [])
             (fun j => match j with inl _ => A | inr _ => B end) (inl ia));
      [exact Hh | reflexivity | | | | | | | ].
    + intros [[e He]|[]]; apply Hsp; apply record_copyins_ok_iff; cbn [proj1_sig].
      * exists (mkEffect (errno_ret e) [] []). split.
        2:{ unfold with_copyins, ret_ci. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
            rewrite app_nil_r. reflexivity. }
        apply open_result_ok_iff. left. exists e. auto.
      * exists (mkEffect (alloc_fd (m_fds model)) [] []). split.
        2:{ unfold with_copyins, ret_ci. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
            rewrite app_nil_r. reflexivity. }
        apply open_result_ok_iff. right. auto.
    + intros eff m' evs Hs. apply Hsp, record_copyins_ok_iff in Hs as (eff0 & Hs & ->).
      apply open_result_ok_iff in Hs as [(e & He & -> & -> & ->) | (_ & -> & -> & ->)].
      * exists (inl (exist _ e He)). cbn [proj1_sig]. auto.
      * exists (inr tt). auto.
    + intros Hs. apply Hsp, record_copyins_unmodeled_iff in Hs. exact (open_result_unmodeled _ _ _ Hs).
    + intros eff. apply not_spurious_fs; [exact Hfs | exact Hno].
    + intros [_|_]; [exact Hh | rewrite with_fds_halted; exact Hh].
    + intros [_|_]; [exact Hlz | rewrite with_fds_lazy; exact Hlz].
    + intros [[e He]|[]]; unfold ret_ci; rewrite adv_epend_ret; cbn [proj1_sig]; [apply HA; exact He | exact HB].
  - apply t_alt_sum_nil; [exact ia | |].
    + exact (realizes_cfg_nonempty segs cfg _ _ (HA ENOMEM ltac:(left; reflexivity))).
    + exact (realizes_cfg_nonempty segs cfg _ _ HB).
Qed.

(* [comment removed for export] *)
#[using="Hfs"] Lemma rzc_openat_file : forall regs pc mem model p data A B,
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 56 ->
  fd32 (getr regs 10) = AT_FDCWD32 ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  read_cstr (mrb segs mem) (getr regs 11) = CstrOk p ->
  path_eqb p [] = false -> path_has_slash p = false -> path_is_dirref p = false ->
  fs_lookup (m_fs model) p = Some data ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     realizes_cfg segs cfg (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) A) ->
  realizes_cfg segs cfg
    (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem (seg_rom segs))
           (with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model)) (FdFile p (Z_to_bv 64 0))) model)) B ->
  realizes_cfg segs cfg (mkCfg (PEND regs pc mem) model) (t_alt2 A B).
Proof. LiaFast.lf_pins (fun (Hfs : LiaFast.U) => LiaFast.u0).
  intros regs pc mem model p data A B Hh Hlz H17 Hd Hfl Hc Hne Hsl Hdr Hlk Hfree HA HB.
  apply (rzc_openat_can_open regs pc mem model p (FdFile p (Z_to_bv 64 0)) A B); try assumption.
  intro o. unfold openat_read_spec. rewrite Hdr, Hlk. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hfs"] Lemma rzc_openat_dirref : forall regs pc mem model p A B,
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 56 ->
  fd32 (getr regs 10) = AT_FDCWD32 ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  read_cstr (mrb segs mem) (getr regs 11) = CstrOk p ->
  path_eqb p [] = false -> path_has_slash p = false -> path_is_dirref p = true ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     realizes_cfg segs cfg (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) A) ->
  realizes_cfg segs cfg
    (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem (seg_rom segs))
           (with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model)) FdDir) model)) B ->
  realizes_cfg segs cfg (mkCfg (PEND regs pc mem) model) (t_alt2 A B).
Proof. LiaFast.lf_pins (fun (Hfs : LiaFast.U) => LiaFast.u0).
  intros regs pc mem model p A B Hh Hlz H17 Hd Hfl Hc Hne Hsl Hdr Hfree HA HB.
  apply (rzc_openat_can_open regs pc mem model p FdDir A B); try assumption.
  intro o. unfold openat_read_spec. rewrite Hdr. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hfs"] Lemma rzc_openat_det_err : forall regs pc mem model (e : Z) T,
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 56 ->
  (forall o, syscall_spec (sys_input segs (PEND regs pc mem) (getr regs 17)) model o <->
     record_copyins [(getr regs 11, cstr_access_len_aux (mrb segs mem) (getr regs 11) path_max)] (err_ret e)
       (sys_input segs (PEND regs pc mem) (getr regs 17)) model o) ->
  realizes_cfg segs cfg (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) T ->
  realizes_cfg segs cfg (mkCfg (PEND regs pc mem) model) T.
Proof. LiaFast.lf_pins (fun (Hfs : LiaFast.U) => LiaFast.u0).
  intros regs pc mem model e T Hh Hlz H17 Hsp HK.
  set (i := sys_input segs (PEND regs pc mem) (getr regs 17)) in *.
  assert (A0 : in_arg i 0 = getr regs 10) by apply in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply in_arg2_epend.
  assert (Hno : bv_unsigned (in_sysno i) = 56%Z) by (apply in_sysno_pend; [exact H17 | lia]).
  set (ci := [(getr regs 11, cstr_access_len_aux (mrb segs mem) (getr regs 11) path_max)]) in *.
  apply (rzc_sys_det segs cfg (PEND regs pc mem) model (getr regs 17) (ret_ci (errno_ret e) ci) model T);
    [exact Hh | reflexivity | | | | | exact Hh | exact Hlz | ].
  - apply Hsp. apply record_copyins_ok_iff. exists (mkEffect (errno_ret e) [] []).
    split.
    2:{ unfold with_copyins, ret_ci. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
        rewrite app_nil_r. reflexivity. }
    apply err_ret_ok_iff. auto.
  - intros eff1 m1 evs1 Hs. apply Hsp, record_copyins_ok_iff in Hs as (eff0 & Hs & ->).
    apply err_ret_ok_iff in Hs as (-> & -> & ->). auto.
  - intros Hs. apply Hsp, record_copyins_unmodeled_iff in Hs. exact (err_ret_unmodeled _ _ _ Hs).
  - intros eff. apply not_spurious_fs; [exact Hfs | exact Hno].
  - unfold ret_ci. rewrite adv_epend_ret. exact HK.
Qed.

(* [comment removed for export] *)
#[using="Hfs"] Lemma rzc_openat_enoent : forall regs pc mem model p T,
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 56 ->
  fd32 (getr regs 10) = AT_FDCWD32 ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  read_cstr (mrb segs mem) (getr regs 11) = CstrOk p ->
  path_eqb p [] = false -> path_has_slash p = false -> path_is_dirref p = false ->
  fs_lookup (m_fs model) p = None ->
  realizes_cfg segs cfg (mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem (seg_rom segs)) model) T ->
  realizes_cfg segs cfg (mkCfg (PEND regs pc mem) model) T.
Proof. LiaFast.lf_pins (fun (Hfs : LiaFast.U) => LiaFast.u0).
  intros regs pc mem model p T Hh Hlz H17 Hd Hfl Hc Hne Hsl Hdr Hlk HK.
  apply (rzc_openat_det_err regs pc mem model ENOENT T Hh Hlz H17); [|exact HK].
  intro o. set (i := sys_input segs (PEND regs pc mem) (getr regs 17)).
  assert (A0 : in_arg i 0 = getr regs 10) by apply in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply in_arg2_epend.
  assert (Hno : bv_unsigned (in_sysno i) = 56%Z) by (apply in_sysno_pend; [exact H17 | lia]).
  rewrite (syscall_spec_56 i model o Hno).
  rewrite (A0), (A1), (A2).
  rewrite (openat_rd_reduce (fd32 (getr regs 10)) (getr regs 11) (getr regs 12) p i model o Hd Hfl
             ltac:(exact Hc) Hne Hsl).
  change (in_mem i) with (mrb segs mem).
  unfold openat_read_spec. rewrite Hdr, Hlk. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hfs"] Lemma rzc_openat_empty : forall regs pc mem model T,
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 56 ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  read_cstr (mrb segs mem) (getr regs 11) = CstrOk [] ->
  realizes_cfg segs cfg (mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem (seg_rom segs)) model) T ->
  realizes_cfg segs cfg (mkCfg (PEND regs pc mem) model) T.
Proof. LiaFast.lf_pins (fun (Hfs : LiaFast.U) => LiaFast.u0).
  intros regs pc mem model T Hh Hlz H17 Hfl Hc HK.
  apply (rzc_openat_det_err regs pc mem model ENOENT T Hh Hlz H17); [|exact HK].
  intro o. set (i := sys_input segs (PEND regs pc mem) (getr regs 17)).
  assert (A0 : in_arg i 0 = getr regs 10) by apply in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply in_arg2_epend.
  assert (Hno : bv_unsigned (in_sysno i) = 56%Z) by (apply in_sysno_pend; [exact H17 | lia]).
  rewrite (syscall_spec_56 i model o Hno).
  rewrite (A0), (A1), (A2).
  rewrite (openat_empty_reduce (fd32 (getr regs 10)) (getr regs 11) (getr regs 12) i model o Hfl
             ltac:(exact Hc)).
  reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hfs"] Lemma rzc_openat_toolong : forall regs pc mem model T,
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 56 ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  read_cstr (mrb segs mem) (getr regs 11) = CstrTooLong ->
  realizes_cfg segs cfg (mkCfg (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4) mem (seg_rom segs)) model) T ->
  realizes_cfg segs cfg (mkCfg (PEND regs pc mem) model) T.
Proof. LiaFast.lf_pins (fun (Hfs : LiaFast.U) => LiaFast.u0).
  intros regs pc mem model T Hh Hlz H17 Hfl Hc HK.
  apply (rzc_openat_det_err regs pc mem model ENAMETOOLONG T Hh Hlz H17); [|exact HK].
  intro o. set (i := sys_input segs (PEND regs pc mem) (getr regs 17)).
  assert (A0 : in_arg i 0 = getr regs 10) by apply in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply in_arg2_epend.
  assert (Hno : bv_unsigned (in_sysno i) = 56%Z) by (apply in_sysno_pend; [exact H17 | lia]).
  rewrite (syscall_spec_56 i model o Hno).
  rewrite (A0), (A1), (A2).
  rewrite (openat_toolong_reduce (fd32 (getr regs 10)) (getr regs 11) (getr regs 12) i model o Hfl
             ltac:(exact Hc)).
  reflexivity.
Qed.

End Open.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_det_ret : forall regs pc mem model (no : Z) (r : word) (m' : Model) T,
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 no -> (0 <= no < 2^64)%Z ->
  injected_arm no = None ->
  (forall eff m1 evs, syscall_spec (sys_input segs (PEND regs pc mem) (getr regs 17)) model (Ok eff m1 evs) <->
     eff = mkEffect r [] [] /\ m1 = m' /\ evs = []) ->
  ~ syscall_spec (sys_input segs (PEND regs pc mem) (getr regs 17)) model Unmodeled ->
  m_halted m' = None -> m_vm_lazy m' = [] ->
  realizes_cfg segs cfg (mkCfg (mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs)) m') T ->
  realizes_cfg segs cfg (mkCfg (PEND regs pc mem) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model no r m' T Hh Hlz H17 Hr Hinj Hsp Hnu HhM HlM HK.
  apply (rzc_sys_det segs cfg (PEND regs pc mem) model (getr regs 17) (mkEffect r [] []) m' T);
    [exact Hh | reflexivity | apply Hsp; auto | | exact Hnu | | exact HhM | exact HlM | ].
  - intros eff1 m1 evs1 Hs. apply Hsp in Hs. exact Hs.
  - intros eff. apply not_spurious_uninjected. rewrite (in_sysno_pend regs pc mem no H17 Hr). exact Hinj.
  - change (mkEffect r [] []) with (mkEffectU r [] [] [] [] []). rewrite adv_epend_ret. exact HK.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_read_dir : forall regs pc mem model T,
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some FdDir ->
  access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
  realizes_cfg segs cfg (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) T ->
  realizes_cfg segs cfg (mkCfg (PEND regs pc mem) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model T Hh Hlz H17 Hfd Hok HK.
  set (i := sys_input segs (PEND regs pc mem) (getr regs 17)).
  assert (A0 : in_arg i 0 = getr regs 10) by apply in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply in_arg2_epend.
  assert (Hno : bv_unsigned (in_sysno i) = 63%Z) by (apply in_sysno_pend; [exact H17 | lia]).
  assert (Hsp : forall o, syscall_spec i model o <-> err_ret EISDIR i model o).
  { intro o. rewrite (syscall_spec_63 i model o Hno). rewrite (A0), (A1), (A2).
    unfold read_spec. rewrite bind_input, bind_get_model. rewrite Hfd, Hok. reflexivity. }
  apply (rzc_det_ret regs pc mem model 63 (errno_ret EISDIR) model T Hh Hlz H17 ltac:(lia) eq_refl);
    [ | | exact Hh | exact Hlz | exact HK].
  - intros eff m1 evs. fold i. rewrite Hsp. apply err_ret_ok_iff.
  - intros Hs. fold i in Hs. apply Hsp in Hs. exact (err_ret_unmodeled _ _ _ Hs).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_read_file : forall regs pc mem model p off data T,
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
  read_bytes_map (wview segs mem) (getr regs 11)
    (len_word (file_read data off (Z_to_bv 64 (rw_count_clamp (getr regs 12))))) <> None ->
  realizes_cfg segs cfg
    (mkCfg (mkst (regupd regs 10 (len_word (file_read data off (Z_to_bv 64 (rw_count_clamp (getr regs 12))))))
                 (v_addi pc 4)
                 (wbytes mem (getr regs 11) (file_read data off (Z_to_bv 64 (rw_count_clamp (getr regs 12)))))
                 (seg_rom segs))
           (with_fds (fd_insert (m_fds model) (fd32 (getr regs 10))
                        (FdFile p (off + len_word (file_read data off (Z_to_bv 64 (rw_count_clamp (getr regs 12)))))))
                     model)) T ->
  realizes_cfg segs cfg (mkCfg (PEND regs pc mem) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model p off data T Hh Hlz H17 Hfd Hlk Hok Hw HK.
  set (bs := file_read data off (Z_to_bv 64 (rw_count_clamp (getr regs 12)))) in *.
  set (m' := with_fds (fd_insert (m_fds model) (fd32 (getr regs 10)) (FdFile p (off + len_word bs))) model) in *.
  set (i := sys_input segs (PEND regs pc mem) (getr regs 17)).
  assert (A0 : in_arg i 0 = getr regs 10) by apply in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply in_arg2_epend.
  assert (Hno : bv_unsigned (in_sysno i) = 63%Z) by (apply in_sysno_pend; [exact H17 | lia]).
  assert (W0 : in_wmem i = wview segs mem) by apply in_wmem_epend.
  set (eff := mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) []).
  assert (Hsp : forall eff1 m1 evs1, syscall_spec i model (Ok eff1 m1 evs1) <-> eff1 = eff /\ m1 = m' /\ evs1 = []).
  { intros eff1 m1 evs1. rewrite (syscall_spec_63 i model _ Hno). rewrite (A0), (A1), (A2).
    unfold read_spec. rewrite bind_input, bind_get_model. rewrite Hfd, Hok. cbn [negb]. rewrite Hlk.
    rewrite W0. fold bs.
    destruct (read_bytes_map (wview segs mem) (getr regs 11) (len_word bs)) as [w|] eqn:Ew; [|exfalso; apply Hw; reflexivity].
    unfold set_fds, modify, bind, pure. split.
    - intros H. sys_destruct. rewrite app_nil_l. auto.
    - intros (-> & -> & ->). exists tt, m', [], []. auto. }
  assert (Hnu : ~ syscall_spec i model Unmodeled).
  { intros Hs. rewrite (syscall_spec_63 i model _ Hno) in Hs. unfold i at 1 2 3 in Hs.
    rewrite in_arg0_epend, in_arg1_epend, in_arg2_epend in Hs.
    unfold read_spec in Hs. rewrite bind_input, bind_get_model in Hs. rewrite Hfd, Hok in Hs. cbn [negb] in Hs.
    rewrite Hlk in Hs. rewrite W0 in Hs. fold bs in Hs.
    destruct (read_bytes_map (wview segs mem) (getr regs 11) (len_word bs)) as [w|] eqn:Ew; [|apply Hw; reflexivity].
    unfold set_fds, modify, bind, pure in Hs. sys_destruct. }
  apply (rzc_sys_det segs cfg (PEND regs pc mem) model (getr regs 17) eff m' T);
    [exact Hh | reflexivity | apply Hsp; auto | intros; apply Hsp; assumption | exact Hnu | |
     unfold m'; rewrite with_fds_halted; exact Hh | unfold m'; rewrite with_fds_lazy; exact Hlz | ].
  - intros eff1. apply not_spurious_uninjected. fold i. rewrite Hno. reflexivity.
  - unfold eff, delivered_writes. destruct bs as [|b bs'] eqn:Ebs.
    + change (mkEffect (len_word []) [] []) with (mkEffectU (len_word (@nil byte)) [] [] [] [] []).
      rewrite adv_epend_ret. exact HK.
    + change (mkEffect (len_word (b :: bs')) [(getr regs 11, b :: bs')] [])
        with (mkEffectU (len_word (b :: bs')) [(getr regs 11, b :: bs')] [] [] [] []).
      rewrite adv_epend_write. exact HK.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_close : forall regs pc mem model (ent : FdEntry) T,
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 57 ->
  fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some ent ->
  realizes_cfg segs cfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))
                               (with_fds (fd_remove (m_fds model) (fd32 (getr regs 10))) model)) T ->
  realizes_cfg segs cfg (mkCfg (PEND regs pc mem) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model ent T Hh Hlz H17 Hfd HK.
  set (i := sys_input segs (PEND regs pc mem) (getr regs 17)).
  assert (A0 : in_arg i 0 = getr regs 10) by apply in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply in_arg2_epend.
  assert (Hno : bv_unsigned (in_sysno i) = 57%Z) by (apply in_sysno_pend; [exact H17 | lia]).
  assert (Hsp : forall o, syscall_spec i model o <->
             (set_fds (fd_remove (m_fds model) (fd32 (getr regs 10))) ;; ret_only (Z_to_bv 64 0)) i model o).
  { intro o. rewrite (syscall_spec_57 i model o Hno). rewrite (A0).
    unfold close_spec. rewrite bind_get_model. rewrite Hfd. reflexivity. }
  apply (rzc_det_ret regs pc mem model 57 (Z_to_bv 64 0) (with_fds (fd_remove (m_fds model) (fd32 (getr regs 10))) model) T
           Hh Hlz H17 ltac:(lia) eq_refl);
    [ | | rewrite with_fds_halted; exact Hh | rewrite with_fds_lazy; exact Hlz | exact HK].
  - intros eff m1 evs. fold i. rewrite Hsp. unfold set_fds, modify, ret_only, bind, pure. split.
    + intros H. sys_destruct. auto.
    + intros (-> & -> & ->). exists tt, (with_fds (fd_remove (m_fds model) (fd32 (getr regs 10))) model), [], [].
      auto.
  - intros Hs. fold i in Hs. apply Hsp in Hs. unfold set_fds, modify, ret_only, bind, pure in Hs. sys_destruct.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_ioctl_notty : forall regs pc mem model (ch : word) T,
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 29 ->
  fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel ch) ->
  tty_only_request (cmd32 (getr regs 11)) = true ->
  realizes_cfg segs cfg (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem (seg_rom segs)) model) T ->
  realizes_cfg segs cfg (mkCfg (PEND regs pc mem) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model ch T Hh Hlz H17 Hfd Htty HK.
  set (i := sys_input segs (PEND regs pc mem) (getr regs 17)).
  assert (A0 : in_arg i 0 = getr regs 10) by apply in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply in_arg2_epend.
  assert (Hno : bv_unsigned (in_sysno i) = 29%Z) by (apply in_sysno_pend; [exact H17 | lia]).
  assert (Hsp : forall o, syscall_spec i model o <-> err_ret ENOTTY i model o).
  { intro o. rewrite (syscall_spec_29 i model o Hno). rewrite (A0), (A1).
    unfold ioctl_spec. rewrite bind_get_model. rewrite Hfd, Htty. reflexivity. }
  apply (rzc_det_ret regs pc mem model 29 (errno_ret ENOTTY) model T Hh Hlz H17 ltac:(lia) eq_refl);
    [ | | exact Hh | exact Hlz | exact HK].
  - intros eff m1 evs. fold i. rewrite Hsp. apply err_ret_ok_iff.
  - intros Hs. fold i in Hs. apply Hsp in Hs. exact (err_ret_unmodeled _ _ _ Hs).
Qed.

End FsNodes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Writev.
Context {fx : FPState}.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Local Abbreviation PEND regs pc mem := (epend regs pc mem (seg_rom segs) (getr regs 17)).

#[using="Type"] Lemma u64_roundtrip : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. LiaFast.lf_pins LiaFast.u0. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

#[using="Type"] Lemma bv_add_Zform : forall (a b : word), a + b = Z_to_bv 64 (bv_unsigned a + bv_unsigned b).
Proof. LiaFast.lf_pins LiaFast.u0. intros a b. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity. Qed.

#[using="Type"] Lemma word_to_nat_Z : forall z, (0 <= z < 2^64)%Z -> word_to_nat (Z_to_bv 64 z) = Z.to_nat z.
Proof. LiaFast.lf_pins LiaFast.u0. intros z Hz. unfold word_to_nat. rewrite u64_lit by exact Hz. reflexivity. Qed.

#[using="Type"] Lemma access_okb_of_le : forall (b : word) (n : Z),
  (0 <= n)%Z -> (bv_unsigned b + n <= TASK_SIZE)%Z -> access_okb b n = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b n Hn H. unfold access_okb. pose proof (bv_unsigned_in_range 64 b) as [Hb _].
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

#[using="Type"] Lemma mrb_read_aux : forall mem k a,
  read_bytes_aux (mrb segs mem) a k = rdn segs mem a k.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem k; induction k as [|k IH]; intros a; [reflexivity|].
  cbn [read_bytes_aux rdn]. unfold mrb. rewrite IH. reflexivity.
Qed.

#[using="Type"] Lemma mrb_read_bytes : forall mem a n,
  read_bytes_map (mrb segs mem) a n = rdn segs mem a (word_to_nat n).
Proof. LiaFast.lf_pins LiaFast.u0. intros mem a n. rewrite read_bytes_map_eq. apply mrb_read_aux. Qed.

#[using="Type"] Lemma read_u64_rdn : forall mem a v,
  rdn segs mem a 8%nat = Some (word_to_le_bytes 8 v) ->
  read_u64 (mrb segs mem) a = Some v.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem a v H. unfold read_u64. rewrite mrb_read_bytes.
  change (word_to_nat (Z_to_bv 64 8)) with 8%nat. rewrite H.
  f_equal. apply le_word_v. apply bytes_le_to_Z_8.
Qed.

(* [comment removed for export] *)
Fixpoint iov_array (mem : word -> option byte) (iov : word) (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r =>
      rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b)
      /\ rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n)
      /\ (bv_unsigned n < 2 ^ 63)%Z
      /\ iov_array mem (Z_to_bv 64 (bv_unsigned iov + 16)) r
  end.

#[using="Type"] Lemma read_iovec_entry_of_array : forall mem b n r iov,
  iov_array mem iov ((b, n) :: r) ->
  read_iovec_entry (mrb segs mem) iov = IovEntry b n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem b n r iov (Hb & Hn & Hlt & _). unfold read_iovec_entry.
  rewrite (read_u64_rdn mem iov b Hb).
  rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
  rewrite (read_u64_rdn mem _ n Hn).
  rewrite (proj2 (Z.leb_gt _ _) Hlt). reflexivity.
Qed.

#[using="Type"] Lemma copy_iovecs_of_array : forall mem iovs iov,
  iov_array mem iov iovs ->
  copy_iovecs_aux (mrb segs mem) iov (length iovs) = ImpOk iovs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem iovs; induction iovs as [|[b n] r IH]; intros iov Ha; [reflexivity|].
  cbn [length copy_iovecs_aux].
  rewrite (read_iovec_entry_of_array mem b n r iov Ha).
  destruct Ha as (_ & _ & _ & Hr).
  rewrite bv_add_Zform. change (bv_unsigned (16 : word)) with 16%Z.
  rewrite (IH _ Hr). reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint iov_bufs (mem : word -> option byte) (iovs : list (word * word)) (bss : list (list byte)) : Prop :=
  match iovs, bss with
  | [], [] => True
  | (b, n) :: r, bs :: bss' => rdn segs mem b (word_to_nat n) = Some bs /\ iov_bufs mem r bss'
  | _, _ => False
  end.

#[using="Type"] Lemma gather_of_bufs : forall mem iovs bss,
  iov_bufs mem iovs bss ->
  gather_iovecs (mrb segs mem) iovs = Some (concat bss).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem iovs; induction iovs as [|[b n] r IH]; intros [|bs bss] Hb; cbn in Hb; try contradiction.
  - reflexivity.
  - destruct Hb as [H1 H2]. cbn [gather_iovecs concat].
    rewrite mrb_read_bytes, H1, (IH bss H2). reflexivity.
Qed.

#[using="Type"] Lemma cap_iovecs_id : forall iovs left,
  (iovs_total iovs <= left)%Z -> cap_iovecs_aux iovs left = iovs.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction iovs as [|[b n] r IH]; intros left H; [reflexivity|].
  cbn [cap_iovecs_aux]. cbn [iovs_total] in H. pose proof (iovs_total_nonneg r).
  rewrite Z.min_r by lia. rewrite u64_roundtrip, IH by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint iov_bufs_ok (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r => (bv_unsigned b + bv_unsigned n <= TASK_SIZE)%Z /\ iov_bufs_ok r
  end.

#[using="Type"] Lemma iovs_access_okb_of_ok : forall iovs, iov_bufs_ok iovs -> iovs_access_okb iovs = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction iovs as [|[b n] r IH]; intros H; [reflexivity|].
  destruct H as [Hb Hr]. unfold iovs_access_okb. cbn [forallb fst snd].
  rewrite (access_okb_intro b n Hb). cbn [andb]. exact (IH Hr).
Qed.

#[using="Type"] Lemma import_iovecs_of_array : forall mem iovs iov,
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array mem iov iovs ->
  iov_bufs_ok iovs ->
  import_iovecs (mrb segs mem) iov (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem iovs iov Hcnt Hok Harr Hbok. unfold import_iovecs.
  destruct iovs as [|[b n] r]; [cbn in Hcnt; lia|].
  destruct r as [|[b2 n2] r2].
  - cbn [length] in *. change (Z.of_nat 1) with 1%Z in *.
    rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    rewrite (read_iovec_entry_of_array mem b n [] iov Harr).
    destruct Hbok as [Hb _]. pose proof (bv_unsigned_in_range 64 n) as Hn. unfold bv_modulus in Hn.
    rewrite (access_okb_of_le b (Z.min (bv_unsigned n) MAX_RW_COUNT))
      by (unfold MAX_RW_COUNT in *; lia).
    reflexivity.
  - set (cnt := Z.of_nat (length ((b, n) :: (b2, n2) :: r2))) in *.
    assert (Hc2 : (2 <= cnt <= 1024)%Z) by (unfold cnt; cbn [length] in *; lia).
    assert (E1 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 1) = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
    assert (E0 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 0) = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
    rewrite E1, E0. rewrite u64_lit by lia.
    replace ((IOV_MAX <? cnt)%Z) with false by (symmetry; apply Z.ltb_ge; unfold IOV_MAX; lia).
    rewrite (access_okb_of_le iov (16 * cnt)) by lia.
    rewrite word_to_nat_Z by lia. unfold cnt. rewrite Nat2Z.id.
    rewrite (copy_iovecs_of_array mem _ iov Harr).
    rewrite (iovs_access_okb_of_ok _ Hbok). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma writev_ch_ok_iff : forall regs pc mem model (ch : word) iovs bss eff m' evs,
  getr regs 17 = Z_to_bv 64 66 ->
  fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel ch) ->
  w_is0 ch = false ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned (getr regs 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array mem (getr regs 11) iovs -> iov_bufs_ok iovs -> iov_bufs mem iovs bss ->
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  let bs := concat bss in
  let CA := import_iovecs_accesses (mrb segs mem) (getr regs 11) (Z_to_bv 64 (Z.of_nat (length iovs))) in
  (syscall_spec (sys_input segs (PEND regs pc mem) (getr regs 17)) model (Ok eff m' evs) <->
   exists k, (1 <= k <= length bs)%nat
     /\ eff = ret_ci (Z_to_bv 64 (Z.of_nat k)) (CA ++ (iov_prefix_accesses iovs k ++ []))
     /\ m' = model /\ evs = map (WriteEv ch) (firstn k bs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model ch iovs bss eff m' evs H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30 bs CA.
  set (i := sys_input segs (PEND regs pc mem) (getr regs 17)).
  assert (A0 : in_arg i 0 = getr regs 10) by apply in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply in_arg2_epend.
  assert (M0 : in_mem i = mrb segs mem) by reflexivity.
  assert (Hno : bv_unsigned (in_sysno i) = 66%Z) by (cbn [in_sysno i sys_input]; rewrite H17; reflexivity).
  pose proof (gather_of_bufs mem iovs bss Hbufs) as Hg. fold bs in Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  assert (Hcap : cap_iovecs iovs = iovs).
  { unfold cap_iovecs. apply cap_iovecs_id. unfold MAX_RW_COUNT. lia. }
  assert (Hlw : bv_unsigned (len_word bs) = iovs_total iovs).
  { unfold len_word. rewrite Hlen. apply u64_lit. lia. }
  rewrite (syscall_spec_66 i model _ Hno). rewrite A0, A1, A2, H12.
  unfold writev_spec. rewrite bind_input, bind_get_model. rewrite Hfd, Hch. rewrite M0, Hcnt32.
  rewrite record_copyins_ok_iff.
  rewrite (import_iovecs_of_array mem iovs (getr regs 11) Hcnt Hiok Harr Hbok). fold CA.
  unfold writev_gathered. rewrite Hcap, (gather_prefix_full _ _ _ Hg). fold bs.
  cbv beta iota zeta.
  replace ((iovs_total iovs =? 0)%Z) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((length bs =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (addr_is_error_b (len_word bs)) with false
    by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite Hlw; lia).
  split.
  - intros (eff0 & Hs & ->).
    unfold bind, choose, emit, pure in Hs. sys_destruct.
    match goal with H : record_copyins _ _ _ _ _ |- _ => apply record_copyins_ok_iff in H as (eff1 & H & ->) end.
    unfold ret_only, pure in *. sys_destruct.
    match goal with H : ?ds = firstn (length ?ds) bs |- _ => rename H into Hds; rename ds into dd end.
    exists (length dd). refine (conj _ (conj _ (conj _ _))); [split; [lia | rewrite Hds; rewrite length_firstn; lia] | | reflexivity | ].
    + unfold with_copyins, ret_ci. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
      rewrite !app_nil_r. unfold len_word. reflexivity.
    + rewrite app_nil_r. cbn [app]. f_equal. exact Hds.
  - intros (k & Hk & -> & -> & ->).
    exists (ret_ci (Z_to_bv 64 (Z.of_nat k)) (iov_prefix_accesses iovs k ++ [])). split.
    2:{ unfold with_copyins, ret_ci. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins]. reflexivity. }
    unfold bind, choose, emit, pure.
    exists (firstn k bs), model, [], (map (WriteEv ch) (firstn k bs)). split.
    { exists (firstn k bs). split; [|reflexivity]. rewrite length_firstn, Nat.min_l by lia.
      refine (conj _ (conj _ (conj _ _))).
      - lia.
      - unfold two_pow_64. lia.
      - unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge. unfold len_word. rewrite length_firstn, Nat.min_l by lia.
        rewrite u64_lit by lia. lia.
      - reflexivity. }
    split; [| reflexivity].
    exists tt, model, (map (WriteEv ch) (firstn k bs)), []. split; [reflexivity|]. split; [|rewrite app_nil_r; reflexivity].
    try rewrite Hcap. rewrite length_firstn, Nat.min_l by lia.
    apply record_copyins_ok_iff. exists (mkEffect (len_word (firstn k bs)) [] []). split; [reflexivity|].
    unfold with_copyins, ret_ci, len_word. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
    rewrite length_firstn, Nat.min_l by lia. reflexivity.
Qed.

#[using="Type"] Lemma writev_ch_no_unmodeled : forall regs pc mem model (ch : word) iovs bss,
  getr regs 17 = Z_to_bv 64 66 ->
  fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel ch) ->
  w_is0 ch = false ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned (getr regs 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array mem (getr regs 11) iovs -> iov_bufs_ok iovs -> iov_bufs mem iovs bss ->
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  ~ syscall_spec (sys_input segs (PEND regs pc mem) (getr regs 17)) model Unmodeled.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model ch iovs bss H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30.
  set (i := sys_input segs (PEND regs pc mem) (getr regs 17)).
  assert (A0 : in_arg i 0 = getr regs 10) by apply in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply in_arg2_epend.
  assert (M0 : in_mem i = mrb segs mem) by reflexivity.
  assert (Hno : bv_unsigned (in_sysno i) = 66%Z) by (cbn [in_sysno i sys_input]; rewrite H17; reflexivity).
  pose proof (gather_of_bufs mem iovs bss Hbufs) as Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  assert (Hcap : cap_iovecs iovs = iovs).
  { unfold cap_iovecs. apply cap_iovecs_id. unfold MAX_RW_COUNT. lia. }
  assert (Hlw : bv_unsigned (len_word (concat bss)) = iovs_total iovs).
  { unfold len_word. rewrite Hlen. apply u64_lit. lia. }
  intros Hs. rewrite (syscall_spec_66 i model _ Hno) in Hs. rewrite A0, A1, A2, H12 in Hs.
  unfold writev_spec in Hs. rewrite bind_input, bind_get_model in Hs. rewrite Hfd, Hch in Hs.
  rewrite M0, Hcnt32 in Hs. apply record_copyins_unmodeled_iff in Hs.
  rewrite (import_iovecs_of_array mem iovs (getr regs 11) Hcnt Hiok Harr Hbok) in Hs.
  unfold writev_gathered in Hs. rewrite Hcap, (gather_prefix_full _ _ _ Hg) in Hs.
  cbv beta iota zeta in Hs.
  replace ((iovs_total iovs =? 0)%Z) with false in Hs by (symmetry; apply Z.eqb_neq; lia).
  replace ((length (concat bss) =? 0)%nat) with false in Hs by (symmetry; apply Nat.eqb_neq; lia).
  replace (addr_is_error_b (len_word (concat bss))) with false in Hs
    by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite Hlw; lia).
  unfold bind, choose, emit, pure in Hs. sys_destruct.
  match goal with H : record_copyins _ _ _ _ _ |- _ => apply record_copyins_unmodeled_iff in H end.
  unfold ret_only, pure in *. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_writev_ch : forall regs pc mem model (ch : word) iovs bss (T : nat -> TSet),
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 66 ->
  fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel ch) ->
  w_is0 ch = false ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned (getr regs 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array mem (getr regs 11) iovs -> iov_bufs_ok iovs -> iov_bufs mem iovs bss ->
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length (concat bss))%nat ->
     realizes_cfg segs cfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model) (T k)) ->
  realizes_cfg segs cfg (mkCfg (PEND regs pc mem) model)
    (t_alt (fun i : wr_index (concat bss) =>
       t_emit (map (WriteEv ch) (firstn (proj1_sig i) (concat bss))) (T (proj1_sig i)))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model ch iovs bss T Hh Hlz H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30 HK.
  set (bs := concat bss) in *.
  set (CA := import_iovecs_accesses (mrb segs mem) (getr regs 11) (Z_to_bv 64 (Z.of_nat (length iovs)))).
  pose proof (gather_of_bufs mem iovs bss Hbufs) as Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. fold bs in Hlen.
  assert (Hnb : (1 <= length bs)%nat) by lia.
  assert (Hno : bv_unsigned (in_sysno (sys_input segs (PEND regs pc mem) (getr regs 17))) = 66%Z)
    by (cbn [in_sysno sys_input]; rewrite H17; reflexivity).
  apply (rzc_sys segs cfg (PEND regs pc mem) model (getr regs 17) (wr_index bs)
           (fun j => ret_ci (Z_to_bv 64 (Z.of_nat (proj1_sig j))) (CA ++ (iov_prefix_accesses iovs (proj1_sig j) ++ [])))
           (fun _ => model)
           (fun j => map (WriteEv ch) (firstn (proj1_sig j) bs))
           (fun j => T (proj1_sig j)) (wr_full bs Hnb));
    [exact Hh | reflexivity | | | | | | | ].
  - intros [k Hk]. cbn [proj1_sig].
    apply (writev_ch_ok_iff regs pc mem model ch iovs bss _ _ _ H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30).
    exists k. auto.
  - intros eff m' evs Hs.
    apply (writev_ch_ok_iff regs pc mem model ch iovs bss _ _ _ H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30)
      in Hs as (k & Hk & -> & -> & ->).
    exists (exist _ k Hk). auto.
  - exact (writev_ch_no_unmodeled regs pc mem model ch iovs bss H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30).
  - intros eff. apply not_spurious_uninjected. rewrite Hno. reflexivity.
  - intros _. exact Hh.
  - intros _. exact Hlz.
  - intros [k [Hk1 Hk2]]. cbn [proj1_sig]. unfold ret_ci. rewrite adv_epend_ret. apply HK; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_writev_ch_wall : forall regs pc mem model (ch : word) iovs bss (K : TSet),
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 66 ->
  fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel ch) ->
  w_is0 ch = false ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned (getr regs 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array mem (getr regs 11) iovs -> iov_bufs_ok iovs -> iov_bufs mem iovs bss ->
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length (concat bss))%nat ->
     realizes_cfg segs cfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
       (t_emit (map (WriteEv ch) (skipn k (concat bss))) K)) ->
  realizes_cfg segs cfg (mkCfg (PEND regs pc mem) model) (t_emit (map (WriteEv ch) (concat bss)) K).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model ch iovs bss K Hh Hlz H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30 HK0 HK.
  pose proof (gather_of_bufs mem iovs bss Hbufs) as Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
  eapply rzc_conseq.
  - apply (rzc_writev_ch regs pc mem model ch iovs bss (fun k => t_emit (map (WriteEv ch) (skipn k (concat bss))) K));
      assumption.
  - apply t_alt_wall; [exact HK0 | lia].
Qed.

End Writev.
