(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall Uaccess Dispatch SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import ReadWrite Open.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Exit Fork.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OSSVerify.Proofs.openssl.pem.lib.Cls Require Import ClsSyscallFacts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Structural.
Variable b : SpuriousCfg.
Variable segs : list Segment.
Variable code : word.

Local Notation "'ME' c" := (must_exit_at_cfg b segs code c) (at level 10, c at level 9, only parsing).

(* [comment removed for export] *)
Lemma me_cfg_halted : forall ms model,
  m_halted model = Some code -> m_killed model = None -> ME (mkCfg ms model).
Proof. intros ms model Hh Hk. apply must_exit_at_cfg_halted; [exact Hh | exact Hk]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_cfg_instr_inv : forall ms model evs st,
  ms_svc_pending ms = None ->
  sstep_cfg segs b (mkCfg ms model) evs st ->
  evs = [] /\
  match mi_account_step segs ms model with
  | MachineOk (ms', model') => st = SNext (mkCfg ms' model')
  | _ => st = SError
  end.
Proof.
  intros ms model evs st Hsvc Hss.
  inversion Hss; subst;
    match goal with
    | H : mi_account_step _ _ _ = _ |- _ => rewrite H; split; reflexivity
    | H : ms_svc_pending _ = Some _ |- _ => rewrite Hsvc in H; discriminate H
    end.
Qed.

(* [comment removed for export] *)
Lemma me_cfg_instr : forall ms model ms' model',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  ME (mkCfg ms' model') -> ME (mkCfg ms model).
Proof.
  intros ms model ms' model' Hh Hsvc Hstep Hme.
  apply must_exit_at_cfg_running.
  - exact Hh.
  - exists [], (SNext (mkCfg ms' model')). apply sstep_cfg_instr; assumption.
  - intros evs Hss. destruct (sstep_cfg_instr_inv _ _ _ _ Hsvc Hss) as [_ Hst].
    rewrite Hstep in Hst. discriminate Hst.
  - intros evs c' Hss. destruct (sstep_cfg_instr_inv _ _ _ _ Hsvc Hss) as [_ Hst].
    rewrite Hstep in Hst. injection Hst as ->. exact Hme.
Qed.

(* [comment removed for export] *)
Lemma me_cfg_instr_inv : forall ms model,
  ms_svc_pending ms = None ->
  ME (mkCfg ms model) ->
  m_halted model = None ->
  exists ms' model', mi_account_step segs ms model = MachineOk (ms', model')
                     /\ ME (mkCfg ms' model').
Proof.
  intros ms model Hsvc Hme Hh.
  inversion Hme as [c Hh' Hc | c Hh' Hprog Hnoerr Hnext Hc]; subst.
  - cbn [cfg_model] in Hh'. rewrite Hh in Hh'. discriminate Hh'.
  - destruct Hprog as (evs & st & Hss).
    destruct (sstep_cfg_instr_inv _ _ _ _ Hsvc Hss) as [-> Hst].
    destruct (mi_account_step segs ms model) as [[ms' model']| |] eqn:Hstep.
    + exists ms', model'. split; [reflexivity|]. apply (Hnext []). subst st. exact Hss.
    + subst st. exfalso. exact (Hnoerr [] Hss).
    + subst st. exfalso. exact (Hnoerr [] Hss).
Qed.

(* [comment removed for export] *)
Fixpoint instr_steps (n : nat) (c : config) : option config :=
  match n with
  | O => Some c
  | S k =>
      match m_halted (cfg_model c), ms_svc_pending (cfg_ms c) with
      | None, None =>
          match mi_account_step segs (cfg_ms c) (cfg_model c) with
          | MachineOk (ms', model') => instr_steps k (mkCfg ms' model')
          | _ => None
          end
      | _, _ => None
      end
  end.

Lemma me_cfg_instr_steps : forall n c c',
  instr_steps n c = Some c' -> ME c' -> ME c.
Proof.
  induction n as [|k IH]; intros [ms model] c' Hrun Hme; cbn [instr_steps cfg_ms cfg_model] in Hrun.
  - injection Hrun as ->. exact Hme.
  - destruct (m_halted model) eqn:Hh; [discriminate Hrun|].
    destruct (ms_svc_pending ms) eqn:Hsvc; [discriminate Hrun|].
    destruct (mi_account_step segs ms model) as [[ms' model']| |] eqn:Hstep; try discriminate Hrun.
    eapply me_cfg_instr; [exact Hh | exact Hsvc | exact Hstep | exact (IH _ _ Hrun Hme)].
Qed.

Lemma instr_steps_app : forall n k c c',
  instr_steps n c = Some c' -> instr_steps (n + k) c = instr_steps k c'.
Proof.
  induction n as [|n IH]; intros k [ms model] c' H; cbn [instr_steps Nat.add cfg_ms cfg_model] in *.
  - injection H as ->. reflexivity.
  - destruct (m_halted model); [discriminate H|]. destruct (ms_svc_pending ms); [discriminate H|].
    destruct (mi_account_step segs ms model) as [[ms' model']| |]; try discriminate H.
    exact (IH k _ _ H).
Qed.

(* [comment removed for export] *)
Lemma me_cfg_step : forall ms ms' model,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  ME (mkCfg ms' model) -> ME (mkCfg ms model).
Proof.
  intros ms ms' model Hh Hlazy Hsvc Hstep Hme.
  eapply me_cfg_instr; [exact Hh | exact Hsvc | | exact Hme].
  rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

End Structural.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma in_sysno_sys_input : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
Lemma in_arg_sys_input : forall segs ms x8 k, (k < 6)%nat ->
  in_arg (sys_input segs ms x8) k = ms_gpr ms k.
Proof.
  intros segs ms x8 k Hk.
  do 6 (destruct k as [|k]; [reflexivity|]). lia.
Qed.
Lemma in_mem_sys_input : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.
Lemma in_wmem_sys_input : forall segs ms x8, in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma materialize_model_accesses_nil : forall m, materialize_model_accesses m [] = Some m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma syscall_effect_accesses_ret : forall r zs us cs,
  syscall_effect_accesses (mkEffectU r [] zs us cs []) = [].
Proof. reflexivity. Qed.

Section Syscall.
Variable b : SpuriousCfg.
Variable segs : list Segment.
Variable code : word.
Local Notation "'ME' c" := (must_exit_at_cfg b segs code c) (at level 10, c at level 9, only parsing).

(* [comment removed for export] *)
Lemma sstep_cfg_sys_inv : forall ms model x8 evs st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs b (mkCfg ms model) evs st ->
  let i := sys_input segs ms x8 in
  (exists eff model' evs0,
      syscall_spec i model (Ok eff model' evs0)
      /\ ~ spurious_refusal_cfg b i model eff
      /\ m_halted model' = None
      /\ match materialize_model_accesses model' (syscall_effect_accesses eff) with
         | Some model'' => evs = evs0 /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')
         | None => evs = [] /\ st = SError
         end)
  \/ (exists eff model' evs0 code',
      syscall_spec i model (Ok eff model' evs0)
      /\ m_halted model' = Some code'
      /\ ((m_killed model' = None /\ evs = evs0 ++ [ExitEv code' (m_fs model')])
          \/ (m_killed model' = Some code' /\ evs = evs0 ++ [KillEv code' (m_fs model')]))
      /\ st = SNext (mkCfg ms model'))
  \/ (syscall_spec i model Unmodeled /\ evs = [] /\ st = SError).
Proof.
  intros ms model x8 evs st Hsvc Hss. cbv zeta.
  inversion Hss; subst;
    try match goal with H : ms_svc_pending ms = None |- _ => rewrite Hsvc in H; discriminate H end;
    match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; injection H as <- end.
  - left. eexists _, _, _. repeat (split; [eassumption|]).
    match goal with H : materialize_model_accesses _ _ = Some _ |- _ => rewrite H end. split; reflexivity.
  - left. eexists _, _, _. repeat (split; [eassumption|]).
    match goal with H : materialize_model_accesses _ _ = None |- _ => rewrite H end. split; reflexivity.
  - right; left. eexists _, _, _, _. repeat (split; [eassumption|]). split; [|reflexivity].
    left. split; [assumption|reflexivity].
  - (* [comment removed for export] *)
    right; left.
    match goal with Hk : m_killed ?m' = Some ?sg |- _ =>
      assert (Hh' : m_halted m' = Some sg)
        by (unfold m_killed in Hk; unfold m_halted;
            destruct (procst_killed (m_proc m')); [exact Hk | discriminate Hk]);
      eexists _, _, _, _; split; [eassumption|]; split; [exact Hh'|]; split; [|reflexivity];
      right; split; [exact Hk|reflexivity]
    end.
  - right; right. split; [assumption|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma me_cfg_syscall : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  let i := sys_input segs ms x8 in
  ~ syscall_spec i model Unmodeled ->
  (exists eff model' evs, syscall_spec i model (Ok eff model' evs)
      /\ (m_halted model' = None -> ~ spurious_refusal_cfg b i model eff)) ->
  (forall eff model' evs, syscall_spec i model (Ok eff model' evs) ->
      ~ spurious_refusal_cfg b i model eff -> m_halted model' = None ->
      exists model'', materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
                      /\ ME (mkCfg (advance_past_svc (apply_effect ms eff)) model'')) ->
  (forall eff model' evs code', syscall_spec i model (Ok eff model' evs) ->
      m_halted model' = Some code' -> code' = code /\ m_killed model' = None) ->
  ME (mkCfg ms model).
Proof.
  intros ms model x8 Hh Hsvc i Hmod (eff0 & m0 & evs0 & Hspec0 & Hadm0) Hrun Hhalt.
  apply must_exit_at_cfg_running.
  - exact Hh.
  - destruct (m_halted m0) as [c0|] eqn:Hh0.
    + do 2 eexists. eapply sstep_cfg_exit; [exact Hh | exact Hsvc | exact Hspec0 | exact Hh0
                                           | exact (proj2 (Hhalt _ _ _ _ Hspec0 Hh0))].
    + destruct (Hrun eff0 m0 evs0 Hspec0 (Hadm0 eq_refl) Hh0) as (m0' & Hmat & _).
      do 2 eexists. eapply sstep_cfg_syscall; [exact Hh | exact Hsvc | exact Hspec0 | exact (Hadm0 eq_refl) | exact Hh0 | exact Hmat].
  - intros evs Hss.
    destruct (sstep_cfg_sys_inv _ _ _ _ _ Hsvc Hss)
      as [(eff & m' & evs1 & Hspec & Hadm & Hh' & Hm) | [(eff & m' & evs1 & c' & _ & _ & _ & Hst) | (Hum & _ & _)]].
    + destruct (Hrun eff m' evs1 Hspec Hadm Hh') as (m'' & Hmat & _). rewrite Hmat in Hm.
      destruct Hm as [_ Hst]. discriminate Hst.
    + discriminate Hst.
    + exact (Hmod Hum).
  - intros evs c' Hss.
    destruct (sstep_cfg_sys_inv _ _ _ _ _ Hsvc Hss)
      as [(eff & m' & evs1 & Hspec & Hadm & Hh' & Hm) | [(eff & m' & evs1 & c'' & Hspec & Hh' & _ & Hst) | (_ & _ & Hst)]].
    + destruct (Hrun eff m' evs1 Hspec Hadm Hh') as (m'' & Hmat & Hme). rewrite Hmat in Hm.
      destruct Hm as [_ Hst]. injection Hst as ->. exact Hme.
    + injection Hst as ->. destruct (Hhalt _ _ _ _ Hspec Hh') as [<- Hk].
      apply must_exit_at_cfg_halted; cbn [cfg_model]; [exact Hh' | exact Hk].
    + discriminate Hst.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma me_cfg_syscall_fam : forall ms model x8 (P : SyscallEffect -> Model -> list event -> Prop),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  let i := sys_input segs ms x8 in
  (forall o, syscall_spec i model o <-> exists eff m' evs, o = Ok eff m' evs /\ P eff m' evs) ->
  (forall eff m' evs, P eff m' evs -> m_halted m' = None) ->
  (exists eff m' evs, P eff m' evs /\ ~ spurious_refusal_cfg b i model eff) ->
  (forall eff m' evs, P eff m' evs -> ~ spurious_refusal_cfg b i model eff ->
      exists m'', materialize_model_accesses m' (syscall_effect_accesses eff) = Some m''
                  /\ ME (mkCfg (advance_past_svc (apply_effect ms eff)) m'')) ->
  ME (mkCfg ms model).
Proof.
  intros ms model x8 P Hh Hsvc i Hchar Hrunning (eff0 & m0 & evs0 & HP0 & Hadm0) Hall.
  apply (me_cfg_syscall ms model x8 Hh Hsvc).
  - intros Hum. apply Hchar in Hum. destruct Hum as (? & ? & ? & Hum & _). discriminate Hum.
  - exists eff0, m0, evs0. split; [apply Hchar; eexists _, _, _; split; [reflexivity | exact HP0] |].
    intros _. exact Hadm0.
  - intros eff m' evs Hspec Hadm _. apply Hchar in Hspec.
    destruct Hspec as (? & ? & ? & Heq & HP). injection Heq as <- <- <-.
    exact (Hall _ _ _ HP Hadm).
  - intros eff m' evs c' Hspec Hh'. apply Hchar in Hspec.
    destruct Hspec as (? & ? & ? & Heq & HP). injection Heq as <- <- <-.
    rewrite (Hrunning _ _ _ HP) in Hh'. discriminate Hh'.
Qed.

(* [comment removed for export] *)
Lemma me_cfg_syscall_det : forall ms model x8 eff m' evs m'',
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok eff m' evs) ->
  ~ spurious_refusal_cfg b (sys_input segs ms x8) model eff ->
  m_halted m' = None ->
  materialize_model_accesses m' (syscall_effect_accesses eff) = Some m'' ->
  ME (mkCfg (advance_past_svc (apply_effect ms eff)) m'') ->
  ME (mkCfg ms model).
Proof.
  intros ms model x8 eff m' evs m'' Hh Hsvc Hchar Hadm Hh' Hmat Hme.
  apply (me_cfg_syscall_fam ms model x8 (fun e m v => e = eff /\ m = m' /\ v = evs) Hh Hsvc).
  - intros o. rewrite Hchar. split.
    + intros ->. eexists _, _, _. repeat split; reflexivity.
    + intros (? & ? & ? & -> & -> & -> & ->). reflexivity.
  - intros ? ? ? (_ & -> & _). exact Hh'.
  - eexists _, _, _. split; [repeat split; reflexivity | exact Hadm].
  - intros ? ? ? (-> & -> & ->) _. exists m''. split; [exact Hmat | exact Hme].
Qed.

(* [comment removed for export] *)
Lemma me_cfg_syscall_inv : forall ms model x8 eff m' evs m'',
  ms_svc_pending ms = Some x8 ->
  ME (mkCfg ms model) ->
  m_halted model = None ->
  syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
  ~ spurious_refusal_cfg b (sys_input segs ms x8) model eff ->
  m_halted m' = None ->
  materialize_model_accesses m' (syscall_effect_accesses eff) = Some m'' ->
  ME (mkCfg (advance_past_svc (apply_effect ms eff)) m'').
Proof.
  intros ms model x8 eff m' evs m'' Hsvc Hme Hh Hspec Hadm Hh' Hmat.
  inversion Hme as [c Hh0 Hc | c Hh0 Hprog Hnoerr Hnext Hc]; subst.
  - cbn [cfg_model] in Hh0. rewrite Hh in Hh0. discriminate Hh0.
  - apply (Hnext evs). eapply sstep_cfg_syscall; eassumption.
Qed.

End Syscall.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Nodes.
Variable b : SpuriousCfg.
Variable segs : list Segment.
Variable code : word.
Local Notation "'ME' c" := (must_exit_at_cfg b segs code c) (at level 10, c at level 9, only parsing).

(* [comment removed for export] *)
Lemma me_cfg_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (bv_unsigned x8 = 93%Z \/ bv_unsigned x8 = 94%Z) ->
  must_exit_at_cfg b segs (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (mkCfg ms model).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  assert (Hchar : forall o, syscall_spec (sys_input segs ms x8) model o <->
            o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []).
  { intros o. rewrite (syscall_spec_exit _ model o) by (rewrite in_sysno_sys_input; exact Hx8).
    rewrite (in_arg_sys_input segs ms x8 0) by lia. apply exit_outcome. }
  apply (me_cfg_syscall b segs _ ms model x8 Hh Hsvc).
  - intros Hum. apply Hchar in Hum. discriminate Hum.
  - eexists _, _, _. split; [apply Hchar; reflexivity|]. rewrite m_halted_with_halted. intros H; discriminate H.
  - intros eff m' evs Hspec _ Hh'. apply Hchar in Hspec. apply Ok_inj in Hspec as (_ & -> & _).
    rewrite m_halted_with_halted in Hh'. discriminate Hh'.
  - intros eff m' evs c' Hspec Hh'. apply Hchar in Hspec. apply Ok_inj in Hspec as (_ & -> & _).
    rewrite m_halted_with_halted in Hh'. injection Hh' as <-. split; [reflexivity | apply m_killed_with_halted].
Qed.

(* [comment removed for export] *)
Lemma bv_and_255_small : forall k, (0 <= k < 256)%Z ->
  bv_and (Z_to_bv 64 k) (Z_to_bv 64 255) = Z_to_bv 64 k.
Proof.
  intros k Hk. apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite !Z.mod_small by lia.
  replace 255%Z with (Z.ones 8) by reflexivity. rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2 ^ 8)%Z with 256%Z. lia.
Qed.

Lemma me_cfg_exit_lit : forall ms model x8 (k : Z),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (bv_unsigned x8 = 93%Z \/ bv_unsigned x8 = 94%Z) ->
  ms_gpr ms 0 = Z_to_bv 64 k -> (0 <= k < 256)%Z ->
  must_exit_at_cfg b segs (Z_to_bv 64 k) (mkCfg ms model).
Proof.
  intros ms model x8 k Hh Hsvc Hx8 Ha0 Hk.
  rewrite <- (bv_and_255_small k Hk), <- Ha0. exact (me_cfg_exit ms model x8 Hh Hsvc Hx8).
Qed.

(* [comment removed for export] *)
Lemma me_cfg_set_tid : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  (forall t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z ->
     ME (mkCfg (advance_past_svc (apply_effect ms (mkEffect t [] []))) (with_tid t model))) ->
  ME (mkCfg ms model).
Proof.
  intros ms model x8 Hh Hsvc Hx8 Htid Hk.
  apply (me_cfg_syscall_fam b segs code ms model x8
           (fun eff m' evs => exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z /\
                              eff = mkEffect t [] [] /\ m' = with_tid t model /\ evs = []) Hh Hsvc).
  - intros o. rewrite (syscall_spec_96 _ model o) by (rewrite in_sysno_sys_input; exact Hx8).
    rewrite (set_tid_fresh_outcome _ model o Htid). split.
    + intros (t & Ht & ->). eexists _, _, _. split; [reflexivity|]. exists t. split; [exact Ht|]. repeat split; reflexivity.
    + intros (? & ? & ? & -> & t & Ht & -> & -> & ->). exists t. split; [exact Ht|reflexivity].
  - intros eff m' evs (t & _ & _ & -> & _). rewrite m_halted_with_tid. exact Hh.
  - eexists _, _, _. split; [exists (Z_to_bv 64 1); split; [vm_compute; split; reflexivity|repeat split; reflexivity]|].
    apply (spurious_refusal_cfg_sysno b _ model _ 96); [rewrite in_sysno_sys_input; exact Hx8 | reflexivity].
  - intros eff m' evs (t & Ht & -> & -> & ->) _. exists (with_tid t model).
    split; [apply materialize_model_accesses_nil | exact (Hk t Ht)].
Qed.

End Nodes.

Section Nodes2.
Variable b : SpuriousCfg.
Variable segs : list Segment.
Variable code : word.
Local Notation "'ME' c" := (must_exit_at_cfg b segs code c) (at level 10, c at level 9, only parsing).

(* [comment removed for export] *)
Lemma me_cfg_ret : forall ms model x8 r m',
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  existsb (Z.eqb (bv_unsigned x8)) injected_sysnos = false ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok (mkEffect r [] []) m' []) ->
  m_halted m' = None ->
  ME (mkCfg (advance_past_svc (apply_effect ms (mkEffect r [] []))) m') ->
  ME (mkCfg ms model).
Proof.
  intros ms model x8 r m' Hh Hsvc Hout Hchar Hh' Hme.
  eapply (me_cfg_syscall_det b segs code ms model x8 _ m' [] m' Hh Hsvc Hchar);
    [| exact Hh' | apply materialize_model_accesses_nil | exact Hme].
  apply spurious_refusal_cfg_outside. rewrite in_sysno_sys_input. exact Hout.
Qed.

End Nodes2.
