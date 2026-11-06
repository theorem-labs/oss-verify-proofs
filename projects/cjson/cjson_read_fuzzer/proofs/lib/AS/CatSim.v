(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require List.
From Stdlib Require Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.LinuxProcessSem Require OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.EquivalenceDefinition Require OmniEquivalence.
Module SimInv.
(* [comment removed for export] *)

Import Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Unset Lia Cache.

Import ListNotations.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac norm_fd32 :=
  repeat match goal with
         | |- context [fd32 AT_FDCWD] =>
             change (fd32 AT_FDCWD) with AT_FDCWD32
         | H : context [fd32 AT_FDCWD] |- _ =>
             change (fd32 AT_FDCWD) with AT_FDCWD32 in H
         | |- context [fd32 ?x] => change (fd32 x) with x
         | H : context [fd32 ?x] |- _ => change (fd32 x) with x in H
         end.

(* [comment removed for export] *)
Ltac fd32_ok :=
  solve [ reflexivity
        | assumption
        | apply fd32_lt31; assumption
        | apply fd32_id; assumption
        | apply fd32_lt31; lia
        | apply fd32_id; lia ].

(* [comment removed for export] *)
Lemma star_inv (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c') :
  forall c tr c', Inv c -> star segs c tr c' -> Inv c'.
Proof.
  intros c tr c' HInv Hstar. induction Hstar; [exact HInv|].
  apply IHHstar. eapply Hstep; eauto.
Qed.

(* [comment removed for export] *)
Lemma inv_no_reaches_error (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep segs c evs SError) :
  forall c, Inv c -> ~ reaches_error segs c.
Proof.
  intros c HInv (tr & c' & evs & Hstar & Hss).
  eapply Hnoerr; [| exact Hss].
  eapply star_inv; eauto.
Qed.

(* [comment removed for export] *)
Lemma inv_coexec (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep segs c evs SError) :
  forall c, Inv c -> OmniRun.coexec segs c never_errors.
Proof.
  cofix CH. intros c HInv.
  destruct (m_halted (cfg_model c)) as [code |] eqn:Hh.
  - apply coexec_halt; [rewrite Hh; discriminate | exact (fun h => h)].
  - apply coexec_step; [exact Hh | |].
    + intros evs Hss. exfalso. exact (Hnoerr c evs HInv Hss).
    + intros evs c' Hss. exact (CH c' (Hstep c evs c' HInv Hss)).
Qed.

(* [comment removed for export] *)
Lemma no_error_run_corun :
  forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw)
         (lim : Z) (inp : ProcInput),
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp never_errors.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp H. cbn [omni_corun].
  apply no_error_coexec, H.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma no_error_run_modeled :
  forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw)
         (lim : Z) (inp : ProcInput),
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  Equivalence.modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp H.
  apply modeled_iff. cbn [img_segments].
  eapply coexec_conseq; [apply no_error_run_corun, H | apply never_errors_covered].
Qed.
End SimInv.

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require Bool.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require MustExit.
Module ExitSim.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.MustExit LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import SimInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Unset Lia Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_exit_no (no : word) : Prop :=
  bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.

Lemma syscall_spec_exit : forall i m o,
  is_exit_no (in_sysno i) ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof.
  intros i m o [E|E]; unfold syscall_spec, dispatch; rewrite E; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_ok : forall i m,
  is_exit_no (in_sysno i) ->
  syscall_spec i m
    (Ok (mkEffect (Z_to_bv 64 0) [] [])
        (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []).
Proof.
  intros i m Hno. apply (proj2 (syscall_spec_exit i m _ Hno)).
  unfold exit_spec, set_halted, ret_only, modify, bind, pure. cbn.
  eexists tt, (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m),
    [], []. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_ok_inv : forall i m eff m' evs,
  is_exit_no (in_sysno i) ->
  syscall_spec i m (Ok eff m' evs) ->
  eff = mkEffect (Z_to_bv 64 0) [] [] /\
  m' = with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m /\ evs = [].
Proof.
  intros i m eff m' evs Hno Hspec.
  apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct. rewrite app_nil_l in *. repeat split; congruence.
Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_no_unmodeled : forall i m,
  is_exit_no (in_sysno i) -> ~ syscall_spec i m Unmodeled.
Proof.
  intros i m Hno Hspec.
  apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct.
Qed.

(* [comment removed for export] *)
Lemma in_arg0_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma in_sysno_sys_input : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable code : word.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive to_exit : machine_state -> Prop :=
| te_here : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    ms_gpr ms 0 = code ->
    to_exit ms
| te_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_exit ms' ->
    to_exit ms.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint sim_c (fuel : nat) (ms : machine_state) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    match ms_svc_pending ms with
    | Some x8 => ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z)
                 && bv_eqb (ms_gpr ms 0) code
    | None =>
      match RiscvSemantics.step segs ms with
      | MachineOk ms' => sim_c fuel' ms'
      | MachineFault | MachineUnmodeled => false
      end
    end
  end.

Lemma sim_c_to_exit : forall fuel ms, sim_c fuel ms = true -> to_exit ms.
Proof.
  induction fuel as [|fuel IH]; intros ms H; [discriminate|].
  cbn in H. destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
  - apply andb_true_iff in H as [Hx8 Hgpr].
    apply bv_eqb_eq in Hgpr.
    eapply te_here; eauto.
    apply orb_true_iff in Hx8. destruct Hx8 as [H|H]; apply Z.eqb_eq in H;
      [left|right]; exact H.
  - destruct (RiscvSemantics.step segs ms) as [ms'| |] eqn:Hstep;
      [|discriminate|discriminate].
    eapply te_step; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sim_step : forall fuel ms ms',
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sim_c fuel ms' = true ->
  sim_c (S fuel) ms = true.
Proof.
  intros fuel ms ms' Hsvc Hstep Hrec.
  cbn [sim_c]. rewrite Hsvc. cbv beta iota. rewrite Hstep. exact Hrec.
Qed.

(* [comment removed for export] *)
Lemma sim_c_exit_now : forall fuel ms x8,
  ms_svc_pending ms = Some x8 ->
  ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z) = true ->
  bv_eqb (ms_gpr ms 0) code = true ->
  sim_c (S fuel) ms = true.
Proof.
  intros fuel ms x8 Hsvc Hx8 Hcode.
  cbn [sim_c]. rewrite Hsvc. cbv beta iota. rewrite Hx8. cbn [andb]. exact Hcode.
Qed.

(* [comment removed for export] *)
Lemma sim_ecall_exit : forall fuel ms,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some 0x73 ->
  ((bv_unsigned (ms_reg ms 17) =? 93)%Z || (bv_unsigned (ms_reg ms 17) =? 94)%Z) = true ->
  bv_eqb (ms_gpr ms 0) code = true ->
  sim_c (S (S fuel)) ms = true.
Proof.
  intros fuel ms Hsvc Hfetch Hcheck Hcode.
  set (ms1 := {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
                 ms_svc_pending := Some (ms_reg ms 17); ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
                 ms_mem := ms_mem ms; ms_rom := ms_rom ms |}).
  apply (sim_step (S fuel) ms ms1 Hsvc).
  - change (drop_access_report (step_accesses segs ms) = MachineOk ms1).
    unfold step_accesses. rewrite Hfetch. unfold ms1. reflexivity.
  - apply (sim_c_exit_now fuel ms1 (ms_reg ms 17)).
    + subst ms1. reflexivity.
    + exact Hcheck.
    + exact Hcode.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_instr_inv : forall ms model ms' evs st,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\ st = SNext (mkCfg ms' model).
Proof.
  intros ms model ms' evs st Hlazy Hsvc Hstep Hss.
  inversion Hss; subst.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; inversion H; subst end.
    split; reflexivity.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step segs ms model = MachineFault |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
Qed.

(* [comment removed for export] *)
Lemma sstep_exit_inv : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)] /\
  st = SNext (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
Proof.
  intros ms model x8 evs st Hh Hsvc Hx8 Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    autorewrite with model in *.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' ?evs0),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (Heff & Hm & Hevs);
      rewrite in_arg0_sys_input in Hm;
      subst evs0 model';
      assert (Hcode : code = bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
        by (autorewrite with model in H6; congruence);
      subst code
    end.
    cbn. split; reflexivity.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled,
      H2 : ms_svc_pending ms = Some ?x |- _ =>
      eapply exit_dispatch_no_unmodeled; [| exact H3];
      rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8
    end.
Qed.

(* [comment removed for export] *)
Lemma star_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star segs c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
  - split; reflexivity.
  - exfalso. destruct c as [ms model]. cbn in Hh.
    inversion Hss; subst; cbn in Hh; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition exit_post (fs : Fs.Fs) : post :=
  fun tr o => tr = [ExitEv (bv_and code (Z_to_bv 64 255)) fs]
              /\ exits_with (bv_and code (Z_to_bv 64 255)) tr o.

Lemma to_exit_exec : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  OmniRun.exec segs (mkCfg ms model) (exit_post (m_fs model)).
Proof.
  intros ms model Hh Hlazy Hte.
  induction Hte as [ms x8 Hsvc Hx8 Hgpr | ms ms' Hsvc Hstep Hte IH].
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * unfold exit_post. cbn beta. rewrite app_nil_r, Hgpr. split; [reflexivity |].
        cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact IH |]. intros tr o H. cbn [app]. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_exit_star_only : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    tr = [] \/ tr = [ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)].
Proof.
  intros ms model Hh Hlazy Hte tr c Hstar.
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_exit_exec ms model Hh Hlazy Hte) Hstar))
    as (tr' & o & _ & HQ).
  unfold exit_post in HQ. cbn beta in HQ. destruct HQ as (Heq & _).
  destruct (app_eq_unit _ _ Heq) as [(-> & _) | (-> & _)]; [left | right]; reflexivity.
Qed.

Lemma to_exit_star_admits : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  exists c, star segs (mkCfg ms model)
              [ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)] c.
Proof.
  intros ms model Hh Hlazy Hte.
  destruct (exec_realizes _ _ _ (to_exit_exec ms model Hh Hlazy Hte))
    as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
  subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  exists c'. exact Hstar.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition on_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
   to_exit (cfg_ms c))
  \/ m_halted (cfg_model c) <> None.

Lemma on_path_step : forall c evs c',
  on_path c -> sstep segs c evs (SNext c') -> on_path c'.
Proof.
  intros [ms model] evs [ms' model'] Hop Hss.
  unfold on_path in *; cbn in Hop |- *.
  destruct Hop as [[Hh [Hlazy Hte]] | Hh].
  - destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
    + (* [comment removed for export] *)
      destruct (sstep_exit_inv ms0 model x8 evs (SNext (mkCfg ms' model'))
                  Hh Hsvc Hx8 Hss) as [_ Hc'].
      inversion Hc'; subst. right. cbn. discriminate.
    + (* [comment removed for export] *)
      destruct (sstep_instr_inv ms0 model ms0' evs (SNext (mkCfg ms' model'))
                  Hlazy Hsvc Hstep Hss) as [_ Hc'].
      inversion Hc'; subst. left. repeat split; assumption.
  - (* [comment removed for export] *)
    exfalso. inversion Hss; subst; cbn in Hh; congruence.
Qed.

Lemma on_path_no_error : forall c evs, on_path c -> ~ sstep segs c evs SError.
Proof.
  intros [ms model] evs Hop Hss.
  unfold on_path in *; cbn in Hop.
  destruct Hop as [[Hh [Hlazy Hte]] | Hh].
  - destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
    + destruct (sstep_exit_inv ms0 model x8 evs SError Hh Hsvc Hx8 Hss) as [_ Hc'].
      discriminate.
    + destruct (sstep_instr_inv ms0 model ms0' evs SError Hlazy Hsvc Hstep Hss) as [_ Hc'].
      discriminate.
  - inversion Hss; subst; cbn in Hh; congruence.
Qed.

Lemma star_on_path : forall c tr c',
  on_path c -> star segs c tr c' -> on_path c'.
Proof. exact (star_inv segs on_path on_path_step). Qed.

Lemma to_exit_no_error : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model Hh Hlazy Hte. apply exec_no_error.
  eapply exec_conseq; [exact (to_exit_exec ms model Hh Hlazy Hte) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition overlay_argc_bytes (sp : word) (argc : nat)
    (base_mem : word -> option byte) : word -> option byte :=
  let bytes := word_le8 (nat_to_word argc) in
  fun addr =>
    if (bv_unsigned addr =? bv_unsigned sp)%Z then nth_error bytes 0
    else if (bv_unsigned addr =? bv_unsigned sp + 1)%Z then nth_error bytes 1
    else if (bv_unsigned addr =? bv_unsigned sp + 2)%Z then nth_error bytes 2
    else if (bv_unsigned addr =? bv_unsigned sp + 3)%Z then nth_error bytes 3
    else if (bv_unsigned addr =? bv_unsigned sp + 4)%Z then nth_error bytes 4
    else if (bv_unsigned addr =? bv_unsigned sp + 5)%Z then nth_error bytes 5
    else if (bv_unsigned addr =? bv_unsigned sp + 6)%Z then nth_error bytes 6
    else if (bv_unsigned addr =? bv_unsigned sp + 7)%Z then nth_error bytes 7
    else base_mem addr.

Lemma stm_at (sp : word) (bytes : list byte) (addr : word) (i : nat) :
  (i < length bytes)%nat ->
  bv_unsigned addr = (bv_unsigned sp + Z.of_nat i)%Z ->
  stack_to_mem sp bytes addr = nth_error bytes i.
Proof.
  intros Hi Haddr. unfold stack_to_mem. rewrite Haddr. cbv beta zeta.
  destruct (Z.leb (bv_unsigned sp) (bv_unsigned sp + Z.of_nat i)) eqn:E1.
  2: { apply Z.leb_gt in E1; lia. }
  replace (bv_unsigned sp + Z.of_nat i - bv_unsigned sp)%Z with (Z.of_nat i) by lia.
  destruct (Z.ltb (Z.of_nat i) (Z.of_nat (length bytes))) eqn:E2.
  - rewrite Nat2Z.id. reflexivity.
  - apply Z.ltb_ge in E2. lia.
Qed.

Lemma build_stack_starts_with_argc :
  forall ph sp argv envp uid hw rnd,
  exists rest,
    build_stack_bytes ph sp argv envp uid hw rnd =
    word_le8 (nat_to_word (length argv)) ++ rest.
Proof.
  intros ph sp argv envp uid hw rnd. unfold build_stack_bytes, len_word, nat_to_word.
  destruct (string_addrs _ argv) as [? ?]. destruct (string_addrs _ envp) as [? ?].
  eexists. exact (eq_sym (app_assoc _ _ _)).
Qed.

Lemma word_le8_length : forall v, length (word_le8 v) = 8%nat.
Proof. intro v. reflexivity. Qed.

Lemma build_stack_min_length : forall ph sp argv envp uid hw rnd,
  (8 <= length (build_stack_bytes ph sp argv envp uid hw rnd))%nat.
Proof.
  intros ph sp argv envp uid hw rnd.
  destruct (build_stack_starts_with_argc ph sp argv envp uid hw rnd) as [rest Hr].
  rewrite Hr, length_app, word_le8_length. lia.
Qed.

(* [comment removed for export] *)
Lemma init_first8 :
  forall segs init_pc ph init_sp init_rnd argv envp addr i uid hw, (i < 8)%nat ->
  bv_unsigned addr = (bv_unsigned init_sp + Z.of_nat i)%Z ->
  ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw) addr =
  nth_error (word_le8 (nat_to_word (length argv))) i.
Proof.
  intros segs init_pc ph init_sp init_rnd argv envp addr i uid hw Hi Haddr.
  assert (Hstk : stack_to_mem init_sp (entry_stack_image ph init_sp argv envp uid hw init_rnd) addr
                 = nth_error (word_le8 (nat_to_word (length argv))) i).
  { rewrite stack_to_mem_image_in_block
      by (pose proof (build_stack_min_length ph init_sp argv envp uid hw init_rnd);
          unfold entry_block_top; lia).
    rewrite (stm_at init_sp _ addr i);
      [ | pose proof (build_stack_min_length ph init_sp argv envp uid hw init_rnd); lia
        | exact Haddr ].
    destruct (build_stack_starts_with_argc ph init_sp argv envp uid hw init_rnd) as [rest Hr].
    rewrite Hr. apply nth_error_app1. rewrite word_le8_length. lia. }
  change (ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw) addr)
    with (match stack_to_mem init_sp (entry_stack_image ph init_sp argv envp uid hw init_rnd) addr with
          | Some b => Some b
          | None =>
              if andb (Z.leb (bv_unsigned init_sp - stack_max_size)
                             (bv_unsigned addr))
                      (Z.ltb (bv_unsigned addr) (bv_unsigned init_sp))
              then Some (Z_to_bv 8 0) else None
          end).
  rewrite Hstk.
  destruct (nth_error (word_le8 (nat_to_word (length argv))) i) eqn:E; [reflexivity|].
  apply nth_error_None in E. rewrite word_le8_length in E. lia.
Qed.

Lemma actual_mem_is_overlay :
  forall segs init_pc ph init_sp init_rnd argv envp uid hw,
  ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw) =
  overlay_argc_bytes init_sp (length argv)
    (ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw)).
Proof.
  intros segs init_pc ph init_sp init_rnd argv envp uid hw.
  apply functional_extensionality. intro addr.
  unfold overlay_argc_bytes.
  destruct ((bv_unsigned addr =? bv_unsigned init_sp)%Z) eqn:E0;
    [ apply Z.eqb_eq in E0;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 0 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 1)%Z) eqn:E1;
    [ apply Z.eqb_eq in E1;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 1 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 2)%Z) eqn:E2;
    [ apply Z.eqb_eq in E2;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 2 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 3)%Z) eqn:E3;
    [ apply Z.eqb_eq in E3;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 3 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 4)%Z) eqn:E4;
    [ apply Z.eqb_eq in E4;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 4 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 5)%Z) eqn:E5;
    [ apply Z.eqb_eq in E5;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 5 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 6)%Z) eqn:E6;
    [ apply Z.eqb_eq in E6;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 6 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 7)%Z) eqn:E7;
    [ apply Z.eqb_eq in E7;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 7 uid hw); lia | ].
  reflexivity.
Qed.

Lemma machine_state_eta : forall ms : machine_state,
  ms = {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
          ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
          ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.
Proof. intros []; reflexivity. Qed.

(* [comment removed for export] *)
Definition enum_state (segs : list Segment) (init_pc : N) (ph : PhdrInfo)
    (init_sp : word) (init_rnd : EntryDraw) (argc : nat)
    (base : word -> option byte) (uid : word)
    (hw : word) : machine_state :=
  {| ms_regs       := ms_regs (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw); ms_fregs := ms_fregs (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
     ms_pc_val     := ms_pc_val (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
     ms_svc_pending := ms_svc_pending (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
     ms_resv       := ms_resv (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw); ms_fcsr := ms_fcsr (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
     ms_mem        := overlay_argc_bytes init_sp argc base;
     ms_rom        := ms_rom (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw) |}.

(* [comment removed for export] *)
Lemma init_eq_enum_state :
  forall segs init_pc ph init_sp init_rnd argv envp uid hw,
  init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw =
  enum_state segs init_pc ph init_sp init_rnd (length argv)
    (ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw)) uid hw.
Proof.
  intros segs init_pc ph init_sp init_rnd argv envp uid hw. unfold enum_state.
  rewrite (machine_state_eta (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw)) at 1.
  f_equal; try reflexivity. apply actual_mem_is_overlay.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma exit_omni_run : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c segs code F (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (exit_post code (in_fs inp)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim.
  cbn [omni_run]. unfold init_config.
  exact (to_exit_exec segs code
           (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
           (init_model (segments_reserved segs) brk0 mb sp lim inp)
           eq_refl eq_refl (sim_c_to_exit segs code F _ Hsim)).
Qed.

Lemma exit_obs_iff : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c segs code F (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
             <-> is_prefix tr [ExitEv (bv_and code (Z_to_bv 64 255)) (in_fs inp)].
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim tr.
  apply exec_obs_iff.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.

Lemma exit_no_error_run : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c segs code F (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply exec_no_error.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
Lemma exit_must_exit_with : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c segs code F (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  must_exit_with (bv_and code (Z_to_bv 64 255)) (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply must_exit_with_iff.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr o (_ & Hx). exact Hx.
Qed.

Lemma exit_omni_run_code_unique : forall segs pc ph sp brk0 mb rnd lim code inp F code',
  sim_c segs code F (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (exits_with code') ->
  code' = bv_and code (Z_to_bv 64 255).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F code' Hsim Hex.
  pose proof (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) as Hrun.
  cbn [omni_run] in Hrun, Hex.
  destruct (exec_realizes _ _ _ Hrun) as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'. symmetry. exact Hx'.
Qed.

(* [comment removed for export] *)
Lemma exit_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA,
  sim_c source_segs code FR
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  sim_c target_segs code FA
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA
    Hsource Htarget.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (exit_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource) |].
    intros tr o (_ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource tr).
    rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (exit_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget).
Qed.

(* [comment removed for export] *)
Lemma exit_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA,
  sim_c source_segs code FR
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  sim_c target_segs code FA
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA
    Hsource Htarget.
  split.
  { apply no_error_run_modeled.
    apply (exit_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource tr).
    rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd alim code inp FA Htarget tr).
    reflexivity.
  - cbn. apply (exit_no_error_run target_segs apc aph asp abrk amb arnd alim code inp FA Htarget).
Qed.
End ExitSim.

(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
Import SimInv.
Import ExitSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Unset Lia Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma read_aux_read_byte : forall ms k a,
  read_bytes_aux (ms_read_byte ms) a k = ms_read_bytes_aux ms a k.
Proof.
  intros ms. induction k as [|k IH]; intro a; [reflexivity|].
  cbn [read_bytes_aux ms_read_bytes_aux].
  destruct (ms_read_byte ms a) as [b|]; [rewrite IH|]; reflexivity.
Qed.

Lemma read_bytes_map_read_byte : forall ms a len,
  read_bytes_map (ms_read_byte ms) a len = ms_read_bytes ms a len.
Proof. intros. rewrite read_bytes_map_eq. unfold ms_read_bytes.
  apply read_aux_read_byte. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma apply_effect_no_write : forall ms r,
  apply_effect ms (mkEffect r [] []) = set_gpr0 ms r.
Proof.
  intros ms r. unfold apply_effect, set_gpr0.
  cbn [eff_ret eff_writes eff_zeros apply_zeros apply_writes].
  reflexivity.
Qed.

Lemma apply_effect_copyins_no_write : forall ms r copyins,
  apply_effect ms (with_copyins copyins (mkEffect r [] [])) = set_gpr0 ms r.
Proof.
  intros ms r copyins. unfold with_copyins, apply_effect, set_gpr0.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies
       apply_unmaps apply_zeros apply_copies apply_writes].
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sysno_sys_input64 : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
Lemma in_arg0_sys_input64 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.
Lemma in_arg1_sys_input64 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.
Lemma in_arg2_sys_input64 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.
Lemma in_mem_sys_input : forall segs ms x8,
  in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma syscall_spec_write : forall segs ms x8 model o,
  bv_unsigned x8 = 64%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> write_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
         (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  change (in_sysno (sys_input segs ms x8)) with x8.
  rewrite Hno. reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fd1chan (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).

(* [comment removed for export] *)
Definition buf_modeled (b : list byte) : Prop :=
  (Z.of_nat (length b) <= rw_bytes_max)%Z.

Definition bufs_modeled (bufs : list (list byte)) : Prop :=
  Forall buf_modeled bufs.

(* [comment removed for export] *)
Lemma bufs_modeled_single : forall b, buf_modeled b -> bufs_modeled [b].
Proof. intros b H. apply Forall_cons; [exact H | apply Forall_nil]. Qed.

(* [comment removed for export] *)
Lemma buf_modeled_nil : buf_modeled [].
Proof. unfold buf_modeled. cbn. unfold rw_bytes_max. lia. Qed.

Lemma buf_modeled_skipn : forall n (b : list byte),
  buf_modeled b -> buf_modeled (skipn n b).
Proof.
  intros n b H. unfold buf_modeled in *. rewrite length_skipn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma write1_check_n : forall segs ms x8 model buf n,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  check_write (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (with_copyins [(ms_gpr ms 1, n)]
      (mkEffect (len_word (firstn n buf)) [] [])) model
    = CheckOk model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf)).
Proof.
  intros segs ms x8 model buf n Hfd Hno Hg Hr Hcnt Hn1 Hn2.
  unfold fd1chan in Hfd.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  pose proof (word_unsigned_range (ms_gpr ms 2)) as Hcr.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  unfold check_write.
  rewrite Hg; norm_fd32; rewrite Hfd.
  change (w_is0 (Z_to_bv 64 1)) with false. cbv beta iota.
  rewrite Hmc. cbv beta iota.
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc. cbv beta iota. cbv zeta.
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb).
  assert (Hg0 : Nat.eqb (length buf) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hg0. cbv beta iota. unfold with_copyins; cbn.
  assert (Hlenf : Z.of_nat (length (firstn n buf)) = Z.of_nat n)
    by (rewrite length_firstn; lia).
  assert (Hru : bv_unsigned (len_word (firstn n buf)) = Z.of_nat n).
  { rewrite (len_word_unsigned (firstn n buf));
      [exact Hlenf | rewrite Hlenf; lia]. }
  rewrite ?Hru.
  assert (Hg1 : (1 <=? Z.of_nat n)%Z = true) by (apply Z.leb_le; lia).
  assert (Hg2 : (Z.of_nat n <=? Z.of_nat (length buf))%Z = true)
    by (apply Z.leb_le; lia).
  rewrite ?Hg1, ?Hg2. cbn [andb].
  rewrite ?Nat2Z.id, bv_eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma write1_ok_n : forall segs ms x8 model buf n,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (with_copyins [(ms_gpr ms 1, n)]
          (mkEffect (len_word (firstn n buf)) [] [])) model
        (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
Proof.
  intros segs ms x8 model buf n Hfd Hno Hg Hr Hcnt Hn1 Hn2.
  apply (proj2 (syscall_spec_write _ _ _ _ _ Hno)).
  apply check_write_sound_ok. apply write1_check_n; assumption.
Qed.

(* [comment removed for export] *)
Lemma write1_ok_inv : forall segs ms x8 model eff model' evs buf,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (1 <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    eff = with_copyins [(ms_gpr ms 1, n)]
            (mkEffect (len_word (firstn n buf)) [] []) /\ model' = model /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf).
Proof.
  intros segs ms x8 model eff model' evs buf Hfd Hno Hg Hr Hnb Hspec.
  unfold fd1chan in Hfd.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply check_write_complete_ok in Hspec.
  unfold check_write in Hspec.
  rewrite Hg in Hspec; norm_fd32; rewrite Hfd in Hspec.
  change (w_is0 (Z_to_bv 64 1)) with false in Hspec. cbv beta iota in Hspec.
  (* [comment removed for export] *)
  destruct (negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)));
    cbv beta iota in Hspec; [discriminate|].
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc in Hspec. cbv beta iota zeta in Hspec.
  (* [comment removed for export] *)
  rewrite (write_source_prefix _ _ _ _ Hrb) in Hspec.
  pose proof (rw_count_clamp_range (ms_gpr ms 2)) as Hcl.
  set (c := Z.to_nat (rw_count_clamp (ms_gpr ms 2))) in *.
  assert (Hcpos : (1 <= c)%nat)
    by (unfold c, rw_count_clamp, MAX_RW_COUNT in *; lia).
  assert (Hfl : length (firstn c buf) = Nat.min c (length buf))
    by apply length_firstn.
  assert (Hg0 : Nat.eqb (length (firstn c buf)) 0 = false)
    by (rewrite Hfl; apply Nat.eqb_neq; lia).
  rewrite Hg0 in Hspec. cbv beta iota in Hspec.
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
    destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; try discriminate.
  destruct ((1 <=? bv_unsigned ret)%Z
            && (bv_unsigned ret <=? Z.of_nat (length (firstn c buf)))%Z) eqn:Hgr;
    [|discriminate].
  destruct (access_ranges_eqb copyins [(ms_gpr ms 1, Z.to_nat (bv_unsigned ret))])
    eqn:Hreads; [|discriminate].
  inversion Hspec; clear Hspec; subst.
  apply andb_true_iff in Hgr as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  rewrite Hfl in H2.
  apply access_ranges_eqb_eq in Hreads. subst copyins.
  exists (Z.to_nat (bv_unsigned ret)).
  assert (Hff : firstn (Z.to_nat (bv_unsigned ret)) (firstn c buf)
                = firstn (Z.to_nat (bv_unsigned ret)) buf)
    by (rewrite firstn_firstn; f_equal; lia).
  rewrite Hff.
  assert (Hlw : len_word (firstn (Z.to_nat (bv_unsigned ret)) buf) = ret)
    by (apply len_word_firstn_ret; lia).
  rewrite Hlw. repeat split; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma write1_no_unmodeled : forall segs ms x8 model buf,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (* [comment removed for export] *)
  (1 <= length buf)%nat ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb Hspec.
  unfold fd1chan in Hfd.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply (check_write_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_write in Hspec.
  rewrite Hg in Hspec; norm_fd32; rewrite Hfd in Hspec.
  change (w_is0 (Z_to_bv 64 1)) with false in Hspec. cbv beta iota in Hspec.
  rewrite Hmc in Hspec. cbv beta iota in Hspec.
  destruct (w_is0 (ms_gpr ms 2)) eqn:Hc; try rewrite Hc in Hspec.
  { exfalso.
    assert (Hc0 : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
    congruence. }
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb)
    in Hspec.
  destruct (length buf =? 0)%nat eqn:Hz; try rewrite Hz in Hspec.
  { now apply check_ret_only_no_unmodeled in Hspec. }
  discriminate Hspec.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma is_prefix_app_mono {A} : forall (l a b : list A),
  is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof.
  induction l as [|x l IH]; intros a b H; cbn; [exact H | split; [reflexivity | apply IH; exact H]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint wevents_ch (ch : word) (bufs : list (list byte)) : list event :=
  match bufs with
  | [] => []
  | buf :: rest => map (WriteEv ch) buf ++ wevents_ch ch rest
  end.

Inductive wpick (ch : word) : list (list byte) -> list event -> Prop :=
| wp_nil : wpick ch [] []
| wp_cons : forall buf bufs n tr,
    (1 <= n)%nat -> (n <= length buf)%nat ->
    wpick ch bufs tr ->
    wpick ch (buf :: bufs) (map (WriteEv ch) (firstn n buf) ++ tr).

(* [comment removed for export] *)
Lemma wpick_wevents : forall ch bufs,
  Forall (fun b => (1 <= length b)%nat) bufs ->
  wpick ch bufs (wevents_ch ch bufs).
Proof.
  intros ch bufs H; induction H as [|b bs Hb Hbs IH].
  - apply wp_nil.
  - cbn [wevents_ch].
    pose proof (wp_cons ch b bs (length b) _ Hb (Nat.le_refl _) IH) as Hc.
    rewrite firstn_all in Hc. exact Hc.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive to_wexit : machine_state -> list (list byte) -> word -> Prop :=
| tw_exit : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    to_wexit ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| tw_write : forall ms x8 buf bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
    (1 <= length buf)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
       to_wexit (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
    to_wexit ms (buf :: bufs) code
| tw_step : forall ms ms' bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wexit ms' bufs code ->
    to_wexit ms bufs code.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive msteps : machine_state -> machine_state -> Prop :=
| mst_refl : forall ms, msteps ms ms
| mst_step : forall ms ms' ms'',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    msteps ms' ms'' ->
    msteps ms ms''.

Lemma msteps_one : forall ms ms',
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  msteps ms ms'.
Proof. intros ms ms' Hsvc Hstep. eapply mst_step; [exact Hsvc | exact Hstep | apply mst_refl]. Qed.

Lemma msteps_trans : forall ms ms' ms'',
  msteps ms ms' -> msteps ms' ms'' -> msteps ms ms''.
Proof.
  intros ms ms' ms'' H; induction H; [auto|].
  intro H2. eapply mst_step; eauto.
Qed.

Lemma msteps_to_wexit : forall ms ms' bufs code,
  msteps ms ms' -> to_wexit ms' bufs code -> to_wexit ms bufs code.
Proof.
  intros ms ms' bufs code H; induction H; [auto|].
  intro Hw. eapply tw_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma to_wexit_bufs_nonempty : forall ms bufs code,
  to_wexit ms bufs code ->
  Forall (fun b => (1 <= length b)%nat) bufs.
Proof.
  intros ms bufs code H;
    induction H as
      [ms x8 Hsvc Hx8
      | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
      | ms ms' bufs code Hsvc Hstep Hte IH].
  - constructor.
  - constructor; [exact Hnb | apply (IH (length buf)); lia].
  - exact IH.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_write_next_inv : forall ms model x8 buf evs c',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs (SNext c') ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
    c' = mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model.
Proof.
  intros ms model x8 buf evs c' Hh Hlazy Hfd Hsvc Hno Hg Hr Hnb Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
        as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
      subst eff model' evs0; exists n
    end.
    match goal with
    | Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
        rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
        inversion Hmat; subst model''
    end.
    rewrite apply_effect_copyins_no_write. repeat split; auto.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite Hh in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite (m_killed_of_m_halted_none model Hh) in H6;
      discriminate
    end.
Qed.

Lemma sstep_write_inv : forall ms model x8 buf evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs st ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
    st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model).
Proof.
  intros ms model x8 buf evs st Hh Hlazy Hfd Hsvc Hno Hg Hr Hcnt Hnb Hss.
  destruct st as [c'|].
  - destruct (sstep_write_next_inv ms model x8 buf evs c'
                Hh Hlazy Hfd Hsvc Hno Hg Hr Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc').
    exists n. repeat split; [exact Hn1 | exact Hn2 | exact Hevs | now rewrite Hc'].
  - (* [comment removed for export] *)
    exfalso. inversion Hss; subst; try congruence.
    + match goal with
      | H2 : ms_svc_pending ms = Some ?x,
        H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
        Hmat : materialize_model_accesses ?model' _ = None |- _ =>
        assert (Hx : x = x8) by congruence; subst x;
        destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf
                    Hfd Hno Hg Hr Hnb H3)
          as (n & _ & _ & _ & Hm & _);
        subst model'; rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
        discriminate
      end.
    + match goal with
      | H2 : ms_svc_pending ms = Some ?x,
        H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
        assert (Hx : x = x8) by congruence; subst x;
        apply (write1_no_unmodeled segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb H3)
      end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint wevents (bufs : list (list byte)) : list event :=
  match bufs with
  | [] => []
  | buf :: rest => map (WriteEv (Z_to_bv 64 1)) buf ++ wevents rest
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wexit_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
  fun tr o =>
    (exists full, wpick (Z_to_bv 64 1) bufs full /\ tr = full ++ [ExitEv code fs])
    /\ exits_with code tr o.

Lemma to_wexit_exec : forall ms bufs code,
  to_wexit ms bufs code ->
  forall model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  bufs_modeled bufs ->
  OmniRun.exec segs (mkCfg ms model) (wexit_post bufs code (m_fs model)).
Proof.
  intros ms bufs code Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model Hh Hlazy Hfd Hbm.
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * unfold wexit_post. cbn beta. rewrite app_nil_r. split.
        -- exists []. split; [apply wp_nil | reflexivity].
        -- cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* [comment removed for export] *)
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    apply exec_step; [exact Hh | | |].
    + (* [comment removed for export] *)
      eexists; eexists.
      apply (sstep_syscall segs ms model x8
               (with_copyins [(ms_gpr ms 1, length buf)]
                  (mkEffect (len_word (firstn (length buf) buf)) [] [])) model model
               (map (WriteEv (Z_to_bv 64 1)) (firstn (length buf) buf))).
      * exact Hh.
      * exact Hsvc.
      * apply write1_ok_n; try assumption. apply Nat.le_refl.
      * exact Hh.
      * rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
    + intros evs Hss.
      destruct (sstep_write_inv ms model x8 buf evs SError
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hb Hnb Hss) as (n & _ & _ & _ & Habs).
      discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_write_inv ms model x8 buf evs (SNext c')
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hb Hnb Hss) as (n & Hn1 & Hn2 & -> & Hc').
      injection Hc' as ->.
      eapply exec_conseq; [exact (IH n Hn1 Hn2 model Hh Hlazy Hfd Hbs) |].
      intros tr o ((full & Hpick & ->) & Hx). split.
      * exists (map (WriteEv (Z_to_bv 64 1)) (firstn n buf) ++ full).
        split; [apply wp_cons; assumption | apply app_assoc].
      * exact Hx.
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH model Hh Hlazy Hfd Hbm) |].
      intros tr o H. cbn [app]. exact H.
Qed.

Lemma to_wexit_star_admits : forall ms bufs code,
  to_wexit ms bufs code ->
  forall model full,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  bufs_modeled bufs ->
  wpick (Z_to_bv 64 1) bufs full ->
  exists c, star segs (mkCfg ms model) (full ++ [ExitEv code (m_fs model)]) c.
Proof.
  intros ms bufs code Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model full Hh Hlazy Hfd Hbm Hpick.
  - (* [comment removed for export] *)
    inversion Hpick; subst. cbn [app].
    exists (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
    apply star_one.
    replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
      with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                     (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
      by (cbn; reflexivity).
    apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
             (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
             (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
    + exact Hh.
    + exact Hsvc.
    + apply (exit_dispatch_ok (sys_input segs ms x8) model).
      rewrite in_sysno_sys_input. exact Hx8.
    + cbn. reflexivity.
    + apply m_killed_with_halted.
  - (* [comment removed for export] *)
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    inversion Hpick as [|buf' bufs' n tr Hn1 Hn2 Hpick']; subst.
    destruct (IH n Hn1 Hn2 model tr Hh Hlazy Hfd Hbs Hpick') as [c Hstar].
    exists c. rewrite <- app_assoc.
    eapply star_step; [| exact Hstar].
    rewrite <- (apply_effect_copyins_no_write ms
                  (len_word (firstn n buf)) [(ms_gpr ms 1, n)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, n)]
                (mkEffect (len_word (firstn n buf)) [] [])) model model
             (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
    + exact Hh.
    + exact Hsvc.
    + apply write1_ok_n; assumption.
    + exact Hh.
    + rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
  - (* [comment removed for export] *)
    destruct (IH model full Hh Hlazy Hfd Hbm Hpick) as [c Hstar].
    exists c.
    replace (full ++ [ExitEv code (m_fs model)])
      with ([] ++ (full ++ [ExitEv code (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma to_wexit_star_only : forall ms bufs code,
  to_wexit ms bufs code ->
  forall model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  bufs_modeled bufs ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    exists full, wpick (Z_to_bv 64 1) bufs full /\
      is_prefix tr (full ++ [ExitEv code (m_fs model)]).
Proof.
  intros ms bufs code Hte model Hh Hlazy Hfd Hbm tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (to_wexit_exec ms bufs code Hte model Hh Hlazy Hfd Hbm) Hstar))
    as (tr' & o & _ & HQ).
  unfold wexit_post in HQ. cbn beta in HQ. destruct HQ as ((full & Hpick & Heq) & _).
  exists full. split; [exact Hpick |]. rewrite <- Heq. apply is_prefix_app.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_wexit_no_error : forall ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  to_wexit ms bufs code ->
  bufs_modeled bufs ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model bufs code Hh Hlazy Hfd Hte Hbm. apply exec_no_error.
  eapply exec_conseq; [exact (to_wexit_exec ms bufs code Hte model Hh Hlazy Hfd Hbm) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma init_model_fd1chan : forall reserved brk0 mb sp lim inp,
  fd1chan (init_model reserved brk0 mb sp lim inp).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cat_omni_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
  bufs_modeled bufs ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (wexit_post bufs code (in_fs inp)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm.
  cbn [omni_run]. unfold init_config.
  exact (to_wexit_exec segs _ bufs code Hte
           (init_model (segments_reserved segs) brk0 mb sp lim inp)
           eq_refl eq_refl eq_refl Hbm).
Qed.

Lemma cat_obs_iff_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
  bufs_modeled bufs ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
             <-> exists full, wpick (Z_to_bv 64 1) bufs full /\
                 is_prefix tr (full ++ [ExitEv code (in_fs inp)]).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm tr.
  set (fs0 := in_fs inp) in *.
  unfold init_config in *.
  set (ms := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
  assert (Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = None) by reflexivity.
  assert (Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = []) by reflexivity.
  assert (Hfd : fd1chan (init_model (segments_reserved segs) brk0 mb sp lim inp)) by reflexivity.
  assert (Hfs : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = fs0) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (to_wexit_star_only segs ms bufs code Hte _ Hh Hlazy Hfd Hbm tr' c Hstar)
      as (full & Hw & Hpref).
    rewrite Hfs in Hpref.
    exists full. split; [exact Hw|].
    eapply is_prefix_trans; eauto.
  - intros (full & Hw & Hp).
    destruct (to_wexit_star_admits segs ms bufs code Hte _ full Hh Hlazy Hfd Hbm Hw)
      as [c Hstar].
    rewrite Hfs in Hstar.
    exists (full ++ [ExitEv code fs0]), c. split; assumption.
Qed.

Lemma cat_no_error_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
  bufs_modeled bufs ->
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm. apply exec_no_error.
  eapply exec_conseq; [exact (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
Lemma cat_must_exit_with_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
  bufs_modeled bufs ->
  must_exit_with code (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm. apply must_exit_with_iff.
  eapply exec_conseq; [exact (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm) |].
  intros tr o (_ & Hx). exact Hx.
Qed.

Lemma cat_omni_run_te_code_unique : forall segs pc ph sp brk0 mb rnd lim inp bufs code code',
  to_wexit segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
  bufs_modeled bufs ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (exits_with code') ->
  code' = code.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code code' Hte Hbm Hex.
  pose proof (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm) as Hrun.
  cbn [omni_run] in Hrun, Hex.
  destruct (exec_realizes _ _ _ Hrun) as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'. symmetry. exact Hx'.
Qed.

(* [comment removed for export] *)
Lemma cat_omni_strong_equiv_te :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp,
  to_wexit source_segs (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
  to_wexit target_segs (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
  bufs_modeled bufs ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp
    Hsource Htarget Hbm.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (cat_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code Hsource Hbm) |].
    intros tr o (_ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code Hsource Hbm tr).
    rewrite (cat_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code Htarget Hbm tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (cat_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code Htarget Hbm).
Qed.

(* [comment removed for export] *)
Lemma cat_strong_equiv_te :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp,
  to_wexit source_segs (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
  to_wexit target_segs (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
  bufs_modeled bufs ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp Hsource Htarget Hbm.
  split.
  { apply no_error_run_modeled.
    apply (cat_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code Hsource Hbm). }
  right. split.
  - intro tr. cbn.
    rewrite (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code Hsource Hbm tr).
    rewrite (cat_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bufs code Htarget Hbm tr).
    reflexivity.
  - cbn. apply (cat_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bufs code Htarget Hbm).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fdchan (fd ch : word) (model : Model) : Prop :=
  fd_lookup (m_fds model) fd = Some (FdChannel ch) /\ w_is0 ch = false.

Lemma fd1chan_fdchan : forall model,
  fd1chan model -> fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model.
Proof.
  intros model H. split; [exact H | reflexivity].
Qed.

Lemma init_model_fdchan2 : forall reserved brk0 mb sp lim inp,
  fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) (init_model reserved brk0 mb sp lim inp).
Proof. intros. split; reflexivity. Qed.

Lemma write_ch_check_n : forall segs ms x8 model fd ch buf n,
  fdchan fd ch model ->
  fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  check_write (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (with_copyins [(ms_gpr ms 1, n)]
      (mkEffect (len_word (firstn n buf)) [] [])) model
    = CheckOk model (map (WriteEv ch) (firstn n buf)).
Proof.
  intros segs ms x8 model fd ch buf n [Hfd Hch] H32 Hno Hg Hr Hcnt Hn1 Hn2.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  pose proof (word_unsigned_range (ms_gpr ms 2)) as Hcr.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  unfold check_write.
  rewrite Hg, H32, Hfd, Hch. cbv beta iota.
  rewrite Hmc. cbv beta iota.
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc. cbv beta iota. cbv zeta.
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb).
  assert (Hg0 : Nat.eqb (length buf) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hg0. cbv beta iota. unfold with_copyins; cbn.
  assert (Hlenf : Z.of_nat (length (firstn n buf)) = Z.of_nat n)
    by (rewrite length_firstn; lia).
  assert (Hru : bv_unsigned (len_word (firstn n buf)) = Z.of_nat n).
  { rewrite (len_word_unsigned (firstn n buf));
      [exact Hlenf | rewrite Hlenf; lia]. }
  rewrite ?Hru.
  assert (Hg1 : (1 <=? Z.of_nat n)%Z = true) by (apply Z.leb_le; lia).
  assert (Hg2 : (Z.of_nat n <=? Z.of_nat (length buf))%Z = true)
    by (apply Z.leb_le; lia).
  rewrite ?Hg1, ?Hg2. cbn [andb].
  rewrite ?Nat2Z.id, bv_eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

Lemma write_ch_ok_n : forall segs ms x8 model fd ch buf n,
  fdchan fd ch model -> fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (with_copyins [(ms_gpr ms 1, n)]
          (mkEffect (len_word (firstn n buf)) [] [])) model
        (map (WriteEv ch) (firstn n buf))).
Proof.
  intros segs ms x8 model fd ch buf n Hfdc H32 Hno Hg Hr Hcnt Hn1 Hn2.
  apply (proj2 (syscall_spec_write _ _ _ _ _ Hno)).
  apply check_write_sound_ok. eapply write_ch_check_n; eassumption.
Qed.

Lemma write_ch_ok_inv : forall segs ms x8 model fd ch eff model' evs buf,
  fdchan fd ch model -> fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (1 <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    eff = with_copyins [(ms_gpr ms 1, n)]
            (mkEffect (len_word (firstn n buf)) [] []) /\ model' = model /\
    evs = map (WriteEv ch) (firstn n buf).
Proof.
  intros segs ms x8 model fd ch eff model' evs buf Hfdc H32 Hno Hg Hr Hnb Hspec.
  destruct Hfdc as [Hfd Hch].
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply check_write_complete_ok in Hspec.
  unfold check_write in Hspec.
  rewrite Hg, H32, Hfd, Hch in Hspec. cbv beta iota in Hspec.
  (* [comment removed for export] *)
  destruct (negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)));
    cbv beta iota in Hspec; [discriminate|].
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc in Hspec. cbv beta iota zeta in Hspec.
  (* [comment removed for export] *)
  rewrite (write_source_prefix _ _ _ _ Hrb) in Hspec.
  pose proof (rw_count_clamp_range (ms_gpr ms 2)) as Hcl.
  set (c := Z.to_nat (rw_count_clamp (ms_gpr ms 2))) in *.
  assert (Hcpos : (1 <= c)%nat)
    by (unfold c, rw_count_clamp, MAX_RW_COUNT in *; lia).
  assert (Hfl : length (firstn c buf) = Nat.min c (length buf))
    by apply length_firstn.
  assert (Hg0 : Nat.eqb (length (firstn c buf)) 0 = false)
    by (rewrite Hfl; apply Nat.eqb_neq; lia).
  rewrite Hg0 in Hspec. cbv beta iota in Hspec.
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
    destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; try discriminate.
  destruct ((1 <=? bv_unsigned ret)%Z
            && (bv_unsigned ret <=? Z.of_nat (length (firstn c buf)))%Z) eqn:Hgr;
    [|discriminate].
  destruct (access_ranges_eqb copyins [(ms_gpr ms 1, Z.to_nat (bv_unsigned ret))])
    eqn:Hreads; [|discriminate].
  inversion Hspec; clear Hspec; subst.
  apply andb_true_iff in Hgr as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  rewrite Hfl in H2.
  apply access_ranges_eqb_eq in Hreads. subst copyins.
  exists (Z.to_nat (bv_unsigned ret)).
  assert (Hff : firstn (Z.to_nat (bv_unsigned ret)) (firstn c buf)
                = firstn (Z.to_nat (bv_unsigned ret)) buf)
    by (rewrite firstn_firstn; f_equal; lia).
  rewrite Hff.
  assert (Hlw : len_word (firstn (Z.to_nat (bv_unsigned ret)) buf) = ret)
    by (apply len_word_firstn_ret; lia).
  rewrite Hlw. repeat split; try reflexivity; lia.
Qed.

Lemma write_ch_no_unmodeled : forall segs ms x8 model fd ch buf,
  fdchan fd ch model -> fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (* [comment removed for export] *)
  (1 <= length buf)%nat ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model fd ch buf [Hfd Hch] H32 Hno Hg Hr Hcnt Hnb Hspec.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply (check_write_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_write in Hspec.
  rewrite Hg, H32, Hfd, Hch in Hspec. cbv beta iota in Hspec.
  rewrite Hmc in Hspec. cbv beta iota in Hspec.
  destruct (w_is0 (ms_gpr ms 2)) eqn:Hc; try rewrite Hc in Hspec.
  { exfalso.
    assert (Hc0 : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
    congruence. }
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb)
    in Hspec.
  destruct (length buf =? 0)%nat eqn:Hz; try rewrite Hz in Hspec.
  { now apply check_ret_only_no_unmodeled in Hspec. }
  discriminate Hspec.
Qed.

Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

(* [comment removed for export] *)
Inductive to_wexit_ch : machine_state -> list (list byte) -> word -> Prop :=
| twc_exit : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    to_wexit_ch ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twc_write : forall ms x8 buf bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = fd ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
    (1 <= length buf)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
       to_wexit_ch (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
    to_wexit_ch ms (buf :: bufs) code
| twc_step : forall ms ms' bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wexit_ch ms' bufs code ->
    to_wexit_ch ms bufs code.

Lemma msteps_to_wexit_ch : forall ms ms' bufs code,
  msteps segs ms ms' -> to_wexit_ch ms' bufs code -> to_wexit_ch ms bufs code.
Proof.
  intros ms ms' bufs code H; induction H; [auto|].
  intro Hw. eapply twc_step; eauto.
Qed.

Hypothesis Hfd32 : fd32 fd = fd.

Lemma sstep_write_ch_inv : forall ms model x8 buf evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs st ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv ch) (firstn n buf) /\
    st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model).
Proof.
  intros ms model x8 buf evs st Hh Hlazy Hfdc Hsvc Hno Hg Hr Hcnt Hnb Hss.
  revert Hg Hfdc. inversion Hss; subst; intros Hg Hfdc; try congruence.
  - match goal with
    | H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hnb H3)
        as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
      subst eff model' evs0; exists n
    end.
    match goal with
    | Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
        rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
        inversion Hmat; subst model''
    end.
    rewrite apply_effect_copyins_no_write. repeat split; auto.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf
                  Hfdc Hfd32 Hno Hg Hr Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
      discriminate
    end.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite Hh in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite (m_killed_of_m_halted_none model Hh) in H6;
      discriminate
    end.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      apply (write_ch_no_unmodeled segs ms x8 model fd ch buf Hfdc Hfd32 Hno Hg Hr Hcnt Hnb H3)
    end.
Qed.

End WithSegsCh.

(* [comment removed for export] *)
Lemma to_wexit_ch_1 : forall segs ms bufs code,
  to_wexit segs ms bufs code ->
  to_wexit_ch segs (Z_to_bv 64 1) ms bufs code.
Proof.
  intros segs ms bufs code H; induction H.
  - eapply twc_exit; eassumption.
  - eapply twc_write; eassumption.
  - eapply twc_step; eassumption.
Qed.

Lemma wevents_ch_1 : forall bufs, wevents_ch (Z_to_bv 64 1) bufs = wevents bufs.
Proof.
  induction bufs as [|b bs IH]; cbn [wevents_ch wevents]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.
