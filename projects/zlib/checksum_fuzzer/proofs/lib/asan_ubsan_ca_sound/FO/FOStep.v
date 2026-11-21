(** * FO.FOStep — moving step-level proofs onto the filtered run at memory forced-only

    Proofs that build or invert [Run.sstep] steps move onto [Run.sstep_cfg] with three facts: an
    instruction or exit step needs nothing; a syscall step needs its outcome not to be a spurious
    refusal, which holds for every non-allocation syscall at [alloc_forced_cfg] (its family may still
    fail) and for every non-refusal answer whatever the syscall; and inversion goes through
    [Run.sstep_cfg_sub].  [sstep_cfg_syscall_ns] is the [sstep_syscall] constructor with that one
    extra premise FIRST, so a proof that applied [sstep_syscall] gains exactly one leading subgoal. *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(** The families [alloc_forced_cfg] reads as forced-only are the allocation arms: brk, munmap, mremap, mmap,
    mprotect.  sem727: a STATEMENT change of this library list, because
    rocq-LPS 's [Run.injected_table] adds munmap (215, munmap_errnos) to [FamAlloc]; r30q2 had 214 / 216 /
    222 / 226 only. *)
Definition alloc_sysnos : list Z := [214; 215; 216; 222; 226]%Z.

Lemma alloc_forced_family_off : forall i,
  injected_family_off alloc_forced_cfg i = true -> In (bv_unsigned (in_sysno i)) alloc_sysnos.
Proof.
  intros i H. unfold injected_family_off, injected_arm in H.
  destruct (lookup_injected injected_table (bv_unsigned (in_sysno i))) as [a|] eqn:E; [|discriminate H].
  apply lookup_injected_in in E as [Hin Hno]. rewrite <- Hno.
  unfold injected_table in Hin.
  repeat (destruct Hin as [<-|Hin]; [cbn in H |- *; first [discriminate H | tauto] |]).
  destruct Hin.
Qed.

Lemma no_spurious_nonalloc : forall i m eff,
  ~ In (bv_unsigned (in_sysno i)) alloc_sysnos -> ~ spurious_refusal_cfg alloc_forced_cfg i m eff.
Proof.
  intros i m eff Hn. apply spurious_refusal_family_on.
  destruct (injected_family_off alloc_forced_cfg i) eqn:E; [|reflexivity].
  exfalso. exact (Hn (alloc_forced_family_off i E)).
Qed.

Lemma in_sysno_sys_input_fo : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

(** For a concrete syscall number outside the allocation arms. *)
Lemma no_spurious_sysno : forall segs ms x8 m eff,
  ~ In (bv_unsigned x8) alloc_sysnos ->
  ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) m eff.
Proof.
  intros segs ms x8 m eff Hn. apply no_spurious_nonalloc. rewrite in_sysno_sys_input_fo. exact Hn.
Qed.

(* STATEMENT change, one more conjunct [z <> 215] (munmap is an allocation arm at ) *)
Lemma not_alloc_sysno : forall z,
  (z <> 214 /\ z <> 215 /\ z <> 216 /\ z <> 222 /\ z <> 226)%Z -> ~ In z alloc_sysnos.
Proof.
  intros z (H1 & H5 & H2 & H3 & H4) Hin. unfold alloc_sysnos in Hin. cbn in Hin.
  destruct Hin as [?|[?|[?|[?|[?|[]]]]]]; subst; congruence.
Qed.

(** Discharges [~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) m eff] from a hypothesis
    [bv_unsigned x8 = n] with [n] a non-allocation number, or from a non-refusal answer. *)
Ltac no_spurious_tac :=
  first
    [ apply no_spurious_sysno; apply not_alloc_sysno;
      match goal with H : bv_unsigned _ = _ |- _ => rewrite H end; lia
    | apply spurious_refusal_not_refusal; reflexivity ].

Section Intro.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma sstep_cfg_syscall_ns : forall ms model x8 eff model' model'' evs,
  ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  m_halted model' = None ->
  materialize_model_accesses model' (syscall_effect_accesses eff) = Some model'' ->
  sstep_cfg segs cfg (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')).
Proof. intros. eapply sstep_cfg_syscall; eassumption. Qed.

(** Any step whose syscall outcome (if any) cannot be spurious is a filtered step. *)
Lemma sstep_cfg_of_sstep_ns : forall c e st,
  sstep segs c e st ->
  (forall ms model x8 eff, c = mkCfg ms model -> ms_svc_pending ms = Some x8 ->
     ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff) ->
  sstep_cfg segs cfg c e st.
Proof.
  intros c e st H Hns. destruct H.
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled; eassumption.
  (* 's sstep / sstep_cfg gain the three vDSO-call arms, here (proof only: a vDSO
     arm of sstep_cfg takes no spurious-refusal premise, so the statement needs nothing more) *)
  - eapply sstep_cfg_vdso_call; eassumption.
  - eapply sstep_cfg_vdso_materialization_fault; eassumption.
  - eapply sstep_cfg_vdso_unmodeled; eassumption.
  - eapply sstep_cfg_syscall; try eassumption. eapply Hns; [reflexivity| eassumption].
  - eapply sstep_cfg_syscall_materialization_fault; try eassumption. eapply Hns; [reflexivity| eassumption].
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs cfg c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma star_cfg_one : forall c e c', sstep_cfg segs cfg c e (SNext c') -> star_cfg segs cfg c e c'.
Proof. intros c e c' H. rewrite <- (app_nil_r e). eapply star_cfg_step; [exact H| apply star_cfg_refl]. Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs cfg c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hs. inversion Hs; subst; [split; reflexivity|].
  exfalso. apply Hh. eapply sstep_cfg_halted_none; eassumption.
Qed.

Lemma obs_trace_cfg_nil : forall c, obs_trace_cfg segs cfg c [].
Proof. intros c. exists [], c. split; [apply star_cfg_refl| apply is_prefix_nil]. Qed.

End Intro.
