(** * FOU.MmapFO — the modeled mmap over the filtered step at memory forced-only (submissions 1 and 2)

    The UBSan framework of submissions 1 and 2 was proved against the release spec's unfiltered step,
    where every modeled anonymous mmap also offers its errnos.  At [FOCore.alloc_forced_cfg] an errno
    answer is a refusal the state did not force as soon as one grant exists ([mmap_errno_spurious]),
    so beside a grant witness the filtered step only grants ([sstep_cfg_mmap_inv_grant]).  The same
    facts proved for submission 21 (its MmapSim patch), here over submission 1's own
    [MmapSim] names. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import SimInv ExitSim PropExec CatSim AllocSim MmapSim.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithFP.
Context {fx : FPState}.

Lemma mmap_grant_not_refusal : forall segs ms model x8 a,
  bv_unsigned x8 = 222%Z ->
  grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  refusal_b (sys_input segs ms x8) model a = false.
Proof.
  intros segs ms model x8 a Hno Hg. unfold refusal_b. rewrite in_sysno_sys_input, Hno. cbn -[mmap_errnos].
  change (errno_ret_in mmap_errnos a = false).
  apply (grant_not_errno (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))); [|exact Hg].
  apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia.
Qed.

Lemma mmap_errno_refusal : forall segs ms model x8 e,
  bv_unsigned x8 = 222%Z -> In e mmap_errnos ->
  refusal_b (sys_input segs ms x8) model (errno_ret e) = true.
Proof.
  intros segs ms model x8 e Hno He. unfold refusal_b. rewrite in_sysno_sys_input, Hno. cbn -[mmap_errnos].
  change (errno_ret_in mmap_errnos (errno_ret e) = true). apply errno_ret_in_intro. exact He.
Qed.

Lemma mmap_family_off : forall segs ms x8,
  bv_unsigned x8 = 222%Z -> injected_family_off alloc_forced_cfg (sys_input segs ms x8) = true.
Proof. intros segs ms x8 Hno. unfold injected_family_off. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma mprotect_family_off : forall segs ms x8,
  bv_unsigned x8 = 226%Z -> injected_family_off alloc_forced_cfg (sys_input segs ms x8) = true.
Proof. intros segs ms x8 Hno. unfold injected_family_off. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

(** The refusals of the mmap and mprotect arms are their errno answers. *)
Lemma refusal_b_mmap : forall segs ms model x8 r,
  bv_unsigned x8 = 222%Z -> refusal_b (sys_input segs ms x8) model r = errno_ret_in mmap_errnos r.
Proof. intros segs ms model x8 r Hno. unfold refusal_b. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma refusal_b_mprotect : forall segs ms model x8 r,
  bv_unsigned x8 = 226%Z -> refusal_b (sys_input segs ms x8) model r = errno_ret_in mprotect_errnos r.
Proof. intros segs ms model x8 r Hno. unfold refusal_b. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

(** Beside a grant, every errno answer of the modeled mmap is a refusal the state did not force. *)
Lemma mmap_errno_spurious : forall segs ms model x8 a0 e,
  bv_unsigned x8 = 222%Z -> mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->  (* port727: mmap_succ_ok's decline premise *)
  grant_ok (ms_gpr ms 0) model a0 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  In e mmap_errnos ->
  spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model (mkEffect (errno_ret e) [] []).
Proof.
  intros segs ms model x8 a0 e Hno Ha Hdecl Ha0 He. split; [exact (mmap_family_off segs ms x8 Hno)|]. split.
  - exact (mmap_errno_refusal segs ms model x8 e Hno He).
  - exists (mkEffect a0 [] [(a0, page_round_up (ms_gpr ms 1))]),
      (mmap_model a0 (page_round_up (ms_gpr ms 1)) model), []. split.
    + apply mmap_succ_ok; assumption.
    + exact (mmap_grant_not_refusal segs ms model x8 a0 Hno Ha0).
Qed.

(** port727: munmap (215) is an allocation arm at (FO/FOStep alloc_sysnos), and its arm admits an
    errno answer that changes nothing (MmapSim munmap_fail_ok). At [alloc_forced_cfg], beside the cut (munmap_ok),
    every such answer is a spurious refusal, so the filtered munmap step only cuts ([sstep_cfg_munmap_inv] below).
    These mirror the mmap lemmas above. *)
Lemma refusal_b_munmap : forall segs ms model x8 r,
  bv_unsigned x8 = 215%Z -> refusal_b (sys_input segs ms x8) model r = errno_ret_in munmap_errnos r.
Proof. intros segs ms model x8 r Hno. unfold refusal_b. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma munmap_family_off : forall segs ms x8,
  bv_unsigned x8 = 215%Z -> injected_family_off alloc_forced_cfg (sys_input segs ms x8) = true.
Proof. intros segs ms x8 Hno. unfold injected_family_off. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma munmap_errno_spurious : forall segs ms model x8 e,
  bv_unsigned x8 = 215%Z -> munmap_args_ok ms model -> In e munmap_errnos ->
  spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model (mkEffect (errno_ret e) [] []).
Proof.
  intros segs ms model x8 e Hno Ha He. split; [exact (munmap_family_off segs ms x8 Hno)|]. split.
  - rewrite (refusal_b_munmap segs ms model x8 _ Hno). apply errno_ret_in_intro. exact He.
  - exists (munmap_eff ms), (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model), []. split.
    + apply munmap_ok; assumption.
    + rewrite (refusal_b_munmap segs ms model x8 _ Hno). reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

(** Beside a grant witness, the filtered mmap step only grants. *)
Lemma sstep_cfg_mmap_inv_grant : forall ms model x8 evs st a0,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->  (* port727: mmap_succ_ok's decline premise *)
  grant_ok (ms_gpr ms 0) model a0 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  sstep_cfg segs alloc_forced_cfg (mkCfg ms model) evs st ->
  evs = [] /\
  exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true /\
      st = SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                        (mmap_model a (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros ms model x8 evs st a0 Hh Hlazy Hsvc Hno Hargs Hdecl Ha0 Hss.
  inversion Hss; subst; try congruence.
  - match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hn : ~ spurious_refusal_cfg _ _ _ _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x; rename Hn into Hns;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as [(e & HIn & -> & ->) | (a & Hg & -> & ->)].
    + exfalso. exact (Hns (mmap_errno_spurious segs ms model x8 a0 e Hno Hargs Hdecl Ha0 HIn)).
    + match goal with
      | Hmat : materialize_model_accesses (mmap_model a _ model) _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _
          (eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat;
        inversion Hmat; subst
      end.
      exists a. auto.
  - exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat
      | rewrite (materialize_model_accesses_no_lazy _ _
          (eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat ];
      discriminate
    end.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite Hh in H6; discriminate
      | rewrite mmap_model_halted, Hh in H6; discriminate ]
    end.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
      destruct Hcase as [(e & _ & _ & Hm) | (a & _ & _ & Hm)]; subst model';
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
      | assert (Hhn : m_halted
                        (mmap_model a (page_round_up (ms_gpr ms 1)) model) = None)
          by (rewrite mmap_model_halted; exact Hh);
        rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate ]
    end.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (mmap_no_unmodeled segs ms x8 model Hno Hargs Hdecl H3)  (* port727: the decline premise *)
    end.
Qed.

(** port727: the filtered munmap step only cuts (the errno answer is a spurious refusal, above). *)
Lemma sstep_cfg_munmap_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sstep_cfg segs alloc_forced_cfg (mkCfg ms model) evs st ->
  evs = [] /\
  st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hn : ~ spurious_refusal_cfg _ _ _ _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x; rename Hn into Hns;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as [(e & HIn & -> & ->) | (-> & ->)].
    + exfalso. exact (Hns (munmap_errno_spurious segs ms model x8 e Hno Hargs HIn)).
    + match goal with
      | Hmat : materialize_model_accesses
          (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _
          (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
        inversion Hmat; subst
      end.
      reflexivity.
  - exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & -> & ->) | (-> & ->)];
      [ rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat
      | rewrite (materialize_model_accesses_no_lazy _ _
          (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat ];
      discriminate
    end.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
      [ rewrite Hh in H6
      | rewrite munmap_model_halted, Hh in H6 ];
      discriminate
    end.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6
      | rewrite m_killed_of_m_halted_none in H6;
        [| rewrite munmap_model_halted; exact Hh] ];
      discriminate
    end.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.

End WithSegs.
End WithFP.
