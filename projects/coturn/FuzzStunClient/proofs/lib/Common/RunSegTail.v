(* SPDX-License-Identifier: MIT *)
(* Bridge (B), first half (B1), for coturn's PLAIN [ShapeAlg.realizes]:
   a derivation over a binary's own segments [segs] is a derivation over [segs ++ tail] when the tail is
   non-executable and non-writable and [segs] carries no vDSO image.  [Run.run_segments segs inp sp mb] is
   [segs ++ vdso_segments ..], whose two segments are exactly such a tail ([vdso_segments_nx/_nw]).

   Made from projects/bzip2/bzip2_compress_target/proofs/lib/Common/Cfg/RomStable.v lines 255-574, as in the
   LPS 727298f3 update, with the step relation the plain [Run.sstep] (coturn's [ShapeAlg.node_ok]) in place
   of [sstep_cfg kit_cfg], and without [segments_reserved_vdso], [segments_reserved_app] and
   [segments_reserved_run_segments].  [sys_rob_app_tail] ([rz_node] asks [RomBase.sys_rob]) follows from
   [sys_input_app_nw]: [sys_input] over [segs ++ tail] is [sys_input] over [segs], the tail being non-writable.
   The second half (B2: the start state's larger read-only backing, [init_config (run_segments ..)] =
   [cwrom (init_config segs ..) ..]) needs [sys_rob] at every syscall node and is NOT in this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma find_segment_app : forall segs tail addr n,
  find_segment (segs ++ tail) addr n
  = match find_segment segs addr n with
    | Some s => Some s
    | None => find_segment tail addr n
    end.
Proof.
  induction segs as [|seg rest IH]; intros tail addr n; [reflexivity|].
  cbn [find_segment app].
  destruct (Z.leb (Z.of_N (seg_base seg)) addr
            && Z.leb (addr + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)))%bool;
    [reflexivity | apply IH].
Qed.

Lemma find_segment_in : forall segs addr n s,
  find_segment segs addr n = Some s -> In s segs.
Proof.
  induction segs as [|seg rest IH]; intros addr n s H; [discriminate H|].
  cbn [find_segment] in H.
  destruct (Z.leb (Z.of_N (seg_base seg)) addr
            && Z.leb (addr + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)))%bool.
  - injection H as <-. left. reflexivity.
  - right. exact (IH _ _ _ H).
Qed.

Section AppTail.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.

  Lemma code_read_app_nx : forall a n,
    code_read (segs ++ tail) a n = code_read segs a n.
  Proof.
    intros a n. unfold code_read. rewrite find_segment_app.
    destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|]; [reflexivity|].
    destruct (find_segment tail (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E; [|reflexivity].
    rewrite (Hnx s (find_segment_in _ _ _ _ E)). reflexivity.
  Qed.

  Lemma code_read_ov_app_nx : forall m a n,
    code_read_ov (segs ++ tail) m a n = code_read_ov segs m a n.
  Proof.
    intros m a n. unfold code_read_ov. rewrite find_segment_app.
    destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|]; [reflexivity|].
    destruct (find_segment tail (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E; [|reflexivity].
    rewrite (Hnx s (find_segment_in _ _ _ _ E)). reflexivity.
  Qed.

  Lemma fetch_word_app_nx : forall a,
    fetch_word (segs ++ tail) a = fetch_word segs a.
  Proof. intros a. unfold fetch_word. rewrite code_read_app_nx. reflexivity. Qed.

  Lemma fetch_word_ov_app_nx : forall m a,
    fetch_word_ov (segs ++ tail) m a = fetch_word_ov segs m a.
  Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_app_nx. reflexivity. Qed.

  Lemma fetch_half_any_app_nx : forall m a,
    fetch_half_any (segs ++ tail) m a = fetch_half_any segs m a.
  Proof.
    intros m a. unfold fetch_half_any, fetch_half, fetch_half_ov.
    rewrite code_read_app_nx, code_read_ov_app_nx. reflexivity.
  Qed.

  Lemma fetch_tail_any_app_nx : forall m a,
    fetch_tail_any (segs ++ tail) m a = fetch_tail_any segs m a.
  Proof.
    intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_app_nx. reflexivity.
  Qed.

  Lemma memory_read_app_nx : forall a n bs,
    memory_read segs a n = Some bs -> memory_read (segs ++ tail) a n = Some bs.
  Proof.
    intros a n bs. unfold memory_read. rewrite find_segment_app.
    destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|];
      [intro H; exact H | intro H; discriminate H].
  Qed.

  Lemma ov_read_bytes_app_nx : forall n m a bs,
    ov_read_bytes segs m a n = Some bs -> ov_read_bytes (segs ++ tail) m a n = Some bs.
  Proof.
    induction n as [|n IH]; intros m a bs; cbn [ov_read_bytes]; [intro H; exact H|].
    destruct (m a) as [b|].
    - destruct (ov_read_bytes segs m (a + 1) n) as [rest|] eqn:E; [|intro H; discriminate H].
      rewrite (IH _ _ _ E). intro H; exact H.
    - destruct (memory_read segs a 1) as [[|b rest0]|] eqn:Em;
        [intro H; discriminate H | | intro H; discriminate H].
      rewrite (memory_read_app_nx _ _ _ Em).
      destruct (ov_read_bytes segs m (a + 1) n) as [rest|] eqn:E; [|intro H; discriminate H].
      rewrite (IH _ _ _ E). intro H; exact H.
  Qed.

  Lemma wview_app_nw : forall m a, wview (segs ++ tail) m a = wview segs m a.
  Proof.
    intros m a. unfold wview. destruct (m a) as [b|]; [reflexivity|].
    rewrite find_segment_app.
    destruct (find_segment segs (bv_unsigned a) 1) as [s|]; [reflexivity|].
    destruct (find_segment tail (bv_unsigned a) 1) as [s|] eqn:E; [|reflexivity].
    rewrite (Hnw s (find_segment_in _ _ _ _ E)). reflexivity.
  Qed.

  Lemma store_ok_app_nw : forall n m a,
    store_ok (segs ++ tail) m a n = store_ok segs m a n.
  Proof.
    induction n as [|n IH]; intros m a; cbn [store_ok]; [reflexivity|].
    rewrite wview_app_nw. destruct (wview segs m a); [apply IH | reflexivity].
  Qed.

  Lemma interp_eff_accesses_app_nx : forall t m r,
    interp_eff_accesses segs t m = MachineOk r ->
    interp_eff_accesses (segs ++ tail) t m = MachineOk r.
  Proof.
    induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r;
      cbn [interp_eff_accesses]; try (intro H; exact H).
    - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|] eqn:E.
      + rewrite (ov_read_bytes_app_nx _ _ _ _ E).
        match goal with
        | |- context [interp_eff_accesses segs ?t' ?m'] =>
            destruct (interp_eff_accesses segs t' m') as [rep| |] eqn:E2;
              [| intro H; discriminate H | intro H; discriminate H]
        end.
        rewrite (IH _ _ _ E2). intro H; exact H.
      + destruct (range_meets_vvar segs a (width_bytes n)); intro H; discriminate H.
    - rewrite store_ok_app_nw.
      destruct (store_ok segs m a (width_bytes n)) eqn:E; [|intro H; discriminate H].
      match goal with
      | |- context [interp_eff_accesses segs k ?m'] =>
          destruct (interp_eff_accesses segs k m') as [rep| |] eqn:E2;
            [| intro H; discriminate H | intro H; discriminate H]
      end.
      rewrite (IH _ _ E2). intro H; exact H.
  Qed.

  Lemma decode_exec_accesses_app_nx : forall st w rep,
    decode_exec_accesses segs st w = MachineOk rep ->
    decode_exec_accesses (segs ++ tail) st w = MachineOk rep.
  Proof.
    intros st w rep. unfold decode_exec_accesses.
    destruct (is_ecall w); [intro H; exact H|].
    destruct (decode_any w) as [[i isz]|]; [|intro H; exact H].
    match goal with
    | |- context [interp_eff_accesses segs ?t ?m] =>
        destruct (interp_eff_accesses segs t m) as [r| |] eqn:E;
          [rewrite (interp_eff_accesses_app_nx _ _ _ E); intro H; exact H
          | intro H; discriminate H | intro H; discriminate H]
    end.
  Qed.

  Lemma step_accesses_app_nx : forall st rep,
    step_accesses segs st = MachineOk rep ->
    step_accesses (segs ++ tail) st = MachineOk rep.
  Proof.
    intros st rep. unfold step_accesses.
    rewrite fetch_word_app_nx, fetch_word_ov_app_nx, fetch_tail_any_app_nx.
    destruct (fetch_word segs (ms_pc st)) as [w|]; [apply decode_exec_accesses_app_nx|].
    destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|];
      [apply decode_exec_accesses_app_nx|].
    destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|];
      [apply decode_exec_accesses_app_nx|].
    destruct (fetch_failure segs (ms_mem st) (ms_pc st)) eqn:Ef;
      [| intro H; discriminate H | intro H; discriminate H].
    exfalso. revert Ef. unfold fetch_failure. cbv zeta.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      intro Ef; discriminate Ef.
  Qed.

  Lemma mi_account_step_app_nx : forall ms model r,
    mi_account_step segs ms model = MachineOk r ->
    mi_account_step (segs ++ tail) ms model = MachineOk r.
  Proof.
    intros ms model r. unfold mi_account_step.
    destruct (step_accesses segs ms) as [rep| |] eqn:E;
      [rewrite (step_accesses_app_nx _ _ E); intro H; exact H
      | intro H; discriminate H | intro H; discriminate H].
  Qed.

  Lemma sys_input_app_nw : forall ms x8,
    sys_input (segs ++ tail) ms x8 = sys_input segs ms x8.
  Proof.
    intros ms x8. unfold sys_input. f_equal.
    apply functional_extensionality. intro a. unfold ms_writable_byte. apply wview_app_nw.
  Qed.

  Lemma sys_rob_app_tail : forall c,
    RomBase.sys_rob segs c -> RomBase.sys_rob (segs ++ tail) c.
  Proof.
    intros [ms m] Hrob r x8 Hr Hs o. cbn [cfg_ms cfg_model] in *.
    rewrite !sys_input_app_nw. exact (Hrob r x8 Hr Hs o).
  Qed.

  Hypothesis Hvi : vdso_image segs = None.

  Lemma vdso_entry_fn_none : forall pc, vdso_entry_fn segs pc = None.
  Proof. intros pc. unfold vdso_entry_fn. rewrite Hvi. reflexivity. Qed.

  (* plain [Run.sstep], 11 arms in model order: instr, instr_fault, instr_unmodeled, vdso_call,
     vdso_materialization_fault, vdso_unmodeled, syscall, syscall_materialization_fault, exit, killed,
     syscall_unmodeled.  Over [segs] the three vDSO arms are impossible ([vdso_entry_fn_none]). *)
  Lemma sstep_app_next : forall c e c',
    sstep segs c e (SNext c') -> sstep (segs ++ tail) c e (SNext c').
  Proof.
    intros c e c' H. inversion H; subst.
    - eapply sstep_instr; [assumption | assumption |].
      apply mi_account_step_app_nx. assumption.
    - exfalso. rewrite vdso_entry_fn_none in *. discriminate.
    - eapply sstep_syscall; rewrite ?sys_input_app_nw; eassumption.
    - eapply sstep_exit; rewrite ?sys_input_app_nw; eassumption.
    - eapply sstep_killed; rewrite ?sys_input_app_nw; eassumption.
  Qed.

  Lemma sstep_app_back : forall ms model e st,
    (ms_svc_pending ms = None -> exists r, mi_account_step segs ms model = MachineOk r) ->
    sstep (segs ++ tail) (mkCfg ms model) e st ->
    sstep segs (mkCfg ms model) e st.
  Proof.
    intros ms model e st Hok H. inversion H; subst.
    - destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'.
      match goal with Hb : mi_account_step (_ ++ _) _ _ = MachineOk _ |- _ =>
        rewrite Hr' in Hb; injection Hb as Hb'; subst r end.
      eapply sstep_instr; eassumption.
    - exfalso. destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'. congruence.
    - exfalso. destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'. congruence.
    - exfalso. destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'. congruence.
    - exfalso. destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'. congruence.
    - exfalso. destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'. congruence.
    - rewrite sys_input_app_nw in *. eapply sstep_syscall; eassumption.
    - rewrite sys_input_app_nw in *. eapply sstep_syscall_materialization_fault; eassumption.
    - rewrite sys_input_app_nw in *. eapply sstep_exit; eassumption.
    - rewrite sys_input_app_nw in *. eapply sstep_killed; eassumption.
    - rewrite sys_input_app_nw in *. eapply sstep_syscall_unmodeled; eassumption.
  Qed.

  Lemma node_ok_app_tail : forall c (I : Type) evs nx (i0 : I),
    ShapeAlg.node_ok segs c I evs nx -> ShapeAlg.node_ok (segs ++ tail) c I evs nx.
  Proof.
    intros [ms model] I evs nx i0 [Hc Hs]. split.
    - intros i. apply sstep_app_next. exact (Hc i).
    - intros e st Hb. apply Hs. apply (sstep_app_back ms model e st); [| exact Hb].
      intros Hsvc. pose proof (Hc i0) as H0. inversion H0; subst.
      + eexists. eassumption.
      + exfalso. rewrite vdso_entry_fn_none in *. discriminate.
      + congruence.
      + congruence.
      + congruence.
  Qed.

  Theorem realizes_app_tail : forall c T, realizes segs c T -> realizes (segs ++ tail) c T.
  Proof.
    intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
    - exact (rz_node (segs ++ tail) c I evs nx T i0 (node_ok_app_tail c I evs nx i0 Hnode)
               (sys_rob_app_tail c Hrob) IH).
    - exact (rz_halt (segs ++ tail) c Hh).
    - exact (rz_conseq (segs ++ tail) c T T' IH Heq).
  Qed.
End AppTail.

Section VdsoPair.
  Local Transparent vdso_segments.

  Lemma vdso_segments_nx : forall kb (sp mbase : word) s,
    In s (vdso_segments kb sp mbase) -> seg_executable s = false.
  Proof.
    intros kb sp mbase s H. unfold vdso_segments in H. cbv zeta in H.
    match type of H with In _ (if ?b then _ else _) => destruct b end;
      [destruct H|].
    destruct H as [<-|[<-|[]]]; reflexivity.
  Qed.

  Lemma vdso_segments_nw : forall kb (sp mbase : word) s,
    In s (vdso_segments kb sp mbase) -> seg_writable s = false.
  Proof.
    intros kb sp mbase s H. unfold vdso_segments in H. cbv zeta in H.
    match type of H with In _ (if ?b then _ else _) => destruct b end;
      [destruct H|].
    destruct H as [<-|[<-|[]]]; reflexivity.
  Qed.
End VdsoPair.

(** (B1): a derivation over the binary's own segments is one over the run's segment list. *)
Theorem realizes_run_segments : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  realizes segs c T -> realizes (run_segments segs inp sp mb) c T.
Proof.
  intros segs inp sp mb c T Hvi H. unfold run_segments.
  apply (realizes_app_tail segs _
           (fun s Hs => vdso_segments_nx _ _ _ s Hs) (fun s Hs => vdso_segments_nw _ _ _ s Hs) Hvi).
  exact H.
Qed.
