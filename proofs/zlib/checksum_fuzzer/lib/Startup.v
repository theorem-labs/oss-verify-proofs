(** A limited startup certificate for the pinned checksum_fuzzer plain image.
    This does not prove termination, checksum correctness, or syscall behavior.
    The executor below calls the published CPU step and stops at any pending
    syscall or machine error. No instruction or system-call semantics is changed. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.zlib.checksum_fuzzer.images Require Plain.

Definition replace_mem (st : machine_state) (mem : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs st; ms_fregs := ms_fregs st; ms_pc_val := ms_pc_val st;
     ms_svc_pending := ms_svc_pending st; ms_resv := ms_resv st; ms_fcsr := ms_fcsr st;
     ms_mem := mem; ms_rom := ms_rom st |}.
Lemma replace_mem_eta : forall st, st = replace_mem st (ms_mem st).
Proof. intro st. destruct st. reflexivity. Qed.

Module E := OssFuzzTheorems.zlib.checksum_fuzzer.images.Plain.M.

Fixpoint pure_prefix (segs : list Segment) (fuel : nat) (ms : machine_state)
    : option machine_state :=
  match fuel with
  | O => Some ms
  | S fuel' =>
      match ms_svc_pending ms with
      | Some _ => None
      | None =>
          match RiscvSemantics.step segs ms with
          | MachineOk ms' => pure_prefix segs fuel' ms'
          | MachineFault | MachineUnmodeled => None
          end
      end
  end.

Definition startup_view (ms : machine_state) :=
  (ms_pc ms, ms_reg ms (Z_to_bv 5 3), ms_gpr ms 1, ms_svc_pending ms).

Lemma startup_view_equal : forall (a b c a' b' c' : word) (d d' : option word),
  bv_unsigned a = bv_unsigned a' ->
  bv_unsigned b = bv_unsigned b' ->
  bv_unsigned c = bv_unsigned c' -> d = d' ->
  (a, b, c, d) = (a', b', c', d').
Proof.
  intros a b c a' b' c' d d' Ha Hb Hc Hd.
  apply bv_eq in Ha. apply bv_eq in Hb. apply bv_eq in Hc.
  now subst.
Qed.

(** A certificate is an ordinary chain of the original, unmodified CPU step,
    with no pending syscall at an intermediate state. *)
Inductive pure_steps (segs : list Segment)
    : nat -> machine_state -> machine_state -> Prop :=
| pure_steps_zero : forall ms, pure_steps segs 0 ms ms
| pure_steps_succ : forall n ms mid final,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk mid ->
    pure_steps segs n mid final ->
    pure_steps segs (S n) ms final.

Lemma pure_prefix_sound : forall segs n ms final,
  pure_prefix segs n ms = Some final -> pure_steps segs n ms final.
Proof.
  intros segs n. induction n as [|n IH]; intros ms final H.
  - cbn [pure_prefix] in H. inversion H; subst. constructor.
  - cbn [pure_prefix] in H.
    destruct (ms_svc_pending ms) as [svc|] eqn:Hp; [discriminate|].
    destruct (RiscvSemantics.step segs ms) as [mid| |] eqn:Hs;
      try discriminate.
    eapply pure_steps_succ; [exact Hp | exact Hs |].
    eapply IH. exact H.
Qed.

Lemma pure_prefix_view_sound {A : Type} : forall segs n ms
    (view : machine_state -> A) (expected : A),
  option_map view (pure_prefix segs n ms) = Some expected ->
  exists final, pure_steps segs n ms final /\ view final = expected.
Proof.
  intros segs n ms view expected H.
  destruct (pure_prefix segs n ms) as [final|] eqn:He;
    cbn [option_map] in H; [|discriminate].
  exists final. split.
  - eapply pure_prefix_sound. exact He.
  - injection H as Hv. exact Hv.
Qed.

(** Every initial stack/input has the same seven-instruction control prefix.
    It reaches the first stack load, with gp established and a1 cleared.
    No condition about the checksums or the later startup is asserted here. *)
Theorem startup_seven_steps : forall sp rnd argv envp uid hw,
  option_map startup_view
    (pure_prefix E.loaded_segments 7
      (init_machine_state E.loaded_segments E.init_pc E.phdrs sp rnd argv envp uid hw))
  = Some (Z_to_bv 64 0x13c20, Z_to_bv 64 0x10800, Z_to_bv 64 0, None).
Proof.
  intros. rewrite (replace_mem_eta (init_machine_state _ _ _ _ _ _ _ _ _)).
  generalize (ms_mem (init_machine_state E.loaded_segments E.init_pc E.phdrs
                        sp rnd argv envp uid hw)).
  intros mem. vm_compute. apply f_equal. apply startup_view_equal;
    vm_compute; reflexivity.
Qed.

Theorem startup_certificate : forall sp rnd argv envp uid hw,
  exists final,
    pure_steps E.loaded_segments 7
      (init_machine_state E.loaded_segments E.init_pc E.phdrs sp rnd argv envp uid hw) final
    /\ startup_view final
      = (Z_to_bv 64 0x13c20, Z_to_bv 64 0x10800, Z_to_bv 64 0, None).
Proof.
  intros. eapply pure_prefix_view_sound. apply startup_seven_steps.
Qed.

Set Printing Fully Qualified.
Print Assumptions startup_certificate.
