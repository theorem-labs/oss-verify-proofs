(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState Frame Exec ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit Require Import TopLevel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AS Require Import ShapeAlg SpinAlg ShapeHaltsA.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma in_map_WriteEv_no_exit : forall fd l code fs, ~ In (ExitEv code fs) (map (WriteEv fd) l).
Proof. intros fd l code fs Hin. apply in_map_iff in Hin as (x & Hx & _). discriminate Hx. Qed.

Lemma nstep_no_exit : forall n mo eff mo' evs,
  nstep n mo eff mo' evs -> forall code fs, ~ In (ExitEv code fs) evs.
Proof.
  intros n mo eff mo' evs Hst code fs.
  destruct n; cbn [nstep] in Hst.
  - destruct Hst as (k & _ & _ & _ & ->). apply in_map_WriteEv_no_exit.
  - destruct Hst as (_ & Hst).
    destruct (Z.of_nat (length (concat bufs)) =? 0).
    + destruct Hst as (_ & ->). intros [].
    + destruct Hst as (k & _ & _ & ->). apply in_map_WriteEv_no_exit.
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
Qed.

Lemma nexit_any_exit : forall n mo1 code mo2, nexit n mo1 code mo2 -> In code AnyExit.codes.
Proof.
  intros n mo1 code mo2 H. destruct n; cbn [nexit] in H; try contradiction.
  destruct H as [-> _]. apply any_exit_covers.
Qed.

Lemma ttrace_exit_any : forall {R : Type} (t : itree node R) mo tr,
  ttrace nstep nexit t mo tr -> forall code fs, In (ExitEv code fs) tr -> In code AnyExit.codes.
Proof.
  intros R t. induction t as [r | n k IH]; intros mo tr Htr code fs Hin.
  - cbn in Htr. subst tr. destruct Hin.
  - cbn [ttrace] in Htr. destruct Htr as [(code' & mo' & Hex & ->) | (rsp & mo' & evs & tr' & Hst & Htr' & ->)].
    + destruct Hin as [H | []]. injection H as -> _. exact (nexit_any_exit _ _ _ _ Hex).
    + apply in_app_or in Hin as [Hin | Hin].
      * exfalso. exact (nstep_no_exit _ _ _ _ _ Hst code fs Hin).
      * exact (IH rsp mo' tr' Htr' code fs Hin).
Qed.

Lemma in_is_prefix_full : forall (l full : list event) x, is_prefix l full -> In x l -> In x full.
Proof.
  induction l as [|y l IH]; intros full x Hp Hin; [destruct Hin|].
  destruct full as [|e full]; cbn in Hp; [contradiction|]. destruct Hp as [-> Hp].
  destruct Hin as [-> | Hin]; [left; reflexivity | right; exact (IH full x Hp Hin)].
Qed.

Theorem tree_traces_ends_in_any : forall {R : Type} (t : itree node R) mo, ends_in AnyExit.codes (tree_traces t mo).
Proof.
  intros R t mo. split.
  - intros tr code fs (full & Hf & Hp).
    apply (ttrace_exit_any t mo full Hf code fs). apply (in_is_prefix_full _ _ _ Hp). apply in_or_app. right. left. reflexivity.
  - intros tr sig fs H. apply (tree_traces_no_kill t mo _ H sig fs). apply in_or_app. right. left. reflexivity.
Qed.

Theorem halts_of_srealizes : forall segs pc ph (T : ProcInput -> ExecEntry -> TSet),
  (forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
     (* the run reads the run's list run_segments = segs ++ the vDSO pair, and starts at that
        list's init_config (the form of TopLevelGen's side_ok_of_srealizes) *)
     let vsegs := run_segments segs inp (en_sp en) (en_mmap_base en) in
     srealizes vsegs (init_config vsegs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) source_alloc_limit inp) (T inp en)
     /\ ends_in AnyExit.codes (T inp en)) ->
  halts_core alloc_forced_cfg source_alloc_limit AnyExit.codes (mkImage segs pc ph).
Proof.
  intros segs pc ph T H en inp Hve Hvi.
  pose proof (H en inp Hve (valid_input_either_of_valid_input inp Hvi)) as HH. cbv zeta in HH.
  destruct HH as [Hsrz Hend].
  destruct en as [sp brk mb dr]. cbn [must_exit_in_scfg]. cbn [en_sp en_brk en_mmap_base en_draw] in Hsrz.
  set (vsegs := run_segments segs inp sp mb) in *.
  apply (realizes_must_exit_init vsegs AnyExit.codes _ (T inp (mkEntry sp brk mb dr)) (realizes_of_srealizes vsegs _ _ Hsrz) Hend).
  change (init_config vsegs pc ph sp brk mb dr source_alloc_limit inp)
    with (init_config vsegs pc ph (en_sp (mkEntry sp brk mb dr)) (en_brk (mkEntry sp brk mb dr))
                      (en_mmap_base (mkEntry sp brk mb dr)) (en_draw (mkEntry sp brk mb dr)) source_alloc_limit inp).
  rewrite (init_config_eq vsegs pc ph source_alloc_limit (mkEntry sp brk mb dr) inp).
  apply mo0_not_halted.
Qed.
