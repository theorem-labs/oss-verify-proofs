(** Exit-status obligations for a returning, allocation-free checksum harness.
    This model is useful only after its binary library contract is proved. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail Require Import TraceHalting.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition zallowed : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
#[global] Instance checksum_shape : lib_shape.
Proof.
  refine {| LIBK := fun pl fs K => K (LL 0 fs []);
    lib_delta := fun n b => b; lib_room := fun b n => True |}.
  intros pl fs K K' H. apply H.
Defined.
Lemma permitted_prefix : forall allowed a b,
  is_prefix a b -> Forall (permitted_event allowed) b -> Forall (permitted_event allowed) a.
Proof.
  intros allowed a. induction a as [|x a IH]; intros b H HF.
  - constructor.
  - destruct b as [|y b]; [contradiction|].
    cbn in H. destruct H as [-> H]. inversion HF; subst.
    constructor; [assumption|]. eapply IH; eassumption.
Qed.
Lemma permitted_emit : forall allowed es T,
  Forall (permitted_event allowed) es -> permitted_traces allowed T ->
  permitted_traces allowed (t_emit es T).
Proof.
  intros allowed es T HE HT tr [HP|[tail [-> Htail]]].
  - eapply permitted_prefix; eassumption.
  - apply Forall_app. split; [exact HE|apply HT; exact Htail].
Qed.
Lemma permitted_wr : forall allowed ch bs T,
  permitted_traces allowed T -> permitted_traces allowed (wr ch bs T).
Proof.
  intros allowed ch bs T HT. apply permitted_emit; [|exact HT].
  apply Forall_map. apply Forall_forall. intros x Hx. exact I.
Qed.
Lemma permitted_ex : forall allowed code fs,
  In (Z_to_bv 64 code) allowed -> permitted_traces allowed (ex code fs).
Proof.
  intros allowed code fs Hin. apply permitted_emit.
  - constructor; [exact Hin|constructor].
  - intros tr ->. constructor.
Qed.
Lemma zpermitted_diag : forall msg fs, permitted_traces zallowed (diag msg fs).
Proof. intros. apply permitted_wr, permitted_ex. right; left; reflexivity. Qed.
Lemma permitted_alt2 : forall allowed A B,
  permitted_traces allowed A -> permitted_traces allowed B ->
  permitted_traces allowed (t_alt2 A B).
Proof. intros allowed A B HA HB tr [H|H]; [apply HA|apply HB]; exact H. Qed.
Lemma permitted_tset {S A} : forall allowed (t : itree S A) K,
  (forall a, permitted_traces allowed (K a)) ->
  permitted_traces allowed (tset t K).
Proof.
  intros allowed t. induction t as [a|q s k IH|e]; intros K HK; cbn.
  - apply HK.
  - destruct (fallible q); [destruct (spurious q)|];
      try apply permitted_alt2; apply IH; exact HK.
  - intros tr H. contradiction.
Qed.
Section Model.
Context {fx : FPState} {rc : RunCeil}.
Lemma checksum_iter_identity : forall pl j K fs,
  lib_iter pl j K fs = K fs.
Proof. intros pl j. induction j; intros; cbn [lib_iter LIBK checksum_shape ll_fs]; auto. Qed.
Lemma zpermitted_run : forall pl k fs,
  permitted_traces zallowed (run_shape pl k fs).
Proof.
  intros pl [|k] fs; cbn [run_shape LIBK checksum_shape ll_fs].
  - apply permitted_ex. left; reflexivity.
  - apply permitted_wr. rewrite checksum_iter_identity.
    unfold run_tail. destruct k; try apply permitted_wr;
      apply permitted_ex; left; reflexivity.
Qed.
Lemma zpermitted_leaf : forall data fs r,
  permitted_traces zallowed (leaf_shape data fs r).
Proof.
  intros data fs [dl a]. destruct dl; cbn [leaf_shape fst];
    try apply zpermitted_diag.
  - unfold ex. destruct (count_mode data); apply permitted_ex;
      [left|right;left]; reflexivity.
  - apply permitted_wr, permitted_ex. left; reflexivity.
Qed.
Lemma zpermitted_leafX : forall data fs r,
  permitted_traces zallowed (leaf_shapeX data fs r).
Proof.
  intros data fs [dl a]. destruct dl; cbn [leaf_shapeX fst];
    try apply zpermitted_leaf; apply zpermitted_run.
Qed.
Theorem checksum_SPECX_exits_allowed : forall inp,
  permitted_traces zallowed (SPECX inp).
Proof.
  intros inp. unfold SPECX, SPECX_args.
  destruct (in_argv inp) as [|a [|p [|b rest]]]; try solve [apply zpermitted_diag].
  destruct (classify_open p (in_fs inp)) as [| |data].
  - apply zpermitted_diag.
  - apply permitted_alt2; [apply zpermitted_diag|].
    unfold SPEC_dir. apply permitted_tset. intros [b s].
    destruct b; apply zpermitted_diag.
  - apply permitted_alt2; [apply zpermitted_diag|].
    unfold SPECX_loaded. apply permitted_tset. apply zpermitted_leafX.
Qed.
End Model.
