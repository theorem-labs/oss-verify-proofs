(* SPDX-License-Identifier: MIT *)
(** Exit-status obligations for a returning, allocation-free checksum harness.
    This model is useful only after its binary library contract is proved. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
  YK11 YK15 YO0i YO0f YM02 YO05 YO09 YO06 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import TraceHalting AllocSlots AllocRoom.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition zallowed : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
#[global] Instance checksum_shape : lib_shape.
Proof.
  refine {| LIBK := fun pl fs K => K (LL 0 fs []);
    lib_delta := fun n b => b;
    lib_room := fun b n => sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAPMAX |}.
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
Definition shape_permitted (LS : lib_shape) : Prop :=
  forall pl fs K, (forall l, permitted_traces zallowed (K l)) -> permitted_traces zallowed (@LIBK LS pl fs K).
Lemma checksum_permitted : shape_permitted checksum_shape.
Proof. intros pl fs K HK. exact (HK _). Qed.
Section Model.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape}.
Hypothesis LSP : shape_permitted LS.
Lemma zpermitted_iter : forall pl j K fs,
  (forall fs', permitted_traces zallowed (K fs')) -> permitted_traces zallowed (lib_iter pl j K fs).
Proof using LSP.
  intros pl j. induction j as [|j IH]; intros K fs HK; cbn [lib_iter]; [apply HK|].
  apply LSP. intros l. apply IH. exact HK.
Qed.
Lemma zpermitted_run : forall pl k fs,
  permitted_traces zallowed (run_shape pl k fs).
Proof using LSP.
  intros pl [|k] fs; cbn [run_shape].
  - apply permitted_ex. left; reflexivity.
  - apply LSP. intros l. apply permitted_wr. apply zpermitted_iter. intros fs'.
    unfold run_tail. destruct k; try apply permitted_wr;
      apply permitted_ex; left; reflexivity.
Qed.
Lemma zpermitted_leaf : forall data fs r,
  permitted_traces zallowed (leaf_shape data fs r).
Proof using.
  intros data fs [dl a]. destruct dl; cbn [leaf_shape fst];
    try apply zpermitted_diag.
  - unfold ex. destruct (count_mode data); apply permitted_ex;
      [left|right;left]; reflexivity.
  - apply permitted_wr, permitted_ex. left; reflexivity.
Qed.
Lemma zpermitted_leafX : forall data fs r,
  permitted_traces zallowed (leaf_shapeX data fs r).
Proof using LSP.
  intros data fs [dl a]. destruct dl; cbn [leaf_shapeX fst];
    try apply zpermitted_leaf; apply zpermitted_run.
Qed.
Theorem checksum_SPECX_exits_allowed : forall inp,
  permitted_traces zallowed (SPECX inp).
Proof using LSP.
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
