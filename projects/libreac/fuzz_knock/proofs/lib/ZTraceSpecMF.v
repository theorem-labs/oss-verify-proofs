From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import HaltsAllowed.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
  YK11 YK15 YO0i YO0f YM02 YO05 YO09 YO06 YM05 YO0d_mf YO06_mf.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import TraceHalting ZTraceSpec.
Import ListNotations.
Open Scope Z_scope.
Lemma permitted_tset_mf {S A} : forall allowed (t : itree S A) K,
  (forall a, permitted_traces allowed (K a)) ->
  permitted_traces allowed (tset_mf t K).
Proof.
  intros allowed t. induction t as [a|q s k IH|e]; intros K HK; cbn.
  - apply HK.
  - destruct q; cbn;
      first [ intros tr [z Hz]; exact (IH (proj1_sig z) K HK tr Hz)
            | apply permitted_alt2; apply IH; exact HK
            | apply IH; exact HK
            | destruct (fallible _); [apply permitted_alt2|]; apply IH; exact HK ].
  - intros tr H. contradiction.
Qed.
Lemma permitted_traces_incl : forall (allowed allowed' : list word) T,
  (forall w, In w allowed -> In w allowed') ->
  permitted_traces allowed T -> permitted_traces allowed' T.
Proof.
  intros allowed allowed' T Hinc HT tr Htr. specialize (HT tr Htr).
  eapply Forall_impl; [|exact HT]. intros [] He; cbn in *; auto.
Qed.
Lemma zallowed_any : forall w, In w zallowed -> In w AnyExit.codes.
Proof.
  intros w [<-|[<-|[]]]; apply in_byte_codes; lia.
Qed.
Section Model.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape}.
Hypothesis LSP : shape_permitted LS.
Theorem checksum_SPECX_mf_exits_allowed : forall inp,
  permitted_traces zallowed (SPECX_mf inp).
Proof using LSP.
  intros inp. unfold SPECX_mf, SPECX_args_mf.
  destruct (in_argv inp) as [|a [|p [|b rest]]]; try solve [apply zpermitted_diag].
  destruct (classify_open p (in_fs inp)) as [| |data].
  - apply zpermitted_diag.
  - apply permitted_alt2; [apply zpermitted_diag|].
    unfold SPEC_dir_mf. apply permitted_tset_mf. intros [b s].
    destruct b; apply zpermitted_diag.
  - apply permitted_alt2; [apply zpermitted_diag|].
    unfold SPECX_loaded_mf. apply permitted_tset_mf. apply (zpermitted_leafX LSP).
Qed.
Theorem checksum_SPECX_mf_exits_any : forall inp,
  permitted_traces AnyExit.codes (SPECX_mf inp).
Proof using LSP.
  intros inp. exact (permitted_traces_incl _ _ _ zallowed_any (checksum_SPECX_mf_exits_allowed inp)).
Qed.
End Model.
