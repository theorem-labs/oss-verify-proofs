(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the new launch (process input, auxv, group id, exec file name); the run over the run's segments. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import SimInv ExitSim CatSim ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_KillFree () := "C47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib4Init5Logic7f_equalI47Corelib5Lists7ListDef6Forall00C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes8list_indC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapI46Stdlib5Lists4List6Exists00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib5Lists7ListDef6Forall01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic9False_indI47Corelib4Init5Logic2eq00K47Corelib5Lists7ListDef6Forall02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic3and00I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg5t_nilC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFree9kill_freeC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFree;ev_not_killC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_emitC13~~~I47Corelib4Init5Logic2ex00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFree=Forall_prefixC13~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:Forall_appK47Corelib4Init5Logic3and01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~I47Corelib4Init5Logic2or00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_alt2C13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K4ELinuxProcessSemantics?LinuxProcessSem5State5event03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFree>kill_free_emitC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_exitC13~~~K47Corelib7Numbers7BinNums8positive03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFree=kill_free_nilC13~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec1WC13~~~C45stdpp9bitvector;definitions7Z_to_bvc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFreeFForall_not_kill_writesC13~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec9exit_codeC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFree>kill_free_exitC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFree@kill_free_W_emitC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec5t_dieC13~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3lebK47Corelib4Init9Datatypes3nat02C56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec:zero_linesC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFree=kill_free_dieC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:BigintSpec6t_bodyC13~~~C47Corelib5Lists7ListDef3nthC45stdpp9bitvector;definitions;bv_unsignedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec9MAX_INPUTC13~~~I47Corelib4Init9Datatypes4bool00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;msg_refusedC13~~~K47Corelib4Init9Datatypes3nat01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec9msg_shortC13~~~K47Corelib7Numbers7BinNums1Z01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;msg_overrunC13~~~I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3lebC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec?msg_cannot_openC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec=list_byte_eqbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec>msg_read_errorC13~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFree>kill_free_alt2C13~~~I47Corelib4Init9Datatypes6option00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFree@kill_free_t_bodyC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:BigintSpec4specC13~~~C46Stdlib5Lists4List2hdC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec9msg_usageC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec8dot_pathC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srealizes000C13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence>dies_by_signalK4ELinuxProcessSemantics?LinuxProcessSem5State5event04C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ShapeEFDsrealizes_traces_iffC13~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic3notK4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run8run_scfgC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesI4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~C4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence:error_freeC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ShapeEFDsrealizes_error_freeC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFreeLsrealizes_not_dies_by_signalC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ev_not_kill (e : event) : Prop :=
  match e with KillEv _ _ => False | _ => True end.

Definition kill_free (T : TSet) : Prop := forall tr, T tr -> Forall ev_not_kill tr.

Lemma Forall_prefix {A} (P : A -> Prop) : forall (l1 l2 : list A),
  is_prefix l1 l2 -> Forall P l2 -> Forall P l1.
Proof.
  induction l1 as [|x l1 IH]; intros l2 Hp Hl2; [constructor|].
  destruct l2 as [|y l2]; cbn in Hp; [contradiction|].
  destruct Hp as [-> Hp]. inversion Hl2; subst. constructor; [assumption | eapply IH; eassumption].
Qed.

Lemma kill_free_nil : kill_free t_nil.
Proof. intros tr ->. constructor. Qed.

Lemma kill_free_emit : forall evs T,
  Forall ev_not_kill evs -> kill_free T -> kill_free (t_emit evs T).
Proof.
  intros evs T Hevs HT tr [Hp | (tr' & -> & Htr')].
  - eapply Forall_prefix; eassumption.
  - apply Forall_app. split; [exact Hevs | exact (HT _ Htr')].
Qed.

Lemma kill_free_alt2 : forall A B, kill_free A -> kill_free B -> kill_free (t_alt2 A B).
Proof. intros A B HA HB tr [H | H]; [exact (HA _ H) | exact (HB _ H)]. Qed.

Lemma kill_free_exit : forall code fs, kill_free (t_exit code fs).
Proof.
  intros code fs. unfold t_exit. apply kill_free_emit; [| apply kill_free_nil].
  constructor; [exact I | constructor].
Qed.

Lemma Forall_not_kill_writes : forall ch (s : list byte), Forall ev_not_kill (map (WriteEv ch) s).
Proof. intros ch s. induction s as [|b s IH]; cbn; constructor; [exact I | exact IH]. Qed.

Section FPX_1.
Context {fx : PropExec.FPState}.

Lemma kill_free_W_emit : forall ch s T, kill_free T -> kill_free (t_emit (W ch s) T).
Proof. intros ch s T HT. apply kill_free_emit; [apply Forall_not_kill_writes | exact HT]. Qed.

Lemma kill_free_die : forall msg fs, kill_free (t_die msg fs).
Proof. intros msg fs. unfold t_die. apply kill_free_W_emit. apply kill_free_exit. Qed.

Lemma kill_free_t_body : forall data fs, kill_free (BigintSpec.t_body data fs).
Proof.
  intros data fs. unfold BigintSpec.t_body.
  repeat first [ apply kill_free_die
               | apply kill_free_W_emit
               | apply kill_free_exit
               | match goal with |- kill_free (if ?c then _ else _) => destruct c end
               | match goal with |- kill_free (match ?c with _ => _ end) => destruct c end ].
Qed.

Lemma kill_free_spec : forall argv fs, kill_free (BigintSpec.spec argv fs).
Proof.
  intros argv fs. unfold BigintSpec.spec.
  repeat first [ apply kill_free_die
               | apply kill_free_t_body
               | apply kill_free_alt2
               | apply kill_free_exit
               | match goal with |- kill_free (if ?c then _ else _) => destruct c end
               | match goal with |- kill_free (match ?c with _ => _ end) => destruct c end ].
Qed.

(* [comment removed for export] *)
Lemma srealizes_not_dies_by_signal : forall scfg segs pc ph sp brk0 mb rnd lim inp T,
  srealizes0 (run_segments segs inp sp mb) scfg(init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  kill_free T ->
  ~ dies_by_signal (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros scfg segs pc ph sp brk0 mb rnd lim inp T Hs HK (tr & sig & fs & Htr & Hin).
  apply (srealizes_traces_iff scfg segs pc ph sp brk0 mb rnd lim inp T tr Hs) in Htr.
  pose proof (HK _ Htr) as HF.
  apply Forall_forall with (x := KillEv sig fs) in HF; [exact HF | exact Hin].
Qed.

Lemma srealizes_error_free_unkilled : forall scfg segs pc ph sp brk0 mb rnd lim inp T,
  srealizes0 (run_segments segs inp sp mb) scfg(init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  kill_free T ->
  error_free_unkilled (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros. split; [eapply srealizes_error_free; eassumption | eapply srealizes_not_dies_by_signal; eassumption].
Qed.

End FPX_1.
