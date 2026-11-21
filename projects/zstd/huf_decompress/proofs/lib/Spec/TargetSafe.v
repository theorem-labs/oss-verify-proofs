(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (5 recorded proofs replaced by written proofs (fuzz_malloc_spec, free_opt_spec, fuzz_one_spec and 2 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad MSafe MSafeP Harness Adapter Driver.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Keeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_TargetSafe () := "C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness;fuzz_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe4assnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP9mspecP_ifC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC46Stdlib7Sorting;Permutation>Permutation_inC59OSSVerify5KrLib4Spec5MSafe5mspecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP6mspecPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP<mspec_mspecPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP:mspecP_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP;mspecP_bindC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec6MSafeP;mspecP_pureC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3ltbK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02c59OSSVerify5KrLib4Spec:TargetSafe5olistC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6MSafeP5etwfPC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00c59OSSVerify5KrLib4Spec:TargetSafe9OPNEW_MAXC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes9Empty_set00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec7Harness8free_optC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe9mspec_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib4Spec7Harness=dt_size_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness7dt_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness?dbuf_size_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness9dbuf_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic6eq_indc59OSSVerify5KrLib4Spec:TargetSafe@fuzz_malloc_specC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr03c59OSSVerify5KrLib4Spec:TargetSafe=free_opt_specC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationHPermutation_app_swap_appC46Stdlib5Lists4List9app_assocC59OSSVerify5KrLib4Spec5MSafe9mspec_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness8fuzz_oneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe9mspec_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver9MAX_INPUTC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib4Spec7Harness8BUFF_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness<BUFF_MAX_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness=PRODUCER_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness9WKSP_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness=WKSP_SIZE_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Adapter9run_callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Adapter:target_runC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:TargetSafe=fuzz_one_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP:mspecP_seqC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natc59OSSVerify5KrLib4Spec:TargetSafe>run_calls_specC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Section TargetSafe.
Context {St ptr : Type}.
Variable raw_malloc : Z -> M St (option ptr).
Variable raw_free : ptr -> M St unit.
Variable new_handler : M St Empty_set.
Variable emit : Z -> M St unit.
Variable own : list ptr -> assn St.

(* [comment removed for export] *)
Definition OPNEW_MAX : Z := 2^31.

Hypothesis Hm : forall X n, 0 <= n ->
  mspec (own X) (raw_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
(* [comment removed for export] *)
Hypothesis HmS : forall X n, 0 <= n <= OPNEW_MAX ->
  mspecP (own X) (raw_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => False end).
Hypothesis Hf : forall X p, mspec (own (p :: X)) (raw_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
(* [comment removed for export] *)
Hypothesis Hleak : forall X Y s mo, own (Y ++ X) s mo -> own X s mo.
Hypothesis Hemit : forall X v, mspec (own X) (emit v) (fun _ => own X).

(* [comment removed for export] *)
Definition olist (o : option ptr) : list ptr := match o with Some p => [p] | None => [] end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fuzz_malloc_spec : forall X n, n <= OPNEW_MAX ->
  mspecP (own X) (fuzz_malloc raw_malloc new_handler n) (fun r => own (olist r ++ X)).
Proof.
  intros X n Hn. unfold fuzz_malloc.
  apply mspecP_if; intros C.
  - apply Z.ltb_lt in C.
    eapply mspecP_bind; [apply HmS; lia|].
    intros [p|]; cbn beta iota.
    + apply mspecP_pure. intros _. apply mspecP_ret. intros s mo H; exact H.
    + intros s mo [].
  - apply mspecP_ret. intros s mo H; exact H.
Qed.

Lemma free_opt_spec : forall X o,
  mspec (own (olist o ++ X)) (free_opt raw_free o) (fun _ => own X).
Proof.
  intros X [p|]; cbn [free_opt olist app]; [apply Hf| apply mspec_ret; intros s mo H; exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fuzz_one_spec : forall X data, zlength data <= MAX_INPUT ->
  mspecP (own X) (fuzz_one raw_malloc raw_free new_handler data) (fun _ => own X).
Proof.
  intros X data Hlen. unfold fuzz_one.
  pose proof (dt_size_range data ltac:(unfold MAX_INPUT in Hlen; exact Hlen)) as Hdt.
  pose proof (dbuf_size_range data ltac:(unfold MAX_INPUT in Hlen; exact Hlen)) as Hdb. rewrite BUFF_MAX_val in Hdb.
  eapply mspecP_bind; [apply fuzz_malloc_spec; unfold PRODUCER_SIZE, OPNEW_MAX; lia|]. intros producer.
  eapply mspecP_bind; [apply fuzz_malloc_spec; unfold OPNEW_MAX; lia|]. intros dt.
  eapply mspecP_bind; [apply fuzz_malloc_spec; rewrite WKSP_SIZE_val; unfold OPNEW_MAX; lia|]. intros wksp.
  eapply mspecP_bind; [apply fuzz_malloc_spec; unfold OPNEW_MAX; lia|]. intros dBuf.
  apply mspec_mspecP.
  (* the frees run dt, wksp, dBuf, producer; each frame is the one before, permuted *)
  eapply mspec_seq.
  { eapply mspec_pre; [apply (free_opt_spec ((olist producer ++ X) ++ (olist dBuf ++ olist wksp)) dt)|].
    intros s mo H. eapply Hperm; [|exact H].
    rewrite (app_assoc (olist dBuf) (olist wksp) (olist dt ++ olist producer ++ X)).
    rewrite (app_assoc (olist dt) (olist producer ++ X) (olist dBuf ++ olist wksp)).
    apply Permutation_app_comm. }
  intros _.
  eapply mspec_seq.
  { eapply mspec_pre; [apply (free_opt_spec ((olist producer ++ X) ++ olist dBuf) wksp)|].
    intros s mo H. eapply Hperm; [|exact H].
    rewrite (app_assoc (olist producer ++ X) (olist dBuf) (olist wksp)).
    apply Permutation_app_comm. }
  intros _.
  eapply mspec_seq.
  { eapply mspec_pre; [apply (free_opt_spec (olist producer ++ X) dBuf)|].
    intros s mo H. eapply Hperm; [|exact H]. apply Permutation_app_comm. }
  intros _.
  eapply mspec_seq; [apply free_opt_spec|]. intros _.
  apply mspec_ret. intros s mo H; exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_calls_spec : forall X n payload rc, zlength payload <= MAX_INPUT ->
  mspecP (own X) (run_calls (fuzz_one raw_malloc raw_free new_handler) emit n payload rc) (fun _ => own X).
Proof.
  intros X n. induction n as [|n IH]; intros payload rc Hlen; cbn [run_calls].
  - apply mspecP_ret. intros s mo H; exact H.
  - eapply mspecP_seq; [apply fuzz_one_spec; exact Hlen|]. intros rc'.
    eapply mspecP_seq; [apply mspec_mspecP; apply Hemit|]. intros _. apply IH. exact Hlen.
Qed.

Theorem target_run_spec : forall X cfg payload, zlength payload <= MAX_INPUT ->
  mspecP (own X) (target_run raw_malloc raw_free (fuzz_one raw_malloc raw_free new_handler) emit cfg payload) (fun _ => own X).
Proof using Hm HmS Hf Hperm Hleak Hemit.   (* [comment removed for export] *)
  intros X cfg payload Hlen. unfold target_run.
  eapply mspecP_bind with (Q1 := fun a s mo => match a with
                                               | None => own X s mo
                                               | Some None => own X s mo
                                               | Some (Some p) => own (p :: X) s mo
                                               end).
  { apply mspecP_if; intros _; [apply mspecP_ret; intros s mo H; exact H|].
    eapply mspecP_bind; [apply mspec_mspecP; apply Hm; unfold zlength; lia|]. intros [p|]; apply mspecP_ret; cbn; [intros s mo [H _]; exact H| intros s mo H; exact H]. }
  intros [[p|]|]; cbn beta iota.
  - eapply mspecP_seq; [apply run_calls_spec; exact Hlen|]. intros rc. eapply mspecP_seq; [apply mspec_mspecP; apply Hf|]. intros _. apply mspecP_ret. intros s mo H; exact H.
  - eapply mspecP_seq; [apply run_calls_spec; exact Hlen|]. intros rc. eapply mspecP_seq; [apply mspecP_ret; intros s mo H; exact H|]. intros _. apply mspecP_ret. intros s mo H; exact H.
  - apply mspecP_ret. intros s mo H; exact H.
Qed.

End TargetSafe.
