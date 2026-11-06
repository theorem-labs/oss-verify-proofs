From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import ContractCF.
Import ListNotations.
Local Open Scope Z_scope.

(* The lemmas of U/Prog/ReaderRes.v stated at the sbound form, restated at ContractCF.sb_form (the same malloc, free
   and realloc as Contract.sb_form; only the room differs). *)
Lemma sb_form_malloc : forall (b : sbound) n, rf_malloc sb_form b n = sb_malloc b n.
Proof. reflexivity. Qed.

Lemma sb_form_free : forall (b : sbound) n, rf_free sb_form b n = sb_free b n.
Proof. reflexivity. Qed.

Lemma sb_form_realloc : forall (b : sbound) k n, rf_realloc sb_form b k n = sb_realloc b k n.
Proof. reflexivity. Qed.

Lemma sb_run_eq : forall tr (b : sbound),
  rf_run sb_form b tr = SB (sb_live b + nlive tr) (sb_bytes b + held tr + 16 * nlive tr) (sb_cap b).
Proof.
  unfold rf_run. induction tr as [|e tr IH]; intros b; cbn [fold_left nlive held].
  - destruct b as [l y c]. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
  - rewrite IH. destruct e as [n|[|m] n|n|n]; cbn [rf_ev nlive_ev held_ev].
    + rewrite sb_form_malloc. unfold sb_malloc. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
    + unfold rf_grow. change (Z.of_nat 0) with 0. rewrite Z.eqb_refl, sb_form_malloc. unfold sb_malloc.
      cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
    + unfold rf_grow. rewrite (proj2 (Z.eqb_neq (Z.of_nat (S m)) 0)) by lia. rewrite sb_form_realloc.
      unfold sb_realloc. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
    + f_equal; lia.
    + rewrite sb_form_free. unfold sb_free. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
Qed.

Lemma sb_frees_eq : forall D (b : sbound),
  rf_frees sb_form b D =
  SB (sb_live b - Z.of_nat (length D)) (sb_bytes b - lsum D - 16 * Z.of_nat (length D)) (sb_cap b).
Proof.
  unfold rf_frees. induction D as [|[a k] D IH]; intros b; cbn [fold_left length lsum snd].
  - destruct b as [l y c]. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
  - rewrite IH, sb_form_free. unfold sb_free. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
Qed.

Lemma sb_frees_run : forall (b : sbound) tr D, Permutation (map snd D) (map Z.of_nat (lsz tr)) ->
  Z.of_nat (length D) = nlive tr -> rf_frees sb_form (rf_run sb_form b tr) D = b.
Proof.
  intros b tr D HP HN. pose proof (lsz_counts D tr HP HN) as HL. rewrite sb_frees_eq, sb_run_eq.
  destruct b as [l y c]. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
Qed.

Lemma sb_frees_perm : forall (b : sbound) D D', Permutation D D' ->
  rf_frees sb_form b D = rf_frees sb_form b D'.
Proof.
  intros b D D' HP. revert b. unfold rf_frees.
  induction HP as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; intros b; cbn [fold_left].
  - reflexivity.
  - apply IH.
  - f_equal. change (sb_free (sb_free b (snd y + 16)) (snd x + 16) = sb_free (sb_free b (snd x + 16)) (snd y + 16)).
    unfold sb_free. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
  - rewrite IH1. apply IH2.
Qed.

