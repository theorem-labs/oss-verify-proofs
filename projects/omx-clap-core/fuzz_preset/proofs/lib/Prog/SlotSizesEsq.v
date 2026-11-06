From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import EntSQ_Cnt SlotSizes.
Local Open Scope Z_scope.

Lemma esq_wl1_holds : esq_wl1.
Proof. intros x t H _. exact (wlen_false_read _ x t H). Qed.

Lemma esq_wl2_holds : esq_wl2.
Proof. intros x t H _. exact (wlen_true_read _ x t H). Qed.

Lemma esq_esz_holds : esq_esz.
Proof. intros x t H HN. exact (crt_esz _ x t H HN). Qed.
