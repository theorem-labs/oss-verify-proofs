From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import EntSQ_Cnt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require SlotSizes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require SlotSizes.
Local Open Scope Z_scope.

Lemma esq_wl1_holds : esq_wl1.
Proof.
  intros x t H _.
  exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.SlotSizes.wlen_false_read _ x t H).
Qed.

Lemma esq_wl2_holds : esq_wl2.
Proof.
  intros x t H _.
  exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.SlotSizes.wlen_true_read _ x t H).
Qed.

Lemma esq_esz_holds : esq_esz.
Proof.
  intros x t H HN e He.
  rewrite OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.SlotSizes.crt_tree_plain in He.
  exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.SlotSizes.crt_esz _ x t H HN e He).
Qed.
