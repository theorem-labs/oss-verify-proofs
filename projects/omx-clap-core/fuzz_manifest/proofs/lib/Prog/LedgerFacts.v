From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import Ledger.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lsum_app : forall l1 l2, lsum (l1 ++ l2) = lsum l1 + lsum l2.
Proof. induction l1 as [|[a k] l1 IH]; intros l2; cbn [app lsum]; [reflexivity | rewrite IH; lia]. Qed.

Lemma lsum_nonneg : forall Lam, Forall (fun ak => 0 <= snd ak) Lam -> 0 <= lsum Lam.
Proof.
  induction Lam as [|[a k] Lam IH]; intros H; cbn [lsum]; [lia|].
  inversion H as [|x l Hk Hr]; subst. cbn [snd] in Hk. specialize (IH Hr). lia.
Qed.

Section LedgerFree.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Let segs := ms_segs B.

Lemma ledger_sizes : forall L A mem Lam peak cnt fail, ledger B L A mem Lam peak cnt fail ->
  Forall (fun ak => 0 <= snd ak) Lam.
Proof.
  intros L A mem Lam peak cnt fail (_ & _ & _ & _ & _ & HF).
  eapply Forall_impl; [|exact HF]. intros [a k] (Hk & _). exact Hk.
Qed.

Lemma ledger_free : forall L A mem L' A' mem' l1 l2 p k peak cnt fail b1 b2,
  ledger B L A mem (l1 ++ (p, k) :: l2) peak cnt fail ->
  blocks L A = b1 ++ (p - 16, k + 16) :: b2 -> blocks L' A' = b1 ++ b2 ->
  (forall a n i, In (a, n) (blocks L A) -> a <> p - 16 -> 0 <= i < n ->
     mbyte segs mem' (a + i) = mbyte segs mem (a + i)) ->
  word_mem segs mem' G_LIVE (lsum (l1 ++ l2)) ->
  (forall x, G_PEAK <= x < G_PEAK + 8 \/ G_COUNT <= x < G_COUNT + 8 \/ G_FAIL <= x < G_FAIL + 8 ->
     mbyte segs mem' x = mbyte segs mem x) ->
  ledger B L' A' mem' (l1 ++ l2) peak cnt fail.
Proof.
  intros L A mem L' A' mem' l1 l2 p k peak cnt fail b1 b2 Hled Hb Hb' Hk HL Hg.
  pose proof (ledger_sizes _ _ _ _ _ _ _ Hled) as Hs.
  destruct Hled as ((_ & HWp & HWc & HWf) & HP & HC & HF & HN & HB).
  assert (Hk0 : 0 <= k).
  { rewrite Forall_forall in Hs. exact (Hs (p, k) ltac:(apply in_or_app; right; left; reflexivity)). }
  rewrite lsum_app in HP. cbn [lsum] in HP.
  rewrite map_app in HN. cbn [map fst] in HN. apply NoDup_ListNoDup in HN.
  split.
  { split; [exact HL|].
    split; [apply (word_mem_frame segs mem mem'); [exact HWp | intros j Hj; apply Hg; left; unfold G_PEAK; lia]|].
    split; [apply (word_mem_frame segs mem mem'); [exact HWc | intros j Hj; apply Hg; right; left; unfold G_COUNT; lia]|].
    apply (word_mem_frame segs mem mem'); [exact HWf | intros j Hj; apply Hg; right; right; unfold G_FAIL; lia]. }
  split; [rewrite lsum_app; lia|]. split; [exact HC|]. split; [exact HF|].
  split; [rewrite map_app; apply NoDup_ListNoDup; exact (NoDup_remove_1 _ _ _ HN)|].
  rewrite Forall_forall in HB |- *. intros [a k'] Hin.
  assert (Hne : a <> p).
  { intros ->. apply (NoDup_remove_2 _ _ _ HN). rewrite <- map_app. apply in_map_iff.
    exists (p, k'). split; [reflexivity | exact Hin]. }
  assert (Hin0 : In (a, k') (l1 ++ (p, k) :: l2)).
  { apply in_app_or in Hin. apply in_or_app. destruct Hin as [H|H]; [left; exact H | right; right; exact H]. }
  pose proof (HB (a, k') Hin0) as H. unfold lblock in H |- *. cbn [fst snd] in H |- *.
  destruct H as (H0 & Hin1 & Hw & Hi).
  split; [exact H0|]. split; [|split; [|exact Hi]].
  - rewrite Hb'. rewrite Hb in Hin1. apply in_app_or in Hin1. apply in_or_app.
    destruct Hin1 as [H|[H|H]]; [left; exact H | injection H; intros; lia | right; exact H].
  - apply (word_mem_frame segs mem mem'); [exact Hw|]. intros j Hj. apply (Hk (a - 16) (k' + 16)); [exact Hin1 | lia | lia].
Qed.

End LedgerFree.
