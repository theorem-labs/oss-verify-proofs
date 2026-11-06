From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
WriterSpec WriterSpecFacts WriterApp WriterAppFacts WriterValue check_reject_clean_starved_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma crs_dbl_le : forall f c need, (exists j, 0 <= j /\ c = 4096 * 2 ^ j) -> c <= 2 ^ 28 -> need <= 2 ^ 28 ->
  dbl f c need <= 2 ^ 28.
Proof.
  assert (E28 : 2 ^ 28 = 4096 * 2 ^ 16) by reflexivity.
  induction f as [|f IH]; intros c need [j [Hj Ec]] Hc Hn; cbn [dbl]; [exact Hc|].
  destruct (Z.leb_spec need c) as [H|H]; [exact Hc|].
  assert (Hj16 : j + 1 <= 16).
  { destruct (Z.lt_ge_cases j 16) as [L|L]; [lia|].
    pose proof (Z.pow_le_mono_r 2 16 j ltac:(lia) L). lia. }
  assert (Hp : 2 ^ (j + 1) = 2 * 2 ^ j) by (rewrite Z.pow_add_r by lia; rewrite Z.pow_1_r; lia).
  assert (Hq : 2 ^ (j + 1) <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia).
  apply IH; [exists (j + 1); split; lia | lia | exact Hn].
Qed.

Lemma newcap_le28 : forall c need, (c = 0 \/ cap_pow c) -> c < need <= 2 ^ 28 -> newcap c need <= 2 ^ 28.
Proof.
  intros c need Hc Hn. unfold newcap. apply crs_dbl_le; [| |lia].
  - destruct (Z.eqb_spec c 0) as [_|Hne]; [exists 0; split; [lia|reflexivity]|].
    destruct Hc as [->|[j [Hj ->]]]; [lia|]. exists j. split; [lia|reflexivity].
  - destruct (Z.eqb_spec c 0) as [_|Hne]; [|lia].
    assert (E28 : 2 ^ 28 = 268435456) by reflexivity. lia.
Qed.

Lemma wdpieces_nonempty : forall t p, wdpieces t p <> [].
Proof. intros t p. unfold wdpieces. destruct t; cbn [wvpieces]; try unfold spieces; cbn [app]; discriminate. Qed.

Lemma crs_skipn_app : forall (l m : list Z), skipn (length l) (l ++ m) = m.
Proof. induction l as [|x l IH]; intros m; [reflexivity|]. cbn [length skipn app]. apply IH. Qed.

Lemma crs_put1_calls : forall st bs, (length (w_calls st) <= length (w_calls (put1 st bs)))%nat.
Proof.
  intros [f t c n fl cs] bs. destruct (Z.eqb_spec f 0) as [->|Hf].
  - destruct (Z.ltb_spec c (Z.of_nat (length t) + Z.of_nat (length bs) + 1)) as [Hg|Hg].
    + destruct (Z.eqb_spec n fl) as [Heq|Hne].
      * rewrite put1_starve by assumption. cbn [w_calls]. rewrite length_app. lia.
      * rewrite put1_grow by assumption. cbn [w_calls]. rewrite length_app. lia.
    + rewrite put1_fit by assumption. cbn [w_calls]. lia.
  - assert (E : put1 (mkW f t c n fl cs) bs = mkW f t c n fl cs) by exact (putN_failed [bs] (mkW f t c n fl cs) Hf).
    rewrite E. lia.
Qed.

Lemma crs_calls_mono : forall P st, (length (w_calls st) <= length (w_calls (putN st P)))%nat.
Proof.
  induction P as [|bs P IH]; intros st; [rewrite putN_nil; lia|].
  rewrite putN_cons. eapply Nat.le_trans; [apply crs_put1_calls|apply IH].
Qed.

Lemma crs_wcalls_gen : forall P st, w_failed st = 0 ->
  exists m, w_calls (putN st P) =
    w_calls st ++ firstn m (grow_calls (Z.of_nat (length (w_text st))) (w_cap st) (piece_lens P)).
Proof.
  induction P as [|bs P IH]; intros [f t c n fl cs] Hf; cbn [w_failed w_text w_cap w_calls] in *; subst f.
  - exists 0%nat. rewrite putN_nil. cbn [w_calls firstn]. rewrite app_nil_r. reflexivity.
  - rewrite putN_cons, piece_lens_cons, grow_calls_cons.
    destruct (Z.ltb_spec c (Z.of_nat (length t) + Z.of_nat (length bs) + 1)) as [Hg|Hg].
    + destruct (Z.eqb_spec n fl) as [Heq|Hne].
      * rewrite put1_starve by assumption. rewrite putN_failed by (cbn [w_failed]; lia).
        exists 1%nat. cbn [w_calls firstn]. reflexivity.
      * rewrite put1_grow by assumption.
        match goal with |- context [putN ?s P] => destruct (IH s eq_refl) as [m E] end.
        rewrite E. exists (S m). cbn [w_calls w_text w_cap firstn].
        rewrite length_app, Nat2Z.inj_add, <- app_assoc. reflexivity.
    + rewrite put1_fit by assumption.
      match goal with |- context [putN ?s P] => destruct (IH s eq_refl) as [m E] end.
      rewrite E. exists m. cbn [w_calls w_text w_cap]. rewrite length_app, Nat2Z.inj_add. reflexivity.
Qed.

Lemma wcalls_prefix : forall P cnt fail,
  exists m, w_calls (putN (w0 cnt fail) P) = firstn m (grow_calls 0 0 (piece_lens P)).
Proof.
  intros P cnt fail. destruct (crs_wcalls_gen P (w0 cnt fail) eq_refl) as [m E]. exists m. exact E.
Qed.

Lemma crs_dbl_reach : forall f c need, 1 <= c -> need <= c * 2 ^ Z.of_nat f -> need <= dbl f c need.
Proof.
  induction f as [|f IH]; intros c need Hc Hn; cbn [dbl].
  - change (2 ^ Z.of_nat 0) with 1 in Hn. lia.
  - destruct (Z.leb_spec need c) as [H|H]; [exact H|]. apply IH; [lia|].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hn by lia. lia.
Qed.

Lemma crs_newcap_reach : forall c need, 0 <= c -> need <= 2 ^ 64 -> need <= newcap c need.
Proof.
  intros c need Hc Hn. unfold newcap. apply crs_dbl_reach.
  - destruct (Z.eqb_spec c 0); lia.
  - change (Z.of_nat 64) with 64. destruct (Z.eqb_spec c 0); nia.
Qed.

Lemma crs_gc_len : forall ls x c, 0 <= x -> x + 1 <= c -> Forall (fun l => 0 <= l) ls ->
  x + fold_right Z.add 0 ls + 1 <= 2 ^ 62 ->
  Z.of_nat (length (grow_calls x c ls)) <= fold_right Z.add 0 ls.
Proof.
  induction ls as [|l ls IH]; intros x c Hx Hc Hf Hs; [cbn; lia|].
  apply Forall_cons_iff in Hf as [Hl Hf]. cbn [grow_calls fold_right] in *.
  assert (Hr : 0 <= fold_right Z.add 0 ls).
  { clear -Hf. induction Hf as [|a l' Ha _ IH]; cbn; lia. }
  destruct (Z.ltb_spec c (x + l + 1)) as [H|H].
  - pose proof (crs_newcap_reach c (x + l + 1) ltac:(lia) ltac:(lia)) as Hn.
    specialize (IH (x + l) (newcap c (x + l + 1)) ltac:(lia) ltac:(lia) Hf ltac:(lia)).
    cbn [length]. lia.
  - specialize (IH (x + l) c ltac:(lia) ltac:(lia) Hf ltac:(lia)). lia.
Qed.

Lemma crs_lens_sum : forall P, fold_right Z.add 0 (piece_lens P) = Z.of_nat (length (concat P)).
Proof.
  induction P as [|bs P IH]; [reflexivity|]. unfold piece_lens in *. cbn [map fold_right concat].
  rewrite IH, length_app. lia.
Qed.

Lemma crs_lens_nn : forall P, Forall (fun l => 0 <= l) (piece_lens P).
Proof. intros P. unfold piece_lens. apply Forall_forall. intros l Hl. apply in_map_iff in Hl as (b & <- & _). lia. Qed.

Lemma crs_wcalls_le : forall P, Z.of_nat (length (concat P)) + 1 <= 2 ^ 62 ->
  Z.of_nat (length (grow_calls 0 0 (piece_lens P))) <= Z.of_nat (length (concat P)) + 1.
Proof.
  intros P Hs. pose proof (crs_lens_nn P) as Hf. rewrite <- crs_lens_sum in *.
  revert Hs Hf. generalize (piece_lens P). intros ls0 Hs Hf.
  destruct ls0 as [|l ls]; [cbn; lia|].
  apply Forall_cons_iff in Hf as [Hl Hf]. cbn [grow_calls fold_right] in *.
  assert (Hr : 0 <= fold_right Z.add 0 ls).
  { clear -Hf. induction Hf as [|a l' Ha _ IH]; cbn; lia. }
  rewrite (proj2 (Z.ltb_lt 0 (0 + l + 1))) by lia.
  pose proof (crs_newcap_reach 0 (0 + l + 1) ltac:(lia) ltac:(lia)) as Hn.
  pose proof (crs_gc_len ls (0 + l) (newcap 0 (0 + l + 1)) ltac:(lia) ltac:(lia) Hf ltac:(lia)) as H.
  cbn [length]. lia.
Qed.
