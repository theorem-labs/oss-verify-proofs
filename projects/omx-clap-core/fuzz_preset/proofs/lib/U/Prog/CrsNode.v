From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
Import ListNotations.
Local Open Scope Z_scope.

Section CrsNode.
Variable segs : list Segment.

Lemma cn_mrd : forall (m : word -> option byte) y, Mem.mrd segs m (Mem.wa y) = mbyte segs m y.
Proof. reflexivity. Qed.

Lemma cn_bytes : forall m m' a bs, Mem.bytes_at segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte segs m' x = mbyte segs m x) ->
  Mem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs (Ha & Hl & H) E. split; [lia|]. split; [lia|].
  intros i Hi. specialize (H i Hi). rewrite cn_mrd in H |- *. rewrite E by lia. exact H.
Qed.

Lemma cn_rw : forall m m' p, pj_rw segs m p ->
  (forall x, p <= x < p + 56 -> mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x -> writable_at segs m' x)) ->
  pj_rw segs m' p.
Proof.
  intros m m' p (Hm & H1 & H2 & H) E. split; [exact Hm|]. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [W [b R]]. destruct (E a Ha) as [E1 E2]. split.
  - exact (E2 W).
  - exists b. rewrite cn_mrd in R |- *. rewrite E1. exact R.
Qed.

Lemma cn_u64 : forall m m' a v, pj_u64 segs m a v ->
  (forall x, a <= x < a + 8 -> mbyte segs m' x = mbyte segs m x) -> pj_u64 segs m' a v.
Proof.
  intros m m' a v (Hv & Hb) E. split; [exact Hv|]. apply (cn_bytes m m'); [exact Hb|].
  intros x Hx. apply E. rewrite Mem.length_le8 in Hx. lia.
Qed.

Lemma cn_hdr : forall m m' p ty num str kids keys n cap,
  pj_hdr segs m p ty num str kids keys n cap ->
  (forall x, p <= x < p + 56 -> mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x -> writable_at segs m' x)) ->
  pj_hdr segs m' p ty num str kids keys n cap.
Proof.
  intros m m' p ty num str kids keys n cap (Hrw & (T0 & T1) & (N0 & N1) & (S0 & S1) & (K0 & K1) & (Y0 & Y1) & (C0 & C1) & (P0 & P1)) E.
  assert (F : forall a bs, Mem.bytes_at segs m a bs -> p <= a -> a + Z.of_nat (length bs) <= p + 56 ->
    Mem.bytes_at segs m' a bs).
  { intros a bs Hb Hpa Hab. apply (cn_bytes m m'); [exact Hb|]. intros x Hx. apply E. lia. }
  split; [exact (cn_rw m m' p Hrw E)|].
  split; [split; [exact T0 | apply F; [exact T1 | lia | rewrite Mem.length_le4; lia]]|].
  split; [split; [exact N0 | apply F; [exact N1 | lia | rewrite Mem.length_le8; lia]]|].
  split; [split; [exact S0 | apply F; [exact S1 | lia | rewrite Mem.length_le8; lia]]|].
  split; [split; [exact K0 | apply F; [exact K1 | lia | rewrite Mem.length_le8; lia]]|].
  split; [split; [exact Y0 | apply F; [exact Y1 | lia | rewrite Mem.length_le8; lia]]|].
  split; [split; [exact C0 | apply F; [exact C1 | lia | rewrite Mem.length_le8; lia]]|].
  split; [exact P0 | apply F; [exact P1 | lia | rewrite Mem.length_le8; lia]].
Qed.

Lemma cn_cstr_mframe : forall m m' lb a k s, pj_cstr segs m lb a k s ->
  (forall x, a <= x < a + k -> mbyte segs m' x = mbyte segs m x) -> pj_cstr segs m' lb a k s.
Proof.
  intros m m' lb a k s (Hl & Hk & Hf & Hb) E.
  split; [exact Hl|]. split; [exact Hk|]. split; [exact Hf|].
  apply (cn_bytes m m'); [exact Hb|]. intros x Hx. apply E.
  rewrite length_map, length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma cn_node_mframe : forall m m' lb p t D, pj_node segs m lb p t D ->
  (forall x, pj_foot p D x -> mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x -> writable_at segs m' x)) ->
  pj_node segs m' lb p t D.
Proof.
  intros m m' lb p t. revert m m' lb p.
  induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
    intros m m' lblk p D H HM; cbn [pj_node] in H |- *;
    assert (HM1 : forall x, pj_foot p D x -> mbyte segs m' x = mbyte segs m x) by (intros x Hx; exact (proj1 (HM x Hx)));
    destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
    (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap;
    (split; [apply (cn_hdr m m'); [exact Hh | intros x Hx; apply HM; left; exact Hx]|]).
  - exact Hb.
  - exact Hb.
  - exact Hb.
  - destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    exists k. split; [|exact ED].
    apply (cn_cstr_mframe m m'); [exact Hc|].
    intros x Hx. apply HM1. right. exists (str, k).
    split; [subst D; left; reflexivity | unfold pj_holds; cbn [fst snd]; exact Hx].
  - destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
    split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    exists k. split; [|exact ED].
    apply (cn_cstr_mframe m m'); [exact Hc|].
    intros x Hx. apply HM1. right. exists (str, k).
    split; [subst D; left; reflexivity | unfold pj_holds; cbn [fst snd]; exact Hx].
  - destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
    split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|]. split; [exact Hcap|].
    assert (Hin : 0 < cap -> In (kids, 56 * cap) D).
    { intros Hp. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
    assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
    exists Di. split; [exact ED|].
    apply (pj_items_mono (pj_node segs m lblk) (pj_node segs m' lblk)); [|exact Hi].
    intros i u D1 Hil Hu Hinc HP.
    assert (Hp : 0 < cap) by lia.
    rewrite Forall_forall in IH.
    apply (IH u Hu m m' lblk _ D1 HP).
    intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
    + right. exists (kids, 56 * cap). split; [apply (Hin Hp) | unfold pj_holds; cbn [fst snd]; lia].
    + right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
  - destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
    split; [exact Es|]. split; [exact En|]. split; [exact Hc|]. split; [exact Hcap|].
    assert (Hin : 0 < cap -> In (kids, 56 * cap) D /\ In (keys, 8 * cap) D).
    { intros Hp. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. split; [left; reflexivity | right; left; reflexivity]. }
    assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
    exists Di. split; [exact ED|].
    apply (pj_mems_mono segs m lblk m' lblk (pj_node segs m lblk) (pj_node segs m' lblk)); [|exact Hi].
    intros i nm u x k D1 Hil Hu Hxk Hinc Hx Hcs HP.
    assert (Hp : 0 < cap) by lia.
    split; [|split].
    + apply (cn_u64 m m'); [exact Hx|]. intros y Hy. apply HM1. right. exists (keys, 8 * cap).
      split; [apply (proj2 (Hin Hp)) | unfold pj_holds; cbn [fst snd]; lia].
    + apply (cn_cstr_mframe m m'); [exact Hcs|].
      intros y Hy. apply HM1. right. exists (x, k).
      split; [apply HDi; exact Hxk | unfold pj_holds; cbn [fst snd]; exact Hy].
    + rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
      apply (IH m m' lblk _ D1 HP).
      intros y Hy. apply HM. destruct Hy as [Hy|(b & Hb & Hy)].
      * right. exists (kids, 56 * cap). split; [apply (proj1 (Hin Hp)) | unfold pj_holds; cbn [fst snd]; lia].
      * right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hy].
Qed.

End CrsNode.
