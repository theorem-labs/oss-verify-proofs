From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import write_value_blocks.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct.
Import ListNotations.
Open Scope Z_scope.

Section WriterNode.
Variable segs : list Segment.

Lemma wnd_bytes : forall m m' a bs, bytes_at segs m a bs ->
  (forall x, 0 <= x < 2 ^ 64 -> a <= x < a + Z.of_nat (length bs) -> mrd segs m' (wa x) = mrd segs m (wa x)) ->
  bytes_at segs m' a bs.
Proof.
  intros m m' a bs (Ha & Hl & H) E. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite (E (a + Z.of_nat i) ltac:(lia) ltac:(lia)). exact (H i Hi).
Qed.

Lemma wnd_stk : forall m m' lo hi, stk segs m lo hi ->
  (forall x, 0 <= x < 2 ^ 64 -> lo <= x < hi -> mrd segs m' (wa x) = mrd segs m (wa x)) ->
  (forall x, 0 <= x < 2 ^ 64 -> lo <= x < hi -> wview segs m (wa x) <> None -> wview segs m' (wa x) <> None) ->
  stk segs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) E W. split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Wa & b & Hb). split.
  - exact (W a ltac:(lia) Ha Wa).
  - exists b. rewrite (E a ltac:(lia) Ha). exact Hb.
Qed.

Lemma wnd_u64 : forall m m' a v, pj_u64 segs m a v ->
  (forall x, 0 <= x < 2 ^ 64 -> a <= x < a + 8 -> mrd segs m' (wa x) = mrd segs m (wa x)) ->
  pj_u64 segs m' a v.
Proof.
  intros m m' a v (Hv & B) E. split; [exact Hv|]. apply (wnd_bytes m m'); [exact B|].
  intros x Hx0 Hx. apply E; [exact Hx0|]. rewrite length_le8 in Hx. lia.
Qed.

Lemma wnd_hdr : forall m m' p ty num str kids keys n cap,
  pj_hdr segs m p ty num str kids keys n cap ->
  (forall x, 0 <= x < 2 ^ 64 -> p <= x < p + 56 -> mrd segs m' (wa x) = mrd segs m (wa x)) ->
  (forall x, 0 <= x < 2 ^ 64 -> p <= x < p + 56 -> wview segs m (wa x) <> None -> wview segs m' (wa x) <> None) ->
  pj_hdr segs m' p ty num str kids keys n cap.
Proof.
  intros m m' p ty num str kids keys n cap
    ((Ha & Hs) & (T0 & T1) & (N0 & N1) & (S0 & S1) & (K0 & K1) & (Y0 & Y1) & (C0 & C1) & (P0 & P1)) E W.
  assert (F : forall a bs, bytes_at segs m a bs -> p <= a -> a + Z.of_nat (length bs) <= p + 56 ->
    bytes_at segs m' a bs).
  { intros a bs B Hpa Hab. apply (wnd_bytes m m'); [exact B|]. intros x Hx0 Hx. apply E; [exact Hx0 | lia]. }
  split; [split; [exact Ha | exact (wnd_stk m m' p (p + 56) Hs E W)]|].
  split; [split; [exact T0 | apply F; [exact T1 | lia | rewrite length_le4; lia]]|].
  split; [split; [exact N0 | apply F; [exact N1 | lia | rewrite length_le8; lia]]|].
  split; [split; [exact S0 | apply F; [exact S1 | lia | rewrite length_le8; lia]]|].
  split; [split; [exact K0 | apply F; [exact K1 | lia | rewrite length_le8; lia]]|].
  split; [split; [exact Y0 | apply F; [exact Y1 | lia | rewrite length_le8; lia]]|].
  split; [split; [exact C0 | apply F; [exact C1 | lia | rewrite length_le8; lia]]|].
  split; [exact P0 | apply F; [exact P1 | lia | rewrite length_le8; lia]].
Qed.

Lemma wnd_cstr : forall m lblk m' lblk' a k s,
  pj_cstr segs m lblk a k s -> lblk' a k ->
  (forall x, 0 <= x < 2 ^ 64 -> pj_holds (a, k) x -> mrd segs m' (wa x) = mrd segs m (wa x)) ->
  pj_cstr segs m' lblk' a k s.
Proof.
  intros m lblk m' lblk' a k s (Hl & Hk & Hf & Hb) Hl' E.
  split; [exact Hl'|]. split; [exact Hk|]. split; [exact Hf|].
  apply (wnd_bytes m m'); [exact Hb|]. intros x Hx0 Hx. apply E; [exact Hx0|].
  unfold pj_holds; cbn [fst snd]. rewrite length_map, length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma pj_node_mrd : forall t m lblk m' lblk' p D,
  pj_node segs m lblk p t D ->
  (forall a k, In (a, k) D -> lblk' a k) ->
  (forall x, 0 <= x < 2 ^ 64 -> pj_foot p D x -> mrd segs m' (wa x) = mrd segs m (wa x)) ->
  (forall x, 0 <= x < 2 ^ 64 -> pj_foot p D x -> wview segs m (wa x) <> None -> wview segs m' (wa x) <> None) ->
  pj_node segs m' lblk' p t D.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
    intros m lblk m' lblk' p D H HL HM HW; cbn [pj_node] in H |- *;
    destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
    (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap;
    (split; [apply (wnd_hdr m m'); [exact Hh | intros x Hx0 Hx; apply HM; [exact Hx0 | left; exact Hx]
                                  | intros x Hx0 Hx Hw; apply HW; [exact Hx0 | left; exact Hx | exact Hw]]|]).
  - exact Hb.
  - exact Hb.
  - exact Hb.
  - destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    exists k. split; [|exact ED].
    apply (wnd_cstr m lblk m' lblk'); [exact Hc | apply HL; subst D; left; reflexivity |].
    intros x Hx0 Hx. apply HM; [exact Hx0|]. right. exists (str, k). split; [subst D; left; reflexivity | exact Hx].
  - destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
    split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    exists k. split; [|exact ED].
    apply (wnd_cstr m lblk m' lblk'); [exact Hc | apply HL; subst D; left; reflexivity |].
    intros x Hx0 Hx. apply HM; [exact Hx0|]. right. exists (str, k). split; [subst D; left; reflexivity | exact Hx].
  - destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
    split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
    assert (Hin : 0 < cap -> In (kids, 56 * cap) D).
    { intros Hp. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
    assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
    split; [destruct Hcap as [Hcap|(Hp & L0)]; [left; exact Hcap | right; split; [exact Hp | apply HL; apply (Hin Hp)]]|].
    exists Di. split; [exact ED|].
    apply (pj_items_mono (pj_node segs m lblk) (pj_node segs m' lblk')); [|exact Hi].
    intros i u D1 Hil Hu Hinc HP.
    assert (Hp : 0 < cap) by lia.
    assert (Hfoot : forall x, pj_foot (kids + 56 * Z.of_nat i) D1 x -> pj_foot p D x).
    { intros x [Hx|(b & Hb & Hx)].
      - right. exists (kids, 56 * cap). split; [apply (Hin Hp) | unfold pj_holds; cbn [fst snd]; lia].
      - right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx]. }
    rewrite Forall_forall in IH.
    apply (IH u Hu m lblk m' lblk' _ D1 HP).
    + intros a k Hak. apply HL. apply HDi. apply Hinc. exact Hak.
    + intros x Hx0 Hx. apply HM; [exact Hx0 | apply Hfoot; exact Hx].
    + intros x Hx0 Hx Hw. apply HW; [exact Hx0 | apply Hfoot; exact Hx | exact Hw].
  - destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
    split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
    assert (Hin : 0 < cap -> In (kids, 56 * cap) D /\ In (keys, 8 * cap) D).
    { intros Hp. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. split; [left; reflexivity | right; left; reflexivity]. }
    assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
    split; [destruct Hcap as [Hcap|(Hp & L0 & L1)];
            [left; exact Hcap | right; split; [exact Hp|]; split; [apply HL; apply (proj1 (Hin Hp)) | apply HL; apply (proj2 (Hin Hp))]]|].
    exists Di. split; [exact ED|].
    apply (pj_mems_mono segs m lblk m' lblk' (pj_node segs m lblk) (pj_node segs m' lblk')); [|exact Hi].
    intros i nm u x k D1 Hil Hu Hxk Hinc Hx Hcs HP.
    assert (Hp : 0 < cap) by lia.
    split; [|split].
    + apply (wnd_u64 m m'); [exact Hx|]. intros y Hy0 Hy. apply HM; [exact Hy0|]. right. exists (keys, 8 * cap).
      split; [apply (proj2 (Hin Hp)) | unfold pj_holds; cbn [fst snd]; lia].
    + apply (wnd_cstr m lblk m' lblk'); [exact Hcs | apply HL; apply HDi; exact Hxk |].
      intros y Hy0 Hy. apply HM; [exact Hy0|]. right. exists (x, k). split; [apply HDi; exact Hxk | exact Hy].
    + assert (Hfoot : forall y, pj_foot (kids + 56 * Z.of_nat i) D1 y -> pj_foot p D y).
      { intros y [Hy|(b & Hb & Hy)].
        - right. exists (kids, 56 * cap). split; [apply (proj1 (Hin Hp)) | unfold pj_holds; cbn [fst snd]; lia].
        - right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hy]. }
      rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
      apply (IH m lblk m' lblk' _ D1 HP).
      * intros a k' Hak. apply HL. apply HDi. apply Hinc. exact Hak.
      * intros y Hy0 Hy. apply HM; [exact Hy0 | apply Hfoot; exact Hy].
      * intros y Hy0 Hy Hw. apply HW; [exact Hy0 | apply Hfoot; exact Hy | exact Hw].
Qed.

Lemma pj_mems_nth : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) l a ka D i,
  pj_mems segs m lblk P a ka l D -> (i < length l)%nat ->
  exists x k Di, In (x, k) D /\ (forall b, In b Di -> In b D) /\ pj_u64 segs m (ka + 8 * Z.of_nat i) x /\
    pj_cstr segs m lblk x k (fst (nth i l ([], JNull))) /\ P (a + 56 * Z.of_nat i) (snd (nth i l ([], JNull))) Di.
Proof.
  intros m lblk P l. induction l as [|[nm u] r IH]; intros a ka D i H Hi; cbn [length] in Hi; [lia|].
  cbn [pj_mems] in H. destruct H as (x & k & D1 & D2 & E & Hx & Hc & HP & HR).
  destruct i as [|i].
  - exists x, k, D1. split; [subst D; left; reflexivity|].
    split; [intros b Hb; subst D; right; apply in_or_app; left; exact Hb|].
    replace (ka + 8 * Z.of_nat 0) with ka by lia. replace (a + 56 * Z.of_nat 0) with a by lia.
    split; [exact Hx|]. split; [exact Hc | exact HP].
  - destruct (IH (a + 56) (ka + 8) D2 i HR ltac:(lia)) as (x' & k' & Di & Hxk & HDi & Hx' & Hc' & HP').
    exists x', k', Di. split; [subst D; right; apply in_or_app; right; exact Hxk|].
    split; [intros b Hb; subst D; right; apply in_or_app; right; apply HDi; exact Hb|].
    replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) by lia.
    replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia.
    split; [exact Hx'|]. split; [exact Hc' | exact HP'].
Qed.

End WriterNode.

Lemma pj_items_nth : forall (P : Z -> jv -> list (Z * Z) -> Prop) l a D i,
  pj_items P a l D -> (i < length l)%nat ->
  exists Di, (forall b, In b Di -> In b D) /\ P (a + 56 * Z.of_nat i) (nth i l JNull) Di.
Proof.
  intros P l. induction l as [|u r IH]; intros a D i H Hi; cbn [length] in Hi; [lia|].
  cbn [pj_items] in H. destruct H as (D1 & D2 & E & HP & HR).
  destruct i as [|i].
  - exists D1. split; [intros b Hb; subst D; apply in_or_app; left; exact Hb|].
    replace (a + 56 * Z.of_nat 0) with a by lia. exact HP.
  - destruct (IH (a + 56) D2 i HR ltac:(lia)) as (Di & HDi & HPi).
    exists Di. split; [intros b Hb; subst D; apply in_or_app; right; apply HDi; exact Hb|].
    replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia. exact HPi.
Qed.

Lemma wnd_app : forall m a b bs1 bs2, bytes_at rsegs m a bs1 -> b = a + Z.of_nat (length bs1) ->
  bytes_at rsegs m b bs2 -> bytes_at rsegs m a (bs1 ++ bs2).
Proof. intros m a b bs1 bs2 H1 -> H2. apply (proj2 (bytes_at_app rsegs m a bs1 bs2)). split; [exact H1 | exact H2]. Qed.

Lemma pj_hdr_wv_node : forall m p ty num str kids keys n cap,
  pj_hdr rsegs m p ty num str kids keys n cap -> exists pa pb, wv_node m p ty str kids keys n pa pb.
Proof.
  intros m p ty num str kids keys n cap
    ((Ha & Hs) & (T0 & T1) & (N0 & N1) & (S0 & S1) & (K0 & K1) & (Y0 & Y1) & (C0 & C1) & (P0 & P1)).
  pose proof Hs as (H1 & H2 & HS).
  assert (Hs4 : stk rsegs m (p + 4) (p + 8)).
  { split; [lia|]. split; [lia|]. intros a Ha'. apply HS. lia. }
  destruct (stk_bytes rsegs m (p + 4) (p + 8) Hs4 ltac:(lia)) as (bs & Hbl & Hb).
  assert (Hl4 : length bs = 4%nat) by (rewrite Hbl; replace (p + 8 - (p + 4)) with 4 by lia; reflexivity).
  exists (bs ++ le8 (Z_to_bv 64 num)), (le8 (Z_to_bv 64 cap)).
  unfold wv_node. split; [split|].
  - cbn [cells_wf cell_wf]. rewrite length_app, Hl4, !length_le8. repeat split.
  - cbn [cells_bytes cbytes].
    apply (wnd_app m p (p + 4)); [exact T1 | rewrite length_le4; lia |].
    apply (wnd_app m (p + 4) (p + 16));
      [apply (wnd_app m (p + 4) (p + 8)); [exact Hb | rewrite Hl4; lia | exact N1]
      | rewrite length_app, Hl4, length_le8; lia |].
    apply (wnd_app m (p + 16) (p + 24)); [exact S1 | rewrite length_le8; lia |].
    apply (wnd_app m (p + 24) (p + 32)); [exact K1 | rewrite length_le8; lia |].
    apply (wnd_app m (p + 32) (p + 40)); [exact Y1 | rewrite length_le8; lia |].
    apply (wnd_app m (p + 40) (p + 48)); [exact C1 | rewrite length_le8; lia |].
    rewrite app_nil_r. exact P1.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|].
    intros i Hi. exact (proj1 (HS (p + i) ltac:(lia))).
Qed.
