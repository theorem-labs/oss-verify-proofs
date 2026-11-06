From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import tx_put_c TxRet Ledger.
Import ListNotations.
Local Open Scope Z_scope.

Section PjM.
Variable segs : list Segment.

Lemma tt_mrd : forall (m : word -> option byte) y, Mem.mrd segs m (Mem.wa y) = mbyte segs m y.
Proof. reflexivity. Qed.

Lemma tt_bytes : forall m m' a bs, Mem.bytes_at segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte segs m' x = mbyte segs m x) ->
  Mem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs (Ha & Hl & H) E. split; [lia|]. split; [lia|].
  intros i Hi. specialize (H i Hi). rewrite tt_mrd in H |- *. rewrite E by lia. exact H.
Qed.

Lemma tt_rw : forall m m' p, pj_rw segs m p ->
  (forall x, p <= x < p + 56 -> mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x -> writable_at segs m' x)) ->
  pj_rw segs m' p.
Proof.
  intros m m' p (Hm & H1 & H2 & H) E. split; [exact Hm|]. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [W [b R]]. destruct (E a Ha) as [E1 E2]. split.
  - exact (E2 W).
  - exists b. rewrite tt_mrd in R |- *. rewrite E1. exact R.
Qed.

Lemma tt_u64 : forall m m' a v, pj_u64 segs m a v ->
  (forall x, a <= x < a + 8 -> mbyte segs m' x = mbyte segs m x) -> pj_u64 segs m' a v.
Proof.
  intros m m' a v (Hv & Hb) E. split; [exact Hv|]. apply (tt_bytes m m'); [exact Hb|].
  intros x Hx. apply E. rewrite Mem.length_le8 in Hx. lia.
Qed.

Lemma tt_hdr : forall m m' p ty num str kids keys n cap,
  pj_hdr segs m p ty num str kids keys n cap ->
  (forall x, p <= x < p + 56 -> mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x -> writable_at segs m' x)) ->
  pj_hdr segs m' p ty num str kids keys n cap.
Proof.
  intros m m' p ty num str kids keys n cap (Hrw & (T0 & T1) & (N0 & N1) & (S0 & S1) & (K0 & K1) & (Y0 & Y1) & (C0 & C1) & (P0 & P1)) E.
  assert (F : forall a bs, Mem.bytes_at segs m a bs -> p <= a -> a + Z.of_nat (length bs) <= p + 56 ->
    Mem.bytes_at segs m' a bs).
  { intros a bs Hb Hpa Hab. apply (tt_bytes m m'); [exact Hb|]. intros x Hx. apply E. lia. }
  split; [exact (tt_rw m m' p Hrw E)|].
  split; [split; [exact T0 | apply F; [exact T1 | lia | rewrite Mem.length_le4; lia]]|].
  split; [split; [exact N0 | apply F; [exact N1 | lia | rewrite Mem.length_le8; lia]]|].
  split; [split; [exact S0 | apply F; [exact S1 | lia | rewrite Mem.length_le8; lia]]|].
  split; [split; [exact K0 | apply F; [exact K1 | lia | rewrite Mem.length_le8; lia]]|].
  split; [split; [exact Y0 | apply F; [exact Y1 | lia | rewrite Mem.length_le8; lia]]|].
  split; [split; [exact C0 | apply F; [exact C1 | lia | rewrite Mem.length_le8; lia]]|].
  split; [exact P0 | apply F; [exact P1 | lia | rewrite Mem.length_le8; lia]].
Qed.

Lemma pj_cstr_mframe : forall m m' lb a k s, pj_cstr segs m lb a k s ->
  (forall x, a <= x < a + k -> mbyte segs m' x = mbyte segs m x) -> pj_cstr segs m' lb a k s.
Proof.
  intros m m' lb a k s (Hl & Hk & Hf & Hb) E.
  split; [exact Hl|]. split; [exact Hk|]. split; [exact Hf|].
  apply (tt_bytes m m'); [exact Hb|]. intros x Hx. apply E.
  rewrite length_map, length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma pj_node_mframe : forall m m' lb p t D, pj_node segs m lb p t D ->
  (forall x, pj_foot p D x -> mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x -> writable_at segs m' x)) ->
  pj_node segs m' lb p t D.
Proof.
  intros m m' lb p t. revert m m' lb p.
  induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
    intros m m' lblk p D H HM; cbn [pj_node] in H |- *;
    assert (HM1 : forall x, pj_foot p D x -> mbyte segs m' x = mbyte segs m x) by (intros x Hx; exact (proj1 (HM x Hx)));
    destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
    (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap;
    (split; [apply (tt_hdr m m'); [exact Hh | intros x Hx; apply HM; left; exact Hx]|]).
  - exact Hb.
  - exact Hb.
  - exact Hb.
  - destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    exists k. split; [|exact ED].
    apply (pj_cstr_mframe m m'); [exact Hc|].
    intros x Hx. apply HM1. right. exists (str, k).
    split; [subst D; left; reflexivity | unfold pj_holds; cbn [fst snd]; exact Hx].
  - destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
    split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    exists k. split; [|exact ED].
    apply (pj_cstr_mframe m m'); [exact Hc|].
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
    + apply (tt_u64 m m'); [exact Hx|]. intros y Hy. apply HM1. right. exists (keys, 8 * cap).
      split; [apply (proj2 (Hin Hp)) | unfold pj_holds; cbn [fst snd]; lia].
    + apply (pj_cstr_mframe m m'); [exact Hcs|].
      intros y Hy. apply HM1. right. exists (x, k).
      split; [apply HDi; exact Hxk | unfold pj_holds; cbn [fst snd]; exact Hy].
    + rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
      apply (IH m m' lblk _ D1 HP).
      intros y Hy. apply HM. destruct Hy as [Hy|(b & Hb & Hy)].
      * right. exists (kids, 56 * cap). split; [apply (proj1 (Hin Hp)) | unfold pj_holds; cbn [fst snd]; lia].
      * right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hy].
Qed.

End PjM.

Section K.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.
Hypothesis ERRB : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GST : forall a, alloc_statics a -> in_img B a /\ ~ (errno_addr B <= a < errno_addr B + 4) /\
  forall L A mem md, aa_MR API L A mem md -> ~ owned B L A a.

Lemma tt_statics_low : forall a, alloc_statics a -> a < alloc_ceiling.
Proof.
  intros a H. pose proof alloc_ceiling_value.
  unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in H. lia.
Qed.

Lemma tt_blk : forall L A mem md a k, aa_MR API L A mem md -> In (a, k) (blocks L A) ->
  4096 <= a /\ a + k <= alloc_ceiling.
Proof.
  intros L A mem md a k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin.
  destruct Hin as ([q n] & E & Hq). cbn [fst snd] in E. injection E as E1 E2. subst a k.
  exact (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n HM Hq).
Qed.

Lemma tt_present : forall L A mem md a k i, aa_MR API L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  present mem (a + i).
Proof.
  intros L A mem md a k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin.
  destruct Hin as ([q n] & E & Hq). cbn [fst snd] in E. injection E as E1 E2. subst a k.
  exact (proj1 (mr_blocks _ _ (aa_laws API) _ _ _ _ q n i HM Hq Hi)).
Qed.

Lemma tt_inv_range : forall L A mem md b len cap txt x, aa_MR API L A mem md -> tx_inv B L A mem b len cap txt ->
  b <= x < b + cap -> x < alloc_ceiling /\ ~ in_img B x.
Proof.
  intros L A mem md b len cap txt x HM (_ & [(E1 & E2 & E3)|(Hc & Hin & _ & _ & HI)]) Hx; [lia|].
  destruct (tt_blk L A mem md b cap HM Hin) as [_ Hb]. split; [lia|].
  replace x with (b + (x - b)) by lia. apply HI. lia.
Qed.

Lemma tx_rel_lam : forall stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j Lam peak cnt fail,
  tx_relx B API F stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j ->
  ledger B L A mem Lam peak cnt fail -> (forall a n, In (a, n) Lam -> a - 16 <> b0) ->
  (forall a n, In (a, n) Lam -> In (a - 16, n + 16) (blocks L' A') /\ a - 16 <> b1) /\
  (forall a n i, In (a, n) Lam -> -16 <= i < n ->
     mbyte segs mem' (a + i) = mbyte segs mem (a + i) /\ writable_at segs mem' (a + i)).
Proof.
  intros stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j Lam peak cnt fail
    (HF & _ & HK & HP & HP2 & _) HL HN.
  destruct HF as (HM' & _).
  destruct HL as (_ & _ & _ & _ & _ & HB). rewrite Forall_forall in HB.
  assert (HQ : forall a n, In (a, n) Lam -> In (a - 16, n + 16) (blocks L' A') /\ a - 16 <> b1).
  { intros a n Han. destruct (HB _ Han) as (Hn & Hin & _ & _). cbn [fst snd] in Hn, Hin.
    split; [apply HP; [exact Hin | intros E; injection E as E1 _; exact (HN a n Han E1)]|].
    apply (HP2 _ _ Hin); [lia | exact (HN a n Han)]. }
  split; [exact HQ|].
  intros a n i Han Hi. destruct (HB _ Han) as (Hn & Hin & _ & _). cbn [fst snd] in Hn, Hin.
  replace (a + i) with (a - 16 + (i + 16)) by lia. split.
  - apply (HK (a - 16) (n + 16)); [exact Hin | exact (HN a n Han) | lia].
  - apply (present_writable B).
    apply (tt_present L' A' mem' md' (a - 16) (n + 16)); [exact HM' | exact (proj1 (HQ a n Han)) | lia].
Qed.

Lemma tx_rel_ledger : forall stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j Lam peak cnt fail,
  tx_relx B API F stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j ->
  aa_MR API L A mem md -> 0 <= stk -> alloc_ceiling + stk <= spZ regs -> spZ regs <= t ->
  tx_inv B L A mem b0 len0 cap0 txt ->
  ledger B L A mem Lam peak cnt fail -> (forall a n, In (a, n) Lam -> a - 16 <> b0) ->
  ledger B L' A' mem' Lam peak cnt fail /\ (forall a n, In (a, n) Lam -> a - 16 <> b1) /\
  (forall a n i, In (a, n) Lam -> -16 <= i < n ->
     mbyte segs mem' (a + i) = mbyte segs mem (a + i) /\ writable_at segs mem' (a + i)).
Proof.
  intros stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j Lam peak cnt fail
    HR HM Hs Hsp Ht Hinv HL HN.
  destruct (tx_rel_lam stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j Lam peak cnt fail
    HR HL HN) as (HQ & HX).
  destruct HR as (HF & _ & HK & _ & _ & _ & _ & Hinv' & _).
  destruct HF as (HM' & _ & _ & _ & _ & _ & HI & _).
  split; [|split; [intros a n Han; exact (proj2 (HQ a n Han)) | exact HX]].
  assert (HS : forall a, alloc_statics a -> mbyte segs mem' a = mbyte segs mem a).
  { intros a Ha. destruct (GST a Ha) as (Hi & He & Ho). pose proof (tt_statics_low a Ha) as Hlo.
    eapply proj1. apply (HI a); [right; exact Hi | exact (Ho _ _ _ _ HM) | exact (Ho _ _ _ _ HM') | |].
    - intros [Hw|Hw]; [lia | exact (He Hw)].
    - intros [Hw|[Hw|Hw]]; [lia | |].
      + exact (proj2 (tt_inv_range L A mem md b0 len0 cap0 txt a HM Hinv Hw) Hi).
      + exact (proj2 (tt_inv_range L' A' mem' md' b1 _ cap1 _ a HM' Hinv' Hw) Hi). }
  assert (WM : forall g v, (forall k, 0 <= k < 8 -> alloc_statics (g + k)) ->
    word_mem segs mem g v -> word_mem segs mem' g v).
  { intros g v Hg Hw k Hk. rewrite HS by (apply Hg; lia). exact (Hw k Hk). }
  destruct HL as ((W1 & W2 & W3 & W4) & Hpk & Hc & Hf & HD & HB). rewrite Forall_forall in HB.
  split; [|split; [exact Hpk|split; [exact Hc|split; [exact Hf|split; [exact HD|]]]]].
  - split; [apply WM; [intros k Hk; unfold alloc_statics; left; lia | exact W1]|].
    split; [apply WM; [intros k Hk; unfold alloc_statics; right; left; lia | exact W2]|].
    split; [apply WM; [intros k Hk; unfold alloc_statics; right; right; left; lia | exact W3]|].
    apply WM; [intros k Hk; unfold alloc_statics; right; right; right; lia | exact W4].
  - rewrite Forall_forall. intros [a n] Han. cbn [fst snd].
    destruct (HB _ Han) as (Hn & Hin & Hw & Hi). cbn [fst snd] in Hn, Hin, Hw, Hi.
    split; [exact Hn|]. split; [exact (proj1 (HQ a n Han))|]. split; [|exact Hi].
    intros k Hk. rewrite (HK (a - 16) (n + 16) (Z.of_nat k) Hin (HN a n Han) ltac:(lia)). exact (Hw k Hk).
Qed.

Lemma tx_rel_node : forall stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j Lam peak cnt fail
    v tv D,
  tx_relx B API F stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j ->
  aa_MR API L A mem md -> 0 <= stk -> alloc_ceiling + stk <= spZ regs ->
  tx_inv B L A mem b0 len0 cap0 txt ->
  ledger B L A mem Lam peak cnt fail -> (forall a n, In (a, n) Lam -> a - 16 <> b0) ->
  pj_node segs mem (fun a n => In (a, n) Lam) v tv D -> (forall b, In b D -> In b Lam) ->
  (spZ regs <= v \/ exists a n, In (a, n) Lam /\ a <= v /\ v + 56 <= a + n) ->
  v + 56 <= 2 ^ 64 -> (v + 56 <= t \/ t + 24 <= v) ->
  pj_node segs mem' (fun a n => In (a, n) Lam) v tv D /\
  forall x, pj_foot v D x -> mbyte segs mem' x = mbyte segs mem x.
Proof.
  intros stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j Lam peak cnt fail v tv D
    HR HM Hs Hsp Hinv HL HN Hn HD Hv Hv64 Hvt.
  destruct (tx_rel_lam stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j Lam peak cnt fail
    HR HL HN) as (_ & HX).
  destruct HR as (HF & _ & _ & _ & _ & _ & _ & Hinv' & _).
  destruct HF as (HM' & _ & _ & _ & _ & _ & HI & _).
  assert (HB : forall x, pj_foot v D x ->
    mbyte segs mem' x = mbyte segs mem x /\ (writable_at segs mem x -> writable_at segs mem' x)).
  { intros x [Hx|([a n] & Hb & Hx)].
    - destruct Hv as [Hv|(a & n & Han & Ha & Han')].
      + pose proof alloc_ceiling_value.
        assert (G : mbyte segs mem' x = mbyte segs mem x /\ (writable_at segs mem x <-> writable_at segs mem' x)).
        { apply HI.
          - left. lia.
          - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ x HM Ho). lia.
          - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ x HM' Ho). lia.
          - intros [Hw|Hw]; lia.
          - intros [Hw|[Hw|Hw]]; [lia | |].
            + pose proof (tt_inv_range L A mem md b0 len0 cap0 txt x HM Hinv Hw). lia.
            + pose proof (tt_inv_range L' A' mem' md' b1 _ cap1 _ x HM' Hinv' Hw). lia. }
        destruct G as [G1 G2]. split; [exact G1 | intros W; exact (proj1 G2 W)].
      + destruct (HX a n (x - a) Han ltac:(lia)) as [E1 E2]. replace (a + (x - a)) with x in E1, E2 by lia.
        split; [exact E1 | intros _; exact E2].
    - unfold pj_holds in Hx. cbn [fst snd] in Hx.
      destruct (HX a n (x - a) (HD _ Hb) ltac:(lia)) as [E1 E2].
      replace (a + (x - a)) with x in E1, E2 by lia. split; [exact E1 | intros _; exact E2]. }
  split; [apply (pj_node_mframe segs mem mem'); [exact Hn | exact HB] | intros x Hx; exact (proj1 (HB x Hx))].
Qed.

Lemma tx_rel_cstr : forall stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j Lam peak cnt fail
    s k bs,
  tx_relx B API F stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j ->
  ledger B L A mem Lam peak cnt fail -> (forall a n, In (a, n) Lam -> a - 16 <> b0) ->
  pj_cstr segs mem (fun a n => In (a, n) Lam) s k bs ->
  pj_cstr segs mem' (fun a n => In (a, n) Lam) s k bs /\
  forall x, s <= x < s + k -> mbyte segs mem' x = mbyte segs mem x.
Proof.
  intros stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j Lam peak cnt fail s k bs
    HR HL HN Hc.
  destruct (tx_rel_lam stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j Lam peak cnt fail
    HR HL HN) as (_ & HX).
  assert (HB : forall x, s <= x < s + k -> mbyte segs mem' x = mbyte segs mem x).
  { intros x Hx. destruct Hc as (Hin & _). destruct (HX s k (x - s) Hin ltac:(lia)) as [E _].
    replace (s + (x - s)) with x in E by lia. exact E. }
  split; [apply (pj_cstr_mframe segs mem mem'); [exact Hc | exact HB] | exact HB].
Qed.

End K.
