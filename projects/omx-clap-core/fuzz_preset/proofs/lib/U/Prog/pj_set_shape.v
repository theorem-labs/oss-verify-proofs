From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Frame.
Import ListNotations.
Open Scope Z_scope.

Lemma ps_set_hit : forall ms i nm u tv, nth_error ms i = Some (nm, u) ->
  (forall j nm' u', (j < i)%nat -> nth_error ms j = Some (nm', u') -> nm' <> nm) ->
  pj_set_model ms nm tv = firstn i ms ++ (nm, tv) :: skipn (S i) ms.
Proof.
  induction ms as [|[k v] r IH]; intros i nm u tv Hi Hl; [destruct i; discriminate|].
  destruct i as [|i]; cbn in Hi |- *.
  - injection Hi as -> ->. destruct (list_eq_dec Z.eq_dec nm nm) as [_|N]; [reflexivity | contradiction].
  - destruct (list_eq_dec Z.eq_dec k nm) as [E|N].
    + exfalso. apply (Hl 0%nat k v); [lia | reflexivity | exact E].
    + f_equal. apply (IH i nm u tv Hi). intros j nm' u' Hj Hn. apply (Hl (S j) nm' u'); [lia | exact Hn].
Qed.

Lemma ps_set_miss : forall ms nm tv, (forall nm' u, In (nm', u) ms -> nm' <> nm) ->
  pj_set_model ms nm tv = ms ++ [(nm, tv)].
Proof.
  induction ms as [|[k v] r IH]; intros nm tv H; cbn; [reflexivity|].
  destruct (list_eq_dec Z.eq_dec k nm) as [E|N].
  - exfalso. exact (H k v (or_introl eq_refl) E).
  - f_equal. apply IH. intros nm' u Hin. exact (H nm' u (or_intror Hin)).
Qed.

Lemma ps_depth_items : forall ms dd, (depth (JObj ms) <= S dd)%nat -> Forall (fun t => (depth t <= dd)%nat) (map snd ms).
Proof.
  intros ms dd H. cbn [depth] in H.
  assert (Hm : (list_max (map (fun '(_, v) => depth v) ms) <= dd)%nat) by lia.
  apply list_max_le in Hm. rewrite Forall_forall in Hm |- *. intros t Ht.
  apply in_map_iff in Ht as ([k v] & <- & Hin). cbn [snd].
  apply Hm. apply in_map_iff. exists (k, v). split; [reflexivity | exact Hin].
Qed.

Section S.
Variable segs : list Segment.

Lemma ps_slots_eq : forall kids keys cap,
  pis_slots true kids keys cap = (if cap =? 0 then [] else [(kids, 56 * cap); (keys, 8 * cap)]).
Proof.
  intros kids keys cap. unfold pis_slots, kids_blk, keys_blk, pis_oz. destruct (cap =? 0); reflexivity.
Qed.

Lemma ps_node_open : forall m lblk o ms D num str kids keys n cap,
  pj_node segs m lblk o (JObj ms) D -> pj_hdr segs m o 6 num str kids keys n cap -> cap <= 2 ^ 54 ->
  exists Di, D = pis_slots true kids keys cap ++ Di /\ str = 0 /\ n = Z.of_nat (length ms) /\
    pis_open segs m lblk o true num kids keys cap n (map snd ms) (map fst ms) Di.
Proof.
  intros m lblk o ms D num str kids keys n cap HN Hh Hc.
  cbn [pj_node tag] in HN.
  destruct HN as (HND & HA & num' & str' & kids' & keys' & n' & cap' & Hh' & Es & En & Hle & Hcap & Di & ED & Hm).
  pose proof Hh as (_ & _ & U1 & U2 & U3 & U4 & U5 & U6).
  pose proof Hh' as (_ & _ & V1 & V2 & V3 & V4 & V5 & V6).
  pose proof (pj_u64_uniq segs m _ _ _ U1 V1) as <-. pose proof (pj_u64_uniq segs m _ _ _ U2 V2) as <-.
  pose proof (pj_u64_uniq segs m _ _ _ U3 V3) as <-. pose proof (pj_u64_uniq segs m _ _ _ U4 V4) as <-.
  pose proof (pj_u64_uniq segs m _ _ _ U5 V5) as <-. pose proof (pj_u64_uniq segs m _ _ _ U6 V6) as <-.
  exists Di. rewrite ps_slots_eq. split; [exact ED|]. split; [exact Es|]. split; [exact En|].
  subst D str. unfold pis_open. rewrite ps_slots_eq.
  split; [exact HND|]. split; [exact HA|]. split; [exact Hh|].
  split.
  { split; [right; reflexivity|]. split; [lia|].
    split; [intros E0; destruct Hcap as [(_ & K0 & Y0)|(Cp & _)]; [split; [exact K0 | intros _; exact Y0] | lia]|].
    intros Cp. destruct Hcap as [(C0 & _)|(_ & L0 & L1)]; [lia|]. split; [exact L0 | intros _; exact L1]. }
  split; [intros E; discriminate|].
  cbn [pis_items]. split; [rewrite !length_map; reflexivity|]. rewrite pis_combine_map. exact Hm.
Qed.

Lemma ps_obj_node : forall m lblk o ms Di num kids keys n cap,
  pis_open segs m lblk o true num kids keys cap n (map snd ms) (map fst ms) Di -> n = Z.of_nat (length ms) ->
  pj_node segs m lblk o (JObj ms) (pis_slots true kids keys cap ++ Di).
Proof.
  intros m lblk o ms Di num kids keys n cap (HND & HA & Hh & Hs & _ & Hi) En.
  cbn [pis_items] in Hi. destruct Hi as (_ & Hm). rewrite pis_combine_map in Hm.
  destruct Hs as (_ & (Hn & Hc) & Hc0 & Hcp).
  cbn [pj_node tag]. split; [exact HND|]. split; [exact HA|].
  exists num, 0, kids, keys, n, cap. split; [exact Hh|].
  split; [reflexivity|]. split; [exact En|]. split; [lia|].
  split.
  { destruct (Z.eq_dec cap 0) as [E0|E0].
    - left. destruct (Hc0 E0) as (K0 & Y0). split; [exact E0|]. split; [exact K0 | exact (Y0 eq_refl)].
    - right. destruct (Hcp ltac:(lia)) as (L0 & L1). split; [lia|]. split; [exact L0 | exact (L1 eq_refl)]. }
  exists Di. split; [rewrite ps_slots_eq; reflexivity | exact Hm].
Qed.

Lemma ps_mems_split : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) ms a ka D i nm u,
  pj_mems segs m lblk P a ka ms D -> nth_error ms i = Some (nm, u) ->
  exists Dpre x k Du Dpost, D = Dpre ++ (x, k) :: Du ++ Dpost /\
    pj_mems segs m lblk P a ka (firstn i ms) Dpre /\
    pj_u64 segs m (ka + 8 * Z.of_nat i) x /\ pj_cstr segs m lblk x k nm /\ P (a + 56 * Z.of_nat i) u Du /\
    pj_mems segs m lblk P (a + 56 * Z.of_nat (S i)) (ka + 8 * Z.of_nat (S i)) (skipn (S i) ms) Dpost.
Proof.
  intros m lblk P ms. induction ms as [|[nm0 u0] r IH]; intros a ka D i nm u H Hi; [destruct i; discriminate|].
  cbn [pj_mems] in H. destruct H as (x & k & D1 & D2 & E & Hx & Hc & HP & HR).
  destruct i as [|i]; cbn in Hi.
  - injection Hi as <- <-. exists [], x, k, D1, D2.
    split; [subst D; reflexivity|]. split; [reflexivity|].
    replace (ka + 8 * Z.of_nat 0) with ka by lia. replace (a + 56 * Z.of_nat 0) with a by lia.
    split; [exact Hx|]. split; [exact Hc|]. split; [exact HP|].
    replace (a + 56 * Z.of_nat 1) with (a + 56) by lia. replace (ka + 8 * Z.of_nat 1) with (ka + 8) by lia.
    exact HR.
  - destruct (IH (a + 56) (ka + 8) D2 i nm u HR Hi) as (Dpre & x' & k' & Du & Dpost & E2 & H1 & H2 & H3 & H4 & H5).
    exists ((x, k) :: D1 ++ Dpre), x', k', Du, Dpost.
    split; [subst D D2; cbn [app]; rewrite <- app_assoc; reflexivity|].
    split; [cbn [firstn pj_mems]; exists x, k, D1, Dpre; split; [reflexivity|]; split; [exact Hx|];
            split; [exact Hc|]; split; [exact HP | exact H1]|].
    replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) by lia.
    replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia.
    split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
    replace (a + 56 * Z.of_nat (S (S i))) with (a + 56 + 56 * Z.of_nat (S i)) by lia.
    replace (ka + 8 * Z.of_nat (S (S i))) with (ka + 8 + 8 * Z.of_nat (S i)) by lia.
    cbn [skipn] in H5 |- *. exact H5.
Qed.

Lemma ps_mems_join : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) l1 l2 a ka Dpre x k Du Dpost nm u,
  pj_mems segs m lblk P a ka l1 Dpre ->
  pj_u64 segs m (ka + 8 * Z.of_nat (length l1)) x -> pj_cstr segs m lblk x k nm ->
  P (a + 56 * Z.of_nat (length l1)) u Du ->
  pj_mems segs m lblk P (a + 56 * Z.of_nat (S (length l1))) (ka + 8 * Z.of_nat (S (length l1))) l2 Dpost ->
  pj_mems segs m lblk P a ka (l1 ++ (nm, u) :: l2) (Dpre ++ (x, k) :: Du ++ Dpost).
Proof.
  intros m lblk P l1. induction l1 as [|[nm0 u0] r IH]; intros l2 a ka Dpre x k Du Dpost nm u H Hx Hc HP HR.
  - cbn [pj_mems] in H. subst Dpre. cbn [app length pj_mems] in *.
    replace (ka + 8 * Z.of_nat 0) with ka in Hx by lia. replace (a + 56 * Z.of_nat 0) with a in HP by lia.
    replace (a + 56 * Z.of_nat 1) with (a + 56) in HR by lia. replace (ka + 8 * Z.of_nat 1) with (ka + 8) in HR by lia.
    exists x, k, Du, Dpost. split; [reflexivity|]. split; [exact Hx|]. split; [exact Hc|]. split; [exact HP | exact HR].
  - cbn [pj_mems] in H. destruct H as (x0 & k0 & D1 & D2 & E & Hx0 & Hc0 & HP0 & HR0).
    cbn [app pj_mems]. exists x0, k0, D1, (D2 ++ (x, k) :: Du ++ Dpost).
    split; [subst Dpre; cbn [app]; rewrite <- app_assoc; reflexivity|].
    split; [exact Hx0|]. split; [exact Hc0|]. split; [exact HP0|].
    cbn [length] in Hx, HP, HR.
    apply (IH l2 (a + 56) (ka + 8) D2 x k Du Dpost nm u HR0).
    + replace (ka + 8 + 8 * Z.of_nat (length r)) with (ka + 8 * Z.of_nat (S (length r))) by lia. exact Hx.
    + exact Hc.
    + replace (a + 56 + 56 * Z.of_nat (length r)) with (a + 56 * Z.of_nat (S (length r))) by lia. exact HP.
    + replace (a + 56 + 56 * Z.of_nat (S (length r))) with (a + 56 * Z.of_nat (S (S (length r)))) by lia.
      replace (ka + 8 + 8 * Z.of_nat (S (length r))) with (ka + 8 * Z.of_nat (S (S (length r)))) by lia. exact HR.
Qed.

Lemma ps_mems_frame : forall m lblk m' lblk' l a ka D,
  pj_mems segs m lblk (pj_node segs m lblk) a ka l D ->
  (forall a' k', In (a', k') D -> lblk' a' k') ->
  (forall z, (a <= z < a + 56 * Z.of_nat (length l) \/ ka <= z < ka + 8 * Z.of_nat (length l) \/
              exists b, In b D /\ pj_holds b z) -> pis_same segs m m' z) ->
  pj_mems segs m' lblk' (pj_node segs m' lblk') a ka l D.
Proof.
  intros m lblk m' lblk' l a ka D H HL HM.
  rewrite <- (Z.add_0_r a), <- (Z.add_0_r ka).
  rewrite <- (Z.add_0_r a), <- (Z.add_0_r ka) in H.
  apply (pis_mems_shift segs m lblk m' lblk' (pj_node segs m lblk) (pj_node segs m' lblk') l (a + 0) (ka + 0)
           (a + 0) (ka + 0) D); [|exact H].
  intros i nm u x k D1 Hi Hu Hxk Hinc Hx Hc HP.
  split; [|split].
  - apply (pis_u64_frame segs m m'); [exact Hx|]. intros y Hy. apply HM. right. left. lia.
  - apply (pis_cstr_frame segs m lblk m' lblk'); [exact Hc | apply HL; exact Hxk|].
    intros y Hy. apply HM. right. right. exists (x, k). split; [exact Hxk | exact Hy].
  - apply (pis_node_frame segs u m lblk m' lblk' _ D1 HP).
    + intros a' k' Hb. apply HL. apply Hinc. exact Hb.
    + intros y Hy. apply HM. destruct Hy as [Hy|(b & Hb & Hy)].
      * left. lia.
      * right. right. exists b. split; [apply Hinc; exact Hb | exact Hy].
Qed.

End S.
