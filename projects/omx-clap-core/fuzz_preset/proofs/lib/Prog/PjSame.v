From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
Import ListNotations.
Open Scope Z_scope.

Definition slots (t : jv) : list (option (list Z) * jv) :=
  match t with
  | JArr l => map (fun u => (None, u)) l
  | JObj l => map (fun nu => (Some (fst nu), snd nu)) l
  | _ => []
  end.

Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite bv_swrap_small; [reflexivity|].
  change (bv_half_modulus 32) with (2^31). lia.
Qed.

Lemma tag_range : forall t, 0 <= tag t <= 6.
Proof. destruct t; cbn; lia. Qed.

Lemma bv_eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma bv_eqb_true : forall x y : word, bv_eqb x y = true -> x = y.
Proof. intros x y H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma bv_eqb_false : forall x y : word, bv_eqb x y = false -> x <> y.
Proof. intros x y H E. subst y. unfold bv_eqb in H. rewrite Z.eqb_refl in H. discriminate. Qed.

Lemma tag_cases : forall t, tag t = 0 \/ tag t = 1 \/ tag t = 2 \/ tag t = 3 \/ tag t = 4 \/ tag t = 5 \/ tag t = 6.
Proof. destruct t; cbn; tauto. Qed.

Lemma scalar_eq : forall ta tb, tag ta = tag tb -> tag ta <= 2 -> ta = tb.
Proof. intros ta tb E H. destruct ta, tb; cbn in E, H; try lia; reflexivity. Qed.

Lemma tag_num : forall t, tag t = 3 -> exists txt bits, t = JNum txt bits.
Proof. intros t H. destruct t; cbn in H; try lia. eexists _, _. reflexivity. Qed.

Lemma tag_str : forall t, tag t = 4 -> exists s, t = JStr s.
Proof. intros t H. destruct t; cbn in H; try lia. eexists. reflexivity. Qed.

Lemma slots_eq : forall ta tb, tag ta = tag tb -> (tag ta = 5 \/ tag ta = 6) -> slots ta = slots tb -> ta = tb.
Proof.
  intros ta tb Et Ht Es.
  destruct ta as [| | | ? ? | ? | la | ma]; destruct tb as [| | | ? ? | ? | lb | mb]; cbn [tag] in Et, Ht; try lia;
    cbn [slots] in Es; f_equal.
  - revert lb Es. induction la as [|x la IH]; intros [|y lb] Es; cbn in Es; try discriminate; [reflexivity|].
    injection Es as E1 E2. subst y. f_equal. apply IH. exact E2.
  - revert mb Es. induction ma as [|x ma IH]; intros [|y mb] Es; cbn in Es; try discriminate; [reflexivity|].
    injection Es as E1 E2 E3. f_equal; [destruct x, y; cbn in *; subst; reflexivity|]. apply IH. exact E3.
Qed.

Lemma slot_depth : forall t i o u, nth_error (slots t) i = Some (o, u) -> (depth u < depth t)%nat.
Proof.
  intros t i o u E. apply nth_error_In in E.
  destruct t as [| | | | | items | members]; cbn [slots] in E; try contradiction.
  - apply in_map_iff in E. destruct E as (v & Ev & Hv). injection Ev as E1 E2. subst v. apply depth_item. exact Hv.
  - apply in_map_iff in E. destruct E as ([nm v] & Ev & Hv). cbn in Ev. injection Ev as E1 E2. subst v.
    apply (depth_member members nm). exact Hv.
Qed.

Lemma slot_kind : forall t i o u, nth_error (slots t) i = Some (o, u) ->
  (tag t = 6 -> exists nm, o = Some nm) /\ (tag t = 5 -> o = None).
Proof.
  intros t i o u E.
  destruct t as [| | | | | items | members]; cbn [slots tag] in *; try (destruct i; discriminate);
    rewrite nth_error_map in E.
  - destruct (nth_error items i); cbn in E; [|discriminate]. injection E as E1 E2. subst o.
    split; [lia | reflexivity].
  - destruct (nth_error members i) as [[nm v]|]; cbn in E; [|discriminate]. injection E as E1 E2. subst o.
    split; [eexists; reflexivity | lia].
Qed.

Lemma items_in : forall (P : Z -> jv -> list (Z * Z) -> Prop) (Q : Z * Z -> Prop) l a D,
  (forall a' u D1, In u l -> P a' u D1 -> forall b, In b D1 -> Q b) ->
  pj_items P a l D -> forall b, In b D -> Q b.
Proof.
  intros P Q l. induction l as [|u r IH]; intros a D H Hl b Hb; cbn [pj_items] in Hl.
  - subst D. destruct Hb.
  - destruct Hl as (D1 & D2 & ED & HP & HR). subst D. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
    + exact (H a u D1 (or_introl eq_refl) HP b Hb).
    + apply (IH (a + 56) D2); [|exact HR|exact Hb]. intros a' v D3 Hv HP3. exact (H a' v D3 (or_intror Hv) HP3).
Qed.

Lemma items_nth : forall (P : Z -> jv -> list (Z * Z) -> Prop) l a D i u,
  pj_items P a l D -> nth_error l i = Some u ->
  exists D1, incl D1 D /\ P (a + 56 * Z.of_nat i) u D1.
Proof.
  intros P l. induction l as [|v r IH]; intros a D i u H E; [destruct i; discriminate|].
  cbn [pj_items] in H. destruct H as (D1 & D2 & ED & HP & HR).
  destruct i as [|i]; cbn in E.
  - injection E as E. subst u. exists D1. split; [subst D; intros b Hb; apply in_or_app; left; exact Hb|].
    replace (a + 56 * Z.of_nat 0) with a by lia. exact HP.
  - destruct (IH (a + 56) D2 i u HR E) as (D3 & Hinc & HP3). exists D3. split.
    + subst D; intros b Hb; apply in_or_app; right; apply Hinc; exact Hb.
    + replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia. exact HP3.
Qed.

Lemma firstn_snoc_eq : forall (A : Type) (l l' : list A) i x, nth_error l i = Some x -> nth_error l' i = Some x ->
  firstn i l = firstn i l' -> firstn (S i) l = firstn (S i) l'.
Proof.
  intros A l. induction l as [|y l IH]; intros l' i x E E' F; [destruct i; discriminate|].
  destruct l' as [|y' l']; [destruct i; discriminate|].
  destruct i as [|i]; cbn in E, E', F |- *.
  - injection E as E. injection E' as E'. subst. reflexivity.
  - injection F as F1 F2. subst y'. f_equal. apply (IH l' i x E E' F2).
Qed.

Lemma le8_inj : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> le8 (Z_to_bv 64 x) = le8 (Z_to_bv 64 y) -> x = y.
Proof.
  intros x y Hx Hy E. apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E.
  apply (f_equal (@bv_unsigned 64)) in E. rewrite !unsigned_lit in E by lia. exact E.
Qed.

Lemma map8_inj : forall s1 s2, Forall (fun c => 0 < c < 256) s1 -> Forall (fun c => 0 < c < 256) s2 ->
  map (Z_to_bv 8) s1 = map (Z_to_bv 8) s2 -> s1 = s2.
Proof.
  induction s1 as [|x s1 IH]; intros [|y s2] H1 H2 E; cbn in E; try discriminate; [reflexivity|].
  assert (Ex : Z_to_bv 8 x = Z_to_bv 8 y) by congruence.
  assert (Es : map (Z_to_bv 8) s1 = map (Z_to_bv 8) s2) by congruence.
  inversion H1 as [|? ? Hx H1']; subst. inversion H2 as [|? ? Hy H2']; subst.
  f_equal; [|apply IH; assumption].
  apply (f_equal (@bv_unsigned 8)) in Ex. rewrite !Z_to_bv_unsigned in Ex. unfold bv_wrap in Ex.
  change (bv_modulus 8) with 256 in Ex. rewrite !Z.mod_small in Ex by lia. exact Ex.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma rd8 : forall m a v, pj_u64 segs m a v -> ov_read_bytes segs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v [Hv B].
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read segs m a (le8 (Z_to_bv 64 v)) 0 8 B ltac:(lia)) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Lemma rd4 : forall m a v, pj_u32 segs m a v -> ov_read_bytes segs m (wa a) 4 = Some (le4 (Z_to_bv 64 v)).
Proof.
  intros m a v [Hv B].
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read segs m a (le4 (Z_to_bv 64 v)) 0 4 B ltac:(lia)) by (rewrite length_le4; lia).
  reflexivity.
Qed.

Lemma pj_view : forall m L p t D, pj_node segs m L p t D ->
  exists num str kids keys n cap, pj_hdr segs m p (tag t) num str kids keys n cap /\
    n = Z.of_nat (length (slots t)) /\
    match t with
    | JNum txt bits => num = bits /\ exists k, pj_cstr segs m L str k txt
    | JStr s => exists k, pj_cstr segs m L str k s
    | _ => True
    end.
Proof.
  intros m L p t D H.
  destruct t as [| | | txt bits | s | items | members]; cbn [pj_node] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & Hb);
    exists num, str, kids, keys, n, cap; (split; [exact Hh|]); cbn [slots]; rewrite ?length_map.
  - destruct Hb as (_ & _ & _ & En & _). split; [cbn; lia | exact I].
  - destruct Hb as (_ & _ & _ & En & _). split; [cbn; lia | exact I].
  - destruct Hb as (_ & _ & _ & En & _). split; [cbn; lia | exact I].
  - destruct Hb as (Eb & _ & _ & En & _ & k & Hc & _). split; [cbn; lia|]. split; [exact Eb | exists k; exact Hc].
  - destruct Hb as (_ & _ & En & _ & k & Hc & _). split; [cbn; lia|]. exists k; exact Hc.
  - destruct Hb as (_ & _ & En & _). split; [exact En | exact I].
  - destruct Hb as (_ & En & _). split; [exact En | exact I].
Qed.

Lemma mems_in : forall m L (P : Z -> jv -> list (Z * Z) -> Prop) (Q : Z * Z -> Prop) l a ka D,
  (forall a' nm u D1, In (nm, u) l -> P a' u D1 -> forall b, In b D1 -> Q b) ->
  (forall x k nm, pj_cstr segs m L x k nm -> Q (x, k)) ->
  pj_mems segs m L P a ka l D -> forall b, In b D -> Q b.
Proof.
  intros m L P Q l. induction l as [|[nm u] r IH]; intros a ka D H HC Hl b Hb; cbn [pj_mems] in Hl.
  - subst D. destruct Hb.
  - destruct Hl as (x & k & D1 & D2 & ED & _ & Hc & HP & HR). subst D. destruct Hb as [Hb|Hb].
    + subst b. exact (HC x k nm Hc).
    + apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      * exact (H a nm u D1 (or_introl eq_refl) HP b Hb).
      * apply (IH (a + 56) (ka + 8) D2); [|exact HC|exact HR|exact Hb].
        intros a' nm' v D3 Hv HP3. exact (H a' nm' v D3 (or_intror Hv) HP3).
Qed.

Lemma pj_node_blocks : forall t m L p D, pj_node segs m L p t D -> forall a k, In (a, k) D -> L a k.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
    intros m L p D H a k Hin; cbn [pj_node] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & Hb).
  - destruct Hb as (_ & _ & _ & _ & _ & ED). subst D. destruct Hin.
  - destruct Hb as (_ & _ & _ & _ & _ & ED). subst D. destruct Hin.
  - destruct Hb as (_ & _ & _ & _ & _ & ED). subst D. destruct Hin.
  - destruct Hb as (_ & _ & _ & _ & _ & k' & (HL & _) & ED). subst D. destruct Hin as [E|[]].
    injection E as <- <-. exact HL.
  - destruct Hb as (_ & _ & _ & _ & k' & (HL & _) & ED). subst D. destruct Hin as [E|[]].
    injection E as <- <-. exact HL.
  - destruct Hb as (_ & _ & _ & _ & Hcap & Di & ED & Hi). subst D. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + revert Hin. destruct (Z.eqb_spec cap 0) as [C|C]; intros Hin; [destruct Hin|].
      destruct Hin as [E|[]]. injection E as <- <-.
      destruct Hcap as [(C0 & _)|(_ & HL)]; [lia | exact HL].
    + refine (items_in (pj_node segs m L) (fun b => L (fst b) (snd b)) items kids Di _ Hi (a, k) Hin).
      intros a' u D1 Hu HP [x y] Hb. rewrite Forall_forall in IH. exact (IH u Hu m L a' D1 HP x y Hb).
  - destruct Hb as (_ & _ & _ & Hcap & Di & ED & Hi). subst D. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + revert Hin. destruct (Z.eqb_spec cap 0) as [C|C]; intros Hin; [destruct Hin|].
      destruct Hin as [E|[E|[]]]; injection E as <- <-;
        destruct Hcap as [(C0 & _)|(_ & HL1 & HL2)]; first [lia | assumption].
    + refine (mems_in m L (pj_node segs m L) (fun b => L (fst b) (snd b)) members kids keys Di _ _ Hi (a, k) Hin).
      * intros a' nm u D1 Hu HP [x y] Hb. rewrite Forall_forall in IH. exact (IH (nm, u) Hu m L a' D1 HP x y Hb).
      * intros x k' nm (HL & _). exact HL.
Qed.

Lemma mems_nth : forall m L (P : Z -> jv -> list (Z * Z) -> Prop) l a ka D i nm u,
  pj_mems segs m L P a ka l D -> nth_error l i = Some (nm, u) ->
  exists x k D1, incl D1 D /\ pj_u64 segs m (ka + 8 * Z.of_nat i) x /\
    pj_cstr segs m L x k nm /\ P (a + 56 * Z.of_nat i) u D1.
Proof.
  intros m L P l. induction l as [|[nm0 v] r IH]; intros a ka D i nm u H E; [destruct i; discriminate|].
  cbn [pj_mems] in H. destruct H as (x & k & D1 & D2 & ED & Hx & Hc & HP & HR).
  destruct i as [|i]; cbn in E.
  - injection E as E1 E2. subst nm0 v. exists x, k, D1.
    split; [subst D; intros b Hb; right; apply in_or_app; left; exact Hb|].
    replace (ka + 8 * Z.of_nat 0) with ka by lia. replace (a + 56 * Z.of_nat 0) with a by lia. auto.
  - destruct (IH (a + 56) (ka + 8) D2 i nm u HR E) as (x' & k' & D3 & Hinc & Hx' & Hc' & HP').
    exists x', k', D3.
    split; [subst D; intros b Hb; right; apply in_or_app; right; apply Hinc; exact Hb|].
    replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) by lia.
    replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia. auto.
Qed.

Lemma pj_slot : forall m L p t D i o u, pj_node segs m L p t D -> nth_error (slots t) i = Some (o, u) ->
  exists num str kids keys n cap D1,
    pj_hdr segs m p (tag t) num str kids keys n cap /\
    Z.of_nat i < cap /\ L kids (56 * cap) /\
    pj_node segs m L (kids + 56 * Z.of_nat i) u D1 /\
    (forall z, pj_foot (kids + 56 * Z.of_nat i) D1 z -> pj_foot p D z) /\
    match o with
    | Some nm => L keys (8 * cap) /\ exists x k, pj_u64 segs m (keys + 8 * Z.of_nat i) x /\ pj_cstr segs m L x k nm
    | None => True
    end.
Proof.
  intros m L p t D i o u H E.
  destruct t as [| | | txt bits | s | items | members]; cbn [slots] in E; try (destruct i; discriminate);
    rewrite nth_error_map in E.
  - destruct (nth_error items i) as [v|] eqn:Ev; cbn in E; [|discriminate].
    injection E as E1 E2. subst o v.
    cbn [pj_node] in H.
    destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & Di & ED & Hi).
    destruct (items_nth _ items kids Di i u Hi Ev) as (D1 & Hinc & HP).
    assert (Hil : (i < length items)%nat) by (apply nth_error_Some; rewrite Ev; discriminate).
    exists num, str, kids, keys, n, cap, D1. split; [exact Hh|]. split; [lia|].
    split; [destruct Hcap as [(C0 & _)|(_ & HL)]; [lia | exact HL]|].
    split; [exact HP|]. split; [|exact I].
    intros z [Hz|(b & Hb & Hz)].
    + right. exists (kids, 56 * cap). split.
      * subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity.
      * unfold pj_holds; cbn [fst snd]. lia.
    + right. exists b. split; [subst D; apply in_or_app; right; apply Hinc; exact Hb | exact Hz].
  - destruct (nth_error members i) as [[nm v]|] eqn:Ev; cbn in E; [|discriminate].
    injection E as E1 E2. subst o v.
    cbn [pj_node] in H.
    destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & Es & En & Hc & Hcap & Di & ED & Hi).
    destruct (mems_nth m L _ members kids keys Di i nm u Hi Ev) as (x & k & D1 & Hinc & Hx & Hcs & HP).
    assert (Hil : (i < length members)%nat) by (apply nth_error_Some; rewrite Ev; discriminate).
    exists num, str, kids, keys, n, cap, D1. split; [exact Hh|]. split; [lia|].
    split; [destruct Hcap as [(C0 & _)|(_ & HL & _)]; [lia | exact HL]|].
    split; [exact HP|].
    split; [|split; [destruct Hcap as [(C0 & _)|(_ & _ & HL)]; [lia | exact HL] | exists x, k; split; assumption]].
    intros z [Hz|(b & Hb & Hz)].
    + right. exists (kids, 56 * cap). split.
      * subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity.
      * unfold pj_holds; cbn [fst snd]. lia.
    + right. exists b. split; [subst D; apply in_or_app; right; apply Hinc; exact Hb | exact Hz].
Qed.

Lemma cstr_bytes : forall m L a k s, pj_cstr segs m L a k s ->
  bytes_at segs m a (map (Z_to_bv 8) s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) s).
Proof.
  intros m L a k s (_ & _ & Hf & Hb). rewrite map_app in Hb. split; [exact Hb|].
  intros Hin. apply in_map_iff in Hin. destruct Hin as (c & Ec & Hc).
  rewrite Forall_forall in Hf. specialize (Hf c Hc).
  apply (f_equal (@bv_unsigned 8)) in Ec. rewrite !Z_to_bv_unsigned in Ec. unfold bv_wrap in Ec.
  change (bv_modulus 8) with 256 in Ec. rewrite (Z.mod_small c) in Ec by lia. rewrite Z.mod_0_l in Ec by lia. lia.
Qed.

Lemma cstr_forall : forall m L a k s, pj_cstr segs m L a k s -> Forall (fun c => 0 < c < 256) s.
Proof. intros m L a k s (_ & _ & Hf & _). exact Hf. Qed.

End WithSegs.
