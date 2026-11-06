(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YO0y.v; 166 of its 252 lines of code are new or changed and 91 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/AllocPack3Malloc.v; 299 of its 311 lines of code are new or changed and 240 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Arith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0g YO0h YO0w YO0s YO11 YO15 YO12 YO0z YO14 YO0u YO0q YO0v YO0t YO0e YO0m YO0x YO03 YO0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocSI AllocGS AllocRealloc AllocPack AllocPackFree AllocPack3 AllocPack3Free.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require AllocFree AllocMalloc AllocBound.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Lemma lv2_nth L k n j : length L = 49%nat -> 0 <= j -> 0 <= k -> 0 <= n ->
  znth j (lv_add (lv_add L (band k) (-1)) (band n) 1) =
  znth j L - (if j =? band k then 1 else 0) + (if j =? band n then 1 else 0).
Proof.
  intros HL Hj Hk Hn. pose proof (band_range k Hk) as Bk. pose proof (band_range n Hn) as Bn.
  rewrite !lv_add_nth by lia. rewrite lv_add_length, HL. change (Z.of_nat 49) with 49.
  destruct (Z.eqb_spec j (band n)); destruct (Z.eqb_spec j (band k)); destruct (Z.ltb_spec (band n) 49);
    destruct (Z.ltb_spec (band k) 49); cbn [andb]; lia.
Qed.

Lemma lv_comm L k n j : length L = 49%nat -> 0 <= k -> 0 <= n -> 0 <= j ->
  znth j (lv_add (lv_add L (band n) 1) (band k) (-1)) = znth j (lv_add (lv_add L (band k) (-1)) (band n) 1).
Proof.
  intros HL Hk Hn Hj. pose proof (band_range k Hk) as Bk. pose proof (band_range n Hn) as Bn.
  rewrite (lv2_nth L k n j HL Hj Hk Hn). rewrite !lv_add_nth by lia. rewrite lv_add_length, HL.
  change (Z.of_nat 49) with 49.
  destruct (Z.eqb_spec j (band n)); destruct (Z.eqb_spec j (band k)); destruct (Z.ltb_spec (band n) 49);
    destruct (Z.ltb_spec (band k) 49); cbn [andb]; lia.
Qed.

Lemma UPB3_swap s s' L M M' k n : length L = 49%nat -> 0 <= k -> 0 <= n -> UPB3 s L M ->
  (forall j, bcount s' j + (if band k =? j then 1 else 0) = bcount s j + (if band n =? j then 1 else 0)) ->
  (forall c, 1 <= c < 48 -> upc s' c + mis_in s M c <= upc s c + mis_in s' M' c) ->
  UPB3 s' (lv_add (lv_add L (band k) (-1)) (band n) 1) M'.
Proof.
  intros HL Hk Hn (U1 & U2) B Up. split.
  - intros j Hj. rewrite (lv2_nth L k n j HL ltac:(lia) Hk Hn). specialize (U1 j Hj). specialize (B j).
    revert B. destruct (Z.eqb_spec (band k) j); destruct (Z.eqb_spec (band n) j); destruct (Z.eqb_spec j (band k));
      destruct (Z.eqb_spec j (band n)); cbv beta iota; intros B; lia.
  - intros c Hc. rewrite (lv2_nth L k n c HL ltac:(lia) Hk Hn). specialize (U2 c Hc). specialize (B c).
    specialize (Up c Hc).
    revert B. destruct (Z.eqb_spec (band k) c); destruct (Z.eqb_spec (band n) c); destruct (Z.eqb_spec c (band k));
      destruct (Z.eqb_spec c (band n)); cbv beta iota; intros B; lia.
Qed.

Lemma mis_in_cons s e M c : mis_in s (e :: M) c = (if mis_ok s c e then 1 else 0) + mis_in s M c.
Proof. unfold mis_in. cbn [filter]. destruct (mis_ok s c e); cbn [length]; lia. Qed.

Lemma count_del3 M p c : count_mis (mis_del M p) c <= count_mis M c.
Proof.
  unfold count_mis, mis_del. rewrite f3_filter_filter. apply Nat2Z.inj_le. apply f3_len_mono.
  intros x _ Hx. cbv beta in Hx |- *. apply andb_prop in Hx as [_ Hx]. exact Hx.
Qed.

Lemma mis_re_ne M k n p q : sptr_eqb q p = false -> mis_realloc M k n p q = mis_del M p.
Proof. intros H. unfold mis_realloc. rewrite H. reflexivity. Qed.

Lemma band_big n : MMAP_THRESHOLD <= n -> band n = 48.
Proof. intros H. unfold band. destruct (Z.leb_spec MMAP_THRESHOLD n); [reflexivity | lia]. Qed.

Lemma mis_re_big M k n p q : band n = 48 -> mis_realloc M k n p q = mis_del M p.
Proof.
  intros H. unfold mis_realloc. rewrite H. replace (48 + 1 <? 48) with false by reflexivity.
  rewrite andb_false_r. reflexivity.
Qed.

Lemma mis_re3 s s' M k n p q mc l1 l2 : MIS s M mc -> user_blocks s = l1 ++ (p, k) :: l2 ->
  user_blocks s' = l1 ++ (q, n) :: l2 -> (band n + 1 < 48 -> count_mis M (band n + 1) + 1 <= znth (band n + 1) mc) ->
  0 <= n -> MIS s' (mis_realloc M k n p q) mc.
Proof.
  intros HM E1 E2 Hc Hn.
  assert (D : MIS s' (mis_del M p) mc).
  { apply (mis_del3 s s' M p mc HM). intros x m Hx Ne. rewrite E1 in Hx. rewrite E2.
    exact (f3_in_del l1 l2 [(q, n)] p k x m Hx Ne). }
  unfold mis_realloc. match goal with |- MIS _ (if ?b then _ else _) _ => destruct b eqn:Cnd end; [|exact D].
  apply andb_prop in Cnd as [Cnd _]. apply andb_prop in Cnd as [Eq Lt]. apply sptr_eqb_eq in Eq.
  apply Z.ltb_lt in Lt. subst q.
  pose proof (band_range n Hn) as Bn. destruct D as (ND & DE & DC). split; [|split].
  - cbn [map fst]. constructor; [|exact ND]. intros Hin. apply in_map_iff in Hin as (e & Ee & He).
    unfold mis_del in He. apply filter_In in He as [_ He]. cbv beta in He. rewrite Ee, sptr_eqb_refl in He. cbn [negb] in He.
    discriminate.
  - intros e [<-|He]; [|exact (DE e He)]. cbn [fst snd]. split; [lia|]. exists n. rewrite E2.
    apply in_or_app. right. left. reflexivity.
  - intros c Hcl. pose proof (DC c Hcl) as D1. pose proof (count_del3 M p c) as D2.
    unfold count_mis in *. cbn [filter snd].
    destruct (Z.eqb_spec (band n + 1) c) as [Ec|Ne]; cbn [length].
    + subst c. specialize (Hc Lt). lia.
    + exact D1.
Qed.

Lemma ip3_gen s g am am1 i fr f1 caps mc L M M' : WF s -> usedX [] s g am -> 0 <= i <= am_last am ->
  ss_fr (nth_slot am i) = Some fr -> fr_kind fr = FUser -> pk_shp am am1 ->
  (forall j, 0 <= j -> j <> i -> nth_slot am1 j = nth_slot am j) ->
  ss_fr (nth_slot am1 i) = Some f1 -> fr_kind f1 = FUser -> 0 <= fr_n f1 ->
  (am_sc am < 48 -> fr_n f1 < MMAP_THRESHOLD /\ am_sc am <= size_to_class (fr_n f1) + 1) ->
  (exists l1 l2 x y, user_blocks s = l1 ++ (x, fr_n fr) :: l2 /\
     user_blocks (upd_meta g (MUsed am1) s) = l1 ++ (y, fr_n f1) :: l2) ->
  PKS [] s -> PKC3 [] caps mc s -> UPB3 s L M -> NoDup (map fst M) -> length L = 49%nat ->
  (forall c, mis_in (upd_meta g (MUsed am1) s) (mis_del M (frame_ptr am i fr)) c <=
     mis_in (upd_meta g (MUsed am1) s) M' c) ->
  (forall c, 1 <= c < 48 -> am_sc am = c -> 1 <= am_last am -> band (fr_n f1) = c - 1 ->
     band (fr_n fr) = c \/ mis_lookup M (frame_ptr am i fr) = Some c ->
     mis_in (upd_meta g (MUsed am1) s) (mis_del M (frame_ptr am i fr)) c + 1 <=
     mis_in (upd_meta g (MUsed am1) s) M' c) ->
  PKS [] (upd_meta g (MUsed am1) s) /\ PKC3 [] caps mc (upd_meta g (MUsed am1) s) /\
  UPB3 (upd_meta g (MUsed am1) s) (lv_add (lv_add L (band (fr_n fr)) (-1)) (band (fr_n f1)) 1) M'.
Proof.
  intros HW Hu Hi Hfr Hk Sh Hj Hf1 Hk1 Hn1 Hc1 Hbl HP HC HU ND HL Mge Mnew.
  pose proof Sh as (M0 & Lm & S & T).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg _]. pose proof (proj1 (inv_keys HW)) as N.
  destruct (pk_frame s g am i fr HW Hu Hi Hfr) as (Hk0 & Fo & F2 & Hs0).
  assert (Fk : 1 <= am_last am -> am_sc am < 48 -> am_sc am - 1 <= band (fr_n fr) <= am_sc am).
  { intros Hl Hs. pose proof HP as (P1 & _). destruct (P1 g am i fr Hu Hs Hi Hfr Hk) as (Hm & Hb).
    assert (St : stride_of am = class_size (am_sc am)).
    { unfold stride_of. destruct (Z.eqb_spec (am_last am) 0); [lia | reflexivity]. }
    rewrite St in F2. unfold UNIT in F2.
    pose proof (stc_le (am_sc am) (fr_n fr) ltac:(lia) Hk0 ltac:(lia)) as Le.
    unfold band. destruct (Z.leb_spec MMAP_THRESHOLD (fr_n fr)); lia. }
  split; [|split].
  - apply (PKS_upd s g am am1 i HP Hu Sh Hj). intros f Ef. rewrite Hf1 in Ef. injection Ef as <-.
    split; [exact Hk1 | exact Hc1].
  - exact (PKC3_upd s g am am1 caps mc HW HC Hu S T).
  - destruct Hbl as (l1 & l2 & x & y & E1 & E2).
    apply (UPB3_swap s _ L M M' (fr_n fr) (fr_n f1) HL Hk0 Hn1 HU).
    + intros j. exact (bcount_swap s _ l1 l2 (x, fr_n fr) (y, fr_n f1) j E1 E2).
    + intros c Hc. pose proof (upc_upd s g am am1 c N Mg) as E.
      pose proof (mis_step s _ M (frame_ptr am i fr) c ND
        (keep_upd s g am am1 i fr c HW Hu Hi Hfr (fun _ _ => conj Sh Hj))) as Ms.
      pose proof (mrp3_range s M (frame_ptr am i fr) c) as Rr.
      pose proof (Mge c) as Mg'.
      assert (Rp : mrp3 s M (frame_ptr am i fr) c = 1 ->
                   am_sc am = c /\ 1 <= am_last am /\ band (fr_n fr) = c - 1 /\ mis_lookup M (frame_ptr am i fr) = Some c).
      { unfold mrp3. destruct (mis_lookup M (frame_ptr am i fr)) as [c'|] eqn:Lk; [|intros R1; discriminate].
        destruct (Z.eqb_spec c' c) as [Ec|Ne]; [subst c'|cbn [andb]; intros R1; discriminate].
        destruct (pmis3 s (frame_ptr am i fr) c) eqn:Pm; [|cbn [andb]; intros R1; discriminate].
        intros _. destruct (pmis_loc s _ c g am i fr HW Hu Hi Hfr eq_refl Pm) as (A1 & A2 & A3).
        split; [exact A1|]. split; [exact A2|]. split; [exact A3 | reflexivity]. }
      destruct ((am_sc am =? c) && (1 <=? am_last am)) eqn:Cd.
      * pose proof (ucnt_on c am am1 i fr f1 Cd Sh Hi Hj Hfr Hk Hf1 Hk1) as E'.
        apply andb_prop in Cd as [Cs Cl]. apply Z.eqb_eq in Cs. apply Z.leb_le in Cl.
        destruct (Fk Cl ltac:(lia)) as [Fk1 Fk2].
        pose proof (Mnew c Hc Cs Cl) as Nw.
        assert (Key : mis_in (upd_meta g (MUsed am1) s) (mis_del M (frame_ptr am i fr)) c + mrp3 s M (frame_ptr am i fr) c +
                      (if band (fr_n f1) =? c - 1 then 1 else 0) <=
                      mis_in (upd_meta g (MUsed am1) s) M' c + (if band (fr_n fr) =? c - 1 then 1 else 0)).
        { destruct (Z.eqb_spec (band (fr_n f1)) (c - 1)) as [Nc|Nc]; destruct (Z.eqb_spec (band (fr_n fr)) (c - 1)) as [Kc|Kc];
            cbv beta iota.
          - destruct (Z.eq_dec (mrp3 s M (frame_ptr am i fr) c) 1) as [R1|R0].
            + destruct (Rp R1) as (_ & _ & _ & Lk). pose proof (Nw Nc (or_intror Lk)). lia.
            + lia.
          - assert (Kc' : band (fr_n fr) = c) by lia. pose proof (Nw Nc (or_introl Kc')).
            destruct (Z.eq_dec (mrp3 s M (frame_ptr am i fr) c) 1) as [R1|R0].
            + destruct (Rp R1) as (_ & _ & Kc'' & _). lia.
            + lia.
          - lia.
          - destruct (Z.eq_dec (mrp3 s M (frame_ptr am i fr) c) 1) as [R1|R0].
            + destruct (Rp R1) as (_ & _ & Kc'' & _). lia.
            + lia. }
        unfold pk_bnd in E'. revert E E' Key.
        destruct (Z.eqb_spec (band (fr_n fr)) (c - 1)); destruct (Z.eqb_spec (band (fr_n f1)) (c - 1));
          cbv beta iota; intros E E' Key; lia.
      * assert (Cd1 : (am_sc am1 =? c) && (1 <=? am_last am1) = false) by (rewrite S, T; exact Cd).
        rewrite (ucnt_off c am Cd), (ucnt_off c am1 Cd1) in E.
        assert (R00 : mrp3 s M (frame_ptr am i fr) c = 0).
        { destruct (Z.eq_dec (mrp3 s M (frame_ptr am i fr) c) 1) as [R1|R0]; [|lia].
          destruct (Rp R1) as (A1 & A2 & _). rewrite A1, Z.eqb_refl, (proj2 (Z.leb_le 1 (am_last am)) A2) in Cd.
          cbn [andb] in Cd. discriminate. }
        lia.
Qed.

Lemma ip3 s g am i fr n caps mc L M : IPH s g am i fr n -> PKS [] s -> PKC3 [] caps mc s -> UPB3 s L M -> MIS s M mc ->
  length L = 49%nat -> (am_sc am < 48 -> n < MMAP_THRESHOLD /\ am_sc am <= size_to_class n + 1) ->
  (band n + 1 < 48 -> count_mis M (band n + 1) + 1 <= znth (band n + 1) mc) ->
  PKS [] (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s) /\
  PKC3 [] caps mc (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s) /\
  UPB3 (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s) (lv_add (lv_add L (band (fr_n fr)) (-1)) (band n) 1)
    (mis_realloc M (fr_n fr) n (frame_ptr am i fr) (frame_ptr am i fr)) /\
  MIS (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s)
    (mis_realloc M (fr_n fr) n (frame_ptr am i fr) (frame_ptr am i fr)) mc.
Proof.
  intros H HP HC HU HM HL Hc1 Hcm. pose proof H as (HW & Hu & Hi & Hfr & Hk & Hn & _).
  destruct (rs_fields am i (fr_off fr) n) as (Mm & T & S & Lm & _ & SS).
  destruct (ip_blocks s g am i fr n H) as (l1 & l2 & E1 & E2).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg _]. pose proof (proj1 (inv_keys HW)) as N.
  assert (N' : NoDup (keys (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s)))
    by (rewrite keys_upd_In by exact (MT_Some_In_keys _ _ _ Mg); exact N).
  assert (Hj : forall j, 0 <= j -> j <> i -> nth_slot (rs_am am i (fr_off fr) n) j = nth_slot am j).
  { intros j Hj Ne. rewrite (ip_ns s g am i fr n j H Hj). apply Z.eqb_neq in Ne. rewrite Ne. reflexivity. }
  assert (Sh : pk_shp am (rs_am am i (fr_off fr) n)) by exact (conj Mm (conj Lm (conj S T))).
  assert (Hp1 : frame_ptr (rs_am am i (fr_off fr) n) i (mkFrame (fr_off fr) n FUser) = frame_ptr am i fr).
  { unfold frame_ptr. rewrite SS. reflexivity. }
  assert (MGE : forall c, mis_in (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s) (mis_del M (frame_ptr am i fr)) c <=
    mis_in (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s) (mis_realloc M (fr_n fr) n (frame_ptr am i fr) (frame_ptr am i fr)) c).
  { intros c. unfold mis_realloc. match goal with |- context [if ?b then _ else _] => destruct b end; cbv beta iota; [|lia].
    rewrite mis_in_cons. match goal with |- context [if ?b then _ else _] => destruct b end; cbv beta iota; lia. }
  assert (MNEW : forall c, 1 <= c < 48 -> am_sc am = c -> 1 <= am_last am ->
     band (fr_n (mkFrame (fr_off fr) n FUser)) = c - 1 ->
     band (fr_n fr) = c \/ mis_lookup M (frame_ptr am i fr) = Some c ->
     mis_in (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s) (mis_del M (frame_ptr am i fr)) c + 1 <=
     mis_in (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s) (mis_realloc M (fr_n fr) n (frame_ptr am i fr) (frame_ptr am i fr)) c).
  { intros c Hc Cs Cl Nc Dj. cbn [fr_n] in Nc.
    assert (C1 : band n + 1 = c) by lia.
    unfold mis_realloc. rewrite C1, sptr_eqb_refl, (proj2 (Z.ltb_lt c 48) (proj2 Hc)).
    assert (Cd : ((c =? band (fr_n fr)) || match mis_lookup M (frame_ptr am i fr) with Some c0 => c0 =? c | None => false end) = true).
    { destruct Dj as [D|D].
      - rewrite D, Z.eqb_refl. reflexivity.
      - rewrite D. cbn beta iota. rewrite Z.eqb_refl. apply orb_true_r. }
    rewrite Cd. cbn [andb]. rewrite mis_in_cons.
    assert (Ok : mis_ok (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s) c (frame_ptr am i fr, c) = true).
    { unfold mis_ok. cbn [fst snd]. rewrite Z.eqb_refl. cbn [andb]. apply existsb_exists.
      exists (frame_ptr am i fr, n). split.
      - rewrite <- Hp1. apply (in_ubc3 [] _ c g (rs_am am i (fr_off fr) n) i (mkFrame (fr_off fr) n FUser) N').
        + apply usedX_upd. left. split; [reflexivity|]. split; reflexivity.
        + lia.
        + exact (ip_fr1 s g am i fr n H).
        + reflexivity.
        + lia.
        + lia.
      - cbn [fst snd]. rewrite sptr_eqb_refl. cbn [andb]. apply Z.eqb_eq. lia. }
    rewrite Ok. cbv beta iota. lia. }
  destruct (ip3_gen s g am (rs_am am i (fr_off fr) n) i fr (mkFrame (fr_off fr) n FUser) caps mc L M
    (mis_realloc M (fr_n fr) n (frame_ptr am i fr) (frame_ptr am i fr)) HW Hu Hi Hfr Hk Sh Hj (ip_fr1 s g am i fr n H)
    eq_refl Hn Hc1 (ex_intro _ l1 (ex_intro _ l2 (ex_intro _ _ (ex_intro _ _ (conj E1 E2))))) HP HC HU (proj1 HM) HL
    MGE MNEW) as (P1 & C1 & U1).
  split; [exact P1|]. split; [exact C1|]. split; [exact U1|].
  exact (mis_re3 s _ M (fr_n fr) n (frame_ptr am i fr) (frame_ptr am i fr) mc l1 l2 HM E1 E2 Hcm Hn).
Qed.

Lemma rm3 s g am fr n caps mc L M : RMH s g am fr n -> PKS [] s -> PKC3 [] caps mc s -> UPB3 s L M -> MIS s M mc ->
  length L = 49%nat -> 0 <= n -> 0 <= fr_n fr ->
  PKS [] (rm_state s g am 0 (fr_off fr) n) /\ PKC3 [] caps mc (rm_state s g am 0 (fr_off fr) n) /\
  UPB3 (rm_state s g am 0 (fr_off fr) n) (lv_add (lv_add L (band (fr_n fr)) (-1)) (band n) 1)
    (mis_del M (frame_ptr am 0 fr)) /\
  MIS (rm_state s g am 0 (fr_off fr) n) (mis_del M (frame_ptr am 0 fr)) mc.
Proof.
  intros H HP HC HU HM HL Hn Hk0. pose proof H as (HW & Hu & Hfr & Hk & Hsc & Hbig).
  destruct (rm_basic s g am fr n H) as (Hl & _ & _ & _ & _ & _ & _ & Hsl & Foff & _).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg _]. pose proof (proj1 (inv_keys HW)) as N.
  assert (EM : st_metas (rm_state s g am 0 (fr_off fr) n) =
               st_metas (upd_meta g (MUsed (rm_am s am 0 (fr_off fr) n)) s)) by reflexivity.
  destruct (rm_blocks s g am fr n H) as (l1 & l2 & E1 & E2).
  split; [|split; [|split]].
  - apply (PKS_metas _ _ EM). apply (PKS_tr s _ HP). intros q a' Hq.
    apply usedX_upd in Hq as [(-> & _ & E) | (Ne & Hq)].
    + injection E as <-. right. split; [exact Hsc|]. split.
      * pose proof (rm_need_facts n (fr_off fr) Hbig Foff) as (_ & RN & _).
        change (0 < rm_need n (fr_off fr) / 4096). lia.
      * intros j f Hj Hf. change (0 <= j <= am_last am) in Hj. rewrite Hl in Hj. assert (j = 0) by lia. subst j.
        rewrite (rm_slot0 s am (fr_off fr) n Hsl) in Hf. cbn [resize_slot ss_fr] in Hf. injection Hf as <-. reflexivity.
    + left. exists a'. split; [exact Hq|]. split; [split; [reflexivity | split; [reflexivity | split; reflexivity]]|].
      intros j f _ Hf. left. exact Hf.
  - apply (PKC3_metas _ _ caps mc EM).
    exact (PKC3_upd s g am (rm_am s am 0 (fr_off fr) n) caps mc HW HC Hu eq_refl eq_refl).
  - apply (UPB3_swap s _ L M _ (fr_n fr) n HL Hk0 Hn HU).
    + intros j. exact (bcount_swap s _ l1 l2 _ _ j E1 E2).
    + intros c Hc. rewrite (upc_metas _ _ c EM). pose proof (upc_upd s g am (rm_am s am 0 (fr_off fr) n) c N Mg) as E.
      rewrite (ucnt63 c am Hsc ltac:(lia)), (ucnt63 c (rm_am s am 0 (fr_off fr) n) Hsc ltac:(lia)) in E.
      assert (K : keep3 s (rm_state s g am 0 (fr_off fr) n) (frame_ptr am 0 fr) c).
      { apply (keep_metas s _ _ _ c EM). apply (keep_upd s g am _ 0 fr c HW Hu ltac:(lia) Hfr).
        intros Hs. exfalso. lia. }
      pose proof (mis_step s _ M _ c (proj1 HM) K) as Ms.
      assert (R0 : mrp3 s M (frame_ptr am 0 fr) c = 0).
      { unfold mrp3. destruct (mis_lookup M (frame_ptr am 0 fr)) as [c'|]; [|reflexivity].
        destruct (pmis3 s (frame_ptr am 0 fr) c) eqn:Pm; [|rewrite andb_false_r; reflexivity].
        destruct (pmis_loc s _ c g am 0 fr HW Hu ltac:(lia) Hfr eq_refl Pm) as (A & _). exfalso. lia. }
      lia.
  - apply (mis_del3 s _ M _ mc HM). intros x m Hx Ne. rewrite E1 in Hx. rewrite E2.
    exact (f3_in_del l1 l2 [_] _ _ x m Hx Ne).
Qed.

Section Pack3Realloc.

Hypothesis malloc_pack3_h : forall s n caps mc L M tr r s',
  WF s -> SI s -> GS s -> NL s -> noraw s -> PKS [] s -> PKC3 [] caps mc s -> UPB3 s L M -> MIS s M mc ->
  length caps = 49%nat -> length L = 49%nat -> length mc = 49%nat ->
  (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps /\ 0 <= znth k mc) ->
  0 <= n -> yields (malloc n s) tr (r, s') ->
  PKS [] s' /\ PKC3 [] caps mc s' /\
  UPB3 s' (match r with Some _ => lv_add L (band n) 1 | None => L end) M /\ MIS s' M mc.

Theorem realloc_pack3 : forall s p k n caps mc L M tr q s',
  WF s -> SI s -> GS s -> NL s -> noraw s -> PKS [] s -> PKC3 [] caps mc s -> UPB3 s L M -> MIS s M mc ->
  length caps = 49%nat -> length L = 49%nat -> length mc = 49%nat ->
  (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps /\ 0 <= znth k mc) ->
  In (p, k) (user_blocks s) -> 0 <= n ->
  (band n + 1 < 48 -> count_mis M (band n + 1) + 1 <= znth (band n + 1) mc) ->
  yields (realloc (Some p) n s) tr (Some q, s') ->
  PKS [] s' /\ PKC3 [] caps mc s' /\
  UPB3 s' (lv_add (lv_add L (band k) (-1)) (band n) 1) (mis_realloc M k n p q) /\ MIS s' (mis_realloc M k n p q) mc.
Proof using malloc_pack3_h.
  intros s p k n caps mc L M tr q s' HW HS HG HN HR HP HC HU HM Lc LL Lm Lb Hin Hn Hcm Y.
  pose proof (AllocBound.ub_nonneg s HW (p, k) Hin) as Hk0. cbn [snd] in Hk0.
  destruct (ra_cases answer_ok s p k n tr (Some q) s' HW Hin (rpath_yields _ _ _ Y))
    as [[E _] | (g & am & i & fr & Hu & Hi & Hfr & Hk & En & Ep & C)]; [discriminate|].
  subst k.
  destruct C as [(Hc & Eq & ->) | [(Hsc & Hbig & Hml & Eq & ->) | [(Hsc & Hbig & Hne & Eq & ->) | (tr' & Hm)]]].
  - injection Eq as Eq. subst q. subst p.
    pose proof (ip_of_c1 s g am i fr n HW Hu Hi Hfr Hk Hn Hc) as I.
    unfold ra_c1 in Hc. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [_ H2].
    apply Z.ltb_lt in H2. apply Z.leb_le in H3.
    exact (ip3 s g am i fr n caps mc L M I HP HC HU HM LL (fun _ => conj H2 H3) Hcm).
  - injection Eq as Eq. subst q. subst p.
    pose proof (ip_of_same s g am i fr n HW Hu Hi Hfr Hk Hsc Hbig Hml) as I.
    assert (Hc' : am_sc am < 48 -> n < MMAP_THRESHOLD /\ am_sc am <= size_to_class n + 1) by (intros; exfalso; lia).
    exact (ip3 s g am i fr n caps mc L M I HP HC HU HM LL Hc' Hcm).
  - injection Eq as Eq. subst q. destruct (rm_of s g am i fr n HW Hu Hi Hfr Hk Hsc Hbig) as [Ei R]. subst i p.
    rewrite (mis_re_big M (fr_n fr) n _ _ (band_big n Hbig)).
    exact (rm3 s g am fr n caps mc L M R HP HC HU HM LL Hn Hk0).
  - destruct (ra_move answer_ok p n s tr' (Some q) s' Hm) as (tr1 & q1 & s1 & H1 & Hq).
    pose proof (yields_rpath _ _ _ H1) as Y1.
    destruct q1 as [q1|]; [|destruct Hq as [Hq _]; discriminate].
    destruct Hq as (Eq & tr2 & H2). injection Eq as Eq. subst q1.
    destruct (malloc_pack3_h s n caps mc L M tr1 (Some q) s1 HW HS HG HN HR HP HC HU HM Lc LL Lm Lb Hn Y1)
      as (P1 & C1 & U1 & M1).
    pose proof (malloc_wf s n tr1 (Some q) s1 HW Hn Y1) as HW1.
    pose proof (AllocMalloc.malloc_SI s n tr1 (Some q) s1 HW HS Hn Y1) as HS1.
    destruct (malloc_blocks s n tr1 (Some q) s1 HW Hn Y1) as (l1 & l2 & E1 & E2 & _ & Fq).
    pose proof (in_after_malloc s s1 l1 l2 q n (p, fr_n fr) E1 E2 Hin) as Hin1.
    destruct (free_pack3 s1 p (fr_n fr) caps mc (lv_add L (band n) 1) M tr2 tt s' HW1 HS1 P1 C1 U1 M1 Hin1
      (yields_rpath _ _ _ H2)) as (P2 & C2 & U2 & M2).
    assert (Nq : sptr_eqb q p = false).
    { apply sptr_eqb_neq. intros Eqp. subst q. apply Fq. apply in_map_iff. exists (p, fr_n fr). split; [reflexivity | exact Hin]. }
    rewrite (mis_re_ne M (fr_n fr) n p q Nq).
    split; [exact P2|]. split; [exact C2|]. split; [|exact M2].
    apply (UPB3_mono s' (lv_add (lv_add L (band n) 1) (band (fr_n fr)) (-1)) _ _); [|exact U2].
    intros j Hj. rewrite (lv_comm L (fr_n fr) n j LL Hk0 Hn ltac:(lia)). lia.
Qed.

End Pack3Realloc.
