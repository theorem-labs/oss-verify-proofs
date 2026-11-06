(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YO0y.v; 234 of its 324 lines of code are new or changed and 87 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO0i YO0f YO0g YO0h YO0w YO0s YO11 YO15 YO12 YO0z YO14 YO0u YO0q YO0v YO0y YO03 YO0m YO0p.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import AllocSI AllocGS AllocMalloc AllocCount AllocPack AllocPackUPB AllocPackMallocN AllocPackMallocW AllocPackMallocC AllocPackMallocA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Lemma band_range n : 0 <= n -> 0 <= band n <= 48.
Proof.
  intros Hn. unfold band. destruct (MMAP_THRESHOLD <=? n) eqn:E; [lia|]. apply Z.leb_gt in E.
  pose proof (size_to_class_range n ltac:(lia)). lia.
Qed.

Lemma len_filter {A} (f : A -> bool) l : (length (filter f l) <= length l)%nat.
Proof. induction l as [|x l IH]; cbn [filter length]; [lia|]. destruct (f x); cbn [length]; lia. Qed.

Lemma upc_le s c : upc s c <= Z.of_nat (length (ub_cls s c)).
Proof. unfold upc. pose proof (len_filter (fun b => band (snd b) =? c - 1) (ub_cls s c)). lia. Qed.

Lemma delta_k (sc l b c : Z) : 0 <= b <= 48 ->
  ((if 1 <=? l then sc else 100) =? c) && (b =? c - 1) = (sc =? c) && (1 <=? l) && (b =? c - 1).
Proof.
  intros Hb. destruct (1 <=? l); destruct (sc =? c); destruct (100 =? c) eqn:E; destruct (b =? c - 1) eqn:F;
  cbn [andb]; try reflexivity; exfalso; apply Z.eqb_eq in E; apply Z.eqb_eq in F; lia.
Qed.

Lemma bcount_ins s s3 L1 L2 q n : user_blocks s3 = L1 ++ (q, n) :: L2 -> user_blocks s = L1 ++ L2 ->
  forall b, bcount s3 b = bcount s b + (if band n =? b then 1 else 0).
Proof.
  intros E1 E2 b. unfold bcount. rewrite E1, E2, !filter_app. cbn [filter snd].
  destruct (band n =? b); rewrite !length_app; cbn [length]; lia.
Qed.

Lemma ucls_split s g x c : NoDup (keys s) -> In g (keys s) ->
  exists K1 K2, ub_cls (upd_meta g x s) c = K1 ++ ucls c (Some x) ++ K2 /\ ub_cls s c = K1 ++ ucls c (MT s g) ++ K2.
Proof.
  intros N Hg. pose proof N as N'. rewrite <- (keys_upd_In g x s Hg) in N'.
  rewrite (ub_cls_keys _ c N'), (ub_cls_keys s c N), (keys_upd_In g x s Hg).
  destruct (in_split _ _ Hg) as (k1 & k2 & Ek). pose proof N as ND. rewrite Ek in ND. pose proof (NoDup_remove_2 _ _ _ ND) as Hni.
  rewrite Ek, !flat_map_app. cbn [flat_map]. rewrite MT_upd_same.
  exists (flat_map (fun q => ucls c (MT s q)) k1), (flat_map (fun q => ucls c (MT s q)) k2). split; [|reflexivity].
  rewrite (flat_map_ext_In (fun q => ucls c (MT (upd_meta g x s) q)) (fun q => ucls c (MT s q)) k1).
  2:{ intros q Hq. rewrite MT_upd_other; [reflexivity|]. intros ->. apply Hni. apply in_app_iff. left. exact Hq. }
  rewrite (flat_map_ext_In (fun q => ucls c (MT (upd_meta g x s) q)) (fun q => ucls c (MT s q)) k2).
  2:{ intros q Hq. rewrite MT_upd_other; [reflexivity|]. intros ->. apply Hni. apply in_app_iff. right. exact Hq. }
  reflexivity.
Qed.

Lemma upc_ins s2 gm am idx hdr off n c : NoDup (keys s2) -> MT s2 gm = Some (MUsed am) -> 0 <= idx <= am_last am ->
  length (am_slots am) = Z.to_nat (am_last am + 1) -> ss_fr (nth_slot am idx) = None ->
  upc (upd_meta gm (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser))))) s2) c =
  upc s2 c + (if (am_sc am =? c) && (1 <=? am_last am) && (band n =? c - 1) then 1 else 0).
Proof.
  intros N Mg Hi Hlen Hfr.
  destruct (ucls_split s2 gm (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser))))) c N
    (MT_Some_In_keys _ _ _ Mg)) as (K1 & K2 & E1 & E2).
  unfold upc. rewrite E1, E2, Mg. cbn [ucls].
  pose proof (upd_slot_fields am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser)))) as (Fm & Fl & Fsc & _). rewrite Fsc, Fl.
  destruct (blocks_of_upd_slot gm am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser))) Hi Hlen) as (l1 & l2 & B1 & B2).
  apply (f_equal (map fst)) in B1. apply (f_equal (map fst)) in B2. rewrite map_fst_blocks_of, !map_app in B1, B2.
  unfold slot_block in B1. rewrite Hfr in B1. cbn [map app] in B1.
  unfold slotst_block in B2. cbn [ss_fr fr_kind fr_off fr_n map fst] in B2.
  rewrite B1, B2.
  destruct (am_sc am =? c); destruct (1 <=? am_last am); cbn [andb].
  - rewrite !filter_app, !length_app. cbn [filter snd app]. destruct (band n =? c - 1); cbn [length]; lia.
  - lia.
  - lia.
  - lia.
Qed.

Lemma final_UPB s s2 L gm am idx hdr off n :
  Inv [] (Some (gm, idx)) U0 s2 -> NoDup (keys s) -> ub_same s s2 -> CL s s2 -> UPB s L -> length L = 49%nat -> 0 <= n ->
  MT s2 gm = Some (MUsed am) -> 0 <= idx <= am_last am -> length (am_slots am) = Z.to_nat (am_last am + 1) ->
  ss_fr (nth_slot am idx) = None ->
  ((if 1 <=? am_last am then am_sc am else 100) = band n + 1 -> 1 <= band n + 1 < 48 -> upc s (band n + 1) <= 12) ->
  UPB (upd_meta gm (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser))))) s2) (lv_add L (band n) 1).
Proof.
  intros HI2 N0 UB2 CL2 HU HLn Hn Mg2 Hidx Glen Hfr Hco.
  pose proof (proj1 (inv_keys HI2)) as N2.
  assert (N3 : NoDup (keys (upd_meta gm (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser))))) s2)))
    by (rewrite keys_upd_In by exact (MT_Some_In_keys _ _ _ Mg2); exact N2).
  destruct (enframe_inserts [] (Some (gm, idx)) U0 s s2 gm am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser)))
    (padd (slot_start am idx) (UNIT * off)) n HI2 UB2 Mg2 Hidx Glen Hfr eq_refl) as (l1 & l2 & E1 & E2).
  pose proof (band_range n Hn) as BR.
  apply (UPB_step s _ L n (if 1 <=? am_last am then am_sc am else 100) HU HLn ltac:(lia)).
  - apply (bcount_ins s _ (map fst l1) (map fst l2) (padd (slot_start am idx) (UNIT * off)) n).
    + rewrite (user_blocks_ublist _ N3), E1, map_app. reflexivity.
    + rewrite (user_blocks_ublist s N0), E2, map_app. reflexivity.
  - intros c. rewrite (delta_k (am_sc am) (am_last am) (band n) c ltac:(lia)).
    rewrite (upc_ins s2 gm am idx hdr off n c N2 Mg2 Hidx Glen Hfr).
    assert (Eu : upc s2 c = upc s c) by (unfold upc; rewrite (ub_cls_same s s2 c N0 N2 UB2 CL2); reflexivity).
    rewrite Eu. reflexivity.
  - intros Hk Hk48. rewrite Hk in Hk48 |- *. exact (Hco Hk Hk48).
Qed.

Theorem malloc_PK caps L s n (HC : CAPS caps L) (HLn : length L = 49%nat) :
  Inv [] None U0 s -> WI True False False [] None K0 s -> PKS [] s -> PKC [] caps s -> UPB s L -> 0 <= n ->
  itok (malloc n s) (fun r => PKS [] (snd r) /\ PKC [] caps (snd r) /\
    UPB (snd r) (match fst r with Some _ => lv_add L (band n) 1 | None => L end)).
Proof.
intros HI HW HP1 HP2 HU Hn. pose proof (proj1 (inv_keys HI)) as N0. unfold malloc.
destruct (size_overflows n) eqn:Eov.
{ apply itok_ret. cbn [fst snd]. split; [exact HP1 | split; [exact HP2 | exact HU]]. }
destruct (MMAP_THRESHOLD <=? n) eqn:Eth.
-
apply Z.leb_le in Eth.
mbinds. apply itok_ask; [cbn [req_ok]; unfold size_overflows in Eov; apply Z.leb_gt in Eov; unfold IB, UNIT; lia|]. intros z _. msimp.
destruct (z =? 0); cbn [negb].
{ apply itok_ret. cbn [fst snd]. split; [exact HP1 | split; [exact HP2 | exact HU]]. }
mbinds. eapply new_region_spec; [exact HI | | reflexivity | pose proof (page_round_ge (n + IB + UNIT)); unfold IB, UNIT in *; lia]. intros s1 HI1 Es1. msimp.
set (r := length (st_regions s)).
assert (Hr1 : region_of s1 r = Some (mkRegion RkMap (page_round (n + IB + UNIT)) [] true)).
{ rewrite Es1. apply region_of_app_new. }
assert (Em1 : st_metas s1 = st_metas s) by (rewrite Es1; reflexivity).
mbinds. eapply step_seq_spec; [exact HI1|]. intros s2 HI2 (Em2 & Ea2 & Er2 & Eu2 & Ec2 & _). msimp.
assert (Hr2 : region_of s2 r = Some (mkRegion RkMap (page_round (n + IB + UNIT)) [] true)) by (unfold region_of in *; rewrite Er2; exact Hr1).
assert (Em21 : st_metas s2 = st_metas s) by (rewrite Em2; exact Em1).
assert (EU2 : forall q a, usedX [] s2 q a <-> usedX [] s q a) by (intros; unfold usedX, MTX, MT; rewrite Em21; tauto).
assert (FRESH : forall q a, usedX [] s q a -> (prid (am_mem a) < r)%nat).
{ intros q a Hu. exact (used_group_prid_lt _ _ _ _ q a HI Hu). }
pose proof (page_round_ge (n + IB + UNIT)) as PR1. pose proof (page_round_mod (n + IB + UNIT)) as PR2.
pose proof (proj1 (inv_keys HI2)) as N2.
destruct (PK_metas [] s s2 caps Em21 HP1 HP2) as [P21 P22].
mbinds. eapply alloc_meta_spec'; [exact HI2 | |].
+
intros s3 HI3 (Ea3 & Eu3 & Erg3 & Len3 & Ec3) EU3 UB3 RL3 HK3. msimp.
mbinds. apply itok_ask.
{ cbn [req_ok]. exists (mkRegion RkMap (page_round (n + IB + UNIT)) [] true). cbn [rg_kind rg_live rg_len].
split; [apply Erg3; [exact Hr2 | reflexivity]|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [unfold IB, UNIT; lia|].
apply Forall_forall. intros [q a] Hin Hml. cbn [snd] in *.
apply (used_metas_iff s3 q a (proj1 (inv_keys HI3))) in Hin.
assert (Hu : usedX [] s q a) by (apply EU2, EU3; exact Hin).
pose proof (FRESH q a Hu). lia. }
intros z' _. msimp. mbinds.
eapply upd_region_kill_spec; [exact HI3 | apply Erg3; [exact Hr2 | reflexivity] | reflexivity | |].
{ intros q a Hu _. apply EU3, EU2 in Hu. pose proof (FRESH q a Hu). lia. }
intros s4 HI4 Em4 _. msimp. apply itok_ret. cbn [fst snd].
pose proof (proj1 (inv_keys HI3)) as N3. pose proof (proj1 (inv_keys HI4)) as N4.
assert (C3 : corr [] s2 [] s3) by (apply corr_eqv; exact EU3).
destruct (PK_corr _ _ _ _ caps C3 N2 N3 P21 P22) as [P31 P32].
destruct (PK_metas [] s3 s4 caps Em4 P31 P32) as [P41 P42].
split; [exact P41|]. split; [exact P42|].
apply (UPB_same s s4 L N0 N4); [| | exact HU].
* eapply ub_same_trans; [| apply ub_same_metas; exact Em4]. eapply ub_same_trans; [| exact UB3]. apply ub_same_metas. exact Em21.
* exact (CL_trans _ _ _ (CL_metas s s2 Em21) (CL_trans _ _ _ (CL_corr [] s2 [] s3 (inv_X HI2) C3) (CL_metas s3 s4 Em4))).
+
intros g s3 HI3 NX Kg Mg (Ea3 & Eu3 & Erg3 & Len3 & Ec3) EU3 UB3 RL3 HK3. msimp.
pose proof (proj1 (inv_keys HI3)) as N3.
assert (C3 : corr [] s2 [g] s3) by (apply corr_eqv; exact EU3).
destruct (PK_corr _ _ _ _ caps C3 N2 N3 P21 P22) as [P31 P32].
pose proof (CL_trans _ _ _ (CL_metas s s2 Em21) (CL_corr [] s2 [g] s3 (inv_X HI2) C3)) as CL3.
set (maplen := page_round (n + IB + UNIT) / 4096).
assert (Hml : page_round (n + IB + UNIT) = maplen * PGSZ).
{ subst maplen. rewrite Z.mul_comm. unfold PGSZ. pose proof (Z_div_mod_eq_full (page_round (n + IB + UNIT)) 4096). unfold PGSZ in PR2. lia. }
assert (Hml1 : 1 <= maplen) by (clear - Hml PR1 Eth; unfold MMAP_THRESHOLD, PGSZ, IB, UNIT in *; nia).
mbinds. change (mkAMeta None None (SP r 0) 0 0 0 63 (page_round (n + IB + UNIT) / 4096) 0 [slot_zero]) with (direct_am r maplen).
eapply install_direct_spec; [exact HI3 | exact NX | apply Erg3; [exact Hr2 | reflexivity] | reflexivity | reflexivity | exact Hml | exact Hml1 | |].
{ intros q a Hu Hp. apply EU3, EU2 in Hu. pose proof (FRESH q a Hu). lia. }
intros s4 Es4 HI4 U4 UB4. msimp.
assert (PK4 : PKS [] s4 /\ PKC [] caps s4).
{ rewrite Es4. apply (PK_install [] s3 _ g (direct_am r maplen) caps NX N3 Kg (keys_upd_In _ _ _ Kg)).
  - apply MT_upd_same.
  - intros q Hq. apply MT_upd_other. exact Hq.
  - intros i. apply direct_frameless.
  - intros H0. exfalso. change (am_maplen (direct_am r maplen)) with maplen in H0. lia.
  - intros H. exfalso. change (am_sc (direct_am r maplen)) with 63 in H. lia.
  - intros H. exfalso. change (am_sc (direct_am r maplen)) with 63 in H. lia.
  - intros c Hc Hg. exfalso. unfold gfull in Hg. change (am_sc (direct_am r maplen)) with 63 in Hg.
    apply andb_prop in Hg as [Hg _]. apply Z.eqb_eq in Hg. lia.
  - intros c Hc Hg. exfalso. unfold gred in Hg. change (am_sc (direct_am r maplen)) with 63 in Hg.
    apply andb_prop in Hg as [Hg _]. apply Z.eqb_eq in Hg. lia.
  - exact P31.
  - exact P32. }
assert (CL4 : CL s s4).
{ apply (CL_trans _ _ _ CL3). apply (CL_upd_X _ _ g).
  - intros q Hq. rewrite Es4. apply MT_upd_other. exact Hq.
  - intros a Ma. exfalso. destruct Mg as [M|M]; rewrite M in Ma; discriminate. }
assert (UBs4 : ub_same s s4).
{ eapply ub_same_trans; [| exact UB4]. eapply ub_same_trans; [| exact UB3]. apply ub_same_metas. exact Em21. }
mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp.
pose proof (inv_ctx HI4) as (_&_&_&_&_&_&_&_&C9&_).
set (s5 := set_mmap_counter _ s4).
assert (HI5 : Inv [] (Some (g, 0)) U0 s5) by (apply Inv_set_mmap_counter; [exact HI4 | apply land32_range; lia]).
assert (U5 : usedX [] s5 g (direct_am r maplen)) by (unfold usedX, MTX, MT in *; subst s5; cbn; exact U4).
assert (Em54 : st_metas s5 = st_metas s4) by reflexivity.
assert (Hstr : stride_of (direct_am r maplen) = maplen * 4096 - UNIT).
{ unfold stride_of, direct_am. cbn [am_last am_maplen am_sc Z.eqb andb].
destruct (maplen =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
mbinds. eapply (enframe_spec [] U0 s5 g 0 n _ FUser (direct_am r maplen));
[exact HI5 | exact U5 | exact Hn | rewrite Hstr; unfold PGSZ, UNIT, IB in *; lia | apply land32_range; lia | discriminate | auto
| cbn; lia |].
intros off s6 hdr Hoff Hfit _ Es6 HI6. msimp. apply itok_ret. cbn [fst snd]. rewrite Es6.
pose proof (proj1 (inv_keys HI5)) as N5.
destruct PK4 as [P41 P42]. destruct (PK_metas [] s4 s5 caps Em54 P41 P42) as [P51 P52].
assert (Mg5 : MT s5 g = Some (MUsed (direct_am r maplen))) by exact (proj1 (usedX_MT _ _ _ _ U5)).
assert (Kg5 : In g (keys s5)) by exact (MT_Some_In_keys _ _ _ Mg5).
assert (NS0 : forall i, 0 <= i -> nth_slot (upd_slot (direct_am r maplen) 0 (mkSlot (Some hdr) (Some (mkFrame off n FUser)))) i =
  if i =? 0 then mkSlot (Some hdr) (Some (mkFrame off n FUser)) else nth_slot (direct_am r maplen) i).
{ intros i Hi. apply nth_slot_upd_slot; [lia | exact Hi | cbn [am_slots direct_am length Z.to_nat]; lia]. }
assert (PK6 : PKS [] (upd_meta g (MUsed (upd_slot (direct_am r maplen) 0 (mkSlot (Some hdr) (Some (mkFrame off n FUser))))) s5) /\
  PKC [] caps (upd_meta g (MUsed (upd_slot (direct_am r maplen) 0 (mkSlot (Some hdr) (Some (mkFrame off n FUser))))) s5)).
{ apply (PK_upd [] s5 _ g (direct_am r maplen) _ 0 caps U5 N5 (keys_upd_In _ _ _ Kg5) (MT_upd_same _ _ _)
    (fun q Hq => MT_upd_other _ _ _ q Hq)); [reflexivity | reflexivity | reflexivity | reflexivity | | | | exact P51 | exact P52].
  - intros i Hi Hne. rewrite (NS0 i Hi). rewrite (proj2 (Z.eqb_neq i 0) Hne). reflexivity.
  - intros fr _ _ H. exfalso. change (am_sc (direct_am r maplen)) with 63 in H. lia.
  - intros fr Hfr Hk. rewrite (NS0 0 ltac:(lia)), Z.eqb_refl in Hfr. cbn [ss_fr] in Hfr.
    injection Hfr as Hfr. subst fr. discriminate Hk. }
destruct PK6 as [R1 R2]. split; [exact R1|]. split; [exact R2|].
apply (final_UPB s s5 L g (direct_am r maplen) 0 hdr off n HI5 N0); [| | exact HU | exact HLn | exact Hn | exact Mg5
  | change (am_last (direct_am r maplen)) with 0; lia | reflexivity | reflexivity |].
  -- eapply ub_same_trans; [exact UBs4 | apply ub_same_metas; exact Em54].
  -- exact (CL_trans _ _ _ CL4 (CL_metas s4 s5 Em54)).
  -- intros Hk _. change (100 = band n + 1) in Hk. pose proof (band_range n Hn). lia.
-
apply Z.leb_gt in Eth.
pose proof (size_to_class_range n ltac:(lia)) as [Hsc0 Hfit0].
mbinds. apply itok_get. msimp. cbn zeta.
set (sc0 := size_to_class n) in *.
match goal with |- itok (bind (match nth (Z.to_nat ?c) _ _ with _ => _ end) _ _) _ => set (sc := c) end.
assert (Hsc : 0 <= sc < 48 /\ n + IB <= class_size sc /\ (sc = sc0 \/ (sc = sc0 + 1 /\ usage_of s (sc0 + 1) <= 12))).
{ subst sc. destruct (_ && (usage_of s sc0 =? 0)) eqn:E.
- apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [E E32].
apply andb_prop in E as [_ E4]. apply Z.ltb_lt in E32.
destruct (_ <=? 12) eqn:E12; [|split; [exact Hsc0 | split; [exact Hfit0 | left; reflexivity]]].
pose proof (class_size_mono sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). split; [lia|]. split; [lia|]. right. split; [reflexivity|].
apply Z.leb_le in E12. revert E12. match goal with |- context [if ?b then _ else _] => destruct b end; intros E12; lia.
- split; [exact Hsc0 | split; [exact Hfit0 | left; reflexivity]]. }
destruct Hsc as [Hsc [Hfit Hco]]. clearbody sc.
change (nth (Z.to_nat sc) (st_active s) None) with (active_hd s sc).
mbinds.
match goal with |- itok (?mm s) ?K =>
assert (FAST : itok (mm s) (fun r => match fst r with
| None => snd r = s
| Some (gm, idx) => exists am, Inv [] (Some (gm, idx)) U0 (snd r) /\ usedX [] (snd r) gm am /\
n + IB <= stride_of am /\ 0 <= idx <= am_last am /\ am_sc am = sc /\
active_hd (snd r) sc = Some gm /\ ub_same s (snd r) /\ CL s (snd r) /\ PKS [] (snd r) /\ PKC [] caps (snd r) end)) end.
{ destruct (active_hd s sc) as [gm|] eqn:Ehd; [|apply itok_ret; reflexivity].
destruct (head_used _ _ _ _ sc gm HI Hsc Ehd) as (am & Hu & Hsa).
pose proof (usedX_MT _ _ _ _ Hu) as [Mgm NXgm].
mbinds. eapply itok_getm; [exact Mgm|]. msimp.
destruct (am_avail am =? 0) eqn:Eav; [apply itok_ret; reflexivity|]. apply Z.eqb_neq in Eav.
mbinds. apply itok_setm'. msimp. apply itok_ret. cbn [fst snd].
rewrite <- Hsa in Hsc, Ehd.
destruct (take_bit_Inv [] U0 s gm am HI Hu Hsc Ehd Eav) as (Hk & Hfirst & Hbit & HI1).
pose proof (inv_groups HI gm am Hu) as ((_ & Gai & _) & _).
pose proof (RT_setm s gm am (am_set_avail (am_avail am - lowbit (am_avail am)) am) Mgm ltac:(destruct am; reflexivity)) as RT1.
destruct (RT_corr [] s _ RT1) as (C1 & _ & _).
destruct (PK_corr _ _ _ _ caps C1 N0 (proj1 (inv_keys HI1)) HP1 HP2) as [P11 P12].
eexists. split; [exact HI1|]. split; [apply usedX_upd; left; auto|].
split.
{ pose proof (avail_bit_not_undersized [] None U0 s gm am (ctz32 (lowbit (am_avail am))) HI Hu Hsc ltac:(lia)
ltac:(rewrite Z.lor_spec, Hbit; reflexivity)) as Hus.
rewrite Hsa in Hus.
replace (stride_of (am_set_avail (am_avail am - lowbit (am_avail am)) am)) with (stride_of am) by (destruct am; reflexivity). lia. }
split; [cbn [am_last am_set_avail]; lia|]. split; [exact Hsa|]. split; [rewrite <- Hsa; exact Ehd|].
split; [apply ub_same_upd_In; [eapply MT_Some_In_keys; exact Mgm | rewrite Mgm; cbn; apply blocks_of_avail]|].
split; [exact (CL_RT _ _ RT1)|]. split; [exact P11 | exact P12]. }
revert FAST. apply itok_mono. intros [r s1] Hfast. cbn [fst snd] in Hfast. msimp.
mbinds.
match goal with |- itok (?mm s1) ?K =>
assert (SLOW : itok (mm s1) (fun r => match fst r with
| None => Inv [] None U0 (snd r) /\ ub_same s (snd r) /\ CL s (snd r) /\ PKS [] (snd r) /\ PKC [] caps (snd r)
| Some (gm, idx) => exists am, Inv [] (Some (gm, idx)) U0 (snd r) /\ usedX [] (snd r) gm am /\
n + IB <= stride_of am /\ 0 <= idx <= am_last am /\ am_sc am = sc /\
active_hd (snd r) sc = Some gm /\ ub_same s (snd r) /\ CL s (snd r) /\ PKS [] (snd r) /\ PKC [] caps (snd r) end)) end.
{ destruct r as [[gm idx]|].
- apply itok_ret. cbn [fst snd]. exact Hfast.
- subst s1. mbinds.
  assert (T : itok (alloc_slot NEST_FUEL sc n s) (fun r => slot_post [] U0 s sc n r /\ PX [] caps s (snd r) sc)).
  { apply itok_conj.
    - destruct (alloc_mutual NEST_FUEL) as [AS _].
      eapply AS; [exact HI | exact Hsc | exact Hn | exact Hfit | apply need_le_fuel; lia | intros r Hr; exact Hr].
    - destruct (pack_mutual caps L HC NEST_FUEL) as [AS _].
      eapply AS; [exact HI | exact HW | exact HP1 | exact HP2 | exact HU | exact Hsc | exact Hn | exact Hfit | apply need_le_fuel; lia | intros r Hr; exact Hr]. }
  revert T. apply itok_mono. intros [idx s2] [[_ [UB2 Hpost]] (Q1 & Q2 & Q3 & _)]. cbn [fst snd] in Hpost, UB2, Q1, Q2, Q3. msimp.
  destruct Hpost as [[-> HI2] | (Hidx & g & am & HI2 & Hhd2 & U2 & Sc2 & Str2 & Hlast)].
  + cbn. split; [exact HI2|]. split; [exact UB2|]. split; [exact Q3|]. split; [exact Q1 | exact Q2].
  + destruct (idx <? 0) eqn:E; [apply Z.ltb_lt in E; lia|].
    mbinds. apply itok_get_head. msimp. change (nth (Z.to_nat sc) (st_active s2) None) with (active_hd s2 sc). rewrite Hhd2.
    apply itok_ret. cbn [fst snd]. exists am. repeat (split; [assumption|]). split; [lia|]. split; [exact Sc2|].
    split; [exact Hhd2|]. split; [exact UB2|]. split; [exact Q3|]. split; [exact Q1 | exact Q2]. }
revert SLOW. apply itok_mono. intros [gi s2] Hslow. cbn [fst snd] in Hslow. msimp.
destruct gi as [[gm idx]|].
2:{ apply itok_ret. cbn [fst snd]. destruct Hslow as (HI2 & UB2 & CL2 & P1 & P2).
    split; [exact P1|]. split; [exact P2|]. exact (UPB_same s s2 L N0 (proj1 (inv_keys HI2)) UB2 CL2 HU). }
destruct Hslow as (am & HI2 & U2 & Str2 & Hidx & Sc2 & Hhd2 & UB2 & CL2 & P1 & P2).
mbinds. apply itok_get. msimp.
pose proof (inv_ctx HI2) as (_&_&_&_&_&_&_&_&C9&_).
assert (H63 : am_sc am <> 63) by lia.
mbinds. eapply (enframe_spec [] U0 s2 gm idx n (st_mmap_counter s2) FUser am);
[exact HI2 | exact U2 | exact Hn | unfold IB in *; lia | lia | discriminate | intros H; exfalso; exact (H63 H)
| intros _ _; rewrite Sc2; exact Hhd2 |].
intros off s3 hdr Hoff Hofit _ Es3 HI3. msimp. apply itok_ret. cbn [fst snd]. rewrite Es3.
pose proof (inv_groups HI2 gm am U2) as ((_ & _ & Glen & _) & _).
destruct (inv_reserved HI2 gm idx eq_refl) as (am_ & U_ & _ & Hfr_ & _). pose proof (usedX_fun _ _ _ _ _ U_ U2) as E_. rewrite E_ in Hfr_.
pose proof (upd_slot_fields am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser)))) as (Fm & Fl & Fsc & Fml & Fst & _).
pose proof (proj1 (inv_keys HI2)) as N2.
assert (Mg2 : MT s2 gm = Some (MUsed am)) by exact (proj1 (usedX_MT _ _ _ _ U2)).
assert (Kg : In gm (keys s2)) by exact (MT_Some_In_keys _ _ _ Mg2).
assert (NSi : forall i, 0 <= i -> nth_slot (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser)))) i =
  if i =? idx then mkSlot (Some hdr) (Some (mkFrame off n FUser)) else nth_slot am i).
{ intros i Hi. apply nth_slot_upd_slot; [lia | exact Hi | rewrite Glen; lia]. }
assert (PK3 : PKS [] (upd_meta gm (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser))))) s2) /\
  PKC [] caps (upd_meta gm (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser))))) s2)).
{ apply (PK_upd [] s2 _ gm am _ idx caps U2 N2 (keys_upd_In _ _ _ Kg) (MT_upd_same _ _ _)
    (fun q Hq => MT_upd_other _ _ _ q Hq) Fsc Fl Fm Fml); [| | | exact P1 | exact P2].
  - intros i Hi Hne. rewrite (NSi i Hi). rewrite (proj2 (Z.eqb_neq i idx) Hne). reflexivity.
  - intros fr Hfr _ _. rewrite (NSi idx ltac:(lia)), Z.eqb_refl in Hfr. cbn [ss_fr] in Hfr. injection Hfr as Hfr. subst fr.
    cbn [fr_n]. split; [lia|]. rewrite Sc2. change (size_to_class n) with sc0. destruct Hco as [->|[-> _]]; lia.
  - intros fr Hfr Hk. rewrite (NSi idx ltac:(lia)), Z.eqb_refl in Hfr. cbn [ss_fr] in Hfr. injection Hfr as Hfr. subst fr.
    discriminate Hk. }
destruct PK3 as [R1 R2]. split; [exact R1|]. split; [exact R2|].
apply (final_UPB s s2 L gm am idx hdr off n HI2 N0 UB2 CL2 HU HLn Hn Mg2 Hidx Glen Hfr_).
intros Hk Hk48.
assert (Bn : band n = sc0) by (unfold band; rewrite (proj2 (Z.leb_gt MMAP_THRESHOLD n)) by lia; reflexivity).
destruct (Z.le_gt_cases 1 (am_last am)) as [EL|EL].
+ rewrite (proj2 (Z.leb_le 1 (am_last am)) EL) in Hk. change (am_sc am = band n + 1) in Hk.
  rewrite Bn in Hk |- *. rewrite Sc2 in Hk. destruct Hco as [Hc|[Hc Hu12]]; [lia|].
  pose proof (upc_le s (sc0 + 1)). pose proof (ub_cls_len None s (sc0 + 1) HI ltac:(lia)). lia.
+ rewrite (proj2 (Z.leb_gt 1 (am_last am)) EL) in Hk. change (100 = band n + 1) in Hk. pose proof (band_range n Hn). lia.
Qed.

Theorem malloc_pack : forall s n caps L tr r s',
  WF s -> SI s -> GS s -> NL s -> noraw s -> PKS [] s -> PKC [] caps s -> UPB s L ->
  length caps = 49%nat -> length L = 49%nat -> (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps) ->
  0 <= n -> yields (malloc n s) tr (r, s') ->
  PKS [] s' /\ PKC [] caps s' /\ UPB s' (match r with Some _ => lv_add L (band n) 1 | None => L end).
Proof.
  intros s n caps L tr r s' HW HS HG HN HR HP1 HP2 HU Hcl HLn HL Hn Hy.
  assert (WI0 : WI True False False [] None K0 s) by (apply WI_of; [intros _; exact HS | intros [] | intros []]).
  exact (itok_yields _ _ tr (r, s') (malloc_PK caps L s n HL HLn HW WI0 HP1 HP2 HU Hn) Hy).
Qed.
