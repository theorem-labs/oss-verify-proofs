(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YO0v.v; 226 of its 364 lines of code are new or changed and 832 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0g YO0h YO0w YO0s YO11 YO15 YO12 YO0z YO14 YO0u YO0q YO0v YO0y YO03 YO0m YO0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocSI AllocGS AllocMalloc AllocCount AllocPack AllocPackMallocN AllocPackMallocW AllocPackMallocC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Definition PX (X : list sptr) (caps : list Z) (s s' : astate) (sc : Z) : Prop :=
  PKS X s' /\ PKC X caps s' /\ CL s s' /\ (forall c, 0 <= c < sc -> usage_of s' c = usage_of s c).

Definition CAPS (caps L : list Z) : Prop := forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps.

Lemma usage_nonneg X R U s c : Inv X R U s -> 0 <= usage_of s c.
Proof.
  intros HI. pose proof (inv_ctx HI) as (_ & _ & _ & _ & C5 & _). unfold usage_of, znth.
  destruct (nth_in_or_default (Z.to_nat c) (st_usage s) 0) as [H|H]; [apply C5; exact H | rewrite H; lia].
Qed.

Lemma keys_ig m sc cnt aidx maplen mem sl s : In m (keys s) -> keys (ig_st m sc cnt aidx maplen mem sl s) = keys s.
Proof.
  intros H. unfold ig_st, set_head_st. change (keys (set_active ?l ?st)) with (keys st).
  rewrite keys_upd_In by (rewrite keys_upd_In; exact H). rewrite keys_upd_In by exact H. reflexivity.
Qed.

Theorem pack_mutual caps L (HC : CAPS caps L) fuel :
  (forall X s sc req (Q : Z * astate -> Prop),
    Inv X None U0 s -> WI True False False X None K0 s -> PKS X s -> PKC X caps s -> UPB s L ->
    0 <= sc < 48 -> 0 <= req -> req + IB <= class_size sc -> (need sc <= fuel)%nat ->
    (forall r, PX X caps s (snd r) sc -> Q r) -> itok (alloc_slot fuel sc req s) Q) /\
  (forall X s sc req (Q : option sptr * astate -> Prop),
    Inv X None U0 s -> WI True False False X None K0 s -> PKS X s -> PKC X caps s -> UPB s L ->
    0 <= sc < 48 -> 0 <= req -> req + IB <= class_size sc -> (need sc <= S fuel)%nat -> active_hd s sc = None ->
    (forall r, PX X caps s (snd r) sc -> Q r) -> itok (alloc_group fuel sc req s) Q).
Proof.
induction fuel as [|f [IHs IHg]].
{ split; intros X s sc req Q HI HW HP1 HP2 HU Hsc Hreq Hfit Hf; pose proof (need_ge2 sc); lia. }
split.
-
intros X s sc req Q HI HW HP1 HP2 HU Hsc Hreq Hfit Hf HQ.
pose proof (proj1 (inv_keys HI)) as N0.
cbn fix beta iota delta [alloc_slot]. mbinds.
apply (itok_lw _ _ _ (try_avail_RT FA sc s)).
eapply try_avail_spec; [exact HI | exact Hsc | |].
+ intros s1 HI1 Hhd1 EH1 UB1 RT1. cbn [snd] in RT1. msimp. cbn [Z.eqb negb].
  pose proof (proj1 (inv_keys HI1)) as N1.
  destruct (RT_corr X s s1 RT1) as (C1 & RL1 & HK1).
  pose proof (WI_corr _ _ _ _ _ _ _ _ _ C1 RL1 HK1 HW) as HW1.
  destruct (PK_corr X s X s1 caps C1 N0 N1 HP1 HP2) as [P1 P2].
  pose proof (CL_RT s s1 RT1) as CL1.
  pose proof (UPB_same s s1 L N0 N1 UB1 CL1 HU) as HU1.
  mbinds.
  eapply IHg; [exact HI1 | exact HW1 | exact P1 | exact P2 | exact HU1 | exact Hsc | exact Hreq | exact Hfit | exact Hf | exact Hhd1 |].
  intros [og s2] (Q1 & Q2 & Q3 & Q4). msimp. cbn [snd] in Q1, Q2, Q3, Q4.
  destruct og as [g|]; apply itok_ret; apply HQ; cbn [snd]; (split; [exact Q1|]); (split; [exact Q2|]);
  (split; [exact (CL_trans _ _ _ CL1 Q3)|]); intros c Hc; rewrite (Q4 c Hc);
  exact (usage_RT X None None U0 s s1 c HI HI1 RT1 ltac:(lia)).
+ intros first s1 (Hnz & g & am & HI1 & Hhd1 & U1 & Sc1 & Str1 & Hidx & EH1 & UB1) RT1. cbn [snd] in RT1. msimp.
  pose proof (proj1 (inv_keys HI1)) as N1.
  destruct (RT_corr X s s1 RT1) as (C1 & RL1 & HK1).
  destruct (PK_corr X s X s1 caps C1 N0 N1 HP1 HP2) as [P1 P2].
  destruct (first =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|]. cbn [negb].
  apply itok_ret. apply HQ. cbn [snd]. split; [exact P1|]. split; [exact P2|]. split; [exact (CL_RT s s1 RT1)|].
  intros c Hc. exact (usage_RT X None _ U0 s s1 c HI HI1 RT1 ltac:(lia)).
-
intros X s sc req Q HI HW HP1 HP2 HU Hsc Hreq Hfit Hf Hhd HQ.
pose proof (class_size_bounds sc Hsc) as [S16 Smax].
pose proof (proj1 (inv_keys HI)) as N0.
cbn fix beta iota delta [alloc_group]. mbinds.
eapply alloc_meta_spec'; [exact HI | |].
{ intros s1 HI1 Fr1 EU1 UB1 RL1 HK1. msimp. apply itok_ret. apply HQ. cbn [snd].
  pose proof (proj1 (inv_keys HI1)) as N1. assert (C1 : corr X s X s1) by (apply corr_eqv; exact EU1).
  destruct (PK_corr _ _ _ _ caps C1 N0 N1 HP1 HP2) as [P1 P2].
  split; [exact P1|]. split; [exact P2|]. split; [exact (CL_corr X s X s1 (inv_X HI) C1)|].
  intros c Hc. destruct Fr1 as (_ & EUs & _). unfold usage_of. rewrite EUs. reflexivity. }
intros m s1 HI1 NX Km Mm Fr1 EU1 UB1 RL1 HK1. msimp. mbinds. apply itok_get. msimp. cbn zeta.
pose proof (proj1 (inv_keys HI1)) as N1.
assert (C1 : corr X s (m :: X) s1) by (apply corr_eqv; exact EU1).
assert (HW1 : WI True False False (m :: X) None K0 s1) by (eapply WI_corr; [exact C1 | exact RL1 | exact HK1 | exact HW]).
destruct (PK_corr _ _ _ _ caps C1 N0 N1 HP1 HP2) as [P1 P2].
pose proof (CL_corr X s (m :: X) s1 (inv_X HI) C1) as CL1.
pose proof (UPB_same s s1 L N0 N1 UB1 CL1 HU) as HU1.
pose proof Fr1 as (EA1 & EUs1 & _ & Len1 & Emc1).
assert (Hhd1 : active_hd s1 sc = None) by (unfold active_hd; rewrite EA1; exact Hhd).
assert (Us1 : forall c, usage_of s1 c = usage_of s c) by (intros c; unfold usage_of; rewrite EUs1; reflexivity).
destruct (proj1 HW1 I) as (_ & _ & _ & CO1 & _).
assert (HRn : forall g i am, (None : option (sptr * Z)) = Some (g, i) -> usedX (m :: X) s1 g am -> am_sc am <> sc) by (intros; discriminate).
pose proof (usage_nonneg _ _ _ _ sc HI1) as Hu0.
pose proof (usage_nonneg _ _ _ _ (sc + 1) HI1) as Hu1.
pose proof (initial_cnt_facts sc (usage_of s1 sc) Hsc) as (Hc0 & Hc0s & Hc026).
pose proof (init_le sc (usage_of s1 sc) Hsc Hu0) as Hle0.
pose proof (init_big sc (usage_of s1 sc)) as Hbig.
pose proof (mmap_cnt s1 sc req (usage_of s1 sc) Hsc Hu0) as MC.
assert (MF : 128 <= usage_of s1 sc -> fst (mmap_plan s1 sc req (initial_cnt sc (usage_of s1 sc)) (usage_of s1 sc)) = FC sc).
{ intros H. rewrite (init_big sc _ H). apply mmap_full; [exact Hsc | exact H | exact Hu1]. }
set (cnt0 := initial_cnt sc (usage_of s1 sc)) in *.
assert (FRESH : forall q a, usedX (m :: X) s1 q a -> (prid (am_mem a) < length (st_regions s1))%nat).
{ intros q a Hu. apply EU1 in Hu. pose proof (used_group_prid_lt _ _ _ _ q a HI Hu). lia. }
destruct (PGSZ / 2 <? class_size sc * cnt0 + UNIT) eqn:Ebr.
+
pose proof (mmap_plan_len_bound s1 sc req cnt0 (usage_of s1 sc) ltac:(unfold IB in Hfit; lia) ltac:(lia)) as PB.
destruct (mmap_plan s1 sc req cnt0 (usage_of s1 sc)) as [cnt needed] eqn:Ep. cbn [fst snd].
rewrite ?Ep in PB, MC, MF. cbn [fst snd] in PB, MC, MF.
pose proof (mmap_plan_facts s1 sc req cnt0 (usage_of s1 sc) cnt needed Hsc Hc0 Hc0s Hreq Hfit Hc026 Ep)
as (Hcnt & Hcs & Hc26 & Nmod & N4096 & Nmax & Nfit & Nreq & Npr).
mbinds. apply (itok_lw _ _ _ (account_bounce_lw FA sc s1)).
eapply account_bounce_spec; [exact HI1|]. intros s2 HI2 (Em2 & Ea2 & Er2 & Eu2 & Ec2 & _) NM2. cbn [snd] in NM2. msimp.
mbinds. apply (itok_lw _ _ _ (step_seq_lw FA s2)).
eapply step_seq_spec; [exact HI2|]. intros s3 HI3 (Em3 & Ea3 & Er3 & Eu3 & Ec3 & _) NM3. cbn [snd] in NM3. msimp.
mbinds. apply itok_ask; [cbn; unfold PGSZ in N4096; clear - N4096 Nmax; lia|]. intros z _. msimp.
assert (EU3 : forall q a, usedX (m :: X) s3 q a <-> usedX (m :: X) s1 q a).
{ intros q a. unfold usedX, MTX, MT. rewrite Em3, Em2. tauto. }
assert (Em31 : st_metas s3 = st_metas s1) by (rewrite Em3, Em2; reflexivity).
destruct (z =? 0); cbn [negb].
*
mbinds. eapply free_meta_spec; [exact HI3 | left; reflexivity |]. intros s4 HI4 Sb4 Ea4 EU4 UB4. msimp.
apply itok_ret. apply HQ. cbn [snd]. rewrite (remove_head_notin m X NX) in EU4, HI4.
pose proof (proj1 (inv_keys HI3)) as N3. pose proof (proj1 (inv_keys HI4)) as N4.
assert (C4 : corr (m :: X) s3 X s4) by (apply corr_eqv; exact EU4).
destruct (PK_metas (m :: X) s1 s3 caps Em31 P1 P2) as [P31 P32].
destruct (PK_corr _ _ _ _ caps C4 N3 N4 P31 P32) as [P41 P42].
split; [exact P41|]. split; [exact P42|].
split; [exact (CL_trans _ _ _ CL1 (CL_trans _ _ _ (CL_metas s1 s3 Em31) (CL_corr _ _ _ _ (inv_X HI3) C4)))|].
intros c Hc. rewrite (sbmh_usage_of _ _ c Sb4). rewrite <- (Us1 c). unfold usage_of. rewrite Eu3, Eu2. reflexivity.
*
rewrite (page_round_fixed needed Nmod) in PB |- *.
mbinds. eapply new_region_spec; [exact HI3 | | reflexivity | unfold PGSZ in N4096; lia]. intros s4 HI4 Es4. msimp.
mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp.
set (r := length (st_regions s3)).
set (s5 := set_mmap_counter (Z.land (st_mmap_counter s4 + 1) (2 ^ 32 - 1)) s4).
pose proof (inv_ctx HI4) as (_&_&_&_&_&_&_&_&C9&_).
assert (HI5 : Inv (m :: X) None U0 s5) by (apply Inv_set_mmap_counter; [exact HI4 | apply land32_range; lia]).
assert (EU5 : forall q a, usedX (m :: X) s5 q a <-> usedX (m :: X) s1 q a).
{ intros q a. rewrite <- EU3. unfold usedX, MTX, MT. subst s5 s4. cbn. tauto. }
assert (Em51 : st_metas s5 = st_metas s1) by (subst s5; rewrite Es4; cbn [st_metas set_mmap_counter set_regions]; exact Em31).
assert (Hr5 : region_of s5 r = Some (mkRegion RkMap needed [] true)).
{ subst s5 s4 r. unfold region_of. cbn [st_regions set_mmap_counter set_regions]. apply region_of_app_new. }
set (aidx := if (if cnt - 1 <? (4096 - UNIT) / class_size sc - 1 then cnt - 1 else (4096 - UNIT) / class_size sc - 1) <? 0 then 0
else if cnt - 1 <? (4096 - UNIT) / class_size sc - 1 then cnt - 1 else (4096 - UNIT) / class_size sc - 1).
assert (Haidx : 0 <= aidx <= cnt - 1).
{ subst aidx. destruct (cnt - 1 <? (4096 - UNIT) / class_size sc - 1) eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1];
(destruct (_ <? 0) eqn:E2; [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]); lia. }
assert (Hml : 1 <= needed / 4096).
{ apply Z.div_le_lower_bound; unfold PGSZ in *; lia. }
assert (Hml' : needed / 4096 * 4096 = needed).
{ pose proof (Z_div_mod_eq_full needed 4096). unfold PGSZ in Nmod. lia. }
assert (Hhd5 : active_hd s5 sc = None).
{ unfold active_hd. subst s5 s4. cbn [st_active set_mmap_counter set_regions]. rewrite Ea3, Ea2. exact Hhd1. }
assert (Km5 : In m (keys s5)).
{ apply MT_Some_In_keys with (x := match MT s1 m with Some x => x | None => MRaw end).
unfold MT in *. subst s5. rewrite Es4. cbn [st_metas set_mmap_counter set_regions]. rewrite Em3, Em2.
destruct Mm as [M|M]; rewrite M; reflexivity. }
mbinds.
apply (itok_lw _ _ _ (install_group_lw FA m sc cnt aidx (needed / 4096) (SP r 0) slot_zero s5 Hhd5)).
eapply (install_group_spec X U0 s5 m sc cnt aidx (needed / 4096) (SP r 0) slot_zero).
-- exact HI5.
-- exact NX.
-- exact Hsc.
-- exact Hcnt.
-- exact Haidx.
-- lia.
-- exact Hhd5.
-- left. split; [reflexivity | lia].
--
right. cbn [am_sc am_last am_maplen new_am]. rewrite new_am_stride.
split; [exact Hsc|]. split; [|split].
++ intros Hlt. destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)) eqn:E.
** apply andb_prop in E as [E _]. apply Z.eqb_eq in E. split; [exact E|]. rewrite new_am_allocated by lia. reflexivity.
** lia.
++ intros H26. right. specialize (Hc26 H26). lia.
++ destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)) eqn:E.
** apply andb_prop in E as [E _]. apply Z.eqb_eq in E. rewrite E. unfold UNIT. lia.
** replace (cnt - 1 + 1) with cnt by lia. exact Hcs.
--
intros _. exists r, (mkRegion RkMap needed [] true). cbn [am_mem am_maplen am_last new_am rg_kind rg_live rg_len].
split; [reflexivity|]. split; [exact Hr5|]. split; [reflexivity|]. split; [reflexivity|].
rewrite new_am_stride. unfold PGSZ. split; [lia|]. split.
{ destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)) eqn:E.
++ apply andb_prop in E as [E _]. apply Z.eqb_eq in E. rewrite E. unfold UNIT. lia.
++ destruct (Z.eq_dec cnt 1) as [->|Hne1].
{ exfalso. cbn [Z.sub Z.eqb] in E. destruct (needed / 4096 =? 0) eqn:E2; [apply Z.eqb_eq in E2; lia | discriminate]. }
replace (cnt - 1 + 1) with cnt by lia. specialize (Nfit ltac:(lia)). lia. }
cbn [am_sc new_am]. intros Hl0 _. specialize (Npr ltac:(lia)). unfold PGSZ in Npr |- *. lia.
-- intros H0. lia.
-- intros q a Hu Hp. exfalso. apply EU5 in Hu. pose proof (FRESH q a Hu). cbn [prid] in Hp. rewrite <- Er2, <- Er3 in H. subst r. clear - H Hp. lia.
-- intros _ q a Hu _ Hp. apply EU5 in Hu. pose proof (FRESH q a Hu). cbn [prid] in Hp. rewrite <- Er2, <- Er3 in H. subst r. clear - H Hp. lia.
-- intros s6 HI6 Hhd6 U6 EH6 Er6 Ec6 UB6 Es6. cbn [snd] in Es6. msimp. apply itok_ret. apply HQ. cbn [snd]. rewrite Es6.
pose proof (proj1 (inv_keys HI5)) as N5.
destruct (PK_metas (m :: X) s1 s5 caps Em51 P1 P2) as [P51 P52].
assert (MT51 : MT s5 m = MT s1 m) by (unfold MT; rewrite Em51; reflexivity).
set (a1 := am_set_links (Some m) (Some m) (new_am (SP r 0) sc cnt aidx (needed / 4096) slot_zero)).
assert (PKI : PKS X (ig_st m sc cnt aidx (needed / 4096) (SP r 0) slot_zero s5) /\
  PKC X caps (ig_st m sc cnt aidx (needed / 4096) (SP r 0) slot_zero s5)).
{ apply (PK_install X s5 _ m a1 caps NX N5 Km5 (keys_ig _ _ _ _ _ _ _ _ Km5)).
  - rewrite MT_ig, sptr_eqb_refl. reflexivity.
  - intros q Hq. rewrite MT_ig. apply sptr_eqb_neq in Hq. rewrite Hq. reflexivity.
  - intros i. apply ig_frameless. reflexivity.
  - intros H0. exfalso. unfold a1 in H0. cbn [am_maplen am_set_links new_am] in H0. lia.
  - intros _. unfold a1. cbn [am_sc am_last am_set_links new_am]. lia.
  - intros _ _. unfold a1. cbn [am_sc am_set_links new_am]. apply (nestF_false sc cnt0 Hsc); [lia | apply Z.ltb_lt; exact Ebr].
  - intros c Hc Hg. unfold a1, gfull in Hg. cbn [am_sc am_last am_set_links new_am] in Hg.
    apply andb_prop in Hg as [G1 G2]. apply Z.eqb_eq in G1. subst c.
    rewrite (gcount_metas (m :: X) s1 s5 _ Em51). exact (count_full (m :: X) None s1 caps L sc HI1 HRn Hhd1 CO1 P1 P2 HU1 HC Hsc).
  - intros c Hc Hg. unfold a1, gred in Hg. cbn [am_sc am_last am_set_links new_am] in Hg.
    apply andb_prop in Hg as [G1 G2]. apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. subst c.
    assert (Hlow : usage_of s1 sc < 128).
    { destruct (Z.lt_ge_cases (usage_of s1 sc) 128) as [H|H]; [exact H|]. exfalso. specialize (MF H). lia. }
    rewrite (gcount_metas (m :: X) s1 s5 _ Em51). pose proof (count_red (m :: X) None s1 sc HI1 Hsc). unfold RED. lia.
  - exact P51.
  - exact P52. }
destruct PKI as [R1 R2]. split; [exact R1|]. split; [exact R2|]. split.
{ apply (CL_trans _ _ _ CL1). apply (CL_trans _ _ _ (CL_metas s1 s5 Em51)). apply (CL_upd_X _ _ m).
  - intros q Hq. rewrite MT_ig. apply sptr_eqb_neq in Hq. rewrite Hq. reflexivity.
  - intros a Ma. exfalso. rewrite MT51 in Ma. destruct Mm as [M|M]; rewrite M in Ma; discriminate. }
intros c Hc. rewrite usage_ig by lia. rewrite <- (Us1 c). unfold usage_of. subst s5. rewrite Es4.
cbn [st_usage set_mmap_counter set_regions]. rewrite Eu3, Eu2. reflexivity.
+
apply Z.ltb_ge in Ebr.
pose proof (nested_facts sc cnt0 Hsc ltac:(lia) Hc026 Ebr) as NF. cbv zeta in NF.
destruct NF as (H23 & Hc2 & Htot & Hj & Hj48 & Hjfit & Hjlt).
set (total := UNIT + cnt0 * class_size sc - IB) in *. set (j := size_to_class total) in *.
mbinds.
assert (T : itok (alloc_slot f j total s1)
  (fun r => slot_post' True False False (m :: X) U0 s1 j total r /\ PX (m :: X) caps s1 (snd r) j)).
{ apply itok_conj.
  - eapply (proj1 (alloc_mutual' True False False f)); [exact HI1 | exact HW1 | exact Hj48 | lia | exact Hjfit | | intros r Hr; exact Hr].
    pose proof (need_nested sc j H23 ltac:(lia)). lia.
  - eapply IHs; [exact HI1 | exact HW1 | exact P1 | exact P2 | exact HU1 | exact Hj48 | lia | exact Hjfit | | intros r Hr; exact Hr].
    pose proof (need_nested sc j H23 ltac:(lia)). lia. }
revert T. apply itok_mono. intros [idx s2] [[[HB2 [UB2 Hpost]] HW2] (Q1 & Q2 & Q3 & Q4)]. msimp.
cbn [fst snd] in HB2, UB2, Hpost, HW2, Q1, Q2, Q3, Q4.
destruct (idx <? 0) eqn:Eneg.
*
apply Z.ltb_lt in Eneg. destruct Hpost as [[_ HI2] | [Hge _]]; [|cbn [fst] in Hge; lia]. cbn [snd] in HI2.
mbinds. eapply free_meta_spec; [exact HI2 | left; reflexivity |]. intros s3 HI3 Sb3 Ea3 EU3 UB3. msimp.
apply itok_ret. apply HQ. cbn [snd]. rewrite (remove_head_notin m X NX) in EU3, HI3.
pose proof (proj1 (inv_keys HI2)) as N2. pose proof (proj1 (inv_keys HI3)) as N3.
assert (C3 : corr (m :: X) s2 X s3) by (apply corr_eqv; exact EU3).
destruct (PK_corr _ _ _ _ caps C3 N2 N3 Q1 Q2) as [P31 P32].
split; [exact P31|]. split; [exact P32|].
split; [exact (CL_trans _ _ _ CL1 (CL_trans _ _ _ Q3 (CL_corr _ _ _ _ (inv_X HI2) C3)))|].
intros c Hc. rewrite (sbmh_usage_of _ _ c Sb3), (Q4 c ltac:(lia)). apply Us1.
* apply Z.ltb_ge in Eneg. destruct Hpost as [[Hm1 _] | [_ (g & am & HI2 & Hhd2 & U2 & Sc2 & Str2 & Hidx2)]]; [cbn [fst] in Hm1; lia|].
cbn [fst snd] in HI2, Hhd2, U2, Hidx2, HB2.
destruct HW2 as [[Hm1 _] | [_ (g' & Hhd2' & HW2)]]; [lia|]. rewrite Hhd2 in Hhd2'. injection Hhd2' as <-.
pose proof (proj1 (inv_keys HI2)) as N2.
destruct (proj1 HW2 I) as (_ & _ & _ & CO2 & _).
pose proof (UPB_same s1 s2 L N1 N2 UB2 Q3 HU1) as HU2.
assert (Hhd2s : active_hd s2 sc = None) by (rewrite (HB2 sc ltac:(lia)); exact Hhd1).
assert (HR2 : forall g0 i0 am0, Some (g, idx) = Some (g0, i0) -> usedX (m :: X) s2 g0 am0 -> am_sc am0 <> sc).
{ intros g0 i0 am0 E U0'. injection E as E1 E2. subst g0. rewrite (usedX_fun _ _ _ _ _ U0' U2). lia. }
pose proof (count_full (m :: X) (Some (g, idx)) s2 caps L sc HI2 HR2 Hhd2s CO2 Q1 Q2 HU2 HC Hsc) as CF2.
pose proof (count_red (m :: X) (Some (g, idx)) s2 sc HI2 Hsc) as CR2.
rewrite (Q4 sc ltac:(lia)) in CR2.
mbinds. apply itok_get_head. msimp. change (nth (Z.to_nat j) (st_active s2) None) with (active_hd s2 j). rewrite Hhd2. msimp.
pose proof (inv_groups HI2 g am U2) as G2. pose proof G2 as ((_ & _ & Glen & _) & Gml & _ & Gcl & _).
assert (Hstr : stride_of am = class_size j).
{ destruct Gcl as [(C63 & _) | (_ & _ & C26 & _)]; [lia|]. specialize (C26 ltac:(lia)).
unfold stride_of. rewrite Sc2. destruct C26 as [C|C]; [rewrite C|].
- destruct (am_last am =? 0); reflexivity.
- destruct (am_last am =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
mbinds. eapply itok_getm; [exact (proj1 (usedX_MT _ _ _ _ U2))|]. msimp.
mbinds. apply itok_mcheck; [rewrite Hstr; apply Z.eqb_refl|]. msimp.
mbinds. apply itok_get. msimp.
pose proof (inv_ctx HI2) as (_&_&_&_&_&_&_&_&C9&_).
mbinds. eapply (enframe_spec (m :: X) U0 s2 g idx (class_size j - IB) (st_mmap_counter s2) FGroup am);
[exact HI2 | exact U2 | pose proof (class_size_bounds j Hj48); unfold IB; lia | rewrite Hstr; lia | lia | intros _; rewrite Hstr; reflexivity | intros H63; exfalso; lia
| intros _ _; rewrite Sc2; exact Hhd2 |].
intros off s3 hdr Hoff Hofit Hoff0 Es3 HI3. msimp. specialize (Hoff0 eq_refl). subst off. rewrite Z.mul_0_r, padd_0.
set (am' := upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame 0 (class_size j - IB) FGroup)))) in Es3.
pose proof (upd_slot_fields am idx (mkSlot (Some hdr) (Some (mkFrame 0 (class_size j - IB) FGroup)))) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold am' in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
assert (U3 : usedX (m :: X) s3 g am').
{ rewrite Es3. apply usedX_upd. left. pose proof (usedX_MT _ _ _ _ U2) as [_ NXg]. auto. }
assert (Hext1 : group_extent (new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk) = total).
{ unfold group_extent. rewrite new_am_stride. cbn [am_last new_am Z.eqb andb negb].
destruct (cnt0 - 1 =? 0); cbn [andb]; subst total; (replace (cnt0 - 1 + 1) with cnt0 by lia); lia. }
assert (Hhd3 : active_hd s3 sc = None).
{ rewrite Es3. unfold active_hd. cbn. pose proof (HB2 sc ltac:(lia)) as E. unfold active_hd in E. rewrite E, EA1. exact Hhd. }
assert (Hgm : g <> m).
{ intros ->. pose proof (usedX_MT _ _ _ _ U2) as [_ NXg]. rewrite memb_cons, sptr_eqb_refl in NXg. discriminate. }
assert (Km3 : In m (keys s3)).
{ rewrite Es3, keys_upd_In by (eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ U2))).
pose proof (inv_X HI2 m (or_introl eq_refl)) as [K _]. exact K. }
pose proof (proj1 (inv_keys HI3)) as N3.
assert (K32 : keys s3 = keys s2) by (rewrite Es3; apply keys_upd_In; eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ U2))).
assert (M3g : MT s3 g = Some (MUsed am')) by (rewrite Es3; apply MT_upd_same).
assert (M3o : forall q, q <> g -> MT s3 q = MT s2 q) by (intros q Hq; rewrite Es3; apply MT_upd_other; exact Hq).
destruct (inv_reserved HI2 g idx eq_refl) as (am_ & U_ & _ & Hfr_ & _). pose proof (usedX_fun _ _ _ _ _ U_ U2) as E_. rewrite E_ in Hfr_.
assert (NS' : nth_slot am' idx = mkSlot (Some hdr) (Some (mkFrame 0 (class_size j - IB) FGroup))).
{ unfold am'. rewrite nth_slot_upd_slot by (try lia; rewrite Glen; lia). rewrite Z.eqb_refl. reflexivity. }
assert (SS' : slot_start am' idx = slot_start am idx) by (unfold slot_start; rewrite Fst, Fm; reflexivity).
assert (PK3 : PKS (m :: X) s3 /\ PKC (m :: X) caps s3).
{ apply (PK_upd (m :: X) s2 s3 g am am' idx caps U2 N2 K32 M3g M3o Fsc Fl Fm Fml); [| | | exact Q1 | exact Q2].
  - intros i Hi Hne. unfold am'. rewrite nth_slot_upd_slot by (try lia; rewrite Glen; lia).
    rewrite (proj2 (Z.eqb_neq i idx) Hne). reflexivity.
  - intros fr Hfr Hk. rewrite NS' in Hfr. cbn [ss_fr] in Hfr. injection Hfr as Hfr. subst fr. discriminate Hk.
  - intros fr _ _ c0 ac Uc Hml Hmem. exfalso.
    pose proof (inv_groups HI2 c0 ac Uc) as (_ & _ & _ & _ & _ & Gns).
    destruct (Gns Hml) as (_ & g1 & a1' & i1 & fr1 & U1' & Hi1 & Hfr1 & Hk1 & Hm1 & _).
    rewrite Hmem in Hm1.
    destruct (slot_starts_distinct (m :: X) (Some (g, idx)) U0 s2 HI2 g am idx g1 a1' i1 U2 U1' ltac:(lia) Hi1 Hm1) as [E1 E2].
    subst g1 i1. rewrite (usedX_fun _ _ _ _ _ U1' U2) in Hfr1. rewrite Hfr_ in Hfr1. discriminate. }
destruct PK3 as [P31 P32].
assert (GS3 : forall f, f am' = f am -> gcountX (m :: X) s3 f = gcountX (m :: X) s2 f)
  by (intros f0 Ef; exact (gcount_set _ _ _ g am am' f0 N2 K32 U2 M3g M3o Ef)).
mbinds.
apply (itok_lw _ _ _ (install_group_lw FA m sc cnt0 (cnt0 - 1) 0 (slot_start am idx) slot_junk s3 Hhd3)).
eapply (install_group_spec X U0 s3 m sc cnt0 (cnt0 - 1) 0 (slot_start am idx) slot_junk).
-- exact HI3.
-- exact NX.
-- exact Hsc.
-- lia.
-- lia.
-- lia.
-- exact Hhd3.
-- right. split; reflexivity.
-- right. cbn [am_sc am_last am_maplen new_am]. rewrite new_am_stride. cbn [Z.eqb andb negb].
replace ((cnt0 - 1 =? 0) && false) with false by (destruct (cnt0 - 1 =? 0); reflexivity).
split; [exact Hsc|]. split; [lia|]. split; [auto|]. replace (cnt0 - 1 + 1) with cnt0 by lia. exact Hc0s.
-- intros H0. cbn in H0. lia.
-- intros _. exists g, am', idx, (mkFrame 0 (class_size j - IB) FGroup). rewrite Fl, Fsc, Fss. cbn [fr_kind fr_n].
split; [exact U3|]. split; [lia|]. split.
{ unfold am'. rewrite nth_slot_upd_slot by (try lia; rewrite Glen; lia). rewrite Z.eqb_refl. reflexivity. }
split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. subst total. unfold UNIT, IB in *. nia.
-- intros q a Hu Hp. rewrite prid_slot_start in Hp. rewrite Es3 in Hu.
assert (Htot2 : 0 < total <= class_size j - IB).
{ pose proof Hjfit as HJ. subst total. unfold UNIT, IB in *. split; [nia | lia]. }
destruct (nested_lam (m :: X) U0 s2 g idx am hdr (class_size j - IB) q a sc cnt0 HI2 U2 ltac:(rewrite Hstr; reflexivity)
ltac:(rewrite Hext1; exact Htot2) Hu Hp) as [D | [I | P]].
++ left. exact D.
++ right; left. rewrite Es3. exact I.
++ right; right. split; [reflexivity|]. exact P.
-- intros H0. lia.
-- intros s4 HI4 Hhd4 U4 EH4 Er4 Ec4 UB4 Es4. cbn [snd] in Es4. msimp. apply itok_ret. apply HQ. cbn [snd]. rewrite Es4.
set (a1 := am_set_links (Some m) (Some m) (new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk)).
assert (PKI : PKS X (ig_st m sc cnt0 (cnt0 - 1) 0 (slot_start am idx) slot_junk s3) /\
  PKC X caps (ig_st m sc cnt0 (cnt0 - 1) 0 (slot_start am idx) slot_junk s3)).
{ apply (PK_install X s3 _ m a1 caps NX N3 Km3 (keys_ig _ _ _ _ _ _ _ _ Km3)).
  - rewrite MT_ig, sptr_eqb_refl. reflexivity.
  - intros q Hq. rewrite MT_ig. apply sptr_eqb_neq in Hq. rewrite Hq. reflexivity.
  - intros i. apply ig_frameless. reflexivity.
  - intros _ g0 a0 i0 fr0 Ug0 Hi0 Hfr0 Hk0 Hm0. unfold a1 in Hm0. cbn [am_mem am_set_links new_am] in Hm0.
    rewrite <- SS' in Hm0.
    destruct (slot_starts_distinct (m :: X) None U0 s3 HI3 g am' idx g0 a0 i0 U3 Ug0 ltac:(rewrite Fl; lia) Hi0 Hm0) as [E1 E2].
    subst g0 i0. rewrite (usedX_fun _ _ _ _ _ Ug0 U3). rewrite Fsc, Sc2. unfold a1. cbn [am_sc am_last am_set_links new_am].
    unfold jof. replace (cnt0 - 1 + 1) with cnt0 by lia. unfold j, total. rewrite (Z.mul_comm cnt0 (class_size sc)). reflexivity.
  - intros _. unfold a1. cbn [am_sc am_last am_set_links new_am]. lia.
  - intros _ H0. unfold a1 in H0. cbn [am_maplen am_set_links new_am] in H0. lia.
  - intros c Hc Hg. unfold a1, gfull in Hg. cbn [am_sc am_last am_set_links new_am] in Hg.
    apply andb_prop in Hg as [Hg1 Hg2]. apply Z.eqb_eq in Hg1. subst c.
    rewrite (GS3 (gfull sc)) by (unfold gfull; rewrite Fsc, Fl; reflexivity). exact CF2.
  - intros c Hc Hg. unfold a1, gred in Hg. cbn [am_sc am_last am_set_links new_am] in Hg.
    apply andb_prop in Hg as [Hg1 Hg2]. apply Z.eqb_eq in Hg1. apply Z.ltb_lt in Hg2. subst c.
    assert (Hlow : usage_of s1 sc < 128).
    { destruct (Z.lt_ge_cases (usage_of s1 sc) 128) as [H|H]; [exact H|]. exfalso. specialize (Hbig H). lia. }
    rewrite (GS3 (gred sc)) by (unfold gred; rewrite Fsc, Fl; reflexivity). unfold RED. lia.
  - exact P31.
  - exact P32. }
destruct PKI as [R1 R2]. split; [exact R1|]. split; [exact R2|]. split.
{ apply (CL_trans _ _ _ CL1). apply (CL_trans _ _ _ Q3). apply (CL_trans _ s3).
  - apply (CL_upd_geom s2 s3 g am am' (proj1 (usedX_MT _ _ _ _ U2)) M3g M3o Fsc Fl).
    rewrite <- (map_fst_blocks_of g am'), <- (map_fst_blocks_of g am). f_equal. unfold am'.
    apply blocks_of_upd_slot_same; [lia | exact Glen |]. unfold slotst_block, slot_block. cbn. rewrite Hfr_. reflexivity.
  - apply (CL_upd_X _ _ m).
    + intros q Hq. rewrite MT_ig. apply sptr_eqb_neq in Hq. rewrite Hq. reflexivity.
    + intros a Ma. exact (Xok_bo (m :: X) s3 m a (inv_X HI3) (or_introl eq_refl) Ma). }
intros c Hc. rewrite usage_ig by lia. rewrite Es3.
change (usage_of (upd_meta g (MUsed am') s2) c) with (usage_of s2 c). rewrite (Q4 c ltac:(lia)). apply Us1.
Qed.
