(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmCurDefs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSomeSem_u.
Import ListNotations. Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PSSC.
Definition icsb (x : Z) : bool := existsb (Z.eqb x) PMCUR.ICS.
Lemma icsb_spec : forall x, icsb x = true <-> In x PMCUR.ICS.
Proof.
  intros x. unfold icsb. rewrite existsb_exists. split.
  - intros (y & Hy & He). apply Z.eqb_eq in He. subst y. exact Hy.
  - intros H. exists x. split; [exact H | apply Z.eqb_refl].
Qed.
Lemma ics_dec : forall x, {In x PMCUR.ICS} + {~ In x PMCUR.ICS}.
Proof. intros x. destruct (icsb x) eqn:H; [left; exact (proj1 (icsb_spec x) H) | right; intros X; rewrite <- icsb_spec in X; congruence]. Qed.

Definition stk_ok (stk : list Z) (lvl : Z) : Prop := (exists x, In x stk /\ In x PMCUR.ICS) -> 1 <= lvl.
Lemma lvl_ok_split : forall ps, PMCUR.lvl_ok ps <-> (ps_more ps = true -> (In (ps_st ps) PMCUR.ICS -> 1 <= ps_level ps) /\ stk_ok (ps_stack ps) (ps_level ps)).
Proof.
  intros ps. unfold PMCUR.lvl_ok, stk_ok. split.
  - intros H Hm. split; [intros X; exact (H Hm (or_introl X)) | intros X; exact (H Hm (or_intror X))].
  - intros H Hm [X|X]; [exact (proj1 (H Hm) X) | exact (proj2 (H Hm) X)].
Qed.

Lemma not_ics_root_cont : forall C, Forall is_container C -> forall x, In x (ST_ROOT :: C) -> ~ In x PMCUR.ICS.
Proof.
  intros C HC x Hx Hi. unfold PMCUR.ICS in Hi. cbn [In] in Hx.
  destruct Hx as [<-|Hx]; [unfold ST_ROOT in Hi; cbn in Hi; unfold ST_EXPECT_COMMA_OR_END, ST_EXPECT_MEMBER_NAME_OR_END, ST_EXPECT_MEMBER_NAME, ST_EXPECT_COLON, ST_EXPECT_VALUE_OR_END, ST_EXPECT_VALUE, ST_MEMBER_NAME in Hi; lia|].
  rewrite Forall_forall in HC. destruct (HC x Hx) as [->| ->]; cbn in Hi;
    unfold ST_OBJECT, ST_ARRAY, ST_EXPECT_COMMA_OR_END, ST_EXPECT_MEMBER_NAME_OR_END, ST_EXPECT_MEMBER_NAME, ST_EXPECT_COLON, ST_EXPECT_VALUE_OR_END, ST_EXPECT_VALUE, ST_MEMBER_NAME in Hi; lia.
Qed.

Lemma stk_ok_nil_T : forall ps C, ps_stack ps = ST_ROOT :: C ++ [] -> Forall is_container C -> forall lvl, stk_ok (ps_stack ps) lvl.
Proof. intros ps C Hs HC lvl (x & Hx & Hi). rewrite Hs, app_nil_r in Hx. exfalso. exact (not_ics_root_cont C HC x Hx Hi). Qed.

Lemma lvl_stop : forall ps st sst nst done bcap bptr buf w, PMCUR.lvl_ok (PSS.upd ps st sst nst false done bcap bptr buf w).
Proof. intros ps st sst nst done bcap bptr buf w X. discriminate X. Qed.

Lemma lvl_plain : forall ps st sst nst done bcap bptr buf w,
  wf_ps ps -> ps_more ps = true -> ~ comment_or_cr (ps_st ps) -> ps_st ps <> ST_STRING -> (In st PMCUR.ICS -> 1 <= ps_level ps) ->
  PMCUR.lvl_ok (PSS.upd ps st sst nst true done bcap bptr buf w).
Proof.
  intros ps st sst nst done bcap bptr buf w (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)) Hm Hnc Hns HL.
  destruct (W7 Hm) as (X1 & X2 & X3 & X4 & X5 & X6).
  assert (HT : T = []).
  { destruct X4 as [(HT & _)|[(_ & Hst)|[(S & _ & _ & Hc)|(S & _ & _ & Hc)]]]; [exact HT | contradiction | contradiction | exfalso; apply Hnc; right; exact Hc]. }
  subst T. apply lvl_ok_split. intros _. unfold PSS.upd. cbn [ps_st ps_stack ps_level]. split; [exact HL|]. exact (stk_ok_nil_T ps C W5 W6 _).
Qed.

Lemma lvl_src : forall ps, PMCUR.lvl_ok ps -> ps_more ps = true -> (In (ps_st ps) PMCUR.ICS -> 1 <= ps_level ps) /\ stk_ok (ps_stack ps) (ps_level ps).
Proof. intros ps H Hm. exact (proj1 (lvl_ok_split ps) H Hm). Qed.

Lemma lvl_plain_src : forall ps st sst nst done bcap bptr buf w,
  wf_ps ps -> PMCUR.lvl_ok ps -> ps_more ps = true -> ~ comment_or_cr (ps_st ps) -> ps_st ps <> ST_STRING ->
  (In st PMCUR.ICS -> In (ps_st ps) PMCUR.ICS \/ 1 <= ps_level ps) ->
  PMCUR.lvl_ok (PSS.upd ps st sst nst true done bcap bptr buf w).
Proof.
  intros ps st sst nst done bcap bptr buf w WF LV Hm Hnc Hns HL. apply lvl_plain; try assumption.
  intros Hi. destruct (HL Hi) as [Hs|Hs]; [exact (proj1 (lvl_src ps LV Hm) Hs) | exact Hs].
Qed.

Lemma lvl_comment : forall ps st sst nst done bcap bptr buf w,
  PMCUR.lvl_ok ps -> ps_more ps = true -> 3 <= st <= 6 -> PMCUR.lvl_ok (PSS.upd ps st sst nst true done bcap bptr buf w).
Proof.
  intros ps st sst nst done bcap bptr buf w LV Hm Hc. apply lvl_ok_split. intros _. unfold PSS.upd. cbn [ps_st ps_stack ps_level].
  split; [|exact (proj2 (lvl_src ps LV Hm))]. intros Hi. exfalso. unfold PMCUR.ICS in Hi. cbn in Hi.
  unfold ST_EXPECT_COMMA_OR_END, ST_EXPECT_MEMBER_NAME_OR_END, ST_EXPECT_MEMBER_NAME, ST_EXPECT_COLON, ST_EXPECT_VALUE_OR_END, ST_EXPECT_VALUE, ST_MEMBER_NAME in Hi. lia.
Qed.

Lemma lvl_pop : forall ps rest x sst nst done bcap bptr buf w,
  PMCUR.lvl_ok ps -> ps_more ps = true -> ps_stack ps = rest ++ [x] ->
  PMCUR.lvl_ok (PS x sst nst true done (ps_level ps) rest (ps_sb ps) (ps_scap ps) bcap bptr buf w).
Proof.
  intros ps rest x sst nst done bcap bptr buf w LV Hm Hs. destruct (lvl_src ps LV Hm) as (_ & SK).
  apply lvl_ok_split. intros _. cbn [ps_st ps_stack ps_level]. split.
  - intros Hi. apply SK. exists x. split; [rewrite Hs; apply in_or_app; right; left; reflexivity | exact Hi].
  - intros (y & Hy & Hi). apply SK. exists y. split; [rewrite Hs; apply in_or_app; left; exact Hy | exact Hi].
Qed.

Lemma lvl_push : forall ps x st' sst nst done sb' scap' bcap bptr buf w,
  PMCUR.lvl_ok ps -> ps_more ps = true -> (In x PMCUR.ICS -> In (ps_st ps) PMCUR.ICS) -> ~ In st' PMCUR.ICS ->
  PMCUR.lvl_ok (PS st' sst nst true done (ps_level ps) (ps_stack ps ++ [x]) sb' scap' bcap bptr buf w).
Proof.
  intros ps x st' sst nst done sb' scap' bcap bptr buf w LV Hm HX Hst. destruct (lvl_src ps LV Hm) as (LS & SK).
  apply lvl_ok_split. intros _. cbn [ps_st ps_stack ps_level]. split; [intros Hi; contradiction|].
  intros (y & Hy & Hi). apply in_app_or in Hy as [Hy|[<-|[]]]; [apply SK; exists y; split; assumption | exact (LS (HX Hi))].
Qed.

Lemma lvl_win : forall ps w, PMCUR.lvl_ok ps -> PMCUR.lvl_ok (ps_set_win ps w).
Proof. intros ps w H. destruct ps; exact H. Qed.
Lemma lvl_set_more : forall ps, PMCUR.lvl_ok (PMCUR.ps_set_more ps true) -> ps_more ps = true -> PMCUR.lvl_ok ps.
Proof. intros [] H Hm; cbn in *; subst; exact H. Qed.
Lemma wf_c_intro : forall ps, wf_ps ps -> PMCUR.lvl_ok ps -> PMCUR.wf_c ps.
Proof. intros ps H1 H2. split; assumption. Qed.

Lemma lvl_keep_nics : forall ps1 ps2, PMCUR.lvl_ok ps1 -> ps_more ps1 = true -> ps_stack ps2 = ps_stack ps1 -> ps_level ps2 = ps_level ps1 -> ~ In (ps_st ps2) PMCUR.ICS ->
  PMCUR.lvl_ok ps2.
Proof.
  intros ps1 ps2 LV Hm HS HL Hn. apply lvl_ok_split. intros _. destruct (lvl_src ps1 LV Hm) as (_ & SK).
  split; [intros X; contradiction|]. rewrite HS, HL. exact SK.
Qed.

Lemma lvl_same : forall ps1 ps2, PMCUR.lvl_ok ps1 -> ps_more ps2 = ps_more ps1 -> ps_st ps2 = ps_st ps1 -> ps_stack ps2 = ps_stack ps1 -> ps_level ps2 = ps_level ps1 ->
  PMCUR.lvl_ok ps2.
Proof. intros ps1 ps2 LV Hm Hs HS HL. unfold PMCUR.lvl_ok. rewrite Hm, Hs, HS, HL. exact LV. Qed.
Lemma nics_15 : ~ In ST_STRING PMCUR.ICS. Proof. unfold PMCUR.ICS, ST_STRING. cbn. unfold ST_EXPECT_COMMA_OR_END, ST_EXPECT_MEMBER_NAME_OR_END, ST_EXPECT_MEMBER_NAME, ST_EXPECT_COLON, ST_EXPECT_VALUE_OR_END, ST_EXPECT_VALUE, ST_MEMBER_NAME. lia. Qed.
Lemma nics_17 : ~ In ST_NUMBER PMCUR.ICS. Proof. unfold PMCUR.ICS, ST_NUMBER. cbn. unfold ST_EXPECT_COMMA_OR_END, ST_EXPECT_MEMBER_NAME_OR_END, ST_EXPECT_MEMBER_NAME, ST_EXPECT_COLON, ST_EXPECT_VALUE_OR_END, ST_EXPECT_VALUE, ST_MEMBER_NAME. lia. Qed.
Lemma ics_9 : In ST_EXPECT_MEMBER_NAME_OR_END PMCUR.ICS. Proof. unfold PMCUR.ICS. cbn. tauto. Qed.
Lemma ics_10 : In ST_EXPECT_MEMBER_NAME PMCUR.ICS. Proof. unfold PMCUR.ICS. cbn. tauto. Qed.
Lemma ics_16 : In ST_MEMBER_NAME PMCUR.ICS. Proof. unfold PMCUR.ICS. cbn. tauto. Qed.

Lemma regJ_nz : forall g, regJ g <> LS0. Proof. intros [| | | | |]; discriminate. Qed.
Lemma regC_nz : forall g, regC g <> LS0. Proof. intros [| | | | |]; discriminate. Qed.
End PSSC.
