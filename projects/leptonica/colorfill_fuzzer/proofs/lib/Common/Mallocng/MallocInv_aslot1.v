(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_wf3 MallocInv_wf4 MallocInv_wf6 MallocInv_wf7 MallocInv_wf8 MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm
  MallocInv_coh MallocInv_ops MallocInv_usage MallocInv_live MallocInv_hints MallocInv_sc MallocInv_sc3 MallocInv_ameta_iface MallocInv_ametax_iface MallocInv_ntfree MallocInv_ntpost MallocInv_ntq
  MallocInv_nt1 MallocInv_ntfm MallocInv_take MallocInv_tav_iface MallocInv_agrp_iface MallocInv_agm3 MallocInv_aslot_iface MallocInv_agtail MallocInv_agroot MallocInv_agnest.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Unset Lia Cache.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.
Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition gdom (A : astate) (x : Z) : Prop :=
  exists ma mt aib slots, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\
    0 < mt_maplen mt /\ mt_mem mt <= x < mt_mem mt + grp_map_len mt.

Definition gnew (A A' : astate) (m0 : word -> option byte) : Prop :=
  forall x, gdom A' x -> gdom A x \/ m0 (Z_to_bv 64 x) = None.

Definition inoroom (A : astate) (s : mstate) (k : Z) : Prop :=
  (k <= spare A -> refusal (ms_vm s)) /\
  (a_areas A = [] ->
     ~ (vm_backed_bytes (ms_vm s) + 4096 <= vm_limit (ms_vm s) /\
        (0 < a_ctx A KAac \/ exists a, grant_ok_na_vm (ms_vm s) a 8192 = true))
     \/ exists h2, am_delta (ms_vm s) h2 /\ refusal h2).

Lemma inoroom_noroom : forall sp0 argv envp cb A s k, 0 <= k <= 4 -> inoroom A s k -> aslot_noroom sp0 argv envp cb A s.
Proof using Type. pu_keep tt. intros sp0 argv envp cb A s k Hk [H1 H2]. split; [intros Hs; apply H1; lia | exact H2]. Qed.

Lemma gdom_dom : forall A x, gdom A x -> dom A x.
Proof using Type. pu_keep tt. intros A x (ma & mt & aib & sl & H1 & H2 & H3 & H4). right; left. exists ma, mt, aib, sl. auto. Qed.

Lemma dom_cases : forall A x, dom A x ->
  gdom A x \/ (exists pg, (In pg (a_areas A) \/ In pg (a_pages A)) /\ pg <= x < pg + 4096).
Proof using Type. pu_keep tt.
  intros A x [(pg & Hpg & Hx) | [(ma & mt & aib & sl & H1 & H2 & H3 & H4) | (pg & Hpg & Hx)]].
  - right. exists pg. auto.
  - left. exists ma, mt, aib, sl. auto.
  - right. exists pg. auto.
Qed.

Lemma newdom_of_gnew : forall A A' m0, gnew A A' m0 ->
  forall x, dom A' x -> dom A x \/ m0 (Z_to_bv 64 x) = None \/ (exists pg, (In pg (a_areas A') \/ In pg (a_pages A')) /\ pg <= x < pg + 4096).
Proof using Type. pu_keep tt.
  intros A A' m0 G x Hd. destruct (dom_cases A' x Hd) as [Hg | Hp]; [| right; right; exact Hp].
  destruct (G x Hg) as [Hg0 | Hn]; [left; exact (gdom_dom A x Hg0) | right; left; exact Hn].
Qed.

(* [comment removed for export] *)
Lemma gdom_transfer : forall A A',
  (forall y mt' aib' sl', a_meta A' y = Some mt' -> mt_role mt' = RGroup aib' sl' ->
     exists mt aib sl, a_meta A y = Some mt /\ mt_role mt = RGroup aib sl /\ mt_w32 mt = mt_w32 mt' /\ mt_mem mt = mt_mem mt') ->
  forall x, gdom A' x -> gdom A x.
Proof using Type. pu_keep tt.
  intros A A' Hb x (ma & mt' & aib' & sl' & H1 & H2 & H3 & H4).
  destruct (Hb ma mt' aib' sl' H1 H2) as (mt & aib & sl & G1 & G2 & W & M).
  exists ma, mt, aib, sl. split; [exact G1|]. split; [exact G2|].
  unfold mt_maplen, grp_map_len, mt_maplen in *. rewrite W, M. auto.
Qed.

Lemma gnew_refl_groups : forall A A' m0,
  (forall y mt' aib' sl', a_meta A' y = Some mt' -> mt_role mt' = RGroup aib' sl' ->
     exists mt aib sl, a_meta A y = Some mt /\ mt_role mt = RGroup aib sl /\ mt_w32 mt = mt_w32 mt' /\ mt_mem mt = mt_mem mt') ->
  gnew A A' m0.
Proof using Type. pu_keep tt. intros A A' m0 Hb x Hg. left. exact (gdom_transfer A A' Hb x Hg). Qed.

(* [comment removed for export] *)
Lemma dom_of_FR : forall A s A' s', WF A -> FR A s A' s' -> forall x, dom A x -> dom A' x.
Proof using MLok. pu_keep (MLok).
  intros A s A' s' HW F x Hd. pose proof layout_small as LS. pose proof layout_nums as LN.
  destruct (fr_owned _ _ _ _ F x (or_intror Hd)) as [Hc | Hd']; [| exact Hd'].
  exfalso. destruct (dom_heap A x HW Hd) as (lo & hi & Hh & Hx). unfold heap_range in Hh. lia.
Qed.

Lemma none_of_FR : forall A s A' s', FR A s A' s' -> forall a, ms_mem s' a = None -> ms_mem s a = None.
Proof using Type. pu_keep tt.
  intros A s A' s' F a Ha. destruct (ms_mem s a) eqn:E; [| reflexivity].
  exfalso. apply (fr_mapped _ _ _ _ F a); [rewrite E; discriminate | exact Ha].
Qed.

Lemma spare_nonneg : forall A, WF A -> 0 <= spare A.
Proof using Type. pu_keep tt. intros A HW. unfold spare. pose proof (wf_ctx_nonneg A HW KAmc). lia. Qed.

(* [comment removed for export] *)
Lemma spare_nil_areas : forall A, WF A -> a_areas A = [] -> spare A = 0.
Proof using Type. pu_keep tt.
  intros A HW E. unfold spare. pose proof (wf_amc A HW) as Hc.
  assert (K0 : a_ctx A KAmc = 0).
  { destruct (Z.eq_dec (a_ctx A KAmc) 0) as [H|H]; [exact H|]. exfalso.
    destruct (wf_am A HW ltac:(lia)) as (pg & Hne & _). exact (Hne E). }
  rewrite K0. destruct (a_freelist A) as [|x l] eqn:F; [reflexivity|]. exfalso.
  destruct (proj1 (wf_fl_mem A HW x) ltac:(rewrite F; left; reflexivity)) as (mt & Hx & _).
  destruct (proj1 (wf_meta_dom A HW x) ltac:(rewrite Hx; discriminate)) as (pg & k & Hpg & _). rewrite E in Hpg. exact Hpg.
Qed.

Lemma in_slots_shape : forall cnt, in_slots cnt = STaken :: repeat SIdle (Z.to_nat (cnt - 1)).
Proof using Type. pu_keep tt. reflexivity. Qed.
Lemma ir_slots_shape : forall cnt, ir_slots cnt = STaken :: repeat SIdle (Z.to_nat (cnt - 1)).
Proof using Type. pu_keep tt. reflexivity. Qed.

Lemma nth_repeat_idle : forall n j st, nth_error (repeat SIdle n) j = Some st -> st = SIdle.
Proof using Type. pu_keep tt.
  intros n. induction n as [|n IH]; intros [|j] st H; cbn in H; try discriminate H; [injection H as <-; reflexivity | exact (IH j st H)].
Qed.

(* [comment removed for export] *)
Lemma size_class_15_19_23 : forall j, j = 15 \/ j = 19 \/ j = 23 -> 0 <= j < 48 /\ size_class j <= 127 /\ 31 <= size_class j.
Proof using Type. pu_keep tt.
  intros j [-> | [-> | ->]];
    [replace (size_class 15) with 31 by reflexivity | replace (size_class 19) with 63 by reflexivity | replace (size_class 23) with 127 by reflexivity]; lia.
Qed.

Lemma nest_rank_range : forall c, 0 <= nest_rank c <= 3.
Proof using Type. pu_keep tt. intros c. unfold nest_rank. destruct (c =? 15); [lia|]. destruct (c =? 19); [lia|]. destruct (c =? 23); lia. Qed.

Lemma nest_rank_pos : forall c, 0 < nest_rank c -> c = 15 \/ c = 19 \/ c = 23.
Proof using Type. pu_keep tt.
  intros c H. unfold nest_rank in H.
  destruct (Z.eqb_spec c 15); [auto|]. destruct (Z.eqb_spec c 19); [auto|]. destruct (Z.eqb_spec c 23); [auto | lia].
Qed.

(* [comment removed for export] *)
Lemma size_class_big : forall sc, 38 < sc < 48 -> 2047 <= size_class sc.
Proof using Type. pu_keep tt.
  intros sc Hsc.
  assert (H : sc = 39 \/ sc = 40 \/ sc = 41 \/ sc = 42 \/ sc = 43 \/ sc = 44 \/ sc = 45 \/ sc = 46 \/ sc = 47) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
    [replace (size_class 39) with 2047 by reflexivity | replace (size_class 40) with 2340 by reflexivity | replace (size_class 41) with 2730 by reflexivity
    | replace (size_class 42) with 3276 by reflexivity | replace (size_class 43) with 4095 by reflexivity | replace (size_class 44) with 4680 by reflexivity
    | replace (size_class 45) with 5460 by reflexivity | replace (size_class 46) with 6552 by reflexivity | replace (size_class 47) with 8191 by reflexivity]; lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zbv_inj : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
Proof using Type. pu_keep tt. intros a b Ha Hb E. pose proof (f_equal bv_unsigned E) as E'. rewrite !uZ in E' by lia. exact E'. Qed.

Lemma size_class_big0 : forall sc, 38 < sc < 48 -> sc mod 4 <> 3 -> 2340 <= size_class sc.
Proof using Type. pu_keep tt.
  intros sc Hsc Hm.
  assert (H : sc = 40 \/ sc = 41 \/ sc = 42 \/ sc = 44 \/ sc = 45 \/ sc = 46).
  { assert (sc <> 39) by (intros ->; apply Hm; reflexivity). assert (sc <> 43) by (intros ->; apply Hm; reflexivity).
    assert (sc <> 47) by (intros ->; apply Hm; reflexivity). lia. }
  destruct H as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    [replace (size_class 40) with 2340 by reflexivity | replace (size_class 41) with 2730 by reflexivity | replace (size_class 42) with 3276 by reflexivity
    | replace (size_class 44) with 4680 by reflexivity | replace (size_class 45) with 5460 by reflexivity | replace (size_class 46) with 6552 by reflexivity]; lia.
Qed.

(* [comment removed for export] *)
Lemma single_exact : forall sc szc cnt1 c2 req cnt L,
  38 < sc < 48 -> sc mod 4 <> 3 -> szc = size_class sc -> 1 <= cnt1 <= 32 -> 0 <= req < 2^40 -> 0 <= cnt < 2^64 -> 0 <= L < 2^64 ->
  cnt2w (Z_to_bv 64 sc) (Z_to_bv 64 0) (Z_to_bv 64 4096) (Z_to_bv 64 (16 * szc * cnt1)) (Z_to_bv 64 cnt1) false = Z_to_bv 64 c2 ->
  0 <= c2 < 2^64 ->
  cn3w false (Z_to_bv 64 c2) (Z_to_bv 64 (page_round_up_Z (16 * szc * c2 + 16))) (Z_to_bv 64 req) (Z_to_bv 64 4096) (Z_to_bv 64 (16 * szc)) (Z_to_bv 64 0)
    = (Z_to_bv 64 cnt, Z_to_bv 64 L) ->
  (16384 <= page_round_up_Z (req + 20) \/ page_round_up_Z (req + 20) < 16 * szc + 16) ->
  cnt = 1 /\ L = page_round_up_Z (req + 20).
Proof using Type. pu_keep tt.
  intros sc szc cnt1 c2 req cnt L Hsc Hm Hszc Hc1 Hreq Hcnt HL E2 Hc2 E3 Hpre.
  pose proof (size_class_big0 sc Hsc Hm) as SB. pose proof (size_class_range sc ltac:(lia)) as SR. subst szc.
  assert (Hc23 : c2 = 2 \/ c2 = 3).
  { unfold cnt2w, wlit in E2. rewrite v_slliw_Z in E2 by lia. rewrite swrap32_small in E2 by lia. rewrite c_ltu_Z in E2 by lia.
    replace (0 <? cnt1 * 2^2) with true in E2 by (symmetry; apply Z.ltb_lt; lia). cbn [negb] in E2.
    rewrite v_andi_Z in E2 by lia. replace (Z.land sc 3) with (sc mod 4) in E2 by (change 3 with (2^2 - 1); rewrite land_ones_low by lia; reflexivity).
    pose proof (Z.mod_pos_bound sc 4 ltac:(lia)) as M4.
    rewrite !v_slli_Z in E2 by lia. change (4096 * 2^3) with 32768 in E2. change (4096 * 2^2) with 16384 in E2. change (4096 * 2^1) with 8192 in E2.
    rewrite !c_eq_Z, !c_ltu_Z, is0_Z in E2 by nia.
    assert (B : 32768 < 16 * size_class sc * cnt1) by nia.
    replace (32768 <? 16 * size_class sc * cnt1) with true in E2 by (symmetry; apply Z.ltb_lt; lia).
    replace (16384 <? 16 * size_class sc * cnt1) with true in E2 by (symmetry; apply Z.ltb_lt; lia).
    destruct (Z.eqb_spec (sc mod 4) 1) as [E1|N1]; cbn [andb] in E2; [left; symmetry; apply (zbv_inj 2 c2); [lia | lia | exact E2]|].
    destruct (Z.eqb_spec (sc mod 4) 2) as [E2'|N2]; cbn [andb] in E2; [right; symmetry; apply (zbv_inj 3 c2); [lia | lia | exact E2]|].
    destruct (Z.eqb_spec (sc mod 4) 0) as [E0|N0]; cbn [andb] in E2; [right; symmetry; apply (zbv_inj 3 c2); [lia | lia | exact E2]|].
    exfalso. lia. }
  assert (Hc27 : 1 <= c2 <= 7) by lia.
  unfold cn3w, wlit in E3. rewrite c_ltu_Z in E3 by lia. replace (7 <? c2) with false in E3 by (symmetry; apply Z.ltb_ge; lia).
  rewrite roundup_word20 in E3 by lia. destruct (page_round_up_Z_spec (req + 20) ltac:(lia)) as [B _].
  rewrite v_addi_Z, v_slli_Z in E3 by lia. change (4096 * 2^2) with 16384 in E3. rewrite !c_ltu_Z in E3 by lia.
  assert (FIN : (Z_to_bv 64 1, Z_to_bv 64 (page_round_up_Z (req + 20))) = (Z_to_bv 64 cnt, Z_to_bv 64 L) -> cnt = 1 /\ L = page_round_up_Z (req + 20)).
  { intros E. pose proof (f_equal fst E) as E1. pose proof (f_equal snd E) as EL. cbn [fst snd] in E1, EL. split; [symmetry; apply (zbv_inj 1 cnt); [lia | lia | exact E1] | symmetry; apply zbv_inj; [lia | lia | exact EL]]. }
  destruct (Z.ltb_spec (page_round_up_Z (req + 20)) (16 * size_class sc + 16)); [exact (FIN E3)|].
  replace (page_round_up_Z (req + 20) <? 16384) with false in E3 by (symmetry; apply Z.ltb_ge; lia).
  rewrite v_slliw_Z in E3 by lia. rewrite swrap32_small in E3 by lia. rewrite c_ltu_Z in E3 by lia.
  replace (0 <? c2 * 2^1) with true in E3 by (symmetry; apply Z.ltb_lt; lia). exact (FIN E3).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TA.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z).
  Variables (A : astate) (s : mstate) (A1 : astate) (s1 : mstate) (sc : Z).
  Hypothesis HII : II sp0 argv envp cb D A s.
  Hypothesis Hsc : 0 <= sc < 48.
  (* [comment removed for export] *)
  Hypothesis HII1 : II sp0 argv envp cb D A1 s1.
  Hypothesis NF1 : ntframe A s s1.
  Hypothesis TV : tavrel A A1 sc.

  Let HW : WF A := is_wf _ _ _ _ _ _ (ii_is HII).
  Let HW1 : WF A1 := is_wf _ _ _ _ _ _ (ii_is HII1).

  Lemma pf_FR1 : FR A s A1 s1.
  Proof using NF1 TV. pu_keep (NF1, TV).
    apply (FR_of_ntframe A A1 s s1 NF1); [| exact (tv_live _ _ _ TV)].
    intros x [Hc | Hd]; [left; exact Hc | right]. apply (proj2 (tv_dom _ _ _ TV x)). exact Hd.
  Qed.

  Lemma pf_spare1 : spare A1 = spare A.
  Proof using TV. pu_keep (TV).
    unfold spare. rewrite (tv_fl _ _ _ TV). rewrite (tv_ctx _ _ _ TV KAmc I ltac:(discriminate) ltac:(intros H; exact H)). reflexivity.
  Qed.

  Lemma pf_areas1 : a_areas A1 = a_areas A. Proof using TV. pu_keep (TV). exact (tv_areas _ _ _ TV). Qed.

  Lemma pf_usage1 : usage_of A1 sc = usage_of A sc.
  Proof using TV. pu_keep (TV).
    apply usage_of_ext; [exact pf_areas1|]. intros ma. unfold meta_usage.
    destruct (a_meta A1 ma) as [mt1|] eqn:E1.
    - destruct (mt_role mt1) as [| | | aib1 sl1] eqn:R1;
        try (rewrite (tv_other_back _ _ _ TV ma mt1 E1 ltac:(intros aib sl E; rewrite R1 in E; discriminate E)); rewrite R1; reflexivity).
      destruct (tv_grp _ _ _ TV ma mt1 aib1 sl1 E1 R1) as (mt0 & aib0 & H0 & R0 & W & _). rewrite H0, R0. unfold mt_sc, mt_cnt, mt_last. rewrite W. reflexivity.
    - destruct (a_meta A ma) as [mt0|] eqn:E0; [| reflexivity].
      destruct (mt_role mt0) as [| | | aib0 sl0] eqn:R0; try reflexivity.
      destruct (tv_grp_back _ _ _ TV ma mt0 aib0 sl0 E0 R0) as (mtx & aibx & Hx & _). rewrite E1 in Hx. discriminate Hx.
  Qed.

  Lemma pf_had_idle1 : aslot_had_idle A1 -> aslot_had_idle A.
  Proof using TV. pu_keep (TV).
    apply aslot_had_idle_transfer. intros x mt' aib' sl' Hx Hr. destruct (tv_grp _ _ _ TV x mt' aib' sl' Hx Hr) as (mt & aib & H1 & H2 & W & _). exists mt, aib. auto.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section TakeLeaf.
    Variables (g : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (req : Z) (s' : mstate).
    Hypothesis Hne1 : a_active A1 sc <> [].
    Hypothesis Hhd : g = hd 0 (a_active A1 sc).
    Hypothesis Hg : a_meta A1 g = Some mt.
    Hypothesis Hr : mt_role mt = RGroup aib slots.
    Hypothesis Hav : mt_avail mt <> 0.
    Hypothesis Hreq : req + 4 <= 16 * size_class sc.
    Let i := ctz32 (mt_avail mt).
    Let A' := tkA A1 g mt aib slots i.
    Hypothesis HII' : II sp0 argv envp cb D A' s'.
    Hypothesis NF' : ntframe A1 s1 s'.

    Lemma tk_facts : 0 <= i < 32 /\ Z.testbit (mt_avail mt) i = true /\ nth_error slots (Z.to_nat i) = Some SIdle /\ mt_sc mt = sc /\ 16 * size_class sc <= mt_stride mt.
    Proof using HW1 Hav Hg Hhd Hne1 Hr Hsc. pu_keep (HW1, Hav, Hg, Hhd, Hne1, Hr, Hsc).
      pose proof (take_facts sp0 argv envp cb D A1 s1 HII1 sc g mt aib slots Hsc Hg Hr Hav) as (Hv & Hi & Hbit).
      pose proof (tk_slot_idle A1 HW1 sc g mt aib slots i Hsc Hhd Hne1 Hg Hr ltac:(lia) Hbit) as Hidle.
      assert (Hgsc : mt_sc mt = sc).
      { destruct (wf_act_mem A1 HW1 sc g ltac:(rewrite Hhd; destruct (a_active A1 sc); [exfalso; exact (Hne1 eq_refl) | left; reflexivity])) as (mt' & aib' & sl' & Hm' & _ & Hs).
        rewrite Hg in Hm'. injection Hm' as <-. exact Hs. }
      refine (conj Hi (conj Hbit (conj Hidle (conj Hgsc _)))).
      rewrite <- Hgsc. apply (wf_reusable A1 HW1 g mt aib slots Hg Hr); [rewrite Hgsc; lia|].
      intros Hz. apply Hav. apply Z.bits_inj'. intros j Hj. rewrite Z.bits_0.
      pose proof (f_equal (fun z => Z.testbit z j) Hz) as E. cbn beta in E. rewrite Z.lor_spec, Z.bits_0 in E.
      apply Bool.orb_false_iff in E. exact (proj1 E).
    Qed.

    Lemma take_leaf :
      FR A s A' s' /\ aslot_ok A A' sc req g i (ms_mem s) s' /\ gnew A A' (ms_mem s) /\ aslot_vm A sc s s' /\
      a_ctx A' (KActive sc) = g /\ g = hd 0 (a_active A' sc) /\ a_active A' sc <> [] /\
      a_meta A' g = Some (tk_mt mt aib slots i) /\ mt_role (tk_mt mt aib slots i) = RGroup aib (tk_slots slots i) /\
      mt_sc (tk_mt mt aib slots i) = sc /\ 0 <= i <= mt_last (tk_mt mt aib slots i) /\
      nth_error (tk_slots slots i) (Z.to_nat i) = Some STaken /\ req + 4 <= mt_stride (tk_mt mt aib slots i) /\
      16 * size_class sc <= mt_stride (tk_mt mt aib slots i) /\ aslot_had_idle A.
    Proof using HII' HW1 Hav Hg Hhd Hne1 Hr Hreq Hsc NF' NF1 TV. pu_keep (HII', HW1, Hav, Hg, Hhd, Hne1, Hr, Hreq, Hsc, NF', NF1, TV).
      pose proof tk_facts as (Hi & Hbit & Hidle & Hgsc & Hstride). pose proof (nest_rank_range sc) as Hnr.
      pose proof (tk_i_last A1 HW1 sc g mt aib slots i Hsc Hhd Hne1 Hg Hr ltac:(lia) Hbit) as Hil.
      assert (GB : forall y mt' aib' sl', a_meta A' y = Some mt' -> mt_role mt' = RGroup aib' sl' ->
        exists mt0 aib0 sl0, a_meta A y = Some mt0 /\ mt_role mt0 = RGroup aib0 sl0 /\ mt_w32 mt0 = mt_w32 mt' /\ mt_mem mt0 = mt_mem mt').
      { intros y mt' aib' sl' Hy Hry. destruct (tkA_meta_inv A1 g mt aib slots i y mt' Hy) as [(-> & ->) | (Hne & Hy1)].
        - destruct (tv_grp _ _ _ TV g mt aib slots Hg Hr) as (mt0 & aib0 & H0 & R0 & W & M). exists mt0, aib0, slots. auto.
        - destruct (tv_grp _ _ _ TV y mt' aib' sl' Hy1 Hry) as (mt0 & aib0 & H0 & R0 & W & M). exists mt0, aib0, sl'. auto. }
      assert (KEEP : aslot_keep A A' sc (ms_mem s)).
      { constructor.
        - unfold A'. rewrite tkA_live. exact (tv_live _ _ _ TV).
        - intros x mtx Hx Hrx. unfold A'. rewrite (tkA_meta_other A1 g mt aib slots i x).
          + apply (tv_other _ _ _ TV x mtx Hx). intros aib0 sl0 E. rewrite Hrx in E. discriminate E.
          + intros ->. pose proof (tv_other _ _ _ TV g mtx Hx ltac:(intros aib0 sl0 E; rewrite Hrx in E; discriminate E)) as H1. rewrite Hg in H1. injection H1 as ->. rewrite Hr in Hrx. discriminate Hrx.
        - intros x Hd. apply (proj2 (dom_tkA A1 g mt aib slots i Hg Hr x)). apply (proj2 (tv_dom _ _ _ TV x)). exact Hd.
        - intros x Hd. left. apply (proj1 (tv_dom _ _ _ TV x)). apply (proj1 (dom_tkA A1 g mt aib slots i Hg Hr x)). exact Hd.
        - intros c Hc _. unfold A'. rewrite tkA_active. exact (tv_act _ _ _ TV c Hc).
        - unfold A'. rewrite tkA_xmaps. exact (tv_xmaps _ _ _ TV).
        - intros x mt0 aib0 sl0 Hx Hrx. destruct (tv_grp_back _ _ _ TV x mt0 aib0 sl0 Hx Hrx) as (mt1 & aib1 & Hx1 & Hr1 & W1 & M1).
          destruct (Z.eq_dec x g) as [-> | Hxg].
          + rewrite Hg in Hx1. injection Hx1 as <-. rewrite Hr in Hr1. injection Hr1 as <- <-.
            exists (tk_mt mt aib slots i), aib, (tk_slots slots i). split; [apply tkA_meta_same|]. split; [apply tk_mt_role|].
            split; [rewrite tk_mt_w32; symmetry; exact W1|]. split; [rewrite tk_mt_mem; symmetry; exact M1|].
            split; [unfold tk_slots; apply list_set_length|].
            intros j st Hj Hst. destruct (Nat.eq_dec j (Z.to_nat i)) as [-> | Hnj]; [rewrite Hidle in Hj; injection Hj as <-; exfalso; exact (Hst eq_refl)|].
            rewrite (tk_slots_other slots i j Hnj). exact Hj.
          + exists mt1, aib1, sl0. unfold A'. rewrite (tkA_meta_other A1 g mt aib slots i x Hxg). rewrite W1, M1. repeat split; auto.
        - intros _. left. unfold A'. rewrite tkA_areas, pf_areas1. split; [reflexivity|]. replace (spare (tkA A1 g mt aib slots i)) with (spare A1) by reflexivity. rewrite pf_spare1. lia. }
      assert (HFR : FR A s A' s').
      { apply (FR_trans _ _ _ _ _ _ pf_FR1). apply (FR_of_ntframe A1 A' s1 s' NF'); [| unfold A'; apply tkA_live].
        intros x [Hc | Hd]; [left; exact Hc | right]. apply (proj2 (dom_tkA A1 g mt aib slots i Hg Hr x)). exact Hd. }
      split; [exact HFR|]. split.
      { constructor.
        - exact KEEP.
        - intros x mtx aibx slx Hx Hrx. left. destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & aib0 & sl0 & H0 & R0 & _). exists mt0, aib0, sl0. auto.
        - intros mt0 aib0 sl0 Hx0 Hr0. destruct (tv_grp_back _ _ _ TV g mt0 aib0 sl0 Hx0 Hr0) as (mt1 & aib1 & Hx1 & Hr1 & _).
          rewrite Hg in Hx1. injection Hx1 as <-. rewrite Hr in Hr1. injection Hr1 as <- <-. exact Hidle.
        - intros mtx aibx slx _ _ Hnew. exfalso. destruct (tv_grp _ _ _ TV g mt aib slots Hg Hr) as (mt0 & aib0 & H0 & R0 & _). exact (Hnew mt0 aib0 slots H0 R0).
        - intros _ x mtx aibx slx Hx Hrx _. destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & aib0 & sl0 & H0 & R0 & _). exists mt0, aib0, sl0. auto.
        - intros mtx aibx slx _ _ Hnew. exfalso. destruct (tv_grp _ _ _ TV g mt aib slots Hg Hr) as (mt0 & aib0 & H0 & R0 & _). exact (Hnew mt0 aib0 slots H0 R0).
        - intros mtx aibx slx Hx Hrx Hshort. exfalso. unfold A' in Hx. rewrite (tkA_meta_same A1 g mt aib slots i) in Hx. injection Hx as <-.
          rewrite tk_mt_stride in Hshort. lia.
        - intros _. left. unfold A'. rewrite tkA_areas, pf_areas1. split; [reflexivity|].
          replace (spare (tkA A1 g mt aib slots i)) with (spare A1) by reflexivity. rewrite pf_spare1. lia. }
      split; [exact (gnew_refl_groups A A' (ms_mem s) GB)|].
      split.
      { constructor.
        - intros b sz Hin. rewrite (nf_vm _ _ _ NF'), (nf_vm _ _ _ NF1). exact Hin.
        - intros b sz Hin Hf. rewrite (nf_vm _ _ _ NF'), (nf_vm _ _ _ NF1). exact Hf.
        - intros _. rewrite (nf_vm _ _ _ NF'), (nf_vm _ _ _ NF1). lia. }
      split; [unfold A'; rewrite tkA_ctx, (wf_act_head A1 HW1 sc Hsc), <- Hhd; reflexivity|].
      split; [unfold A'; rewrite tkA_active; exact Hhd|].
      split; [unfold A'; rewrite tkA_active; exact Hne1|].
      split; [apply tkA_meta_same|]. split; [apply tk_mt_role|]. split; [rewrite tk_mt_sc; exact Hgsc|].
      split; [rewrite tk_mt_last; lia|].
      split; [exact (tk_slots_i A1 HW1 sc g mt aib slots i Hsc Hhd Hne1 Hg Hr ltac:(lia) Hbit)|].
      split; [rewrite tk_mt_stride; lia|]. split; [rewrite tk_mt_stride; exact Hstride|].
      apply pf_had_idle1. exists g, mt, aib, slots, (Z.to_nat i). rewrite Hgsc. split; [exact Hg|]. split; [exact Hr|]. split; [lia | exact Hidle].
    Qed.
  End TakeLeaf.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section NoneBranch.
  Hypothesis Hact1 : a_active A1 sc = [].

  (* [comment removed for export] *)
  Section AmFail.
    Variables (A2 : astate) (s2 : mstate).
    Hypothesis HII2 : II sp0 argv envp cb D A2 s2.
    Hypothesis FR2 : FR A1 s1 A2 s2.
    Hypothesis GS : gsame A1 A2.
    Hypothesis AM : AMvm A1 A2 s1 s2.
    Hypothesis Hxm2 : a_xmaps A2 = a_xmaps A1.
    Hypothesis DOM2 : forall x, dom A2 x <-> dom A1 x.
    Hypothesis SP0 : spare A1 = 0.
    Hypothesis AR2 : a_areas A2 = a_areas A1.
    Let HW2 : WF A2 := is_wf _ _ _ _ _ _ (ii_is HII2).

    Lemma amfail_leaf : FR A s A2 s2 /\ aslot_fail A A2 sc (ms_mem s) /\ aslot_vm A sc s s2 /\ (~ am_budget A1 s1 -> inoroom A s (4 - nest_rank sc)).
    Proof using AM AR2 DOM2 FR2 GS HW2 Hsc Hxm2 NF1 SP0 TV. pu_keep (AM, AR2, DOM2, FR2, GS, HW2, Hsc, Hxm2, NF1, SP0, TV).
      pose proof (nest_rank_range sc) as Hnr. pose proof pf_spare1 as S1. pose proof pf_areas1 as E1.
      assert (GB : forall y mt' aib' sl', a_meta A2 y = Some mt' -> mt_role mt' = RGroup aib' sl' ->
        exists mt0 aib0, a_meta A y = Some mt0 /\ mt_role mt0 = RGroup aib0 sl' /\ mt_w32 mt0 = mt_w32 mt' /\ mt_mem mt0 = mt_mem mt').
      { intros y mt' aib' sl' Hy Hry. pose proof (gs_grp_back _ _ GS y mt' aib' sl' Hy Hry) as Hy1.
        destruct (tv_grp _ _ _ TV y mt' aib' sl' Hy1 Hry) as (mt0 & aib0 & H0 & R0 & W & M). exists mt0, aib0. auto. }
      assert (KEEP : aslot_keep A A2 sc (ms_mem s)).
      { constructor.
        - rewrite (gs_live _ _ GS). exact (tv_live _ _ _ TV).
        - intros x mtx Hx Hrx. apply (gs_dead _ _ GS x mtx); [| exact Hrx]. apply (tv_other _ _ _ TV x mtx Hx). intros aib0 sl0 E. rewrite Hrx in E. discriminate E.
        - intros x Hd. apply (proj2 (DOM2 x)). apply (proj2 (tv_dom _ _ _ TV x)). exact Hd.
        - intros x Hd. left. apply (proj1 (tv_dom _ _ _ TV x)). apply (proj1 (DOM2 x)). exact Hd.
        - intros c Hc _. rewrite (gs_active _ _ GS c). exact (tv_act _ _ _ TV c Hc).
        - rewrite Hxm2. exact (tv_xmaps _ _ _ TV).
        - intros x mt0 aib0 sl0 Hx Hrx. destruct (tv_grp_back _ _ _ TV x mt0 aib0 sl0 Hx Hrx) as (mt1 & aib1 & Hx1 & Hr1 & W1 & M1).
          exists mt1, aib1, sl0. split; [exact (gs_grp _ _ GS x mt1 aib1 sl0 Hx1 Hr1)|]. rewrite W1, M1. repeat split; auto.
        - intros Hpre. left. rewrite AR2, E1. split; [reflexivity|]. pose proof (spare_nonneg A2 HW2). lia. }
      split; [exact (FR_trans _ _ _ _ _ _ pf_FR1 FR2)|].
      split.
      { constructor.
        - exact KEEP.
        - intros x mt0 aib0 sl0 Hx Hrx. destruct (tv_grp_back _ _ _ TV x mt0 aib0 sl0 Hx Hrx) as (mt1 & aib1 & Hx1 & Hr1 & _).
          exists mt1, aib1. split; [exact (gs_grp _ _ GS x mt1 aib1 sl0 Hx1 Hr1) | exact Hr1].
        - intros x mt' aib' sl' Hx Hrx. destruct (GB x mt' aib' sl' Hx Hrx) as (mt0 & aib0 & H0 & R0 & _). exists mt0, aib0. auto.
        - left. rewrite AR2, E1. split; [reflexivity|]. pose proof (spare_nonneg A2 HW2). lia. }
      split.
      { constructor.
        - intros b sz Hin. apply (amv_maps _ _ _ _ AM). rewrite (nf_vm _ _ _ NF1). exact Hin.
        - intros b sz Hin Hf. apply (amv_acc _ _ _ _ AM); rewrite (nf_vm _ _ _ NF1); assumption.
        - intros Hpre. assert (E0 : a_areas A1 = []) by (rewrite E1; destruct Hpre as [H|H]; [exact H | exfalso; lia]).
          pose proof (amv_budget _ _ _ _ AM E0) as B. rewrite (nf_vm _ _ _ NF1) in B. lia. }
      intros NB. split; [intros Hk; exfalso; lia|].
      intros E0. left. intros [Hb Hor]. apply NB. right. rewrite (nf_vm _ _ _ NF1). split; [exact Hb|].
      destruct Hor as [HK | (a & Ha)]; [left | right].
      - rewrite (tv_ctx _ _ _ TV KAac I ltac:(discriminate) ltac:(intros H; exact H)). exact HK.
      - split; [rewrite E1; exact E0|]. exists a. exact Ha.
    Qed.
  End AmFail.

Section Prefix.
  Variables (A2 : astate) (s2 : mstate) (m : Z).
  (* [comment removed for export] *)
  Hypothesis HII2 : II sp0 argv envp cb (m :: D) A2 s2.
  Hypothesis FR2 : FR A1 s1 A2 s2.
  Hypothesis GM : got_meta A1 D A2 m.
  Hypothesis AM : AMvm A1 A2 s1 s2.
  Hypothesis Hxm2 : a_xmaps A2 = a_xmaps A1.
  Hypothesis SPARE : (0 < spare A1 /\ ms_vm s2 = ms_vm s1 /\ a_areas A2 = a_areas A1 /\ spare A2 = spare A1 - 1)
                     \/ (spare A1 = 0 /\ a_areas A2 = a_areas A1 ++ [m - 24] /\ a_ctx A2 KAmc = 100 /\ a_freelist A2 = []).

  Let HW2 : WF A2 := is_wf _ _ _ _ _ _ (ii_is HII2).
  Let GS : gsame A1 A2 := gm_gsame _ _ _ _ GM.


  Lemma pf_FR : FR A s A2 s2.
  Proof using FR2 NF1 TV. pu_keep (FR2, NF1, TV). exact (FR_trans _ _ _ _ _ _ pf_FR1 FR2). Qed.

  Lemma pf_md : exists md, a_meta A2 m = Some md /\ mt_role md = RDead /\ forall fl, mt_f md fl = 0.
  Proof using GM. pu_keep (GM). exact (gm_meta _ _ _ _ GM). Qed.

  Lemma pf_mD : ~ In m D. Proof using GM. pu_keep (GM). exact (gm_fresh _ _ _ _ GM). Qed.

  Lemma pf_live : a_live A2 = a_live A.
  Proof using GS TV. pu_keep (GS, TV). rewrite (gs_live _ _ GS). exact (tv_live _ _ _ TV). Qed.

  (* [comment removed for export] *)
  Lemma pf_m_A1 : forall mt, a_meta A1 m = Some mt -> mt_role mt <> RDead /\ forall aib sl, mt_role mt <> RGroup aib sl.
  Proof using GS HII1. pu_keep (GS, HII1).
    intros mt Hm. destruct pf_md as (md & Hmd & Hrd & _). split.
    - intros Hr. apply pf_mD. apply (proj1 (ii_dd HII1 m)). exists mt. auto.
    - intros aib sl Hr. pose proof (gs_grp _ _ GS m mt aib sl Hm Hr) as Hm2. rewrite Hmd in Hm2. injection Hm2 as ->. rewrite Hr in Hrd. discriminate Hrd.
  Qed.

  Lemma pf_m_A : forall mt, a_meta A m = Some mt -> mt_role mt <> RDead /\ forall aib sl, mt_role mt <> RGroup aib sl.
  Proof using GS HII1 TV. pu_keep (GS, HII1, TV).
    intros mt Hm. split.
    - intros Hr. pose proof (tv_other _ _ _ TV m mt Hm ltac:(intros aib sl E; rewrite Hr in E; discriminate E)) as Hm1.
      exact (proj1 (pf_m_A1 mt Hm1) Hr).
    - intros aib sl Hr. destruct (tv_grp_back _ _ _ TV m mt aib sl Hm Hr) as (mtx & aibx & Hx & Hrx & _). exact (proj2 (pf_m_A1 mtx Hx) aibx sl Hrx).
  Qed.

  Lemma pf_dead : forall x mt, a_meta A x = Some mt -> mt_role mt = RDead -> a_meta A2 x = Some mt.
  Proof using GS TV. pu_keep (GS, TV).
    intros x mt Hx Hr. apply (gs_dead _ _ GS x mt); [| exact Hr].
    apply (tv_other _ _ _ TV x mt Hx). intros aib sl E. rewrite Hr in E. discriminate E.
  Qed.

  (* [comment removed for export] *)
  Lemma pf_grp : forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl ->
    exists mt' aib', a_meta A2 x = Some mt' /\ mt_role mt' = RGroup aib' sl /\ mt_w32 mt' = mt_w32 mt /\ mt_mem mt' = mt_mem mt.
  Proof using GS TV. pu_keep (GS, TV).
    intros x mt aib sl Hx Hr. destruct (tv_grp_back _ _ _ TV x mt aib sl Hx Hr) as (mt1 & aib1 & Hx1 & Hr1 & W1 & M1).
    exists mt1, aib1. split; [exact (gs_grp _ _ GS x mt1 aib1 sl Hx1 Hr1)|]. split; [exact Hr1|]. split; [symmetry; exact W1 | symmetry; exact M1].
  Qed.

  Lemma pf_grp_back : forall x mt' aib' sl', a_meta A2 x = Some mt' -> mt_role mt' = RGroup aib' sl' ->
    exists mt aib, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl' /\ mt_w32 mt = mt_w32 mt' /\ mt_mem mt = mt_mem mt'.
  Proof using GS TV. pu_keep (GS, TV).
    intros x mt' aib' sl' Hx Hr. pose proof (gs_grp_back _ _ GS x mt' aib' sl' Hx Hr) as Hx1.
    destruct (tv_grp _ _ _ TV x mt' aib' sl' Hx1 Hr) as (mt & aib & H1 & H2 & W & M). exists mt, aib. auto.
  Qed.

  Lemma pf_gdom : forall x, gdom A2 x -> gdom A x.
  Proof using GS TV. pu_keep (GS, TV).
    apply gdom_transfer. intros y mt' aib' sl' Hy Hr. destruct (pf_grp_back y mt' aib' sl' Hy Hr) as (mt & aib & H1 & H2 & W & M).
    exists mt, aib, sl'. auto.
  Qed.

  Lemma pf_dom : forall x, dom A x -> dom A2 x.
  Proof using FR2 HW1 MLok TV. pu_keep (FR2, HW1, MLok, TV). intros x Hd. apply (dom_of_FR A1 s1 A2 s2 HW1 FR2). apply (proj2 (tv_dom _ _ _ TV x)). exact Hd. Qed.

  Lemma pf_newdom : forall x, dom A2 x -> dom A x \/ (exists pg, (In pg (a_areas A2) \/ In pg (a_pages A2)) /\ pg <= x < pg + 4096).
  Proof using GS TV. pu_keep (GS, TV).
    intros x Hd. destruct (dom_cases A2 x Hd) as [Hg | Hp]; [left | right; exact Hp]. exact (gdom_dom A x (pf_gdom x Hg)).
  Qed.

  Lemma pf_act : forall c, c <> sc -> a_active A2 c = a_active A c.
  Proof using GS TV. pu_keep (GS, TV). intros c Hc. rewrite (gs_active _ _ GS c). exact (tv_act _ _ _ TV c Hc). Qed.

  Lemma pf_act_sc : a_active A2 sc = [].
  Proof using GS Hact1. pu_keep (GS, Hact1). rewrite (gs_active _ _ GS sc). exact Hact1. Qed.

  Lemma pf_xmaps : a_xmaps A2 = a_xmaps A.
  Proof using Hxm2 TV. pu_keep (Hxm2, TV). rewrite Hxm2. exact (tv_xmaps _ _ _ TV). Qed.



  Lemma pf_spare : (0 < spare A /\ ms_vm s2 = ms_vm s /\ a_areas A2 = a_areas A /\ spare A2 = spare A - 1)
                   \/ (spare A = 0 /\ a_areas A2 = a_areas A ++ [m - 24] /\ spare A2 = 100).
  Proof using NF1 SPARE TV. pu_keep (NF1, SPARE, TV).
    rewrite <- pf_spare1, <- pf_areas1. destruct SPARE as [(S1 & V & E & S2) | (S1 & E & K & F)]; [left | right].
    - rewrite V, (nf_vm _ _ _ NF1). auto.
    - split; [exact S1|]. split; [exact E|]. unfold spare. rewrite K, F. reflexivity.
  Qed.

  Lemma pf_areas : forall pg, In pg (a_areas A) -> In pg (a_areas A2).
  Proof using NF1 SPARE TV. pu_keep (NF1, SPARE, TV). intros pg Hpg. destruct pf_spare as [(_ & _ & E & _) | (_ & E & _)]; rewrite E; [exact Hpg | apply in_or_app; left; exact Hpg]. Qed.

  Lemma pf_maps : forall b sz, In (b, sz) (vm_maps (ms_vm s)) -> In (b, sz) (vm_maps (ms_vm s2)).
  Proof using AM NF1. pu_keep (AM, NF1). intros b sz Hin. apply (amv_maps _ _ _ _ AM). rewrite (nf_vm _ _ _ NF1). exact Hin. Qed.

  Lemma pf_acc : forall b sz, In (b, sz) (vm_maps (ms_vm s)) -> region_free (vm_noaccess (ms_vm s)) b sz = true ->
    region_free (vm_noaccess (ms_vm s2)) b sz = true.
  Proof using AM NF1. pu_keep (AM, NF1). intros b sz Hin Hf. apply (amv_acc _ _ _ _ AM); rewrite (nf_vm _ _ _ NF1); assumption. Qed.

  Lemma pf_limit : vm_limit (ms_vm s2) = vm_limit (ms_vm s).
  Proof using FR2 NF1 TV. pu_keep (FR2, NF1, TV). exact (fr_limit _ _ _ _ pf_FR). Qed.

  (* [comment removed for export] *)
  Lemma pf_budget : (a_areas A = [] \/ 0 < spare A) ->
    vm_live_bytes (ms_vm s2) <= vm_live_bytes (ms_vm s) + 12288 /\
    (0 < spare A -> ms_vm s2 = ms_vm s).
  Proof using AM Hsc NF1 SPARE TV. pu_keep (AM, Hsc, NF1, SPARE, TV).
    intros Hpre. split.
    - destruct pf_spare as [(_ & V & _ & _) | (S0 & _ & _)]; [rewrite V; lia|].
      destruct Hpre as [E | Hs]; [| lia]. rewrite <- (nf_vm _ _ _ NF1). apply (amv_budget _ _ _ _ AM). rewrite pf_areas1. exact E.
    - intros Hs. destruct pf_spare as [(_ & V & _ & _) | (S0 & _ & _)]; [exact V | lia].
  Qed.

  Lemma pf_usage : usage_of A2 sc = usage_of A sc.
  Proof using GS HII1 HII2 Hsc TV. pu_keep (GS, HII1, HII2, Hsc, TV).
    rewrite <- (ii_us HII2 sc Hsc). rewrite (gs_ctx _ _ GS (KUsage sc) I ltac:(cbn; lia)). rewrite (ii_us HII1 sc Hsc). exact pf_usage1.
  Qed.

  Lemma pf_had_idle : aslot_had_idle A2 -> aslot_had_idle A.
  Proof using GS TV. pu_keep (GS, TV).
    apply aslot_had_idle_transfer. intros x mt' aib' sl' Hx Hr. destruct (pf_grp_back x mt' aib' sl' Hx Hr) as (mt & aib & H1 & H2 & W & _). exists mt, aib. auto.
  Qed.

  (* [comment removed for export] *)
  Section Keep.
    Variable A' : astate.
    Hypothesis L_live : a_live A' = a_live A2.
    Hypothesis L_dead : forall x mt, a_meta A2 x = Some mt -> mt_role mt = RDead -> x <> m -> a_meta A' x = Some mt.
    Hypothesis L_dom : forall x, dom A2 x -> dom A' x.
    Hypothesis L_gnew : gnew A2 A' (ms_mem s2).
    Hypothesis L_act : forall c, c <> sc -> nest_rank c <= nest_rank sc -> a_active A' c = a_active A2 c.
    Hypothesis L_xmaps : a_xmaps A' = a_xmaps A2.
    Hypothesis L_grp : forall x mt aib sl, a_meta A2 x = Some mt -> mt_role mt = RGroup aib sl ->
      exists mt' aib' sl', a_meta A' x = Some mt' /\ mt_role mt' = RGroup aib' sl' /\
        mt_w32 mt' = mt_w32 mt /\ mt_mem mt' = mt_mem mt /\ length sl' = length sl /\
        (forall j st, nth_error sl j = Some st -> st <> SIdle -> nth_error sl' j = Some st).
    Hypothesis L_acct : (a_areas A2 = [] \/ 4 - nest_rank sc - 1 <= spare A2) ->
      (a_areas A' = a_areas A2 /\ spare A2 - (4 - nest_rank sc - 1) <= spare A') \/
      (a_areas A2 = [] /\ (exists pg, a_areas A' = [pg]) /\ 100 - (4 - nest_rank sc - 1) <= spare A').

    Lemma gnew_of_prefix : gnew A A' (ms_mem s).
    Proof using FR2 GS L_gnew NF1 TV. pu_keep (FR2, GS, L_gnew, NF1, TV).
      intros x Hg. destruct (L_gnew x Hg) as [Hg2 | Hn]; [left; exact (pf_gdom x Hg2) | right].
      exact (none_of_FR A s A2 s2 pf_FR _ Hn).
    Qed.

    Lemma keep_of_prefix : aslot_keep A A' sc (ms_mem s).
    Proof using FR2 GS HW1 Hsc Hxm2 L_acct L_act L_dead L_dom L_gnew L_grp L_live L_xmaps MLok NF1 SPARE TV. pu_keep (FR2, GS, HW1, Hsc, Hxm2, L_acct, L_act, L_dead, L_dom, L_gnew, L_grp, L_live, L_xmaps, MLok, NF1, SPARE, TV).
      pose proof (nest_rank_range sc) as Hnr.
      constructor.
      - rewrite L_live. exact pf_live.
      - intros x mt Hx Hr. apply (L_dead x mt (pf_dead x mt Hx Hr) Hr). intros ->. exact (proj1 (pf_m_A mt Hx) Hr).
      - intros x Hd. exact (L_dom x (pf_dom x Hd)).
      - exact (newdom_of_gnew A A' (ms_mem s) gnew_of_prefix).
      - intros c Hc Hr. rewrite (L_act c Hc Hr). exact (pf_act c Hc).
      - rewrite L_xmaps. exact pf_xmaps.
      - intros x mt aib sl Hx Hr. destruct (pf_grp x mt aib sl Hx Hr) as (mt2 & aib2 & Hx2 & Hr2 & W2 & M2).
        destruct (L_grp x mt2 aib2 sl Hx2 Hr2) as (mt' & aib' & sl' & Hx' & Hr' & W' & M' & Ln & K').
        exists mt', aib', sl'. rewrite W', M'. auto 10.
      - intros Hpre. destruct pf_spare as [(S0 & _ & E & S2) | (S0 & E & S2)].
        + destruct (L_acct ltac:(destruct Hpre as [H|H]; [left; rewrite E; exact H | right; lia])) as [(E' & S') | (E0 & (pg & E') & S')].
          * left. rewrite E', E. split; [reflexivity | lia].
          * right. rewrite E in E0. split; [exact E0|]. split; [exists pg; exact E' | lia].
        + assert (E0 : a_areas A = []) by (destruct Hpre as [H|H]; [exact H | exfalso; lia]).
          rewrite E0 in E. cbn [app] in E.
          destruct (L_acct ltac:(right; lia)) as [(E' & S') | (E2 & _ & _)]; [| rewrite E in E2; discriminate E2].
          right. split; [exact E0|]. split; [exists (m - 24); rewrite E'; exact E | lia].
    Qed.
  End Keep.

  (* [comment removed for export] *)
  Section Vm.
    Variable s' : mstate.
    Hypothesis V_maps : forall b sz, In (b, sz) (vm_maps (ms_vm s2)) -> In (b, sz) (vm_maps (ms_vm s')).
    Hypothesis V_acc : forall b sz, In (b, sz) (vm_maps (ms_vm s2)) ->
      region_free (vm_noaccess (ms_vm s2)) b sz = true -> region_free (vm_noaccess (ms_vm s')) b sz = true.
    Hypothesis V_budget : (a_areas A2 = [] \/ 4 - nest_rank sc - 1 <= spare A2) ->
      vm_live_bytes (ms_vm s') <= vm_live_bytes (ms_vm s2) + (4 - nest_rank sc - 1) * 2^21 + (2^21 - 12288).

    Lemma vm_of_prefix : aslot_vm A sc s s'.
    Proof using AM Hsc NF1 SPARE TV V_acc V_budget V_maps. pu_keep (AM, Hsc, NF1, SPARE, TV, V_acc, V_budget, V_maps).
      pose proof (nest_rank_range sc) as Hnr. constructor.
      - intros b sz Hin. exact (V_maps b sz (pf_maps b sz Hin)).
      - intros b sz Hin Hf. exact (V_acc b sz (pf_maps b sz Hin) (pf_acc b sz Hin Hf)).
      - intros Hpre. destruct pf_spare as [(S0 & V & E & S2) | (S0 & E & S2)].
        + specialize (V_budget ltac:(destruct Hpre as [H|H]; [left; rewrite E; exact H | right; lia])). rewrite V in V_budget. lia.
        + assert (E0 : a_areas A = []) by (destruct Hpre as [H|H]; [exact H | exfalso; lia]).
          pose proof (proj1 (pf_budget (or_introl E0))) as B. specialize (V_budget ltac:(right; lia)). lia.
    Qed.
  End Vm.

  (* [comment removed for export] *)
  Lemma inoroom_of_prefix : forall k, 1 <= k <= 4 ->
    (k - 1 <= spare A2 -> refusal (ms_vm s2)) ->
    (a_areas A1 = [] -> am_delta (ms_vm s1) (ms_vm s2)) ->
    inoroom A s k.
  Proof using HW Hsc NF1 SPARE TV. pu_keep (HW, Hsc, NF1, SPARE, TV).
    intros k Hk H AMD. split.
    - intros Hsp. destruct pf_spare as [(S0 & V & E & S2) | (S0 & E & S2)]; [| lia]. rewrite <- V. apply H. lia.
    - intros E0. right. pose proof (spare_nil_areas A HW E0) as SP0.
      destruct pf_spare as [(S0 & _ & _ & _) | (_ & E & S2)]; [lia|].
      exists (ms_vm s2). split; [| apply H; lia]. rewrite <- (nf_vm _ _ _ NF1). apply AMD. rewrite pf_areas1. exact E0.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section NestFail.
    Variables (j : Z) (A3 : astate) (s3 : mstate) (A4 : astate) (s4 : mstate).
    Hypothesis Hj : 0 <= j < 48.
    Hypothesis Hrk : nest_rank sc < nest_rank j.
    Hypothesis HII3 : II sp0 argv envp cb (m :: D) A3 s3.
    Hypothesis FR3 : FR A2 s2 A3 s3.
    Hypothesis AF3 : aslot_fail A2 A3 j (ms_mem s2).
    Hypothesis AV3 : aslot_vm A2 j s2 s3.
    (* [comment removed for export] *)
    Hypothesis HII4 : II sp0 argv envp cb D A4 s4.
    Hypothesis NF4 : ntframe A3 s3 s4.
    Hypothesis F_live : a_live A4 = a_live A3.
    Hypothesis F_grp : forall x mt aib sl, a_meta A3 x = Some mt -> mt_role mt = RGroup aib sl -> a_meta A4 x = Some mt.
    Hypothesis F_grp_back : forall x mt' aib sl, a_meta A4 x = Some mt' -> mt_role mt' = RGroup aib sl -> a_meta A3 x = Some mt'.
    Hypothesis F_dom : forall x, dom A4 x <-> dom A3 x.
    Hypothesis F_act : a_active A4 = a_active A3.
    Hypothesis F_xmaps : a_xmaps A4 = a_xmaps A3.
    Hypothesis F_areas : a_areas A4 = a_areas A3.
    Hypothesis F_amc : a_ctx A4 KAmc = a_ctx A3 KAmc.
    Hypothesis F_fl : a_freelist A4 = a_freelist A3 ++ [m].
    Hypothesis F_dead : forall x mt, x <> m -> a_meta A3 x = Some mt -> mt_role mt = RDead -> a_meta A4 x = Some mt.

    Lemma nestfail_leaf :
      FR A s A4 s4 /\ aslot_fail A A4 sc (ms_mem s) /\ aslot_vm A sc s s4 /\
      (inoroom A2 s2 (4 - nest_rank j) -> (a_areas A1 = [] -> am_delta (ms_vm s1) (ms_vm s2)) -> inoroom A s (4 - nest_rank sc)).
    Proof using AF3 AM AV3 FR2 FR3 F_act F_amc F_areas F_dead F_dom F_fl F_grp F_grp_back F_live F_xmaps GS HII3 HW HW1 Hj Hrk Hsc Hxm2 MLok NF1 NF4 SPARE TV. pu_keep (AF3, AM, AV3, FR2, FR3, F_act, F_amc, F_areas, F_dead, F_dom, F_fl, F_grp, F_grp_back, F_live, F_xmaps, GS, HII3, HW, HW1, Hj, Hrk, Hsc, Hxm2, MLok, NF1, NF4, SPARE, TV).
      pose proof (nest_rank_range sc) as Hnr. pose proof (nest_rank_range j) as Hnrj.
      pose proof (af_keep _ _ _ _ AF3) as K3. pose proof (is_wf _ _ _ _ _ _ (ii_is HII3)) as HW3.
      assert (Hjsc : j <> sc) by (intros ->; lia).
      (* [comment removed for export] *)
      assert (GB3 : forall y mt' aib' sl', a_meta A3 y = Some mt' -> mt_role mt' = RGroup aib' sl' ->
        exists mt0 aib0, a_meta A2 y = Some mt0 /\ mt_role mt0 = RGroup aib0 sl' /\ mt_w32 mt0 = mt_w32 mt' /\ mt_mem mt0 = mt_mem mt').
      { intros y mt' aib' sl' Hy Hry. destruct (af_grp_back _ _ _ _ AF3 y mt' aib' sl' Hy Hry) as (mt0 & aib0 & H0 & R0).
        destruct (ak_grp _ _ _ _ K3 y mt0 aib0 sl' H0 R0) as (mt1 & aib1 & sl1 & H1 & R1 & W1 & M1 & _).
        rewrite Hy in H1. injection H1 as <-. exists mt0, aib0. rewrite <- W1, <- M1. auto. }
      assert (SP4 : spare A4 = spare A3 + 1) by (unfold spare; rewrite F_amc, F_fl, length_app; cbn [length]; lia).
      assert (KEEP : aslot_keep A A4 sc (ms_mem s)).
      { apply keep_of_prefix.
        - rewrite F_live. exact (ak_live _ _ _ _ K3).
        - intros x mtx Hx Hrx Hxm. apply (F_dead x mtx Hxm); [| exact Hrx]. exact (ak_dead _ _ _ _ K3 x mtx Hx Hrx).
        - intros x Hd. apply (proj2 (F_dom x)). exact (ak_dom _ _ _ _ K3 x Hd).
        - apply gnew_refl_groups. intros y mt' aib' sl' Hy Hry. pose proof (F_grp_back y mt' aib' sl' Hy Hry) as Hy3.
          destruct (GB3 y mt' aib' sl' Hy3 Hry) as (mt0 & aib0 & H0 & R0 & W & M). exists mt0, aib0, sl'. auto.
        - intros c Hc Hr. rewrite F_act. apply (ak_act _ _ _ _ K3 c); [intros ->; lia | lia].
        - rewrite F_xmaps. exact (ak_xmaps _ _ _ _ K3).
        - intros x mt0 aib0 sl0 Hx Hrx. destruct (af_slots _ _ _ _ AF3 x mt0 aib0 sl0 Hx Hrx) as (mt' & aib' & Hx' & Hr').
          destruct (ak_grp _ _ _ _ K3 x mt0 aib0 sl0 Hx Hrx) as (mt1 & aib1 & sl1 & H1 & R1 & W1 & M1 & _).
          rewrite Hx' in H1. injection H1 as <-. rewrite Hr' in R1. injection R1 as <- <-.
          exists mt', aib', sl0. split; [exact (F_grp x mt' aib' sl0 Hx' Hr')|]. rewrite W1, M1. repeat split; auto.
        - intros Hpre. rewrite F_areas, SP4.
          destruct (ak_acct _ _ _ _ K3 ltac:(destruct Hpre as [H|H]; [left; exact H | right; lia])) as [(E & S) | (E0 & (pg & E) & S)]; [left | right].
          + rewrite E. split; [reflexivity | lia].
          + split; [exact E0|]. split; [exists pg; exact E | lia]. }
      split.
      { apply (FR_trans _ _ _ _ _ _ pf_FR). apply (FR_trans _ _ _ _ _ _ FR3).
        apply (FR_of_ntframe A3 A4 s3 s4 NF4); [| exact F_live]. intros x [Hc | Hd]; [left; exact Hc | right]. apply (proj2 (F_dom x)). exact Hd. }
      split.
      { constructor.
        - exact KEEP.
        - intros x mt0 aib0 sl0 Hx Hrx. destruct (pf_grp x mt0 aib0 sl0 Hx Hrx) as (mt2 & aib2 & Hx2 & Hr2 & _).
          destruct (af_slots _ _ _ _ AF3 x mt2 aib2 sl0 Hx2 Hr2) as (mt' & aib' & Hx' & Hr'). exists mt', aib'. split; [exact (F_grp x mt' aib' sl0 Hx' Hr') | exact Hr'].
        - intros x mt' aib' sl' Hx Hrx. pose proof (F_grp_back x mt' aib' sl' Hx Hrx) as Hx3.
          destruct (af_grp_back _ _ _ _ AF3 x mt' aib' sl' Hx3 Hrx) as (mt2 & aib2 & Hx2 & Hr2).
          destruct (pf_grp_back x mt2 aib2 sl' Hx2 Hr2) as (mt0 & aib0 & H0 & R0 & _). exists mt0, aib0. auto.
        - rewrite F_areas, SP4. destruct pf_spare as [(S0 & _ & E & S2) | (S0 & E & S2)].
          + destruct (af_acct0 _ _ _ _ AF3) as [(E3 & S3) | (G3 & (pg & E3) & S3)].
            * left. rewrite E3, E. split; [reflexivity | lia].
            * right. split; [lia|]. split; [exists pg; rewrite E3, E; reflexivity | lia].
          + destruct (af_acct0 _ _ _ _ AF3) as [(E3 & S3) | (G3 & _ & _)]; [| exfalso; lia].
            right. split; [lia|]. split; [exists (m - 24); rewrite E3, E; reflexivity | lia]. }
      split.
      { apply vm_of_prefix.
        - intros b sz Hin. rewrite (nf_vm _ _ _ NF4). exact (av_maps _ _ _ _ AV3 b sz Hin).
        - intros b sz Hin Hf. rewrite (nf_vm _ _ _ NF4). exact (av_acc _ _ _ _ AV3 b sz Hin Hf).
        - intros Hpre. rewrite (nf_vm _ _ _ NF4). pose proof (av_budget _ _ _ _ AV3 ltac:(destruct Hpre as [H|H]; [left; exact H | right; lia])) as B.
          assert (M : (4 - nest_rank j) * 2^21 <= (4 - nest_rank sc - 1) * 2^21) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
      intros [INR1 _] AMD. apply (inoroom_of_prefix (4 - nest_rank sc)); [lia| |exact AMD]. intros Hsp. apply INR1. lia.
    Qed.
  End NestFail.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section MmapFail.
    Variables (A3 : astate) (s3 : mstate).
    Hypothesis HII3 : II sp0 argv envp cb D A3 s3.
    Hypothesis FR3 : FR A2 s2 A3 s3.
    Hypothesis Hvm3 : ms_vm s3 = ms_vm s2.
    Hypothesis AGF : agfail A2 A3 m.
    Hypothesis F_dead : forall x mt, a_meta A2 x = Some mt -> mt_role mt = RDead -> x <> m -> a_meta A3 x = Some mt.
    Hypothesis F_fl : a_freelist A3 = a_freelist A2 ++ [m].

    Lemma mmapfail_leaf :
      FR A s A3 s3 /\ aslot_fail A A3 sc (ms_mem s) /\ aslot_vm A sc s s3 /\
      (refusal (ms_vm s2) -> (a_areas A1 = [] -> am_delta (ms_vm s1) (ms_vm s2)) -> inoroom A s (4 - nest_rank sc)).
    Proof using AGF AM FR2 FR3 F_dead F_fl GS HW HW1 Hsc Hvm3 Hxm2 MLok NF1 SPARE TV. pu_keep (AGF, AM, FR2, FR3, F_dead, F_fl, GS, HW, HW1, Hsc, Hvm3, Hxm2, MLok, NF1, SPARE, TV).
      pose proof (nest_rank_range sc) as Hnr.
      assert (SP3 : spare A3 = spare A2 + 1).
      { unfold spare. rewrite F_fl, length_app. cbn [length]. rewrite (af_ctx _ _ _ AGF KAmc I ltac:(discriminate) ltac:(intros H; exact H)). lia. }
      assert (KEEP : aslot_keep A A3 sc (ms_mem s)).
      { apply keep_of_prefix.
        - exact (af_live _ _ _ AGF).
        - exact F_dead.
        - intros x Hd. apply (proj2 (af_dom _ _ _ AGF x)). exact Hd.
        - apply gnew_refl_groups. intros y mt' aib' sl' Hy Hry. exists mt', aib', sl'. split; [exact (af_grp _ _ _ AGF y mt' aib' sl' Hy Hry) | auto].
        - intros c Hc _. rewrite (af_active _ _ _ AGF). reflexivity.
        - exact (af_xmaps _ _ _ AGF).
        - intros x mt0 aib0 sl0 Hx Hrx. exists mt0, aib0, sl0. split; [exact (MallocInv_agrp_iface.af_grp_back _ _ _ AGF x mt0 aib0 sl0 Hx Hrx) | repeat split; auto].
        - intros Hpre. left. rewrite (af_areas _ _ _ AGF), SP3. split; [reflexivity | lia]. }
      split; [exact (FR_trans _ _ _ _ _ _ pf_FR FR3)|].
      split.
      { constructor.
        - exact KEEP.
        - intros x mt0 aib0 sl0 Hx Hrx. destruct (pf_grp x mt0 aib0 sl0 Hx Hrx) as (mt2 & aib2 & Hx2 & Hr2 & _).
          exists mt2, aib2. split; [exact (MallocInv_agrp_iface.af_grp_back _ _ _ AGF x mt2 aib2 sl0 Hx2 Hr2) | exact Hr2].
        - intros x mt' aib' sl' Hx Hrx. pose proof (af_grp _ _ _ AGF x mt' aib' sl' Hx Hrx) as Hx2.
          destruct (pf_grp_back x mt' aib' sl' Hx2 Hrx) as (mt0 & aib0 & H0 & R0 & _). exists mt0, aib0. auto.
        - rewrite (af_areas _ _ _ AGF), SP3. destruct pf_spare as [(S0 & _ & E & S2) | (S0 & E & S2)].
          + left. rewrite E. split; [reflexivity | lia].
          + right. split; [lia|]. split; [exists (m - 24); exact E | lia]. }
      split.
      { apply vm_of_prefix.
        - intros b sz Hin. rewrite Hvm3. exact Hin.
        - intros b sz Hin Hf. rewrite Hvm3. exact Hf.
        - intros _. rewrite Hvm3. lia. }
      intros NR AMD. apply (inoroom_of_prefix (4 - nest_rank sc)); [lia | intros _; exact NR | exact AMD].
    Qed.
  End MmapFail.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section NestOk.
    Variables (md : meta_rec) (j gj idx : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (cnt1 req : Z) (A3 : astate) (s3 : mstate).
    Hypothesis Hmd2 : a_meta A2 m = Some md.
    Hypothesis Hrd : mt_role md = RDead.
    Hypothesis Hmd0 : forall fl, mt_f md fl = 0.
    Hypothesis Hj15 : j = 15 \/ j = 19 \/ j = 23.
    Hypothesis Hrk : nest_rank sc < nest_rank j.
    Hypothesis Hcnt1 : 2 <= cnt1 <= 32.
    Hypothesis Hfitj : 16 * size_class sc * cnt1 + 16 <= 16 * size_class j.
    Hypothesis Hsmall : 16 * size_class sc * cnt1 + 16 <= 2048.
    Hypothesis Hreq : 0 <= req /\ req + 4 <= 16 * size_class sc.
    (* [comment removed for export] *)
    Hypothesis HII3 : II sp0 argv envp cb (m :: D) A3 s3.
    Hypothesis FR3 : FR A2 s2 A3 s3.
    Hypothesis AO3 : aslot_ok A2 A3 j (16 * size_class sc * cnt1 + 12) gj idx (ms_mem s2) s3.
    Hypothesis GN3 : gnew A2 A3 (ms_mem s2).
    Hypothesis AV3 : aslot_vm A2 j s2 s3.
    Hypothesis Hgj3 : a_ctx A3 (KActive j) = gj.
    Hypothesis Hmt3 : a_meta A3 gj = Some mt.
    Hypothesis Hrl3 : mt_role mt = RGroup aib slots.
    Hypothesis Hscj : mt_sc mt = j.
    Hypothesis Hidx : 0 <= idx <= mt_last mt.
    Hypothesis Hslot : nth_error slots (Z.to_nat idx) = Some STaken.
    Hypothesis Hstr3 : 16 * size_class j <= mt_stride mt \/
      (mt_last mt = 0 /\ 0 < mt_maplen mt /\ mt_stride mt + 16 = page_round_up_Z (16 * size_class sc * cnt1 + 12 + 20)).

    Let HW3 : WF A3 := is_wf _ _ _ _ _ _ (ii_is HII3).
    Let K3 : aslot_keep A2 A3 j (ms_mem s2) := ao_keep _ _ _ _ _ _ _ _ AO3.

    Lemma no_Hj : 0 <= j < 48. Proof using Hj15. pu_keep (Hj15). exact (proj1 (size_class_15_19_23 j Hj15)). Qed.
    Lemma no_jsc : j <> sc. Proof using Hrk Hsc. pu_keep (Hrk, Hsc). intros E. rewrite E in Hrk. lia. Qed.
    Lemma no_m3 : a_meta A3 m = Some md. Proof using Hmd2 Hrd K3. pu_keep (Hmd2, Hrd, K3). exact (ak_dead _ _ _ _ K3 m md Hmd2 Hrd). Qed.
    Lemma no_act3 : a_active A3 sc = [].
    Proof using GS Hact1 Hrk Hsc K3. pu_keep (GS, Hact1, Hrk, Hsc, K3). rewrite (ak_act _ _ _ _ K3 sc (not_eq_sym no_jsc) ltac:(lia)). exact pf_act_sc. Qed.
    Lemma no_gjm : gj <> m.
    Proof using Hidx Hmd2 Hmt3 Hrd Hrl3 Hscj Hstr3 K3. pu_keep (Hidx, Hmd2, Hmt3, Hrd, Hrl3, Hscj, Hstr3, K3). intros E. rewrite E, no_m3 in Hmt3. injection Hmt3 as <-. rewrite Hrd in Hrl3. discriminate Hrl3. Qed.
    Lemma no_stride : mt_stride mt = 16 * size_class j.
    Proof using HW3 Hcnt1 Hj15 Hmt3 Hrl3 Hsc Hscj Hstr3. pu_keep (HW3, Hcnt1, Hj15, Hmt3, Hrl3, Hsc, Hscj, Hstr3).
      pose proof (size_class_15_19_23 j Hj15) as (_ & S256 & S31). pose proof (szc_rng sc Hsc) as SZC.
      assert (SG : mt_last mt = 0 -> 0 < mt_maplen mt -> mt_stride mt <= 16 * size_class j).
      { intros Hl Hml. destruct (wf_single A3 HW3 gj mt aib slots Hmt3 Hrl3 Hl Hml ltac:(rewrite Hscj; lia)) as [H|H]; rewrite Hscj in H; lia. }
      destruct Hstr3 as [H | (Hl & Hml & E)].
      - unfold mt_stride in *. rewrite Hscj in *. destruct ((mt_maplen mt =? 0) || negb (mt_last mt =? 0))%bool eqn:C; [reflexivity|].
        apply Bool.orb_false_iff in C. destruct C as [C1 C2]. apply Z.eqb_neq in C1. apply Bool.negb_false_iff in C2. apply Z.eqb_eq in C2.
        pose proof (SG C2 ltac:(unfold mt_maplen in *; pose proof (Z.div_pos (mt_w32 mt) 4096); lia)). lia.
      - exfalso. pose proof (SG Hl Hml).
        destruct (page_round_up_Z_spec (16 * size_class sc * cnt1 + 12 + 20) ltac:(lia)) as [B M].
        assert (4096 <= page_round_up_Z (16 * size_class sc * cnt1 + 12 + 20)).
        { set (r := page_round_up_Z (16 * size_class sc * cnt1 + 12 + 20)) in *. pose proof (Z.div_mod r 4096 ltac:(lia)) as DM.
          assert (Hq : 1 <= r / 4096) by (destruct (Z_lt_le_dec (r / 4096) 1); [exfalso; assert (r / 4096 = 0) by (pose proof (Z.div_pos r 4096); lia); lia | lia]). clear - DM M Hq. nia. }
        lia.
    Qed.

    (* [comment removed for export] *)
    Variables (ab : Z) (s4 : mstate).
    Hypothesis Hab : 0 <= ab < 256.
    Let A4 := nestA A3 sc m j gj mt aib slots idx cnt1 ab.
    Let NMT := nmt7 sc m j mt aib slots idx cnt1 ab.
    Hypothesis HII4 : II sp0 argv envp cb D A4 s4.
    Hypothesis FR4 : FR A3 s3 A4 s4.
    Hypothesis Hvm4 : ms_vm s4 = ms_vm s3.

    Lemma nmt_facts : mt_sc NMT = sc /\ mt_last NMT = cnt1 - 1 /\ mt_maplen NMT = 0 /\ mt_stride NMT = 16 * size_class sc.
    Proof using Hab Hcnt1 Hsc aib idx j m mt slots. pu_keep (Hab, Hcnt1, Hsc, aib, idx, j, m, mt, slots).
      assert (W : mt_w32 NMT = iw32 0 sc cnt1) by (unfold mt_w32, NMT; rewrite nmt7_f; reflexivity).
      assert (S : mt_sc NMT = sc) by (unfold mt_sc; rewrite W; apply iw32_sc; first [reflexivity | lia]).
      assert (L : mt_last NMT = cnt1 - 1) by (unfold mt_last; rewrite W; apply iw32_last; first [reflexivity | lia]).
      assert (ML0 : mt_maplen NMT = 0) by (unfold mt_maplen; rewrite W; rewrite iw32_maplen by (first [reflexivity | lia]); reflexivity).
      refine (conj S (conj L (conj ML0 _))). unfold mt_stride. rewrite ML0, S. reflexivity.
    Qed.

    Lemma nestok_leaf :
      FR A s A4 s4 /\ aslot_ok A A4 sc req m 0 (ms_mem s) s4 /\ gnew A A4 (ms_mem s) /\ aslot_vm A sc s s4 /\
      a_ctx A4 (KActive sc) = m /\ m = hd 0 (a_active A4 sc) /\ a_active A4 sc <> [] /\
      a_meta A4 m = Some NMT /\ mt_role NMT = RGroup (in_aib cnt1 ab) (in_slots cnt1) /\
      mt_sc NMT = sc /\ 0 <= 0 <= mt_last NMT /\ nth_error (in_slots cnt1) (Z.to_nat 0) = Some STaken /\
      req + 4 <= mt_stride NMT /\ 16 * size_class sc <= mt_stride NMT /\ (aslot_had_idle A2 -> aslot_had_idle A).
    Proof using AM AV3 FR2 FR3 FR4 GN3 GS HII4 HW1 HW3 Hab Hact1 Hcnt1 Hfitj Hidx Hj15 Hmd0 Hmd2 Hmt3 Hrd Hreq Hrk Hrl3 Hsc Hscj Hslot Hsmall Hstr3 Hvm4 Hxm2 K3 MLok NF1 SPARE TV. pu_keep (AM, AV3, FR2, FR3, FR4, GN3, GS, HII4, HW1, HW3, Hab, Hact1, Hcnt1, Hfitj, Hidx, Hj15, Hmd0, Hmd2, Hmt3, Hrd, Hreq, Hrk, Hrl3, Hsc, Hscj, Hslot, Hsmall, Hstr3, Hvm4, Hxm2, K3, MLok, NF1, SPARE, TV).
      pose proof (nest_rank_range sc) as Hnr. pose proof (nest_rank_range j) as Hnrj. pose proof no_Hj as Hj. pose proof no_gjm as Hgjm.
      pose proof nmt_facts as (NS & NL & NML & NST). pose proof (szc_rng sc Hsc) as SZC.
      pose proof (nestA_meta_inv A3 sc m md j gj mt aib slots idx cnt1 no_m3 Hrd no_act3 Hmt3 Hrl3 Hscj Hidx no_stride ab) as MINV.
      pose proof (nestA_old A3 sc m j gj mt aib slots idx cnt1 no_act3 ab) as OLD.
      pose proof (nestA_gj A3 sc m md j gj mt aib slots idx cnt1 no_m3 Hrd no_act3 Hmt3 Hrl3 Hscj Hidx no_stride ab) as GJ.
      destruct pf_md as (md' & Hmd2' & _ & _). rewrite Hmd2 in Hmd2'. injection Hmd2' as <-.
      (* [comment removed for export] *)
      assert (GD4 : forall x, gdom A4 x -> gdom A3 x).
      { intros x (y & mty & aiby & sly & Hy & Hry & Hml & Hx).
        destruct (MINV y mty Hy) as [(-> & ->) | [(-> & ->) | (Hym & Hyg & Hy3)]].
        - exfalso. fold NMT in Hml. lia.
        - exists gj, mt, aib, slots. split; [exact Hmt3|]. split; [exact Hrl3|].
          unfold mt_maplen, grp_map_len, mt_maplen, mt_mem in *. rewrite pm'_w32 in Hml, Hx. cbn [mt3 mt_w32 mt_f MT mr_w32 mr_mem] in Hml, Hx.
          change (mt_f (MT (mt_f mt) (RGroup aib (slots3 j slots idx))) FW32) with (mt_f mt FW32) in *.
          change (mt_f (MT (mt_f mt) (RGroup aib (slots3 j slots idx))) FMem) with (mt_f mt FMem) in *. auto.
        - exists y, mty, aiby, sly. auto. }
      assert (KEEP : aslot_keep A A4 sc (ms_mem s)).
      { apply keep_of_prefix.
        - unfold A4. rewrite nestA_live. exact (ak_live _ _ _ _ K3).
        - intros x mtx Hx Hrx Hxm. unfold A4. rewrite (OLD x Hxm).
          + exact (ak_dead _ _ _ _ K3 x mtx Hx Hrx).
          + intros ->. pose proof (ak_dead _ _ _ _ K3 gj mtx Hx Hrx) as H. rewrite Hmt3 in H. injection H as ->. rewrite Hrl3 in Hrx. discriminate Hrx.
        - intros x Hd. apply (proj2 (dom_nestA A3 sc m md j gj mt aib slots idx cnt1 no_m3 Hrd Hsc Hmt3 Hrl3 Hscj Hidx Hslot no_stride Hcnt1 ab Hab x)).
          exact (ak_dom _ _ _ _ K3 x Hd).
        - intros x Hg. exact (GN3 x (GD4 x Hg)).
        - intros c Hc Hr. unfold A4. rewrite (nestA_active_other A3 sc m j gj mt aib slots idx cnt1 ab c Hc).
          apply (ak_act _ _ _ _ K3 c); [intros ->; lia | lia].
        - unfold A4. rewrite nestA_xmaps. exact (ak_xmaps _ _ _ _ K3).
        - intros x mt0 aib0 sl0 Hx Hrx.
          destruct (ak_grp _ _ _ _ K3 x mt0 aib0 sl0 Hx Hrx) as (mt1 & aib1 & sl1 & H1 & R1 & W1 & M1 & L1 & K1).
          destruct (Z.eq_dec x m) as [-> | Hxm]; [rewrite Hmd2 in Hx; injection Hx as ->; rewrite Hrd in Hrx; discriminate Hrx|].
          destruct (Z.eq_dec x gj) as [-> | Hxg].
          + rewrite Hmt3 in H1. injection H1 as <-. rewrite Hrl3 in R1. injection R1 as <- <-.
            exists (pm' m (mt3 j mt aib slots idx) aib (slots3 j slots idx) idx), aib, (psl' m (slots3 j slots idx) idx).
            split; [exact GJ|]. split; [reflexivity|]. split; [rewrite pm'_w32; exact W1|]. split; [exact M1|].
            split; [unfold psl', slots3; rewrite !list_set_length; exact L1|].
            intros j0 st Hj0 Hst. unfold psl', slots3.
            destruct (Nat.eq_dec (Z.to_nat idx) j0) as [<- | Hnj].
            * exfalso. rewrite (ao_idle _ _ _ _ _ _ _ _ AO3 mt0 aib0 sl0 Hx Hrx) in Hj0. injection Hj0 as <-. exact (Hst eq_refl).
            * rewrite !list_set_nth_other by exact Hnj. exact (K1 j0 st Hj0 Hst).
          + exists mt1, aib1, sl1. unfold A4. rewrite (OLD x Hxm Hxg). rewrite W1, M1. repeat split; auto.
        - intros Hpre. unfold A4. rewrite nestA_areas.
          assert (SP4 : spare (nestA A3 sc m j gj mt aib slots idx cnt1 ab) = spare A3).
          { unfold spare. rewrite nestA_freelist.
            rewrite (nestA_ctx sp0 argv envp cb D A3 s3 sc m md j gj mt aib slots idx cnt1 HII3 no_m3 Hrd Hsc Hj Hmt3 Hrl3 Hscj Hidx Hslot no_stride Hcnt1 Hfitj Hsmall ab Hab KAmc I).
            destruct (cslot_eq_dec KAmc (KActive sc)) as [E|_]; [discriminate E|]. destruct (cslot_eq_dec KAmc (KUsage sc)) as [E|_]; [discriminate E|]. reflexivity. }
          rewrite SP4.
          destruct (ak_acct _ _ _ _ K3 ltac:(destruct Hpre as [H|H]; [left; exact H | right; lia])) as [(E & S) | (E0 & (pg & E) & S)]; [left | right].
          + rewrite E. split; [reflexivity | lia].
          + split; [exact E0|]. split; [exists pg; exact E | lia]. }
      assert (HFR : FR A s A4 s4) by (apply (FR_trans _ _ _ _ _ _ pf_FR); apply (FR_trans _ _ _ _ _ _ FR3); exact FR4).
      split; [exact HFR|]. split.
      { constructor.
        - exact KEEP.
        - intros x mtx aibx slx Hx Hrx. destruct (MINV x mtx Hx) as [(-> & ->) | [(-> & ->) | (Hxm & Hxg & Hx3)]].
          + right; left. reflexivity.
          + destruct (ao_grp_back _ _ _ _ _ _ _ _ AO3 gj mt aib slots Hmt3 Hrl3) as [(mt0 & aib0 & sl0 & H0 & R0) | [_ | (Hne & _)]]; [| | exfalso; exact (Hne eq_refl)].
            * left. destruct (pf_grp_back gj mt0 aib0 sl0 H0 R0) as (mtA & aibA & HA & RA & _). exists mtA, aibA, sl0. auto.
            * right; right. split; [exact Hgjm|]. unfold mt_sc. rewrite pm'_w32. change (mt_w32 (mt3 j mt aib slots idx)) with (mt_w32 mt). fold (mt_sc mt). rewrite Hscj. lia.
          + destruct (ao_grp_back _ _ _ _ _ _ _ _ AO3 x mtx aibx slx Hx3 Hrx) as [(mt0 & aib0 & sl0 & H0 & R0) | [E | (_ & S48 & RK)]].
            * left. destruct (pf_grp_back x mt0 aib0 sl0 H0 R0) as (mtA & aibA & HA & RA & _). exists mtA, aibA, sl0. auto.
            * exfalso. exact (Hxg E).
            * right; right. split; [exact Hxm | lia].
        - intros mt0 aib0 sl0 H0 R0. exfalso. exact (proj2 (pf_m_A mt0 H0) aib0 sl0 R0).
        - intros mt' aib' sl' Hx Hrx _. unfold A4 in Hx. rewrite nestA_m in Hx. injection Hx as <-. rewrite nmt7_role in Hrx. injection Hrx as <- <-.
          fold NMT. rewrite NL. split; [reflexivity | reflexivity].
        - intros Hbig. exfalso. assert (16 * size_class sc * 2 <= 16 * size_class sc * cnt1) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
        - intros mt' aib' sl' _ _ _ Hsc38. exfalso. pose proof (size_class_big sc ltac:(lia)). assert (16 * size_class sc * 2 <= 16 * size_class sc * cnt1) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
        - intros mt' aib' sl' Hx Hrx Hshort. exfalso. unfold A4 in Hx. rewrite nestA_m in Hx. injection Hx as <-. fold NMT in Hshort. lia.
        - intros Hbig. exfalso. assert (16 * size_class sc * 2 <= 16 * size_class sc * cnt1) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
      split; [exact (gnew_of_prefix A4 ltac:(intros x Hg; exact (GN3 x (GD4 x Hg))))|].
      split.
      { apply vm_of_prefix.
        - intros b sz Hin. rewrite Hvm4. exact (av_maps _ _ _ _ AV3 b sz Hin).
        - intros b sz Hin Hf. rewrite Hvm4. exact (av_acc _ _ _ _ AV3 b sz Hin Hf).
        - intros Hpre. rewrite Hvm4. pose proof (av_budget _ _ _ _ AV3 ltac:(destruct Hpre as [H|H]; [left; exact H | right; lia])) as B.
          assert (M : (4 - nest_rank j) * 2^21 <= (4 - nest_rank sc - 1) * 2^21) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
      split.
      { unfold A4. rewrite (nestA_ctx sp0 argv envp cb D A3 s3 sc m md j gj mt aib slots idx cnt1 HII3 no_m3 Hrd Hsc Hj Hmt3 Hrl3 Hscj Hidx Hslot no_stride Hcnt1 Hfitj Hsmall ab Hab (KActive sc) ltac:(cbn; lia)).
        destruct (cslot_eq_dec (KActive sc) (KActive sc)); [reflexivity | contradiction]. }
      split; [unfold A4; rewrite nestA_active_sc; reflexivity|].
      split; [unfold A4; rewrite nestA_active_sc; discriminate|].
      split; [unfold A4, NMT; apply nestA_m|]. split; [unfold NMT; apply nmt7_role|]. split; [exact NS|].
      split; [rewrite NL; lia|]. split; [reflexivity|]. split; [rewrite NST; lia|]. split; [rewrite NST; lia|].
      exact pf_had_idle.
    Qed.
  End NestOk.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section MmapOk.
    Variables (md : meta_rec) (req c0 cnt1 : Z) (A3 : astate) (s3 : mstate) (md3 : meta_rec) (p L cnt aidx : Z).
    Hypothesis Hmd2 : a_meta A2 m = Some md.
    Hypothesis Hrd : mt_role md = RDead.
    Hypothesis Hreq : 0 <= req /\ req + 4 <= 16 * size_class sc.
    Hypothesis Hc0 : In c0 (cnt_cands sc).
    Hypothesis Hcnt1 : cnt1 = cnt1_of (16 * size_class sc) c0.
    (* [comment removed for export] *)
    Hypothesis HII3 : II sp0 argv envp cb (m :: D) A3 s3.
    Hypothesis AGFR : agframe A2 s2 s3 p L.
    Hypothesis AH : aghand A2 A3 m p L.
    Hypothesis Hmd3 : a_meta A3 m = Some md3.
    Hypothesis Hrd3 : mt_role md3 = RDead.
    Hypothesis Hpal : page_aligned p.
    Hypothesis Hhr : heap_range p (p + L).
    Hypothesis HL : 0 < L.
    Hypothesis HLm : L mod 4096 = 0.
    Hypothesis Hnodom3 : forall x, p <= x < p + L -> ~ dom A3 x.
    Hypothesis Hspan : 16 * size_class sc * cnt < 2^20.
    Hypothesis Hpsc : aidx < cnt - 1 -> 7 <= sc.
    Hypothesis Hzero3 : forall a : word, p <= u a < p + L -> ms_mem s3 a = Some (Z_to_bv 8 0).
    Hypothesis Hcnt : 1 <= cnt <= 32.
    Hypothesis HreqL : cnt = 1 -> req + 20 <= L.
    Hypothesis Hfit : 1 < cnt -> 16 * size_class sc * cnt + 16 <= L.
    Hypothesis Haidx : 0 <= aidx <= cnt - 1.
    Hypothesis Hsingle : cnt = 1 -> 256 <= size_class sc \/ L - 16 <= 16 * size_class sc.
    Hypothesis Hs20 : cnt = 1 -> L < 2^20 + 16.
    Hypothesis NONE2 : forall a : word, p <= u a < p + L -> ms_mem s2 a = None.
    Hypothesis EXACT : exists (ns : bool) (usage2 c2 : Z),
      ((sc < 7 \/ 38 < sc) -> ns = false) /\ (31 < sc -> usage2 = a_ctx A2 (KUsage sc)) /\ 0 <= usage2 < 2^64 /\ 1 <= c2 <= 32 /\
      cnt2w (Z_to_bv 64 sc) (Z_to_bv 64 usage2) (Z_to_bv 64 4096) (Z_to_bv 64 (16 * size_class sc * cnt1)) (Z_to_bv 64 cnt1) ns = Z_to_bv 64 c2 /\
      cn3w ns (Z_to_bv 64 c2) (Z_to_bv 64 (page_round_up_Z (16 * size_class sc * c2 + 16))) (Z_to_bv 64 req) (Z_to_bv 64 4096) (Z_to_bv 64 (16 * size_class sc)) (Z_to_bv 64 usage2)
        = (Z_to_bv 64 cnt, Z_to_bv 64 L).
    (* [comment removed for export] *)
    Variables (ab : Z) (s4 : mstate).
    Hypothesis Hab : 0 <= ab < 256.
    Let xs := a_xmaps A2.
    Let A4 := rootA A3 sc m p L cnt aidx xs ab.
    Let RMT := rmt5 sc m p L cnt aidx ab.
    Hypothesis HII4 : II sp0 argv envp cb D A4 s4.
    Hypothesis FR4 : FR A3 s3 A4 s4.
    Hypothesis Hvm4 : ms_vm s4 = ms_vm s3.
    Hypothesis ZP4 : forall a : word, p + 16 <= u a < p + L -> ms_mem s4 a = ms_mem s3 a.

    Let HW3 : WF A3 := is_wf _ _ _ _ _ _ (ii_is HII3).

    Lemma mo_act3 : a_active A3 sc = []. Proof using AH GS Hact1. pu_keep (AH, GS, Hact1). rewrite (ah_active _ _ _ _ _ AH). exact pf_act_sc. Qed.
    Lemma mo_xm3 : a_xmaps A3 = (p, L) :: xs. Proof using AH. pu_keep (AH). exact (ah_xmaps _ _ _ _ _ AH). Qed.

    (* [comment removed for export] *)
    Lemma mo_exact : L <= 2^20 + 2^13 /\ (cnt = 1 -> L = page_round_up_Z (req + 20) \/ 16 * size_class sc + 16 <= L) /\
      (38 < sc -> sc mod 4 <> 3 -> usage_of A sc = 0 ->
       (16384 <= page_round_up_Z (req + 20) \/ page_round_up_Z (req + 20) < 16 * size_class sc + 16) ->
       cnt = 1 /\ L = page_round_up_Z (req + 20)).
    Proof using AGFR AH EXACT FR4 GS HII1 HII2 HII4 HL HLm Hab Hc0 Hcnt Hcnt1 Hfit Hhr Hnodom3 Hreq HreqL Hs20 Hsc Hsingle Hspan Hzero3 MLok NONE2 TV ZP4. pu_keep (AGFR, AH, EXACT, FR4, GS, HII1, HII2, HII4, HL, HLm, Hab, Hc0, Hcnt, Hcnt1, Hfit, Hhr, Hnodom3, Hreq, HreqL, Hs20, Hsc, Hsingle, Hspan, Hzero3, MLok, NONE2, TV, ZP4).
      pose proof (szc_rng sc Hsc) as SZC. pose proof Hhr as HR. unfold heap_range in HR. pose proof layout_small as LS.
      pose proof (cnt_facts sc c0 Hsc Hc0) as CF. cbv zeta in CF. rewrite <- Hcnt1 in CF. destruct CF as (C1 & C20 & C2 & _ & _).
      destruct EXACT as (ns & usage2 & c2 & Hns & Hu2 & Ru2 & Hc2 & E2 & E3).
      destruct (cnt2_word sc (size_class sc) cnt1 (Z_to_bv 64 usage2) ns Hsc SZC C1) as (c2' & REL & E2').
      pose proof (C2 c2' REL) as Hc2le. rewrite E2 in E2'. apply zbv_inj in E2'; [| lia | lia]. subst c2'.
      assert (Hsz2 : 16 * size_class sc * c2 <= 16 * size_class sc * cnt1) by (apply Z.mul_le_mono_nonneg_l; lia).
      destruct (page_round_up_Z_spec (16 * size_class sc * c2 + 16) ltac:(lia)) as [B2 _].
      destruct (page_round_up_Z_spec (req + 20) ltac:(lia)) as [B3 _].
      destruct (cn3_word ns c2 (page_round_up_Z (16 * size_class sc * c2 + 16)) req (size_class sc) (Z_to_bv 64 usage2) Hc2 ltac:(lia) ltac:(lia) SZC) as (c3 & n3 & E3' & CASES).
      rewrite E3 in E3'. pose proof (f_equal fst E3') as Ec. pose proof (f_equal snd E3') as En. cbn [fst snd] in Ec, En.
      assert (Hn3 : 0 <= n3 < 2^64) by (destruct CASES as [(-> & ->) | (-> & -> & _)]; lia).
      apply zbv_inj in Ec; [| lia | destruct CASES as [(-> & _) | (-> & _)]; lia]. apply zbv_inj in En; [| lia | exact Hn3]. subst c3 n3.
      split; [destruct CASES as [(_ & ->) | (_ & -> & _)]; lia|].
      split; [intros Hc; destruct CASES as [(E & ->) | (_ & -> & _)]; [right; lia | left; reflexivity]|].
      intros H38 Hm4 Hus0 Hpre. rewrite (Hns (or_intror H38)) in *. rewrite (Hu2 ltac:(lia)) in *.
      rewrite (ii_us HII2 sc Hsc), pf_usage, Hus0 in E2, E3.
      exact (single_exact sc (size_class sc) cnt1 c2 req cnt L ltac:(lia) Hm4 eq_refl C1 ltac:(lia) ltac:(lia) ltac:(lia) E2 ltac:(lia) E3 Hpre).
    Qed.

    Lemma rmt_facts : mt_sc RMT = sc /\ mt_last RMT = cnt - 1 /\ mt_maplen RMT = L / 4096 /\ 0 < mt_maplen RMT /\ mt_mem RMT = p /\
      grp_map_len RMT = L /\ mt_stride RMT = (if cnt =? 1 then L - 16 else 16 * size_class sc).
    Proof using HL HLm Hab Hcnt Hfit Hs20 Hsc Hsingle aidx m. pu_keep (HL, HLm, Hab, Hcnt, Hfit, Hs20, Hsc, Hsingle, aidx, m).
      unfold RMT. pose proof (Z.div_mod L 4096 ltac:(lia)) as DM. rewrite HLm in DM.
      refine (conj (rmt5_sc sc m p L cnt aidx Hsc HL HLm Hcnt ab Hab) (conj (rmt5_last sc m p L cnt aidx Hsc HL HLm Hcnt ab Hab) (conj (rmt5_maplen sc m p L cnt aidx Hsc HL HLm Hcnt ab Hab) _))).
      split; [rewrite (rmt5_maplen sc m p L cnt aidx Hsc HL HLm Hcnt ab Hab); apply Z.div_str_pos; lia|].
      split; [apply rmt5_mem|]. split; [unfold grp_map_len; rewrite (rmt5_maplen sc m p L cnt aidx Hsc HL HLm Hcnt ab Hab); lia|].
      rewrite rmt5_stride. apply ir_stride; [left; exact Hsc | exact Hcnt | exact Hab | exact HL | exact HLm | intros Hc _; exact (Hsingle Hc) | intros Hc _; exact (Hs20 Hc)].
    Qed.

    Lemma mmapok_leaf :
      FR A s A4 s4 /\ aslot_ok A A4 sc req m 0 (ms_mem s) s4 /\ gnew A A4 (ms_mem s) /\ aslot_vm A sc s s4 /\
      a_ctx A4 (KActive sc) = m /\ m = hd 0 (a_active A4 sc) /\ a_active A4 sc <> [] /\
      a_meta A4 m = Some RMT /\ mt_role RMT = RGroup (ir_aib aidx ab) (ir_slots cnt) /\
      mt_sc RMT = sc /\ 0 <= 0 <= mt_last RMT /\ nth_error (ir_slots cnt) (Z.to_nat 0) = Some STaken /\
      req + 4 <= mt_stride RMT /\
      (16 * size_class sc <= mt_stride RMT \/ (mt_last RMT = 0 /\ 0 < mt_maplen RMT /\ mt_stride RMT + 16 = page_round_up_Z (req + 20))) /\
      (aslot_had_idle A2 -> aslot_had_idle A).
    Proof using AGFR AH AM EXACT FR2 FR4 GS HII2 HII3 HII4 HL HLm HW1 Hab Hact1 Haidx Hc0 Hcnt Hcnt1 Hfit Hhr Hmd2 Hmd3 Hnodom3 Hpal Hpsc Hrd Hrd3 Hreq HreqL Hs20 Hsc Hsingle Hspan Hvm4 Hxm2 Hzero3 MLok NF1 NONE2 SPARE TV ZP4. pu_keep (AGFR, AH, AM, EXACT, FR2, FR4, GS, HII2, HII3, HII4, HL, HLm, HW1, Hab, Hact1, Haidx, Hc0, Hcnt, Hcnt1, Hfit, Hhr, Hmd2, Hmd3, Hnodom3, Hpal, Hpsc, Hrd, Hrd3, Hreq, HreqL, Hs20, Hsc, Hsingle, Hspan, Hvm4, Hxm2, Hzero3, MLok, NF1, NONE2, SPARE, TV, ZP4).
      pose proof (nest_rank_range sc) as Hnr. pose proof (szc_rng sc Hsc) as SZC. pose proof Hhr as HR. unfold heap_range in HR. pose proof layout_small as LS.
      pose proof rmt_facts as (RS & RL & RML & RMLp & RM & RG & RST). pose proof mo_exact as (HLup & HSGL & HEX).
      pose proof mo_act3 as Hact3. pose proof mo_xm3 as Hxm3.
      pose proof (rootA_meta_inv A3 sc m p L cnt aidx xs Hact3 ab) as MINV.
      pose proof (rootA_other A3 sc m p L cnt aidx xs Hact3 ab) as OLD.
      pose proof (dom_rootA A3 sc m md3 p L cnt aidx xs Hmd3 Hrd3 Hsc HL HLm Hcnt Haidx ab Hab) as DOM.
      destruct pf_md as (md' & Hmd2' & _ & _). rewrite Hmd2 in Hmd2'. injection Hmd2' as <-.
      (* [comment removed for export] *)
      assert (O23 : forall x, x <> m -> a_meta A3 x = a_meta A2 x) by (intros x Hx; exact (ah_other _ _ _ _ _ AH x Hx)).
      assert (GD4 : forall x, gdom A4 x -> gdom A2 x \/ ms_mem s2 (Z_to_bv 64 x) = None).
      { intros x (y & mty & aiby & sly & Hy & Hry & Hml & Hx).
        destruct (MINV y mty Hy) as [(-> & ->) | (Hym & Hy3)].
        - right. fold RMT in Hx, Hml. rewrite RM, RG in Hx. apply NONE2. rewrite uZ by lia. exact Hx.
        - left. exists y, mty, aiby, sly. rewrite <- (O23 y Hym). auto. }
      assert (KEEP : aslot_keep A A4 sc (ms_mem s)).
      { apply keep_of_prefix.
        - unfold A4. rewrite rootA_live. exact (ah_live _ _ _ _ _ AH).
        - intros x mtx Hx Hrx Hxm. unfold A4. rewrite (OLD x Hxm), (O23 x Hxm). exact Hx.
        - intros x Hd. apply (proj2 (DOM x)). left. apply (proj2 (ah_dom _ _ _ _ _ AH x)). exact Hd.
        - exact GD4.
        - intros c Hc _. unfold A4. rewrite (rootA_active_other A3 sc m p L cnt aidx xs ab c Hc). rewrite (ah_active _ _ _ _ _ AH). reflexivity.
        - unfold A4. rewrite rootA_xmaps. reflexivity.
        - intros x mt0 aib0 sl0 Hx Hrx. destruct (Z.eq_dec x m) as [-> | Hxm]; [rewrite Hmd2 in Hx; injection Hx as ->; rewrite Hrd in Hrx; discriminate Hrx|].
          exists mt0, aib0, sl0. unfold A4. rewrite (OLD x Hxm), (O23 x Hxm). repeat split; auto.
        - intros Hpre. left. unfold A4. rewrite rootA_areas, (ah_areas _ _ _ _ _ AH). split; [reflexivity|].
          assert (SP : spare (rootA A3 sc m p L cnt aidx xs ab) = spare A2); [| rewrite SP; lia].
          unfold spare. rewrite rootA_freelist, (ah_fl _ _ _ _ _ AH).
          rewrite (rootA_ctx sp0 argv envp cb D A3 s3 sc m md3 p L cnt aidx xs HII3 Hmd3 Hrd3 Hsc Hpal Hhr HL HLm Hnodom3 Hcnt Hspan Hfit Haidx Hsingle Hs20 Hpsc ab Hab KAmc I).
          destruct (cslot_eq_dec KAmc (KActive sc)) as [E|_]; [discriminate E|]. destruct (cslot_eq_dec KAmc (KUsage sc)) as [E|_]; [discriminate E|].
          rewrite (ah_ctx _ _ _ _ _ AH KAmc I ltac:(intros H; exact H)). reflexivity. }
      assert (HFR : FR A s A4 s4).
      { apply (FR_trans _ _ _ _ _ _ pf_FR). destruct AGFR as [GL GH GV GMm GLV GMP]. destruct FR4 as [L4 H4 O4 M4 V4 P4 Q4 T4]. constructor.
        - rewrite L4. exact GL.
        - rewrite H4. exact GH.
        - intros x [Hc | Hd]; [left; exact Hc |]. apply O4. right. apply (proj2 (ah_dom _ _ _ _ _ AH x)). exact Hd.
        - intros a Hno Herr. rewrite (M4 a Hno Herr). apply GMm.
          + intros Ho. apply Hno. apply O4. destruct Ho as [Hc | Hd]; [left; exact Hc | right]. apply (proj2 (ah_dom _ _ _ _ _ AH _)). exact Hd.
          + intros Hp. apply Hno. right. apply (proj2 (DOM _)). right. exact Hp.
        - intros q n Hq. apply V4. rewrite (ah_live _ _ _ _ _ AH). exact Hq.
        - intros q n a Hq Ha. rewrite (P4 q n a ltac:(rewrite (ah_live _ _ _ _ _ AH); exact Hq) Ha). exact (GLV q n a Hq Ha).
        - intros a Ha. apply Q4. apply GMP. exact Ha.
        - rewrite T4, GV. reflexivity. }
      split; [exact HFR|]. split.
      { constructor.
        - exact KEEP.
        - intros x mtx aibx slx Hx Hrx. destruct (MINV x mtx Hx) as [(-> & ->) | (Hxm & Hx3)]; [right; left; reflexivity | left].
          rewrite (O23 x Hxm) in Hx3. destruct (pf_grp_back x mtx aibx slx Hx3 Hrx) as (mt0 & aib0 & H0 & R0 & _). exists mt0, aib0, slx. auto.
        - intros mt0 aib0 sl0 H0 R0. exfalso. exact (proj2 (pf_m_A mt0 H0) aib0 sl0 R0).
        - intros mt' aib' sl' Hx Hrx _. unfold A4 in Hx. rewrite rootA_m in Hx. injection Hx as <-. rewrite rmt5_role in Hrx. injection Hrx as <- <-.
          fold RMT. rewrite RL. split; [reflexivity | reflexivity].
        - intros _ x mtx aibx slx Hx Hrx Hxm. destruct (MINV x mtx Hx) as [(E & _) | (_ & Hx3)]; [exfalso; exact (Hxm E)|].
          rewrite (O23 x Hxm) in Hx3. destruct (pf_grp_back x mtx aibx slx Hx3 Hrx) as (mt0 & aib0 & H0 & R0 & _). exists mt0, aib0, slx. auto.
        - intros mt' aib' sl' Hx Hrx _ H38 Hm4 Hus0 Hpre. unfold A4 in Hx. rewrite rootA_m in Hx. injection Hx as <-. fold RMT.
          destruct (HEX H38 Hm4 Hus0 Hpre) as [Hc1 EL]. rewrite RL, RST, Hc1. cbn [Z.eqb Pos.eqb]. split; [reflexivity|]. split; [exact RMLp | lia].
        - intros mt' aib' sl' Hx Hrx Hshort a Ha. unfold A4 in Hx. rewrite rootA_m in Hx. injection Hx as <-. fold RMT in Hshort, Ha.
          unfold slot_start, slot_end, slot_start_g, slot_end_g in Ha. rewrite RM in Ha.
          assert (Hc1 : cnt = 1) by (rewrite RST in Hshort; destruct (Z.eqb_spec cnt 1); lia).
          rewrite RST, Hc1 in Ha. cbn [Z.eqb Pos.eqb] in Ha.
          rewrite (ZP4 a) by lia. apply Hzero3. lia.
        - intros _. unfold A4. rewrite rootA_areas, (ah_areas _ _ _ _ _ AH).
          assert (SP : spare (rootA A3 sc m p L cnt aidx xs ab) = spare A2).
          { unfold spare. rewrite rootA_freelist, (ah_fl _ _ _ _ _ AH).
            rewrite (rootA_ctx sp0 argv envp cb D A3 s3 sc m md3 p L cnt aidx xs HII3 Hmd3 Hrd3 Hsc Hpal Hhr HL HLm Hnodom3 Hcnt Hspan Hfit Haidx Hsingle Hs20 Hpsc ab Hab KAmc I).
            destruct (cslot_eq_dec KAmc (KActive sc)) as [E|_]; [discriminate E|]. destruct (cslot_eq_dec KAmc (KUsage sc)) as [E|_]; [discriminate E|].
            rewrite (ah_ctx _ _ _ _ _ AH KAmc I ltac:(intros H; exact H)). reflexivity. }
          rewrite SP. destruct pf_spare as [(S0 & _ & E & S2) | (S0 & E & S2)].
          + left. rewrite E. split; [reflexivity | lia].
          + right. split; [lia|]. split; [exists (m - 24); exact E | lia]. }
      split; [exact (gnew_of_prefix A4 GD4)|].
      split.
      { destruct AGFR as [GL GH GV GMm GLV GMP]. apply vm_of_prefix.
        - intros b sz Hin. rewrite Hvm4, GV. cbn [vm_maps vm_mmap]. right. exact Hin.
        - intros b sz Hin Hf. rewrite Hvm4, GV. cbn [vm_noaccess vm_mmap]. exact Hf.
        - intros _. rewrite Hvm4, GV. unfold vm_live_bytes. cbn [vm_maps vm_mmap live_bytes]. fold (vm_live_bytes (ms_vm s2)). rewrite uZ by lia. lia. }
      split.
      { unfold A4. rewrite (rootA_ctx sp0 argv envp cb D A3 s3 sc m md3 p L cnt aidx xs HII3 Hmd3 Hrd3 Hsc Hpal Hhr HL HLm Hnodom3 Hcnt Hspan Hfit Haidx Hsingle Hs20 Hpsc ab Hab (KActive sc) ltac:(cbn; lia)).
        destruct (cslot_eq_dec (KActive sc) (KActive sc)); [reflexivity | contradiction]. }
      split; [unfold A4; rewrite rootA_active_sc; reflexivity|].
      split; [unfold A4; rewrite rootA_active_sc; discriminate|].
      split; [unfold A4, RMT; apply rootA_m|]. split; [unfold RMT; apply rmt5_role|]. split; [exact RS|].
      split; [rewrite RL; lia|]. split; [reflexivity|].
      split; [rewrite RST; destruct (Z.eqb_spec cnt 1); [pose proof (HreqL ltac:(assumption)); lia | lia]|].
      split.
      { rewrite RST, RL. destruct (Z.eqb_spec cnt 1) as [Hc1 | Hc1]; [| left; lia].
        destruct (HSGL Hc1) as [EL | GE]; [| left; lia].
        destruct (Z_lt_le_dec (L - 16) (16 * size_class sc)); [right | left; lia]. split; [lia|]. split; [exact RMLp | lia]. }
      exact pf_had_idle.
    Qed.
  End MmapOk.

End Prefix.
End NoneBranch.
End TA.

End WithLayout.
