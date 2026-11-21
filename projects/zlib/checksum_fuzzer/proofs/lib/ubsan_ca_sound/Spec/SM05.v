(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Bool.
From Stdlib Require Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Malloc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require KInv.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require MI_Inv.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require MI_List.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require MI_Ext.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require MI_Pres3.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require MI_Pres4.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require MI_WFree2.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM02.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require MI_WCreate.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM03.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM04.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require MI_WAMeta.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require MI_WTry2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module MI_WCreate2.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_Inv. Import SM08. Import SM08.MI_Kit. Import SM01. Import SM01.MI_Arith. Import SM01.MI_Geom. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_List. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_Ext. Import SM01.MI_Shadow. Import SM01.MI_Pres1. Import SM01.MI_Pres2. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_Pres3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_Pres4. Import SM01.MI_Read. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_WFree2. Import SM02. Import SM02.MI_WGroup. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_WCreate. Import SM03. Import SM03.MI_Cnt. Import SM04. Import SM04.MI_TF2.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Lemma land31_id x : 0 <= x <= 31 -> Z.land x 31 = x.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land63_id x : 0 <= x <= 63 -> Z.land x 63 = x.
Proof. intros. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land52_id x : 0 <= x < 2 ^ 52 -> Z.land x (2 ^ 52 - 1) = x.
Proof. intros. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma one5_A (A B E : Prop) : A -> ~ B -> ~ E -> one5 A B False False E.
Proof. intros. unfold one5. tauto. Qed.
Lemma one5_B (A B E : Prop) : ~ A -> B -> ~ E -> one5 A B False False E.
Proof. intros. unfold one5. tauto. Qed.
Lemma one5_E (A B E : Prop) : ~ A -> ~ B -> E -> one5 A B False False E.
Proof. intros. unfold one5. tauto. Qed.

Lemma cell_read_shadow0 o : cell_read shadow0 o = Known 0.
Proof. unfold cell_read. cbn. rewrite !lookup_empty. reflexivity. Qed.

Lemma known_noshadow st rid o : s_shadow st !! rid = None -> known st (rid, o) 0.
Proof. intros H. unfold known, SHd, get_shadow. cbn. rewrite H. cbn. apply cell_read_shadow0. Qed.


Definition agG (sc : Z) (p : aptr) (cnt ai : Z) (r : meta) : meta :=
  m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
    (m_set_mem (Some p) (m_set_freed (mask_upto (cnt - 1) - mask_upto ai) (m_set_avail (mask_upto ai) r))))).

Definition agt (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z) : mstate :=
  let st0 := hdr_havoc p st in
  let st1 := set_usage sc (usage st0 sc + cnt) st0 in
  let st2 := upd_meta m (agG sc p cnt ai) st1 in
  let st3 := put_group p (Some m) ai st2 in
  add_slots m p (get_stride (get_meta_rec st3 m)) cnt st3.

Lemma ag_tail_eq {T} st sc m p cnt ai (k : mstate -> optr -> M T) :
  ag_tail full_lay st sc m p cnt ai k = k (agt st sc m p cnt ai) (Some m).
Proof. reflexivity. Qed.

Section AGT.
Variables (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z).
Let st' := agt st sc m p cnt ai.
Let mr' := agG sc p cnt ai (MR st m).

Lemma agt_metas : s_metas st' = <[m := mr']> (s_metas st).
Proof. reflexivity. Qed.
Lemma agt_MR_m : MR st' m = mr'.
Proof. unfold MR, get_meta_rec. rewrite agt_metas, lookup_insert_eq. reflexivity. Qed.
Lemma agt_MR_other x : x <> m -> MR st' x = MR st x.
Proof. intros NE. unfold MR, get_meta_rec. rewrite agt_metas, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma agt_groups : s_groups st' = <[p := mkGhdr (Some m) (Z.land ai 31)]> (s_groups st).
Proof. reflexivity. Qed.
Lemma agt_rec3 :
  get_meta_rec (put_group p (Some m) ai (upd_meta m (agG sc p cnt ai) (set_usage sc (usage (hdr_havoc p st) sc + cnt) (hdr_havoc p st)))) m = mr'.
Proof. unfold get_meta_rec. cbn -[agG get_meta_rec]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma agt_slots s : 0 <= cnt -> 0 < get_stride mr' ->
  s_slots st' !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod get_stride mr' =? 0) && ((snd s - snd p - UNIT) / get_stride mr' <? cnt)
  then Some (m, (snd s - snd p - UNIT) / get_stride mr') else s_slots st !! s.
Proof. intros Hc Hs. unfold st', agt. cbn zeta. rewrite agt_rec3. rewrite lookup_add_slots by assumption. reflexivity. Qed.
Lemma agt_shadow : s_shadow st' = s_shadow (hdr_havoc p st). Proof. reflexivity. Qed.
Lemma agt_regions : s_regions st' = s_regions st. Proof. reflexivity. Qed.
Lemma agt_areas : s_areas st' = s_areas st. Proof. reflexivity. Qed.
Lemma agt_next_rid : s_next_rid st' = s_next_rid st. Proof. reflexivity. Qed.
Lemma agt_tick : s_tick st' = s_tick st. Proof. reflexivity. Qed.
Lemma agt_secret : s_secret st' = s_secret st. Proof. reflexivity. Qed.
Lemma agt_reserved : s_reserved st' = s_reserved st. Proof. reflexivity. Qed.
Lemma agt_atop : s_atop st' = s_atop st. Proof. reflexivity. Qed.
Lemma agt_ctx : s_ctx st' = set_usage_map (<[sc := usage st sc + cnt]> (c_usage (s_ctx st))) (s_ctx st). Proof. reflexivity. Qed.
Lemma agt_usage sc0 : usage st' sc0 = usage st sc0 + (if sc0 =? sc then cnt else 0).
Proof.
  unfold usage at 1. unfold ctx. rewrite agt_ctx. cbn -[usage]. destruct (Z.eqb_spec sc0 sc) as [->|NE].
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. unfold usage, ctx. lia.
Qed.
Lemma agt_active sc0 : active st' sc0 = active st sc0. Proof. reflexivity. Qed.
Lemma agt_get_head h : get_head st' h = get_head st h. Proof. destruct h; reflexivity. Qed.

Lemma agt_TF0 : TF0 st -> TF0 st'.
Proof. intros H. apply (TF0_ctrl (hdr_havoc p st)); [reflexivity| reflexivity|]. apply TF0_hdr_havoc. exact H. Qed.
Lemma agt_TW P : TW st P -> TW st' P.
Proof. intros H. apply (TW_ctrl (hdr_havoc p st)); [reflexivity| reflexivity|]. apply TW_hdr_havoc. exact H. Qed.
End AGT.


Section AG_TOP.
Variables (idle0 : list aptr) (st2 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m : aptr) (rid : N) (r : region) (sc cnt needed ai : Z).
Let X := mkX (m :: idle0) [] None (Some rid) None.
Let X' := mkX idle0 [] None None (Some m).
Hypothesis INV : INVL X st2 L BL LS.
Hypothesis Hr : s_regions st2 !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Lr : r_len r = needed.
Hypothesis NS : s_shadow st2 !! rid = None.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hai : 0 <= ai <= cnt - 1.
Hypothesis Hai0 : sc = 0 -> ai = cnt - 1.
Hypothesis EMP : LS (LActive sc) = [].
Hypothesis TF : TF0 st2.
Hypothesis NIm : ~ In m idle0.
Let p : aptr := (rid, 0).
Let ml := Z.shiftr needed 12.
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let st3 := upd_ctx MC st2.
Let st4 := upd_meta m (m_set_maplen ml) st3.
Let st' := agt st4 sc m p cnt ai.
Let mr' := agG sc p cnt ai (m_set_maplen ml meta0).

Let IM := proj1 (proj2 (proj2 INV)).
Lemma top_MRm : MR st2 m = meta0.
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). reflexivity. Qed.

Lemma top_INV3 : INVL X st3 L BL LS.
Proof. exact (INVL_mmap_counter X st2 L BL LS INV). Qed.

Lemma top_MR4 : MR st4 m = m_set_maplen ml meta0.
Proof. unfold st4, MR. rewrite get_meta_rec_upd_same. f_equal. exact top_MRm. Qed.

Lemma top_facts :
  let size := UNIT * size_class sc in
  let stride := get_stride mr' in
  1 <= cnt <= 32 /\ ml = needed / 4096 /\ 1 <= ml <= 256 /\ UNIT + stride * cnt <= ml * 4096
  /\ (stride <= size \/ 28 <= sc) /\ (cnt - 1 = 0 -> 27 <= sc) /\ stride * cnt < 2 ^ 20 /\ 16 <= stride /\ stride mod 16 = 0
  /\ ml * 4096 = round_up_pg needed /\ 0 < needed
  /\ mr' = mkMeta None None (Some p) (mask_upto ai) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml.
Proof.
  unfold ml in *. pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  assert (Emr : mr' = mkMeta None None (Some p) (mask_upto ai) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml).
  { lazymatch goal with |- ?g0 => let g1 := eval unfold mr', agG, m_set_sizeclass, m_set_freeable, m_set_last_idx, m_set_mem, m_set_freed, m_set_avail, m_set_maplen in g0 in let g2 := eval cbn in g1 in change g2 end.
    rewrite land31_id by lia. rewrite land63_id by lia. rewrite land52_id by lia. reflexivity. }
  assert (Es : get_stride mr' = (if (cnt - 1 =? 0) && negb (ml =? 0) then ml * 4096 - UNIT else UNIT * size_class sc)).
  { rewrite Emr. unfold get_stride. cbn. reflexivity. }
  cbn zeta. unfold ml in *.
  assert (RU : needed / 4096 * 4096 = round_up_pg needed).
  { destruct (round_up_pg_spec needed) as [A B]. pose proof (Z.div_mod needed 4096 ltac:(lia)). rewrite G2 in H.
    pose proof (Z.div_mod (round_up_pg needed) 4096 ltac:(lia)). rewrite B in H0. clear - G2 A B; nia. }
  rewrite Es. repeat split; try assumption; try lia.
Qed.

Theorem ag_top_ok :
  INVL X' st' L BL LS /\ TF0 st' /\ MR st' m = mr'
  /\ s_groups st' !! p = Some (mkGhdr (Some m) ai)
  /\ (forall sc0, active st' sc0 = active st2 sc0) /\ (forall h, get_head st' h = get_head st2 h)
  /\ s_tick st' = s_tick st2.
Proof.
  pose proof top_facts as TFX. cbn zeta in TFX. destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
  pose proof top_INV3 as INV3. pose proof INV3 as (IR & IA & IM3 & IL & IG & IS & ISH).
  assert (MR'm : MR st' m = mr') by (unfold st'; rewrite agt_MR_m; unfold mr'; rewrite top_MR4; reflexivity).
  pose proof (created_masks ai (cnt - 1) Hai ltac:(lia)) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
  assert (Sp : get_stride mr' > 0) by lia.
  assert (INV' : INVL X' st' L BL LS).
  { apply (INVL_create X X' st3 st' L BL LS m p ai mr' INV3 ltac:(left; reflexivity)).
    all: try (rewrite Emr; cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed]).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - exact Hai0.
    - left. lia.
    - unfold tbit. repeat split; try lia; assumption.
    - intros _. rewrite <- Emr. repeat split; lia.
    - rewrite <- Emr. lia.
    - cbn. unfold UNIT. split; [lia| reflexivity].
    - left. reflexivity.
    - reflexivity.
    - intros x Hx. cbn in Hx |- *. split; [right; exact Hx|]. intros ->. exact (NIm Hx).
    - reflexivity.
    - reflexivity.
    - intros i Hi. unfold tbit. cbn [x_pend X'].
      destruct (Z.le_gt_cases i ai).
      + apply one5_A; [apply M7; lia| intros Hf; exact (M5 i ltac:(lia) (M7 i ltac:(lia)) Hf)| discriminate].
      + apply one5_B; [intros Ha; pose proof (M3 i ltac:(lia) Ha); lia| apply M6; lia| discriminate].
    - intros s Hs. discriminate.
    - intros _. exact EMP.
    - left. rewrite <- Emr. cbn [snd fst x_orph x_pend X X' p]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists r. split; [exact Hr|]. split; [exact Kr|]. rewrite Lr. replace (m_maplen mr') with ml by (rewrite Emr; reflexivity).
      split; [exact F10|]. unfold cnt_of. replace (m_last_idx mr') with (cnt - 1) by (rewrite Emr; reflexivity). lia.
    - intros i Hi. apply known_noshadow. exact NS.
    - intros o v tk Ho Hc. exfalso. unfold get_shadow in Hc. cbn in Hc. rewrite NS in Hc. cbn in Hc. rewrite lookup_empty in Hc. discriminate.
    - unfold st'. rewrite agt_metas. unfold st4. rewrite s_metas_upd_meta. apply map_eq. intros kk. destruct (decide (kk = m)) as [->|NE].
      + rewrite !lookup_insert_eq. f_equal. fold st4. first [rewrite top_MR4; exact Emr| unfold mr'; f_equal; exact top_MR4].
      + rewrite !lookup_insert_ne by congruence. reflexivity.
    - unfold st'. rewrite agt_groups. rewrite land31_id by lia. reflexivity.
    - intros s. unfold st'. rewrite (agt_slots st4 sc m p cnt ai s); [| lia| rewrite top_MR4; fold mr'; lia].
      rewrite top_MR4. fold mr'. rewrite Emr. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - cbn. repeat split; reflexivity.
    - pose proof (ia_ctx _ IA) as (C & _). exact C.
    - intros sc0 Hsc0. unfold st'. rewrite agt_usage. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - intros sc0 v Hv. unfold st' in Hv. rewrite agt_ctx in Hv. cbn in Hv.
      destruct (Z.eq_dec sc0 sc) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hv by congruence. exact (ia_usage_keys _ IA sc0 v Hv). }
  split; [exact INV'|]. split.
  { unfold st'. apply agt_TF0. apply (TF0_ctrl st2); [reflexivity| reflexivity| exact TF]. }
  split; [exact MR'm|]. split; [unfold st'; rewrite agt_groups, lookup_insert_eq, land31_id by lia; reflexivity|].
  split; [intros; reflexivity|]. split; [intros h; destruct h; reflexivity| reflexivity].
Qed.
End AG_TOP.


Lemma set_metas_id st v : v = s_metas st -> Malloc.set_metas v st = st.
Proof. destruct st; cbn; intros ->; reflexivity. Qed.

Definition hdr3_f (i : Z) : bool := (Z.land (Z.lor (Z.land i 31) 192) 255 =? i + 192) && (Z.land (i + 192) 31 =? i).
Lemma hdr3_all : forallb hdr3_f (zrange 0 32) = true. Proof. vm_compute. reflexivity. Qed.
Lemma hdr3_facts i : 0 <= i <= 31 -> Z.land (Z.lor (Z.land i 31) 192) 255 = i + 192 /\ Z.land (i + 192) 31 = i.
Proof.
  intros Hi. pose proof (forallb_zrange hdr3_f 0 32 i hdr3_all ltac:(lia) ltac:(lia)) as H. unfold hdr3_f in H.
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed.

Section AG_NESTED.
Variables (idle0 : list aptr) (st1 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m g bg : aptr) (aig idx sc cnt : Z).
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).
Let p : aptr := (fst bg, sstart (MR st1 g) idx).
Let X := mkX (m :: idle0) [] (Some p) None None.
Let X' := mkX idle0 [] None None (Some m).
Hypothesis INV : INVL X st1 L BL LS.
Hypothesis Hg : s_groups st1 !! bg = Some (mkGhdr (Some g) aig).
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st1 g).
Hypothesis SCg : m_sizeclass (MR st1 g) = j.
Hypothesis STR : get_stride (MR st1 g) = UNIT * size_class j.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis EMP : LS (LActive sc) = [].
Hypothesis TF : TF2 st1.
Hypothesis NIm : ~ In m idle0.
Let st2 := nest_layout st1 g idx j size cnt.
Let st3 := upd_meta m (m_set_maplen 0) st2.
Let st' := agt st3 sc m p cnt (cnt - 1).
Let mr' := agG sc p cnt (cnt - 1) meta0.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma nst_MRm : MR st1 m = meta0.
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). reflexivity. Qed.
Lemma nst_hosts : hosts st1 bg g. Proof. exists aig. exact Hg. Qed.

Lemma nst_facts :
  2 <= cnt <= 32 /\ sc < j <= 23 /\ UNIT + cnt * size <= UNIT * size_class j /\ size * cnt < 2 ^ 20
  /\ 16 <= size /\ size mod 16 = 0 /\ size_class j <= 127
  /\ mr' = mkMeta None None (Some p) (mask_upto (cnt - 1)) 0 (cnt - 1) 1 sc 0
  /\ get_stride mr' = size.
Proof.
  pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0.
  destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
  pose proof (size_class_bound sc Hsc) as SB.
  assert (Emr : mr' = mkMeta None None (Some p) (mask_upto (cnt - 1)) 0 (cnt - 1) 1 sc 0).
  { unfold mr', agG, m_set_sizeclass, m_set_freeable, m_set_last_idx, m_set_mem, m_set_freed, m_set_avail. cbn.
    rewrite land31_id by lia. rewrite land63_id by lia. rewrite Z.sub_diag. reflexivity. }
  assert (SJ : size_class j <= 127) by (change 127 with (size_class 23); apply size_class_le; lia).
  repeat split; try lia.
  - unfold size, UNIT. lia.
  - unfold size, UNIT. rewrite Z.mul_comm. apply Z_mod_mult.
  - exact Emr.
  - rewrite Emr. unfold get_stride. cbn -[Z.eqb size_class Z.mul]. replace (cnt - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma nst_layout :
  INVL X st2 L BL LS /\ ctrl_eq st1 st2 /\ s_tick st2 = s_tick st1
  /\ known st2 (aadd p (-3)) (Z.land (Z.lor (Z.land idx 31) 192) 255)
  /\ known st2 (aadd p (-2)) (Z.land ((snd p - (snd bg + UNIT)) / UNIT) 255)
  /\ known st2 (aadd (aadd p (-2)) 1) (Z.land (Z.shiftr ((snd p - (snd bg + UNIT)) / UNIT) 8) 255)
  /\ (forall k, 0 <= k <= cnt -> known st2 (aadd p (UNIT + k * size - 4)) 0)
  /\ st2 = wrs (nl_list st1 g bg idx size cnt) st1.
Proof.
  pose proof nst_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & _ & _).
  pose proof (nest_layout_ok X st1 L BL LS g bg aig idx j size cnt INV Hg Hidx eq_refl STR N6 N5 ltac:(lia) ltac:(rewrite STR; exact N3)
                (TF2_TF X st1 L BL LS INV TF)) as (A & _ & C & D & E & F & G & H & _).
  refine (conj A (conj C (conj D (conj E (conj F (conj G (conj H _))))))). apply (nl_eq X st1 L BL LS g bg aig idx j size cnt INV Hg STR).
Qed.

Lemma nst_st3 : st3 = st2.
Proof.
  pose proof nst_layout as (INV2 & CE & _).
  unfold st3, upd_meta, put_meta. apply set_metas_id.
  assert (E : get_meta_rec st2 m = meta0) by (rewrite (get_meta_rec_ext st1 st2 m (ce_metas _ _ CE)); exact nst_MRm).
  rewrite E. change (m_set_maplen 0 meta0) with meta0. apply insert_id. rewrite (ce_metas _ _ CE). exact (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))).
Qed.

Theorem ag_nested_ok :
  INVL X' st' L BL LS /\ TF2 st' /\ MR st' m = mr'
  /\ s_groups st' !! p = Some (mkGhdr (Some m) (cnt - 1))
  /\ (forall sc0, active st' sc0 = active st1 sc0) /\ (forall h, get_head st' h = get_head st1 h)
  /\ s_tick st' = s_tick st1.
Proof.
  pose proof nst_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & Emr & Es).
  pose proof nst_layout as (INV2 & CE & TK2 & K3 & K2 & K1 & KZ & Ewrs).
  pose proof INV as (IR1 & IA1 & IM1 & IL1 & IG1 & IS1 & ISH1).
  pose proof INV2 as (IR & IA & IM2 & IL & IG2 & IS2 & ISH).
  pose proof nst_st3 as E3.
  assert (MR2 : forall x, MR st2 x = MR st1 x) by (intros x; apply MR_ext; exact (ce_metas _ _ CE)).
  assert (MR'm : MR st' m = mr') by (unfold st'; rewrite agt_MR_m; unfold mr'; rewrite E3, MR2, nst_MRm; reflexivity).
  pose proof (created_masks (cnt - 1) (cnt - 1) ltac:(lia) ltac:(lia)) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
  rewrite Z.sub_diag in *.
  pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG1 _ _ _ Hg)) as LI31.
  pose proof (hdr3_facts idx ltac:(lia)) as [H3a H3b].
  pose proof (sstart_res X st1 L BL LS INV bg g idx nst_hosts) as PR. fold p in PR.
  assert (P16 : snd p mod 16 = 0).
  { unfold p. cbn [snd]. unfold IB in PR. pose proof (Z.div_mod (sstart (MR st1 g) idx - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st1 g) idx) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (sstart (MR st1 g) idx) 16 ltac:(lia)). lia. }
  pose proof (hosts_gbase _ _ _ IM1 _ _ nst_hosts) as GB.
  assert (S0 : sstart (MR st1 g) idx = snd bg + UNIT + get_stride (MR st1 g) * idx) by (unfold sstart; rewrite GB; reflexivity).
  assert (Q : (snd p - snd bg - UNIT) / UNIT = size_class j * idx).
  { unfold p. cbn [snd]. rewrite S0, STR. unfold UNIT. replace (snd bg + 16 + 16 * size_class j * idx - snd bg - 16) with ((size_class j * idx) * 16) by lia. apply Z.div_mul. lia. }
  assert (Qr : 0 <= size_class j * idx < 2 ^ 16).
  { pose proof (size_class_bound j ltac:(clear - N2 Hsc; lia)) as SB.
    destruct (g_stride _ _ _ _ _ _ (ig_ok _ _ _ IG1 _ _ _ Hg) ltac:(rewrite SCg; clear - N2; lia)) as (_ & _ & LT).
    rewrite STR in LT. unfold cnt_of in LT. clear - SB LT Hidx. unfold UNIT in LT. nia. }
  assert (NH : s_groups st1 !! p = None).
  { pose proof (is_part _ _ _ IS1 _ _ _ idx Hg Hidx) as P5. cbn zeta in P5. rewrite (slot_start'_eq _ _ _ IM1 _ _ _ nst_hosts) in P5. fold p in P5.
    destruct (s_groups st1 !! p) eqn:E; [| reflexivity]. exfalso. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity]. }
  assert (INV' : INVL X' st' L BL LS).
  { apply (INVL_create X X' st2 st' L BL LS m p (cnt - 1) mr' INV2 ltac:(left; reflexivity)).
    all: try (rewrite Emr; cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed]).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - intros _. reflexivity.
    - left. lia.
    - unfold tbit. repeat split; try lia; try assumption; try (intros i Hi Hb; rewrite Z.bits_0 in Hb; discriminate).
    - intros _. rewrite <- Emr, Es. unfold size. clear - N1 N4. repeat split; lia.
    - rewrite <- Emr, Es. lia.
    - unfold UNIT. split; [| exact P16]. unfold p. cbn [snd]. pose proof (sstart0 _ _ _ IM1 _ _ nst_hosts). pose proof (sstart_mono _ _ _ IG1 _ _ 0 idx nst_hosts ltac:(lia)).
      destruct (hosts_ok _ _ _ IG1 _ _ nst_hosts) as (a0 & _ & GO). pose proof (g_align _ _ _ _ _ _ GO). unfold UNIT in *. lia.
    - left. reflexivity.
    - reflexivity.
    - intros x Hx. cbn [x_idle X X'] in Hx |- *. split; [right; exact Hx|]. intros ->. exact (NIm Hx).
    - reflexivity.
    - reflexivity.
    - intros i Hi. unfold tbit. cbn [x_pend X']. apply one5_A; [apply M7; lia| rewrite Z.bits_0; discriminate| discriminate].
    - intros s Hs. discriminate.
    - intros _. exact EMP.
    - right. rewrite <- Emr. cbn [x_pend x_orph X X']. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists g, idx, bg. rewrite !MR2.
      split; [rewrite (ce_slots _ _ CE); unfold p; rewrite <- (slot_start'_eq _ _ _ IM1 _ _ idx nst_hosts); exact (is_total _ _ _ IS1 _ _ _ nst_hosts Hidx)|].
      split; [apply (proj2 (hosts_ext st1 st2 (ce_groups _ _ CE) bg g)); exact nst_hosts|].
      split; [reflexivity|]. split; [exact Hidx|]. split; [reflexivity|].
      split; [rewrite Es; unfold p; cbn [snd]; rewrite STR; unfold cnt_of; replace (m_last_idx mr') with (cnt - 1) by (rewrite Emr; reflexivity); unfold size in N3 |- *; lia|].
      split; [rewrite SCg; replace (m_sizeclass mr') with sc by (rewrite Emr; reflexivity); lia|].
      split; [rewrite STR, SCg; reflexivity|].
      split; [exists (idx + 192); split; [| split; [exact H3b| clear - Hidx LI31; lia]]; rewrite <- H3a; exact K3|].
      rewrite Q. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r. rewrite <- Q.
      replace (snd p - snd bg - UNIT) with (snd p - (snd bg + UNIT)) by lia.
      split; [exact K2|]. split; [replace (fst p, snd p - 1) with (aadd (aadd p (-2)) 1) by (unfold aadd; cbn [fst snd]; f_equal; lia); exact K1|].
      replace ((snd p - (snd bg + UNIT)) / UNIT) with (size_class j * idx) by (rewrite <- Q; f_equal; lia). exact Qr.
    - rewrite <- Emr. intros i Hi. rewrite Es. replace (fst p, snd p + UNIT + size * i - IB) with (aadd p (UNIT + i * size - 4)) by (unfold aadd, IB; f_equal; lia).
      apply KZ. unfold cnt_of in Hi. rewrite ?Emr in Hi. cbn [m_last_idx] in Hi. lia.
    - intros o v tk Ho Hc. rewrite Ewrs in Hc. rewrite wrs_cells_other in Hc.
      + rewrite TK2. exact (TF2_ghdr_old X st1 L BL LS INV p TF P16 o v tk Ho Hc).
      + unfold nl_list. rewrite map_app. intros Hin. apply in_app_iff in Hin. unfold p in Ho. cbn [snd] in Ho. destruct Hin as [Hin|Hin].
        * cbn [map fst In] in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; apply (f_equal snd) in E; unfold aadd in E; cbn [fst snd] in E; clear - E Ho N1 N5; lia.
        * apply in_zlist in Hin as (k & Hk & E). apply (f_equal snd) in E. unfold aadd in E. cbn [fst snd] in E. unfold UNIT in E.
          assert (0 <= k * size) by (apply Z.mul_nonneg_nonneg; clear - Hk N5; lia). clear - E Ho H Hk N5. lia.
    - unfold st'. rewrite agt_metas. rewrite E3. apply map_eq. intros kk. destruct (decide (kk = m)) as [->|NE].
      + rewrite !lookup_insert_eq. f_equal. rewrite MR2, nst_MRm. first [exact Emr| reflexivity].
      + rewrite !lookup_insert_ne by congruence. reflexivity.
    - unfold st'. rewrite agt_groups, E3. rewrite land31_id by lia. reflexivity.
    - intros s. unfold st'. rewrite (agt_slots st3 sc m p cnt (cnt - 1) s); [| lia| rewrite E3, MR2, nst_MRm; fold mr'; rewrite Es; lia].
      rewrite E3, MR2, nst_MRm. fold mr'. rewrite Emr. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - unfold st'. rewrite agt_shadow, E3. reflexivity.
    - unfold st'. rewrite agt_regions, E3. reflexivity.
    - unfold st'. rewrite agt_areas, E3. reflexivity.
    - unfold st'. rewrite agt_next_rid, E3. reflexivity.
    - unfold st'. rewrite agt_tick, E3. reflexivity.
    - unfold st'. rewrite agt_secret, E3. reflexivity.
    - unfold st'. rewrite agt_reserved, E3. reflexivity.
    - unfold st'. rewrite agt_atop, E3. reflexivity.
    - unfold st'. rewrite agt_ctx, E3. repeat split; reflexivity.
    - unfold st'. rewrite agt_ctx, E3. cbn [c_mmap_counter set_usage_map]. rewrite (ce_ctx _ _ CE). pose proof (ia_ctx _ IA1) as (C & _). exact C.
    - intros sc0 Hsc0. unfold st'. rewrite agt_usage, E3. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - intros sc0 v Hv. unfold st' in Hv. rewrite agt_ctx, E3 in Hv. cbn [c_usage set_usage_map] in Hv.
      destruct (Z.eq_dec sc0 sc) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hv by congruence. rewrite (ce_ctx _ _ CE) in Hv. exact (ia_usage_keys _ IA1 sc0 v Hv). }
  split; [exact INV'|]. split.
  {
    unfold TF2. unfold st'. rewrite E3.
    apply (TW_mono _ (fun q => PS st1 q \/ In q (map fst (nl_list st1 g bg idx size cnt)))).
    2:{ apply agt_TW. rewrite Ewrs. apply TW_wrs; [| intros q Hq; right; exact Hq]. apply (TW_mono _ (PS st1)); [intros q Hq; left; exact Hq| exact TF]. }
    intros q [Hq|Hq].
    - apply (PS_mono st1); [| exact Hq]. apply geom_kept_of.
      + intros b h Hb. rewrite <- E3. fold st'. unfold st'. rewrite agt_groups, E3, (ce_groups _ _ CE).
        rewrite lookup_insert_ne; [exact Hb|]. intros ->. rewrite NH in Hb. discriminate.
      + intros b x Hx. rewrite <- E3. fold st'. rewrite (agt_MR_other st3 sc m p cnt (cnt - 1) x), E3, MR2; [reflexivity|].
        intros ->. exact (idle_not_live _ _ _ _ _ INV m ltac:(left; reflexivity) (ex_intro _ b Hx)).
    - assert (Hm' : hosts (agt st2 sc m p cnt (cnt - 1)) p m) by (exists (Z.land (cnt - 1) 31); rewrite agt_groups, lookup_insert_eq; reflexivity).
      assert (R' : MR (agt st2 sc m p cnt (cnt - 1)) m = mr') by (rewrite <- E3; exact MR'm).
      exists p, m. split; [exact Hm'|]. rewrite R'.
      unfold nl_list in Hq. rewrite map_app in Hq. apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
      + cbn [map fst In app] in Hq. assert (E : fst q = fst p /\ snd p - 3 <= snd q <= snd p - 1).
        { destruct Hq as [E|[E|[E|[E|[E|[]]]]]]; subst q; unfold aadd, p; cbn [fst snd]; split; first [reflexivity| lia]. }
        destruct E as [E1 E2]. split; [symmetry; exact E1|]. right. split; [rewrite Emr; reflexivity| exact E2].
      + apply in_zlist in Hq as (k & Hk & ->). unfold aadd. cbn [fst snd]. split; [reflexivity|]. left. exists k.
        split; [unfold cnt_of; rewrite Emr; cbn [m_last_idx]; clear - Hk; lia|].
        unfold sstart. replace (gbase mr') with p by (rewrite Emr; reflexivity). rewrite Es. unfold p. cbn [snd]. unfold sstart, UNIT, IB. lia. }
  split; [exact MR'm|].
  split; [unfold st'; rewrite agt_groups, E3, lookup_insert_eq, land31_id by lia; reflexivity|].
  split; [intros sc0; unfold st'; rewrite agt_active, E3; unfold active, ctx; rewrite (ce_ctx _ _ CE); reflexivity|].
  split; [intros h; unfold st'; rewrite agt_get_head, E3; unfold get_head, active, ctx; rewrite (ce_ctx _ _ CE); reflexivity|].
  unfold st'. rewrite agt_tick, E3. exact TK2.
Qed.
End AG_NESTED.


Lemma round_up_pg_div x : 0 < x -> (x + 4095) / 4096 * 4096 = round_up_pg x.
Proof.
  intros Hx. destruct (round_up_pg_spec x) as [A B].
  pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as M1.
  pose proof (Z.div_mod (round_up_pg x) 4096 ltac:(lia)) as D2. rewrite B in D2. nia.
Qed.

Definition F63 (rid : N) (ml : Z) (mr : meta) : meta :=
  m_set_freed 0 (m_set_avail 0 (m_set_maplen ml (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr)))))).

Section CREATE63.
Variables (st3 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g : aptr) (rid : N) (r : region) (needed : Z).
Let X := mkX [g] [] None (Some rid) None.
Let p : aptr := (rid, 0).
Let X' := mkX [] [] (Some (rid, 16)) None None.
Hypothesis INV : INVL X st3 L BL LS.
Hypothesis Hr : s_regions st3 !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Lr : r_len r = needed.
Hypothesis NS : s_shadow st3 !! rid = None.
Hypothesis Hn : 0 < needed < 2 ^ 63.
Hypothesis TF : TF0 st3.
Let ml := (needed + 4095) / 4096.
Let st4 := upd_meta g (F63 rid ml) st3.
Let st5 := put_group p (Some g) (group_active_idx st4 p) (hdr_havoc p st4).
Let st6 := add_slots g p (get_stride (get_meta_rec st5 g)) 1 st5.
Let mr' := mkMeta None None (Some p) 0 0 0 1 63 ml.

Let IR := proj1 INV.
Let IM := proj1 (proj2 (proj2 INV)).

Lemma c63_MRg : MR st3 g = meta0.
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM g ltac:(left; reflexivity))). reflexivity. Qed.

Lemma c63_ml : 1 <= ml < 2 ^ 52 /\ ml * 4096 = round_up_pg needed.
Proof.
  unfold ml. split; [| apply round_up_pg_div; lia].
  split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia].
Qed.

Lemma c63_F : F63 rid ml meta0 = mr'.
Proof.
  pose proof c63_ml as [M _]. lazymatch goal with |- ?g0 => let g1 := eval unfold F63, mr', m_set_freed, m_set_avail, m_set_maplen, m_set_sizeclass, m_set_freeable, m_set_last_idx, m_set_mem in g0 in let g2 := eval cbn in g1 in change g2 end.
  rewrite land52_id by lia. reflexivity.
Qed.

Lemma c63_stride : get_stride mr' = ml * 4096 - UNIT.
Proof. pose proof c63_ml as [M _]. unfold get_stride, mr'. cbn -[Z.mul Z.sub Z.eqb]. replace (ml =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

Lemma c63_nogroup : s_groups st3 !! p = None.
Proof. destruct (ir_orph _ _ _ IR rid eq_refl) as (r0 & _ & _ & NG). apply NG. reflexivity. Qed.

Lemma c63_rec5 : get_meta_rec st5 g = mr'.
Proof. unfold get_meta_rec. cbn -[F63 get_meta_rec]. rewrite lookup_insert_eq. fold (MR st3 g). rewrite c63_MRg. exact c63_F. Qed.

Theorem create63_ok :
  INVL X' st6 L BL LS /\ TF0 st6 /\ MR st6 g = mr' /\ s_groups st6 !! p = Some (mkGhdr (Some g) 0)
  /\ s_ctx st6 = s_ctx st3 /\ s_tick st6 = s_tick st3 /\ s_regions st6 = s_regions st3
  /\ get_stride mr' = ml * 4096 - UNIT /\ ml * 4096 = round_up_pg needed.
Proof.
  pose proof c63_ml as [M RU]. pose proof c63_stride as Es.
  pose proof INV as (IR0 & IA & IM0 & IL & IG & IS & ISH).
  assert (Emetas : s_metas st6 = <[g := mr']> (s_metas st3)).
  { change (s_metas st6) with (s_metas st4). unfold st4. rewrite s_metas_upd_meta. fold (MR st3 g). rewrite c63_MRg, c63_F. reflexivity. }
  assert (MR'g : MR st6 g = mr') by (unfold MR, get_meta_rec; rewrite Emetas, lookup_insert_eq; reflexivity).
  assert (GAI : group_active_idx st4 p = 0).
  { unfold group_active_idx, get_group. change (s_groups st4) with (s_groups st3). rewrite c63_nogroup. reflexivity. }
  assert (Egroups : s_groups st6 = <[p := mkGhdr (Some g) 0]> (s_groups st3)).
  { change (s_groups st6) with (s_groups st5). unfold st5. rewrite GAI. reflexivity. }
  assert (INV' : INVL X' st6 L BL LS).
  { apply (INVL_create X X' st3 st6 L BL LS g p 0 mr' INV ltac:(left; reflexivity)).
    all: cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed mr'].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - intros _. reflexivity.
    - right. lia.
    - unfold tbit. repeat split; try lia; intros i Hi Hb; rewrite Z.testbit_0_l in Hb; discriminate.
    - lia.
    - fold mr'. rewrite Es. unfold UNIT. split; [lia|]. replace (ml * 4096 - 16) with ((ml * 256 - 1) * 16) by lia. apply Z_mod_mult.
    - cbn. unfold UNIT. split; [lia| reflexivity].
    - right. split; reflexivity.
    - reflexivity.
    - intros x Hx. destruct Hx.
    - reflexivity.
    - reflexivity.
    - intros i Hi. unfold tbit. cbn [x_pend X' fst snd p]. apply one5_E; [rewrite Z.testbit_0_l; discriminate| rewrite Z.testbit_0_l; discriminate|].
      assert (i = 0) by lia. subst i. rewrite Z.mul_0_r. reflexivity.
    - intros s Hs. cbn [x_pend X'] in Hs. inversion Hs. subst s. exists 0. split; [lia|]. cbn [fst snd p]. rewrite Z.mul_0_r. reflexivity.
    - intros H. lia.
    - left. cbn [x_orph x_pend X X' fst snd p]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists r. split; [exact Hr|]. split; [exact Kr|]. rewrite Lr. split; [exact RU|]. fold mr'. rewrite Es. unfold UNIT. lia.
    - intros i Hi. apply known_noshadow. exact NS.
    - intros o v tk Ho Hc. exfalso. unfold get_shadow in Hc. cbn [fst p] in Hc. rewrite NS in Hc. cbn in Hc. rewrite lookup_empty in Hc. discriminate.
    - exact Emetas.
    - exact Egroups.
    - intros s. unfold st6. rewrite c63_rec5. rewrite lookup_add_slots; [| lia| rewrite Es; unfold UNIT; lia]. fold mr'. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - repeat split; reflexivity.
    - pose proof (ia_ctx _ IA) as (C & _). exact C.
    - intros sc0 Hsc0. replace (sc0 =? 63) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.add_0_r. reflexivity.
    - intros sc0 v Hv. exact (ia_usage_keys _ IA sc0 v Hv). }
  split; [exact INV'|]. split.
  { apply (TF0_ctrl (hdr_havoc p st4)); [reflexivity| reflexivity|]. apply TF0_hdr_havoc. apply (TF0_ctrl st3); [reflexivity| reflexivity| exact TF]. }
  split; [exact MR'g|]. split; [rewrite Egroups, lookup_insert_eq; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Es| exact RU].
Qed.
End CREATE63.
End MI_WCreate2.

Module MI_WSlot.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KInv. Import SM01. Import SM01.MI_Tree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_Inv. Import SM08. Import SM08.MI_Kit. Import SM01.MI_Arith. Import SM01.MI_Geom. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_List. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_Ext. Import SM01.MI_Shadow. Import SM01.MI_Pres1. Import SM01.MI_Pres2. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_Pres3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_Pres4. Import SM01.MI_Read. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_WFree2. Import SM02. Import SM02.MI_Ledger. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_WAMeta. Import SM04. Import SM04.MI_WAMeta2. Import SM04.MI_WTry. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_WTry2. Import SM02.MI_WGroup. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_WCreate. Import SM03. Import SM03.MI_Cnt. Import SM04.MI_TF2. Import MI_WCreate2.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition X_as (idle : list aptr) : extras := mkX idle [] None None None.


Definition GP (st st' : mstate) : Prop :=
  (forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> s_regions st' !! rid = Some r)
  /\ s_secret st' = s_secret st.
Lemma GP_refl st : GP st st. Proof. split; [intros rid r H _; exact H| reflexivity]. Qed.
Lemma GP_trans a b c : GP a b -> GP b c -> GP a c.
Proof. intros [H1 S1] [H2 S2]. split; [intros rid r H K; exact (H2 rid r (H1 rid r H K) K)| congruence]. Qed.
Lemma GP_eq st st' : s_regions st' = s_regions st -> s_secret st' = s_secret st -> GP st st'.
Proof. intros E S. split; [intros rid r H _; rewrite E; exact H| exact S]. Qed.
Lemma GP_amf st st' : AM_frame st st' -> GP st st'.
Proof. intros AF. split; [exact (amf_regions _ _ AF)| exact (amf_ssec _ _ AF)]. Qed.
Lemma GP_taf st st' sc : TA_frame st st' sc -> GP st st'.
Proof. intros TF. apply GP_eq; [exact (taf_regions _ _ _ TF)| exact (taf_ssec _ _ _ TF)]. Qed.


Definition geo_of (r : meta) : (optr * Z * Z * Z)%type := (m_mem r, m_last_idx r, m_maplen r, m_sizeclass r).

Lemma geo_facts r r' : geo_of r' = geo_of r ->
  (forall i, sstart r' i = sstart r i) /\ cnt_of r' = cnt_of r /\ m_maplen r' = m_maplen r /\ get_stride r' = get_stride r.
Proof.
  unfold geo_of. intros H. injection H. intros E1 E2 E3 E4.
  assert (ES : get_stride r' = get_stride r) by (unfold get_stride; rewrite E2, E3, E1; reflexivity).
  unfold sstart, cnt_of, gbase. rewrite ES, E4, E3, E2. auto.
Qed.

Lemma geom_kept_geo st st' :
  (forall b h, s_groups st !! b = Some h -> s_groups st' !! b = Some h) ->
  (forall x, geo_of (MR st' x) = geo_of (MR st x)) ->
  geom_kept st st'.
Proof.
  intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
  destruct (geo_facts _ _ (HM m)) as (A & B & C & _). auto.
Qed.


Lemma INVL_idle_sub X idle' st L BL LS :
  (forall x, In x idle' -> In x (x_idle X)) -> INVL X st L BL LS -> INVL (xidle X idle') st L BL LS.
Proof.
  intros SUB (IR & IA & IM & IL & IG & IS & ISH).
  split; [exact (inv_R_X X (xidle X idle') st L eq_refl IR)|]. split; [exact IA|].
  split.
  { destruct IM as [Q1 Q2 Q3 Q4 Q5]; constructor; cbn; auto. }
  split; [exact IL|]. split; [exact (inv_G_X X (xidle X idle') st LS eq_refl eq_refl IG)|]. split; [exact (inv_S_X X (xidle X idle') st BL eq_refl IS)| exact ISH].
Qed.


Section FREE_IDLE.
Variables (idle : list aptr) (m : aptr) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL (X_as (m :: idle)) st L BL LS.
Hypothesis NIm : ~ In m idle.
Let st' := fm_st st m.
Let LS' := fupd LS LFree (LS LFree ++ [m]).

Let IM := proj1 (proj2 (proj2 INV)).
Lemma fi_metas : s_metas st !! m = Some meta0.
Proof. exact (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). Qed.
Lemma fi_put : put_meta m meta0 st = st.
Proof. unfold put_meta. apply set_metas_id. apply insert_id. exact fi_metas. Qed.

Lemma free_idle_ok :
  INVL (X_as idle) st' L BL LS'
  /\ s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st
  /\ s_regions st' = s_regions st /\ s_next_rid st' = s_next_rid st
  /\ (forall sc, active st' sc = active st sc) /\ (forall sc, usage st' sc = usage st sc)
  /\ c_mmap_counter (s_ctx st') = c_mmap_counter (s_ctx st)
  /\ c_bounces (s_ctx st') = c_bounces (s_ctx st) /\ c_seq (s_ctx st') = c_seq (s_ctx st).
Proof.
  pose proof (INVL_idle_sub (X_as (m :: idle)) idle st L BL LS ltac:(intros x Hx; right; exact Hx) INV) as INV1.
  assert (MRm : MR st m = meta0) by (unfold MR, get_meta_rec; rewrite fi_metas; reflexivity).
  unfold st', fm_st. rewrite fi_put.
  pose proof (INVL_queue (xidle (X_as (m :: idle)) idle) st L BL LS m LFree INV1 ltac:(rewrite MRm; reflexivity)
                ltac:(rewrite fi_metas; discriminate) ltac:(cbn; rewrite MRm; split; [reflexivity| tauto])) as INV2.
  destruct (queue_frame LFree m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC).
  split; [exact INV2|]. split; [exact F2|]. split; [exact F7|]. split; [exact F5|]. split; [exact F6|]. split; [exact F1|]. split; [exact F3|].
  split; [intros sc; change (active ?s sc) with (get_head s (LActive sc)); rewrite queue_head; destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]|].
  split; [intros sc; unfold usage, ctx; rewrite (cb_usage _ _ FC); reflexivity|].
  split; [exact (cb_mc _ _ FC)|]. split; [exact (cb_bounces _ _ FC)| exact (cb_seq _ _ FC)].
Qed.
End FREE_IDLE.


Section FINISH.
Variables (T : Type) (idle : list aptr) (st2 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m b : aptr) (ai last sc ml : Z) (k : mstate -> M T) (bail : M T).
Let X2 := mkX idle [] None None (Some m).
Hypothesis INV : INVL X2 st2 L BL LS.
Hypothesis Hb : s_groups st2 !! b = Some (mkGhdr (Some m) ai).
Hypothesis Em : MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml.
Hypothesis Hai : 0 <= ai <= last.
Hypothesis Hl : last <= 31.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis HA : active st2 sc = None.
Hypothesis UND : get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0.
Hypothesis TF : TF2 st2.

Let st3 := upd_meta m (fun r => m_set_avail (m_avail r - 1) r) st2.
Let st4 := queue_st (LActive sc) m st3.
Let LS4 := fupd LS (LActive sc) (LS (LActive sc) ++ [m]).
Let s0 : aptr := (fst b, sstart (MR st2 m) 0).

Lemma fin_hosts : hosts st2 b m. Proof. exists ai. exact Hb. Qed.
Lemma fin_empty : LS (LActive sc) = [].
Proof.
  pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. cbn in HH. rewrite HA in HH.
  destruct (LS (LActive sc)); [reflexivity| discriminate].
Qed.

Lemma mask_upto_pred a : 0 <= a -> mask_upto a - 1 = Z.ldiff (mask_upto a) 1.
Proof.
  intros Ha. apply Z.sub_nocarry_ldiff. apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0, testbit_mask_upto by lia.
  destruct (Z.eq_dec i 0) as [->|NZ].
  - cbn. replace (0 <=? a) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - replace (Z.testbit 1 i) with false; [reflexivity|]. symmetry. change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma testbit_avail' i : 0 <= i -> Z.testbit (mask_upto ai - 1) i = ((1 <=? i) && (i <=? ai)).
Proof.
  intros Hi. rewrite mask_upto_pred by lia. rewrite Z.ldiff_spec, testbit_mask_upto by lia.
  change 1 with (2 ^ 0) at 1. rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.leb_spec i ai); destruct (Z.leb_spec 1 i); destruct (Z.eqb_spec 0 i); cbn; try reflexivity; lia.
Qed.

Lemma st3_eq : st3 = upd_meta m (fun r => m_set_avail (mask_upto ai - 1) (m_set_freed (mask_upto last - mask_upto ai) r)) st2.
Proof.
  unfold st3, upd_meta. f_equal. fold (MR st2 m). rewrite Em. reflexivity.
Qed.

Lemma fin_INV3 : INVL (mkX idle [] (Some s0) None (Some m)) st3 L BL LS.
Proof.
  rewrite st3_eq.
  pose proof (created_masks ai last Hai Hl) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (Elast : m_last_idx (MR st2 m) = last) by (rewrite Em; reflexivity).
  apply (INVL_mask_change X2 st2 L BL LS m b ai (mask_upto ai - 1) (mask_upto last - mask_upto ai) (Some s0) INV Hb).
  - rewrite Elast. unfold tbit. split; [unfold mask_upto; assert (P2 : 2 ^ 1 <= 2 ^ (ai + 1)) by (apply Z.pow_le_mono_r; lia); change (2 ^ 1) with 2 in P2; lia|].
    split; [exact M2|]. split; [intros i Hi Hb'; rewrite testbit_avail' in Hb' by lia; apply andb_true_iff in Hb' as [_ Hb']; apply Z.leb_le in Hb'; exact Hb'|].
    split; [exact M4|]. split; [| exact M6].
    intros i Hi Ha Hf. rewrite testbit_avail' in Ha by lia. apply andb_true_iff in Ha as [_ Ha]. apply Z.leb_le in Ha. exact (M5 i Hi (M7 i ltac:(lia)) Hf).
  - rewrite Elast. intros i Hi. cbn zeta. unfold tbit.
    pose proof (is_part _ _ _ IS _ _ _ i Hb ltac:(rewrite Elast; exact Hi)) as P5. cbn zeta in P5. rewrite Em in P5. cbn [m_avail m_freed x_pend X2] in P5.
    rewrite <- Em in P5.
    destruct P5 as (_ & _ & nAC & nAD & _ & nBC & nBD & _ & _ & _ & _).
    rewrite testbit_avail' by lia.
    destruct (Z.eq_dec i 0) as [->|NZ].
    + assert (A0 : Z.testbit (mask_upto ai) 0 = true) by (apply M7; lia).
      apply one5_iff_create; [apply one5_E| intros C; exact (nAC (conj A0 C))| intros D; exact (nAD (conj A0 D))].
      * cbn. discriminate.
      * intros F. exact (M5 0 ltac:(lia) A0 F).
      * unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
    + destruct (Z.le_gt_cases i ai) as [Hle|Hgt].
      * assert (A : Z.testbit (mask_upto ai) i = true) by (apply M7; lia).
        apply one5_iff_create; [apply one5_A| intros C; exact (nAC (conj A C))| intros D; exact (nAD (conj A D))].
        -- replace (1 <=? i) with true by (symmetry; apply Z.leb_le; lia). replace (i <=? ai) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
        -- intros F. exact (M5 i ltac:(lia) A F).
        -- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
           pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
      * assert (F : Z.testbit (mask_upto last - mask_upto ai) i = true) by (apply M6; lia).
        apply one5_iff_create; [apply one5_B| intros C; exact (nBC (conj F C))| intros D; exact (nBD (conj F D))].
        -- replace (i <=? ai) with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r. discriminate.
        -- exact F.
        -- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
           pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
  - right. split; [intros s Hs; discriminate|]. intros s Hs. inversion Hs. exists 0. rewrite Elast. split; [lia|].
    rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
Qed.

Lemma fin_MR3 : MR st3 m = mkMeta None None (Some b) (mask_upto ai - 1) (mask_upto last - mask_upto ai) last 1 sc ml.
Proof. unfold st3, MR. rewrite get_meta_rec_upd_same. fold (MR st2 m). rewrite Em. reflexivity. Qed.
Lemma fin_MR3_other x : x <> m -> MR st3 x = MR st2 x.
Proof. intros NE. unfold st3, MR. apply get_meta_rec_upd_other. exact NE. Qed.

Lemma fin_queue_eq : queue (LActive sc) m st3 k bail = k st4.
Proof. apply queue_eq; fold (MR st3 m); rewrite fin_MR3; reflexivity. Qed.

Lemma fin_head3 : get_head st3 (LActive sc) = None.
Proof. unfold st3. rewrite get_head_upd_meta. cbn. exact HA. Qed.

Lemma fin_INV4 : INVL (mkX idle [] (Some s0) None (Some m)) st4 L BL LS4.
Proof.
  apply (INVL_queue (mkX idle [] (Some s0) None (Some m)) st3 L BL LS m (LActive sc) fin_INV3).
  - rewrite fin_MR3. reflexivity.
  - unfold st3. rewrite s_metas_upd_meta, lookup_insert_eq. discriminate.
  - cbn. split; [exact Hsc|]. split; [exists b; exists ai; exact Hb|]. split; [rewrite fin_MR3; reflexivity| reflexivity].
Qed.

Lemma fin_LS4 : LS4 (LActive sc) = [m].
Proof. unfold LS4. rewrite fupd_eq, fin_empty. reflexivity. Qed.

Lemma fin_MR4 : geo_of (MR st4 m) = geo_of (MR st3 m) /\ m_avail (MR st4 m) = m_avail (MR st3 m) /\ m_freed (MR st4 m) = m_freed (MR st3 m).
Proof.
  pose proof (queue_data (LActive sc) m st3 m) as D. apply data_of_eq in D. destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  unfold geo_of. fold st4 in D1, D2, D3, D4, D5, D6, D7. rewrite D1, D4, D7, D6, D2, D3. auto.
Qed.

Lemma fin_geo x : geo_of (MR st4 x) = geo_of (MR st2 x).
Proof.
  pose proof (queue_data (LActive sc) m st3 x) as D. apply data_of_eq in D. destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  fold st4 in D1, D2, D3, D4, D5, D6, D7. unfold geo_of. rewrite D1, D4, D6, D7.
  destruct (aptr_eq_dec x m) as [->|NE].
  - rewrite fin_MR3, Em. reflexivity.
  - rewrite (fin_MR3_other x NE). reflexivity.
Qed.

Theorem slot_finish_ok :
  exists LS',
    queue (LActive sc) m st3 k bail = k st4
    /\ INVL (xpend (X_as idle) (Some s0)) st4 L BL LS'
    /\ TF2 st4
    /\ active st4 sc = Some m /\ (forall sc', sc' <> sc -> active st4 sc' = active st2 sc')
    /\ s_groups st4 = s_groups st2 /\ s_tick st4 = s_tick st2 /\ s_shadow st4 = s_shadow st2
    /\ m_last_idx (MR st4 m) = last /\ m_sizeclass (MR st4 m) = sc /\ get_stride (MR st4 m) = get_stride (MR st2 m)
    /\ (forall i, sstart (MR st4 m) i = sstart (MR st2 m) i) /\ s_regions st4 = s_regions st2 /\ s_secret st4 = s_secret st2.
Proof.
  exists LS4. destruct (queue_frame (LActive sc) m st3) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC). fold st4 in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, FC.
  pose proof fin_INV4 as INV4.
  assert (G4 : s_groups st4 = s_groups st2) by (rewrite F5; reflexivity).
  destruct (geo_facts _ _ (fin_geo m)) as (S1 & S2 & S3 & S4).
  split; [exact fin_queue_eq|].
  split.
  {
    apply (INVL_clear_fresh (mkX idle [] (Some s0) None (Some m)) st4 L BL LS4 m INV4 eq_refl).
    intros b' ai' Hb'. rewrite G4 in Hb'.
    assert (Eb : b' = b /\ ai' = ai).
    { pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ fin_hosts (ex_intro _ ai' Hb')) as <-. rewrite Hb in Hb'. inversion Hb'. auto. }
    destruct Eb as [-> ->].
    assert (Esc : m_sizeclass (MR st4 m) = sc) by (pose proof (fin_geo m) as G; unfold geo_of in G; rewrite Em in G; injection G; intros; congruence).
    rewrite Esc. split; [| split; [| split]].
    - intros _. rewrite fin_LS4. left. reflexivity.
    - intros _ NI. exfalso. apply NI. exists (LActive sc). rewrite fin_LS4. left. reflexivity.
    - intros sc0 Hin Hh. exfalso.
      pose proof (il_disj _ _ (proj1 (proj2 (proj2 (proj2 INV4)))) (LActive sc0) (LActive sc) m Hin ltac:(rewrite fin_LS4; left; reflexivity)) as E.
      inversion E. subst sc0. rewrite fin_LS4 in Hh. apply Hh. reflexivity.
    - intros _ HU. destruct fin_MR4 as (_ & EA & EF). rewrite EA, EF, fin_MR3. cbn. rewrite S4 in HU.
      destruct (UND HU) as [-> ->]. cbn. split; reflexivity. }
  split.
  { apply (TF2_kept st2 st4); [rewrite F2; reflexivity| rewrite F7; reflexivity| | exact TF].
    apply geom_kept_geo; [intros bb h Hh; rewrite G4; exact Hh| apply fin_geo]. }
  split; [change (active st4 sc) with (get_head st4 (LActive sc)); unfold st4; rewrite queue_head; destruct (decide (LActive sc = LActive sc)); [rewrite fin_head3; reflexivity| congruence]|].
  split; [intros sc' NE; change (active st4 sc') with (get_head st4 (LActive sc')); change (active st2 sc') with (get_head st2 (LActive sc')); unfold st4; rewrite queue_head; destruct (decide (LActive sc' = LActive sc)); [congruence|]; unfold st3; rewrite get_head_upd_meta; reflexivity|].
  split; [exact G4|]. split; [rewrite F7; reflexivity|]. split; [rewrite F2; reflexivity|].
  pose proof (fin_geo m) as G. unfold geo_of in G. rewrite Em in G. injection G. intros E4 E3 E2 E1.
  split; [exact E2|]. split; [exact E4|]. split; [exact S4|]. split; [exact S1|]. split; [rewrite F1; reflexivity| rewrite F8; reflexivity].
Qed.
End FINISH.
End MI_WSlot.

Module MI_WSlot2.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KInv. Import SM01. Import SM01.MI_Tree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_Inv. Import SM08.MI_Kit. Import SM01.MI_Arith. Import SM01.MI_Geom. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_List. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_Ext. Import SM01.MI_Shadow. Import SM01.MI_Pres1. Import SM01.MI_Pres2. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_Pres3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_Pres4. Import SM01.MI_Read. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_WFree2. Import SM02. Import SM02.MI_Ledger. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_WAMeta. Import SM04. Import SM04.MI_WAMeta2. Import SM04.MI_WTry. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_WTry2. Import SM02.MI_WGroup. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import MI_WCreate. Import SM03. Import SM03.MI_Cnt. Import SM04.MI_TF2. Import MI_WCreate2. Import MI_WSlot.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Definition SLOT_POST (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
   (st1 : mstate) (idx : Z) (L1 : mled) (LS1 : lhead -> list aptr) : Prop :=
  (forall sc', sc' < sc -> active st1 sc' = active st sc') /\ ld_live L1 = ld_live L /\ GP st st1 /\
  ((idx = -1 /\ INVL (X_as idle) st1 L1 BL LS1 /\ TF0 st1)
   \/ (exists g bg ai, 0 <= idx <= m_last_idx (MR st1 g) /\ active st1 sc = Some g
         /\ s_groups st1 !! bg = Some (mkGhdr (Some g) ai) /\ m_sizeclass (MR st1 g) = sc
         /\ req + IB <= get_stride (MR st1 g)
         /\ (sc < 28 -> get_stride (MR st1 g) = UNIT * size_class sc)
         /\ INVL (xpend (X_as idle) (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1
         /\ TF2 st1)).

Definition AG_POST (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
   (st2 : mstate) (go : optr) (L2 : mled) (LS2 : lhead -> list aptr) : Prop :=
  (forall sc', sc' <= sc -> active st2 sc' = active st sc') /\ ld_live L2 = ld_live L /\ GP st st2 /\
  match go with
  | None => INVL (X_as idle) st2 L2 BL LS2 /\ TF0 st2
  | Some m => exists b ai last ml,
      s_groups st2 !! b = Some (mkGhdr (Some m) ai)
      /\ MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml
      /\ 0 <= ai <= last /\ last <= 31
      /\ req + IB <= get_stride (MR st2 m)
      /\ (sc < 28 -> get_stride (MR st2 m) = UNIT * size_class sc)
      /\ (get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0)
      /\ INVL (mkX idle [] None None (Some m)) st2 L2 BL LS2 /\ TF2 st2
  end.

Definition REC_OK (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop) : Prop :=
  forall j idle st L BL LS req (k : mstate -> Z -> M T) bail,
  sc < j < 48 ->
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= req -> req + IB <= UNIT * size_class j ->
  (forall st1 idx L1 LS1, SLOT_POST idle j req st L BL st1 idx L1 LS1 -> ftree L1 (k st1 idx) Post) ->
  ftree L (rec st j req k bail) Post.


Definition ag_cnt1 (sc u0 : Z) : Z :=
  let size := UNIT * size_class sc in
  let cnt := cnt0_of sc u0 in
  if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt.

Definition ag_cnt2 (sc cnt1 u1 : Z) (nosmall : bool) : Z :=
  if (u1 <? 4 * cnt1) && negb nosmall then adj sc (UNIT * size_class sc) cnt1 else cnt1.

Definition ag_cn3 (sc req cnt2 u1 : Z) (nosmall : bool) : Z * Z :=
  let size := UNIT * size_class sc in
  let needed := round_up_pg (size * cnt2 + UNIT) in
  if negb nosmall && (cnt2 <=? 7) then
    let req' := round_up_pg (req + IB + UNIT) in
    if (req' <? size + UNIT) || ((4 * PGSZ <=? req') && (u1 <? 2 * cnt2)) then (1, req') else (cnt2, needed)
  else (cnt2, needed).

Lemma ag_arith sc req u0 u1 ns c3 n3 :
  0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  let size := UNIT * size_class sc in
  (PGSZ / 2 < size * ag_cnt1 sc u0 + UNIT ->
   ag_cn3 sc req (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) u1 ns = (c3, n3) ->
   grp_ok sc c3 n3 = true /\ ((c3 = 1 /\ n3 = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (size * c3 + UNIT <= n3)))
  /\ (size * ag_cnt1 sc u0 + UNIT <= PGSZ / 2 -> nest_ok sc (ag_cnt1 sc u0) = true).
Proof.
  intros Hsc Hreq Hfit. pose proof (alloc_group_arith sc req u0 u1 ns Hsc Hreq Hfit) as AR. cbn zeta in AR.
  change (if (cnt0_of sc u0 =? 1) && (UNIT * size_class sc * cnt0_of sc u0 + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc u0) with (ag_cnt1 sc u0) in AR.
  destruct AR as [AR1 AR2]. cbn zeta. split; [| exact AR2].
  intros HB E. specialize (AR1 HB).
  change (if (u1 <? 4 * ag_cnt1 sc u0) && negb ns
          then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 2
               else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 3
               else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 3
               else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 5
               else ag_cnt1 sc u0
          else ag_cnt1 sc u0) with (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) in AR1.
  set (c2 := ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) in *. clearbody c2.
  unfold ag_cn3 in E. cbn zeta in E.
  destruct (negb ns && (c2 <=? 7)).
  - destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
    + inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [R|(R1 & R2 & R3)]; [left; exact R| right; rewrite R2 at 1; lia].
    + inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [(R1 & R2 & R3)|(R1 & R2 & R3)]; [| right; exact R3].
      right. rewrite R1. pose proof (proj1 (round_up_pg_spec (UNIT * size_class sc * 1 + UNIT))). lia.
  - inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [(R1 & R2 & R3)|(R1 & R2 & R3)]; [| right; exact R3].
    right. rewrite R1. pose proof (proj1 (round_up_pg_spec (UNIT * size_class sc * 1 + UNIT))). lia.
Qed.


Lemma shadow_next_rid_none X st L BL LS : INVL X st L BL LS -> s_shadow st !! s_next_rid st = None.
Proof.
  intros INV. destruct (s_shadow st !! s_next_rid st) as [sh|] eqn:E; [| reflexivity]. exfalso.
  destruct (ish_dom _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ E) as (r & Hr & _).
  pose proof (ir_ids _ _ _ (proj1 INV) _ _ Hr). lia.
Qed.

Lemma LS_empty_of X st L BL LS sc : INVL X st L BL LS -> active st sc = None -> LS (LActive sc) = [].
Proof.
  intros INV HA. pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. cbn in HH. rewrite HA in HH.
  destruct (LS (LActive sc)); [reflexivity| discriminate].
Qed.

Lemma step_seq_fields st : let st' := step_seq st in
  s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ (forall sc, active st' sc = active st sc) /\ s_regions st' = s_regions st
  /\ s_next_rid st' = s_next_rid st /\ s_metas st' = s_metas st /\ s_groups st' = s_groups st /\ (forall sc, usage st' sc = usage st sc).
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); cbn; repeat split; reflexivity. Qed.

Lemma account_bounce_fields sc0 st : let st' := account_bounce sc0 st in
  s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ (forall sc, active st' sc = active st sc) /\ s_regions st' = s_regions st
  /\ s_next_rid st' = s_next_rid st /\ s_metas st' = s_metas st /\ s_groups st' = s_groups st /\ (forall sc, usage st' sc = usage st sc).
Proof.
  unfold account_bounce. destruct (sc_in_seq_range sc0); [| cbn; repeat split; reflexivity].
  destruct (negb (unmap_seq st (sc0 - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc0 - 7) <? 10)); [| cbn; repeat split; reflexivity].
  destruct (bounces st (sc0 - 7) + 1 <? 100); cbn; repeat split; reflexivity.
Qed.


Section MMAP_BRANCH.
Variables (T : Type) (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt needed : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis RED : (cnt = 1 /\ needed = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (UNIT * size_class sc * cnt + UNIT <= needed).
Hypothesis HK : forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let st1' := step_seq (account_bounce sc st1).
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let AI := let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if cnt - 1 <? ai then cnt - 1 else ai in if ai <? 0 then 0 else ai.

Lemma st1'_facts :
  INVL (X_as (m :: idle)) st1' L1 BL LS1 /\ s_shadow st1' = s_shadow st1 /\ s_tick st1' = s_tick st1
  /\ (forall sc', active st1' sc' = active st1 sc') /\ TF0 st1' /\ s_regions st1' = s_regions st1 /\ s_secret st1' = s_secret st1.
Proof.
  destruct (account_bounce_fields sc st1) as (A1 & A2 & A3 & A4 & _). destruct (step_seq_fields (account_bounce sc st1)) as (B1 & B2 & B3 & B4 & _).
  assert (SH : s_shadow st1' = s_shadow st1) by (unfold st1'; rewrite B1, A1; reflexivity).
  assert (TK : s_tick st1' = s_tick st1) by (unfold st1'; rewrite B2, A2; reflexivity).
  split; [apply INVL_step_seq; apply INVL_account_bounce; exact INV1|].
  split; [exact SH|]. split; [exact TK|]. split; [intros sc'; unfold st1'; rewrite B3, A3; reflexivity|].
  split; [exact (TF0_ctrl st1 st1' SH TK TF1)|]. split; [unfold st1'; rewrite B4, A4; reflexivity|].
  unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity.
Qed.

Theorem ag_mmap_ft :
  ftree L1 (SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
    if negb (mmap_answer_ok (s_atop st1') (live_ranges st1') needed r) then bad_answer bail
    else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
    else let '(st2, rid) := new_region RKGroup r needed st1' in
         ag_tail full_lay (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) sc m (rid, 0) cnt AI k)) Post.
Proof.
  destruct st1'_facts as (INV1' & SH1 & TK1 & ACT1 & TF1' & RG1 & SS1').
  pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  apply ftree_vis; [reflexivity| reflexivity| | |].
  - cbn. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV1'))|]. split; [reflexivity|]. split; [reflexivity|].
    split; [right; reflexivity|]. unfold LEN_MAX. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha |- *.
    change (event_post L1 (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L1 else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L1) L1 else KInv.set_groups ((a, needed) :: ld_groups L1) L1 else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L1)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    +
      rewrite free_meta_eq.
      destruct (free_idle_ok idle m st1' L1 BL LS1 INV1' NIm) as (INV2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK. split; [intros sc' _; rewrite F7, ACT1; apply HA1|]. split; [exact HL1|].
      split.
      { eapply GP_trans; [exact HG1| apply GP_eq; [rewrite F5, RG1; reflexivity|]].
        unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st1')) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. cbn. exact SS1'. }
      split; [exact INV2|]. exact (TF0_ctrl st1' _ F1 F2 TF1').
    +
      destruct (new_region RKGroup a needed st1') as [st2 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st1') by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est2 : st2 = fst (new_region RKGroup a needed st1')) by (rewrite EN; reflexivity).
      pose proof (INVL_new_group_region (X_as (m :: idle)) st1' L1 BL LS1 a needed INV1' eq_refl Ha ER ltac:(unfold LEN_MAX; lia)) as INV2.
      rewrite <- Est2, <- Erid in INV2. cbn [xorph X_as x_idle x_zomb x_pend x_fresh] in INV2.
      assert (Hr : s_regions st2 !! rid = Some (mkRegion RKGroup a needed)).
      { rewrite Est2, ng_lookup, Erid, N.eqb_refl. reflexivity. }
      assert (NS : s_shadow st2 !! rid = None).
      { rewrite Est2, Erid. change (s_shadow (fst (new_region RKGroup a needed st1'))) with (s_shadow st1'). exact (shadow_next_rid_none _ _ _ _ _ INV1'). }
      assert (ACT2 : forall sc', active st2 sc' = active st0 sc') by (intros sc'; rewrite Est2; change (active (fst (new_region RKGroup a needed st1')) sc') with (active st1' sc'); rewrite ACT1; apply HA1).
      assert (EMP : LS1 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT2; exact HA0).
      assert (TF2' : TF0 st2) by (apply (TF0_ctrl st1'); [rewrite Est2; reflexivity| rewrite Est2; reflexivity| exact TF1']).
      pose proof (clamp_ai (UNIT * size_class sc) cnt ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
      assert (HAI0 : sc = 0 -> AI = cnt - 1).
      { intros Hsc0. unfold AI. rewrite Hsc0. change (UNIT * size_class 0) with 16. change ((4096 - UNIT) / 16 - 1) with 254.
        pose proof (grp_ok_sound sc cnt needed GRP) as (Gc & _).
        replace (cnt - 1 <? 254) with true by (symmetry; apply Z.ltb_lt; lia). replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite ag_tail_eq.
      change (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) with (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)).
      destruct (ag_top_ok idle st2 (KInv.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1 m rid (mkRegion RKGroup a needed) sc cnt needed AI
                  INV2 Hr eq_refl eq_refl NS GRP Hsc HAI HAI0 EMP TF2' NIm) as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
      pose proof (top_facts rid sc cnt needed AI GRP Hsc) as TFX. cbn zeta in TFX.
      destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
      rewrite Emr in MR', F4, F5, F7, F8, F9. rewrite <- MR' in F4, F5, F7, F8, F9.
      eapply HK. split; [intros sc' _; rewrite ACT'; apply ACT2|]. split; [cbn; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1|]. split.
        - intros q rq Hq Kq. rewrite agt_regions. cbn. rewrite Est2. apply (ng_keep _ _ _ _ _ _ _ INV1'). rewrite RG1. exact Hq.
        - rewrite agt_secret. cbn. rewrite Est2. cbn. exact SS1'. }
      exists (rid, 0), AI, (cnt - 1), (Z.shiftr needed 12).
      split; [exact GR'|]. split; [exact MR'|]. split; [exact HAI|]. split; [lia|].
      assert (STR : get_stride (MR (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) m)
                    = if (cnt - 1 =? 0) && negb (Z.shiftr needed 12 =? 0) then Z.shiftr needed 12 * 4096 - UNIT else UNIT * size_class sc).
      { rewrite MR'. unfold get_stride. cbn. reflexivity. }
      assert (NZ : (Z.shiftr needed 12 =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite NZ in STR. cbn [negb] in STR. rewrite andb_true_r in STR.
      assert (E12 : Z.shiftr needed 12 * 4096 = needed) by (rewrite F2; pose proof (Z.div_mod needed 4096 ltac:(lia)); lia).
      split; [| split; [| split; [| split; [exact INV'| apply TF0_TF2; exact TF']]]].
      * destruct RED as [(C1 & Nd & S28)|NR].
        -- rewrite STR. replace (cnt - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite E12, Nd.
           pose proof (proj1 (round_up_pg_spec (req + IB + UNIT))). unfold UNIT, IB in *. lia.
        -- rewrite STR. destruct (Z.eqb_spec (cnt - 1) 0); [rewrite E12; unfold UNIT in *; nia| lia].
      * intros S28. destruct RED as [(C1 & Nd & S28')|NR]; [lia|].
        rewrite STR in F5 |- *. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| reflexivity].
        destruct F5 as [F5|]; [| lia]. rewrite E12 in F5 |- *. assert (cnt = 1) by lia. subst cnt. lia.
      * intros UNDER. rewrite STR in UNDER. destruct RED as [(C1 & Nd & S28)|NR].
        -- clear - HAI C1. lia.
        -- exfalso. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| lia]. rewrite E12 in UNDER. assert (cnt = 1) by lia. subst cnt. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. exact I.
Qed.
End MMAP_BRANCH.


Section NEST_BRANCH.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T).
Variables (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OK T rec sc Post.
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis ND : NoDup idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis HK : forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).

Theorem ag_nest_ft :
  ftree L1 (rec st1 j (UNIT + cnt * size - IB) (fun st2 idx =>
     if idx <? 0 then free_meta m st2 (fun st3 => k st3 None) bail
     else match active st2 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g => ag_tail full_lay (upd_meta m (m_set_maplen 0) (nest_layout st2 g idx j size cnt)) sc m (slot_of st2 g idx) cnt (cnt - 1) k
          end) bail) Post.
Proof.
  pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0. destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
  apply (REC j (m :: idle) st1 L1 BL LS1 (UNIT + cnt * size - IB) _ bail ltac:(lia) INV1 TF1).
  - apply NoDup_cons. split; [intros Hin; apply NIm; apply list_elem_of_In; exact Hin| exact ND].
  - exact N5.
  - lia.
  - intros st2 idx L2 LS2 (ACT & LIVE & GP2 & RES). destruct RES as [(-> & INV2 & TF2')|(g & bg & aig & Hidx & HAj & Hg & SCg & FIT & STR & INV2 & TF2')].
    +
      change (-1 <? 0) with true. cbn iota. rewrite free_meta_eq.
      destruct (free_idle_ok idle m st2 L2 BL LS2 INV2 NIm) as (INV3 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK. split; [intros sc' Hs; rewrite F7, ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq; [exact F5|]]].
        unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st2)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity. }
      split; [exact INV3|]. exact (TF0_ctrl st2 _ F1 F2 TF2').
    + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HAj.
      assert (Hgh : hosts st2 bg g) by (exists aig; exact Hg).
      assert (Ep : slot_of st2 g idx = (fst bg, sstart (MR st2 g) idx)).
      { unfold slot_of. fold (MR st2 g). exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ idx Hgh). }
      rewrite Ep. rewrite ag_tail_eq.
      specialize (STR ltac:(lia)).
      assert (EMP : LS2 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT by lia; rewrite HA1; exact HA0).
      destruct (ag_nested_ok idle st2 L2 BL LS2 m g bg aig idx sc cnt INV2 Hg Hidx SCg STR NEST Hsc EMP TF2' NIm)
        as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
      pose proof (nst_facts st2 g bg idx sc cnt NEST Hsc) as NF. cbn zeta in NF.
      destruct NF as (_ & _ & _ & _ & _ & _ & _ & Emr & Es).
      fold size in MR', GR', ACT', INV', TF', Emr, Es |- *. fold j in MR', GR', ACT', INV', TF' |- *.
      rewrite Emr in MR'. rewrite Emr in Es.
      eapply HK. split; [intros sc' Hs; rewrite ACT', ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq]].
        - rewrite agt_regions. change (s_regions (nest_layout st2 g idx j size cnt) = s_regions st2).
          rewrite <- (s_regions_strip (nest_layout st2 g idx j size cnt)), strip_nest_layout. reflexivity.
        - rewrite agt_secret. change (s_secret (nest_layout st2 g idx j size cnt) = s_secret st2).
          rewrite <- (s_secret_strip (nest_layout st2 g idx j size cnt)), strip_nest_layout. reflexivity. }
      exists (fst bg, sstart (MR st2 g) idx), (cnt - 1), (cnt - 1), 0.
      rewrite Z.sub_diag. split; [exact GR'|]. split; [exact MR'|]. split; [lia|]. split; [lia|].
      rewrite MR', Es. split; [unfold size; lia|]. split; [intros _; reflexivity|]. split; [unfold size; intros; lia|].
      split; [exact INV'| exact TF'].
Qed.
End NEST_BRANCH.


Section AG.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OK T rec sc Post.

Theorem alloc_group_ft idle st L BL LS req (k : mstate -> optr -> M T) bail :
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  active st sc = None ->
  (forall st2 go L2 LS2, AG_POST idle sc req st L BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post) ->
  ftree L (alloc_group T full_lay rec st sc req k bail) Post.
Proof.
  intros INV TF ND Hsc Hreq Hfit HA HK. unfold alloc_group.
  eapply (alloc_meta_ft T BL Post _ bail (X_as idle) st L); [ | | exact INV| apply amf_refl| apply lf_refl].
  -
    intros st1 L1 LS1 INV1 AF LF. cbn beta iota. eapply HK.
    split; [intros sc' _; apply (amf_active _ _ AF)|]. split; [exact (lf_live _ _ LF)|]. split; [exact (GP_amf _ _ AF)|]. split; [exact INV1|].
    exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
  -
    intros st1 L1 LS1 m INV1 NIm AF LF. cbn beta iota zeta.
    change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
      with (cnt0_of sc (usage st1 sc)).
    change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
      with (ag_cnt1 sc (usage st1 sc)).
    change (lh_nest full_lay) with nest_layout.
    assert (HA1 : forall sc', active st1 sc' = active st sc') by (intros; apply (amf_active _ _ AF)).
    assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
    pose proof (ag_arith sc req (usage st1 sc)) as AR.
    set (c1 := ag_cnt1 sc (usage st1 sc)) in *.
    destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
    +
      set (ns := is_bouncing sc st1).
      set (st1' := step_seq (account_bounce sc st1)).
      set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc).
      change (if (u1 <? 4 * c1) && negb ns
              then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1) then 2
                   else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1) then 5
                   else c1
              else c1) with (ag_cnt2 sc c1 u1 ns).
      set (c2 := ag_cnt2 sc c1 u1 ns).
      specialize (AR u1 ns). 
      assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 ns = (c3, n3) ->
        ftree L1 (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
          if negb (mmap_answer_ok (s_atop st1') (live_ranges st1') n3 r) then bad_answer bail
          else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
          else let '(st2, rid) := new_region RKGroup r n3 st1' in
               ag_tail full_lay (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
                 (let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k)) Post).
      { intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP RED].
        exact (ag_mmap_ft T idle st st1 L L1 BL LS1 m sc req c3 n3 k bail Post INV1 NIm TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) GRP RED HK). }
      unfold ag_cn3 in GO. cbn zeta in GO.
      destruct (negb ns && (c2 <=? 7)).
      * destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
        -- cbn beta iota. exact (GO _ _ eq_refl).
        -- cbn beta iota. exact (GO _ _ eq_refl).
      * cbn beta iota. exact (GO _ _ eq_refl).
    +
      pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
      exact (ag_nest_ft T rec idle st st1 L L1 BL LS1 m sc req c1 k bail Post REC INV1 NIm ND TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) NEST HK).
Qed.
End AG.
End MI_WSlot2.
