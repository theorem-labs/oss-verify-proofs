(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Decode.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv KStep KLink KEv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_Cnt MI_TF2 MI_WCreate2 MI_WSlot MI_WSlot2 MI_WSlot3 MI_WMalloc MI_Bits
  LB_Tables LB_Inv LB_Sum LB_Kernel LB_KCount LB_Embed LB_Bound LB_Count LB_WNtf LB_XferF LB_Tree LB_QM LB_WAMeta LB_WTry LB_Cnt LB_AG LB_StmtA LB_WFree LB_WSlot.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma MIS_le_LS st BL c : MIS st BL c <= LS st BL c.
Proof.
  unfold MIS, LS. induction BL as [|k l IH]; [unfold zcount, zlen; cbn; lia|].
  rewrite !zcount_cons. destruct (slotcls st (bslot k)) as [c'|]; [| lia]. destruct (c' =? c); cbn [andb]; [destruct (size_to_class (bsize k) =? c - 1); lia| lia].
Qed.

Lemma SG_add_block st BL c off n m i :
  SG st BL -> s_slots st !! c = Some (m, i) -> m_sizeclass (MR st m) < 48 -> 0 <= n < MMAP_THRESHOLD ->
  (size_to_class n = m_sizeclass (MR st m) \/ (size_to_class n = m_sizeclass (MR st m) - 1 /\ MIS st BL (m_sizeclass (MR st m)) <= 12)) ->
  SG st (((c, off), n) :: BL).
Proof.
  intros S Hs Hsc Hn CLS. destruct S as [S1 S2 S3 S4 S5 S6 S7]. constructor; auto.
  - intros k [<-|Hk]; [| exact (S1 k Hk)]. exists m, i. cbn [bslot bsize fst snd]. split; [exact Hs|].
    split; [intros _; split; [lia| destruct CLS as [E|[E _]]; [left; exact E| right; exact E]]| intros E63; exfalso; lia].
  - intros c'. unfold MIS. rewrite zcount_cons. fold (MIS st BL c'). cbn [bslot bsize fst snd]. unfold slotcls at 1. rewrite Hs. unfold cls.
    destruct (Z.eqb_spec (m_sizeclass (MR st m)) c') as [<-|NE]; cbn [andb]; [| pose proof (S2 c'); lia].
    destruct (Z.eqb_spec (size_to_class n) (m_sizeclass (MR st m) - 1)) as [E|NE]; [| pose proof (S2 (m_sizeclass (MR st m))); lia].
    destruct CLS as [E'|[_ M]]; [exfalso; lia| lia].
  - intros b x ai Hb H63. right. exact (S6 b x ai Hb H63).
Qed.

Lemma AQ_add_block st BL P c off n :
  AQ st BL P -> 0 <= n -> ROOM BL P n -> AQ st (((c, off), n) :: BL) P.
Proof.
  intros A Hn [R1 R2]. destruct A as [A1 A2 A3 A4 A5]. constructor; auto.
  - intros c' Hc'. unfold LR. rewrite zcount_cons. fold (LR BL c'). cbn [bsize snd]. unfold isbig. cbn [bsize snd].
    destruct (Z.leb_spec MMAP_THRESHOLD n) as [GE|LT]; cbn [negb andb]; [exact (A1 c' Hc')|].
    destruct (Z.eqb_spec (size_to_class n) c') as [<-|NE]; [specialize (R1 LT); lia| exact (A1 c' Hc')].
  - unfold n63. rewrite zcount_cons. fold (n63 BL). unfold isbig. cbn [bsize snd].
    destruct (Z.leb_spec MMAP_THRESHOLD n) as [GE|LT]; [specialize (R2 GE); lia| exact A3].
Qed.

Lemma R63_cons c off n BL : R63 (((c, off), n) :: BL) = bigb n + R63 BL.
Proof. unfold R63, bigb, isbig. cbn [map bsize snd]. rewrite zsum_cons. reflexivity. Qed.

Lemma bigb_small n : n < MMAP_THRESHOLD -> bigb n = 0.
Proof. intros H. unfold bigb. replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; exact H). reflexivity. Qed.

Lemma bigb_big n : MMAP_THRESHOLD <= n -> bigb n = round_up_pg (n + IB + UNIT).
Proof. intros H. unfold bigb. replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact H). reflexivity. Qed.

Lemma mmap_len_rup l : mmap_len l = round_up_pg l.
Proof. unfold mmap_len. symmetry. apply round_up_pg_eq. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma small_class X st L BL LS n : INVL X st L BL LS -> 0 <= n < MMAP_THRESHOLD ->
  let sc0 := size_to_class n in
  let sc := match active st sc0 with
            | Some _ => sc0
            | None =>
              if (4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0) then
                let usage1 := usage st (Z.lor sc0 1) in
                let usage1 := match active st (Z.lor sc0 1) with
                              | None => usage1 + 3
                              | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc0 1))) in
                                          if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                              end in
                if usage1 <=? 12 then Z.lor sc0 1 else sc0
              else sc0
            end in
  0 <= sc < 48 /\ n + IB <= UNIT * size_class sc /\ (size_to_class n = sc \/ (size_to_class n = sc - 1 /\ gcnt st sc <= 12)).
Proof.
  intros INV Hn. pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT]. cbn zeta.
  set (sc0 := size_to_class n) in *.
  destruct (active st sc0); [auto|].
  destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [| auto].
  apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  rewrite (lor1_even sc0 ltac:(lia) EV).
  assert (U : usage st (sc0 + 1) = gcnt st (sc0 + 1)) by exact (ia_usage _ (proj1 (proj2 INV)) (sc0 + 1) ltac:(lia)).
  match goal with |- context [if ?c then sc0 + 1 else sc0] => destruct c eqn:LE end; [| auto].
  apply Z.leb_le in LE.
  pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)).
  split; [lia|]. split; [unfold UNIT in *; lia|]. right. split; [lia|].
  rewrite <- U. destruct (active st (sc0 + 1)); [| lia]. destruct (_ && _); lia.
Qed.

Lemma size_to_class_ne62 m : size_to_class m <> 62.
Proof.
  unfold size_to_class.
  set (n' := Z.shiftr (m + IB - 1) 4). destruct (Z.ltb_spec n' 10) as [LT|GE]; [lia|].
  set (i := (28 - clz32 (n' + 1)) * 4 + 8).
  assert (S61 : forall k, 48 <= k -> size_class k = 0).
  { intros k Hk. unfold size_class. rewrite nth_overflow; [reflexivity|]. cbn. lia. }
  destruct (size_class (i + 1) <? n' + 1) eqn:E1.
  - destruct (size_class (i + 2) <? n' + 1) eqn:E2; [lia|]. intros E. replace (i + 2) with 62 in E2 by lia.
    rewrite (S61 62 ltac:(lia)) in E2. apply Z.ltb_ge in E2. lia.
  - destruct (size_class i <? n' + 1) eqn:E2; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section C63Q.
Variables (st3 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (P : Z -> Z).
Variables (g : aptr) (rid : N) (r : region) (needed n off : Z).
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
Hypothesis En : needed = n + IB + UNIT.
Hypothesis Hbig : MMAP_THRESHOLD <= n.
Hypothesis SG3 : SG st3 BL.
Hypothesis Q3 : QM X st3 0.
Hypothesis A3 : AQ st3 BL P.
Hypothesis R63room : n63 BL + 1 <= P 63.
Let ml := (needed + 4095) / 4096.
Let st4 := upd_meta g (F63 rid ml) st3.
Let st5 := put_group p (Some g) (group_active_idx st4 p) (hdr_havoc p st4).
Let st6 := add_slots g p (get_stride (get_meta_rec st5 g)) 1 st5.
Let mr' := mkMeta None None (Some p) 0 0 0 1 63 ml.
Let k0 : blk := (((rid, 16), off), n).

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma q63_metas : s_metas st6 = <[g := mr']> (s_metas st3).
Proof.
  change (s_metas st6) with (s_metas st4). unfold st4. rewrite s_metas_upd_meta. fold (MR st3 g).
  rewrite (c63_MRg st3 L BL LS g rid INV). unfold ml, mr', p. rewrite (c63_F rid needed Hn). reflexivity.
Qed.

Lemma q63_groups : s_groups st6 = <[p := mkGhdr (Some g) 0]> (s_groups st3).
Proof.
  change (s_groups st6) with (s_groups st5). unfold st5, put_group. cbn [s_groups Malloc.set_groups].
  unfold group_active_idx, get_group. change (s_groups st4) with (s_groups st3). rewrite (c63_nogroup st3 L BL LS g rid INV). reflexivity.
Qed.

Lemma q63_rec5 : get_meta_rec st5 g = mr'.
Proof. unfold get_meta_rec. change (s_metas st5) with (s_metas st6). rewrite q63_metas, lookup_insert_eq. reflexivity. Qed.

Lemma q63_slots : s_slots st6 = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof.
  unfold st6, add_slots. rewrite q63_rec5. cbn [Z.iter Pos.iter snd s_slots set_slots].
  replace (aadd p (UNIT + get_stride mr' * 0)) with (rid, 16); [reflexivity|].
  unfold aadd, p. cbn [fst snd]. f_equal. unfold UNIT. lia.
Qed.

Lemma q63_MR x : x <> g -> MR st6 x = MR st3 x.
Proof. intros NE. unfold MR, get_meta_rec. rewrite q63_metas, lookup_insert_ne by congruence. reflexivity. Qed.

Lemma q63_MRg : MR st6 g = mr'.
Proof. unfold MR, get_meta_rec. rewrite q63_metas, lookup_insert_eq. reflexivity. Qed.

Lemma q63_old x : (exists b, hosts st3 b x) -> x <> g /\ MR st6 x = MR st3 x.
Proof.
  intros [b Hb]. assert (NE : x <> g).
  { intros ->. pose proof (hosts_mem _ _ _ IM _ _ Hb) as MM. rewrite (c63_MRg st3 L BL LS g rid INV) in MM. cbn in MM. discriminate. }
  split; [exact NE| exact (q63_MR x NE)].
Qed.

Lemma q63_nogroup_rid b : fst b = rid -> s_groups st3 !! b = None.
Proof. intros Hb. destruct (ir_orph _ _ _ (proj1 INV) rid eq_refl) as (r0 & _ & _ & NG). exact (NG b Hb). Qed.

Lemma q63_noslot : s_slots st3 !! (rid, 16) = None.
Proof.
  destruct (s_slots st3 !! (rid, 16)) as [[x i]|] eqn:E; [| reflexivity]. exfalso.
  destruct (is_valid _ _ _ IS _ _ _ E) as ([b Hb] & Hi & Es).
  rewrite (slot_start'_eq _ _ _ IM x b i Hb) in Es. assert (Eb : fst b = rid) by (inversion Es; reflexivity).
  destruct Hb as [ai Hb]. rewrite (q63_nogroup_rid b Eb) in Hb. discriminate.
Qed.

Lemma q63_slots_old s v : s_slots st3 !! s = Some v -> s_slots st6 !! s = Some v.
Proof. intros Hs. rewrite q63_slots, lookup_insert_ne; [exact Hs|]. intros <-. rewrite q63_noslot in Hs. discriminate. Qed.

Lemma q63_slotcls_old s : s_slots st3 !! s <> None -> slotcls st6 s = slotcls st3 s.
Proof.
  intros Hs. destruct (s_slots st3 !! s) as [[x i]|] eqn:E; [| congruence]. unfold slotcls. rewrite (q63_slots_old _ _ E), E.
  destruct (is_valid _ _ _ IS _ _ _ E) as ([b Hb] & _). destruct (q63_old x (ex_intro _ b Hb)) as [_ MRx]. unfold cls. rewrite MRx. reflexivity.
Qed.

Lemma q63_gmetas : Permutation (gmetas st6) ((g, p) :: gmetas st3).
Proof.
  unfold gmetas, groups_l. rewrite q63_groups.
  etransitivity; [apply Permutation_flat_map; apply mtl_insert; exact (q63_nogroup_rid p eq_refl)|]. cbn. apply Permutation_refl.
Qed.

Lemma q63_gmetas_hosts x b : In (x, b) (gmetas st3) -> exists b', hosts st3 b' x.
Proof. intros H. apply gmetas_in in H as [aix Hb]. exists b, aix. exact Hb. Qed.

Lemma q63_sum (F F' : aptr * aptr -> Z) :
  (forall x b, In (x, b) (gmetas st3) -> F' (x, b) = F (x, b)) ->
  zsum (map F' (gmetas st6)) = F' (g, p) + zsum (map F (gmetas st3)).
Proof.
  intros HF. rewrite (zsum_map_perm _ _ _ q63_gmetas). cbn [map]. rewrite zsum_cons. f_equal. apply zsum_map_ext. intros [x b] Hin. apply HF. exact Hin.
Qed.

Lemma q63_gcnt c : c <> 63 -> gcnt st6 c = gcnt st3 c.
Proof.
  intros NE. rewrite !gcnt_gmetas. rewrite (q63_sum (fun mb => if m_sizeclass (MR st3 (fst mb)) =? c then cnt_of (MR st3 (fst mb)) else 0)).
  - cbn [fst]. rewrite q63_MRg. unfold mr'. cbn [m_sizeclass]. replace (63 =? c) with false by (symmetry; apply Z.eqb_neq; lia). lia.
  - intros x b Hin. cbn [fst]. destruct (q63_old x (q63_gmetas_hosts x b Hin)) as [_ E]. rewrite E. reflexivity.
Qed.

Lemma q63_stdg_g : stdg st6 g = false.
Proof.
  unfold stdg, cls. rewrite q63_MRg. cbn [m_sizeclass]. unfold mr', ml, p. rewrite (c63_stride rid needed Hn).
  pose proof (c63_ml needed Hn) as [M _]. replace (_ =? S_ 63) with false; [apply andb_false_r|].
  symmetry. apply Z.eqb_neq. unfold S_. change (size_class 63) with 0. unfold UNIT. lia.
Qed.

Lemma q63_stdg_old x : (exists b, hosts st3 b x) -> stdg st6 x = stdg st3 x.
Proof. intros Hx. destruct (q63_old x Hx) as [_ E]. unfold stdg, cls. rewrite E. reflexivity. Qed.

Lemma q63_nsc c : 0 <= c < 48 -> nsc st6 c = nsc st3 c.
Proof.
  intros Hc. unfold nsc. rewrite (q63_sum (fun mb => if (cls st3 (fst mb) =? c) && negb (stdg st3 (fst mb)) then cnt_of (MR st3 (fst mb)) else 0)).
  - cbn [fst]. unfold cls at 1. rewrite q63_MRg. unfold mr'. cbn [m_sizeclass]. replace (63 =? c) with false by (symmetry; apply Z.eqb_neq; lia). cbn. reflexivity.
  - intros x b Hin. cbn [fst]. pose proof (q63_gmetas_hosts x b Hin) as Hx. rewrite (q63_stdg_old x Hx). destruct (q63_old x Hx) as [_ E]. unfold cls. rewrite E. reflexivity.
Qed.

Lemma q63_ncarved : ncarved st6 = ncarved st3.
Proof.
  unfold ncarved. rewrite q63_metas.
  pose proof (proj1 (im_idle _ _ _ IM g ltac:(left; reflexivity))) as Hg.
  change (zlen (map_to_list (<[g:=mr']> (s_metas st3))) = zlen (map_to_list (s_metas st3))).
  unfold zlen. rewrite (Permutation_length (mtl_insert_old (s_metas st3) g mr' _ Hg)), (Permutation_length (mtl_delete (s_metas st3) g _ Hg)). reflexivity.
Qed.

Lemma q63_MIS c : MIS st6 BL c = MIS st3 BL c.
Proof.
  unfold MIS. apply zcount_ext. intros k Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). rewrite (q63_slotcls_old (bslot k)); [reflexivity| rewrite Hs; discriminate].
Qed.

Theorem c63_quant : SG st6 (k0 :: BL) /\ QM x0 st6 0 /\ AQ st6 (k0 :: BL) P /\ BLF st3 st6 BL.
Proof.
  pose proof (c63_ml needed Hn) as [M RU].
  assert (GRP' : forall b x aix, s_groups st6 !! b = Some (mkGhdr (Some x) aix) -> (x = g /\ b = p) \/ (x <> g /\ s_groups st3 !! b = Some (mkGhdr (Some x) aix) /\ MR st6 x = MR st3 x)).
  { intros b x aix Hb. rewrite q63_groups in Hb. destruct (aptr_eq_dec b p) as [->|NE].
    - rewrite lookup_insert_eq in Hb. inversion Hb. left. auto.
    - rewrite lookup_insert_ne in Hb by congruence. right. destruct (q63_old x (ex_intro _ b (ex_intro _ aix Hb))) as [NEx MRx]. auto. }
  assert (BF : BLF st3 st6 BL).
  { intros k Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). apply q63_slotcls_old. rewrite Hs. discriminate. }
  split; [| split; [| split; [| exact BF]]].
  - (* [comment removed for export] *) destruct SG3 as [S1 S2 S3 S4 S5 S6 S7]. constructor.
    + intros k [<-|Hk].
      * exists g, 0. unfold k0. cbn [bslot bsize fst snd]. rewrite q63_slots, lookup_insert_eq, q63_MRg. unfold mr'. cbn [m_sizeclass m_maplen].
        split; [reflexivity|]. split; [intros; exfalso; lia|]. intros _. split; [exact Hbig|]. unfold ml in *. rewrite RU, En. reflexivity.
      * destruct (S1 k Hk) as (x & i & Hs & C1 & C2). exists x, i. split; [exact (q63_slots_old _ _ Hs)|].
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _). destruct (q63_old x (ex_intro _ b Hb)) as [_ MRx]. rewrite MRx. auto.
    + intros c. unfold MIS. rewrite zcount_cons. fold (MIS st6 BL c). rewrite q63_MIS. unfold k0. cbn [bslot bsize fst snd].
      unfold slotcls. rewrite q63_slots, lookup_insert_eq. unfold cls. rewrite q63_MRg. unfold mr'. cbn [m_sizeclass].
      pose proof (S2 c). pose proof (size_to_class_ne62 n).
      destruct (Z.eqb_spec 63 c) as [<-|NE]; cbn [andb]; [| lia]. replace (size_to_class n =? 63 - 1) with false by (symmetry; apply Z.eqb_neq; lia). lia.
    + intros b x aix Hb Hc Hml. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite q63_MRg in Hc; unfold mr' in Hc; cbn in Hc; lia|].
      rewrite MRx in *. exact (S3 _ _ _ Hb0 Hc Hml).
    + intros b x aix Hb SD. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite q63_stdg_g in SD; discriminate|].
      rewrite (q63_stdg_old x (ex_intro _ b (ex_intro _ aix Hb0))) in SD. rewrite MRx. destruct (S4 _ _ _ Hb0 SD) as (Q1 & Q2 & Q3').
      split; [exact Q1|]. split; [| exact Q3']. intros Z0. destruct (Q2 Z0) as (g0 & i0 & Hs & Eg). exists g0, i0. split; [exact (q63_slots_old _ _ Hs)|].
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (q63_old g0 (ex_intro _ bg Hbg)) as [_ MRg0]. rewrite MRg0. exact Eg.
    + intros c Hc. rewrite (q63_nsc c Hc). exact (S5 c Hc).
    + intros b x aix Hb H63. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)].
      * left. rewrite q63_MRg. unfold k0, slot_start', mr'. cbn -[Z.add Z.mul]. unfold p. cbn [fst snd]. f_equal. rewrite (c63_stride rid needed Hn) || idtac. unfold UNIT. lia.
      * right. rewrite MRx in *. exact (S6 _ _ _ Hb0 H63).
    + intros b x aix g0 i Hb Z0 Hs'. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite q63_MRg in Z0; unfold mr' in Z0; cbn in Z0; unfold ml in Z0; lia|].
      rewrite MRx in Z0. destruct (g_nest _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb0) Z0) as (g1 & i1 & Hs & _).
      rewrite (q63_slots_old _ _ Hs) in Hs'. assert (g1 = g0 /\ i1 = i) as [-> ->] by (split; congruence).
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (q63_old g0 (ex_intro _ bg Hbg)) as [_ MRg0]. rewrite MRg0. exact (S7 _ _ _ _ _ Hb0 Z0 Hs).
  - (* [comment removed for export] *)
    assert (RG' : s_regions st6 = s_regions st3) by reflexivity.
    assert (CX' : s_ctx st6 = s_ctx st3) by reflexivity.
    assert (AP' : apages st6 = apages st3) by (apply apages_ext; [exact RG'| rewrite CX'; reflexivity]).
    destruct Q3 as [Q1 Q2 Q3' Q4 Q5 Q6]. constructor; rewrite ?RG', ?q63_ncarved, ?AP', ?CX'; auto.
    intros x mr Hx Z0. rewrite q63_metas in Hx. destruct (aptr_eq_dec x g) as [->|NE].
    + rewrite lookup_insert_eq in Hx. inversion Hx. subst mr. cbn in Z0. discriminate.
    + rewrite lookup_insert_ne in Hx by congruence. destruct (Q1 x mr Hx Z0) as [N0|I0]; [left; exact N0|]. cbn in I0. destruct I0 as [I0|[]]. congruence.
  - (* [comment removed for export] *) destruct A3 as [A1 A2 A3' A4 A5]. constructor; auto.
    + intros c Hc. unfold LR. rewrite zcount_cons. fold (LR BL c). unfold isbig, k0. cbn [bsize snd]. replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact Hbig). cbn. exact (A1 c Hc).
    + intros c Hc. rewrite (q63_gcnt c ltac:(lia)). exact (A2 c Hc).
    + unfold n63. rewrite zcount_cons. fold (n63 BL). unfold isbig, k0. cbn [bsize snd]. replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact Hbig). lia.
    + rewrite q63_ncarved. exact A4.
Qed.
End C63Q.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section COREQ.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (P : Z -> Z) (n B : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis TF : TF0 st.
Hypothesis SI : SINV x0 st BL.
Hypothesis HAQ : AQ st BL P.
Hypothesis Hn : 0 <= n.
Hypothesis HR : ROOM BL P n.
Hypothesis HB : PHI P + R63 BL + bigb n <= B + 3 * PGSZ.
Hypothesis HNR : n <= NREQ.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma small_leaf st1 L1 LS1 g bg idx sc X1 :
  INVL X1 st1 L1 BL LS1 -> x_idle X1 = [] -> hosts st1 bg g -> 0 <= idx <= m_last_idx (MR st1 g) ->
  m_sizeclass (MR st1 g) = sc -> 0 <= sc < 48 ->
  (size_to_class n = sc \/ (size_to_class n = sc - 1 /\ gcnt st sc <= 12)) ->
  SINV X1 st1 BL -> AQ st1 BL P -> BLF st st1 BL -> n < MMAP_THRESHOLD ->
  CORE_POSTQ n BL P L1 (st1, Some (g, idx)).
Proof.
  intros INV1 HX Hh Hidx SCg Hsc CLS SI1 A1 BF Hlt. unfold CORE_POSTQ. cbn [fst snd]. intros bg' off Hh'.
  pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ _ Hh' Hh) as ->.
  pose proof (is_total _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1)))))) bg g idx Hh Hidx) as T.
  rewrite (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) g bg idx Hh) in T.
  split.
  - apply (SINV_X X1 x0); [rewrite HX; reflexivity|]. apply SINV_split in SI1 as [G1 Q1]. apply SINV_split. split; [| exact Q1].
    apply (SG_add_block st1 BL _ off n g idx G1 T ltac:(lia) ltac:(lia)). rewrite SCg.
    destruct CLS as [E|[E G12]]; [left; exact E| right]. split; [exact E|].
    rewrite (BLF_MIS st st1 BL sc BF). pose proof (MIS_le_LS st BL sc). pose proof (LS_le_gcnt x0 st L BL LS INV sc). lia.
  - exact (AQ_add_block st1 BL P _ off n A1 Hn HR).
Qed.


Lemma malloc_small_fq : n < MMAP_THRESHOLD ->
  fqtree B L (malloc_small_ctrl full_lay st n (fun st1 r => ret (st1, r)) (ret (st, @None (aptr * Z)))) (CORE_POSTQ n BL P).
Proof.
  intros Hlt. pose proof (small_class x0 st L BL LS n INV ltac:(lia)) as SCF. cbn zeta in SCF.
  pose proof HB as HB0. rewrite (bigb_small n Hlt), Z.add_0_r in HB0.
  pose proof (SINV_QPOST P [] BL st x0 eq_refl SI HAQ) as QP.
  unfold malloc_small_ctrl.
  set (sc0 := size_to_class n) in *.
  set (sc := match active st sc0 with Some _ => sc0 | None => _ end) in *.
  clearbody sc. destruct SCF as (SC' & FIT' & CLS).
  assert (SLOT : fqtree B L (alloc_slot full_lay FUEL st sc n (fun st1 idx =>
             if idx <? 0 then ret (st1, None)
             else match active st1 sc with
                  | Some gp => ret (st1, Some (gp, idx))
                  | None => SVis (EUndef UBadPtr) (fun _ => ret (st, @None (aptr * Z)))
                  end) (ret (st, None))) (CORE_POSTQ n BL P)).
  { apply (alloc_slot_fq (mstate * option (aptr * Z)) P B (CORE_POSTQ n BL P) FUEL sc [] st L BL LS n); try assumption.
    - unfold FUEL. cbn. lia.
    - apply NoDup_nil_2.
    - pose proof (rank_range sc). unfold zlen. cbn. lia.
    - intros st1 idx L1 LS1 (ACT & LIVE & GP1 & RES) QP1 GC1 BF1.
      destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1)].
      + change (-1 <? 0) with true. cbn iota. apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd].
        exact (QPOST_SINV P [] BL st1 x0 eq_refl QP1).
      + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. apply fqtree_ret.
        destruct (QPOST_SINV P [] BL st1 (xpend (X_as []) (Some (fst bg, sstart (MR st1 g) idx))) eq_refl QP1) as [SI1 A1].
        apply (small_leaf st1 L1 LS1 g bg idx sc _ INV1 eq_refl (ex_intro _ ai Hg) Hidx SCg SC' CLS SI1 A1 BF1 Hlt). }
  destruct (active st sc) as [gp|] eqn:HA; [| exact SLOT].
  destruct (Z.eqb_spec (m_avail (get_meta_rec st gp)) 0) as [AZ|ANZ].
  { rewrite AZ. change (lowbit 0) with 0. cbn [negb Z.eqb]. exact SLOT. }
  (* [comment removed for export] *)
  destruct (hd_facts x0 st L BL LS sc gp INV HA) as (_ & Esc & bm & ai & Hbm).
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbm) as GO.
  pose proof (proj1 (g_masks _ _ _ _ _ _ GO)) as A0. fold (MR st gp) in ANZ |- *.
  destruct (lowbit_idiom (m_avail (MR st gp)) ltac:(lia)) as (k & Hk & LB & CTZ & TB & _).
  assert (LNZ : (lowbit (m_avail (MR st gp)) =? 0) = false) by (apply Z.eqb_neq; rewrite LB; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); lia).
  rewrite LNZ. cbn [negb]. apply fqtree_ret.
  pose proof (ta_fin_ok x0 st L BL LS gp bm ai INV eq_refl eq_refl Hbm ltac:(rewrite Esc; exact (hd_head x0 st L BL LS sc gp INV HA)) ANZ) as (INV1 & Hidx & _ & _ & STR).
  set (st1 := upd_meta gp (m_set_avail (m_avail (MR st gp) - lowbit (m_avail (MR st gp)))) st) in *.
  assert (MRg : m_last_idx (MR st1 gp) = m_last_idx (MR st gp) /\ m_sizeclass (MR st1 gp) = m_sizeclass (MR st gp)).
  { unfold st1, MR. rewrite get_meta_rec_upd_same. destruct (get_meta_rec st gp); cbn; split; reflexivity. }
  destruct MRg as [ML MSC].
  assert (F01 : FFR st st1).
  { unfold st1. apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ GO)| intros r; destruct r; reflexivity| intros r Hr; destruct r; exact Hr]. }
  destruct (SINVx_xfer x0 (xpend x0 (Some (fst bm, sstart (MR st gp) (ctz32 (lowbit (m_avail (MR st gp))))))) st st1 L L BL LS LS P None INV INV1 eq_refl F01 HAQ (SINV_SINVx _ _ _ SI) ltac:(intros; discriminate)) as (SI1 & A1 & _).
  apply (small_leaf st1 L LS gp bm _ sc _ INV1 eq_refl); try assumption.
  - apply (proj2 (hosts_ext st st1 eq_refl bm gp)). exists ai. exact Hbm.
  - rewrite ML. exact Hidx.
  - rewrite MSC. exact Esc.
  - exact (BLF_ffr _ st st1 L BL LS INV1 F01).
Qed.

(* [comment removed for export] *)
Lemma malloc_big_fq : MMAP_THRESHOLD <= n -> size_overflows n = false ->
  fqtree B L
    (SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (s_atop st) (live_ranges st) (n + IB + UNIT) r) then bad_answer (ret (st, @None (aptr * Z))) else
      if is_err r then ret (st, None) else
      let '(st1, rid) := new_region RKGroup r (n + IB + UNIT) st in
      let st2 := step_seq st1 in
      alloc_meta st2 (fun st3 go =>
        match go with
        | None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st, @None (aptr * Z))))
        | Some g =>
          let st4 := upd_meta g (fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((n + IB + UNIT + 4095) / 4096)
                       (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
          let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr full_lay st4 (rid, 0)) in
          let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
          let st7 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6 in
          ret (st7, Some (g, 0))
        end) (ret (st, @None (aptr * Z)))))
    (CORE_POSTQ n BL P).
Proof.
  intros Hbig Hov. unfold size_overflows in Hov. apply Z.leb_gt in Hov.
  set (needed := n + IB + UNIT).
  assert (HN : 131072 <= needed < 2 ^ 63 - 4000) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
  pose proof HB as HB0. rewrite (bigb_big n Hbig) in HB0. fold needed in HB0.
  pose proof (round_up_pg_spec needed) as [[RU1 RU2] _].
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (SINV_QPOST P [] BL st x0 eq_refl SI HAQ) as QP. destruct QP as (SGst & Qst & Ast).
  (* [comment removed for export] *)
  assert (HQB : QB L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) B).
  { intros _. split.
    - rewrite mmap_len_rup. unfold RMAX. unfold NREQ in HNR. unfold needed, IB, UNIT in RU2 |- *. lia.
    - pose proof (aq_pq _ _ _ HAQ) as [PQ1 PQ2].
      pose proof (ledger_count x0 st L BL LS P INV SI HAQ eq_refl ltac:(lia)) as LC.
      unfold NMAX. unfold zlen in LC. lia. }
  apply fqtree_vis; [reflexivity| reflexivity| | exact HQB| | |].
  - cbn. left. split; [exact (brk_quiet_of _ _ _ IR)|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity|].
    unfold LEN_MAX. clear -HN. lia.
  - (* [comment removed for export] *)
    intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha.
    change (event_post L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L) L else KInv.set_groups ((a, needed) :: ld_groups L) L else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    pose proof (state_bytes_B x0 st L BL LS P (B - round_up_pg needed) INV eq_refl eq_refl SI HAQ ltac:(lia)) as SB.
    destruct (is_err a); [lia|]. rewrite gm_add_group, BB_set_groups, mmap_len_rup. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    change (event_post L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L) L else KInv.set_groups ((a, needed) :: ld_groups L) L else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    + apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd]. split; [exact SI| exact HAQ].
    + destruct (new_region RKGroup a needed st) as [st1 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st) by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est1 : st1 = fst (new_region RKGroup a needed st)) by (rewrite EN; reflexivity).
      pose proof (INVL_new_group_region x0 st L BL LS a needed INV eq_refl Ha ER ltac:(unfold LEN_MAX; clear -HN; lia)) as INV1.
      rewrite <- Est1, <- Erid in INV1.
      set (L1 := KInv.set_groups ((a, needed) :: ld_groups L) L) in *.
      assert (Hr1 : s_regions st1 !! rid = Some (mkRegion RKGroup a needed)) by (rewrite Est1, ng_lookup, Erid, N.eqb_refl; reflexivity).
      assert (FR : s_regions st !! rid = None) by (rewrite Erid; exact (nm_fresh _ _ _ _ _ INV)).
      assert (NS1 : s_shadow st1 !! rid = None).
      { rewrite Est1, Erid. change (s_shadow (fst (new_region RKGroup a needed st))) with (s_shadow st). exact (shadow_next_rid_none _ _ _ _ _ INV). }
      assert (TF1 : TF0 (step_seq st1)).
      { destruct (step_seq_fields st1) as (A' & B' & _). apply (TF0_ctrl st1); [exact A'| exact B'|]. apply (TF0_ctrl st); [rewrite Est1; reflexivity| rewrite Est1; reflexivity| exact TF]. }
      pose proof (INVL_step_seq _ _ _ _ _ INV1) as INV2.
      destruct (step_seq_fields st1) as (SS1 & SS2 & SS3 & SS4 & SS5 & _).
      (* [comment removed for export] *)
      pose proof (QPOST_new_group_region P [] BL st x0 L LS a needed INV (conj SGst (conj Qst Ast))) as QP1. rewrite <- Est1 in QP1.
      pose proof (QPOST_qsame P [] BL st1 (step_seq st1) _ L1 LS INV1 (qsame_step_seq st1) QP1) as (SG2 & Q2 & A2).
      set (st2 := step_seq st1) in *.
      assert (GB2 : group_bytes st2 = group_bytes st + round_up_pg needed).
      { rewrite (group_bytes_ext st1 st2 SS4). rewrite !group_bytes_msum, Est1. unfold new_region. cbn [fst s_regions set_next_rid set_regions].
        rewrite <- Erid. rewrite (msum_regions_insert_fresh gbF st rid _ FR). unfold gbF at 1. cbn. lia. }
      pose proof (proj2 (SINV_split (xorph x0 (Some rid)) st2 BL) (conj SG2 (QM_X (X_as []) (xorph x0 (Some rid)) st2 0 eq_refl Q2))) as SI2.
      pose proof (ledger_count (xorph x0 (Some rid)) st2 L1 BL LS P INV2 SI2 A2 eq_refl ltac:(pose proof (aq_pq _ _ _ A2) as [PQ1 _]; lia)) as LC2.
      pose proof (aq_pq _ _ _ A2) as [_ PQ2'].
      eapply (alloc_meta_fq (mstate * option (aptr * Z)) BL P B (CORE_POSTQ n BL P) _ _ (xorph x0 (Some rid)) st2 L1 LS INV2 SG2 A2);
        [ | | lia| | | exact INV2| apply amf_refl| apply lf_refl| | reflexivity| reflexivity].
      * (* [comment removed for export] *)
        intros HFH. pose proof (ncarved_le_groups (xorph x0 (Some rid)) st2 L1 BL LS INV2 0 (QM_X (X_as []) (xorph x0 (Some rid)) st2 0 eq_refl Q2) HFH eq_refl) as NC.
        pose proof (ngroups_le (xorph x0 (Some rid)) st2 L1 BL LS P INV2 SG2 A2) as NG0. cbn [x_idle xorph x0] in NC. unfold zlen in NC. cbn [length] in NC. change (Z.of_nat 0) with 0 in NC. unfold NCAP. lia.
      * (* [comment removed for export] *)
        rewrite GB2. pose proof (group_bytes_B x0 st L BL LS P (B - round_up_pg needed) INV eq_refl eq_refl SI HAQ ltac:(lia)). lia.
      * (* [comment removed for export] *)
        intros st3 L3 LS3 INV3 AF LF SI3 A3' GC3 GEO3. cbn beta iota.
        assert (Hr3 : s_regions st3 !! rid = Some (mkRegion RKGroup a needed)) by (apply (amf_regions _ _ AF); [rewrite SS4; exact Hr1| reflexivity]).
        pose proof (proj1 INV3) as IR3.
        assert (GPOS : forall g, In g (ld_groups L3) -> 0 <= snd g).
        { intros g Hg. apply (Permutation_in _ (ir_groups _ _ _ IR3)) in Hg. apply in_map_iff in Hg as ([q rq] & <- & Hin). cbn.
          apply filter_In in Hin as [Hin _]. apply mtl_in in Hin. pose proof (ir_shape _ _ _ IR3 _ _ Hin) as (_ & _ & L0 & _). lia. }
        apply fqtree_vis; [reflexivity| reflexivity| | exact I| | |].
        -- cbn. split; [exact (brk_quiet_of _ _ _ IR3)|]. exists needed. rewrite (lf_groups _ _ LF). split; [left; reflexivity| left; reflexivity].
        -- intros z Hz. etransitivity; [apply lbytes_event_post_munmap; exact GPOS|].
           pose proof (ledger_bound _ st3 L3 BL LS3 INV3) as LB3. pose proof (regions_bound _ st3 L3 BL LS3 P INV3 SI3 A3' eq_refl) as RB3.
           unfold ORPH in RB3. cbn [x_orph xorph x0] in RB3. rewrite Hr3 in RB3. cbn [r_len] in RB3. lia.
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd].
           destruct (SINV_drop_orph _ st3 L3 BL LS3 P rid _ INV3 Hr3 eq_refl SI3 A3') as [S'' A'']. split; [exact (SINV_X (xorph x0 (Some rid)) x0 _ _ eq_refl S'')| exact A''].
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. exact I.
      * (* [comment removed for export] *)
        intros st3 L3 LS3 g INV3 NIg AF LF SI3 A3' NC3 GC3 GEO3. cbn beta iota zeta.
        change (lh_hdr full_lay) with (fun s b => hdr_havoc b s). cbn beta.
        assert (Hr3 : s_regions st3 !! rid = Some (mkRegion RKGroup a needed)) by (apply (amf_regions _ _ AF); [rewrite SS4; exact Hr1| reflexivity]).
        assert (NS3 : s_shadow st3 !! rid = None) by (rewrite (amf_shadow _ _ AF), SS1; exact NS1).
        assert (TF3 : TF0 st3) by (apply (TF0_ctrl st2); [exact (amf_shadow _ _ AF)| exact (amf_tick _ _ AF)| exact TF1]).
        cbn [xidle xorph x_idle x_zomb x_pend x_orph x_fresh x0] in INV3, SI3.
        destruct (create63_ok st3 L3 BL LS3 g rid (mkRegion RKGroup a needed) needed INV3 Hr3 eq_refl eq_refl NS3 ltac:(lia) TF3)
          as (INV6 & TF6 & MR6 & GR6 & CTX6 & TK6 & RG6 & STR6 & RU6).
        match goal with |- fqtree _ _ (ret (upd_ctx ?f ?s6, _)) _ => set (st6 := s6) in * end.
        apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd]. intros bg off Hh.
        pose proof (INVL_mmap_counter _ _ _ _ _ INV6) as INV7.
        set (st7 := upd_ctx _ st6) in *.
        assert (Hh6 : hosts st6 bg g) by exact Hh.
        pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV6))) _ _ _ Hh6 (ex_intro _ 0 GR6)) as ->.
        assert (MR7 : MR st7 g = MR st6 g) by reflexivity. rewrite MR7, MR6.
        replace (sstart (mkMeta None None (Some (rid, 0)) 0 0 0 1 63 ((needed + 4095) / 4096)) 0) with 16 by (unfold sstart, gbase; cbn -[Z.mul Z.add get_stride]; unfold UNIT; lia).
        change (fst (rid, 0)) with rid.
        apply SINV_split in SI3 as [SG3 Q3].
        destruct (c63_quant st3 L3 BL LS3 P g rid needed n off INV3 ltac:(lia) eq_refl Hbig SG3 Q3 A3' ltac:(exact (proj2 HR Hbig)))
          as (SG6 & Q6 & A6 & _).
        fold st6 in SG6, Q6, A6.
        assert (SV6 : forall s x i, s_slots st6 !! s = Some (x, i) -> exists b, hosts st6 b x).
        { intros s x i Hs. exact (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV6)))))) _ _ _ Hs)). }
        split.
        -- apply SINV_split. split.
           ++ apply (SG_frame st6 st7 _ eq_refl eq_refl ltac:(intros; reflexivity) SV6 SG6).
           ++ destruct Q6 as [Q1' Q2' Q3' Q4' Q5' Q6']. constructor; auto.
        -- apply (AQ_frame st6 st7 _ P eq_refl ltac:(intros; reflexivity)); [| exact A6]. exact (aq_carved _ _ _ A6).
      * (* [comment removed for export] *)
        split; [exact (QM_X (X_as []) (xorph x0 (Some rid)) st2 0 eq_refl Q2)|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. exact I.
Qed.

Theorem malloc_core_fq : fqtree B L (malloc_core full_lay st n) (CORE_POSTQ n BL P).
Proof.
  unfold malloc_core.
  destruct (size_overflows n) eqn:Hov.
  - apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd]. split; [exact SI| exact HAQ].
  - destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hbig|Hsmall].
    + exact (malloc_big_fq Hbig Hov).
    + exact (malloc_small_fq Hsmall).
Qed.
End COREQ.

Theorem malloc_core_fq_proof : malloc_core_fq_stmt.
Proof. intros st L BL LS P n B INV TF SI HAQ Hn HNR HR HB. exact (malloc_core_fq st L BL LS P n B INV TF SI HAQ Hn HR HB HNR). Qed.

Check (malloc_core_fq_proof : malloc_core_fq_stmt).
