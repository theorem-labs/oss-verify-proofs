(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk HeapIface HeapIfaceA HeapIfaceABx As0Tables ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatRzLog_b BatPoison_b BatAllocA_b BatAllocG_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b
     BatClsRep_b BatClsGfa2_b BatClsRefill_b BatCARSpec_b BatAlloc3Pure_b BatByteCell_b BatCellEx_b BatDepotA_b BatDepot_b BatAllocate3_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvMallocPure_b BatInvMalloc_b BatFxQ_b BatInvFreePure_b BatInvFree_b BatInvRepX_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx ShadowRLawsB.      (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Lemma art_batch_list_append : forall M M' bs f l t0 ts tl,
  bs <> [] -> NoDup (map bt_addr bs) -> art_batch_list M bs f l ->
  (forall b0, In b0 bs -> 0 <= bt_addr b0 /\ bt_addr b0 + 8192 < 2 ^ 64) ->
  (forall b0 (x : word), In b0 bs -> bt_addr b0 <= U x < bt_addr b0 + 8192 -> ~ (bt_addr b0 = l /\ U x < l + 8) -> M' x = M x) ->
  cellA M' l 8 (bt_addr t0) -> art_batch_list M' (t0 :: ts) (bt_addr t0) tl ->
  art_batch_list M' (bs ++ t0 :: ts) f tl.
Proof.
  intros M M' bs. induction bs as [|x r IH]; intros f l t0 ts tl NE ND BL RNG EQ CL BN; [contradiction|].
  cbn [art_batch_list] in BL. destruct BL as (Ef & Hl & C1 & C2 & CI & LK & R).
  destruct (RNG x (or_introl eq_refl)) as (R0 & R1).
  assert (TX : forall a (j : nat) v, bt_addr x + 8 <= a -> a + Z.of_nat j <= bt_addr x + 8192 -> cellA M a j v -> cellA M' a j v).
  { intros a j v Ha Hj C. apply (art_cell_agree _ M M'); [|lia|lia|exact C]. intros y Hy. apply (EQ x y (or_introl eq_refl)); [lia|]. intros (E & Y). lia. }
  assert (TI : forall j it, nth_error (bt_items x) j = Some it -> cellA M' (bt_addr x + 24 + 8 * Z.of_nat j) 8 (fst it)).
  { intros j it Hj. pose proof (art_nth_error_lt _ _ _ _ Hj) as Hlt. apply TX; [lia|cbn; lia|exact (CI j it Hj)]. }
  destruct r as [|y r'].
  - destruct LK as (El & C0). cbn [app]. cbn [art_batch_list]. cbn [art_batch_list] in BN. split; [exact Ef|]. split; [exact Hl|]. split; [apply TX; [lia|cbn; lia|exact C1]|].
    split; [apply TX; [lia|cbn; lia|exact C2]|]. split; [exact TI|]. split; [rewrite <- El; exact CL|]. exact BN.
  - assert (El : l = bt_addr (art_lastb (y :: r'))) by (apply (art_batch_list_last M (y :: r') (bt_addr y) l); [discriminate|exact R]).
    assert (Nx : bt_addr x <> l).
    { rewrite El. intros E. cbn [map] in ND. inversion ND as [|a0 l0 Hni HND]; subst a0 l0. apply Hni. apply list_elem_of_In. rewrite E. change (bt_addr y :: map bt_addr r') with (map bt_addr (y :: r')). apply in_map. unfold art_lastb. apply BatFxQ_b.art_last_in. discriminate. }
    change ((x :: y :: r') ++ t0 :: ts) with (x :: y :: (r' ++ t0 :: ts)). cbn [art_batch_list]. split; [exact Ef|]. split; [exact Hl|]. split; [apply TX; [lia|cbn; lia|exact C1]|].
    split; [apply TX; [lia|cbn; lia|exact C2]|]. split; [exact TI|].
    split. { apply (art_cell_agree _ M M'); [|lia|cbn; lia|exact LK]. intros z Hz. apply (EQ x z (or_introl eq_refl)); [cbn in Hz; lia|]. intros (E & _). exact (Nx E). }
    change (y :: (r' ++ t0 :: ts)) with ((y :: r') ++ t0 :: ts). apply (IH (bt_addr y) l t0 ts tl); [discriminate| | exact R | | | exact CL | exact BN].
    + cbn [map] in ND. inversion ND as [|a0 l0 Hni HND]; subst a0 l0. exact HND.
    + intros b0 Hb0. apply RNG. right. exact Hb0.
    + intros b0 z Hb0. apply EQ. right. exact Hb0.
Qed.

Lemma art_in_batches_perm : forall (a b c d : list art_batch) h m, (forall x, In x (a ++ b) -> In x (c ++ d)) -> art_in_batches (a ++ b) h m -> art_in_batches (c ++ d) h m.
Proof. intros a b c d h m INC (x & Hx & Hi). exists x. split; [apply INC; exact Hx|exact Hi]. Qed.

Lemma art_nodup_map_app_d : forall (A : Type) (f : A -> Z) (l1 l2 : list A) a1 a2, List.NoDup (map f (l1 ++ l2)) -> In a1 l1 -> In a2 l2 -> f a1 <> f a2.
Proof.
  intros A f l1 l2 a1 a2. induction l1 as [|y r IH]; intros ND H1 H2; [contradiction|]. cbn [app map] in ND. apply NoDup_cons_iff in ND. destruct ND as (Hy & ND').
  destruct H1 as [->|H1]; [|exact (IH ND' H1 H2)]. intros E. apply Hy. rewrite E. apply in_map. apply in_or_app. right. exact H2.
Qed.

Section Drain.
Variable FSG : Type.
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M M' : word -> option byte) (bound sp ft lt fg lg : Z).
Let qtl := g_qt FSG G.
Let qgl := g_qg FSG G.
Let L := Z.of_nat (length qtl).
Let GL := Z.of_nat (length qgl).
Let Gd := art_gs_drain G.
Definition art_drain_W : list (Z * Z) :=
  [ (sp - 48, 48); (0x13c8b0 + 152, 16); (0x13c8b0 + 176, 16); (rn_t rn + 80, 32); ((if GL =? 0 then 0x13c8b0 + 168 else lg), 8) ].

Hypothesis REPB : art_alloc_rep_b FSG bound rn G LB M.
Hypothesis NEq : qtl <> [].
Hypothesis Tf : cellA M (rn_t rn + 88) 8 ft.
Hypothesis BLt : art_batch_list M qtl ft lt.
Hypothesis Gf : cellA M (0x13c8b0 + 168) 8 fg.
Hypothesis BLg : art_batch_list M qgl fg lg.
Hypothesis HSP : rn_HI rn <= sp - 48.
Hypothesis HSP' : sp <= 2 ^ 47.
Hypothesis NR : art_batches_bytes qgl + art_batches_bytes qtl <= 2 ^ 28.
Hypothesis GRW : mem_grows M M'.
Hypothesis AGR : art_agree art_drain_W M M'.
Hypothesis POST : cellA M' (rn_t rn + 80) 8 0 /\ cellA M' (rn_t rn + 80 + 8) 8 0 /\ cellA M' (rn_t rn + 80 + 16) 8 0 /\ cellA M' (rn_t rn + 80 + 24) 8 0
    /\ cellA M' (0x13c8b0 + 160) 8 (GL + L) /\ cellA M' (0x13c8b0 + 176) 8 lt /\ cellA M' (0x13c8b0 + 184) 8 (art_batches_bytes qgl + art_batches_bytes qtl) /\ cellA M' (0x13c8b0 + 152) 4 0
    /\ (GL = 0 -> cellA M' (0x13c8b0 + 168) 8 ft) /\ (GL <> 0 -> cellA M' lg 8 ft).
Hypothesis LIVE : forall p, In p (art_live (g_log FSG G)) ->
  0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
  /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o)).

(* [comment removed for export] *)
#[using="LB M bound fg REPB BLg"] Lemma art_drn_lg : GL <> 0 -> exists wG, lg = rn_spb rn + 24 * 2 ^ 32 + 16 * wG /\ art_cptr_ok 8192 (cl_au (g_cls FSG G 24)) wG /\ g_st FSG G 24 wG = CBatch.
Proof.
  intros NG. destruct REPB as (_ & _ & _ & _ & _ & _ & QR & _). destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH).
  assert (NEg : qgl <> []) by (intros E; apply NG; unfold GL; rewrite E; reflexivity).
  pose proof (art_batch_list_last M qgl fg lg NEg BLg) as El.
  destruct (BCH (art_lastb qgl)) as (wG & E & V & St). { apply in_or_app. right. unfold art_lastb. apply BatFxQ_b.art_last_in. exact NEg. }
  exists wG. rewrite art_class_size_24 in V. rewrite El. split; [exact E|]. split; [exact V|exact St].
Qed.

(* [comment removed for export] *)
#[using="LB M bound fg qtl L REPB BLg"] Lemma art_drn_num : 0x10007fff8000 <= rn_HI rn /\ (GL <> 0 -> rn_spb rn + 24 * 2 ^ 32 <= lg /\ lg + 8192 <= rn_spb rn + 24 * 2 ^ 32 + cl_mu (g_cls FSG G 24) /\ cl_mu (g_cls FSG G 24) <= 3758096384).
Proof.
  pose proof REPB as (ROK & _ & _ & (_ & PRIM & _) & _). rok_open14 ROK. geo_open GEO. split; [clear - G1; lia|]. intros NG. destruct (art_drn_lg NG) as (wG & E & (V0 & V1 & _) & _).
  destruct (PRIM 24 ltac:(lia)) as (_ & OK & _). destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _). rewrite E. clear - V0 V1 Haumu Hmu3. lia.
Qed.

#[using="LB M bound fg qtl L REPB BLg HSP"] Lemma art_dgap_img : forall a len, 0x10000 <= a -> a + len <= 0x696000 -> (a + len <= 0x13c948 \/ 0x13c970 <= a) -> art_gap art_drain_W a len.
Proof.
  intros a len Ha Hl Hq. destruct art_drn_num as (HHI & HLG). pose proof REPB as (ROK & _). rok_open14 ROK. geo_open GEO.
  unfold art_drain_W. cbn [art_gap fst snd]. unfold apart. destruct (Z.eqb_spec GL 0) as [E|NG]; [|destruct (HLG NG) as (X1 & X2 & X3)]; clear - Ha Hl Hq HSP HHI G4 G9 X1 || clear - Ha Hl Hq HSP HHI G4 G9; repeat split; try exact I; lia.
Qed.
#[using="LB M bound fg qtl L REPB BLg HSP"] Lemma art_dgap_thread : forall a len, rn_t rn <= a -> a + len <= rn_t rn + 4096 -> (a + len <= rn_t rn + 80 \/ rn_t rn + 112 <= a) -> art_gap art_drain_W a len.
Proof.
  intros a len Ha Hl Hq. destruct art_drn_num as (HHI & HLG). pose proof REPB as (ROK & _). rok_open14 ROK. geo_open GEO. unfold apart in G11.
  unfold art_drain_W. cbn [art_gap fst snd]. unfold apart. destruct (Z.eqb_spec GL 0) as [E|NG]; [|destruct (HLG NG) as (X1 & X2 & X3)]; clear - Ha Hl Hq HSP HHI G4 G8 G9 G11 X1 X2 X3 || clear - Ha Hl Hq HSP HHI G4 G8 G9 G11; repeat split; try exact I; lia.
Qed.
(* [comment removed for export] *)
#[using="LB M bound fg qtl L REPB BLg HSP"] Lemma art_dgap_far : forall a len, 0 <= a -> a + len <= rn_HI rn -> (a + len <= 0x10000 \/ 0x696000 <= a) -> apart a len (rn_t rn) 4096 ->
  (a + len <= rn_spb rn + 24 * 2 ^ 32 \/ rn_spb rn + 24 * 2 ^ 32 + 3758096384 <= a) -> art_gap art_drain_W a len.
Proof.
  intros a len Ha Hl Hi At Hk. destruct art_drn_num as (HHI & HLG). pose proof REPB as (ROK & _). rok_open14 ROK. geo_open GEO. unfold apart in At.
  unfold art_drain_W. cbn [art_gap fst snd]. unfold apart. destruct (Z.eqb_spec GL 0) as [E|NG]; [|destruct (HLG NG) as (X1 & X2 & X3)]; clear - Ha Hl Hi At Hk HSP HHI X1 X2 X3 || clear - Ha Hl Hi At Hk HSP HHI; repeat split; try exact I; lia.
Qed.

#[using="FSG rn G LB bound sp fg lg qtl qgl L GL REPB BLg HSP AGR"] Lemma art_drn_cell_img : forall a (j : nat) v, 0x10000 <= a -> a + Z.of_nat j <= 0x696000 -> (a + Z.of_nat j <= 0x13c948 \/ 0x13c970 <= a) -> cellA M a j v -> cellA M' a j v.
Proof. intros a j v Ha Hl Hq C. apply (art_cell_tr art_drain_W M M' a j v AGR (art_dgap_img a _ Ha Hl Hq)); [lia|lia|exact C]. Qed.

(* [comment removed for export] *)
#[using="FSG rn G LB bound sp fg lg qtl qgl L GL REPB BLg HSP AGR"] Lemma art_drn_shadow : forall a, 0x7fff8000 <= a < 0x10007fff8000 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros a Ha. destruct art_drn_num as (HHI & HLG). pose proof REPB as (ROK & _). rok_open14 ROK. geo_open GEO. unfold apart in G10.
  apply AGR. rewrite art_u_lit by lia. unfold art_drain_W. cbn [art_out fst snd].
  destruct (Z.eqb_spec GL 0) as [E|NG]; [|destruct (HLG NG) as (X1 & X2 & X3)]; clear - Ha HSP HHI G4 G10 X1 || clear - Ha HSP HHI G4 G10; repeat split; try exact I; lia.
Qed.

(* [comment removed for export] *)
#[using="LB bound sp fg lg qtl qgl L GL REPB BLg HSP AGR"] Lemma art_drn_chunk : forall c0 w0 a, 1 <= c0 <= 30 -> art_cptr_ok (AsanTab.class_size c0) (cl_au (g_cls FSG G c0)) w0 -> g_st FSG G c0 w0 <> CBatch ->
  rn_spb rn + c0 * 2 ^ 32 + 16 * w0 <= a < rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + AsanTab.class_size c0 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros c0 w0 a Hc0 V NS Ha. destruct art_drn_num as (HHI & HLG). pose proof REPB as (ROK & _ & _ & (_ & PRIM & _) & _). rok_open14 ROK. geo_open GEO. unfold apart in G11.
  destruct (PRIM c0 Hc0) as (_ & OK0 & _). destruct OK0 as (_ & (_ & Haumu0) & _ & _ & _ & Hmu30 & _). pose proof (art_class_size_facts c0 Hc0) as (Hsz0 & _). pose proof V as (V0 & V1 & _).
  apply AGR. rewrite art_u_lit by (clear - Ha Hc0 V0 V1 Haumu0 Hmu30 G4 G6 G2 Eris; lia). unfold art_drain_W. cbn [art_out fst snd].
  destruct (Z.eqb_spec GL 0) as [E|NG].
  - clear - Ha Hc0 V0 V1 Haumu0 Hmu30 HSP HHI G4 G6 G8 G11 Espb Eris. repeat split; try exact I; lia.
  - destruct (art_drn_lg NG) as (wG & ElG & VG & StG).
    assert (APG : c0 = 24 -> 16 * wG + 8192 <= 16 * w0 \/ 16 * w0 + 8192 <= 16 * wG).
    { intros ->. rewrite art_class_size_24 in V. apply (art_cptr_apart 8192 (cl_au (g_cls FSG G 24)) w0 wG ltac:(clear; lia) V VG). intros ->. exact (NS StG). }
    destruct VG as (VG0 & VG1 & _). destruct (PRIM 24 ltac:(lia)) as (_ & OK24 & _). destruct OK24 as (_ & (_ & Haumu24) & _ & _ & _ & Hmu324 & _).
    destruct (Z.eq_dec c0 24) as [E24|N24].
    + specialize (APG E24). subst c0. rewrite art_class_size_24 in Ha, V1. rewrite ElG. clear - Ha APG V0 HSP HHI G4 G6 G8 G11 Espb Eris Hmu30 Haumu0 V1. repeat split; try exact I; lia.
    + rewrite ElG. clear - Ha N24 Hc0 V0 V1 Haumu0 Hmu30 VG0 VG1 Haumu24 Hmu324 HSP HHI G4 G6 G8 G11 Espb Eris Hsz0. repeat split; try exact I; lia.
Qed.

(* [comment removed for export] *)
#[using="rn LB bound sp fg L REPB BLg HSP AGR"] Lemma art_drn_batch : forall b0 (x : word), In b0 (qtl ++ qgl) -> bt_addr b0 <= U x < bt_addr b0 + 8192 -> ~ (GL <> 0 /\ bt_addr b0 = lg /\ U x < lg + 8) -> M' x = M x.
Proof.
  intros b0 x Hb0 Hx NX. destruct art_drn_num as (HHI & HLG). pose proof REPB as (ROK & _ & _ & (_ & PRIM & _) & _ & _ & QR & _). rok_open14 ROK. geo_open GEO. unfold apart in G11.
  destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH). destruct (BCH b0 Hb0) as (w0 & E0 & V & St0). rewrite art_class_size_24 in V. pose proof V as (V0 & V1 & _).
  destruct (PRIM 24 ltac:(lia)) as (_ & OK24 & _). destruct OK24 as (_ & (_ & Haumu24) & _ & _ & _ & Hmu324 & _).
  apply AGR. unfold art_drain_W. cbn [art_out fst snd]. rewrite E0 in Hx.
  destruct (Z.eqb_spec GL 0) as [E|NG].
  - clear - Hx V0 V1 Haumu24 Hmu324 HSP HHI G4 G6 G8 G11 Espb Eris. repeat split; try exact I; lia.
  - destruct (art_drn_lg NG) as (wG & ElG & VG & StG).
    destruct (Z.eq_dec w0 wG) as [->|Nw].
    + assert (Y : ~ U x < lg + 8) by (intros Y; apply NX; repeat split; [exact NG|rewrite E0, ElG; reflexivity|exact Y]). rewrite ElG in Y |- *.
      clear - Hx Y V0 V1 Haumu24 Hmu324 HSP HHI G4 G6 G8 G11 Espb Eris. repeat split; try exact I; lia.
    + pose proof (art_cptr_apart 8192 (cl_au (g_cls FSG G 24)) w0 wG ltac:(clear; lia) V VG Nw) as AP. rewrite ElG.
      clear - Hx AP V0 V1 Haumu24 Hmu324 HSP HHI G4 G6 G8 G11 Espb Eris. repeat split; try exact I; lia.
Qed.

(* [comment removed for export] *)
#[using="FSG G LB M bound sp fg lg qtl qgl L GL REPB BLg HSP AGR"] Lemma art_drn_statics : art_rt_statics rn M'.
Proof.
  pose proof REPB as (ROK & ST & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct ST as (PC & LY & T & RO & RZ & DR & TG & CS).
  unfold art_rt_statics.
  split. { destruct PC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9). unfold art_prim_consts. repeat split; (apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|assumption]). }
  split. { destruct LY as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15). unfold art_layout. unfold SB, kHighMemEnd in *.
           repeat split; (apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|assumption]). }
  split. { apply (art_tsd_tr _ M M' _ _ _ _ _ AGR); [apply art_dgap_img; lia|apply art_dgap_img; lia|apply art_dgap_img; lia| |exact T].
           apply art_dgap_far; [clear - G13; lia|clear - G14; lia|clear - G15; lia|unfold apart in G18 |- *; clear - G18; lia|unfold apart in G17; clear - G17; lia]. }
  split. { unfold art_alloc_rodata in *. destruct RO as (a1 & a2 & a3). repeat split; (apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|assumption]). }
  split. { unfold art_rz_rodata in *. destruct RZ as (a1 & a2 & a3). repeat split; (apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|assumption]). }
  split. { destruct DR as (a1 & a2 & a3). unfold DRoD. repeat split; (apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|assumption]). }
  split. { destruct TG as (GN & T1 & T2). split; [|split].
           - intros a Ha. rewrite (AGR (Z_to_bv 64 a)); [exact (GN a Ha)|]. rewrite art_u_lit by lia. apply (art_gap_out _ a 1); [apply art_dgap_img; lia|lia].
           - apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|exact T1].
           - apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|exact T2]. }
  decompose [and] CS. repeat split; (apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|assumption]).
Qed.

#[using="LB M bound fg qtl L REPB BLg HSP LIVE"] Lemma art_dgap_grant : forall p a len, In p (art_live (g_log FSG G)) -> fst p <= a -> a + len <= fst p + snd p -> art_gap art_drain_W a len.
Proof.
  intros p a len Hp Ha Hl. destruct (LIVE p Hp) as (P0 & P1 & P2 & P3 & PO).
  pose proof (PO _ (or_introl eq_refl)) as At. pose proof (PO _ (or_intror (or_intror (or_introl eq_refl)))) as Ak.
  pose proof (PO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))) as Ai1.
  pose proof (PO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))) as Ai2.
  pose proof (PO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))))) as Ai3.
  pose proof (PO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))))) as Ai4.
  cbn [fst snd] in At, Ak, Ai1, Ai2, Ai3, Ai4. pose proof REPB as (ROK & _). rok_open14 ROK. geo_open GEO.
  apply art_dgap_far; [clear - P0 Ha; lia|clear - P2 Hl; lia|unfold apart in Ai1, Ai2, Ai3, Ai4; clear - P1 Ha Hl Ai1 Ai2 Ai3 Ai4; lia|unfold apart in At |- *; clear - At Ha Hl; lia|unfold apart in Ak; clear - Ak Ha Hl Kspb Kend; lia].
Qed.

#[using="FSG rn G LB bound sp fg lg qtl qgl L GL REPB BLg HSP AGR"] Lemma art_drn_byte_sh : forall a v, 0 <= a < 2 ^ 47 -> byte_at M (HeapIfaceA.S a) v -> byte_at M' (HeapIfaceA.S a) v.
Proof.
  intros a v Ha Bt. apply (art_byte_at_eq M M'); [|exact Bt]. apply art_drn_shadow.
  pose proof (art_S_ge a 0 ltac:(lia)). pose proof (art_S_lt a (2 ^ 44) ltac:(lia)). lia.
Qed.
#[using="FSG rn G LB bound sp fg lg qtl qgl L GL REPB BLg HSP AGR"] Lemma art_drn_shadow_blk : forall u0 n0, 0 <= u0 -> 0 < n0 -> u0 + n0 <= 2 ^ 47 -> HAJ.shadow_blkR M u0 n0 -> HAJ.shadow_blkR M' u0 n0.
Proof.
  intros u0 n0 Hu0 Hn0 Hhi SB0.
  assert (TBY : forall j, 0 <= j -> (j < n0 / 8 \/ (j = n0 / 8 /\ n0 mod 8 <> 0)) -> forall v, byte_at M (HeapIfaceA.S u0 + j) v -> byte_at M' (HeapIfaceA.S u0 + j) v).
  { intros j Hj0 Hj v Bt. apply (art_byte_at_eq M M'); [|exact Bt]. apply art_drn_shadow.
    pose proof (art_S_ge u0 0 ltac:(lia)) as B0. pose proof (art_S_blk_hi u0 n0 j Hn0 Hj) as B1. pose proof (art_S_lt (u0 + n0 - 1) (2 ^ 44) ltac:(lia)) as B2. lia. }
  exact (shadow_blkR_tby M M' u0 n0 Hn0 TBY SB0).
Qed.

#[using="FSG G LB M bound sp fg lg qtl qgl L GL REPB BLg HSP GRW AGR"] Lemma art_drn_thread : art_rt_thread rn M'.
Proof.
  pose proof REPB as (ROK & _ & TH & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct TH as (Wt & C1 & C2 & C3 & C4 & C5 & C6 & C7).
  assert (TT : forall a (j : nat) v, rn_t rn <= a -> a + Z.of_nat j <= rn_t rn + 4096 -> (a + Z.of_nat j <= rn_t rn + 80 \/ rn_t rn + 112 <= a) -> cellA M a j v -> cellA M' a j v).
  { intros a j v Ha Hk Hlo C. apply (art_cell_tr art_drain_W M M' a j v AGR (art_dgap_thread a _ Ha Hk Hlo)); [lia|lia|exact C]. }
  unfold art_rt_thread. split; [eapply wr_grows; [exact GRW|exact Wt]|].
  split; [apply TT; [lia|cbn; lia|cbn; lia|exact C1]|].
  split. { apply (art_cell_tr art_drain_W M M' (rn_ctx rn + 8) 4%nat 0 AGR); [|lia|cbn; lia|exact C2].
           apply art_dgap_far; [clear - G13; lia|clear - G14; lia|clear - G15; lia|unfold apart in G18 |- *; clear - G18; lia|unfold apart in G17; clear - G17; lia]. }
  split; [apply TT; [lia|cbn; lia|cbn; lia|exact C3]|]. split; [apply TT; [lia|cbn; lia|cbn; lia|exact C4]|].
  split; [apply TT; [lia|cbn; lia|cbn; lia|exact C5]|]. split; [apply TT; [lia|cbn; lia|cbn; lia|exact C6]|].
  apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|exact C7].
Qed.

#[using="LB M bound sp fg lg qtl qgl L GL REPB BLg HSP GRW AGR"] Lemma art_drn_primary : art_rt_primary FSG rn Gd M'.
Proof.
  pose proof REPB as (ROK & _ & _ & (PH & PRIM & Wsh) & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  unfold art_rt_primary, Gd. cbn [art_gs_drain g_inited g_cls].
  split. { apply (art_pc_hdr_tr art_drain_W (rn_t rn + 208) _ M M' ltac:(lia) ltac:(lia) AGR); [|exact PH]. intros c Hc. apply art_dgap_thread; lia. }
  split; [|eapply wr_grows; [exact GRW|exact Wsh]].
  intros c Hc. destruct (PRIM c Hc) as (RC & OK & REST). split; [|split; [exact OK|exact REST]].
  pose proof OK as (Hl16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & _).
  apply (art_cls_rep_tr art_drain_W (rn_t rn + 208) (rn_spb rn) (rn_ris rn) c (g_cls FSG G c) M M'); first [ exact RC | exact GRW | exact AGR | exact Hl16 | lia | idtac ].
  - apply art_dgap_thread; lia.
  - apply art_dgap_thread; lia.
  - apply art_dgap_far; [lia|lia|lia|unfold apart in G11 |- *; clear - G11 Hc Eris; lia|right; clear - Hc Eris; lia].
  - apply art_dgap_far; [lia|clear - Hc Hnf4 Hmfa1 G6 Eris; lia|clear - Hc G4; lia|unfold apart in G11 |- *; clear - G11 Hc Hnf4 Hmfa1; lia|].
    destruct (Z_lt_ge_dec c 24) as [Lo|Hi]; [left; clear - Lo Hnf4 Hmfa1; lia|right; clear - Hi; lia].
Qed.

#[using="M bound sp fg lg qtl qgl L GL REPB BLg HSP AGR"] Lemma art_drn_chunks : art_rt_chunks FSG rn Gd LB M'.
Proof.
  pose proof REPB as (ROK & _ & _ & (_ & PRIM & _) & CH & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  intros c Hc. pose proof (CH c Hc) as CH0. cbv zeta in CH0. cbv zeta. unfold Gd. cbn [art_gs_drain g_cls g_st g_qt g_qg]. destruct CH0 as (I0 & II & II' & III).
  destruct (PRIM c Hc) as (_ & OK0 & _). pose proof OK0 as (_ & (Hau0 & Haumu0) & _ & _ & _ & Hmu30 & _). pose proof (art_class_size_facts c Hc) as (Hsz & Hsz16).
  assert (RB : forall y, 0 <= y <= cl_mu (g_cls FSG G c) -> 0 <= rn_spb rn + c * 2 ^ 32 + y < 2 ^ 47) by (intros y Hy; clear - Hy Hc Hmu30 G4 G6 G2 Eris; lia).
  split. { intros x Hx Hx8. apply art_drn_byte_sh; [apply RB; clear - Hx Hau0; lia|exact (I0 x Hx Hx8)]. }
  split; [exact II|]. split; [exact II'|].
  intros w V. specialize (III w V). pose proof V as (V0 & V1 & _).
  assert (TCELL : g_st FSG G c w <> CBatch -> forall a (j : nat) v, rn_spb rn + c * 2 ^ 32 + 16 * w <= a -> a + Z.of_nat j <= rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c -> cellA M a j v -> cellA M' a j v).
  { intros NS a j v Ha Hj C. apply (art_cell_agree _ M M'); [|clear - Ha Hc V0 G4; lia|clear - Hj Hc V1 Haumu0 Hmu30 G6 G2 Eris; lia|exact C].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (art_drn_chunk c w (U x) Hc V NS). clear - Hx Ha Hj. lia. }
  assert (THDR : g_st FSG G c w <> CBatch -> forall u0 n0 st, rn_spb rn + c * 2 ^ 32 + 16 * w + 16 <= u0 -> u0 + n0 <= rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c -> art_chunk_hdr M u0 n0 st -> art_chunk_hdr M' u0 n0 st).
  { intros NS u0 n0 st L1 L2 (bb & Hb & Hbt & C1 & C2 & Hn0). exists bb. split; [exact Hb|]. split; [exact Hbt|]. split; [|split; [|exact Hn0]].
    - apply (TCELL NS); [lia|cbn; lia|exact C1]. - apply (TCELL NS); [lia|cbn; lia|exact C2]. }
  assert (TLCH : g_st FSG G c w <> CBatch -> forall u0, art_lch M (rn_spb rn + c * 2 ^ 32 + 16 * w) u0 -> art_lch M' (rn_spb rn + c * 2 ^ 32 + 16 * w) u0).
  { intros NS u0 LC NE. destruct (LC NE) as (C1 & C2). split; (apply (TCELL NS); [lia|cbn; clear - Hsz; lia|assumption]). }
  assert (TSB : forall a v, rn_spb rn + c * 2 ^ 32 + 16 * w = a -> byte_at M (HeapIfaceA.S a) v -> byte_at M' (HeapIfaceA.S a) v).
  { intros a v <- Bt. apply art_drn_byte_sh; [|exact Bt]. specialize (RB (16 * w) ltac:(clear - V0 V1 Haumu0 Hsz; lia)). clear - RB. lia. }
  destruct (g_st FSG G c w) as [|u0 n0|u0 n0|] eqn:St.
  - destruct III as (I1 & I2). split; [exact I1|exact (TSB _ _ eq_refl I2)].
  - destruct III as (J1 & J2 & J3 & J4 & J5 & J6 & J7). pose proof J4 as (_ & _ & _ & _ & _ & Hn0).
    split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. split; [apply THDR; [discriminate|exact J2|exact J3|exact J4]|].
    split. { apply art_drn_shadow_blk; [clear - J2 Hc V0 G4; lia|clear - Hn0; lia| |exact J5]. specialize (RB (16 * w + AsanTab.class_size c) ltac:(clear - V0 V1 Haumu0 Hsz; lia)). clear - RB J3. lia. }
    split; [exact (TSB _ _ eq_refl J6)|apply TLCH; [discriminate|exact J7]].
  - destruct III as (J2 & J3 & J4 & J5 & J6 & J7). split; [exact J2|]. split; [exact J3|]. split; [apply THDR; [discriminate|exact J2|exact J3|exact J4]|].
    split. { apply (art_in_batches_perm (g_qt FSG G) (g_qg FSG G) [] (g_qg FSG G ++ g_qt FSG G)); [|exact J5]. intros x Hx. cbn [app]. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]; [right|left]; exact Hx. }
    split; [exact (TSB _ _ eq_refl J6)|apply TLCH; [discriminate|exact J7]].
  - destruct III as (E24 & b0 & Hb0 & Eb0). split; [exact E24|]. exists b0. split; [|exact Eb0]. cbn [app]. apply in_app_or in Hb0. apply in_or_app. destruct Hb0 as [Hb0|Hb0]; [right|left]; exact Hb0.
Qed.

#[using="M bound sp fg lg qtl qgl L GL REPB BLg HSP GRW AGR LIVE"] Lemma art_drn_sec : art_rt_sec FSG rn Gd LB M'.
Proof.
  pose proof REPB as (ROK & _ & _ & _ & _ & SEC & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct SEC as (C1 & C2 & C3 & C4 & C5 & C6 & S1 & S2 & SALL & SLIVE & SLEN).
  unfold art_rt_sec, Gd. cbn [art_gs_drain g_sec g_sec_committed g_log g_qt g_qg].
  split; [apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|exact C1]|]. split; [apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|exact C2]|].
  split; [apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|exact C3]|]. split; [apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|exact C4]|].
  split; [apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|exact C5]|]. split; [apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|exact C6]|]. split; [exact S1|].
  split; [intros E; eapply wr_grows; [exact GRW|exact (S2 E)]|]. split; [|split; [exact SLIVE|exact SLEN]].
  intros i s Hi. destruct (SALL i s Hi) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
  assert (Hil : Z.of_nat i < Z.of_nat (length (g_sec FSG G))). { apply Nat2Z.inj_lt. apply nth_error_Some. rewrite Hi. discriminate. }
  destruct (LIVE _ P2) as (L0 & L1 & L2 & _). cbn [fst snd] in L0, L1, L2.
  assert (Hn0s : 1 <= sc_n s). { destruct (sc_quar s); [destruct P9 as ((bb & _ & _ & _ & _ & H) & _)|destruct P9 as (_ & (bb & _ & _ & _ & _ & H) & _)]; lia. }
  assert (TG : forall a (j : nat) v, sc_map s <= a -> a + Z.of_nat j <= sc_map s + sc_msize s -> cellA M a j v -> cellA M' a j v).
  { intros a j v Ha Hj C. apply (art_cell_tr art_drain_W M M' a j v AGR (art_dgap_grant (sc_map s, sc_msize s) a _ P2 Ha Hj)); [clear - L0 Ha; lia|clear - L2 Hj G2; lia|exact C]. }
  assert (THDR : forall st, art_chunk_hdr M (sc_u s) (sc_n s) st -> art_chunk_hdr M' (sc_u s) (sc_n s) st).
  { intros st (bb & Hb & Hbt & E1 & E2 & Hn0). exists bb. split; [exact Hb|]. split; [exact Hbt|]. split; [|split; [|exact Hn0]].
    - apply TG; [clear - P7; lia|cbn; clear - P8 Hn0s; lia|exact E1]. - apply TG; [clear - P7; lia|cbn; clear - P8 Hn0s; lia|exact E2]. }
  split. { apply (art_cell_tr art_drain_W M M' _ 8%nat _ AGR); [|clear - Plo; lia|cbn; clear - Phi G2 Hil SLEN; lia|exact P1].
           apply art_dgap_far; [clear - Plo; lia|clear - Phi Hil SLEN; lia|clear - Plo; lia|unfold apart in Apt |- *; clear - Apt Hil SLEN; lia|unfold apart in Apk; clear - Apk Hil SLEN; lia]. }
  split; [exact P2|]. split; [eapply wr_grows; [exact GRW|exact P3]|].
  split; [apply TG; [clear; lia|cbn; clear - P7 P8 Hn0s; lia|exact P4]|]. split; [apply TG; [clear; lia|cbn; clear - P7 P8 Hn0s; lia|exact P5]|].
  split; [apply TG; [clear; lia|cbn; clear - P7 P8 Hn0s; lia|exact P6]|]. split; [exact P7|]. split; [exact P8|]. split; [|exact P10].
  destruct (sc_quar s).
  - destruct P9 as (Q1 & Q2). split; [exact (THDR _ Q1)|].
    apply (art_in_batches_perm (g_qt FSG G) (g_qg FSG G) [] (g_qg FSG G ++ g_qt FSG G)); [|exact Q2]. intros x Hx. cbn [app]. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]; [right|left]; exact Hx.
  - destruct P9 as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact (THDR _ Q2)|]. apply art_drn_shadow_blk; [clear - L0 P7; lia|clear - Hn0s; lia|clear - P8 L2 G2; lia|exact Q3].
Qed.

#[using="LB M bound sp fg lg qtl qgl L GL REPB BLg HSP AGR"] Lemma art_drn_depot : art_rt_depot FSG rn Gd M'.
Proof.
  pose proof REPB as (ROK & _ & _ & _ & _ & _ & _ & DEP & _). rok_open14 ROK. geo_open GEO. unfold art_rt_depot, Gd in *. cbn [art_gs_drain g_depot].
  apply (DInvD_frame (rn_l2 rn) (rn_blk rn) _ M M' DEP). intros x Dx. apply AGR. revert Dx. apply art_dpriv_out.
  - apply art_dgap_img; lia.
  - apply art_dgap_far; [lia|lia|lia|exact Al2t|unfold apart in Al2k; clear - Al2k; lia].
  - apply art_dgap_far; [lia|lia|lia|exact Abt|unfold apart in Abk; clear - Abk; lia].
Qed.

#[using="rn LB M bound sp fg lg qtl qgl L GL REPB NEq BLg HSP AGR"] Lemma art_drn_ia : art_rt_ia FSG Gd M'.
Proof.
  pose proof REPB as (_ & _ & _ & _ & _ & _ & _ & _ & (IA1 & IA2 & IA3) & _). unfold art_rt_ia, Gd. cbn [art_gs_drain g_ia g_qt g_qg].
  split; [apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|exact IA1]|]. split.
  - intros E j Hj. apply art_drn_cell_img; [lia|cbn; lia|cbn; lia|exact (IA2 E j Hj)].
  - intros E. destruct (IA3 E) as (E1 & _). exfalso. exact (NEq E1).
Qed.

#[using="M bound REPB"] Lemma art_drn_blocks : art_rt_blocks FSG rn Gd LB.
Proof. pose proof REPB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BLK & _). exact BLK. Qed.
(* [comment removed for export] *)
#[using="LB M bound sp fg lg qtl qgl L GL REPB BLg HSP AGR"] Lemma art_drn_ghost : art_rt_ghost FSG rn Gd M'.
Proof.
  clear NR.
  pose proof REPB as (ROK & _ & _ & (_ & PRIM & _) & _ & _ & QR & _ & _ & _ & (T1 & T23 & T4 & T5)). rok_open14 ROK. geo_open GEO.
  destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH).
  assert (PERM : forall b, In b (g_qt FSG Gd ++ g_qg FSG Gd) -> In b (g_qt FSG G ++ g_qg FSG G)).
  { intros b Hb. unfold Gd in Hb. cbn [art_gs_drain g_qt g_qg app] in Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [right|left]; exact Hb. }
  split; [intros b it Hb Hit; exact (T1 b it (PERM b Hb) Hit)|]. split; [exact T23|]. split.
  - intros b Hb. pose proof (T4 b (PERM b Hb)) as B. destruct (BCH b (PERM b Hb)) as (w0 & Ew0 & (V0 & V1 & _) & _). rewrite art_class_size_24 in V1.
    destruct (PRIM 24 ltac:(lia)) as (_ & OK0 & _). destruct OK0 as (_ & (_ & Haumu0) & _ & _ & _ & Hmu30 & _).
    apply (art_byte_at_eq M M'); [|exact B]. apply art_drn_shadow. unfold HeapIfaceA.S, HeapIfaceA.SB.
    assert (0 <= bt_addr b / 8) by (apply Z.div_pos; [rewrite Ew0; clear - V0 G4|]; lia).
    assert (bt_addr b / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; [lia|]; rewrite Ew0; clear - V1 Haumu0 Hmu30 G6 G2 Eris; lia). lia.
  - apply art_drn_cell_img; [lia|cbn; lia|left; cbn; lia|exact T5].
Qed.

(* [comment removed for export] *)
#[using="LB M bound sp ft lt fg lg L GL REPB NEq BLt Gf BLg HSP AGR POST"] Lemma art_drn_quar_x : art_rt_quar_x FSG (2 ^ 20) (art_batches_bytes qgl + art_batches_bytes qtl) rn Gd M'.
Proof.
  clear NR.
  pose proof REPB as (ROK & _ & _ & (_ & PRIM & _) & _ & _ & QR & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct QR as (_ & _ & Bt & Bg & Cmx & ND & NEI & ITEMS & NDI & BCH).
  destruct POST as (P80 & P88 & P96 & P104 & P160 & P176 & P184 & P152 & PF0 & PFN).
  apply NoDup_ListNoDup in ND. apply NoDup_ListNoDup in NDI.
  assert (COMM : forall x, In x (g_qg FSG G ++ g_qt FSG G) -> In x (g_qt FSG G ++ g_qg FSG G)).
  { intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]; [right|left]; exact Hx. }
  assert (ADDRB : forall b0, In b0 (g_qt FSG G ++ g_qg FSG G) -> 0 <= bt_addr b0 /\ bt_addr b0 + 8192 < 2 ^ 64).
  { intros b0 Hb0. destruct (BCH b0 Hb0) as (w0 & Ew0 & (V0 & V1 & _) & _). rewrite art_class_size_24 in V1. destruct (PRIM 24 ltac:(lia)) as (_ & OK0 & _).
    destruct OK0 as (_ & (_ & Haumu0) & _ & _ & _ & Hmu30 & _). rewrite Ew0. clear - V0 V1 Haumu0 Hmu30 G4 G6 G2 Eris Espb. lia. }
  unfold art_rt_quar_x, Gd. cbn [art_gs_drain g_qt g_qg g_cls g_st g_sec]. fold qtl. fold qgl.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
  - exists 0, 0. cbn [length art_batches_bytes fold_right art_batch_list]. split; [exact P80|]. split; [replace (rn_t rn + 88) with (rn_t rn + 80 + 8) by lia; exact P88|].
    split; [replace (rn_t rn + 96) with (rn_t rn + 80 + 16) by lia; exact P96|]. split; [replace (rn_t rn + 104) with (rn_t rn + 80 + 24) by lia; exact P104|reflexivity].
  - assert (EX : exists t0 ts, qtl = t0 :: ts). { clear - NEq. destruct qtl as [|t0 ts]; [contradiction|]. exists t0, ts. reflexivity. }
    destruct EX as (t0 & ts & Eqt). pose proof BLt as BLt'. rewrite Eqt in BLt'. rewrite Eqt.
    assert (Eft : ft = bt_addr t0) by (cbn [art_batch_list] in BLt'; destruct BLt' as (E & _); exact E).
    assert (InT : forall b0, In b0 (t0 :: ts) -> In b0 (g_qt FSG G ++ g_qg FSG G)) by (intros b0 Hb0; apply in_or_app; left; fold qtl; rewrite Eqt; exact Hb0).
    assert (InG : forall b0, In b0 qgl -> In b0 (g_qt FSG G ++ g_qg FSG G)) by (intros b0 Hb0; apply in_or_app; right; exact Hb0).
    assert (BT' : art_batch_list M' (t0 :: ts) (bt_addr t0) lt).
    { rewrite <- Eft. apply (art_batch_list_tr M M'); [|exact BLt']. intros b0 Hb0. destruct (ADDRB b0 (InT b0 Hb0)) as (A0 & A1). split; [exact A0|]. split; [exact A1|].
      intros x Hx. apply (art_drn_batch b0 x); [fold qtl; rewrite Eqt; apply in_or_app; left; exact Hb0|exact Hx|]. intros (NG & EB & _).
      assert (NEg : qgl <> []) by (intros E; apply NG; unfold GL; rewrite E; reflexivity).
      pose proof (art_batch_list_last M qgl fg lg NEg BLg) as El.
      assert (InL : In (art_lastb qgl) qgl) by (unfold art_lastb; apply BatFxQ_b.art_last_in; exact NEg).
      refine (art_nodup_map_app_d _ bt_addr (g_qt FSG G) (g_qg FSG G) b0 (art_lastb qgl) ND _ InL _); [fold qtl; rewrite Eqt; exact Hb0|rewrite EB; exact El]. }
    exists (if GL =? 0 then ft else fg), lt.
    split. { rewrite length_app, Nat2Z.inj_add. fold GL. replace (Z.of_nat (length (t0 :: ts))) with L by (unfold L; rewrite Eqt; reflexivity). exact P160. }
    split. { destruct (Z.eqb_spec GL 0) as [EG|NG]; [exact (PF0 EG)|]. apply (art_cell_tr art_drain_W M M' _ 8%nat _ AGR); [|lia|cbn; lia|exact Gf].
             destruct art_drn_num as (HHI & HLG). destruct (HLG NG) as (X1 & X2 & X3). unfold art_drain_W. cbn [art_gap fst snd]. unfold apart. unfold apart in G11.
             destruct (Z.eqb_spec GL 0) as [E|_]; [contradiction|]. clear - HSP HHI G4 G9 X1. repeat split; try exact I; lia. }
    split; [exact P176|]. split. { rewrite <- Eqt. rewrite art_batches_bytes_app. exact P184. }
    destruct (Z.eqb_spec GL 0) as [EG|NG].
    + assert (Eg0 : qgl = []) by (apply length_zero_iff_nil; unfold GL in EG; clear - EG; lia). rewrite Eg0. cbn [app]. rewrite Eft. exact BT'.
    + assert (NEg : qgl <> []) by (intros E; apply NG; unfold GL; rewrite E; reflexivity).
      apply (art_batch_list_append M M' qgl fg lg t0 ts lt NEg); [ | exact BLg | | | | exact BT' ].
      * apply NoDup_ListNoDup. rewrite map_app in ND. exact (NoDup_app_remove_l _ _ ND).
      * intros b0 Hb0. exact (ADDRB b0 (InG b0 Hb0)).
      * intros b0 x Hb0 Hx NX. apply (art_drn_batch b0 x); [apply in_or_app; right; exact Hb0|exact Hx|]. intros (_ & EB & Y). apply NX. split; assumption.
      * rewrite <- Eft. exact (PFN NG).
  - cbn. lia.
  - rewrite art_batches_bytes_app. lia.
  - exact P152.
  - cbn [app]. apply NoDup_ListNoDup. rewrite map_app. rewrite map_app in ND. exact (Permutation_NoDup (Permutation_app_comm _ _) ND).
  - intros b0 Hb0. cbn [app] in Hb0. exact (NEI b0 (COMM b0 Hb0)).
  - intros b0 it Hb0 Hit. cbn [app] in Hb0. exact (ITEMS b0 it (COMM b0 Hb0) Hit).
  - cbn [app]. apply NoDup_ListNoDup. rewrite flat_map_app, map_app. rewrite flat_map_app, map_app in NDI. exact (Permutation_NoDup (Permutation_app_comm _ _) NDI).
  - intros b0 Hb0. cbn [app] in Hb0. exact (BCH b0 (COMM b0 Hb0)).
Qed.

#[using="LB M bound sp ft lt fg lg qtl qgl L GL REPB NEq BLt Gf BLg HSP NR AGR POST"] Lemma art_drn_quar : art_rt_quar FSG rn Gd M'.
Proof.
  destruct art_drn_quar_x as (Q1 & Q2 & Q3 & Q4 & Q5). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [|exact Q5].
  unfold Gd. cbn [art_gs_drain g_qg]. fold qtl. fold qgl. rewrite art_batches_bytes_app. exact NR.
Qed.

#[using="M bound sp ft lt fg lg L GL REPB NEq BLt Gf BLg HSP GRW AGR POST LIVE"] Theorem art_alloc_rep_drain_x : art_alloc_rep_x FSG (2 ^ 20) (art_batches_bytes qgl + art_batches_bytes qtl) rn Gd LB M'.
Proof.
  clear NR.
  pose proof REPB as (ROK & _).
  split; [exact ROK|]. split; [exact art_drn_statics|]. split; [exact art_drn_thread|]. split; [exact art_drn_primary|]. split; [exact art_drn_chunks|].
  split; [exact art_drn_sec|]. split; [exact art_drn_quar_x|]. split; [exact art_drn_depot|]. split; [exact art_drn_ia|]. split; [exact art_drn_blocks|exact art_drn_ghost].
Qed.

#[using="M bound sp ft lt fg lg qtl qgl L GL REPB NEq BLt Gf BLg HSP NR GRW AGR POST LIVE"] Theorem art_alloc_rep_drain : art_alloc_rep FSG rn Gd LB M'.
Proof.
  pose proof REPB as (ROK & _).
  split; [exact ROK|]. split; [exact art_drn_statics|]. split; [exact art_drn_thread|]. split; [exact art_drn_primary|]. split; [exact art_drn_chunks|].
  split; [exact art_drn_sec|]. split; [exact art_drn_quar|]. split; [exact art_drn_depot|]. split; [exact art_drn_ia|]. split; [exact art_drn_blocks|exact art_drn_ghost].
Qed.

(* [comment removed for export] *)
#[using="qtl L"] Lemma art_drn_fp_where : forall x, ~ art_out art_drain_W x ->
  (sp - 48 <= x < sp) \/ (0x13c948 <= x < 0x13c970) \/ (rn_t rn + 80 <= x < rn_t rn + 112) \/ (GL <> 0 /\ lg <= x < lg + 8).
Proof.
  intros x N. unfold art_drain_W in N. cbn [art_out fst snd] in N. destruct (Z.eqb_spec GL 0) as [E|NG]; lia.
Qed.
(* [comment removed for export] *)
#[using="LB M bound fg qtl L REPB BLg HSP"] Lemma art_drn_out_shadow : forall a, 0x7fff8000 <= a < 0x10007fff8000 -> art_out art_drain_W a.
Proof.
  intros a Ha. destruct art_drn_num as (HHI & HLG). pose proof REPB as (ROK & _). rok_open14 ROK. geo_open GEO. unfold apart in G10.
  unfold art_drain_W. cbn [art_out fst snd].
  destruct (Z.eqb_spec GL 0) as [E|NG]; [|destruct (HLG NG) as (X1 & X2 & X3)]; clear - Ha HSP HHI G4 G10 X1 || clear - Ha HSP HHI G4 G10; repeat split; try exact I; lia.
Qed.

#[using="M bound fg qtl L REPB BLg HSP LIVE"] Lemma art_drn_out_block : forall b0 a, In b0 LB -> (fst b0 <= a < fst b0 + snd b0 \/ in_shadow_of (fst b0) (snd b0) a) -> art_out art_drain_W a.
Proof.
  intros b0 a Hb0 Ha. destruct art_drn_num as (HHI & HLG). pose proof REPB as (ROK & _ & _ & (_ & PRIM & _) & CH & SEC & _ & _ & _ & BLK & _). rok_open14 ROK. geo_open GEO. unfold apart in G11.
  unfold in_shadow_of in Ha.
  destruct (BLK b0 Hb0) as [(c0 & w0 & Hc0 & V0 & St0)|(s & Hs & Hq & Esu & Esn)].
  - specialize (CH c0 Hc0). cbv zeta in CH. destruct CH as (_ & _ & _ & III). specialize (III w0 V0). rewrite St0 in III. destruct III as (_ & J2 & J3 & (bb & _ & _ & _ & _ & Hn0) & _).
    destruct (PRIM c0 Hc0) as (_ & OK0 & _). destruct OK0 as (_ & (_ & Haumu0) & _ & _ & _ & Hmu30 & _). pose proof V0 as (V00 & V01 & _).
    destruct Ha as [Ha|Ha].
    + (* [comment removed for export] *)
      assert (INC : rn_spb rn + c0 * 2 ^ 32 + 16 * w0 <= a < rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + AsanTab.class_size c0) by (clear - Ha J2 J3; lia).
      unfold art_drain_W. cbn [art_out fst snd]. destruct (Z.eqb_spec GL 0) as [E|NG].
      * clear - INC Hc0 V00 V01 Haumu0 Hmu30 HSP HHI G4 G6 G8 G11 Espb Eris. repeat split; try exact I; lia.
      * destruct (art_drn_lg NG) as (wG & ElG & VG & StG). destruct (PRIM 24 ltac:(lia)) as (_ & OK24 & _). destruct OK24 as (_ & (_ & Haumu24) & _ & _ & _ & Hmu324 & _).
        pose proof (art_class_size_facts c0 Hc0) as (Hsz0 & _).
        destruct (Z.eq_dec c0 24) as [E24|N24].
        -- subst c0. rewrite art_class_size_24 in INC, V0, V01. assert (Nw : w0 <> wG) by (intros ->; rewrite StG in St0; discriminate).
           pose proof (art_cptr_apart 8192 (cl_au (g_cls FSG G 24)) w0 wG ltac:(clear; lia) V0 VG Nw) as AP. rewrite ElG.
           clear - INC AP V00 V01 HSP HHI G4 G6 G8 G11 Espb Eris Hmu30 Haumu0. repeat split; try exact I; lia.
        -- destruct VG as (VG0 & VG1 & _). rewrite ElG. clear - INC N24 Hc0 V00 V01 Haumu0 Hmu30 VG0 VG1 Haumu24 Hmu324 HSP HHI G4 G6 G8 G11 Espb Eris Hsz0. repeat split; try exact I; lia.
    + apply art_drn_out_shadow. pose proof (art_S_ge (fst b0) 0 ltac:(clear - J2 Hc0 V00 G4; lia)) as B0.
      pose proof (art_S_lt (fst b0 + snd b0 - 1) (2 ^ 44) ltac:(clear - J3 Hc0 V01 Haumu0 Hmu30 G6 G2 Eris; lia)) as B1. clear - Ha B0 B1. lia.
  - destruct SEC as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _). destruct (In_nth_error _ _ Hs) as (i & Hi). destruct (SALL i s Hi) as (_ & P2 & _ & _ & _ & _ & P7 & P8 & P9 & _).
    rewrite Hq in P9. destruct P9 as (_ & (bb & _ & _ & _ & _ & Hn0) & _). destruct (LIVE _ P2) as (L0 & L1 & L2 & _). cbn [fst snd] in L0, L1, L2. rewrite Esu in P7. rewrite Esu, Esn in P8.
    destruct Ha as [Ha|Ha].
    + apply (art_gap_out _ a 1); [|clear; lia]. apply (art_dgap_grant (sc_map s, sc_msize s) a 1 P2); cbn [fst snd]; clear - Ha P7 P8; lia.
    + apply art_drn_out_shadow. pose proof (art_S_ge (fst b0) 0 ltac:(clear - L0 P7; lia)) as B0.
      pose proof (art_S_lt (fst b0 + snd b0 - 1) (2 ^ 44) ltac:(clear - L2 P8 G2; lia)) as B1. clear - Ha B0 B1. lia.
Qed.

#[using="M bound fg qtl L REPB BLg HSP LIVE"] Theorem art_drn_out_bundle :
  (forall b0 a, In b0 LB -> (fst b0 <= a < fst b0 + snd b0 \/ in_shadow_of (fst b0) (snd b0) a) -> art_out art_drain_W a)
  /\ (forall a, 0x7fff8000 <= a < 0x10007fff8000 -> art_out art_drain_W a)
  /\ (forall a, rn_HI rn <= a -> ~ (sp - 48 <= a < sp) -> art_out art_drain_W a)
  /\ (forall a, 0x10000 <= a < 0x696000 -> ~ (0x13c948 <= a < 0x13c970) -> art_out art_drain_W a)
  /\ (forall a, ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES -> art_out art_drain_W a)
  /\ (forall a, rn_dtls rn <= a < rn_dtls rn + 4096 -> art_out art_drain_W a)
  /\ (forall a, rn_t rn <= a < rn_t rn + 80 -> art_out art_drain_W a).
Proof.
  split; [exact art_drn_out_block|]. split; [exact art_drn_out_shadow|].
  destruct art_drn_num as (HHI & HLG). pose proof REPB as (ROK & _). rok_open14 ROK. geo_open GEO. unfold apart in G11.
  split. { intros a Ha Ns. unfold art_drain_W. cbn [art_out fst snd].
           destruct (Z.eqb_spec GL 0) as [E|NG]; [|destruct (HLG NG) as (X1 & X2 & X3)]; clear - Ha Ns HHI G4 G6 G8 X1 X2 X3 Eris || clear - Ha Ns HHI G4 G6 G8 Eris; repeat split; try exact I; lia. }
  split. { intros a Ha Nq. apply (art_gap_out _ a 1); [|clear; lia]. apply art_dgap_img; clear - Ha Nq; lia. }
  split. { intros a Ha. apply (art_gap_out _ a 1); [|clear; lia]. unfold FS_BYTES in *.
           apply art_dgap_far; [clear - Flo Ha; lia|clear - Fhi Ha; lia|clear - Fimg Ha; lia|unfold apart in Aft |- *; clear - Aft Ha; lia|unfold apart in Afk; clear - Afk Ha; lia]. }
  split. { intros a Ha. apply (art_gap_out _ a 1); [|clear; lia].
           apply art_dgap_far; [clear - D0 Ha; lia|clear - D1 Ha; lia|clear - D2 Ha; lia|unfold apart in Adt |- *; clear - Adt Ha; lia|unfold apart in Adk; clear - Adk Ha Kspb Kend; lia]. }
  intros a Ha. apply (art_gap_out _ a 1); [|clear; lia]. apply art_dgap_thread; clear - Ha; lia.
Qed.
End Drain.
