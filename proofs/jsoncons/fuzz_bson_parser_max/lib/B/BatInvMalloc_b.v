(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceABx As0Tables
     ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatRzLog_b BatAllocA_b BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatCellEx_b BatByteCell_b BatCellJoin_b
     BatCARSpec_b BatAlloc3Pure_b BatDepotA_b BatDepot_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocate3_b BatInv_b BatInvMallocPure_b BatInvMallocFp_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx ShadowRLawsB.      (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Lemma art_prim_consts_tr : forall W M M' spb ris, art_agree W M M' -> (forall z, 0x10000 <= z < 0x211b08 -> art_out W z) ->
  art_prim_consts spb ris M -> art_prim_consts spb ris M'.
Proof.
  intros W M M' spb ris A O (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
  assert (TI : forall a (n : nat) v, 0x10000 <= a -> a + Z.of_nat n <= 0x211b08 -> cellA M a n v -> cellA M' a n v).
  { intros a n v Ha Hn C. apply (art_cell_agree _ M M'); [|lia|lia|exact C]. intros x Hx. apply A. apply O. lia. }
  unfold art_prim_consts. repeat split; apply TI; first [assumption | cbn; lia].
Qed.

(* [comment removed for export] *)
Definition art_gs_malloc {FSG : Type} (G : art_gs FSG) (spb c w u n : Z) (kb : nat) : art_gs FSG :=
  GS FSG (g_log FSG G ++ art_ca_events spb c (g_cls FSG G c)) true
     (fun c0 => if c0 =? c then art_cls_pop (art_ca_pre c (g_cls FSG G c)) else g_cls FSG G c0)
     (fun c0 w0 => if (c0 =? c) && (w0 =? w) then CAlloc u n else g_st FSG G c0 w0)
     (g_sec FSG G) (g_sec_committed FSG G) (g_qt FSG G) (g_qg FSG G) kb (g_ia FSG G) (g_fs FSG G).

(* [comment removed for export] *)
Definition art_malloc_out (rn : art_run) (M M' : word -> option byte) (S n rz qz rs qr qn m8 km : Z) (kb : nat) (cl : art_cls) (b1 : Z) : Prop :=
  let c := AsanTab.class_id (rs + rz) in
  let w := art_ca_cptr c cl in
  let ab := rn_spb rn + c * 2 ^ 32 + w * 16 in
  let shb := 2147450880 + 8192 * rn_qs rn + c * 2 ^ 29 in
  mem_grows M M'
  /\ (forall x : word, ~ art_malloc_fp S (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) c km ab rz n rs (rn_l2 rn) (rn_blk rn) (U x) -> M' x = M x)
  /\ DInvD (rn_l2 rn) (rn_blk rn) kb M'
  /\ art_pc_hdr (rn_t rn + 208) true M' /\ art_cls_rep (rn_t rn + 208) (rn_spb rn) (rn_ris rn) c (art_cls_pop (art_ca_pre c cl)) M'
  /\ art_cls_ok c (art_cls_pop (art_ca_pre c cl))
  /\ art_cptr_ok (AsanTab.class_size c) (cl_au (art_ca_pre c cl)) w
  /\ 0 <= b1 < 256 /\ b1 mod 4 = 1
  /\ cellA M' (ab + rz - 16) 1 2 /\ cellA M' (ab + rz - 15) 1 b1 /\ cellA M' (ab + rz - 14) 2 0 /\ cellA M' (ab + rz - 12) 4 n
  /\ cellA M' (shb + 2 * w) 1 250
  /\ (forall j, 0 <= j < qn -> cellA M' (shb + 2 * w + 2 * qz + j) 1 0) /\ (m8 <> 0 -> cellA M' (shb + 2 * w + 2 * qz + qn) 1 m8)
  /\ (cl_cache cl = [] -> art_cls_needs_populate c cl = true ->
        forall j, 0 <= j < 32768 -> ~ (2 * w + 2 * qz <= 32768 * km + j < 2 * w + 2 * qz + qr) -> cellA M' (shb + 32768 * km + j) 1 250)
  /\ (rz <> 16 -> cellA M' ab 8 0xcc6e96b9cc6e96b9 /\ cellA M' (ab + 8) 8 (ab + rz - 16)).                (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma art_S_lin : forall qs0 c0 y, HeapIfaceA.S (65536 * qs0 + c0 * 2 ^ 32 + 8 * y) = 2147450880 + 8192 * qs0 + c0 * 2 ^ 29 + y.
Proof.
  intros qs0 c0 y. unfold HeapIfaceA.S, HeapIfaceA.SB. replace (65536 * qs0 + c0 * 2 ^ 32 + 8 * y) with ((8192 * qs0 + c0 * 2 ^ 29 + y) * 8) by lia.
  rewrite Z_div_mult by lia. lia.
Qed.
Lemma art_S_mono : forall a b, a <= b -> HeapIfaceA.S a <= HeapIfaceA.S b.
Proof. intros a b H. unfold HeapIfaceA.S. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.
Lemma art_S_blk_hi : forall u0 n0 j, 0 < n0 -> (j < n0 / 8 \/ (j = n0 / 8 /\ n0 mod 8 <> 0)) -> HeapIfaceA.S u0 + j <= HeapIfaceA.S (u0 + n0 - 1).
Proof.
  intros u0 n0 j Hn0 Hj. unfold HeapIfaceA.S.
  pose proof (Z.div_mod u0 8 ltac:(lia)) as Du. pose proof (Z.mod_pos_bound u0 8 ltac:(lia)) as Ru.
  pose proof (Z.div_mod n0 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n0 8 ltac:(lia)) as Rn.
  assert (E : u0 / 8 + j <= (u0 + n0 - 1) / 8); [|lia].
  apply Z.div_le_lower_bound; [lia|]. destruct Hj as [Hj|[Hj Hm]]; lia.
Qed.

Lemma art_S_lt : forall a y', a < 8 * y' -> HeapIfaceA.S a < y' + 2147450880.
Proof. intros a y' H. unfold HeapIfaceA.S, HeapIfaceA.SB. pose proof (Z.div_lt_upper_bound a 8 y' ltac:(lia) H). lia. Qed.
Lemma art_S_ge : forall a y', 8 * y' <= a -> y' + 2147450880 <= HeapIfaceA.S a.
Proof. intros a y' H. unfold HeapIfaceA.S, HeapIfaceA.SB. pose proof (Z.div_le_lower_bound a 8 y' ltac:(lia) H). lia. Qed.
Lemma art_byte_at_eq : forall (M M' : word -> option byte) a v, M' (Z_to_bv 64 a) = M (Z_to_bv 64 a) -> byte_at M a v -> byte_at M' a v.
Proof. intros M M' a v E B. unfold byte_at in *. rewrite E. exact B. Qed.

Lemma art_batch_list_tr : forall (M M' : word -> option byte) bs first last,
  (forall b, In b bs -> 0 <= bt_addr b /\ bt_addr b + 8192 < 2 ^ 64 /\ forall x : word, bt_addr b <= U x < bt_addr b + 8192 -> M' x = M x) ->
  art_batch_list M bs first last -> art_batch_list M' bs first last.
Proof.
  intros M M' bs. induction bs as [|b r IH]; intros first last H BL; [exact BL|].
  cbn [art_batch_list] in BL |- *. destruct BL as (E1 & Hlen & C1 & C2 & CI & CN & BR).
  destruct (H b (or_introl eq_refl)) as (B0 & B1 & EQ).
  assert (T : forall a (k : nat) v, bt_addr b <= a -> a + Z.of_nat k <= bt_addr b + 8192 -> cellA M a k v -> cellA M' a k v).
  { intros a k v Ha Hk C. apply (art_cell_agree _ M M'); [intros x Hx; apply EQ; lia|lia|lia|exact C]. }
  split; [exact E1|]. split; [exact Hlen|]. split; [apply T; [lia|cbn; lia|exact C1]|]. split; [apply T; [lia|cbn; lia|exact C2]|].
  split. { intros j it Hj. assert (Z.of_nat j < Z.of_nat (length (bt_items b))) by (apply Nat2Z.inj_lt; apply nth_error_Some; rewrite Hj; discriminate).
           apply T; [lia|cbn; lia|exact (CI j it Hj)]. }
  split. { destruct r as [|b' r']; [destruct CN as (CN1 & CN2); split; [exact CN1|apply T; [lia|cbn; lia|exact CN2]]|apply T; [lia|cbn; lia|exact CN]]. }
  apply IH; [intros b0 Hb0; apply H; right; exact Hb0|exact BR].
Qed.

Lemma art_class_size_24 : AsanTab.class_size 24 = 8192.
Proof. vm_compute. reflexivity. Qed.

Ltac rok_open ROK :=
  destruct ROK as (GEO & Esb & Kal & Kspb & Kend & Pal & Plo & Phi & Papp & Hkey & Hloff & Hloff' & Hloff'' & Htpd & Htsdd & Dl2 & Dblk
                   & Al2t & Al2c & Al2k & Al2s & Abt & Abc & Abk & Abs & Apt & Apc & Apk & Apl & Apb & Aft & Afc & Afk & Afl & Afb & Afp & Fhi & Fapp & Fimg & Flo).
Ltac geo_open GEO :=
  destruct GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).

(* [comment removed for export] *)
Lemma art_ghost_cls_pop : forall c0 cl0, 1 <= c0 <= 30 -> art_cls_ok c0 cl0 ->
  (0 < cl_au cl0 -> 262144 <= cl_mfa cl0) -> Z.of_nat (length (cl_cache cl0)) <= art_ic_mc c0 ->
  (0 < cl_au (art_cls_pop (art_ca_pre c0 cl0)) -> 262144 <= cl_mfa (art_cls_pop (art_ca_pre c0 cl0)))
  /\ Z.of_nat (length (cl_cache (art_cls_pop (art_ca_pre c0 cl0)))) <= art_ic_mc c0.
Proof.
  intros c0 cl0 Hc OK T2 T3. pose proof (art_ic_mc_range c0 ltac:(lia)) as Rmc.
  destruct OK as (_ & (Hau0 & Haumu) & _ & _ & _ & _ & (kf & Ekf) & (Hmfa0 & _) & _). destruct (art_class_size_facts c0 Hc) as (S1 & _).
  assert (RL : forall l : list Z, Z.of_nat (length (removelast l)) <= Z.of_nat (length l)).
  { intros l. destruct l as [|x r] using rev_ind; [cbn; lia|]. rewrite removelast_last, length_app. cbn [length]. lia. }
  unfold art_cls_pop. cbn [cl_au cl_mfa cl_cache]. unfold art_ca_pre. destruct (cl_cache cl0) as [|x0 r0] eqn:Ec.
  - unfold art_cls_refill, art_cls_take. cbn [cl_au cl_mfa cl_cache].
    assert (HM : Z.of_nat (art_refill_n c0) <= art_ic_mc c0).
    { unfold art_refill_n. rewrite Z2Nat.id by (apply Z.div_pos; lia). apply Z.div_le_upper_bound; lia. }
    destruct (art_cls_needs_populate c0 cl0) eqn:NP; cbn [art_cls_populate cl_au cl_mfa cl_free].
    + split.
      * intros _. unfold art_cls_mfa'. set (tot := Z.of_nat (length (cl_free cl0)) + art_cls_new c0 cl0).
        assert (Hnew : 1 <= art_cls_new c0 cl0). { unfold art_cls_new. apply Z.div_le_lower_bound; lia. }
        assert (Htot : 1 <= tot) by (unfold tot; lia).
        destruct (4 * tot <=? cl_mfa cl0) eqn:EL; [apply Z.leb_le in EL; lia|].
        assert (1 <= (4 * tot + 262143) / 262144) by (apply Z.div_le_lower_bound; lia). lia.
      * eapply Z.le_trans; [apply RL|]. rewrite length_skipn. lia.
    + split; [exact T2|]. eapply Z.le_trans; [apply RL|]. rewrite length_skipn. lia.
  - split; [exact T2|]. eapply Z.le_trans; [apply RL|]. rewrite Ec. exact T3.
Qed.

Section Rep.
Variable FSG : Type.
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M M' : word -> option byte).
Variables (Sp n rz qz rs qr qn m8 km : Z) (kb : nat) (b1 : Z).
Let c := AsanTab.class_id (rs + rz).
Let cl := g_cls FSG G c.
Let w := art_ca_cptr c cl.
Let ab := rn_spb rn + c * 2 ^ 32 + w * 16.
Let shb := 2147450880 + 8192 * rn_qs rn + c * 2 ^ 29.
Let u := ab + rz.
Let sz := AsanTab.class_size c.

Hypothesis REP : art_alloc_rep FSG rn G LB M.
Hypothesis Hn : 1 <= n.
Hypothesis Erz16 : rz = 16 * qz.
Hypothesis Hqz : 1 <= qz <= 128.
Hypothesis En : n = 8 * qn + m8.
Hypothesis Hm8 : 0 <= m8 <= 7.
Hypothesis Ers : rs = 8 * qr.
Hypothesis Hnrs : n <= rs.
Hypothesis Hprim : rs + rz <= 65536.
Hypothesis HS : rn_HI rn + 4096 <= Sp - 4096.
Hypothesis Emu : cl_mu cl = 262144 * km.
Hypothesis Edep : g_depot FSG G = Datatypes.S kb.
Hypothesis OUT : art_malloc_out rn M M' Sp n rz qz rs qr qn m8 km kb cl b1.
Hypothesis LIVE : forall p, In p (art_live (g_log FSG G)) ->      (* [comment removed for export] *)
  0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
  /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o)).
Hypothesis OKpre : art_cls_ok c (art_ca_pre c cl).          (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="rn LB M M' Sp n qz qr qn m8 kb b1 ab shb u REP Hn Erz16 Hqz Hnrs Hprim Emu Edep OUT"] Lemma art_mrep_num :
  1 <= c <= 30 /\ rs + rz <= sz /\ 32 <= sz <= 65536 /\ 0 <= km /\ 262144 * km <= 3758096384
  /\ 0 <= w /\ 16 * w + sz <= cl_au (art_ca_pre c cl) /\ cl_au (art_ca_pre c cl) <= cl_mu (art_ca_pre c cl) /\ cl_mu (art_ca_pre c cl) <= 3758096384.
Proof.
  destruct OUT as (_ & _ & _ & _ & _ & OK' & CP & _). fold c in OK', CP. fold w in CP. fold sz in CP.
  pose proof (AsanTab.class_id_ok (rs + rz) ltac:(lia)) as (Hc & Hfit & _). fold c in Hc, Hfit. fold sz in Hfit.
  pose proof (art_class_size_facts c Hc) as (Hsz & _). fold sz in Hsz.
  destruct REP as (_ & _ & _ & (_ & PRIM & _) & _). destruct (PRIM c Hc) as (_ & OK & _). fold cl in OK.
  destruct OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _).
  unfold art_cls_ok in OK'. cbn [art_cls_pop cl_cache cl_free cl_au cl_mu cl_mfa] in OK'. destruct OK' as (_ & (_ & Haumu') & _ & _ & _ & Hmu3' & _).
  destruct CP as (Hw0 & Hwsz & _). repeat split; lia.
Qed.

(* [comment removed for export] *)
Definition art_mrep_W : list (Z * Z) :=
  [ (rn_HI rn, 2 ^ 64 - rn_HI rn); (rn_t rn + 208, 2952); (rn_spb rn + 2 ^ 32, 2 ^ 37 + 4096 - 2 ^ 32);
    (2147450880 + 8192 * rn_qs rn + 2 ^ 29, 2 ^ 34 - 2 ^ 29); (0x211b08, 0x661b28 - 0x211b08); (rn_l2 rn, 2 ^ 20); (rn_blk rn, 2 ^ 23) ].

#[using="LB qn m8 kb b1 ab REP Erz16 Ers OUT"] Lemma art_mrep_lin : forall x, ~ art_malloc_fp_lin Sp (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) (U x) -> M' x = M x.
Proof.
  intros x N. destruct OUT as (_ & FR & _). apply FR. fold c. fold w. fold ab. intros F. apply N.
  destruct REP as (ROK & _). destruct ROK as (GEO & _). geo_open GEO.
  apply (art_malloc_fp_cases Sp (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) c km ab rz n rs (rn_l2 rn) (rn_blk rn) w qz qr (U x) Espb Eris eq_refl Erz16 Ers F).
Qed.

#[using="FSG G LB Sp n rz qz rs qr qn m8 km kb b1 c cl w ab shb u sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_agree : art_agree art_mrep_W M M'.
Proof.
  intros x Hx. apply art_mrep_lin. intros F.
  destruct art_mrep_num as (Hc & Hfit & Hsz & Hkm & Hkm' & Hw0 & Hwsz & Haumu' & Hmu3').
  pose proof (art_mfp_coarse Sp (rn_HI rn) (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) (U x) Hc Hkm Hkm' Hw0 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) HS F) as CO.
  unfold art_mrep_W in Hx. cbn [art_out fst snd] in Hx. unfold art_malloc_coarse in CO. pose proof (u64_range x). lia.
Qed.

(* [comment removed for export] *)
#[using="FSG G LB M REP"] Lemma art_mgap_img : forall a k, 0x10000 <= a -> a + k <= 0x211b08 -> art_gap art_mrep_W a k.
Proof.
  intros a k Ha Hk. destruct REP as (ROK & _ & _ & _ & _ & _ & _ & DEP & _). rok_open ROK. geo_open GEO.
  destruct DEP as (dN & dTF & dST & DG1 & DG2 & DG3 & DG4 & DG5 & _).
  unfold art_mrep_W. cbn [art_gap fst snd]. unfold apart in *. clear - Ha Hk G1 G4 Espb G9 DG1 DG4. repeat split; try exact I; lia.
Qed.
#[using="FSG G LB M REP"] Lemma art_mgap_tls : forall a k, 0x661b28 <= a -> a + k <= 0x696000 -> art_gap art_mrep_W a k.
Proof.
  intros a k Ha Hk. destruct REP as (ROK & _ & _ & _ & _ & _ & _ & DEP & _). rok_open ROK. geo_open GEO.
  destruct DEP as (dN & dTF & dST & DG1 & DG2 & DG3 & DG4 & DG5 & _).
  unfold art_mrep_W. cbn [art_gap fst snd]. unfold apart in *. clear - Ha Hk G1 G4 Espb G9 DG1 DG4. repeat split; try exact I; lia.
Qed.
#[using="FSG G LB M REP"] Lemma art_mgap_thread : forall a k, rn_t rn <= a -> a + k <= rn_t rn + 4096 -> (a + k <= rn_t rn + 208 \/ rn_t rn + 3160 <= a) -> art_gap art_mrep_W a k.
Proof.
  intros a k Ha Hk Hlo. destruct REP as (ROK & _). rok_open ROK. geo_open GEO.
  unfold art_mrep_W. cbn [art_gap fst snd]. unfold apart in *. clear - Ha Hk Hlo G1 G2 G4 G6 Eris Espb G7 G8 G9 G10 G11 Al2t Abt. repeat split; try exact I; lia.
Qed.
#[using="FSG G LB M REP"] Lemma art_mgap_ctx : forall a k, rn_ctx rn <= a -> a + k <= rn_ctx rn + 4096 -> art_gap art_mrep_W a k.
Proof.
  intros a k Ha Hk. destruct REP as (ROK & _). rok_open ROK. geo_open GEO.
  unfold art_mrep_W. cbn [art_gap fst snd]. unfold apart in *. clear - Ha Hk G1 G2 G4 G6 Eris Espb G13 G14 G15 G16 G17 G18 Al2c Abc. repeat split; try exact I; lia.
Qed.

#[using="FSG rn G LB Sp n rz qz rs qr qn m8 km kb b1 c cl w ab shb u sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_cell_img : forall a (k : nat) v, 0x10000 <= a -> a + Z.of_nat k <= 0x211b08 -> cellA M a k v -> cellA M' a k v.
Proof. intros a k v Ha Hk C. apply (art_cell_tr art_mrep_W M M' a k v art_mrep_agree (art_mgap_img a _ Ha Hk)); [lia|lia|exact C]. Qed.

(* [comment removed for export] *)
#[using="FSG G LB M Sp n rz qz rs qr qn m8 km kb b1 c cl w ab shb u sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_statics : art_rt_statics rn M'.
Proof.
  pose proof REP as (ROK & ST & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct ST as (PC & L & T & RO & RZ & DR & TG & CS).
  assert (OI : forall z, 0x10000 <= z < 0x211b08 -> art_out art_mrep_W z).
  { intros z Hz. apply (art_gap_out _ z 1); [apply art_mgap_img; lia|lia]. }
  pose proof T as (_ & _ & _ & _ & _ & TR).
  unfold art_rt_statics.
  split; [eapply art_prim_consts_tr; [exact art_mrep_agree|exact OI|exact PC]|].
  split; [eapply art_layout_fp; [exact art_mrep_agree|exact OI|exact L]|].
  split. { apply (art_tsd_tr _ M M' _ _ _ _ _ art_mrep_agree); [apply art_mgap_img; lia|apply art_mgap_tls; lia|apply art_mgap_tls; lia|apply art_mgap_ctx; lia|exact T]. }
  split. { unfold art_alloc_rodata in *. destruct RO as (a1 & a2 & a3). repeat split; apply art_mrep_cell_img; first [assumption|cbn; lia]. }
  split. { unfold art_rz_rodata in *. destruct RZ as (a1 & a2 & a3). repeat split; apply art_mrep_cell_img; first [assumption|cbn; lia]. }
  split. { apply (DRoD_frame M M' DR). intros x Hx. apply art_mrep_agree. apply OI. exact Hx. }
  split. { destruct TG as (GN & T1 & T2). split; [|split].
           - intros a Ha. assert (EU : U (Z_to_bv 64 a) = a) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); apply Z.mod_small; lia).
             rewrite (art_mrep_agree (Z_to_bv 64 a)); [exact (GN a Ha)|]. rewrite EU. apply OI. lia.
           - apply (art_cell_tr art_mrep_W M M' 0x673cf8 8%nat _ art_mrep_agree (art_mgap_tls 0x673cf8 8 ltac:(lia) ltac:(lia))); [lia|cbn; lia|exact T1].
           - apply (art_cell_tr art_mrep_W M M' 0x673d28 8%nat _ art_mrep_agree (art_mgap_tls 0x673d28 8 ltac:(lia) ltac:(lia))); [lia|cbn; lia|exact T2]. }
  decompose [and] CS. repeat split; apply art_mrep_cell_img; first [assumption|cbn; lia].
Qed.

#[using="FSG G LB M Sp n rz qz rs qr qn m8 km kb b1 c cl w ab shb u sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_thread : art_rt_thread rn M'.
Proof.
  pose proof REP as (ROK & _ & TH & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct TH as (Wt & C1 & C2 & C3 & C4 & C5 & C6 & C7). destruct OUT as (GR & _).
  assert (TT : forall a (k : nat) v, rn_t rn <= a -> a + Z.of_nat k <= rn_t rn + 4096 -> (a + Z.of_nat k <= rn_t rn + 208 \/ rn_t rn + 3160 <= a) -> cellA M a k v -> cellA M' a k v).
  { intros a k v Ha Hk Hlo C. apply (art_cell_tr art_mrep_W M M' a k v art_mrep_agree (art_mgap_thread a _ Ha Hk Hlo)); [lia|lia|exact C]. }
  unfold art_rt_thread. split; [eapply wr_grows; [exact GR|exact Wt]|].
  split; [apply TT; [lia|cbn; lia|cbn; lia|exact C1]|].
  split. { apply (art_cell_tr art_mrep_W M M' (rn_ctx rn + 8) 4%nat 0 art_mrep_agree (art_mgap_ctx (rn_ctx rn + 8) 4 ltac:(lia) ltac:(lia))); [lia|cbn; lia|exact C2]. }
  split; [apply TT; [lia|cbn; lia|cbn; lia|exact C3]|]. split; [apply TT; [lia|cbn; lia|cbn; lia|exact C4]|].
  split; [apply TT; [lia|cbn; lia|cbn; lia|exact C5]|]. split; [apply TT; [lia|cbn; lia|cbn; lia|exact C6]|].
  apply (art_cell_tr art_mrep_W M M' (rn_tp rn + rn_loff rn) 4%nat 0 art_mrep_agree (art_mgap_tls (rn_tp rn + rn_loff rn) 4 ltac:(lia) ltac:(lia))); [lia|cbn; lia|exact C7].
Qed.

#[local] Abbreviation G' := (art_gs_malloc G (rn_spb rn) c w u n kb).

#[using="LB M Sp qz qr qn m8 km b1 shb sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_ia : art_rt_ia FSG G' M'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & IA & _). destruct IA as (C1 & C3 & C4).
  unfold art_rt_ia. cbn [art_gs_malloc g_ia g_qt g_qg].
  split; [apply art_mrep_cell_img; [lia|cbn; lia|exact C1]|].
  split; [|exact C4]. intros E k Hk. apply art_mrep_cell_img; [lia|cbn; lia|exact (C3 E k Hk)].
Qed.

#[using="M Sp qz qr qn m8 km b1 OUT"] Lemma art_mrep_depot : art_rt_depot FSG rn G' M'.
Proof. unfold art_rt_depot. cbn [art_gs_malloc g_depot]. destruct OUT as (_ & _ & DI & _). exact DI. Qed.

(* [comment removed for export] *)
#[using="FSG G LB Sp n qz qr qn m8 km kb b1 cl w ab shb u sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_out_cache : forall c0 x, 1 <= c0 <= 31 -> c0 <> c ->
  (rn_t rn + 208 + 80 * c0 <= U x < rn_t rn + 208 + 80 * c0 + 4 \/ rn_t rn + 208 + 80 * c0 + 16 <= U x < rn_t rn + 208 + 80 * c0 + 80) -> M' x = M x.
Proof.
  intros c0 x Hc0 Ne Hx. apply art_mrep_lin.
  destruct art_mrep_num as (Hc & Hfit & Hsz & Hkm & Hkm' & Hw0 & Hwsz & Haumu' & Hmu3').
  pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
  apply (art_mfp_out_cache Sp (rn_HI rn) (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) c0 (U x) Hc Hc0 Ne Hw0 ltac:(lia) ltac:(lia) ltac:(lia) Hkm Hkm'
           ltac:(lia) ltac:(lia) HS ltac:(lia) ltac:(lia) G1 Espb G4 G8 G11); [unfold apart; clear - G10; lia|unfold apart; clear - G9; lia|exact Al2t|exact Abt|exact Hx].
Qed.

#[using="FSG G LB Sp n qz qr qn m8 km kb b1 cl w ab shb u sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_out_class : forall c0 x, 1 <= c0 <= 30 -> c0 <> c ->
  (rn_spb rn + c0 * 2 ^ 32 <= U x < rn_spb rn + c0 * 2 ^ 32 + 2 ^ 32
   \/ 2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29 <= U x < 2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29 + 2 ^ 29
   \/ rn_spb rn + 2 ^ 37 + 128 * c0 <= U x < rn_spb rn + 2 ^ 37 + 128 * c0 + 128) -> M' x = M x.
Proof.
  intros c0 x Hc0 Ne Hx. apply art_mrep_lin.
  destruct art_mrep_num as (Hc & Hfit & Hsz & Hkm & Hkm' & Hw0 & Hwsz & Haumu' & Hmu3').
  pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
  apply (art_mfp_out_class Sp (rn_HI rn) (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) c0 (U x) Hc Hc0 Ne Hkm Hkm' Hw0 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(lia) ltac:(lia) HS G1 Espb G4 ltac:(lia) ltac:(lia) G11); [unfold apart; clear - G10; lia|exact Al2k|exact Al2s|exact Abk|exact Abs|exact Hx].
Qed.

(* [comment removed for export] *)
#[using="LB M Sp qz qr qn m8 km b1 shb sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_primary : art_rt_primary FSG rn G' M'.
Proof.
  pose proof REP as (ROK & _ & _ & PRIM & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct PRIM as (PH & PRIM & Wsh). destruct OUT as (GR & _ & _ & PH' & RC' & OK' & _). fold c in RC', OK'. fold cl in RC', OK'.
  unfold art_rt_primary. cbn [art_gs_malloc g_inited g_cls].
  split; [exact PH'|]. split; [|eapply wr_grows; [exact GR|exact Wsh]].
  intros c0 Hc0. destruct (Z.eqb_spec c0 c) as [->|Ne].
  - split; [exact RC'|]. split; [exact OK'|]. split; [intros _; reflexivity|].
    split; [|intros _; reflexivity]. destruct OK' as (_ & _ & _ & Hk & _). exact Hk.
  - destruct (PRIM c0 Hc0) as (RC0 & OK0 & _ & Hk0 & _). split; [|split; [exact OK0|split; [intros _; reflexivity|split; [exact Hk0|intros _; reflexivity]]]].
    destruct OK0 as (Hl16 & _ & _ & _ & _ & _ & _ & (_ & Hmfa1) & Hnf4 & _).
    destruct RC0 as [[C0 CW] (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu)].
    assert (TC : forall a (k : nat) v, (rn_t rn + 208 + 80 * c0 <= a /\ a + Z.of_nat k <= rn_t rn + 208 + 80 * c0 + 4 \/ rn_t rn + 208 + 80 * c0 + 16 <= a /\ a + Z.of_nat k <= rn_t rn + 208 + 80 * c0 + 80) ->
                cellA M a k v -> cellA M' a k v).
    { intros a k v Ha C. apply (art_cell_agree _ M M'); [|clear - Ha G7 Hc0; lia|clear - Ha G8 G2 Hc0; lia|exact C]. intros x Hx. apply (art_mrep_out_cache c0 x ltac:(lia) Ne). clear - Ha Hx. lia. }
    assert (TR : forall a (k : nat) v, (rn_spb rn + c0 * 2 ^ 32 <= a /\ a + Z.of_nat k <= rn_spb rn + c0 * 2 ^ 32 + 2 ^ 32 \/ rn_spb rn + 2 ^ 37 + 128 * c0 <= a /\ a + Z.of_nat k <= rn_spb rn + 2 ^ 37 + 128 * c0 + 128) ->
                cellA M a k v -> cellA M' a k v).
    { intros a k v Ha C. apply (art_cell_agree _ M M'); [|clear - Ha G4 Hc0; lia|clear - Ha G6 Eris G2 Hc0; lia|exact C]. intros x Hx. apply (art_mrep_out_class c0 x Hc0 Ne). clear - Ha Hx. lia. }
    rewrite Eris in *.
    split; [split|].
    + apply TC; [left; cbn; lia|exact C0].
    + intros j Hj. apply TC; [right; cbn; clear - Hj Hl16; lia|exact (CW j Hj)].
    + unfold art_region_rep.
      split; [apply TR; [right; cbn; lia|exact Rmx]|]. split; [apply TR; [right; cbn; lia|exact Rnf]|]. split; [apply TR; [right; cbn; lia|exact Rmfa]|].
      split; [apply TR; [right; cbn; lia|exact Rau]|]. split; [apply TR; [right; cbn; lia|exact Ram]|]. split; [apply TR; [right; cbn; lia|exact Rmu]|].
      split; [apply TR; [right; cbn; lia|exact Rmm]|]. split; [apply TR; [right; cbn; lia|exact Rna]|]. split; [apply TR; [right; cbn; lia|exact Rnfr]|].
      split. { intros j Hj. apply TR; [left; cbn; clear - Hj Hnf4 Hmfa1; lia|exact (Rfa j Hj)]. }
      split; [eapply wr_grows; [exact GR|exact Wr]|]. split; [eapply wr_grows; [exact GR|exact Wfa]|eapply wr_grows; [exact GR|exact Wu]].
Qed.

(* [comment removed for export] *)
#[using="FSG G LB Sp n qz qr qn m8 km kb b1 cl w ab shb u sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_eq_class : forall c0 a, 1 <= c0 <= 30 -> c0 <> c ->
  (rn_spb rn + c0 * 2 ^ 32 <= a < rn_spb rn + c0 * 2 ^ 32 + 2 ^ 32
   \/ 2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29 <= a < 2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29 + 2 ^ 29) ->
  M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros c0 a Hc0 Ne Ha. apply (art_mrep_out_class c0 _ Hc0 Ne).
  pose proof REP as (ROK & _). destruct ROK as (GEO & _). geo_open GEO.
  rewrite art_u_lit by (clear - Ha G4 Espb G6 Eris G2 Hc0; lia). clear - Ha. lia.
Qed.

#[using="LB Sp n qz qr qn m8 km kb b1 ab u REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_eq_chunk : forall w0 a, art_cptr_ok sz (cl_au cl) w0 -> w0 <> w ->
  (rn_spb rn + c * 2 ^ 32 + 16 * w0 <= a < rn_spb rn + c * 2 ^ 32 + 16 * w0 + sz
   \/ 8 * (a - shb) + 8 <= 16 * w0 + sz /\ shb + 2 * w0 <= a) ->
  M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros w0 a V0 Ne Ha. apply art_mrep_lin.
  destruct art_mrep_num as (Hc & Hfit & Hsz & Hkm & Hkm' & Hw0 & Hwsz & Haumu' & Hmu3').
  pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _). rok_open ROK. geo_open GEO.
  destruct (PRIM c Hc) as (_ & OK & _). fold cl in OK. pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _).
  destruct OUT as (_ & _ & _ & _ & _ & OK' & CP & _). fold c in OK', CP. fold cl in OK', CP. fold w in CP. fold sz in CP.
  assert (V0' : art_cptr_ok sz (cl_au (art_ca_pre c cl)) w0).
  { eapply art_cptr_mono; [|exact V0]. destruct (art_ca_pre_au c cl) as [E|(_ & _ & E)]; rewrite E; [lia|].
    assert (0 <= art_cls_new c cl * AsanTab.class_size c); [|lia]. apply Z.mul_nonneg_nonneg; [|fold sz; lia]. unfold art_cls_new. apply Z.div_pos; fold sz; lia. }
  pose proof (art_cptr_apart sz _ w w0 ltac:(lia) CP V0' ltac:(intros E; apply Ne; symmetry; exact E)) as AP.
  destruct V0 as (V00 & V01 & _).
  assert (Ua : U (Z_to_bv 64 a) = a).
  { apply art_u_lit. unfold shb in Ha. clear - Ha G4 Espb G6 Eris G2 Hc V00 V01 Haumu Hmu3 Hsz. lia. }
  rewrite Ua.
  apply (art_mfp_out_chunk Sp (rn_HI rn) (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) sz w0 a Hc Hkm Hkm' Hw0 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(lia) ltac:(lia) ltac:(lia) V00 ltac:(lia) AP HS G1 Espb G4 ltac:(lia) ltac:(lia) G11); [unfold apart; clear - G10; lia|exact Al2k|exact Al2s|exact Abk|exact Abs|].
  unfold shb in Ha. exact Ha.
Qed.

#[using="LB Sp n qz qr qn m8 km kb b1 ab u REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_eqw_chunk : forall w0 (x : word), art_cptr_ok sz (cl_au cl) w0 -> w0 <> w ->
  (rn_spb rn + c * 2 ^ 32 + 16 * w0 <= U x < rn_spb rn + c * 2 ^ 32 + 16 * w0 + sz
   \/ 8 * (U x - shb) + 8 <= 16 * w0 + sz /\ shb + 2 * w0 <= U x) -> M' x = M x.
Proof. intros w0 x V Ne Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply (art_mrep_eq_chunk w0 (U x) V Ne Hx). Qed.

(* [comment removed for export] *)
#[using="FSG rn G rz rs kb c cl w ab shb u sz Edep"] Lemma art_blk_shadow_in : forall qs0 c0 w0 sz0 u0 n0 j, sz0 mod 16 = 0 -> 0 < n0 ->
  65536 * qs0 + c0 * 2 ^ 32 + 16 * w0 + 16 <= u0 -> u0 + n0 <= 65536 * qs0 + c0 * 2 ^ 32 + 16 * w0 + sz0 ->
  (j < n0 / 8 \/ (j = n0 / 8 /\ n0 mod 8 <> 0)) -> 0 <= j ->
  let a := HeapIfaceA.S u0 + j in let shb0 := 2147450880 + 8192 * qs0 + c0 * 2 ^ 29 in
  8 * (a - shb0) + 8 <= 16 * w0 + sz0 /\ shb0 + 2 * w0 <= a.
Proof.
  intros qs0 c0 w0 sz0 u0 n0 j Hsz16 Hn0 Hlo Hhi Hj Hj0 a shb0.
  assert (Es : sz0 = 16 * (sz0 / 16)). { pose proof (Z.div_mod sz0 16 ltac:(lia)) as D. rewrite Hsz16 in D. lia. }
  pose proof (art_S_blk_hi u0 n0 j Hn0 Hj) as H1.
  pose proof (art_S_lt (u0 + n0 - 1) (8192 * qs0 + c0 * 2 ^ 29 + 2 * w0 + 2 * (sz0 / 16)) ltac:(lia)) as H2.
  pose proof (art_S_ge u0 (8192 * qs0 + c0 * 2 ^ 29 + 2 * w0 + 2) ltac:(lia)) as H3.
  unfold a, shb0. split; lia.
Qed.

(* [comment removed for export] *)
#[using="M Sp qz qr qn m8 km b1 shb sz REP Hn Erz16 Hqz En Hm8 Ers Hnrs Hprim HS Emu Edep OUT OKpre"] Lemma art_mrep_chunks : art_rt_chunks FSG rn G' ((u, n) :: LB) M'.
Proof.
  pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & CH & _). pose proof ROK as ROK'. rok_open ROK'. pose proof GEO as GEO'. geo_open GEO'.
  destruct art_mrep_num as (Hc & Hfit & Hsz & Hkm & Hkm' & Hw0 & Hwsz & Haumu' & Hmu3').
  intros c0 Hc0. specialize (CH c0 Hc0). cbv zeta in CH. cbv zeta. destruct CH as (I & II & II' & III).
  cbn [art_gs_malloc g_cls g_st g_qt g_qg].
  destruct (Z.eqb_spec c0 c) as [Ec0|Ne]; cbn [andb].
  - (* [comment removed for export] *)
    subst c0. fold cl in I, II, II', III. fold sz in II', III |- *.
    destruct (PRIM c Hc) as (_ & OK & _). fold cl in OK. pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & Hka & Hmu3 & _). fold sz in Hka.
    pose proof (art_class_size_facts c Hc) as (_ & Hsz16). fold sz in Hsz16.
    destruct OUT as (GR & _ & _ & _ & _ & OK' & CP & Hb1 & Hty & CL1 & CL3 & CL4 & CL2 & SAB & SHZ & SHP & PSH & LCH).
    fold c in OK', CP, CL1, CL3, CL4, CL2, SAB, SHZ, SHP, PSH, LCH. fold cl in OK', CP, PSH, LCH. fold w in CP, CL1, CL3, CL4, CL2, SAB, SHZ, SHP, PSH, LCH. fold sz in CP.
    fold ab in CL1, CL3, CL4, CL2, LCH. fold shb in SAB, SHZ, SHP, PSH.
    cbn [art_cls_pop cl_cache cl_free cl_au cl_mu]. fold cl.
    assert (Hau' : cl_au cl <= cl_au (art_ca_pre c cl)).
    { destruct (art_ca_pre_au c cl) as [E|(_ & _ & E)]; rewrite E; [lia|].
      assert (0 <= art_cls_new c cl * AsanTab.class_size c); [|lia]. apply Z.mul_nonneg_nonneg; [|fold sz; lia]. unfold art_cls_new. apply Z.div_pos; fold sz; lia. }
    assert (BYTE : forall y v, 0 <= y < 2 ^ 32 -> 0 <= v < 256 -> cellA M' (shb + y) 1 v -> byte_at M' (shb + y) v).
    { intros y v Hy Hv C. apply art_byte_of_cell1; [right; unfold shb; clear - Hy G4 Espb Hc; lia|unfold shb; clear - Hy G4 Espb G6 Eris G2 Hc; lia|exact Hv|exact C]. }
    assert (SHC : forall y v, 0 <= y -> y < 32768 * km -> (y < 2 * w + 2 * qz \/ 2 * w + 2 * qz + qr <= y) -> byte_at M (shb + y) v -> byte_at M' (shb + y) v).
    { intros y v Hy Hy' Hyu B. apply (art_byte_at_eq M M'); [|exact B]. apply art_mrep_lin.
      rewrite art_u_lit by (unfold shb; clear - Hy Hy' Hkm' G4 Espb G6 Eris G2 Hc; lia). unfold shb.
      apply (art_mfp_out_shc Sp (rn_HI rn) (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) y Hc Hkm Hkm' Hw0 ltac:(lia) ltac:(lia) ltac:(lia) HS G1 Espb G4
               ltac:(lia) ltac:(lia)); [unfold apart; clear - G10; lia|exact Al2s|exact Abs|exact Hy|exact Hy'|exact Hyu]. }
    assert (ES : forall y, HeapIfaceA.S (rn_spb rn + c * 2 ^ 32 + 8 * y) = shb + y). { intros y. rewrite Espb. unfold shb. apply art_S_lin. }
    (* [comment removed for export] *)
    split.
    { (* [comment removed for export] *)
      intros x Hx Hx8. assert (Ex : x = 8 * (x / 8)). { pose proof (Z.div_mod x 8 ltac:(lia)) as D. rewrite Hx8 in D. lia. }
      rewrite Ex, ES. set (y := x / 8) in *.
      assert (Hyu : 2 * w + 2 * qz + qr <= y) by lia.
      destruct (Z_lt_ge_dec x (cl_mu cl)) as [Lo|Hi].
      - apply SHC; [lia|lia|right; exact Hyu|]. rewrite <- ES, <- Ex. apply I; [lia|exact Hx8].
      - destruct (art_ca_pre_mu_cases c cl) as [(E & _)|(E1 & E2 & E3)]; [rewrite E in Hx; lia|]. rewrite E3 in Hx.
        pose proof (PSH E1 E2 (y - 32768 * km) ltac:(lia) ltac:(lia)) as C.
        replace (shb + 32768 * km + (y - 32768 * km)) with (shb + y) in C by lia. apply BYTE; [lia|lia|exact C]. }
    split.
    { (* [comment removed for export] *)
      intros w0 Hin. destruct (art_malloc_in_free c cl Hc OK w0 OKpre Hin) as (Nw & [Hold|Hnew]); fold w in Nw; try fold sz in Hnew.
      - rewrite (proj2 (Z.eqb_neq w0 w) Nw). exact (II w0 Hold).
      - rewrite (proj2 (Z.eqb_neq w0 w) Nw). exact (II' w0 Hnew). }
    split.
    { (* [comment removed for export] *)
      intros w0 NV'. destruct (Z.eqb_spec w0 w) as [->|Nw]; [contradiction|]. apply II'. intros V. apply NV'. eapply art_cptr_mono; [exact Hau'|exact V]. }
    (* [comment removed for export] *)
    intros w0 V'. destruct (Z.eqb_spec w0 w) as [Ew|Nw].
    { (* [comment removed for export] *)
      subst w0. split; [left; reflexivity|]. unfold u. split; [unfold ab; lia|]. split; [unfold ab; lia|].
      split. { exists b1. split; [exact Hb1|]. split; [exact Hty|].
               split. { replace (2 + 256 * b1) with (2 + 256 * b1) by reflexivity.
                        apply (art_hdr_word M' (ab + rz - 16) 2 b1); [unfold ab; lia|unfold ab; lia|lia|exact Hb1|exact CL1| |].
                        - replace (ab + rz - 16 + 1) with (ab + rz - 15) by lia. exact CL3.
                        - replace (ab + rz - 16 + 2) with (ab + rz - 14) by lia. exact CL4. }
               split; [exact CL2|lia]. }
      assert (ESu : HeapIfaceA.S (ab + rz) = shb + (2 * w + 2 * qz)). { rewrite <- ES. f_equal. unfold ab. lia. }
      assert (Hqn : n / 8 = qn). { symmetry. apply (Z.div_unique _ 8 qn m8); lia. }
      assert (Hmod : n mod 8 = m8). { rewrite (Z.mod_eq n 8) by lia. rewrite Hqn. lia. }
      split.
      { left. split.
        - intros j Hj. rewrite ESu. replace (shb + (2 * w + 2 * qz) + j) with (shb + (2 * w + 2 * qz + j)) by lia. apply BYTE; [lia|lia|].
          replace (shb + (2 * w + 2 * qz + j)) with (shb + 2 * w + 2 * qz + j) by lia. apply SHZ. lia.
        - intros Hm. rewrite ESu, Hqn, Hmod. replace (shb + (2 * w + 2 * qz) + qn) with (shb + (2 * w + 2 * qz + qn)) by lia. apply BYTE; [lia|lia|].
          replace (shb + (2 * w + 2 * qz + qn)) with (shb + 2 * w + 2 * qz + qn) by lia. apply SHP. lia. }
      split.
      { replace (rn_spb rn + c * 2 ^ 32 + 16 * w) with (rn_spb rn + c * 2 ^ 32 + 8 * (2 * w)) by lia. rewrite ES. apply BYTE; [lia|lia|exact SAB]. }
      unfold art_lch. intros NE. replace (rn_spb rn + c * 2 ^ 32 + 16 * w) with ab by (unfold ab; lia). apply LCH. intros E16. apply NE. unfold ab. lia. }
    destruct (art_cptr_ok_dec sz (cl_au cl) w0 ltac:(lia)) as [V|NV].
    + (* [comment removed for export] *)
      specialize (III w0 V). pose proof V as (V0 & V1 & _).
      assert (TB : byte_at M (HeapIfaceA.S (rn_spb rn + c * 2 ^ 32 + 16 * w0)) 250 -> byte_at M' (HeapIfaceA.S (rn_spb rn + c * 2 ^ 32 + 16 * w0)) 250).
      { replace (rn_spb rn + c * 2 ^ 32 + 16 * w0) with (rn_spb rn + c * 2 ^ 32 + 8 * (2 * w0)) by lia. rewrite ES. intros B.
        apply (art_byte_at_eq M M'); [|exact B]. apply (art_mrep_eq_chunk w0 _ V Nw). right. lia. }
      assert (THDR : forall u0 n0 st, rn_spb rn + c * 2 ^ 32 + 16 * w0 + 16 <= u0 -> u0 + n0 <= rn_spb rn + c * 2 ^ 32 + 16 * w0 + sz ->
                       art_chunk_hdr M u0 n0 st -> art_chunk_hdr M' u0 n0 st).
      { intros u0 n0 st L1 L2 (b & Hb & Hbt & C1 & C2 & Hn0). exists b. split; [exact Hb|]. split; [exact Hbt|]. split; [|split; [|exact Hn0]].
        - apply (art_cell_agree _ M M'); [intros x Hx; apply (art_mrep_eqw_chunk w0 x V Nw); left; cbn in Hx; lia|lia|cbn; lia|exact C1].
        - apply (art_cell_agree _ M M'); [intros x Hx; apply (art_mrep_eqw_chunk w0 x V Nw); left; cbn in Hx; lia|lia|cbn; lia|exact C2]. }
      assert (TSH : forall u0 n0, 0 < n0 -> rn_spb rn + c * 2 ^ 32 + 16 * w0 + 16 <= u0 -> u0 + n0 <= rn_spb rn + c * 2 ^ 32 + 16 * w0 + sz ->
                      HAJ.shadow_blkR M u0 n0 -> HAJ.shadow_blkR M' u0 n0).
      { intros u0 n0 Hn0 L1 L2 SB0. apply (shadow_blkR_tby M M' u0 n0 Hn0); [|exact SB0]. intros j Hj0 Hjc v Bv. apply (art_byte_at_eq M M'); [|exact Bv].
        destruct Hjc as [Hj|(Ej & Hm)].
        - assert (Hj' : 0 <= j < n0 / 8) by lia. clear Hj. rename Hj' into Hj. apply (art_mrep_eq_chunk w0 _ V Nw). right.
          pose proof (art_blk_shadow_in (rn_qs rn) c w0 sz u0 n0 j Hsz16 Hn0 ltac:(lia) ltac:(lia) ltac:(left; lia) ltac:(lia)) as B. cbv zeta in B. unfold shb. exact B.
        - subst j. apply (art_mrep_eq_chunk w0 _ V Nw). right.
          pose proof (art_blk_shadow_in (rn_qs rn) c w0 sz u0 n0 (n0 / 8) Hsz16 Hn0 ltac:(lia) ltac:(lia) ltac:(right; split; [reflexivity|exact Hm]) ltac:(apply Z.div_pos; lia)) as B.
          cbv zeta in B. unfold shb. exact B. }
      assert (TLCH : forall u0, art_lch M (rn_spb rn + c * 2 ^ 32 + 16 * w0) u0 -> art_lch M' (rn_spb rn + c * 2 ^ 32 + 16 * w0) u0).
      { intros u0 LC NE. destruct (LC NE) as (C1 & C2). split.
        - apply (art_cell_agree _ M M'); [intros x Hx; apply (art_mrep_eqw_chunk w0 x V Nw); left; cbn in Hx; lia|lia|cbn; lia|exact C1].
        - apply (art_cell_agree _ M M'); [intros x Hx; apply (art_mrep_eqw_chunk w0 x V Nw); left; cbn in Hx; lia|lia|cbn; lia|exact C2]. }
      destruct (g_st FSG G c w0) as [|u0 n0|u0 n0|].
      * destruct III as (I1 & I2). split; [|exact (TB I2)]. apply (art_malloc_free_in c cl Hc OK w0 OKpre V' Nw). intros _. exact I1.
      * destruct III as (J1 & J2 & J3 & J4 & J5 & J6 & J7). pose proof J4 as (_ & _ & _ & _ & _ & Hn0).
        split; [right; exact J1|]. split; [exact J2|]. split; [exact J3|]. split; [exact (THDR u0 n0 2 J2 J3 J4)|]. split; [apply TSH; [lia|exact J2|exact J3|exact J5]|]. split; [exact (TB J6)|exact (TLCH u0 J7)].
      * destruct III as (J2 & J3 & J4 & J5 & J6 & J7). split; [exact J2|]. split; [exact J3|]. split; [exact (THDR u0 n0 3 J2 J3 J4)|]. split; [exact J5|]. split; [exact (TB J6)|exact (TLCH u0 J7)].
      * exact III.
    + (* [comment removed for export] *)
      rewrite (II' w0 NV). split; [apply (art_malloc_free_in c cl Hc OK w0 OKpre V' Nw); intros V; contradiction|].
      pose proof (art_cptr_new_lo sz (cl_au cl) _ w0 ltac:(lia) Hka V' NV) as Hlo. pose proof V' as (V0 & V1 & _).
      pose proof (art_cptr_apart sz _ w w0 ltac:(lia) CP V' ltac:(intros E; apply Nw; symmetry; exact E)) as AP.
      replace (rn_spb rn + c * 2 ^ 32 + 16 * w0) with (rn_spb rn + c * 2 ^ 32 + 8 * (2 * w0)) by lia. rewrite ES.
      assert (Hyu : 2 * w0 < 2 * w + 2 * qz \/ 2 * w + 2 * qz + qr <= 2 * w0) by lia.
      destruct (Z_lt_ge_dec (16 * w0) (cl_mu cl)) as [Lo|Hi].
      * apply SHC; [lia|lia|exact Hyu|]. rewrite <- ES. replace (8 * (2 * w0)) with (16 * w0) by lia. apply I; [lia|]. replace (16 * w0) with (2 * w0 * 8) by lia. apply Z_mod_mult.
      * destruct (art_ca_pre_mu_cases c cl) as [(E & _)|(E1 & E2 & E3)]; [rewrite E in Haumu'; lia|].
        pose proof (PSH E1 E2 (2 * w0 - 32768 * km) ltac:(lia) ltac:(lia)) as C.
        replace (shb + 32768 * km + (2 * w0 - 32768 * km)) with (shb + 2 * w0) in C by lia. apply BYTE; [lia|lia|exact C].
  - (* [comment removed for export] *)
    pose proof (art_class_size_facts c0 Hc0) as (Hsz0 & Hsz016).
    destruct (PRIM c0 Hc0) as (_ & OK0 & _). pose proof OK0 as (_ & (Hau0 & Haumu0) & _ & _ & _ & Hmu30 & _).
    assert (TBx : forall x, 0 <= x < 3758096384 -> byte_at M (HeapIfaceA.S (rn_spb rn + c0 * 2 ^ 32 + x)) 250 -> byte_at M' (HeapIfaceA.S (rn_spb rn + c0 * 2 ^ 32 + x)) 250).
    { intros x Hx B. apply (art_byte_at_eq M M'); [|exact B]. apply (art_mrep_eq_class c0 _ Hc0 Ne). right.
      pose proof (art_S_ge (rn_spb rn + c0 * 2 ^ 32 + x) (8192 * rn_qs rn + c0 * 2 ^ 29) ltac:(lia)) as B1.
      pose proof (art_S_lt (rn_spb rn + c0 * 2 ^ 32 + x) (8192 * rn_qs rn + c0 * 2 ^ 29 + 2 ^ 29) ltac:(lia)) as B2. lia. }
    split; [intros x Hx Hx8; apply TBx; [lia|exact (I x Hx Hx8)]|]. split; [exact II|]. split; [exact II'|].
    intros w0 V. specialize (III w0 V). pose proof V as (V0 & V1 & _).
    assert (THDR : forall u0 n0 st, rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + 16 <= u0 -> u0 + n0 <= rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + AsanTab.class_size c0 ->
                     art_chunk_hdr M u0 n0 st -> art_chunk_hdr M' u0 n0 st).
    { intros u0 n0 st L1 L2 (b & Hb & Hbt & C1 & C2 & Hn0). exists b. split; [exact Hb|]. split; [exact Hbt|]. split; [|split; [|exact Hn0]].
      - apply (art_cell_agree _ M M'); [intros x Hx; apply (art_mrep_out_class c0 x Hc0 Ne); left; cbn in Hx; lia|lia|cbn; lia|exact C1].
      - apply (art_cell_agree _ M M'); [intros x Hx; apply (art_mrep_out_class c0 x Hc0 Ne); left; cbn in Hx; lia|lia|cbn; lia|exact C2]. }
    assert (TSH : forall u0 n0, 0 < n0 -> rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + 16 <= u0 -> u0 + n0 <= rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + AsanTab.class_size c0 ->
                    HAJ.shadow_blkR M u0 n0 -> HAJ.shadow_blkR M' u0 n0).
    { intros u0 n0 Hn0 L1 L2 SB0. apply (shadow_blkR_tby M M' u0 n0 Hn0); [|exact SB0]. intros j Hj0 Hjc v Bv. apply (art_byte_at_eq M M'); [|exact Bv].
      destruct Hjc as [Hj|(Ej & Hm)].
      - assert (Hj' : 0 <= j < n0 / 8) by lia. clear Hj. rename Hj' into Hj. apply (art_mrep_eq_class c0 _ Hc0 Ne). right.
        pose proof (art_blk_shadow_in (rn_qs rn) c0 w0 _ u0 n0 j Hsz016 Hn0 ltac:(lia) ltac:(lia) ltac:(left; lia) ltac:(lia)) as B. cbv zeta in B. lia.
      - subst j. apply (art_mrep_eq_class c0 _ Hc0 Ne). right.
        pose proof (art_blk_shadow_in (rn_qs rn) c0 w0 _ u0 n0 (n0 / 8) Hsz016 Hn0 ltac:(lia) ltac:(lia) ltac:(right; split; [reflexivity|exact Hm]) ltac:(apply Z.div_pos; lia)) as B.
        cbv zeta in B. lia. }
    assert (TLCH : forall u0, art_lch M (rn_spb rn + c0 * 2 ^ 32 + 16 * w0) u0 -> art_lch M' (rn_spb rn + c0 * 2 ^ 32 + 16 * w0) u0).
    { intros u0 LC NE. destruct (LC NE) as (C1 & C2). split.
      - apply (art_cell_agree _ M M'); [intros x Hx; apply (art_mrep_out_class c0 x Hc0 Ne); left; cbn in Hx; lia|lia|cbn; lia|exact C1].
      - apply (art_cell_agree _ M M'); [intros x Hx; apply (art_mrep_out_class c0 x Hc0 Ne); left; cbn in Hx; lia|lia|cbn; lia|exact C2]. }
    destruct (g_st FSG G c0 w0) as [|u0 n0|u0 n0|].
    + destruct III as (I1 & I2). split; [exact I1|apply TBx; [lia|exact I2]].
    + destruct III as (J1 & J2 & J3 & J4 & J5 & J6 & J7). pose proof J4 as (_ & _ & _ & _ & _ & Hn0).
      split; [right; exact J1|]. split; [exact J2|]. split; [exact J3|]. split; [exact (THDR u0 n0 2 J2 J3 J4)|]. split; [apply TSH; [lia|exact J2|exact J3|exact J5]|]. split; [apply TBx; [lia|exact J6]|exact (TLCH u0 J7)].
    + destruct III as (J2 & J3 & J4 & J5 & J6 & J7). split; [exact J2|]. split; [exact J3|]. split; [exact (THDR u0 n0 3 J2 J3 J4)|]. split; [exact J5|]. split; [apply TBx; [lia|exact J6]|exact (TLCH u0 J7)].
    + exact III.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_live_ca_events : forall log spb0 c0 cl0, art_live (log ++ art_ca_events spb0 c0 cl0) = art_live log.
Proof.
  intros log spb0 c0 cl0. unfold art_ca_events, art_refill_events. destruct (cl_cache cl0); [|rewrite app_nil_r; reflexivity].
  destruct (art_cls_needs_populate c0 cl0); [|rewrite app_nil_r; reflexivity].
  match goal with |- context [if ?b then _ else _] => destruct b end.
  - rewrite art_live_snoc. reflexivity.
  - change (?a :: [?b]) with ([a] ++ [b]). rewrite app_assoc, !art_live_snoc. reflexivity.
Qed.

#[using="FSG G LB M REP"] Lemma art_mgap_parr : forall a k, rn_parr rn <= a -> a + k <= rn_parr rn + 2 ^ 23 -> art_gap art_mrep_W a k.
Proof.
  intros a k Ha Hk. destruct REP as (ROK & _). rok_open ROK. geo_open GEO. destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap.
  unfold art_mrep_W. cbn [art_gap fst snd]. unfold apart in *. clear - Ha Hk G1 G2 G4 G6 Eris Espb Plo Phi Pap Apt Apk Apl Apb. repeat split; try exact I; lia.
Qed.

#[using="LB M REP LIVE"] Lemma art_mgap_grant : forall p a k, In p (art_live (g_log FSG G)) -> fst p <= a -> a + k <= fst p + snd p -> art_gap art_mrep_W a k.
Proof.
  intros p a k Hp Ha Hk. destruct (LIVE p Hp) as (L0 & L1 & L2 & L3 & LO).
  pose proof (LO _ (or_introl eq_refl)) as At. pose proof (LO _ (or_intror (or_intror (or_introl eq_refl)))) as Ak.
  pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) as Al.
  pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) as Ab.
  pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))))) as Ai.
  cbn [fst snd] in At, Ak, Al, Ab, Ai.
  destruct REP as (ROK & _). rok_open ROK. geo_open GEO.
  unfold art_mrep_W. cbn [art_gap fst snd]. unfold apart in *. clear - Ha Hk L0 L1 L2 L3 At Ak Al Ab Ai G1 G2 G4 G6 Eris Espb Kspb. repeat split; try exact I; lia.
Qed.

(* [comment removed for export] *)
#[using="LB M rz rs kb c cl w ab shb u sz REP Edep LIVE"] Lemma art_mgap_grant_sha : forall p u0 n0 a, In p (art_live (g_log FSG G)) -> fst p <= u0 -> u0 + n0 <= fst p + snd p -> 0 < n0 ->
  HeapIfaceA.S u0 <= a <= HeapIfaceA.S (u0 + n0 - 1) -> art_gap art_mrep_W a 1.
Proof.
  intros p u0 n0 a Hp Hlo Hhi Hn0 Ha. destruct (LIVE p Hp) as (L0 & L1 & L2 & L3 & LO).
  pose proof (LO _ (or_intror (or_intror (or_introl eq_refl)))) as Ak. cbn [fst snd] in Ak.
  destruct REP as (ROK & _). rok_open ROK. geo_open GEO.
  pose proof (art_S_ge u0 0 ltac:(lia)) as B0. pose proof (art_S_lt (u0 + n0 - 1) (2 ^ 44) ltac:(lia)) as B2.
  assert (OUTK : a < 2147450880 + 8192 * rn_qs rn + 2 ^ 29 \/ 2147450880 + 8192 * rn_qs rn + 2 ^ 34 <= a).
  { unfold apart in Ak. destruct Ak as [Ak|Ak].
    - left. pose proof (art_S_lt (u0 + n0 - 1) (8192 * rn_qs rn) ltac:(lia)). lia.
    - right. pose proof (art_S_ge u0 (8192 * rn_qs rn + 2 ^ 34) ltac:(lia)). lia. }
  unfold art_mrep_W. cbn [art_gap fst snd]. unfold apart in *. clear - B0 B2 Ha OUTK G1 G2 G4 G6 Eris Espb G10 Al2s Abs. repeat split; try exact I; lia.
Qed.
#[using="LB M rz rs kb c cl w ab shb u sz REP Edep LIVE"] Lemma art_mgap_grant_sh : forall p u0 n0 j, In p (art_live (g_log FSG G)) -> fst p <= u0 -> u0 + n0 <= fst p + snd p -> 0 < n0 -> 0 <= j ->
  (j < n0 / 8 \/ (j = n0 / 8 /\ n0 mod 8 <> 0)) -> art_gap art_mrep_W (HeapIfaceA.S u0 + j) 1.
Proof.
  intros p u0 n0 j Hp Hlo Hhi Hn0 Hj0 Hj. apply (art_mgap_grant_sha p u0 n0 _ Hp Hlo Hhi Hn0). pose proof (art_S_blk_hi u0 n0 j Hn0 Hj). lia.
Qed.

#[using="rn LB Sp n rz qz rs qr qn m8 km kb b1 c cl w ab shb u sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT LIVE"] Lemma art_mrep_far_hdr : forall p u0 n0 st, In p (art_live (g_log FSG G)) -> fst p + 16 <= u0 -> u0 + n0 <= fst p + snd p ->
  art_chunk_hdr M u0 n0 st -> art_chunk_hdr M' u0 n0 st.
Proof.
  intros p u0 n0 st Hp L1 L2 (b & Hb & Hbt & C1 & C2 & Hn0). destruct (LIVE p Hp) as (L0 & L1' & L2' & _).
  pose proof REP as (ROK & _). destruct ROK as (GEO & _). geo_open GEO.
  exists b. split; [exact Hb|]. split; [exact Hbt|]. split; [|split; [|exact Hn0]].
  - apply (art_cell_tr art_mrep_W M M' (u0 - 16) 4%nat _ art_mrep_agree (art_mgap_grant p (u0 - 16) 4 Hp ltac:(lia) ltac:(lia))); [lia|cbn; lia|exact C1].
  - apply (art_cell_tr art_mrep_W M M' (u0 - 12) 4%nat _ art_mrep_agree (art_mgap_grant p (u0 - 12) 4 Hp ltac:(lia) ltac:(lia))); [lia|cbn; lia|exact C2].
Qed.

#[using="rn LB Sp n rz qz rs qr qn m8 km kb b1 c cl w ab shb u sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT LIVE"] Lemma art_mrep_far_shadow : forall p u0 n0, In p (art_live (g_log FSG G)) -> fst p <= u0 -> u0 + n0 <= fst p + snd p -> 0 < n0 ->
  HAJ.shadow_blkR M u0 n0 -> HAJ.shadow_blkR M' u0 n0.
Proof.
  intros p u0 n0 Hp L1 L2 Hn0 SB0. destruct (LIVE p Hp) as (L0 & _).
  assert (TBY : forall j, 0 <= j -> (j < n0 / 8 \/ (j = n0 / 8 /\ n0 mod 8 <> 0)) -> forall v, byte_at M (HeapIfaceA.S u0 + j) v -> byte_at M' (HeapIfaceA.S u0 + j) v).
  { intros j Hj0 Hj v B. apply (art_byte_at_eq M M'); [|exact B]. apply art_mrep_agree.
    pose proof (art_S_ge u0 0 ltac:(lia)) as B0. pose proof (art_S_blk_hi u0 n0 j Hn0 Hj) as B1.
    pose proof REP as (ROK & _). destruct ROK as (GEO & _). geo_open GEO. destruct (LIVE p Hp) as (_ & _ & L2' & _).
    pose proof (art_S_lt (u0 + n0 - 1) (2 ^ 44) ltac:(lia)) as B2.
    rewrite art_u_lit by lia. apply (art_gap_out _ (HeapIfaceA.S u0 + j) 1); [|lia]. apply (art_mgap_grant_sh p u0 n0 j Hp L1 L2 Hn0 Hj0 Hj). }
  exact (shadow_blkR_tby M M' u0 n0 Hn0 TBY SB0).
Qed.

#[using="M Sp qz qr qn m8 km b1 shb sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT LIVE"] Lemma art_mrep_sec : art_rt_sec FSG rn G' ((u, n) :: LB) M'.
Proof.
  pose proof REP as (ROK & _ & _ & _ & _ & SEC & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct SEC as (C1 & C2 & C3 & C4 & C5 & C6 & S1 & S2 & SALL & SLIVE & SLEN). destruct OUT as (GR & _).
  unfold art_rt_sec. cbn [art_gs_malloc g_sec g_sec_committed g_log g_qt g_qg]. rewrite art_live_ca_events.
  split; [apply art_mrep_cell_img; [lia|cbn; lia|exact C1]|]. split; [apply art_mrep_cell_img; [lia|cbn; lia|exact C2]|].
  split; [apply art_mrep_cell_img; [lia|cbn; lia|exact C3]|]. split; [apply art_mrep_cell_img; [lia|cbn; lia|exact C4]|].
  split; [apply art_mrep_cell_img; [lia|cbn; lia|exact C5]|]. split; [apply art_mrep_cell_img; [lia|cbn; lia|exact C6]|]. split; [exact S1|]. split; [intros E; eapply wr_grows; [exact GR|exact (S2 E)]|].
  split; [|split; [exact SLIVE|exact SLEN]].
  intros i s Hi. destruct (SALL i s Hi) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
  assert (Hil : Z.of_nat i < Z.of_nat (length (g_sec FSG G))). { apply Nat2Z.inj_lt. apply nth_error_Some. rewrite Hi. discriminate. }
  destruct (LIVE _ P2) as (L0 & L1 & L2 & _). cbn [fst snd] in L0, L1, L2.
  assert (Hn0s : 1 <= sc_n s). { destruct (sc_quar s); [destruct P9 as ((b & _ & _ & _ & _ & H) & _)|destruct P9 as (_ & (b & _ & _ & _ & _ & H) & _)]; lia. }
  split. { apply (art_cell_tr art_mrep_W M M' _ 8%nat _ art_mrep_agree (art_mgap_parr (rn_parr rn + 8 * Z.of_nat i) 8 ltac:(lia) ltac:(lia))); [lia|cbn; lia|exact P1]. }
  split; [exact P2|]. split; [eapply wr_grows; [exact GR|exact P3]|].
  split. { apply (art_cell_tr art_mrep_W M M' _ 8%nat _ art_mrep_agree (art_mgap_grant (sc_map s, sc_msize s) (sc_map s) 8 P2 ltac:(cbn; lia) ltac:(cbn; lia))); [lia|cbn; lia|exact P4]. }
  split. { apply (art_cell_tr art_mrep_W M M' _ 8%nat _ art_mrep_agree (art_mgap_grant (sc_map s, sc_msize s) (sc_map s + 8) 8 P2 ltac:(cbn; lia) ltac:(cbn; lia))); [lia|cbn; lia|exact P5]. }
  split. { apply (art_cell_tr art_mrep_W M M' _ 8%nat _ art_mrep_agree (art_mgap_grant (sc_map s, sc_msize s) (sc_map s + 24) 8 P2 ltac:(cbn; lia) ltac:(cbn; lia))); [lia|cbn; lia|exact P6]. }
  split; [exact P7|]. split; [exact P8|]. split; [|exact P10].
  destruct (sc_quar s).
  - destruct P9 as (Q1 & Q2). split; [|exact Q2]. apply (art_mrep_far_hdr (sc_map s, sc_msize s) _ _ _ P2); [cbn; lia|cbn; lia|exact Q1].
  - destruct P9 as (Q1 & Q2 & Q3). pose proof Q2 as (_ & _ & _ & _ & _ & Hn0). split; [right; exact Q1|]. split.
    + apply (art_mrep_far_hdr (sc_map s, sc_msize s) _ _ _ P2); [cbn; lia|cbn; lia|exact Q2].
    + apply (art_mrep_far_shadow (sc_map s, sc_msize s) _ _ P2); [cbn; lia|cbn; lia|lia|exact Q3].
Qed.

(* [comment removed for export] *)
#[using="rn LB M M' Sp n qz qr qn m8 km kb b1 ab shb u sz REP Hn Erz16 Hqz Hnrs Hprim Emu Edep OUT"] Lemma art_mrep_w_free : g_st FSG G c w = CFree.
Proof.
  destruct art_mrep_num as (Hc & Hfit & Hsz & _).
  pose proof REP as (_ & _ & _ & (_ & PRIM & _) & CH & _). destruct (PRIM c Hc) as (_ & OK & _). fold cl in OK.
  specialize (CH c Hc). cbv zeta in CH. destruct CH as (_ & II & II' & _). fold cl in II, II'. fold sz in II'.
  pose proof (art_ca_cptr_origin c cl Hc OK) as ORG. fold w in ORG. destruct ORG as [Hin|(_ & _ & Hlo)]; [exact (II w Hin)|].
  apply II'. intros (_ & B & _). lia.
Qed.

(* [comment removed for export] *)
#[using="LB M M' qn m8 kb b1 ab shb u sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_nfp_W : forall a, 0 <= a < 2 ^ 64 -> art_out art_mrep_W a ->
  ~ art_malloc_fp_lin Sp (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) a.
Proof.
  intros a Ha Hx F.
  destruct art_mrep_num as (Hc & Hfit & Hsz & Hkm & Hkm' & Hw0 & Hwsz & Haumu' & Hmu3').
  pose proof (art_mfp_coarse Sp (rn_HI rn) (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) a Hc Hkm Hkm' Hw0 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) HS F) as CO.
  unfold art_mrep_W in Hx. cbn [art_out fst snd] in Hx. unfold art_malloc_coarse in CO. lia.
Qed.

#[using="LB M M' qn m8 kb b1 ab shb u sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_nfp_class : forall c0 a, 1 <= c0 <= 30 -> c0 <> c ->
  (rn_spb rn + c0 * 2 ^ 32 <= a < rn_spb rn + c0 * 2 ^ 32 + 2 ^ 32
   \/ 2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29 <= a < 2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29 + 2 ^ 29
   \/ rn_spb rn + 2 ^ 37 + 128 * c0 <= a < rn_spb rn + 2 ^ 37 + 128 * c0 + 128) ->
  ~ art_malloc_fp_lin Sp (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) a.
Proof.
  intros c0 a Hc0 Ne Hx.
  destruct art_mrep_num as (Hc & Hfit & Hsz & Hkm & Hkm' & Hw0 & Hwsz & Haumu' & Hmu3').
  pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
  apply (art_mfp_out_class Sp (rn_HI rn) (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) c0 a Hc Hc0 Ne Hkm Hkm' Hw0 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(lia) ltac:(lia) HS G1 Espb G4 ltac:(lia) ltac:(lia) G11); [unfold apart; clear - G10; lia|exact Al2k|exact Al2s|exact Abk|exact Abs|exact Hx].
Qed.

#[using="LB M M' qn m8 kb b1 ab u REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_nfp_chunk : forall w0 a, art_cptr_ok sz (cl_au cl) w0 -> w0 <> w ->
  (rn_spb rn + c * 2 ^ 32 + 16 * w0 <= a < rn_spb rn + c * 2 ^ 32 + 16 * w0 + sz
   \/ 8 * (a - shb) + 8 <= 16 * w0 + sz /\ shb + 2 * w0 <= a) ->
  ~ art_malloc_fp_lin Sp (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) a.
Proof.
  intros w0 a V0 Ne Ha.
  destruct art_mrep_num as (Hc & Hfit & Hsz & Hkm & Hkm' & Hw0 & Hwsz & Haumu' & Hmu3').
  pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _). rok_open ROK. geo_open GEO.
  destruct (PRIM c Hc) as (_ & OK & _). fold cl in OK. pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _).
  destruct OUT as (_ & _ & _ & _ & _ & OK' & CP & _). fold c in OK', CP. fold cl in OK', CP. fold w in CP. fold sz in CP.
  assert (V0' : art_cptr_ok sz (cl_au (art_ca_pre c cl)) w0).
  { eapply art_cptr_mono; [|exact V0]. destruct (art_ca_pre_au c cl) as [E|(_ & _ & E)]; rewrite E; [lia|].
    assert (0 <= art_cls_new c cl * AsanTab.class_size c); [|lia]. apply Z.mul_nonneg_nonneg; [|fold sz; lia]. unfold art_cls_new. apply Z.div_pos; fold sz; lia. }
  pose proof (art_cptr_apart sz _ w w0 ltac:(lia) CP V0' ltac:(intros E; apply Ne; symmetry; exact E)) as AP.
  destruct V0 as (V00 & V01 & _).
  apply (art_mfp_out_chunk Sp (rn_HI rn) (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) sz w0 a Hc Hkm Hkm' Hw0 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(lia) ltac:(lia) ltac:(lia) V00 ltac:(lia) AP HS G1 Espb G4 ltac:(lia) ltac:(lia) G11); [unfold apart; clear - G10; lia|exact Al2k|exact Al2s|exact Abk|exact Abs|].
  unfold shb in Ha. exact Ha.
Qed.

(* [comment removed for export] *)
#[using="LB M Sp qz qr qn m8 km b1 shb sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_quar : art_rt_quar FSG rn G' M'.
Proof.
  pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _ & _ & QU & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct art_mrep_num as (Hc & Hfit & Hsz & Hkm & Hkm' & Hw0 & Hwsz & Haumu' & Hmu3').
  destruct QU as ((ft & lt & T1 & T2 & T3 & T4 & TL) & (fg & lg & Q1 & Q2 & Q3 & Q4 & QL) & B1 & B2 & F1 & ND & NEB & ITEMS & NDI & BCH).
  destruct (PRIM 24 ltac:(lia)) as (_ & OK24 & _). pose proof OK24 as (_ & (Hau24 & Haumu24) & _ & _ & _ & Hmu324 & _).
  assert (BEQ : forall b, In b (g_qt FSG G ++ g_qg FSG G) -> 0 <= bt_addr b /\ bt_addr b + 8192 < 2 ^ 64 /\ forall x : word, bt_addr b <= U x < bt_addr b + 8192 -> M' x = M x).
  { intros b Hb. destruct (BCH b Hb) as (wb & Eb & Vb & Stb). pose proof Vb as (Vb0 & Vb1 & _). rewrite art_class_size_24 in Vb1.
    split; [rewrite Eb; clear - G4 Vb0; lia|]. split; [rewrite Eb; clear - G4 Espb G6 Eris G2 Vb1 Haumu24 Hmu324; lia|]. intros x Hx. rewrite Eb in Hx.
    destruct (Z.eq_dec c 24) as [E24|N24].
    - assert (Nw : wb <> w). { intros ->. pose proof art_mrep_w_free as F. rewrite E24 in F at 1. rewrite F in Stb. discriminate Stb. }
      apply (art_mrep_eqw_chunk wb x); [unfold sz, cl; rewrite E24; exact Vb|exact Nw|]. left. unfold sz. rewrite E24, art_class_size_24. lia.
    - apply (art_mrep_out_class 24 x ltac:(lia) ltac:(intros E; apply N24; symmetry; exact E)). left. clear - Hx Vb0 Vb1 Haumu24 Hmu324. lia. }
  assert (TT : forall a (k : nat) v, rn_t rn <= a -> a + Z.of_nat k <= rn_t rn + 208 -> cellA M a k v -> cellA M' a k v).
  { intros a k v Ha Hk C. apply (art_cell_tr art_mrep_W M M' a k v art_mrep_agree (art_mgap_thread a (Z.of_nat k) Ha ltac:(lia) ltac:(left; lia))); [lia|lia|exact C]. }
  unfold art_rt_quar. cbn [art_gs_malloc g_qt g_qg g_cls g_st].
  split. { exists ft, lt. split; [apply TT; [lia|cbn; lia|exact T1]|]. split; [apply TT; [lia|cbn; lia|exact T2]|]. split; [apply TT; [lia|cbn; lia|exact T3]|].
           split; [apply TT; [lia|cbn; lia|exact T4]|]. apply (art_batch_list_tr M M'); [|exact TL]. intros b Hb. apply BEQ. apply in_or_app. left. exact Hb. }
  split. { exists fg, lg. split; [apply art_mrep_cell_img; [lia|cbn; lia|exact Q1]|]. split; [apply art_mrep_cell_img; [lia|cbn; lia|exact Q2]|].
           split; [apply art_mrep_cell_img; [lia|cbn; lia|exact Q3]|]. split; [apply art_mrep_cell_img; [lia|cbn; lia|exact Q4]|].
           apply (art_batch_list_tr M M'); [|exact QL]. intros b Hb. apply BEQ. apply in_or_app. right. exact Hb. }
  split; [exact B1|]. split; [exact B2|]. split; [apply art_mrep_cell_img; [lia|cbn; lia|exact F1]|].
  split; [exact ND|]. split; [exact NEB|].
  assert (AUM : cl_au cl <= cl_au (art_cls_pop (art_ca_pre c cl))).
  { cbn [art_cls_pop cl_au]. destruct (art_ca_pre_au c cl) as [E|(_ & _ & E)]; rewrite E; [lia|].
    assert (0 <= art_cls_new c cl * AsanTab.class_size c); [|lia]. apply Z.mul_nonneg_nonneg; [|fold sz; lia]. unfold art_cls_new.
    destruct (PRIM c Hc) as (_ & OKc & _). fold cl in OKc. destruct OKc as (_ & (Ha0 & Ham) & _). apply Z.div_pos; fold sz; lia. }
  split.
  { intros b it Hb Hit. destruct (ITEMS b it Hb Hit) as [(c0 & w0 & Hc0 & V0 & St0)|SEC0]; [left|right; exact SEC0].
    exists c0, w0. split; [exact Hc0|].
    destruct (Z.eqb_spec c0 c) as [Ec|Nc]; cbn [andb].
    - subst c0. split; [eapply art_cptr_mono; [exact AUM|exact V0]|].
      destruct (Z.eqb_spec w0 w) as [Ew|Nw]; [|exact St0]. exfalso. subst w0. rewrite art_mrep_w_free in St0. discriminate St0.
    - split; [exact V0|exact St0]. }
  split; [exact NDI|].
  intros b Hb. destruct (BCH b Hb) as (wb & Eb & Vb & Stb). exists wb. split; [exact Eb|].
  destruct (Z.eqb_spec 24 c) as [E24|N24]; cbn [andb].
  - split.
    + eapply art_cptr_mono; [|exact Vb]. cbn [art_cls_pop cl_au]. rewrite E24. fold cl.
      destruct (art_ca_pre_au c cl) as [E|(_ & _ & E)]; rewrite E; [lia|].
      assert (0 <= art_cls_new c cl * AsanTab.class_size c); [|lia]. apply Z.mul_nonneg_nonneg; [|fold sz; lia]. unfold art_cls_new.
      destruct (PRIM c Hc) as (_ & OKc & _). fold cl in OKc. destruct OKc as (_ & (Ha0 & Ham) & _). apply Z.div_pos; fold sz; lia.
    + destruct (Z.eqb_spec wb w) as [Ew|Nw]; [|exact Stb]. exfalso. pose proof art_mrep_w_free as F. rewrite <- E24, <- Ew in F. rewrite F in Stb. discriminate Stb.
  - split; [exact Vb|exact Stb].
Qed.

(* [comment removed for export] *)
#[using="M M' Sp qz qr qn m8 km b1 shb sz REP Hn Erz16 Hqz Hnrs Hprim Emu Edep OUT"] Lemma art_mrep_blocks : art_rt_blocks FSG rn G' ((u, n) :: LB).
Proof.
  destruct art_mrep_num as (Hc & Hfit & Hsz & _).
  pose proof REP as (_ & _ & _ & (_ & PRIM & _) & _ & _ & _ & _ & _ & BL & _).
  destruct OUT as (_ & _ & _ & _ & _ & _ & CP & _). fold c in CP. fold cl in CP. fold w in CP. fold sz in CP.
  intros b [Eb|Hb].
  - left. exists c, w. split; [exact Hc|]. cbn [art_gs_malloc g_cls g_st]. rewrite !Z.eqb_refl. cbn [andb art_cls_pop cl_au]. fold cl. fold sz. split; [exact CP|]. rewrite <- Eb. reflexivity.
  - destruct (BL b Hb) as [(c0 & w0 & Hc0 & V0 & St0)|SEC]; [|right; exact SEC].
    left. exists c0, w0. split; [exact Hc0|]. cbn [art_gs_malloc g_cls g_st]. destruct (Z.eqb_spec c0 c) as [E|N]; cbn [andb].
    + subst c0. fold cl in V0. fold sz in V0. split.
      * eapply art_cptr_mono; [|exact V0]. cbn [art_cls_pop cl_au]. fold cl.
        destruct (art_ca_pre_au c cl) as [E|(_ & _ & E)]; rewrite E; [lia|].
        assert (0 <= art_cls_new c cl * AsanTab.class_size c); [|lia]. apply Z.mul_nonneg_nonneg; [|fold sz; lia]. unfold art_cls_new.
        destruct (PRIM c Hc) as (_ & OKc & _). fold cl in OKc. destruct OKc as (_ & (Ha0 & Ham) & _). apply Z.div_pos; fold sz; lia.
      * destruct (Z.eqb_spec w0 w) as [Ew|Nw]; [|exact St0]. exfalso. pose proof art_mrep_w_free as F. rewrite <- Ew in F. rewrite F in St0. discriminate St0.
    + split; [exact V0|exact St0].
Qed.

(* [comment removed for export] *)
#[using="M M' Sp n qz qr qn m8 km kb b1 ab shb u sz REP Hn Erz16 Hqz Hnrs Hprim Emu Edep OUT"] Lemma art_mrep_block_cases : forall b, In b LB ->
  (exists c0 w0, 1 <= c0 <= 30 /\ art_cptr_ok (AsanTab.class_size c0) (cl_au (g_cls FSG G c0)) w0 /\ (c0 = c -> w0 <> w) /\ 1 <= snd b
      /\ rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + 16 <= fst b /\ fst b + snd b <= rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + AsanTab.class_size c0)
  \/ (exists p, In p (art_live (g_log FSG G)) /\ fst p + 4096 <= fst b /\ fst b + snd b <= fst p + snd p /\ 1 <= snd b).
Proof.
  intros b Hb. pose proof REP as (_ & _ & _ & _ & CH & SEC & _ & _ & _ & BL & _).
  destruct (BL b Hb) as [(c0 & w0 & Hc0 & V0 & St0)|(s & Hs & Hq & Eu & En0)].
  - left. exists c0, w0. specialize (CH c0 Hc0). cbv zeta in CH. destruct CH as (_ & _ & _ & III). specialize (III w0 V0). rewrite St0 in III.
    destruct III as (_ & J2 & J3 & (bb & _ & _ & _ & _ & Hn0) & _). split; [exact Hc0|]. split; [exact V0|]. split; [|split; [lia|split; [exact J2|exact J3]]].
    intros Ec Ew. subst c0 w0. pose proof art_mrep_w_free as F. rewrite F in St0. discriminate St0.
  - right. destruct SEC as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _). destruct (In_nth_error _ _ Hs) as (i & Hi).
    destruct (SALL i s Hi) as (_ & P2 & _ & _ & _ & _ & P7 & P8 & P9 & _). rewrite Hq in P9. destruct P9 as (_ & (bb & _ & _ & _ & _ & Hn0) & _).
    exists (sc_map s, sc_msize s). cbn [fst snd]. rewrite <- Eu, <- En0. split; [exact P2|]. split; [lia|]. split; [exact P8|lia].
Qed.

#[using="M M' qn m8 kb b1 ab shb u sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT LIVE"] Lemma art_mrep_nfp_block : forall b a, In b LB -> (fst b <= a < fst b + snd b \/ in_shadow_of (fst b) (snd b) a) ->
  ~ art_malloc_fp_lin Sp (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) a.
Proof.
  intros b a Hb Ha. pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _). rok_open ROK. geo_open GEO. unfold in_shadow_of in Ha.
  destruct (art_mrep_block_cases b Hb) as [(c0 & w0 & Hc0 & V0 & Nw & Hn0 & J2 & J3)|(p & Hp & P1 & P2 & Hn0)].
  - destruct (PRIM c0 Hc0) as (_ & OK0 & _). pose proof OK0 as (_ & (Ha0 & Ham0) & _ & _ & _ & Hmu30 & _). pose proof V0 as (V00 & V01 & _).
    pose proof (art_class_size_facts c0 Hc0) as (Hsz0 & Hsz016).
    assert (Es : AsanTab.class_size c0 = 16 * (AsanTab.class_size c0 / 16)). { pose proof (Z.div_mod (AsanTab.class_size c0) 16 ltac:(lia)) as D. rewrite Hsz016 in D. lia. }
    assert (SHB : fst b <= a < fst b + snd b \/ (8 * (a - (2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29)) + 8 <= 16 * w0 + AsanTab.class_size c0 /\ 2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29 + 2 * w0 <= a)).
    { destruct Ha as [Ha|Ha]; [left; exact Ha|right].
      pose proof (art_S_lt (fst b + snd b - 1) (8192 * rn_qs rn + c0 * 2 ^ 29 + 2 * w0 + 2 * (AsanTab.class_size c0 / 16)) ltac:(lia)) as H2.
      pose proof (art_S_ge (fst b) (8192 * rn_qs rn + c0 * 2 ^ 29 + 2 * w0 + 2) ltac:(lia)) as H3. split; lia. }
    destruct (Z.eq_dec c0 c) as [Ec|Ne].
    + subst c0. apply (art_mrep_nfp_chunk w0 a V0 (Nw eq_refl)). fold sz in SHB, J3. unfold shb. destruct SHB as [B|B]; [left; lia|right; exact B].
    + apply (art_mrep_nfp_class c0 a Hc0 Ne). destruct SHB as [B|B]; [left; lia|right; left; lia].
  - destruct (LIVE p Hp) as (L0 & L1 & L2 & _).
    apply art_mrep_nfp_W.
    + destruct Ha as [Ha|Ha]; [lia|]. pose proof (art_S_ge (fst b) 0 ltac:(lia)). pose proof (art_S_lt (fst b + snd b - 1) (2 ^ 44) ltac:(lia)). lia.
    + apply (art_gap_out _ a 1); [|lia]. destruct Ha as [Ha|Ha]; [apply (art_mgap_grant p a 1 Hp); lia|apply (art_mgap_grant_sha p (fst b) (snd b) a Hp); lia].
Qed.

#[using="M M' Sp qz qr qn m8 km kb b1 shb sz REP Hn Erz16 Hqz Hnrs Hprim Emu Edep OUT LIVE"] Lemma art_mrep_blocks_apart : blocks_apart u n LB.
Proof.
  intros b Hb. destruct art_mrep_num as (Hc & Hfit & Hsz & Hkm & Hkm' & Hw0 & Hwsz & Haumu' & Hmu3').
  pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _). rok_open ROK. geo_open GEO. unfold u, ab.
  destruct (art_mrep_block_cases b Hb) as [(c0 & w0 & Hc0 & V0 & Nw & Hn0 & J2 & J3)|(p & Hp & P1 & P2 & Hn0)].
  - destruct (PRIM c0 Hc0) as (_ & OK0 & _). pose proof OK0 as (_ & (Ha0 & Ham0) & _ & _ & _ & Hmu30 & _). pose proof V0 as (V00 & V01 & _).
    pose proof (art_class_size_facts c0 Hc0) as (Hsz0 & _).
    destruct (Z.eq_dec c0 c) as [Ec|Ne]; [|lia]. subst c0. fold cl in V0. fold sz in V0, J3.
    destruct OUT as (_ & _ & _ & _ & _ & _ & CP & _). fold c in CP. fold cl in CP. fold w in CP. fold sz in CP.
    assert (V0' : art_cptr_ok sz (cl_au (art_ca_pre c cl)) w0).
    { eapply art_cptr_mono; [|exact V0]. destruct (PRIM c Hc) as (_ & OK & _). fold cl in OK. destruct OK as (_ & (Hau0 & Haumu) & _).
      destruct (art_ca_pre_au c cl) as [E|(_ & _ & E)]; rewrite E; [lia|].
      assert (0 <= art_cls_new c cl * AsanTab.class_size c); [|lia]. apply Z.mul_nonneg_nonneg; [|fold sz; lia]. unfold art_cls_new. apply Z.div_pos; fold sz; lia. }
    pose proof (art_cptr_apart sz _ w w0 ltac:(lia) CP V0' ltac:(intros E; apply (Nw eq_refl); symmetry; exact E)) as AP. lia.
  - destruct (LIVE p Hp) as (L0 & L1 & L2 & L3 & LO). pose proof (LO _ (or_intror (or_intror (or_introl eq_refl)))) as Ak. cbn [fst snd] in Ak. unfold apart in Ak. lia.
Qed.

(* [comment removed for export] *)
#[using="LB M Sp qz qr qn m8 km b1 shb sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_ghost : art_rt_ghost FSG rn G' M'.
Proof.
  destruct art_mrep_num as (Hc & Hfit & Hsz & _).
  pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _ & _ & QR & _ & _ & _ & (T1 & T23 & T4 & T5)). destruct ROK as (GEO & _). geo_open GEO.
  destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH).
  unfold art_rt_ghost, G'. cbn [art_gs_malloc g_qt g_qg g_cls].
  split; [exact T1|]. split.
  { intros c0 Hc0. destruct (Z.eqb_spec c0 c) as [->|NE]; [|exact (T23 c0 Hc0)]. destruct (PRIM c Hc) as (_ & OK & _). destruct (T23 c Hc) as (X2 & X3).
    exact (art_ghost_cls_pop c (g_cls FSG G c) Hc OK X2 X3). }
  split; [|apply art_mrep_cell_img; [lia|cbn; lia|exact T5]].
  intros b Hb. pose proof (T4 b Hb) as B. destruct (BCH b Hb) as (wb & Ewb & OKwb & Stb). rewrite art_class_size_24 in OKwb. pose proof OKwb as (Hwb0 & Hwbau & _).
  destruct (PRIM 24 ltac:(lia)) as (_ & OK24 & _). destruct OK24 as (_ & (_ & Haumu24) & _ & _ & _ & Hmu324 & _).
  apply (art_byte_at_eq M M'); [|exact B]. rewrite Ewb, Espb. replace (65536 * rn_qs rn + 24 * 2 ^ 32 + 16 * wb) with (65536 * rn_qs rn + 24 * 2 ^ 32 + 8 * (2 * wb)) by lia. rewrite art_S_lin.
  destruct (Z.eq_dec c 24) as [E24|N24].
  - assert (Nw : wb <> w) by (intros ->; pose proof art_mrep_w_free as X; rewrite E24 in X; rewrite X in Stb; discriminate Stb).
    assert (Vwb : art_cptr_ok sz (cl_au cl) wb) by (unfold sz, cl; rewrite E24, art_class_size_24; exact OKwb).
    apply (art_mrep_eq_chunk wb _ Vwb Nw). right. unfold shb, sz. rewrite E24, art_class_size_24. lia.
  - apply (art_mrep_eq_class 24); [lia|intros E; apply N24; symmetry; exact E|]. right. lia.
Qed.

(* [comment removed for export] *)
#[using="M Sp qz qr qn m8 km b1 shb sz REP Hn Erz16 Hqz En Hm8 Ers Hnrs Hprim HS Emu Edep OUT LIVE OKpre"] Theorem art_alloc_rep_malloc_pre : art_alloc_rep FSG rn G' ((u, n) :: LB) M'.
Proof.
  pose proof REP as (ROK & _).
  split; [exact ROK|]. split; [exact art_mrep_statics|]. split; [exact art_mrep_thread|]. split; [exact art_mrep_primary|]. split; [exact art_mrep_chunks|].
  split; [exact art_mrep_sec|]. split; [exact art_mrep_quar|]. split; [exact art_mrep_depot|]. split; [exact art_mrep_ia|]. split; [exact art_mrep_blocks|exact art_mrep_ghost].
Qed.
(* [comment removed for export] *)
#[using="FSG G LB M REP"] Lemma art_mgap_fs : forall a k, ar_fs (rn_ar rn) <= a -> a + k <= ar_fs (rn_ar rn) + FS_BYTES -> art_gap art_mrep_W a k.
Proof.
  intros a k Ha Hk. destruct REP as (ROK & _). rok_open ROK. geo_open GEO. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap.
  unfold art_mrep_W. cbn [art_gap fst snd]. unfold apart, FS_BYTES in *. clear - Ha Hk G1 G2 G4 G6 Eris Espb Kspb Fhi Fap Fimg Aft Afk Afl Afb. repeat split; try exact I; lia.
Qed.

#[using="FSG G LB M rz rs kb c cl w ab shb u sz REP Edep"] Lemma art_mgap_far_sh : forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> apart lo len (rn_spb rn) (2 ^ 37 + 4096) ->
  HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> art_gap art_mrep_W a 1.
Proof.
  intros lo len a Hlo Hlen Hhi Ak Ha.
  destruct REP as (ROK & _). rok_open ROK. geo_open GEO.
  pose proof (art_S_ge lo 0 ltac:(lia)) as B0. pose proof (art_S_lt (lo + len - 1) (2 ^ 44) ltac:(lia)) as B2.
  assert (OUTK : a < 2147450880 + 8192 * rn_qs rn + 2 ^ 29 \/ 2147450880 + 8192 * rn_qs rn + 2 ^ 34 <= a).
  { unfold apart in Ak. destruct Ak as [Ak|Ak].
    - left. pose proof (art_S_lt (lo + len - 1) (8192 * rn_qs rn) ltac:(lia)). lia.
    - right. pose proof (art_S_ge lo (8192 * rn_qs rn + 2 ^ 34) ltac:(lia)). lia. }
  unfold art_mrep_W. cbn [art_gap fst snd]. unfold apart in *. clear - B0 B2 Ha OUTK G1 G2 G4 G6 Eris Espb G10 Al2s Abs. repeat split; try exact I; lia.
Qed.

#[using="LB M M' qn m8 kb b1 ab shb u sz REP Hn Erz16 Hqz Ers Hnrs Hprim Emu Edep OUT"] Lemma art_mrep_nfp_stack : forall a, rn_HI rn <= a -> ~ (Sp - 4096 <= a < Sp) ->
  ~ art_malloc_fp_lin Sp (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) a.
Proof.
  intros a Ha Ns. destruct art_mrep_num as (Hc & Hfit & Hsz & Hkm & Hkm' & Hw0 & Hwsz & Haumu' & Hmu3').
  pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
  apply (art_mfp_out_stack Sp (rn_HI rn) (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) a Hc Hkm Hkm' Hw0 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(lia) ltac:(lia) G1 Espb G4 ltac:(lia) ltac:(lia) G8 Dl2 Dblk Ha Ns).
Qed.

#[using="LB M M' qn m8 kb b1 ab shb u sz REP Hn Erz16 Hqz Ers Hnrs Hprim HS Emu Edep OUT"] Lemma art_mrep_nfp_image : forall a, 0x10000 <= a < 0x696000 -> ~ (0x211b08 <= a < 0x661b28) ->
  ~ art_malloc_fp_lin Sp (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) a.
Proof.
  intros a Ha Nd. destruct art_mrep_num as (Hc & Hfit & Hsz & Hkm & Hkm' & Hw0 & Hwsz & Haumu' & Hmu3').
  pose proof REP as (ROK & _ & _ & _ & _ & _ & _ & DEP & _). rok_open ROK. geo_open GEO. destruct DEP as (dN & dTF & dST & DG1 & DG2 & DG3 & DG4 & _).
  apply (art_mfp_out_image Sp (rn_HI rn) (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) a Hc Hkm Hw0 ltac:(lia) ltac:(lia) ltac:(lia) HS G1 Espb G4
           ltac:(unfold apart; clear - G9; lia) DG1 DG4 Ha Nd).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="qn m8 b1 shb sz REP Hn Erz16 Hqz En Hm8 Ers Hnrs Hprim HS Emu Edep OUT LIVE OKpre"] Lemma art_mrep_new_shadow : shadow_blk M' u n.
Proof.
  pose proof REP as (ROK & _). pose proof ROK as ROK'. rok_open ROK'. pose proof GEO as GEO'. geo_open GEO'.
  destruct art_mrep_num as (Hc & Hfit & Hsz & Hkm & Hkm' & Hw0 & Hwsz & Haumu' & Hmu3').
  destruct OUT as (GR & _ & _ & _ & _ & OK' & CP & Hb1 & Hty & CL1 & CL3 & CL4 & CL2 & SAB & SHZ & SHP & PSH & LCH).
  fold c in OK', CP, CL1, CL3, CL4, CL2, SAB, SHZ, SHP, PSH, LCH. fold cl in OK', CP, PSH, LCH. fold w in CP, CL1, CL3, CL4, CL2, SAB, SHZ, SHP, PSH, LCH.
  fold ab in CL1, CL3, CL4, CL2, LCH. fold shb in SAB, SHZ, SHP, PSH.
  assert (BYTE : forall y v, 0 <= y < 2 ^ 32 -> 0 <= v < 256 -> cellA M' (shb + y) 1 v -> byte_at M' (shb + y) v).
  { intros y v Hy Hv C. apply art_byte_of_cell1; [right; unfold shb; clear - Hy G4 Espb Hc; lia|unfold shb; clear - Hy G4 Espb G6 Eris G2 Hc; lia|exact Hv|exact C]. }
  assert (ES : forall y, HeapIfaceA.S (rn_spb rn + c * 2 ^ 32 + 8 * y) = shb + y). { intros y. rewrite Espb. unfold shb. apply art_S_lin. }
  assert (ESu : HeapIfaceA.S (ab + rz) = shb + (2 * w + 2 * qz)). { rewrite <- ES. f_equal. unfold ab. lia. }
  assert (Hqn : n / 8 = qn). { symmetry. apply (Z.div_unique _ 8 qn m8); lia. }
  assert (Hmod : n mod 8 = m8). { rewrite (Z.mod_eq n 8) by lia. rewrite Hqn. lia. }
  unfold u. split.
  - intros j Hj. rewrite ESu. replace (shb + (2 * w + 2 * qz) + j) with (shb + (2 * w + 2 * qz + j)) by lia. apply BYTE; [lia|lia|].
    replace (shb + (2 * w + 2 * qz + j)) with (shb + 2 * w + 2 * qz + j) by lia. apply SHZ. lia.
  - intros Hm. rewrite ESu, Hqn, Hmod. replace (shb + (2 * w + 2 * qz) + qn) with (shb + (2 * w + 2 * qz + qn)) by lia. apply BYTE; [lia|lia|].
    replace (shb + (2 * w + 2 * qz + qn)) with (shb + 2 * w + 2 * qz + qn) by lia. apply SHP. lia.
Qed.

#[using="qn m8 b1 shb REP Hn Erz16 Hqz En Hm8 Ers Hnrs Hprim HS Emu Edep OUT LIVE OKpre"] Theorem art_mrep_bundle :
  art_alloc_rep FSG rn G' ((u, n) :: LB) M'
  /\ blocks_apart u n LB
  /\ (forall x : word, ~ art_malloc_fp_lin Sp (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) (U x) -> M' x = M x)
  /\ (forall b a, In b LB -> (fst b <= a < fst b + snd b \/ in_shadow_of (fst b) (snd b) a) ->
        ~ art_malloc_fp_lin Sp (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) a)
  /\ (forall a, 0 <= a < 2 ^ 64 -> art_out art_mrep_W a -> ~ art_malloc_fp_lin Sp (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) a)
  /\ (forall a, rn_HI rn <= a -> ~ (Sp - 4096 <= a < Sp) -> ~ art_malloc_fp_lin Sp (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) a)
  /\ (forall a, 0x10000 <= a < 0x696000 -> ~ (0x211b08 <= a < 0x661b28) -> ~ art_malloc_fp_lin Sp (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) a)
  /\ (forall a k, ar_fs (rn_ar rn) <= a -> a + k <= ar_fs (rn_ar rn) + FS_BYTES -> art_gap art_mrep_W a k)
  /\ (forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> apart lo len (rn_spb rn) (2 ^ 37 + 4096) ->
        HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> art_gap art_mrep_W a 1)
  /\ (forall a k, rn_t rn <= a -> a + k <= rn_t rn + 4096 -> (a + k <= rn_t rn + 208 \/ rn_t rn + 3160 <= a) -> art_gap art_mrep_W a k)
  /\ (1 <= c <= 30 /\ rs + rz <= sz /\ 32 <= sz <= 65536 /\ 0 <= w /\ 16 * w + sz <= cl_au (art_ca_pre c cl) /\ cl_au (art_ca_pre c cl) <= cl_mu (art_ca_pre c cl)
      /\ cl_mu (art_ca_pre c cl) <= 3758096384).
Proof.
  split; [exact art_alloc_rep_malloc_pre|]. split; [exact art_mrep_blocks_apart|]. split; [exact art_mrep_lin|]. split; [exact art_mrep_nfp_block|].
  split; [exact art_mrep_nfp_W|]. split; [exact art_mrep_nfp_stack|]. split; [exact art_mrep_nfp_image|]. split; [exact art_mgap_fs|]. split; [exact art_mgap_far_sh|]. split; [exact art_mgap_thread|].
  destruct art_mrep_num as (Hc & Hfit & Hsz & Hkm & Hkm' & Hw0 & Hwsz & Haumu' & Hmu3'). repeat split; lia.
Qed.

End Rep.

Definition art_alloc_rep_malloc := art_alloc_rep_malloc_pre.
