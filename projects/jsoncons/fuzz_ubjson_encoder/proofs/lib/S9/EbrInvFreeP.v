(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatSim StoreOk HeapIface HeapIfaceA HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem EbtLeaf EbtRzLog EbtPoison EbtAllocA EbtAllocG ArtRunsMem EbtInitCache EbtPopulate1 ArtRuns EbtCls EbtFp EbtClsRep EbtClsGfa2 EbtClsRefill EbtCARSpec EbtAlloc3Pure EbtByteCell EbtCellEx EbtDepotA EbtDepot EbtAllocate3 ArtBridge EbrInv EbtInvMallocPure EbrInvMalloc EbrFsInvLaws EbtFxQ EbtFxBatch2 EbtFxBatch3 EbrFreeTop3 EbrInvFreePure EbrInvFree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import HeapIfaceAEx ShadowRLawsB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import EbtSecAllocPost EbtRecycle1 EbtRecycle2C EbtRecycle4S EbrInvRecycleA EbrInvRecycleC EbrInvRecycleD EbrFxPutP EbrFreeTop3P EbrTopFree3 EbrDep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Local Ltac lia0 := repeat match goal with H : _ |- _ => clear H end; L5FastLiaT.plia1.
Local Ltac lia0c := repeat match goal with H : _ |- _ => clear H end; cbn; L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Ltac rok_open14 ROK :=
  destruct ROK as (GEO & Esb & Kal & Kspb & Kend & Pal & Plo & Phi & Papp & Hkey & Hloff & Hloff' & Hloff'' & Htpd & Htsdd & Dl2 & Dblk
                   & Al2t & Al2c & Al2k & Al2s & Abt & Abc & Abk & Abs & Apt & Apc & Apk & Apl & Apb & Aft & Afc & Afk & Afl & Afb & Afp & Fhi & Fapp & Fimg & Flo
                   & Il2 & Iblk & Afkb & D0 & D1 & D2 & D3 & Adt & Adc & Adk & Adp & Adl & Adb & Adf & Atkb & Ackb & Al2kb & Apkb).
Ltac geo_open GEO :=
  destruct GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).

Lemma art_inP_t : forall rn, In (rn_t rn, 4096) (art_objs rn).
Proof. intros rn. unfold art_objs. cbn [In]. do 0 right. left. reflexivity. Qed.
Lemma art_inP_ctx : forall rn, In (rn_ctx rn, 4096) (art_objs rn).
Proof. intros rn. unfold art_objs. cbn [In]. do 1 right. left. reflexivity. Qed.
Lemma art_inP_kbase : forall rn, In (rn_kbase rn, 0x2000011000) (art_objs rn).
Proof. intros rn. unfold art_objs. cbn [In]. do 2 right. left. reflexivity. Qed.
Lemma art_inP_parr : forall rn, In (rn_parr rn, 2 ^ 23) (art_objs rn).
Proof. intros rn. unfold art_objs. cbn [In]. do 3 right. left. reflexivity. Qed.
Lemma art_inP_l2 : forall rn, In (rn_l2 rn, 2 ^ 20) (art_objs rn).
Proof. intros rn. unfold art_objs. cbn [In]. do 4 right. left. reflexivity. Qed.
Lemma art_inP_blk : forall rn, In (rn_blk rn, 2 ^ 23) (art_objs rn).
Proof. intros rn. unfold art_objs. cbn [In]. do 5 right. left. reflexivity. Qed.
Lemma art_inP_fs : forall rn, In (ar_fs (rn_ar rn), FS_BYTES) (art_objs rn).
Proof. intros rn. unfold art_objs. cbn [In]. do 6 right. left. reflexivity. Qed.
Lemma art_inP_img4 : forall rn, In (0x13f000, 0x55d000) (art_objs rn).
Proof. intros rn. unfold art_objs. cbn [In]. do 10 right. left. reflexivity. Qed.
Lemma art_inP_dtls : forall rn, In (rn_dtls rn, 4096) (art_objs rn).
Proof. intros rn. unfold art_objs. cbn [In]. do 11 right. left. reflexivity. Qed.

Section RepP.
Variable FSG : Type.
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M M7 M' : word -> option byte).
Variables (Sp u n q16 qr b1 : Z) (kb : nat) (i : nat) (s : art_sec).
Variable Dz : list (list Z).
Let bl := map art_sec_b (g_sec FSG G).
Let mb := sc_map s.
Let ms := sc_msize s.
Let evs := art_flush_events mb ms ++ [AMunmap mb ms].
Definition art_gs_freeP : art_gs FSG :=
  GS FSG (g_log FSG G ++ evs) (g_inited FSG G) (g_cls FSG G) (g_st FSG G) (art_swap_remove art_dsec i (g_sec FSG G)) (g_sec_committed FSG G)
     (g_qt FSG G) (g_qg FSG G) kb true (g_fs FSG G).
Let G' := art_gs_freeP.

Definition art_freeP_W : list (Z * Z) :=
  art_free3_W Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn)
  ++ art_cbr_sec_fp (Sp - 2208) (rn_t rn) (rn_parr rn) (Z.of_nat i) (fst (nth (length bl - 1) bl (0, 0))) mb ms.

Hypothesis REP : art_alloc_rep FSG rn G LB M.
Hypothesis KIND : nth_error (g_sec FSG G) i = Some s /\ sc_quar s = false /\ sc_u s = u /\ sc_n s = n.
Hypothesis Eu : u = 16 * q16.
Hypothesis Hn : 1 <= n.
Hypothesis Hqr : n <= 8 * qr <= n + 7.
Hypothesis Hb1 : 0 <= b1 < 2 ^ 24.
Hypothesis HS : rn_HI rn + 4096 <= Sp - 4096.
Hypothesis HS47 : Sp < 2 ^ 47.
Hypothesis Edep : (kb <= g_depot FSG G)%nat.
Hypothesis OUT : art_free3P_out M M7 M' Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn) b1 (rn_parr rn) mb ms bl i kb Dz.
Hypothesis HDz : incl (rn_keys rn) Dz.
Hypothesis LIVE : forall p, In p (art_live (g_log FSG G)) ->
  0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
  /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o)).
Hypothesis LIVE2 : forall p p', In p (art_live (g_log FSG G)) -> In p' (art_live (g_log FSG G)) -> fst p <> fst p' -> apart (fst p) (snd p) (fst p') (snd p').
Hypothesis LIVE3 : forall p, In p (art_live (g_log FSG G)) -> fst p mod 4096 = 0 /\ snd p mod 4096 = 0.
Hypothesis Hother : forall b0, In b0 (lb_remove u LB) -> In b0 LB /\ fst b0 <> u.

Lemma art_frepP_rec : forall j s', nth_error (g_sec FSG G) j = Some s' ->
  In (sc_map s', sc_msize s') (art_live (g_log FSG G)) /\ sc_map s' + 4096 <= sc_u s' - 16 /\ sc_u s' + sc_n s' <= sc_map s' + sc_msize s' /\ 1 <= sc_n s' /\ 0x69c000 <= sc_map s'
  /\ 0 < sc_map s' /\ sc_map s' + sc_msize s' <= rn_HI rn /\ (sc_map s' + sc_msize s' <= 0x7fff7000 \/ 0x10007fff8000 <= sc_map s')
  /\ (forall o, In o (art_objs rn) -> apart (sc_map s') (sc_msize s') (fst o) (snd o)).
Proof.
  intros j s' Hj. pose proof REP as (_ & _ & _ & _ & _ & SECR & _). destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & PER & _).
  destruct (PER j s' Hj) as (_ & P2 & _ & _ & _ & _ & Lo & Hi2 & Q & P0).
  assert (Hn' : 1 <= sc_n s') by (destruct (sc_quar s'); [destruct Q as ((bb & _ & _ & _ & _ & X) & _)|destruct Q as (_ & (bb & _ & _ & _ & _ & X) & _)]; clear - X; lia).
  destruct (LIVE _ P2) as (L0 & L1 & L2 & L3 & OB). cbn [fst snd] in L0, L1, L2, L3, OB.
  split; [exact P2|]. split; [exact Lo|]. split; [exact Hi2|]. split; [exact Hn'|]. split; [exact P0|]. split; [exact L0|]. split; [exact L2|]. split; [exact L3|exact OB].
Qed.

Lemma art_frepP_me :
  In (mb, ms) (art_live (g_log FSG G)) /\ mb + 4096 <= u - 16 /\ u + 8 * qr <= mb + ms /\ 0x69c000 <= mb /\ 0 < mb /\ mb + ms <= rn_HI rn
  /\ (mb + ms <= 0x7fff7000 \/ 0x10007fff8000 <= mb) /\ mb mod 4096 = 0 /\ ms mod 4096 = 0
  /\ (forall o, In o (art_objs rn) -> apart mb ms (fst o) (snd o)) /\ In s (g_sec FSG G) /\ (i < length (g_sec FSG G))%nat.
Proof.
  destruct KIND as (Hi & Hq & Esu & Esn). destruct (art_frepP_rec i s Hi) as (P2 & Lo & Hi2 & _ & P0 & L0 & L2 & L3 & OB). unfold mb, ms.
  destruct (LIVE3 _ P2) as (A1 & A2). cbn [fst snd] in A1, A2. rewrite Esu in Lo. rewrite Esu, Esn in Hi2.
  assert (Hms8 : (sc_map s + sc_msize s) mod 8 = 0).
  { pose proof (Z.div_mod (sc_map s) 4096 ltac:(lia)) as D1. rewrite A1 in D1. pose proof (Z.div_mod (sc_msize s) 4096 ltac:(lia)) as D2. rewrite A2 in D2.
    replace (sc_map s + sc_msize s) with ((512 * (sc_map s / 4096) + 512 * (sc_msize s / 4096)) * 8) by lia. apply Z_mod_mult. }
  assert (Hu8 : (u + 8 * qr) mod 8 = 0) by (rewrite Eu; replace (16 * q16 + 8 * qr) with ((2 * q16 + qr) * 8) by lia; apply Z_mod_mult).
  assert (Hle : u + 8 * qr <= sc_map s + sc_msize s).
  { pose proof (Z.div_mod (u + 8 * qr) 8 ltac:(lia)) as D1. rewrite Hu8 in D1. pose proof (Z.div_mod (sc_map s + sc_msize s) 8 ltac:(lia)) as D2. rewrite Hms8 in D2.
    clear - D1 D2 Hi2 Hqr. lia. }
  split; [exact P2|]. split; [exact Lo|]. split; [exact Hle|]. split; [exact P0|]. split; [exact L0|]. split; [exact L2|]. split; [exact L3|].
  split; [exact A1|]. split; [exact A2|]. split; [exact OB|]. split; [exact (nth_error_In _ _ Hi)|]. assert (X : nth_error (g_sec FSG G) i <> None) by (rewrite Hi; discriminate). apply nth_error_Some in X. exact X.
Qed.

Lemma art_frepP_live : art_live (g_log FSG G') = List.filter (fun p => negb (fst p =? mb)) (art_live (g_log FSG G)).
Proof. cbn [G' art_gs_freeP g_log]. unfold evs. apply art_live_app_unmap. Qed.

Lemma art_frepP_live_in : forall p, In p (art_live (g_log FSG G')) <-> In p (art_live (g_log FSG G)) /\ fst p <> mb.
Proof.
  intros p. rewrite art_frepP_live, filter_In. destruct (Z.eqb_spec (fst p) mb); cbn [negb]; split; intros H; try tauto. destruct H as [_ H]; discriminate H.
Qed.
Lemma art_frepP_last : exists sl, nth_error (g_sec FSG G) (length (g_sec FSG G) - 1) = Some sl /\ fst (nth (length bl - 1) bl (0, 0)) = sc_map sl /\ In sl (g_sec FSG G).
Proof.
  destruct art_frepP_me as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi).
  destruct (nth_error (g_sec FSG G) (length (g_sec FSG G) - 1)) as [sl|] eqn:E.
  - exists sl. split; [reflexivity|]. split; [|exact (nth_error_In _ _ E)]. unfold bl. rewrite length_map.
    change (0, 0) with (art_sec_b art_dsec). rewrite map_nth. rewrite (nth_error_nth _ _ _ E). reflexivity.
  - exfalso. apply nth_error_None in E. clear - E Hi. lia.
Qed.
Lemma art_frepP_nums :
  0 <= Z.of_nat i /\ 8 * Z.of_nat i + 8 <= 131072 /\ Z.of_nat (length (g_sec FSG G)) <= 16384
  /\ 0 <= mb / 8 /\ mb / 8 + ms / 8 <= 2 ^ 44 /\ mb / 8 <= 2 * q16 /\ 2 * q16 + qr <= mb / 8 + ms / 8 /\ (mb + ms) / 8 = mb / 8 + ms / 8.
Proof.
  destruct art_frepP_me as (_ & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & _ & _ & Hi).
  pose proof REP as (ROK & _ & _ & _ & _ & SECR & _). destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SLEN). rok_open14 ROK. geo_open GEO.
  pose proof (Z.div_mod mb 4096 ltac:(lia)) as Dv1. rewrite A1 in Dv1. pose proof (Z.div_mod ms 4096 ltac:(lia)) as Dv2. rewrite A2 in Dv2.
  assert (E1 : mb / 8 = 512 * (mb / 4096)) by (rewrite Dv1 at 1; replace (4096 * (mb / 4096) + 0) with ((512 * (mb / 4096)) * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
  assert (E2 : ms / 8 = 512 * (ms / 4096)) by (rewrite Dv2 at 1; replace (4096 * (ms / 4096) + 0) with ((512 * (ms / 4096)) * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
  assert (E3 : (mb + ms) / 8 = 512 * (mb / 4096) + 512 * (ms / 4096)).
  { rewrite Dv1, Dv2 at 1. replace (4096 * (mb / 4096) + 0 + (4096 * (ms / 4096) + 0)) with ((512 * (mb / 4096) + 512 * (ms / 4096)) * 8) by lia. rewrite Z_div_mult by lia. reflexivity. }
  assert (E4 : (u - 16) / 8 = 2 * q16 - 2) by (rewrite Eu; replace (16 * q16 - 16) with ((2 * q16 - 2) * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
  assert (E5 : (u + 8 * qr) / 8 = 2 * q16 + qr) by (rewrite Eu; replace (16 * q16 + 8 * qr) with ((2 * q16 + qr) * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
  pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Lo) as M1. pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Hi2) as M2.
  rewrite E3 in M2. rewrite E5 in M2.
  assert (M3 : (mb + 4096) / 8 = 512 * (mb / 4096) + 512) by (rewrite Dv1 at 1; replace (4096 * (mb / 4096) + 0 + 4096) with ((512 * (mb / 4096) + 512) * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
  rewrite M3, E4 in M1.
  clear - Hi SLEN Dv1 Dv2 E1 E2 E3 M1 M2 L0 L2 G2. repeat split; lia.
Qed.

Lemma art_fgapP_img : forall a len,
  (0x10000 <= a /\ a + len <= 0x142ad8 + 56) \/ (0x142d48 <= a /\ a + len <= 0x142d58) \/ (0x142d68 <= a /\ a + len <= 0x147300)
  \/ (0x1c8330 <= a /\ a + len <= 0x1d5b88) \/ (0x1d5b8c <= a /\ a + len <= 0x217fc8) -> art_gap art_freeP_W a len.
Proof.
  intros a len Ha. pose proof I as Hk. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  unfold art_freeP_W, art_free3_W, art_cbr_sec_fp, art_secd_fp. rewrite Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G9; lia) | idtac ].
Qed.
Lemma art_fgapP_tls : forall a len, 0x667fe8 <= a -> a + len <= 0x69c000 -> art_gap art_freeP_W a len.
Proof.
  intros a len Ha Hk. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  unfold art_freeP_W, art_free3_W, art_cbr_sec_fp, art_secd_fp. rewrite Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G9; lia) | idtac ].
Qed.
Lemma art_fgapP_thread : forall a len, rn_t rn <= a -> a + len <= rn_t rn + 4096 ->
  (a + len <= rn_t rn + 2824 \/ (rn_t rn + 2856 <= a /\ a + len <= rn_t rn + 2888) \/ (rn_t rn + 2904 <= a /\ a + len <= rn_t rn + 3168) \/ rn_t rn + 3169 <= a) ->
  art_gap art_freeP_W a len.
Proof.
  intros a len Ha Hk Hlo. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  pose proof (OB (rn_t rn, 4096) (art_inP_t rn)) as Ot. pose proof (QB (rn_t rn, 4096) (art_inP_t rn)) as Qt. cbn [fst snd] in Ot, Qt.
  unfold art_freeP_W, art_free3_W, art_cbr_sec_fp, art_secd_fp. rewrite Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Ot; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Qt; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G9; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G10; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Al2t; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Abt; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Apt; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Hlo; lia) | idtac ].
Qed.
Lemma art_fgapP_ctx : forall a len, rn_ctx rn <= a -> a + len <= rn_ctx rn + 4096 -> art_gap art_freeP_W a len.
Proof.
  intros a len Ha Hk. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  pose proof (OB (rn_ctx rn, 4096) (art_inP_ctx rn)) as Oc. pose proof (QB (rn_ctx rn, 4096) (art_inP_ctx rn)) as Qc. cbn [fst snd] in Oc, Qc.
  unfold art_freeP_W, art_free3_W, art_cbr_sec_fp, art_secd_fp. rewrite Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Oc; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Qc; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G15; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G16; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G18; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Al2c; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Abc; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Apc; lia) | idtac ].
Qed.
Lemma art_fgapP_kspace : forall a len, rn_spb rn <= a -> a + len <= rn_spb rn + 2 ^ 37 + 4096 -> art_gap art_freeP_W a len.
Proof.
  intros a len Ha Hk. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  pose proof (OB (rn_kbase rn, 0x2000011000) (art_inP_kbase rn)) as Ok. pose proof (QB (rn_kbase rn, 0x2000011000) (art_inP_kbase rn)) as Qk. cbn [fst snd] in Ok, Qk.
  unfold art_freeP_W, art_free3_W, art_cbr_sec_fp, art_secd_fp. rewrite Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Ok; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Qk; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G11; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Al2k; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Abk; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Apk; lia) | idtac ].
Qed.
Lemma art_fgapP_kshadow : forall a len, 2147450880 + 8192 * rn_qs rn <= a -> a + len <= 2147450880 + 8192 * rn_qs rn + 2 ^ 34 + 512 -> art_gap art_freeP_W a len.
Proof.
  intros a len Ha Hk. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  pose proof (OB (rn_kbase rn, 0x2000011000) (art_inP_kbase rn)) as Ok. pose proof (QB (rn_kbase rn, 0x2000011000) (art_inP_kbase rn)) as Qk. cbn [fst snd] in Ok, Qk.
  assert (SH : mb / 8 + ms / 8 <= 8192 * rn_qs rn \/ 8192 * rn_qs rn + 2 ^ 34 + 512 <= mb / 8).
  { unfold apart in Ok. destruct Ok as [X|X].
    - left. rewrite <- N8. apply (Z.le_trans _ (rn_kbase rn / 8)); [apply Z.div_le_mono; [lia0|exact X]|]. apply Z.div_le_upper_bound; [lia0|]. clear - Kspb Espb. lia.
    - right. apply Z.div_le_lower_bound; [lia0|]. clear - X Kspb Espb. lia. }
  unfold art_freeP_W, art_free3_W, art_cbr_sec_fp, art_secd_fp. rewrite Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Ok; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G10; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Al2s; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Abs; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH L3; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Q6; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Papp; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH SH; lia) | idtac ].
Qed.
Lemma art_fgapP_grant : forall p a len, In p (art_live (g_log FSG G)) -> fst p <> mb -> fst p + 32 <= a -> a + len <= fst p + snd p -> art_gap art_freeP_W a len.
Proof.
  intros p a len Hp Hne Ha Hk. destruct (LIVE p Hp) as (Hp0 & Hp1 & HpH & Hps & HpO).
  pose proof (HpO (rn_t rn, 4096) (art_inP_t rn)) as Hpt. pose proof (HpO (rn_l2 rn, 2 ^ 20) (art_inP_l2 rn)) as Hpl. pose proof (HpO (rn_blk rn, 2 ^ 23) (art_inP_blk rn)) as Hpb.
  pose proof (HpO (rn_parr rn, 2 ^ 23) (art_inP_parr rn)) as Hpp. pose proof (HpO (0x13f000, 0x55d000) (art_inP_img4 rn)) as Hpi. cbn [fst snd] in Hpt, Hpl, Hpb, Hpp, Hpi.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  pose proof (LIVE2 _ _ Hp Pme Hne) as Hpm. cbn [fst snd] in Hpm.
  assert (Hpq : fst p = sc_map sl \/ apart (fst p) (snd p) (sc_map sl) (sc_msize sl)).
  { destruct (Z.eq_dec (fst p) (sc_map sl)) as [E|NE]; [left; exact E|right]. exact (LIVE2 _ _ Hp Qme NE). }
  unfold art_freeP_W, art_free3_W, art_cbr_sec_fp, art_secd_fp. rewrite Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Hpm; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Hpq; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Hpt; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Hps; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Hpl; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Hpb; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Hpp; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Hpi; lia) | idtac ].
Qed.
Lemma art_fgapP_fs : forall a len, ar_fs (rn_ar rn) <= a -> a + len <= ar_fs (rn_ar rn) + FS_BYTES -> art_gap art_freeP_W a len.
Proof.
  intros a len Ha Hk. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  pose proof (OB (ar_fs (rn_ar rn), FS_BYTES) (art_inP_fs rn)) as Of. pose proof (QB (ar_fs (rn_ar rn), FS_BYTES) (art_inP_fs rn)) as Qf. cbn [fst snd] in Of, Qf. unfold FS_BYTES in *.
  unfold art_freeP_W, art_free3_W, art_cbr_sec_fp, art_secd_fp. rewrite Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Of; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Qf; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Aft; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Afl; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Afb; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Afp; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Fimg; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Fapp; lia) | idtac ].
Qed.
Lemma art_fgapP_dtls : forall a len, rn_dtls rn <= a -> a + len <= rn_dtls rn + 4096 -> art_gap art_freeP_W a len.
Proof.
  intros a len Ha Hk. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  pose proof (OB (rn_dtls rn, 4096) (art_inP_dtls rn)) as Od. pose proof (QB (rn_dtls rn, 4096) (art_inP_dtls rn)) as Qd. cbn [fst snd] in Od, Qd.
  unfold art_freeP_W, art_free3_W, art_cbr_sec_fp, art_secd_fp. rewrite Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Od; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Qd; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Adt; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Adl; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Adb; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Adp; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH D2; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH D3; lia) | idtac ].
Qed.

Lemma art_fgapP3_img : forall a len, 0x10000 <= a -> (a + len <= 0x147300 \/ (0x1c8330 <= a /\ a + len <= 0x1d5b88) \/ (0x1d5b8c <= a /\ a + len <= 0x217fc8) \/ (0x667fe8 <= a /\ a + len <= 0x69c000)) -> art_gap (art_free3_W Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn)) a len.
Proof.
  intros a len Ha Hk. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  unfold art_free3_W. rewrite ?Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G9; lia) | idtac ].
Qed.
Lemma art_fgapP3_thread : forall a len, rn_t rn <= a -> a + len <= rn_t rn + 4096 -> (a + len <= rn_t rn + 2824 \/ (rn_t rn + 2840 <= a /\ a + len <= rn_t rn + 3168) \/ rn_t rn + 3169 <= a) -> art_gap (art_free3_W Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn)) a len.
Proof.
  intros a len Ha Hk Hlo. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  pose proof (OB (rn_t rn, 4096) (art_inP_t rn)) as Ot. pose proof (QB (rn_t rn, 4096) (art_inP_t rn)) as Qt. cbn [fst snd] in Ot, Qt.
  unfold art_free3_W. rewrite ?Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Ot; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G9; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G10; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Al2t; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Abt; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Hlo; lia) | idtac ].
Qed.
Lemma art_fgapP3_ctx : forall a len, rn_ctx rn <= a -> a + len <= rn_ctx rn + 4096 -> art_gap (art_free3_W Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn)) a len.
Proof.
  intros a len Ha Hk. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  pose proof (OB (rn_ctx rn, 4096) (art_inP_ctx rn)) as Oc. pose proof (QB (rn_ctx rn, 4096) (art_inP_ctx rn)) as Qc. cbn [fst snd] in Oc, Qc.
  unfold art_free3_W. rewrite ?Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Oc; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G15; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G16; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G18; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Al2c; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Abc; lia) | idtac ].
Qed.
Lemma art_fgapPc_img : forall a len, 0x10000 <= a -> (a + len <= 0x142ad8 + 56 \/ (0x142d48 <= a /\ a + len <= 0x142d58) \/ (0x142d68 <= a /\ a + len <= 0x69c000)) -> art_gap (art_cbr_sec_fp (Sp - 2208) (rn_t rn) (rn_parr rn) (Z.of_nat i) (fst (nth (length bl - 1) bl (0, 0))) mb ms) a len.
Proof.
  intros a len Ha Hk. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  unfold art_cbr_sec_fp, art_secd_fp. rewrite ?Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G9; lia) | idtac ].
Qed.
Lemma art_fgapPc_thread : forall a len, rn_t rn <= a -> a + len <= rn_t rn + 4096 -> (a + len <= rn_t rn + 2840 \/ (rn_t rn + 2856 <= a /\ a + len <= rn_t rn + 2888) \/ rn_t rn + 2904 <= a) -> art_gap (art_cbr_sec_fp (Sp - 2208) (rn_t rn) (rn_parr rn) (Z.of_nat i) (fst (nth (length bl - 1) bl (0, 0))) mb ms) a len.
Proof.
  intros a len Ha Hk Hlo. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  pose proof (OB (rn_t rn, 4096) (art_inP_t rn)) as Ot. pose proof (QB (rn_t rn, 4096) (art_inP_t rn)) as Qt. cbn [fst snd] in Ot, Qt.
  unfold art_cbr_sec_fp, art_secd_fp. rewrite ?Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Ot; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Qt; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G9; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G10; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Apt; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Hlo; lia) | idtac ].
Qed.
Lemma art_fgapPc_ctx : forall a len, rn_ctx rn <= a -> a + len <= rn_ctx rn + 4096 -> art_gap (art_cbr_sec_fp (Sp - 2208) (rn_t rn) (rn_parr rn) (Z.of_nat i) (fst (nth (length bl - 1) bl (0, 0))) mb ms) a len.
Proof.
  intros a len Ha Hk. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  pose proof (OB (rn_ctx rn, 4096) (art_inP_ctx rn)) as Oc. pose proof (QB (rn_ctx rn, 4096) (art_inP_ctx rn)) as Qc. cbn [fst snd] in Oc, Qc.
  unfold art_cbr_sec_fp, art_secd_fp. rewrite ?Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Oc; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Qc; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G15; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G16; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH G18; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Apc; lia) | idtac ].
Qed.
Lemma art_fgapPc_l2 : forall a len, rn_l2 rn <= a -> a + len <= rn_l2 rn + 2 ^ 20 -> art_gap (art_cbr_sec_fp (Sp - 2208) (rn_t rn) (rn_parr rn) (Z.of_nat i) (fst (nth (length bl - 1) bl (0, 0))) mb ms) a len.
Proof.
  intros a len Ha Hk. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  pose proof (OB (rn_l2 rn, 2 ^ 20) (art_inP_l2 rn)) as Ol. pose proof (QB (rn_l2 rn, 2 ^ 20) (art_inP_l2 rn)) as Ql. cbn [fst snd] in Ol, Ql.
  unfold art_cbr_sec_fp, art_secd_fp. rewrite ?Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Ol; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Ql; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Al2t; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Al2s; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Apl; lia) | idtac ].
Qed.
Lemma art_fgapPc_blk : forall a len, rn_blk rn <= a -> a + len <= rn_blk rn + 2 ^ 23 -> art_gap (art_cbr_sec_fp (Sp - 2208) (rn_t rn) (rn_parr rn) (Z.of_nat i) (fst (nth (length bl - 1) bl (0, 0))) mb ms) a len.
Proof.
  intros a len Ha Hk. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  pose proof (OB (rn_blk rn, 2 ^ 23) (art_inP_blk rn)) as Ob. pose proof (QB (rn_blk rn, 2 ^ 23) (art_inP_blk rn)) as Qb. cbn [fst snd] in Ob, Qb.
  unfold art_cbr_sec_fp, art_secd_fp. rewrite ?Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: first [ (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Ob; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Qb; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Abt; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Abs; lia) | (clear - Ha Hk HS HS47 G1 G2 G4 G6 G7 G8 G13 G14 Espb Eris Kspb Kend Plo Phi Il2 Iblk Dl2 Dblk Lo Hi2 P0 L0 L2 Hn Hqr Eu N1 N2 N3 N4 N5 N6 N7 N8 Q0 Q1 Q2 Q3 Q4 Q5 Flo Fhi D0 D1 Hp0 Hp1 HpH Apb; lia) | idtac ].
Qed.

#[using="M7 M' b1 kb Dz REP KIND Eu Hn Hqr Hb1 HS HS47 Edep OUT HDz LIVE LIVE2 LIVE3 Hother"] Lemma art_frepP_agree : art_agree art_freeP_W M M'.
Proof. destruct OUT as (_ & A07 & _ & _ & _ & _ & _ & A7' & _). exact (art_agree_trans _ _ _ _ _ A07 A7'). Qed.

Lemma art_frepP_cell_img : forall a (j : nat) v,
  (0x10000 <= a /\ a + Z.of_nat j <= 0x142ad8 + 56) \/ (0x142d48 <= a /\ a + Z.of_nat j <= 0x142d58) \/ (0x142d68 <= a /\ a + Z.of_nat j <= 0x147300)
  \/ (0x1c8330 <= a /\ a + Z.of_nat j <= 0x1d5b88) \/ (0x1d5b8c <= a /\ a + Z.of_nat j <= 0x217fc8) ->
  cellA M a j v -> cellA M' a j v.
Proof. intros a j v Ha C. apply (art_cell_tr art_freeP_W M M' a j v art_frepP_agree (art_fgapP_img a _ Ha)); [clear - Ha; lia|clear - Ha; lia|exact C]. Qed.
Lemma art_frepP_cell_tls : forall a (j : nat) v, 0x667fe8 <= a -> a + Z.of_nat j <= 0x69c000 -> cellA M a j v -> cellA M' a j v.
Proof. intros a j v Ha Hk C. apply (art_cell_tr art_freeP_W M M' a j v art_frepP_agree (art_fgapP_tls a _ Ha Hk)); [clear - Ha; lia|clear - Hk; lia|exact C]. Qed.

Lemma art_frepP_statics : art_rt_statics rn M'.
Proof.
  pose proof REP as (ROK & ST & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct ST as (PC & LY & T & RO & RZ & DR & TG & CS).
  unfold art_rt_statics.
  split. { unfold art_prim_consts in *. decompose [and] PC. repeat split; (apply art_frepP_cell_img; [lia0c|assumption]). }
  split. { unfold art_layout in *. decompose [and] LY. repeat split; (apply art_frepP_cell_img; [lia0c|assumption]). }
  split. { apply (art_tsd_tr _ M M' _ _ _ _ _ art_frepP_agree); [apply art_fgapP_img; lia0|apply art_fgapP_tls; clear - Htpd G20; lia|apply art_fgapP_tls; clear - Htsdd G22 Hkey; lia|apply art_fgapP_ctx; lia0|exact T]. }
  split. { unfold art_alloc_rodata in *. decompose [and] RO. repeat split; (apply art_frepP_cell_img; [lia0c|assumption]). }
  split. { unfold art_rz_rodata in *. decompose [and] RZ. repeat split; (apply art_frepP_cell_img; [lia0c|assumption]). }
  split. { unfold DRoD in *. decompose [and] DR. repeat split; (apply art_frepP_cell_img; [lia0c|assumption]). }
  split. { destruct TG as (GN & T1 & T2). split; [|split].
           - intros a Ha. assert (EU : U (Z_to_bv 64 a) = a) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); apply Z.mod_small; clear - Ha; lia).
             rewrite (art_frepP_agree (Z_to_bv 64 a)); [exact (GN a Ha)|]. rewrite EU. apply (art_gap_out _ a 1); [apply art_fgapP_img; clear - Ha; lia|lia0].
           - apply art_frepP_cell_tls; [lia0|lia0c|exact T1].
           - apply art_frepP_cell_tls; [lia0|lia0c|exact T2]. }
  decompose [and] CS. repeat split; (apply art_frepP_cell_img; [lia0c|assumption]).
Qed.

Lemma art_frepP_thread : art_rt_thread rn M'.
Proof.
  pose proof REP as (ROK & _ & TH & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct TH as (Wt & C1 & C2 & C3 & C4 & C5 & C6 & C7). destruct OUT as (GR7 & _ & _ & _ & _ & _ & Cunw7 & A7' & _ & _ & WRT & _).
  destruct art_frepP_me as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OB & _). pose proof (OB (rn_t rn, 4096) (art_inP_t rn)) as Ot. cbn [fst snd] in Ot.
  assert (TT : forall a (j : nat) v, rn_t rn <= a -> a + Z.of_nat j <= rn_t rn + 4096 -> a + Z.of_nat j <= rn_t rn + 2824 -> cellA M a j v -> cellA M' a j v).
  { intros a j v Ha Hk Hlo C. apply (art_cell_tr art_freeP_W M M' a j v art_frepP_agree (art_fgapP_thread a _ Ha Hk (or_introl Hlo))); [clear - Ha G7; lia|clear - Hk G8 G2; lia|exact C]. }
  unfold art_rt_thread. split. { apply WRT; [clear - G7; lia|clear - G8 G2; lia|unfold apart in Ot |- *; clear - Ot; lia|eapply wr_grows; [exact GR7|exact Wt]]. }
  split; [apply TT; [lia0|lia0c|lia0c|exact C1]|].
  split. { apply (art_cell_tr art_freeP_W M M' (rn_ctx rn + 8) 4%nat 0 art_frepP_agree (art_fgapP_ctx (rn_ctx rn + 8) 4 ltac:(lia0) ltac:(lia0))); [clear - G13; lia|clear - G14 G2; cbn; lia|exact C2]. }
  split; [apply TT; [lia0|lia0c|lia0c|exact C3]|]. split; [apply TT; [lia0|lia0c|lia0c|exact C4]|].
  split; [apply TT; [lia0|lia0c|lia0c|exact C5]|].
  split. { apply (art_cell_tr _ M7 M' _ 1%nat _ A7' (art_fgapPc_thread (rn_t rn + 3168) 1 ltac:(lia0) ltac:(lia0) ltac:(right; right; lia0))); [clear - G7; lia|clear - G8 G2; cbn; lia|exact Cunw7]. }
  apply art_frepP_cell_tls; [clear - Htpd Hloff; lia|clear - Hloff''; cbn; lia|exact C7].
Qed.

Lemma art_frepP_depot : forall D, DInvK (rn_l2 rn) (rn_blk rn) kb D M7 -> DInvK (rn_l2 rn) (rn_blk rn) kb D M'.
Proof.
  intros D DK. destruct OUT as (_ & _ & _ & _ & _ & _ & _ & A7' & _). pose proof REP as (ROK & _). rok_open14 ROK.
  apply (DInvK_frame (rn_l2 rn) (rn_blk rn) D _ M7 M' DK). intros x Dx. apply A7'. revert Dx. apply art_dpriv_out.
  - apply art_fgapPc_img; lia0.
  - apply art_fgapPc_l2; lia0.
  - apply art_fgapPc_blk; lia0.
Qed.
Lemma art_frepP_rt_depot : art_rt_depot FSG rn G' M'.
Proof. destruct OUT as (_ & _ & DI7 & _). unfold art_rt_depot. cbn [G' art_gs_freeP g_depot]. exact (DInvK_incl _ _ _ _ _ _ (art_frepP_depot _ DI7) HDz). Qed.
#[using="M7 M' b1 kb Dz REP KIND Eu Hn Hqr Hb1 HS HS47 Edep OUT HDz LIVE LIVE2 LIVE3 Hother"] Lemma art_frepP_dinv : DInvK (rn_l2 rn) (rn_blk rn) kb Dz M'.
Proof. destruct OUT as (_ & _ & DI7 & _). exact (art_frepP_depot _ DI7). Qed.

Lemma art_frepP_ia : art_rt_ia FSG G' M'.
Proof.
  destruct OUT as (_ & _ & _ & _ & Cia7 & Ctab7 & _ & A7' & _). unfold art_rt_ia. cbn [G' art_gs_freeP g_ia].
  split. { apply (art_cell_tr _ M7 M' _ 4%nat _ A7' (art_fgapPc_img 0x1d5b88 4 ltac:(lia0) ltac:(lia0))); [lia0|lia0c|exact Cia7]. }
  split; [|intros X; discriminate X]. intros _ k Hk. replace (0x147300 + 8 + 8 * k) with (0x147308 + 8 * k) by (lia0).
  apply (art_cell_tr _ M7 M' _ 8%nat _ A7' (art_fgapPc_img (0x147308 + 8 * k) 8 ltac:(clear - Hk; lia) ltac:(clear -Hk; lia))); [clear - Hk; lia|clear - Hk; cbn; lia|exact (Ctab7 k Hk)].
Qed.

Lemma art_frepP_primary : art_rt_primary FSG rn G' M'.
Proof.
  pose proof REP as (ROK & _ & _ & PRIM & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct PRIM as (PH & PRIM & Wsh). destruct OUT as (GR7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & WRT & _).
  destruct art_frepP_me as (_ & _ & _ & _ & _ & _ & L3 & _ & _ & OB & _). pose proof (OB (rn_kbase rn, 0x2000011000) (art_inP_kbase rn)) as Ok. cbn [fst snd] in Ok.
  unfold art_rt_primary. cbn [G' art_gs_freeP g_inited g_cls].
  split. { apply (art_pc_hdr_tr art_freeP_W (rn_t rn + 208) _ M M' ltac:(clear - G7; lia) ltac:(clear - G8 G2; lia) art_frepP_agree); [|exact PH].
           intros c Hc. apply art_fgapP_thread; clear - Hc; lia. }
  split.
  2: { apply WRT; [clear - Espb G4; lia|clear - Kspb Kend G2 G4 Espb; lia| |eapply wr_grows; [exact GR7|exact Wsh]].
       unfold apart, BIGSHADOW_LO, BIGSHADOW_HI in *. clear - L3 Kspb Kend G2 G4 Espb. lia. }
  intros c0 Hc0. destruct (PRIM c0 Hc0) as (RC0 & OK0 & Hin0 & Hk0 & Hau0).
  split; [|split; [exact OK0|split; [exact Hin0|split; [exact Hk0|exact Hau0]]]].
  destruct OK0 as (Hl16 & _ & _ & _ & _ & Hmu3 & _ & (_ & Hmfa1) & Hnf4 & _).
  destruct RC0 as [[C0 CW] (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu)].
  assert (TC : forall a (j : nat) v, (rn_t rn + 208 + 80 * c0 <= a /\ a + Z.of_nat j <= rn_t rn + 208 + 80 * c0 + 80) -> cellA M a j v -> cellA M' a j v).
  { intros a j v Ha C. apply (art_cell_tr art_freeP_W M M' a j v art_frepP_agree); [apply art_fgapP_thread; clear - Ha Hc0; lia|clear - Ha G7 Hc0; lia|clear - Ha G8 G2 Hc0; lia|exact C]. }
  assert (TR : forall a (j : nat) v, (rn_spb rn + c0 * 2 ^ 32 + 3758096384 <= a /\ a + Z.of_nat j <= rn_spb rn + c0 * 2 ^ 32 + 2 ^ 32 \/ rn_ris rn + 128 * c0 <= a /\ a + Z.of_nat j <= rn_ris rn + 128 * c0 + 128) ->
              cellA M a j v -> cellA M' a j v).
  { intros a j v Ha C. apply (art_cell_tr art_freeP_W M M' a j v art_frepP_agree); [apply art_fgapP_kspace; clear - Ha Hc0 Eris; lia|clear - Ha G4 G6 Eris Hc0; lia|clear - Ha G6 Eris G2 Hc0; lia|exact C]. }
  assert (WK : forall a k, rn_spb rn <= a -> a + k <= rn_spb rn + 2 ^ 37 + 4096 -> wrA M a k -> wrA M' a k).
  { intros a k Ha Hk W0. apply WRT; [clear - Ha G4; lia|clear - Hk Kspb Kend G2; lia|unfold apart in Ok |- *; clear - Ok Ha Hk Kspb; lia|eapply wr_grows; [exact GR7|exact W0]]. }
  split; [split|].
  + apply TC; [cbn; lia0|exact C0].
  + intros j Hj. apply TC; [cbn; clear - Hj Hl16; lia|exact (CW j Hj)].
  + unfold art_region_rep.
    split; [apply TR; [right; cbn; lia0|exact Rmx]|]. split; [apply TR; [right; cbn; lia0|exact Rnf]|]. split; [apply TR; [right; cbn; lia0|exact Rmfa]|].
    split; [apply TR; [right; cbn; lia0|exact Rau]|]. split; [apply TR; [right; cbn; lia0|exact Ram]|]. split; [apply TR; [right; cbn; lia0|exact Rmu]|].
    split; [apply TR; [right; cbn; lia0|exact Rmm]|]. split; [apply TR; [right; cbn; lia0|exact Rna]|]. split; [apply TR; [right; cbn; lia0|exact Rnfr]|].
    split. { intros j Hj. apply TR; [left; cbn; clear - Hj Hnf4 Hmfa1; lia|exact (Rfa j Hj)]. }
    split; [apply WK; [clear - Hc0 Eris; lia|clear - Hc0 Eris; lia|exact Wr]|]. split; [apply WK; [clear - Hc0; lia|clear - Hc0 Hmfa1; lia|exact Wfa]|apply WK; [clear - Hc0; lia|clear - Hc0 Hmu3; lia|exact Wu]].
Qed.

Lemma art_frepP_kcell : forall a (j : nat) v, rn_spb rn <= a -> a + Z.of_nat j <= rn_spb rn + 2 ^ 37 + 4096 -> cellA M a j v -> cellA M' a j v.
Proof.
  intros a j v Ha Hk C. pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  apply (art_cell_tr art_freeP_W M M' a j v art_frepP_agree (art_fgapP_kspace a _ Ha Hk)); [clear - Ha G4; lia|clear - Hk Kspb Kend G2; lia|exact C].
Qed.
Lemma art_frepP_kbyte : forall a v, rn_spb rn <= a -> a < rn_spb rn + 2 ^ 37 + 4096 -> byte_at M (HeapIfaceA.S a) v -> byte_at M' (HeapIfaceA.S a) v.
Proof.
  intros a v Ha Hk B. pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  assert (E8 : rn_spb rn / 8 = 8192 * rn_qs rn) by (rewrite Espb; replace (65536 * rn_qs rn) with ((8192 * rn_qs rn) * 8) by (lia0); rewrite Z_div_mult by (lia0); reflexivity).
  pose proof (Z.div_le_mono _ _ 8 ltac:(lia0) Ha) as X1. rewrite E8 in X1.
  assert (X2 : a / 8 <= 8192 * rn_qs rn + 2 ^ 34 + 511).
  { apply (Z.le_trans _ ((rn_spb rn + 2 ^ 37 + 4095) / 8)); [apply Z.div_le_mono; clear - Hk; lia|].
    rewrite Espb. replace (65536 * rn_qs rn + 2 ^ 37 + 4095) with (7 + (8192 * rn_qs rn + 2 ^ 34 + 511) * 8) by (lia0). rewrite Z.div_add by (lia0). change (7 / 8) with 0. lia0. }
  assert (R1 : 2147450880 + 8192 * rn_qs rn <= HeapIfaceA.S a) by (unfold HeapIfaceA.S, HeapIfaceA.SB; clear - X1; lia).
  assert (R2 : HeapIfaceA.S a + 1 <= 2147450880 + 8192 * rn_qs rn + 2 ^ 34 + 512) by (unfold HeapIfaceA.S, HeapIfaceA.SB; clear - X2; lia).
  apply (art_byte_at_eq M M'); [|exact B]. apply art_frepP_agree. rewrite art_u_lit by (clear - R1 R2 Kspb Kend G2 G4 Espb; lia).
  apply (art_gap_out _ (HeapIfaceA.S a) 1); [apply art_fgapP_kshadow; [exact R1|exact R2]|lia0].
Qed.
Lemma art_frepP_kshblk : forall u0 n0, rn_spb rn <= u0 -> u0 + n0 <= rn_spb rn + 2 ^ 37 -> 0 < n0 -> HAJ.shadow_blkR M u0 n0 -> HAJ.shadow_blkR M' u0 n0.
Proof.
  intros u0 n0 H0 H1 Hn0 SH. apply (shadow_blkR_tby M M' u0 n0 Hn0); [|exact SH]. intros j Hj0 Hj v B.
  pose proof (art_S_blk_hi u0 n0 j Hn0 Hj) as B1.
  assert (E : HeapIfaceA.S u0 + j = HeapIfaceA.S (u0 + j * 8)) by (unfold HeapIfaceA.S, HeapIfaceA.SB; rewrite Z.div_add by (lia0); lia0).
  rewrite E in B |- *. apply (art_frepP_kbyte (u0 + j * 8) v); [clear - H0 Hj0; lia| |exact B].
  unfold HeapIfaceA.S, HeapIfaceA.SB in B1.
  pose proof (Z.div_mod u0 8 ltac:(lia0)) as D8. pose proof (Z.mod_pos_bound u0 8 ltac:(lia0)) as M8.
  pose proof (Z.div_mod (u0 + n0 - 1) 8 ltac:(lia0)) as D9. pose proof (Z.mod_pos_bound (u0 + n0 - 1) 8 ltac:(lia0)) as M9.
  clear - B1 D8 M8 D9 M9 H1 Hj0. lia.
Qed.
Lemma art_swap_remove_keepsP : forall (A : Type) (d : A) i0 (l : list A) x, (i0 < length l)%nat -> In x l -> x <> nth i0 l d -> In x (art_swap_remove d i0 l).
Proof.
  intros A d i0 l x Hi0 Hx Hne. destruct (In_nth l x d Hx) as (j & Hj & Ej). unfold art_swap_remove. apply in_map_iff.
  destruct (Nat.eq_dec j i0) as [E|NE]; [subst j; exfalso; exact (Hne (eq_sym Ej))|].
  destruct (Nat.eq_dec j (length l - 1)) as [EL|NL].
  - exists i0. rewrite Nat.eqb_refl. split; [rewrite <- EL; exact Ej|]. apply in_seq. clear - Hi0 Hj NE EL. lia.
  - exists j. destruct (Nat.eqb_spec j i0) as [E2|_]; [contradiction|]. split; [exact Ej|]. apply in_seq. clear - Hj NL. lia.
Qed.

Lemma art_frepP_chunks : art_rt_chunks FSG rn G' (lb_remove u LB) M'.
Proof.
  pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & CH & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi). pose proof (OB (rn_kbase rn, 0x2000011000) (art_inP_kbase rn)) as Ok. cbn [fst snd] in Ok.
  unfold art_rt_chunks. cbn [G' art_gs_freeP g_cls g_st g_qt g_qg]. intros c Hc. cbv zeta.
  destruct (CH c Hc) as (C1 & C2 & C3 & C4). cbv zeta in C1, C2, C3, C4.
  destruct (PRIM c Hc) as (_ & OK & _). destruct OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _). destruct (art_class_size_facts c Hc) as (S1 & S16).
  split. { intros x Hx Hx8. apply art_frepP_kbyte; [clear - Hc Hx Hau0; lia|clear - Hc Hx Hmu3; lia|exact (C1 x Hx Hx8)]. }
  split; [exact C2|]. split; [exact C3|].
  intros w OKw. specialize (C4 w OKw). pose proof OKw as (Hw0 & Hwau & _).
  assert (KC : forall a (j : nat) v, rn_spb rn + c * 2 ^ 32 <= a -> a + Z.of_nat j <= rn_spb rn + c * 2 ^ 32 + 2 ^ 32 -> cellA M a j v -> cellA M' a j v).
  { intros a j v Ha Hk C. apply art_frepP_kcell; [clear - Ha Hc; lia|clear - Hk Hc; lia|exact C]. }
  assert (HDR : forall u0 n0 st, rn_spb rn + c * 2 ^ 32 + 16 <= u0 -> u0 <= rn_spb rn + c * 2 ^ 32 + 2 ^ 32 -> art_chunk_hdr M u0 n0 st -> art_chunk_hdr M' u0 n0 st).
  { intros u0 n0 st Hu0 Hu1 (bb & Hbb & Htb & Ch & Cn' & Hn'). exists bb. split; [exact Hbb|]. split; [exact Htb|].
    split; [apply KC; [clear - Hu0; lia|clear - Hu1; cbn; lia|exact Ch]|]. split; [apply KC; [clear - Hu0; lia|clear - Hu1; cbn; lia|exact Cn']|exact Hn']. }
  assert (LCH : forall u0, art_lch M (rn_spb rn + c * 2 ^ 32 + 16 * w) u0 -> art_lch M' (rn_spb rn + c * 2 ^ 32 + 16 * w) u0).
  { intros u0 LC NE. destruct (LC NE) as (X1 & X2). split; (apply KC; [clear - Hw0; lia|clear - Hwau Haumu Hmu3 S1; cbn; lia|assumption]). }
  assert (BY : byte_at M (HeapIfaceA.S (rn_spb rn + c * 2 ^ 32 + 16 * w)) 250 -> byte_at M' (HeapIfaceA.S (rn_spb rn + c * 2 ^ 32 + 16 * w)) 250).
  { intros B. apply art_frepP_kbyte; [clear - Hc Hw0; lia|clear - Hc Hwau Haumu Hmu3 S1; lia|exact B]. }
  destruct (g_st FSG G c w) as [|u0 n0|u0 n0|].
  - destruct C4 as (X1 & X2). split; [exact X1|exact (BY X2)].
  - destruct C4 as (X1 & X2 & X3 & X4 & X5 & X6 & X7). pose proof X4 as (?bq & _ & _ & _ & _ & Hn0).
    split. { apply (art_lb_remove_keep0 u); [exact X1|]. cbn [fst]. intros E. unfold apart in Ok. clear - Ok E X2 X3 Lo Hi2 Hc Hw0 Hwau Haumu Hmu3 S1 Kspb Hn Hqr Hn0. lia. }
    split; [exact X2|]. split; [exact X3|]. split; [apply HDR; [clear - X2 Hw0; lia|clear - X3 Hwau Haumu Hmu3 Hn0; lia|exact X4]|].
    split; [apply art_frepP_kshblk; [clear - X2 Hc Hw0; lia|clear - X3 Hc Hwau Haumu Hmu3; lia|clear - Hn0; lia|exact X5]|]. split; [exact (BY X6)|exact (LCH _ X7)].
  - destruct C4 as (X2 & X3 & X4 & X5 & X6 & X7). pose proof X4 as (?bq & _ & _ & _ & _ & Hn0).
    split; [exact X2|]. split; [exact X3|]. split; [apply HDR; [clear - X2 Hw0; lia|clear - X3 Hwau Haumu Hmu3 Hn0; lia|exact X4]|].
    split; [exact X5|]. split; [exact (BY X6)|exact (LCH _ X7)].
  - exact C4.
Qed.

Lemma art_frepP_quar : art_rt_quar FSG rn G' M'.
Proof.
  pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _ & _ & QU & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct QU as ((ft & lt & T1 & T2 & T3 & T4 & TL) & (fg & lg & Q1 & Q2 & Q3 & Q4 & QL) & B1 & B2 & F1 & ND & NEB & ITEMS & NDI & BCH).
  destruct (PRIM 24 ltac:(lia0)) as (_ & OK24 & _). pose proof OK24 as (_ & (Hau24 & Haumu24) & _ & _ & _ & Hmu324 & _).
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi). destruct KIND as (Hnth & Hq & Esu & Esn).
  assert (BEQ : forall b0, In b0 (g_qt FSG G ++ g_qg FSG G) -> 0 <= bt_addr b0 /\ bt_addr b0 + 8192 < 2 ^ 64 /\ forall x : word, bt_addr b0 <= U x < bt_addr b0 + 8192 -> M' x = M x).
  { intros b0 Hb0. destruct (BCH b0 Hb0) as (wb & Eb & Vb & Stb). pose proof Vb as (Vb0 & Vb1 & _). rewrite art_class_size_24 in Vb1.
    split; [rewrite Eb; clear - G4 Vb0; lia|]. split; [rewrite Eb; clear - G4 Espb G6 Eris G2 Vb1 Haumu24 Hmu324; lia|]. intros x Hx. rewrite Eb in Hx.
    apply art_frepP_agree. apply (art_gap_out _ (rn_spb rn + 24 * 2 ^ 32 + 16 * wb) 8192); [apply art_fgapP_kspace; clear - Vb0 Vb1 Haumu24 Hmu324; lia|exact Hx]. }
  assert (TT : forall a (k : nat) v, rn_t rn <= a -> a + Z.of_nat k <= rn_t rn + 208 -> cellA M a k v -> cellA M' a k v).
  { intros a k v Ha Hk C. apply (art_cell_tr art_freeP_W M M' a k v art_frepP_agree (art_fgapP_thread a (Z.of_nat k) Ha ltac:(clear - Hk; lia) ltac:(left; clear - Hk; lia))); [clear - Ha G7; lia|clear - Hk G8 G2; lia|exact C]. }
  unfold art_rt_quar. cbn [G' art_gs_freeP g_qt g_qg g_cls g_st g_sec].
  split. { exists ft, lt. split; [apply TT; [lia0|lia0c|exact T1]|]. split; [apply TT; [lia0|lia0c|exact T2]|]. split; [apply TT; [lia0|lia0c|exact T3]|].
           split; [apply TT; [lia0|lia0c|exact T4]|]. apply (art_batch_list_tr M M'); [|exact TL]. intros b0 Hb0. apply BEQ. apply in_or_app. left. exact Hb0. }
  split. { exists fg, lg. split; [apply art_frepP_cell_img; [lia0c|exact Q1]|]. split; [apply art_frepP_cell_img; [lia0c|exact Q2]|].
           split; [apply art_frepP_cell_img; [lia0c|exact Q3]|]. split; [apply art_frepP_cell_img; [lia0c|exact Q4]|].
           apply (art_batch_list_tr M M'); [|exact QL]. intros b0 Hb0. apply BEQ. apply in_or_app. right. exact Hb0. }
  split; [exact B1|]. split; [exact B2|]. split; [apply art_frepP_cell_img; [lia0c|exact F1]|].
  split; [exact ND|]. split; [exact NEB|].
  split. { intros b0 it Hb0 Hit. destruct (ITEMS b0 it Hb0 Hit) as [PRI|(s0 & Hs0 & Hq0 & Eu0 & En0)]; [left; exact PRI|right].
           exists s0. split; [|split; [exact Hq0|split; [exact Eu0|exact En0]]].
           apply art_swap_remove_keepsP; [exact Hi|exact Hs0|]. rewrite (nth_error_nth _ _ art_dsec Hnth). intros ->. rewrite Hq in Hq0. discriminate Hq0. }
  split; [exact NDI|]. exact BCH.
Qed.

Lemma art_frepP_blocks : art_rt_blocks FSG rn G' (lb_remove u LB).
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BL & _). destruct art_frepP_me as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & Hi). destruct KIND as (Hnth & Hq & Esu & Esn).
  unfold art_rt_blocks. cbn [G' art_gs_freeP g_cls g_st g_sec]. intros b0 Hb0. destruct (Hother b0 Hb0) as (Hb & Hne).
  destruct (BL b0 Hb) as [PRI|(s0 & Hs0 & Hq0 & Eu0 & En0)]; [left; exact PRI|right]. exists s0. split; [|split; [exact Hq0|split; [exact Eu0|exact En0]]].
  apply art_swap_remove_keepsP; [exact Hi|exact Hs0|]. rewrite (nth_error_nth _ _ art_dsec Hnth). intros ->. apply Hne. rewrite <- Eu0. exact Esu.
Qed.

Lemma art_frepP_ghost : art_rt_ghost FSG rn G' M'.
Proof.
  pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _ & _ & QU & _ & _ & _ & GH). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct GH as (T1 & T2 & T3 & T4). destruct QU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH).
  destruct (PRIM 24 ltac:(lia0)) as (_ & OK24 & _). pose proof OK24 as (_ & (Hau24 & Haumu24) & _ & _ & _ & Hmu324 & _).
  unfold art_rt_ghost. cbn [G' art_gs_freeP g_qt g_qg g_cls].
  split; [exact T1|]. split; [exact T2|]. split; [|apply art_frepP_cell_img; [lia0c|exact T4]].
  intros b0 Hb0. destruct (BCH b0 Hb0) as (wb & Eb & (Vb0 & Vb1 & _) & _). rewrite art_class_size_24 in Vb1. rewrite Eb.
  apply art_frepP_kbyte; [clear - Vb0; lia|clear - Vb1 Haumu24 Hmu324; lia|rewrite <- Eb; exact (T3 b0 Hb0)].
Qed.

Lemma art_swap_remove_mapP : forall (A B : Type) (f : A -> B) (d : A) i0 (l : list A), map f (art_swap_remove d i0 l) = art_swap_remove (f d) i0 (map f l).
Proof. intros A B f d i0 l. unfold art_swap_remove. rewrite map_map, length_map. apply map_ext. intros j. symmetry. apply map_nth. Qed.
Lemma art_nodup_map_neq : forall (A B : Type) (f : A -> B) (l : list A) x y, List.NoDup (map f l) -> In x l -> In y l -> x <> y -> f x <> f y.
Proof.
  intros A B f l x y ND Hx Hy NE E. apply NE. destruct (In_nth_error _ _ Hx) as (i1 & H1). destruct (In_nth_error _ _ Hy) as (i2 & H2).
  assert (i1 = i2).
  { rewrite NoDup_nth_error in ND. apply ND; [rewrite length_map; apply nth_error_Some; rewrite H1; discriminate|]. rewrite !nth_error_map, H1, H2. cbn. f_equal. exact E. }
  subst i2. rewrite H1 in H2. injection H2 as E2. exact E2.
Qed.

Lemma art_cell8_injP : forall (M0 : word -> option byte) a v w, cellA M0 a 8 v -> cellA M0 a 8 w -> 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 -> v = w.
Proof.
  intros M0 a v w C1 C2 Hv Hw. unfold cell in *. rewrite C1 in C2.
  apply (f_equal (fun o : option (list byte) => match o with Some l => bytes_le_to_Z l | None => 0 end)) in C2.
  rewrite !SeqExec.bytes_le_to_Z_8 in C2. rewrite !art_u_lit in C2 by lia. exact C2.
Qed.
Lemma art_frepP_maps_nodup : List.NoDup (map sc_map (g_sec FSG G)).
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & SECR & _). destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & PER & _ & SLEN).
  rewrite NoDup_nth_error. intros i1 i2 Hi1 E. rewrite length_map in Hi1. rewrite !nth_error_map in E.
  destruct (nth_error (g_sec FSG G) i1) as [s1|] eqn:E1; [|exfalso; apply nth_error_None in E1; clear - E1 Hi1; lia].
  destruct (nth_error (g_sec FSG G) i2) as [s2|] eqn:E2; [|cbn in E; discriminate E]. cbn in E. injection E as E'.
  destruct (PER i1 s1 E1) as (_ & _ & _ & _ & _ & C1 & _). destruct (PER i2 s2 E2) as (_ & _ & _ & _ & _ & C2 & _). rewrite E' in C1.
  pose proof (art_nth_error_lt _ _ _ _ E1) as L1. pose proof (art_nth_error_lt _ _ _ _ E2) as L2.
  apply Nat2Z.inj. apply (art_cell8_injP _ _ _ _ C1 C2); clear - L1 L2 SLEN; lia.
Qed.

Lemma art_frepP_pnums : forall p, In p (art_live (g_log FSG G)) -> fst p <> mb ->
  0 <= fst p / 8 /\ (fst p + snd p) / 8 = fst p / 8 + snd p / 8 /\ fst p / 8 + snd p / 8 <= 2 ^ 44
  /\ (mb / 8 + ms / 8 <= fst p / 8 \/ fst p / 8 + snd p / 8 <= mb / 8).
Proof.
  intros p Hp Hne. destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi). destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  destruct (LIVE p Hp) as (Hp0 & Hp1 & HpH & Hps & HpO). destruct (LIVE3 p Hp) as (B1 & B2). pose proof (LIVE2 _ _ Hp Pme Hne) as Ap. cbn [fst snd] in Ap.
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  pose proof (Z.div_mod (fst p) 4096 ltac:(lia0)) as Dv1. rewrite B1 in Dv1. pose proof (Z.div_mod (snd p) 4096 ltac:(lia0)) as Dv2. rewrite B2 in Dv2.
  assert (E1 : fst p / 8 = 512 * (fst p / 4096)) by (rewrite Dv1 at 1; replace (4096 * (fst p / 4096) + 0) with ((512 * (fst p / 4096)) * 8) by (lia0); rewrite Z_div_mult by (lia0); reflexivity).
  assert (E2 : snd p / 8 = 512 * (snd p / 4096)) by (rewrite Dv2 at 1; replace (4096 * (snd p / 4096) + 0) with ((512 * (snd p / 4096)) * 8) by (lia0); rewrite Z_div_mult by (lia0); reflexivity).
  assert (E3 : (fst p + snd p) / 8 = 512 * (fst p / 4096) + 512 * (snd p / 4096)).
  { rewrite Dv1, Dv2 at 1. replace (4096 * (fst p / 4096) + 0 + (4096 * (snd p / 4096) + 0)) with ((512 * (fst p / 4096) + 512 * (snd p / 4096)) * 8) by (lia0). rewrite Z_div_mult by (lia0). reflexivity. }
  pose proof (Z.div_mod mb 4096 ltac:(lia0)) as Dv3. rewrite A1 in Dv3. pose proof (Z.div_mod ms 4096 ltac:(lia0)) as Dv4. rewrite A2 in Dv4.
  assert (E4 : mb / 8 = 512 * (mb / 4096)) by (rewrite Dv3 at 1; replace (4096 * (mb / 4096) + 0) with ((512 * (mb / 4096)) * 8) by (lia0); rewrite Z_div_mult by (lia0); reflexivity).
  assert (E5 : ms / 8 = 512 * (ms / 4096)) by (rewrite Dv4 at 1; replace (4096 * (ms / 4096) + 0) with ((512 * (ms / 4096)) * 8) by (lia0); rewrite Z_div_mult by (lia0); reflexivity).
  unfold apart in Ap. clear - Hp0 Hp1 HpH G2 Ap Dv1 Dv2 Dv3 Dv4 E1 E2 E3 E4 E5 L0. repeat split; lia.
Qed.

Lemma art_fgapP_gshadow : forall p a len, In p (art_live (g_log FSG G)) -> fst p <> mb ->
  2147450880 + fst p / 8 <= a -> a + len <= 2147450880 + fst p / 8 + snd p / 8 -> art_gap art_freeP_W a len.
Proof.
  intros p a len Hp Hne Ha Hk. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct (art_frepP_pnums p Hp Hne) as (R1 & R2 & R3 & SHP).
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  unfold art_freeP_W, art_free3_W, art_cbr_sec_fp, art_secd_fp. rewrite ?Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: try (clear - Ha Hk R1 R2 R3 HS G1; lia).
  all: try (clear - Ha Hk R1 R2 R3 G10; lia).
  all: try (clear - Ha Hk R1 R2 R3 L3 Lo Hi2 Hqr Hn; lia).
  all: try (clear - Ha Hk R1 R2 R3 SHP N4 N5 N6 N7 Hqr Hn; lia).
  all: try (clear - Ha Hk R1 R2 R3; lia).
  all: try (clear - Ha Hk R1 R2 R3 Al2s; lia).
  all: try (clear - Ha Hk R1 R2 R3 Abs; lia).
  all: try (clear - Ha Hk R1 R2 R3 Papp N1 N2; lia).
  all: try (clear - Ha Hk R1 R2 R3 Q6 Q1 Q2 Q3; lia).
  all: fail 99 "OPEN".
Qed.
Lemma art_frepP_sec : art_rt_sec FSG rn G' (lb_remove u LB) M'.
Proof.
  pose proof REP as (ROK & _ & _ & _ & _ & SECR & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct SECR as (S0 & S8 & S56 & S48 & S616 & S16 & SNE & SCW & PER & SLV & SLEN).
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi). destruct KIND as (Hnth & Hq & Esu & Esn).
  destruct OUT as (GR7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & WRT & SC8).
  assert (EBL : art_swap_remove (0, 0) i bl = map art_sec_b (art_swap_remove art_dsec i (g_sec FSG G))) by (unfold bl; symmetry; apply art_swap_remove_mapP).
  rewrite EBL in SC8. destruct SC8 as (I0 & I8 & I56 & I616 & IW & IPER). rewrite length_map in I56, IW.
  pose proof (OB (rn_parr rn, 2 ^ 23) (art_inP_parr rn)) as Op. cbn [fst snd] in Op.
  pose proof art_frepP_maps_nodup as SMAPS.
  assert (Es : nth i (g_sec FSG G) art_dsec = s) by exact (nth_error_nth _ _ art_dsec Hnth).
  assert (KEEP : forall s', In s' (art_swap_remove art_dsec i (g_sec FSG G)) -> In s' (g_sec FSG G) /\ sc_map s' <> mb).
  { intros s' Hs'. split; [exact (art_swap_remove_in _ _ _ _ _ Hs')|]. unfold mb. rewrite <- Es. exact (art_swap_remove_gone _ _ sc_map art_dsec i (g_sec FSG G) s' SMAPS Hi Hs'). }
  unfold art_rt_sec. cbn [G' art_gs_freeP g_sec g_sec_committed g_log g_qt g_qg].
  split; [exact I0|]. split; [exact I8|]. split; [exact I56|].
  split; [apply art_frepP_cell_img; [lia0c|exact S48]|]. split; [exact I616|]. split; [apply art_frepP_cell_img; [lia0c|exact S16]|].
  split. { intros NE. apply SNE. intros E. apply NE. rewrite E. reflexivity. }
  split. { intros C. apply WRT; [clear - Plo; lia|clear - Phi G2; lia|unfold apart in Op |- *; clear - Op; lia|eapply wr_grows; [exact GR7|exact (SCW C)]]. }
  split.
  { intros j s' Hj. pose proof (nth_error_In _ _ Hj) as Hs''. destruct (KEEP s' Hs'') as (Hs' & Hne). destruct (In_nth_error _ _ Hs') as (j0 & Hj0).
    destruct (PER j0 s' Hj0) as (_ & P2 & _ & _ & _ & _ & Lo' & Hi' & Q & P0').
    destruct (IPER j (art_sec_b s') ltac:(rewrite nth_error_map, Hj; reflexivity)) as (J1 & J2 & J3 & J4 & J5 & J6). cbn [art_sec_b fst snd] in J1, J2, J3, J4, J5, J6.
    assert (Hn' : 1 <= sc_n s') by (destruct (sc_quar s'); [destruct Q as ((bb & _ & _ & _ & _ & X) & _)|destruct Q as (_ & (bb & _ & _ & _ & _ & X) & _)]; clear - X; lia).
    destruct (LIVE _ P2) as (K0 & K1 & K2 & K3 & _). cbn [fst snd] in K0, K1, K2, K3.
    assert (TRg : forall a (k : nat) v, sc_map s' + 32 <= a -> a + Z.of_nat k <= sc_map s' + sc_msize s' -> cellA M a k v -> cellA M' a k v).
    { intros a k v Ha Hk C. apply (art_cell_tr art_freeP_W M M' a k v art_frepP_agree (art_fgapP_grant _ a _ P2 Hne Ha Hk)); [clear - Ha K0; lia|clear - Hk K2 G2; lia|exact C]. }
    assert (HDR : forall st, art_chunk_hdr M (sc_u s') (sc_n s') st -> art_chunk_hdr M' (sc_u s') (sc_n s') st).
    { intros st (bb & Hbb & Hty & Chw & Cn & Hn''). exists bb. split; [exact Hbb|]. split; [exact Hty|].
      split; [apply TRg; [clear - Lo'; lia|clear - Hi' Hn'; cbn; lia|exact Chw]|]. split; [apply TRg; [clear - Lo'; lia|clear - Hi' Hn'; cbn; lia|exact Cn]|exact Hn'']. }
    split; [exact J1|]. split. { apply art_frepP_live_in. split; [exact P2|exact Hne]. }
    split; [exact J5|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|]. split; [exact Lo'|]. split; [exact Hi'|]. split; [|exact P0'].
    destruct (sc_quar s') eqn:Eq'.
    - destruct Q as (Qh & Qb). split; [exact (HDR 3 Qh)|exact Qb].
    - destruct Q as (Qlb & Qh & Qsh). split.
      { apply (art_lb_remove_keep0 u); [exact Qlb|]. cbn [fst]. intros E. pose proof (LIVE2 _ _ P2 Pme Hne) as Ap. cbn [fst snd] in Ap. unfold apart in Ap.
        clear - Ap E Lo Hi2 Lo' Hi' Hn Hqr Hn'. lia. }
      split; [exact (HDR 2 Qh)|].
      apply (shadow_blkR_tby M M' (sc_u s') (sc_n s') ltac:(clear - Hn'; lia)); [|exact Qsh]. intros jj Hjj0 Hjj v B.
      pose proof (art_S_blk_hi (sc_u s') (sc_n s') jj ltac:(clear - Hn'; lia) Hjj) as B1. unfold HeapIfaceA.S, HeapIfaceA.SB in B1 |- *.
      destruct (art_frepP_pnums _ P2 Hne) as (R1 & R2 & R3 & _). cbn [fst snd] in R1, R2, R3.
      destruct (LIVE3 _ P2) as (B8a & B8b). cbn [fst snd] in B8a, B8b.
      assert (Mw9 : (sc_map s' + sc_msize s') mod 8 = 0).
      { pose proof (Z.div_mod (sc_map s') 4096 ltac:(lia0)) as X1. rewrite B8a in X1. pose proof (Z.div_mod (sc_msize s') 4096 ltac:(lia0)) as X2. rewrite B8b in X2.
        replace (sc_map s' + sc_msize s') with ((512 * (sc_map s' / 4096) + 512 * (sc_msize s' / 4096)) * 8) by (clear - X1 X2; lia). apply Z_mod_mult. }
      pose proof (Z.div_mod (sc_map s' + sc_msize s') 8 ltac:(lia0)) as Dw9. rewrite Mw9 in Dw9.
      pose proof (Z.div_le_mono (sc_map s') (sc_u s') 8 ltac:(lia0) ltac:(clear - Lo'; lia)) as DwA.
      pose proof (Z.div_le_mono (sc_u s' + sc_n s' - 1) (sc_map s' + sc_msize s' - 1) 8 ltac:(lia0) ltac:(clear - Hi'; lia)) as Dw2.
      pose proof (Z.div_mod (sc_map s' + sc_msize s' - 1) 8 ltac:(lia0)) as Dw5. pose proof (Z.mod_pos_bound (sc_map s' + sc_msize s' - 1) 8 ltac:(lia0)) as Mw5.
      apply (art_byte_at_eq M M'); [|exact B]. apply art_frepP_agree. rewrite art_u_lit by (clear - B1 R1 R2 R3 DwA Dw2 Dw9 Dw5 Mw5 Hjj0; lia).
      apply (art_gap_out _ (sc_u s' / 8 + 2147450880 + jj) 1); [|lia0].
      apply (art_fgapP_gshadow _ _ _ P2 Hne); cbn [fst snd]; [clear - DwA Hjj0; lia|]. clear - B1 R2 Dw2 Dw9 Dw5 Mw5. lia. }
  split.
  { intros p Hp. apply art_frepP_live_in in Hp. destruct Hp as (Hp & Hne). destruct (SLV p Hp) as (s' & Hs' & ->). exists s'. split; [|reflexivity].
    apply art_swap_remove_keepsP; [exact Hi|exact Hs'|]. rewrite Es. intros ->. apply Hne. reflexivity. }
  rewrite art_swap_remove_length. assert (X : (length (g_sec FSG G) - 1 <= length (g_sec FSG G))%nat) by (lia0). clear - SLEN X. lia.
Qed.

#[using="M7 M' b1 kb Dz REP KIND Eu Hn Hqr Hb1 HS HS47 Edep OUT HDz LIVE LIVE2 LIVE3 Hother"] Theorem art_frepP_rep : art_alloc_rep FSG rn G' (lb_remove u LB) M'.
Proof.
  pose proof REP as (ROK & _).
  split; [exact ROK|]. split; [exact art_frepP_statics|]. split; [exact art_frepP_thread|]. split; [exact art_frepP_primary|]. split; [exact art_frepP_chunks|].
  split; [exact art_frepP_sec|]. split; [exact art_frepP_quar|]. split; [exact art_frepP_rt_depot|]. split; [exact art_frepP_ia|]. split; [exact art_frepP_blocks|exact art_frepP_ghost].
Qed.

Lemma art_fgapP_high : forall a len, rn_HI rn <= a -> (a + len <= Sp - 4096 \/ Sp <= a) -> art_gap art_freeP_W a len.
Proof.
  intros a len Ha Hk. pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi).
  destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  unfold art_freeP_W, art_free3_W, art_cbr_sec_fp, art_secd_fp. rewrite ?Esl. cbn [art_gap fst snd app]. unfold apart, EbtPoison.SB, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, AsanTab.BIG_LO, AsanTab.BIG_HI in *.
  repeat split; try exact I.
  all: try (clear - Ha Hk; lia).
  all: try (clear - Ha Hk G8; lia).
  all: try (clear - Ha Hk L2 Lo Hi2 Hqr Hn; lia).
  all: try (clear - Ha Hk G1 N4 N5 N6 N7 Hqr Hn; lia).
  all: try (clear - Ha Hk G1; lia).
  all: try (clear - Ha Hk Dl2; lia).
  all: try (clear - Ha Hk Dblk; lia).
  all: try (clear - Ha Hk Phi N1 N2; lia).
  all: try (clear - Ha Hk Q5 Q1 Q2 Q3; lia).
  all: fail 99 "OPEN".
Qed.

#[using="M7 M' b1 kb Dz REP KIND Eu Hn Hqr Hb1 HS HS47 Edep OUT HDz LIVE LIVE2 LIVE3 Hother"] Theorem art_frepP_out_bundle :
  (forall b0 a, In b0 (lb_remove u LB) -> (fst b0 <= a < fst b0 + snd b0 \/ in_shadow_of (fst b0) (snd b0) a) -> art_out art_freeP_W a)
  /\ (forall a, rn_HI rn <= a -> a < 2 ^ 64 -> ~ (Sp - 4096 <= a < Sp) -> art_out art_freeP_W a)
  /\ (forall a, 0x10000 <= a < 0x69c000 -> ~ (0x142a40 <= a < 0x1d7e40) -> ~ (0x217fc8 <= a < 0x667fe8) -> art_out art_freeP_W a)
  /\ (forall a, ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES -> art_out art_freeP_W a)
  /\ (forall a, rn_dtls rn <= a < rn_dtls rn + 4096 -> art_out art_freeP_W a)
  /\ (forall a, rn_t rn <= a < rn_t rn + 2824 -> art_out art_freeP_W a)
  /\ (forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> (lo + len <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= lo) ->
        (forall p, In p (art_live (g_log FSG G)) -> apart (fst p) (snd p) lo len) -> HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> art_out art_freeP_W a)
  /\ (forall z, in_ev_ranges evs z -> exists p, In p art_freeP_W /\ fst p <= z < fst p + snd p).
Proof.
  pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & CH & SECR & _ & _ & _ & BL & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct art_frepP_me as (Pme & Lo & Hi2 & P0 & L0 & L2 & L3 & A1 & A2 & OB & Hs & Hi). pose proof KIND as (Hnth & Hq & Esu & Esn).
  destruct art_frepP_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  split.
  { intros b0 a Hb0 Ha. destruct (Hother b0 Hb0) as (Hb & Hne). destruct (BL b0 Hb) as [(c & w & Hc & OKw & St)|(s' & Hs' & Hq' & Eu' & En')].
    - destruct (CH c Hc) as (_ & _ & _ & C4). cbv zeta in C4. specialize (C4 w OKw). rewrite St in C4. destruct C4 as (_ & X2 & X3 & X4 & _).
      pose proof X4 as (?bq & _ & _ & _ & _ & Hn0). pose proof OKw as (Hw0 & Hwau & _).
      destruct (PRIM c Hc) as (_ & OK & _). destruct OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _). destruct (art_class_size_facts c Hc) as (S1 & S16).
      destruct Ha as [Ha|Ha].
      + apply (art_gap_out _ (fst b0) (snd b0)); [|exact Ha]. apply art_fgapP_kspace; [clear - X2 Hc Hw0; lia|clear - X3 Hc Hwau Haumu Hmu3; lia].
      + unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB in Ha.
        assert (E8 : rn_spb rn / 8 = 8192 * rn_qs rn) by (rewrite Espb; replace (65536 * rn_qs rn) with ((8192 * rn_qs rn) * 8) by (lia0); rewrite Z_div_mult by (lia0); reflexivity).
        pose proof (Z.div_le_mono (rn_spb rn) (fst b0) 8 ltac:(lia0) ltac:(clear - X2 Hc Hw0; lia)) as Dv1. rewrite E8 in Dv1.
        assert (Dv2 : (fst b0 + snd b0 - 1) / 8 <= 8192 * rn_qs rn + 2 ^ 34 + 511).
        { apply (Z.le_trans _ ((rn_spb rn + 2 ^ 37 + 4095) / 8)); [apply Z.div_le_mono; [lia0|clear - X3 Hc Hwau Haumu Hmu3; lia]|].
          rewrite Espb. replace (65536 * rn_qs rn + 2 ^ 37 + 4095) with (7 + (8192 * rn_qs rn + 2 ^ 34 + 511) * 8) by (lia0). rewrite Z.div_add by (lia0). change (7 / 8) with 0. lia0. }
        apply (art_gap_out _ a 1); [|lia0]. apply art_fgapP_kshadow; clear - Ha Dv1 Dv2; lia.
    - destruct (In_nth_error _ _ Hs') as (j0 & Hj0). destruct (art_frepP_rec _ _ Hj0) as (P2 & Lo' & Hi' & Hn' & P0' & K0 & K2 & K3 & KO).
      assert (Hne' : sc_map s' <> mb).
      { apply (art_nodup_map_neq _ _ sc_map (g_sec FSG G) s' s art_frepP_maps_nodup Hs' Hs). intros ->. apply Hne. rewrite <- Eu'. exact Esu. }
      rewrite <- Eu', <- En' in Ha. destruct Ha as [Ha|Ha].
      + apply (art_gap_out _ (sc_u s') (sc_n s')); [|exact Ha]. apply (art_fgapP_grant _ _ _ P2 Hne'); cbn [fst snd]; [clear - Lo'; lia|exact Hi'].
      + unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB in Ha.
        destruct (art_frepP_pnums _ P2 Hne') as (R1 & R2 & R3 & _). cbn [fst snd] in R1, R2, R3.
        destruct (LIVE3 _ P2) as (B8a & B8b). cbn [fst snd] in B8a, B8b.
        assert (Mw9 : (sc_map s' + sc_msize s') mod 8 = 0).
        { pose proof (Z.div_mod (sc_map s') 4096 ltac:(lia0)) as X1. rewrite B8a in X1. pose proof (Z.div_mod (sc_msize s') 4096 ltac:(lia0)) as X2. rewrite B8b in X2.
          replace (sc_map s' + sc_msize s') with ((512 * (sc_map s' / 4096) + 512 * (sc_msize s' / 4096)) * 8) by (clear - X1 X2; lia). apply Z_mod_mult. }
        pose proof (Z.div_mod (sc_map s' + sc_msize s') 8 ltac:(lia0)) as Dw9. rewrite Mw9 in Dw9.
        pose proof (Z.div_le_mono (sc_map s') (sc_u s') 8 ltac:(lia0) ltac:(clear - Lo'; lia)) as DwA.
        pose proof (Z.div_le_mono (sc_u s' + sc_n s' - 1) (sc_map s' + sc_msize s' - 1) 8 ltac:(lia0) ltac:(clear - Hi'; lia)) as Dw2.
        pose proof (Z.div_mod (sc_map s' + sc_msize s' - 1) 8 ltac:(lia0)) as Dw5. pose proof (Z.mod_pos_bound (sc_map s' + sc_msize s' - 1) 8 ltac:(lia0)) as Mw5.
        apply (art_gap_out _ a 1); [|lia0]. apply (art_fgapP_gshadow _ _ _ P2 Hne'); cbn [fst snd]; [clear - Ha DwA; lia|clear - Ha R2 Dw2 Dw9 Dw5 Mw5; lia]. }
  split. { intros a Ha H64 Ns. apply (art_gap_out _ a 1); [|lia0]. apply art_fgapP_high; [exact Ha|clear - Ns; lia]. }
  split. { intros a Ha N1z N2z. apply (art_gap_out _ a 1); [|lia0].
           destruct (Z_lt_ge_dec a 0x667fe8) as [Lo2|Hi3]; [apply art_fgapP_img; clear - Ha N1z N2z Lo2; lia|apply art_fgapP_tls; clear - Ha Hi3; lia]. }
  split. { intros a Ha. apply (art_gap_out _ a 1); [apply art_fgapP_fs; clear - Ha; lia|lia0]. }
  split. { intros a Ha. apply (art_gap_out _ a 1); [apply art_fgapP_dtls; clear - Ha; lia|lia0]. }
  split. { intros a Ha. apply (art_gap_out _ a 1); [apply art_fgapP_thread; clear - Ha; lia|lia0]. }
  split.
  { intros lo len a H0 H1 H47 Hkb Hlv Ha. unfold HeapIfaceA.S, HeapIfaceA.SB in Ha. pose proof (Hlv _ Pme) as Am. cbn [fst snd] in Am.
    pose proof I as Hp0. pose proof I as Hp1. pose proof I as HpH. pose proof I as Hk.
    destruct art_frepP_last as (sl & Hsl & Esl & Hsl2). destruct (art_frepP_rec _ _ Hsl) as (Qme & Q1 & Q2 & Q3 & Q0 & Q4 & Q5 & Q6 & QB).
    assert (SH2 : (lo + len - 1) / 8 < mb / 8 \/ mb / 8 + ms / 8 <= lo / 8).
    { unfold apart in Am. destruct Am as [Am|Am].
      - right. rewrite <- N8. apply Z.div_le_mono; [lia0|exact Am].
      - left. pose proof (Z.div_mod mb 4096 ltac:(lia0)) as X1. rewrite A1 in X1.
        pose proof (Z.div_le_mono (lo + len - 1) (mb - 1) 8 ltac:(lia0) ltac:(clear - Am; lia)) as X6.
        replace (mb - 1) with (7 + (512 * (mb / 4096) - 1) * 8) in X6 by (clear - X1; lia). rewrite Z.div_add in X6 by (lia0). change (7 / 8) with 0 in X6.
        assert (X7 : mb / 8 = 512 * (mb / 4096)). { rewrite <- (Z_div_mult (512 * (mb / 4096)) 8) by (lia0). f_equal. clear - X1; lia. }
        rewrite X7. clear - X6. lia. }
    assert (R0 : 0 <= lo / 8) by (apply Z.div_pos; [exact H0|lia0]).
    assert (R47 : (lo + len - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; [lia0|clear - H47; lia]).
    pose proof (Z.div_le_mono lo (lo + len - 1) 8 ltac:(lia0) ltac:(clear - H1; lia)) as R5.
    unfold art_freeP_W, art_free3_W, art_cbr_sec_fp, art_secd_fp. rewrite ?Esl. apply art_out_intro. intros p Hp. cbn [In app] in Hp. unfold EbtPoison.SB in Hp.
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in *.
    repeat (destruct Hp as [<-|Hp]); try (destruct Hp); cbn [fst snd].
    all: try (clear - Ha R0 R47 R5 HS G1; lia).
    all: try (clear - Ha R0 R47 R5 G10; lia).
    all: try (clear - Ha R0 R47 R5 L3 Lo Hi2 Hqr Hn; lia).
    all: try (clear - Ha R0 R47 R5 SH2 N4 N5 N6 N7 N8 Hqr Hn; lia).
    all: try (clear - Ha R0 R47 R5; lia).
    all: try (clear - Ha R0 R47 R5 Al2s; unfold apart in Al2s; lia).
    all: try (clear - Ha R0 R47 R5 Abs; unfold apart in Abs; lia).
    all: try (clear - Ha R0 R47 R5 Papp N1 N2; lia).
    all: try (clear - Ha R0 R47 R5 Q6 Q1 Q2 Q3; lia).
    all: fail 99 "OPEN". }
  intros z (ev & Hev & Hz). unfold evs in Hev. apply in_app_or in Hev.
  assert (INm : In (mb, ms) art_freeP_W) by (unfold art_freeP_W, art_cbr_sec_fp, art_secd_fp; apply in_or_app; right; cbn [In app]; do 9 right; left; reflexivity).
  assert (INs : In (EbtPoison.SB + mb / 8, ms / 8) art_freeP_W) by (unfold art_freeP_W, art_cbr_sec_fp, art_secd_fp; apply in_or_app; right; cbn [In app]; do 8 right; left; reflexivity).
  destruct (EbtRecycle1.art_flush_range mb ms A1 A2 ltac:(clear - L0; lia) ltac:(clear - Lo Hi2 Hn Hqr; lia)) as (F1 & F2 & F3 & F4 & F5 & F6 & _).
  destruct Hev as [Hev|[<-|[]]].
  - unfold EbtRecycle2C.art_flush_events in Hev. destruct (EbtRecycle1.art_flush_beg mb <? EbtRecycle1.art_flush_end mb ms); [|destruct Hev]. destruct Hev as [<-|[]].
    cbn [art_ev_range fst snd] in Hz. exists (EbtPoison.SB + mb / 8, ms / 8). split; [exact INs|]. cbn [fst snd]. clear - Hz F4 F5 F6. lia.
  - cbn [art_ev_range fst snd] in Hz. exists (mb, ms). split; [exact INm|]. cbn [fst snd]. exact Hz.
Qed.

#[using="M7 M' b1 kb Dz REP KIND Eu Hn Hqr Hb1 HS HS47 Edep OUT HDz LIVE LIVE2 LIVE3 Hother"] Lemma art_frepP_wscr : wrA M (Sp - 4096) 4096 -> wrA M' (Sp - 4096) 4096.
Proof.
  intros W0. destruct OUT as (GR7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & WRT & _). destruct art_frepP_me as (_ & _ & _ & _ & _ & L2 & _).
  pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
  apply WRT; [clear - HS G1; lia|clear - HS47; lia|unfold apart; clear - L2 HS; lia|eapply wr_grows; [exact GR7|exact W0]].
Qed.
End RepP.
