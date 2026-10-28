(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare AsanAcct HeapIface HeapIfaceA HeapIfaceABx As0Tables
     ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatRzLog_b BatAllocA_b BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatClsRefill_b BatCellEx_b BatByteCell_b
     BatCARSpec_b BatAlloc3Pure_b BatDepotA_b BatDepot_b BatUnwind_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocate3_b BatInv_b BatInvMallocPure_b BatInvMalloc_b BatFxQ_b BatFxBatch2_b BatFxBatch3_b BatFxImg_b BatFreeTop3_b BatInvFreePure_b BatInvFree_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require BatImgCell_b BatPoison3_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx ShadowRLawsB.      (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Lemma art_bt_bytes_ge : forall b, (forall it, In it (bt_items b) -> 0 <= snd it) -> 8192 <= art_bt_bytes b.
Proof.
  intros b H. unfold art_bt_bytes. induction (bt_items b) as [|x r IH]; cbn [fold_right]; [lia|].
  pose proof (H x (or_introl eq_refl)). specialize (IH (fun it Hi => H it (or_intror Hi))). lia.
Qed.
Lemma art_batches_bytes_cons : forall b r, art_batches_bytes (b :: r) = art_bt_bytes b + art_batches_bytes r.
Proof. intros b r. unfold art_batches_bytes, art_bt_bytes. cbn [fold_right]. lia. Qed.
Lemma art_batches_bytes_ge : forall bs, (forall b it, In b bs -> In it (bt_items b) -> 0 <= snd it) ->
  8192 * Z.of_nat (length bs) <= art_batches_bytes bs /\ forall b, In b bs -> art_bt_bytes b <= art_batches_bytes bs.
Proof.
  induction bs as [|x r IH]; intros H; [split; [cbn; lia|intros b []]|].
  destruct (IH (fun b it Hb Hi => H b it (or_intror Hb) Hi)) as (I1 & I2). pose proof (art_bt_bytes_ge x (fun it Hi => H x it (or_introl eq_refl) Hi)) as Hx.
  rewrite art_batches_bytes_cons. split; [cbn [length]; lia|]. intros b [<-|Hb]; [lia|]. specialize (I2 b Hb). lia.
Qed.
Lemma art_batch_list_last_hdr : forall (M0 : word -> option byte) r lb f l, art_batch_list M0 (r ++ [lb]) f l ->
  (length (bt_items lb) <= 1021)%nat /\ cellA M0 (bt_addr lb + 16) 8 (Z.of_nat (length (bt_items lb))) /\ cellA M0 (bt_addr lb + 8) 8 (art_bt_bytes lb).
Proof.
  intros M0 r. induction r as [|x r' IH]; intros lb f l BL.
  - cbn [app art_batch_list] in BL. destruct BL as (_ & Hl & C1 & C2 & _). split; [exact Hl|]. split; [exact C1|exact C2].
  - change ((x :: r') ++ [lb]) with (x :: (r' ++ [lb])) in BL. cbn [art_batch_list] in BL. destruct BL as (_ & _ & _ & _ & _ & _ & R). exact (IH lb _ _ R).
Qed.

Lemma art_wr_of_bytes : forall (M : word -> option byte) a n, 0 <= a -> a + n < 2 ^ 64 -> (forall i, 0 <= i < n -> exists v, byte_at M (a + i) v) -> wrA M a n.
Proof.
  intros M a n Ha Hn H d k Hd Hk. apply store_ok_of_all; [rewrite art_u_lit by lia; lia|]. intros x Hx. rewrite art_u_lit in Hx by lia.
  destruct (H (U x - a) ltac:(lia)) as (v & Bv). unfold byte_at in Bv. replace (a + (U x - a)) with (U x) in Bv by lia. rewrite Z_to_bv_bv_unsigned in Bv.
  unfold wview. rewrite Bv. discriminate.
Qed.

Section EntryFacts.
Variable FSG : Type.
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M : word -> option byte).
Hypothesis REP : art_alloc_rep FSG rn G LB M.

(* [comment removed for export] *)
#[using="rn M REP"] Lemma art_wfa_kind : forall u n, In (u, n) LB ->
  exists k, match k with
            | FKP c w => 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w /\ g_st FSG G c w = CAlloc u n
            | FKS i => exists s, nth_error (g_sec FSG G) i = Some s /\ sc_quar s = false /\ sc_u s = u /\ sc_n s = n
            end.
Proof.
  intros u n Hin. destruct REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BLK & _). destruct (BLK (u, n) Hin) as [(c & w & Hc & V & St)|(s & Hs & Hq & Eu & En)]; cbn [fst snd] in *.
  - exists (FKP c w). split; [exact Hc|]. split; [exact V|exact St].
  - destruct (In_nth_error _ _ Hs) as (i & Hi). exists (FKS i). exists s. repeat split; assumption.
Qed.

(* [comment removed for export] *)
#[using="rn LB REP"] Lemma art_wfa_hdr : forall u n k,
  match k with
  | FKP c w => 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w /\ g_st FSG G c w = CAlloc u n
  | FKS i => exists s, nth_error (g_sec FSG G) i = Some s /\ sc_quar s = false /\ sc_u s = u /\ sc_n s = n
  end ->
  art_chunk_hdr M u n 2 /\ HAJ.shadow_blkR M u n.
Proof.
  intros u n k KIND. destruct REP as (_ & _ & _ & _ & CH & SECR & _). destruct k as [c w|i].
  - destruct KIND as (Hc & V & St). specialize (CH c Hc). cbv zeta in CH. destruct CH as (_ & _ & _ & III). specialize (III w V). rewrite St in III.
    destruct III as (_ & _ & _ & J4 & J5 & _). split; assumption.
  - destruct KIND as (s & Hs & Hq & Esu & Esn). destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _). destruct (SALL i s Hs) as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _).
    rewrite Hq in P9. rewrite Esu, Esn in P9. destruct P9 as (_ & Q2 & Q3). split; assumption.
Qed.

(* [comment removed for export] *)
#[using="rn LB M REP"] Lemma art_wfa_items : forall b it, In b (g_qt FSG G ++ g_qg FSG G) -> In it (bt_items b) -> 1 <= snd it.
Proof.
  intros b it Hb Hit. destruct REP as (_ & _ & _ & _ & CH & SECR & QR & _). destruct QR as (_ & _ & _ & _ & _ & _ & _ & ITEMS & _).
  destruct (ITEMS b it Hb Hit) as [(c & w & Hc & V & St)|(s & Hs & Hq & Esu & Esn)].
  - specialize (CH c Hc). cbv zeta in CH. destruct CH as (_ & _ & _ & III). specialize (III w V). rewrite St in III. destruct III as (_ & _ & (bb & _ & _ & _ & _ & Hn0) & _). lia.
  - destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _). destruct (In_nth_error _ _ Hs) as (i & Hi). destruct (SALL i s Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _).
    rewrite Hq in P9. destruct P9 as ((bb & _ & _ & _ & _ & Hn0) & _). rewrite <- Esn. lia.
Qed.

(* [comment removed for export] *)
#[using="LB REP"] Lemma art_wfa_thq : forall n, 1 <= n < 2 ^ 28 ->
  let qtl := g_qt FSG G in let lastb := art_lastb qtl in let L := Z.of_nat (length qtl) in let B := bt_addr lastb in let cntB := Z.of_nat (length (bt_items lastb)) in
  0 <= L < 2 ^ 63 /\ 0 <= B < 2 ^ 63 /\ 0 <= art_batches_bytes qtl /\ art_batches_bytes qtl + n + 8192 < 2 ^ 64
  /\ cellA M (rn_t rn + 80) 8 L /\ cellA M (rn_t rn + 80 + 24) 8 (art_batches_bytes qtl)
  /\ exists wB, (L <> 0 -> B = rn_spb rn + 24 * 2 ^ 32 + 16 * wB /\ art_cptr_ok 8192 (cl_au (g_cls FSG G 24)) wB /\ ~ In wB (cl_cache (g_cls FSG G 24) ++ cl_free (g_cls FSG G 24))
                           /\ cellA M (rn_t rn + 80 + 16) 8 B /\ cellA M (B + 16) 8 cntB /\ cellA M (B + 8) 8 (art_bt_bytes lastb) /\ 0 <= cntB <= 1021
                           /\ 0 <= art_bt_bytes lastb /\ art_bt_bytes lastb + n < 2 ^ 64).
Proof.
  intros n Hn qtl lastb L B cntB. pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & CH & _ & QR & _). destruct ROK as (GEO & _). geo_open GEO.
  destruct QR as ((ft & lt & Ct80 & Ct88 & Ct96 & Ct104 & BLt) & _ & Bt & _ & _ & _ & _ & _ & _ & BCH). fold qtl in Ct80, Ct104, BLt, Bt.
  assert (POS : forall b it, In b qtl -> In it (bt_items b) -> 0 <= snd it). { intros b it Hb Hit. pose proof (art_wfa_items b it (in_or_app _ _ _ (or_introl Hb)) Hit). lia. }
  destruct (art_batches_bytes_ge qtl POS) as (BY1 & BY2).
  assert (HL : 0 <= L < 2 ^ 63) by (unfold L; lia).
  assert (HB : L <> 0 -> In lastb qtl). { intros NL. unfold lastb, art_lastb. apply BatFxQ_b.art_last_in. intros E. apply NL. unfold L. rewrite E. reflexivity. }
  assert (HBW : L <> 0 -> exists wB, B = rn_spb rn + 24 * 2 ^ 32 + 16 * wB /\ art_cptr_ok 8192 (cl_au (g_cls FSG G 24)) wB /\ g_st FSG G 24 wB = CBatch).
  { intros NL. destruct (BCH lastb (in_or_app _ _ _ (or_introl (HB NL)))) as (wB & E & V & St). rewrite art_class_size_24 in V. exists wB. split; [exact E|]. split; assumption. }
  destruct (PRIM 24 ltac:(lia)) as (_ & OK24 & _). destruct OK24 as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _).
  split; [exact HL|]. split.
  { destruct (Z.eq_dec L 0) as [EL|NL].
    - assert (E0 : qtl = []) by (apply length_zero_iff_nil; unfold L in EL; lia). unfold B, lastb. rewrite E0. cbn. lia.
    - destruct (HBW NL) as (wB & E & (V0 & V1 & _) & _). rewrite E. clear - V0 V1 Haumu Hmu3 G4 G6 G2 Eris. lia. }
  split; [lia|]. split; [lia|]. split; [exact Ct80|]. split; [replace (rn_t rn + 80 + 24) with (rn_t rn + 104) by lia; exact Ct104|].
  destruct (Z.eq_dec L 0) as [EL|NL]; [exists 0; intros X; contradiction|].
  destruct (HBW NL) as (wB & E & V & St). exists wB. intros _.
  assert (NEq : qtl <> []) by (intros E0; apply NL; unfold L; rewrite E0; reflexivity).
  pose proof (art_qt_split qtl NEq) as ESP. fold lastb in ESP.
  pose proof BLt as BLt'. rewrite ESP in BLt'. destruct (art_batch_list_last_hdr M _ lastb _ _ BLt') as (H1 & H2 & H3).
  pose proof (art_batch_list_last M qtl ft lt NEq BLt) as El. fold lastb in El. fold B in El.
  split; [exact E|]. split; [exact V|]. split.
  { intros Hi. specialize (CH 24 ltac:(lia)). cbv zeta in CH. destruct CH as (_ & II & _). rewrite (II wB Hi) in St. discriminate. }
  split; [replace (rn_t rn + 80 + 16) with (rn_t rn + 96) by lia; rewrite <- El; exact Ct96|]. split; [exact H2|]. split; [exact H3|]. split; [unfold cntB; lia|].
  pose proof (BY2 lastb (HB NL)). pose proof (art_bt_bytes_ge lastb (fun it Hi => POS lastb it (HB NL) Hi)). lia.
Qed.
End EntryFacts.

(* [comment removed for export] *)
Section Entry.
Variable FSG : Type.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_wf_entry :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) R (Mr rom : word -> option byte) (raw0 : word) (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z))
         (Sp u n q16 qr b1 km top bot : Z) (kb : nat) (k : art_fk),
    let qtl := g_qt FSG G in
    let cl24 := g_cls FSG G 24 in
    let newb := art_free_newb qtl in
    let lastb := art_lastb qtl in
    let L := Z.of_nat (length qtl) in
    let B := bt_addr lastb in
    let cntB := Z.of_nat (length (bt_items lastb)) in
    let bytes' := art_batches_bytes qtl + n + (if newb then 8192 else 0) in
    art_alloc_rep FSG rn G LB Mr ->
    match k with
    | FKP c w => 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w /\ g_st FSG G c w = CAlloc u n
    | FKS i => exists s, nth_error (g_sec FSG G) i = Some s /\ sc_quar s = false /\ sc_u s = u /\ sc_n s = n
    end ->
    getr R 1 = raw0 -> ret_ok raw0 -> getr R 2 = Z_to_bv 64 Sp -> getr R 4 = Z_to_bv 64 (rn_tp rn) -> getr R 10 = Z_to_bv 64 u ->
    u = 16 * q16 -> 1 <= n < 2 ^ 28 -> n <= 8 * qr <= n + 7 -> 0 <= b1 < 256 -> b1 mod 4 = 1 ->
    cellA Mr (u - 16) 4 (2 + 256 * b1) -> cellA Mr (u - 12) 4 n -> HAJ.shadow_blkR Mr u n ->
    rn_HI rn + 4096 <= Sp - 4096 -> Sp < 2 ^ 47 -> Sp mod 16 = 0 ->
    top = ar_stack_top (rn_ar rn) -> bot = ar_stack_bottom (rn_ar rn) -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 ->
    wrA Mr (Sp - 4096) 4096 -> readable8 Mr Sp top ->
    g_depot FSG G = Datatypes.S kb -> cl_mu cl24 = 262144 * km ->
    (newb = true -> cl_cache cl24 = [] -> art_cls_needs_populate 24 cl24 = true ->
       cl_mu cl24 + 262144 <= 3758096384 /\ art_cls_mfa' cl24 (Z.of_nat (length (cl_free cl24)) + art_cls_new 24 cl24) <= 536870912) ->
    (newb = true -> art_cls_ok 24 (art_ca_pre 24 cl24)) ->
    art_evok_list EVOK log (art_enq_events newb (rn_spb rn) cl24) ->
    (forall p, In p (art_live (g_log FSG G)) ->
       0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
       /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o))) ->
    (forall p p', In p (art_live (g_log FSG G)) -> In p' (art_live (g_log FSG G)) -> fst p <> fst p' -> apart (fst p) (snd p) (fst p') (snd p')) ->
    (forall p, In p (art_live (g_log FSG G)) -> fst p mod 4096 = 0 /\ snd p mod 4096 = 0) ->
    (* [comment removed for export] *)
    (forall regs' (Mr' : word -> option byte),
        getr regs' 2 = Z_to_bv 64 Sp -> getr regs' 1 = raw0 ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r) ->
        bytes' <= 2 ^ 20 ->
        art_free3_out Mr Mr' Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn) b1 n (rn_spb rn) (rn_ris rn) (rn_qs rn) km L B cntB (art_bt_bytes lastb) (art_batches_bytes qtl) kb (g_inited FSG G) cl24 ->
        Q (log ++ art_enq_events newb (rn_spb rn) cl24) (mkst regs' raw0 Mr' rom)) ->
    (* [comment removed for export] *)
    (forall regs' (Mr' : word -> option byte),
        getr regs' 1 = (0x56a84 : bv 64)%bv -> getr regs' 2 = Z_to_bv 64 (Sp - 2208) ->
        getr regs' 10 = Z_to_bv 64 0x13c8b0 -> getr regs' 11 = Z_to_bv 64 (rn_t rn + 80) -> getr regs' 12 = Z_to_bv 64 (rn_t rn + 208) -> getr regs' 13 = Z_to_bv 64 (Sp - 2128) ->
        (forall r : reg, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r) ->
        2 ^ 20 < bytes' ->
        art_free3_out Mr Mr' Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn) b1 n (rn_spb rn) (rn_ris rn) (rn_qs rn) km L B cntB (art_bt_bytes lastb) (art_batches_bytes qtl) kb (g_inited FSG G) cl24 ->
        art_free3_epi Mr' Sp u raw0 R -> wrA Mr' (Sp - 4096) 4096 ->
        aruns ASEGS EVOK GR Q (log ++ art_enq_events newb (rn_spb rn) cl24) (mkst regs' (0x542b0 : word) Mr' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst R (0x79824 : word) Mr rom).
Proof.
  intros Q log R Mr rom raw0 rn G LB Sp u n q16 qr b1 km top bot kb k qtl cl24 newb lastb L B cntB bytes'
         REP KIND H1 Hret H2 H4 H10 Eu Hn Hqr Hb1 Hty Chw Cn SHB HHI HS47 HS16 Etop Ebot Hbot Hbt Htop4 Htop W RD0 Edep Emu Room OKpre EV LIVE LIVE2 LIVE3 K1 K2.
  destruct (art_wfa_thq FSG rn G LB Mr REP n Hn) as (HL & HB & Hby & Hby' & CL & Cby & wB & LBN).
  destruct (art_frep_u_far FSG rn G LB Mr u n q16 qr b1 kb k REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3) as (U1 & U2 & U3 & U4 & Ut & Uc & Ul2 & Ublk & _ & _ & _ & Uris & Ufa).
  pose proof (art_frep_u_B FSG rn G LB Mr u n q16 qr b1 kb k REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3) as UB.
  pose proof (art_frep_wr_hdr FSG rn G LB Mr u n q16 b1 kb k REP Eu Hn KIND Edep LIVE3) as Wp.
  pose proof (art_frep_wr_sh FSG rn G LB Mr u n q16 qr b1 kb k REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3 SHB) as Wus.
  pose proof (art_frep_hp24 FSG rn G LB Mr Sp u n q16 qr b1 km kb k REP Eu Hn Hqr Hb1 KIND HHI Emu Edep LIVE LIVE2 LIVE3 OKpre) as HP24.
  assert (Hq0 : 1 <= qr) by (clear - Hn Hqr; lia).
  pose proof REP as (ROK & ST & TH & (PH & PRIM & Wsh) & _ & _ & _ & DEP & (IA1 & IA2 & _) & _).
  rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct ST as (PC & LY & T & _ & _ & DR & _ & C1 & _ & _ & _ & _ & _ & C7 & _ & C9 & _ & _ & _ & C13 & C14 & C15 & C16 & _).
  destruct TH as (Wt & T1 & T2 & T3 & T4 & T5 & T6 & _). rewrite <- Etop in T3. rewrite <- Ebot in T4.
  destruct (PRIM 24 ltac:(lia)) as (RC & OK & Hinit & _). fold cl24 in RC, OK, Hinit.
  pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _).
  unfold art_rt_depot in DEP. rewrite Edep in DEP.
  assert (A24 : forall X Y, apart (u - 16) (16 + 8 * qr) X Y -> apart (u - 16) 24 X Y) by (intros X Y A; unfold apart in *; clear - A Hq0; lia).
  assert (A24' : forall X Y, apart (u - 16) 32 X Y -> apart (u - 16) 24 X Y) by (intros X Y A; unfold apart in *; clear - A; lia).
  apply (art_free3 EVOK GR Q log R Mr rom raw0 Sp (rn_HI rn) u q16 n qr b1 (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) km
           (rn_l2 rn) (rn_blk rn) top bot L B wB cntB (art_bt_bytes lastb) (art_batches_bytes qtl) kb (g_ia FSG G) (g_inited FSG G) cl24
           H1 Hret H2 H4 H10 ltac:(clear - U1; lia) Eu Hn Hqr Hb1 Hty
           ltac:(unfold BatPoison3_b.art_poison_lo_ok, BatPoison3_b.art_poison_hi_ok, SB, kHighMemBeg, kHighMemEnd; clear - U1 U2 U4 Hq0 G2; lia)
           GEO HHI HS47 HS16 Hbot Hbt Htop4 Htop Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs
           ltac:(clear - U3; lia) (A24 _ _ Ut) (A24 _ _ Uc) (A24 _ _ Ul2) (A24 _ _ Ublk) (A24' _ _ Uris) (A24' _ _ Ufa) UB
           W RD0 Wt Wp Wus (art_img_wr_iaflag Mr 0x1cf6c8 4 ltac:(lia) ltac:(lia) ltac:(lia)) (art_img_wr_iatab Mr 0x140e40 0x81030 ltac:(lia) ltac:(lia) ltac:(lia))
           LY T PC C1 C13 C14 T6 T5 T3 T4 IA1
           ltac:(intros E j Hj; replace (0x140e48 + 8 * j) with (0x140e40 + 8 + 8 * j) by lia; exact (IA2 E j Hj))
           Chw Cn C7 T1 T2 C15 C16 C9 PH RC OK Hinit Emu).
  - (* [comment removed for export] *)
    intros E1 E2 E3. destruct (Room E1 E2 E3) as (R1 & R2). split; [exact R1|]. split; [exact R2|].
    split; (eapply wr_sub; [exact Wsh| |]); clear - R1 Emu Hau0 Haumu; lia.
  - exact EV.
  - exact HL.
  - exact HB.
  - exact Hby.
  - exact Hby'.
  - exact CL.
  - exact Cby.
  - exact LBN.
  - exact HP24.
  - exact DEP.
  - exact DR.
  - exact K1.
  - exact K2.
Qed.
End Entry.
