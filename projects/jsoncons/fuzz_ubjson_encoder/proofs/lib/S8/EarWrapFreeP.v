(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatSim StoreOk Hoare AsanAcct HeapIface HeapIfaceA HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem EatLeaf EatAllocG EatPoison EatRzLog EatAllocA EatInitCache EatPopulate1 ArtRuns ArtRunsMem EatCls EatFp EatClsRep EatClsGfa2 EatClsRefill EatCellEx EatByteCell EatCARSpec EatAlloc3Pure EatDepotA EatDepot EatUnwind ArtBridge EatAllocate3 EarInv EatInvMallocPure EarInvMalloc EatLift EatWrapPure EarWrapKit EatWrapMallocH EarWrapMallocX EarIfaceLaws EatFxQ EatFxBatch2 EatFxBatch3 EatFxImg EarFreeTop3 EarInvFreePure EarInvFree EarWrapFreeA EarWrapFreeC EarWrapFreeR.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require EatImgCell EatPoison3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import HeapIfaceAEx ShadowRLawsB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import EatSecAllocPost EatRecycle1 EatRecycle2C EatRecycle4S EarInvRecycleA EarInvRecycleC EarInvRecycleD EarInvRecycle EarFxPutP EarFreeTop3P EarTopFree3 EarDep EarUkey
     EarCreditQ EarCredit EarCreditT EarCreditF EarInvFreeP.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Local Ltac lia0 := repeat match goal with H : _ |- _ => clear H end; L5FastLiaT.plia1.
Local Ltac lia0c := repeat match goal with H : _ |- _ => clear H end; cbn; L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Ltac rok_open14 ROK :=
  destruct ROK as (GEO & Esb & Kal & Kspb & Kend & Pal & Plo & Phi & Papp & Hkey & Hloff & Hloff' & Hloff'' & Htpd & Htsdd & Dl2 & Dblk
                   & Al2t & Al2c & Al2k & Al2s & Abt & Abc & Abk & Abs & Apt & Apc & Apk & Apl & Apb & Aft & Afc & Afk & Afl & Afb & Afp & Fhi & Fapp & Fimg & Flo
                   & Il2 & Iblk & Afkb & D0 & D1 & D2 & D3 & Adt & Adc & Adk & Adp & Adl & Adb & Adf & Atkb & Ackb & Al2kb & Apkb).
Ltac geo_open GEO :=
  destruct GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).

Lemma art_free3P_out_dn : forall (M0 M7 M' : word -> option byte) (S t p q16 qr l2 blk b1 parr mb ms : Z) (bl : list (Z * Z)) (idx : nat) (kb kb' : nat) (D : list (list Z)),
  art_free3P_out M0 M7 M' S t p q16 qr l2 blk b1 parr mb ms bl idx kb' D -> (kb <= kb')%nat -> art_free3P_out M0 M7 M' S t p q16 qr l2 blk b1 parr mb ms bl idx kb D.
Proof.
  intros M0 M7 M' S t p q16 qr l2 blk b1 parr mb ms bl idx kb kb' D (O1 & O2 & O3 & REST) Hle.
  split; [exact O1|]. split; [exact O2|]. split; [exact (DInvK_le _ _ _ _ _ _ O3 Hle)|exact REST].
Qed.

Lemma art_cell8_injW : forall (M : word -> option byte) a v w, cellA M a 8 v -> cellA M a 8 w -> 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 -> v = w.
Proof.
  intros M a v w C1 C2 Hv Hw. unfold cell in *. rewrite C1 in C2.
  apply (f_equal (fun o : option (list byte) => match o with Some l => bytes_le_to_Z l | None => 0 end)) in C2.
  rewrite !SeqExec.bytes_le_to_Z_8 in C2. rewrite !art_u_lit in C2 by lia. exact C2.
Qed.

Section EntryFactsP.
Variable FSG : Type.
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M : word -> option byte).
Hypothesis REP : art_alloc_rep FSG rn G LB M.
Hypothesis LIVE : forall p, In p (art_live (g_log FSG G)) ->
  0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
  /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o)).
Hypothesis LIVE2 : forall p p', In p (art_live (g_log FSG G)) -> In p' (art_live (g_log FSG G)) -> fst p <> fst p' -> apart (fst p) (snd p) (fst p') (snd p').
Hypothesis LIVE3 : forall p, In p (art_live (g_log FSG G)) -> fst p mod 4096 = 0 /\ snd p mod 4096 = 0.
Hypothesis LIVESH : forall p, In p (art_live (g_log FSG G)) -> wrA M (EatPoison.SB + fst p / 8) (snd p / 8).

#[using="rn G LB M REP LIVE LIVE2 LIVE3 LIVESH"] Lemma art_wfp_sec :
  let bl := map art_sec_b (g_sec FSG G) in
  art_sec_cells M (rn_parr rn) bl /\ art_sec_geo (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_parr rn) bl
  /\ (forall b, In b bl -> In b (art_live (g_log FSG G))).
Proof.
  intros bl. pose proof REP as (ROK & ST & TH & (PCH & PRIM & WSH) & CH & SECR & QR & _). rok_open14 ROK. geo_open GEO.
  destruct SECR as (S0 & S8 & S56 & _ & S616 & _ & SNE & SCW & PER & _ & SLEN).
  assert (LENB : Z.of_nat (length bl) = Z.of_nat (length (g_sec FSG G))) by (unfold bl; rewrite length_map; reflexivity).
  assert (NTH : forall j b, nth_error bl j = Some b -> exists s, nth_error (g_sec FSG G) j = Some s /\ b = art_sec_b s).
  { intros j b Hj. unfold bl in Hj. rewrite nth_error_map in Hj. destruct (nth_error (g_sec FSG G) j) as [s|] eqn:Es; [|discriminate Hj]. cbn in Hj. injection Hj as <-. exists s. split; reflexivity. }
  assert (INB : forall b, In b bl -> exists i s, nth_error (g_sec FSG G) i = Some s /\ b = art_sec_b s).
  { intros b Hb. unfold bl in Hb. apply in_map_iff in Hb. destruct Hb as (s & <- & Hs). destruct (In_nth_error _ _ Hs) as (i & Hi). exists i, s. split; [exact Hi|reflexivity]. }
  assert (OBJ : forall p o, In p (art_live (g_log FSG G)) -> In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o)) by (intros p o Hp Ho; exact (proj2 (proj2 (proj2 (proj2 (LIVE p Hp)))) o Ho)).
  split.
  {
    unfold art_sec_cells. rewrite LENB. split; [exact S0|]. split; [exact S8|]. split; [exact S56|]. split; [exact S616|].
    split. { destruct (g_sec FSG G) as [|s0 r0] eqn:Es.
             - intros d k0 Hd Hk0. cbn [length] in Hk0. assert (k0 = 0%nat) by (clear - Hd Hk0; lia). subst k0. reflexivity.
             - eapply wr_sub; [exact (SCW (SNE ltac:(discriminate)))|clear; lia|clear - SLEN; lia]. }
    intros j b Hj. destruct (NTH j b Hj) as (s & Hs & ->). destruct (PER j s Hs) as (P1 & P2 & P3 & P4 & P5 & P6 & _). cbn [art_sec_b fst snd].
    split; [exact P1|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P3|exact (LIVESH _ P2)]. }
  split.
  {
    unfold art_sec_geo. rewrite LENB. split; [exact Plo|]. split; [clear - Phi SLEN; lia|]. split; [clear - SLEN; lia|].
    split. { unfold appmem, EatPoison.SB, kHighMemBeg. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Papp. clear - Papp SLEN. lia. }
    split. { unfold apart in *. clear - Apt SLEN. lia. } split. { unfold apart in *. clear - Apc SLEN. lia. }
    split.
    - intros b Hb. destruct (INB b Hb) as (i & s & Hs & ->). destruct (PER i s Hs) as (_ & P2 & _ & _ & _ & _ & Lo & Hi & Q & P0). cbn [art_sec_b fst snd].
      destruct (LIVE _ P2) as (L0 & L1 & L2 & L3 & _). destruct (LIVE3 _ P2) as (A1 & A2). cbn [fst snd] in *.
      assert (Hn : 1 <= sc_n s) by (destruct (sc_quar s); [destruct Q as ((b1 & _ & _ & _ & _ & Hn) & _)|destruct Q as (_ & (b1 & _ & _ & _ & _ & Hn) & _)]; clear - Hn; lia).
      split; [exact A1|]. split; [exact A2|]. split; [clear - Lo Hi Hn; lia|]. split; [exact P0|]. split; [exact L2|].
      split. { unfold appmem, EatPoison.SB, kHighMemBeg. clear - L3. lia. }
      pose proof (OBJ _ (rn_parr rn, 2 ^ 23) P2 ltac:(cbn; tauto)) as O1. pose proof (OBJ _ (rn_t rn, 4096) P2 ltac:(cbn; tauto)) as O2. pose proof (OBJ _ (rn_ctx rn, 4096) P2 ltac:(cbn; tauto)) as O3.
      cbn [fst snd] in O1, O2, O3. unfold apart in *. clear - O1 O2 O3 SLEN. repeat split; lia.
    - intros i j b b' Hi Hj NE. destruct (NTH i b Hi) as (s & Hs & ->). destruct (NTH j b' Hj) as (s' & Hs' & ->). cbn [art_sec_b fst snd].
      destruct (PER i s Hs) as (_ & P2 & _). destruct (PER j s' Hs') as (_ & P2' & _).
      apply (LIVE2 _ _ P2 P2'). cbn [fst]. intros E. apply NE. destruct (PER i s Hs) as (_ & _ & _ & _ & _ & Ci & _). destruct (PER j s' Hs') as (_ & _ & _ & _ & _ & Ci' & _). rewrite <- E in Ci'.
      assert (Li : (i < length (g_sec FSG G))%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
      assert (Li' : (j < length (g_sec FSG G))%nat) by (apply nth_error_Some; rewrite Hs'; discriminate).
      pose proof (art_cell8_injW _ _ _ _ Ci Ci' ltac:(clear - Li SLEN; lia) ltac:(clear - Li' SLEN; lia)) as Ei. apply Nat2Z.inj in Ei. exact Ei. }
  intros b Hb. destruct (INB b Hb) as (i & s & Hs & ->). destruct (PER i s Hs) as (_ & P2 & _). exact P2.
Qed.
End EntryFactsP.

Lemma art_objs_in6 : forall rn, In (rn_t rn, 4096) (art_objs rn) /\ In (rn_ctx rn, 4096) (art_objs rn) /\ In (rn_kbase rn, 0x2000011000) (art_objs rn)
  /\ In (rn_parr rn, 2 ^ 23) (art_objs rn) /\ In (rn_l2 rn, 2 ^ 20) (art_objs rn) /\ In (rn_blk rn, 2 ^ 23) (art_objs rn).
Proof. intros rn. unfold art_objs. cbn [In]. repeat split; tauto. Qed.

Section EntryP.
Variable FSG : Type.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_wf_entryPU :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) R (Mr rom : word -> option byte) (raw0 : word) (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z))
         (Sp u n q16 qr b1 km top bot : Z) (kb : nat) (i : nat) (s : art_sec) (Lz : HeapIfaceA.asan_layout) (Kz : list Z) (k0 : nat),
    let qtl := g_qt FSG G in
    let cl24 := g_cls FSG G 24 in
    let newb := art_free_newb qtl in
    let lastb := art_lastb qtl in
    let L := Z.of_nat (length qtl) in
    let B := bt_addr lastb in
    let cntB := Z.of_nat (length (bt_items lastb)) in
    let evs := art_flush_events (sc_map s) (sc_msize s) ++ [AMunmap (sc_map s) (sc_msize s)] in
    art_alloc_rep FSG rn G LB Mr ->
    nth_error (g_sec FSG G) i = Some s /\ sc_quar s = false /\ sc_u s = u /\ sc_n s = n ->
    getr R 1 = raw0 -> ret_ok raw0 -> getr R 2 = Z_to_bv 64 Sp -> getr R 4 = Z_to_bv 64 (rn_tp rn) -> getr R 10 = Z_to_bv 64 u ->
    u = 16 * q16 -> 2 ^ 28 < n <= 2 ^ 34 -> n <= 8 * qr <= n + 7 -> 0 <= b1 < 2 ^ 24 -> b1 mod 4 = 1 -> b1 / 256 = n / 2 ^ 32 ->
    cellA Mr (u - 16) 4 (2 + 256 * b1) -> cellA Mr (u - 12) 4 n -> HAJ.shadow_blkR Mr u n ->
    rn_HI rn + 4096 <= Sp - 4096 -> Sp < 2 ^ 47 -> Sp mod 16 = 0 ->
    top = ar_stack_top (rn_ar rn) -> bot = ar_stack_bottom (rn_ar rn) -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 ->
    wrA Mr (Sp - 4096) 4096 -> HeapIfaceA.hl_segs Lz = ASEGS -> ukeyG Lz (rn_ar rn) 0x7a2e0 Mr Sp (U raw0) (U (getr R 8)) Kz ->
    g_depot FSG G = k0 -> (In Kz (rn_keys rn) \/ (1 <= k0)%nat) -> (kb <= if HeapIfaceAEr.HAR.kin Kz (rn_keys rn) then k0 else pred k0)%nat ->
    cl_mu cl24 = 262144 * km ->
    (newb = true -> cl_cache cl24 = [] -> art_cls_needs_populate 24 cl24 = true ->
       cl_mu cl24 + 262144 <= 3758096384 /\ art_cls_mfa' cl24 (Z.of_nat (length (cl_free cl24)) + art_cls_new 24 cl24) <= 536870912) ->
    (newb = true -> art_cls_ok 24 (art_ca_pre 24 cl24)) ->
    art_evok_list EVOK log (art_enq_events newb (rn_spb rn) cl24) ->
    art_evok_list EVOK log evs ->
    (forall p, In p (art_live (g_log FSG G)) ->
       0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
       /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o))) ->
    (forall p p', In p (art_live (g_log FSG G)) -> In p' (art_live (g_log FSG G)) -> fst p <> fst p' -> apart (fst p) (snd p) (fst p') (snd p')) ->
    (forall p, In p (art_live (g_log FSG G)) -> fst p mod 4096 = 0 /\ snd p mod 4096 = 0) ->
    (forall p, In p (art_live (g_log FSG G)) -> wrA Mr (EatPoison.SB + fst p / 8) (snd p / 8)) ->

    (forall regs' (M7 Mr' : word -> option byte),
        getr regs' 2 = Z_to_bv 64 Sp -> getr regs' 1 = raw0 ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r) ->
        art_free3P_out Mr M7 Mr' Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn) b1 (rn_parr rn) (sc_map s) (sc_msize s) (map art_sec_b (g_sec FSG G)) i kb (Kz :: rn_keys rn) ->
        Q (log ++ evs) (mkst regs' raw0 Mr' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst R (0x7a1a8 : word) Mr rom).
Proof.
  intros Q log R Mr rom raw0 rn G LB Sp u n q16 qr b1 km top bot kb i s Lz Kz k0 qtl cl24 newb lastb L B cntB evs
         REP KIND H1 Hret H2 H4 H10 Eu Hn Hqr Hb1 Hty Hlink Chw Cn SHB HHI HS47 HS16 Etop Ebot Hbot Hbt Htop4 Htop W HSEGz UKz Edep HKin Hkb Emu Room OKpre EV SEV LIVE LIVE2 LIVE3 LIVESH KX.
  assert (EdepW : (kb <= g_depot FSG G)%nat) by (rewrite Edep; destruct (HeapIfaceAEr.HAR.kin Kz (rn_keys rn)); cbn [pred] in Hkb; clear - Hkb; Lia.lia).
  assert (Hn30 : 1 <= n <= 2 ^ 34) by (clear - Hn; lia).
  assert (KINDk : exists s0, nth_error (g_sec FSG G) i = Some s0 /\ sc_quar s0 = false /\ sc_u s0 = u /\ sc_n s0 = n) by (exists s; exact KIND).
  pose proof KIND as (His & Hqs & Esu & Esn).
  destruct (art_wfa_thq FSG rn G LB Mr REP n Hn30) as (HL & HB & Hby & Hby' & CL & Cby & wB & LBN).
  destruct (art_frep_u_far FSG rn G LB Mr u n q16 qr 0 kb (FKS i) REP Eu Hn30 Hqr ltac:(clear; lia) KINDk EdepW LIVE LIVE2 LIVE3) as (U1 & U2 & U3 & U4 & Ut & Uc & Ul2 & Ublk & Uparr & _ & _ & Uris & Ufa).
  pose proof (art_frep_u_B FSG rn G LB Mr u n q16 qr 0 kb (FKS i) REP Eu Hn30 Hqr ltac:(clear; lia) KINDk EdepW LIVE LIVE2 LIVE3) as UB.
  pose proof (art_frep_wr_hdr FSG rn G LB Mr u n q16 b1 kb (FKS i) REP Eu Hn30 KINDk EdepW LIVE3) as Wp.
  pose proof (art_frep_wr_sh FSG rn G LB Mr u n q16 qr 0 kb (FKS i) REP Eu Hn30 Hqr ltac:(clear; lia) KINDk EdepW LIVE LIVE2 LIVE3 SHB) as Wus.
  pose proof (art_frep_hp24 FSG rn G LB Mr Sp u n q16 qr 0 km kb (FKS i) REP Eu Hn30 Hqr ltac:(clear; lia) KINDk HHI Emu EdepW LIVE LIVE2 LIVE3 OKpre) as HP24.
  assert (Hq0 : 1 <= qr) by (clear - Hn Hqr; lia).
  pose proof REP as (ROK & ST & TH & (PH & PRIM & Wsh) & _ & SECR & QR & DEP & (IA1 & IA2 & _) & _).
  assert (Cgot : cellA Mr 0x1391f8 8 1) by (clear - ST; unfold art_rt_statics, art_alloc_rodata in ST; decompose [and] ST; assumption).
  assert (Hby20 : art_batches_bytes qtl <= 2 ^ 20) by (destruct QR as (_ & _ & Bt & _); exact Bt).
  rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct ST as (PC & LY & T & _ & _ & DR & _ & C1 & _ & _ & _ & _ & _ & C7 & _ & C9 & _ & _ & _ & C13 & C14 & C15 & C16 & _).
  destruct TH as (Wt & T1 & T2 & T3 & T4 & T5 & T6 & _). rewrite <- Etop in T3. rewrite <- Ebot in T4.
  destruct (PRIM 24 ltac:(lia)) as (RC & OK & Hinit & _). fold cl24 in RC, OK, Hinit.
  pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _).
  unfold art_rt_depot in DEP. rewrite Edep in DEP.
  assert (A24 : forall X Y, apart (u - 16) (16 + 8 * qr) X Y -> apart (u - 16) 24 X Y) by (intros X Y A; unfold apart in *; clear - A Hq0; lia).
  assert (A24' : forall X Y, apart (u - 16) 32 X Y -> apart (u - 16) 24 X Y) by (intros X Y A; unfold apart in *; clear - A; lia).

  destruct SECR as (S0 & S8 & S56 & _ & S616 & _ & SNE & SCW & PER & _ & SLEN).
  destruct (PER i s His) as (P1 & P2 & P3 & P4 & P5 & P6 & Lo & Hi2 & _ & P0). rewrite Esu in Lo. rewrite Esu, Esn in Hi2.
  destruct (LIVE _ P2) as (L0 & L1 & L2 & L3 & OB). cbn [fst snd] in L0, L1, L2, L3, OB. destruct (LIVE3 _ P2) as (Am1 & Am2). cbn [fst snd] in Am1, Am2.
  assert (Hil : (i < length (g_sec FSG G))%nat) by (apply nth_error_Some; rewrite His; discriminate).
  destruct (art_objs_in6 rn) as (Iot & Ioc & Iok & Iop & Iol & Iob).
  pose proof (OB _ Iok) as Okb. pose proof (OB _ Iot) as Ot. pose proof (OB _ Iol) as Ol2. pose proof (OB _ Iob) as Oblk. pose proof (OB _ Iop) as Oparr. cbn [fst snd] in Okb, Ot, Ol2, Oblk, Oparr.

  destruct (art_cell_exists Mr (rn_t rn + 2800 + 40) 8 ltac:(lia0) ltac:(clear - G9; cbn; lia) ltac:(clear - G7; lia) ltac:(clear - G8 G2; cbn; lia) ltac:(eapply wr_sub; [exact Wt|lia0|lia0c])) as (f1 & _ & Cf1).
  destruct (art_cell_exists Mr (rn_t rn + 2800 + 48) 8 ltac:(lia0) ltac:(clear - G9; cbn; lia) ltac:(clear - G7; lia) ltac:(clear - G8 G2; cbn; lia) ltac:(eapply wr_sub; [exact Wt|lia0|lia0c])) as (f2 & _ & Cf2).

  destruct (art_wfp_sec FSG rn G LB Mr REP LIVE LIVE2 LIVE3 LIVESH) as (SCELLS & SGEO & SBL).
  apply (art_free3P EVOK GR Lz (rn_ar rn) Q log R Mr rom raw0 Sp (rn_HI rn) u q16 n qr b1 (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) km
           (rn_l2 rn) (rn_blk rn) top bot L B wB cntB (art_bt_bytes lastb) (art_batches_bytes qtl) k0 (rn_keys rn) Kz (g_ia FSG G) (g_inited FSG G) cl24
           (rn_parr rn) (sc_map s) (sc_msize s) f1 f2 (map art_sec_b (g_sec FSG G)) i
           H1 Hret H2 H4 H10 ltac:(clear - U1; lia) Eu Hn Hqr Hb1 Hty Hlink
           ltac:(unfold EatPoison3.art_poison_lo_ok, EatPoison3.art_poison_hi_ok, SB, kHighMemBeg, kHighMemEnd; clear - U1 U2 U4 Hq0 G2; lia)
           GEO HHI HS47 HS16 Hbot Hbt Htop4 Htop Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs
           ltac:(clear - U3; lia) (A24 _ _ Ut) (A24 _ _ Uc) (A24 _ _ Ul2) (A24 _ _ Ublk) (A24' _ _ Uris) (A24' _ _ Ufa) UB
           W HSEGz (eq_sym Etop) (eq_sym Ebot) UKz Wt Wp Wus (art_img_wr_iaflag Mr 0x1d1488 4 ltac:(lia) ltac:(lia) ltac:(lia)) (art_img_wr_iatab Mr 0x142c00 0x81030 ltac:(lia) ltac:(lia) ltac:(lia))
           LY T PC C1 C13 C14 T6 T5 T3 T4 IA1
           ltac:(intros E j Hj; replace (0x142c08 + 8 * j) with (0x142c00 + 8 + 8 * j) by lia; exact (IA2 E j Hj))
           Chw Cn C7 T1 T2 C15 C16 C9 PH RC OK Hinit Emu).
  -
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
  - exact HKin.
  - exact DR.
  -   rewrite nth_error_map, His. reflexivity.
  - exact SGEO.
  -   unfold apart in Okb |- *. clear - Okb Kspb. lia.
  - exact Lo.
  - clear - Hi2 Hn. lia.
  -
    intros M' GR7 AG7.
    assert (GP : forall a len, 0x698000 <= a -> a + len <= rn_HI rn -> (a + len <= 0x7fff7000 \/ 0x10007fff8000 <= a) ->
              apart a len (rn_t rn) 4096 -> apart a len (rn_l2 rn) (2 ^ 20) -> apart a len (rn_blk rn) (2 ^ 23) -> (a + len <= u - 16 \/ u + 8 <= a) ->
              art_gap (art_free3_W Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn)) a len).
    { intros a len Ha0 Ha1 Ha2 Xt Xl2 Xblk Xu. unfold art_free3_W. cbn [art_gap fst snd]. unfold apart in Xt, Xl2, Xblk |- *.
      pose proof (Z.div_le_mono _ _ 8 ltac:(lia0) (proj1 Hqr)) as D8.
      repeat split; try exact I.
      all: try (clear - Ha1 HHI; lia). all: try (clear - Xt; lia). all: try (clear - Xu; lia). all: try (clear - Xu Hqr Hn; lia).
      all: try (clear - Ha2 Ha0 Eu U1 U2 Hq0 G2; lia). all: try (clear - Ha0; lia). all: try (clear - Xl2; lia). all: try (clear - Xblk; lia). }
    apply (art_sec_cells_tr (art_free3_W Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn)) Mr M' (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_parr rn) _ SGEO ltac:(clear - G2; lia) GR7 AG7).
    + unfold art_free3_W. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I.
      all: try (clear - HHI G1; lia). all: try (clear - G9; lia). all: try (clear - U1 Eu; lia). all: try (clear - Il2; lia). all: try (clear - Iblk; lia). all: try lia0.
    + apply (art_cell_tr _ Mr M' _ 4%nat _ AG7); [|lia0|lia0c|exact S616].
      unfold art_free3_W. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I.
      all: try (clear - HHI G1; lia). all: try (clear - G9; lia). all: try (clear - U1 Eu; lia). all: try (clear - Il2; lia). all: try (clear - Iblk; lia). all: try lia0.
    + rewrite length_map. unfold art_free3_W. cbn [art_gap fst snd]. unfold apart. unfold apart in Apt, Apl, Apb, Uparr. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Papp. repeat split; try exact I.
      all: try (clear - Phi HHI SLEN; lia). all: try (clear - Apt SLEN; lia). all: try (clear - Uparr SLEN Hq0; lia). all: try (clear - Papp SLEN Eu U1 U2 G2 Hq0; lia). all: try (clear - Plo SLEN; lia).
      all: try (clear - Apl SLEN; lia). all: try (clear - Apb SLEN; lia).
    + intros b Hb. pose proof (SBL b Hb) as HbL. destruct (LIVE _ HbL) as (Bl0 & Bl1 & Bl2 & Bl3 & OBb). destruct (LIVE3 _ HbL) as (Bm1 & Bm2).
      apply in_map_iff in Hb. destruct Hb as (s' & <- & Hs'). cbn [art_sec_b fst snd] in *.
      destruct (In_nth_error _ _ Hs') as (j & Hj). destruct (PER j s' Hj) as (_ & _ & _ & _ & _ & _ & Lo' & Hi2' & Q' & P0').
      assert (Hn' : 1 <= sc_n s') by (destruct (sc_quar s'); [destruct Q' as ((bb & _ & _ & _ & _ & X) & _)|destruct Q' as (_ & (bb & _ & _ & _ & _ & X) & _)]; clear - X; lia).
      pose proof (OBb _ Iot) as Bt'. pose proof (OBb _ Iol) as Bl2'. pose proof (OBb _ Iob) as Bblk'. cbn [art_sec_b fst snd] in Bt', Bl2', Bblk', Bl0, Bl1, Bl2, Bl3, Bm1, Bm2.
      assert (Xu : sc_map s' + 32 <= u - 16 \/ u + 8 <= sc_map s').
      { destruct (Z.eq_dec (sc_map s') (sc_map s)) as [E|NE].
        - left. rewrite E. clear - Lo. lia.
        - pose proof (LIVE2 _ _ HbL P2 NE) as AP. cbn [art_sec_b fst snd] in AP. unfold apart in AP. clear - AP Lo Hi2 Hn Lo' Hi2' Hn'. lia. }
      apply GP; [exact P0'|clear - Bl2 Lo' Hi2' Hn'; lia|clear - Bl3 Lo' Hi2' Hn'; lia| | | |exact Xu].
      * unfold apart in Bt' |- *. clear - Bt' Lo' Hi2' Hn'. lia.
      * unfold apart in Bl2' |- *. clear - Bl2' Lo' Hi2' Hn'. lia.
      * unfold apart in Bblk' |- *. clear - Bblk' Lo' Hi2' Hn'. lia.
    + exact SCELLS.
  -
    intros x Hx.
    destruct (nth_error (g_sec FSG G) (length (g_sec FSG G) - 1)) as [sl|] eqn:Esl; [|exfalso; apply nth_error_None in Esl; clear - Esl Hil; lia].
    assert (EL : fst (nth (length (map art_sec_b (g_sec FSG G)) - 1) (map art_sec_b (g_sec FSG G)) (0, 0)) = sc_map sl).
    { rewrite length_map. change (0, 0) with (art_sec_b art_dsec). rewrite map_nth. rewrite (nth_error_nth _ _ _ Esl). reflexivity. }
    rewrite EL. destruct (PER _ sl Esl) as (_ & Q2 & _ & _ & _ & _ & QLo & QHi & QQ & Q0).
    destruct (LIVE _ Q2) as (Ql0 & Ql1 & Ql2 & Ql3 & OBl). cbn [fst snd] in Ql0, Ql1, Ql2, Ql3, OBl.
    pose proof (OBl _ Iot) as Qt. cbn [fst snd] in Qt.
    assert (Hnl : 1 <= sc_n sl) by (destruct (sc_quar sl); [destruct QQ as ((bb & _ & _ & _ & _ & X) & _)|destruct QQ as (_ & (bb & _ & _ & _ & _ & X) & _)]; clear - X; lia).
    pose proof (Z.div_mod (sc_map s) 4096 ltac:(lia0)) as Dv1. rewrite Am1 in Dv1. pose proof (Z.div_mod (sc_msize s) 4096 ltac:(lia0)) as Dv2. rewrite Am2 in Dv2.
    assert (E1 : sc_map s / 8 = 512 * (sc_map s / 4096)) by (rewrite Dv1 at 1; replace (4096 * (sc_map s / 4096) + 0) with ((512 * (sc_map s / 4096)) * 8) by lia0; rewrite Z_div_mult by lia0; reflexivity).
    assert (E2 : sc_msize s / 8 = 512 * (sc_msize s / 4096)) by (rewrite Dv2 at 1; replace (4096 * (sc_msize s / 4096) + 0) with ((512 * (sc_msize s / 4096)) * 8) by lia0; rewrite Z_div_mult by lia0; reflexivity).
    unfold art_cbr_sec_fp, art_secd_fp. apply art_out_intro. intros p Hp. cbn [In app] in Hp. unfold EatPoison.SB in Hp.
    repeat (destruct Hp as [<-|Hp]); try (destruct Hp); cbn [fst snd]; unfold apart in Qt, Ot.
    all: try (clear - Hx; lia).
    all: try (clear - Hx G8 HHI; lia).
    all: try (clear - Hx G1 G9 HHI; lia).
    all: try (clear - Hx Phi HHI Hil SLEN Apt; unfold apart in Apt; lia).
    all: try (clear - Hx QLo QHi Hnl Ql2 HHI Qt; lia).
    all: try (clear - Hx Dv1 Dv2 E1 E2 L0 L2 G1 G2 G10 G8 HHI; lia).
    all: try (clear - Hx L2 HHI Ot; lia).
    all: fail 99 "SFR open".
  - exact Cgot.
  - exact Cf1.
  - exact Cf2.
  - exact Hby20.
  - exact SEV.
  - intros regs' M7 Mr' Q2 Q1 QK OUT. apply (KX regs' M7 Mr' Q2 Q1 QK). exact (art_free3P_out_dn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OUT Hkb).
Qed.
End EntryP.

Lemma art_frepP_credit : forall FSG BUDGET rn (G : art_gs FSG) (LB : list (Z * Z)) (u n : Z) (kb i : nat) (s : art_sec) (cr : credit) (warm : bool),
  nth_error (g_sec FSG G) i = Some s ->
  art_credit_ok FSG BUDGET rn G LB cr -> List.NoDup (map fst LB) -> In (u, n) LB ->
  (if warm then kb = g_depot FSG G else g_depot FSG G = Datatypes.S kb) ->
  art_credit_ok FSG BUDGET rn (art_gs_freeP FSG G kb i s) (lb_remove u LB) (if warm then (fst cr + 1, snd cr) else cr).
Proof.
  intros FSG BUDGET rn G LB u n kb i s cr warm His (irr & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & QT & QG) NDLB Hin KBW.
  set (evs := art_flush_events (sc_map s) (sc_msize s) ++ [AMunmap (sc_map s) (sc_msize s)]).
  pose proof (art_lb_remove_length u n LB Hin) as HLEN. pose proof (art_nirr_lb_remove (rn_spb rn) u n LB NDLB Hin) as HIRR.
  assert (ECS : art_cost_sum evs = 0 /\ art_cost_sec evs = 0).
  { unfold evs, EatRecycle2C.art_flush_events. destruct (EatRecycle1.art_flush_beg (sc_map s) <? EatRecycle1.art_flush_end (sc_map s) (sc_msize s)); split; reflexivity. }
  destruct ECS as (EC1 & EC2).
  assert (LL : Z.of_nat (length (art_live (g_log FSG G ++ evs))) <= Z.of_nat (length (art_live (g_log FSG G)))).
  { unfold evs. rewrite art_live_app_unmap. apply Nat2Z.inj_le. apply filter_length_le. }
  assert (SL : Z.of_nat (length (art_swap_remove art_dsec i (g_sec FSG G))) + 1 = Z.of_nat (length (g_sec FSG G))).
  { rewrite art_swap_remove_length. assert (Hi : (i < length (g_sec FSG G))%nat) by (apply nth_error_Some; rewrite His; discriminate). clear - Hi. lia. }
  exists irr. unfold art_credit_ok. cbn [art_gs_freeP g_log g_sec g_sec_committed g_depot g_cls g_qt g_qg]. fold evs.
  rewrite EarWrapMallocX.art_cost_sum_app, art_cost_sec_app, EC1, EC2.
  assert (DEP : 2 * ((if warm then fst cr + 1 else fst cr) + Z.of_nat (length (lb_remove u LB))) <= Z.of_nat kb /\ 0 <= (if warm then fst cr + 1 else fst cr) /\ (if warm then fst cr + 1 else fst cr) <= fst cr + 1).
  { destruct warm; [subst kb|rewrite KBW, Nat2Z.inj_succ in C9]; cbn [fst]; clear - C1 C9 HLEN; lia. }
  destruct DEP as (DEP & P1 & P2).
  destruct warm; cbn [fst snd] in DEP, P1, P2 |- *; destruct (art_irr (rn_spb rn) (u - 16, n)).
  all: split; [exact P1|]; split; [exact C2|]; split; [exact C3|]; split; [clear - C4 HLEN P2 HIRR; lia|]; split; [clear - C5; lia|]; split; [clear - C6; lia|].
  all: split; [clear - C7 LL; lia|]; split; [clear - C8 SL; lia|]; split; [exact DEP|]; split; [clear - C10 HIRR; lia|]; split; [exact QT|exact QG].
Qed.

Section FinishP.
Variable FSG : Type.
Variable FSINV : art_run -> FSG -> list fframe -> list fframe -> (word -> option byte) -> Prop.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable L : asan_layout.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x698000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Hypothesis FSLAW2 : forall gfs FF LK (M M' : word -> option byte), FSINV rn gfs FF LK M -> (forall x : word, art_fs_zone rn (U x) -> M' x = M x) ->
  (forall a : word, in_shadow_rw (U a) -> M' a <> None) -> FSINV rn gfs FF LK M'.
Hypothesis FS_IN : forall gfs FF LK M, FSINV rn gfs FF LK M ->
  forall f, In f (FF ++ LK) -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f).

#[using="HLlo HLhi HLst FSLAW2 FS_IN"] Theorem art_wf_finishP : forall (G : art_gs FSG) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A A' : list (Z * Z)) (M M1 : word -> option byte) (model model' : Model)
    (log' : list aev) (Sp u n q16 qr b1 : Z) (kb : nat) (i : nat) (s : art_sec) (Dz : list (list Z)) (M7 : word -> option byte),
  let evs := art_flush_events (sc_map s) (sc_msize s) ++ [AMunmap (sc_map s) (sc_msize s)] in
  let G' := art_gs_freeP FSG G kb i s in
  art_alloc_rep FSG rn G LB (mrestrict (bhid A model) M) ->
  nth_error (g_sec FSG G) i = Some s /\ sc_quar s = false /\ sc_u s = u /\ sc_n s = n ->
  u = 16 * q16 -> 1 <= n <= 2 ^ 34 -> n <= 8 * qr <= n + 7 -> 0 <= b1 < 2 ^ 24 -> rn_HI rn + 4096 <= Sp - 4096 -> Sp < 2 ^ 47 -> (kb <= g_depot FSG G)%nat ->
  incl (rn_keys rn) Dz ->
  FSINV rn (g_fs FSG G) FF LK M ->
  art_credit_ok FSG BUDGET rn G' (lb_remove u LB) cr ->
  art_client_ok rn LB FF LK A M -> art_kn_ok MAPS0 RESV0 rn ->
  art_lazy_ok FSG rn G A (m_vm_lazy model) -> art_eager_ok LB A (m_vm_lazy model) ->
  In (u, n) LB -> (forall b0, In b0 (lb_remove u LB) -> In b0 LB /\ fst b0 <> u) ->
  (forall p, In p (art_live (g_log FSG G)) ->
     0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
     /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o))) ->
  (forall p p', In p (art_live (g_log FSG G)) -> In p' (art_live (g_log FSG G)) -> fst p <> fst p' -> apart (fst p) (snd p) (fst p') (snd p')) ->
  (forall p, In p (art_live (g_log FSG G)) -> fst p mod 4096 = 0 /\ snd p mod 4096 = 0) ->
  wrA (mrestrict (bhid A model) M) (Sp - 4096) 4096 ->
  log' = g_log FSG G ++ evs ->
  BInv ASEGS MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET log' A' M1 model' ->
  bhist A M model (g_log FSG G) log' A' M1 model' ->
  art_free3P_out (mrestrict (bhid A model) M) M7 (mrestrict (bhid A' model') M1) Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn) b1 (rn_parr rn) (sc_map s) (sc_msize s) (map art_sec_b (g_sec FSG G)) i kb Dz ->
  art_ri_inv FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn (lb_remove u LB) FF LK cr A' M1 (vml_of model')
  /\ DInvK (rn_l2 rn) (rn_blk rn) kb Dz (mrestrict (bhid A' model') M1)
  /\ aheap_pres L (rn_ar rn) (lb_remove u LB) FF Sp 4096 M M1.
Proof.
  intros G LB FF LK cr A A' M M1 model model' log' Sp u n q16 qr b1 kb i s Dz M7 evs G' REP KIND Eu Hn Hqr Hb1 HHI HS47 Edep HDz FS CREDp CLI KN LZ EG Hin Hother LIVE LIVE2 LIVE3 W0 Elog B1 BH OUT.
  set (Mr0 := mrestrict (bhid A model) M) in *. set (Mr' := mrestrict (bhid A' model') M1) in *.
  pose proof (art_frepP_rep FSG rn G LB Mr0 M7 Mr' Sp u n q16 qr b1 kb i s Dz REP KIND Eu (proj1 Hn) Hqr Hb1 HHI HS47 Edep OUT HDz LIVE LIVE2 LIVE3 Hother) as REP'. fold G' in REP'.
  pose proof (art_frepP_dinv FSG rn G LB Mr0 M7 Mr' Sp u n q16 qr b1 kb i s Dz REP KIND Eu (proj1 Hn) Hqr Hb1 HHI HS47 Edep OUT HDz LIVE LIVE2 LIVE3 Hother) as DIz.
  pose proof (art_frepP_agree FSG rn G LB Mr0 M7 Mr' Sp u n q16 qr b1 kb i s Dz REP KIND Eu (proj1 Hn) Hqr Hb1 HHI HS47 Edep OUT HDz LIVE LIVE2 LIVE3 Hother) as AGR.
  pose proof (art_frepP_wscr FSG rn G LB Mr0 M7 Mr' Sp u n q16 qr b1 kb i s Dz REP KIND Eu (proj1 Hn) Hqr Hb1 HHI HS47 Edep OUT HDz LIVE LIVE2 LIVE3 Hother W0) as WSCR.
  destruct (art_frepP_out_bundle FSG rn G LB Mr0 M7 Mr' Sp u n q16 qr b1 kb i s Dz REP KIND Eu (proj1 Hn) Hqr Hb1 HHI HS47 Edep OUT HDz LIVE LIVE2 LIVE3 Hother) as (RB & RST & RIM & RFS & RDT & RTH & RSH & EVR).
  set (W := art_freeP_W FSG rn G Sp u q16 qr i s) in *.
  assert (KINDk : exists s0, nth_error (g_sec FSG G) i = Some s0 /\ sc_quar s0 = false /\ sc_u s0 = u /\ sc_n s0 = n) by (exists s; exact KIND).
  destruct (art_frep_u_far FSG rn G LB Mr0 u n q16 qr 0 kb (FKS i) REP Eu Hn Hqr ltac:(clear; lia) KINDk Edep LIVE LIVE2 LIVE3) as (U1 & U2 & _ & _ & _ & _ & _ & _ & _ & Ufs & _).
  assert (Hq0 : 1 <= qr) by (clear - Hn Hqr; lia).
  set (FPT := fun z => exists p, In p W /\ fst p <= z < fst p + snd p).
  assert (NF : forall a, art_out W a -> ~ FPT a) by (intros a Ho (p & Hp & Hr); exact (art_in_not_out _ _ a Hp Hr Ho)).
  assert (FR3 : forall x : word, ~ FPT (U x) -> Mr' x = Mr0 x).
  { intros x N. apply AGR. apply art_out_intro. intros p Hp Hr. apply N. exists p. split; [exact Hp|exact Hr]. }
  assert (EVL : forall sfx, log' = g_log FSG G ++ sfx -> forall z, in_ev_ranges sfx z -> FPT z).
  { intros sfx El z Hz. rewrite Elog in El. apply app_inv_head in El. subst sfx. exact (EVR z Hz). }
  pose proof (art_lift_frame A A' M M1 model model' (g_log FSG G) log' BH FPT FR3 EVL) as FRF.
  pose proof BH as (sfx & Esfx & INC & BH2 & _ & BH4 & BH5).
  assert (Esfx' : sfx = evs). { rewrite Elog in Esfx. apply app_inv_head in Esfx. symmetry. exact Esfx. }
  assert (KINDS : forall ev, In ev evs -> (exists a l, ev = AMadvise a l) \/ (exists a l, ev = AMunmap a l)).
  { intros ev Hev. unfold evs, EatRecycle2C.art_flush_events in Hev. apply in_app_or in Hev. destruct Hev as [Hev|[<-|[]]]; [|right; eexists; eexists; reflexivity].
    destruct (EatRecycle1.art_flush_beg (sc_map s) <? EatRecycle1.art_flush_end (sc_map s) (sc_msize s)); [|destruct Hev]. destruct Hev as [<-|[]]. left. eexists; eexists; reflexivity. }
  assert (NONULL : forall len r, ~ In (AMmapNull len r) sfx).
  { intros len r Hev. rewrite Esfx' in Hev. destruct (KINDS _ Hev) as [(a0 & l0 & E)|(a0 & l0 & E)]; discriminate E. }
  assert (NONR : forall a l, ~ In (AMmapFixedNR a l) sfx).
  { intros a l Hev. rewrite Esfx' in Hev. destruct (KINDS _ Hev) as [(a0 & l0 & E)|(a0 & l0 & E)]; discriminate E. }
  assert (B5' : forall x : word, page_in_ranges (page_base x) (m_vm_lazy model') = true -> page_in_ranges (page_base x) (m_vm_lazy model) = true).
  { intros x Hx. destruct (BH5 x Hx) as [Hl|(a & l & Hev & _)]; [exact Hl|]. exfalso. exact (NONR _ _ Hev). }
  pose proof REP as (ROK & _). pose proof ROK as ROK'. rok_open14 ROK'. pose proof GEO as GEO'. geo_open GEO'.

  assert (LZ' : art_lazy_ok FSG rn G' A' (m_vm_lazy model')).
  { apply (art_lazy_ok_step FSG rn G G' A (m_vm_lazy model) A' (m_vm_lazy model') LZ INC).
    - intros x Hx. exact (proj1 (BH2 x Hx)).
    - intros wd Hwd. destruct (BH4 wd Hwd) as [Hi|(len & r & Hev & _)]; [exact Hi|]. exfalso. exact (NONULL _ _ Hev).
    - exact B5'.
    - intros x C. left. exact C. }
  assert (EG' : art_eager_ok (lb_remove u LB) A' (m_vm_lazy model')) by exact (art_eager_ok_remove LB A (m_vm_lazy model) A' (m_vm_lazy model') u EG (bi_awf _ _ _ _ _ _ _ _ _ _ _ B1) B5').

  assert (NSH3 : forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> (lo + len <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= lo) ->
            (lo + len <= u - 16 \/ u + 8 * qr <= lo) -> (forall p, In p (art_live (g_log FSG G)) -> apart (fst p) (snd p) lo len) -> HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> ~ FPT a).
  { intros lo len a H0 H1 H47 Hk Hu Hl Ha. apply NF. exact (RSH lo len a H0 H1 H47 Hk Hl Ha). }

  assert (SCR1 : forall a, Sp - 4096 <= a < Sp -> M1 (Z_to_bv 64 a) <> None).
  { intros a Ha. pose proof (art_wr_wview ASEGS Mr' (Sp - 4096) 4096 ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia) WSCR (Z_to_bv 64 a)) as V.
    rewrite art_u_lit in V by (clear - Ha HHI G1 HS47; lia). specialize (V ltac:(clear - Ha; lia)). rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha HHI G1 HS47; lia); right; clear - Ha HHI G1; lia).
    unfold Mr', mrestrict in V. destruct (bhid A' model' (Z_to_bv 64 a)); [exfalso; apply V; reflexivity|exact V]. }
  assert (LVF : forall p, In p (art_live (g_log FSG G)) -> 0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o))).
  { intros p Hp. destruct (LIVE p Hp) as (X0 & X1 & X2 & _ & X4). split; [exact X0|]. split; [exact X1|]. split; [exact X2|exact X4]. }
  destruct (art_wfc_client_r L HLlo HLhi HLst rn LB FF LK A A' M M1 FPT (art_live (g_log FSG G)) Sp u n qr ROK CLI INC FRF
              ltac:(intros b0 a Hb0 Ha; apply NF; exact (RB b0 a Hb0 Ha))
              ltac:(intros a Ha Ns; apply NF; exact (RST a (proj1 Ha) (proj2 Ha) Ns))
              ltac:(intros a Ha NZ; apply NF; apply (RIM a Ha); intros X; apply NZ; unfold art_zone_statics; [right; left; exact X|right; right; left; exact X])
              ltac:(intros a Ha; apply NF; exact (RFS a Ha))
              NSH3 LVF (conj U1 (conj U2 Ufs)) Hq0 (FS_IN _ _ _ _ FS) SCR1) as (CLI' & AHP).
  split; [|split; [exact DIz|exact AHP]].

  exists G'. cbn [vml_of fst snd]. fold Mr'.
  split; [exact REP'|]. split.
  { change (g_fs FSG G') with (g_fs FSG G). apply (FSLAW2 (g_fs FSG G) FF LK M M1 FS); [|exact (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B1)]. intros x Hz. apply FRF. unfold apart in Ufs. unfold FS_BYTES in *.
    destruct Hz as [Z0|[Z0|[Z0|[(Z0 & NS)|[Z0|Z0]]]]].
    - apply NF. apply RFS. unfold FS_BYTES. exact Z0.
    - apply NF. apply RTH. clear - Z0. lia.
    - apply (NSH3 (ar_fs (rn_ar rn)) 0xb09000 (U x)); [clear - Flo; lia|lia0|clear - Fhi G2; lia|unfold apart in Afkb; clear - Afkb; lia|clear - Ufs Hq0; lia| |].
      + intros p Hp. destruct (LVF p Hp) as (_ & _ & _ & OB). pose proof (OB (ar_fs (rn_ar rn), FS_BYTES) (proj1 (art_objs_in_r rn))) as Ap. cbn [fst snd] in Ap. unfold FS_BYTES in Ap. exact Ap.
      + pose proof (art_S_pred (ar_fs (rn_ar rn) + 0xb09000)). unfold FS_BYTES in Z0. clear - Z0 H. lia.
    - apply NF. apply (RIM _ Z0); intros X; apply NS; unfold art_zone_statics; [right; left; exact X|right; right; left; exact X].
    - apply (NSH3 0x10000 (0x698000 - 0x10000) (U x)); [lia0|lia0|lia0|left; clear - G4 Kspb; lia|left; clear - U1; lia| |].
      + intros p Hp. destruct (LVF p Hp) as (_ & P1 & _ & OB).
        destruct (art_objs_in_r rn) as (_ & I1 & I2 & I3 & I4).
        pose proof (OB _ I1) as A1. pose proof (OB _ I2) as A2. pose proof (OB _ I3) as A3. pose proof (OB _ I4) as A4.
        cbn [fst snd] in A1, A2, A3, A4. unfold apart in *. clear - A1 A2 A3 A4 P1. lia.
      + pose proof (art_S_pred 0x698000). replace (0x10000 + (0x698000 - 0x10000) - 1) with (0x698000 - 1) by lia0. clear - Z0 H. lia.
    - apply NF. apply RDT. exact Z0. }
  split. { assert (ELOG : g_log FSG G' = log') by (rewrite Elog; reflexivity). rewrite ELOG. exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1). }
  split; [exact CREDp|]. split; [exact CLI'|]. split; [exact KN|]. split; [exact LZ'|exact EG'].
Qed.
End FinishP.
