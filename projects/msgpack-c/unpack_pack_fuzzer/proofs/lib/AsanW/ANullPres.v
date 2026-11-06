(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ADepot_iface ARep ARepFrame ALayout AHeapP AMalloc_iface AFrameD AEmbRep AEmbFrame ARecGeo
     ARefill_iface_x ARefillP_x AC6Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC. Context {rc : runConstT} {ov : annOV}.

Lemma munch_app : forall (W1 W2 : list ivl) (m1 m2 m3 : amem), munch W1 m1 m2 -> munch W2 m2 m3 -> munch (W1 ++ W2) m1 m3.
Proof. intros W1 W2 m1 m2 m3 H1 H2 x Hx. apply ARefillP.ARefillP.outside_app in Hx as [O1 O2]. rewrite (H2 x O2). exact (H1 x O1). Qed.
Definition nzl (W : list (Z * Z)) : list (Z * Z) := map (fun iv => nz (fst iv) (snd iv - fst iv)) W.
Lemma outside_nzl : forall W x, outside (nzl W) x -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; [exact I|]. cbn [nzl map fst snd] in H. apply outside_cons in H as [H1 H2].
  apply nz_outside in H1. cbn [outside]. split; [lia| exact (IH x H2)].
Qed.
Lemma munch_nzl : forall (W : list ivl) (m m' : amem), munch W m m' -> munch (nzl W) m m'.
Proof. intros W m m' MU x Hx. apply MU. apply outside_nzl. exact Hx. Qed.

Definition nf_kind (L : alayout) (RESV : list (Z * Z)) (st : astate) (SP c : Z) (iv : Z * Z) : Prop :=
     (ATOP <= fst iv /\ snd iv <= SP)
  \/ (al_t L + 208 <= fst iv /\ snd iv <= al_t L + 3169)
  \/ (aregion_info L c <= fst iv /\ snd iv <= aregion_info L c + 128)
  \/ (AEMB <= fst iv /\ snd iv <= AEMB + 56)
  \/ (snd iv <= ATOP /\ avoids_all (fst iv) (snd iv - fst iv) (RESV ++ flat_map sec_iv (achunks st)) = true)
  \/ (0x15bd20 <= fst iv /\ snd iv <= 0x15bd21)
  \/ (AERRNO <= fst iv /\ snd iv <= AERRNO + 4).

Definition nf_piece (L : alayout) (RESV : list (Z * Z)) (st : astate) (SP c : Z) (iv : Z * Z) : Prop :=
  fst iv < snd iv -> nf_kind L RESV st SP c iv.

Definition nf_pieceN (L : alayout) (RESV : list (Z * Z)) (st : astate) (SP c : Z) (iv : Z * Z) : Prop :=
  iv = (0, 0) \/ (fst iv < snd iv /\ nf_kind L RESV st SP c iv).
Lemma nzl_pieces : forall L RESV st SP c W, Forall (nf_piece L RESV st SP c) W -> Forall (nf_pieceN L RESV st SP c) (nzl W).
Proof.
  intros L RESV st SP c W H. unfold nzl. apply Forall_map. eapply Forall_impl; [| exact H]. intros [lo hi] K. cbn [fst snd] in *.
  unfold nz. destruct (0 <? hi - lo) eqn:Q; [| left; reflexivity]. apply Z.ltb_lt in Q. right.
  replace (lo + (hi - lo)) with hi by lia. cbn [fst snd]. split; [lia|]. apply K. cbn [fst snd]. lia.
Qed.
Lemma nf_piece_SP : forall L RESV st SP SP' c iv, SP <= SP' -> nf_piece L RESV st SP c iv -> nf_piece L RESV st SP' c iv.
Proof.
  intros L RESV st SP SP' c iv LE K LT. specialize (K LT). unfold nf_kind in *.
  destruct K as [[K1 K2]|K]; [left; split; [exact K1| lia]| right; exact K].
Qed.
Lemma nf_pieceN_piece : forall L RESV st SP c W, Forall (nf_pieceN L RESV st SP c) W -> Forall (nf_piece L RESV st SP c) W.
Proof. intros L RESV st SP c W H. eapply Forall_impl; [| exact H]. intros iv [->|[_ K]] LT; [cbn in LT; lia| exact K]. Qed.

Lemma dj_Forall : forall (W : list ivl) A k, Forall (fun iv => A + k <= fst iv \/ snd iv <= A) W -> disjoint_from W A k.
Proof. induction W as [|[lo hi] W IH]; intros A k H; cbn; [exact I|]. inversion H; subst. cbn [fst snd] in *. split; [assumption| apply IH; assumption]. Qed.

Definition nf_kindA (L : alayout) (RESV : list (Z * Z)) (st : astate) (SP c : Z) (iv : Z * Z) : Prop :=
  nf_kind L RESV st SP c iv /\ (snd iv <= AERRNO \/ AERRNO + 4 <= fst iv \/ (snd iv <= ATOP /\ avoids_all (fst iv) (snd iv - fst iv) RESV = true)).
Definition nf_pieceA (L : alayout) (RESV : list (Z * Z)) (st : astate) (SP c : Z) (iv : Z * Z) : Prop :=
  fst iv < snd iv -> nf_kindA L RESV st SP c iv.
Lemma nf_pieceA_SP : forall L RESV st SP SP' c iv, SP <= SP' -> nf_pieceA L RESV st SP c iv -> nf_pieceA L RESV st SP' c iv.
Proof.
  intros L RESV st SP SP' c iv LE K LT. destruct (K LT) as [K1 K2]. split; [| exact K2]. unfold nf_kind in *.
  destruct K1 as [[Q1 Q2]|Q]; [left; split; [exact Q1| lia]| right; exact Q].
Qed.
Lemma nf_pieceA_piece : forall L RESV st SP c W, Forall (nf_pieceA L RESV st SP c) W -> Forall (nf_piece L RESV st SP c) W.
Proof. intros L RESV st SP c W H. eapply Forall_impl; [| exact H]. intros iv K LT. exact (proj1 (K LT)). Qed.

Lemma avoids_out : forall d n (l : list (Z * Z)) lo hi x, avoids_all d n l = true -> In (lo, hi) l -> lo <= x < hi -> ~ (d <= x < d + n).
Proof.
  intros d n l lo hi x AV Hin Hx. unfold avoids_all in AV. rewrite forallb_forall in AV. specialize (AV _ Hin). unfold iv_clear in AV. cbn [fst snd] in AV.
  apply orb_prop in AV as [Q|Q]; apply Z.leb_le in Q; lia.
Qed.
Lemma avoids_pcov_out : forall RESV d n lo hi x, pcov RESV lo hi -> avoids_all d n RESV = true -> lo <= x < hi -> ~ (d <= x < d + n).
Proof. intros RESV d n lo hi x PC AV Hx. destruct (PC x Hx) as ([l h] & Hin & R). exact (avoids_out d n RESV l h x AV Hin R). Qed.

Section Geo.
Variables (L : alayout) (RESV : list (Z * Z)) (st : astate) (X : aconc) (SP c : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis ARV : aresv_ok L RESV.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis SPHI : ATOP <= SP.

Lemma ri_geo : forall c', 1 <= c' < K_NUM_CLASSES ->
  aregion_info L c' = al_space_beg L + 137438953472 + c' * 128
  /\ al_res L + 137438957568 <= aregion_info L c' /\ aregion_info L c' + 128 <= al_res L + 137439023104.
Proof.
  intros c' Hc. pose proof (ao_space L ALO) as SB.
  assert (E : aregion_info L c' = al_space_beg L + 137438953472 + c' * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  unfold K_NUM_CLASSES in Hc. split; [exact E|]. rewrite E. clear E. lia.
Qed.

Definition nf_loc (a : Z) : Prop :=
     SP <= a
  \/ (0x10000 <= a < AIMG_HI /\ ~ (AEMB <= a < AEMB + 56) /\ a <> 0x15bd20 /\ ~ (AERRNO <= a < AERRNO + 4))
  \/ (al_res L + 4096 <= a < al_space_beg L + 137438953472)
  \/ (exists p mb ms n, (a_live st) !! p = Some (CSec mb ms n) /\ sec_wf1 L (CSec mb ms n) /\ mb <= a < mb + ms)
  \/ (al_fake L <= a < al_fake L + 11571200)
  \/ (al_dtls L <= a < al_dtls L + 4096)
  \/ (0x7fff7000 <= a < 0x10007fff8000)
  \/ (al_t L <= a < al_t L + 208)
  \/ (exists c', 1 <= c' < K_NUM_CLASSES /\ c' <> c /\ aregion_info L c' <= a < aregion_info L c' + 128).

Lemma live_sec_chunk : forall p mb ms n, (a_live st) !! p = Some (CSec mb ms n) -> In (mb, mb + ms) (flat_map sec_iv (achunks st)).
Proof.
  intros p mb ms n LV. apply in_flat_map. exists (CSec mb ms n). split; [| left; reflexivity].
  unfold achunks. apply in_or_app. left. apply in_map_iff. exists (p, CSec mb ms n). split; [reflexivity|].
  apply list_elem_of_In. apply elem_of_map_to_list. exact LV.
Qed.

Lemma nf_kind_loc : forall iv a, nf_kind L RESV st SP c iv -> fst iv <= a < snd iv -> nf_loc a -> False.
Proof.
  intros [lo hi] a K IN LOC. unfold nf_kind in K. cbn [fst snd] in *. pose proof atop_range as ATR.
  pose proof (ao_t L ALO) as (_ & OT0 & OT1 & OTs & OTi). unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OTs, OTi.
  pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_space L ALO) as RSP.
  pose proof (ao_fake L ALO) as OF. pose proof (aobj_img _ _ OF ltac:(lia)) as OFi. destruct OF as (_ & _ & OF1 & _). unfold AIMG_HI in OFi.
  pose proof (ao_dtls L ALO) as (_ & OD0 & OD1 & _ & ODi). unfold iclr, AIMG_LO, AIMG_HI in ODi.
  pose proof (ad_t_res L ALO) as DTR. pose proof (ad_fake_res L ALO) as DFR. pose proof (ad_t_fake L ALO) as DTF.
  pose proof (ad_dtls_res L ALO) as DDR. pose proof (ad_t_dtls L ALO) as DTD. unfold adisj in DTR, DFR, DTF, DDR, DTD.
  destruct (ri_geo c HC) as (RIE & RI1 & RI2).
  destruct ARV as (PCI & PCSH & PCR & _ & PCT & _ & _ & _ & PCF & PCD & _). fold (al_res L) in PCR. fold (al_dtls L) in PCD.

  assert (BUF : forall l h, pcov RESV l h -> l <= a < h ->
            avoids_all lo (hi - lo) (RESV ++ flat_map sec_iv (achunks st)) = true -> False).
  { intros l h PC Ha AV. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
    apply (avoids_pcov_out RESV lo (hi - lo) l h a PC AV Ha). lia. }
  destruct LOC as [ST|[(I1 & I2 & I3 & I4)|[SLOT|[(p & mb & ms & n & LV & SW & R)|[FK|[DT|[SH|[TLO|(c' & Hc' & NE & R)]]]]]]]].
  -
    unfold AEMB, AERRNO, ATP in *. destruct K as [K|[K|[K|[K|[K|[K|K]]]]]]; lia.
  -
    unfold AIMG_HI, AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    exact (BUF 0x10000 0x62f000 PCI ltac:(lia) AV).
  -
    unfold AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    exact (BUF _ _ PCR ltac:(lia) AV).
  -
    cbn [sec_wf1] in SW. destruct SW as (_ & BK & TOP & _ & _ & _ & (Ct & _ & Cr & _)). unfold ablk, KLS, AIMG_HI in BK.
    unfold AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [_ AV].
    apply (avoids_out lo (hi - lo) _ mb (mb + ms) a AV (live_sec_chunk p mb ms n LV) R). lia.
  -
    unfold AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    exact (BUF _ _ PCF ltac:(lia) AV).
  -
    unfold AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    exact (BUF _ _ PCD ltac:(lia) AV).
  -
    unfold AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    exact (BUF _ _ PCSH ltac:(lia) AV).
  -
    unfold AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    exact (BUF _ _ PCT ltac:(lia) AV).
  -
    destruct (ri_geo c' Hc') as (RIE' & RI1' & RI2'). unfold K_NUM_CLASSES, AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    exact (BUF _ _ PCR ltac:(lia) AV).
Qed.

Lemma nf_outside : forall (W : list ivl) a, Forall (nf_piece L RESV st SP c) W -> nf_loc a -> outside W a.
Proof.
  intros W a PCS LOC. apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros iv K IN.
  exact (nf_kind_loc iv a (K ltac:(lia)) IN LOC).
Qed.

Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.

Hypothesis CI_OK3 : Forall (fun iv => (snd iv <= AEMB \/ AEMB + 56 <= fst iv) /\ (snd iv <= 0x15bd20 \/ 0x15bd21 <= fst iv)) CI.
Hypothesis WF : awf L st X.

Lemma nf_client_loc : forall LB a, ablocks L st X LB -> 0 <= a < 2 ^ 64 -> aclient_addr CI LB SP a -> ~ (AERRNO <= a < AERRNO + 4) -> nf_loc a.
Proof.
  intros LB a BL Ha CL NERR. unfold nf_loc.
  destruct CL as [STa | [CIa | [BLK | SH]]].
  - left. lia.
  - right; left. destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & _ & Q3).
    pose proof (proj1 (Forall_forall _ _) CI_OK3 iv Hiv) as (Q4 & Q5). split; [lia|]. split; [lia|]. split; [lia| exact NERR].
  - destruct BLK as (b & Hb & R). pose proof (lb_geo L st X LB b ALO WF BL Hb) as G.
    destruct b as [[p|cls] A n]; cbn [ab_kind ab_addr ab_size] in G, R.
    + destruct G as [(xb & Hxb & _ & G1 & G2)|(mb & ms & n' & LV & SW & G1 & G2)].
      * right; right; left. pose proof (busy_slot_geo L st X ALO WF xb Hxb) as (_ & _ & Q1 & Q2 & (Q3 & Q4 & Q5) & _ & _ & Q8 & _).
        unfold K_SPACE_SIZE, K_REGION, K_FREEARR_OFF in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *. lia.
      * right; right; right; left. exists p, mb, ms, n'. split; [exact LV|]. split; [exact SW|]. unfold SEC_UOFF in G1. lia.
    + do 4 right. left. lia.
  - do 6 right. left. destruct SH as (a' & Ha' & ->). rewrite shad_div. unfold ASHOFF.
    pose proof (ao_fake L ALO) as OF. pose proof (aobj_img _ _ OF ltac:(lia)) as OFi. destruct OF as (_ & _ & OF1 & _). unfold AIMG_HI in OFi.
    pose proof atop_range as ATR.
    assert (A' : 0x10000 <= a' < 2 ^ 47).
    { destruct Ha' as [STa | [CIa | FK]].
      - lia.
      - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & _ & Q3). unfold AIMG_HI in Q3. lia.
      - destruct FK as (cls & FA & sz & Hin & R). destruct BL as (_ & B2 & _). destruct (B2 cls FA sz Hin) as (F1 & F2 & F3). lia. }
    clear - A'. Z.div_mod_to_equations. lia.
Qed.

Theorem nf_client_outside : forall LB (W : list ivl) a, ablocks L st X LB -> Forall (nf_piece L RESV st SP c) W ->
  0 <= a < 2 ^ 64 -> aclient_addr CI LB SP a -> ~ (AERRNO <= a < AERRNO + 4) -> outside W a.
Proof. intros LB W a BL PCS Ha CL NERR. exact (nf_outside W a PCS (nf_client_loc LB a BL Ha CL NERR)). Qed.

Lemma nf_errno_outside : forall (W : list ivl) x, Forall (nf_pieceA L RESV st SP c) W -> AERRNO <= x < AERRNO + 4 -> outside W x.
Proof.
  intros W x PCS Hx. apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros [lo hi] K IN. cbn [fst snd] in *.
  destruct (K ltac:(cbn [fst snd]; lia)) as [_ [Q|[Q|[_ AV]]]]; cbn [fst snd] in *; [lia| lia|].
  destruct ARV as (PCI & _). apply (avoids_pcov_out RESV lo (hi - lo) 0x10000 AIMG_HI x PCI AV); unfold AIMG_HI, AERRNO, ATP in *; lia.
Qed.
Theorem nf_client_outsideA : forall LB (W : list ivl) a, ablocks L st X LB -> Forall (nf_pieceA L RESV st SP c) W ->
  0 <= a < 2 ^ 64 -> aclient_addr CI LB SP a -> outside W a.
Proof.
  intros LB W a BL PCS Ha CL. destruct (Z_lt_le_dec a AERRNO) as [LT|GE]; [| destruct (Z_lt_le_dec a (AERRNO + 4)) as [LT2|GE2]].
  - apply (nf_client_outside LB W a BL (nf_pieceA_piece _ _ _ _ _ _ PCS) Ha CL). lia.
  - apply (nf_errno_outside W a PCS). lia.
  - apply (nf_client_outside LB W a BL (nf_pieceA_piece _ _ _ _ _ _ PCS) Ha CL). lia.
Qed.

Lemma nf_flag_outside : forall (W : list ivl) c' x, Forall (nf_piece L RESV st SP c) W -> 1 <= c' < K_NUM_CLASSES -> c' <> c ->
  aregion_info L c' + 68 <= x < aregion_info L c' + 68 + 1 -> outside W x.
Proof.
  intros W c' x PCS Hc' NE Hx. apply (nf_outside W x PCS). unfold nf_loc. do 8 right. exists c'. split; [exact Hc'|]. split; [exact NE| lia].
Qed.
End Geo.

Lemma nf_fake : forall L RESV st SP c (W : list ivl), alayout_ok L -> aresv_ok L RESV -> 1 <= c < K_NUM_CLASSES -> ATOP <= SP ->
  Forall (nf_pieceN L RESV st SP c) W ->
  disjoint_from W (al_t L + 72) 8 /\ fake_untouched L W /\ Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W.
Proof.
  intros L RESV st SP c W ALO ARV HC SPHI PCS. pose proof atop_range as ATR.
  pose proof (ao_t L ALO) as (_ & OT0 & OT1 & OTs & OTi). unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OTs, OTi.
  pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_space L ALO) as RSP.
  pose proof (ao_fake L ALO) as OF. pose proof (aobj_img _ _ OF ltac:(lia)) as OFi. destruct OF as (_ & OF0 & OF1 & OFs & _). unfold AIMG_HI in OFi. unfold sclr, KLS in OFs.
  pose proof (ao_dtls L ALO) as (_ & OD0 & OD1 & _ & ODi). unfold iclr, AIMG_LO, AIMG_HI in ODi.
  pose proof (ad_t_res L ALO) as DTR. pose proof (ad_fake_res L ALO) as DFR. pose proof (ad_t_fake L ALO) as DTF.
  pose proof (ad_dtls_res L ALO) as DDR. pose proof (ad_t_dtls L ALO) as DTD. unfold adisj in DTR, DFR, DTF, DDR, DTD.
  destruct (ri_geo L ALO c HC) as (RIE & RI1 & RI2).
  assert (SHF : 0x7fff7000 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 0x10007fff8000 /\ 0 <= shad (al_fake L)).
  { rewrite shad_div, shlen_div. unfold ASHOFF. clear - OF0 OF1 ATR. Z.div_mod_to_equations. lia. }
  destruct SHF as (SF1 & SF2 & SF3).
  destruct ARV as (PCI & PCSH & PCR & _ & PCT & _ & _ & _ & PCF & PCD & _). fold (al_res L) in PCR. fold (al_dtls L) in PCD.
  assert (EACH : Forall (fun iv : Z * Z => ((al_t L + 72) + 8 <= fst iv \/ snd iv <= al_t L + 72)
             /\ ((snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
                 /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
                 /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
                 /\ (snd iv <= 0xd3358 \/ 0xd3358 + 8 <= fst iv)
                 /\ (snd iv <= 0x60cc78 \/ 0x60cc78 + 16 <= fst iv)
                 /\ (snd iv <= 0x60cc88 \/ 0x60cc88 + 8 <= fst iv)
                 /\ (snd iv <= 0x60cca8 \/ 0x60cca8 + 8 <= fst iv)
                 /\ (snd iv <= 0x16b671 \/ 0x16b671 + 1 <= fst iv)
                 /\ (snd iv <= 0x169558 \/ 0x169558 + 4 <= fst iv))
             /\ (snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv)) W).
  { eapply Forall_impl; [| exact PCS]. intros [lo hi] [E|[NEMP K]]; unfold nf_kind in *; cbn [fst snd] in *.
    - injection E as -> ->. repeat split; lia.
    - assert (BUFC : forall l h, pcov RESV l h -> l < h ->
                avoids_all lo (hi - lo) (RESV ++ flat_map sec_iv (achunks st)) = true -> hi <= l \/ h <= lo).
      { intros l h PC LH AV. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
        destruct (pcov_clear _ _ _ _ _ PC AV LH ltac:(lia)) as [Q|Q]; lia. }
      unfold AEMB, AERRNO, ATP in *.
      destruct K as [K|[K|[K|[K|[[TOP AV]|[K|K]]]]]].
      1-4,6-7: (repeat split; lia).
      pose proof (BUFC _ _ PCI ltac:(unfold AIMG_HI; lia) AV) as B1. unfold AIMG_HI in B1.
      pose proof (BUFC _ _ PCSH ltac:(lia) AV) as B2. pose proof (BUFC _ _ PCT ltac:(lia) AV) as B3.
      pose proof (BUFC _ _ PCF ltac:(lia) AV) as B4. pose proof (BUFC _ _ PCD ltac:(lia) AV) as B5.
      repeat split; lia. }
  split; [| split].
  - apply dj_Forall. eapply Forall_impl; [| exact EACH]. cbv beta. intros iv (Q & _). exact Q.
  - unfold fake_untouched. eapply Forall_impl; [| exact EACH]. cbv beta. intros iv (_ & Q & _). exact Q.
  - eapply Forall_impl; [| exact EACH]. cbv beta. intros iv (_ & _ & Q). exact Q.
Qed.

Lemma exh_mem_set_emb : forall c e s, exh_mem c (set_emb e s) = exh_mem c s.
Proof. intros c e s. destruct s. reflexivity. Qed.
End CANSEC.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ADepot_iface.TwinB ARep.TwinB ARepFrame.TwinB ALayout.TwinB AHeapP.TwinB AMalloc_iface.TwinB AFrameD.TwinB AEmbRep.TwinB AEmbFrame.TwinB ARecGeo.TwinB ARefill_iface_x.TwinB ARefillP_x.TwinB AC6Frame.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC. Context {rc : runConstT} {ov : annOV}.

Lemma munch_app : forall (W1 W2 : list ivl) (m1 m2 m3 : amem), munch W1 m1 m2 -> munch W2 m2 m3 -> munch (W1 ++ W2) m1 m3.
Proof. intros W1 W2 m1 m2 m3 H1 H2 x Hx. apply ARefillP.TwinB.ARefillP.outside_app in Hx as [O1 O2]. rewrite (H2 x O2). exact (H1 x O1). Qed.
Definition nzl (W : list (Z * Z)) : list (Z * Z) := map (fun iv => nz (fst iv) (snd iv - fst iv)) W.
Lemma outside_nzl : forall W x, outside (nzl W) x -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; [exact I|]. cbn [nzl map fst snd] in H. apply outside_cons in H as [H1 H2].
  apply nz_outside in H1. cbn [outside]. split; [lia| exact (IH x H2)].
Qed.
Lemma munch_nzl : forall (W : list ivl) (m m' : amem), munch W m m' -> munch (nzl W) m m'.
Proof. intros W m m' MU x Hx. apply MU. apply outside_nzl. exact Hx. Qed.

Definition nf_kind (L : alayout) (RESV : list (Z * Z)) (st : astate) (SP c : Z) (iv : Z * Z) : Prop :=
     (ATOP <= fst iv /\ snd iv <= SP)
  \/ (al_t L + 208 <= fst iv /\ snd iv <= al_t L + 3169)
  \/ (aregion_info L c <= fst iv /\ snd iv <= aregion_info L c + 128)
  \/ (AEMB <= fst iv /\ snd iv <= AEMB + 56)
  \/ (snd iv <= ATOP /\ avoids_all (fst iv) (snd iv - fst iv) (RESV ++ flat_map sec_iv (achunks st)) = true)
  \/ (0x15dee0 <= fst iv /\ snd iv <= 0x15dee1)
  \/ (AERRNO <= fst iv /\ snd iv <= AERRNO + 4).

Definition nf_piece (L : alayout) (RESV : list (Z * Z)) (st : astate) (SP c : Z) (iv : Z * Z) : Prop :=
  fst iv < snd iv -> nf_kind L RESV st SP c iv.

Definition nf_pieceN (L : alayout) (RESV : list (Z * Z)) (st : astate) (SP c : Z) (iv : Z * Z) : Prop :=
  iv = (0, 0) \/ (fst iv < snd iv /\ nf_kind L RESV st SP c iv).
Lemma nzl_pieces : forall L RESV st SP c W, Forall (nf_piece L RESV st SP c) W -> Forall (nf_pieceN L RESV st SP c) (nzl W).
Proof.
  intros L RESV st SP c W H. unfold nzl. apply Forall_map. eapply Forall_impl; [| exact H]. intros [lo hi] K. cbn [fst snd] in *.
  unfold nz. destruct (0 <? hi - lo) eqn:Q; [| left; reflexivity]. apply Z.ltb_lt in Q. right.
  replace (lo + (hi - lo)) with hi by lia. cbn [fst snd]. split; [lia|]. apply K. cbn [fst snd]. lia.
Qed.
Lemma nf_piece_SP : forall L RESV st SP SP' c iv, SP <= SP' -> nf_piece L RESV st SP c iv -> nf_piece L RESV st SP' c iv.
Proof.
  intros L RESV st SP SP' c iv LE K LT. specialize (K LT). unfold nf_kind in *.
  destruct K as [[K1 K2]|K]; [left; split; [exact K1| lia]| right; exact K].
Qed.
Lemma nf_pieceN_piece : forall L RESV st SP c W, Forall (nf_pieceN L RESV st SP c) W -> Forall (nf_piece L RESV st SP c) W.
Proof. intros L RESV st SP c W H. eapply Forall_impl; [| exact H]. intros iv [->|[_ K]] LT; [cbn in LT; lia| exact K]. Qed.

Lemma dj_Forall : forall (W : list ivl) A k, Forall (fun iv => A + k <= fst iv \/ snd iv <= A) W -> disjoint_from W A k.
Proof. induction W as [|[lo hi] W IH]; intros A k H; cbn; [exact I|]. inversion H; subst. cbn [fst snd] in *. split; [assumption| apply IH; assumption]. Qed.

Definition nf_kindA (L : alayout) (RESV : list (Z * Z)) (st : astate) (SP c : Z) (iv : Z * Z) : Prop :=
  nf_kind L RESV st SP c iv /\ (snd iv <= AERRNO \/ AERRNO + 4 <= fst iv \/ (snd iv <= ATOP /\ avoids_all (fst iv) (snd iv - fst iv) RESV = true)).
Definition nf_pieceA (L : alayout) (RESV : list (Z * Z)) (st : astate) (SP c : Z) (iv : Z * Z) : Prop :=
  fst iv < snd iv -> nf_kindA L RESV st SP c iv.
Lemma nf_pieceA_SP : forall L RESV st SP SP' c iv, SP <= SP' -> nf_pieceA L RESV st SP c iv -> nf_pieceA L RESV st SP' c iv.
Proof.
  intros L RESV st SP SP' c iv LE K LT. destruct (K LT) as [K1 K2]. split; [| exact K2]. unfold nf_kind in *.
  destruct K1 as [[Q1 Q2]|Q]; [left; split; [exact Q1| lia]| right; exact Q].
Qed.
Lemma nf_pieceA_piece : forall L RESV st SP c W, Forall (nf_pieceA L RESV st SP c) W -> Forall (nf_piece L RESV st SP c) W.
Proof. intros L RESV st SP c W H. eapply Forall_impl; [| exact H]. intros iv K LT. exact (proj1 (K LT)). Qed.

Lemma avoids_out : forall d n (l : list (Z * Z)) lo hi x, avoids_all d n l = true -> In (lo, hi) l -> lo <= x < hi -> ~ (d <= x < d + n).
Proof.
  intros d n l lo hi x AV Hin Hx. unfold avoids_all in AV. rewrite forallb_forall in AV. specialize (AV _ Hin). unfold iv_clear in AV. cbn [fst snd] in AV.
  apply orb_prop in AV as [Q|Q]; apply Z.leb_le in Q; lia.
Qed.
Lemma avoids_pcov_out : forall RESV d n lo hi x, pcov RESV lo hi -> avoids_all d n RESV = true -> lo <= x < hi -> ~ (d <= x < d + n).
Proof. intros RESV d n lo hi x PC AV Hx. destruct (PC x Hx) as ([l h] & Hin & R). exact (avoids_out d n RESV l h x AV Hin R). Qed.

Section Geo.
Variables (L : alayout) (RESV : list (Z * Z)) (st : astate) (X : aconc) (SP c : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis ARV : aresv_ok L RESV.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis SPHI : ATOP <= SP.

Lemma ri_geo : forall c', 1 <= c' < K_NUM_CLASSES ->
  aregion_info L c' = al_space_beg L + 137438953472 + c' * 128
  /\ al_res L + 137438957568 <= aregion_info L c' /\ aregion_info L c' + 128 <= al_res L + 137439023104.
Proof.
  intros c' Hc. pose proof (ao_space L ALO) as SB.
  assert (E : aregion_info L c' = al_space_beg L + 137438953472 + c' * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  unfold K_NUM_CLASSES in Hc. split; [exact E|]. rewrite E. clear E. lia.
Qed.

Definition nf_loc (a : Z) : Prop :=
     SP <= a
  \/ (0x10000 <= a < AIMG_HI /\ ~ (AEMB <= a < AEMB + 56) /\ a <> 0x15dee0 /\ ~ (AERRNO <= a < AERRNO + 4))
  \/ (al_res L + 4096 <= a < al_space_beg L + 137438953472)
  \/ (exists p mb ms n, (a_live st) !! p = Some (CSec mb ms n) /\ sec_wf1 L (CSec mb ms n) /\ mb <= a < mb + ms)
  \/ (al_fake L <= a < al_fake L + 11571200)
  \/ (al_dtls L <= a < al_dtls L + 4096)
  \/ (0x7fff7000 <= a < 0x10007fff8000)
  \/ (al_t L <= a < al_t L + 208)
  \/ (exists c', 1 <= c' < K_NUM_CLASSES /\ c' <> c /\ aregion_info L c' <= a < aregion_info L c' + 128).

Lemma live_sec_chunk : forall p mb ms n, (a_live st) !! p = Some (CSec mb ms n) -> In (mb, mb + ms) (flat_map sec_iv (achunks st)).
Proof.
  intros p mb ms n LV. apply in_flat_map. exists (CSec mb ms n). split; [| left; reflexivity].
  unfold achunks. apply in_or_app. left. apply in_map_iff. exists (p, CSec mb ms n). split; [reflexivity|].
  apply list_elem_of_In. apply elem_of_map_to_list. exact LV.
Qed.

Lemma nf_kind_loc : forall iv a, nf_kind L RESV st SP c iv -> fst iv <= a < snd iv -> nf_loc a -> False.
Proof.
  intros [lo hi] a K IN LOC. unfold nf_kind in K. cbn [fst snd] in *. pose proof atop_range as ATR.
  pose proof (ao_t L ALO) as (_ & OT0 & OT1 & OTs & OTi). unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OTs, OTi.
  pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_space L ALO) as RSP.
  pose proof (ao_fake L ALO) as OF. pose proof (aobj_img _ _ OF ltac:(lia)) as OFi. destruct OF as (_ & _ & OF1 & _). unfold AIMG_HI in OFi.
  pose proof (ao_dtls L ALO) as (_ & OD0 & OD1 & _ & ODi). unfold iclr, AIMG_LO, AIMG_HI in ODi.
  pose proof (ad_t_res L ALO) as DTR. pose proof (ad_fake_res L ALO) as DFR. pose proof (ad_t_fake L ALO) as DTF.
  pose proof (ad_dtls_res L ALO) as DDR. pose proof (ad_t_dtls L ALO) as DTD. unfold adisj in DTR, DFR, DTF, DDR, DTD.
  destruct (ri_geo c HC) as (RIE & RI1 & RI2).
  destruct ARV as (PCI & PCSH & PCR & _ & PCT & _ & _ & _ & PCF & PCD & _). fold (al_res L) in PCR. fold (al_dtls L) in PCD.

  assert (BUF : forall l h, pcov RESV l h -> l <= a < h ->
            avoids_all lo (hi - lo) (RESV ++ flat_map sec_iv (achunks st)) = true -> False).
  { intros l h PC Ha AV. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
    apply (avoids_pcov_out RESV lo (hi - lo) l h a PC AV Ha). lia. }
  destruct LOC as [ST|[(I1 & I2 & I3 & I4)|[SLOT|[(p & mb & ms & n & LV & SW & R)|[FK|[DT|[SH|[TLO|(c' & Hc' & NE & R)]]]]]]]].
  -
    unfold AEMB, AERRNO, ATP in *. destruct K as [K|[K|[K|[K|[K|[K|K]]]]]]; lia.
  -
    unfold AIMG_HI, AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    exact (BUF 0x10000 0x631000 PCI ltac:(lia) AV).
  -
    unfold AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    exact (BUF _ _ PCR ltac:(lia) AV).
  -
    cbn [sec_wf1] in SW. destruct SW as (_ & BK & TOP & _ & _ & _ & (Ct & _ & Cr & _)). unfold ablk, KLS, AIMG_HI in BK.
    unfold AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [_ AV].
    apply (avoids_out lo (hi - lo) _ mb (mb + ms) a AV (live_sec_chunk p mb ms n LV) R). lia.
  -
    unfold AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    exact (BUF _ _ PCF ltac:(lia) AV).
  -
    unfold AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    exact (BUF _ _ PCD ltac:(lia) AV).
  -
    unfold AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    exact (BUF _ _ PCSH ltac:(lia) AV).
  -
    unfold AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    exact (BUF _ _ PCT ltac:(lia) AV).
  -
    destruct (ri_geo c' Hc') as (RIE' & RI1' & RI2'). unfold K_NUM_CLASSES, AEMB, AERRNO, ATP in *.
    destruct K as [K|[K|[K|[K|[[_ AV]|[K|K]]]]]]; try lia.
    exact (BUF _ _ PCR ltac:(lia) AV).
Qed.

Lemma nf_outside : forall (W : list ivl) a, Forall (nf_piece L RESV st SP c) W -> nf_loc a -> outside W a.
Proof.
  intros W a PCS LOC. apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros iv K IN.
  exact (nf_kind_loc iv a (K ltac:(lia)) IN LOC).
Qed.

Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.

Hypothesis CI_OK3 : Forall (fun iv => (snd iv <= AEMB \/ AEMB + 56 <= fst iv) /\ (snd iv <= 0x15dee0 \/ 0x15dee1 <= fst iv)) CI.
Hypothesis WF : awf L st X.

Lemma nf_client_loc : forall LB a, ablocks L st X LB -> 0 <= a < 2 ^ 64 -> aclient_addr CI LB SP a -> ~ (AERRNO <= a < AERRNO + 4) -> nf_loc a.
Proof.
  intros LB a BL Ha CL NERR. unfold nf_loc.
  destruct CL as [STa | [CIa | [BLK | SH]]].
  - left. lia.
  - right; left. destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & _ & Q3).
    pose proof (proj1 (Forall_forall _ _) CI_OK3 iv Hiv) as (Q4 & Q5). split; [lia|]. split; [lia|]. split; [lia| exact NERR].
  - destruct BLK as (b & Hb & R). pose proof (lb_geo L st X LB b ALO WF BL Hb) as G.
    destruct b as [[p|cls] A n]; cbn [ab_kind ab_addr ab_size] in G, R.
    + destruct G as [(xb & Hxb & _ & G1 & G2)|(mb & ms & n' & LV & SW & G1 & G2)].
      * right; right; left. pose proof (busy_slot_geo L st X ALO WF xb Hxb) as (_ & _ & Q1 & Q2 & (Q3 & Q4 & Q5) & _ & _ & Q8 & _).
        unfold K_SPACE_SIZE, K_REGION, K_FREEARR_OFF in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *. lia.
      * right; right; right; left. exists p, mb, ms, n'. split; [exact LV|]. split; [exact SW|]. unfold SEC_UOFF in G1. lia.
    + do 4 right. left. lia.
  - do 6 right. left. destruct SH as (a' & Ha' & ->). rewrite shad_div. unfold ASHOFF.
    pose proof (ao_fake L ALO) as OF. pose proof (aobj_img _ _ OF ltac:(lia)) as OFi. destruct OF as (_ & _ & OF1 & _). unfold AIMG_HI in OFi.
    pose proof atop_range as ATR.
    assert (A' : 0x10000 <= a' < 2 ^ 47).
    { destruct Ha' as [STa | [CIa | FK]].
      - lia.
      - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & _ & Q3). unfold AIMG_HI in Q3. lia.
      - destruct FK as (cls & FA & sz & Hin & R). destruct BL as (_ & B2 & _). destruct (B2 cls FA sz Hin) as (F1 & F2 & F3). lia. }
    clear - A'. Z.div_mod_to_equations. lia.
Qed.

Theorem nf_client_outside : forall LB (W : list ivl) a, ablocks L st X LB -> Forall (nf_piece L RESV st SP c) W ->
  0 <= a < 2 ^ 64 -> aclient_addr CI LB SP a -> ~ (AERRNO <= a < AERRNO + 4) -> outside W a.
Proof. intros LB W a BL PCS Ha CL NERR. exact (nf_outside W a PCS (nf_client_loc LB a BL Ha CL NERR)). Qed.

Lemma nf_errno_outside : forall (W : list ivl) x, Forall (nf_pieceA L RESV st SP c) W -> AERRNO <= x < AERRNO + 4 -> outside W x.
Proof.
  intros W x PCS Hx. apply outside_Forall. eapply Forall_impl; [| exact PCS]. intros [lo hi] K IN. cbn [fst snd] in *.
  destruct (K ltac:(cbn [fst snd]; lia)) as [_ [Q|[Q|[_ AV]]]]; cbn [fst snd] in *; [lia| lia|].
  destruct ARV as (PCI & _). apply (avoids_pcov_out RESV lo (hi - lo) 0x10000 AIMG_HI x PCI AV); unfold AIMG_HI, AERRNO, ATP in *; lia.
Qed.
Theorem nf_client_outsideA : forall LB (W : list ivl) a, ablocks L st X LB -> Forall (nf_pieceA L RESV st SP c) W ->
  0 <= a < 2 ^ 64 -> aclient_addr CI LB SP a -> outside W a.
Proof.
  intros LB W a BL PCS Ha CL. destruct (Z_lt_le_dec a AERRNO) as [LT|GE]; [| destruct (Z_lt_le_dec a (AERRNO + 4)) as [LT2|GE2]].
  - apply (nf_client_outside LB W a BL (nf_pieceA_piece _ _ _ _ _ _ PCS) Ha CL). lia.
  - apply (nf_errno_outside W a PCS). lia.
  - apply (nf_client_outside LB W a BL (nf_pieceA_piece _ _ _ _ _ _ PCS) Ha CL). lia.
Qed.

Lemma nf_flag_outside : forall (W : list ivl) c' x, Forall (nf_piece L RESV st SP c) W -> 1 <= c' < K_NUM_CLASSES -> c' <> c ->
  aregion_info L c' + 68 <= x < aregion_info L c' + 68 + 1 -> outside W x.
Proof.
  intros W c' x PCS Hc' NE Hx. apply (nf_outside W x PCS). unfold nf_loc. do 8 right. exists c'. split; [exact Hc'|]. split; [exact NE| lia].
Qed.
End Geo.

Lemma nf_fake : forall L RESV st SP c (W : list ivl), alayout_ok L -> aresv_ok L RESV -> 1 <= c < K_NUM_CLASSES -> ATOP <= SP ->
  Forall (nf_pieceN L RESV st SP c) W ->
  disjoint_from W (al_t L + 72) 8 /\ fake_untouched L W /\ Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W.
Proof.
  intros L RESV st SP c W ALO ARV HC SPHI PCS. pose proof atop_range as ATR.
  pose proof (ao_t L ALO) as (_ & OT0 & OT1 & OTs & OTi). unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OTs, OTi.
  pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_space L ALO) as RSP.
  pose proof (ao_fake L ALO) as OF. pose proof (aobj_img _ _ OF ltac:(lia)) as OFi. destruct OF as (_ & OF0 & OF1 & OFs & _). unfold AIMG_HI in OFi. unfold sclr, KLS in OFs.
  pose proof (ao_dtls L ALO) as (_ & OD0 & OD1 & _ & ODi). unfold iclr, AIMG_LO, AIMG_HI in ODi.
  pose proof (ad_t_res L ALO) as DTR. pose proof (ad_fake_res L ALO) as DFR. pose proof (ad_t_fake L ALO) as DTF.
  pose proof (ad_dtls_res L ALO) as DDR. pose proof (ad_t_dtls L ALO) as DTD. unfold adisj in DTR, DFR, DTF, DDR, DTD.
  destruct (ri_geo L ALO c HC) as (RIE & RI1 & RI2).
  assert (SHF : 0x7fff7000 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 0x10007fff8000 /\ 0 <= shad (al_fake L)).
  { rewrite shad_div, shlen_div. unfold ASHOFF. clear - OF0 OF1 ATR. Z.div_mod_to_equations. lia. }
  destruct SHF as (SF1 & SF2 & SF3).
  destruct ARV as (PCI & PCSH & PCR & _ & PCT & _ & _ & _ & PCF & PCD & _). fold (al_res L) in PCR. fold (al_dtls L) in PCD.
  assert (EACH : Forall (fun iv : Z * Z => ((al_t L + 72) + 8 <= fst iv \/ snd iv <= al_t L + 72)
             /\ ((snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
                 /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
                 /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
                 /\ (snd iv <= 0xd5470 \/ 0xd5470 + 8 <= fst iv)
                 /\ (snd iv <= 0x60ee38 \/ 0x60ee38 + 16 <= fst iv)
                 /\ (snd iv <= 0x60ee48 \/ 0x60ee48 + 8 <= fst iv)
                 /\ (snd iv <= 0x60ee68 \/ 0x60ee68 + 8 <= fst iv)
                 /\ (snd iv <= 0x16d831 \/ 0x16d831 + 1 <= fst iv)
                 /\ (snd iv <= 0x16b718 \/ 0x16b718 + 4 <= fst iv))
             /\ (snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv)) W).
  { eapply Forall_impl; [| exact PCS]. intros [lo hi] [E|[NEMP K]]; unfold nf_kind in *; cbn [fst snd] in *.
    - injection E as -> ->. repeat split; lia.
    - assert (BUFC : forall l h, pcov RESV l h -> l < h ->
                avoids_all lo (hi - lo) (RESV ++ flat_map sec_iv (achunks st)) = true -> hi <= l \/ h <= lo).
      { intros l h PC LH AV. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
        destruct (pcov_clear _ _ _ _ _ PC AV LH ltac:(lia)) as [Q|Q]; lia. }
      unfold AEMB, AERRNO, ATP in *.
      destruct K as [K|[K|[K|[K|[[TOP AV]|[K|K]]]]]].
      1-4,6-7: (repeat split; lia).
      pose proof (BUFC _ _ PCI ltac:(unfold AIMG_HI; lia) AV) as B1. unfold AIMG_HI in B1.
      pose proof (BUFC _ _ PCSH ltac:(lia) AV) as B2. pose proof (BUFC _ _ PCT ltac:(lia) AV) as B3.
      pose proof (BUFC _ _ PCF ltac:(lia) AV) as B4. pose proof (BUFC _ _ PCD ltac:(lia) AV) as B5.
      repeat split; lia. }
  split; [| split].
  - apply dj_Forall. eapply Forall_impl; [| exact EACH]. cbv beta. intros iv (Q & _). exact Q.
  - unfold fake_untouched. eapply Forall_impl; [| exact EACH]. cbv beta. intros iv (_ & Q & _). exact Q.
  - eapply Forall_impl; [| exact EACH]. cbv beta. intros iv (_ & _ & Q). exact Q.
Qed.

Lemma exh_mem_set_emb : forall c e s, exh_mem c (set_emb e s) = exh_mem c s.
Proof. intros c e s. destruct s. reflexivity. Qed.
End CANSEC.
End TwinB.
