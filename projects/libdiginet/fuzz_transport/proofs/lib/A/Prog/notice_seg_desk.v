(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v for libreac/fuzz_grant's program walk: the listing's names are gsym, PALib names fuzz_grant.asan's objects and the wrappers' 4-byte jumps, and fuzz_grant's image bound; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: taken by path from libreac/fuzz_grant's copy (proofs/libreac/fuzz_grant/lib/A/Prog/GrantPaLib.v, file sha256 1750b9b228be; donor not released) for libreac/fuzz_decode's
   program walk: module paths and the listing's names changed. *)
(* Modified by Theorem Labs, 2026-10: image B's twin of this unit's lib/A/Prog/DecodePaLib.v, in the shape of proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBPaLib.v (file sha256 73c9e12166f6; donor not released): the names are dbsym's (the wrappers' free and malloc entries are DB___interceptor_trampoline_free and DB___interceptor_trampoline_malloc); PALib names fuzz_decode.asan-ubsan's objects of lib/B/Prog/DecodeBAddr.v and lib/B/AsanCells.v: the shadow-base GOT word is object 1 (GOT_CELL_K 0x992e8) and its cell object 14 (CELL_K 0xa1338), the side-stack flag's GOT word object 0 (GOT_UAR 0x99340) and its cell object 15 (UAR 0xa1340); the two cells are one object later than image A's 13 and 14 because image B's slots load one more object (object 13, 0x103c8); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/DgnTransportBPaLib.v; 9 of its 34 lines of code are new or changed and 475 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/TransportGRunB.v, with its module paths and module names changed; 398 of its 427 lines of code are new or changed and 5 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/notice_seg_lib.v, with its module paths and module names changed; 367 of its 442 lines of code are new or changed and 352 lines of the source are left out. *)
(* notice_seg_desk: the arm of notice for a notice of kind N_DESK (0x835c8; DgnTransportList.v lines 2345-2352),
   which counts the notice and tail-jumps to check_state_desk:
     +0x50 .. +0x58  a2 = (s32) GOT.desk, a2 = a2 + 1 (a0 the auipc value of the field, A_HI 72);
     +0x5c           `sw a2, -536(a0)` with a0 pinned to the field's object A_OBJ 36, so the store lands in its region;
     +0x60 .. +0x6c  a0 = p, ra restored, sp + 16, and the tail jump to check_state_desk (0x8538c) from notice's entry
                     sp and ra.
   The world after the store is set_GOT_desk Bw (GOT_desk Bw + 1), the world check_state_desk_m reads in notice_m's
   N_DESK case (nt_m_desk). check_state_desk is a donor-form callee, lifted by TransportGCg.v gx_call_cg; it gets the
   notice with its announce cut to 10 + 10 bytes (nt_cut, nt_desk_cut), the bytes notice_apart keeps apart from
   GOT.desk. Its post becomes notice's (ntd_tail_post): the same sp (CSDESK_STK = NOTICE_STK), no event
   (CSDESK_EV = NOTICE_EV = 0), its written range empty, the walk's own changed bytes (its window and GOT.desk) the
   written range notice_wr, and the world kept across the callee (gx_kept). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_data_cg check_state_desk_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import notice_seg_base notice_seg_lib notice_seg_disp.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The written bytes, values                                           *)
(* ------------------------------------------------------------------ *)

(* The bytes a notice of kind N_DESK writes: GOT.desk's four. *)
Lemma ntd_wr_desk : forall Bw n a, TI.n_kind n = TC.N_DESK -> notice_wr Bw n a ->
  TA_GOT + 208 <= a < TA_GOT + 212.
Proof.
  intros Bw n a Hk Hw.
  unfold notice_wr, TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in Hk, Hw.
  unfold twa_fld, TW.A_GOT_desk, TW.OFF_GOT in Hw.
  destruct Hw as [(E & _) | [(E & _) | [(E & _) | [(E & Ha) | [(E & _) | (E & _)]]]]]; try lia.
Qed.

Lemma ntd_le_byte_small : forall v (m j : nat), 0 <= YO0f.le_byte v m j < 256.
Proof. intros v m j. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

Lemma ntd_mod_64_32 : forall v, bv_unsigned (Z_to_bv 64 v) mod 2 ^ 32 = v mod 2 ^ 32.
Proof.
  intros v. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity.
Qed.

Lemma ntd_le_byte_mod32 : forall v (j : nat), YO0f.le_byte (v mod 2 ^ 32) 4 j = YO0f.le_byte v 4 j.
Proof.
  intros v j. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* The first k bytes of an array are an array. *)
Lemma ntd_garr8_firstn : forall (mm : word -> option byte) q (l : list byte) k,
  garr8 tfibsegs mm q (map DSpec.bz l) -> garr8 tfibsegs mm q (map DSpec.bz (firstn k l)).
Proof.
  intros mm q l k H. rewrite <- (firstn_skipn k l) in H. rewrite map_app in H.
  apply garr8_app in H. exact (proj1 H).
Qed.

(* ------------------------------------------------------------------ *)
(* The callee's premises, carried from the entry memory to the jump's  *)
(* ------------------------------------------------------------------ *)

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

(* A range a callee reads: placed by trans_src_ok, outside the walk's window, apart from notice_wr: kept. *)
Lemma ntd_view_rng : forall lyc Sc (W : world segs) memc mdc m regs Bw n q len,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  nt_KA W memc m (nt_Zs regs Bw n) ->
  trans_src_ok B lyc Sc W memc q len -> decode_off_win regs NOTICE_STK q len ->
  (forall x, q <= x < q + len -> ~ notice_wr Bw n x) ->
  forall a, q <= a < q + len -> aview segs (w_H W) m a = aview segs (w_H W) memc a.
Proof.
  intros lyc Sc W memc mdc m regs Bw n q len LAWS HAR [K _] Hs Hoff Hnw a Ha.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hl : 0 < len) by lia.
  destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc q len HAR Hs Hl) as [Hp | Hp];
    (apply K; [ lia
              | intros [Hz | Hz]; [unfold decode_off_win in Hoff; lia | exact (Hnw a Ha Hz)] ]).
Qed.

(* The shadow band is kept: the walk's window is above it, GOT and M below. *)
Lemma ntd_view_sh : forall (W : world segs) memc m regs Bw n,
  alloc_ceiling <= spZ regs - NOTICE_STK -> nt_KA W memc m (nt_Zs regs Bw n) ->
  forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W) m s = aview segs (w_H W) memc s.
Proof.
  intros W memc m regs Bw n Hce [K _] s Hs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply K; [lia|]. intros Hz.
  destruct (nt_Zs_far regs Bw n s Hce Hz) as [H|H]; unfold TA_M, TA_GOT in H; lia.
Qed.

Lemma ntd_src_keep : forall lyc Sc (W : world segs) memc mdc m regs Bw n q len,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc -> alloc_ceiling <= spZ regs - NOTICE_STK ->
  nt_KA W memc m (nt_Zs regs Bw n) ->
  trans_src_ok B lyc Sc W memc q len -> decode_off_win regs NOTICE_STK q len ->
  (forall x, q <= x < q + len -> ~ notice_wr Bw n x) ->
  trans_src_ok B lyc Sc W m q len.
Proof.
  intros lyc Sc W memc mdc m regs Bw n q len LAWS HAR Hce KA Hs Hoff Hnw.
  exact (trans_src_ok_view B lyc Sc W W memc m q len Hs
    (ntd_view_rng lyc Sc W memc mdc m regs Bw n q len LAWS HAR KA Hs Hoff Hnw)
    (ntd_view_sh W memc m regs Bw n Hce KA)).
Qed.

Lemma ntd_garr8 : forall (W : world segs) memc m q l,
  garr8 segs (mrestrict (w_H W) memc) q l ->
  (forall a, q <= a < q + Z.of_nat (length l) -> aview segs (w_H W) m a = aview segs (w_H W) memc a) ->
  garr8 segs (mrestrict (w_H W) m) q l.
Proof.
  intros W memc m q l HG HV. apply (garr8_frame segs (mrestrict (w_H W) memc) (mrestrict (w_H W) m) q l HG).
  intros a Ha. apply (mbyte_of_aview segs). exact (HV a Ha).
Qed.

Lemma ntd_off : forall regs regsT q len, spZ regsT = spZ regs ->
  decode_off_win regs NOTICE_STK q len -> decode_off_win regsT CSDESK_STK q len.
Proof.
  intros regs regsT q len Hsp H. assert (FC : CSDESK_STK = NOTICE_STK) by reflexivity.
  unfold decode_off_win in *. rewrite Hsp, FC. exact H.
Qed.

(* The notice check_state_desk gets: n with its announce cut to 10 + 10 bytes, at the jump's memory and sp. *)
Lemma ntd_ntc_keep : forall lyc Sc (W : world segs) memc mdc m regs regsT Bw n Fr p,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= spZ regs - NOTICE_STK -> spZ regsT = spZ regs ->
  nt_KA W memc m (nt_Zs regs Bw n) ->
  notice_apart W memc p n Fr Bw ->
  trans_ntc_at B lyc Sc W memc regs NOTICE_STK p n ->
  trans_ntc_at B lyc Sc W m regsT CSDESK_STK p (nt_cut n).
Proof.
  intros lyc Sc W memc mdc m regs regsT Bw n Fr p LAWS HAR Hce Hsp KA HAP HNT.
  destruct HNT as (P0 & P8 & Hsrc & Hoff & NB2 & HNB2 & HL2 & HK0 & HK4 & HK8 & HK12 & HKp & HKm & HKb & HK64
    & HK68 & HBg & HBs & HBo & HA).
  assert (AP1 : forall x, p <= x < p + NTC_SIZE -> ~ notice_wr Bw n x)
    by (intros x Hx Hw; exact (proj1 (HAP x Hw) Hx)).
  assert (AP2 : forall x, TW.u_at NB2 48 8 <= x < TW.u_at NB2 48 8 + Z.of_nat (length (TI.n_body n)) ->
    ~ notice_wr Bw n x)
    by (intros x Hx Hw; exact (proj1 (proj1 (proj2 (HAP x Hw)) NB2 HNB2 HL2) Hx)).
  pose proof (ntd_view_rng lyc Sc W memc mdc m regs Bw n p NTC_SIZE LAWS HAR KA Hsrc Hoff AP1) as V1.
  pose proof (ntd_view_rng lyc Sc W memc mdc m regs Bw n _ _ LAWS HAR KA HBs HBo AP2) as V2.
  unfold trans_ntc_at.
  split; [exact P0|]. split; [exact P8|].
  split; [exact (ntd_src_keep lyc Sc W memc mdc m regs Bw n p NTC_SIZE LAWS HAR Hce KA Hsrc Hoff AP1)|].
  split; [exact (ntd_off regs regsT p NTC_SIZE Hsp Hoff)|].
  exists NB2.
  split.
  { apply (ntd_garr8 W memc m p _ HNB2). intros a Ha. apply V1.
    rewrite length_map, HL2 in Ha. unfold NTC_SIZE. lia. }
  split; [exact HL2|].
  unfold nt_cut.
  cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_counter TI.n_retry TI.n_mac_offset TI.n_pers TI.n_ann
    TI.n_body TI.n_body_len].
  split; [exact HK0|]. split; [exact HK4|]. split; [exact HK8|]. split; [exact HK12|].
  split; [exact HKp|]. split; [exact HKm|]. split; [exact HKb|]. split; [exact HK64|]. split; [exact HK68|].
  split.
  { apply (ntd_garr8 W memc m _ _ HBg). intros a Ha. apply V2. rewrite length_map in Ha. exact Ha. }
  split; [exact (ntd_src_keep lyc Sc W memc mdc m regs Bw n _ _ LAWS HAR Hce KA HBs HBo AP2)|].
  split; [exact (ntd_off regs regsT _ _ Hsp HBo)|].
  assert (AP3 : TI.n_ann n <> None -> forall x, TW.u_at NB2 24 8 <= x < TW.u_at NB2 24 8 + ANN_SIZE ->
    ~ notice_wr Bw n x)
    by (intros Hn x Hx Hw; exact (proj2 (proj1 (proj2 (HAP x Hw)) NB2 HNB2 HL2) Hn Hx)).
  revert HA AP3. destruct (TI.n_ann n) as [an|]; cbn [option_map]; intros HA AP3; [|exact HA].
  destruct HA as (A0 & A8 & HAv & HAn & HAs & HAo).
  specialize (AP3 ltac:(discriminate)).
  pose proof (ntd_view_rng lyc Sc W memc mdc m regs Bw n _ _ LAWS HAR KA HAs HAo AP3) as V3.
  unfold nt_ann_cut. cbn [TI.ta_version TI.ta_name].
  split; [exact A0|]. split; [exact A8|].
  split.
  { apply (ntd_garr8 W memc m _ _ (ntd_garr8_firstn _ _ _ 10 HAv)). intros a Ha. apply V3.
    rewrite length_map, length_firstn in Ha. unfold ANN_SIZE. lia. }
  split.
  { apply (ntd_garr8 W memc m _ _ (ntd_garr8_firstn _ _ _ 10 HAn)). intros a Ha. apply V3.
    rewrite length_map, length_firstn in Ha. unfold ANN_SIZE. lia. }
  split; [exact (ntd_src_keep lyc Sc W memc mdc m regs Bw n _ _ LAWS HAR Hce KA HAs HAo AP3)|].
  exact (ntd_off regs regsT _ _ Hsp HAo).
Qed.

(* The current frame at the jump's memory and sp. *)
Lemma ntd_tf_keep : forall lyc Sc (W : world segs) memc mdc m regs regsT Bw n p Fr,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= spZ regs - NOTICE_STK -> spZ regsT = spZ regs ->
  nt_KA W memc m (nt_Zs regs Bw n) ->
  notice_apart W memc p n Fr Bw ->
  trans_tframe_at B lyc Sc W memc regs NOTICE_STK Fr ->
  trans_tframe_at B lyc Sc W m regsT CSDESK_STK Fr.
Proof.
  intros lyc Sc W memc mdc m regs regsT Bw n p Fr LAWS HAR Hce Hsp KA HAP HTF.
  destruct Fr as [fr|]; [|exact I].
  destruct HTF as (A0 & Hg & Hs & Ho).
  assert (AP : forall x, TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) ->
    ~ notice_wr Bw n x)
    by (intros x Hx Hw; exact (proj2 (proj2 (HAP x Hw)) fr eq_refl Hx)).
  pose proof (ntd_view_rng lyc Sc W memc mdc m regs Bw n _ _ LAWS HAR KA Hs Ho AP) as V.
  split; [exact A0|].
  split.
  { apply (ntd_garr8 W memc m _ _ Hg). intros a Ha. apply V. rewrite length_map in Ha. exact Ha. }
  split; [exact (ntd_src_keep lyc Sc W memc mdc m regs Bw n _ _ LAWS HAR Hce KA Hs Ho AP)|].
  exact (ntd_off regs regsT _ _ Hsp Ho).
Qed.

(* The read-only bytes of the image are kept: each lies below 0xa4000. *)
Lemma ntd_ro_keep : forall (W : world segs) memc m regs Bw n,
  alloc_ceiling <= spZ regs - NOTICE_STK -> nt_KA W memc m (nt_Zs regs Bw n) ->
  trans_rom_view_rd W memc -> trans_rom_view_rd W m.
Proof.
  intros W memc m regs Bw n Hce [KA _] HRO a Ha.
  pose proof (trans_ro_rd_bounds a Ha) as Hb.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite (KA a ltac:(lia)); [exact (HRO a Ha)|].
  intros Hz. destruct (nt_Zs_far regs Bw n a Hce Hz) as [H|H]; unfold TA_M, TA_GOT in H; lia.
Qed.

(* The post at the tail jump: check_state_desk's post (lifted by gx_call_cg), entered with notice's ra, sp and
   callee-saved registers on the same journal, at the memory after GOT.desk++, is notice's. *)
Lemma ntd_tail_post : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs n Bw Bw' Bw1
    memT regsT,
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS -> @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - NOTICE_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - NOTICE_STK -> 2 ^ 46 <= spZ regs <= 2 ^ 47 ->
  nt_KA W memc memT (nt_Zs regs Bw n) ->
  aregs_preserved regs regsT -> YK11.getr regsT 1 = YK11.getr regs 1 -> spZ regsT = spZ regs ->
  tw_at TMAP_A (aview segs (w_H W) memT) Bw1 ->
  forall W2 c2,
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT k
    regsT CSDESK_STK CSDESK_EV 0 (fun _ => False)
    (fun regs2 W2 mem2 => (fun _ _ _ => Bw' = Bw1) regs2 W2 mem2 /\ gx_kept segs TG.G_HARNESS W memT W2 mem2)
    W2 c2 ->
  @transport_notice_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n Bw Bw' W2 c2.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs n Bw Bw' Bw1 memT regsT
    LAWS HGX HAR Hwin Hce Hsp KAT HP R1 Hspt HtwT W2 c2 HQ.
  pose proof KAT as [KA GA].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : NOTICE_STK = 8240) by reflexivity.
  assert (FC : CSDESK_STK = NOTICE_STK) by reflexivity.
  assert (GLOW : forall a, inG TG.G_HARNESS a -> a < kLowMemEnd).
  { intros a Ha. exact (proj2 (transport_segs_low a (proj1 (HGX a Ha)))). }
  unfold transport_cg_post in HQ.
  destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e & Hc & He & HJ2 & HP2 & Hfr & Hperm & HK & HMO & HX & HGK).
  unfold transport_notice_post, transport_cg_post.
  exists ly2, S2, regs2, mem2, md2, e.
  split; [rewrite Hc, R1; reflexivity|].
  split; [unfold CSDESK_EV in He; unfold NOTICE_EV; lia|].
  split; [exact HJ2|].
  split; [exact (aregs_preserved_trans regs regsT regs2 HP HP2)|].
  split; [exact Hfr|].
  split; [exact Hperm|].
  split.
  { rewrite Hspt, FC in HK.
    eapply dk_kept_trans_g with (W1 := W) (memX := memT) (slo' := spZ regs - NOTICE_STK) (shi' := spZ regs)
      (Eo' := fun _ => False).
    - exact Hce.
    - lia.
    - apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc memT
        (spZ regs - NOTICE_STK) (spZ regs) (notice_wr Bw n) (nt_Zs regs Bw n) HAR).
      + apply dk_kept_refl_g. exact Hwin.
      + exact KA.
      + exact GA.
      + intros a [Hw | Hw] Hc'; [exact Hw|]. exfalso. pose proof (GLOW a (nt_wr_G _ _ _ Hw)). unfold kLowMemEnd in *. lia.
      + intros b m i Hb Hi [Hw | Hw]; [|exact Hw]. exfalso.
        destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
      + intros a [Hw | Hw] Hi HnG _ _.
        * pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
        * exact (HnG (nt_wr_G _ _ _ Hw)).
      + intros cid pos a Hin Hr [Hw | Hw]; [|exact Hw]. exfalso.
        destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
        pose proof (fs_frame_bytes_nonneg cid) as Hfs.
        destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
        pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
        assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
        unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
    - exact HK.
    - lia.
    - lia.
    - intros a []. }
  split; [exact HMO|].
  cbv beta in HX. rewrite HX.
  apply (tw_kept_GA (aview segs (w_H W) memT) (aview segs (w_H W2) mem2) Bw1 HtwT).
  intros b0 n0 i Hin Hi. exact (gx_kept_rows segs TG.G_HARNESS W memT W2 mem2 HGK b0 n0 i Hin Hi).
Qed.
End k.

(* ------------------------------------------------------------------ *)
(* The arm                                                              *)
(* ------------------------------------------------------------------ *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma nt_path_desk : @nt_path fx rc B MT TC.N_DESK NT_DESK.
Proof.
unfold nt_path.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E ms md
  HC Ek HS HEI HElo HEd SHOK HJ KA.
destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
  as (HAR & Hwin & Hsp & Hce & Hm16 & Hp4096 & Hp47 & Hp8 & Hoffp & Hrd).
pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJ0 Hra Hra4 Hgp Htp H11 Hsp16
  Hlo Hhi HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : NOTICE_STK = 8240) by reflexivity.
destruct (nt_m_desk timg_A Fr Bw n Bw' Ek Hm) as [Hmax Hcs].
(* the valuation at the arm *)
pose proof (nt_E_atom regs NB Bw 6%nat ltac:(lia)) as E38q. cbn [Nat.add nth nt_vals] in E38q.
assert (E38 : ew E 38 = Z_to_bv 64 (TW.u_at Bw TW.A_GOT_desk 4)) by (rewrite (HElo 38%nat ltac:(lia)); exact E38q).
assert (U36 : bv_unsigned (ew E (A_OBJ 36)) = TA_GOT + 208)
  by (rewrite (HEI (A_OBJ 36) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); vm_compute; reflexivity).
assert (U36n : bv_unsigned (ew E 277%nat) = TA_GOT + 208) by exact U36.
pose proof (nt_KA_mono W memc (ms_mem ms) (nt_Wn regs) (nt_Zs regs Bw n)
  (fun a Ha => nt_Wn_Zs regs Bw n a Ha) KA) as KA0.
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (HElo 2%nat ltac:(lia)); rewrite (nt_E_reg regs NB Bw 2%nat 2%bv eq_refl); reflexivity).
pose proof (nt_E_atom regs NB Bw 0%nat ltac:(lia)) as E32q. cbn [Nat.add nth nt_vals] in E32q.
assert (E32e : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (HElo 32%nat ltac:(lia)); exact E32q).
assert (U11e : bv_unsigned (ew E 11) = p).
{ rewrite (HElo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11%nat 11%bv eq_refl), H11.
  apply unsigned_lit_small. lia. }
assert (HtwM : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) Bw).
{ apply (nt_tw_keep W memc (ms_mem ms) Bw (nt_Wn regs) Htw KA).
  intros x Hx Hz. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia. }
(* GOT.desk's region added *)
pose proof (nt_add E _ _ (nt_reg_fld 36 38) HS ltac:(vm_compute; reflexivity)) as HSq. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq.
specialize (HSq ltac:(cbn [ms_mem restrict]; apply (nt_fld_ok W _ E Bw 36%nat 38%nat 208);
  [exact U36 | lia | unfold TW.SZ_GOT; lia | exact E38 | exact HtwM])).
specialize (HSq ltac:(cbn [all_disjoint]; split; [|exact I];
  unfold extent_disjoint, nt_reg_fld, nt_reg_frame;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold TA_GOT in U36; lia)).
rename HSq into HS.
pose proof (nt_facts_set E _ _ (nt_facts_f 277%nat (TA_GOT + 208)) HS
  ltac:(apply (nt_facts_f_ok E (spZ regs) p 277%nat (TA_GOT + 208));
        first [exact Usp | exact U11e | exact E32e | exact U36n | lia])) as HSq.
clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
(* run 1: the load of GOT.desk and the increment; the store needs its auipc pinned *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ nt_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (md1 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md1; clear mt end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
  assert (KA1 : nt_KA W memc (ms_mem mz) (nt_Zs regs Bw n)) by
    (apply (nt_KA_run _ _ W memc _ _ _ KA0 HFr HG);
     intros b wlo whi x Hin Hx; cbv beta;
     nt_win Hin Hx ltac:(rewrite ?Usp, ?U36n in Hx;
       first [ left; unfold nt_Wn; lia
             | right; unfold notice_wr, twa_fld, TW.A_GOT_desk, TW.OFF_GOT;
               do 3 right; left; split; [exact Ek | unfold TA_GOT in *; lia] ])) end.
clear HF HFr HG.
nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (TA_GOT + 208 + 536)) Q10
  ltac:(cbn [sv_denot]; rewrite (HEI 472%nat ltac:(unfold A_TEXT, A_LIM; lia)); f_equal; vm_compute; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ =>
  assert (QD : sv_denot EF (SOff (A_OBJ 36) 536) = Z_to_bv 64 (TA_GOT + 208 + 536)) by
    (cbn [sv_denot]; rewrite (HEI (A_OBJ 36) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
     f_equal; vm_compute; reflexivity);
  pose proof (nt_pin EF _ _ (Z_to_bv 5 10) (SOff (A_OBJ 36) 536) HS (eq_trans Q10 (eq_sym QD))
    ltac:(vm_compute; reflexivity)) as HSq end.
clear HS Q10. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
(* run 2: the store of GOT.desk + 1, a0 = p, the epilogue and the tail jump *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ nt_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (md2 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md2; clear mt end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?mz) =>
  assert (KA2 : nt_KA W memc (ms_mem mz) (nt_Zs regs Bw n)) by
    (apply (nt_KA_run _ _ W memc _ _ _ KA1 HFr HG);
     intros b wlo whi x Hin Hx; cbv beta;
     nt_win Hin Hx ltac:(rewrite ?Usp, ?U36n in Hx;
       first [ left; unfold nt_Wn; lia
             | right; unfold notice_wr, twa_fld, TW.A_GOT_desk, TW.OFF_GOT;
               do 3 right; left; split; [exact Ek | unfold TA_GOT in *; lia] ])) end.
clear HF HFr HG KA1.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?mz) => rename mz into msF end.
(* the field's new value, read back from its region *)
assert (HVAL : val_mem segs (mrestrict (w_H W) (ms_mem msF)) (TA_GOT + 208 + 0) 4
  (bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 38 0)) (SLit 1))) mod 2 ^ (8 * Z.of_N 4))).
{ eapply (field_of_region_any E _ 277%nat (TA_GOT + 208) _ 0 4 0 4 0 4%N
    (SAlu ALU_ADD (SExt true 32 (SOff 38 0)) (SLit 1))).
  - exact (st_ok_region_nth E _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)).
  - exact U36n.
  - cbn [In]. left. reflexivity.
  - lia. }
assert (HDEN : sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 38 0)) (SLit 1))
  = Z_to_bv 64 (TW.GOT_desk Bw + 1)).
{ change (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 38 0)) (SLit 1)))
    with (alu64 ALU_ADD (sv_denot E (SExt true 32 (SOff 38 0))) (Z_to_bv 64 1)).
  pose proof (TWL.u_at_range Bw TW.A_GOT_desk 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  rewrite (nt_sext32 E 38 _ E38 R).
  rewrite nt_add_lit. reflexivity. }
rewrite HDEN in HVAL. change (8 * Z.of_N 4) with 32 in HVAL. rewrite ntd_mod_64_32 in HVAL.
(* the world after the store: GOT.desk + 1 *)
assert (HtwF : tw_at TMAP_A (aview segs (w_H W) (ms_mem msF)) (TW.set_GOT_desk Bw (TW.GOT_desk Bw + 1))).
{ unfold TW.set_GOT_desk, TW.A_GOT_desk.
  apply (tw_write TMAP_A (aview segs (w_H W) memc) _ Bw TW.OFF_GOT TA_GOT TW.SZ_GOT 208 4
    (TW.GOT_desk Bw + 1) TMAP_A_ok Htw TMAP_A_GOT ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)).
  - intros j Hj. unfold aview.
    replace (TA_GOT + 208 + Z.of_nat j) with (TA_GOT + 208 + 0 + Z.of_nat j) by lia.
    rewrite (HVAL j Hj). cbn [option_map]. f_equal.
    rewrite AF0x.unsigned_lit_small8
      by (match goal with |- 0 <= YO0f.le_byte ?v ?m ?jj < _ => pose proof (ntd_le_byte_small v m jj) end; lia).
    apply ntd_le_byte_mod32.
  - intros x Hx Hout. destruct KA2 as [KA2v _]. apply KA2v.
    + pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. lia.
    + intros [Hz | Hz].
      * pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia.
      * pose proof (ntd_wr_desk Bw n x Ek Hz) as Hr. lia. }
clear HVAL HDEN.
(* the registers at the tail jump: ra, sp, gp and tp the entry's, a0 = p *)
nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) R1
  ltac:(cbn [sv_denot]; rewrite (HElo 1%nat ltac:(lia));
        rewrite (nt_E_reg regs NB Bw 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
nt_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) R2
  ltac:(cbn [sv_denot]; rewrite (HElo 2%nat ltac:(lia));
        rewrite (nt_E_reg regs NB Bw 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
nt_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (HElo 3%nat ltac:(lia));
        rewrite (nt_E_reg regs NB Bw 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
nt_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (HElo 4%nat ltac:(lia));
        rewrite (nt_E_reg regs NB Bw 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
nt_reg HS (Z_to_bv 5 10) (w64 p) R10
  ltac:(cbn [sv_denot]; rewrite (HElo 11%nat ltac:(lia));
        rewrite (nt_E_reg regs NB Bw 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
assert (HPF : aregs_preserved regs (ms_regs msF)).
{ apply (aregs_preserved_of_st_ok segs (w_H W) E _ msF regs (nt_vals NB Bw) HS).
  - apply nt_agree; [intros j Hj; apply HElo; lia | exact HEd].
  - vm_compute. reflexivity. }
assert (FC : CSDESK_STK = NOTICE_STK) by reflexivity.
assert (Hsp1 : spZ (ms_regs msF) = spZ regs) by exact (f_equal bv_unsigned R2).
assert (Hsp16' : spZ (ms_regs msF) mod 16 = 0) by (rewrite Hsp1; exact Hsp16).
assert (Hlo' : sp0 - STK <= spZ (ms_regs msF) - CSDESK_STK) by (rewrite Hsp1, FC; exact Hlo).
assert (Hhi' : spZ (ms_regs msF) <= sp0) by (rewrite Hsp1; exact Hhi).
(* the callee's premises at the jump's memory *)
pose proof (ntd_ntc_keep B lyc Sc W memc mdc (ms_mem msF) regs (ms_regs msF) Bw n Fr p LAWS HAR Hce Hsp1 KA2 HAP HNT)
  as HNTF.
pose proof (ntd_tf_keep B lyc Sc W memc mdc (ms_mem msF) regs (ms_regs msF) Bw n p Fr LAWS HAR Hce Hsp1 KA2 HAP HTF)
  as HTFF.
pose proof (ntd_ro_keep W memc (ms_mem msF) regs Bw n Hce KA2 HRO) as HROF.
pose proof (eq_trans (nt_desk_cut timg_A Fr (TW.set_GOT_desk Bw (TW.GOT_desk Bw + 1)) n) Hcs) as HcsC.
(* the tail jump to check_state_desk: its contract at the jump's state, lifted to the G journal *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_check_state_desk) rg mm mdx) Q) end.
eapply SRr_mono.
{ apply (gx_call_cg segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
    (ms_mem msF) md2 k _ (ms_regs msF) CSDESK_STK CSDESK_EV 0 (fun _ => False)
    (fun _ _ _ => Bw' = TW.set_GOT_desk Bw (TW.GOT_desk Bw + 1)) HGX HGE HJ).
  intros memS HJS.
  exact (HDESK fx STK sp0 FP ly S W0 memS md0 own lyc Sc W (ms_mem msF) md2 k (ms_regs msF) p (nt_cut n) Fr
    (TW.set_GOT_desk Bw (TW.GOT_desk Bw + 1)) Bw' HJS
    (eq_ind_r YK0s.ret_ok Hra R1) (eq_ind_r (fun w => 4096 <= bv_unsigned w) Hra4 R1) R3 R4 R10
    Hsp16' Hlo' Hhi' HNTF HTFF HROF HtwF HcsC Hev). }
intros W2 c2 _ HQ.
exact (ntd_tail_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs n Bw Bw'
  (TW.set_GOT_desk Bw (TW.GOT_desk Bw + 1)) (ms_mem msF) (ms_regs msF)
  LAWS HGX HAR Hwin Hce Hsp KA2 HPF R1 Hsp1 HtwF W2 c2 HQ).
Qed.
End d.
