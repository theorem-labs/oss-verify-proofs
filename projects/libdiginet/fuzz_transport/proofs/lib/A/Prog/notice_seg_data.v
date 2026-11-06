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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/notice_seg_desk.v, with its numbers changed; 318 of its 459 lines of code are new or changed and 301 lines of the source are left out. *)
(* notice_seg_data: the arm of notice for a notice of kind N_DATA (0x835fc), which checks the notice against the data
   slot GOT.ndata names and counts it:
     +0x84 .. +0x88   a0 = p (`mv a0, a1`), the call of check_state_data at 0x83600 (return address 0x83604) from
                      sp - 16: a donor-form callee (check_state_data_cg.v), lifted into notice's G journal by
                      TransportGCg.v gx_call_cg; it gets the notice with its announce cut to 10 bytes (nt_cut), the
                      frame, the world and the body range of nt_ctx, carried from the entry memory across the walk's
                      own window (ntn_ntc_call, ntn_tf_call, ntn_src_keep); its post may change the world, so the walk
                      goes on at the world W2 it returns, the frame region kept (ntn_region_kept);
     +0x8c .. +0x98   a1 = (s32) GOT.ndata, a1 = a1 + 1, `sw a1, -584(a0)` with a0 the auipc value of the field (pinned to
                      the field's object so the store lands in its region);
     +0x9c            the jump to the epilogue +0x1b4 .. +0x1bc (ra restored, sp + 16) and `ret`.
   The world's only change is GOT.ndata (notice_m's N_DATA case, nt_m_data). The post is closed at W2 (ntn_close), with
   the post's kept fact carried before, across and after the call (ntn_kp_step, dk_kept_trans_g). *)
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

(* The bytes a notice of kind N_DATA writes: GOT.ndata's four. *)
Lemma ntn_wr_data : forall Bw n a, TI.n_kind n = TC.N_DATA -> notice_wr Bw n a ->
  TA_GOT + 220 <= a < TA_GOT + 224.
Proof.
  intros Bw n a Hk Hw.
  unfold notice_wr, TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in Hk, Hw.
  unfold twa_fld, TW.A_GOT_ndata, TW.OFF_GOT in Hw.
  destruct Hw as [(E & _) | [(E & _) | [(E & _) | [(E & _) | [(E & Ha) | (E & _)]]]]]; try lia.
Qed.

Lemma ntn_le_byte_small : forall v (m j : nat), 0 <= YO0f.le_byte v m j < 256.
Proof. intros v m j. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

Lemma ntn_mod_64_32 : forall v, bv_unsigned (Z_to_bv 64 v) mod 2 ^ 32 = v mod 2 ^ 32.
Proof.
  intros v. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity.
Qed.

Lemma ntn_le_byte_mod32 : forall v (j : nat), YO0f.le_byte (v mod 2 ^ 32) 4 j = YO0f.le_byte v 4 j.
Proof.
  intros v j. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* A prefix of a byte array is a byte array. *)
Lemma ntn_garr8_firstn : forall (mm : word -> option byte) q (l : list byte) kk,
  garr8 tfibsegs mm q (map DSpec.bz l) -> garr8 tfibsegs mm q (map DSpec.bz (firstn kk l)).
Proof.
  intros mm q l kk H. rewrite <- (firstn_skipn kk l) in H. rewrite map_app in H.
  exact (proj1 (proj1 (garr8_app tfibsegs mm q _ _) H)).
Qed.

(* A range outside notice's window [sp - NOTICE_STK, sp) is outside check_state_data's window at sp - 16. *)
Lemma ntn_off_shift : forall (regs regs1 : bvmap 5 word) q m, spZ regs1 = spZ regs - 16 ->
  decode_off_win regs NOTICE_STK q m -> decode_off_win regs1 CSDATA_STK q m.
Proof.
  intros regs regs1 q m Hs Ho. unfold decode_off_win in *. rewrite Hs.
  assert (NOTICE_STK = 16 + CSDATA_STK) by reflexivity. lia.
Qed.

Section dh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.

(* A byte of a range placed by trans_src_ok and outside notice's window. *)
Lemma ntn_rng : forall lyc Sc (W : world segs) memc mdc (regs : bvmap 5 word) q m,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  trans_src_ok B lyc Sc W memc q m -> decode_off_win regs NOTICE_STK q m ->
  forall a, q <= a < q + m -> 0 <= a < 2 ^ 64 /\ ~ nt_Wn regs a.
Proof.
  intros lyc Sc W memc mdc regs q m LAWS HAR Hs Ho a Ha.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc q m HAR Hs ltac:(lia)) as [H|H];
    unfold decode_off_win, nt_Wn in *; lia.
Qed.

(* trans_src_ok carried across the walk's own runs (they change only the window). *)
Lemma ntn_src_keep : forall lyc Sc (W : world segs) memc mdc m1 (regs : bvmap 5 word) q m,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc -> alloc_ceiling <= spZ regs - NOTICE_STK ->
  nt_KA W memc m1 (nt_Wn regs) ->
  trans_src_ok B lyc Sc W memc q m -> decode_off_win regs NOTICE_STK q m ->
  trans_src_ok B lyc Sc W m1 q m.
Proof.
  intros lyc Sc W memc mdc m1 regs q m LAWS HAR Hce [KA _] Hs Ho.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (trans_src_ok_view B lyc Sc W W memc m1 q m Hs).
  - intros a Ha. destruct (ntn_rng lyc Sc W memc mdc regs q m LAWS HAR Hs Ho a Ha) as [H1 H2]. exact (KA a H1 H2).
  - intros s Hs'. apply KA; [lia | unfold nt_Wn; lia].
Qed.

(* A byte array inside such a range, carried across the walk's own runs. *)
Lemma ntn_garr_keep : forall lyc Sc (W : world segs) memc mdc m1 (regs : bvmap 5 word) q0 m0 q (l : list Z),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  nt_KA W memc m1 (nt_Wn regs) ->
  trans_src_ok B lyc Sc W memc q0 m0 -> decode_off_win regs NOTICE_STK q0 m0 ->
  q0 <= q -> q + Z.of_nat (length l) <= q0 + m0 ->
  garr8 segs (mrestrict (w_H W) memc) q l -> garr8 segs (mrestrict (w_H W) m1) q l.
Proof.
  intros lyc Sc W memc mdc m1 regs q0 m0 q l LAWS HAR KA Hs Ho H1 H2 HG.
  apply (nt_garr8_keep W memc m1 (nt_Wn regs) q l KA HG).
  intros a Ha. exact (ntn_rng lyc Sc W memc mdc regs q0 m0 LAWS HAR Hs Ho a ltac:(lia)).
Qed.

(* The notice check_state_data gets at the call (its announce cut to 10 bytes: nt_cut). *)
Lemma ntn_ntc_call : forall lyc Sc (W : world segs) memc mdc m1 (regs regs1 : bvmap 5 word) p n,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc -> alloc_ceiling <= spZ regs - NOTICE_STK ->
  spZ regs1 = spZ regs - 16 -> nt_KA W memc m1 (nt_Wn regs) ->
  trans_ntc_at B lyc Sc W memc regs NOTICE_STK p n ->
  trans_ntc_at B lyc Sc W m1 regs1 CSDATA_STK p (nt_cut n).
Proof.
  intros lyc Sc W memc mdc m1 regs regs1 p n LAWS HAR Hce Hs1 KA
    (P0 & P8 & Hsrc & Hoff & NB & HNB & HNBL & HK0 & HK4 & HK8 & HK12 & Hpers & Hmac & Hblen & HK64 & HK68 &
     HBG & HBS & HBO & HANN).
  unfold trans_ntc_at, nt_cut.
  cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_counter TI.n_retry TI.n_mac_offset TI.n_pers TI.n_ann
    TI.n_body TI.n_body_len].
  split; [exact P0|]. split; [exact P8|].
  split; [exact (ntn_src_keep lyc Sc W memc mdc m1 regs p NTC_SIZE LAWS HAR Hce KA Hsrc Hoff)|].
  split; [exact (ntn_off_shift regs regs1 p NTC_SIZE Hs1 Hoff)|].
  exists NB.
  split.
  { apply (ntn_garr_keep lyc Sc W memc mdc m1 regs p NTC_SIZE p _ LAWS HAR KA Hsrc Hoff);
      [lia | rewrite length_map, HNBL; unfold NTC_SIZE; lia | exact HNB]. }
  split; [exact HNBL|]. split; [exact HK0|]. split; [exact HK4|]. split; [exact HK8|]. split; [exact HK12|].
  split; [exact Hpers|]. split; [exact Hmac|]. split; [exact Hblen|]. split; [exact HK64|]. split; [exact HK68|].
  split.
  { apply (ntn_garr_keep lyc Sc W memc mdc m1 regs _ _ _ _ LAWS HAR KA HBS HBO);
      [lia | rewrite length_map; lia | exact HBG]. }
  split; [exact (ntn_src_keep lyc Sc W memc mdc m1 regs _ _ LAWS HAR Hce KA HBS HBO)|].
  split; [exact (ntn_off_shift regs regs1 _ _ Hs1 HBO)|].
  destruct (TI.n_ann n) as [an|]; cbn [option_map]; [|exact HANN].
  destruct HANN as (A0 & A8 & AV & AN & AS & AO).
  unfold nt_ann_cut. cbn [TI.ta_version TI.ta_name].
  split; [exact A0|]. split; [exact A8|].
  split.
  { apply (ntn_garr_keep lyc Sc W memc mdc m1 regs (TW.u_at NB 24 8) ANN_SIZE _ _ LAWS HAR KA AS AO);
      [lia | rewrite length_map, length_firstn; unfold ANN_SIZE; lia | exact (ntn_garr8_firstn _ _ _ 10 AV)]. }
  split.
  { apply (ntn_garr_keep lyc Sc W memc mdc m1 regs (TW.u_at NB 24 8) ANN_SIZE _ _ LAWS HAR KA AS AO);
      [lia | rewrite length_map, length_firstn; unfold ANN_SIZE; lia | exact (ntn_garr8_firstn _ _ _ 10 AN)]. }
  split; [exact (ntn_src_keep lyc Sc W memc mdc m1 regs _ _ LAWS HAR Hce KA AS AO)|].
  exact (ntn_off_shift regs regs1 _ _ Hs1 AO).
Qed.

(* The current heap frame check_state_data gets at the call. *)
Lemma ntn_tf_call : forall lyc Sc (W : world segs) memc mdc m1 (regs regs1 : bvmap 5 word) Fr,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc -> alloc_ceiling <= spZ regs - NOTICE_STK ->
  spZ regs1 = spZ regs - 16 -> nt_KA W memc m1 (nt_Wn regs) ->
  trans_tframe_at B lyc Sc W memc regs NOTICE_STK Fr ->
  trans_tframe_at B lyc Sc W m1 regs1 CSDATA_STK Fr.
Proof.
  intros lyc Sc W memc mdc m1 regs regs1 [fr|] LAWS HAR Hce Hs1 KA H; [|exact I].
  destruct H as (A0 & G & Ts & Off).
  split; [exact A0|].
  split.
  { apply (ntn_garr_keep lyc Sc W memc mdc m1 regs _ _ _ _ LAWS HAR KA Ts Off);
      [lia | rewrite length_map; lia | exact G]. }
  split; [exact (ntn_src_keep lyc Sc W memc mdc m1 regs _ _ LAWS HAR Hce KA Ts Off)|].
  exact (ntn_off_shift regs regs1 _ _ Hs1 Off).
Qed.

(* A region of the symbolic state kept across a call that may change the world. *)
Lemma ntn_region_kept : forall E (H H2 : word -> bool) (m m2 : word -> option byte) nn b lo hi wlo whi cs,
  bv_unsigned (ew E nn) = b ->
  (forall a, b + lo <= a < b + hi -> aview segs H2 m2 a = aview segs H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
  region_kept segs E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some nn) lo hi wlo whi cs).
Proof.
  intros E H H2 m m2 nn b lo hi wlo whi cs Hn Hav Hp.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
  - apply (mbyte_of_aview segs). apply Hav. exact Ha.
  - intros _. apply (apresent_writable segs). apply Hp. exact Ha.
Qed.

(* One step that changes only notice's window and the bytes notice_wr names keeps the post's kept fact (TransportGCg.v
   dk_kept_step_g, at the world of the step). *)
Lemma ntn_kp_step : forall lyc Sc (W : world segs) memc mdc (W1 : world segs) m1 m2 (regs : bvmap 5 word) Bw n,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc -> alloc_ceiling <= spZ regs - NOTICE_STK ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W1 m1 (spZ regs - NOTICE_STK) (spZ regs) (notice_wr Bw n) ->
  nt_KA W1 m1 m2 (nt_Zs regs Bw n) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W1 m2 (spZ regs - NOTICE_STK) (spZ regs) (notice_wr Bw n).
Proof.
  intros lyc Sc W memc mdc W1 m1 m2 regs Bw n LAWS HAR Hce (K1 & K2 & K3 & K4 & K5 & K6) [Kv Kp].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WL : forall a, notice_wr Bw n a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; destruct (nt_wr_range Bw n a Ha) as [H|H]; unfold TA_GOT, TA_M in H; rewrite C5; lia).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. rewrite Kv; [exact (K1 a Ha Hw) | lia |].
    intros [Hz | Hz]; [exact (Hw Hz) | pose proof (WL a Hz); lia].
  - intros b m i Hb Hi Hn.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
    rewrite Kv; [exact (K2 b m i Hb Hi Hn) | lia |].
    intros [Hz | Hz]; [lia | exact (Hn Hz)].
  - intros a Hi HnG Hno He. pose proof (transport_segs_low a Hi) as Hl.
    rewrite Kv; [exact (K3 a Hi HnG Hno He) | lia |].
    intros [Hz | Hz]; [lia | exact (HnG (nt_wr_G _ _ _ Hz))].
  - intros cid pos a Hin Hr Hn.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    assert (Ha : 0 <= a < alloc_ceiling).
    { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
    rewrite Kv; [exact (K4 cid pos a Hin Hr Hn) | lia |].
    intros [Hz | Hz]; [lia | exact (Hn Hz)].
  - intros a Ha Hw Hp. apply Kp. exact (K5 a Ha Hw Hp).
  - intros a Ha. apply Kp. exact (K6 a Ha).
Qed.
End dh.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The post at the return, after the call: the journal at the state the call left, the call's kept facts. *)
Lemma ntn_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
    ly2 S2 (W2 : world segs) regsF mF mdF,
  @nt_ctx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mF
    mdF k ->
  frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> mo_le MT Sc S2 0 ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mF (spZ regs - NOTICE_STK) (spZ regs) (notice_wr Bw n) ->
  tw_at TMAP_A (aview segs (w_H W2) mF) Bw' ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 ->
  forall mat, @transport_notice_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n Bw Bw' W2
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ly2 S2 W2 regsF mF mdF HC HJF
    Hfr Hperm Hmo KP HtwF HP RF1 mat.
  pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJ Hra Hra4 Hgp Htp H11 Hsp16
    Hlo Hhi HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
  unfold transport_notice_post, transport_cg_post.
  exists ly2, S2, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), 0.
  split.
  { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [unfold NOTICE_EV; lia|].
  split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJF|].
  split; [exact HP|]. split; [exact Hfr|]. split; [exact Hperm|]. split; [exact KP|].
  split; [exact Hmo | exact HtwF].
Qed.

Lemma nt_path_data : @nt_path fx rc B MT TC.N_DATA NT_DATA.
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
assert (FD : CSDATA_STK = 8224) by reflexivity.
destruct (nt_m_data timg_A Fr Bw n Bw' Ek Hm) as (HmD & Hmax & HBw).
destruct (HDT Ek) as (HDs & HDo & HDl).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (HElo 2%nat ltac:(lia)); rewrite (nt_E_reg regs NB Bw 2%nat 2%bv eq_refl); reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport)) as RET.
(* run 1, from the jump `jr a0` to +0x88: a0 = p, the call of check_state_data *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ nt_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (md1 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md1; clear mt end.
lazymatch type of HS with YP0l.st_ok _ _ _ (restrict _ ?mz) => rename mz into ms1 end.
assert (KA1 : nt_KA W memc (ms_mem ms1) (nt_Wn regs)) by
  (apply (nt_KA_run _ _ W memc _ _ _ KA HFr HG);
   intros b wlo whi x Hin Hx; cbv beta; unfold nt_Wn;
   nt_win Hin Hx ltac:(rewrite ?Usp in Hx; lia)).
clear HF HFr HG.
pmkst HS.
assert (HBASE : BASE = 0x81264) by (vm_compute; reflexivity).
nt_reg HS (Z_to_bv 5 10) (w64 p) Q10
  ltac:(cbn [sv_denot]; rewrite (HElo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11%nat 11%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H11).
nt_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 9120)) R1 ltac:(apply codeptr_val; exact HEI).
nt_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 16)) Q2 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
nt_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (HElo 3%nat ltac:(lia)), (nt_E_reg regs NB Bw 3%nat 3%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Hgp).
nt_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (HElo 4%nat ltac:(lia)), (nt_E_reg regs NB Bw 4%nat 4%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Htp).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms1) (Z_to_bv 5 2)) = spZ regs - 16)
  by (rewrite Q2; apply unsigned_lit_small; lia).
assert (Hsp1 : spZ (ms_regs ms1) = spZ regs - 16) by exact ESP.
assert (HtwC : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms1)) Bw).
{ apply (nt_tw_keep W memc (ms_mem ms1) Bw (nt_Wn regs) Htw KA1).
  intros x Hx Hz. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia. }
(* +0x88: check_state_data (p), a donor-form callee lifted into the G journal (TransportGCg.v gx_call_cg) *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_check_state_data) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_call_cg fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
    (ms_mem ms1) md1 k _ (ms_regs ms1) CSDATA_STK CSDATA_EV 0 (fun _ => False) (fun _ _ _ => Bw = Bw) HGX HGE HJ).
  intros memS HJS. eapply SRr_mono.
  { apply (HDATA fx STK sp0 FP ly S W0 memS md0 own lyc Sc W (ms_mem ms1) md1 k (ms_regs ms1) p (nt_cut n) Fr Bw Bw
      HJS).
    - rewrite R1. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
    - change (raZ (ms_regs ms1)) with (bv_unsigned (YK11.getr (ms_regs ms1) 1)). rewrite R1, HBASE.
      rewrite unsigned_lit_small by lia. lia.
    - exact R3.
    - exact R4.
    - exact Q10.
    - rewrite Hsp1, Zminus_mod, Hsp16. reflexivity.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. lia.
    - exact (ntn_ntc_call B lyc Sc W memc mdc (ms_mem ms1) regs (ms_regs ms1) p n LAWS HAR Hce Hsp1 KA1 HNT).
    - exact (ntn_tf_call B lyc Sc W memc mdc (ms_mem ms1) regs (ms_regs ms1) Fr LAWS HAR Hce Hsp1 KA1 HTF).
    - exact HtwC.
    - rewrite nt_data_cut. exact HmD.
    - exact (ntn_src_keep B lyc Sc W memc mdc (ms_mem ms1) regs _ _ LAWS HAR Hce KA1 HDs HDo).
    - exact (ntn_off_shift regs (ms_regs ms1) _ _ Hsp1 HDo).
    - exact HDl.
    - unfold CSDATA_EV. unfold NOTICE_EV in Hev. lia. }
  intros W' c' _ Hp.
  exact (decode_cg_post_dcg B MT STK sp0 FP ly S W0 memS md0 own lyc Sc W (ms_mem ms1) k (ms_regs ms1) _ _ _ _ _ W' c'
    Hp). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & e & -> & He & J2 & HPR & Hfr2 & Hperm2 & HK & Hmo2 &
  (_ & HGK)).
assert (Ee : e = 0) by (unfold CSDATA_EV in He; lia). subst e. rewrite Z.add_0_r in J2.
rewrite R1.
(* the post's kept fact at the call, then across it *)
assert (KP0 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W (ms_mem ms1) (spZ regs - NOTICE_STK) (spZ regs)
  (notice_wr Bw n)).
{ apply (ntn_kp_step B lyc Sc W memc mdc W memc (ms_mem ms1) regs Bw n LAWS HAR Hce).
  - apply dk_kept_refl_g. exact Hwin.
  - exact (nt_KA_mono W memc (ms_mem ms1) (nt_Wn regs) (nt_Zs regs Bw n) (fun a Ha => nt_Wn_Zs regs Bw n a Ha) KA1). }
assert (KP2 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - NOTICE_STK) (spZ regs)
  (notice_wr Bw n)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS lyc Sc W memc W (ms_mem ms1) W2 mem2 (spZ regs - NOTICE_STK) (spZ regs)
    (spZ (ms_regs ms1) - CSDATA_STK) (spZ (ms_regs ms1)) _ (fun _ => False));
    [lia | lia | exact KP0 | exact HK | rewrite Hsp1; lia | rewrite Hsp1; lia | intros a []]. }
assert (Htw2 : tw_at TMAP_A (aview segs (w_H W2) mem2) Bw).
{ apply (tw_kept_GA _ _ Bw HtwC). intros b m i Hin Hi.
  exact (gx_kept_rows _ _ _ _ _ _ HGK b m i Hin Hi). }
(* the symbolic state after the call: the frame region kept *)
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W2) mem2) HPR [0%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  apply (ntn_region_kept E (w_H W) (w_H W2) (ms_mem ms1) mem2 2%nat (spZ regs)); [exact Usp | |].
  - intros a Ha. destruct HK as (K1 & _). apply K1; [lia | rewrite Hsp1; lia].
  - intros a Ha. destruct HK as (_ & _ & _ & _ & K5 & _). apply K5; [lia | rewrite Hsp1; lia |].
    destruct KA1 as [_ KA1p]. apply KA1p. apply Hwin. lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in HS end.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall j, (j < 1024)%nat -> ew E1 j = ew E j) by (intros j Hj; apply ew_havoc_old; exact Hj).
clear HJ SHOK HEI0. rename J2 into HJ.
assert (SHOK : sh_ok segs NT_Bx [] E1 (mrestrict (w_H W2) mem2)) by (unfold sh_ok; constructor).
(* the valuation after the call *)
pose proof (nt_E_atom regs NB Bw 7%nat ltac:(lia)) as E39q. cbn [Nat.add nth nt_vals] in E39q.
assert (E39 : ew E1 39 = Z_to_bv 64 (TW.u_at Bw TW.A_GOT_ndata 4))
  by (rewrite E1lo by lia; rewrite (HElo 39%nat ltac:(lia)); exact E39q).
assert (U37 : bv_unsigned (ew E1 (A_OBJ 37)) = TA_GOT + 220)
  by (rewrite (HEI1 (A_OBJ 37) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); vm_compute; reflexivity).
assert (U37n : bv_unsigned (ew E1 278%nat) = TA_GOT + 220) by exact U37.
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite E1lo by lia; exact Usp).
pose proof (nt_E_atom regs NB Bw 0%nat ltac:(lia)) as E32q. cbn [Nat.add nth nt_vals] in E32q.
assert (E32e : ew E1 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite E1lo by lia; rewrite (HElo 32%nat ltac:(lia)); exact E32q).
assert (U11e : bv_unsigned (ew E1 11) = p).
{ rewrite E1lo by lia. rewrite (HElo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11%nat 11%bv eq_refl), H11.
  apply unsigned_lit_small. lia. }
(* GOT.ndata's region added, its address in the facts *)
pose proof (nt_add E1 _ _ (nt_reg_fld 37 39) HS ltac:(vm_compute; reflexivity)) as HSq. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq.
specialize (HSq ltac:(cbn [ms_mem restrict]; apply (nt_fld_ok W2 mem2 E1 Bw 37%nat 39%nat 220);
  [exact U37 | lia | unfold TW.SZ_GOT; lia | exact E39 | exact Htw2])).
specialize (HSq ltac:(cbn [all_disjoint]; split; [|exact I];
  unfold extent_disjoint, nt_reg_fld;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold TA_GOT in U37, U37n; lia)).
rename HSq into HS.
pose proof (nt_facts_set E1 _ _ (nt_facts_f 278%nat (TA_GOT + 220)) HS
  ltac:(apply (nt_facts_f_ok E1 (spZ regs) p 278%nat (TA_GOT + 220));
        first [exact Usp1 | exact U11e | exact E32e | exact U37n | lia])) as HSq.
clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
(* run 2, +0x8c .. +0x94: the load of GOT.ndata and the increment; the store needs its auipc pinned *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ nt_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (md3 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md3; clear mt end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
  assert (KA3 : nt_KA W2 mem2 (ms_mem mz) (nt_Zs regs Bw n)) by
    (apply (nt_KA_run _ _ W2 mem2 _ _ _ (nt_KA_refl W2 mem2 _) HFr HG);
     intros b wlo whi x Hin Hx; cbv beta;
     nt_win Hin Hx ltac:(rewrite ?Usp1, ?U37n in Hx;
       first [ left; lia
             | right; unfold notice_wr, twa_fld, TW.A_GOT_ndata, TW.OFF_GOT;
               do 4 right; left; split; [exact Ek | unfold TA_GOT in *; lia] ])) end.
clear HF HFr HG.
nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (TA_GOT + 220 + 584)) Q10b
  ltac:(cbn [sv_denot]; rewrite (HEI1 474%nat ltac:(unfold A_TEXT, A_LIM; lia)); f_equal; vm_compute; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ =>
  assert (QD : sv_denot EF (SOff (A_OBJ 37) 584) = Z_to_bv 64 (TA_GOT + 220 + 584)) by
    (cbn [sv_denot]; rewrite (HEI1 (A_OBJ 37) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
     f_equal; vm_compute; reflexivity);
  pose proof (nt_pin EF _ _ (Z_to_bv 5 10) (SOff (A_OBJ 37) 584) HS (eq_trans Q10b (eq_sym QD))
    ltac:(vm_compute; reflexivity)) as HSq end.
clear HS Q10b. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
(* run 3, +0x98 .. +0x9c and the epilogue +0x1b4 .. +0x1bc: the store of GOT.ndata + 1, the jump, `ret` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ nt_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (md4 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md4; clear mt end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
  assert (KA4 : nt_KA W2 mem2 (ms_mem mz) (nt_Zs regs Bw n)) by
    (apply (nt_KA_run _ _ W2 mem2 _ _ _ KA3 HFr HG);
     intros b wlo whi x Hin Hx; cbv beta;
     nt_win Hin Hx ltac:(rewrite ?Usp1, ?U37n in Hx;
       first [ left; lia
             | right; unfold notice_wr, twa_fld, TW.A_GOT_ndata, TW.OFF_GOT;
               do 4 right; left; split; [exact Ek | unfold TA_GOT in *; lia] ])) end.
clear HF HFr HG KA3.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into msF end.
(* the field's new value, read back from its region *)
assert (HVAL : val_mem segs (mrestrict (w_H W2) (ms_mem msF)) (TA_GOT + 220 + 0) 4
  (bv_unsigned (sv_denot E1 (SAlu ALU_ADD (SExt true 32 (SOff 39 0)) (SLit 1))) mod 2 ^ (8 * Z.of_N 4))).
{ eapply (field_of_region_any E1 _ 278%nat (TA_GOT + 220) _ 0 4 0 4 0 4%N
    (SAlu ALU_ADD (SExt true 32 (SOff 39 0)) (SLit 1))).
  - exact (st_ok_pi_region_nth E1 _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)).
  - exact U37n.
  - cbn [In]. left. reflexivity.
  - lia. }
assert (HDEN : sv_denot E1 (SAlu ALU_ADD (SExt true 32 (SOff 39 0)) (SLit 1))
  = Z_to_bv 64 (TW.GOT_ndata Bw + 1)).
{ change (sv_denot E1 (SAlu ALU_ADD (SExt true 32 (SOff 39 0)) (SLit 1)))
    with (alu64 ALU_ADD (sv_denot E1 (SExt true 32 (SOff 39 0))) (Z_to_bv 64 1)).
  pose proof (TWL.u_at_range Bw TW.A_GOT_ndata 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  rewrite (nt_sext32 E1 39 _ E39 R).
  rewrite nt_add_lit. reflexivity. }
rewrite HDEN in HVAL. change (8 * Z.of_N 4) with 32 in HVAL. rewrite ntn_mod_64_32 in HVAL.
(* the return *)
nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (HElo 1%nat ltac:(lia));
        rewrite (nt_E_reg regs NB Bw 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (HPF : aregs_preserved regs (ms_regs msF)).
{ apply (aregs_preserved_of_st_ok segs (w_H W2) E1 _ msF regs (nt_vals NB Bw) HS).
  - apply nt_agree; [intros j Hj; rewrite E1lo by lia; apply HElo; lia | exact HEd].
  - vm_compute. reflexivity. }
eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
refine (ntn_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ly2 S2 W2
  (ms_regs msF) (ms_mem msF) md4 HC HJ Hfr2 Hperm2 Hmo2 _ _ HPF RF1 mat').
- exact (ntn_kp_step B lyc Sc W memc mdc W2 mem2 (ms_mem msF) regs Bw n LAWS HAR Hce KP2 KA4).
- (* the world after the store: GOT.ndata + 1 *)
  rewrite HBw. unfold TW.set_GOT_ndata, TW.A_GOT_ndata.
  apply (tw_write TMAP_A (aview segs (w_H W2) mem2) _ Bw TW.OFF_GOT TA_GOT TW.SZ_GOT 220 4
    (TW.GOT_ndata Bw + 1) TMAP_A_ok Htw2 TMAP_A_GOT ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)).
  + intros j Hj. unfold aview.
    replace (TA_GOT + 220 + Z.of_nat j) with (TA_GOT + 220 + 0 + Z.of_nat j) by lia.
    refine (eq_trans (f_equal (option_map (fun b : byte => bv_unsigned b)) (HVAL j Hj)) _).
    cbn [option_map]. f_equal.
    rewrite AF0x.unsigned_lit_small8
      by (match goal with |- 0 <= YO0f.le_byte ?v ?m ?jj < _ => pose proof (ntn_le_byte_small v m jj) end; lia).
    apply ntn_le_byte_mod32.
  + intros x Hx Hout. destruct KA4 as [KA4v _]. apply KA4v.
    * pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. lia.
    * intros [Hz | Hz].
      -- pose proof (TMAP_A_hull x Hx) as Hh. unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia.
      -- pose proof (ntn_wr_data Bw n x Ek Hz) as Hr. lia.
Qed.
End d.
