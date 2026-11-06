(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module names changed; 1031 of its 1126 lines of code are new or changed and 935 lines of the source are left out. *)
(* diginet_session_wake_seg_ntc: the notice piece of the image-A ASan walk of diginet_session_wake,
   wake_ntc_pc : wake_ntc_stmt (lib/A/Prog/diginet_session_wake_seg_cut.v), code +0x350 .. +0x40c of the listing
   (0x86a4c .. 0x86b08), from the notice cut WAKE_NTC (state wake_ntc_cur, registers wake_regs_ntc) to the e2 cut
   WAKE_E2 (state wake_rel_cur, registers wake_regs_rel), whose Prop wake_e2_at the statement hands it. The walk holds
   the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS 0 []) with the class-2 frame F owned; the runs are
   lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x over that journal.
     run 1  +0x350 .. +0x380  s4 = p = F + 32 (`addi s4, s9, 32`); the nine `sb zero, k(s8)`, k = 8 .. 0xb, 4 .. 7,
                              0xc: the frame's shadow bytes 4 .. 12 := 0 (the notice's 72 bytes usable); a0 = p + 16,
                              a2 = 56, a1 = 0. The write rights are the own frame's bytes and shadow bytes
                              (TransportGFrame.v awr_ok_x_cons_own) and g_s (awr_ok_x_cons_g).
     +0x384                   `jal __asan_memset`: TransportGCg.v gx_intrin_at with OSet; the destination
                              [p + 16, p + 72) is a byte range of the own frame (transport_twr_ok_g_intro, an awr_byte
                              of the frame list below alloc_ceiling, so outside the ESTACK window), addressable by the
                              shadow bytes 6 .. 12 just written (wn_ra_zero), its hull visible (wn_hull_in).
     run 2  +0x388 .. +0x3dc  the 8 bytes 0x0000000100000002 at p (kind N_STATE, state S_WAKING), `sw s7, 8(s4)` (old =
                              S_state Bw, which wake_regs_ntc gives in s7), `sw s11, 12(s4)` (reason R_WAKE = 1); the
                              checked store of 1 at s + 112 (the shadow byte read through s6 is 0: trans_wake_cells);
                              the checked loads of s + 96 (a2 = g_s.notify) and s + 104 (a0 = notify_ctx); a1 = p.
                              The 72 bytes at p are then WalkNotify.v ntc_state_bytes 1 (S_state Bw) 1 (wn_nb): the
                              notice wake_ntc Bw as check_state_data_cg.v trans_ntc_at reads it (wn_ntc_at). The world
                              relation holds at set_S_state (wake_w3 B1 e2 now) S_WAKING (TWorldG.v tw_write in g_s's
                              row), and a2 = TI.ti_notice timg_A (wake_ntc_cur's S_notify, wn_notify).
     +0x3e0                   `jalr a2`: notice_cg.v transport_notice_cg at TI.ti_notice timg_A in the same G journal,
                              its premises: the current heap frame at the call state from the entry's trans_tframe_at
                              and what the walk has kept (wn_tframe), the read-only view (the entry's, kept by the
                              image clause of acall_kept_g), the world relation, the model's notice_m (wake_ntc_cur),
                              notice_apart (wn_apart: an N_STATE notice writes GOT, a part of wake_wr Bw on this path),
                              the N_DATA premise (vacuous) and the event budget (WAKE_EV = SENDCTL_EV + NOTICE_EV).
                              Its acall_kept_g folds into the walk's with TransportGCg.v dk_kept_trans_nf_g (NF = the
                              own frame, TransportGFrame.v dkg_nf_sep_gw).
     run 3  +0x3e4 .. +0x40c  a0 = 0 (DIGINET_OK, wake_ntc_cur's r), a1 = -8, the nine shadow bytes 4 .. 12 := 0xf8,
                              up to WAKE_E2; the state wake_rel_cur there (the post's X is notice's tw_at at Bw' and
                              wake_ntc_cur's g_fail_next Bw' <= 1) and the registers wake_regs_rel conclude by
                              wake_e2_at.
   What the call keeps (acall_kept_g over wake_wr Bw) is carried over each run by wn_kept_w (TransportGFrame.v
   dk_kept_step_gw with dkg_nf_sep_gw: every byte a run changes is in the call's stack window, the own frame or G). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
diginet_session_wake_cg diginet_session_wake_seg_cut diginet_session_wake_seg_keep.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkNotify.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From Stdlib Require Znumtheory.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module WN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkNotify.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. Shadow geometry of a frame                                       *)
(* ------------------------------------------------------------------ *)

(* A range of an 8-aligned frame whose granules lo .. hi - 1 have the shadow byte 0 is addressable. *)
Lemma wn_ra_zero : forall (rd : Z -> option Z) F q n lo hi,
  0 <= F -> F mod 8 = 0 -> F + 8 * lo <= q -> q + n <= F + 8 * hi ->
  (forall i, lo <= i < hi -> rd (SHADOW_OFF + F / 8 + i) = Some 0) ->
  range_addressable rd SHADOW_OFF q n.
Proof.
  intros rd F q n lo hi HF0 HF8 Hlo Hhi HZ x Hx.
  exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr.
  pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
  set (f := F / 8) in *.
  assert (Ex : x / 8 = f + (x - F) / 8).
  { replace x with (f * 8 + (x - F)) at 1 by lia. apply Z.div_add_l. lia. }
  rewrite Ex, Z.add_assoc. apply HZ. split.
  - apply Z.div_le_lower_bound; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

(* The shadow hull of a range of a 64-aligned frame of fs bytes (a multiple of 64) lies in the frame's fs / 8
   shadow bytes; the range may be empty. *)
Lemma wn_hull_in : forall (rd : Z -> option Z) Fc fs q n,
  0 <= Fc -> Fc mod 64 = 0 -> fs mod 64 = 0 -> 64 <= fs -> Fc <= q -> 0 <= n -> q + n <= Fc + fs ->
  (forall i, 0 <= i < fs / 8 -> rd (SHADOW_OFF + Fc / 8 + i) <> None) ->
  shadow_hull_vis rd q n.
Proof.
  intros rd Fc fs q n HF0 HF64 Hfs64 Hfs Hq Hn Hqn HV s Hs.
  unfold shadow_addr, SHADOW_OFF in Hs.
  pose proof (Z.div_mod Fc 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  pose proof (Z.div_mod fs 64 ltac:(lia)) as DS. rewrite Hfs64, Z.add_0_r in DS.
  set (g := Fc / 64) in *. set (h := fs / 64) in *.
  assert (EF8 : Fc / 8 = 8 * g) by (rewrite DF; replace (64 * g) with ((8 * g) * 8) by ring; apply Z.div_mul; lia).
  assert (ES8 : fs / 8 = 8 * h) by (rewrite DS; replace (64 * h) with ((8 * h) * 8) by ring; apply Z.div_mul; lia).
  assert (Hg : 0 <= g) by lia. assert (Hh : 1 <= h) by lia.
  assert (L1 : 8 * g <= q / 8) by (apply Z.div_le_lower_bound; lia).
  assert (L2 : (q + n - 1) / 8 < 8 * g + 8 * h) by (apply Z.div_lt_upper_bound; lia).
  assert (A1 : 268431360 + g <= (2147450880 + q / 8) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (A2 : (2147450880 + (q + n - 1) / 8) / 8 < 268431360 + g + h) by (apply Z.div_lt_upper_bound; lia).
  replace s with (SHADOW_OFF + Fc / 8 + (s - (SHADOW_OFF + Fc / 8))) by ring.
  apply HV. rewrite ES8. unfold SHADOW_OFF. rewrite EF8. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The bytes a store leaves                                         *)
(* ------------------------------------------------------------------ *)

(* Two byte lists with the same values are equal (their bytes' well-formedness proofs may not be convertible). *)
Lemma wn_bytes_eq : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity |].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma wn_garr8_val : forall (segs : list Segment) (mem : word -> option byte) a (n : nat) v,
  val_mem segs mem a n v -> garr8 segs mem a (map DSpec.bz (TW.put n v)).
Proof.
  intros segs mem a n v H j Hj. rewrite length_map, TWL.length_put in Hj.
  assert (E : nth j (map DSpec.bz (TW.put n v)) 0 = YO0f.le_byte v n j).
  { rewrite (nth_indep _ 0 (DSpec.bz (Z_to_bv 8 0))) by (rewrite length_map, TWL.length_put; exact Hj).
    rewrite map_nth. unfold DSpec.bz. apply tw_le_byte_put. exact Hj. }
  assert (R : 0 <= YO0f.le_byte v n j < 256) by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
  rewrite E. split; [|exact R].
  intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (tw_le_byte1 _ R). exact (H j Hj).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The model at its numeral offsets                                 *)
(* ------------------------------------------------------------------ *)

(* The store of S_WAKING at s + 112 (`sw a1, 0x70(s3)`, a1 = 1) as TWorldG.v tw_write states it. *)
Lemma wn_set_state_eq : forall X, TW.set_S_state X TS0.DIGINET_S_WAKING = TW.upd X (TW.OFF_g_s + 112) (TW.put 4 1).
Proof. intros X. reflexivity. Qed.

(* g_s.notify after the store of the state: the 8 bytes at s + 96 of the world before it. *)
Lemma wn_notify : forall X, length X = Z.to_nat TW.W_LEN ->
  TW.S_notify (TW.set_S_state X TS0.DIGINET_S_WAKING) = TW.u_at X (TW.OFF_g_s + 96) 8.
Proof.
  intros X LX. destruct (wk_set_state_keep X TS0.DIGINET_S_WAKING LX) as (_ & _ & _ & HN). rewrite HN.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The written ranges                                               *)
(* ------------------------------------------------------------------ *)

(* An N_STATE notice writes GOT.t[GOT.n] (0 <= GOT.n < 16) and GOT.n: bytes of [GOT, GOT + 196). *)
Lemma wn_nwr_got : forall Bw (n : TI.ntc) a, TI.n_kind n = TC.N_STATE -> notice_wr Bw n a ->
  TA_GOT <= a < TA_GOT + 196.
Proof.
  intros Bw n a K H. unfold notice_wr in H. rewrite K in H.
  destruct H as [(_ & [(Hg & Hf) | Hf]) | [(E & _) | [(E & _) | [(E & _) | [(E & _) | (E & _)]]]]];
    try (unfold TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in E; discriminate E).
  - unfold twa_fld, TW.A_GOT_t_state, TW.GOT_t_ESZ, TC.TRANS_MAX, TW.OFF_GOT in *. lia.
  - unfold twa_fld, TW.A_GOT_n, TW.OFF_GOT in Hf. lia.
Qed.

Lemma wn_nwr_G : forall Bw (n : TI.ntc) a, TI.n_kind n = TC.N_STATE -> notice_wr Bw n a -> inG TG.G_HARNESS a.
Proof.
  intros Bw n a K H. pose proof (wn_nwr_got Bw n a K H) as Hr.
  unfold inG. apply Exists_exists. exists (TA_GOT, TW.SZ_GOT).
  split; [exact (TMAP_A_in_G _ _ _ TMAP_A_GOT) | unfold in_zr, TW.SZ_GOT; cbn [fst snd]; lia].
Qed.

Ltac wn_offs :=
  unfold TA_g_s, TA_GOT, TA_M, TA_g_cmd, TA_g_q, TA_g_fail_next, TA_g_last_counter, TA_g_nq,
    TW.A_S_stats_refused, TW.A_S_e1_named_us, TW.A_S_wake_acked, TW.A_S_wake_sent_us, TW.A_S_inflight_frame,
    TW.A_S_inflight_len, TW.A_S_stats_tx_wakes, TW.A_S_inflight, TW.A_S_inflight_counter, TW.A_S_inflight_retries,
    TW.A_S_inflight_sent_us, TW.A_S_stats_tx_frames, TW.A_S_state, SENDCTL_F,
    TW.A_GOT_e2, TW.A_GOT_e3, TW.A_GOT_acks, TW.A_M_host_counter, TW.A_M_next_ka, TW.A_M_last_display,
    TW.A_M_display_sent, TW.A_M_fly_on, TW.A_M_fly_cmd, TW.A_M_fly_counter, TW.A_M_fly_retries, TW.A_M_fly_sent,
    TW.A_M_fly_len, TW.A_M_fly_frame, TC.SPEC_MAX_FRAME, TC.CMDS_MAX, TW.A_Cmd_st,
    TW.OFF_g_s, TW.OFF_GOT, TW.OFF_M, TW.OFF_g_cmd, TW.OFF_g_q, TW.OFF_g_nq, TW.OFF_g_fail_next,
    TW.OFF_g_last_counter, TW.SZ_g_q, TW.SZ_g_nq in *.

(* Every byte the call stores outside its own frames lies below 0x700000 (in the image's data). *)
Lemma wn_wr_low : forall Bw a, wake_wr Bw a -> 0 <= a < 0x700000.
Proof.
  intros Bw a H. unfold wake_wr, iosend_wr in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|(_ & [H|H])]]]]]]]]]]]]].
  15: { pose proof (wn_nwr_got Bw (wake_ntc Bw) a eq_refl H) as Hr. unfold TA_GOT in Hr. lia. }
  13: { repeat match type of H with _ \/ _ => destruct H as [H|H] end;
        try (destruct H as (s & Hs & H)); unfold twa_fld in H; wn_offs; cbv beta in H; lia. }
  all: unfold twa_fld in H; wn_offs; cbv beta in H; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. Symbolic states                                                  *)
(* ------------------------------------------------------------------ *)

(* The shadow byte of g_s.notify (s + 96); s + 104 and s + 112 have the next two. *)
Definition WN_SH : Z := 2148220740.
Lemma WN_SH_eq : WN_SH = SHADOW_OFF + (WAKE_S + 96) / 8.
Proof. reflexivity. Qed.
(* At the notice cut: s8 (atom 24) the frame's shadow address, s9 (atom 25) the frame F; s3 = s, s10 = the shadow
   base, s6 = the shadow address of s + 112 and s11 = 1 pinned. Regions: the frame's shadow bytes 4 .. 12, the
   notice's first 16 bytes, g_s.notify / g_s.notify_ctx (atoms 32 / 33) and g_s.state, and the three shadow bytes of
   s + 96 .. s + 119 (0: trans_wake_cells). *)
Definition WN_R_sh : YP09.region := YP09.mkRegion (Some 24%nat) 4 13 4 13 [].
Definition WN_R_p : YP09.region := YP09.mkRegion (Some 25%nat) 32 48 32 48 [].
Definition WN_R_gs : YP09.region :=
  YP09.mkRegion None (WAKE_S + 96) (WAKE_S + 116) (WAKE_S + 112) (WAKE_S + 116)
    [YP09.mkChunk (WAKE_S + 96) (YP09.CVal 8 (SOff 32 0)); YP09.mkChunk (WAKE_S + 104) (YP09.CVal 8 (SOff 33 0))].
Definition WN_R_shg : YP09.region :=
  YP09.mkRegion None WN_SH (WN_SH + 3) 0 0
    [YP09.mkChunk WN_SH (YP09.CVal 1 (SLit 0)); YP09.mkChunk (WN_SH + 1) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (WN_SH + 2) (YP09.CVal 1 (SLit 0))].
Definition WN_FACTS : facts :=
  mkFacts [(24%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3); (25%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition WN_REGS : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 19) (SLit WAKE_S)) (Z_to_bv 5 26) (SLit SHADOW_OFF))
    (Z_to_bv 5 22) (SLit (WN_SH + 2))) (Z_to_bv 5 27) (SLit 1).
Definition ss_wn : sstate := mkSS WAKE_NTC WN_REGS [WN_R_sh; WN_R_p; WN_R_gs; WN_R_shg] None WN_FACTS.
Definition WN_Bx : sv := SLit 0.
Definition WN_B0 : Z * Z := (0, 0).
(* After notice returns (+0x3e4): the registers as atoms, the frame's shadow bytes 4 .. 12. *)
Definition ss_wn3 : sstate := mkSS (WAKE_NTC + 0x94) sr_atoms [WN_R_sh] None
  (mkFacts [(24%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3)] [] []).

(* A byte of the shadow read as 0 is a stored 0. *)
Lemma wn_vm0 : forall (H : word -> bool) (m : word -> option byte) a,
  aview tfibsegs H m a = Some 0 -> val_mem tfibsegs (mrestrict H m) a 1 0.
Proof.
  intros H m a Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold aview in Hv. destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Hv].
  cbn in Hv. injection Hv as Hb. change (YO0f.le_byte 0 1 0) with 0.
  f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* A region with no base, kept by a step that keeps its bytes' views and presence. *)
Lemma wn_rk_none : forall E H (m m2 : word -> option byte) lo hi wlo whi cs,
  (forall a, lo <= a < hi -> aview tfibsegs H m2 a = aview tfibsegs H m a) ->
  (forall a, apresent H m a -> apresent H m2 a) ->
  region_kept tfibsegs E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion None lo hi wlo whi cs).
Proof.
  intros E H m m2 lo hi wlo whi cs Hav Hp.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
  - apply (mbyte_of_aview tfibsegs). apply Hav. lia.
  - apply writable_kept. apply Hp.
Qed.

(* A one-byte chunk of the literal 0 reads 0. *)
Lemma wn_chunk0 : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal 1 (SLit 0))) cs ->
  aview tfibsegs H m (base_val E bopt + off) = Some 0.
Proof.
  intros E H m bopt lo hi wlo whi cs off (_ & _ & _ & Hcs) Hin.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2). rewrite Z.add_0_r in Hb2. cbn [YP09.c_off] in Hb2.
  cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1. injection Hb1 as <-.
  unfold aview. rewrite Hb2. reflexivity.
Qed.

(* A chunk of w bytes of the value e reads, byte k, the k-th little-endian byte of e. *)
Lemma wn_chunk_val : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem tfibsegs (mrestrict H m) (base_val E bopt + off) (N.to_nat w)
    (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
  intros E H m bopt lo hi wlo whi cs off w e (_ & _ & _ & Hcs) Hin Hw.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  exact (val_of_chunk_any tfibsegs E _ _ off w e Hc Hw).
Qed.

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac wn_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac wn_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "wn_reg: no match for" T; fail
  end.

(* The write rights of a run from a state with the four regions of ss_wn (U24 / U25: the bases' values; EF: the
   frame's address F = frame_addr ly2 WAKE_CID pos at the journal's layout). *)
Ltac wn_awr U24 U25 EF :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  eapply awr_ok_x_cons_own with (cid := WAKE_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U24 in Ha;
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- EF; change (fs_frame_bytes WAKE_CID / 8) with 32; lia |];
  eapply awr_ok_x_cons_own with (cid := WAKE_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U25 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite <- EF; change (fs_frame_bytes WAKE_CID) with 256; lia |];
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    unfold inG; apply Exists_exists; exists (TA_g_s, TW.SZ_g_s);
    split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, WAKE_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia] |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_nil.

Section wn. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* ------------------------------------------------------------------ *)
(* 6. The current heap frame at the call of notice                     *)
(* ------------------------------------------------------------------ *)

(* TF as trans_tframe_at states it at the entry, at a later state (ly2, S2, W2, memN) of the walk whose frames are the
   entry's with the own frame on top: its bytes are kept (a block or a caller's frame outside wake_wr Bw by
   wake_apart, never G by trans_tf_off_g, the stack outside the call's window, TRANS_RO_RD by the image clause), the
   caller's frames' shadow bytes are kept (wake_wr Bw lies in the image's data), and the placements carry. *)
Lemma wn_tframe : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) memN mdN (regs regsN : bvmap 5 word)
    (TF : option TI.tframe) (Bw : list byte) cid pos,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 memN mdN ->
  frames S2 = (cid, pos) :: frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  ly_F ly2 = ly_F lyc -> ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  ly_stk_lo lyc < ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 memN (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw) ->
  trans_tf_off_g TF -> wake_apart TF Bw ->
  spZ regs - WAKE_STK <= spZ regsN - NOTICE_STK -> spZ regsN <= spZ regs ->
  trans_tframe_at B lyc Sc W memc regs WAKE_STK TF ->
  trans_tframe_at B ly2 S2 W2 memN regsN NOTICE_STK TF.
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 memN mdN regs regsN TF Bw cid pos HARc HAR2 Hfr Hperm ELF Elo Ehi
    Hstk (K1 & K2 & K3 & K4 & K5 & K6) HoffG Hap Hw1 Hw2 HT.
  destruct TF as [fr|]; [|exact I].
  destruct HT as (Ha0 & Hg8 & Hsrc & Hoff).
  set (q := TI.tf_addr fr) in *. set (n := Z.of_nat (length (TI.tf_bytes fr))) in *.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  assert (HnE : forall a, q <= a < q + n -> ~ wake_wr Bw a) by (intros a Ha Hx; exact (Hap a Hx fr eq_refl Ha)).
  assert (HnG : forall a, q <= a < q + n -> ~ inG TG.G_HARNESS a) by (intros a Ha; exact (HoffG fr eq_refl a Ha)).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hfin : forall f, In f (frames Sc) -> In f (frames S2)) by (intros f Hf; rewrite Hfr; right; exact Hf).
  assert (Efa : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
    by (intros c p; unfold frame_addr; rewrite ELF; reflexivity).
  (* the bytes of TF's range are the entry's *)
  assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) memN a = aview segs (w_H W) memc a).
  { intros a Ha. destruct Hsrc as [(bA & nA & HinA & B1 & B2) | (HL & _)].
    - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HARc HinA) as (_ & _ & _ & _ & _ & _ & Hn1).
      pose proof (req_size_pos nA (proj1 Hn1)) as [_ Hreq].
      replace a with (bA + (a - bA)) by lia.
      apply (K2 bA nA (a - bA) HinA ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
    - destruct HL as [(c & p & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
      + apply (K4 c p a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
      + exfalso. exact (HnG a Ha (HG a Ha)).
      + destruct (trans_stk_bounds B lyc Sc W memc mdc HARc) as [T1 T2].
        apply K1; [lia | unfold decode_off_win in Hoff; lia].
      + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
        apply (K3 a (trans_ro_img a Ra)); [|exact Ho | exact He].
        intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ra) as Rb.
        unfold TG.G_HARNESS_LO in Gh. lia. }
  (* the caller's frames' shadow bytes are the entry's: wake_wr lies below 0x700000 *)
  assert (KS : forall c p s, In (c, p) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8) ->
     aview segs (w_H W2) memN s = aview segs (w_H W) memc s).
  { intros c p s Hin Hs. apply (K4 c p s Hin (or_intror Hs)). intros Hw.
    pose proof (wn_wr_low Bw s Hw) as Hl.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c p HARc Hin) as (F1 & F2 & _).
    pose proof (Z.div_pos (frame_addr lyc c p) 8 ltac:(lia) ltac:(lia)).
    unfold in_zr in Hs. cbn [fst snd] in Hs. unfold shadow_addr, SHADOW_OFF in *. lia. }
  split; [exact Ha0|]. split.
  { eapply garr8_frame; [exact Hg8|]. intros a Ha. rewrite length_map in Ha. apply (mbyte_of_aview segs). apply KV. exact Ha. }
  split.
  2: { unfold decode_off_win in *. lia. }
  destruct Hsrc as [(bA & nA & HinA & B1 & B2) | (HL & Hrd)].
  - left. exists bA, nA. split; [exact (Permutation_in _ (Permutation_sym Hperm) HinA) | lia].
  - right. split.
    + destruct HL as [(c & p & Hin & F1 & F2) | [HG | [(S1 & S3) | HR]]].
      * left. exists c, p. rewrite Efa. split; [exact (Hfin _ Hin) | lia].
      * right; left; exact HG.
      * right; right; left. rewrite Elo, Ehi. lia.
      * right; right; right; exact HR.
    + destruct (Z_lt_le_dec 0 n) as [Hn | Hn].
      * destruct HL as [HF | [(HG & _) | [(S1 & S3) | (_ & Hsh)]]].
        -- exact (decode_rd_ok_fake_kept B LAWS lyc Sc W W2 memc memN mdc q n HARc HF Hrd Hn KV KS).
        -- exfalso. exact (HnG q ltac:(lia) (HG q ltac:(lia))).
        -- destruct (stack_zshadow_ra B ly2 S2 W2 memN mdN q n HAR2 Hn ltac:(lia) ltac:(lia)) as [Ha Hh].
           exact (trans_rd_ok_sh W W2 memc memN q n Hrd KV Ha Hh).
        -- destruct (Hsh ly2 S2 W2 memN mdN HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc memN q n Hrd KV Ha Hh).
      * assert (En : n = 0) by lia.
        apply (trans_rd_ok_sh W W2 memc memN q n Hrd KV); [intros x Hx; lia|].
        destruct HL as [(c & p & Hin & F1 & F2) | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
        -- assert (Hin2 : In (c, p) (frames S2)) by exact (Hfin _ Hin).
           destruct (al_frames _ _ LAWS ly2 S2 W2 memN mdN c p HAR2 Hin2) as (_ & _ & _ & HFsh).
           destruct (TransportGCg.dkg_frame_al64 segs B ly2 S2 W2 memN mdN c p HAR2 Hin2) as (A1 & A2 & A3).
           destruct (frames_bounds segs B LAWS ly2 S2 W2 memN mdN c p HAR2 Hin2) as (G1 & G2 & _).
           rewrite Efa in A1, G1, G2, HFsh.
           apply (wn_hull_in _ (frame_addr lyc c p) (fs_frame_bytes c) q n); try lia.
           intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
        -- exact (proj2 (Hsh ly2 S2 W2 memN mdN HAR2)).
        -- destruct (Z_lt_le_dec q (ly_stk_hi lyc)) as [Hq | Hq].
           ++ destruct (stack_zshadow_ra B ly2 S2 W2 memN mdN q 1 HAR2 ltac:(lia) ltac:(lia) ltac:(lia)) as [_ Hh].
              exact (trans_hull_sub _ q 1 q n Hh ltac:(lia) ltac:(lia)).
           ++ destruct (stack_zshadow_ra B ly2 S2 W2 memN mdN (q - 1) 1 HAR2 ltac:(lia) ltac:(lia) ltac:(lia))
                as [_ Hh].
              exact (trans_hull_sub _ (q - 1) 1 q n Hh ltac:(lia) ltac:(lia)).
        -- exact (proj2 (Hsh ly2 S2 W2 memN mdN HAR2)).
Qed.

(* ------------------------------------------------------------------ *)
(* 7. The entry states of the runs                                     *)
(* ------------------------------------------------------------------ *)

(* The valuation of runs 1 and 2: the registers at the cut, then g_s.notify and g_s.notify_ctx of the world X. *)
Definition wn_vals (X : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 96) 8); Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 104) 8)].
Definition wn_E (regs : bvmap 5 word) (X : list byte) : env := Eimg (PI := PI_transport) (Ereg regs (wn_vals X)).

Lemma wn_entry0 : forall ly S (W : world segs) regs mem md X F,
  trans_wake_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) X ->
  YK11.getr regs 24 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 25 = w64 F ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= 2 ^ 47 -> in_app F 256 ->
  (F + 256 <= WAKE_S \/ WAKE_S + TW.SZ_g_s <= F) ->
  (forall a, F + 32 <= a < F + 48 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (wn_E regs X) (mkSS WAKE_NTC sr_atoms [WN_R_sh; WN_R_p; WN_R_gs; WN_R_shg] None WN_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + WAKE_NTC)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md X F HSC HAR Htw R24 R25 HF0 HF64 HFc HFapp HFG Hpf Hpsh.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64)) by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (Hg : 64 <= F / 64 * 64) by lia.
  set (E := wn_E regs X).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, wn_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF + F / 8)
    by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U25 : bv_unsigned (ew E 25) = F)
    by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (wn_vals X) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, wn_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  cbn [Nat.add nth wn_vals] in E32, E33.
  pose proof (TWL.u_at_range X (TW.OFF_g_s + 96) 8) as R32.
  pose proof (TWL.u_at_range X (TW.OFF_g_s + 104) 8) as R33.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32, R33.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZSH : forall j, (j < 3)%nat -> val_mem segs (mrestrict (w_H W) mem) (WN_SH + Z.of_nat j) 1 0).
  { intros j Hj. apply wn_vm0.
    replace (WN_SH + Z.of_nat j) with (FCells.shadow_addr (WAKE_S + 96 + 8 * Z.of_nat j)).
    - apply (decode_zshadow_rd B ly S W mem md WAKE_S (WAKE_S + TW.SZ_g_s) _ HAR); [| | | exact HSC].
      + unfold WAKE_S, TA_g_s. rewrite Z.add_mod, Z.mul_comm, Z.mod_mul by lia. reflexivity.
      + lia.
      + unfold TW.SZ_g_s. lia.
    - unfold FCells.shadow_addr, FCells.ASAN_K, WN_SH, WAKE_S, TA_g_s.
      replace (6158784 + 96 + 8 * Z.of_nat j) with ((769860 + Z.of_nat j) * 8) by lia.
      rewrite Z.div_mul by lia. lia. }
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks WN_R_sh WN_R_p WN_R_gs WN_R_shg
        base_val]; rewrite ?U24, ?U25.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
    + split; [unfold WAKE_S, TA_g_s; lia|]. split; [unfold WAKE_S, TA_g_s; lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
        unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
        split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, WAKE_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
      * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val segs E _ 0 (WAKE_S + 96) 8 (SOff 32 0) (TW.u_at X (TW.OFF_g_s + 96) 8));
             [apply DEN; [exact E32 | exact R32] | exact R32 | unfold WAKE_S, TA_g_s; lia |].
           replace (0 + (WAKE_S + 96)) with (TA_g_s + 96) by (unfold WAKE_S; lia).
           exact (tw_read_val segs _ TMAP_A X TW.OFF_g_s TA_g_s TW.SZ_g_s 96 8 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ 0 (WAKE_S + 104) 8 (SOff 33 0) (TW.u_at X (TW.OFF_g_s + 104) 8));
             [apply DEN; [exact E33 | exact R33] | exact R33 | unfold WAKE_S, TA_g_s; lia |].
           replace (0 + (WAKE_S + 104)) with (TA_g_s + 104) by (unfold WAKE_S; lia).
           exact (tw_read_val segs _ TMAP_A X TW.OFF_g_s TA_g_s TW.SZ_g_s 104 8 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold WN_SH, SHADOW_OFF, WAKE_S, TA_g_s; lia|]. split; [unfold WN_SH, SHADOW_OFF, WAKE_S, TA_g_s; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 WN_SH 1 (SLit 0) 0); [reflexivity | lia | unfold WN_SH, SHADOW_OFF, WAKE_S, TA_g_s; lia |].
        rewrite Z.add_0_l. pose proof (ZSH 0%nat ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0. exact Z0.
      * apply (chunk_ok_val segs E _ 0 (WN_SH + 1) 1 (SLit 0) 0); [reflexivity | lia | unfold WN_SH, SHADOW_OFF, WAKE_S, TA_g_s; lia |].
        rewrite Z.add_0_l. exact (ZSH 1%nat ltac:(lia)).
      * apply (chunk_ok_val segs E _ 0 (WN_SH + 2) 1 (SLit 0) 0); [reflexivity | lia | unfold WN_SH, SHADOW_OFF, WAKE_S, TA_g_s; lia |].
        rewrite Z.add_0_l. exact (ZSH 2%nat ltac:(lia)).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, WN_R_sh, WN_R_p, WN_R_gs, WN_R_shg.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U24, U25.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, WN_SH, SHADOW_OFF, WAKE_S, TA_g_s, TW.SZ_g_s in *.
    rewrite HF8. repeat split; first [exact I | lia].
  - unfold WN_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U24, U25.
    change (2 ^ 3) with 8. change (2 ^ 6) with 64.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma wn_entry : forall ly S (W : world segs) regs mem md X F,
  trans_wake_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) X ->
  YK11.getr regs 24 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 25 = w64 F ->
  YK11.getr regs 19 = w64 WAKE_S -> YK11.getr regs 26 = w64 SHADOW_OFF -> YK11.getr regs 22 = w64 (WN_SH + 2) ->
  YK11.getr regs 27 = w64 1 ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= 2 ^ 47 -> in_app F 256 ->
  (F + 256 <= WAKE_S \/ WAKE_S + TW.SZ_g_s <= F) ->
  (forall a, F + 32 <= a < F + 48 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (wn_E regs X) ss_wn
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + WAKE_NTC)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md X F HSC HAR Htw R24 R25 R19 R26 R22 R27 HF0 HF64 HFc HFapp HFG Hpf Hpsh.
  rewrite restrict_mkst_fx.
  pose proof (wn_entry0 ly S W regs mem md X F HSC HAR Htw R24 R25 HF0 HF64 HFc HFapp HFG Hpf Hpsh) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 19) WAKE_S H0 R19 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 26) SHADOW_OFF H1 R26 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 22) (WN_SH + 2) H2 R22 eq_refl) as H3.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 27) 1 H3 R27 eq_refl) as H4.
  exact H4.
Qed.

(* The symbolic state at +0x3e4 (after notice returns). *)
Lemma wn_entry3 : forall (W : world segs) regs mem F,
  YK11.getr regs 24 = w64 (SHADOW_OFF + F / 8) -> 4096 <= F -> F mod 64 = 0 -> F + 256 <= 2 ^ 47 ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) ss_wn3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (WAKE_NTC + 0x94))) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F R24 HF0 HF64 HFc Hpsh.
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64)) by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  set (E := Eimg (PI := PI_transport) (Ereg regs [])).
  assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF + F / 8)
    by (unfold E; rewrite (ew_Eimg_Ereg_nat regs [] 24 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small;
        unfold SHADOW_OFF; lia).
  rewrite restrict_mkst_fx. unfold ss_wn3.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks WN_R_sh base_val]. rewrite U24.
    split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U24. change (2 ^ 3) with 8.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 8. The notice at p, its apartness, and what a run keeps             *)
(* ------------------------------------------------------------------ *)

(* The bytes the piece may change between the cut and the call of notice: the notice's shadow bytes 4 .. 12, the
   notice's 72 bytes, g_s.state, and the stack window of __asan_memset below sp1. *)
Definition wn_Z (F sp1 : Z) (x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) \/ (F + 32 <= x < F + 104) \/
  (WAKE_S + 112 <= x < WAKE_S + 116) \/ (sp1 - ESTACK <= x < sp1).

(* A store of w bytes of a register holding v leaves v's low w bytes. *)
Lemma wn_vm_w : forall (m : word -> option byte) a (w : N) v, Z.of_N w <= 8 ->
  val_mem segs m a (N.to_nat w) (bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_N w)) -> val_mem segs m a (N.to_nat w) v.
Proof.
  intros m a w v Hw H.
  assert (Hd : (2 ^ (8 * Z.of_N w) | 2 ^ 64)).
  { exists (2 ^ (64 - 8 * Z.of_N w)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (E : (bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_N w)) mod 2 ^ (8 * Z.of_N w) = v mod 2 ^ (8 * Z.of_N w)).
  { rewrite Zmod_mod, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    apply Z.mod_mod_divide; try exact Hd; try (apply Z.pow_nonzero; lia); try (apply Z.pow_pos_nonneg; lia). }
  intros k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite N_nat_Z, E. reflexivity.
Qed.

(* The 72 bytes of the notice at p = F + 32: the store of 0x0000000100000002 (8 bytes), old and 1 (4 bytes each), and
   the memset's 56 zeros, read as WalkNotify.v ntc_state_bytes (state S_WAKING = 1, reason R_WAKE = 1). *)
Lemma wn_nb : forall (H : word -> bool) (m : word -> option byte) F old,
  val_mem segs (mrestrict H m) (F + 32) 8 4294967298 ->
  val_mem segs (mrestrict H m) (F + 40) 4 old ->
  val_mem segs (mrestrict H m) (F + 44) 4 1 ->
  (forall a, F + 48 <= a < F + 104 -> aview segs H m a = Some 0) ->
  garr8 segs (mrestrict H m) (F + 32) (map DSpec.bz (WN.ntc_state_bytes 1 old 1)).
Proof.
  intros H m F old V0 V8 V12 Z0.
  assert (Ep : TW.put 4 2 ++ TW.put 4 1 = TW.put 8 4294967298) by (apply wn_bytes_eq; vm_compute; reflexivity).
  unfold WN.ntc_state_bytes. rewrite app_assoc, Ep.
  rewrite !map_app. apply garr8_app. split; [exact (wn_garr8_val segs _ _ 8 4294967298 V0) |].
  rewrite length_map, TWL.length_put. replace (F + 32 + Z.of_nat 8) with (F + 40) by lia.
  apply garr8_app. split; [exact (wn_garr8_val segs _ _ 4 old V8) |].
  rewrite length_map, TWL.length_put. replace (F + 40 + Z.of_nat 4) with (F + 44) by lia.
  apply garr8_app. split; [exact (wn_garr8_val segs _ _ 4 1 V12) |].
  rewrite length_map, TWL.length_put. replace (F + 44 + Z.of_nat 4) with (F + 48) by lia.
  rewrite map_repeat. change (DSpec.bz (DSpec.b8 0)) with 0.
  apply garr8_zeros. intros a Ha.
  pose proof (Z0 a ltac:(lia)) as Za. unfold aview in Za.
  destruct (YP09.mbyte segs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Za].
  cbn in Za. injection Za as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* The notice at p = F + 32, as notice's statement reads it (check_state_data_cg.v trans_ntc_at). *)
Lemma wn_ntc_at : forall ly2 S2 (W2 : world segs) memN mdN (regsC : bvmap 5 word) Bw F pos,
  AR_laws segs B -> @AR rc segs B ly2 S2 W2 memN mdN -> In (WAKE_CID, pos) (frames S2) ->
  F = frame_addr ly2 WAKE_CID pos -> 4096 <= F -> F mod 64 = 0 -> F + 256 <= alloc_ceiling -> in_app F 256 ->
  F + 256 <= spZ regsC - NOTICE_STK ->
  (forall i, 4 <= i < 13 -> aview segs (w_H W2) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  garr8 segs (mrestrict (w_H W2) memN) (F + 32) (map DSpec.bz (WN.ntc_state_bytes 1 (TW.S_state Bw) 1)) ->
  trans_ntc_at B ly2 S2 W2 memN regsC NOTICE_STK (F + 32) (wake_ntc Bw).
Proof.
  intros ly2 S2 W2 memN mdN regsC Bw F pos LAWS HAR Hin EF HF0 HF64 HFc HFapp Hwin ZS HNB.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_frames _ _ LAWS ly2 S2 W2 memN mdN WAKE_CID pos HAR Hin) as (_ & _ & HFb & HFsh).
  rewrite <- EF in HFb, HFsh. change (fs_frame_bytes WAKE_CID) with 256 in HFb.
  change (fs_frame_bytes WAKE_CID / 8) with 32 in HFsh. change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh.
  assert (DFm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  set (old := TW.S_state Bw) in *.
  assert (Hold : - 2 ^ 31 <= old < 2 ^ 31) by (unfold old, TW.S_state; apply TWL.s32_range).
  unfold trans_ntc_at.
  split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
  split.
  { right. split.
    - left. exists WAKE_CID, pos. split; [exact Hin|]. rewrite <- EF. change (fs_frame_bytes WAKE_CID) with 256.
      unfold NTC_SIZE. lia.
    - unfold decode_rd_ok, NTC_SIZE. split; [|split; [|split; [|split; [|split]]]].
      + intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
      + apply (wn_ra_zero _ F (F + 32) 72 4 13); [lia | exact DFm8 | lia | lia | exact ZS].
      + apply (wn_hull_in _ F 256 (F + 32) 72); [lia | exact HF64 | reflexivity | lia | lia | lia | lia |].
        intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
      + apply (amem_range_sub_app F 256); [exact HFapp | lia | lia | lia | lia].
      + lia.
      + lia. }
  split; [left; unfold NTC_SIZE; lia|].
  exists (WN.ntc_state_bytes 1 old 1).
  split; [exact HNB|].
  unfold wake_ntc. fold old.
  cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len TI.n_counter TI.n_retry
    TI.n_body TI.n_ann length].
  unfold WN.ntc_state_bytes, TW.s32_at.
  assert (Z0 : TW.u_at (TW.put 4 2 ++ TW.put 4 1 ++ TW.put 4 old ++ TW.put 4 1 ++ repeat (DSpec.b8 0) 56) 48 8 = 0)
    by WN.ntc_field.
  rewrite Z0.
  split; [rewrite ?length_app, ?TWL.length_put, ?repeat_length; reflexivity |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field; apply WN.swrap32_mod; exact Hold |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [apply garr8_nil |].
  split; [exact (trans_src_ok_null B ly2 S2 W2 memN) |].
  split; [left; lia |].
  WN.ntc_field.
Qed.

(* notice's stores (an N_STATE notice at the world X with GOT_n X = GOT_n Bw: bytes of GOT, of wake_wr Bw on this
   path) are apart from the notice's own bytes (a frame is not image), from its empty body, and from TF (wake_apart). *)
Lemma wn_apart : forall ly2 S2 (W2 : world segs) mem2 md2 (Wn : world segs) memN (TF : option TI.tframe) Bw X F pos,
  AR_laws segs B -> @AR rc segs B ly2 S2 W2 mem2 md2 -> In (WAKE_CID, pos) (frames S2) ->
  F = frame_addr ly2 WAKE_CID pos ->
  wake_apart TF Bw -> TW.S_state Bw <> TS0.DIGINET_S_WAKING -> TW.GOT_n X = TW.GOT_n Bw ->
  notice_apart Wn memN (F + 32) (wake_ntc Bw) TF X.
Proof.
  intros ly2 S2 W2 mem2 md2 Wn memN TF Bw X F pos LAWS HAR Hin EF Hap Hst HGn x Hx.
  assert (Hx' : notice_wr Bw (wake_ntc Bw) x) by (unfold notice_wr in Hx |- *; rewrite HGn in Hx; exact Hx).
  assert (Hw : wake_wr Bw x) by (unfold wake_wr; do 13 right; split; [exact Hst | right; exact Hx']).
  split; [|split].
  - intros Hr. apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 WAKE_CID pos x HAR Hin);
      [rewrite <- EF; change (fs_frame_bytes WAKE_CID) with 256; unfold NTC_SIZE in Hr; lia|].
    exact (trans_g_img x (wn_nwr_G Bw (wake_ntc Bw) x eq_refl Hx')).
  - intros NB _ _. split.
    + unfold wake_ntc. cbn [TI.n_body length Z.of_nat]. lia.
    + intros Hn. exfalso. apply Hn. reflexivity.
  - intros fr Hfr. exact (Hap x Hw fr Hfr).
Qed.

(* One step of the walk keeps the caller's memory when each byte it may change is in the call's stack window, in the
   own frame of class WAKE_CID (its bytes, its shadow, its flag byte) or in G: TransportGFrame.v dk_kept_step_gw with
   the own frame's separation facts (dkg_nf_sep_gw) at a current state (ly2, S2) and world W1. *)
Lemma wn_kept_w : forall lyc Sc ly2 S2 (W W1 : world segs) memc mdc mem2 md2 memX memY slo shi pos F FL
    (Eo Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS -> frame_flag_lawP segs B ->
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W1 mem2 md2 ->
  frames S2 = (WAKE_CID, pos) :: frames Sc -> (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  ly_F ly2 = ly_F lyc -> F = frame_addr lyc WAKE_CID pos -> FL = flag_addr lyc WAKE_CID pos ->
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  (forall a, Zs a -> (slo <= a < shi) \/ dkg_nf WAKE_CID F FL a \/ inG TG.G_HARNESS a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W1 memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W1) memY a = aview segs (w_H W1) memX a) ->
  (forall a, apresent (w_H W1) memX a -> apresent (w_H W1) memY a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W1 memY slo shi Eo.
Proof.
  intros lyc Sc ly2 S2 W W1 memc mdc mem2 md2 memX memY slo shi pos F FL Eo Zs LAWS HG FFL HARc HAR2 Hfrs Hbl ELF EF
    EFL Hce Hshi HZ KP Hkp Hgr.
  destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W1 mem2 md2 WAKE_CID pos F FL HAR2 Hfrs Hbl ELF
    EF EFL FFL) as (N1 & N2 & N3 & N4).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (dk_kept_step_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc W1 memX memY slo shi Eo Zs HARc
    KP Hkp Hgr).
  - intros a Ha Hc. destruct (HZ a Ha) as [Hw | [Hn | Hg]]; [exact Hw | pose proof (N4 a Hn); lia |].
    pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HG Hg). unfold kLowMemEnd in *. lia.
  - intros b m i Hb Hi Ha. exfalso. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HARc Hb) as (_ & H4096 & Hbc & _).
    destruct (HZ _ Ha) as [Hw | [Hn | Hg]]; [lia | exact (N1 b m i Hb Hi Hn) |].
    destruct (HG _ Hg) as [Hi' _]. exact (blk_img segs B LAWS lyc Sc W memc mdc b m (b + i) HARc Hb ltac:(lia) Hi').
  - intros a Ha Hi HnG _ _. exfalso. pose proof (transport_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    destruct (HZ a Ha) as [Hw | [Hn | Hg]]; [lia | exact (N2 a Hn Hi) | exact (HnG Hg)].
  - intros cid pos' a Hin Hr Ha. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos' HARc Hin) as (G4096 & Gce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct (HZ a Ha) as [Hw | [Hn | Hg]].
    + destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos') (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos' + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
    + exact (N3 cid pos' a Hin Hr Hn).
    + destruct (HG _ Hg) as [Hi _]. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HG Hg) as Hl.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
      * exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos' a HARc Hin Hr Hi).
      * pose proof (Z.div_pos (frame_addr lyc cid pos') 8 ltac:(lia) ltac:(lia)).
        unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 9. The piece                                                        *)
(* ------------------------------------------------------------------ *)

Lemma wake_ntc_pc : @wake_ntc_stmt fx rc B MT.
Proof.
unfold wake_ntc_stmt. intros HE2. unfold wake_ntc_at.
intros LAWS0 HMS HN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' B1 e2 pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HSC & HGU & HGN & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm & HTF & HTFG &
  Hrom & Hapart & Hfly & Hcmd & Hcnt & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & HL2 & Htw1 & Hst3 & Hst & HGn &
  HNT & HNM & Hgf' & Hr0).
pose proof HTFG as HoffG.
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R24 & R25) & R19 & R21 & R22 & R23 & R26 & R27).
set (X := wake_w3 B1 e2 now) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold WAKE_FBYTES in HFc, HFapp, HFLw.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite ?Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _ & _ & _ & ESLO & ESHI & _).
pose proof HJ1 as (_ & _ & (memS1 & HJi1 & _) & _).
pose proof HJi1 as (_ & Hlyle2 & _).
pose proof Hlyle2 as (_ & _ & _ & _ & _ & ELF2 & _ & _ & _ & ESLO2 & ESHI2 & _).
clear HJi1 memS1.
assert (ESLO2c : ly_stk_lo ly2 = ly_stk_lo lyc) by (rewrite ESLO2, ESLO; reflexivity).
assert (ESHI2c : ly_stk_hi ly2 = ly_stk_hi lyc) by (rewrite ESHI2, ESHI; reflexivity).
destruct wake_stk_bounds as (WB1 & WB2 & WB3 & WB4 & WB5 & WB6).
assert (EST : ESTACK = 4096) by reflexivity.
assert (HSTKLT : ly_stk_lo lyc < ly_stk_hi lyc) by (rewrite ESLO, ESHI; lia).
assert (Hsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold WAKE_FRAME.
  pose proof (Z.div_mod (spZ regs - 128) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 128) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 128) / 32) in *. set (r0 := (spZ regs - 128) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hin : In (WAKE_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Efa2 : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite HlyF; reflexivity).
assert (EF2 : F = frame_addr ly2 WAKE_CID pos) by (rewrite Efa2; exact EF).
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 WAKE_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
rewrite <- EF2 in HFb, HFsh.
change (fs_frame_bytes WAKE_CID) with 256 in HFb. change (fs_frame_bytes WAKE_CID / 8) with 32 in HFsh.
set (FL := flag_addr lyc WAKE_CID pos) in *.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
assert (HFG : F + 256 <= WAKE_S \/ WAKE_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 256) WAKE_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (WAKE_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, F <= x < F + 256 /\ WAKE_S <= x < WAKE_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F WAKE_S) as [h3|h3]; [exists WAKE_S | exists F]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2).
  apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 WAKE_CID pos x HAR2 Hin);
    [rewrite <- EF2; change (fs_frame_bytes WAKE_CID) with 256; lia|].
  apply trans_g_img. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
  split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, WAKE_S in *; cbn [fst snd]; lia]. }
(* the model's facts on this path *)
assert (LX : length X = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw1).
assert (R22' : YK11.getr regs2 22 = w64 (WN_SH + 2)) by (rewrite R22; reflexivity).
(* +0x350 .. +0x384: s4 = p, shadow bytes 4 .. 12 := 0, the memset's arguments, `jal __asan_memset` *)
pose proof (wn_entry ly2 S2 W2 regs2 mem2 md2 X F HSC HAR2 Htw1 R24 R25 R19 R26 R22' R27 HF0 HF64 ltac:(lia) HFapp HFG
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia))))) as HS.
set (E0 := wn_E regs2 X) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, wn_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r' Hn; unfold E0, wn_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (U24 : bv_unsigned (ew E0 24) = SHADOW_OFF + F / 8)
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U25 : bv_unsigned (ew E0 25) = F)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs WN_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ1 SHOK WN_B0.
{ wn_awr U24 U25 EF2. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ wn_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (wn_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta.
  wn_win Hiw Hx ltac:(rewrite ?U24, ?U25 in Hx; unfold wn_Z, WAKE_S, TA_g_s;
    first [lia | left; lia | right; left; lia | right; right; left; lia]). }
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
assert (ZS1 : forall i, 4 <= i < 13 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U24.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (wn_chunk0 E0 (w_H W2) (ms_mem ms) (Some 24%nat) _ _ _ _ _ _ RG0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
clear HF HFr HG RG0.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
destruct (al_frames _ _ LAWS ly2 S2 W2 (ms_mem ms) md1 WAKE_CID pos HAR1 Hin) as (_ & _ & HFb1 & HFsh1).
rewrite <- EF2, ESH in HFsh1. change (fs_frame_bytes WAKE_CID / 8) with 32 in HFsh1.
pmkst HS.
wn_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 48)) Q10 ltac:(cbn [sv_denot]; rewrite U25; reflexivity).
wn_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
wn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 56) Q12 ltac:(reflexivity).
wn_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
wn_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 22560)) Q1 ltac:(apply codeptr_val; exact HEI).
wn_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
wn_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
assert (QSP : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* +0x384: __asan_memset (p + 16, 0, 56), through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet (transport_sigma TS___asan_memset)
    (HMS fx) TG.G_HARNESS W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 ((WAKE_CID, pos) :: own) ly2 S2 md1
    (k + e) (F + 48) 0 56 (sp1 - sp0) (Z_to_bv 64 (BASE + 22560)) HGX G_HARNESS_rw HJ1 Q10 Q11 Q12).
  - lia.
  - lia.
  - lia.
  - rewrite QSP. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    destruct Hsp1 as (_ & M1). rewrite M1, Z.add_0_r in D1. rewrite Hsp0a, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
    apply Z.mod_mul. lia.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ1|]. intros a Ha. left. rewrite QSP. split.
    + unfold awr_byte. right; right; right. unfold in_frames. exists WAKE_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite <- EF2. change (fs_frame_bytes WAKE_CID) with 256. lia.
    + lia.
  - apply (amem_range_sub_app F 256); [exact HFapp | lia | lia | lia | lia].
  - apply (wn_ra_zero _ F (F + 48) 56 6 13); [lia | exact DFm8 | lia | lia |].
    intros i Hi. exact (ZS1 i ltac:(lia)).
  - intros _. apply (wn_hull_in _ F 256 (F + 48) 56); [lia | exact HF64 | reflexivity | lia | lia | lia | lia |].
    intros i Hi. apply can_aview_vis. exact (proj1 (HFsh1 i Hi)).
  - exact I. }
cbv beta. intros Wm c2 _ (-> & regsM & memM & mdM & -> & HJ2 & HPM & HA0M & HsetM & HeffM & HgrM).
assert (DF8 : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 8 ltac:(lia)) as D; rewrite DFm8, Z.add_0_r in D; exact D).
assert (HSHF : SHADOW_OFF + F / 8 + 32 <= F \/ F + 256 <= SHADOW_OFF + F / 8).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia. }
assert (HACE : alloc_ceiling <= sp1 - NOTICE_STK) by lia.
assert (KAM : forall a, 0 <= a < 2 ^ 64 -> ~ wn_Z F sp1 a ->
  aview segs (w_H W2) memM a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite HeffM; [exact (KR1 a Ha Hn) | exact Ha | |].
  - intros Hd. apply Hn. right. left. lia.
  - intros Hd. apply Hn. right. right. right. lia. }
assert (GAM : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memM a) by (intros a Ha; exact (HgrM a (GA1 a Ha))).
jafter_call_keep_hi HS 1024%nat regsM (mrestrict (w_H W2) memM) HPM [0%nat; 1%nat; 2%nat; 3%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 24%nat (SHADOW_OFF + F / 8)); [exact U24 | | exact HgrM].
    intros a Ha. unfold SHADOW_OFF in *. apply HeffM; [lia | destruct HSHF; lia | lia].
  - apply (region_kept_aview _ _ _ _ 25%nat F); [exact U25 | | exact HgrM].
    intros a Ha. apply HeffM; lia.
  - apply wn_rk_none; [| exact HgrM]. intros a Ha. unfold WAKE_S, TA_g_s in *.
    apply HeffM; [lia | destruct HFG; unfold WAKE_S, TA_g_s, TW.SZ_g_s in *; lia | lia].
  - apply wn_rk_none; [| exact HgrM]. intros a Ha. unfold WN_SH in *.
    apply HeffM; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
      destruct HFapp as (_ & [HL | (HH1 & HH2)]); lia | lia]. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regsM) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (U24b : bv_unsigned (ew E1 24) = SHADOW_OFF + F / 8) by (rewrite E1lo by lia; exact U24).
assert (U25b : bv_unsigned (ew E1 25) = F) by (rewrite E1lo by lia; exact U25).
assert (SHOK1 : sh_ok segs WN_Bx (@nil shent) E1 (mrestrict (w_H W2) memM)) by constructor.
assert (ZMM : forall a, F + 48 <= a < F + 104 -> aview segs (w_H W2) memM a = Some 0).
{ intros a Ha. replace a with ((F + 48) + (a - (F + 48))) by lia. rewrite (HsetM (a - (F + 48)) ltac:(lia)). reflexivity. }
clear dependent ms.
(* +0x388 .. +0x3e0: the notice's first 16 bytes, the checked store of 1 at s + 112, the checked loads at s + 96 and
   s + 104, up to `jalr a2` *)
paj_run_tok RUN HS HJ2 SHOK1 WN_B0.
{ wn_awr U24b U25b EF2. }
set (md3 := with_vm_backing (m_vm_lazy mdM) mat mdM) in *. clearbody md3. clear mat.
assert (KRN : forall a, 0 <= a < 2 ^ 64 -> ~ wn_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) memM a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (wn_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta.
  wn_win Hiw Hx ltac:(rewrite ?U24b, ?U25b in Hx; unfold wn_Z, WAKE_S, TA_g_s;
    first [lia | left; lia | right; left; lia | right; right; left; lia]). }
assert (ZMN : forall a, F + 48 <= a < F + 104 -> aview segs (w_H W2) (ms_mem ms) a = Some 0).
{ intros a Ha. rewrite <- (ZMM a Ha).
  apply (kept_of_frame _ _ _ _ _ (fun x => (F + 32 <= x < F + 48) \/ (WAKE_S + 112 <= x < WAKE_S + 116) \/
    (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13)) HFr); [| lia |].
  - intros b wlo whi x Hiw Hx. cbv beta.
    wn_win Hiw Hx ltac:(rewrite ?U24b, ?U25b in Hx; unfold WAKE_S, TA_g_s;
      first [lia | left; lia | right; left; lia | right; right; lia]).
  - cbv beta. unfold WAKE_S, TA_g_s, SHADOW_OFF, TW.SZ_g_s in *.
    intros [Hx | [Hx | Hx]]; [lia | destruct HFG as [Hg | Hg]; lia | destruct HSHF as [Hg | Hg]; lia]. }
assert (KAN : forall a, 0 <= a < 2 ^ 64 -> ~ wn_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a)
  by (intros a Ha Hn; rewrite (KRN a Ha Hn); exact (KAM a Ha Hn)).
assert (GAN : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAM a Ha))).
clear HF HFr HG.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RS1.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RS2.
cbn [ms_mem restrict] in RS0, RS1, RS2.
assert (ZSN : forall i, 4 <= i < 13 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U24b.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (wn_chunk0 E1 (w_H W2) (ms_mem ms) (Some 24%nat) _ _ _ _ _ _ RS0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
set (old := TW.S_state Bw) in *.
assert (Hold : - 2 ^ 31 <= old < 2 ^ 31) by (unfold old, TW.S_state; apply TWL.s32_range).
assert (D23 : sv_denot E1 (SOff 23 0) = Z_to_bv 64 old).
{ cbn [sv_denot]. rewrite E1lo by lia. rewrite (EE 23%nat 23%bv eq_refl), R23. unfold w64.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (wn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 32 8 (SLit 4294967298) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP0.
pose proof (wn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 40 4 (SOff 23 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP8.
pose proof (wn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 44 4 (SLit 1) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP12.
pose proof (wn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 6158896 4 (SLit 1) RS2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG.
cbn [base_val] in VP0, VP8, VP12, VG. rewrite U25b in VP0, VP8, VP12. rewrite D23 in VP8.
change (N.to_nat 8) with 8%nat in VP0. change (N.to_nat 4) with 4%nat in VP8, VP12, VG.
change (bv_unsigned (sv_denot E1 (SLit 4294967298)) mod 2 ^ (8 * Z.of_N 8)) with 4294967298 in VP0.
change (bv_unsigned (sv_denot E1 (SLit 1)) mod 2 ^ (8 * Z.of_N 4)) with 1 in VP12, VG.
apply (wn_vm_w _ _ 4 old ltac:(lia)) in VP8.
change (N.to_nat 4) with 4%nat in VP8.
pose proof (wn_nb (w_H W2) (ms_mem ms) F old VP0 VP8 VP12 ZMN) as HNB.
(* what the call kept, from its entry to the call of notice *)
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 WAKE_CID pos F FL HAR2 Hfrs Hbl HlyF
  EF eq_refl FFL) as (N1 & N2 & N3 & N4).
assert (NZG : forall x, inG TG.G_HARNESS x -> ~ (WAKE_S + 112 <= x < WAKE_S + 116) -> ~ wn_Z F sp1 x).
{ intros x Hx Hn Hz. pose proof (inG_low segs B transport_segs_low _ x HGX Hx) as Hl. unfold kLowMemEnd in Hl.
  destruct Hz as [Hz | [Hz | [Hz | Hz]]].
  - unfold SHADOW_OFF in Hz. lia.
  - apply (N2 x); [left; change (fs_frame_bytes WAKE_CID) with 256; lia | exact (trans_g_img x Hx)].
  - exact (Hn Hz).
  - lia. }
assert (HSZ : forall a, wn_Z F sp1 a ->
  (spZ regs - WAKE_STK <= a < spZ regs) \/ dkg_nf WAKE_CID F FL a \/ inG TG.G_HARNESS a).
{ intros a [Hz | [Hz | [Hz | Hz]]].
  - right; left; right; left. change (fs_frame_bytes WAKE_CID / 8) with 32. lia.
  - right; left; left. change (fs_frame_bytes WAKE_CID) with 256. lia.
  - right; right. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
    split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, WAKE_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
  - left; lia. }
pose proof (wn_kept_w lyc Sc ly2 S2 W W2 memc mdc mem2 md2 mem2 (ms_mem ms) (spZ regs - WAKE_STK) (spZ regs) pos F FL
  (wake_wr Bw) (wn_Z F sp1) LAWS HGX FFL HARc HAR2 Hfrs Hbl HlyF EF eq_refl ltac:(lia) ltac:(lia) HSZ HK KAN GAN)
  as KCN.
(* the registers at `jalr a2` *)
assert (E32 : ew E1 32 = Z_to_bv 64 (TI.ti_notice timg_A)).
{ rewrite E1lo by lia. unfold E0, wn_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  pose proof (ew_Ereg_extra regs2 (wn_vals X) 0) as Xv. cbn [Nat.add nth wn_vals] in Xv. rewrite Xv.
  rewrite <- (wn_notify X LX), HNT. reflexivity. }
wn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 (TI.ti_notice timg_A)) T12
  ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
wn_reg HS (Z_to_bv 5 11) (w64 (F + 32)) T11 ltac:(cbn [sv_denot]; rewrite U25b; reflexivity).
wn_reg HS (Z_to_bv 5 2) (w64 sp1) T2
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
wn_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) T3
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R3 Hgp)).
wn_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) T4
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R4 Htp)).
wn_reg HS (Z_to_bv 5 8) (YK11.getr regs2 (Z_to_bv 5 8)) T8
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
wn_reg HS (Z_to_bv 5 9) (YK11.getr regs2 (Z_to_bv 5 9)) T9
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
wn_reg HS (Z_to_bv 5 18) (YK11.getr regs2 (Z_to_bv 5 18)) T18
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
wn_reg HS (Z_to_bv 5 24) (YK11.getr regs2 (Z_to_bv 5 24)) T24
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
wn_reg HS (Z_to_bv 5 25) (YK11.getr regs2 (Z_to_bv 5 25)) T25
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
(* +0x3e0: `jalr a2`, a2 = notice *)
assert (P4 : 0 <= TI.ti_notice timg_A < 2 ^ 64) by (rewrite (proj1 notice_at); lia).
assert (P5 : TI.ti_notice timg_A mod 2 = 0) by (rewrite (proj1 notice_at); reflexivity).
eapply (SRr_jalr_call_pi (PL := PL_transport) (PI := PI_transport) W2 E1 _ _ _ _ 0x600e7 (1%bv : bv 5) (12%bv : bv 5)
  (TI.ti_notice timg_A) HEI1 HS eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact T12 | exact P4 | exact P5 |].
intros matC ms1 Ems1 _. subst ms1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  set (regsC := rg); set (mdC := mdx);
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_notice timg_A) regsC (ms_mem ms) mdC) Qx) end.
assert (EBN : BASE + (22648 + 4) = 0x86ae0) by (vm_compute; reflexivity).
assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + (22648 + 4)))
  by (unfold regsC; rewrite YK11.getr_same by (intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc;
      discriminate Hc); reflexivity).
assert (RCK : forall r' : bv 5, bv_unsigned r' <> 1 -> YK11.getr regsC r' = YK11.getr (ms_regs ms) r')
  by (intros r' Hr; unfold regsC; apply YK11.getr_other; intros Ex; apply Hr; rewrite Ex; reflexivity).
assert (RC2 : YK11.getr regsC 2%bv = w64 sp1) by (rewrite RCK by (vm_compute; discriminate); exact T2).
assert (RC3 : YK11.getr regsC 3%bv = w64 (as_gp B)) by (rewrite RCK by (vm_compute; discriminate); exact T3).
assert (RC4 : YK11.getr regsC 4%bv = w64 (as_tp B)) by (rewrite RCK by (vm_compute; discriminate); exact T4).
assert (RC11 : YK11.getr regsC 11%bv = w64 (F + 32)) by (rewrite RCK by (vm_compute; discriminate); exact T11).
assert (USPC : spZ regsC = sp1) by (unfold spZ; rewrite RC2; unfold w64; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARN.
assert (PTW : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms)) (TW.set_S_state X TS0.DIGINET_S_WAKING)).
{ rewrite wn_set_state_eq.
  apply (tw_write TMAP_A (aview segs (w_H W2) mem2) _ X TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 1 TMAP_A_ok Htw1
    TMAP_A_g_s); [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. unfold aview. replace (TA_g_s + 112 + Z.of_nat j) with (0 + 6158896 + Z.of_nat j)
      by (unfold TA_g_s; lia).
    rewrite (VG j Hj).
    destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
  - intros x Hx Hn. destruct Hx as (o & b & n & Hin3 & Hx).
    assert (HxG : inG TG.G_HARNESS x).
    { unfold inG. apply Exists_exists. exists (b, n). split; [exact (TMAP_A_in_G o b n Hin3) | unfold in_zr; cbn [fst snd]; lia]. }
    apply KAN; [pose proof (inG_low segs B transport_segs_low _ x HGX HxG); unfold kLowMemEnd in *; lia|].
    apply NZG; [exact HxG | unfold WAKE_S; cbn [Z.of_nat Pos.of_succ_nat] in Hn; lia]. }
eapply SRr_bind.
{ exact (HN fx STK sp0 FP ly S W0 mem0 md0 ((WAKE_CID, pos) :: own) ly2 S2 W2 (ms_mem ms) mdC (k + e) regsC
    (F + 32) (wake_ntc Bw) TF (TW.set_S_state X TS0.DIGINET_S_WAKING) Bw'
    ltac:(apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJ2)
    ltac:(rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite RC1, EBN; rewrite unsigned_lit_small by lia; lia)
    RC3 RC4 RC11
    ltac:(rewrite USPC; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1; destruct Hsp1 as (_ & M1);
          rewrite M1, Z.add_0_r in D1; rewrite D1; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring;
          apply Z.mod_mul; lia)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    (wn_ntc_at ly2 S2 W2 (ms_mem ms) md3 regsC Bw F pos LAWS HARN Hin EF2 HF0 HF64 HFc HFapp
       ltac:(rewrite USPC; lia) ZSN HNB)
    (wn_tframe LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 (ms_mem ms) md3 regs regsC TF Bw WAKE_CID pos HARc HARN Hfrs
       Hperm HlyF ESLO2c ESHI2c HSTKLT KCN HoffG Hapart ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia) HTF)
    ltac:(intros a Ha; rewrite <- (Hrom a Ha); pose proof KCN as (_ & _ & K3 & _);
          destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He];
          apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He];
          intro Ga; pose proof (inG_G_HARNESS_hull a Ga) as Gh; pose proof (trans_ro_rd_bounds a Ha) as Rb;
          unfold TG.G_HARNESS_LO in Gh; lia)
    PTW HNM
    (wn_apart ly2 S2 W2 mem2 md2 W2 (ms_mem ms) TF Bw (TW.set_S_state X TS0.DIGINET_S_WAKING) F pos LAWS HAR2 Hin EF2
       Hapart Hst HGn)
    ltac:(intros HD; exfalso; unfold wake_ntc in HD; cbn [TI.n_kind] in HD;
          unfold TS0.DIGINET_N_STATE, TC.N_DATA in HD; discriminate HD)
    ltac:(unfold NOTICE_EV; lia)). }
intros W3 c3 _ HPOST.
unfold transport_notice_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md4 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3).
assert (He30 : e3 = 0) by (unfold NOTICE_EV in He3; lia). subst e3.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _).
pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
clear HJi3 memS3.
assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF; reflexivity).
assert (EF3 : frame_addr ly3 WAKE_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF3c; reflexivity).
assert (Hin3 : In (WAKE_CID, pos) (frames S3)) by (rewrite Hfr3; exact Hin).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md4 WAKE_CID pos HAR3 Hin3) as (_ & _ & _ & HFsh3).
rewrite EF3 in HFsh3. change (fs_frame_bytes WAKE_CID / 8) with 32 in HFsh3. rewrite ESH in HFsh3.
assert (Hfrs3 : frames S3 = (WAKE_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
assert (Hbl3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3)).
{ intros bm Hbm. apply Hbl in Hbm. exact (Permutation_in _ (Permutation_sym Hperm3) Hbm). }
assert (R3_24 : YK11.getr regs3 (Z_to_bv 5 24) = w64 (SHADOW_OFF + F / 8)).
{ rewrite (HP3 24 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). rewrite T24. exact R24. }
(* what the call kept, from its entry to notice's return *)
assert (KC3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 (ms_mem ms) W3 mem3
    (spZ regs - WAKE_STK) (spZ regs) (spZ regsC - NOTICE_STK) (spZ regsC) (wake_wr Bw)
    (notice_wr (TW.set_S_state X TS0.DIGINET_S_WAKING) (wake_ntc Bw)) (dkg_nf WAKE_CID F FL)).
  - lia.
  - lia.
  - exact Efa2.
  - intros f Hf. rewrite Hfrs. right. exact Hf.
  - exact Hbl.
  - exact N1.
  - exact N3.
  - exact KCN.
  - exact HK3.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. left. unfold notice_wr in Ha. rewrite HGn in Ha. unfold wake_wr. do 13 right.
    split; [exact Hst | right; exact Ha]. }
(* +0x3e4 .. +0x40c: a0 = 0, a1 = -8, shadow bytes 4 .. 12 := 0xf8, to the e2 cut *)
rewrite RC1. change (Z_to_bv 64 (BASE + (22648 + 4))) with (Z_to_bv 64 (BASE + (WAKE_NTC + 0x94))).
pose proof (wn_entry3 W3 regs3 mem3 F R3_24 HF0 HF64 ltac:(lia)
  ltac:(intros i Hi; exact (proj1 (HFsh3 i ltac:(lia))))) as HS3.
set (E3 := Eimg (PI := PI_transport) (Ereg regs3 [])) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n (r' : bv 5), Z.of_nat n = bv_unsigned r' -> ew E3 n = YK11.getr regs3 r')
  by (intros n r' Hn; unfold E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U24c : bv_unsigned (ew E3 24) = SHADOW_OFF + F / 8)
  by (rewrite (EE3 24%nat (Z_to_bv 5 24) eq_refl), R3_24; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (SHOK3 : sh_ok segs WN_Bx (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 WN_B0 WAKE_E2.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  eapply awr_ok_x_cons_own with (cid := WAKE_CID); [left; reflexivity | |].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U24c in Ha.
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EF3. change (fs_frame_bytes WAKE_CID / 8) with 32. lia.
  - apply awr_ok_x_nil. }
set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms4 end.
assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 13) ->
  aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) HFr);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta. wn_win Hiw Hx ltac:(rewrite ?U24c in Hx; lia). }
assert (GA4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms4) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KC4 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 (ms_mem ms4) (spZ regs - WAKE_STK) (spZ regs)
  (wake_wr Bw)).
{ apply (wn_kept_w lyc Sc ly3 S3 W W3 memc mdc mem3 md4 mem3 (ms_mem ms4) (spZ regs - WAKE_STK) (spZ regs) pos F FL
    (wake_wr Bw) (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) LAWS HGX FFL HARc HAR3 Hfrs3 Hbl3
    ELF3c EF eq_refl ltac:(lia) ltac:(lia)); [| exact KC3 | exact KR4 | exact GA4].
  intros a Ha. right. left. right. left. change (fs_frame_bytes WAKE_CID / 8) with 32. cbv beta in Ha. lia. }
pmkst HS3.
(* the registers the e2 cut reads *)
wn_reg HS3 (Z_to_bv 5 10) (Z_to_bv 64 0) F10 ltac:(reflexivity).
wn_reg HS3 (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) F2
  ltac:(cbn [sv_denot]; rewrite (EE3 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
wn_reg HS3 (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) F3
  ltac:(cbn [sv_denot]; rewrite (EE3 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
wn_reg HS3 (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) F4
  ltac:(cbn [sv_denot]; rewrite (EE3 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
wn_reg HS3 (Z_to_bv 5 8) (YK11.getr regs3 (Z_to_bv 5 8)) F8
  ltac:(cbn [sv_denot]; rewrite (EE3 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
wn_reg HS3 (Z_to_bv 5 9) (YK11.getr regs3 (Z_to_bv 5 9)) F9
  ltac:(cbn [sv_denot]; rewrite (EE3 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
wn_reg HS3 (Z_to_bv 5 18) (YK11.getr regs3 (Z_to_bv 5 18)) F18
  ltac:(cbn [sv_denot]; rewrite (EE3 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
wn_reg HS3 (Z_to_bv 5 24) (YK11.getr regs3 (Z_to_bv 5 24)) F24
  ltac:(cbn [sv_denot]; rewrite (EE3 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
wn_reg HS3 (Z_to_bv 5 25) (YK11.getr regs3 (Z_to_bv 5 25)) F25
  ltac:(cbn [sv_denot]; rewrite (EE3 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* the bytes the release reads: the saved words above sp1 and the frame's last word *)
pose proof HK3 as (K31 & _ & _ & K34 & _).
assert (KSTK : forall a, sp1 <= a < spZ regs -> aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. rewrite KR4 by (unfold SHADOW_OFF; lia). rewrite USPC in K31. rewrite K31 by lia.
  apply KAN; [lia|]. unfold wn_Z, WAKE_S, TA_g_s, SHADOW_OFF. lia. }
assert (KFL : forall i, 0 <= i < 8 ->
  aview segs (w_H W3) (ms_mem ms4) (F + 248 + i) = aview segs (w_H W2) mem2 (F + 248 + i)).
{ intros i Hi. rewrite KR4 by (unfold SHADOW_OFF in *; destruct HSHF; lia).
  rewrite (K34 WAKE_CID pos (F + 248 + i) Hin).
  - apply KAN; [lia|]. unfold wn_Z, WAKE_S, TA_g_s, SHADOW_OFF in *.
    intros [Hz | [Hz | [Hz | Hz]]]; [destruct HSHF; lia | lia | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia | lia].
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF2. change (fs_frame_bytes WAKE_CID) with 256. lia.
  - intros Hw. pose proof (wn_nwr_got (TW.set_S_state X TS0.DIGINET_S_WAKING) (wake_ntc Bw) (F + 248 + i) eq_refl Hw)
      as Hg.
    apply (N2 (F + 248 + i)); [left; change (fs_frame_bytes WAKE_CID) with 256; lia|].
    apply trans_g_img. unfold inG. apply Exists_exists. exists (TA_GOT, TW.SZ_GOT).
    split; [exact (TMAP_A_in_G _ _ _ TMAP_A_GOT) | unfold in_zr, TW.SZ_GOT; cbn [fst snd]; lia]. }
assert (HSo : forall o, In o WAKE_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold WAKE_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
apply (HE2 LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ly3 S3 W3
  (ms_mem ms4) md5 e (ms_regs ms4) HFIX).
- split; [|split].
  + split; [replace (k + e) with (k + e + 0) by lia; exact HJ3|].
    split; [exact He0|].
    split; [exact Hfrs3|].
    split; [exact (Permutation_trans Hperm3 Hperm)|].
    split; [exact ELF3c|].
    split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
    split; [exact KC4|].
    split.
    * rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
      pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK. lia.
    * unfold WAKE_FBYTES. change (flag_addr lyc WAKE_CID pos) with FL. rewrite <- HFLw.
      replace (F + 256 - 8) with (F + 248) by lia.
      apply rdword_ext. intros i Hi. exact (KFL i Hi).
  + apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact Htw3|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KR4; [lia | unfold SHADOW_OFF; lia].
  + exact Hgf'.
- assert (CH : forall n, acallee_saved n -> bv_unsigned (Z_to_bv 5 n) <> 1 ->
    YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr (ms_regs ms) (Z_to_bv 5 n))
    by (intros n Hn H1; rewrite (HP3 n Hn); exact (RCK _ H1)).
  split; [split|].
  + exact (eq_trans F2 (eq_trans (CH 2 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T2)).
  + split; [exact (eq_trans F3 (eq_trans (CH 3 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T3 (eq_sym Hgp))))|].
    split; [exact (eq_trans F4 (eq_trans (CH 4 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T4 (eq_sym Htp))))|].
    split; [exact (eq_trans F8 (eq_trans (CH 8 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T8 R8)))|].
    split; [exact (eq_trans F9 (eq_trans (CH 9 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T9 R9)))|].
    split; [exact (eq_trans F18 (eq_trans (CH 18 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T18 R18)))|].
    split; [exact (eq_trans F24 (eq_trans (CH 24 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T24 R24)))|].
    exact (eq_trans F25 (eq_trans (CH 25 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T25 R25))).
  + rewrite Hr0. exact F10.
Qed.

End wn.

Print Assumptions wake_ntc_pc.
