(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 945 of its 1029 lines of code are new or changed and 475 lines of the source are left out. *)
(* diginet_session_wake_seg_mid (image B): Lemma wakeb_mid : wakeb_mid_stmt (lib/B/Prog/diginet_session_wake_seg_cut.v),
   the mid piece of the image-B ASan walk of diginet_session_wake (fuzz_transport.asan-ubsan 0x86a38 = transportb_sigma
   TB_diginet_session_wake, AF_diginet_session_wake = 0x5798 of lib/B/Prog/DgnTransportBList.v), from the mid cut
   WAKEB_MID (+0x224, 0x86c5c) to the e2 cut WAKEB_E2 (+0x2fc, 0x86d34). The walk holds the caller's G journal
   (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS_B 0 []) with the class-1 frame F owned; the runs are
   lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x. Registers at the cut (wakeb_regs_mid): s1 = sp1, s3 = now,
   s4 = s, s5 = s + 18224, s6 = e2 = F + 32, s10 = the shadow base.
     run 1   +0x224 .. +0x230  `ld s7, 24(s1)`: e2_len, the out cell send_control filled (wakeb_mid_cur's garr8 of
                               put 8 60 at sp1 + 24, wmb_klp_val); a0 = s + 216, a1 = s6 = e2, a2 = s7 = 60;
     +0x234                    `jal __asan_memcpy`: lib/A/Prog/TransportGCg.v gx_intrin_at at OCpy. The destination
                               [s + 216, s + 276) is bytes of g_s (G: writable by TransportGRwB.v G_HARNESS_B_rw, its
                               shadow 0 by trans_wake_cells through DgnTransportBCg.v decode_zshadow_ra); the source
                               [e2, e2 + 60) is the own frame's (wakeb_mid_cur's decode_rd_ok, kept by run 1); the two
                               are apart (a frame byte is not an image byte: frm_img). Run 1's five regions are kept
                               across the call (YC1h.v jafter_call_keep_hi): the call changes [s + 216, s + 276) and the
                               ESTACK bytes below sp1 only;
     run 2   +0x238 .. +0x2f4  the seven checked accesses of g_s, each check reading a zero shadow byte of g_s's payload
                               (the shadow entries WMB_SH, wmb_shok): the 8-byte store of 60 at s + 1736, the 8-byte
                               load / + 1 / store at s + 18224 (s5), the 4-byte load of s + 160, the stores of 1 at
                               s + 212, of the loaded counter at s + 1744, of 0 at s + 1748 and of now at s + 1752; then
                               a1 = 1 (S_WAKING), a2 = 1 (R_WAKE), a0 = s4 and `jal set_state`;
     +0x2f4                    set_state_cg.v transport_set_state_cg at transportb_sigma TB_set_state, in the same G
                               journal: the world relation at wake_w3 B1 e2 now (wmb_writes: TWorldG.v tw_upd for the
                               memcpy's 60 bytes and the six stores, in the model's order; the values from run 2's
                               regions, wmb_field), the model's set_state_m equation (wake_model on wakeb_mid_cur's path,
                               rs >= 0; Bw' and r read off by wakeb_some_inv), the current heap frame at the call from
                               wakeb_fix's trans_tframe_at through what the walk kept (wmb_tframe), the read-only view
                               (wmb_rom), sstate_apart from wake_apart (sstate_wr lies in wake_wr Bw: S_state and GOT.n
                               of wake_w3 B1 e2 now and of its set_S_state are Bw's, wmb_swr), the class-2 count (the
                               own frame is of class 1). Its acall_kept_g folds into the walk's with TransportGCg.v
                               dk_kept_trans_nf_g (NF = the own frame, TransportGFrame.v dkg_nf_sep_gw);
     run 3   +0x2f8            `li a0, 0` (DIGINET_OK), up to WAKEB_E2, from a state with no region: the state
                               wakeb_rel_cur there (the post's X is set_state's) and wakeb_regs_rel conclude by
                               wakeb_e2_at.
   What the call keeps (acall_kept_g over wake_wr Bw) is carried over runs 1 and 2 and the memcpy by
   TransportGFrame.v dk_kept_step_gw (every byte they may change is an ESTACK byte below sp1 or a byte of wmb_wr, which
   lies in wake_wr Bw and in G: wmb_wr_in). The model's facts are lib/A/Prog/diginet_session_wake_seg_keep.v's
   (wk_w3_keep, restated once at image B's statement names as wmb_w3_keep; wk_set_state_keep, wk_put8_u64,
   wk_put4_s32). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YI09 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
diginet_session_wake_cg diginet_session_wake_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_seg_keep.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

Definition WMB_B0 : Z * Z := (0, 0).
(* The entry state at +0x224. Atoms 0 .. 31: the registers at the cut; 32: the shadow base; 33: B1's 8 bytes at
   s + 18224 (stats.tx_wakes); 34: B1's 4 bytes at s + 160 (host_counter). Regions: e2_len at sp1 + 24 (60, read
   only), host_counter (read only), and the bytes run 2 stores: [s + 212, s + 216), [s + 1736, s + 1760) and
   stats.tx_wakes (based at s5 = s + 18224). *)
Definition wmb_rg_klp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (YP09.CVal 8 (SLit 60))].
Definition wmb_rg_hc : YP09.region :=
  YP09.mkRegion (Some 20%nat) 160 164 0 0 [YP09.mkChunk 160 (YP09.CVal 4 (SOff 34 0))].
Definition wmb_rg_inf : YP09.region := YP09.mkRegion (Some 20%nat) 212 216 212 216 [].
Definition wmb_rg_il : YP09.region := YP09.mkRegion (Some 20%nat) 1736 1760 1736 1760 [].
Definition wmb_rg_tx : YP09.region :=
  YP09.mkRegion (Some 21%nat) 0 8 0 8 [YP09.mkChunk 0 (YP09.CVal 8 (SOff 33 0))].
Definition wmb_regions : smem := [wmb_rg_klp; wmb_rg_hc; wmb_rg_inf; wmb_rg_il; wmb_rg_tx].
Definition wmb_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF WAKE_S WAKE_S 6);
           (21%nat, mkAF (WAKE_S + 18224) (WAKE_S + 18224) 4); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 64 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_wmb0 : sstate := mkSS WAKEB_MID sr_atoms wmb_regions None wmb_facts.
(* The shadow entries of run 2's checks ([s + 160, s + 1760) and s5's 8 bytes), and the shadow base s10. *)
Definition WMB_SH : list shent := [mkSHE 20 160 1760; mkSHE 21 0 8].
Definition WMB_Bx : sv := SOff 26 0.
(* set_state's return address, +0x2f8 (`li a0, 0`), from a state with no region. *)
Definition WMB_C3 : Z := AF_diginet_session_wake + 0x2f8.
Definition ss_wmb3 : sstate := mkSS WMB_C3 sr_atoms [] None (mkFacts [] [] []).

(* The bytes the runs may store (the windows of the writable regions), and every byte of g_s the piece may change
   before set_state. *)
Definition wmb_win (a : Z) : Prop :=
  (WAKE_S + 212 <= a < WAKE_S + 216) \/ (WAKE_S + 1736 <= a < WAKE_S + 1760) \/
  (WAKE_S + 18224 <= a < WAKE_S + 18232).
Definition wmb_wr (a : Z) : Prop := (WAKE_S + 216 <= a < WAKE_S + 276) \/ wmb_win a.

(* ------------------------------------------------------------------ *)
(* 2. Model-side facts                                                 *)
(* ------------------------------------------------------------------ *)

(* A byte of a row of G is a byte of G. *)
Lemma wmb_inG_row : forall b0 n0 a, In (b0, n0) TG.G_HARNESS_B -> b0 <= a < b0 + n0 -> inG TG.G_HARNESS_B a.
Proof.
  intros b0 n0 a Hin Ha. unfold inG. apply Exists_exists. exists (b0, n0).
  split; [exact Hin | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma wmb_inG : forall a, WAKE_S <= a < WAKE_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. apply (wmb_inG_row _ _ a (TMAP_B_in_G _ _ _ TMAP_B_g_s)). unfold WAKE_S in Ha. lia. Qed.

(* Every byte the piece may change in g_s before set_state is a byte of wake_wr Bw and of G. *)
Lemma wmb_wr_in : forall Bw a, wmb_wr a -> wake_wr Bw a /\ inG TG.G_HARNESS_B a.
Proof.
intros Bw a Ha. split; [|apply wmb_inG; unfold wmb_wr, wmb_win, WAKE_S, TB_g_s, TW.SZ_g_s in *; lia].
unfold wmb_wr, wmb_win in Ha. unfold wake_wr, twb_fld.
unfold TW.A_S_inflight_frame, TW.A_S_inflight_len, TW.A_S_stats_tx_wakes, TW.A_S_inflight, TW.A_S_inflight_counter,
  TW.A_S_inflight_retries, TW.A_S_inflight_sent_us, TW.OFF_g_s, SENDCTL_F, WAKE_S, TB_g_s in *.
destruct Ha as [H|[H|[H|H]]].
- do 4 right; left. lia.
- do 7 right; left. lia.
- destruct (Z_lt_ge_dec a (6157888 + 1744)) as [L1|L1]; [do 5 right; left; lia|].
  destruct (Z_lt_ge_dec a (6157888 + 1748)) as [L2|L2]; [do 8 right; left; lia|].
  destruct (Z_lt_ge_dec a (6157888 + 1752)) as [L3|L3]; [do 9 right; left; lia|].
  do 10 right; left. lia.
- do 6 right; left. lia.
Qed.

(* An N_STATE notice writes GOT.t[GOT.n] (0 <= GOT.n < 16) and GOT.n: bytes of GOT. *)
Lemma wmb_nwr_got : forall Bx (n : TI.ntc) a, TI.n_kind n = TC.N_STATE -> notice_wr Bx n a ->
  TB_GOT <= a < TB_GOT + TW.SZ_GOT.
Proof.
  intros Bx n a K H. unfold notice_wr in H. rewrite K in H.
  destruct H as [(_ & [(Hg & Hf) | Hf]) | [(E & _) | [(E & _) | [(E & _) | [(E & _) | (E & _)]]]]];
    try (unfold TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in E; discriminate E).
  - unfold twb_fld, TW.A_GOT_t_state, TW.GOT_t_ESZ, TC.TRANS_MAX, TW.OFF_GOT, TW.SZ_GOT in *. lia.
  - unfold twb_fld, TW.A_GOT_n, TW.OFF_GOT, TW.SZ_GOT in *. lia.
Qed.

(* notice_wr reads the world only through GOT.n and the notice only through its kind. *)
Lemma wmb_nwr_eq : forall X Y (n n' : TI.ntc) a, TW.GOT_n X = TW.GOT_n Y -> TI.n_kind n = TI.n_kind n' ->
  notice_wr X n a -> notice_wr Y n' a.
Proof. intros X Y n n' a HG HK H. unfold notice_wr in *. rewrite <- HG, <- HK. exact H. Qed.

Ltac wmb_offs :=
  unfold TB_g_s, TB_GOT, TB_M, TB_g_cmd, TB_g_q, TB_g_fail_next, TB_g_last_counter, TB_g_nq,
    TW.A_S_stats_refused, TW.A_S_e1_named_us, TW.A_S_wake_acked, TW.A_S_wake_sent_us, TW.A_S_inflight_frame,
    TW.A_S_inflight_len, TW.A_S_stats_tx_wakes, TW.A_S_inflight, TW.A_S_inflight_counter, TW.A_S_inflight_retries,
    TW.A_S_inflight_sent_us, TW.A_S_stats_tx_frames, TW.A_S_state, SENDCTL_F,
    TW.A_GOT_e2, TW.A_GOT_e3, TW.A_GOT_acks, TW.A_M_host_counter, TW.A_M_next_ka, TW.A_M_last_display,
    TW.A_M_display_sent, TW.A_M_fly_on, TW.A_M_fly_cmd, TW.A_M_fly_counter, TW.A_M_fly_retries, TW.A_M_fly_sent,
    TW.A_M_fly_len, TW.A_M_fly_frame, TC.SPEC_MAX_FRAME, TC.CMDS_MAX, TW.A_Cmd_st,
    TW.OFF_g_s, TW.OFF_GOT, TW.OFF_M, TW.OFF_g_cmd, TW.OFF_g_q, TW.OFF_g_nq, TW.OFF_g_fail_next,
    TW.OFF_g_last_counter, TW.SZ_g_q, TW.SZ_g_nq, TW.SZ_g_s, TW.SZ_GOT, TW.SZ_M, TW.SZ_g_cmd,
    TW.SZ_g_last_counter in *.

(* Every byte the call stores outside its own frames is a byte of G. *)
Lemma wmb_wr_G : forall Bw a, wake_wr Bw a -> inG TG.G_HARNESS_B a.
Proof.
  intros Bw a H.
  pose proof (TMAP_B_in_G _ _ _ TMAP_B_g_s) as Gs. pose proof (TMAP_B_in_G _ _ _ TMAP_B_GOT) as Gg.
  pose proof (TMAP_B_in_G _ _ _ TMAP_B_M) as Gm. pose proof (TMAP_B_in_G _ _ _ TMAP_B_g_cmd) as Gc.
  pose proof (TMAP_B_in_G _ _ _ TMAP_B_g_q) as Gq. pose proof (TMAP_B_in_G _ _ _ TMAP_B_g_nq) as Gn.
  pose proof (TMAP_B_in_G _ _ _ TMAP_B_g_fail_next) as Gf.
  pose proof (TMAP_B_in_G _ _ _ TMAP_B_g_last_counter) as Gl.
  unfold wake_wr, iosend_wr in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|(_ & [H|H])]]]]]]]]]]]]].
  14: { apply (wmb_inG_row _ _ a Gs). unfold twb_fld in H. wmb_offs. lia. }
  14: { apply (wmb_inG_row _ _ a Gg). exact (wmb_nwr_got Bw (wake_ntc Bw) a eq_refl H). }
  13: { repeat match type of H with _ \/ _ => destruct H as [H|H] end;
        [ apply (wmb_inG_row _ _ a Gf) | apply (wmb_inG_row _ _ a Gg) | apply (wmb_inG_row _ _ a Gg)
        | apply (wmb_inG_row _ _ a Gg) | apply (wmb_inG_row _ _ a Gl) | apply (wmb_inG_row _ _ a Gm)
        | apply (wmb_inG_row _ _ a Gm) | apply (wmb_inG_row _ _ a Gm) | apply (wmb_inG_row _ _ a Gm)
        | apply (wmb_inG_row _ _ a Gm) | apply (wmb_inG_row _ _ a Gm) | apply (wmb_inG_row _ _ a Gm)
        | apply (wmb_inG_row _ _ a Gm) | apply (wmb_inG_row _ _ a Gm) | apply (wmb_inG_row _ _ a Gm)
        | apply (wmb_inG_row _ _ a Gm) | apply (wmb_inG_row _ _ a Gc) | apply (wmb_inG_row _ _ a Gq)
        | apply (wmb_inG_row _ _ a Gn) ];
        try (destruct H as (s & Hs & H)); unfold twb_fld in H; wmb_offs; cbv beta in H; lia. }
  all: apply (wmb_inG_row _ _ a Gs); unfold twb_fld in H; wmb_offs; lia.
Qed.

(* The model lemmas of lib/A/Prog/diginet_session_wake_seg_keep.v at image B's statement names (the same text). *)
Lemma wmb_w3_keep : forall B1 e2 now, length B1 = Z.to_nat TW.W_LEN -> length e2 = 60%nat ->
  length (wake_w2 B1 e2) = Z.to_nat TW.W_LEN /\
  length (wake_w3 B1 e2 now) = Z.to_nat TW.W_LEN /\
  TW.S_state (wake_w3 B1 e2 now) = TW.S_state B1 /\
  TW.GOT_n (wake_w3 B1 e2 now) = TW.GOT_n B1 /\
  TW.g_fail_next (wake_w3 B1 e2 now) = TW.g_fail_next B1.
Proof. exact wk_w3_keep. Qed.

(* byte k of a value read modulo a larger power of two *)
Lemma wmb_byte_mod : forall x N k, 0 <= k -> k + 8 <= N -> Z.shiftr (x mod 2 ^ N) k mod 256 = Z.shiftr x k mod 256.
Proof.
intros x N k Hk HkN. change 256 with (2 ^ 8). apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 8) as [H8|H8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* the sign-extended 4-byte load of an atom *)
Lemma wmb_sext : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 v).
Proof.
intros E n v H R. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma wmb_nth_zs : forall (l : list byte) j, nth j (TW.zs l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
intros l. unfold TW.zs. induction l as [|x l IH]; intros [|j]; cbn [nth map]; try reflexivity. apply IH.
Qed.

(* A sequence of writes inside one payload row: each span written with its bytes, every other payload byte kept. *)
Lemma wmb_writes : forall T o b n (ws : list (Z * list byte)) rd rd' Bw,
  tw_ok T -> In (o, b, n) T -> tw_at T rd Bw ->
  Forall (fun w => 0 <= fst w /\ fst w + Z.of_nat (length (snd w)) <= n /\
     forall j, (j < length (snd w))%nat ->
       rd' (b + fst w + Z.of_nat j) = Some (bv_unsigned (nth j (snd w) (Z_to_bv 8 0)))) ws ->
  (forall x, tw_in T x ->
     Forall (fun w => ~ (b + fst w <= x < b + fst w + Z.of_nat (length (snd w)))) ws -> rd' x = rd x) ->
  tw_at T rd' (fold_left (fun X w => TW.upd X (o + fst w) (snd w)) ws Bw).
Proof.
intros T o b n ws. induction ws as [|w ws IH]; intros rd rd' Bw Hok Hin Hat Hws Hout.
- cbn [fold_left]. apply (tw_kept T rd rd' Bw Hat). intros x Hx. apply Hout; [exact Hx | constructor].
- apply Forall_cons_iff in Hws as [(Hk & Hkn & Hv) Hws]. cbn [fold_left].
  set (rd1 := fun x => if ((b + fst w <=? x) && (x <? b + fst w + Z.of_nat (length (snd w))))%bool then rd' x else rd x).
  apply (IH rd1 rd' (TW.upd Bw (o + fst w) (snd w)) Hok Hin).
  + apply (tw_upd T rd rd1 Bw o b n (fst w) (snd w) Hok Hat Hin Hk Hkn).
    * intros j Hj. unfold rd1.
      replace ((b + fst w <=? b + fst w + Z.of_nat j) && (b + fst w + Z.of_nat j <? b + fst w + Z.of_nat (length (snd w))))%bool
        with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      exact (Hv j Hj).
    * intros x Hx Hn. unfold rd1.
      destruct ((b + fst w <=? x) && (x <? b + fst w + Z.of_nat (length (snd w))))%bool eqn:Eb; [|reflexivity].
      exfalso. apply andb_true_iff in Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
  + exact Hws.
  + intros x Hx Hall. unfold rd1.
    destruct ((b + fst w <=? x) && (x <? b + fst w + Z.of_nat (length (snd w))))%bool eqn:Eb; [reflexivity|].
    apply Hout; [exact Hx|]. constructor; [|exact Hall].
    apply andb_false_iff in Eb. destruct Eb as [Eb|Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; lia.
Qed.

(* The memcpy's 60 bytes and the six stores of +0x238 .. +0x2e4, in the model's order and form. *)
Definition wmb_ws (B1 e2 : list byte) (now : Z) : list (Z * list byte) :=
  [(216, e2); (1736, TW.put 8 (Z.of_nat (length e2)));
   (18224, TW.put 8 (TS0.u64 (TW.S_stats_tx_wakes
                               (TW.set_S_inflight_len (TW.set_S_inflight_frame B1 e2) (Z.of_nat (length e2))) + 1)));
   (212, TW.put 4 1); (1744, TW.put 4 (TW.S_host_counter (wake_w2 B1 e2))); (1748, TW.put 4 0);
   (1752, TW.put 8 now)].

Lemma wmb_ws_w3 : forall B1 e2 now,
  fold_left (fun X w => TW.upd X (TW.OFF_g_s + fst w) (snd w)) (wmb_ws B1 e2 now) B1 = wake_w3 B1 e2 now.
Proof.
intros B1 e2 now. unfold wmb_ws. cbn [fold_left fst snd].
change (TW.OFF_g_s + 216) with TW.A_S_inflight_frame.
change (TW.OFF_g_s + 1736) with TW.A_S_inflight_len.
change (TW.OFF_g_s + 18224) with TW.A_S_stats_tx_wakes.
change (TW.OFF_g_s + 212) with TW.A_S_inflight.
change (TW.OFF_g_s + 1744) with TW.A_S_inflight_counter.
change (TW.OFF_g_s + 1748) with TW.A_S_inflight_retries.
change (TW.OFF_g_s + 1752) with TW.A_S_inflight_sent_us.
unfold wake_w3, wake_w2. cbv zeta.
unfold TW.set_S_inflight_sent_us, TW.set_S_inflight_retries, TW.set_S_inflight_counter, TW.set_S_inflight,
  TW.set_S_stats_tx_wakes, TW.set_S_inflight_len, TW.set_S_inflight_frame.
reflexivity.
Qed.

(* stats.tx_wakes and host_counter, read after the stores before them, are B1's *)
Lemma wmb_tx_eq : forall B1 e2, length B1 = Z.to_nat TW.W_LEN -> length e2 = 60%nat ->
  TW.S_stats_tx_wakes (TW.set_S_inflight_len (TW.set_S_inflight_frame B1 e2) (Z.of_nat (length e2))) =
  TW.u_at B1 (TW.OFF_g_s + 18224) 8.
Proof.
intros B1 e2 HB HL. unfold TW.S_stats_tx_wakes, TW.set_S_inflight_len, TW.set_S_inflight_frame.
wk_out. reflexivity.
Qed.

Lemma wmb_hc_eq : forall B1 e2, length B1 = Z.to_nat TW.W_LEN -> length e2 = 60%nat ->
  TW.u_at (wake_w2 B1 e2) TW.A_S_host_counter 4 = TW.u_at B1 (TW.OFF_g_s + 160) 4.
Proof.
intros B1 e2 HB HL. unfold wake_w2. cbv zeta.
unfold TW.set_S_stats_tx_wakes, TW.set_S_inflight_len, TW.set_S_inflight_frame.
unfold TW.A_S_host_counter. wk_out. reflexivity.
Qed.

(* sstate_wr of set_state's call at the world wake_w3 B1 e2 now lies in wake_wr Bw: the state and GOT.n of that
   world are Bw's (no store before set_state touches g_s.state or GOT.n). *)
Lemma wmb_swr : forall Bw X a, length X = Z.to_nat TW.W_LEN ->
  TW.S_state X = TW.S_state Bw -> TW.GOT_n X = TW.GOT_n Bw ->
  sstate_wr X TS0.DIGINET_S_WAKING TS0.DIGINET_R_WAKE a -> wake_wr Bw a.
Proof.
  intros Bw X a LX HS HG (Hne & H). unfold wake_wr. do 13 right. split; [rewrite <- HS; exact Hne|].
  destruct H as [H | H]; [left; exact H | right].
  destruct (wk_set_state_keep X TS0.DIGINET_S_WAKING LX) as (_ & HGs & _).
  apply (wmb_nwr_eq (sstate_w X TS0.DIGINET_S_WAKING) Bw
    (sstate_ntc X TS0.DIGINET_S_WAKING TS0.DIGINET_R_WAKE) (wake_ntc Bw) a); [| reflexivity | exact H].
  unfold sstate_w. rewrite HGs. exact HG.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Tactics                                                          *)
(* ------------------------------------------------------------------ *)

Ltac wmb_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
Ltac wmb_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* the write right of a run from the five regions: two read-only, three bytes of G *)
Ltac wmb_awr U20x U21x :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  do 2 (apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  do 2 (apply awr_ok_x_cons_g; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U20x in Ha; apply wmb_inG;
          unfold TW.SZ_g_s; lia |]);
  apply awr_ok_x_cons_g; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U21x in Ha; apply wmb_inG;
          unfold TW.SZ_g_s; lia |];
  apply awr_ok_x_nil.
Ltac wmb_awr0 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.
(* the windows a run wrote, each inside wmb_win *)
Ltac wmb_wins Hin Hx U20x U21x :=
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U20x, ?U21x in Hx;
    first [lia | left; lia | right; left; lia | right; right; lia] |]);
  destruct Hin.
(* After the run to a cut from a state with no region: every byte of the view as at m (KD), presence grown (GR). *)
Ltac wmb_after_cut HS W KD GR m msF :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF end;
  assert (KD : forall a, aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) m a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a; rewrite (aview_wrap64 tfibsegs _ (ms_mem msF) a), (aview_wrap64 tfibsegs _ m a);
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha;
    match goal with HFx : frame_of ?E ?rs (mrestrict (w_H W) m) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (can_aview_kept_frame E rs (w_H W) m (ms_mem msF) 0 HFx ltac:(lia)
               ltac:(let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hr := fresh "Hr" in
                     intros x Hx; unfold in_wrange; intros (r & Hr & _); vm_compute in Hr; destruct Hr) _ Ha) end
  | ];
  assert (GR : forall a, apresent (w_H W) m a -> apresent (w_H W) (ms_mem msF) a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    match goal with HGx : mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (apresent_grows _ _ _ a HGx Ha) end
  | ].
Ltac wmb_kreg HS EEx r n Q H :=
  lazymatch type of Q with _ = ?v =>
    wmb_reg HS r v H ltac:(cbn [sv_denot]; rewrite (EEx n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.

(* ------------------------------------------------------------------ *)
(* 4. The machine-side lemmas                                          *)
(* ------------------------------------------------------------------ *)

Section wmb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* Every range of g_s's payload is addressable at every AR state: whole granules of the record's zero shadow. *)
Lemma wmb_ra : forall ly S (W : world segs) mem md q n,
  trans_wake_cells B -> @AR rc segs B ly S W mem md -> WAKE_S <= q -> q + n <= WAKE_S + TW.SZ_g_s ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q n.
Proof.
intros ly S W mem md q n HZ HAR Hq Hqn x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : WAKE_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= WAKE_S + TW.SZ_g_s)
  by (unfold WAKE_S, TB_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md WAKE_S (WAKE_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The shadow entries of run 2 hold at every AR state. *)
Lemma wmb_shok : forall ly S (W : world segs) mem md (E : env),
  trans_wake_cells B -> @AR rc segs B ly S W mem md ->
  bv_unsigned (ew E 20) = WAKE_S -> bv_unsigned (ew E 21) = WAKE_S + 18224 -> bv_unsigned (ew E 26) = SHADOW_OFF ->
  sh_ok segs WMB_Bx WMB_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E HZ HAR U20 U21 U26.
assert (CS : WAKE_S = 6157888) by reflexivity.
assert (UB : U E WMB_Bx = SHADOW_OFF).
{ unfold U, WMB_Bx. cbn [sv_denot]. rewrite U26, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
unfold sh_ok, WMB_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range segs (w_H W) mem _ WMB_Bx 20 (WAKE_S + 160) 1600 WAKE_S 160 1760
    (wmb_ra ly S W mem md (WAKE_S + 160) 1600 HZ HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) UB).
  + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. rewrite CS; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. rewrite CS in Hx. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range segs (w_H W) mem _ WMB_Bx 21 (WAKE_S + 18224) 8 (WAKE_S + 18224) 0 8
    (wmb_ra ly S W mem md (WAKE_S + 18224) 8 HZ HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) UB).
  + unfold U. cbn [sv_denot]. rewrite U21, Z.add_0_r. apply unsigned_lit_small. rewrite CS; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. rewrite CS in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The walk's valuation at the mid cut, and after set_state returns. *)
Definition wmb_E (regs : bvmap 5 word) (TX HC : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 TX; Z_to_bv 64 HC]).
Definition wmb_E3 (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).

(* The entry state at +0x224, and the shadow entries. *)
Lemma wmb_entry0 : forall ly S (W : world segs) regs mem md TX HC sp1,
  trans_wake_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  YK11.getr regs 20 = w64 WAKE_S -> YK11.getr regs 21 = w64 (WAKE_S + 18224) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  0 <= TX < 2 ^ 64 -> 0 <= HC < 2 ^ 32 ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 24) 8 60 ->
  val_mem segs (mrestrict (w_H W) mem) (WAKE_S + 160) 4 HC ->
  val_mem segs (mrestrict (w_H W) mem) (WAKE_S + 18224) 8 TX ->
  st_ok_pi segs VAL (wmb_E regs TX HC) ss_wmb0
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + WAKEB_MID)) mem (YK11.seg_rom segs))) /\
  sh_ok segs WMB_Bx WMB_SH (wmb_E regs TX HC) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md TX HC sp1 HZ HAR R9 Hsp Hsp32 R20 R21 R26 HTX HHC V24 V160 V18224.
assert (CS : WAKE_S = 6157888) by reflexivity.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (wmb_E regs TX HC) n = YK11.getr regs r)
  by (intros n r Hn; unfold wmb_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew (wmb_E regs TX HC) 33 = Z_to_bv 64 TX)
  by (unfold wmb_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (wmb_E regs TX HC) 34 = Z_to_bv 64 HC)
  by (unfold wmb_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (U9 : bv_unsigned (ew (wmb_E regs TX HC) 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew (wmb_E regs TX HC) 20) = WAKE_S)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; rewrite CS; lia).
assert (U21 : bv_unsigned (ew (wmb_E regs TX HC) 21) = WAKE_S + 18224)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; rewrite CS; lia).
assert (U26 : bv_unsigned (ew (wmb_E regs TX HC) 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew (wmb_E regs TX HC) 33) = TX) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (wmb_E regs TX HC) 34) = HC) by (rewrite E34; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_wmb0, wmb_regions.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [wmb_rg_klp wmb_rg_hc wmb_rg_inf wmb_rg_il wmb_rg_tx
         YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ sp1 24 8 (SLit 60) 60); [reflexivity | zside | zside | exact V24].
    * rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ WAKE_S 160 4 (SOff 34 0) HC);
        [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | exact HHC | lia | exact V160].
    * rewrite U20. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (WAKE_S + o) G_HARNESS_B_rw).
      apply wmb_inG. unfold TW.SZ_g_s. lia.
    * rewrite U20. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (WAKE_S + o) G_HARNESS_B_rw).
      apply wmb_inG. unfold TW.SZ_g_s. lia.
    * rewrite U21. split; [lia|]. split; [rewrite CS; lia|]. split.
      -- intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (WAKE_S + 18224 + o) G_HARNESS_B_rw).
         apply wmb_inG. unfold TW.SZ_g_s. lia.
      -- constructor; [|constructor].
         apply (chunk_ok_val segs _ _ (WAKE_S + 18224) 0 8 (SOff 33 0) TX);
           [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact HTX | lia |].
         rewrite Z.add_0_r. exact V18224.
  + apply pairwise_disjoint_of_extents.
    unfold wmb_rg_klp, wmb_rg_hc, wmb_rg_inf, wmb_rg_il, wmb_rg_tx, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U20, U21. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite CS. repeat split; first [exact I | lia].
  + unfold wmb_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U20, U21, U26, U33, U34.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- exact (wmb_shok ly S W mem md _ HZ HAR U20 U21 U26).
Qed.

(* The state at +0x2f8 (set_state's return) with no region. *)
Lemma wmb_entry3 : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (wmb_E3 regs) ss_wmb3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + WMB_C3)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_wmb3.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* A chunk of a region, read byte by byte through the view. *)
Lemma wmb_field : forall E H (m : word -> option byte) n bb cs lo hi wlo whi od (w : N) e x,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = bb -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 x ->
  Z.of_N w <= 8 ->
  forall j, (j < N.to_nat w)%nat -> aview segs H m (bb + od + Z.of_nat j) = Some (YO0f.le_byte x (N.to_nat w) j).
Proof.
intros E H m n bb cs lo hi wlo whi od w e x (_ & _ & _ & Hcs) Hn Hc He Hw j Hj.
pose proof (N_nat_Z w) as Hnw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
destruct (Hck (Z.of_nat j) ltac:(unfold YP09.c_len; cbn [YP09.cv_len YP09.c_val]; lia)) as (b & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. rewrite He in Hb1. injection Hb1 as <-.
unfold aview. rewrite Hb2. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (2 ^ 64). unfold YO0f.le_byte.
rewrite (wmb_byte_mod x 64 (8 * Z.of_nat j)) by lia.
rewrite (wmb_byte_mod x (8 * Z.of_nat (N.to_nat w)) (8 * Z.of_nat j)) by lia.
reflexivity.
Qed.

(* A garr8 byte, read through the view. *)
Lemma wmb_aview_garr8 : forall H (m : word -> option byte) a l j,
  garr8 segs (mrestrict H m) a l -> (j < length l)%nat -> aview segs H m (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m a l j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)).
cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv. unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite tw_le_byte1 by lia. apply Z.mod_small. lia.
Qed.

(* e2_len: the 8 bytes send_control stored at klp hold 60. *)
Lemma wmb_klp_val : forall mm a, garr8 segs mm a (TW.zs (TW.put 8 60)) -> val_mem segs mm a 8 60.
Proof.
intros mm a Hg kk Hk. assert (Hl : length (TW.zs (TW.put 8 60)) = 8%nat) by (vm_compute; reflexivity).
destruct (Hg kk ltac:(rewrite Hl; exact Hk)) as [Hv _]. specialize (Hv 0%nat ltac:(lia)).
cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv. rewrite Hv. f_equal. f_equal.
do 8 (destruct kk as [|kk]; [vm_compute; reflexivity|]). lia.
Qed.

(* The shadow hull of a range of a 64-aligned frame of fs bytes (a multiple of 64) lies in the frame's fs / 8
   shadow bytes; the range may be empty. *)
Lemma wmb_hull_in : forall (rd : Z -> option Z) Fc fs q n,
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

(* The current heap frame, as trans_tframe_at states it at wake's entry, at a later state (ly2, S2, W2, mem2) whose
   frames are the own frame on top of the entry's and whose blocks contain the entry's: what the call kept
   (acall_kept_g over wake_wr Bw) keeps TF's bytes, by the clause of TF's placement (a block or a frame of the entry:
   wake_apart keeps TF out of wake_wr Bw; the machine stack: at or above alloc_ceiling, outside wake's window; a
   TRANS_RO_RD byte: an image byte outside G, the owned statics and errno); a TF inside G is ruled out by
   trans_tf_off_g TF. *)
Lemma wmb_tframe : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 (regs regsN : bvmap 5 word) (K : Z)
    (TF : option TI.tframe) (Bw : list byte) cid pos,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  frames S2 = (cid, pos) :: frames Sc ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc -> ly_stk_lo lyc < ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw) ->
  wake_apart TF Bw -> trans_tf_off_g TF ->
  spZ regs - WAKE_STK <= spZ regsN - K -> spZ regsN <= spZ regs ->
  trans_tframe_at B lyc Sc W memc regs WAKE_STK TF ->
  trans_tframe_at B ly2 S2 W2 mem2 regsN K TF.
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 regs regsN K TF Bw cid pos HARc HAR2 Hfr Hbl Hfa
    Elo Ehi Hstk (K1 & K2 & K3 & K4 & K5 & K6) Hap HoffG Hw1 Hw2 HT.
  destruct TF as [fr|]; [|exact I].
  destruct HT as (Ha0 & Hg8 & Hsrc & Hoff).
  set (q := TI.tf_addr fr) in *. set (n := Z.of_nat (length (TI.tf_bytes fr))) in *.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  assert (HnE : forall a, q <= a < q + n -> ~ wake_wr Bw a) by (intros a Ha Hx; exact (Hap a Hx fr eq_refl Ha)).
  assert (HnG : forall a, q <= a < q + n -> ~ inG TG.G_HARNESS_B a) by (intros a Ha; exact (HoffG fr eq_refl a Ha)).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hfin : forall f, In f (frames Sc) -> In f (frames S2)) by (intros f Hf; rewrite Hfr; right; exact Hf).
  (* the bytes of TF's range are the entry's *)
  assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
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
        unfold TG.G_HARNESS_B_LO in Gh. lia. }
  (* the entry's frames' shadow bytes are the entry's: wake_wr lies in G, below the shadow *)
  assert (KS : forall c p s, In (c, p) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8) ->
     aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
  { intros c p s Hin Hs. apply (K4 c p s Hin (or_intror Hs)). intros Hw.
    pose proof (inG_G_HARNESS_hull s (wmb_wr_G Bw s Hw)) as Hl.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c p HARc Hin) as (F1 & F2 & _).
    pose proof (Z.div_pos (frame_addr lyc c p) 8 ltac:(lia) ltac:(lia)).
    unfold in_zr in Hs. cbn [fst snd] in Hs. unfold shadow_addr, SHADOW_OFF, TG.G_HARNESS_B_HI in *. lia. }
  split; [exact Ha0|]. split.
  { eapply garr8_frame; [exact Hg8|]. intros a Ha. rewrite length_map in Ha. apply (mbyte_of_aview segs). apply KV. exact Ha. }
  split.
  2: { unfold decode_off_win in *. lia. }
  destruct Hsrc as [(bA & nA & HinA & B1 & B2) | (HL & Hrd)].
  - left. exists bA, nA. split; [exact (Hbl _ HinA) | lia].
  - right. split.
    + destruct HL as [(c & p & Hin & F1 & F2) | [HG | [(S1 & S3) | HR]]].
      * left. exists c, p. rewrite !Hfa. split; [exact (Hfin _ Hin) | lia].
      * right; left; exact HG.
      * right; right; left. rewrite Elo, Ehi. lia.
      * right; right; right; exact HR.
    + destruct (Z_lt_le_dec 0 n) as [Hn | Hn].
      * destruct HL as [HF | [(HG & _) | [(S1 & S3) | (_ & Hsh)]]].
        -- exact (decode_rd_ok_fake_kept B LAWS lyc Sc W W2 memc mem2 mdc q n HARc HF Hrd Hn KV KS).
        -- exfalso. exact (HnG q ltac:(lia) (HG q ltac:(lia))).
        -- destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 q n HAR2 Hn ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia))
             as [Ha Hh].
           exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
        -- destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
      * assert (En : n = 0) by lia.
        apply (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV); [intros x Hx; lia|].
        destruct HL as [(c & p & Hin & F1 & F2) | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
        -- assert (Hin2 : In (c, p) (frames S2)) by exact (Hfin _ Hin).
           destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 c p HAR2 Hin2) as (_ & _ & _ & HFsh).
           destruct (TransportGCg.dkg_frame_al64 segs B ly2 S2 W2 mem2 md2 c p HAR2 Hin2) as (A1 & A2 & A3).
           destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 c p HAR2 Hin2) as (G1 & G2 & _).
           rewrite (Hfa c p) in HFsh. rewrite (Hfa c p) in A1. rewrite (Hfa c p) in G1. rewrite (Hfa c p) in G2.
           apply (wmb_hull_in _ (frame_addr lyc c p) (fs_frame_bytes c) q n); try lia.
           intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
        -- exact (proj2 (Hsh ly2 S2 W2 mem2 md2 HAR2)).
        -- destruct (Z_lt_le_dec q (ly_stk_hi lyc)) as [Hq | Hq].
           ++ destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 q 1 HAR2 ltac:(lia) ltac:(rewrite Elo; lia)
                ltac:(rewrite Ehi; lia)) as [_ Hh].
              exact (trans_hull_sub _ q 1 q n Hh ltac:(lia) ltac:(lia)).
           ++ destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 (q - 1) 1 HAR2 ltac:(lia) ltac:(rewrite Elo; lia)
                ltac:(rewrite Ehi; lia)) as [_ Hh].
              exact (trans_hull_sub _ (q - 1) 1 q n Hh ltac:(lia) ltac:(lia)).
        -- exact (proj2 (Hsh ly2 S2 W2 mem2 md2 HAR2)).
Qed.

(* The TRANS_RO_RD bytes at a later state whose memory the call's acall_kept_g relates to the entry's: they are
   image bytes outside G (below G_HARNESS_B_LO), the owned statics and errno. *)
Lemma wmb_rom : trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc (W2 : world segs) mem2 slo shi (Eo : Z -> Prop),
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 slo shi Eo ->
  trans_rom_view_rd W memc -> trans_rom_view_rd W2 mem2.
Proof.
  intros HRU HRE lyc Sc W memc W2 mem2 slo shi Eo (_ & _ & K3 & _) Hrom a Ha.
  rewrite <- (Hrom a Ha). destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
  apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TG.G_HARNESS_B_LO in Gh. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The mid piece                                                   *)
(* ------------------------------------------------------------------ *)

Lemma wakeb_mid : @wakeb_mid_stmt fx rc B MT.
Proof.
unfold wakeb_mid_stmt. intros E2C.
unfold wakeb_mid_at. intros HLAWS AI0 SS0.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' B1 e2 rs pos sp1 F ly2 S2 W2
  mem2 md2 e regs2 HFIX HMID HREGS.
pose proof HLAWS as (HPCS & HCELLS & HZ & HGU & HGNE0 & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof HFIX as (HJe & Hra & Hra4 & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw & Hfn & Hm & HTF0
  & HTFO0 & HROM0 & HAP & Hfly & Hcmd & Hcnt1 & Hcnt2 & Hev & Esp1 & EF & HF4096 & HF64 & HFc & HFapp).
pose proof HMID as (HCUR & Hdk & Hfor & HSC & Hrs & He2 & HST1 & HGOT1 & Htw1 & Hfn1 & Hg8e2 & Hrd2 & Hg8klp).
pose proof HCUR as (HJ & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL).
pose proof HREGS as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q24 & Q25 & Q27) & Q19 & Q20 & Q21 & Q22 & Q26).
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _ & _ & _ & ESLO & ESHI & _).
pose proof HJ as (_ & _ & (memS2 & HJi2 & _) & _).
pose proof HJi2 as (_ & Hlyle2 & _).
pose proof Hlyle2 as (_ & _ & _ & _ & _ & ELF2 & _ & _ & _ & ESLO2 & ESHI2 & _).
clear HJi2 memS2.
assert (ESLO2c : ly_stk_lo ly2 = ly_stk_lo lyc) by (rewrite ESLO2, ESLO; reflexivity).
assert (ESHI2c : ly_stk_hi ly2 = ly_stk_hi lyc) by (rewrite ESHI2, ESHI; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wakeb_stk_bounds as (WS1 & WS2 & WS3 & WS4 & WS5 & WS6).
assert (CS : WAKE_S = 6157888) by reflexivity.
assert (CT : TB_g_s = 6157888) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HEVS : SSTATE_EV = 0) by reflexivity.
assert (HSTKLT : ly_stk_lo lyc < ly_stk_hi lyc) by (rewrite ESLO, ESHI; lia).
unfold WAKEB_FBYTES in HFc, HFapp, HFL.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (can_sp1_facts (spZ regs + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
replace (32 * ((spZ regs + -128) / 32)) with sp1 in Hsp1r, Hsp1al, Hsp1al16
  by (rewrite Esp1; unfold WAKE_FRAME; f_equal; f_equal; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJe) as HAR.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
assert (Hin2 : In (WAKE_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Efa2 : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite HlyF; reflexivity).
assert (EFA : frame_addr ly2 WAKE_CID pos = F) by (rewrite Efa2; exact (eq_sym EF)).
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
assert (NGF : forall a, F <= a < F + 128 -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  apply (frm_img segs B LAWS _ _ _ _ _ WAKE_CID pos a HAR2 Hin2); [|exact Hi].
  rewrite EFA. change (fs_frame_bytes WAKE_CID) with 128. lia. }
set (FL := flag_addr lyc WAKE_CID pos) in *.
(* the values the entry state's chunks hold: B1's bytes *)
assert (HLB1 : length B1 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw1).
set (TX := TW.u_at B1 (TW.OFF_g_s + 18224) 8).
set (HC := TW.u_at B1 (TW.OFF_g_s + 160) 4).
assert (RTX : 0 <= TX < 2 ^ 64) by exact (TWL.u_at_range B1 _ 8).
assert (RHC : 0 <= HC < 2 ^ 32) by exact (TWL.u_at_range B1 _ 4).
assert (V160 : val_mem segs (mrestrict (w_H W2) mem2) (WAKE_S + 160) 4 HC)
  by exact (tw_read_val segs _ TMAP_B B1 TW.OFF_g_s TB_g_s TW.SZ_g_s 160 4 TMAP_B_ok Htw1 TMAP_B_g_s
              ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
assert (V18224 : val_mem segs (mrestrict (w_H W2) mem2) (WAKE_S + 18224) 8 TX)
  by exact (tw_read_val segs _ TMAP_B B1 TW.OFF_g_s TB_g_s TW.SZ_g_s 18224 8 TMAP_B_ok Htw1 TMAP_B_g_s
              ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
unfold WAKEB_KLPOFF in Hg8klp. pose proof (wmb_klp_val _ _ Hg8klp) as Vklp.
change (TW.A_S_stats_tx_wakes - TW.OFF_g_s) with 18224 in Q21.
unfold WAKEB_E2OFF in Q22, Hg8e2, Hrd2. unfold SENDCTL_F in Hrd2.
destruct (wmb_entry0 ly2 S2 W2 regs2 mem2 md2 TX HC sp1 HZ HAR2 Q9 ltac:(lia) Hsp1al Q20 Q21 Q26
  RTX RHC Vklp V160 V18224) as [HS SHOK].
set (E0 := wmb_E regs2 TX HC) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, wmb_E; apply Eimg_env).
assert (EE0 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = YK11.getr regs2 rr)
  by (intros n rr Hn; unfold E0, wmb_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U20 : bv_unsigned (ew E0 20) = WAKE_S)
  by (rewrite (EE0 20%nat 20%bv eq_refl), Q20; apply unsigned_lit_small; rewrite CS; lia).
assert (U21 : bv_unsigned (ew E0 21) = WAKE_S + 18224)
  by (rewrite (EE0 21%nat 21%bv eq_refl), Q21; apply unsigned_lit_small; rewrite CS; lia).
assert (U26 : bv_unsigned (ew E0 26) = SHADOW_OFF)
  by (rewrite (EE0 26%nat 26%bv eq_refl), Q26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U9 : bv_unsigned (ew E0 9) = sp1) by (rewrite (EE0 9%nat 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
assert (E33 : ew E0 33 = Z_to_bv 64 TX)
  by (unfold E0, wmb_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 HC)
  by (unfold E0, wmb_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
(* run 1, +0x224 .. +0x234 *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ wmb_awr U20 U21. }
rename HF into HF1, HFr into HFr1, HG into HG1.
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
rename ms into ms1.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ wmb_win a ->
  aview segs (w_H W2) (ms_mem ms1) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ wmb_win HFr1); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. unfold wmb_win. wmb_wins Hin Hx U20 U21. }
wmb_reg HS (10%bv : bv 5) (w64 (WAKE_S + 216)) Ra10 ltac:(cbn [sv_denot]; rewrite U20; reflexivity).
wmb_reg HS (11%bv : bv 5) (w64 (F + 32)) Ra11
  ltac:(cbn [sv_denot]; rewrite (EE0 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q22).
wmb_reg HS (12%bv : bv 5) (w64 60) Ra12 ltac:(reflexivity).
wmb_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 22992)) Ra1 ltac:(apply codeptr_val; exact HEI).
wmb_reg HS (2%bv : bv 5) (w64 sp1) Ra2
  ltac:(cbn [sv_denot]; rewrite (EE0 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q2).
wmb_reg HS (3%bv : bv 5) (w64 (as_gp B)) Ra3
  ltac:(cbn [sv_denot]; rewrite (EE0 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans Q3 Hgp)).
wmb_reg HS (4%bv : bv 5) (w64 (as_tp B)) Ra4
  ltac:(cbn [sv_denot]; rewrite (EE0 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans Q4 Htp)).
assert (Hsp1 : spZ (ms_regs ms1) = sp1) by (unfold spZ at 1; rewrite Ra2; apply unsigned_lit_small; lia).
(* e2's read facts at the memory of the call *)
assert (Hrd1 : decode_rd_ok W2 (ms_mem ms1) (F + 32) 60).
{ apply (trans_rd_ok_view W2 W2 mem2 (ms_mem ms1) (F + 32) 60 Hrd2).
  - intros a Ha. apply K1; [lia|]. intros X. apply (NGF a ltac:(lia)). apply wmb_inG.
    unfold wmb_win, TW.SZ_g_s in *. lia.
  - intros s Hs. apply K1; [lia|]. unfold wmb_win. rewrite CS. lia. }
destruct Hrd1 as (Hv1 & Hra1 & Hh1 & Ham1 & Hq1 & Hq1').
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
destruct (decode_zshadow_ra B ly2 S2 W2 (ms_mem ms1) md1 WAKE_S (WAKE_S + TW.SZ_g_s) (WAKE_S + 216) 60 HAR1 HZ
  ltac:(lia) ltac:(rewrite CS; apply Z.leb_le; vm_compute; reflexivity)
  ltac:(rewrite CS; unfold TW.SZ_g_s; apply Z.leb_le; vm_compute; reflexivity)) as [HraD HhD].
(* +0x234: __asan_memcpy (s + 216, e2, 60) *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OCpy (transportb_sigma TB___asan_memcpy)
    (AI0 fx) TG.G_HARNESS_B W2 (ms_regs ms1) (ms_mem ms1) STK sp0 FP ly S W0 mem0 md0 ((WAKE_CID, pos) :: own) ly2 S2
    md1 (k + e) (WAKE_S + 216) (F + 32) 60 (sp1 - sp0) (Z_to_bv 64 (BASE + 22992)) HGX G_HARNESS_B_rw HJ Ra10 Ra11
    Ra12).
  - lia.
  - rewrite CS. lia.
  - rewrite CS. lia.
  - rewrite Hsp1. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact Ra3.
  - exact Ra4.
  - exact Ra1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right. apply wmb_inG.
    unfold TW.SZ_g_s. lia.
  - left. rewrite C5, CS. lia.
  - exact HraD.
  - intros _. exact HhD.
  - cbv beta iota. refine (conj _ (conj _ (conj _ (conj _ (conj Ham1 (conj Hra1 (fun _ => Hh1))))))).
    + lia.
    + lia.
    + intros a Ha. split; [exact (Hv1 a Ha) | rewrite Hsp1; lia].
    + destruct (Z_le_gt_dec (WAKE_S + 216 + 60) (F + 32)) as [Hd|Hd]; [left; exact Hd|].
      destruct (Z_le_gt_dec (F + 32 + 60) (WAKE_S + 216)) as [Hd'|Hd']; [right; exact Hd'|].
      exfalso. apply (NGF (Z.max (WAKE_S + 216) (F + 32))); [lia|]. apply wmb_inG.
      unfold TW.SZ_g_s; lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & H10c & Hcpy & Heff & Hgr3).
cbv beta iota in Hcpy.
(* the five regions, kept by the call *)
jafter_call_keep_hi HS 1024%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0%nat; 1%nat; 2%nat; 3%nat; 4%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 9%nat sp1); [exact U9 | | exact Hgr3]. intros a Ha. apply Heff; lia.
  - apply (region_kept_aview _ _ _ _ 20%nat WAKE_S); [exact U20 | | exact Hgr3]. intros a Ha. rewrite CS in Ha.
    apply Heff; rewrite ?CS; lia.
  - apply (region_kept_aview _ _ _ _ 20%nat WAKE_S); [exact U20 | | exact Hgr3]. intros a Ha. rewrite CS in Ha.
    apply Heff; rewrite ?CS; lia.
  - apply (region_kept_aview _ _ _ _ 20%nat WAKE_S); [exact U20 | | exact Hgr3]. intros a Ha. rewrite CS in Ha.
    apply Heff; rewrite ?CS; lia.
  - apply (region_kept_aview _ _ _ _ 21%nat (WAKE_S + 18224)); [exact U21 | | exact Hgr3]. intros a Ha.
    rewrite CS in Ha. apply Heff; rewrite ?CS; lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regs3) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (U20a : bv_unsigned (ew E1 20) = WAKE_S) by (rewrite E1lo by lia; exact U20).
assert (U21a : bv_unsigned (ew E1 21) = WAKE_S + 18224) by (rewrite E1lo by lia; exact U21).
assert (U26a : bv_unsigned (ew E1 26) = SHADOW_OFF) by (rewrite E1lo by lia; exact U26).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
pose proof (wmb_shok _ _ _ _ _ E1 HZ HAR3 U20a U21a U26a) as SHOK1.
clear SHOK.
(* run 2, +0x238 .. +0x2f4 *)
paj_run_tok RUN HS HJ3 SHOK1 YC4b.Bspan.
{ wmb_awr U20a U21a. }
rename HF into HF2, HFr into HFr2, HG into HG2.
set (md5 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md5. clear mat.
rename ms into ms5.
lazymatch type of HS with
| st_ok_pi _ _ ?EF _ _ => set (E5 := EF) in *
| OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ _ => set (E5 := EF) in *
end.
assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew E0 n).
{ intros n Hn. unfold E5. repeat rewrite ew_ewset_other by lia. apply E1lo. exact Hn. }
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ wmb_win a ->
  aview segs (w_H W2) (ms_mem ms5) a = aview segs (w_H W2) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ wmb_win HFr2); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. unfold wmb_win. wmb_wins Hin Hx U20a U21a. }
(* the registers at `jal set_state` *)
wmb_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 23184)) X1 ltac:(apply codeptr_val; assumption).
wmb_reg HS (10%bv : bv 5) (w64 WAKE_S) X10
  ltac:(cbn [sv_denot]; rewrite (E5lo 20%nat ltac:(lia)), (EE0 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact Q20).
wmb_reg HS (11%bv : bv 5) (w64 1) X11 ltac:(reflexivity).
wmb_reg HS (12%bv : bv 5) (w64 1) X12 ltac:(reflexivity).
wmb_reg HS (2%bv : bv 5) (w64 sp1) X2
  ltac:(cbn [sv_denot]; rewrite (E5lo 2%nat ltac:(lia)), (EE0 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q2).
wmb_reg HS (3%bv : bv 5) (w64 (as_gp B)) X3
  ltac:(cbn [sv_denot]; rewrite (E5lo 3%nat ltac:(lia)), (EE0 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans Q3 Hgp)).
wmb_reg HS (4%bv : bv 5) (w64 (as_tp B)) X4
  ltac:(cbn [sv_denot]; rewrite (E5lo 4%nat ltac:(lia)), (EE0 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans Q4 Htp)).
wmb_reg HS (8%bv : bv 5) (w64 (spZ regs)) X8
  ltac:(cbn [sv_denot]; rewrite (E5lo 8%nat ltac:(lia)), (EE0 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q8).
wmb_reg HS (9%bv : bv 5) (w64 sp1) X9
  ltac:(cbn [sv_denot]; rewrite (E5lo 9%nat ltac:(lia)), (EE0 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q9).
wmb_reg HS (18%bv : bv 5) (w64 F) X18
  ltac:(cbn [sv_denot]; rewrite (E5lo 18%nat ltac:(lia)), (EE0 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact Q18).
wmb_reg HS (24%bv : bv 5) (w64 (SHADOW_OFF + F / 8)) X24
  ltac:(cbn [sv_denot]; rewrite (E5lo 24%nat ltac:(lia)), (EE0 24%nat 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact Q24).
wmb_reg HS (25%bv : bv 5) (w64 F) X25
  ltac:(cbn [sv_denot]; rewrite (E5lo 25%nat ltac:(lia)), (EE0 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact Q25).
wmb_reg HS (27%bv : bv 5) (YK11.getr regs 27) X27
  ltac:(cbn [sv_denot]; rewrite (E5lo 27%nat ltac:(lia)), (EE0 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact Q27).
(* run 2's stores, read from its regions *)
pose proof (can_region_nth (segs := segs) E5 _ (restrict (w_H W2) ms5) 2 _ HS eq_refl) as RG2.
cbn [ms_mem restrict] in RG2.
pose proof (can_region_nth (segs := segs) E5 _ (restrict (w_H W2) ms5) 3 _ HS eq_refl) as RG3.
cbn [ms_mem restrict] in RG3.
pose proof (can_region_nth (segs := segs) E5 _ (restrict (w_H W2) ms5) 4 _ HS eq_refl) as RG4.
cbn [ms_mem restrict] in RG4.
assert (U20f : bv_unsigned (ew E5 20) = WAKE_S) by (rewrite E5lo by lia; exact U20).
assert (U21f : bv_unsigned (ew E5 21) = WAKE_S + 18224) by (rewrite E5lo by lia; exact U21).
pose proof (wmb_field _ _ _ _ _ _ _ _ _ _ 212 4 (SLit 1) 1 RG2 U20f ltac:(wmb_in) eq_refl ltac:(lia)) as VINF.
pose proof (wmb_field _ _ _ _ _ _ _ _ _ _ 1736 8 (SLit 60) 60 RG3 U20f ltac:(wmb_in) eq_refl ltac:(lia)) as VLEN.
pose proof (wmb_field _ _ _ _ _ _ _ _ _ _ 1748 4 (SLit 0) 0 RG3 U20f ltac:(wmb_in) eq_refl ltac:(lia)) as VRET.
pose proof (wmb_field _ _ _ _ _ _ _ _ _ _ 1744 4 (SExt true 32 (SOff 34 0)) (bv_swrap 32 HC) RG3 U20f ltac:(wmb_in)
  (wmb_sext E5 34 HC ltac:(rewrite E5lo by lia; exact E34) RHC) ltac:(lia)) as VCNT.
pose proof (wmb_field _ _ _ _ _ _ _ _ _ _ 1752 8 (SOff 19 0) now RG3 U20f ltac:(wmb_in)
  ltac:(cbn [sv_denot]; rewrite (E5lo 19%nat ltac:(lia)), (EE0 19%nat 19%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Q19) ltac:(lia)) as VSENT.
pose proof (wmb_field _ _ _ _ _ _ _ _ _ _ 0 8 (SOff 33 1) (TX + 1) RG4 U21f ltac:(wmb_in)
  ltac:(cbn [sv_denot]; rewrite (E5lo 33%nat ltac:(lia)), E33, unsigned_lit_small by lia; reflexivity)
  ltac:(lia)) as VTX.
clear RG2 RG3 RG4.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR5.
set (m5 := ms_mem ms5) in *.
(* every byte outside the ESTACK window below sp1 and wmb_wr is the one at the mid cut *)
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp1 - ESTACK <= a < sp1) \/ wmb_wr a) ->
  aview segs (w_H W2) m5 a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. unfold wmb_wr in Hn.
  rewrite (K3 a Ha ltac:(intros X; apply Hn; right; right; exact X)).
  rewrite (Heff a Ha ltac:(intros X; apply Hn; right; left; lia) ltac:(intros X; apply Hn; left; lia)).
  exact (K1 a Ha ltac:(intros X; apply Hn; right; right; exact X)). }
assert (GR5 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) m5 a).
{ intros a Ha. apply (apresent_grows _ _ _ a HG2). apply Hgr3. exact (apresent_grows _ _ _ a HG1 Ha). }
(* what the call keeps, at m5 *)
assert (KG5 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 m5 (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw)).
{ apply (TransportGFrame.dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2 m5
    (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw) (fun a => (sp1 - ESTACK <= a < sp1) \/ wmb_wr a) HAR HK KALL GR5).
  - intros a [X|X] Hc; [lia|]. exfalso.
    pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX (proj2 (wmb_wr_in Bw a X))) as Hl. lia.
  - intros b m i Hb Hi [X|X]; [|exact (proj1 (wmb_wr_in Bw _ X))]. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
  - intros a [X|X] Hi HnG _ _.
    + pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
    + exact (HnG (proj2 (wmb_wr_in Bw _ X))).
  - intros cid pos0 a Hin Hr [X|X]; [|exact (proj1 (wmb_wr_in Bw _ X))]. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos0 HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos0) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos0 + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
(* the world relation at wake_w3 B1 e2 now *)
destruct (wmb_w3_keep B1 e2 now HLB1 He2) as (HL2 & HL3 & EST3 & EGOT3 & EFN3).
assert (HWS : Forall (fun w => 0 <= fst w /\ fst w + Z.of_nat (length (snd w)) <= TW.SZ_g_s /\
    forall j, (j < length (snd w))%nat ->
      aview segs (w_H W2) m5 (TB_g_s + fst w + Z.of_nat j) = Some (bv_unsigned (nth j (snd w) (Z_to_bv 8 0))))
  (wmb_ws B1 e2 now)).
{ unfold wmb_ws. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [lia|]);
    (split; [rewrite ?TWL.length_put, ?He2; unfold TW.SZ_g_s; lia|]); intros j Hj; rewrite ?TWL.length_put in Hj.
  - rewrite He2 in Hj.
    rewrite (K3 (TB_g_s + 216 + Z.of_nat j) ltac:(rewrite CT; lia) ltac:(unfold wmb_win; rewrite CS, CT; lia)).
    change TB_g_s with WAKE_S. rewrite (Hcpy (Z.of_nat j) ltac:(lia)).
    rewrite (K1 (F + 32 + Z.of_nat j) ltac:(lia)
      ltac:(intros X; apply (NGF (F + 32 + Z.of_nat j) ltac:(lia)); apply wmb_inG; unfold wmb_win, TW.SZ_g_s in X |- *;
            lia)).
    rewrite (wmb_aview_garr8 _ _ _ _ j Hg8e2 ltac:(unfold TW.zs; rewrite length_map; lia)).
    rewrite wmb_nth_zs. reflexivity.
  - rewrite He2. change (Z.of_nat 60) with 60. rewrite tw_le_byte_put by exact Hj. exact (VLEN j Hj).
  - rewrite (wmb_tx_eq B1 e2 HLB1 He2). fold TX. rewrite wk_put8_u64 by lia.
    rewrite tw_le_byte_put by exact Hj. pose proof (VTX j Hj) as V. rewrite Z.add_0_r in V. exact V.
  - rewrite tw_le_byte_put by exact Hj. exact (VINF j Hj).
  - unfold TW.S_host_counter. rewrite wk_put4_s32. unfold TW.s32_at. rewrite (wmb_hc_eq B1 e2 HLB1 He2). fold HC.
    rewrite tw_le_byte_put by exact Hj. exact (VCNT j Hj).
  - rewrite tw_le_byte_put by exact Hj. exact (VRET j Hj).
  - rewrite tw_le_byte_put by exact Hj. exact (VSENT j Hj). }
assert (HWO : forall x, tw_in TMAP_B x ->
  Forall (fun w => ~ (TB_g_s + fst w <= x < TB_g_s + fst w + Z.of_nat (length (snd w)))) (wmb_ws B1 e2 now) ->
  aview segs (w_H W2) m5 x = aview segs (w_H W2) mem2 x).
{ intros x Hx Hall. unfold wmb_ws in Hall. rewrite !Forall_cons_iff in Hall.
  destruct Hall as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & _). cbn [fst snd] in N1, N2, N3, N4, N5, N6, N7.
  rewrite He2 in N1. rewrite !TWL.length_put in N2, N3, N4, N5, N6, N7.
  assert (Hg : inG TG.G_HARNESS_B x).
  { destruct Hx as (o & b & n & Hin & Hb). exact (wmb_inG_row b n x (TMAP_B_in_G o b n Hin) Hb). }
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX Hg) as Hl.
  apply KALL; [lia|]. intros [X|X]; [lia|]. unfold wmb_wr, wmb_win in X. rewrite CS in X.
  rewrite CT in N1, N2, N3, N4, N5, N6, N7. lia. }
assert (TW5 : tw_at TMAP_B (aview segs (w_H W2) m5) (wake_w3 B1 e2 now)).
{ rewrite <- wmb_ws_w3.
  exact (wmb_writes TMAP_B TW.OFF_g_s TB_g_s TW.SZ_g_s (wmb_ws B1 e2 now) _ _ B1 TMAP_B_ok TMAP_B_g_s Htw1 HWS HWO). }
(* the model: wake_model on wakeb_mid_cur's path, rs >= 0, then set_state_m *)
rewrite wake_model in Hm.
rewrite (proj2 (Z.eqb_neq _ _) Hdk) in Hm. rewrite Hfor in Hm. change (negb (0 =? 0)) with false in Hm.
rewrite HSC in Hm. cbv beta iota in Hm. rewrite (proj2 (Z.ltb_ge _ _) Hrs) in Hm. cbv beta iota in Hm.
destruct (TSS.set_state_m timg_B TF (wake_w3 B1 e2 now) TS0.DIGINET_S_WAKING TS0.DIGINET_R_WAKE) as [[B2 u2]|] eqn:ESS;
  [|discriminate Hm].
destruct (wakeb_some_inv _ _ _ _ Hm) as [EB2 Er].
destruct u2. rewrite EB2 in ESS.
(* set_state's class-2 frame: the own frame is of class 1 *)
assert (HCNT : count_cid SSTATE_CID (frames S2) < fs_frames SSTATE_CID).
{ rewrite Hfrs. change (count_cid 2 (frames Sc) < fs_frames 2). unfold SENDCTL_CID in Hcnt2. lia. }
(* +0x2f4: `jal set_state`, a G-form callee in the same G journal *)
pmkst HS.
set (regsC := ms_regs ms5) in *.
assert (USPC : spZ regsC = sp1) by (unfold spZ at 1; rewrite X2; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_set_state) rg mm mdx) Q) end.
assert (EBR : BASE + 23184 = 0x86d30) by reflexivity.
eapply SRr_bind.
{ exact (SS0 fx STK sp0 FP ly S W0 mem0 md0 ((WAKE_CID, pos) :: own) ly2 S2 W2 m5 md5 (k + e) regsC
    TS0.DIGINET_S_WAKING TS0.DIGINET_R_WAKE TF (wake_w3 B1 e2 now) Bw'
    HJ3
    ltac:(rewrite X1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite X1, EBR; rewrite unsigned_lit_small by lia; lia)
    X3 X4 X10 X11 X12
    ltac:(rewrite USPC; exact Hsp1al16)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    TW5
    ltac:(rewrite EFN3; exact Hfn1)
    ESS
    ltac:(unfold TS0.DIGINET_S_WAKING; lia) ltac:(unfold TS0.DIGINET_R_WAKE; lia)
    (wmb_tframe LAWS HROU HRNE lyc Sc W memc mdc ly2 S2 W2 m5 md5 regs regsC SSTATE_STK TF Bw WAKE_CID pos
       HAR HAR5 Hfrs Hbl Efa2 ESLO2c ESHI2c HSTKLT KG5 HAP HTFO0 ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
       HTF0)
    (wmb_rom HROU HRNE lyc Sc W memc W2 m5 _ _ _ KG5 HROM0)
    (fun x Hx fr Hfr =>
       HAP x (wmb_swr Bw (wake_w3 B1 e2 now) x HL3 (eq_trans EST3 HST1) (eq_trans EGOT3 HGOT1) Hx) fr Hfr)
    HCNT
    ltac:(rewrite HEVS; lia)). }
intros WR cR _ HPOST.
unfold transport_sstate_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (lyR & SR & regsR & memR & mdR & e3 & -> & He3 & HJR & HPR & HfrR & HpermR & HKR & HmoR &
  (HtwR & HfnR)).
assert (He30 : e3 = 0) by (rewrite HEVS in He3; lia). subst e3.
pose proof HJR as (_ & _ & (memSR & HJiR & _) & _).
pose proof HJiR as (HARR & HlyleR & _). pose proof HlyleR as (_ & _ & _ & _ & _ & ELFR & _).
clear HJiR memSR.
assert (ELFRc : ly_F lyR = ly_F lyc) by (rewrite ELFR, ELF; reflexivity).
(* what the call kept, from its entry to set_state's return *)
destruct (TransportGFrame.dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 m5 md5 WAKE_CID pos F FL
  HAR5 Hfrs Hbl HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
assert (KC3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc WR memR (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 m5 WR memR
    (spZ regs - WAKE_STK) (spZ regs) (spZ regsC - SSTATE_STK) (spZ regsC) (wake_wr Bw)
    (sstate_wr (wake_w3 B1 e2 now) TS0.DIGINET_S_WAKING TS0.DIGINET_R_WAKE) (dkg_nf WAKE_CID F FL)).
  - lia.
  - lia.
  - exact Efa2.
  - intros f Hf. rewrite Hfrs. right. exact Hf.
  - exact Hbl.
  - exact N1.
  - exact N3.
  - exact KG5.
  - exact HKR.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. left.
    exact (wmb_swr Bw (wake_w3 B1 e2 now) a HL3 (eq_trans EST3 HST1) (eq_trans EGOT3 HGOT1) Ha). }
pose proof HKR as (KR1 & _ & _ & KR4 & _).
(* the bytes the release reads: the saved words above sp1 and the frame's last word *)
assert (KSTK : forall a, sp1 <= a < spZ regs -> aview segs (w_H WR) memR a = aview segs (w_H W2) mem2 a).
{ intros a Ha. rewrite USPC in KR1. rewrite KR1 by lia.
  apply KALL; [lia|]. intros [X|X]; [lia|].
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX (proj2 (wmb_wr_in Bw _ X))). lia. }
assert (KFL : forall i, 0 <= i < 8 ->
  aview segs (w_H WR) memR (F + 120 + i) = aview segs (w_H W2) mem2 (F + 120 + i)).
{ intros i Hi.
  assert (Hr : in_zr (F + 120 + i) (frame_rng ly2 (WAKE_CID, pos)) \/
               in_zr (F + 120 + i) (shadow_addr (frame_addr ly2 WAKE_CID pos), fs_frame_bytes WAKE_CID / 8)).
  { left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes WAKE_CID) with 128. lia. }
  assert (HnE : ~ sstate_wr (wake_w3 B1 e2 now) TS0.DIGINET_S_WAKING TS0.DIGINET_R_WAKE (F + 120 + i)).
  { intros Hw. apply (NGF (F + 120 + i) ltac:(lia)).
    exact (wmb_wr_G Bw _ (wmb_swr Bw (wake_w3 B1 e2 now) _ HL3 (eq_trans EST3 HST1) (eq_trans EGOT3 HGOT1) Hw)). }
  refine (eq_trans (KR4 WAKE_CID pos (F + 120 + i) Hin2 Hr HnE) _).
  apply KALL; [lia|]. intros [X|X]; [lia|]. exact (NGF (F + 120 + i) ltac:(lia) (proj2 (wmb_wr_in Bw _ X))). }
(* the registers set_state kept *)
assert (CH : forall n, acallee_saved n -> YK11.getr regsR (Z_to_bv 5 n) = YK11.getr regsC (Z_to_bv 5 n))
  by (intros n Hn; exact (HPR n Hn)).
assert (Z2 : YK11.getr regsR (Z_to_bv 5 2) = w64 sp1) by exact (eq_trans (CH 2 ltac:(hnf; lia)) X2).
assert (Z3 : YK11.getr regsR (Z_to_bv 5 3) = YK11.getr regs 3)
  by exact (eq_trans (CH 3 ltac:(hnf; lia)) (eq_trans X3 (eq_sym Hgp))).
assert (Z4 : YK11.getr regsR (Z_to_bv 5 4) = YK11.getr regs 4)
  by exact (eq_trans (CH 4 ltac:(hnf; lia)) (eq_trans X4 (eq_sym Htp))).
assert (Z8 : YK11.getr regsR (Z_to_bv 5 8) = w64 (spZ regs)) by exact (eq_trans (CH 8 ltac:(hnf; lia)) X8).
assert (Z9 : YK11.getr regsR (Z_to_bv 5 9) = w64 sp1) by exact (eq_trans (CH 9 ltac:(hnf; lia)) X9).
assert (Z18 : YK11.getr regsR (Z_to_bv 5 18) = w64 F) by exact (eq_trans (CH 18 ltac:(hnf; lia)) X18).
assert (Z24 : YK11.getr regsR (Z_to_bv 5 24) = w64 (SHADOW_OFF + F / 8))
  by exact (eq_trans (CH 24 ltac:(hnf; lia)) X24).
assert (Z25 : YK11.getr regsR (Z_to_bv 5 25) = w64 F) by exact (eq_trans (CH 25 ltac:(hnf; lia)) X25).
assert (Z27 : YK11.getr regsR (Z_to_bv 5 27) = YK11.getr regs 27) by exact (eq_trans (CH 27 ltac:(hnf; lia)) X27).
(* +0x2f8: `li a0, 0`, to the e2 cut +0x2fc, from a state with no region *)
rewrite X1. change (Z_to_bv 64 (BASE + 23184)) with (Z_to_bv 64 (BASE + WMB_C3)).
pose proof (wmb_entry3 WR regsR memR) as HS3.
assert (HEI3 : img_env VAL A_LIM (wmb_E3 regsR)) by (unfold wmb_E3; apply Eimg_env).
assert (EE3 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (wmb_E3 regsR) n = YK11.getr regsR rr)
  by (intros n rr Hn; unfold wmb_E3; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK3 : sh_ok segs (SOff 32 0) (@nil shent) (wmb_E3 regsR) (mrestrict (w_H WR) memR)) by constructor.
paj_run_to_tok RUNTO HS3 HJR SHOK3 WMB_B0 WAKEB_E2.
{ wmb_awr0. }
wmb_after_cut HS3 WR KD GR memR msF.
wmb_kreg HS3 EE3 (Z_to_bv 5 2) 2%nat Z2 Y2. wmb_kreg HS3 EE3 (Z_to_bv 5 3) 3%nat Z3 Y3.
wmb_kreg HS3 EE3 (Z_to_bv 5 4) 4%nat Z4 Y4. wmb_kreg HS3 EE3 (Z_to_bv 5 8) 8%nat Z8 Y8.
wmb_kreg HS3 EE3 (Z_to_bv 5 9) 9%nat Z9 Y9. wmb_kreg HS3 EE3 (Z_to_bv 5 18) 18%nat Z18 Y18.
wmb_kreg HS3 EE3 (Z_to_bv 5 24) 24%nat Z24 Y24. wmb_kreg HS3 EE3 (Z_to_bv 5 25) 25%nat Z25 Y25.
wmb_kreg HS3 EE3 (Z_to_bv 5 27) 27%nat Z27 Y27.
wmb_reg HS3 (Z_to_bv 5 10) (w64 0) Y10 ltac:(reflexivity).
pmkst HS3.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WAKEB_E2)) mm rom) mdx) Q) end.
apply (E2C HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F lyR SR WR
  (ms_mem msF) _ e (ms_regs msF) HFIX).
- split; [|split].
  + split; [replace (k + e) with (k + e + 0) by lia; exact HJR|].
    split; [exact He|].
    split; [rewrite HfrR; exact Hfrs|].
    split; [exact (Permutation_trans HpermR Hperm)|].
    split; [exact ELFRc|].
    split; [exact (mo_le_trans MT MTL _ _ _ _ _ HMO HmoR)|].
    split.
    { apply (TransportGFrame.dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc WR memR
        (ms_mem msF) (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw) (fun _ => False) HAR KC3).
      - intros a _ _. exact (KD a).
      - exact GR.
      - intros a [].
      - intros b m i _ _ [].
      - intros a [].
      - intros cid pos0 a _ _ []. }
    split.
    { rewrite Forall_forall in HSV |- *. intros o Ho. rewrite <- (HSV o Ho).
      assert (Hob : 8 <= fst o <= 96).
      { unfold WAKEB_SAVED in Ho. cbn [In] in Ho.
        repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
      apply YCbq.rdword_ext. intros i Hi. rewrite KD. apply KSTK. lia. }
    { unfold WAKEB_FBYTES. change (flag_addr lyc WAKE_CID pos) with FL. rewrite <- HFL.
      replace (F + 128 - 8) with (F + 120) by lia.
      apply YCbq.rdword_ext. intros i Hi. rewrite KD. exact (KFL i Hi). }
  + apply (tw_kept TMAP_B (aview segs (w_H WR) memR)); [exact HtwR | intros x _; exact (KD x)].
  + exact HfnR.
- refine (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 (conj Y24 (conj Y25 Y27)))))))) _).
  exact (eq_trans Y10 (f_equal w64 Er)).
Qed.

End wmb.

Print Assumptions wakeb_mid.
