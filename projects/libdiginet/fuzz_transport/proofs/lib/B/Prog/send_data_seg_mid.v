(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its numbers changed; 1131 of its 1294 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickWake.v, with its module paths and module names changed; 1607 of its 1714 lines of code are new or changed and 1187 lines of the source are left out. *)
(* send_data_seg_mid: Lemma sd_mid : sd_mid_stmt (lib/B/Prog/send_data_segs.v), the middle piece of image B's
   G-form walk of send_data (fuzz_transport.asan-ubsan 0x89d78 = transportb_sigma TB_send_data), offsets +0x188 ..
   +0x2a8 of the listing lib/B/Prog/DgnTransportBList.v (0x89f00 .. 0x8a020). Image B's twin of
   lib/A/Prog/send_data_seg_mid.v: the same instructions in the same order, 8 bytes further on, with image B's branch
   immediates to its slow paths (which start at +0x360). It takes the release cut sd_rel_at and gives the cut SD_FB,
   sd_fb_at: from the state the head leaves at `mv a2, a0` it walks to the release cut SD_REL on each of the three
   paths the code has. No UBSan check lies on this stretch.

   The model (lib/TModel/TSess.v send_data_m) decides which path the machine takes, so no machine branch is split by
   the engine: each path carries its own symbolic state whose facts already hold the branch the model forces
   (YP0m.v acond; the engine's decide_cond2 reads them).
     n < 0 (:395-396, ss_neg):  +0x188 `mv a2, a0`, +0x18c `bltz a0` TAKEN to +0x2ac. No region, so the run changes
                                no byte; the model's world is sd_M1 Bw ncmds and the result is n.
     0 <= n (ss_mid):           +0x190 .. +0x280. Seven regions on g_s's payload (the two 8-byte cells at s + 64 and
                                s + 72, the 4 bytes at s + 160, the written spans [s + 212, s + 216),
                                [s + 1736, s + 1760) and [s + 18200, s + 18208)), the slot s1 + 16 that holds now,
                                and the shadow byte of s + 160 the head left in s5. Every instrumented check reads
                                g_s, whose payload has shadow 0 (trans_senddata_cells), so the token engine's shadow
                                entry [s, s + 18264) decides all ten of them and no __asan_report_* is reached. The
                                six stores are :397's inflight_len, inflight_start's four (:113-116) and :399's
                                read-modify-write of stats.tx_data; they make the model's world sd_B8 (sdm_six: the
                                binary stores :397 before :113, each value modulo its field's width). The run stops
                                at `jalr ra, 0(a3)` (+0x280), a3 = g_s.io.send, which the model's call_send forces to
                                be TI.ti_io_send timg_B; DgnTransportBPaLib.v SRr_jalr_call_pi takes the call and
                                io_send_cg.v transport_io_send_cg applies at that address in the same G journal.
     r <> 0 (send_raw :93, ss_fail):  +0x284 `mv a2, a0`, +0x288 `bnez a0` TAKEN to +0x2ac; no region, nothing
                                changes, and the model's world is io_send's.
     r = 0 (send_raw :91-92, ss_mid2): +0x28c .. +0x2a8, one checked read-modify-write of stats.tx_frames at
                                s + 18192 and a2 = 0.
   What the call keeps: each run writes only bytes of G (TransportGCg.v dk_kept_step_gw through sd_keep_step), and
   io_send's acall_kept_g, stated at the call state whose frames hold this walk's own class-0 frame, folds into the
   running one by dk_kept_trans_nf_g with TransportGFrame.v dkg_nf_sep_gw and the cut file's sd_iosend_wr_sub. The
   13 saved words below the entry sp and the frame's last word are outside g_s, so they survive the runs
   (YCbq.v rdword_ext) and the call (its acall_kept_g clauses 1 and 4). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YI67 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_build_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_data_cg send_data_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YO0f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TGx := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
From Stdlib Require Znumtheory.
(* ------------------------------------------------------------------ *)
(* The model's worlds from a world X after the build (sd_B2), by n     *)
(* ------------------------------------------------------------------ *)

Definition sd_B3' (X : list byte) (n : Z) : list byte := TW.set_S_inflight_len X n.
Definition sd_B7' (X : list byte) (n now : Z) : list byte :=
  TW.set_S_inflight_sent_us (TW.set_S_inflight_retries
    (TW.set_S_inflight_counter (TW.set_S_inflight (sd_B3' X n) 1) (TW.S_host_counter (sd_B3' X n))) 0) now.
Definition sd_B8' (X : list byte) (n now : Z) : list byte :=
  TW.set_S_stats_tx_data (sd_B7' X n now) (TS0.u64 (TW.S_stats_tx_data (sd_B7' X n now) + 1)).

(* ---- the world offsets, as numerals ---- *)
Lemma sdm_o_hc : TW.A_S_host_counter = 1808. Proof. reflexivity. Qed.
Lemma sdm_o_dmac : TW.A_S_desk_mac = 1768. Proof. reflexivity. Qed.
Lemma sdm_o_hmac : TW.A_S_cfg_host_mac = 1648. Proof. reflexivity. Qed.
Lemma sdm_o_iosend : TW.A_S_io_send = 1720. Proof. reflexivity. Qed.
Lemma sdm_o_infl : TW.A_S_inflight = 1860. Proof. reflexivity. Qed.
Lemma sdm_o_frame : TW.A_S_inflight_frame = 1864. Proof. reflexivity. Qed.
Lemma sdm_o_len : TW.A_S_inflight_len = 3384. Proof. reflexivity. Qed.
Lemma sdm_o_ctr : TW.A_S_inflight_counter = 3392. Proof. reflexivity. Qed.
Lemma sdm_o_retr : TW.A_S_inflight_retries = 3396. Proof. reflexivity. Qed.
Lemma sdm_o_sent : TW.A_S_inflight_sent_us = 3400. Proof. reflexivity. Qed.
Lemma sdm_o_txf : TW.A_S_stats_tx_frames = 19840. Proof. reflexivity. Qed.
Lemma sdm_o_txd : TW.A_S_stats_tx_data = 19848. Proof. reflexivity. Qed.
Lemma sdm_o_gfn : TW.OFF_g_fail_next = 64968. Proof. reflexivity. Qed.
Lemma sdm_o_ncmd : TW.OFF_g_ncmd = 64984. Proof. reflexivity. Qed.
Lemma sdm_o_cmd : TW.OFF_g_cmd = 19912. Proof. reflexivity. Qed.
Lemma sdm_o_flyon : TW.A_M_fly_on = 96. Proof. reflexivity. Qed.
Lemma sdm_o_flylen : TW.A_M_fly_len = 1640. Proof. reflexivity. Qed.

Ltac sdm_offs :=
  rewrite ?sdm_o_hc, ?sdm_o_dmac, ?sdm_o_hmac, ?sdm_o_iosend, ?sdm_o_infl, ?sdm_o_frame, ?sdm_o_len,
    ?sdm_o_ctr, ?sdm_o_retr, ?sdm_o_sent, ?sdm_o_txf, ?sdm_o_txd, ?sdm_o_gfn, ?sdm_o_ncmd, ?sdm_o_cmd,
    ?sdm_o_flyon, ?sdm_o_flylen.

(* the length of a world the stores make *)
Ltac sdm_wlen :=
  repeat match goal with
  | |- context [length (TW.upd ?bs ?k (TW.put ?n ?v))] =>
      rewrite (TWL.length_upd_put bs k n v) by (sdm_wlen; lia)
  | |- context [length (TW.upd ?bs ?k ?v)] =>
      rewrite (TWL.length_upd bs v k) by (sdm_wlen; rewrite ?TWL.length_put; lia)
  end.
Ltac sdm_side := sdm_wlen; rewrite ?TWL.length_put; lia.
(* a read past every store of a world *)
Ltac sdm_out :=
  repeat match goal with
  | |- context [TW.u_at (TW.upd ?bs ?k ?v) ?k' ?n] =>
      rewrite (TWL.u_at_upd_out bs v k k' n) by sdm_side
  end.
Ltac sdm_unfB8 :=
  unfold sd_B8', sd_B7', sd_B3', TW.set_S_stats_tx_data, TW.set_S_inflight_sent_us, TW.set_S_inflight_retries,
    TW.set_S_inflight_counter, TW.set_S_inflight, TW.set_S_inflight_len;
  sdm_offs.

(* ---- diginet_frame_build's code ---- *)
Lemma sdm_bc_mode : forall body cap mode, 0 <= TNd.diginet_frame_build_code body cap mode -> mode = 0 \/ mode = 1.
Proof.
  intros body cap mode H. unfold TNd.diginet_frame_build_code in H.
  destruct ((mode =? 0) || (mode =? 1)) eqn:E; cbn [negb] in H.
  - apply orb_true_iff in E. destruct E as [E|E]; apply Z.eqb_eq in E; auto.
  - lia.
Qed.

Lemma sdm_bc_val : forall body cap mode, 0 <= TNd.diginet_frame_build_code body cap mode ->
  TNd.diginet_frame_build_code body cap mode = DSpec.frame_len (length body).
Proof.
  intros body cap mode. unfold TNd.diginet_frame_build_code, DLib.lib_build_code.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbv beta iota;
    intros H; first [reflexivity | lia].
Qed.

Lemma sdm_bc_bound : forall bb cap mode, -10 <= TNd.diginet_frame_build_code bb cap mode <= 1514.
Proof.
  intros bb cap mode. unfold TNd.diginet_frame_build_code, DLib.lib_build_code.
  destruct (negb _); cbv beta iota; [lia|].
  destruct (Z.ltb_spec 1484 (Z.of_nat (length bb))); cbv beta iota; [lia|].
  destruct (negb _); cbv beta iota; [lia|].
  destruct (cap <? _); cbv beta iota; [lia|].
  unfold DSpec.frame_len. lia.
Qed.

Lemma sdm_length_lib_frame : forall dmac smac send ack retry cmd nc body mode,
  length dmac = 6%nat -> length smac = 6%nat -> mode = 0 \/ mode = 1 ->
  Z.of_nat (length (DLib.lib_frame dmac smac send ack retry cmd nc body mode)) = DSpec.frame_len (length body).
Proof.
  intros. rewrite DLib.frame_build_bytes by assumption. apply DSpec.length_build_frame; assumption.
Qed.

(* ---- stores modulo the field width ---- *)
Lemma sdm_put_cong32 : forall u v, u mod 2 ^ 32 = v mod 2 ^ 32 -> TW.put 4 u = TW.put 4 v.
Proof.
  intros u v H. unfold TW.put.
  rewrite <- (OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.Z_to_le_bytes_mod 4 u 32) by (cbn; lia).
  rewrite H.
  apply OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.Z_to_le_bytes_mod. cbn; lia.
Qed.

Lemma sdm_swrap32_mod : forall z, bv_swrap 32 z mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
  intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (Z.of_N 32) with 32.
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma sdm_put4_s32 : forall X k, TW.put 4 (TW.s32_at X k) = TW.put 4 (TW.u_at X k 4).
Proof. intros X k. apply sdm_put_cong32. unfold TW.s32_at. apply sdm_swrap32_mod. Qed.

(* ---- reads of the worlds sd_B7' / sd_B8' ---- *)
Lemma sdm_txd_B7 : forall X n now, Z.of_nat (length X) = 65616 ->
  TW.S_stats_tx_data (sd_B7' X n now) = TW.u_at X 19848 8.
Proof.
  intros X n now HL. unfold TW.S_stats_tx_data. sdm_unfB8. sdm_out. reflexivity.
Qed.

Lemma sdm_rd_len : forall Y n now, Z.of_nat (length Y) = 65616 -> 0 <= n <= 1514 ->
  TW.S_inflight_len (sd_B8' Y n now) = n.
Proof.
  intros Y n now HL Hn. unfold TW.S_inflight_len. sdm_unfB8. sdm_out.
  rewrite TWL.u_at_upd_put by sdm_side.
  apply Z.mod_small. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The lemmas                                                           *)
(* ------------------------------------------------------------------ *)

Lemma sdm_B8_eq : forall Bw ncmds body now,
  sd_B8 Bw ncmds body now = sd_B8' (sd_B2 Bw ncmds body) (sd_n Bw ncmds body) now.
Proof.
  intros Bw ncmds body now. unfold sd_B8, sd_B7, sd_B3, sd_B8', sd_B7', sd_B3'. reflexivity.
Qed.

Lemma sdm_unfold : forall TF Bw body ncmds now,
  TSS.send_data_m timg_B TF Bw body ncmds now =
  (if sd_n Bw ncmds body <? 0 then Some (sd_M1 Bw ncmds, sd_n Bw ncmds body)
   else match TSS.inflight_bytes (sd_B8 Bw ncmds body now) with
        | None => None
        | Some fr => TSS.send_raw_m timg_B TF (sd_B8 Bw ncmds body now) fr
        end).
Proof.
  intros TF Bw body ncmds now. unfold TSS.send_data_m, TS0.inflight_start_m. cbv beta iota zeta.
  unfold sd_n, sd_M1, sd_B8, sd_B7, sd_B3, sd_B2, sd_LF. reflexivity.
Qed.

Lemma sdm_bound : forall Bw ncmds body, -10 <= sd_n Bw ncmds body <= 1514.
Proof. intros Bw ncmds body. unfold sd_n. apply sdm_bc_bound. Qed.

Lemma sdm_len_M1 : forall Bw ncmds, Z.of_nat (length Bw) = 65616 ->
  Z.of_nat (length (sd_M1 Bw ncmds)) = 65616.
Proof.
  intros Bw ncmds HL. unfold sd_M1, TW.set_S_host_counter. sdm_offs. sdm_wlen. exact HL.
Qed.

Lemma sdm_lf_len : forall Bw ncmds body, Z.of_nat (length Bw) = 65616 -> 0 <= sd_n Bw ncmds body ->
  Z.of_nat (length (sd_LF Bw ncmds body)) = sd_n Bw ncmds body.
Proof.
  intros Bw ncmds body HL Hn.
  pose proof (sdm_len_M1 Bw ncmds HL) as HM.
  pose proof Hn as Hn'. unfold sd_n in Hn'.
  pose proof (sdm_bc_mode _ _ _ Hn') as Hmode.
  pose proof (sdm_bc_val _ _ _ Hn') as Hval.
  unfold sd_LF. rewrite sdm_length_lib_frame.
  - unfold sd_n. rewrite Hval. reflexivity.
  - unfold TW.S_desk_mac. sdm_offs. apply TWL.length_sub; lia.
  - unfold TW.S_cfg_host_mac. sdm_offs. apply TWL.length_sub; lia.
  - exact Hmode.
Qed.

Lemma sdm_len_B2 : forall Bw ncmds body, Z.of_nat (length Bw) = 65616 -> 0 <= sd_n Bw ncmds body ->
  Z.of_nat (length (sd_B2 Bw ncmds body)) = 65616.
Proof.
  intros Bw ncmds body HL Hn.
  pose proof (sdm_len_M1 Bw ncmds HL) as HM.
  pose proof (sdm_lf_len Bw ncmds body HL Hn) as HF.
  pose proof (sdm_bound Bw ncmds body) as HB.
  unfold sd_B2, TW.set_S_inflight_frame. sdm_offs. sdm_wlen. exact HM.
Qed.

Lemma sdm_len_B8 : forall X n now, Z.of_nat (length X) = 65616 -> 0 <= n <= 1514 ->
  Z.of_nat (length (sd_B8' X n now)) = 65616.
Proof. intros X n now HL Hn. sdm_unfB8. sdm_wlen. exact HL. Qed.

(* the value the binary stores at s + 1744 is the model's *)
Lemma sdm_hc_store : forall X n, Z.of_nat (length X) = 65616 -> 0 <= n <= 1514 ->
  TW.put 4 (TW.s32_at X 1808) = TW.put 4 (TW.S_host_counter (sd_B3' X n)).
Proof.
  intros X n HL Hn. unfold sd_B3', TW.S_host_counter, TW.set_S_inflight_len. sdm_offs. sdm_out.
  apply sdm_put4_s32.
Qed.

(* the six stores the binary makes, in ITS order and with ITS values, from a world X *)
Lemma sdm_six : forall X n now, Z.of_nat (length X) = 65616 -> 0 <= n <= 1514 -> 0 <= now < 2 ^ 64 ->
  TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd X 3384 (TW.put 8 n)) 1860 (TW.put 4 1))
      3392 (TW.put 4 (TW.s32_at X 1808))) 3396 (TW.put 4 0)) 3400 (TW.put 8 now))
      19848 (TW.put 8 (TW.u_at X 19848 8 + 1))
  = sd_B8' X n now.
Proof.
  intros X n now HL Hn Hnow.
  rewrite (sdm_hc_store X n HL Hn).
  unfold sd_B8'. rewrite (sdm_txd_B7 X n now HL).
  unfold TW.set_S_stats_tx_data, TS0.u64. rewrite TWL.put_mod64 by lia.
  unfold sd_B7', TW.set_S_inflight_sent_us, TW.set_S_inflight_retries, TW.set_S_inflight_counter,
    TW.set_S_inflight.
  unfold sd_B3' at 1. unfold TW.set_S_inflight_len at 1. sdm_offs.
  reflexivity.
Qed.

(* what the binary reads at s + 18200 after the five stores before it *)
Lemma sdm_txd_read : forall X n now, Z.of_nat (length X) = 65616 -> 0 <= n <= 1514 ->
  TW.u_at (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd X 3384 (TW.put 8 n)) 1860 (TW.put 4 1))
      3392 (TW.put 4 (TW.s32_at X 1808))) 3396 (TW.put 4 0)) 3400 (TW.put 8 now)) 19848 8
  = TW.u_at X 19848 8.
Proof. intros X n now HL Hn. sdm_out. reflexivity. Qed.

(* the fields no store of sd_B8' touches *)
Lemma sdm_keep_B8 : forall X n now, Z.of_nat (length X) = 65616 -> 0 <= n <= 1514 ->
  TW.S_io_send (sd_B8' X n now) = TW.S_io_send X /\
  TW.g_fail_next (sd_B8' X n now) = TW.g_fail_next X /\
  TW.M_fly_on (sd_B8' X n now) = TW.M_fly_on X /\
  TW.M_fly_len (sd_B8' X n now) = TW.M_fly_len X /\
  TW.g_ncmd (sd_B8' X n now) = TW.g_ncmd X /\
  (forall i, 0 <= i -> TW.Cmd_st (sd_B8' X n now) i = TW.Cmd_st X i) /\
  (forall i, 0 <= i -> TW.Cmd_len (sd_B8' X n now) i = TW.Cmd_len X i).
Proof.
  intros X n now HL Hn.
  unfold TW.S_io_send, TW.g_fail_next, TW.M_fly_on, TW.M_fly_len, TW.g_ncmd, TW.Cmd_st, TW.Cmd_len,
    TW.A_Cmd_st, TW.A_Cmd_len, TW.s32_at.
  sdm_unfB8.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  all: try intros i Hi; sdm_offs; sdm_out; reflexivity.
Qed.

(* the same fields from Bw to sd_M1 and on to sd_B2 *)
Lemma sdm_keep_M1 : forall Bw ncmds, Z.of_nat (length Bw) = 65616 ->
  TW.S_io_send (sd_M1 Bw ncmds) = TW.S_io_send Bw /\
  TW.g_fail_next (sd_M1 Bw ncmds) = TW.g_fail_next Bw /\
  TW.M_fly_on (sd_M1 Bw ncmds) = TW.M_fly_on Bw /\
  TW.M_fly_len (sd_M1 Bw ncmds) = TW.M_fly_len Bw /\
  TW.g_ncmd (sd_M1 Bw ncmds) = TW.g_ncmd Bw /\
  (forall i, 0 <= i -> TW.Cmd_st (sd_M1 Bw ncmds) i = TW.Cmd_st Bw i) /\
  (forall i, 0 <= i -> TW.Cmd_len (sd_M1 Bw ncmds) i = TW.Cmd_len Bw i).
Proof.
  intros Bw ncmds HL.
  unfold sd_M1, TW.set_S_host_counter, TW.S_io_send, TW.g_fail_next, TW.M_fly_on, TW.M_fly_len, TW.g_ncmd,
    TW.Cmd_st, TW.Cmd_len, TW.A_Cmd_st, TW.A_Cmd_len, TW.s32_at.
  sdm_offs.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  all: try intros i Hi; sdm_offs; sdm_out; reflexivity.
Qed.

Lemma sdm_keep_B2 : forall Bw ncmds body, Z.of_nat (length Bw) = 65616 -> 0 <= sd_n Bw ncmds body ->
  TW.S_io_send (sd_B2 Bw ncmds body) = TW.S_io_send (sd_M1 Bw ncmds) /\
  TW.g_fail_next (sd_B2 Bw ncmds body) = TW.g_fail_next (sd_M1 Bw ncmds) /\
  TW.M_fly_on (sd_B2 Bw ncmds body) = TW.M_fly_on (sd_M1 Bw ncmds) /\
  TW.M_fly_len (sd_B2 Bw ncmds body) = TW.M_fly_len (sd_M1 Bw ncmds) /\
  TW.g_ncmd (sd_B2 Bw ncmds body) = TW.g_ncmd (sd_M1 Bw ncmds) /\
  (forall i, 0 <= i -> TW.Cmd_st (sd_B2 Bw ncmds body) i = TW.Cmd_st (sd_M1 Bw ncmds) i) /\
  (forall i, 0 <= i -> TW.Cmd_len (sd_B2 Bw ncmds body) i = TW.Cmd_len (sd_M1 Bw ncmds) i).
Proof.
  intros Bw ncmds body HL Hn.
  pose proof (sdm_len_M1 Bw ncmds HL) as HM.
  pose proof (sdm_lf_len Bw ncmds body HL Hn) as HF.
  pose proof (sdm_bound Bw ncmds body) as HB.
  unfold sd_B2, TW.set_S_inflight_frame, TW.S_io_send, TW.g_fail_next, TW.M_fly_on, TW.M_fly_len, TW.g_ncmd,
    TW.Cmd_st, TW.Cmd_len, TW.A_Cmd_st, TW.A_Cmd_len, TW.s32_at.
  sdm_offs.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  all: try intros i Hi; sdm_offs; sdm_out; reflexivity.
Qed.

(* :400, the bytes handed to io_send *)
Lemma sdm_fr : forall Bw ncmds body now, Z.of_nat (length Bw) = 65616 -> 0 <= sd_n Bw ncmds body ->
  TSS.inflight_bytes (sd_B8 Bw ncmds body now) = Some (sd_fr Bw ncmds body now) /\
  Z.of_nat (length (sd_fr Bw ncmds body now)) = sd_n Bw ncmds body.
Proof.
  intros Bw ncmds body now HL Hn.
  pose proof (sdm_len_B2 Bw ncmds body HL Hn) as H2.
  pose proof (sdm_bound Bw ncmds body) as HB.
  assert (E8 : TW.S_inflight_len (sd_B8 Bw ncmds body now) = sd_n Bw ncmds body)
    by (rewrite sdm_B8_eq; apply sdm_rd_len; [exact H2 | lia]).
  assert (L8 : Z.of_nat (length (sd_B8 Bw ncmds body now)) = 65616)
    by (rewrite sdm_B8_eq; apply sdm_len_B8; [exact H2 | lia]).
  unfold TSS.inflight_bytes. rewrite E8.
  destruct (Z.ltb_spec 1514 (sd_n Bw ncmds body)) as [Hgt|Hle]; [lia|].
  split; [reflexivity|].
  unfold sd_fr. rewrite TWL.length_sub; [lia | rewrite sdm_o_frame; lia | rewrite sdm_o_frame, L8; lia].
Qed.

(* send_raw, with no injection on a world option *)
Lemma sdm_sendraw : forall TF Y fr Bw' r, TSS.send_raw_m timg_B TF Y fr = Some (Bw', r) ->
  TW.S_io_send Y = TI.ti_io_send timg_B /\
  exists B9 r0, TC.io_send_m timg_B Y fr = Some (B9, r0) /\
    ((r0 = 0 /\ Bw' = TW.set_S_stats_tx_frames B9 (TS0.u64 (TW.S_stats_tx_frames B9 + 1)) /\ r = 0) \/
     (r0 <> 0 /\ Bw' = B9 /\ r = r0)).
Proof.
  intros TF Y fr Bw' r. unfold TSS.send_raw_m, TSS.call_send.
  destruct (Z.eqb_spec (TW.S_io_send Y) (TI.ti_io_send timg_B)) as [E|E]; cbv beta iota;
    [| intros H; discriminate H].
  destruct (TC.io_send_m timg_B Y fr) as [[B9 r0]|] eqn:HIO; cbv beta iota; [| intros H; discriminate H].
  intros H. split; [exact E|]. exists B9, r0. split; [reflexivity|].
  revert H. destruct (Z.eqb_spec r0 0) as [Z0|NZ]; cbv beta iota; intros H.
  - left. split; [exact Z0|]. split.
    + exact (eq_sym (sd_some_w _ _ _ _ H)).
    + rewrite <- (sd_some_r _ _ _ _ H). exact Z0.
  - right. split; [exact NZ|]. split.
    + exact (eq_sym (sd_some_w _ _ _ _ H)).
    + exact (eq_sym (sd_some_r _ _ _ _ H)).
Qed.

(* send_raw :91-92, the read-modify-write of stats.tx_frames the binary makes *)
Lemma sdm_txf : forall B9, Z.of_nat (length B9) = 65616 ->
  TW.upd B9 19840 (TW.put 8 (TW.u_at B9 19840 8 + 1))
  = TW.set_S_stats_tx_frames B9 (TS0.u64 (TW.S_stats_tx_frames B9 + 1)) /\
  TW.g_fail_next (TW.set_S_stats_tx_frames B9 (TS0.u64 (TW.S_stats_tx_frames B9 + 1))) = TW.g_fail_next B9 /\
  Z.of_nat (length (TW.set_S_stats_tx_frames B9 (TS0.u64 (TW.S_stats_tx_frames B9 + 1)))) = 65616.
Proof.
  intros B9 HL. unfold TW.set_S_stats_tx_frames, TW.S_stats_tx_frames, TW.g_fail_next. sdm_offs.
  split; [| split].
  - unfold TS0.u64. rewrite TWL.put_mod64 by lia. reflexivity.
  - sdm_out. reflexivity.
  - sdm_wlen. exact HL.
Qed.

(* the two branches the binary takes, as the model's tests *)
Lemma sdm_lts0 : forall v, -2^63 <= v < 2^63 -> bv_lts (Z_to_bv 64 v) (Z_to_bv 64 0) = (v <? 0).
Proof.
  intros v Hv.
  rewrite OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.ZBridge.bv_lts_zero_r,
    OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.MState.unsigned_lit_wrap.
  destruct (Z.ltb_spec v 0) as [L|L].
  - apply Z.leb_le.
    replace (v mod 2 ^ 64) with (v + 2 ^ 64);
      [lia | rewrite <- (Z.mod_add v 1 (2 ^ 64)) by lia; rewrite Z.mod_small; lia].
  - apply Z.leb_gt. rewrite Z.mod_small; lia.
Qed.

Lemma sdm_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb.
  rewrite !OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.MState.unsigned_lit_wrap.
  change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

(* ------------------------------------------------------------------ *)
(* io_send's two facts, from TCb.v io_send_m's own definition          *)
(* (the proofs of lib/TModel/TIoSendFail.v, with no injection on a      *)
(* world-carrying option)                                              *)
(* ------------------------------------------------------------------ *)

(* the world read off an equation between two results *)
Lemma sdm_fst : forall {A : Type} (Bx By : list byte) (x y : A), Some (Bx, x) = Some (By, y) -> Bx = By.
Proof. intros A Bx By x y H. exact (f_equal (fun o => match o with Some (b, _) => b | None => Bx end) H). Qed.
Lemma sdm_snd_some : forall {A B : Type} (a b : A) (x y : B), Some (a, Some x) = Some (b, Some y) -> x = y.
Proof.
  intros A B a b x y H.
  exact (f_equal (fun o => match o with Some (_, Some v) => v | _ => x end) H).
Qed.

Module SdmIoSend.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.

(* a world of the right length whose g_fail_next byte is 0 *)
Definition isf_fn0 (X : list byte) : Prop := length X = Z.to_nat W_LEN /\ g_fail_next X = 0.

Lemma isf_upd : forall X k v, isf_fn0 X -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  k + Z.of_nat (length v) <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k -> isf_fn0 (upd X k v).
Proof.
  intros X k v [HL HF] Hk Hl Hd. unfold isf_fn0, g_fail_next in *.
  assert (HL' : k + Z.of_nat (length v) <= Z.of_nat (length X)) by (rewrite HL; unfold W_LEN in *; lia).
  split.
  - rewrite length_upd by assumption. exact HL.
  - rewrite u_at_upd_out; [exact HF | exact Hk | unfold OFF_g_fail_next; lia | | exact HL'].
    change (Z.of_nat 1) with 1. lia.
Qed.

Lemma isf_put : forall X k n v, isf_fn0 X -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  k + Z.of_nat n <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k -> isf_fn0 (upd X k (put n v)).
Proof. intros X k n v F Hk Hl Hd. apply isf_upd; rewrite ?length_put; assumption. Qed.

Lemma isf_clear : forall B, length B = Z.to_nat W_LEN -> isf_fn0 (set_g_fail_next B 0).
Proof.
  intros B HL. unfold isf_fn0, set_g_fail_next, g_fail_next.
  split.
  - rewrite length_upd_put; [exact HL | unfold OFF_g_fail_next; lia | rewrite HL; unfold OFF_g_fail_next, W_LEN; lia].
  - rewrite u_at_upd_put; [reflexivity | unfold OFF_g_fail_next; lia | rewrite HL; unfold OFF_g_fail_next, W_LEN; lia].
Qed.

Ltac isf_offs :=
  unfold A_M_fly_on, A_M_fly_cmd, A_M_fly_counter, A_M_fly_retries, A_M_fly_sent, A_M_fly_frame, A_M_fly_len,
    A_M_host_counter, A_M_next_ka, A_M_last_display, A_M_display_sent, A_GOT_acks, A_GOT_e2, A_GOT_e3,
    A_Cmd_st, OFF_M, OFF_GOT, OFF_g_cmd, OFF_g_q, OFF_g_last_counter, OFF_g_nq, OFF_g_fail_next, W_LEN,
    SPEC_MAX_FRAME, CMDS_MAX in *.

(* the length side goal of the write of M.fly.frame (:888-889): firstn of at most SPEC_MAX_FRAME bytes *)
Ltac isf_len :=
  rewrite ?length_firstn;
  repeat match goal with Hb : (_ <? _) = true |- _ => apply Z.ltb_lt in Hb end;
  isf_offs; lia.

(* a world built by TWorld setters on a world the context says isf_fn0 of *)
Ltac isf_tac :=
  unfold set_M_fly_on, set_M_fly_cmd, set_M_fly_counter, set_M_fly_retries, set_M_fly_sent, set_M_fly_frame,
    set_M_fly_len, set_M_host_counter, set_M_next_ka, set_M_last_display, set_M_display_sent, set_GOT_acks,
    set_GOT_e2, set_GOT_e3, set_g_last_counter;
  repeat first
    [ assumption
    | apply isf_put; [ | isf_offs; lia | isf_offs; lia | isf_offs; lia ]
    | apply isf_upd; [ | isf_offs; lia | isf_len | isf_len ] ].

(* ---- the checks that return their world unchanged ---- *)

Ltac isf_ck :=
  cbv zeta;
  repeat (match goal with |- context [if ?c then _ else _] => destruct c; cbv beta iota end);
  let H := fresh "H" in intros H; first [discriminate H | exact (eq_sym (sdm_fst _ _ _ _ H))].

Lemma isf_sent : forall X f Y u, check_sent_frame_m X f = Some (Y, u) -> Y = X.
Proof. intros X f Y u. unfold check_sent_frame_m. isf_ck. Qed.
Lemma isf_ack : forall X f Y u, check_ack_frame_m X f = Some (Y, u) -> Y = X.
Proof. intros X f Y u. unfold check_ack_frame_m. isf_ck. Qed.
Lemma isf_ctl : forall X f Y u, check_latest_control_m X f = Some (Y, u) -> Y = X.
Proof. intros X f Y u. unfold check_latest_control_m. isf_ck. Qed.
Lemma isf_retry : forall X f Y u, check_inflight_retry_m X f = Some (Y, u) -> Y = X.
Proof. intros X f Y u. unfold check_inflight_retry_m. isf_ck. Qed.
Lemma isf_wake : forall X Y u, check_state_wake_m X = Some (Y, u) -> Y = X.
Proof. intros X Y u. unfold check_state_wake_m. isf_ck. Qed.
Lemma isf_new : forall X Y u, check_inflight_new_m X = Some (Y, u) -> Y = X.
Proof. intros X Y u. unfold check_inflight_new_m. isf_ck. Qed.
Lemma isf_frame : forall X f c Y u, check_latest_frame_m X f c = Some (Y, u) -> Y = X.
Proof. intros X f c Y u. unfold check_latest_frame_m. isf_ck. Qed.
Lemma isf_ka : forall X Y u, check_keepalive_due_m X = Some (Y, u) -> Y = X.
Proof. intros X Y u. unfold check_keepalive_due_m. isf_ck. Qed.
Lemma isf_disp : forall X Y u, check_latest_display_m X = Some (Y, u) -> Y = X.
Proof. intros X Y u. unfold check_latest_display_m. isf_ck. Qed.

(* ---- check_latest_sent (:626-644) ---- *)

(* tagged_of answers an index of g_cmd below CMDS_MAX (:613-614) *)
Lemma isf_tagged : forall X b n Y s, tagged_of_m X b n = Some (Y, Some s) -> 0 <= s < CMDS_MAX.
Proof.
  intros X b n Y s. unfold tagged_of_m. cbv zeta.
  repeat (match goal with |- context [if ?c then _ else _] => let E := fresh "Ec" in destruct c eqn:E; cbv beta iota end);
    let H := fresh "H" in intros H; try discriminate H.
  apply sdm_snd_some in H. subst s.
  match goal with Ec : (CMDS_MAX <=? _) = false |- _ => apply Z.leb_gt in Ec end.
  split; [|assumption].
  apply Z.lor_nonneg. split; [|apply Z.shiftl_nonneg];
    unfold DgnSpec.at8, DgnSpec.bz;
    match goal with |- 0 <= bv_unsigned ?x => pose proof (bv_unsigned_in_range _ x); lia end.
Qed.

(* q_remove's loop (:619-623) writes g_q[k] with k <= i < CMDS_MAX *)
Lemma isf_q_loop : forall fuel X s nq i k Y k', isf_fn0 X -> 0 <= k <= i ->
  q_remove_loop fuel X s nq i k = Some (Y, k') -> isf_fn0 Y.
Proof.
  induction fuel as [|fuel IH]; intros X s nq i k Y k' FX Hk; cbn [q_remove_loop];
    [let H := fresh "H" in intros H; discriminate H|].
  destruct (Z.ltb_spec i nq) as [Hi|Hi]; cbv beta iota;
    [|let H := fresh "H" in intros H; rewrite <- (sdm_fst _ _ _ _ H); exact FX].
  destruct (Z.leb_spec CMDS_MAX i) as [Hc|Hc]; cbv beta iota; [let H := fresh "H" in intros H; discriminate H|].
  destruct (Q_at X i =? s); cbv beta iota.
  - apply (IH X s nq (i + 1) k Y k' FX). lia.
  - apply (IH _ s nq (i + 1) (k + 1) Y k'); [|lia].
    unfold set_Q_at. apply isf_put; [exact FX | isf_offs; lia | isf_offs; lia | isf_offs; lia].
Qed.

Lemma isf_q_remove : forall X s Y u, isf_fn0 X -> q_remove_m X s = Some (Y, u) -> isf_fn0 Y.
Proof.
  intros X s Y u FX. unfold q_remove_m.
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[X1 k]|] eqn:EL end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  let H := fresh "H" in intros H; rewrite <- (sdm_fst _ _ _ _ H).
  unfold set_g_nq. apply isf_put; [ | isf_offs; lia | isf_offs; lia | isf_offs; lia ].
  exact (isf_q_loop _ X s _ 0 0 X1 k FX ltac:(lia) EL).
Qed.

Lemma isf_ls_loop : forall fuel X body len pos disp Y d, isf_fn0 X ->
  latest_sent_loop fuel X body len pos disp = Some (Y, d) -> isf_fn0 Y.
Proof.
  induction fuel as [|fuel IH]; intros X body len pos disp Y d FX; cbn [latest_sent_loop];
    [let H := fresh "H" in intros H; discriminate H|].
  cbv zeta.
  destruct (pos <? len); cbv beta iota;
    [|let H := fresh "H" in intros H; rewrite <- (sdm_fst _ _ _ _ H); exact FX].
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[X0 t]|] eqn:ET end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  destruct t as [s|]; cbv beta iota; [|let H := fresh "H" in intros H; discriminate H].
  pose proof (isf_tagged _ _ _ _ _ ET) as Hs.
  match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end; cbv beta iota;
    [let H := fresh "H" in intros H; discriminate H|].
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[X2 u2]|] eqn:EQ end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  apply IH. apply (isf_q_remove (set_Cmd_st X s SENT) s X2 u2); [|exact EQ].
  unfold set_Cmd_st. apply isf_put; [exact FX | isf_offs; lia | isf_offs; lia | isf_offs; lia].
Qed.

Lemma isf_ls : forall X body len Y d, isf_fn0 X -> check_latest_sent_m X body len = Some (Y, d) -> isf_fn0 Y.
Proof. intros X body len Y d FX. unfold check_latest_sent_m. apply isf_ls_loop. exact FX. Qed.

(* ---- io_send ---- *)

(* the facts a call's answer E gives: the unchanged world of a check, or isf_fn0 of check_latest_sent's world *)
Ltac isf_fact E Y :=
  lazymatch type of E with
  | check_sent_frame_m _ _ = _ => apply isf_sent in E; subst Y
  | check_ack_frame_m _ _ = _ => apply isf_ack in E; subst Y
  | check_latest_control_m _ _ = _ => apply isf_ctl in E; subst Y
  | check_inflight_retry_m _ _ = _ => apply isf_retry in E; subst Y
  | check_state_wake_m _ = _ => apply isf_wake in E; subst Y
  | check_inflight_new_m _ = _ => apply isf_new in E; subst Y
  | check_latest_frame_m _ _ _ = _ => apply isf_frame in E; subst Y
  | check_keepalive_due_m _ = _ => apply isf_ka in E; subst Y
  | check_latest_display_m _ = _ => apply isf_disp in E; subst Y
  | check_latest_sent_m ?X _ _ = _ =>
      let F := fresh "F" in assert (F : isf_fn0 Y) by (eapply (isf_ls X); [isf_tac | exact E])
  | _ => idtac
  end.

Ltac isf_go :=
  cbv beta iota;
  first
    [ let H := fresh "H" in intros H; discriminate H
    | let H := fresh "H" in intros H; rewrite <- (sdm_fst _ _ _ _ H); isf_tac
    | match goal with |- context [if ?c then _ else _] => let Ec := fresh "Ec" in destruct c eqn:Ec; isf_go end
    | let x := match goal with
               | |- context [match ?x with _ => _ end] =>
                   lazymatch x with context [match _ with _ => _ end] => fail | _ => x end
               end in
      let E := fresh "E" in
      lazymatch type of x with
      | option (prod _ _) =>
          let Y := fresh "Y" in let u := fresh "u" in
          destruct x as [[Y u]|] eqn:E; [isf_fact E Y|]; isf_go
      | _ => destruct x eqn:E; isf_go
      end
    | let H := fresh "H" in intros H;
      lazymatch type of H with _ = Some (?Y, _) => isf_fact H Y; isf_tac end ].

Lemma io_send_m_fail_next : forall I B frame B' r,
  io_send_m I B frame = Some (B', r) -> length B = Z.to_nat W_LEN -> g_fail_next B' = 0.
Proof.
  intros I B frame B' r H HL.
  pose proof (isf_clear B HL) as F0.
  unfold io_send_m in H. cbv zeta in H.
  remember (set_g_fail_next B 0) as B0 eqn:EB0. clear EB0.
  revert H.
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[B1 u1]|] eqn:E1 end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  apply isf_sent in E1. subst B1.
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[B2 u2]|] eqn:E2 end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  intros H. rewrite <- (sdm_fst _ _ _ _ H).
  enough (FB : isf_fn0 B2) by exact (proj2 FB).
  revert E2. isf_go.
Qed.

(* io_send returns 0 or -EIO (:898) *)
Lemma io_send_m_ret : forall I B frame B' r, io_send_m I B frame = Some (B', r) -> r = 0 \/ r = - EIO.
Proof.
  intros I B frame B' r H. unfold io_send_m in H. cbv zeta in H. revert H.
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[B1 u1]|] end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[B2 u2]|] end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  intros H. rewrite <- (sd_some_r _ _ _ _ H). destruct (truth (g_fail_next B)); [right | left]; reflexivity.
Qed.
End SdmIoSend.

(* io_send's two facts, restated at the shape the walk uses *)
Lemma sdm_io_ret : forall Y fr B9 r0, TC.io_send_m timg_B Y fr = Some (B9, r0) -> r0 = 0 \/ r0 = -5.
Proof.
  intros Y fr B9 r0 H. destruct (SdmIoSend.io_send_m_ret _ _ _ _ _ H) as [E|E]; [left; exact E | right].
  rewrite E. reflexivity.
Qed.

Lemma sdm_io_gfn : forall Y fr B9 r0, TC.io_send_m timg_B Y fr = Some (B9, r0) ->
  Z.of_nat (length Y) = 65616 -> TW.g_fail_next B9 = 0.
Proof.
  intros Y fr B9 r0 H HL. apply (SdmIoSend.io_send_m_fail_next _ _ _ _ _ H).
  apply Nat2Z.inj. rewrite Z2Nat.id by (unfold TW.W_LEN; lia). rewrite HL. reflexivity.
Qed.
(* ------------------------------------------------------------------ *)
(* 3. The symbolic states                                             *)
(* ------------------------------------------------------------------ *)

(* the shadow byte of s + 160, which the head left in s5, and g_s.stats.tx_frames *)
Definition SD_SH160 : Z := SHADOW_OFF + (SENDDATA_S + 160) / 8.
Definition SD_TXF : Z := SENDDATA_S + 18192.
(* the return address of the indirect call, and the call itself *)
Definition SD_RET2 : Z := SD_FB + 0xfc.
Definition SD_JALR : Z := SD_FB + 0xf8.

(* state 1, at SD_FB on the path 0 <= n. Atoms 0 .. 31 the registers at the cut; 32 the 4 bytes at s + 160 (the new
   host counter), 33 the 8 bytes at s + 18200 (stats.tx_data), 34 the 8 bytes at s + 64 (io.ctx), 35 now, 36 the
   8 bytes at s + 72 (io.send). The run stops at `jalr ra, 0(a3)`. *)
Definition SD_SH1 : list shent := [mkSHE 19 0 18264].
Definition SD_Bx : sv := SOff 20 0.
Definition sd_rg_io : YP09.region :=
  YP09.mkRegion (Some 19%nat) 64 80 0 0
    [YP09.mkChunk 64 (CVal 8 (SOff 34 0)); YP09.mkChunk 72 (CVal 8 (SOff 36 0))].
Definition sd_rg_hc : YP09.region :=
  YP09.mkRegion (Some 19%nat) 160 164 0 0 [YP09.mkChunk 160 (CVal 4 (SOff 32 0))].
Definition sd_rg_ifl : YP09.region := YP09.mkRegion (Some 19%nat) 212 216 212 216 [].
Definition sd_rg_ist : YP09.region := YP09.mkRegion (Some 19%nat) 1736 1760 1736 1760 [].
Definition sd_rg_txd : YP09.region :=
  YP09.mkRegion (Some 19%nat) 18200 18208 18200 18208 [YP09.mkChunk 18200 (CVal 8 (SOff 33 0))].
Definition sd_rg_now : YP09.region :=
  YP09.mkRegion (Some 9%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 35 0))].
Definition sd_rg_sh : YP09.region := YP09.mkRegion (Some 21%nat) 0 1 0 0 [YP09.mkChunk 0 (CZero 1)].
Definition sd_regs1 : smem :=
  [sd_rg_io; sd_rg_hc; sd_rg_ifl; sd_rg_ist; sd_rg_txd; sd_rg_now; sd_rg_sh].
Definition sd_facts1 : facts :=
  mkFacts [(19%nat, mkAF SENDDATA_S SENDDATA_S 6); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0)]
          [mkAC BC_GE (SOff 10 0) (SLit 0)] [].
Definition ss_mid : sstate := mkSS SD_FB sr_atoms sd_regs1 None sd_facts1.

(* state 2, at the return address, on the path r = 0: the read-modify-write of stats.tx_frames.
   Atom 32 is the 8 bytes at s + 18192. *)
Definition SD_SH2 : list shent := [mkSHE 21 0 8].
Definition sd_rg_txf : YP09.region :=
  YP09.mkRegion (Some 21%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition sd_facts2 : facts :=
  mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (21%nat, mkAF SD_TXF SD_TXF 4)]
          [mkAC BC_EQ (SOff 10 0) (SLit 0)] [].
Definition ss_mid2 : sstate := mkSS SD_RET2 sr_atoms [sd_rg_txf] None sd_facts2.

(* the two states with no region: n < 0 at SD_FB, and r <> 0 at the return address *)
Definition ss_neg : sstate :=
  mkSS SD_FB sr_atoms [] None (mkFacts [] [mkAC BC_LT (SOff 10 0) (SLit 0)] []).
Definition ss_fail : sstate :=
  mkSS SD_RET2 sr_atoms [] None (mkFacts [] [mkAC BC_NE (SOff 10 0) (SLit 0)] []).

(* The bytes each run may change: the stores of :397 / inflight_start / :399, and send_raw's :91-92. *)
Definition sd_Z1 (a : Z) : Prop :=
  (SENDDATA_S + 212 <= a < SENDDATA_S + 216) \/ (SENDDATA_S + 1736 <= a < SENDDATA_S + 1760) \/
  (SENDDATA_S + 18200 <= a < SENDDATA_S + 18208).
Definition sd_Z2 (a : Z) : Prop := SENDDATA_S + 18192 <= a < SENDDATA_S + 18200.

Lemma sd_Z1_G : forall a, sd_Z1 a -> W_journalG.inG TGx.G_HARNESS_B a.
Proof.
intros a Ha. apply sd_inG_gs. change TW.SZ_g_s with 18264. unfold sd_Z1, SENDDATA_S, TB_g_s in *. lia.
Qed.
Lemma sd_Z2_G : forall a, sd_Z2 a -> W_journalG.inG TGx.G_HARNESS_B a.
Proof.
intros a Ha. apply sd_inG_gs. change TW.SZ_g_s with 18264. unfold sd_Z2, SENDDATA_S, TB_g_s in *. lia.
Qed.
Lemma sd_Z1_lo : forall a, sd_Z1 a -> 0 <= a < 2 ^ 64.
Proof. intros a Ha. unfold sd_Z1, SENDDATA_S, TB_g_s in Ha. lia. Qed.
Lemma sd_Z2_lo : forall a, sd_Z2 a -> 0 <= a < 2 ^ 64.
Proof. intros a Ha. unfold sd_Z2, SENDDATA_S, TB_g_s in Ha. lia. Qed.
(* ------------------------------------------------------------------ *)
(* 4. The bytes io_send writes are bytes of G                          *)
(* ------------------------------------------------------------------ *)

Lemma sd_inG_row : forall o b n a, In (o, b, n) TMAP_B -> b <= a < b + n ->
  W_journalG.inG TGx.G_HARNESS_B a.
Proof.
intros o b n a Hin Ha. unfold W_journalG.inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

Lemma sd_iosend_inG : forall n a, 0 <= n -> iosend_wr n a -> W_journalG.inG TGx.G_HARNESS_B a.
Proof.
intros n a Hn H.
pose proof (Z.le_min_r n TC.SPEC_MAX_FRAME) as Hm.
assert (Hm0 : 0 <= Z.min n TC.SPEC_MAX_FRAME) by (apply Z.min_glb; [exact Hn | unfold TC.SPEC_MAX_FRAME; lia]).
unfold TC.SPEC_MAX_FRAME in Hm, Hm0.
unfold iosend_wr, twb_fld, TC.SPEC_MAX_FRAME, TW.A_GOT_e2, TW.A_GOT_e3, TW.A_GOT_acks, TW.A_M_host_counter, TW.A_M_next_ka,
  TW.A_M_last_display, TW.A_M_display_sent, TW.A_M_fly_on, TW.A_M_fly_cmd, TW.A_M_fly_counter,
  TW.A_M_fly_retries, TW.A_M_fly_sent, TW.A_M_fly_len, TW.A_M_fly_frame, TW.A_Cmd_st in H.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]].
- apply (sd_inG_row TW.OFF_g_fail_next TB_g_fail_next 1); [exact TMAP_B_g_fail_next | lia].
- apply (sd_inG_row TW.OFF_GOT TB_GOT TW.SZ_GOT); [exact TMAP_B_GOT | unfold TW.SZ_GOT, TW.OFF_GOT in *; lia].
- apply (sd_inG_row TW.OFF_GOT TB_GOT TW.SZ_GOT); [exact TMAP_B_GOT | unfold TW.SZ_GOT, TW.OFF_GOT in *; lia].
- apply (sd_inG_row TW.OFF_GOT TB_GOT TW.SZ_GOT); [exact TMAP_B_GOT | unfold TW.SZ_GOT, TW.OFF_GOT in *; lia].
- apply (sd_inG_row TW.OFF_g_last_counter TB_g_last_counter TW.SZ_g_last_counter);
    [exact TMAP_B_g_last_counter | unfold TW.SZ_g_last_counter in *; lia].
- apply (sd_inG_row TW.OFF_M TB_M TW.SZ_M); [exact TMAP_B_M | unfold TW.SZ_M, TW.OFF_M in *; lia].
- apply (sd_inG_row TW.OFF_M TB_M TW.SZ_M); [exact TMAP_B_M | unfold TW.SZ_M, TW.OFF_M in *; lia].
- apply (sd_inG_row TW.OFF_M TB_M TW.SZ_M); [exact TMAP_B_M | unfold TW.SZ_M, TW.OFF_M in *; lia].
- apply (sd_inG_row TW.OFF_M TB_M TW.SZ_M); [exact TMAP_B_M | unfold TW.SZ_M, TW.OFF_M in *; lia].
- apply (sd_inG_row TW.OFF_M TB_M TW.SZ_M); [exact TMAP_B_M | unfold TW.SZ_M, TW.OFF_M in *; lia].
- apply (sd_inG_row TW.OFF_M TB_M TW.SZ_M); [exact TMAP_B_M | unfold TW.SZ_M, TW.OFF_M in *; lia].
- apply (sd_inG_row TW.OFF_M TB_M TW.SZ_M); [exact TMAP_B_M | unfold TW.SZ_M, TW.OFF_M in *; lia].
- apply (sd_inG_row TW.OFF_M TB_M TW.SZ_M); [exact TMAP_B_M | unfold TW.SZ_M, TW.OFF_M in *; lia].
- apply (sd_inG_row TW.OFF_M TB_M TW.SZ_M); [exact TMAP_B_M | unfold TW.SZ_M, TW.OFF_M in *; lia].
- apply (sd_inG_row TW.OFF_M TB_M TW.SZ_M); [exact TMAP_B_M | unfold TW.SZ_M, TW.OFF_M in *; lia].
- apply (sd_inG_row TW.OFF_M TB_M TW.SZ_M); [exact TMAP_B_M | unfold TW.SZ_M, TW.OFF_M in *; lia].
- destruct H as (s & Hs & H). unfold TC.CMDS_MAX in Hs.
  apply (sd_inG_row TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd);
    [exact TMAP_B_g_cmd | unfold TW.SZ_g_cmd, TW.OFF_g_cmd in *; lia].
- apply (sd_inG_row TW.OFF_g_q TB_g_q TW.SZ_g_q); [exact TMAP_B_g_q | unfold TW.SZ_g_q in *; lia].
- apply (sd_inG_row TW.OFF_g_nq TB_g_nq TW.SZ_g_nq); [exact TMAP_B_g_nq | unfold TW.SZ_g_nq in *; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 5. A store read through a mixed view                                *)
(* ------------------------------------------------------------------ *)

Definition sd_inb (lo n a : Z) : bool := ((lo <=? a) && (a <? lo + n))%bool.
Definition sd_mix (P : Z -> bool) (rdF rd0 : Z -> option Z) : Z -> option Z :=
  fun x => if P x then rdF x else rd0 x.

Lemma sd_inb_true : forall lo n a, lo <= a < lo + n -> sd_inb lo n a = true.
Proof. intros lo n a H. unfold sd_inb. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma sd_inb_false : forall lo n a, ~ (lo <= a < lo + n) -> sd_inb lo n a = false.
Proof.
intros lo n a H. unfold sd_inb.
destruct (Z.leb_spec lo a) as [h1|h1]; destruct (Z.ltb_spec a (lo + n)) as [h2|h2]; cbn [andb];
  first [reflexivity | exfalso; apply H; lia].
Qed.
Section mid. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

Lemma sd_io_at : BASE + AF_io_send = TI.ti_io_send timg_B /\ VAL A_TEXT = BASE /\
  BASE + AF_io_send = 0x82ffc /\ 0 <= BASE < 2 ^ 40.
Proof.
split; [vm_compute; reflexivity|]. split; [reflexivity|]. split; [vm_compute; reflexivity|].
vm_compute. split; [discriminate | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* 2. g_s: writable, zero shadow, addressable                          *)
(* ------------------------------------------------------------------ *)

Lemma sd_gs_writable : forall (m : word -> option byte) a,
  SENDDATA_S <= a < SENDDATA_S + 18264 -> writable_at segs m a.
Proof.
intros m a Ha. apply (gx_rw_writable segs TGx.G_HARNESS_B a G_HARNESS_B_rw).
apply sd_inG_gs. change TW.SZ_g_s with 18264. exact Ha.
Qed.

Lemma sd_gs_vis : forall (H : word -> bool) (m : word -> option byte) a,
  SENDDATA_S <= a < SENDDATA_S + 18264 -> aview segs H m a <> None.
Proof.
intros H m a Ha. apply (gx_rw_vis segs TGx.G_HARNESS_B a G_HARNESS_B_rw).
apply sd_inG_gs. change TW.SZ_g_s with 18264. exact Ha.
Qed.

Lemma sd_shadow0 : forall ly S (W : world segs) mem md T,
  trans_senddata_cells B -> @AR rc segs B ly S W mem md ->
  T mod 8 = 0 -> SENDDATA_S <= T -> T + 8 <= SENDDATA_S + 18264 ->
  aview segs (w_H W) mem (SHADOW_OFF + T / 8) = Some 0.
Proof.
intros ly S W mem md T HSC HAR H8 H1 H2.
assert (HZ : aview segs (w_H W) mem (FCells.shadow_addr T) = Some 0).
{ apply (decode_zshadow_rd B ly S W mem md SENDDATA_S (SENDDATA_S + TW.SZ_g_s) T HAR H8 H1);
  [change TW.SZ_g_s with 18264; lia | exact HSC]. }
replace (SHADOW_OFF + T / 8) with (FCells.shadow_addr T);
  [exact HZ | unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF; lia].
Qed.

Lemma sd_ra : forall ly S (W : world segs) mem md,
  trans_senddata_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF SENDDATA_S 18264.
Proof.
intros ly S W mem md HSC HAR x Hx.
assert (EC : SENDDATA_S = 6157888) by reflexivity.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
exists 0. split; [|left; reflexivity].
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + (8 * (x / 8)) / 8)
  by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
apply (sd_shadow0 ly S W mem md (8 * (x / 8)) HSC HAR);
  [rewrite Z.mul_comm; apply Z_mod_mult | rewrite EC in *; lia | rewrite EC in *; lia].
Qed.

Lemma sd_hull : forall ly S (W : world segs) mem md q n,
  trans_senddata_cells B -> @AR rc segs B ly S W mem md ->
  0 < n -> SENDDATA_S + 128 <= q -> q + n + 128 <= SENDDATA_S + 18264 ->
  shadow_hull_vis (aview segs (w_H W) mem) q n.
Proof.
intros ly S W mem md q n HSC HAR Hn H1 H2 s Hs.
pose proof (sd_ra ly S W mem md HSC HAR) as HRA.
assert (EC : SENDDATA_S = 6157888) by reflexivity.
unfold shadow_addr in Hs.
pose proof (Z.div_mod q 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Mq.
pose proof (Z.div_mod (q + n - 1) 8 ltac:(lia)) as Dq2. pose proof (Z.mod_pos_bound (q + n - 1) 8 ltac:(lia)) as Mq2.
pose proof (Z.div_mod (SHADOW_OFF + q / 8) 8 ltac:(lia)) as Ds.
pose proof (Z.mod_pos_bound (SHADOW_OFF + q / 8) 8 ltac:(lia)) as Ms.
pose proof (Z.div_mod (SHADOW_OFF + (q + n - 1) / 8) 8 ltac:(lia)) as Ds2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (q + n - 1) / 8) 8 ltac:(lia)) as Ms2.
assert (Hy : SENDDATA_S <= 8 * (s - SHADOW_OFF) < SENDDATA_S + 18264)
  by (unfold SHADOW_OFF in *; rewrite EC in *; lia).
destruct (HRA (8 * (s - SHADOW_OFF)) Hy) as (v & Hv & _).
unfold shadow_of_addr in Hv.
replace (SHADOW_OFF + 8 * (s - SHADOW_OFF) / 8) with s in Hv
  by (rewrite Z.mul_comm, Z.div_mul by lia; lia).
rewrite Hv. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. What a run of this walk keeps                                    *)
(* ------------------------------------------------------------------ *)

Lemma sd_keep_step : forall lyc Sc (W : world segs) memc mdc (W1 : world segs) memX memY slo shi
    (Eo Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B TGx.G_HARNESS_B -> @AR rc segs B lyc Sc W memc mdc ->
  (forall a, Zs a -> W_journalG.inG TGx.G_HARNESS_B a) ->
  acall_kept_g segs B TGx.G_HARNESS_B lyc Sc W memc W1 memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W1) memY a = aview segs (w_H W1) memX a) ->
  (forall a, apresent (w_H W1) memX a -> apresent (w_H W1) memY a) ->
  acall_kept_g segs B TGx.G_HARNESS_B lyc Sc W memc W1 memY slo shi Eo.
Proof.
intros lyc Sc W memc mdc W1 memX memY slo shi Eo Zs LAWS HGX HAR HZG HK Hkp Hgr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (GLOW : forall a, Zs a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (inG_low segs B transportb_segs_low TGx.G_HARNESS_B a HGX (HZG a Ha))).
apply (dk_kept_step_gw segs B LAWS transportb_segs_low TGx.G_HARNESS_B lyc Sc W memc mdc W1 memX memY slo shi Eo Zs
  HAR HK Hkp Hgr).
- intros a Ha Hc. exfalso. pose proof (GLOW a Ha). unfold kLowMemEnd in *. lia.
- intros b m i Hb Hi Ha. exfalso.
  destruct (HGX _ (HZG _ Ha)) as [Hi' _].
  exact (blk_img segs B LAWS lyc Sc W memc mdc b m (b + i) HAR Hb ltac:(lia) Hi').
- intros a Ha _ HnG _ _. exact (HnG (HZG a Ha)).
- intros cid pos a Hin Hr Ha. exfalso.
  destruct (HGX _ (HZG _ Ha)) as [Hi' _].
  pose proof (GLOW a Ha) as Hl.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
  + exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(lia) Hi').
  + pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
Qed.

(* A word of the stack or of the own frame, outside g_s, is kept by a run. *)
Lemma sd_rdword_keep : forall (W1 : world segs) memX memY (Zs : Z -> Prop) a v,
  (forall x, 0 <= x < 2 ^ 64 -> ~ Zs x -> aview segs (w_H W1) memY x = aview segs (w_H W1) memX x) ->
  (forall k, 0 <= k < 8 -> 0 <= a + k < 2 ^ 64 /\ ~ Zs (a + k)) ->
  rdword (aview segs (w_H W1) memX) a = Some v -> rdword (aview segs (w_H W1) memY) a = Some v.
Proof.
intros W1 memX memY Zs a v Hkp Ha Hv.
rewrite (rdword_ext (aview segs (w_H W1) memX) (aview segs (w_H W1) memY) a); [exact Hv|].
intros kk Hk. destruct (Ha kk Hk) as [H1 H2]. exact (Hkp (a + kk) H1 H2).
Qed.

(* ------------------------------------------------------------------ *)
(* 3b. The entry state of a run with no region                         *)
(* ------------------------------------------------------------------ *)

Definition sd_E0 (regsx : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regsx []).

Lemma sd_entry_nr : forall (W : world segs) (regsx : bvmap 5 word) mem (pc : Z) (cc : acond),
  branch_taken (ac_c cc) (sv_denot (sd_E0 regsx) (ac_a cc)) (sv_denot (sd_E0 regsx) (ac_b cc)) = true ->
  st_ok_pi segs VAL (sd_E0 regsx) (mkSS pc sr_atoms [] None (mkFacts [] [cc] []))
    (restrict (w_H W) (@YK11.mkst fx regsx (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regsx mem pc cc Hcc.
rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [exact I|]. split; [|exact I]. split; [|exact I]. destruct cc. exact Hcc.
Qed.

(* ------------------------------------------------------------------ *)
(* 3c. The entry states of the two runs with regions                   *)
(* ------------------------------------------------------------------ *)

(* The valuation of run 1: the 32 registers at the cut, then the four world values the run reads and now. *)
Definition sd_E1 (regsx : bvmap 5 word) (X : list byte) (nw : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regsx
    [w64 (TW.u_at X 1808 4); w64 (TW.u_at X 19848 8); w64 (TW.u_at X 1712 8); w64 nw;
     w64 (TW.u_at X 1720 8)]).
(* The valuation of run 2: the 32 registers at the return, then g_s.stats.tx_frames. *)
Definition sd_E2 (regsx : bvmap 5 word) (Y : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regsx [w64 (TW.u_at Y 19840 8)]).

Lemma sd_shok_of : forall ly S (W : world segs) mem md (E : env) (mt : nat) (p lo hi : Z),
  trans_senddata_cells B -> @AR rc segs B ly S W mem md ->
  ew E 20 = w64 SHADOW_OFF -> ew E mt = w64 p ->
  0 <= p < 2 ^ 47 -> lo < hi -> SENDDATA_S <= p + lo -> p + hi <= SENDDATA_S + 18264 ->
  sh_ok segs SD_Bx [mkSHE mt lo hi] E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E mt p lo hi HSC HAR E20 Emt Hp Hlh H1 H2.
unfold sh_ok. constructor; [|constructor].
apply (shent_ok_of_range segs (w_H W) mem E SD_Bx mt SENDDATA_S 18264 p lo hi
  (sd_ra ly S W mem md HSC HAR)).
- unfold U, SD_Bx. cbn [sv_denot]. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned.
  unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
- unfold U. cbn [sv_denot]. rewrite Emt, Z.add_0_r, Z_to_bv_bv_unsigned.
  unfold w64. apply unsigned_lit_small. lia.
- exact H1.
- exact H2.
- intros x Hx. unfold SHADOW_OFF, SENDDATA_S, TB_g_s in *.
  destruct (Z.min_spec lo hi) as [[_ Em]|[_ Em]]; rewrite Em in Hx;
    destruct (Z.max_spec lo hi) as [[_ EM]|[_ EM]]; rewrite EM in Hx; lia.
Qed.

Lemma sd_entry1 : forall ly S (W : world segs) (regsx : bvmap 5 word) mem md (X : list byte) (nw sp1x nn : Z),
  trans_senddata_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) X ->
  YK11.getr regsx 9 = w64 sp1x ->
  YK11.getr regsx 19 = w64 SENDDATA_S -> YK11.getr regsx 20 = w64 SHADOW_OFF ->
  YK11.getr regsx 21 = w64 SD_SH160 ->
  YK11.getr regsx 10 = w64 nn ->
  alloc_ceiling <= sp1x -> sp1x <= 2 ^ 47 ->
  rdword (aview segs (w_H W) mem) (sp1x + 16) = Some nw ->
  0 <= nn <= 1514 -> 0 <= nw < 2 ^ 64 ->
  st_ok_pi segs VAL (sd_E1 regsx X nw) ss_mid
    (restrict (w_H W) (@YK11.mkst fx regsx (Z_to_bv 64 (BASE + SD_FB)) mem (YK11.seg_rom segs)))
  /\ sh_ok segs SD_Bx SD_SH1 (sd_E1 regsx X nw) (mrestrict (w_H W) mem).
Proof.
intros ly S W regsx mem md X nw sp1x nn HSC HAR Htw R9 R19 R20 R21 R10 Hsp1 Hsp47 Hnow HGE HNWR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESH160 : SD_SH160 = 2148220636) by reflexivity.
assert (ESS : SENDDATA_S = 6157888) by reflexivity.
assert (ESHO : SHADOW_OFF = 2147450880) by reflexivity.
set (E := sd_E1 regsx X nw).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = YK11.getr regsx rr)
  by (intros n rr Hn; unfold E, sd_E1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) =
    nth j [w64 (TW.u_at X 1808 4); w64 (TW.u_at X 19848 8); w64 (TW.u_at X 1712 8); w64 nw;
           w64 (TW.u_at X 1720 8)] (Z_to_bv 64 0))
  by (intros j Hj; unfold E, sd_E1; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36.
cbn [Nat.add nth] in E32, E33, E34, E35, E36.
assert (E19 : ew E 19 = w64 SENDDATA_S) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = w64 SHADOW_OFF) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (U9 : bv_unsigned (ew E 9) = sp1x)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = SENDDATA_S)
  by (rewrite E19; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite E20; unfold w64; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SD_SH160)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small;
      lia).
assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
  by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
assert (RD : forall kk (c : nat), 0 <= kk -> kk + Z.of_nat c <= 18264 ->
    val_mem segs (mrestrict (w_H W) mem) (SENDDATA_S + kk) c (TW.u_at X (TW.OFF_g_s + kk) c))
  by (intros kk c Hk Hc;
      exact (tw_read_val segs _ TMAP_B X TW.OFF_g_s TB_g_s TW.SZ_g_s kk c TMAP_B_ok Htw TMAP_B_g_s Hk
               ltac:(change TW.SZ_g_s with 18264; lia))).
split; [|exact (sd_shok_of ly S W mem md E 19 SENDDATA_S 0 18264 HSC HAR E20 E19
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))].
rewrite restrict_mkst_fx. unfold ss_mid, sd_regs1.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok,
    sd_rg_io, sd_rg_hc, sd_rg_ifl, sd_rg_ist, sd_rg_txd, sd_rg_now, sd_rg_sh;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite ?U9, ?U19, ?U21.
  + split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val segs E _ SENDDATA_S 64 8 (SOff 34 0) (TW.u_at X 1712 8));
        [apply DEN; [exact E34 | apply TWL.u_at_range] | apply TWL.u_at_range | lia |].
      change 1712 with (TW.OFF_g_s + 64). apply RD; lia.
    * apply (chunk_ok_val segs E _ SENDDATA_S 72 8 (SOff 36 0) (TW.u_at X 1720 8));
        [apply DEN; [exact E36 | apply TWL.u_at_range] | apply TWL.u_at_range | lia |].
      change 1720 with (TW.OFF_g_s + 72). apply RD; lia.
  + split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ SENDDATA_S 160 4 (SOff 32 0) (TW.u_at X 1808 4));
      [apply DEN; [exact E32 | pose proof (TWL.u_at_range X 1808 4) as HR4; change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in HR4; lia]
      | pose proof (TWL.u_at_range X 1808 4) as HR4; change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in HR4; lia | lia |].
    change 1808 with (TW.OFF_g_s + 160). apply RD; lia.
  + split; [lia|]. split; [lia|].
    split; [|apply Forall_nil]. intros o Ho. apply sd_gs_writable. lia.
  + split; [lia|]. split; [lia|].
    split; [|apply Forall_nil]. intros o Ho. apply sd_gs_writable. lia.
  + split; [lia|]. split; [lia|].
    split; [intros o Ho; apply sd_gs_writable; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ SENDDATA_S 18200 8 (SOff 33 0) (TW.u_at X 19848 8));
      [apply DEN; [exact E33 | apply TWL.u_at_range] | apply TWL.u_at_range | lia |].
    change 19848 with (TW.OFF_g_s + 18200). apply RD; lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ sp1x 16 8 (SOff 35 0) nw);
      [apply DEN; [exact E35 | exact HNWR] | exact HNWR | lia |].
    exact (val_mem_of_rdword segs (w_H W) mem (sp1x + 16) nw Hnow).
  + split; [lia|].
    split; [lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    intros i Hi. cbn [YP09.c_len YP09.cv_len YP09.c_off YP09.c_val] in Hi |- *.
    exists (Z_to_bv 8 0). split; [reflexivity|].
    replace (SD_SH160 + 0 + i) with (SHADOW_OFF + (SENDDATA_S + 160) / 8) by (unfold SD_SH160 in *; lia).
    assert (HZ : aview segs (w_H W) mem (SHADOW_OFF + (SENDDATA_S + 160) / 8) = Some 0)
      by (apply (sd_shadow0 ly S W mem md (SENDDATA_S + 160) HSC HAR);
          unfold SENDDATA_S, TB_g_s; [reflexivity | lia | lia]).
    unfold aview in HZ.
    destruct (YP09.mbyte segs (mrestrict (w_H W) mem) (SHADOW_OFF + (SENDDATA_S + 160) / 8)) as [b0|] eqn:Eb;
      [|discriminate HZ].
    cbn [option_map] in HZ. injection HZ as HZ.
    apply (f_equal (fun z => Z_to_bv 8 z)) in HZ. rewrite Z_to_bv_bv_unsigned in HZ.
    rewrite HZ in Eb. exact Eb.
- apply pairwise_disjoint_of_extents.
  unfold sd_rg_io, sd_rg_hc, sd_rg_ifl, sd_rg_ist, sd_rg_txd, sd_rg_now, sd_rg_sh, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U19, U21.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold sd_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2 ac_c ac_a ac_b].
  rewrite U19, U20. rewrite !Z.pow_0_r, !Z.mod_1_r.
  split.
  { split; [split; [lia|]|].
    - split; [change (2 ^ 6) with 64; unfold SENDDATA_S, TB_g_s; reflexivity | lia].
    - split; [split; [lia | split; [reflexivity | lia]] | exact I]. }
  split; [|exact I]. split; [|exact I].
  assert (D10 : sv_denot E (SOff 10 0) = w64 nn)
    by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 10%nat 10%bv eq_refl); exact R10).
  unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite D10. cbn [branch_taken sv_denot]. unfold w64.
  rewrite (sdm_lts0 nn ltac:(lia)).
  apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.

Lemma sd_entry2 : forall ly S (W : world segs) (regsx : bvmap 5 word) mem md (Y : list byte),
  trans_senddata_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Y ->
  YK11.getr regsx 20 = w64 SHADOW_OFF -> YK11.getr regsx 21 = w64 SD_TXF ->
  YK11.getr regsx 10 = w64 0 ->
  st_ok_pi segs VAL (sd_E2 regsx Y) ss_mid2
    (restrict (w_H W) (@YK11.mkst fx regsx (Z_to_bv 64 (BASE + SD_RET2)) mem (YK11.seg_rom segs)))
  /\ sh_ok segs SD_Bx SD_SH2 (sd_E2 regsx Y) (mrestrict (w_H W) mem).
Proof.
intros ly S W regsx mem md Y HSC HAR Htw R20 R21 R10.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESS : SENDDATA_S = 6157888) by reflexivity.
assert (ESHO : SHADOW_OFF = 2147450880) by reflexivity.
set (E := sd_E2 regsx Y).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = YK11.getr regsx rr)
  by (intros n rr Hn; unfold E, sd_E2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 (TW.u_at Y 19840 8)).
{ unfold E, sd_E2. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regsx [w64 (TW.u_at Y 19840 8)] 0). }
assert (E20 : ew E 20 = w64 SHADOW_OFF) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = w64 SD_TXF) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite E20; unfold w64; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SD_TXF)
  by (rewrite E21; unfold w64; apply unsigned_lit_small; unfold SD_TXF in *; lia).
split; [|exact (sd_shok_of ly S W mem md E 21 SD_TXF 0 8 HSC HAR E20 E21
                  ltac:(unfold SD_TXF in *; lia) ltac:(lia)
                  ltac:(unfold SD_TXF; lia) ltac:(unfold SD_TXF; lia))].
rewrite restrict_mkst_fx. unfold ss_mid2.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold sd_rg_txf, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U21.
  split; [unfold SD_TXF in *; lia|]. split; [unfold SD_TXF in *; lia|].
  split; [intros o Ho; apply sd_gs_writable; unfold SD_TXF in *; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs E _ SD_TXF 0 8 (SOff 32 0) (TW.u_at Y 19840 8));
    [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | apply TWL.u_at_range | lia |].
  replace (SD_TXF + 0) with (SENDDATA_S + 18192) by (unfold SD_TXF; lia).
  change 19840 with (TW.OFF_g_s + 18192).
  exact (tw_read_val segs _ TMAP_B Y TW.OFF_g_s TB_g_s TW.SZ_g_s 18192 8 TMAP_B_ok Htw TMAP_B_g_s
           ltac:(lia) ltac:(change TW.SZ_g_s with 18264; lia)).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- unfold sd_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2 ac_c ac_a ac_b].
  rewrite U20, U21. rewrite !Z.pow_0_r, !Z.mod_1_r.
  split.
  { split; [split; [lia | split; [reflexivity | lia]]|].
    split; [split; [unfold SD_TXF in *; lia|]|exact I].
    split; [change (2 ^ 4) with 16; unfold SD_TXF, SENDDATA_S, TB_g_s; reflexivity | lia]. }
  split; [|exact I]. split; [|exact I].
  assert (D10 : sv_denot E (SOff 10 0) = w64 0)
    by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 10%nat 10%bv eq_refl); exact R10).
  unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite D10. cbn [branch_taken sv_denot]. unfold w64.
  apply bv_eqb_eq. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 3d. The world after the run's stores                                *)
(* ------------------------------------------------------------------ *)

Lemma sd_vm_byte : forall (H : word -> bool) (m : word -> option byte) a (n : nat) v j,
  val_mem segs (mrestrict H m) a n v -> (j < n)%nat ->
  aview segs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v j Hv Hj. unfold aview. rewrite (Hv j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
cbv [YO0f.le_byte YG0f.le_byte]. apply Z.mod_mod. lia.
Qed.

Ltac sd_mix_step :=
  lazymatch goal with
  | |- forall j, (j < ?m)%nat -> _ =>
      let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; unfold sd_mix;
      repeat (rewrite sd_inb_true by lia || rewrite sd_inb_false by lia); cbn [orb]
  | |- forall x, tw_in _ x -> _ =>
      let x := fresh "x" in let Hx := fresh "Hx" in let Hn := fresh "Hn" in intros x Hx Hn; unfold sd_mix;
      let Hb := fresh "Hb" in
      lazymatch goal with |- (if (_ || sd_inb ?lo ?n x)%bool then _ else _) = _ =>
        assert (Hb : sd_inb lo n x = false) by (apply sd_inb_false; lia); rewrite Hb, orb_false_r; reflexivity
      | |- (if sd_inb ?lo ?n x then _ else _) = _ =>
        assert (Hb : sd_inb lo n x = false) by (apply sd_inb_false; lia); rewrite Hb; reflexivity
      end
  end.

Lemma sd_world6 : forall (W1 : world segs) mem0 mem1 (X : list byte) (nn nw v3 v6 : Z),
  tw_at TMAP_B (aview segs (w_H W1) mem0) X ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ sd_Z1 a -> aview segs (w_H W1) mem1 a = aview segs (w_H W1) mem0 a) ->
  val_mem segs (mrestrict (w_H W1) mem1) (SENDDATA_S + 1736) 8 nn ->
  val_mem segs (mrestrict (w_H W1) mem1) (SENDDATA_S + 212) 4 1 ->
  val_mem segs (mrestrict (w_H W1) mem1) (SENDDATA_S + 1744) 4 v3 ->
  val_mem segs (mrestrict (w_H W1) mem1) (SENDDATA_S + 1748) 4 0 ->
  val_mem segs (mrestrict (w_H W1) mem1) (SENDDATA_S + 1752) 8 nw ->
  val_mem segs (mrestrict (w_H W1) mem1) (SENDDATA_S + 18200) 8 v6 ->
  tw_at TMAP_B (aview segs (w_H W1) mem1)
    (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd X 3384 (TW.put 8 nn)) 1860 (TW.put 4 1))
       3392 (TW.put 4 v3)) 3396 (TW.put 4 0)) 3400 (TW.put 8 nw)) 19848 (TW.put 8 v6)).
Proof.
intros W1 mem0 mem1 X nn nw v3 v6 Htw KR V1 V2 V3 V4 V5 V6.
assert (ESS : SENDDATA_S = 6157888) by reflexivity.
assert (ETA : TB_g_s = 6157888) by reflexivity.
set (rd0 := aview segs (w_H W1) mem0) in *. set (rdF := aview segs (w_H W1) mem1) in *.
set (P1 := fun x => sd_inb (TB_g_s + 1736) 8 x).
set (P2 := fun x => (P1 x || sd_inb (TB_g_s + 212) 4 x)%bool).
set (P3 := fun x => (P2 x || sd_inb (TB_g_s + 1744) 4 x)%bool).
set (P4 := fun x => (P3 x || sd_inb (TB_g_s + 1748) 4 x)%bool).
set (P5 := fun x => (P4 x || sd_inb (TB_g_s + 1752) 8 x)%bool).
set (P6 := fun x => (P5 x || sd_inb (TB_g_s + 18200) 8 x)%bool).
apply (tw_kept TMAP_B (sd_mix P6 rdF rd0)).
2:{ intros x Hx. unfold sd_mix, P6, P5, P4, P3, P2, P1.
    destruct (sd_inb (TB_g_s + 1736) 8 x) eqn:B1; [reflexivity|].
    destruct (sd_inb (TB_g_s + 212) 4 x) eqn:B2; [reflexivity|].
    destruct (sd_inb (TB_g_s + 1744) 4 x) eqn:B3; [reflexivity|].
    destruct (sd_inb (TB_g_s + 1748) 4 x) eqn:B4; [reflexivity|].
    destruct (sd_inb (TB_g_s + 1752) 8 x) eqn:B5; [reflexivity|].
    destruct (sd_inb (TB_g_s + 18200) 8 x) eqn:B6; [reflexivity|].
    cbn [orb]. pose proof (TMAP_B_hull x Hx) as Hh. unfold TGx.G_HARNESS_B_LO, TGx.G_HARNESS_B_HI in Hh.
    unfold sd_inb in B1, B2, B3, B4, B5, B6.
    apply KR; [lia|]. unfold sd_Z1.
    repeat match goal with Hb : ((_ <=? _) && (_ <? _))%bool = false |- _ =>
      apply andb_false_iff in Hb; destruct Hb as [Hb|Hb]; [apply Z.leb_gt in Hb | apply Z.ltb_ge in Hb] end;
    lia. }
apply (tw_write TMAP_B (sd_mix P5 rdF rd0) _ _ TW.OFF_g_s TB_g_s TW.SZ_g_s 18200 8 v6 TMAP_B_ok);
  [| exact TMAP_B_g_s | lia | change TW.SZ_g_s with 18264; lia | | ].
2:{ intros j Hj. assert (Hj' : 0 <= Z.of_nat j < 8) by lia. unfold sd_mix, P6. cbv beta.
    rewrite (sd_inb_true (TB_g_s + 18200) 8 (TB_g_s + 18200 + Z.of_nat j)) by lia. rewrite orb_true_r.
    unfold rdF. rewrite ETA, <- ESS. exact (sd_vm_byte _ _ _ _ _ j V6 Hj). }
2:{ intros x Hx Hn. unfold sd_mix, P6. cbv beta. rewrite (sd_inb_false (TB_g_s + 18200) 8 x) by lia.
    rewrite orb_false_r. reflexivity. }
apply (tw_write TMAP_B (sd_mix P4 rdF rd0) _ _ TW.OFF_g_s TB_g_s TW.SZ_g_s 1752 8 nw TMAP_B_ok);
  [| exact TMAP_B_g_s | lia | change TW.SZ_g_s with 18264; lia | | ].
2:{ intros j Hj. assert (Hj' : 0 <= Z.of_nat j < 8) by lia. unfold sd_mix, P5. cbv beta.
    rewrite (sd_inb_true (TB_g_s + 1752) 8 (TB_g_s + 1752 + Z.of_nat j)) by lia. rewrite orb_true_r.
    unfold rdF. rewrite ETA, <- ESS. exact (sd_vm_byte _ _ _ _ _ j V5 Hj). }
2:{ intros x Hx Hn. unfold sd_mix, P5. cbv beta. rewrite (sd_inb_false (TB_g_s + 1752) 8 x) by lia.
    rewrite orb_false_r. reflexivity. }
apply (tw_write TMAP_B (sd_mix P3 rdF rd0) _ _ TW.OFF_g_s TB_g_s TW.SZ_g_s 1748 4 0 TMAP_B_ok);
  [| exact TMAP_B_g_s | lia | change TW.SZ_g_s with 18264; lia | | ].
2:{ intros j Hj. assert (Hj' : 0 <= Z.of_nat j < 4) by lia. unfold sd_mix, P4. cbv beta.
    rewrite (sd_inb_true (TB_g_s + 1748) 4 (TB_g_s + 1748 + Z.of_nat j)) by lia. rewrite orb_true_r.
    unfold rdF. rewrite ETA, <- ESS. exact (sd_vm_byte _ _ _ _ _ j V4 Hj). }
2:{ intros x Hx Hn. unfold sd_mix, P4. cbv beta. rewrite (sd_inb_false (TB_g_s + 1748) 4 x) by lia.
    rewrite orb_false_r. reflexivity. }
apply (tw_write TMAP_B (sd_mix P2 rdF rd0) _ _ TW.OFF_g_s TB_g_s TW.SZ_g_s 1744 4 v3 TMAP_B_ok);
  [| exact TMAP_B_g_s | lia | change TW.SZ_g_s with 18264; lia | | ].
2:{ intros j Hj. assert (Hj' : 0 <= Z.of_nat j < 4) by lia. unfold sd_mix, P3. cbv beta.
    rewrite (sd_inb_true (TB_g_s + 1744) 4 (TB_g_s + 1744 + Z.of_nat j)) by lia. rewrite orb_true_r.
    unfold rdF. rewrite ETA, <- ESS. exact (sd_vm_byte _ _ _ _ _ j V3 Hj). }
2:{ intros x Hx Hn. unfold sd_mix, P3. cbv beta. rewrite (sd_inb_false (TB_g_s + 1744) 4 x) by lia.
    rewrite orb_false_r. reflexivity. }
apply (tw_write TMAP_B (sd_mix P1 rdF rd0) _ _ TW.OFF_g_s TB_g_s TW.SZ_g_s 212 4 1 TMAP_B_ok);
  [| exact TMAP_B_g_s | lia | change TW.SZ_g_s with 18264; lia | | ].
2:{ intros j Hj. assert (Hj' : 0 <= Z.of_nat j < 4) by lia. unfold sd_mix, P2. cbv beta.
    rewrite (sd_inb_true (TB_g_s + 212) 4 (TB_g_s + 212 + Z.of_nat j)) by lia. rewrite orb_true_r.
    unfold rdF. rewrite ETA, <- ESS. exact (sd_vm_byte _ _ _ _ _ j V2 Hj). }
2:{ intros x Hx Hn. unfold sd_mix, P2. cbv beta. rewrite (sd_inb_false (TB_g_s + 212) 4 x) by lia.
    rewrite orb_false_r. reflexivity. }
apply (tw_write TMAP_B rd0 _ _ TW.OFF_g_s TB_g_s TW.SZ_g_s 1736 8 nn TMAP_B_ok);
  [exact Htw | exact TMAP_B_g_s | lia | change TW.SZ_g_s with 18264; lia | | ].
- intros j Hj. assert (Hj' : 0 <= Z.of_nat j < 8) by lia. unfold sd_mix, P1. cbv beta.
  rewrite (sd_inb_true (TB_g_s + 1736) 8 (TB_g_s + 1736 + Z.of_nat j)) by lia.
  unfold rdF. rewrite ETA, <- ESS. exact (sd_vm_byte _ _ _ _ _ j V1 Hj).
- intros x Hx Hn. unfold sd_mix, P1. cbv beta. rewrite (sd_inb_false (TB_g_s + 1736) 8 x) by lia. reflexivity.
Qed.

Lemma sd_world1 : forall (W1 : world segs) mem0 mem1 (Y : list byte) (v : Z),
  tw_at TMAP_B (aview segs (w_H W1) mem0) Y ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ sd_Z2 a -> aview segs (w_H W1) mem1 a = aview segs (w_H W1) mem0 a) ->
  val_mem segs (mrestrict (w_H W1) mem1) (SENDDATA_S + 18192) 8 v ->
  tw_at TMAP_B (aview segs (w_H W1) mem1) (TW.upd Y 19840 (TW.put 8 v)).
Proof.
intros W1 mem0 mem1 Y v Htw KR V.
assert (ESS : SENDDATA_S = 6157888) by reflexivity.
assert (ETA : TB_g_s = 6157888) by reflexivity.
apply (tw_write TMAP_B (aview segs (w_H W1) mem0) _ _ TW.OFF_g_s TB_g_s TW.SZ_g_s 18192 8 v TMAP_B_ok);
  [exact Htw | exact TMAP_B_g_s | lia | change TW.SZ_g_s with 18264; lia | | ].
- intros j Hj. rewrite ETA, <- ESS. exact (sd_vm_byte _ _ _ _ _ j V Hj).
- intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh. unfold TGx.G_HARNESS_B_LO, TGx.G_HARNESS_B_HI in Hh.
  apply KR; [lia|]. unfold sd_Z2. lia.
Qed.
(* ------------------------------------------------------------------ *)
(* 6. The walk, +0x188 .. +0x2a8                                       *)
(* ------------------------------------------------------------------ *)

Ltac sd_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let ee := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex ee = v); tac)
  | ?T => idtac "sd_reg: no match for" T; fail
  end.

Lemma sd_mid : @sd_mid_stmt fx rc B MT.
Proof.
unfold sd_mid_stmt, sd_fb_at.
intros REL LAWS0 IOS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bodyp ncmds now r body TF Bw Bw'
  pos sp1 F ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as LAWSc. pose proof HFIX as HFIXc.
destruct LAWS0 as (HSM & HCELLS & HSC & HGU & HGN & HROU & HRON & LAWS & MTL & MTF & HSMP & ASF & FFL & HGX & HGXN).
destruct HFIX as (HJ0 & Hret & Hra4 & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hsp16 & Hlo & Hhi & Hnc &
  Hnowr & Hbp & Hgarr & Hsrc & Hdow & Hbng & Htw0 & Hgf0 & HM & HROM & HINV1 & HINV4 & Hcnt0 & Hcnt2 & Hev &
  Esp1 & EF & HF0 & HF64 & HFc & HFapp).
destruct HCUR as (HCUR0 & HTW2 & HROM2 & Hnowslot).
pose proof HCUR0 as (HJ & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw).
destruct HREGS as (HKEEP & R2 & R9 & R10 & R19 & R20 & R21 & R23 & R25).
pose proof HKEEP as (R3 & R4 & R8 & R18 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (He0 : e = 0) by (unfold SENDDATA_EV, FRAME_FB_EV, IOSEND_EV in He; lia).
subst e.
(* the stack window *)
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HSTKe : SENDDATA_STK = 176 + IOSEND_STK) by reflexivity.
assert (HIOS : 160 <= IOSEND_STK) by (vm_compute; discriminate).
assert (Hsp1b : spZ regs - 176 <= sp1 <= spZ regs - 160)
  by (rewrite Esp1; unfold SENDDATA_FRAME; Z.div_mod_to_equations; lia).
assert (Hce1 : alloc_ceiling <= sp1 - IOSEND_STK) by lia.
assert (Hsp1ce : alloc_ceiling <= sp1) by lia.
assert (Hsp147 : sp1 <= 2 ^ 47) by lia.
assert (Hsp1m : sp1 mod 16 = 0) by (rewrite Esp1; unfold SENDDATA_FRAME; Z.div_mod_to_equations; lia).
assert (Hspb : 4096 <= spZ regs <= 2 ^ 47) by lia.
(* AR at the cut and at the call state *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
(* the world's length *)
assert (HLBw : Z.of_nat (length Bw) = 65616).
{ rewrite (tw_len TMAP_B _ Bw Htw0). rewrite Z2Nat.id by (unfold TW.W_LEN; lia). reflexivity. }
pose proof (sdm_bound Bw ncmds body) as HNB.
rewrite (sdm_unfold TF Bw body ncmds now) in HM.
(* the own frame is apart from the caller's blocks, frames and the image *)
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 SENDDATA_CID pos F
  (flag_addr lyc SENDDATA_CID pos) HAR2 Hfrs Hbl ELF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
(* the run chain *)
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TGx.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TGx.G_HARNESS_B HGX
  0 []) as RUNTO.
destruct (Z.ltb_spec (sd_n Bw ncmds body) 0) as [HNEG | HPOS].
- (* ---------------- n < 0: :395-396, straight to the release ---------------- *)
  assert (EBw : Bw' = sd_M1 Bw ncmds) by (symmetry; exact (sd_some_w _ _ _ _ HM)).
  assert (Err : r = sd_n Bw ncmds body) by (symmetry; exact (sd_some_r _ _ _ _ HM)).
  assert (EBfb : sd_Bfb Bw ncmds body = sd_M1 Bw ncmds)
    by (unfold sd_Bfb; rewrite (proj2 (Z.leb_gt 0 (sd_n Bw ncmds body)) HNEG); reflexivity).
  rewrite EBfb, <- EBw in HTW2.
  set (E := sd_E0 regs2).
  assert (HEI : img_env VAL A_LIM E) by (unfold E, sd_E0; apply Eimg_env).
  assert (EE : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = YK11.getr regs2 rr)
    by (intros nn rr Hn; unfold E, sd_E0; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (D10 : sv_denot E (SOff 10 0) = w64 (sd_n Bw ncmds body)).
  { cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 10%nat 10%bv eq_refl). exact R10. }
  assert (HCC : branch_taken (ac_c (mkAC BC_LT (SOff 10 0) (SLit 0)))
      (sv_denot (sd_E0 regs2) (ac_a (mkAC BC_LT (SOff 10 0) (SLit 0))))
      (sv_denot (sd_E0 regs2) (ac_b (mkAC BC_LT (SOff 10 0) (SLit 0)))) = true).
  { cbn [ac_c ac_a ac_b]. fold E. rewrite D10. cbn [branch_taken sv_denot].
    unfold w64. rewrite (sdm_lts0 (sd_n Bw ncmds body) ltac:(lia)). apply Z.ltb_lt. exact HNEG. }
  pose proof (sd_entry_nr W2 regs2 mem2 SD_FB (mkAC BC_LT (SOff 10 0) (SLit 0)) HCC) as HS.
  fold E in HS.
  assert (SHOK : sh_ok segs SD_Bx (@nil shent) E (mrestrict (w_H W2) mem2)) by (apply Forall_nil).
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan SD_REL.
  { apply awr_ok_x_nil. }
  set (mdw := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdw. clear mat.
  assert (KR : forall a, 0 <= a < 2 ^ 64 ->
    aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
  { intros a Ha.
    apply (kept_of_frame (segs := segs) E [] (w_H W2) mem2 (ms_mem ms) (fun _ => False) HFr);
      [intros b wlo whi x Hin Hx; cbn [windows map In] in Hin; destruct Hin | exact Ha | intros []]. }
  assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  assert (HPF : aregs_preserved regs2 (ms_regs ms)).
  { apply (aregs_preserved_of_st_ok segs (w_H W2) E _ ms regs2 [] HS);
      [ split; [intros nn Hn; unfold E, sd_E0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]
      | vm_compute; reflexivity ]. }
  sd_reg HS (Z_to_bv 5 12) (w64 (sd_n Bw ncmds body)) RF12
    ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 10%nat 10%bv eq_refl); exact R10).
  pmkst HS.
  refine (REL LAWSc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bodyp ncmds now r body TF Bw Bw'
    pos sp1 F ly2 S2 W2 (ms_mem ms) mdw 0 (ms_regs ms) HFIXc _ _).
  + split; [|split].
    * split; [exact HJ|].
      split; [unfold SENDDATA_EV, FRAME_FB_EV, IOSEND_EV; lia|].
      split; [exact Hfrs|]. split; [exact Hperm|]. split; [exact ELF|]. split; [exact Hmo|].
      split.
      { exact (sd_keep_step lyc Sc W memc mdc W2 mem2 (ms_mem ms) (spZ regs - SENDDATA_STK) (spZ regs)
          senddata_wr (fun _ => False) LAWS HGX HARc ltac:(intros a []) HK
          ltac:(intros a Ha _; exact (KR a Ha)) GA). }
      split.
      { apply Forall_forall. intros o Ho.
        rewrite (rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem ms)) (spZ regs - fst o)).
        - exact (proj1 (Forall_forall _ _) Hsaved o Ho).
        - intros kk Hk. apply KR.
          unfold SD_SAVED in Ho. cbn [In] in Ho.
          repeat (destruct Ho as [<-|Ho]; [cbn [fst]; lia|]). destruct Ho. }
      { rewrite (rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem ms))
          (F + SENDDATA_FBYTES - 8)); [exact HFLw|].
        intros kk Hk. apply KR. unfold SENDDATA_FBYTES in *. lia. }
    * apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact HTW2|].
      intros x Hx. apply KR. pose proof (TMAP_B_hull x Hx) as Hh.
      unfold TGx.G_HARNESS_B_LO, TGx.G_HARNESS_B_HI in Hh. lia.
    * rewrite EBw. destruct (sdm_keep_M1 Bw ncmds HLBw) as (_ & Hgf & _). rewrite Hgf. exact Hgf0.
  + split.
    * unfold sd_regs_keep.
      split; [transitivity (YK11.getr regs2 3); [exact (HPF 3 ltac:(hnf; lia)) | exact R3]|].
      split; [transitivity (YK11.getr regs2 4); [exact (HPF 4 ltac:(hnf; lia)) | exact R4]|].
      split; [transitivity (YK11.getr regs2 8); [exact (HPF 8 ltac:(hnf; lia)) | exact R8]|].
      split; [transitivity (YK11.getr regs2 18); [exact (HPF 18 ltac:(hnf; lia)) | exact R18]|].
      split; [transitivity (YK11.getr regs2 26); [exact (HPF 26 ltac:(hnf; lia)) | exact R26]|].
      transitivity (YK11.getr regs2 27); [exact (HPF 27 ltac:(hnf; lia)) | exact R27].
    * rewrite Err. exact RF12.
- (* ---------------- 0 <= n: the frame was built ---------------- *)
  assert (HPOSe : 0 <= sd_n Bw ncmds body) by lia.
  destruct (sdm_fr Bw ncmds body now HLBw HPOSe) as (HIB & HFRLEN).
  rewrite HIB in HM.
  destruct (sdm_sendraw TF (sd_B8 Bw ncmds body now) (sd_fr Bw ncmds body now) Bw' r HM)
    as (HIOSEND & B9 & r0 & HIO & HCASE).
  assert (EBfb : sd_Bfb Bw ncmds body = sd_B2 Bw ncmds body)
    by (unfold sd_Bfb; rewrite (proj2 (Z.leb_le 0 (sd_n Bw ncmds body)) HPOSe); reflexivity).
  rewrite EBfb in HTW2.
  rewrite sdm_B8_eq in HIOSEND, HIO.
  set (X := sd_B2 Bw ncmds body) in *.
  set (nn := sd_n Bw ncmds body) in *.
  assert (HLX : Z.of_nat (length X) = 65616) by (apply sdm_len_B2; assumption).
  assert (HNN : 0 <= nn <= 1514) by lia.
  destruct (sdm_keep_B8 X nn now HLX HNN) as (K8io & K8gf & K8fo & K8fl & K8nc & K8cst & K8cln).
  destruct (sdm_keep_B2 Bw ncmds body HLBw HPOSe) as (K2io & K2gf & K2fo & K2fl & K2nc & K2cst & K2cln).
  destruct (sdm_keep_M1 Bw ncmds HLBw) as (K1io & K1gf & K1fo & K1fl & K1nc & K1cst & K1cln).
  fold X in K2io, K2gf, K2fo, K2fl, K2nc, K2cst, K2cln.
  assert (EIOS : TW.u_at X 1720 8 = TI.ti_io_send timg_B).
  { rewrite <- HIOSEND, K8io. unfold TW.S_io_send. rewrite sdm_o_iosend. reflexivity. }
  (* the symbolic state at the cut *)
  destruct (sd_entry1 ly2 S2 W2 regs2 mem2 md2 X now sp1 nn HSC HAR2 HTW2 R9 R19 R20 R21 R10
    ltac:(lia) ltac:(lia) Hnowslot HNN ltac:(lia)) as [HS SHOK].
  set (E := sd_E1 regs2 X now) in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E) by (unfold E, sd_E1; apply Eimg_env).
  assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = YK11.getr regs2 rr)
    by (intros n rr Hn; unfold E, sd_E1; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) =
      nth j [w64 (TW.u_at X 1808 4); w64 (TW.u_at X 19848 8); w64 (TW.u_at X 1712 8); w64 now;
             w64 (TW.u_at X 1720 8)] (Z_to_bv 64 0))
    by (intros j Hj; unfold E, sd_E1; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36.
  cbn [Nat.add nth] in E32, E33, E35, E36.
  assert (U19 : bv_unsigned (ew E 19) = SENDDATA_S)
    by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small;
        unfold SENDDATA_S, TB_g_s; lia).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (U21 : bv_unsigned (ew E 21) = SD_SH160)
    by (rewrite (EE 21%nat 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small;
        assert (SD_SH160 = 2148220636) by reflexivity; lia).
  (* run 1: +0x188 .. the indirect call *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
    repeat (first
      [ apply awr_ok_x_cons;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]
      | apply awr_ok_x_cons_g;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U19 in Ha;
          apply sd_inG_gs; change TW.SZ_g_s with 18264; unfold SENDDATA_S, TB_g_s in *; lia |] ]);
    apply awr_ok_x_nil. }
  set (mdc1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdc1. clear mat.
  assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ sd_Z1 a ->
    aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hn.
    apply (kept_of_frame (segs := segs) E sd_regs1 (w_H W2) mem2 (ms_mem ms) sd_Z1 HFr); [|exact Ha|exact Hn].
    intros b wlo whi x Hin Hx. cbv beta.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin];
      [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U19, ?U9, ?U21 in Hx;
       unfold sd_Z1, SENDDATA_S, TB_g_s in *; lia|]).
    destruct Hin. }
  assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARC.
  (* what the run stored *)
  pose proof (st_ok_pi_region_nth E _ (restrict (w_H W2) ms) 2 _ HS eq_refl) as RGa.
  pose proof (st_ok_pi_region_nth E _ (restrict (w_H W2) ms) 3 _ HS eq_refl) as RGb.
  pose proof (st_ok_pi_region_nth E _ (restrict (w_H W2) ms) 4 _ HS eq_refl) as RGc.
  cbn [ms_mem restrict] in RGa, RGb, RGc.
  destruct RGa as (_ & _ & _ & HCa). destruct RGb as (_ & _ & _ & HCb). destruct RGc as (_ & _ & _ & HCc).
  cbn [base_val YP09.r_base YP09.r_chunks] in HCa, HCb, HCc.
  assert (VMC : forall (cs : list YP09.chunk) off (wN : N) ee,
      Forall (YP09.chunk_ok segs E (mrestrict (w_H W2) (ms_mem ms)) (bv_unsigned (ew E 19))) cs ->
      In (YP09.mkChunk off (CVal wN ee)) cs -> (Z.of_N wN <= 8)%Z ->
      val_mem segs (mrestrict (w_H W2) (ms_mem ms)) (SENDDATA_S + off) (N.to_nat wN)
        (bv_unsigned (sv_denot E ee) mod 2 ^ (8 * Z.of_N wN))).
  { intros cs off wN ee HF' Hin Hw.
    replace (SENDDATA_S + off) with (bv_unsigned (ew E 19) + off) by (rewrite U19; reflexivity).
    exact (val_mem_low_of_chunk segs E (mrestrict (w_H W2) (ms_mem ms)) (bv_unsigned (ew E 19))
             off wN ee (proj1 (Forall_forall _ _) HF' _ Hin) Hw). }
  assert (V2 : val_mem segs (mrestrict (w_H W2) (ms_mem ms)) (SENDDATA_S + 212) 4 1).
  { pose proof (VMC _ 212 4%N (SLit 1) HCa ltac:(cbn [In]; auto) ltac:(cbn; lia)) as HV.
    cbn [sv_denot] in HV. rewrite unsigned_lit_small in HV by lia. exact HV. }
  assert (V1 : val_mem segs (mrestrict (w_H W2) (ms_mem ms)) (SENDDATA_S + 1736) 8 nn).
  { pose proof (VMC _ 1736 8%N (SOff 10 0) HCb ltac:(cbn [In]; auto) ltac:(cbn; lia)) as HV.
    cbn [sv_denot] in HV. rewrite (EE 10%nat 10%bv eq_refl), R10, Z.add_0_r in HV.
    unfold w64 in HV. rewrite Z_to_bv_bv_unsigned, unsigned_lit_small in HV by lia.
    rewrite Z.mod_small in HV by (cbn; lia). exact HV. }
  assert (V4 : val_mem segs (mrestrict (w_H W2) (ms_mem ms)) (SENDDATA_S + 1748) 4 0).
  { pose proof (VMC _ 1748 4%N (SLit 0) HCb ltac:(cbn [In]; auto) ltac:(cbn; lia)) as HV.
    cbn [sv_denot] in HV. rewrite unsigned_lit_small in HV by lia. exact HV. }
  assert (V5 : val_mem segs (mrestrict (w_H W2) (ms_mem ms)) (SENDDATA_S + 1752) 8 now).
  { pose proof (VMC _ 1752 8%N (SOff 35 0) HCb ltac:(cbn [In]; auto) ltac:(cbn; lia)) as HV.
    cbn [sv_denot] in HV. rewrite E35, Z.add_0_r in HV. unfold w64 in HV.
    rewrite Z_to_bv_bv_unsigned, unsigned_lit_small in HV by lia.
    rewrite Z.mod_small in HV by (cbn; lia). exact HV. }
  pose proof (VMC _ 1744 4%N (SExt true 32 (SOff 32 0)) HCb ltac:(cbn [In]; auto) ltac:(cbn; lia)) as V3.
  pose proof (VMC _ 18200 8%N (SOff 33 1) HCc ltac:(cbn [In]; auto) ltac:(cbn; lia)) as V6.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V1, V2, V3, V4, V5, V6.
  (* the world at the call *)
  assert (HTWC : tw_at TMAP_B (aview segs (w_H W2) (ms_mem ms)) (sd_B8' X nn now)).
  { rewrite <- (sdm_six X nn now HLX HNN ltac:(lia)).
    assert (E3v : TW.put 4 (bv_unsigned (sv_denot E (SExt true 32 (SOff 32 0))) mod 2 ^ (8 * Z.of_N 4%N))
                  = TW.put 4 (TW.s32_at X 1808)).
    { apply sdm_put_cong32. cbn [Z.of_N]. change (8 * 4) with 32.
      rewrite Zmod_mod. cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64.
      rewrite Z_to_bv_bv_unsigned.
      pose proof (TWL.u_at_range X 1808 4) as HR4. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in HR4.
      change (Z_to_bv 64 (TW.u_at X 1808 4)) with (le_bytes_to_word (TW.sub X 1808 4)).
      rewrite (lw_world X 1808), MState.unsigned_lit_wrap.
      apply Z.mod_mod_divide. exists (2 ^ 32); reflexivity. }
    assert (E6v : TW.put 8 (bv_unsigned (sv_denot E (SOff 33 1)) mod 2 ^ (8 * Z.of_N 8%N))
                  = TW.put 8 (TW.u_at X 19848 8 + 1)).
    { cbn [Z.of_N]. change (8 * 8) with 64. cbn [sv_denot]. rewrite E33. unfold w64.
      pose proof (TWL.u_at_range X 19848 8) as HR8. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in HR8.
      rewrite !MState.unsigned_lit_wrap, Zmod_mod.
      rewrite (Z.mod_small (TW.u_at X 19848 8) (2 ^ 64)) by lia.
      apply TWL.put_mod64. lia. }
    rewrite <- E3v, <- E6v.
    exact (sd_world6 W2 mem2 (ms_mem ms) X nn now _ _ HTW2 KR1 V1 V2 V3 V4 V5 V6). }
  (* the frame is at least 60 bytes *)
  assert (HNPOS : 60 <= nn).
  { unfold nn, sd_n. rewrite (sdm_bc_val body TS0.DIGINET_MAX_FRAME_LEN
      (TW.S_cfg_sum_mode (sd_M1 Bw ncmds)) HPOSe). unfold DSpec.frame_len. lia. }
  (* the registers at the indirect call *)
  sd_reg HS (Z_to_bv 5 13) (Z_to_bv 64 (TI.ti_io_send timg_B)) T13
    ltac:(cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; unfold w64; rewrite EIOS; reflexivity).
  sd_reg HS (Z_to_bv 5 11) (w64 (SENDDATA_S + 216)) T11
    ltac:(cbn [sv_denot]; rewrite (EE 23%nat 23%bv eq_refl), R23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sd_reg HS (Z_to_bv 5 12) (w64 nn) T12
    ltac:(cbn [sv_denot]; rewrite (EE 10%nat 10%bv eq_refl), R10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sd_reg HS (Z_to_bv 5 2) (w64 sp1) T2
    ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), R2, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sd_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) T3
    ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans R3 Hgp)).
  sd_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) T4
    ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans R4 Htp)).
  sd_reg HS (Z_to_bv 5 8) (YK11.getr regs2 (Z_to_bv 5 8)) T8
    ltac:(cbn [sv_denot]; rewrite (EE 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sd_reg HS (Z_to_bv 5 18) (YK11.getr regs2 (Z_to_bv 5 18)) T18
    ltac:(cbn [sv_denot]; rewrite (EE 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sd_reg HS (Z_to_bv 5 26) (YK11.getr regs2 (Z_to_bv 5 26)) T26
    ltac:(cbn [sv_denot]; rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sd_reg HS (Z_to_bv 5 27) (YK11.getr regs2 (Z_to_bv 5 27)) T27
    ltac:(cbn [sv_denot]; rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sd_reg HS (Z_to_bv 5 21) (w64 SD_TXF) T21
    ltac:(cbn [sv_denot]; rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64, SD_TXF, SENDDATA_S, TB_g_s;
          rewrite unsigned_lit_small by lia; reflexivity).
  sd_reg HS (Z_to_bv 5 20) (w64 SHADOW_OFF) T20
    ltac:(cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), R20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  assert (P4t : 0 <= TI.ti_io_send timg_B < 2 ^ 64)
    by (rewrite <- (proj1 sd_io_at); vm_compute; split; [discriminate | reflexivity]).
  assert (P5t : TI.ti_io_send timg_B mod 2 = 0) by (rewrite <- (proj1 sd_io_at); vm_compute; reflexivity).
  eapply (SRr_jalr_call_pi (PL := PL_transportb) (PI := PI_transportb) W2 E _ _ _ _ 0x680e7 (1%bv : bv 5)
    (13%bv : bv 5) (TI.ti_io_send timg_B) HEI HS eq_refl);
    [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact T13 | exact P4t | exact P5t |].
  intros matC ms1 Ems1 _. subst ms1.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    set (regsC := rg); set (mdC := mdx);
    change (SRr segs Wx (@cfg_at fx segs (TI.ti_io_send timg_B) regsC (ms_mem ms) mdC) Qx) end.
  assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + SD_RET2))
    by (unfold regsC; rewrite YK11.getr_same by (intros Hc; apply (f_equal bv_unsigned) in Hc;
        vm_compute in Hc; discriminate Hc); reflexivity).
  assert (RCK : forall rr : bv 5, bv_unsigned rr <> 1 -> YK11.getr regsC rr = YK11.getr (ms_regs ms) rr)
    by (intros rr Hr; unfold regsC; apply YK11.getr_other; intros Eq; apply Hr; rewrite Eq; reflexivity).
  assert (RC2 : YK11.getr regsC 2%bv = w64 sp1) by (rewrite RCK by (vm_compute; discriminate); exact T2).
  assert (RC3 : YK11.getr regsC 3%bv = w64 (as_gp B)) by (rewrite RCK by (vm_compute; discriminate); exact T3).
  assert (RC4 : YK11.getr regsC 4%bv = w64 (as_tp B)) by (rewrite RCK by (vm_compute; discriminate); exact T4).
  assert (RC11 : YK11.getr regsC 11%bv = w64 (SENDDATA_S + 216))
    by (rewrite RCK by (vm_compute; discriminate); exact T11).
  assert (RC12 : YK11.getr regsC 12%bv = w64 nn) by (rewrite RCK by (vm_compute; discriminate); exact T12).
  assert (USPC : spZ regsC = sp1) by (unfold spZ; rewrite RC2; unfold w64; apply unsigned_lit_small; lia).
  assert (EBN : 0 <= BASE + SD_RET2 < 2 ^ 40) by (vm_compute; split; [discriminate | reflexivity]).
  (* the premises of io_send's contract *)
  assert (HFRE : sd_fr Bw ncmds body now = TW.sub (sd_B8' X nn now) 1864 (Z.to_nat nn))
    by (unfold sd_fr; rewrite sdm_B8_eq, sdm_o_frame; reflexivity).
  assert (HGARR : garr8 segs (mrestrict (w_H W2) (ms_mem ms)) (SENDDATA_S + 216)
      (map DSpec.bz (sd_fr Bw ncmds body now))).
  { rewrite HFRE.
    exact (tw_garr8 segs (mrestrict (w_H W2) (ms_mem ms)) TMAP_B (sd_B8' X nn now) TW.OFF_g_s TB_g_s TW.SZ_g_s
      216 (Z.to_nat nn) TMAP_B_ok HTWC TMAP_B_g_s ltac:(lia) ltac:(change TW.SZ_g_s with 18264; lia)). }
  assert (HRDOK : decode_rd_ok W2 (ms_mem ms) (SENDDATA_S + 216) nn).
  { split; [|split; [|split; [|split; [|split]]]].
    - intros a Ha. apply sd_gs_vis. unfold SENDDATA_S, TB_g_s in *. lia.
    - intros x Hx. apply (sd_ra ly2 S2 W2 (ms_mem ms) mdc1 HSC HARC). unfold SENDDATA_S, TB_g_s in *. lia.
    - apply (sd_hull ly2 S2 W2 (ms_mem ms) mdc1 (SENDDATA_S + 216) nn HSC HARC);
        unfold SENDDATA_S, TB_g_s; lia.
    - unfold amem_range, kLowMemEnd. unfold SENDDATA_S, TB_g_s in *. lia.
    - unfold SENDDATA_S, TB_g_s. lia.
    - unfold SENDDATA_S, TB_g_s. lia. }
  assert (HSRC2 : trans_src_ok B ly2 S2 W2 (ms_mem ms) (SENDDATA_S + 216) nn).
  { apply (trans_src_ok_G_range B ly2 S2 W2 (ms_mem ms) (SENDDATA_S + 216) nn TB_g_s TW.SZ_g_s
      (TMAP_B_in_G _ _ _ TMAP_B_g_s) ltac:(unfold SENDDATA_S, TB_g_s; lia)
      ltac:(change TW.SZ_g_s with 18264; unfold SENDDATA_S, TB_g_s; lia));
      [|exact HRDOK].
    apply (trans_sh_any_zshadow B SENDDATA_S (SENDDATA_S + 18264)); [exact HSC | lia | |];
      unfold SENDDATA_S, TB_g_s; Z.div_mod_to_equations; lia. }
  assert (HROMC : trans_rom_view_rd W2 (ms_mem ms)).
  { intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Hb.
    rewrite (KR1 a ltac:(lia) ltac:(unfold sd_Z1, SENDDATA_S, TB_g_s; lia)). exact (HROM2 a Ha). }
  assert (HGF8 : TW.g_fail_next (sd_B8' X nn now) <= 1)
    by (rewrite K8gf, K2gf, K1gf; exact Hgf0).
  eapply SRr_bind.
  { exact (IOS0 fx STK sp0 FP ly S W0 mem0 md0 ((SENDDATA_CID, pos) :: own) ly2 S2 W2 (ms_mem ms) mdC (k + 0)
      regsC (SENDDATA_S + 216) r0 (sd_fr Bw ncmds body now) (sd_B8' X nn now) B9
      ltac:(apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJ)
      ltac:(rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transportb));
            [vm_compute; split; [discriminate | reflexivity] | reflexivity])
      ltac:(unfold raZ; rewrite RC1; rewrite unsigned_lit_small by lia; vm_compute; discriminate)
      RC3 RC4 RC11
      ltac:(rewrite RC12, HFRLEN; reflexivity)
      ltac:(rewrite USPC; exact Hsp1m) ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
      ltac:(unfold SENDDATA_S, TB_g_s; lia)
      HGARR
      ltac:(rewrite HFRLEN; exact HSRC2)
      ltac:(unfold decode_off_win; rewrite USPC, HFRLEN; left; unfold SENDDATA_S, TB_g_s in *; lia)
      ltac:(unfold iosend_frame_at; right; rewrite HFRLEN; split;
            [unfold SENDDATA_S, TB_g_s; lia | change TW.SZ_g_s with 18264; unfold SENDDATA_S, TB_g_s; lia])
      HGF8 HROMC HTWC HIO
      ltac:(rewrite K8fo, K8fl, K2fo, K2fl, K1fo, K1fl; exact HINV1)
      ltac:(intros sx Hsx Hst; rewrite K8cln, K2cln, K1cln by lia; apply HINV4;
            [rewrite <- K1nc, <- K2nc, <- K8nc; exact Hsx
            | rewrite <- K1cst, <- K2cst, <- K8cst by lia; exact Hst])
      ltac:(unfold IOSEND_EV; lia)). }
  intros W3 c3 _ HPOST.
  unfold transport_io_send_post, transport_cg_post in HPOST. cbv beta in HPOST.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3
    & HX10 & HTW3).
  assert (He30 : e3 = 0) by (unfold IOSEND_EV in He3; lia). subst e3.
  replace (k + 0 + 0) with (k + 0) in HJ3 by lia.
  (* what the call state and the callee's return leave *)
  pose proof HK3 as (K31 & K32 & K33 & K34 & K35 & K36).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
  pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
  clear HJi3 memS3.
  pose proof HJ as (_ & _ & (memS2 & HJi2 & _) & _). rewrite !Z.add_0_r in HJi2.
  pose proof HJi2 as (_ & Hlyle2 & _). pose proof Hlyle2 as (_ & _ & _ & _ & _ & ELF2 & _).
  clear HJi2 memS2.
  assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, <- ELF2; exact ELF).
  assert (Hfrs3 : frames S3 = (SENDDATA_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
  assert (Hperm3c : Permutation (ablocks B ly3 S3) (ablocks B lyc Sc))
    by (apply (Permutation_trans Hperm3); exact Hperm).
  assert (Hbl3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3))
    by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm3c) Hbm)).
  assert (Hmo3c : mo_le MT Sc S3 0) by (exact (mo_le_trans MT MTL Sc S2 S3 0 0 Hmo Hmo3)).
  (* the caller's memory kept, from the cut to the callee's return *)
  assert (KCrun : acall_kept_g segs B TGx.G_HARNESS_B lyc Sc W memc W2 (ms_mem ms)
      (spZ regs - SENDDATA_STK) (spZ regs) senddata_wr)
    by (exact (sd_keep_step lyc Sc W memc mdc W2 mem2 (ms_mem ms) (spZ regs - SENDDATA_STK) (spZ regs)
         senddata_wr sd_Z1 LAWS HGX HARc sd_Z1_G HK KR1 GA1)).
  assert (HFIN : forall kk, 0 <= kk < 8 ->
      dkg_nf SENDDATA_CID F (flag_addr lyc SENDDATA_CID pos) (F + SENDDATA_FBYTES - 8 + kk))
    by (intros kk Hk; unfold dkg_nf; left; change (fs_frame_bytes SENDDATA_CID) with 64;
        unfold SENDDATA_FBYTES in *; lia).
  assert (HNZ1 : forall a, dkg_nf SENDDATA_CID F (flag_addr lyc SENDDATA_CID pos) a -> ~ sd_Z1 a)
    by (intros a Ha Hz; apply (N2 a Ha); destruct (HGX _ (sd_Z1_G _ Hz)) as [Hi _]; exact Hi).
  assert (HNZ2 : forall a, dkg_nf SENDDATA_CID F (flag_addr lyc SENDDATA_CID pos) a -> ~ sd_Z2 a)
    by (intros a Ha Hz; apply (N2 a Ha); destruct (HGX _ (sd_Z2_G _ Hz)) as [Hi _]; exact Hi).
  assert (HNIOW : forall a, dkg_nf SENDDATA_CID F (flag_addr lyc SENDDATA_CID pos) a ->
      ~ iosend_wr (Z.of_nat (length (sd_fr Bw ncmds body now))) a).
  { intros a Ha Hw. apply (N2 a Ha).
    destruct (HGX a (sd_iosend_inG _ a ltac:(apply Zle_0_nat) Hw)) as [Hi _]. exact Hi. }
  assert (KC3 : acall_kept_g segs B TGx.G_HARNESS_B lyc Sc W memc W3 mem3
      (spZ regs - SENDDATA_STK) (spZ regs) senddata_wr).
  { apply (dk_kept_trans_nf_g segs B TGx.G_HARNESS_B lyc Sc ly2 S2 W memc W2 (ms_mem ms) W3 mem3
      (spZ regs - SENDDATA_STK) (spZ regs) (spZ regsC - IOSEND_STK) (spZ regsC) senddata_wr
      (iosend_wr (Z.of_nat (length (sd_fr Bw ncmds body now))))
      (dkg_nf SENDDATA_CID F (flag_addr lyc SENDDATA_CID pos))).
    - lia.
    - lia.
    - intros c p. unfold frame_addr. rewrite ELF. reflexivity.
    - intros f Hf. rewrite Hfrs. right. exact Hf.
    - exact Hbl.
    - exact N1.
    - exact N3.
    - exact KCrun.
    - exact HK3.
    - rewrite USPC. lia.
    - rewrite USPC. lia.
    - intros a Ha. left. exact (sd_iosend_wr_sub _ a Ha). }
  (* the 13 saved words and the frame's flag word at the callee's return *)
  assert (KSV3 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - IOSEND_STK <= a < sp1) ->
      aview segs (w_H W3) mem3 a = aview segs (w_H W2) (ms_mem ms) a)
    by (rewrite <- USPC; exact K31).
  assert (HSAV3 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem3) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SD_SAVED).
  { apply Forall_forall. intros o Ho.
    assert (Hb : 8 <= fst o <= 104)
      by (unfold SD_SAVED in Ho; cbn [In] in Ho;
          repeat (destruct Ho as [<-|Ho]; [cbn [fst]; lia|]); destruct Ho).
    rewrite (rdword_ext (aview segs (w_H W2) (ms_mem ms)) (aview segs (w_H W3) mem3))
      by (intros kk Hk; apply KSV3; lia).
    rewrite (rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem ms)))
      by (intros kk Hk; apply KR1; [lia | unfold sd_Z1, SENDDATA_S, TB_g_s; lia]).
    exact (proj1 (Forall_forall _ _) Hsaved o Ho). }
  assert (HFLw3 : rdword (aview segs (w_H W3) mem3) (F + SENDDATA_FBYTES - 8) =
      Some (flag_addr lyc SENDDATA_CID pos)).
  { rewrite (rdword_ext (aview segs (w_H W2) (ms_mem ms)) (aview segs (w_H W3) mem3)).
    - rewrite (rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem ms)))
        by (intros kk Hk; apply KR1; [unfold SENDDATA_FBYTES in *; lia | exact (HNZ1 _ (HFIN kk Hk))]).
      exact HFLw.
    - intros kk Hk. apply (K34 SENDDATA_CID pos (F + SENDDATA_FBYTES - 8 + kk)).
      + rewrite Hfrs. left. reflexivity.
      + left. unfold in_zr, frame_rng. cbn [fst snd].
        replace (frame_addr ly2 SENDDATA_CID pos) with F
          by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
        change (fs_frame_bytes SENDDATA_CID) with 64. unfold SENDDATA_FBYTES in *. lia.
      + exact (HNIOW _ (HFIN kk Hk)). }
  (* the registers at the return *)
  assert (RF3 : forall rr : Z, acallee_saved rr -> YK11.getr regs3 (Z_to_bv 5 rr) = YK11.getr regsC (Z_to_bv 5 rr))
    by exact HP3.
  assert (G3 : YK11.getr regs3 3%bv = YK11.getr regs 3%bv).
  { transitivity (YK11.getr regsC 3%bv); [exact (RF3 3 ltac:(hnf; lia))|].
    rewrite RCK by (vm_compute; discriminate). exact (eq_trans T3 (eq_sym Hgp)). }
  assert (G4 : YK11.getr regs3 4%bv = YK11.getr regs 4%bv).
  { transitivity (YK11.getr regsC 4%bv); [exact (RF3 4 ltac:(hnf; lia))|].
    rewrite RCK by (vm_compute; discriminate). exact (eq_trans T4 (eq_sym Htp)). }
  assert (G8 : YK11.getr regs3 8%bv = w64 (spZ regs)).
  { transitivity (YK11.getr regsC 8%bv); [exact (RF3 8 ltac:(hnf; lia))|].
    rewrite RCK by (vm_compute; discriminate). exact (eq_trans T8 R8). }
  assert (G18 : YK11.getr regs3 18%bv = w64 F).
  { transitivity (YK11.getr regsC 18%bv); [exact (RF3 18 ltac:(hnf; lia))|].
    rewrite RCK by (vm_compute; discriminate). exact (eq_trans T18 R18). }
  assert (G26 : YK11.getr regs3 26%bv = w64 F).
  { transitivity (YK11.getr regsC 26%bv); [exact (RF3 26 ltac:(hnf; lia))|].
    rewrite RCK by (vm_compute; discriminate). exact (eq_trans T26 R26). }
  assert (G27 : YK11.getr regs3 27%bv = w64 (SHADOW_OFF + F / 8)).
  { transitivity (YK11.getr regsC 27%bv); [exact (RF3 27 ltac:(hnf; lia))|].
    rewrite RCK by (vm_compute; discriminate). exact (eq_trans T27 R27). }
  assert (G20 : YK11.getr regs3 20%bv = w64 SHADOW_OFF).
  { transitivity (YK11.getr regsC 20%bv); [exact (RF3 20 ltac:(hnf; lia))|].
    rewrite RCK by (vm_compute; discriminate). exact T20. }
  assert (G21 : YK11.getr regs3 21%bv = w64 SD_TXF).
  { transitivity (YK11.getr regsC 21%bv); [exact (RF3 21 ltac:(hnf; lia))|].
    rewrite RCK by (vm_compute; discriminate). exact T21. }
  rewrite RC1.
  pose proof (sdm_io_ret (sd_B8' X nn now) (sd_fr Bw ncmds body now) B9 r0 HIO) as HR0.
  destruct HCASE as [(Hr00 & HBw' & Hrr) | (Hr0n & HBw' & Hrr)].
  + (* -------- io_send answered 0: the read-modify-write of stats.tx_frames -------- *)
    subst r0. subst r.
    assert (HLB9 : Z.of_nat (length B9) = 65616)
      by (rewrite (tw_len TMAP_B _ B9 HTW3); rewrite Z2Nat.id by (unfold TW.W_LEN; lia); reflexivity).
    destruct (sdm_txf B9 HLB9) as (ETXF & EGFN9 & ELN9).
    destruct (sd_entry2 ly3 S3 W3 regs3 mem3 md3 B9 HSC HAR3 HTW3 G20 G21 HX10) as [HS2 SHOK2].
    set (E2v := sd_E2 regs3 B9) in HS2, SHOK2.
    assert (HEI2 : img_env VAL A_LIM E2v) by (unfold E2v, sd_E2; apply Eimg_env).
    assert (EE2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E2v n = YK11.getr regs3 rr)
      by (intros n rr Hn; unfold E2v, sd_E2; apply ew_Eimg_Ereg_nat; exact Hn).
    assert (U21b : bv_unsigned (ew E2v 21) = SD_TXF)
      by (rewrite (EE2 21%nat 21%bv eq_refl), G21; unfold w64; apply unsigned_lit_small;
          unfold SD_TXF, SENDDATA_S, TB_g_s; lia).
    assert (E32b : ew E2v 32 = w64 (TW.u_at B9 19840 8))
      by (unfold E2v, sd_E2; rewrite Eimg_low by (unfold A_TEXT; lia);
          exact (ew_Ereg_extra regs3 [w64 (TW.u_at B9 19840 8)] 0)).
    paj_run_to_tok RUNTO HS2 HJ3 SHOK2 YC4b.Bspan SD_REL.
    { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
        let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
      apply awr_ok_x_cons_g;
      [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U21b in Ha;
        apply sd_inG_gs; change TW.SZ_g_s with 18264; unfold SD_TXF, SENDDATA_S, TB_g_s in *; lia |].
      apply awr_ok_x_nil. }
    set (mdF := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdF. clear mat.
    assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ sd_Z2 a ->
      aview segs (w_H W3) (ms_mem ms0) a = aview segs (w_H W3) mem3 a).
    { intros a Ha Hn.
      apply (kept_of_frame (segs := segs) E2v [sd_rg_txf] (w_H W3) mem3 (ms_mem ms0) sd_Z2 HFr0);
        [|exact Ha|exact Hn].
      intros b wlo whi x Hin Hx. cbv beta.
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
      cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U21b in Hx;
         unfold sd_Z2, SD_TXF, SENDDATA_S, TB_g_s in *; lia|]).
      destruct Hin. }
    assert (GA2 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms0) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG0 Ha)).
    pose proof (st_ok_pi_region_nth E2v _ (restrict (w_H W3) ms0) 0 _ HS2 eq_refl) as RGf.
    cbn [ms_mem restrict] in RGf. destruct RGf as (_ & _ & _ & HCf).
    cbn [base_val YP09.r_base YP09.r_chunks] in HCf.
    assert (VF : val_mem segs (mrestrict (w_H W3) (ms_mem ms0)) (SENDDATA_S + 18192) 8
        ((TW.u_at B9 19840 8 + 1) mod 2 ^ 64)).
    { replace (SENDDATA_S + 18192) with (bv_unsigned (ew E2v 21) + 0) by (rewrite U21b; unfold SD_TXF; lia).
      pose proof (val_mem_low_of_chunk segs E2v (mrestrict (w_H W3) (ms_mem ms0)) (bv_unsigned (ew E2v 21))
        0 8%N (SOff 32 1) (proj1 (Forall_forall _ _) HCf _ ltac:(cbn [In]; auto)) ltac:(cbn; lia)) as HV.
      cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N] in HV. change (8 * 8) with 64 in HV.
      cbn [sv_denot] in HV. rewrite E32b in HV. unfold w64 in HV.
      pose proof (TWL.u_at_range B9 19840 8) as HRB. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in HRB.
      rewrite !MState.unsigned_lit_wrap in HV.
      rewrite (Z.mod_small (TW.u_at B9 19840 8) (2 ^ 64)) in HV by lia.
      rewrite Zmod_mod in HV. exact HV. }
    assert (HTWF : tw_at TMAP_B (aview segs (w_H W3) (ms_mem ms0)) Bw').
    { rewrite HBw', <- ETXF.
      replace (TW.put 8 (TW.u_at B9 19840 8 + 1)) with (TW.put 8 ((TW.u_at B9 19840 8 + 1) mod 2 ^ 64))
        by (apply TWL.put_mod64; lia).
      exact (sd_world1 W3 mem3 (ms_mem ms0) B9 _ HTW3 KR2 VF). }
    assert (HPF2 : aregs_preserved regs3 (ms_regs ms0)).
    { apply (aregs_preserved_of_st_ok segs (w_H W3) E2v _ ms0 regs3 [w64 (TW.u_at B9 19840 8)] HS2);
        [ split; [intros nj Hn; unfold E2v, sd_E2; apply Eimg_low; unfold A_TEXT; lia | reflexivity]
        | vm_compute; reflexivity ]. }
    sd_reg HS2 (Z_to_bv 5 12) (w64 0) RF12b ltac:(reflexivity).
    pmkst HS2.
    refine (REL LAWSc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bodyp ncmds now 0 body TF Bw Bw'
      pos sp1 F ly3 S3 W3 (ms_mem ms0) mdF 0 (ms_regs ms0) HFIXc _ _).
    * split; [|split].
      -- split; [exact HJ3|].
         split; [unfold SENDDATA_EV, FRAME_FB_EV, IOSEND_EV; lia|].
         split; [exact Hfrs3|]. split; [exact Hperm3c|]. split; [exact ELF3c|]. split; [exact Hmo3c|].
         split.
         { exact (sd_keep_step lyc Sc W memc mdc W3 mem3 (ms_mem ms0) (spZ regs - SENDDATA_STK) (spZ regs)
             senddata_wr sd_Z2 LAWS HGX HARc sd_Z2_G KC3 KR2 GA2). }
         split.
         { apply Forall_forall. intros o Ho.
           assert (Hb : 8 <= fst o <= 104)
             by (unfold SD_SAVED in Ho; cbn [In] in Ho;
                 repeat (destruct Ho as [<-|Ho]; [cbn [fst]; lia|]); destruct Ho).
           rewrite (rdword_ext (aview segs (w_H W3) mem3) (aview segs (w_H W3) (ms_mem ms0)))
             by (intros kk Hk; apply KR2; [lia | unfold sd_Z2, SENDDATA_S, TB_g_s; lia]).
           exact (proj1 (Forall_forall _ _) HSAV3 o Ho). }
         { rewrite (rdword_ext (aview segs (w_H W3) mem3) (aview segs (w_H W3) (ms_mem ms0)))
             by (intros kk Hk; apply KR2;
                 [unfold SENDDATA_FBYTES in *; lia | exact (HNZ2 _ (HFIN kk Hk))]).
           exact HFLw3. }
      -- exact HTWF.
      -- rewrite HBw', EGFN9.
         rewrite (sdm_io_gfn (sd_B8' X nn now) (sd_fr Bw ncmds body now) B9 0 HIO
           ltac:(apply sdm_len_B8; [exact HLX | exact HNN])). lia.
    * split.
      -- unfold sd_regs_keep.
         split; [transitivity (YK11.getr regs3 3); [exact (HPF2 3 ltac:(hnf; lia)) | exact G3]|].
         split; [transitivity (YK11.getr regs3 4); [exact (HPF2 4 ltac:(hnf; lia)) | exact G4]|].
         split; [transitivity (YK11.getr regs3 8); [exact (HPF2 8 ltac:(hnf; lia)) | exact G8]|].
         split; [transitivity (YK11.getr regs3 18); [exact (HPF2 18 ltac:(hnf; lia)) | exact G18]|].
         split; [transitivity (YK11.getr regs3 26); [exact (HPF2 26 ltac:(hnf; lia)) | exact G26]|].
         transitivity (YK11.getr regs3 27); [exact (HPF2 27 ltac:(hnf; lia)) | exact G27].
      -- exact RF12b.
  + (* -------- io_send answered -EIO: straight to the release -------- *)
    subst Bw'. subst r.
    assert (HCC2 : branch_taken (ac_c (mkAC BC_NE (SOff 10 0) (SLit 0)))
        (sv_denot (sd_E0 regs3) (ac_a (mkAC BC_NE (SOff 10 0) (SLit 0))))
        (sv_denot (sd_E0 regs3) (ac_b (mkAC BC_NE (SOff 10 0) (SLit 0)))) = true).
    { cbn [ac_c ac_a ac_b].
      assert (D10b : sv_denot (sd_E0 regs3) (SOff 10 0) = w64 r0)
        by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
            unfold sd_E0; rewrite (ew_Eimg_Ereg_nat regs3 [] 10%nat 10%bv eq_refl); exact HX10).
      rewrite D10b. cbn [branch_taken sv_denot]. unfold w64.
      rewrite (sdm_eqb0 r0 ltac:(lia)). apply negb_true_iff. apply Z.eqb_neq. exact Hr0n. }
    pose proof (sd_entry_nr W3 regs3 mem3 SD_RET2 (mkAC BC_NE (SOff 10 0) (SLit 0)) HCC2) as HS2.
    set (E2v := sd_E0 regs3) in HS2.
    assert (HEI2 : img_env VAL A_LIM E2v) by (unfold E2v, sd_E0; apply Eimg_env).
    assert (SHOK2 : sh_ok segs SD_Bx (@nil shent) E2v (mrestrict (w_H W3) mem3)) by (apply Forall_nil).
    paj_run_to_tok RUNTO HS2 HJ3 SHOK2 YC4b.Bspan SD_REL.
    { apply awr_ok_x_nil. }
    set (mdF := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdF. clear mat.
    assert (KR2 : forall a, 0 <= a < 2 ^ 64 ->
      aview segs (w_H W3) (ms_mem ms0) a = aview segs (w_H W3) mem3 a).
    { intros a Ha.
      apply (kept_of_frame (segs := segs) E2v [] (w_H W3) mem3 (ms_mem ms0) (fun _ => False) HFr0);
        [intros b wlo whi x Hin Hx; cbn [windows map In] in Hin; destruct Hin | exact Ha | intros []]. }
    assert (GA2 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms0) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG0 Ha)).
    assert (HPF2 : aregs_preserved regs3 (ms_regs ms0)).
    { apply (aregs_preserved_of_st_ok segs (w_H W3) E2v _ ms0 regs3 [] HS2);
        [ split; [intros nj Hn; unfold E2v, sd_E0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]
        | vm_compute; reflexivity ]. }
    sd_reg HS2 (Z_to_bv 5 12) (w64 r0) RF12b
      ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
            unfold E2v, sd_E0; rewrite (ew_Eimg_Ereg_nat regs3 [] 10%nat 10%bv eq_refl); exact HX10).
    pmkst HS2.
    refine (REL LAWSc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bodyp ncmds now r0 body TF Bw B9
      pos sp1 F ly3 S3 W3 (ms_mem ms0) mdF 0 (ms_regs ms0) HFIXc _ _).
    * split; [|split].
      -- split; [exact HJ3|].
         split; [unfold SENDDATA_EV, FRAME_FB_EV, IOSEND_EV; lia|].
         split; [exact Hfrs3|]. split; [exact Hperm3c|]. split; [exact ELF3c|]. split; [exact Hmo3c|].
         split.
         { exact (sd_keep_step lyc Sc W memc mdc W3 mem3 (ms_mem ms0) (spZ regs - SENDDATA_STK) (spZ regs)
             senddata_wr (fun _ => False) LAWS HGX HARc ltac:(intros a []) KC3
             ltac:(intros a Ha _; exact (KR2 a Ha)) GA2). }
         split.
         { apply Forall_forall. intros o Ho.
           assert (Hb : 8 <= fst o <= 104)
             by (unfold SD_SAVED in Ho; cbn [In] in Ho;
                 repeat (destruct Ho as [<-|Ho]; [cbn [fst]; lia|]); destruct Ho).
           rewrite (rdword_ext (aview segs (w_H W3) mem3) (aview segs (w_H W3) (ms_mem ms0)))
             by (intros kk Hk; apply KR2; lia).
           exact (proj1 (Forall_forall _ _) HSAV3 o Ho). }
         { rewrite (rdword_ext (aview segs (w_H W3) mem3) (aview segs (w_H W3) (ms_mem ms0)))
             by (intros kk Hk; apply KR2; unfold SENDDATA_FBYTES in *; lia).
           exact HFLw3. }
      -- apply (tw_kept TMAP_B (aview segs (w_H W3) mem3)); [exact HTW3|].
         intros x Hx. apply KR2. pose proof (TMAP_B_hull x Hx) as Hh.
         unfold TGx.G_HARNESS_B_LO, TGx.G_HARNESS_B_HI in Hh. lia.
      -- rewrite (sdm_io_gfn (sd_B8' X nn now) (sd_fr Bw ncmds body now) B9 r0 HIO
           ltac:(apply sdm_len_B8; [exact HLX | exact HNN])). lia.
    * split.
      -- unfold sd_regs_keep.
         split; [transitivity (YK11.getr regs3 3); [exact (HPF2 3 ltac:(hnf; lia)) | exact G3]|].
         split; [transitivity (YK11.getr regs3 4); [exact (HPF2 4 ltac:(hnf; lia)) | exact G4]|].
         split; [transitivity (YK11.getr regs3 8); [exact (HPF2 8 ltac:(hnf; lia)) | exact G8]|].
         split; [transitivity (YK11.getr regs3 18); [exact (HPF2 18 ltac:(hnf; lia)) | exact G18]|].
         split; [transitivity (YK11.getr regs3 26); [exact (HPF2 26 ltac:(hnf; lia)) | exact G26]|].
         transitivity (YK11.getr regs3 27); [exact (HPF2 27 ltac:(hnf; lia)) | exact G27].
      -- exact RF12b.
Qed.

End mid.

Print Assumptions sd_mid.
