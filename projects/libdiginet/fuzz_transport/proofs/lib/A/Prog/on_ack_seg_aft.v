(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 300 of its 340 lines of code are new or changed and 1884 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_ack_seg_rel.v, with its module names changed; 786 of its 855 lines of code are new or changed and 271 lines of the source are left out. *)
(* on_ack_seg_aft: Lemma onack_aft_piece : onack_aft_stmt (lib/A/Prog/on_ack_segs.v), the after-notice piece of the
   image-A walk of on_ack, offsets +0x24c .. +0x2ac of the listing lib/A/Prog/DgnTransportList.v (fuzz_transport.asan
   0x88678 .. 0x886d8), then the release cut +0x2d8, which the onack_rel_at it is given closes.

   What the code does (:233-236). +0x24c `lb a0, 0(s11)`, +0x250 `bnez a0`: the check of the load at s + 112 (its
   shadow byte is 0: g_s's payload lies in the record's zero shadow, on_ack_cg.v trans_onack_cells, read by
   DgnTransportCg.v decode_zshadow_rd); +0x254 `lw a0, 0(s6)`: S_state of notice's world B2, sign-extended;
   +0x258 `li a1, 1`; +0x25c `bne a0, a1, +0x284`.
     The state is not S_WAKING: the branch goes to the shadow join +0x284; the model's world is B2
       (on_ack_segs.v onack_model_ntc), the world the cut's memory relates to.
     The state is S_WAKING: +0x260 .. +0x270 the check of the store at s + 144 (a computed shadow address, the shadow
       token of the run), +0x274 / +0x278 the store of 1 at s + 144 (:234; the world is set_S_wake_acked B2 1),
       +0x27c `mv a0, s3`, +0x280 `jal maybe_online` (return +0x284).
   +0x284 `li a0, -8` and nine `sb a0, i(s7)`: the frame's shadow bytes 4 .. 12 := 0xf8 (the notice out of scope);
   +0x2ac `j +0x2d8`.

   Four runs of the engine over the caller's G journal (lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x):
     run A (+0x24c .. the `bne`, no shadow token): two read-only regions, s11's shadow byte (value 0) and S_state's
       four bytes at s6 (atom 32, by TWorldG.v tw_read_val at B2); the run stops at the `bne`, which
       DgnTransportPaLib.v paj_branch splits on the model's test S_state B2 =? S_WAKING (oaf_sext, oaf_eqb1); each
       arm runs the one instruction to +0x284 or +0x260 and writes no byte;
     run B (+0x260 .. the `jal`, shadow token): g_s.wake_acked at s3, written (bytes of G); the shadow entry of
       [s + 144, s + 148);
     run C (+0x284 .. the release cut, no shadow token, oaf_tail): the frame's shadow bytes 4 .. 12 at s7, written
       (bytes of the own frame's shadow, TransportGCg.v dkg_nf).
   maybe_online: maybe_online_cg.v transport_maybe_online_cg at transport_sigma TS_maybe_online (a premise of
   onack_aft_at), in the same G journal: the journal at the call (the own frame owned); ra = +0x284; gp, tp kept;
   a0 = s; sp = sp1 (32-aligned, sp1 >= sp - 144 and ONACK_STK = 144 + MAYBEON_STK); tw_at at set_S_wake_acked B2 1
   (TWorldG.v tw_write of the store); g_fail_next (on_ack_seg_wld.v onack_wake_fail); the model premise (oaf_model);
   trans_tframe_at TF at MAYBEON_STK (the cut's, carried over run B: TF's bytes miss s + 144 by onack_apart, the
   shadow band is kept, DgnTransportCg.v trans_src_ok_view, and the window shrinks); trans_rom_view_rd (no
   TRANS_RO_RD byte is s + 144); maybeon_apart (onack_apart through oaf_wr_sub: the range maybe_online writes at
   set_S_wake_acked B2 1 is the one onack_wr names at set_S_wake_acked (onack_w1 Bw) 1, since notice's store of
   GOT.acked keeps every field that range reads, oaf_mwr_cong); the count of class-2 frames (the own frame on top
   of the caller's); no event.
   The release cut's state: the journal, frames, blocks and meter of maybe_online's post; what the call keeps from the
   cut's acall_kept_g over run B (TransportGFrame.v dk_kept_step_gw: s + 144 is a byte of onack_wr) and then
   maybe_online's (TransportGCg.v dk_kept_trans_nf_g, its written range inside onack_wr); the saved words (above
   maybe_online's window) and the frame's last word (a frame byte, not a byte of G) kept; the world relation at Bw' and
   g_fail_next Bw' <= 1 from maybe_online's post. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AE2y AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import maybe_online_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame on_ack_segs on_ack_seg_wld.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.


(* ------------------------------------------------------------------ *)
(* 1. The model on this path, and the range maybe_online writes        *)
(* ------------------------------------------------------------------ *)

(* maybe_online's first store (g_s.next_keepalive_us, 8 bytes at OFF_g_s + 184) keeps the state and GOT.n. *)
Lemma oaf_nk_facts : forall (X : list byte) v, Z.of_nat (length X) = TW.W_LEN ->
  TW.S_state (TW.set_S_next_keepalive_us X v) = TW.S_state X /\
  TW.GOT_n (TW.set_S_next_keepalive_us X v) = TW.GOT_n X /\
  Z.of_nat (length (TW.set_S_next_keepalive_us X v)) = TW.W_LEN.
Proof.
intros X v HL. unfold TW.set_S_next_keepalive_us, TW.S_state, TW.GOT_n.
assert (HP : Z.of_nat (length (TW.put 8 v)) = 8) by (rewrite TWL.length_put; reflexivity).
split; [|split].
- rewrite TWL.s32_at_upd_out; [reflexivity | unfold TW.A_S_next_keepalive_us, TW.OFF_g_s; lia
   | unfold TW.A_S_state, TW.OFF_g_s; lia
   | rewrite HP; unfold TW.A_S_next_keepalive_us, TW.A_S_state, TW.OFF_g_s; lia
   | rewrite HP, HL; unfold TW.A_S_next_keepalive_us, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.s32_at_upd_out; [reflexivity | unfold TW.A_S_next_keepalive_us, TW.OFF_g_s; lia
   | unfold TW.A_GOT_n, TW.OFF_GOT; lia
   | rewrite HP; unfold TW.A_S_next_keepalive_us, TW.A_GOT_n, TW.OFF_g_s, TW.OFF_GOT; lia
   | rewrite HP, HL; unfold TW.A_S_next_keepalive_us, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.length_upd_put; [exact HL | unfold TW.A_S_next_keepalive_us, TW.OFF_g_s; lia
   | rewrite HL; unfold TW.A_S_next_keepalive_us, TW.OFF_g_s, TW.W_LEN; lia].
Qed.

(* maybe_online's store of the state (4 bytes at OFF_g_s + 112) keeps GOT.n. *)
Lemma oaf_st_gotn : forall (X : list byte) v, Z.of_nat (length X) = TW.W_LEN ->
  TW.GOT_n (TW.set_S_state X v) = TW.GOT_n X.
Proof.
intros X v HL. unfold TW.set_S_state, TW.GOT_n.
assert (HP : Z.of_nat (length (TW.put 4 v)) = 4) by (rewrite TWL.length_put; reflexivity).
rewrite TWL.s32_at_upd_out; [reflexivity | unfold TW.A_S_state, TW.OFF_g_s; lia
   | unfold TW.A_GOT_n, TW.OFF_GOT; lia
   | rewrite HP; unfold TW.A_S_state, TW.A_GOT_n, TW.OFF_g_s, TW.OFF_GOT; lia
   | rewrite HP, HL; unfold TW.A_S_state, TW.OFF_g_s, TW.W_LEN; lia].
Qed.

Lemma oaf_mw1_state : forall X, Z.of_nat (length X) = TW.W_LEN -> TW.S_state (maybeon_w1 X) = TW.S_state X.
Proof. intros X HL. unfold maybeon_w1. exact (proj1 (oaf_nk_facts X _ HL)). Qed.

Lemma oaf_mw2_gotn : forall X, Z.of_nat (length X) = TW.W_LEN -> TW.GOT_n (maybeon_w2 X) = TW.GOT_n X.
Proof.
intros X HL. unfold maybeon_w2, maybeon_w1.
destruct (oaf_nk_facts X (TS0.u64 (TW.S_last_rx_us X + TS0.ms_m (TW.S_cfg_keepalive_ms X))) HL) as (_ & E2 & L2).
rewrite (oaf_st_gotn _ _ L2). exact E2.
Qed.

(* The range maybe_online writes reads four fields of the world it is given: S_state, S_wake_acked, S_e1_named_us
   (its test of :178), S_state again through maybeon_w1 (the notice's old state) and GOT.n through maybeon_w2 (the
   notice's stores). Two worlds that agree there have the same written range. *)
Lemma oaf_mwr_cong : forall X1 X2, Z.of_nat (length X1) = TW.W_LEN -> Z.of_nat (length X2) = TW.W_LEN ->
  TW.S_state X1 = TW.S_state X2 -> TW.S_wake_acked X1 = TW.S_wake_acked X2 ->
  TW.S_e1_named_us X1 = TW.S_e1_named_us X2 -> TW.GOT_n X1 = TW.GOT_n X2 ->
  forall a, maybeon_wr X1 a -> maybeon_wr X2 a.
Proof.
intros X1 X2 L1 L2 E1 E2 E3 E6 a (Hgo & Hr).
split.
- unfold maybeon_go in *. rewrite <- E1, <- E2, <- E3. exact Hgo.
- destruct Hr as [Hr | (Hs & Hr)]; [left; exact Hr | right].
  assert (ES : TW.S_state (maybeon_w1 X2) = TW.S_state (maybeon_w1 X1))
    by (rewrite (oaf_mw1_state X1 L1), (oaf_mw1_state X2 L2); symmetry; exact E1).
  rewrite ES. split; [exact Hs|].
  destruct Hr as [Hr | Hr]; [left; exact Hr | right].
  assert (EN : maybeon_ntc X2 = maybeon_ntc X1) by (unfold maybeon_ntc; rewrite ES; reflexivity).
  assert (EG : TW.GOT_n (maybeon_w2 X2) = TW.GOT_n (maybeon_w2 X1))
    by (rewrite (oaf_mw2_gotn X1 L1), (oaf_mw2_gotn X2 L2); symmetry; exact E6).
  rewrite EN. unfold notice_wr in *. rewrite EG. exact Hr.
Qed.

(* The range maybe_online writes at the world this walk hands it (notice's world B2 with wake_acked set) is the one
   on_ack_cg.v onack_wr names (at onack_w1 Bw with wake_acked set): notice's N_ACKED store of GOT.acked changes none
   of the four fields. *)
Lemma oaf_wr_sub : forall I F Bw b B2, Z.of_nat (length Bw) = TW.W_LEN ->
  TSS.call_notify I F (onack_w1 Bw) (onack_ntc Bw b) = Some (B2, tt) ->
  forall a, maybeon_wr (TW.set_S_wake_acked B2 1) a -> onack_wr Bw b a.
Proof.
intros I F Bw b B2 HL HN a Ha.
destruct (onack_B2_eq I F Bw b B2 HN) as (g & EB2). subst B2.
destruct (onack_w1_facts Bw HL) as (_ & _ & _ & _ & _ & _ & L1).
destruct (onack_B2_facts (onack_w1 Bw) g L1) as (B1 & B2 & B3 & _ & _ & B6 & _ & LB).
destruct (onack_wake_facts (TW.set_GOT_acked (onack_w1 Bw) g) 1 LB) as (C1 & C2 & C3 & _ & _ & C6).
destruct (onack_wake_facts (onack_w1 Bw) 1 L1) as (D1 & D2 & D3 & _ & _ & D6).
destruct (onack_wake_fail (TW.set_GOT_acked (onack_w1 Bw) g) 1 LB) as (_ & LX1).
destruct (onack_wake_fail (onack_w1 Bw) 1 L1) as (_ & LX2).
right; right; right; right.
apply (oaf_mwr_cong _ _ LX1 LX2); [| | | | exact Ha].
- rewrite C1, D1. exact B1.
- rewrite C2, D2. reflexivity.
- rewrite C3, D3. exact B3.
- rewrite C6, D6. exact B6.
Qed.

(* The model on this path: notice answered B2; at the state S_WAKING the model's world is maybe_online's at B2
   with wake_acked set, at any other state it is B2. *)
Lemma oaf_model : forall I F Bw b B2 Bw', onack_ign Bw b = false ->
  TSS.on_ack_m I F Bw b = Some (Bw', tt) ->
  TSS.call_notify I F (onack_w1 Bw) (onack_ntc Bw b) = Some (B2, tt) ->
  (TW.S_state B2 = TS0.DIGINET_S_WAKING -> TSS.maybe_online_m I F (TW.set_S_wake_acked B2 1) = Some (Bw', tt)) /\
  (TW.S_state B2 <> TS0.DIGINET_S_WAKING -> Bw' = B2).
Proof.
intros I F Bw b B2 Bw' Hi Hm HN.
destruct (onack_model_ntc I F Bw b Bw' Hi Hm) as (B2' & HN' & Hc).
assert (E : B2' = B2) by exact (onack_some_inv _ _ (eq_trans (eq_sym HN') HN)).
subst B2'.
split; intros Hs.
- rewrite (proj2 (Z.eqb_eq _ _) Hs) in Hc. exact Hc.
- rewrite (proj2 (Z.eqb_neq _ _) Hs) in Hc. exact Hc.
Qed.

(* Every byte maybe_online stores is a byte of G. *)
Lemma oaf_mwr_G : forall Bw a, maybeon_wr Bw a -> inG TG.G_HARNESS a.
Proof.
intros Bw a (_ & [Ha | (_ & [Ha | Ha])]); [| | exact (TransportGNotice.notice_wr_G _ _ a Ha)];
  unfold twa_fld, TW.A_S_next_keepalive_us, TW.A_S_state, TW.OFF_g_s, TA_g_s in Ha;
  unfold inG, TG.G_HARNESS; apply Exists_exists; exists (6158784, 18264);
  (split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia]).
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma oaf_inG : forall a, ONACK_S <= a < ONACK_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df9c0, 18264). split.
- unfold TG.G_HARNESS. cbn [In]. tauto.
- unfold in_zr, ONACK_S, TA_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* The store of :234 at its numeral offset. *)
Lemma oaf_wake_eq : forall Bx, TW.set_S_wake_acked Bx 1 = TW.upd Bx (TW.OFF_g_s + 144) (TW.put 4 1).
Proof. intros Bx. reflexivity. Qed.

(* `bne a0, a1` with a0 the sign-extended state and a1 = 1: the model's S_state = S_WAKING test. *)
Lemma oaf_eqb1 : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 1) = (v =? 1).
Proof.
intros v Hv. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 1 (2 ^ 64)) by lia.
destruct (Z.eqb_spec v 1) as [-> | Hne]; [reflexivity|].
apply Z.eqb_neq. intros HH. apply Hne.
destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
- rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) in HH by lia. lia.
- rewrite (Z.mod_small v (2 ^ 64)) in HH by lia. exact HH.
Qed.

Lemma oaf_state_range : forall Bw, - 2 ^ 31 <= TW.S_state Bw < 2 ^ 31.
Proof.
intros Bw. pose proof (bv_swrap_in_range 32 (TW.u_at Bw TW.A_S_state 4) ltac:(discriminate)) as R.
change (bv_swrap 32 (TW.u_at Bw TW.A_S_state 4)) with (TW.S_state Bw) in R.
change (bv_half_modulus 32) with (2 ^ 31) in R. lia.
Qed.

(* The sign-extended 4-byte load of g_s's state is the model's S_state. *)
Lemma oaf_sext : forall E Bw, ew E 32 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 112) 4) ->
  sv_denot E (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.S_state Bw).
Proof.
intros E Bw H. pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 112) 4) as R. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.


(* ------------------------------------------------------------------ *)
(* 2. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* +0x260, the fall-through of `bne a0, a1` (the state S_WAKING), and +0x284, the shadow join. *)
Definition ONACK_WK : Z := AF_on_ack + 0x260.
Definition ONACK_JOIN : Z := AF_on_ack + 0x284.
(* No shadow token: the span (0, 0). *)
Definition oaf_B0 : Z * Z := (0, 0).
Definition OAF_Bx : sv := SOff 25 0.

(* Run A, +0x24c .. `bne a0, a1` at +0x25c: the shadow byte of s + 112 at s11 (atom 27, value 0), and S_state's
   4 bytes at s6 (atom 22; their value atom 32), both read only. *)
Definition oaf_rg_s11 : YP09.region := YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SLit 0))].
Definition oaf_rg_st : YP09.region := YP09.mkRegion (Some 22%nat) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 32 0))].
Definition ss_oafA : sstate := mkSS ONACK_AFT sr_atoms [oaf_rg_s11; oaf_rg_st] None (mkFacts [] [] []).
(* Run B, +0x260 .. `jal maybe_online` at +0x280: g_s.wake_acked at s3 (atom 19), written; s3 = s, s9 = the shadow
   base; the shadow entry of the check of the store ([s + 144, s + 148)). *)
Definition oaf_rg_wk : YP09.region := YP09.mkRegion (Some 19%nat) 144 148 144 148 [].
Definition oaf_factsB : facts :=
  mkFacts [(19%nat, mkAF ONACK_S ONACK_S 6); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_oafB : sstate := mkSS ONACK_WK sr_atoms [oaf_rg_wk] None oaf_factsB.
Definition OAF_SH : list shent := [mkSHE 19 144 148].
(* Run C, +0x284 .. +0x2ac, to the release cut: the frame's shadow bytes 4 .. 12 at s7 (atom 23), written. *)
Definition oaf_rg_sh7 : YP09.region := YP09.mkRegion (Some 23%nat) 4 13 4 13 [].
Definition oaf_factsC : facts := mkFacts [(23%nat, mkAF SHADOW_OFF (2 ^ 47) 0)] [] [].
Definition ss_oafC : sstate := mkSS ONACK_JOIN sr_atoms [oaf_rg_sh7] None oaf_factsC.

(* The register and region readers of a symbolic state, as lib/A/Prog/DgnTransportPaLib.v states them. *)
Ltac oaf_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* A register the run does not write, at the run's end, from the equation Q of its value at the run's start: the
   run's valuation agrees with the start valuation below atom 1024 (Elo), which reads the registers (EE). *)
Ltac oaf_kreg HS Elo EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    oaf_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (Elo n ltac:(lia)), (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
Ltac oaf_region HS i HR :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac oaf_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac oaf_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The windows a run's regions leave, as the frame_of of its end state reads them: every byte outside Zs kept. *)
Ltac oaf_kept HFr Zs U :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
  intros a Ha Hn; apply (kept_of_frame _ _ _ _ _ Zs HFr); [| exact Ha | exact Hn];
  let b0 := fresh "b0" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b0 wlo whi x Hin Hx; cbv beta;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U in Hx; lia |]);
  destruct Hin.

Section ent. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The runs' valuation: the 32 registers, then the extra atoms. *)
Definition oaf_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transport) (Ereg regs extra).

Lemma oaf_ew : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oaf_E regs extra) n = YK11.getr regs r.
Proof. intros regs extra n r Hn. unfold oaf_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma oaf_ew_x : forall regs extra j, (j < 8)%nat -> ew (oaf_E regs extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j Hj. unfold oaf_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

(* A granule of g_s's payload is addressable at every AR state: the record's zero shadow. *)
Lemma oaf_ra : forall ly S (W : world segs) mem md q,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  q mod 8 = 0 -> ONACK_S <= q -> q + 8 <= ONACK_S + TW.SZ_g_s ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 8.
Proof.
intros ly S W mem md q HZ HAR Hq8 Hq1 Hq2 x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
pose proof (Z.div_mod q 8 ltac:(lia)) as Q8. rewrite Hq8, Z.add_0_r in Q8.
assert (Hx8 : 8 * (x / 8) = q) by lia.
assert (Hz := decode_zshadow_rd B ly S W mem md ONACK_S (ONACK_S + TW.SZ_g_s) q HAR Hq8 Hq1 Hq2 HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr q); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite <- Hx8, Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* Run A's state at +0x24c holds of the machine state there. *)
Lemma oaf_entryA : forall ly S (W : world segs) regs mem md B2,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) B2 ->
  YK11.getr regs 22 = w64 (ONACK_S + 112) -> YK11.getr regs 27 = w64 (SHADOW_OFF + (ONACK_S + 112) / 8) ->
  st_ok_pi segs VAL (oaf_E regs [Z_to_bv 64 (TW.u_at B2 (TW.OFF_g_s + 112) 4)]) ss_oafA
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONACK_AFT)) mem (YK11.seg_rom segs))).
Proof.
intros ly S W regs mem md B2 HZ HAR Htw R22 R27.
set (E := oaf_E regs [Z_to_bv 64 (TW.u_at B2 (TW.OFF_g_s + 112) 4)]).
assert (CS : ONACK_S = 6158784) by reflexivity.
assert (E9 : SHADOW_OFF + (ONACK_S + 112) / 8 = 2148220742) by reflexivity.
rewrite E9 in R27.
assert (U22 : bv_unsigned (ew E 22) = ONACK_S + 112).
{ unfold E. rewrite (oaf_ew regs _ 22 22%bv eq_refl), R22. unfold w64. apply unsigned_lit_small. rewrite CS. lia. }
assert (U27 : bv_unsigned (ew E 27) = 2148220742).
{ unfold E. rewrite (oaf_ew regs _ 27 27%bv eq_refl), R27. unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at B2 (TW.OFF_g_s + 112) 4)) by exact (oaf_ew_x regs _ 0 ltac:(lia)).
assert (R32 : 0 <= TW.u_at B2 (TW.OFF_g_s + 112) 4 < 2 ^ 32) by exact (TWL.u_at_range B2 _ 4).
assert (U32 : bv_unsigned (ew E 32) = TW.u_at B2 (TW.OFF_g_s + 112) 4)
  by (rewrite E32; apply unsigned_lit_small; lia).
assert (Hs11 : aview segs (w_H W) mem 2148220742 = Some 0).
{ pose proof (decode_zshadow_rd B ly S W mem md ONACK_S (ONACK_S + TW.SZ_g_s) (ONACK_S + 112) HAR
    ltac:(rewrite CS; reflexivity) ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) HZ) as H.
  rewrite <- E9. replace (SHADOW_OFF + (ONACK_S + 112) / 8) with (DgnTransportCg.FCells.shadow_addr (ONACK_S + 112))
    by reflexivity. exact H. }
rewrite restrict_mkst_fx. unfold ss_oafA.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks oaf_rg_s11 oaf_rg_st base_val];
    rewrite ?U22, ?U27.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ 2148220742 0 1 (SLit 0) 0); [reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (AE2y.val_mem1_of_aview _ _ _ _ Hs11).
  + rewrite CS in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ (6158784 + 112) 0 4 (SOff 32 0) (TW.u_at B2 (TW.OFF_g_s + 112) 4));
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity
      | exact R32 | lia |].
    rewrite Z.add_0_r.
    exact (tw_read_val segs _ TMAP_A B2 TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 TMAP_A_ok Htw TMAP_A_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, oaf_rg_s11, oaf_rg_st.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U22, U27, CS.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* Run B's state at +0x260 holds of the machine state there, and the run's shadow entry holds. *)
Lemma oaf_entryB : forall ly S (W : world segs) regs mem md,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 19 = w64 ONACK_S -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (oaf_E regs []) ss_oafB
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONACK_WK)) mem (YK11.seg_rom segs))) /\
  sh_ok segs OAF_Bx OAF_SH (oaf_E regs []) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md HZ HAR R19 R25.
set (E := oaf_E regs []).
assert (CS : ONACK_S = 6158784) by reflexivity.
assert (U19 : bv_unsigned (ew E 19) = ONACK_S)
  by (unfold E; rewrite (oaf_ew regs _ 19 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF)
  by (unfold E; rewrite (oaf_ew regs _ 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_oafB.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold oaf_rg_wk, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (ONACK_S + o) G_HARNESS_rw).
    apply oaf_inG. unfold TW.SZ_g_s. lia.
  + apply pairwise_disjoint_of_extents.
    unfold oaf_rg_wk, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold oaf_factsB, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U25.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (oaf_ra ly S W mem md (ONACK_S + 144) HZ HAR ltac:(rewrite CS; reflexivity) ltac:(lia)
    ltac:(unfold TW.SZ_g_s; lia)) as HRA.
  assert (UB : U E OAF_Bx = SHADOW_OFF).
  { unfold U, OAF_Bx. cbn [sv_denot]. rewrite U25, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, OAF_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ OAF_Bx 19 (ONACK_S + 144) 8 ONACK_S 144 148 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The bytes of a value in memory, read byte by byte through the view. *)
Lemma oaf_aview_of_val : forall H (m : word -> option byte) a (n : nat) v,
  val_mem segs (mrestrict H m) a n v -> forall j, (j < n)%nat ->
  aview segs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* Run C's state at +0x284 holds of the machine state there. *)
Lemma oaf_entryC : forall (W : world segs) regs mem F,
  YK11.getr regs 23 = w64 (SHADOW_OFF + F / 8) -> 0 <= F < 2 ^ 47 ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (oaf_E regs []) ss_oafC
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONACK_JOIN)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F R23 HF Hp.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8.
pose proof (Z.div_lt_upper_bound F 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as HF8'.
assert (U23 : bv_unsigned (ew (oaf_E regs []) 23) = SHADOW_OFF + F / 8).
{ rewrite (oaf_ew regs [] 23 23%bv eq_refl), R23. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold oaf_rg_sh7, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U23.
  split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable segs). apply Hp. lia.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. split; exact I.
- unfold oaf_factsC, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.
End ent.


(* ------------------------------------------------------------------ *)
(* 3. The shadow join, +0x284 .. +0x2ac, then the release cut          *)
(* ------------------------------------------------------------------ *)

Section tail. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* From the release cut's facts at +0x284 (either arm): the nine shadow bytes 4 .. 12 of the frame := 0xf8, `j +0x2d8`;
   the run writes the own frame's shadow only (dkg_nf), so every fact of the cut moves to the run's memory; then the
   release cut. *)
Lemma oaf_tail : @onack_laws rc B MT -> @onack_rel_at fx rc B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    onack_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F ->
    onack_rel_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw Bw' pos F ly2 S2 W2 mem2 md2 e ->
    onack_regs_rel regs regs2 sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + ONACK_JOIN)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_onack_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).
Proof.
intros LAWS0 REL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F ly2 S2 W2
  mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (_ & _ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & FFL & HGX & _).
pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EF &
  HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw) & HTW2 & Hgf2).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24).
unfold ONACK_FBYTES in HFc, HFapp, HFLw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the call's window lies above alloc_ceiling, below 2 ^ 47 *)
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : ONACK_STK = 8496) by reflexivity.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
(* the frame and its shadow bytes at the cut *)
assert (Hin : In (ONACK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly2 ONACK_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ ONACK_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
change (fs_frame_bytes ONACK_CID / 8) with 32 in HFsh.
change (fs_frame_bytes ONACK_CID) with 256 in HFb.
rewrite EFA in HFb, HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONACK_CID pos F
  (flag_addr lyc ONACK_CID pos) HAR2 Hfrs Hbl ELF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8p.
pose proof (Z.div_lt_upper_bound F 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as HF8u.
set (s7 := SHADOW_OFF + F / 8) in *.
assert (HFlo : F + 256 <= kLowShadowBeg \/ kHighMemBeg <= F).
{ destruct HFapp as (_ & [HL | [HH _]]); [left; exact HL | right; exact HH]. }
unfold kLowShadowBeg, kHighMemBeg in HFlo.
(* +0x284 .. +0x2ac: a0 = -8, the nine `sb a0, i(s7)`, `j +0x2d8`; the run stops at the release cut *)
pose proof (oaf_entryC (fx := fx) W2 regs2 mem2 F R23 ltac:(lia)
  ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia))))) as HS.
assert (SHOK : sh_ok segs OAF_Bx [] (oaf_E regs2 []) (mrestrict (w_H W2) mem2)) by constructor.
assert (HEI : img_env VAL A_LIM (oaf_E regs2 [])) by (unfold oaf_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oaf_E regs2 []) n = YK11.getr regs2 r)
  by (intros n r Hn; apply oaf_ew; exact Hn).
assert (U23 : bv_unsigned (ew (oaf_E regs2 []) 23) = s7).
{ rewrite (EE 23%nat 23%bv eq_refl), R23. unfold w64. apply unsigned_lit_small. unfold s7, SHADOW_OFF. lia. }
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS HJ1 SHOK oaf_B0 ONACK_REL.
{ oaf_awr_rs.
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ ONACK_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U23 in Ha.
  right. unfold in_zr. cbn [fst snd]. rewrite EFA, ESH. change (fs_frame_bytes ONACK_CID / 8) with 32.
  unfold s7 in Ha. lia. }
lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (E5 := EF) in HS; rename mf into msF end.
assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew (oaf_E regs2 []) n)
  by (intros n Hn; unfold E5; rewrite ?ew_ewset_other by lia; reflexivity).
oaf_kreg HS E5lo EE (2%bv : bv 5) 2%nat R2 X2. oaf_kreg HS E5lo EE (3%bv : bv 5) 3%nat R3 X3.
oaf_kreg HS E5lo EE (4%bv : bv 5) 4%nat R4 X4. oaf_kreg HS E5lo EE (8%bv : bv 5) 8%nat R8 X8.
oaf_kreg HS E5lo EE (9%bv : bv 5) 9%nat R9 X9. oaf_kreg HS E5lo EE (18%bv : bv 5) 18%nat R18 X18.
oaf_kreg HS E5lo EE (23%bv : bv 5) 23%nat R23 X23. oaf_kreg HS E5lo EE (24%bv : bv 5) 24%nat R24 X24.
(* the run wrote the frame's shadow bytes 4 .. 12 only *)
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (s7 + 4 <= a < s7 + 13) ->
  aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem2 a).
{ oaf_kept HFr (fun x => s7 + 4 <= x < s7 + 13) U23. }
assert (GR : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msF) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (NFz : forall a, s7 + 4 <= a < s7 + 13 -> dkg_nf ONACK_CID F (flag_addr lyc ONACK_CID pos) a).
{ intros a Ha. unfold dkg_nf. right; left. change (fs_frame_bytes ONACK_CID / 8) with 32. unfold s7 in Ha. lia. }
(* what the call keeps, over the run *)
assert (KG : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (ms_mem msF) (spZ regs - ONACK_STK) (spZ regs)
  (onack_wr Bw b)).
{ apply (dk_kept_step_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc W2 mem2 (ms_mem msF)
    (spZ regs - ONACK_STK) (spZ regs) (onack_wr Bw b) (fun x => s7 + 4 <= x < s7 + 13) HARc HK KF GR).
  - intros a Hz Hc. cbv beta in Hz. pose proof (N4 a (NFz a Hz)). lia.
  - intros b0 m i Hb Hi Hz. exfalso. exact (N1 b0 m i Hb Hi (NFz _ Hz)).
  - intros a Hz Hi _ _ _. exfalso. exact (N2 a (NFz a Hz) Hi).
  - intros c p a Hc Hr Hz. exfalso. exact (N3 c p a Hc Hr (NFz a Hz)). }
(* the thirteen saved words, at the run's memory *)
assert (HSVn : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) (ms_mem msF)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONACK_SAVED).
{ apply Forall_forall. intros o Hino. cbv beta.
  pose proof (proj1 (Forall_forall _ _) Hsaved o Hino) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONACK_SAVED in Hino. cbn [In] in Hino.
    repeat (destruct Hino as [Hino | Hino]; [subst o; cbn [fst]; lia |]). destruct Hino. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KF; [lia|]. unfold s7, SHADOW_OFF. lia. }
(* the frame's last word, at the run's memory *)
assert (HFLn : rdword (aview segs (w_H W2) (ms_mem msF)) (F + 256 - 8) = Some (flag_addr lyc ONACK_CID pos)).
{ rewrite <- HFLw. apply YCbq.rdword_ext. intros i Hi. apply KF; [lia|]. unfold s7, SHADOW_OFF. lia. }
(* the world relation at Bw': no byte of G is a byte the run wrote *)
assert (TWn : tw_at TMAP_A (aview segs (w_H W2) (ms_mem msF)) Bw').
{ apply (tw_kept_GA (aview segs (w_H W2) mem2)); [exact HTW2|]. intros b0 n i Hbn Hi.
  assert (HG0 : inG TG.G_HARNESS (b0 + i))
    by (unfold inG; apply Exists_exists; exists (b0, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low segs B transport_segs_low TG.G_HARNESS (b0 + i) HGX HG0) as Hl. unfold kLowMemEnd in Hl.
  apply KF; [lia|]. unfold s7, SHADOW_OFF. lia. }
(* the release cut *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONACK_REL)) mm rom) mdx) Q) end.
apply (REL LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F ly2 S2 W2
  (ms_mem msF) _ e (ms_regs msF) HFIX).
- unfold onack_rel_cur, onack_cur.
  refine (conj (conj HJ1 (conj He (conj Hfrs (conj Hperm (conj ELF (conj Hmo (conj KG (conj HSVn _))))))))
    (conj TWn Hgf2)).
  unfold ONACK_FBYTES. exact HFLn.
- exact (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 (conj X23 X24))))))).
Qed.
End tail.


Section mv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

(* A view equal on [0, 2 ^ 64) is equal everywhere (aview reads the address modulo 2 ^ 64). *)
Lemma oaf_kd_all : forall (W : world segs) (m m' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  forall a, aview segs (w_H W) m' a = aview segs (w_H W) m a.
Proof.
intros W m m' H a. rewrite (aview_wrap64 segs _ m' a), (aview_wrap64 segs _ m a).
apply H. apply Z.mod_pos_bound. lia.
Qed.

(* The facts every cut carries move to a later memory whose view is the same at every address. *)
Lemma oaf_cur_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2
    (W2 : world segs) mem2 md2 mem3 md3 e,
  onack_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((ONACK_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  onack_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2 mem3 md3 e
  (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJ3 KD GR.
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
  + intros b0 m i Hb Hi Hn. rewrite KD. exact (K2 b0 m i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
- rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
Qed.
End mv.


(* ------------------------------------------------------------------ *)
(* 4. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Section main. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma oaf_holds : @onack_aft_stmt fx rc B MT.
Proof.
unfold onack_aft_stmt, onack_aft_at.
intros REL LAWS0 HMON STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' B2 pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (_ & _ & HSC & _ & _ & HROU & HRNE & LAWS & MTL & MTF & _ & _ & FFL & HGX & _).
pose proof HFIX as (HJ0 & _ & _ & Hgp & Htp & _ & _ & Hsp16 & Hlo & Hhi & _ & Htw0 & _ & Hm & _ & _ & Hapart &
  Hcnt & Hnev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HC0 & Htw2 & HTF2 & HROM2 & Hig & HN & Hgf2).
pose proof HC0 as (HJ & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R25) & R22 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CS : ONACK_S = 6158784) by reflexivity.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
pose proof (onack_wlen _ _ Htw0) as HLBw.
pose proof (onack_wlen _ _ Htw2) as HLB2.
destruct (oaf_model timg_A TF Bw b B2 Bw' Hig Hm HN) as [HMW HMN].
(* run A, +0x24c .. `bne a0, a1` at +0x25c: the check of the load at s + 112, the load of S_state B2, a1 = 1 *)
pose proof (oaf_entryA (fx := fx) B ly2 S2 W2 regs2 mem2 md2 B2 HSC HAR2 Htw2 R22 R27) as HS.
set (EA := oaf_E regs2 [Z_to_bv 64 (TW.u_at B2 (TW.OFF_g_s + 112) 4)]) in HS.
assert (SHOK : sh_ok segs OAF_Bx [] EA (mrestrict (w_H W2) mem2)) by constructor.
assert (HEI : img_env VAL A_LIM EA) by (unfold EA, oaf_E; apply Eimg_env).
assert (EEA : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EA n = YK11.getr regs2 r)
  by (intros n r Hn; apply oaf_ew; exact Hn).
assert (EA32 : ew EA 32 = Z_to_bv 64 (TW.u_at B2 (TW.OFF_g_s + 112) 4)) by exact (oaf_ew_x regs2 _ 0 ltac:(lia)).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONACK_AFT)) mm rom) mdx) Q) end.
paj_run_tok RUN HS HJ SHOK oaf_B0.
{ oaf_awr_rs.
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }

set (mdA := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdA. clear mat HEI0.
rename ms into msA.
(* run A writes nothing *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msA) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
  intros b0 wlo whi x Hin Hx. cbv beta.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]).
  destruct Hin. }
assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msA) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* `bne a0, a1`: a0 = S_state B2 (sign-extended), a1 = 1 *)
assert (DA : sv_denot EA (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.S_state B2)) by exact (oaf_sext EA B2 EA32).
psrr_branch_tok RUN BR HS SHOK oaf_B0.
- (* S_state B2 <> S_WAKING: the branch is taken, to the shadow join +0x284; the model's world is B2 *)
  cbn [branch_taken] in Hc. rewrite DA in Hc. change (sv_denot EA (SLit 1)) with (Z_to_bv 64 1) in Hc.
  rewrite (oaf_eqb1 _ (oaf_state_range B2)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  pose proof (HMN Hc) as EBw'.
  paj_run_to_tok RUNTO HS HJ SHOK oaf_B0 ONACK_JOIN.
  { oaf_awr_rs.
    repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
    apply awr_ok_x_nil. }
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (E1 := EF) in HS; rename mf into ms1 end.
  assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew EA n)
    by (intros n Hn; unfold E1; rewrite ?ew_ewset_other by lia; reflexivity).
  oaf_kreg HS E1lo EEA (2%bv : bv 5) 2%nat R2 Y2. oaf_kreg HS E1lo EEA (3%bv : bv 5) 3%nat R3 Y3.
  oaf_kreg HS E1lo EEA (4%bv : bv 5) 4%nat R4 Y4. oaf_kreg HS E1lo EEA (8%bv : bv 5) 8%nat R8 Y8.
  oaf_kreg HS E1lo EEA (9%bv : bv 5) 9%nat R9 Y9. oaf_kreg HS E1lo EEA (18%bv : bv 5) 18%nat R18 Y18.
  oaf_kreg HS E1lo EEA (23%bv : bv 5) 23%nat R23 Y23. oaf_kreg HS E1lo EEA (24%bv : bv 5) 24%nat R24 Y24.
  assert (K1 : forall a, aview segs (w_H W2) (ms_mem ms1) a = aview segs (w_H W2) mem2 a).
  { apply oaf_kd_all. intros a Ha. rewrite <- (KA a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]).
    destruct Hin. }
  assert (G1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms1) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA a Ha))).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONACK_JOIN)) mm rom) mdx) Q) end.
  apply (oaf_tail B MT LAWS0 REL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos
    sp1 F ly2 S2 W2 (ms_mem ms1) _ e (ms_regs ms1) HFIX).
  + refine (conj (oaf_cur_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2
      (ms_mem ms1) _ e HC0 HJ K1 G1) (conj _ _)).
    * rewrite EBw'. apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact Htw2 | intros x _; exact (K1 x)].
    * rewrite EBw'. exact Hgf2.
  + exact (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 (conj Y23 Y24))))))).
- (* S_state B2 = S_WAKING: the branch falls through to +0x260 *)
  cbn [branch_taken] in Hc. rewrite DA in Hc. change (sv_denot EA (SLit 1)) with (Z_to_bv 64 1) in Hc.
  rewrite (oaf_eqb1 _ (oaf_state_range B2)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  pose proof (HMW Hc) as HMM.

  paj_run_to_tok RUNTO HS HJ SHOK oaf_B0 ONACK_WK.
  { oaf_awr_rs.
    repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
    apply awr_ok_x_nil. }
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (E1 := EF) in HS; rename mf into ms1 end.
  assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew EA n)
    by (intros n Hn; unfold E1; rewrite ?ew_ewset_other by lia; reflexivity).
  oaf_kreg HS E1lo EEA (2%bv : bv 5) 2%nat R2 Y2. oaf_kreg HS E1lo EEA (3%bv : bv 5) 3%nat R3 Y3.
  oaf_kreg HS E1lo EEA (4%bv : bv 5) 4%nat R4 Y4. oaf_kreg HS E1lo EEA (8%bv : bv 5) 8%nat R8 Y8.
  oaf_kreg HS E1lo EEA (9%bv : bv 5) 9%nat R9 Y9. oaf_kreg HS E1lo EEA (18%bv : bv 5) 18%nat R18 Y18.
  oaf_kreg HS E1lo EEA (19%bv : bv 5) 19%nat R19 Y19.
  oaf_kreg HS E1lo EEA (23%bv : bv 5) 23%nat R23 Y23. oaf_kreg HS E1lo EEA (24%bv : bv 5) 24%nat R24 Y24.
  oaf_kreg HS E1lo EEA (25%bv : bv 5) 25%nat R25 Y25.
  assert (K1 : forall a, aview segs (w_H W2) (ms_mem ms1) a = aview segs (w_H W2) mem2 a).
  { apply oaf_kd_all. intros a Ha. rewrite <- (KA a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]).
    destruct Hin. }
  assert (G1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms1) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA a Ha))).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONACK_WK)) mm rom) mdx) Q) end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end. clearbody md1.
  clear HS SHOK HEI HF HFr HG E1lo E1 KA GA.
  set (regsB := ms_regs ms1) in *. set (memB := ms_mem ms1) in *. clearbody regsB memB. clear ms1 msA.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARB.
  (* run B, +0x260 .. `jal maybe_online` at +0x280: the check of the store at s + 144, the store of 1 there, a0 = s *)
  destruct (oaf_entryB (fx := fx) B ly2 S2 W2 regsB memB md1 HSC HARB Y19 Y25) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (oaf_E regsB [])) by (unfold oaf_E; apply Eimg_env).
  assert (EEB : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oaf_E regsB []) n = YK11.getr regsB r)
    by (intros n r Hn; apply oaf_ew; exact Hn).
  assert (U19B : bv_unsigned (ew (oaf_E regsB []) 19) = ONACK_S)
    by (rewrite (EEB 19%nat 19%bv eq_refl), Y19; apply unsigned_lit_small; lia).
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { oaf_awr_rs.
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19B in Ha;
      apply oaf_inG; unfold TW.SZ_g_s; lia |].
    apply awr_ok_x_nil. }

  lazymatch type of HS with
    OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ (restrict _ ?mf) =>
    set (E6 := EF) in *; rename mf into msC end.
  assert (E6lo : forall n, (n < 1024)%nat -> ew E6 n = ew (oaf_E regsB []) n)
    by (intros n Hn; unfold E6; rewrite ?ew_ewset_other by lia; reflexivity).
  oaf_kreg HS E6lo EEB (2%bv : bv 5) 2%nat Y2 Q2. oaf_kreg HS E6lo EEB (3%bv : bv 5) 3%nat Y3 Q3.
  oaf_kreg HS E6lo EEB (4%bv : bv 5) 4%nat Y4 Q4. oaf_kreg HS E6lo EEB (8%bv : bv 5) 8%nat Y8 Q8.
  oaf_kreg HS E6lo EEB (9%bv : bv 5) 9%nat Y9 Q9. oaf_kreg HS E6lo EEB (18%bv : bv 5) 18%nat Y18 Q18.
  oaf_kreg HS E6lo EEB (23%bv : bv 5) 23%nat Y23 Q23. oaf_kreg HS E6lo EEB (24%bv : bv 5) 24%nat Y24 Q24.
  oaf_reg HS (10%bv : bv 5) (w64 ONACK_S) Q10
    ltac:(cbn [sv_denot]; rewrite (E6lo 19%nat ltac:(lia)), (EEB 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact Y19).
  oaf_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + ONACK_JOIN)) Q1 ltac:(apply codeptr_val; exact HEI1).

  (* the store of :234: the four bytes at s + 144 hold 1 *)
  oaf_region HS 0%nat HRw.
  assert (U19f : bv_unsigned (ew E6 19) = ONACK_S) by (rewrite E6lo by lia; exact U19B).
  pose proof (can_field_of_region E6 _ 19 ONACK_S _ 144 148 144 148 144 4%N (SLit 1) 1 HRw U19f ltac:(oaf_in)
    eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VB.
  change (N.to_nat 4) with 4%nat in VB.
  clear HRw.
  pmkst HS.
  set (regsC := ms_regs msC) in *. set (memC := ms_mem msC) in *.
  set (mdC := with_vm_backing (m_vm_lazy md1) mat0 md1) in *.
  clearbody regsC memC mdC.
  (* run B wrote [s + 144, s + 148) only *)
  assert (CS' : ONACK_S = TA_g_s) by reflexivity.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (ONACK_S + 144 <= a < ONACK_S + 148) ->
    aview segs (w_H W2) memC a = aview segs (w_H W2) memB a).
  { oaf_kept HFr (fun x => ONACK_S + 144 <= x < ONACK_S + 148) U19B. }
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (ONACK_S + 144 <= a < ONACK_S + 148) ->
    aview segs (w_H W2) memC a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hn. rewrite (KB a Ha Hn). exact (K1 a). }
  assert (GC : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memC a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (G1 a Ha))).
  clear KB HF HFr HG.

  (* the call's stack: sp = sp1, 32-aligned, at most 144 below the entry sp *)
  pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  clear HJi memS.
  assert (EOS : ONACK_STK = 8496) by reflexivity.
  assert (EMS : MAYBEON_STK = 8352) by reflexivity.
  assert (Hsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128 /\ sp1 mod 32 = 0).
  { rewrite Esp1. unfold ONACK_FRAME.
    pose proof (Z.div_mod (spZ regs - 128) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (spZ regs - 128) 32 ltac:(lia)) as M.
    pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
    set (q := (spZ regs - 128) / 32) in *. set (r := (spZ regs - 128) mod 32) in *. set (t := spZ regs / 16) in *.
    split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult. }
  destruct Hsp1 as [Hsp1 Hsp132].
  assert (HSPC : spZ regsC = sp1) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
  assert (Hsp116 : sp1 mod 16 = 0).
  { pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp132, Z.add_0_r in D. rewrite D.
    replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
  (* the world relation at set_S_wake_acked B2 1: the store of :234 *)
  assert (TWG : forall x, tw_in TMAP_A x -> inG TG.G_HARNESS x).
  { intros x (o & b0 & n & Hin & Hx).
    assert (HG0 : In (b0, n) TG.G_HARNESS) by exact (TMAP_A_in_G o b0 n Hin).
    unfold inG. apply Exists_exists. exists (b0, n). split; [exact HG0 | unfold in_zr; cbn [fst snd]; lia]. }
  assert (GLOW : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Ha)).
  assert (HtwC : tw_at TMAP_A (aview segs (w_H W2) memC) (TW.set_S_wake_acked B2 1)).
  { rewrite oaf_wake_eq.
    apply (tw_write TMAP_A (aview segs (w_H W2) mem2) (aview segs (w_H W2) memC) B2 TW.OFF_g_s TA_g_s TW.SZ_g_s
      144 4 1 TMAP_A_ok Htw2 TMAP_A_g_s); [lia | unfold TW.SZ_g_s; lia | |].
    - intros j Hj. rewrite <- CS'. exact (oaf_aview_of_val _ _ _ 4 _ VB j Hj).
    - intros x Hx Hn. pose proof (GLOW x (TWG x Hx)) as Hl. unfold kLowMemEnd in Hl.
      apply KC; [lia|]. intros X. apply Hn. rewrite <- CS'. lia. }
  assert (HgfC : TW.g_fail_next (TW.set_S_wake_acked B2 1) <= 1)
    by (rewrite (proj1 (onack_wake_fail B2 1 HLB2)); exact Hgf2).
  (* the current heap frame: its bytes miss s + 144 (onack_apart), its placement is kept *)
  assert (HTFC : trans_tframe_at B ly2 S2 W2 memC regsC MAYBEON_STK TF).
  { clear - HTF2 Hapart KC LAWS HAR2 Hsp1 HSPC EOS EMS C1 C2 C3 C4 C5 CS CS'.
    unfold trans_tframe_at in *. destruct TF as [fr|]; [|exact I].
    destruct HTF2 as (H0 & Hg & Hs & Ho).
    assert (KV : forall a, TI.tf_addr fr <= a < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) ->
      aview segs (w_H W2) memC a = aview segs (w_H W2) mem2 a).
    { intros a Ha.
      destruct (trans_src_ok_place B LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hs ltac:(lia)) as [P|P]; apply KC; try lia;
      intros Hz; refine (Hapart a _ fr eq_refl Ha); right; right; right; left;
      unfold twa_fld, TW.A_S_wake_acked, TW.OFF_g_s; rewrite <- CS'; lia. }
    split; [exact H0|]. split.
    - apply (garr8_frame segs _ _ _ _ Hg). intros a Ha. rewrite length_map in Ha.
      apply mbyte_of_aview. exact (KV a Ha).
    - split.
      + apply (trans_src_ok_view B ly2 S2 W2 W2 mem2 memC _ _ Hs KV).
        intros s0 Hs0. apply KC; [lia|]. rewrite CS. lia.
      + unfold decode_off_win in *. rewrite HSPC. lia. }
  assert (HROMC : trans_rom_view_rd W2 memC).
  { intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Rb.
    rewrite KC; [exact (HROM2 a Ha) | lia | rewrite CS; lia]. }
  assert (HAPC : maybeon_apart TF (TW.set_S_wake_acked B2 1))
    by (intros x Hx fr Efr; exact (Hapart x (oaf_wr_sub timg_A TF Bw b B2 HLBw HN x Hx) fr Efr)).
  assert (HCNTC : count_cid MAYBEON_CID (frames S2) < fs_frames MAYBEON_CID).
  { rewrite Hfrs. cbn [count_cid]. change MAYBEON_CID with ONACK_CID. rewrite Z.eqb_refl. lia. }
  assert (HNEVC : st_nev S + (k + e) + MAYBEON_EV <= EV_MAX)
    by (unfold ONACK_EV, MAYBEON_EV, NOTICE_EV in *; lia).
  assert (EBR : BASE + ONACK_JOIN = 558768) by (vm_compute; reflexivity).
  (* +0x280: maybe_online, in the same G journal *)
  change (SRr segs W2 (@cfg_at fx segs (transport_sigma TS_maybe_online) regsC memC mdC)
    (transport_onack_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b)).
  eapply SRr_bind.
  { apply (HMON fx STK sp0 FP ly S W0 mem0 md0 ((ONACK_CID, pos) :: own) ly2 S2 W2 memC mdC (k + e) regsC TF
      (TW.set_S_wake_acked B2 1) Bw' HJ
      ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold ONACK_JOIN, AF_on_ack; lia | reflexivity])
      ltac:(unfold raZ; rewrite Q1, EBR, unsigned_lit_small by lia; lia)
      ltac:(rewrite Q3; exact Hgp) ltac:(rewrite Q4; exact Htp) Q10
      ltac:(rewrite HSPC; exact Hsp116) ltac:(rewrite HSPC; lia) ltac:(rewrite HSPC; lia)
      HtwC HgfC HMM HTFC HROMC HAPC HCNTC HNEVC). }
  intros W3 c3 _ HPOST.
  unfold transport_maybeon_post, transport_cg_post in HPOST.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 &
    Htw3 & Hgf3).

  rewrite HSPC in HK3.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
  (* the layout keeps the frames where the call's layout puts them *)
  assert (ELF3 : ly_F ly3 = ly_F lyc).
  { pose proof HJ3 as (_ & _ & (memS3 & HJ3i & _) & _). pose proof HJ3i as (_ & Hly3 & _).
    pose proof Hly3 as (_ & _ & _ & _ & _ & E3 & _). pose proof Hlyc as (_ & _ & _ & _ & _ & Ec & _).
    rewrite E3, Ec. reflexivity. }
  assert (Hfa2 : forall cid p, frame_addr ly2 cid p = frame_addr lyc cid p)
    by (intros cid p; unfold frame_addr; rewrite HlyF; reflexivity).
  assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
    by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
  destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONACK_CID pos F
    (flag_addr lyc ONACK_CID pos) HAR2 Hfrs Hbl HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
  (* what the call keeps: the cut's, over run B (s + 144, a byte of onack_wr), then maybe_online's *)
  assert (KGC : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 memC (spZ regs - ONACK_STK) (spZ regs)
    (onack_wr Bw b)).
  { apply (dk_kept_step_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc W2 mem2 memC
      (spZ regs - ONACK_STK) (spZ regs) (onack_wr Bw b) (fun x => ONACK_S + 144 <= x < ONACK_S + 148) HARc HK KC GC).
    - intros a Hz Hc0. cbv beta in Hz. exfalso. lia.
    - intros b0 m i _ _ Hz. cbv beta in Hz. right; right; right; left.
      unfold twa_fld, TW.A_S_wake_acked, TW.OFF_g_s. rewrite <- CS'. lia.
    - intros a Hz _ HnG _ _. cbv beta in Hz. exfalso. apply HnG. apply oaf_inG. unfold TW.SZ_g_s. lia.
    - intros c p a _ _ Hz. cbv beta in Hz. right; right; right; left.
      unfold twa_fld, TW.A_S_wake_acked, TW.OFF_g_s. rewrite <- CS'. lia. }
  assert (Hce1 : alloc_ceiling <= spZ regs - ONACK_STK) by (clear - Hceil Hslo Hlo; lia).
  assert (Hsh1 : spZ regs <= 2 ^ 64) by (clear - Hhi Hshi H47; lia).
  assert (KG3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - ONACK_STK) (spZ regs)
    (onack_wr Bw b)).
  { apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 memC W3 mem3
      (spZ regs - ONACK_STK) (spZ regs) (sp1 - MAYBEON_STK) sp1 (onack_wr Bw b)
      (maybeon_wr (TW.set_S_wake_acked B2 1)) (dkg_nf ONACK_CID F (flag_addr lyc ONACK_CID pos))
      Hce1 Hsh1 Hfa2 ltac:(intros f Hf; rewrite Hfrs; right; exact Hf) Hbl N1 N3 KGC HK3).
    - lia.
    - lia.
    - intros a Ha. left. exact (oaf_wr_sub timg_A TF Bw b B2 HLBw HN a Ha). }
  (* the thirteen saved words and the frame's last word, at the return *)
  destruct HK3 as (L1 & _ & _ & L4 & _).
  assert (HSV3 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem3) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONACK_SAVED).
  { apply Forall_forall. intros o Hino. cbv beta.
    pose proof (proj1 (Forall_forall _ _) HSV o Hino) as Hv. cbv beta in Hv.
    assert (Ho : 8 <= fst o <= 104).
    { unfold ONACK_SAVED in Hino. cbn [In] in Hino.
      repeat (destruct Hino as [Hino | Hino]; [subst o; cbn [fst]; lia |]). destruct Hino. }
    rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi.
    rewrite L1 by lia. apply KC; [lia|]. rewrite CS. lia. }
  assert (Hin2 : In (ONACK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  assert (EFA : frame_addr ly2 ONACK_CID pos = F) by (rewrite Hfa2; symmetry; exact EF).
  assert (HFL3 : rdword (aview segs (w_H W3) mem3) (F + ONACK_FBYTES - 8) = Some (flag_addr lyc ONACK_CID pos)).
  { rewrite <- HFL. unfold ONACK_FBYTES in *. apply YCbq.rdword_ext. intros i Hi.
    assert (HnI : ~ in_img segs (F + 256 - 8 + i)).
    { apply (frm_img segs B LAWS _ _ _ _ _ ONACK_CID pos (F + 256 - 8 + i) HAR2 Hin2).
      rewrite EFA, onack_fbytes. unfold ONACK_FBYTES. lia. }
    rewrite (L4 ONACK_CID pos (F + 256 - 8 + i) Hin2).
    - apply KC; [lia|]. intros X. apply HnI. apply (proj1 (HGX _ (oaf_inG _ ltac:(unfold TW.SZ_g_s; lia)))).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes ONACK_CID) with 256. lia.
    - intros Hw. apply HnI. exact (proj1 (HGX _ (oaf_mwr_G _ _ Hw))). }
  (* the shadow join, then the release cut *)
  rewrite Q1.
  change (SRr segs W3 (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + ONACK_JOIN)) mem3 (YK11.seg_rom segs)) md3)
    (transport_onack_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b)).
  apply (oaf_tail B MT LAWS0 REL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos
    sp1 F ly3 S3 W3 mem3 md3 (e + e3) regs3 HFIX).
  + refine (conj (conj _ (conj _ (conj _ (conj _ (conj ELF3 (conj _ (conj KG3 (conj HSV3 HFL3)))))))) (conj Htw3 Hgf3)).
    * replace (k + (e + e3)) with (k + e + e3) by lia. exact HJ3.
    * unfold ONACK_EV, MAYBEON_EV, NOTICE_EV in *. lia.
    * rewrite Hfr3. exact Hfrs.
    * exact (Permutation_trans Hperm3 Hperm).
    * exact (mo_le_trans MT MTL Sc S2 S3 0 0 HMO Hmo3).
  + unfold onack_regs_rel.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    * exact (eq_trans (HP3 2 ltac:(hnf; lia)) Q2).
    * exact (eq_trans (HP3 3 ltac:(hnf; lia)) Q3).
    * exact (eq_trans (HP3 4 ltac:(hnf; lia)) Q4).
    * exact (eq_trans (HP3 8 ltac:(hnf; lia)) Q8).
    * exact (eq_trans (HP3 9 ltac:(hnf; lia)) Q9).
    * exact (eq_trans (HP3 18 ltac:(hnf; lia)) Q18).
    * exact (eq_trans (HP3 23 ltac:(hnf; lia)) Q23).
    * exact (eq_trans (HP3 24 ltac:(hnf; lia)) Q24).
Qed.
End main.

(* The after-notice piece of the walk of on_ack (on_ack_segs.v onack_aft_stmt), at every machine, run ceiling,
   record and meter. *)
Lemma onack_aft_piece : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT, @onack_aft_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@oaf_holds fx rc B MT). Qed.
