(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 458 of its 503 lines of code are new or changed and 1879 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/diginet_session_wake_seg_rel.v, with its module paths and module names changed; 878 of its 942 lines of code are new or changed and 439 lines of the source are left out. *)
(* on_ack_seg_aft: Lemma onack_aft_piece : onack_aft_stmt (lib/B/Prog/on_ack_segs.v), the after-notice piece of
   on_ack's image-B walk, offsets +0x25c .. +0x2bc of the listing lib/B/Prog/DgnTransportBList.v
   (fuzz_transport.asan-ubsan 0x887e8 .. 0x88848), then the release cut +0x2e8, which the onack_rel_at it is given
   closes.

   What the code does (:233-236). +0x25c `lb a0, 0(s11)` and +0x260 `bnez a0, +0x488`: the shadow byte of s + 112
   (s11 = its address), 0 (g_s's payload lies in the record's zero shadow: on_ack_cg.v trans_onack_cells, read by
   DgnTransportBCg.v decode_zshadow_rd), so the report path is not taken; +0x264 `lw a0, 0(s6)`: S_state of notice's
   world B2 (s6 = s + 112), sign-extended; +0x268 `li a1, 1`; +0x26c `bne a0, a1, +0x294`.
     The arm S_state B2 <> S_WAKING goes to +0x294. The model's world is then B2 (on_ack_segs.v onack_model_ntc).
     The arm S_state B2 = S_WAKING: +0x270 .. +0x280 the check of the 4-byte store at s + 144 (its shadow byte, 0, read
     through s9), +0x284 `li a0, 1`, +0x288 `sw a0, 0x90(s3)` (:234; the world is set_S_wake_acked B2 1),
     +0x28c `mv a0, s3`, +0x290 `jal maybe_online` (0x8ae8c = transportb_sigma TB_maybe_online), return address
     +0x294.
   +0x294 `li a0, -8` and nine `sb a0, i(s7)` (i = 8, 9, 10, 11, 4, 5, 6, 7, 12): the frame's shadow bytes 4 .. 12 :=
   0xf8 (the notice's 72 bytes out of scope again); +0x2bc `j +0x2e8`, the release cut.

   The runs are the token engine's over the caller's G journal (lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x):
     run A    +0x25c .. +0x26c  two read regions: the shadow byte at s11 (value 0) and the 4 bytes of S_state at s6
                               (atom 32, read off the world B2 by TWorldG.v tw_read_val); it stops at the `bne`;
     +0x26c                    taken up again from a state with no region (the registers as atoms) and split on the
                               `bne` (DgnTransportBPaLib.v psrr_branch_tok);
     the arm to +0x294         one instruction, no byte written;
     the arm to +0x270         one instruction, no byte written; then run W (+0x270 .. the `jal`): g_s's wake_acked at
                               s3 (written, a byte range of G), the shadow entry of the check of s + 144; it stops at the
                               call of maybe_online;
     the join (+0x294 .. +0x2e8) the frame's shadow bytes 4 .. 12 at s7 (written; no shadow token), a run to the release
                               cut (oaf_join, shared by both arms).
   The maybe_online call (maybe_online_cg.v transport_maybe_online_cg at transportb_sigma TB_maybe_online), premise by
   premise: the journal at the call state (the own frame owned); ra = +0x294 (DgnTransportBPaLib.v ret_ok_codeptr_v);
   gp, tp, s0 .. s11 and sp kept by the runs; a0 = s = MAYBEON_S; sp = sp1, 32-aligned, and on_ack_cg.v onack_stk_eq
   places maybe_online's window inside on_ack's; tw_at at set_S_wake_acked B2 1 (TWorldG.v tw_write of the store at
   s + 144); g_fail_next of that world (on_ack_seg_wld.v onack_wake_fail); the model (onack_model_ntc, this arm);
   trans_tframe_at and trans_rom_view_rd carried from the cut (the run wrote [s + 144, s + 148) only, and TF lies apart
   from it by onack_apart: onack_wr's wake_acked disjunct); maybeon_apart from onack_apart, since the range
   maybe_online writes at set_S_wake_acked B2 1 is the range it writes at set_S_wake_acked (onack_w1 Bw) 1 (oaf_wr_cong:
   B2 is set_GOT_acked (onack_w1 Bw) a, on_ack_segs.v onack_B2_eq, and maybeon_wr reads S_state, S_wake_acked,
   S_e1_named_us, S_state of maybeon_w1 and GOT.n of maybeon_w2 only); the count (frames S2 = (ONACK_CID, pos) ::
   frames Sc and MAYBEON_CID = ONACK_CID); no event. Its post folds into onack_cur by TransportGCg.v dk_kept_trans_nf_g
   (its written range is a part of onack_wr Bw b), the saved words and the frame's last word by its kept clauses.

   Trap and error paths on this piece: the slow path of the check of s + 112 (`bnez a0` at +0x260 to +0x488) and of
   the check of s + 144 (`bnez a1` at +0x280 to +0x49c): the shadow bytes of s + 112 and of s + 144 are 0
   (trans_onack_cells). This piece passes no UBSan trap word. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import maybe_online_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_seg_kit on_ack_segs on_ack_seg_wld.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
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
(* 1. The model on this piece                                          *)
(* ------------------------------------------------------------------ *)

(* The two later cut points: the instruction after the `bne` (the S_WAKING arm) and the join (+0x294, the `bne`
   target and maybe_online's return address). *)
Definition ONACK_WK : Z := AF_on_ack + 0x270.
Definition ONACK_JOIN : Z := AF_on_ack + 0x294.

(* S_state and the store of :234 at their numeral offsets (OFF_g_s + 112, OFF_g_s + 144). *)
Lemma oaf_state_at : forall X, TW.S_state X = bv_swrap 32 (TW.u_at X (TW.OFF_g_s + 112) 4).
Proof. intros X. reflexivity. Qed.
Lemma oaf_wake_at : forall X v, TW.set_S_wake_acked X v = TW.upd X (TW.OFF_g_s + 144) (TW.put 4 v).
Proof. intros X v. reflexivity. Qed.

Lemma oaf_state_range : forall X, - 2 ^ 31 <= TW.S_state X < 2 ^ 31.
Proof.
intros X. rewrite oaf_state_at.
pose proof (bv_swrap_in_range 32 (TW.u_at X (TW.OFF_g_s + 112) 4) ltac:(discriminate)) as R.
change (bv_half_modulus 32) with (2 ^ 31) in R. lia.
Qed.

(* `bne a0, a1` with a1 = 1, on the sign-extended state. *)
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

(* The sign-extended 4-byte load of g_s's state is the model's S_state. *)
Lemma oaf_sext : forall E X, ew E 32 = Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 112) 4) ->
  sv_denot E (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.S_state X).
Proof.
intros E X H.
assert (R : 0 <= TW.u_at X (TW.OFF_g_s + 112) 4 < 2 ^ 32) by exact (TWL.u_at_range X _ 4).
cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. rewrite oaf_state_at. reflexivity.
Qed.

(* maybe_online's two stores at their numeral offsets (OFF_g_s + 184, OFF_g_s + 112). *)
Lemma oaf_mw1_at : forall X, maybeon_w1 X =
  TW.upd X (TW.OFF_g_s + 184) (TW.put 8 (TS0.u64 (TW.S_last_rx_us X + TS0.ms_m (TW.S_cfg_keepalive_ms X)))).
Proof. intros X. reflexivity. Qed.
Lemma oaf_mw2_at : forall X, maybeon_w2 X = TW.upd (maybeon_w1 X) (TW.OFF_g_s + 112) (TW.put 4 TS0.DIGINET_S_ONLINE).
Proof. intros X. reflexivity. Qed.

Lemma oaf_mw1_len : forall X, Z.of_nat (length X) = TW.W_LEN -> Z.of_nat (length (maybeon_w1 X)) = TW.W_LEN.
Proof.
intros X HL. rewrite oaf_mw1_at.
rewrite TWL.length_upd_put; [exact HL | unfold TW.OFF_g_s; lia | rewrite HL; unfold TW.OFF_g_s, TW.W_LEN; lia].
Qed.

(* The store at OFF_g_s + 184 keeps the state. *)
Lemma oaf_mw1_state : forall X, Z.of_nat (length X) = TW.W_LEN -> TW.S_state (maybeon_w1 X) = TW.S_state X.
Proof.
intros X HL. rewrite oaf_mw1_at. unfold TW.S_state.
assert (HP8 : Z.of_nat (length (TW.put 8 (TS0.u64 (TW.S_last_rx_us X + TS0.ms_m (TW.S_cfg_keepalive_ms X))))) = 8)
  by (rewrite TWL.length_put; reflexivity).
rewrite TWL.s32_at_upd_out; [reflexivity | unfold TW.OFF_g_s; lia | unfold TW.A_S_state, TW.OFF_g_s; lia
  | rewrite HP8; unfold TW.A_S_state, TW.OFF_g_s; lia | rewrite HP8, HL; unfold TW.OFF_g_s, TW.W_LEN; lia].
Qed.

(* The two stores keep GOT.n. *)
Lemma oaf_mw2_gotn : forall X, Z.of_nat (length X) = TW.W_LEN -> TW.GOT_n (maybeon_w2 X) = TW.GOT_n X.
Proof.
intros X HL. pose proof (oaf_mw1_len X HL) as H1.
rewrite oaf_mw2_at. unfold TW.GOT_n.
assert (HP4 : Z.of_nat (length (TW.put 4 TS0.DIGINET_S_ONLINE)) = 4) by (rewrite TWL.length_put; reflexivity).
rewrite TWL.s32_at_upd_out; [| unfold TW.OFF_g_s; lia | unfold TW.A_GOT_n, TW.OFF_GOT; lia
  | rewrite HP4; unfold TW.A_GOT_n, TW.OFF_GOT, TW.OFF_g_s; lia | rewrite HP4, H1; unfold TW.OFF_g_s, TW.W_LEN; lia].
rewrite oaf_mw1_at.
assert (HP8 : Z.of_nat (length (TW.put 8 (TS0.u64 (TW.S_last_rx_us X + TS0.ms_m (TW.S_cfg_keepalive_ms X))))) = 8)
  by (rewrite TWL.length_put; reflexivity).
rewrite TWL.s32_at_upd_out; [reflexivity | unfold TW.OFF_g_s; lia | unfold TW.A_GOT_n, TW.OFF_GOT; lia
  | rewrite HP8; unfold TW.A_GOT_n, TW.OFF_GOT, TW.OFF_g_s; lia | rewrite HP8, HL; unfold TW.OFF_g_s, TW.W_LEN; lia].
Qed.

(* notice_wr reads its world through GOT.n only. *)
Lemma oaf_notice_wr_gotn : forall X Y n a, TW.GOT_n X = TW.GOT_n Y -> notice_wr X n a -> notice_wr Y n a.
Proof. intros X Y n a E H. unfold notice_wr in *. rewrite <- E. exact H. Qed.

(* THE CONGRUENCE: the range maybe_online writes at set_S_wake_acked B2 1, with B2 = set_GOT_acked (onack_w1 Bw) v
   (notice's N_ACKED world), lies in the range it writes at set_S_wake_acked (onack_w1 Bw) 1 (onack_wr's last
   disjunct): maybeon_wr reads S_state, S_wake_acked, S_e1_named_us, S_state of maybeon_w1 (maybeon_ntc too) and GOT.n of
   maybeon_w2, and the store of GOT.acked changes none of them (on_ack_seg_wld.v onack_B2_facts, onack_wake_facts). *)
Lemma oaf_wr_cong : forall Bw v x, Z.of_nat (length Bw) = TW.W_LEN ->
  maybeon_wr (TW.set_S_wake_acked (TW.set_GOT_acked (onack_w1 Bw) v) 1) x ->
  maybeon_wr (TW.set_S_wake_acked (onack_w1 Bw) 1) x.
Proof.
intros Bw v x HL H.
destruct (onack_w1_facts Bw HL) as (_ & _ & _ & _ & _ & _ & L1).
destruct (onack_B2_facts (onack_w1 Bw) v L1) as (B1 & _ & B3 & _ & _ & B6 & _ & L2).
destruct (onack_wake_facts _ 1 L2) as (C1 & C2 & C3 & _ & _ & C6).
destruct (onack_wake_facts _ 1 L1) as (D1 & D2 & D3 & _ & _ & D6).
destruct (onack_wake_fail _ 1 L2) as (_ & LC).
destruct (onack_wake_fail _ 1 L1) as (_ & LD).
set (X1 := TW.set_S_wake_acked (TW.set_GOT_acked (onack_w1 Bw) v) 1) in *.
set (X2 := TW.set_S_wake_acked (onack_w1 Bw) 1) in *.
assert (Es : TW.S_state X1 = TW.S_state X2) by (rewrite C1, D1, B1; reflexivity).
assert (Ew : TW.S_wake_acked X1 = TW.S_wake_acked X2) by (rewrite C2, D2; reflexivity).
assert (Ee : TW.S_e1_named_us X1 = TW.S_e1_named_us X2) by (rewrite C3, D3, B3; reflexivity).
assert (Eg : TW.GOT_n X1 = TW.GOT_n X2) by (rewrite C6, D6, B6; reflexivity).
assert (Es1 : TW.S_state (maybeon_w1 X1) = TW.S_state (maybeon_w1 X2))
  by (rewrite (oaf_mw1_state X1 LC), (oaf_mw1_state X2 LD); exact Es).
assert (Eg2 : TW.GOT_n (maybeon_w2 X1) = TW.GOT_n (maybeon_w2 X2))
  by (rewrite (oaf_mw2_gotn X1 LC), (oaf_mw2_gotn X2 LD); exact Eg).
assert (En : maybeon_ntc X1 = maybeon_ntc X2) by (unfold maybeon_ntc; rewrite Es1; reflexivity).
destruct H as (Hgo & Hw). split.
- unfold maybeon_go in Hgo |- *. rewrite <- Es, <- Ew, <- Ee. exact Hgo.
- destruct Hw as [Hw | (Hs & Hw)]; [left; exact Hw | right].
  split; [rewrite <- Es1; exact Hs|].
  destruct Hw as [Hw | Hw]; [left; exact Hw | right].
  rewrite <- En. exact (oaf_notice_wr_gotn _ _ _ _ Eg2 Hw).
Qed.

(* g_s's and GOT's payload bytes are bytes of G. *)
Lemma oaf_inG_gs : forall a, ONACK_S <= a < ONACK_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df640, 18264). split.
- unfold TG.G_HARNESS_B. cbn [In]. tauto.
- unfold in_zr, ONACK_S, TB_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.
Lemma oaf_inG_got : forall a, TB_GOT <= a < TB_GOT + TW.SZ_GOT -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5e4f60, 224). split.
- unfold TG.G_HARNESS_B. cbn [In]. tauto.
- unfold in_zr, TB_GOT, TW.SZ_GOT in *. cbn [fst snd]. lia.
Qed.

(* Every byte maybe_online stores is a byte of G (its notice has kind N_STATE). *)
Lemma oaf_mwr_G : forall X a, maybeon_wr X a -> inG TG.G_HARNESS_B a.
Proof.
intros X a (_ & [Ha | (_ & [Ha | Ha])]).
- apply oaf_inG_gs. unfold twb_fld, TW.A_S_next_keepalive_us, TW.OFF_g_s in Ha. unfold ONACK_S, TW.SZ_g_s. lia.
- apply oaf_inG_gs. unfold twb_fld, TW.A_S_state, TW.OFF_g_s in Ha. unfold ONACK_S, TW.SZ_g_s. lia.
- unfold notice_wr, maybeon_ntc in Ha. cbn [TI.n_kind] in Ha.
  destruct Ha as [(_ & [(Hn & Ha) | Ha]) | [(Hk & _) | [(Hk & _) | [(Hk & _) | [(Hk & _) | (Hk & _)]]]]];
    try (exfalso; unfold TS0.DIGINET_N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in Hk;
         discriminate Hk).
  + apply oaf_inG_got. unfold twb_fld, TW.A_GOT_t_state, TW.GOT_t_ESZ, TW.OFF_GOT in Ha.
    unfold TC.TRANS_MAX in Hn. unfold TW.SZ_GOT. lia.
  + apply oaf_inG_got. unfold twb_fld, TW.A_GOT_n, TW.OFF_GOT in Ha. unfold TW.SZ_GOT. lia.
Qed.

(* The model on this piece: notice's answer is B2, then by the state either maybe_online's world or B2. *)
Lemma oaf_model : forall I F Bw b Bw' B2, onack_ign Bw b = false ->
  TSS.on_ack_m I F Bw b = Some (Bw', tt) ->
  TSS.call_notify I F (onack_w1 Bw) (onack_ntc Bw b) = Some (B2, tt) ->
  if TW.S_state B2 =? TS0.DIGINET_S_WAKING then TSS.maybe_online_m I F (TW.set_S_wake_acked B2 1) = Some (Bw', tt)
  else Bw' = B2.
Proof.
intros I F Bw b Bw' B2 Hi Hm Hc. destruct (onack_model_ntc I F Bw b Bw' Hi Hm) as (B3 & Hc3 & H).
rewrite Hc in Hc3. pose proof (onack_some_inv _ _ Hc3) as E. subst B3. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* Every run here has no shadow token but run W: the span (0, 0); the shadow base s9 (atom 25). *)
Definition OAF_B0 : Z * Z := (0, 0).
Definition OAF_BX : sv := SOff 25 0.
(* run A at +0x25c: the shadow byte of s + 112 at s11 (atom 27, read, 0); the 4 bytes of S_state at s6 (atom 22,
   read, atom 32). *)
Definition oaf_rg_sh : YP09.region := YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SLit 0))].
Definition oaf_rg_st : YP09.region := YP09.mkRegion (Some 22%nat) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 32 0))].
Definition oaf_facts_a : facts := mkFacts [(32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_oafa : sstate := mkSS ONACK_AFT sr_atoms [oaf_rg_sh; oaf_rg_st] None oaf_facts_a.
(* run W at +0x270: g_s's wake_acked at s3 (atom 19, written); s3 = s and s9 = the shadow base; the shadow entry of
   the check of the 4-byte store at s + 144. *)
Definition oaf_rg_wk : YP09.region := YP09.mkRegion (Some 19%nat) 144 148 144 148 [].
Definition oaf_facts_w : facts :=
  mkFacts [(19%nat, mkAF ONACK_S ONACK_S 6); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_oafw : sstate := mkSS ONACK_WK sr_atoms [oaf_rg_wk] None oaf_facts_w.
Definition OAF_SHW : list shent := [mkSHE 19 144 148].
(* the join at +0x294: the frame's shadow bytes 4 .. 12 at s7 (atom 23, written), placed above the span by a fact. *)
Definition oaf_rg_sh7 : YP09.region := YP09.mkRegion (Some 23%nat) 4 13 4 13 [].
Definition oaf_facts_j : facts := mkFacts [(23%nat, mkAF SHADOW_OFF (2 ^ 47) 0)] [] [].
Definition ss_oafj : sstate := mkSS ONACK_JOIN sr_atoms [oaf_rg_sh7] None oaf_facts_j.

(* The register and region readers of a symbolic state (on_ack_seg_ign.v's oig_reg / oig_region, here also in the
   form a run leaves at a call: st_ok at the callee's pc). *)
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
(* Register r of the machine state of HS, whose symbolic value is atom n, the start value of register rn (Q its
   value): the run's valuation agrees with the start valuation below atom 1024 (Elo), which reads the registers (EE). *)
Ltac oaf_kreg_of HS Elo EE r n rn Q H :=
  lazymatch type of Q with _ = ?v =>
    oaf_reg HS r v H
      ltac:(cbn [sv_denot]; try rewrite (Elo n ltac:(lia)); rewrite (EE n rn eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
            exact Q) end.
Ltac oaf_kreg HS Elo EE r n Q H := oaf_kreg_of HS Elo EE r n r Q H.
Ltac oaf_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac oaf_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac oaf_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The windows of a run's start state, computed, against the bytes Zs a run may change. *)
Ltac oaf_win Hin Hx U :=
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
          [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U in Hx; lia |]);
  destruct Hin.
(* The model of the goal, named. *)
Ltac oaf_name_md md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md := m) in *; clearbody md end.
(* After a run: its valuation agrees with the start valuation E0 below atom 1024 (Hlo), and its machine state is
   named m. *)
Ltac oaf_lo HS E0 Hlo m :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) =>
      assert (Hlo : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity); rename mf into m
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ (restrict _ ?mf) =>
      assert (Hlo : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity); rename mf into m
  end.

Section ent. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The valuations: the 32 registers (and, for run A, atom 32 = the 4 bytes of S_state of the world X). *)
Definition oaf_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).
Definition oaf_Ea (regs : bvmap 5 word) (X : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 112) 4)]).

Lemma oaf_ew : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oaf_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold oaf_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma oaf_ewa : forall regs X n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oaf_Ea regs X) n = YK11.getr regs r.
Proof. intros regs X n r Hn. unfold oaf_Ea. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma oaf_ewa32 : forall regs X, ew (oaf_Ea regs X) 32 = Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 112) 4).
Proof. intros regs X. unfold oaf_Ea. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.

(* The bytes of a value in memory, read byte by byte through the view. *)
Lemma oaf_aview_of_val : forall H (m : word -> option byte) a (n : nat) v,
  val_mem segs (mrestrict H m) a n v -> forall j, (j < n)%nat ->
  aview segs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* One byte read off the view, in val_mem's form. *)
Lemma oaf_val_mem1 : forall H (m : word -> option byte) a v,
  aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. replace k with 0%nat by lia. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte segs (mrestrict H m) a) as [x|]; [|discriminate Hv].
cbn [option_map] in Hv. injection Hv as <-. f_equal. apply bv_eq.
pose proof (bv_unsigned_in_range 8 x) as R. change (bv_modulus 8) with 256 in R.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !(Z.mod_small (bv_unsigned x) 256 R). reflexivity.
Qed.

(* Two views equal at a byte read the same byte. *)
Lemma oaf_mbyte_of_aview : forall H (m m' : word -> option byte) a,
  aview segs H m' a = aview segs H m a -> mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof.
intros H m m' a E. unfold aview in E.
destruct (mbyte segs (mrestrict H m') a) as [x|], (mbyte segs (mrestrict H m) a) as [y|];
  cbn [option_map] in E; [| discriminate E | discriminate E | reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* The symbolic state at +0x25c holds of the machine state there. *)
Lemma oaf_entry_a : forall ly S (W : world segs) regs mem md X,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) X ->
  YK11.getr regs 22 = w64 (ONACK_S + 112) -> YK11.getr regs 27 = w64 (SHADOW_OFF + (ONACK_S + 112) / 8) ->
  st_ok_pi segs VAL (oaf_Ea regs X) ss_oafa
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONACK_AFT)) mem (YK11.seg_rom segs))).
Proof.
intros ly S W regs mem md X HSC HAR Htw R22 R27.
assert (CS : ONACK_S = 6157888) by reflexivity.
assert (E27 : SHADOW_OFF + (ONACK_S + 112) / 8 = 2148220630) by reflexivity.
rewrite E27 in R27.
assert (U22 : bv_unsigned (ew (oaf_Ea regs X) 22) = ONACK_S + 112)
  by (rewrite (oaf_ewa regs X 22 22%bv eq_refl), R22; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew (oaf_Ea regs X) 27) = 2148220630)
  by (rewrite (oaf_ewa regs X 27 27%bv eq_refl), R27; apply unsigned_lit_small; lia).
assert (R32 : 0 <= TW.u_at X (TW.OFF_g_s + 112) 4 < 2 ^ 32) by exact (TWL.u_at_range X _ 4).
assert (U32 : bv_unsigned (ew (oaf_Ea regs X) 32) = TW.u_at X (TW.OFF_g_s + 112) 4)
  by (rewrite oaf_ewa32; apply unsigned_lit_small; lia).
assert (Hs : aview segs (w_H W) mem 2148220630 = Some 0).
{ pose proof (decode_zshadow_rd B ly S W mem md ONACK_S (ONACK_S + TW.SZ_g_s) (ONACK_S + 112) HAR
    ltac:(rewrite CS; reflexivity) ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) HSC) as H.
  replace 2148220630 with (FCells.shadow_addr (ONACK_S + 112)) by reflexivity. exact H. }
rewrite restrict_mkst_fx. unfold ss_oafa.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks oaf_rg_sh oaf_rg_st base_val];
    rewrite ?U22, ?U27.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ 2148220630 0 1 (SLit 0) 0); [reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (oaf_val_mem1 _ _ _ _ Hs).
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ (ONACK_S + 112) 0 4 (SOff 32 0) (TW.u_at X (TW.OFF_g_s + 112) 4));
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | exact R32 | lia |].
    replace (ONACK_S + 112 + 0) with (TB_g_s + 112) by reflexivity.
    exact (tw_read_val segs _ TMAP_B X TW.OFF_g_s TB_g_s TW.SZ_g_s 112 4 TMAP_B_ok Htw TMAP_B_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, oaf_rg_sh, oaf_rg_st. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U22, U27. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold oaf_facts_a, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* A state with no region at any pc of the listing (the `bne` at +0x26c is split from it). *)
Lemma oaf_entry0 : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (oaf_E regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* g_s's bytes [s + 144, s + 148) are addressable at every AR state: a whole granule of the record's zero shadow. *)
Lemma oaf_ra_wk : forall ly S (W : world segs) mem md,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (ONACK_S + 144) 4.
Proof.
intros ly S W mem md HZ HAR x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : ONACK_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= ONACK_S + TW.SZ_g_s)
  by (unfold ONACK_S, TB_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md ONACK_S (ONACK_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The symbolic state at +0x270 holds of the machine state there, and the run's shadow entry holds. *)
Lemma oaf_entry_w : forall ly S (W : world segs) regs mem md,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 19 = w64 ONACK_S -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (oaf_E regs) ss_oafw
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONACK_WK)) mem (YK11.seg_rom segs))) /\
  sh_ok segs OAF_BX OAF_SHW (oaf_E regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md HSC HAR R19 R25.
assert (CS : ONACK_S = 6157888) by reflexivity.
assert (U19 : bv_unsigned (ew (oaf_E regs) 19) = ONACK_S)
  by (rewrite (oaf_ew regs 19 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew (oaf_E regs) 25) = SHADOW_OFF)
  by (rewrite (oaf_ew regs 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_oafw.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold oaf_rg_wk, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (ONACK_S + o) G_HARNESS_B_rw).
    apply oaf_inG_gs. unfold TW.SZ_g_s. lia.
  + apply pairwise_disjoint_of_extents.
    unfold oaf_rg_wk, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold oaf_facts_w, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U25.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (oaf_ra_wk ly S W mem md HSC HAR) as HRA.
  assert (UB : U (oaf_E regs) OAF_BX = SHADOW_OFF).
  { unfold U, OAF_BX. cbn [sv_denot]. rewrite U25, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, OAF_SHW. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ OAF_BX 19 (ONACK_S + 144) 4 ONACK_S 144 148 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The symbolic state at +0x294 holds of the machine state there. *)
Lemma oaf_entry_j : forall (W : world segs) regs mem F,
  YK11.getr regs 23 = w64 (SHADOW_OFF + F / 8) -> 0 <= F < 2 ^ 47 ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (oaf_E regs) ss_oafj
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONACK_JOIN)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F R23 HF Hp.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8.
pose proof (Z.div_lt_upper_bound F 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as HF8'.
assert (U23 : bv_unsigned (ew (oaf_E regs) 23) = SHADOW_OFF + F / 8).
{ rewrite (oaf_ew regs 23 23%bv eq_refl), R23. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
rewrite restrict_mkst_fx. unfold ss_oafj.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold oaf_rg_sh7, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U23.
  split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable segs). apply Hp. lia.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. split; exact I.
- unfold oaf_facts_j, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* trans_tframe_at at a later memory of the walk's own runs, at a smaller window inside the first: the placement
   does not read memory, the bytes and the shadow band are kept. *)
Lemma oaf_tf_move : AR_laws segs B ->
  forall ly2 S2 (W2 : world segs) mem2 md2 mem3 (regs regs' : bvmap 5 word) K K' TF,
  @AR rc segs B ly2 S2 W2 mem2 md2 ->
  trans_tframe_at B ly2 S2 W2 mem2 regs K TF ->
  (forall fr, TF = Some fr -> forall a, TI.tf_addr fr <= a < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) ->
     aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W2) mem3 s = aview segs (w_H W2) mem2 s) ->
  spZ regs - K <= spZ regs' - K' -> spZ regs' <= spZ regs ->
  trans_tframe_at B ly2 S2 W2 mem3 regs' K' TF.
Proof.
intros LAWS ly2 S2 W2 mem2 md2 mem3 regs regs' K K' TF HAR HT KV KS Hw1 Hw2.
destruct TF as [fr|]; [|exact I].
destruct HT as (H0 & Hg & Hs & Hw). specialize (KV fr eq_refl).
split; [exact H0|]. split; [|split].
- apply (garr8_frame segs (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) mem3) _ _ Hg).
  intros a Ha. rewrite length_map in Ha. exact (oaf_mbyte_of_aview _ _ _ a (KV a Ha)).
- exact (trans_src_ok_view B ly2 S2 W2 W2 mem2 mem3 _ _ Hs KV KS).
- unfold decode_off_win in *. lia.
Qed.
End ent.

(* ------------------------------------------------------------------ *)
(* 3. The join, the cut's facts moved, and the piece                    *)
(* ------------------------------------------------------------------ *)

Section main. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The cut's facts at a later memory of the same state whose view differs at most at [s + 144, s + 148) (bytes of G
   in onack_wr Bw b, its wake_acked disjunct). *)
Lemma oaf_cur_step : onack_laws B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 mem3 : word -> option byte) (md2 md3 : Model) (e : Z),
    onack_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F ->
    onack_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2 e ->
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((ONACK_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (ONACK_S + 144 <= a < ONACK_S + 148) ->
       aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
    (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
    onack_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F ly2 S2 W2
  mem2 mem3 md2 md3 e HFIX HCUR HJ3 KD GA.
pose proof HLAWS as (_ & _ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & _ & HGX & _).
pose proof HFIX as (HJe & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EF &
  HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HJ & He & Hfrs & Hperm & HlyF & Hmo & HK & HSV & HFL).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CS : ONACK_S = 6157888) by reflexivity.
unfold ONACK_FBYTES in HFc, HFapp, HFL.
pose proof HJe as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4240 <= ONACK_STK).
{ unfold ONACK_STK, ONACK_FRAME, ONACK_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
assert (Hsp : alloc_ceiling <= spZ regs - 104 /\ spZ regs <= 2 ^ 47) by lia.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJe) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
assert (Hin2 : In (ONACK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFA2 : frame_addr ly2 ONACK_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
refine (conj HJ3 (conj He (conj Hfrs (conj Hperm (conj HlyF (conj Hmo (conj _ (conj _ _)))))))).
- apply (oak_dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2 mem3
    (spZ regs - ONACK_STK) (spZ regs) (onack_wr Bw b) (fun x => ONACK_S + 144 <= x < ONACK_S + 148) HARc HK KD GA).
  + intros a Hz Hc. cbv beta in Hz. exfalso. lia.
  + intros b0 m i _ _ Hz. cbv beta in Hz. right; right; right; left.
    unfold twb_fld, TW.A_S_wake_acked, TW.OFF_g_s. unfold ONACK_S in Hz. lia.
  + intros a Hz _ HnG _ _. cbv beta in Hz. exfalso. apply HnG. apply oaf_inG_gs. unfold TW.SZ_g_s. lia.
  + intros c p a _ _ Hz. cbv beta in Hz. right; right; right; left.
    unfold twb_fld, TW.A_S_wake_acked, TW.OFF_g_s. unfold ONACK_S in Hz. lia.
- apply Forall_forall. intros o Hin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) HSV o Hin) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONACK_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KD; lia.
- unfold ONACK_FBYTES. rewrite <- HFL. apply YCbq.rdword_ext. intros i Hi. apply KD; [lia|]. intros X.
  assert (Hg : inG TG.G_HARNESS_B (F + 256 - 8 + i)) by (apply oaf_inG_gs; unfold TW.SZ_g_s; lia).
  destruct (HGX _ Hg) as [HiG _].
  apply (frm_img segs B LAWS _ _ _ _ _ ONACK_CID pos (F + 256 - 8 + i) HAR2 Hin2); [|exact HiG].
  rewrite EFA2, onack_fbytes. unfold ONACK_FBYTES. lia.
Qed.

(* The join, +0x294 .. +0x2bc: the frame's shadow bytes 4 .. 12 := 0xf8 and `j +0x2e8`, then the release cut. Both
   arms end here: the S_WAKING arm at the state maybe_online returned, the other at the cut's state. What the call
   kept: the state's acall_kept_g over the run (on_ack_seg_kit.v oak_dk_kept_step_gw; the bytes are the own frame's
   shadow, apart from the call's blocks, image and frames: oak_dkg_nf_sep_gw); the saved words, the frame's last word
   and G lie outside the run's window. *)
Lemma oaf_join : @onack_rel_at fx rc B MT -> onack_laws B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly3 : alayout) (S3 : astate)
         (W3 : world segs) (mem3 : word -> option byte) (md3 : Model) (e : Z) (regs3 : bvmap 5 word),
    onack_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F ->
    onack_rel_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw Bw' pos F ly3 S3 W3 mem3 md3 e ->
    onack_regs_rel regs regs3 sp1 F ->
    SRr segs W3 (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + ONACK_JOIN)) mem3 (YK11.seg_rom segs)) md3)
      (@transport_onack_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).
Proof.
intros REL HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F ly3 S3 W3
  mem3 md3 e regs3 HFIX HCUR HREGS.
pose proof HLAWS as (_ & _ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & FFL & HGX & _).
pose proof HFIX as (HJe & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EF &
  HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ & He & Hfrs & Hperm & HlyF & Hmo & HK & HSV & HFL) & Htw & Hgf).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold ONACK_FBYTES in HFc, HFapp, HFL.
pose proof HJe as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4240 <= ONACK_STK).
{ unfold ONACK_STK, ONACK_FRAME, ONACK_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
assert (Hsp : alloc_ceiling <= spZ regs - 104 /\ spZ regs <= 2 ^ 47) by lia.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJe) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR3.
assert (Hin3 : In (ONACK_CID, pos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly3 ONACK_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ ONACK_CID pos HAR3 Hin3) as (_ & _ & _ & HFsh).
change (fs_frame_bytes ONACK_CID / 8) with 32 in HFsh. rewrite EFA in HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity. rewrite ESH in HFsh.
assert (HFr : 0 <= F < 2 ^ 47) by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; lia).
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8p.
pose proof (Z.div_lt_upper_bound F 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as HF8u.
pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8m.
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (oak_dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly3 S3 W3 mem3 md3 ONACK_CID pos F
  (flag_addr lyc ONACK_CID pos) HAR3 Hfrs Hbl HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
(* +0x294 .. +0x2bc in one run, to the release cut *)
pose proof (oaf_entry_j (fx := fx) W3 regs3 mem3 F R23 HFr ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia)))))
  as HS.
assert (SHOK : sh_ok segs OAF_BX [] (oaf_E regs3) (mrestrict (w_H W3) mem3)) by constructor.
assert (HEI : img_env VAL A_LIM (oaf_E regs3)) by (unfold oaf_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oaf_E regs3) n = YK11.getr regs3 r)
  by (intros n r Hn; exact (oaf_ew regs3 n r Hn)).
assert (U23 : bv_unsigned (ew (oaf_E regs3) 23) = SHADOW_OFF + F / 8).
{ rewrite (EE 23%nat 23%bv eq_refl), R23. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK OAF_B0 ONACK_REL.
{ oaf_awr_rs.
  apply (oak_awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ ONACK_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U23 in Ha.
  right. unfold in_zr. cbn [fst snd]. rewrite EFA, ESH. change (fs_frame_bytes ONACK_CID / 8) with 32. lia. }
oaf_name_md md4.
oaf_lo HS (oaf_E regs3) E5lo msF.
(* the registers the release reads, at the cut *)
oaf_kreg HS E5lo EE (2%bv : bv 5) 2%nat R2 X2. oaf_kreg HS E5lo EE (3%bv : bv 5) 3%nat R3 X3.
oaf_kreg HS E5lo EE (4%bv : bv 5) 4%nat R4 X4. oaf_kreg HS E5lo EE (8%bv : bv 5) 8%nat R8 X8.
oaf_kreg HS E5lo EE (9%bv : bv 5) 9%nat R9 X9. oaf_kreg HS E5lo EE (18%bv : bv 5) 18%nat R18 X18.
oaf_kreg HS E5lo EE (23%bv : bv 5) 23%nat R23 X23. oaf_kreg HS E5lo EE (24%bv : bv 5) 24%nat R24 X24.
(* the run wrote the frame's shadow bytes 4 .. 12 only *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 13) ->
  aview segs (w_H W3) (ms_mem msF) a = aview segs (w_H W3) mem3 a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) HFr0);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. cbv beta. oaf_win Hin Hx U23. }
assert (GA : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msF) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
(* what the call keeps, over the run *)
assert (KN : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 (ms_mem msF) (spZ regs - ONACK_STK) (spZ regs)
  (onack_wr Bw b)).
{ apply (oak_dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W3 mem3 (ms_mem msF)
    (spZ regs - ONACK_STK) (spZ regs) (onack_wr Bw b) (dkg_nf ONACK_CID F (flag_addr lyc ONACK_CID pos)) HARc HK).
  - intros a Ha Hn. apply KR; [exact Ha|]. intros X. apply Hn. unfold dkg_nf. right; left.
    change (fs_frame_bytes ONACK_CID / 8) with 32. lia.
  - exact GA.
  - intros a Ha Hc. pose proof (N4 a Ha). lia.
  - intros b0 m i Hb Hi Ha. exfalso. exact (N1 b0 m i Hb Hi Ha).
  - intros a Ha Hi _ _ _. exfalso. exact (N2 a Ha Hi).
  - intros c p a Hc Hr Ha. exfalso. exact (N3 c p a Hc Hr Ha). }
(* the thirteen saved words, the frame's last word and the world, at the run's memory *)
assert (HSVn : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) (ms_mem msF)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONACK_SAVED).
{ apply Forall_forall. intros o Hin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) HSV o Hin) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONACK_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KR; [lia|]. unfold SHADOW_OFF. lia. }
assert (HFLn : rdword (aview segs (w_H W3) (ms_mem msF)) (F + 256 - 8) = Some (flag_addr lyc ONACK_CID pos)).
{ rewrite <- HFL. apply YCbq.rdword_ext. intros i Hi. apply KR; [lia|].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia. }
assert (TWn : tw_at TMAP_B (aview segs (w_H W3) (ms_mem msF)) Bw').
{ apply (tw_kept_GB (aview segs (w_H W3) mem3)); [exact Htw|]. intros b0 n i Hbn Hi.
  assert (Hg : inG TG.G_HARNESS_B (b0 + i))
    by (unfold inG; apply Exists_exists; exists (b0, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  apply KR; [lia | unfold SHADOW_OFF; lia]. }
(* the release cut *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONACK_REL)) mm rom) mdx) Q) end.
apply (REL HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F ly3 S3 W3
  (ms_mem msF) md4 e (ms_regs msF) HFIX).
- unfold onack_rel_cur, onack_cur.
  refine (conj (conj HJ (conj He (conj Hfrs (conj Hperm (conj HlyF (conj Hmo (conj KN (conj HSVn _))))))))
    (conj TWn Hgf)).
  unfold ONACK_FBYTES. exact HFLn.
- exact (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 (conj X23 X24))))))).
Qed.

(* The piece. *)
Lemma oaf_holds : @onack_aft_stmt fx rc B MT.
Proof.
unfold onack_aft_stmt, onack_aft_at.
intros REL HLAWS HMON STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' B2 pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof HLAWS as (_ & _ & HSC & _ & _ & HROU & HRNE & LAWS & MTL & MTF & _ & _ & FFL & HGX & _).
pose proof HFIX as (HJe & _ & _ & Hgp & Htp & _ & _ & Hsp16 & Hwin1 & Hwin2 & _ & Htw0 & _ & Hm & _ & _ & Hapart &
  Hcnt & Hnev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HCUR0 & Htw2 & HTF2 & HROM2 & Hig & Hcn & Hgf2).
pose proof HCUR0 as (HJ1 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R25) & R22 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CS : ONACK_S = 6157888) by reflexivity.
assert (CS' : ONACK_S = TB_g_s) by reflexivity.
assert (EV0 : ONACK_EV = 0) by reflexivity.
assert (EVM : MAYBEON_EV = 0) by reflexivity.
assert (He0 : e = 0) by (rewrite EV0 in He; lia).
assert (ESTK : ONACK_STK = 144 + MAYBEON_STK) by reflexivity.
unfold ONACK_FBYTES in HFc, HFapp, HFLw.
pose proof HJe as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4240 <= ONACK_STK).
{ unfold ONACK_STK, ONACK_FRAME, ONACK_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
assert (Hsp : alloc_ceiling <= spZ regs - ONACK_STK /\ spZ regs <= 2 ^ 47) by lia.
destruct Hsp as [Hspc Hsp47].
(* the realigned sp1 *)
assert (Hsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold ONACK_FRAME.
  pose proof (Z.div_mod (spZ regs - 128) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 128) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 128) / 32) in *. set (r := (spZ regs - 128) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult. }
destruct Hsp1 as [Hsp1 Hsp132].
assert (Hsp116 : sp1 mod 16 = 0).
{ pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp132, Z.add_0_r in D. rewrite D.
  replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
(* the frame at the cut *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJe) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
assert (Hin2 : In (ONACK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Hbl2 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
assert (EFAll : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite HlyF; reflexivity).
assert (EFA2 : frame_addr ly2 ONACK_CID pos = F) by (rewrite EFAll; symmetry; exact EF).
destruct (oak_dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONACK_CID pos F
  (flag_addr lyc ONACK_CID pos) HAR2 Hfrs Hbl2 HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
assert (FNG : forall a, F <= a < F + 256 -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha HGa. destruct (HGX a HGa) as [HiG _].
  exact (frm_img segs B LAWS _ _ _ _ _ ONACK_CID pos a HAR2 Hin2
    ltac:(rewrite EFA2; change (fs_frame_bytes ONACK_CID) with 256; lia) HiG). }
(* the model *)
pose proof (onack_wlen _ _ Htw0) as HLw.
pose proof (onack_wlen _ _ Htw2) as HL2.
destruct (onack_B2_eq _ _ _ _ _ Hcn) as (av & EB2).
pose proof (oaf_model _ _ _ _ _ _ Hig Hm Hcn) as HMOD.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* run A, +0x25c .. +0x26c: the check of s + 112, the load of S_state, a1 = 1; it stops at the `bne` *)
pose proof (oaf_entry_a (fx := fx) B ly2 S2 W2 regs2 mem2 md2 B2 HSC HAR2 Htw2 R22 R27) as HS.
assert (SHOK : sh_ok segs OAF_BX [] (oaf_Ea regs2 B2) (mrestrict (w_H W2) mem2)) by constructor.
assert (HEI : img_env VAL A_LIM (oaf_Ea regs2 B2)) by (unfold oaf_Ea; apply Eimg_env).
assert (EEa : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oaf_Ea regs2 B2) n = YK11.getr regs2 r)
  by (intros n r Hn; exact (oaf_ewa regs2 B2 n r Hn)).
pose proof HJ1 as HJ.
paj_run_tok RUN HS HJ SHOK OAF_B0.
{ oaf_awr_rs.
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
oaf_name_md mdA.
oaf_lo HS (oaf_Ea regs2 B2) EAlo msA.
oaf_reg HS (10%bv : bv 5) (Z_to_bv 64 (TW.S_state B2)) XA10
  ltac:(apply oaf_sext; try rewrite (EAlo 32%nat ltac:(lia)); exact (oaf_ewa32 regs2 B2)).
oaf_reg HS (11%bv : bv 5) (Z_to_bv 64 1) XA11 ltac:(reflexivity).
oaf_kreg HS EAlo EEa (2%bv : bv 5) 2%nat R2 XA2. oaf_kreg HS EAlo EEa (3%bv : bv 5) 3%nat R3 XA3.
oaf_kreg HS EAlo EEa (4%bv : bv 5) 4%nat R4 XA4. oaf_kreg HS EAlo EEa (8%bv : bv 5) 8%nat R8 XA8.
oaf_kreg HS EAlo EEa (9%bv : bv 5) 9%nat R9 XA9. oaf_kreg HS EAlo EEa (18%bv : bv 5) 18%nat R18 XA18.
oaf_kreg HS EAlo EEa (19%bv : bv 5) 19%nat R19 XA19. oaf_kreg HS EAlo EEa (23%bv : bv 5) 23%nat R23 XA23.
oaf_kreg HS EAlo EEa (24%bv : bv 5) 24%nat R24 XA24. oaf_kreg HS EAlo EEa (25%bv : bv 5) 25%nat R25 XA25.
(* run A wrote no byte *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msA) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
  intros b0 wlo whi x Hin Hx. cbv beta. oaf_win Hin Hx EAlo. }
assert (GAa : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msA) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* +0x26c: `bne a0, a1`, taken up again from a state with no region *)
pmkst HS.
clear HS SHOK.
set (rA := ms_regs msA) in *. set (mA := ms_mem msA) in *. clearbody rA mA.
pose proof (oaf_entry0 (fx := fx) W2 rA mA (AF_on_ack + 0x26c)) as HS.
assert (SHOK : sh_ok segs OAF_BX [] (oaf_E rA) (mrestrict (w_H W2) mA)) by constructor.
assert (HEIb : img_env VAL A_LIM (oaf_E rA)) by (unfold oaf_E; apply Eimg_env).
assert (EEb : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oaf_E rA) n = YK11.getr rA r)
  by (intros n r Hn; exact (oaf_ew rA n r Hn)).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + (AF_on_ack + 0x26c))) mm rom) mdx) Q) end.
assert (D10 : sv_denot (oaf_E rA) (SOff 10 0) = Z_to_bv 64 (TW.S_state B2))
  by (cbn [sv_denot]; rewrite (EEb 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact XA10).
assert (D11 : sv_denot (oaf_E rA) (SOff 11 0) = Z_to_bv 64 1)
  by (cbn [sv_denot]; rewrite (EEb 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact XA11).
pose proof (oaf_state_range B2) as HSR.
psrr_branch_tok RUN BR HS SHOK OAF_B0.
- (* S_state B2 <> S_WAKING: to the join +0x294; the model's world is B2 *)
  cbn [branch_taken] in Hc. rewrite D10, D11, (oaf_eqb1 _ HSR) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (EBw' : Bw' = B2).
  { replace (TW.S_state B2 =? TS0.DIGINET_S_WAKING) with false in HMOD
      by (symmetry; apply Z.eqb_neq; exact Hc).
    exact HMOD. }
  paj_run_to_tok RUNTO HS HJ SHOK OAF_B0 ONACK_JOIN.
  { oaf_awr_rs. apply awr_ok_x_nil. }
  oaf_name_md mdB.
  oaf_lo HS (oaf_E rA) EBlo msB.
  oaf_kreg HS EBlo EEb (2%bv : bv 5) 2%nat XA2 Y2. oaf_kreg HS EBlo EEb (3%bv : bv 5) 3%nat XA3 Y3.
  oaf_kreg HS EBlo EEb (4%bv : bv 5) 4%nat XA4 Y4. oaf_kreg HS EBlo EEb (8%bv : bv 5) 8%nat XA8 Y8.
  oaf_kreg HS EBlo EEb (9%bv : bv 5) 9%nat XA9 Y9. oaf_kreg HS EBlo EEb (18%bv : bv 5) 18%nat XA18 Y18.
  oaf_kreg HS EBlo EEb (23%bv : bv 5) 23%nat XA23 Y23. oaf_kreg HS EBlo EEb (24%bv : bv 5) 24%nat XA24 Y24.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W2) mem2 a).
  { intros a Ha. rewrite <- (KA a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta. oaf_win Hin Hx EBlo. }
  assert (GB : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msB) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAa a Ha))).
  pose proof (oaf_cur_step HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos
    sp1 F ly2 S2 W2 mem2 (ms_mem msB) md2 mdB e HFIX HCUR0 HJ ltac:(intros a Ha _; exact (KB a Ha)) GB) as CUR.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONACK_JOIN)) mm rom) mdx) Q) end.
  apply (oaf_join REL HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 (ms_mem msB) mdB e (ms_regs msB) HFIX).
  + refine (conj CUR (conj _ _)).
    * rewrite EBw'. apply (tw_kept_GB (aview segs (w_H W2) mem2)); [exact Htw2|]. intros b0 n i Hbn Hi.
      assert (Hg : inG TG.G_HARNESS_B (b0 + i))
        by (unfold inG; apply Exists_exists; exists (b0, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
      pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
      apply KB. lia.
    * rewrite EBw'. exact Hgf2.
  + exact (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 (conj Y23 Y24))))))).
- (* S_state B2 = S_WAKING: the store of 1 at s + 144, then maybe_online *)
  cbn [branch_taken] in Hc. rewrite D10, D11, (oaf_eqb1 _ HSR) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Pmod : TSS.maybe_online_m timg_B TF (TW.set_S_wake_acked B2 1) = Some (Bw', tt)).
  { replace (TW.S_state B2 =? TS0.DIGINET_S_WAKING) with true in HMOD
      by (symmetry; apply Z.eqb_eq; exact Hc).
    exact HMOD. }
  paj_run_to_tok RUNTO HS HJ SHOK OAF_B0 ONACK_WK.
  { oaf_awr_rs. apply awr_ok_x_nil. }
  oaf_name_md mdB.
  oaf_lo HS (oaf_E rA) EBlo msB.
  oaf_kreg HS EBlo EEb (2%bv : bv 5) 2%nat XA2 Y2. oaf_kreg HS EBlo EEb (3%bv : bv 5) 3%nat XA3 Y3.
  oaf_kreg HS EBlo EEb (4%bv : bv 5) 4%nat XA4 Y4. oaf_kreg HS EBlo EEb (8%bv : bv 5) 8%nat XA8 Y8.
  oaf_kreg HS EBlo EEb (9%bv : bv 5) 9%nat XA9 Y9. oaf_kreg HS EBlo EEb (18%bv : bv 5) 18%nat XA18 Y18.
  oaf_kreg HS EBlo EEb (19%bv : bv 5) 19%nat XA19 Y19. oaf_kreg HS EBlo EEb (23%bv : bv 5) 23%nat XA23 Y23.
  oaf_kreg HS EBlo EEb (24%bv : bv 5) 24%nat XA24 Y24. oaf_kreg HS EBlo EEb (25%bv : bv 5) 25%nat XA25 Y25.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W2) mem2 a).
  { intros a Ha. rewrite <- (KA a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta. oaf_win Hin Hx EBlo. }
  assert (GB : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msB) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAa a Ha))).
  clear HF HFr HG.
  (* run W, +0x270 .. +0x290: the check of s + 144, the store of 1 at s + 144, a0 = s, `jal maybe_online` *)
  pmkst HS.
  clear HS SHOK.
  set (rB := ms_regs msB) in *. set (mB := ms_mem msB) in *. clearbody rB mB.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARB.
  destruct (oaf_entry_w (fx := fx) B ly2 S2 W2 rB mB mdB HSC HARB Y19 Y25) as [HS SHOK].
  assert (HEIw : img_env VAL A_LIM (oaf_E rB)) by (unfold oaf_E; apply Eimg_env).
  assert (EEw : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oaf_E rB) n = YK11.getr rB r)
    by (intros n r Hn; exact (oaf_ew rB n r Hn)).
  assert (U19w : bv_unsigned (ew (oaf_E rB) 19) = ONACK_S)
    by (rewrite (EEw 19%nat 19%bv eq_refl), Y19; apply unsigned_lit_small; lia).
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONACK_WK)) mm rom) mdx) Q) end.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { oaf_awr_rs.
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19w in Ha;
      apply oaf_inG_gs; unfold TW.SZ_g_s; lia |].
    apply awr_ok_x_nil. }
  oaf_name_md mdW.
  oaf_lo HS (oaf_E rB) EWlo msW.
  (* the registers at maybe_online's entry *)
  oaf_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 30080)) W1 ltac:(apply codeptr_val; assumption).
  oaf_kreg HS EWlo EEw (2%bv : bv 5) 2%nat Y2 W2'. oaf_kreg HS EWlo EEw (3%bv : bv 5) 3%nat Y3 W3'.
  oaf_kreg HS EWlo EEw (4%bv : bv 5) 4%nat Y4 W4'. oaf_kreg HS EWlo EEw (8%bv : bv 5) 8%nat Y8 W8'.
  oaf_kreg HS EWlo EEw (9%bv : bv 5) 9%nat Y9 W9'. oaf_kreg HS EWlo EEw (18%bv : bv 5) 18%nat Y18 W18'.
  oaf_kreg HS EWlo EEw (23%bv : bv 5) 23%nat Y23 W23'. oaf_kreg HS EWlo EEw (24%bv : bv 5) 24%nat Y24 W24'.
  oaf_kreg_of HS EWlo EEw (10%bv : bv 5) 19%nat (19%bv : bv 5) Y19 W10'.
  (* the run wrote [s + 144, s + 148) only, with 1 *)
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (ONACK_S + 144 <= a < ONACK_S + 148) ->
    aview segs (w_H W2) (ms_mem msW) a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hn. rewrite <- (KB a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun x => ONACK_S + 144 <= x < ONACK_S + 148) HFr); [| exact Ha | exact Hn].
    intros b0 wlo whi x Hin Hx. cbv beta. oaf_win Hin Hx U19w. }
  assert (GW : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msW) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GB a Ha))).
  oaf_region HS 0%nat HRw.
  lazymatch type of HRw with region_ok _ ?Ex _ (YP09.mkRegion _ _ _ _ _ [YP09.mkChunk _ (CVal _ ?ev)]) =>
    assert (DEN : sv_denot Ex ev = Z_to_bv 64 1) by (cbn [sv_denot]; reflexivity);
    assert (U19f : bv_unsigned (ew Ex 19) = ONACK_S) by (try rewrite (EWlo 19%nat ltac:(lia)); exact U19w);
    pose proof (can_field_of_region Ex _ 19 ONACK_S _ 144 148 144 148 144 4%N ev 1 HRw U19f ltac:(oaf_in) DEN
      ltac:(cbn; lia) ltac:(cbn; lia)) as VB
  end.
  change (N.to_nat 4) with 4%nat in VB.
  clear HRw DEN U19f.
  set (mW := ms_mem msW) in *. set (rW := ms_regs msW) in *.
  (* the cut's facts at the call's memory *)
  pose proof (oaf_cur_step HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos
    sp1 F ly2 S2 W2 mem2 mW md2 mdW e HFIX HCUR0 HJ KW GW) as CURW.
  pose proof CURW as (_ & _ & _ & _ & _ & _ & KCw & HSVw & HFLww).
  unfold ONACK_FBYTES in HFLww.
  (* the world after the store of :234 *)
  assert (TWw : tw_at TMAP_B (aview segs (w_H W2) mW) (TW.set_S_wake_acked B2 1)).
  { rewrite oaf_wake_at.
    apply (tw_write TMAP_B (aview segs (w_H W2) mem2) (aview segs (w_H W2) mW) B2 TW.OFF_g_s TB_g_s TW.SZ_g_s
      144 4 1 TMAP_B_ok Htw2 TMAP_B_g_s); [lia | unfold TW.SZ_g_s; lia | |].
    - intros j Hj. rewrite <- CS'. exact (oaf_aview_of_val _ _ _ 4 _ VB j Hj).
    - intros x Hx Hn.
      assert (Hg : inG TG.G_HARNESS_B x).
      { destruct Hx as (o & b0 & n & Hin & Hb). pose proof (TMAP_B_in_G o b0 n Hin) as HG0.
        unfold inG. apply Exists_exists. exists (b0, n). split; [exact HG0 | unfold in_zr; cbn [fst snd]; lia]. }
      pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX Hg) as Hl. unfold kLowMemEnd in Hl.
      apply KW; [lia|]. intros X. apply Hn. rewrite <- CS'. lia. }
  (* maybe_online's premises *)
  assert (NSP : spZ rW = sp1) by (unfold spZ; rewrite W2'; unfold w64; apply unsigned_lit_small; lia).
  assert (EBR : BASE + 30080 = 0x88820) by (vm_compute; reflexivity).
  assert (Pret : YK0s.ret_ok (YK11.getr rW 1))
    by (rewrite W1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity]).
  assert (Pra4 : 4096 <= raZ rW) by (unfold raZ; rewrite W1, EBR, unsigned_lit_small by lia; lia).
  assert (Pgp : YK11.getr rW 3 = w64 (as_gp B)) by (rewrite W3'; exact Hgp).
  assert (Ptp : YK11.getr rW 4 = w64 (as_tp B)) by (rewrite W4'; exact Htp).
  assert (Pa0 : YK11.getr rW 10 = w64 MAYBEON_S) by exact W10'.
  assert (Psp16 : spZ rW mod 16 = 0) by (rewrite NSP; exact Hsp116).
  assert (Pwin1 : sp0 - STK <= spZ rW - MAYBEON_STK) by (rewrite NSP; lia).
  assert (Pwin2 : spZ rW <= sp0) by (rewrite NSP; lia).
  assert (Pgf : TW.g_fail_next (TW.set_S_wake_acked B2 1) <= 1)
    by (rewrite (proj1 (onack_wake_fail B2 1 HL2)); exact Hgf2).
  assert (Ptf : trans_tframe_at B ly2 S2 W2 mW rW MAYBEON_STK TF).
  { apply (oaf_tf_move B LAWS ly2 S2 W2 mem2 md2 mW regs rW ONACK_STK MAYBEON_STK TF HAR2 HTF2).
    - intros fr Efr a Ha. rewrite Efr in HTF2. destruct HTF2 as (_ & _ & Hs & _).
      destruct (trans_src_ok_place B LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hs ltac:(lia)) as [Hp | Hp];
        (apply KW; [lia|]; intros Hx;
         apply (Hapart a ltac:(right; right; right; left; unfold twb_fld, TW.A_S_wake_acked, TW.OFF_g_s;
                               unfold ONACK_S in Hx; lia) fr Efr Ha)).
    - intros s Hs. apply KW; [unfold kHighShadowEnd in Hs; lia | unfold kLowMemEnd in Hs; lia].
    - rewrite NSP. lia.
    - rewrite NSP. lia. }
  assert (Prom : trans_rom_view_rd W2 mW).
  { intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Rb. rewrite (KW a ltac:(lia) ltac:(lia)). exact (HROM2 a Ha). }
  assert (Pap : maybeon_apart TF (TW.set_S_wake_acked B2 1)).
  { intros x Hx fr Efr.
    assert (Hw : onack_wr Bw b x).
    { unfold onack_wr. right; right; right; right. rewrite EB2 in Hx. exact (oaf_wr_cong Bw av x HLw Hx). }
    exact (Hapart x Hw fr Efr). }
  assert (Pcnt : count_cid MAYBEON_CID (frames S2) < fs_frames MAYBEON_CID).
  { rewrite Hfrs. change MAYBEON_CID with 2. change ONACK_CID with 2 in Hcnt |- *.
    cbn [count_cid]. rewrite Z.eqb_refl. lia. }
  assert (Pnev : st_nev S + (k + e) + MAYBEON_EV <= EV_MAX) by (rewrite EVM, He0; rewrite EV0 in Hnev; lia).
  (* +0x290: maybe_online, in the same G journal *)
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (@cfg_at fx sg (transportb_sigma TB_maybe_online) rg mm mdx) Q) end.
  eapply SRr_bind.
  { exact (HMON fx STK sp0 FP ly S W0 mem0 md0 ((ONACK_CID, pos) :: own) ly2 S2 W2 mW mdW (k + e) rW TF
      (TW.set_S_wake_acked B2 1) Bw' HJ Pret Pra4 Pgp Ptp Pa0 Psp16 Pwin1 Pwin2 TWw Pgf Pmod Ptf Prom Pap Pcnt Pnev). }
  intros W3 c3 _ HPOST.
  unfold transport_maybeon_post, transport_cg_post in HPOST.
  destruct HPOST as (ly3 & S3 & regs5 & mem5 & md6 & e' & -> & He' & HJ6 & HP6 & Hfr6 & Hperm6 & HK6 & Hmo6 & Htw6 & Hgf6).
  rewrite NSP in HK6.
  (* the state maybe_online returned: the cut's facts there *)
  assert (ELF3 : ly_F ly3 = ly_F lyc).
  { pose proof HJ6 as (_ & _ & (memS6 & HJ6i & _) & _). pose proof HJ6i as (_ & Hly3 & _).
    pose proof Hly3 as (_ & _ & _ & _ & _ & E3 & _). pose proof Hlyc as (_ & _ & _ & _ & _ & Ec & _).
    rewrite E3, Ec. reflexivity. }
  assert (K5 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem5 (spZ regs - ONACK_STK) (spZ regs)
    (onack_wr Bw b)).
  { assert (Hce1 : alloc_ceiling <= spZ regs - ONACK_STK) by exact Hspc.
    assert (Hlo1 : spZ regs <= 2 ^ 64) by lia.
    apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 mW W3 mem5
      (spZ regs - ONACK_STK) (spZ regs) (sp1 - MAYBEON_STK) sp1 (onack_wr Bw b)
      (maybeon_wr (TW.set_S_wake_acked B2 1)) (dkg_nf ONACK_CID F (flag_addr lyc ONACK_CID pos))
      Hce1 Hlo1 EFAll ltac:(intros f Hf; rewrite Hfrs; right; exact Hf) Hbl2 N1 N3 KCw HK6).
    - lia.
    - lia.
    - intros a Ha. left. unfold onack_wr. right; right; right; right.
      rewrite EB2 in Ha. exact (oaf_wr_cong Bw av a HLw Ha). }
  assert (HSV5 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem5) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONACK_SAVED).
  { apply Forall_forall. intros o Hin. cbv beta.
    pose proof (proj1 (Forall_forall _ _) HSVw o Hin) as Hv. cbv beta in Hv.
    assert (Ho : 8 <= fst o <= 104).
    { unfold ONACK_SAVED in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
    rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. destruct HK6 as (L1 & _). apply L1; lia. }
  assert (HFL5 : rdword (aview segs (w_H W3) mem5) (F + 256 - 8) = Some (flag_addr lyc ONACK_CID pos)).
  { rewrite <- HFLww. apply YCbq.rdword_ext. intros i Hi. destruct HK6 as (_ & _ & _ & L4 & _).
    apply (L4 ONACK_CID pos (F + 256 - 8 + i) Hin2).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA2. change (fs_frame_bytes ONACK_CID) with 256. lia.
    - intros Hw. exact (FNG (F + 256 - 8 + i) ltac:(lia) (oaf_mwr_G _ _ Hw)). }
  rewrite W1.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONACK_JOIN)) mm rom) mdx) Q) end.
  apply (oaf_join REL HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F
    ly3 S3 W3 mem5 md6 (e + e') regs5 HFIX).
  + unfold onack_rel_cur, onack_cur.
    refine (conj (conj _ (conj _ (conj _ (conj _ (conj ELF3 (conj _ (conj K5 (conj HSV5 _))))))))
      (conj Htw6 Hgf6)).
    * replace (k + (e + e')) with (k + e + e') by lia. exact HJ6.
    * rewrite EV0. rewrite EVM in He'. lia.
    * rewrite Hfr6. exact Hfrs.
    * exact (Permutation_trans Hperm6 Hperm).
    * exact (mo_le_trans MT MTL Sc S2 S3 0 0 Hmo Hmo6).
    * unfold ONACK_FBYTES. exact HFL5.
  + unfold onack_regs_rel.
    split; [exact (eq_trans (HP6 2 ltac:(hnf; lia)) W2')|].
    split; [exact (eq_trans (HP6 3 ltac:(hnf; lia)) W3')|].
    split; [exact (eq_trans (HP6 4 ltac:(hnf; lia)) W4')|].
    split; [exact (eq_trans (HP6 8 ltac:(hnf; lia)) W8')|].
    split; [exact (eq_trans (HP6 9 ltac:(hnf; lia)) W9')|].
    split; [exact (eq_trans (HP6 18 ltac:(hnf; lia)) W18')|].
    split; [exact (eq_trans (HP6 23 ltac:(hnf; lia)) W23')|].
    exact (eq_trans (HP6 24 ltac:(hnf; lia)) W24').
Qed.
End main.

(* The after-notice piece of the walk of on_ack (on_ack_segs.v onack_aft_stmt), at every machine, run ceiling, record
   and meter. *)
Lemma onack_aft_piece : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT, @onack_aft_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@oaf_holds fx rc B MT). Qed.

Print Assumptions onack_aft_piece.
