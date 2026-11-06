(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths, module names and numbers changed; 1344 of its 1469 lines of code are new or changed and 905 lines of the source are left out. *)
(* m_rx_seg_data: the DATA segment of the image-A walk of m_rx (statement lib/A/Prog/m_rx_cg.v, kit
   lib/A/Prog/m_rx_seg_kit.v). Exported: mrx_seg_data, from the TICK cut's continuation to the DATA cut's: from the DATA
   cut (0x84c88, cmd DATA, the model's mrx_data) the code reaches the TICK cut (0x84e1c) at the model's world.

   This file cuts the segment twice more, with cuts of the kit's form (mrx_at / mrx_K at MRX_PC off with a local R):
     D5 0x84cf8 (+0x46c)  the desk counter, the model from mrx_data5 (R_D5);
     D6 0x84d20 (+0x494)  OW.dn[OW.ndata] and OW.ndata, the model from mrx_data6 (R_D6).
   Each part is the kit's symbolic run (TransportGRunA.v paj_run_to_x over the inner journal) from a state built at
   its cut, split at each branch the run cannot decide, and closed at the next cut's mrx_K:
     DATA (0x84c88 .. 0x84cf4): a1 = byte 18 (the spill at sp + 8) and bytes 19, 20, 21 (s11, s5, the spill at sp + 32)
       form send, big-endian and sign-extended; a3 = retry = s7 << 8 | s8; a2 = &OW; OW.acks + 1 stored at OW + 204, 0 at
       M + 88 (fail); retry <> 0: g_cfg.backoff_ms * 1000 + g_now stored at M + 56 (backoff_until; the region of these
       8 bytes joins the state on that side only); M.desk_counter_valid <> 0, retry <> 0 and send = M.desk_counter
       goes to TICK (the model's duplicate), else to D5.
     D5 (0x84cf8 .. 0x84d1c): 1 stored at M + 76, send at M + 80; body_len <> 1 goes to D6. body_len = 1 (a case of
       the proof, before the run): the frame byte fa + 30 is a read-only region and the run's shadow entry is
       [fa + 30, fa + 31) (addressable: decode_rd_ok of the frame, n >= 31); the check of the 1-byte load at fa + 30
       is decided by it, so errpath_load1 (0x84f0c) is not reached; byte 0 goes to TICK, else to D6.
     D6 (0x84d20 .. 0x84da0): k = OW.ndata (signed); 1 < k: k + 1 stored at OW + 220, to TICK. Else 0 <= k (the
       model's None below 0), so k = 0 or k = 1, pinned; OW.dn[k]'s 22 bytes join the state as a writable region of G
       and the four checked stores at OW + 256 + 24 k (+ 0, + 8, + 16, + 20) are decided by the run's shadow entry of
       OW's 304 bytes (zero shadow, trans_mrx_cells), so errpath_store8 (0x84f34, 0x84f3c), errpath_store4 (0x84f20)
       and errpath_store2 (0x84f30) are not reached; k + 1 stored at OW + 220; to TICK.
   At each cut the world relation is the kit's mrx_tw_start / mrx_tw_step / mrx_tw_end over the part's stores (their
   bytes read from the chunks of the last state); every other payload byte is kept (a run writes only its regions). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  m_lost_cg m_wake_cg m_maybe_online_cg m_tick_cg desk_named_cg check_state_data_cg m_rx_cg m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
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
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The model                                                           *)
(* ------------------------------------------------------------------ *)

Lemma mrxd_some_inv : forall x y : list byte, Some (x, tt) = Some (y, tt) -> y = x.
Proof. intros x y H. injection H as H. symmetry. exact H. Qed.

(* The worlds of mrx_data: B1 after OW.acks and M.fail, B4 after the backoff, B5 after the desk counter, B6 after
   OW.dn[k]. *)
Definition mrxd_B1 (B : list byte) : list byte := TW.set_M_fail (TW.set_OW_acks B (TW.OW_acks B + 1)) 0.
Definition mrxd_bkv (B : list byte) : Z := TS0.u64 (TW.g_now B + TC.h_ms_m (TW.Cfg_backoff_ms B)).
Definition mrxd_B4 (fr : TI.tframe) (B : list byte) : list byte :=
  if TC.truth (EPI.mrx_retry fr) then TW.set_M_backoff_until (mrxd_B1 B) (mrxd_bkv (mrxd_B1 B)) else mrxd_B1 B.
Definition mrxd_B5 (fr : TI.tframe) (B : list byte) : list byte :=
  TW.set_M_desk_counter_valid (TW.set_M_desk_counter B (EPI.mrx_send fr)) 1.
Definition mrxd_B6 (fr : TI.tframe) (B : list byte) (k : Z) : list byte :=
  TC.set_OW_dn_retry (TC.set_OW_dn_counter (TC.set_OW_dn_len (TC.set_OW_dn_body B k (TI.tf_addr fr + 30))
    k (EPI.mrx_blen fr)) k (EPI.mrx_send fr)) k (EPI.mrx_retry fr).

Lemma mrxd_data_inv : forall fr B B3, EPI.mrx_data fr B = Some (B3, tt) ->
  TW.OW_acks B <> TC.INT_MAX /\ EPI.mrx_data4 fr (mrxd_B4 fr B) = Some (B3, tt).
Proof.
intros fr B B3 H. unfold EPI.mrx_data, TC.int_inc in H. revert H.
destruct (Z.eqb_spec (TW.OW_acks B) TC.INT_MAX) as [E|E]; intros H; [discriminate H|].
split; [exact E | exact H].
Qed.

Lemma mrxd_data4_tick : forall fr B4 B3,
  TC.truth (TW.M_desk_counter_valid B4) && (EPI.mrx_send fr =? TW.M_desk_counter B4) &&
    TC.truth (EPI.mrx_retry fr) = true ->
  EPI.mrx_data4 fr B4 = Some (B3, tt) -> B3 = B4.
Proof. intros fr B4 B3 Hc H. unfold EPI.mrx_data4 in H. rewrite Hc in H. exact (mrxd_some_inv _ _ H). Qed.

Lemma mrxd_data4_d5 : forall fr B4 B3,
  TC.truth (TW.M_desk_counter_valid B4) && (EPI.mrx_send fr =? TW.M_desk_counter B4) &&
    TC.truth (EPI.mrx_retry fr) = false ->
  EPI.mrx_data4 fr B4 = Some (B3, tt) -> EPI.mrx_data5 fr B4 = Some (B3, tt).
Proof. intros fr B4 B3 Hc H. unfold EPI.mrx_data4 in H. rewrite Hc in H. exact H. Qed.

Lemma mrxd_data5_tick : forall fr B4 B3, EPI.mrx_blen fr = 1 -> DSpec.at8 (EPI.mrx_body fr) 0 = 0 ->
  EPI.mrx_data5 fr B4 = Some (B3, tt) -> B3 = mrxd_B5 fr B4.
Proof.
intros fr B4 B3 H1 H2 H. unfold EPI.mrx_data5 in H. rewrite H1, H2 in H.
replace ((1 =? 1) && (0 =? 0)) with true in H by reflexivity. exact (mrxd_some_inv _ _ H).
Qed.

Lemma mrxd_data5_d6 : forall fr B4 B3,
  ((EPI.mrx_blen fr =? 1) && (DSpec.at8 (EPI.mrx_body fr) 0 =? 0)) = false ->
  EPI.mrx_data5 fr B4 = Some (B3, tt) -> EPI.mrx_data6 fr (mrxd_B5 fr B4) = Some (B3, tt).
Proof. intros fr B4 B3 Hc H. unfold EPI.mrx_data5 in H. rewrite Hc in H. exact H. Qed.

Lemma mrxd_data6_hi : forall fr B5 B3, 2 <= TW.OW_ndata B5 -> EPI.mrx_data6 fr B5 = Some (B3, tt) ->
  TW.OW_ndata B5 <> TC.INT_MAX /\ B3 = TW.set_OW_ndata B5 (TW.OW_ndata B5 + 1).
Proof.
intros fr B5 B3 Hk H. unfold EPI.mrx_data6, TC.int_inc in H.
replace (TW.OW_ndata B5 <? 2) with false in H by (symmetry; apply Z.ltb_ge; lia). cbv beta iota in H. revert H.
destruct (Z.eqb_spec (TW.OW_ndata B5) TC.INT_MAX) as [E|E]; intros H; [discriminate H|].
split; [exact E | exact (mrxd_some_inv _ _ H)].
Qed.

Lemma mrxd_data6_lo : forall fr B5 B3, TW.OW_ndata B5 < 2 -> EPI.mrx_data6 fr B5 = Some (B3, tt) ->
  0 <= TW.OW_ndata B5 /\ B3 = TW.set_OW_ndata (mrxd_B6 fr B5 (TW.OW_ndata B5)) (TW.OW_ndata B5 + 1).
Proof.
intros fr B5 B3 Hk H. unfold EPI.mrx_data6, TC.int_inc in H.
replace (TW.OW_ndata B5 <? 2) with true in H by (symmetry; apply Z.ltb_lt; lia). revert H.
destruct (Z.ltb_spec (TW.OW_ndata B5) 0) as [L|L]; intros H; [discriminate H|].
replace (TW.OW_ndata B5 =? TC.INT_MAX) with false in H by (symmetry; apply Z.eqb_neq; unfold TC.INT_MAX; lia).
split; [exact L | exact (mrxd_some_inv _ _ H)].
Qed.

(* World lengths and the fields the code reads back. *)
Lemma mrxd_len_put : forall B k (m : nat) v, length B = Z.to_nat TW.W_LEN -> 0 <= k -> k + Z.of_nat m <= TW.W_LEN ->
  length (TW.upd B k (TW.put m v)) = Z.to_nat TW.W_LEN.
Proof. intros B k m v HL Hk Hkm. rewrite TWL.length_upd_put; [exact HL | exact Hk | rewrite HL, Z2Nat.id; [exact Hkm | unfold TW.W_LEN; lia]]. Qed.

Lemma mrxd_u_out : forall B k (m : nat) v k' (n : nat), length B = Z.to_nat TW.W_LEN -> 0 <= k -> 0 <= k' ->
  k + Z.of_nat m <= TW.W_LEN -> (k' + Z.of_nat n <= k \/ k + Z.of_nat m <= k') ->
  TW.u_at (TW.upd B k (TW.put m v)) k' n = TW.u_at B k' n.
Proof.
intros B k m v k' n HL Hk Hk' Hkm Hd. apply TWL.u_at_upd_out; [exact Hk | exact Hk' | rewrite TWL.length_put; exact Hd |].
rewrite TWL.length_put, HL, Z2Nat.id; [exact Hkm | unfold TW.W_LEN; lia].
Qed.

Lemma mrxd_B1_len : forall B, length B = Z.to_nat TW.W_LEN -> length (mrxd_B1 B) = Z.to_nat TW.W_LEN.
Proof.
intros B HL. unfold mrxd_B1, TW.set_M_fail, TW.set_OW_acks, TW.A_M_fail, TW.A_OW_acks, TW.OFF_M, TW.OFF_OW.
apply mrxd_len_put; [apply mrxd_len_put; [exact HL | lia | unfold TW.W_LEN; lia] | lia | unfold TW.W_LEN; lia].
Qed.

Lemma mrxd_B1_now : forall B, length B = Z.to_nat TW.W_LEN -> TW.g_now (mrxd_B1 B) = TW.g_now B.
Proof.
intros B HL. unfold mrxd_B1, TW.g_now, TW.set_M_fail, TW.set_OW_acks, TW.A_M_fail, TW.A_OW_acks.
assert (L1 : length (TW.upd B (TW.OFF_OW + 204) (TW.put 4 (TW.OW_acks B + 1))) = Z.to_nat TW.W_LEN)
  by (apply mrxd_len_put; [exact HL | unfold TW.OFF_OW; lia | unfold TW.OFF_OW, TW.W_LEN; lia]).
rewrite (mrxd_u_out _ _ 4 _ _ 8 L1) by (unfold TW.OFF_M, TW.OFF_g_now, TW.W_LEN; cbn; lia).
rewrite (mrxd_u_out _ _ 4 _ _ 8 HL) by (unfold TW.OFF_OW, TW.OFF_g_now, TW.W_LEN; cbn; lia).
reflexivity.
Qed.

Lemma mrxd_B1_bms : forall B, length B = Z.to_nat TW.W_LEN -> TW.Cfg_backoff_ms (mrxd_B1 B) = TW.Cfg_backoff_ms B.
Proof.
intros B HL. unfold mrxd_B1, TW.Cfg_backoff_ms, TW.A_Cfg_backoff_ms, TW.set_M_fail, TW.set_OW_acks, TW.A_M_fail,
  TW.A_OW_acks.
assert (L1 : length (TW.upd B (TW.OFF_OW + 204) (TW.put 4 (TW.OW_acks B + 1))) = Z.to_nat TW.W_LEN)
  by (apply mrxd_len_put; [exact HL | unfold TW.OFF_OW; lia | unfold TW.OFF_OW, TW.W_LEN; lia]).
rewrite (mrxd_u_out _ _ 4 _ _ 4 L1) by (unfold TW.OFF_M, TW.OFF_g_cfg, TW.W_LEN; cbn; lia).
rewrite (mrxd_u_out _ _ 4 _ _ 4 HL) by (unfold TW.OFF_OW, TW.OFF_g_cfg, TW.W_LEN; cbn; lia).
reflexivity.
Qed.

(* M.desk_counter_valid and M.desk_counter of B4 are B's (the stores are at M + 88, OW + 204, M + 56). *)
Lemma mrxd_B4_u : forall fr B k', length B = Z.to_nat TW.W_LEN -> TW.OFF_M + 76 <= k' -> k' + 4 <= TW.OFF_M + 84 ->
  TW.u_at (mrxd_B4 fr B) k' 4 = TW.u_at B k' 4.
Proof.
intros fr B k' HL H1 H2. pose proof (mrxd_B1_len B HL) as L1.
assert (L0 : length (TW.upd B (TW.OFF_OW + 204) (TW.put 4 (TW.OW_acks B + 1))) = Z.to_nat TW.W_LEN)
  by (apply mrxd_len_put; [exact HL | unfold TW.OFF_OW; lia | unfold TW.OFF_OW, TW.W_LEN; lia]).
assert (E1 : TW.u_at (mrxd_B1 B) k' 4 = TW.u_at B k' 4).
{ unfold mrxd_B1, TW.set_M_fail, TW.set_OW_acks, TW.A_M_fail, TW.A_OW_acks.
  rewrite (mrxd_u_out _ _ 4 _ _ 4 L0) by (unfold TW.OFF_M, TW.W_LEN in *; cbn; lia).
  rewrite (mrxd_u_out _ _ 4 _ _ 4 HL) by (unfold TW.OFF_M, TW.OFF_OW, TW.W_LEN in *; cbn; lia).
  reflexivity. }
unfold mrxd_B4. destruct (TC.truth (EPI.mrx_retry fr)); [|exact E1].
unfold TW.set_M_backoff_until, TW.A_M_backoff_until.
rewrite (mrxd_u_out _ _ 8 _ _ 4 L1) by (unfold TW.OFF_M, TW.W_LEN in *; cbn; lia). exact E1.
Qed.

(* ------------------------------------------------------------------ *)
(* Bytes and the values the code computes                              *)
(* ------------------------------------------------------------------ *)

Lemma mrxd_le_eqm : forall a b (w j : nat), a mod 2 ^ (8 * Z.of_nat w) = b mod 2 ^ (8 * Z.of_nat w) ->
  YO0f.le_byte a w j = YO0f.le_byte b w j.
Proof. intros a b w j H. unfold YO0f.le_byte. rewrite H. reflexivity. Qed.

Lemma mrxd_le_sw32 : forall v j, YO0f.le_byte (bv_swrap 32 v) 4 j = YO0f.le_byte v 4 j.
Proof. intros v j. apply mrxd_le_eqm. change (8 * Z.of_nat 4) with 32. apply EPI.mrx_swrap_mod. Qed.

Lemma mrxd_mfb_range : forall fr k, 0 <= mfb fr k < 256.
Proof.
intros fr k. unfold mfb, DSpec.byte_at, TW.zs.
destruct (Nat.lt_ge_cases (Z.to_nat k) (length (TI.tf_bytes fr))) as [Hl|Hl].
- rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hl).
  rewrite map_nth. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k) (TI.tf_bytes fr) (Z_to_bv 8 0))) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R.
- rewrite nth_overflow by (rewrite length_map; exact Hl). lia.
Qed.

Lemma mrxd_mfb_byte : forall fr k, 0 <= k < mlen fr -> mfb fr k = EPI.mrx_byte (TI.tf_bytes fr) k.
Proof. intros fr k Hk. unfold mfb. apply EPI.mrx_byte_at; unfold mlen in Hk; lia. Qed.

Lemma mrxd_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma mrxd_den_or : forall E a b,
  sv_denot E (SAlu ALU_OR a b) = Z_to_bv 64 (Z.lor (bv_unsigned (sv_denot E a)) (bv_unsigned (sv_denot E b))).
Proof.
intros E a b. cbn [sv_denot alu64 alu].
pose proof (bv_unsigned_in_range 64 (bv_or (sv_denot E a) (sv_denot E b))) as R. rewrite bv_or_unsigned in R.
apply bv_eq. rewrite bv_or_unsigned, Z_to_bv_unsigned. symmetry. apply bv_wrap_small. exact R.
Qed.

Lemma mrxd_den_sll8 : forall E a,
  sv_denot E (SAlu ALU_SLL a (SLit 8)) = Z_to_bv 64 (bv_unsigned (sv_denot E a) ≪ 8).
Proof.
intros E a. cbn [sv_denot alu64 alu]. apply bv_eq. rewrite bv_shiftl_unsigned, Z_to_bv_unsigned.
rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity.
Qed.

Lemma mrxd_den_sll16 : forall E a,
  sv_denot E (SAlu ALU_SLL a (SLit 16)) = Z_to_bv 64 (bv_unsigned (sv_denot E a) ≪ 16).
Proof.
intros E a. cbn [sv_denot alu64 alu]. apply bv_eq. rewrite bv_shiftl_unsigned, Z_to_bv_unsigned.
rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity.
Qed.

Lemma mrxd_den_sllw24 : forall E a x, sv_denot E a = Z_to_bv 64 x -> 0 <= x < 256 ->
  sv_denot E (SAluw ALU_SLL a (SLit 24)) = Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) ≪ 24)).
Proof.
intros E a x H Hx. cbn [sv_denot alu32 alu low32]. rewrite H. rewrite LMem.sext_small. f_equal.
unfold bv_signed. rewrite bv_shiftl_unsigned.
assert (A24 : bv_unsigned (bv_and (bv_extract 0 32 (Z_to_bv 64 24)) (Z_to_bv 32 31)) = 24).
{ rewrite bv_and_unsigned, (LMem.extract_low_mod 32 (Z_to_bv 64 24)) by lia. rewrite !Z_to_bv_unsigned. reflexivity. }
unfold low32.
rewrite A24. rewrite (LMem.extract_low_mod 32 (Z_to_bv 64 x)) by lia.
rewrite (unsigned_lit_small x) by lia. change (Z.of_N 32) with 32. rewrite (Z.mod_small x (2 ^ 32)) by lia.
rewrite Z.shiftl_mul_pow2 by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
f_equal. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma mrxd_den_sext32 : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
change (sext 64 (bv_extract 0 32 (Z_to_bv 64 u))) with (Z_to_bv 64 (bv_signed (bv_extract 0 32 (Z_to_bv 64 u)))).
f_equal. rewrite (LMem.signed_of_extract 32 (Z_to_bv 64 u)) by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma mrxd_den_zext : forall E n u (w : N), ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ Z.of_N w -> (0 < w <= 64)%N ->
  sv_denot E (SExt false w (SOff n 0)) = Z_to_bv 64 u.
Proof.
intros E n u w Hn Hu Hw. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite LMem.zext_small. f_equal. rewrite (LMem.extract_low_mod w (Z_to_bv 64 u)) by lia.
assert (Hu64 : 0 <= u < 2 ^ 64).
{ split; [lia|]. apply (Z.lt_le_trans _ (2 ^ Z.of_N w)); [lia | apply Z.pow_le_mono_r; lia]. }
rewrite unsigned_lit_small by exact Hu64. apply Z.mod_small. exact Hu.
Qed.

Lemma mrxd_den_add1 : forall E a x, sv_denot E a = Z_to_bv 64 x ->
  sv_denot E (SAlu ALU_ADD a (SLit 1)) = Z_to_bv 64 (x + 1).
Proof.
intros E a x H. cbn [sv_denot alu64 alu]. rewrite H. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

(* retry = s7 << 8 | s8 (bytes 26, 27). *)
Definition MRXD_RETRY : sv := SAlu ALU_OR (SAlu ALU_SLL (SOff 23 0) (SLit 8)) (SOff 24 0).
(* send = (s11 << 16 | sllw (sp + 8), 24) | s5 << 8 | (sp + 32) (bytes 19, 18, 20, 21), sign-extended. *)
Definition MRXD_SEND : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 27 0) (SLit 16)) (SAluw ALU_SLL (SOff 32 0) (SLit 24)))
    (SAlu ALU_SLL (SOff 21 0) (SLit 8))) (SOff 33 0).

Lemma mrxd_retry_range : forall fr, 0 <= EPI.mrx_retry fr < 65536.
Proof. intros fr. unfold EPI.mrx_retry. apply EPI.mrx_be16_range. Qed.

Lemma mrxd_send_range : forall fr, 22 <= mlen fr -> 0 <= EPI.mrx_send fr < 2 ^ 32.
Proof. intros fr Hl. unfold EPI.mrx_send. apply EPI.mrx_be32_range; unfold mlen in Hl; lia. Qed.

Lemma mrxd_retry_den : forall E fr, 28 <= mlen fr ->
  ew E 23 = Z_to_bv 64 (mfb fr 26) -> ew E 24 = Z_to_bv 64 (mfb fr 27) ->
  sv_denot E MRXD_RETRY = Z_to_bv 64 (EPI.mrx_retry fr).
Proof.
intros E fr Hl H23 H24. unfold MRXD_RETRY. rewrite mrxd_den_or, mrxd_den_sll8.
rewrite (mrxd_den_atom E 23 _ H23), (mrxd_den_atom E 24 _ H24).
pose proof (mrxd_mfb_range fr 26) as R6. pose proof (mrxd_mfb_range fr 27) as R7.
rewrite !(unsigned_lit_small (mfb fr _)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
rewrite unsigned_lit_small by lia.
rewrite (StrFun.lor_add (mfb fr 26 * 2 ^ 8) (mfb fr 27) 8) by (try lia; rewrite Z_mod_mult; reflexivity).
unfold EPI.mrx_retry. rewrite EPI.mrx_be16 by (unfold mlen in Hl; lia).
rewrite <- !mrxd_mfb_byte by lia. reflexivity.
Qed.

Lemma mrxd_send_den : forall E fr, 22 <= mlen fr ->
  ew E 27 = Z_to_bv 64 (mfb fr 19) -> ew E 32 = Z_to_bv 64 (mfb fr 18) ->
  ew E 21 = Z_to_bv 64 (mfb fr 20) -> ew E 33 = Z_to_bv 64 (mfb fr 21) ->
  sv_denot E MRXD_SEND = Z_to_bv 64 (bv_swrap 32 (EPI.mrx_send fr)).
Proof.
intros E fr Hl H27 H32 H21 H33. unfold MRXD_SEND.
pose proof (mrxd_mfb_range fr 18) as R8. pose proof (mrxd_mfb_range fr 19) as R9.
pose proof (mrxd_mfb_range fr 20) as R0. pose proof (mrxd_mfb_range fr 21) as R1.
rewrite !mrxd_den_or, mrxd_den_sll16, mrxd_den_sll8.
rewrite (mrxd_den_sllw24 E (SOff 32 0) (mfb fr 18) (mrxd_den_atom E 32 _ H32) R8).
rewrite (mrxd_den_atom E 27 _ H27), (mrxd_den_atom E 21 _ H21), (mrxd_den_atom E 33 _ H33).
rewrite (EPI.mrx_asm_be32b (mfb fr 18) (mfb fr 19) (mfb fr 20) (mfb fr 21) R8 R9 R0 R1).
unfold EPI.mrx_send. rewrite EPI.mrx_be32 by (unfold mlen in Hl; lia).
rewrite <- !mrxd_mfb_byte by lia. reflexivity.
Qed.

Lemma mrxd_bk_den : forall E g u, ew E 10 = Z_to_bv 64 g -> ew E 37 = Z_to_bv 64 u ->
  0 <= g < 2 ^ 64 -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SExt false 32 (SOff 37 0)) (SLit 1000)) (SOff 10 0)) =
  Z_to_bv 64 (TS0.u64 (g + TC.h_ms_m u)).
Proof.
intros E g u H10 H37 Hg Hu.
change (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SExt false 32 (SOff 37 0)) (SLit 1000)) (SOff 10 0))) with
  (alu64 ALU_ADD (mul_div M_MUL (sv_denot E (SExt false 32 (SOff 37 0))) (sv_denot E (SLit 1000)))
     (sv_denot E (SOff 10 0))).
rewrite (mrxd_den_zext E 37 u 32 H37 Hu ltac:(lia)), (mrxd_den_atom E 10 g H10).
cbn [sv_denot alu64 alu mul_div]. apply bv_eq.
rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned.
unfold TS0.u64, TC.h_ms_m, TS0.u64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small u (2 ^ 64)) by lia. rewrite (Z.mod_small 1000 (2 ^ 64)) by lia.
rewrite (Z.mod_small g (2 ^ 64)) by lia. rewrite Zmod_mod.
rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. f_equal. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* The cuts of this file                                               *)
(* ------------------------------------------------------------------ *)

Definition OFF_D5 : Z := 0x46c.
Definition OFF_D6 : Z := 0x494.

(* The frame byte fa + 30 (read on the body_len = 1 path): its value and its shadow. *)
Definition mrxd_fb (fr : TI.tframe) (Wc : world tfibsegs) (mem : word -> option byte) : Prop :=
  31 <= mlen fr ->
  YI04.val_mem tfibsegs (mrestrict (w_H Wc) mem) (TI.tf_addr fr + 30) 1 (mfb fr 30) /\
  range_addressable (aview tfibsegs (w_H Wc) mem) SHADOW_OFF (TI.tf_addr fr + 30) 1.

(* D5 (0x84cf8, after the duplicate test): s0 = fa + 30, a2 = &OW, a3 = retry, a4 = send (sign-extended),
   s2 = the shadow base, s3 = &M, s4 = body_len; the model from mrx_data5, then m_tick. *)
Definition R_D5 (fr : TI.tframe) (n : Z) (lyc : alayout) (Sc : astate) (Bw' : list byte) (r : Z) :
    world tfibsegs -> list byte -> alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    ly2 = lyc /\ S2 = Sc /\ mrxd_fb fr Wc mem2 /\ mrx_hdr fr n /\
    amem_range (TI.tf_addr fr) (mlen fr) /\ 0 <= TI.tf_addr fr /\
    YK11.getr regs2 8 = Z_to_bv 64 (TI.tf_addr fr + 30) /\ YK11.getr regs2 12 = Z_to_bv 64 TA_OW /\
    YK11.getr regs2 13 = Z_to_bv 64 (EPI.mrx_retry fr) /\
    YK11.getr regs2 14 = Z_to_bv 64 (bv_swrap 32 (EPI.mrx_send fr)) /\
    YK11.getr regs2 18 = Z_to_bv 64 SHADOW_OFF /\ YK11.getr regs2 19 = Z_to_bv 64 TA_M /\
    YK11.getr regs2 20 = Z_to_bv 64 (EPI.mrx_blen fr) /\
    exists B3, EPI.mrx_data5 fr Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* D6 (0x84d20): a0 = 1, s0 = fa + 30, a2 = &OW, a3 = retry, a4 = send (sign-extended), s2 = the shadow base,
   s4 = body_len; the model from mrx_data6, then m_tick. *)
Definition R_D6 (fr : TI.tframe) (lyc : alayout) (Sc : astate) (Bw' : list byte) (r : Z) :
    world tfibsegs -> list byte -> alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    ly2 = lyc /\ S2 = Sc /\ 22 <= mlen fr /\
    YK11.getr regs2 8 = Z_to_bv 64 (TI.tf_addr fr + 30) /\ YK11.getr regs2 10 = Z_to_bv 64 1 /\
    YK11.getr regs2 12 = Z_to_bv 64 TA_OW /\ YK11.getr regs2 13 = Z_to_bv 64 (EPI.mrx_retry fr) /\
    YK11.getr regs2 14 = Z_to_bv 64 (bv_swrap 32 (EPI.mrx_send fr)) /\
    YK11.getr regs2 18 = Z_to_bv 64 SHADOW_OFF /\ YK11.getr regs2 20 = Z_to_bv 64 (EPI.mrx_blen fr) /\
    exists B3, EPI.mrx_data6 fr Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

Definition MRXD_Bx : sv := SOff 18 0.

(* D6: atom 32 = OW.ndata's 4 bytes as an unsigned int. a0 is pinned to 1. *)
Definition d6_nd : YP09.region := YP09.mkRegion (Some 12%nat) 220 224 220 224 [YP09.mkChunk 220 (CVal 4 (SOff 32 0))].
Definition d6_dn (k : Z) : YP09.region :=
  YP09.mkRegion (Some 12%nat) (256 + 24 * k) (278 + 24 * k) (256 + 24 * k) (278 + 24 * k) [].
Definition d6_facts : facts := mkFacts [(12%nat, mkAF TA_OW TA_OW 5); (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_d6 : sstate := mkSS (AF_m_rx + OFF_D6) sr_atoms [d6_nd] None d6_facts.
Definition SH6 : list shent := [mkSHE 12 0 304].

(* D5: M.desk_counter_valid and M.desk_counter, written. body_len = 1: atom 32 = the frame byte fa + 30, a
   read-only region at s0 (atom 8), s4 (atom 20) = 1, and the shadow entry [fa + 30, fa + 31). *)
Definition d5_dcv : YP09.region := YP09.mkRegion (Some 19%nat) 76 80 76 80 [].
Definition d5_dc : YP09.region := YP09.mkRegion (Some 19%nat) 80 84 80 84 [].
Definition d5_fb : YP09.region := YP09.mkRegion (Some 8%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition d5n_facts : facts := mkFacts [(18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (19%nat, mkAF TA_M TA_M 5)] [] [].
Definition d5o_facts : facts :=
  mkFacts [(8%nat, mkAF 30 (2 ^ 47 - 2) 0); (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (19%nat, mkAF TA_M TA_M 5);
           (20%nat, mkAF 1 1 0)] [] [].
Definition ss_d5n : sstate := mkSS (AF_m_rx + OFF_D5) sr_atoms [d5_dcv; d5_dc] None d5n_facts.
Definition ss_d5o : sstate := mkSS (AF_m_rx + OFF_D5) sr_atoms [d5_dcv; d5_dc; d5_fb] None d5o_facts.
Definition SH5 : list shent := [mkSHE 8 0 1].

(* The world after D5's stores: M.desk_counter = send, M.desk_counter_valid = 1. *)
Lemma mrxd_world5 : forall Bw rdF rd0 send,
  tw_at TMAP_A rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 80 + Z.of_nat j) = Some (YO0f.le_byte send 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 76 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_M + 76 <= x < TA_M + 84) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.set_M_desk_counter_valid (TW.set_M_desk_counter Bw send) 1).
Proof.
intros Bw rdF rd0 send Htw VC VV Hk.
unfold TW.set_M_desk_counter_valid, TW.set_M_desk_counter.
pose proof (mrx_tw_start rdF rd0 Bw Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 80 TW.A_M_desk_counter 4 send H0 TMAP_A_M
  ltac:(unfold TW.A_M_desk_counter; lia) ltac:(lia) ltac:(unfold TW.SZ_M; lia) VC) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 76 TW.A_M_desk_counter_valid 4 1 H1 TMAP_A_M
  ltac:(unfold TW.A_M_desk_counter_valid; lia) ltac:(lia) ltac:(unfold TW.SZ_M; lia) VV) as H2.
apply (mrx_tw_end rdF rd0 _ _ H2). intros x Hx HP. mrx_unP HP. apply Hk; [exact Hx | lia].
Qed.

(* The bytes M and OW the code stores into lie apart from the frame byte fa + 30 (mrx_apart: they are bytes of
   mrx_wr). *)
Lemma mrxd_apart30 : forall fr, mrx_apart fr -> 31 <= mlen fr -> forall x,
  (TA_M + 56 <= x < TA_M + 64 \/ TA_M + 76 <= x < TA_M + 84 \/ TA_M + 88 <= x < TA_M + 92 \/
   TA_OW + 204 <= x < TA_OW + 208) -> x <> TI.tf_addr fr + 30.
Proof.
intros fr Hap Hl x Hx Heq. apply (Hap x); [| unfold mlen in Hl; lia].
unfold mrx_wr. destruct Hx as [Hx|[Hx|[Hx|Hx]]].
- do 8 right; left. unfold twa_fld, TW.A_M_backoff_until. lia.
- destruct (Z_lt_le_dec x (TA_M + 80)) as [Hx1|Hx1].
  + do 9 right; left. unfold twa_fld, TW.A_M_desk_counter_valid. lia.
  + do 10 right; left. unfold twa_fld, TW.A_M_desk_counter. lia.
- do 11 right; left. unfold twa_fld, TW.A_M_fail. lia.
- do 16 right; left. unfold twa_fld, TW.A_OW_acks. lia.
Qed.

(* The first body byte, as the model reads it. *)
Lemma mrxd_at8 : forall fr, 31 <= mlen fr -> DSpec.at8 (EPI.mrx_body fr) 0 = mfb fr 30.
Proof.
intros fr Hl. unfold EPI.mrx_body. rewrite EPI.mrx_at8 by (unfold mlen in Hl; lia).
rewrite (mrxd_mfb_byte fr 30) by lia. reflexivity.
Qed.

Lemma mrxd_fa30_out : forall fr x, mrx_apart fr -> 31 <= mlen fr -> x = TI.tf_addr fr + 30 ->
  ~ (TA_M + 56 <= x < TA_M + 64) /\ ~ (TA_M + 76 <= x < TA_M + 84) /\ ~ (TA_M + 88 <= x < TA_M + 92) /\
  ~ (TA_OW + 204 <= x < TA_OW + 208).
Proof.
intros fr x Hap Hl ->. split; [|split; [|split]]; intros Hx;
  apply (mrxd_apart30 fr Hap Hl (TI.tf_addr fr + 30)); try reflexivity; tauto.
Qed.

(* DATA: atoms 32 = byte 18 (the spill at sp + 8), 33 = byte 21 (the spill at sp + 32), and the 4 bytes as unsigned
   ints of 34 = M.desk_counter_valid, 35 = M.desk_counter, 36 = OW.acks, 37 = g_cfg.backoff_ms. The 8 bytes of
   M.backoff_until (mrxd_bk) join the state on the retry <> 0 side. *)
Definition mrxd_stk : YP09.region :=
  YP09.mkRegion (Some 2%nat) 8 40 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0))].
Definition mrxd_dcvR : YP09.region := YP09.mkRegion (Some 19%nat) 76 80 0 0 [YP09.mkChunk 76 (CVal 4 (SOff 34 0))].
Definition mrxd_dcR : YP09.region := YP09.mkRegion (Some 19%nat) 80 84 0 0 [YP09.mkChunk 80 (CVal 4 (SOff 35 0))].
Definition mrxd_fail : YP09.region := YP09.mkRegion (Some 19%nat) 88 92 88 92 [].
Definition mrxd_acks : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 12)) 204 208 204 208 [YP09.mkChunk 204 (CVal 4 (SOff 36 0))].
Definition mrxd_bms : YP09.region := YP09.mkRegion (Some (A_OBJ 49)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 37 0))].
Definition mrxd_bk : YP09.region := YP09.mkRegion (Some 19%nat) 56 64 56 64 [].
Definition data_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (19%nat, mkAF TA_M TA_M 5);
           (A_OBJ 12, mkAF TA_OW TA_OW 5)] [] [].
Definition ss_data : sstate :=
  mkSS (AF_m_rx + OFF_DATA) sr_atoms [mrxd_stk; mrxd_dcvR; mrxd_dcR; mrxd_fail; mrxd_acks; mrxd_bms] None data_facts.

Lemma mrxd_B4_0 : forall fr B, TC.truth (EPI.mrx_retry fr) = false -> mrxd_B4 fr B = mrxd_B1 B.
Proof. intros fr B H. unfold mrxd_B4. rewrite H. reflexivity. Qed.
Lemma mrxd_B4_1 : forall fr B, TC.truth (EPI.mrx_retry fr) = true ->
  mrxd_B4 fr B = TW.set_M_backoff_until (mrxd_B1 B) (mrxd_bkv (mrxd_B1 B)).
Proof. intros fr B H. unfold mrxd_B4. rewrite H. reflexivity. Qed.

(* The world after DATA's stores: OW.acks, M.fail; with the backoff, also M.backoff_until. *)
Lemma mrxd_world1 : forall Bw rdF rd0 ak,
  tw_at TMAP_A rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 204 + Z.of_nat j) = Some (YO0f.le_byte ak 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_OW + 204 <= x < TA_OW + 208) -> ~ (TA_M + 88 <= x < TA_M + 92) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.set_M_fail (TW.set_OW_acks Bw ak) 0).
Proof.
intros Bw rdF rd0 ak Htw VA VF Hk. unfold TW.set_M_fail, TW.set_OW_acks.
pose proof (mrx_tw_start rdF rd0 Bw Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 204 TW.A_OW_acks 4 ak H0 TMAP_A_OW
  ltac:(unfold TW.A_OW_acks; lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) VA) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 88 TW.A_M_fail 4 0 H1 TMAP_A_M
  ltac:(unfold TW.A_M_fail; lia) ltac:(lia) ltac:(unfold TW.SZ_M; lia) VF) as H2.
apply (mrx_tw_end rdF rd0 _ _ H2). intros x Hx HP. mrx_unP HP. apply Hk; [exact Hx | lia | lia].
Qed.

Lemma mrxd_world4 : forall Bw rdF rd0 ak bk,
  tw_at TMAP_A rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 204 + Z.of_nat j) = Some (YO0f.le_byte ak 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 8)%nat -> rdF (TA_M + 56 + Z.of_nat j) = Some (YO0f.le_byte bk 8 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_OW + 204 <= x < TA_OW + 208) -> ~ (TA_M + 88 <= x < TA_M + 92) ->
     ~ (TA_M + 56 <= x < TA_M + 64) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.set_M_backoff_until (TW.set_M_fail (TW.set_OW_acks Bw ak) 0) bk).
Proof.
intros Bw rdF rd0 ak bk Htw VA VF VB Hk. unfold TW.set_M_backoff_until, TW.set_M_fail, TW.set_OW_acks.
pose proof (mrx_tw_start rdF rd0 Bw Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 204 TW.A_OW_acks 4 ak H0 TMAP_A_OW
  ltac:(unfold TW.A_OW_acks; lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) VA) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 88 TW.A_M_fail 4 0 H1 TMAP_A_M
  ltac:(unfold TW.A_M_fail; lia) ltac:(lia) ltac:(unfold TW.SZ_M; lia) VF) as H2.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 56 TW.A_M_backoff_until 8 bk H2 TMAP_A_M
  ltac:(unfold TW.A_M_backoff_until; lia) ltac:(lia) ltac:(unfold TW.SZ_M; lia) VB) as H3.
apply (mrx_tw_end rdF rd0 _ _ H3). intros x Hx HP. mrx_unP HP. apply Hk; [exact Hx | lia | lia | lia].
Qed.

(* M's and OW's payload bytes are bytes of G. *)
Lemma mrxd_inG : forall a, (TA_M <= a < TA_M + 1648) \/ (TA_OW <= a < TA_OW + 304) -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. destruct Ha as [Ha|Ha].
- exists (TA_M, TW.SZ_M). split; [exact (TMAP_A_in_G _ _ _ TMAP_A_M) | unfold in_zr, TW.SZ_M; cbn [fst snd]; lia].
- exists (TA_OW, TW.SZ_OW). split; [exact (TMAP_A_in_G _ _ _ TMAP_A_OW) | unfold in_zr, TW.SZ_OW; cbn [fst snd]; lia].
Qed.

(* Ltac helpers *)
Ltac mrxd_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "mrxd_reg: no match for" T; fail
  end.

Ltac mrxd_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

Ltac mrxd_awr2 U1 U2 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia | rewrite ?U1, ?U2 in Ha; right; left; apply mrxd_inG; lia ] |]);
  apply awr_ok_x_nil.
Ltac mrxd_awr U :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia | rewrite ?U in Ha; right; left; apply mrxd_inG; lia ] |]);
  apply awr_ok_x_nil.

Lemma mrxd_Forall_nth : forall {A : Type} (P : A -> Prop) (l : list A) (n : nat) (x : A),
  Forall P l -> nth_error l n = Some x -> P x.
Proof. intros A P l n x HF Hn. rewrite Forall_forall in HF. apply HF. exact (nth_error_In l n Hn). Qed.

(* The bytes of the chunk number c of region number idx of the state of HS, base rewritten by UB. *)
Ltac mrxd_chunk HS idx c UB v Hden V :=
  let RG := fresh "RG" in let HC := fresh "HC" in let HC1 := fresh "HCk" in
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict ?Hh ?m) =>
    pose proof (st_ok_pi_region_nth EF _ (restrict Hh m) idx _ HS eq_refl) as RG end;
  cbn [ms_mem restrict] in RG;
  destruct RG as (_ & _ & _ & HC);
  cbn [YP09.r_base YP09.r_chunks base_val] in HC;
  rewrite UB in HC;
  pose proof (mrxd_Forall_nth _ _ c _ HC eq_refl) as HC1;
  pose proof (mrx_chunk_rd _ _ _ _ _ _ _ v HC1 Hden ltac:(cbn; lia)) as V;
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V;
  clear HC HC1.

(* After a run: the model term of the goal named md. *)
Ltac mrxd_md md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md := m) in *; clearbody md end.

(* sp, gp, tp of the state of HS are the cut's (regs rg; EE reads the entry valuation; HE moves a later one). *)
Ltac mrxd_regs3 HS EE rg F2 F3 F4 :=
  mrxd_reg HS (2%bv : bv 5) (YK11.getr rg 2%bv) F2
    ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  mrxd_reg HS (3%bv : bv 5) (YK11.getr rg 3%bv) F3
    ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  mrxd_reg HS (4%bv : bv 5) (YK11.getr rg 4%bv) F4
    ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
Ltac mrxd_regs3E HS EE HE rg F2 F3 F4 :=
  mrxd_reg HS (2%bv : bv 5) (YK11.getr rg 2%bv) F2
    ltac:(cbn [sv_denot]; rewrite HE by lia; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  mrxd_reg HS (3%bv : bv 5) (YK11.getr rg 3%bv) F3
    ltac:(cbn [sv_denot]; rewrite HE by lia; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  mrxd_reg HS (4%bv : bv 5) (YK11.getr rg 4%bv) F4
    ltac:(cbn [sv_denot]; rewrite HE by lia; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).

(* A register q (the atom k) the run kept: its value is the cut's. *)
Ltac mrxd_keep HS EE rg q k Q :=
  mrxd_reg HS (q : bv 5) (YK11.getr rg q) Q
    ltac:(cbn [sv_denot]; rewrite (EE k q eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
Ltac mrxd_keepE HS EE HE rg q k Q :=
  mrxd_reg HS (q : bv 5) (YK11.getr rg q) Q
    ltac:(cbn [sv_denot]; rewrite HE by lia; rewrite (EE k q eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).

(* The world after D6's stores at k = i (0 or 1): OW.dn[i]'s four fields and OW.ndata. *)
Lemma mrxd_world6 : forall Bw rdF rd0 i body blen send retry nd,
  tw_at TMAP_A rd0 Bw -> 0 <= i <= 1 ->
  (forall j, (j < 8)%nat -> rdF (TA_OW + (256 + 24 * i) + Z.of_nat j) = Some (YO0f.le_byte body 8 j)) ->
  (forall j, (j < 8)%nat -> rdF (TA_OW + (264 + 24 * i) + Z.of_nat j) = Some (YO0f.le_byte blen 8 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + (272 + 24 * i) + Z.of_nat j) = Some (YO0f.le_byte send 4 j)) ->
  (forall j, (j < 2)%nat -> rdF (TA_OW + (276 + 24 * i) + Z.of_nat j) = Some (YO0f.le_byte retry 2 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 220 + Z.of_nat j) = Some (YO0f.le_byte nd 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_OW + 220 <= x < TA_OW + 224) ->
     ~ (TA_OW + 256 + 24 * i <= x < TA_OW + 278 + 24 * i) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.set_OW_ndata (TC.set_OW_dn_retry (TC.set_OW_dn_counter (TC.set_OW_dn_len
    (TC.set_OW_dn_body Bw i body) i blen) i send) i retry) nd).
Proof.
intros Bw rdF rd0 i body blen send retry nd Htw Hi VB VL VS VR VN Hk.
unfold TW.set_OW_ndata, TC.set_OW_dn_retry, TC.set_OW_dn_counter, TC.set_OW_dn_len, TC.set_OW_dn_body.
pose proof (mrx_tw_start rdF rd0 Bw Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW (256 + 24 * i) (TC.A_OW_dn_body i) 8 body H0 TMAP_A_OW
  ltac:(unfold TC.A_OW_dn_body; lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) VB) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW (264 + 24 * i) (TC.A_OW_dn_len i) 8 blen H1 TMAP_A_OW
  ltac:(unfold TC.A_OW_dn_len; lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) VL) as H2.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW (272 + 24 * i) (TC.A_OW_dn_counter i) 4 send H2 TMAP_A_OW
  ltac:(unfold TC.A_OW_dn_counter; lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) VS) as H3.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW (276 + 24 * i) (TC.A_OW_dn_retry i) 2 retry H3 TMAP_A_OW
  ltac:(unfold TC.A_OW_dn_retry; lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) VR) as H4.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 220 TW.A_OW_ndata 4 nd H4 TMAP_A_OW
  ltac:(unfold TW.A_OW_ndata; lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) VN) as H5.
apply (mrx_tw_end rdF rd0 _ _ H5). intros x Hx HP. mrx_unP HP. apply Hk; [exact Hx | lia | lia].
Qed.

Section seg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis HMRX : trans_mrx_cells B.
Hypothesis HRO : trans_ro_rd_unowned B.
Hypothesis HNE : trans_rom_no_errno B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok tfibsegs B TG.G_HARNESS.
Hypothesis HGNE : gx_noerrno B TG.G_HARNESS.
Hypothesis HBCMP : forall fx' : YK11.FPState, @abcmp_realizes fx' rc tfibsegs B (transport_sigma TS___interceptor_trampoline_bcmp).
Hypothesis HMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc tfibsegs B OCpy (transport_sigma TS___asan_memcpy).
Hypothesis HML : forall fx' : YK11.FPState, @transport_m_lost_cg fx' rc B MT (transport_sigma TS_m_lost).
Hypothesis HDN : forall fx' : YK11.FPState, @transport_desk_named_cg fx' rc B MT (transport_sigma TS_desk_named).
Hypothesis HMW : forall fx' : YK11.FPState, @transport_m_wake_cg fx' rc B MT (transport_sigma TS_m_wake).
Hypothesis HMO : forall fx' : YK11.FPState, @transport_m_maybe_online_cg fx' rc B MT (transport_sigma TS_m_maybe_online).
Hypothesis HMT : forall fx' : YK11.FPState, @transport_m_tick_cg fx' rc B MT (transport_sigma TS_m_tick).
Variable sp1 : Z.
Variable regs0 : bvmap 5 word.
Variable lyc : alayout.
Variable Sc : astate.
Variable W : world tfibsegs.
Variable memc : word -> option byte.
Variable mdc : Model.
Variable fr : TI.tframe.
Variable n : Z.
Variable Bw' : list byte.
Variable r : Z.
Hypothesis HST : mrx_static B sp1 regs0 lyc Sc W memc mdc fr n.
Local Notation K := (@mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r).

Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma mrxd_vals : VAL (A_OBJ 12) = TA_OW /\ VAL (A_OBJ 49) = TA_g_cfg + 36.
Proof. vm_compute. split; reflexivity. Qed.

Lemma mrxd_pc : forall off, BASE + (AF_m_rx + off) = MRX_PC off.
Proof.
intros off. unfold MRX_PC. replace (transport_sigma TS_m_rx) with (BASE + AF_m_rx) by (vm_compute; reflexivity). lia.
Qed.

Lemma mrxd_pcl : forall off k, AF_m_rx + off = k -> BASE + k = MRX_PC off.
Proof. intros off k <-. apply mrxd_pc. Qed.

(* OW.dn[i]'s 22 bytes, a writable region of G at any memory. *)
Lemma mrxd_dn_ok : forall E (m : word -> option byte) i, bv_unsigned (ew E 12) = TA_OW -> 0 <= i <= 1 ->
  region_ok segs E m (d6_dn i).
Proof.
intros E m i HU Hi. assert (EO : TA_OW = 6238304) by reflexivity.
unfold d6_dn, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HU. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw). apply mrxd_inG. lia.
Qed.

(* OW's 304 bytes are addressable at every AR state (trans_mrx_cells: OW's 38 granules have shadow 0). *)
Lemma mrxd_ra_ow : forall ly S (Wx : world segs) mem md, @AR rc segs B ly S Wx mem md ->
  range_addressable (aview segs (w_H Wx) mem) SHADOW_OFF TA_OW 304.
Proof.
intros ly S Wx mem md HAR x Hx. destruct HMRX as (HZ & _).
assert (EO : TA_OW = 6238304) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold shadow_of_addr.
exists 0. split; [|left; reflexivity].
assert (Hz := decode_zshadow_rd B ly S Wx mem md TA_OW (TA_OW + TW.SZ_OW) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
replace (SHADOW_OFF + x / 8) with (ACells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold ACells.shadow_addr, ACells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Lemma mrxd_shok6 : forall ly S (Wx : world segs) mem md (E : env), @AR rc segs B ly S Wx mem md ->
  bv_unsigned (ew E 12) = TA_OW -> ew E 18 = Z_to_bv 64 SHADOW_OFF ->
  sh_ok segs MRXD_Bx SH6 E (mrestrict (w_H Wx) mem).
Proof.
intros ly S Wx mem md E HAR U12 E18.
assert (EO : TA_OW = 6238304) by reflexivity.
unfold sh_ok, SH6. constructor; [|constructor].
apply (shent_ok_of_range segs (w_H Wx) mem E MRXD_Bx 12 TA_OW 304 TA_OW 0 304 (mrxd_ra_ow ly S Wx mem md HAR)).
- unfold U, MRXD_Bx. cbn [sv_denot]. rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U12.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The cut at a run's end: the continuation of the next cut applied to its mrx_at. *)
Lemma mrxd_exit : forall pc (R : world segs -> list byte -> alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Prop)
    (Wc : world segs) Bwc regs2 mem2 regsF memF mdF,
  K pc R ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc Wc memF mdF 0 ->
  mo_le MT Sc Sc 0 ->
  YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK11.getr regs2 3 = YK11.getr regs0 3 -> YK11.getr regs2 4 = YK11.getr regs0 4 ->
  YK11.getr regsF 2 = YK11.getr regs2 2 -> YK11.getr regsF 3 = YK11.getr regs2 3 ->
  YK11.getr regsF 4 = YK11.getr regs2 4 ->
  @mrx_saved Wc mem2 sp1 regs0 ->
  (forall a, sp1 - 104 <= a < sp1 -> aview segs (w_H Wc) memF a = aview segs (w_H Wc) mem2 a) ->
  tw_at TMAP_A (aview segs (w_H Wc) memF) Bwc ->
  R Wc Bwc lyc Sc regsF memF ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 pc) memF (YK11.seg_rom segs)) mdF)
    (mrx_ipost B MT sp1 regs0 lyc Sc W memc mdc Bw' r).
Proof.
intros pc R Wc Bwc regs2 mem2 regsF memF mdF HK HJ Hmo Hsp Hgp Htp F2 F3 F4 Hsv Hkp Htw HR.
apply (HK Wc Bwc).
apply (mrx_at_intro B MT sp1 regs0 lyc Sc W memc mdc pc R Wc Bwc lyc Sc regsF memF mdF); try assumption.
- reflexivity.
- apply Permutation_refl.
- rewrite F2. exact Hsp.
- rewrite F3. exact Hgp.
- rewrite F4. exact Htp.
- exact (mrx_saved_kept Wc Wc mem2 memF sp1 regs0 Hsv Hkp).
Qed.

(* ------------------------------------------------------------------ *)
(* D6: OW.dn[OW.ndata], OW.ndata                                       *)
(* ------------------------------------------------------------------ *)

Lemma mrxd_seg_d6 : K (MRX_PC OFF_TICK) (R_TICK Bw' r) -> K (MRX_PC OFF_D6) (R_D6 fr lyc Sc Bw' r).
Proof.
intros HKT. unfold mrx_K at 1. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hperm & Hmo & Hsp & Hgp & Htp & Hsv & Htw & HR).
destruct HR as (-> & -> & Hl22 & R8 & R10 & R12 & R13 & R14 & R18 & R20 & B3 & Hm & Htk & Hr).
pose proof HST as (Hsp1 & Hsp16 & Hceil & Hlo & Hhi & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
assert (EM : TA_M = 6156640) by reflexivity. assert (EO : TA_OW = 6238304) by reflexivity.
assert (FR : MRX_FRAME = 144) by reflexivity.
assert (STK : MRX_STK = 144 + DNAMED_STK) by reflexivity.
assert (DS : DNAMED_STK = 8208) by reflexivity.
pose proof (TWL.u_at_range Bwc TW.A_OW_ndata 4) as Rnd. change (8 * Z.of_nat 4) with 32 in Rnd.
pose proof (TWL.s32_range Bwc TW.A_OW_ndata) as Snd. change (TW.s32_at Bwc TW.A_OW_ndata) with (TW.OW_ndata Bwc) in Snd.
pose proof (mrxd_retry_range fr) as RR. pose proof (mrxd_send_range fr Hl22) as RS.
(* the valuation *)
set (E0 := Eimg (PI := PI_transport) (Ereg regs2 [Z_to_bv 64 (TW.u_at Bwc TW.A_OW_ndata 4)])).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E0 k = YK11.getr regs2 q)
  by (intros k q Hk; unfold E0; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E0 32 = Z_to_bv 64 (TW.u_at Bwc TW.A_OW_ndata 4))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (U12 : bv_unsigned (ew E0 12) = TA_OW) by (rewrite (EE 12%nat 12%bv eq_refl), R12; apply unsigned_lit_small; lia).
assert (E18 : ew E0 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
(* the entry state *)
assert (HS0 : st_ok_pi segs VAL E0 ss_d6
  (restrict (w_H Wc) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + (AF_m_rx + OFF_D6))) mem2 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold ss_d6.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold d6_nd, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U12. split; [lia|]. split; [lia|]. split.
    + intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw). apply mrxd_inG. lia.
    + constructor; [|constructor].
      apply (chunk_ok_val segs E0 _ TA_OW 220 4 (SOff 32 0) (TW.u_at Bwc TW.A_OW_ndata 4));
        [exact (mrxd_den_atom E0 32 _ E32) | cbn; lia | lia |].
      exact (tw_read_val segs _ TMAP_A Bwc TW.OFF_OW TA_OW TW.SZ_OW 220 4 TMAP_A_ok Htw TMAP_A_OW
        ltac:(lia) ltac:(unfold TW.SZ_OW; lia)).
  - cbn [pairwise_disjoint all_disjoint]. repeat split.
  - unfold d6_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U12, E18, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite EO; reflexivity]. }
pose proof (st_ok_pi_pin_reg' E0 ss_d6 _ (10%bv : bv 5) 1 HS0 R10 eq_refl) as HS.
clear HS0.
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
  let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.
assert (SHOK : sh_ok segs MRXD_Bx SH6 E0 (mrestrict (w_H Wc) mem2))
  by exact (mrxd_shok6 _ _ _ _ _ E0 HAR U12 E18).
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (PI := PI_transport)) as BR.
rewrite <- (mrxd_pc OFF_D6).
(* run 1, 0x84d20 .. 0x84d24: k = OW.ndata; it stops at `blt a0, a5`. *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
{ mrxd_awr U12. }
mrxd_md mdA.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_OW + 220 <= a < TA_OW + 224) ->
  aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
{ intros a Ha H1. apply (kept_of_frame _ _ _ _ _ (fun x => TA_OW + 220 <= x < TA_OW + 224) HFr); [|exact Ha|exact H1].
  intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?U12 in Hx; lia). }
clear HF HFr HG.
rename ms into ms1.
assert (DK : sv_denot E0 (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.OW_ndata Bwc))
  by exact (mrxd_den_sext32 E0 32 _ E32 Rnd).
psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
- (* 1 < k: no OW.dn store *)
  rewrite DK in Hc. cbn [branch_taken sv_denot] in Hc. rewrite EPI.mrxk_lts in Hc by lia. apply Z.ltb_lt in Hc.
  destruct (mrxd_data6_hi fr Bwc B3 ltac:(lia) Hm) as (HnM & ->).
  (* run 2, 0x84d98 .. 0x84da0: k + 1 at OW + 220; to TICK. *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
  { mrxd_awr U12. }
  mrxd_md mdB.
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_OW + 220 <= a < TA_OW + 224) ->
    aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
  { intros a Ha H1. rewrite <- (KA1 a Ha H1).
    apply (kept_of_frame _ _ _ _ _ (fun x => TA_OW + 220 <= x < TA_OW + 224) HFr); [|exact Ha|exact H1].
    intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?U12 in Hx; lia). }
  clear HF HFr HG.
  assert (DN : sv_denot E0 (SAlu ALU_ADD (SExt true 32 (SOff 32 0)) (SLit 1)) = Z_to_bv 64 (TW.OW_ndata Bwc + 1))
    by exact (mrxd_den_add1 E0 _ _ DK).
  mrxd_chunk HS 0%nat 0%nat U12 (TW.OW_ndata Bwc + 1) DN VN.
  assert (HTW : tw_at TMAP_A (aview segs (w_H Wc) (ms_mem ms)) (TW.set_OW_ndata Bwc (TW.OW_ndata Bwc + 1))).
  { unfold TW.set_OW_ndata.
    pose proof (mrx_tw_start (aview segs (w_H Wc) (ms_mem ms)) _ _ Htw) as H0.
    pose proof (mrx_tw_step _ _ _ _ TW.OFF_OW TA_OW TW.SZ_OW 220 TW.A_OW_ndata 4 _ H0 TMAP_A_OW eq_refl
      ltac:(lia) ltac:(unfold TW.SZ_OW; cbn; lia) VN) as H1.
    apply (mrx_tw_end _ _ _ _ H1). intros x Hx HP. mrx_unP HP.
    pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KA; lia. }
  pmkst HS. rewrite (mrxd_pcl OFF_TICK 15288 eq_refl).
  mrxd_regs3 HS EE regs2 F2 F3 F4.
  eapply (mrxd_exit (MRX_PC OFF_TICK) (R_TICK Bw' r) Wc _ regs2 mem2 (ms_regs ms) (ms_mem ms) mdB HKT HJ Hmo Hsp Hgp Htp
    F2 F3 F4 Hsv).
  + intros a Ha. apply KA; lia.
  + exact HTW.
  + unfold R_TICK. split; [exact Htk | exact Hr].
- (* k <= 1: 0 <= k by the model; OW.dn[k] *)
  rewrite DK in Hc. cbn [branch_taken sv_denot] in Hc. rewrite EPI.mrxk_lts in Hc by lia. apply Z.ltb_ge in Hc.
  destruct (mrxd_data6_lo fr Bwc B3 ltac:(lia) Hm) as (Hk0 & ->).
  assert (Hcase : TW.OW_ndata Bwc = 0 \/ TW.OW_ndata Bwc = 1) by lia.
  destruct Hcase as [Hi|Hi].
  (* in each case a5 = k is pinned and OW.dn[k]'s 22 bytes join the state *)
  all: lazymatch goal with Hi : TW.OW_ndata _ = ?i |- _ =>
    mrxd_reg HS (15%bv : bv 5) (Z_to_bv 64 i) Q15 ltac:(rewrite DK, Hi; reflexivity) end.
  all: lazymatch goal with Hi : TW.OW_ndata _ = ?i |- _ =>
    lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
      pose proof (st_ok_pi_pin_reg' Ex ss (restrict Hh m) (15%bv : bv 5) i HS Q15 eq_refl) as HSp end end.
  all: clear HS Q15.
  all: lazymatch type of HSp with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
    let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HSp end.
  all: lazymatch goal with Hi : TW.OW_ndata _ = ?i |- _ =>
    lazymatch type of HSp with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
      pose proof (st_ok_pi_add_region Ex ss (restrict Hh m) (d6_dn i) HSp eq_refl
        (mrxd_dn_ok Ex _ i U12 ltac:(lia)) ltac:(cbn [ss_mem YP09.all_disjoint];
          unfold YP09.extent_disjoint, d6_dn; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite ?U12; repeat split; lia)) as HS end end.
  all: clear HSp.
  all: lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
    let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.
  (* run 2, 0x84d24 .. 0x84da0: x = OW + 256 + 24 k, the four checked stores (decided by SH6), k + 1 at OW + 220 *)
  all: paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK); [mrxd_awr U12 |].
  all: mrxd_md mdB.
  all: lazymatch goal with Hi : TW.OW_ndata _ = ?i |- _ =>
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_OW + 220 <= a < TA_OW + 224) ->
      ~ (TA_OW + 256 + 24 * i <= a < TA_OW + 278 + 24 * i) ->
      aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a)
    by (intros a Ha H1 H2; rewrite <- (KA1 a Ha H1);
        apply (kept_of_frame _ _ _ _ _
          (fun x => (TA_OW + 220 <= x < TA_OW + 224) \/ (TA_OW + 256 + 24 * i <= x < TA_OW + 278 + 24 * i)) HFr);
        [ intros b wlo whi x Hin Hx; cbv beta; mrxd_win Hin Hx ltac:(rewrite ?U12 in Hx; lia)
        | exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)] ]) end.
  all: clear HF HFr HG.
  all: lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in HS end.
  all: assert (HE2 : forall q, (q < 1024)%nat -> ew E2 q = ew E0 q)
    by (intros q Hq; unfold E2; repeat rewrite ew_ewset_other by lia; reflexivity).
  all: assert (U12' : bv_unsigned (ew E2 12) = TA_OW) by (rewrite HE2 by lia; exact U12).
  all: assert (D8 : sv_denot E2 (SOff 8 0) = Z_to_bv 64 (TI.tf_addr fr + 30))
    by (apply mrxd_den_atom; rewrite HE2 by lia; rewrite (EE 8%nat 8%bv eq_refl); exact R8).
  all: assert (D20 : sv_denot E2 (SOff 20 0) = Z_to_bv 64 (EPI.mrx_blen fr))
    by (apply mrxd_den_atom; rewrite HE2 by lia; rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  all: assert (D14 : sv_denot E2 (SOff 14 0) = Z_to_bv 64 (bv_swrap 32 (EPI.mrx_send fr)))
    by (apply mrxd_den_atom; rewrite HE2 by lia; rewrite (EE 14%nat 14%bv eq_refl); exact R14).
  all: assert (D13 : sv_denot E2 (SOff 13 0) = Z_to_bv 64 (EPI.mrx_retry fr))
    by (apply mrxd_den_atom; rewrite HE2 by lia; rewrite (EE 13%nat 13%bv eq_refl); exact R13).
  all: lazymatch goal with Hi : TW.OW_ndata _ = ?i |- _ =>
    assert (DNi : sv_denot E2 (SLit (i + 1)) = Z_to_bv 64 (i + 1)) by reflexivity end.
  all: mrxd_chunk HS 0%nat 0%nat U12' (EPI.mrx_retry fr) D13 VRT.
  all: mrxd_chunk HS 0%nat 1%nat U12' (bv_swrap 32 (EPI.mrx_send fr)) D14 VSN.
  all: mrxd_chunk HS 0%nat 2%nat U12' (EPI.mrx_blen fr) D20 VLN.
  all: mrxd_chunk HS 0%nat 3%nat U12' (TI.tf_addr fr + 30) D8 VBD.
  all: lazymatch goal with Hi : TW.OW_ndata _ = ?i |- _ => mrxd_chunk HS 1%nat 0%nat U12' (i + 1) DNi VND end.
  all: lazymatch goal with Hi : TW.OW_ndata _ = ?i |- _ =>
    assert (HTW : tw_at TMAP_A (aview segs (w_H Wc) (ms_mem ms))
      (TW.set_OW_ndata (mrxd_B6 fr Bwc i) (i + 1)))
    by (unfold mrxd_B6; apply (mrxd_world6 Bwc _ _ i _ _ _ _ _ Htw ltac:(lia));
        [ intros j Hj; exact (VBD j Hj)
        | intros j Hj; exact (VLN j Hj)
        | intros j Hj; rewrite <- (mrxd_le_sw32 (EPI.mrx_send fr) j); exact (VSN j Hj)
        | intros j Hj; exact (VRT j Hj)
        | intros j Hj; exact (VND j Hj)
        | intros x Hx N1 N2; pose proof (TMAP_A_hull x Hx) as Hh;
          unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh; apply KA; lia ]) end.
  all: rewrite Hi in Htk.
  all: pmkst HS.
  all: rewrite (mrxd_pcl OFF_TICK 15288 eq_refl).
  all: mrxd_regs3E HS EE HE2 regs2 F2 F3 F4.
  all: apply (mrxd_exit (MRX_PC OFF_TICK) (R_TICK Bw' r) Wc _ regs2 mem2 (ms_regs ms) (ms_mem ms) mdB HKT HJ Hmo Hsp Hgp Htp
    F2 F3 F4 Hsv ltac:(intros a Ha; apply KA; lia) HTW); unfold R_TICK; split; [exact Htk | exact Hr].
Qed.

(* ------------------------------------------------------------------ *)
(* The frame byte fa + 30                                              *)
(* ------------------------------------------------------------------ *)

Lemma mrxd_fb_of_frs : forall (Wc : world segs) mem, mrx_frs fr Wc mem -> mrxd_fb fr Wc mem.
Proof.
intros Wc mem (Hg & Hrd & _) Hl. split.
- destruct (garr8_nthZ segs _ _ _ 30 Hg ltac:(lia) ltac:(rewrite length_map; unfold mlen in Hl; lia)) as [Hv _].
  exact Hv.
- destruct Hrd as (_ & Hra & _).
  exact (range_addressable_sub _ _ _ _ (TI.tf_addr fr + 30) 1 Hra ltac:(lia) ltac:(lia)).
Qed.

Lemma mrxd_fb_kept : forall (Wc : world segs) m m', mrxd_fb fr Wc m -> 0 <= TI.tf_addr fr ->
  TI.tf_addr fr + 31 <= 2 ^ 47 ->
  (31 <= mlen fr -> aview segs (w_H Wc) m' (TI.tf_addr fr + 30) = aview segs (w_H Wc) m (TI.tf_addr fr + 30)) ->
  (forall s, SHADOW_OFF <= s < 2 ^ 64 -> aview segs (w_H Wc) m' s = aview segs (w_H Wc) m s) ->
  mrxd_fb fr Wc m'.
Proof.
intros Wc m m' Hfb H0 H47 Ka Ks Hl. specialize (Ka Hl). destruct (Hfb Hl) as (Hv & Hra). split.
- intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. specialize (Hv 0%nat Hk).
  cbn [Z.of_nat] in Hv |- *. rewrite Z.add_0_r in Hv |- *.
  change (aview segs (w_H Wc) m' (TI.tf_addr fr + 30)) with
    (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict (w_H Wc) m') (TI.tf_addr fr + 30))) in Ka.
  change (aview segs (w_H Wc) m (TI.tf_addr fr + 30)) with
    (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict (w_H Wc) m) (TI.tf_addr fr + 30))) in Ka.
  rewrite Hv in Ka.
  destruct (YP09.mbyte segs (mrestrict (w_H Wc) m') (TI.tf_addr fr + 30)) as [b|] eqn:Eb; cbn [option_map] in Ka;
    [|discriminate Ka].
  injection Ka as Hb. f_equal. apply bv_eq. exact Hb.
- intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  rewrite Ks; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF. lia.
Qed.

Lemma mrxd_shok5 : forall (Wx : world segs) mem (E : env),
  range_addressable (aview segs (w_H Wx) mem) SHADOW_OFF (TI.tf_addr fr + 30) 1 ->
  amem_range (TI.tf_addr fr) (mlen fr) -> 0 <= TI.tf_addr fr -> 31 <= mlen fr ->
  bv_unsigned (ew E 8) = TI.tf_addr fr + 30 -> ew E 18 = Z_to_bv 64 SHADOW_OFF ->
  sh_ok segs MRXD_Bx SH5 E (mrestrict (w_H Wx) mem).
Proof.
intros Wx mem E Hra Ham H0 Hl U8 E18.
unfold sh_ok, SH5. constructor; [|constructor].
apply (shent_ok_of_range segs (w_H Wx) mem E MRXD_Bx 8 (TI.tf_addr fr + 30) 1 (TI.tf_addr fr + 30) 0 1 Hra).
- unfold U, MRXD_Bx. cbn [sv_denot]. rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U8.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
  unfold SHADOW_OFF. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* D5: the desk counter, the keepalive test                            *)
(* ------------------------------------------------------------------ *)

Lemma mrxd_seg_d5 : K (MRX_PC OFF_TICK) (R_TICK Bw' r) -> K (MRX_PC OFF_D6) (R_D6 fr lyc Sc Bw' r) ->
  K (MRX_PC OFF_D5) (R_D5 fr n lyc Sc Bw' r).
Proof.
intros HKT HK6. unfold mrx_K at 1. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hperm & Hmo & Hsp & Hgp & Htp & Hsv & Htw & HR).
destruct HR as (-> & -> & Hfb & Hhdr & Ham & Hfa0 & R8 & R12 & R13 & R14 & R18 & R19 & R20 & B3 & Hm & Htk & Hr).
pose proof HST as (Hsp1 & Hsp16 & Hceil & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hap & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
assert (EM : TA_M = 6156640) by reflexivity. assert (EO : TA_OW = 6238304) by reflexivity.
assert (FR : MRX_FRAME = 144) by reflexivity. assert (STK : MRX_STK = 144 + DNAMED_STK) by reflexivity.
assert (DS : DNAMED_STK = 8208) by reflexivity.
pose proof Hhdr as (Hn & _ & Hnb).
assert (Hl22 : 22 <= mlen fr) by lia.
pose proof (mrxd_retry_range fr) as RR. pose proof (mrxd_send_range fr Hl22) as RS.
assert (RB : 0 <= EPI.mrx_blen fr <= mlen fr - 30) by (unfold EPI.mrx_blen; lia).
assert (Ham' : TI.tf_addr fr + mlen fr <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (PI := PI_transport)) as BR.
rewrite <- (mrxd_pc OFF_D5).
destruct (Z.eq_dec (EPI.mrx_blen fr) 1) as [BL1|BLn].
2: {
(* body_len <> 1: the stores, then D6 *)
set (E0 := Eimg (PI := PI_transport) (Ereg regs2 [])).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E0 k = YK11.getr regs2 q)
  by (intros k q Hk; unfold E0; apply ew_Eimg_Ereg_nat; exact Hk).
assert (U19 : bv_unsigned (ew E0 19) = TA_M) by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (E18 : ew E0 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E20 : ew E0 20 = Z_to_bv 64 (EPI.mrx_blen fr)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (HS : st_ok_pi segs VAL E0 ss_d5n
  (restrict (w_H Wc) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + (AF_m_rx + OFF_D5))) mem2 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold ss_d5n.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold d5_dcv, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply mrxd_inG. lia.
    + unfold d5_dc, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply mrxd_inG. lia.
  - apply pairwise_disjoint_of_extents. unfold d5_dcv, d5_dc, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; first [exact I | lia].
  - unfold d5n_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19, E18, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite EM; reflexivity]. }
assert (SHOK : sh_ok segs MRXD_Bx [] E0 (mrestrict (w_H Wc) mem2)) by (unfold sh_ok; apply Forall_nil).
(* run 1, 0x84cf8 .. 0x84d04: the two stores; it stops at `bne s4, a0`. *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D6).
{ mrxd_awr U19. }
mrxd_md mdA.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 76 <= a < TA_M + 84) ->
  aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
{ intros a Ha H1. apply (kept_of_frame _ _ _ _ _ (fun x => TA_M + 76 <= x < TA_M + 84) HFr); [|exact Ha|exact H1].
  intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?U19 in Hx; lia). }
clear HF HFr HG. rename ms into ms1.
psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
2: { rewrite (mrxd_den_atom E0 20 _ E20) in Hc. cbn [branch_taken sv_denot] in Hc.
     rewrite EPI.mrxk_eqb in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc. exfalso. exact (BLn Hc). }
(* run 2: to D6 *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D6).
{ mrxd_awr U19. }
mrxd_md mdB.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 76 <= a < TA_M + 84) ->
  aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
{ intros a Ha H1. rewrite <- (KA1 a Ha H1).
  apply (kept_of_frame _ _ _ _ _ (fun x => TA_M + 76 <= x < TA_M + 84) HFr); [|exact Ha|exact H1].
  intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?U19 in Hx; lia). }
clear HF HFr HG.
assert (D14 : sv_denot E0 (SOff 14 0) = Z_to_bv 64 (bv_swrap 32 (EPI.mrx_send fr)))
  by (apply mrxd_den_atom; rewrite (EE 14%nat 14%bv eq_refl); exact R14).
mrxd_chunk HS 0%nat 0%nat U19 1 (@eq_refl _ (Z_to_bv 64 1)) V76.
mrxd_chunk HS 1%nat 0%nat U19 (bv_swrap 32 (EPI.mrx_send fr)) D14 V80.
assert (HTW : tw_at TMAP_A (aview segs (w_H Wc) (ms_mem ms)) (mrxd_B5 fr Bwc)).
{ unfold mrxd_B5. apply (mrxd_world5 Bwc _ _ _ Htw).
  - intros j Hj. rewrite <- (mrxd_le_sw32 (EPI.mrx_send fr) j). exact (V80 j Hj).
  - exact V76.
  - intros x Hx N1. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA; lia. }
assert (HM6 : EPI.mrx_data6 fr (mrxd_B5 fr Bwc) = Some (B3, tt)).
{ apply (mrxd_data5_d6 fr Bwc B3); [|exact Hm]. rewrite (proj2 (Z.eqb_neq _ _) BLn). reflexivity. }
pmkst HS. rewrite (mrxd_pcl OFF_D6 15036 eq_refl).
mrxd_regs3 HS EE regs2 F2 F3 F4.
mrxd_keep HS EE regs2 (8%bv : bv 5) 8%nat Q8. mrxd_keep HS EE regs2 (12%bv : bv 5) 12%nat Q12.
mrxd_keep HS EE regs2 (13%bv : bv 5) 13%nat Q13. mrxd_keep HS EE regs2 (14%bv : bv 5) 14%nat Q14.
mrxd_keep HS EE regs2 (18%bv : bv 5) 18%nat Q18. mrxd_keep HS EE regs2 (20%bv : bv 5) 20%nat Q20.
mrxd_reg HS (10%bv : bv 5) (Z_to_bv 64 1) Q10 ltac:(reflexivity).
apply (mrxd_exit (MRX_PC OFF_D6) (R_D6 fr lyc Sc Bw' r) Wc (mrxd_B5 fr Bwc) regs2 mem2 (ms_regs ms) (ms_mem ms) mdB
  HK6 HJ Hmo Hsp Hgp Htp F2 F3 F4 Hsv ltac:(intros a Ha; apply KA; lia) HTW).
unfold R_D6. cbv beta.
split; [reflexivity|]. split; [reflexivity|]. split; [exact Hl22|].
split; [rewrite Q8; exact R8|]. split; [exact Q10|]. split; [rewrite Q12; exact R12|].
split; [rewrite Q13; exact R13|]. split; [rewrite Q14; exact R14|]. split; [rewrite Q18; exact R18|].
split; [rewrite Q20; exact R20|].
exists B3. split; [exact HM6|]. split; [exact Htk | exact Hr].
}
(* body_len = 1: the stores, the checked load of fa + 30, then TICK (0) or D6 *)
assert (Hl31 : 31 <= mlen fr) by (unfold EPI.mrx_blen in BL1; lia).
destruct (Hfb Hl31) as (Hv30 & Hra30).
pose proof (mrxd_mfb_range fr 30) as R30.
assert (HfaM : ~ (TA_M + 76 <= TI.tf_addr fr + 30 < TA_M + 84)).
{ intros Hx. exact (mrxd_apart30 fr Hap Hl31 (TI.tf_addr fr + 30) (or_intror (or_introl Hx)) eq_refl). }
set (E0 := Eimg (PI := PI_transport) (Ereg regs2 [Z_to_bv 64 (mfb fr 30)])).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E0 k = YK11.getr regs2 q)
  by (intros k q Hk; unfold E0; apply ew_Eimg_Ereg_nat; exact Hk).
assert (U19 : bv_unsigned (ew E0 19) = TA_M) by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (E18 : ew E0 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E20 : ew E0 20 = Z_to_bv 64 (EPI.mrx_blen fr)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E32 : ew E0 32 = Z_to_bv 64 (mfb fr 30))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (U8 : bv_unsigned (ew E0 8) = TI.tf_addr fr + 30)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E0 20) = 1) by (rewrite E20, BL1; reflexivity).
assert (HS : st_ok_pi segs VAL E0 ss_d5o
  (restrict (w_H Wc) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + (AF_m_rx + OFF_D5))) mem2 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold ss_d5o.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold d5_dcv, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply mrxd_inG. lia.
    + unfold d5_dc, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply mrxd_inG. lia.
    + unfold d5_fb, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E0 _ (TI.tf_addr fr + 30) 0 1 (SOff 32 0) (mfb fr 30));
        [exact (mrxd_den_atom E0 32 _ E32) | cbn; lia | lia |].
      rewrite Z.add_0_r. exact Hv30.
  - apply pairwise_disjoint_of_extents. unfold d5_dcv, d5_dc, d5_fb, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; first [exact I | lia].
  - unfold d5o_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U8, U19, U20, E18, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite EM; reflexivity]. }
pose proof (mrxd_shok5 Wc mem2 E0 Hra30 Ham Hfa0 Hl31 U8 E18) as SHOK.
(* run 1, 0x84cf8 .. 0x84d04: the two stores; it stops at `bne s4, a0`. *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D6).
{ mrxd_awr U19. }
mrxd_md mdA.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 76 <= a < TA_M + 84) ->
  aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
{ intros a Ha H1. apply (kept_of_frame _ _ _ _ _ (fun x => TA_M + 76 <= x < TA_M + 84) HFr); [|exact Ha|exact H1].
  intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?U19, ?U8 in Hx; lia). }
clear HF HFr HG. rename ms into ms1.
psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
{ rewrite (mrxd_den_atom E0 20 _ E20) in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite EPI.mrxk_eqb in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc. exfalso. exact (Hc BL1). }
(* run 2, 0x84d08 .. 0x84d1c: the check of fa + 30 (decided by SH5), the load; it stops at `beqz a1`. *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D6).
{ mrxd_awr U19. }
mrxd_md mdB.
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 76 <= a < TA_M + 84) ->
  aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
{ intros a Ha H1. rewrite <- (KA1 a Ha H1).
  apply (kept_of_frame _ _ _ _ _ (fun x => TA_M + 76 <= x < TA_M + 84) HFr); [|exact Ha|exact H1].
  intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?U19, ?U8 in Hx; lia). }
clear HF HFr HG KA1. rename ms into ms2.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in * end.
assert (HE1 : forall q, (q < 1024)%nat -> ew E1 q = ew E0 q)
  by (intros q Hq; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (U19' : bv_unsigned (ew E1 19) = TA_M) by (rewrite HE1 by lia; exact U19).
assert (E32' : ew E1 32 = Z_to_bv 64 (mfb fr 30)) by (rewrite HE1 by lia; exact E32).
assert (D14 : sv_denot E1 (SOff 14 0) = Z_to_bv 64 (bv_swrap 32 (EPI.mrx_send fr)))
  by (apply mrxd_den_atom; rewrite HE1 by lia; rewrite (EE 14%nat 14%bv eq_refl); exact R14).
clear Hc.
psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
- (* fa[30] = 0: the keepalive, to TICK *)
  rewrite (mrxd_den_zext E1 32 (mfb fr 30) 8 E32' ltac:(change (2 ^ Z.of_N 8) with 256; lia) ltac:(lia)) in Hc.
  cbn [branch_taken sv_denot] in Hc. rewrite EPI.mrxk_eqb in Hc by lia. apply Z.eqb_eq in Hc.
  assert (EB3 : B3 = mrxd_B5 fr Bwc)
    by exact (mrxd_data5_tick fr Bwc B3 BL1 ltac:(rewrite (mrxd_at8 fr Hl31); exact Hc) Hm).
  subst B3.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
  { mrxd_awr U19'. }
  mrxd_md mdC.
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 76 <= a < TA_M + 84) ->
    aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
  { intros a Ha H1. rewrite <- (KA2 a Ha H1).
    apply (kept_of_frame _ _ _ _ _ (fun x => TA_M + 76 <= x < TA_M + 84) HFr); [|exact Ha|exact H1].
    intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?U19', ?HE1, ?U8 in Hx by lia; lia). }
  clear HF HFr HG.
  mrxd_chunk HS 0%nat 0%nat U19' 1 (@eq_refl _ (Z_to_bv 64 1)) V76.
  mrxd_chunk HS 1%nat 0%nat U19' (bv_swrap 32 (EPI.mrx_send fr)) D14 V80.
  assert (HTW : tw_at TMAP_A (aview segs (w_H Wc) (ms_mem ms)) (mrxd_B5 fr Bwc)).
  { unfold mrxd_B5. apply (mrxd_world5 Bwc _ _ _ Htw).
    - intros j Hj. rewrite <- (mrxd_le_sw32 (EPI.mrx_send fr) j). exact (V80 j Hj).
    - exact V76.
    - intros x Hx N1. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA; lia. }
  pmkst HS. rewrite (mrxd_pcl OFF_TICK 15288 eq_refl).
  mrxd_regs3E HS EE HE1 regs2 F2 F3 F4.
  apply (mrxd_exit (MRX_PC OFF_TICK) (R_TICK Bw' r) Wc (mrxd_B5 fr Bwc) regs2 mem2 (ms_regs ms) (ms_mem ms) mdC
    HKT HJ Hmo Hsp Hgp Htp F2 F3 F4 Hsv ltac:(intros a Ha; apply KA; lia) HTW).
  unfold R_TICK. split; [exact Htk | exact Hr].
- (* fa[30] <> 0: to D6 *)
  rewrite (mrxd_den_zext E1 32 (mfb fr 30) 8 E32' ltac:(change (2 ^ Z.of_N 8) with 256; lia) ltac:(lia)) in Hc.
  cbn [branch_taken sv_denot] in Hc. rewrite EPI.mrxk_eqb in Hc by lia. apply Z.eqb_neq in Hc.
  assert (HM6 : EPI.mrx_data6 fr (mrxd_B5 fr Bwc) = Some (B3, tt)).
  { apply (mrxd_data5_d6 fr Bwc B3); [|exact Hm].
    rewrite BL1, (mrxd_at8 fr Hl31), (proj2 (Z.eqb_neq _ _) Hc). reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D6).
  { mrxd_awr U19'. }
  mrxd_md mdC.
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 76 <= a < TA_M + 84) ->
    aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
  { intros a Ha H1. rewrite <- (KA2 a Ha H1).
    apply (kept_of_frame _ _ _ _ _ (fun x => TA_M + 76 <= x < TA_M + 84) HFr); [|exact Ha|exact H1].
    intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?U19', ?HE1, ?U8 in Hx by lia; lia). }
  clear HF HFr HG.
  mrxd_chunk HS 0%nat 0%nat U19' 1 (@eq_refl _ (Z_to_bv 64 1)) V76.
  mrxd_chunk HS 1%nat 0%nat U19' (bv_swrap 32 (EPI.mrx_send fr)) D14 V80.
  assert (HTW : tw_at TMAP_A (aview segs (w_H Wc) (ms_mem ms)) (mrxd_B5 fr Bwc)).
  { unfold mrxd_B5. apply (mrxd_world5 Bwc _ _ _ Htw).
    - intros j Hj. rewrite <- (mrxd_le_sw32 (EPI.mrx_send fr) j). exact (V80 j Hj).
    - exact V76.
    - intros x Hx N1. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA; lia. }
  pmkst HS. rewrite (mrxd_pcl OFF_D6 15036 eq_refl).
  mrxd_regs3E HS EE HE1 regs2 F2 F3 F4.
  mrxd_keepE HS EE HE1 regs2 (8%bv : bv 5) 8%nat Q8. mrxd_keepE HS EE HE1 regs2 (12%bv : bv 5) 12%nat Q12.
  mrxd_keepE HS EE HE1 regs2 (13%bv : bv 5) 13%nat Q13. mrxd_keepE HS EE HE1 regs2 (14%bv : bv 5) 14%nat Q14.
  mrxd_keepE HS EE HE1 regs2 (18%bv : bv 5) 18%nat Q18. mrxd_keepE HS EE HE1 regs2 (20%bv : bv 5) 20%nat Q20.
  mrxd_reg HS (10%bv : bv 5) (Z_to_bv 64 1) Q10 ltac:(reflexivity).
  apply (mrxd_exit (MRX_PC OFF_D6) (R_D6 fr lyc Sc Bw' r) Wc (mrxd_B5 fr Bwc) regs2 mem2 (ms_regs ms) (ms_mem ms) mdC
    HK6 HJ Hmo Hsp Hgp Htp F2 F3 F4 Hsv ltac:(intros a Ha; apply KA; lia) HTW).
  unfold R_D6. cbv beta.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hl22|].
  split; [rewrite Q8; exact R8|]. split; [exact Q10|]. split; [rewrite Q12; exact R12|].
  split; [rewrite Q13; exact R13|]. split; [rewrite Q14; exact R14|]. split; [rewrite Q18; exact R18|].
  split; [rewrite Q20; exact R20|].
  exists B3. split; [exact HM6|]. split; [exact Htk | exact Hr].
Qed.

(* ------------------------------------------------------------------ *)
(* DATA: OW.acks, M.fail, the backoff, the duplicate test              *)
(* ------------------------------------------------------------------ *)

(* The cut D5 at a run's end. *)
Lemma mrxd_to_d5 : forall (Wc : world segs) Bwc regs2 mem2 regsF memF mdF B3,
  K (MRX_PC OFF_D5) (R_D5 fr n lyc Sc Bw' r) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc Wc memF mdF 0 ->
  mo_le MT Sc Sc 0 ->
  YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK11.getr regs2 3 = YK11.getr regs0 3 -> YK11.getr regs2 4 = YK11.getr regs0 4 ->
  YK11.getr regsF 2 = YK11.getr regs2 2 -> YK11.getr regsF 3 = YK11.getr regs2 3 ->
  YK11.getr regsF 4 = YK11.getr regs2 4 ->
  @mrx_saved Wc mem2 sp1 regs0 ->
  (forall a, sp1 - 104 <= a < sp1 -> aview segs (w_H Wc) memF a = aview segs (w_H Wc) mem2 a) ->
  tw_at TMAP_A (aview segs (w_H Wc) memF) Bwc ->
  mrxd_fb fr Wc memF -> mrx_hdr fr n -> amem_range (TI.tf_addr fr) (mlen fr) -> 0 <= TI.tf_addr fr ->
  YK11.getr regsF 8 = Z_to_bv 64 (TI.tf_addr fr + 30) -> YK11.getr regsF 12 = Z_to_bv 64 TA_OW ->
  YK11.getr regsF 13 = Z_to_bv 64 (EPI.mrx_retry fr) ->
  YK11.getr regsF 14 = Z_to_bv 64 (bv_swrap 32 (EPI.mrx_send fr)) ->
  YK11.getr regsF 18 = Z_to_bv 64 SHADOW_OFF -> YK11.getr regsF 19 = Z_to_bv 64 TA_M ->
  YK11.getr regsF 20 = Z_to_bv 64 (EPI.mrx_blen fr) ->
  EPI.mrx_data5 fr Bwc = Some (B3, tt) -> TC.m_tick_m B3 = Some (Bw', tt) -> r = 1 ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 (MRX_PC OFF_D5)) memF (YK11.seg_rom segs)) mdF)
    (mrx_ipost B MT sp1 regs0 lyc Sc W memc mdc Bw' r).
Proof.
intros Wc Bwc regs2 mem2 regsF memF mdF B3 HK HJ Hmo Hsp Hgp Htp F2 F3 F4 Hsv Hkp Htw Hfb Hh Ham H0
  Q8 Q12 Q13 Q14 Q18 Q19 Q20 Hm Htk Hr.
apply (mrxd_exit (MRX_PC OFF_D5) (R_D5 fr n lyc Sc Bw' r) Wc Bwc regs2 mem2 regsF memF mdF HK HJ Hmo Hsp Hgp Htp
  F2 F3 F4 Hsv Hkp Htw).
unfold R_D5. cbv beta.
split; [reflexivity|]. split; [reflexivity|]. split; [exact Hfb|]. split; [exact Hh|]. split; [exact Ham|].
split; [exact H0|]. split; [exact Q8|]. split; [exact Q12|]. split; [exact Q13|]. split; [exact Q14|].
split; [exact Q18|]. split; [exact Q19|]. split; [exact Q20|].
exists B3. split; [exact Hm|]. split; [exact Htk | exact Hr].
Qed.

Lemma mrx_seg_data :
  K (MRX_PC OFF_TICK) (R_TICK Bw' r) ->
  K (MRX_PC OFF_DATA) (R_DATA fr n sp1 lyc Sc Bw' r).
Proof using All.
intros HKT.
pose proof (mrxd_seg_d5 HKT (mrxd_seg_d6 HKT)) as HK5.
unfold mrx_K at 1. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hperm & Hmo & Hsp & Hgp & Htp & Hsv & Htw & HR).
destruct HR as (-> & -> & Hfrs & Hhdr & H28 & R10 & R8 & R19 & R20 & Hhr & Hs8 & B3 & Hm & Htk & Hr).
destruct Hhr as (R18 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & Hs16 & Hs24 & Hs32).
pose proof HST as (Hsp1 & Hsp16 & Hceil & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hap & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
assert (EM : TA_M = 6156640) by reflexivity. assert (EO : TA_OW = 6238304) by reflexivity.
assert (EG : TA_g_cfg = 6156416) by reflexivity.
assert (FR : MRX_FRAME = 144) by reflexivity. assert (STK : MRX_STK = 144 + DNAMED_STK) by reflexivity.
assert (DS0 : DNAMED_STK = 8208) by reflexivity.
pose proof Hhdr as (Hn & _ & Hnb).
pose proof Hfrs as (_ & (_ & _ & _ & Ham & Hfa0 & _) & _).
assert (Ham' : TI.tf_addr fr + mlen fr <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
pose proof (mrxd_fb_of_frs Wc mem2 Hfrs) as Hfb0.
(* the model *)
destruct (mrxd_data_inv fr Bwc B3 Hm) as (HnI & Hm4). clear Hm.
pose proof (tw_len _ _ _ Htw) as LB.
assert (FV : TW.M_desk_counter_valid (mrxd_B4 fr Bwc) = TW.M_desk_counter_valid Bwc).
{ unfold TW.M_desk_counter_valid, TW.s32_at. rewrite (mrxd_B4_u fr Bwc _ LB) by (unfold TW.A_M_desk_counter_valid; lia).
  reflexivity. }
assert (FC : TW.M_desk_counter (mrxd_B4 fr Bwc) = TW.M_desk_counter Bwc).
{ unfold TW.M_desk_counter. apply (mrxd_B4_u fr Bwc _ LB); unfold TW.A_M_desk_counter; lia. }
assert (FBK : mrxd_bkv (mrxd_B1 Bwc) = TS0.u64 (TW.g_now Bwc + TC.h_ms_m (TW.Cfg_backoff_ms Bwc))).
{ unfold mrxd_bkv. rewrite (mrxd_B1_now Bwc LB), (mrxd_B1_bms Bwc LB). reflexivity. }
clear LB.
(* the values *)
pose proof (mrxd_retry_range fr) as RR. pose proof (mrxd_send_range fr ltac:(lia)) as RS.
pose proof (TWL.u_at_range Bwc TW.A_M_desk_counter_valid 4) as R34.
pose proof (TWL.u_at_range Bwc TW.A_M_desk_counter 4) as R35.
pose proof (TWL.u_at_range Bwc TW.A_OW_acks 4) as R36.
pose proof (TWL.u_at_range Bwc TW.A_Cfg_backoff_ms 4) as R37.
pose proof (TWL.u_at_range Bwc TW.OFF_g_now 8) as Rnow.
change (8 * Z.of_nat 4) with 32 in R34, R35, R36, R37. change (8 * Z.of_nat 8) with 64 in Rnow.
change (TW.u_at Bwc TW.A_M_desk_counter 4) with (TW.M_desk_counter Bwc) in R35.
pose proof (TWL.s32_range Bwc TW.A_M_desk_counter_valid) as S34.
change (TW.s32_at Bwc TW.A_M_desk_counter_valid) with (TW.M_desk_counter_valid Bwc) in S34.
pose proof (mrxd_mfb_range fr 18) as B18. pose proof (mrxd_mfb_range fr 21) as B21.
(* the valuation *)
set (E0 := Eimg (PI := PI_transport) (Ereg regs2 [Z_to_bv 64 (mfb fr 18); Z_to_bv 64 (mfb fr 21);
  Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_counter_valid 4); Z_to_bv 64 (TW.M_desk_counter Bwc);
  Z_to_bv 64 (TW.u_at Bwc TW.A_OW_acks 4); Z_to_bv 64 (TW.u_at Bwc TW.A_Cfg_backoff_ms 4)])).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E0 k = YK11.getr regs2 q)
  by (intros k q Hk; unfold E0; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E0 32 = Z_to_bv 64 (mfb fr 18))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 (mfb fr 21))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_counter_valid 4))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E0 35 = Z_to_bv 64 (TW.M_desk_counter Bwc))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E0 36 = Z_to_bv 64 (TW.u_at Bwc TW.A_OW_acks 4))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
assert (E37 : ew E0 37 = Z_to_bv 64 (TW.u_at Bwc TW.A_Cfg_backoff_ms 4))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 5)).
destruct mrxd_vals as (V12 & V49).
assert (E253 : ew E0 (A_OBJ 12) = Z_to_bv 64 TA_OW)
  by (unfold E0; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V12; reflexivity).
assert (U253 : bv_unsigned (ew E0 (A_OBJ 12)) = TA_OW) by (rewrite E253; apply unsigned_lit_small; lia).
assert (U253' : bv_unsigned (ew E0 253%nat) = TA_OW) by exact U253.
assert (E290 : ew E0 (A_OBJ 49) = Z_to_bv 64 (TA_g_cfg + 36))
  by (unfold E0; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V49; reflexivity).
assert (U290 : bv_unsigned (ew E0 (A_OBJ 49)) = TA_g_cfg + 36) by (rewrite E290; apply unsigned_lit_small; lia).
assert (U290' : bv_unsigned (ew E0 290%nat) = TA_g_cfg + 36) by exact U290.
assert (Usp : bv_unsigned (ew E0 2) = sp1 - MRX_FRAME)
  by (rewrite (EE 2%nat 2%bv eq_refl), Hsp; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E0 19) = TA_M) by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (E18 : ew E0 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E10 : ew E0 10 = Z_to_bv 64 (TW.g_now Bwc)) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E21 : ew E0 21 = Z_to_bv 64 (mfb fr 20)) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E23 : ew E0 23 = Z_to_bv 64 (mfb fr 26)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E0 24 = Z_to_bv 64 (mfb fr 27)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (E27 : ew E0 27 = Z_to_bv 64 (mfb fr 19)) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
(* the values the code computes *)
assert (DR : sv_denot E0 (SAlu ALU_OR (SAlu ALU_SLL (SOff 23 0) (SLit 8)) (SOff 24 0)) = Z_to_bv 64 (EPI.mrx_retry fr))
  by exact (mrxd_retry_den E0 fr ltac:(lia) E23 E24).
assert (DSd : sv_denot E0 (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 27 0) (SLit 16))
    (SAluw ALU_SLL (SOff 32 0) (SLit 24))) (SAlu ALU_SLL (SOff 21 0) (SLit 8))) (SOff 33 0)) =
  Z_to_bv 64 (bv_swrap 32 (EPI.mrx_send fr)))
  by exact (mrxd_send_den E0 fr ltac:(lia) E27 E32 E21 E33).
assert (DACK : sv_denot E0 (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)) = Z_to_bv 64 (TW.OW_acks Bwc + 1))
  by exact (mrxd_den_add1 E0 _ _ (mrxd_den_sext32 E0 36 _ E36 R36)).
assert (DBK : sv_denot E0 (SAlu ALU_ADD (SMd M_MUL (SExt false 32 (SOff 37 0)) (SLit 1000)) (SOff 10 0)) =
  Z_to_bv 64 (TS0.u64 (TW.g_now Bwc + TC.h_ms_m (TW.Cfg_backoff_ms Bwc))))
  by exact (mrxd_bk_den E0 _ _ E10 E37 Rnow R37).
assert (DDV : sv_denot E0 (SExt true 32 (SOff 34 0)) = Z_to_bv 64 (TW.M_desk_counter_valid Bwc))
  by exact (mrxd_den_sext32 E0 34 _ E34 R34).
assert (DDC : sv_denot E0 (SExt true 32 (SOff 35 0)) = Z_to_bv 64 (bv_swrap 32 (TW.M_desk_counter Bwc)))
  by exact (mrxd_den_sext32 E0 35 _ E35 R35).
(* the entry state *)
assert (M16 : (sp1 - MRX_FRAME) mod 16 = 0).
{ rewrite FR. replace (sp1 - 144) with (sp1 + (-9) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
assert (HS : st_ok_pi segs VAL E0 ss_data
  (restrict (w_H Wc) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + (AF_m_rx + OFF_DATA))) mem2 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold ss_data.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + unfold mrxd_stk, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val segs E0 _ (sp1 - MRX_FRAME) 8 8 (SOff 32 0) (mfb fr 18));
          [exact (mrxd_den_atom E0 32 _ E32) | change (8 * Z.of_N 8) with 64; lia | lia |].
        exact (val_mem_of_rdword segs (w_H Wc) mem2 _ _ Hs8).
      * apply (chunk_ok_val segs E0 _ (sp1 - MRX_FRAME) 32 8 (SOff 33 0) (mfb fr 21));
          [exact (mrxd_den_atom E0 33 _ E33) | change (8 * Z.of_N 8) with 64; lia | lia |].
        exact (val_mem_of_rdword segs (w_H Wc) mem2 _ _ Hs32).
    + unfold mrxd_dcvR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E0 _ TA_M 76 4 (SOff 34 0) (TW.u_at Bwc TW.A_M_desk_counter_valid 4));
        [exact (mrxd_den_atom E0 34 _ E34) | change (8 * Z.of_N 4) with 32; lia | lia |].
      exact (tw_read_val segs _ TMAP_A Bwc TW.OFF_M TA_M TW.SZ_M 76 4 TMAP_A_ok Htw TMAP_A_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold mrxd_dcR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E0 _ TA_M 80 4 (SOff 35 0) (TW.M_desk_counter Bwc));
        [exact (mrxd_den_atom E0 35 _ E35) | change (8 * Z.of_N 4) with 32; lia | lia |].
      exact (tw_read_val segs _ TMAP_A Bwc TW.OFF_M TA_M TW.SZ_M 80 4 TMAP_A_ok Htw TMAP_A_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold mrxd_fail, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply mrxd_inG. lia.
    + unfold mrxd_acks, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U253. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw). apply mrxd_inG. lia.
      * constructor; [|constructor].
        apply (chunk_ok_val segs E0 _ TA_OW 204 4 (SOff 36 0) (TW.u_at Bwc TW.A_OW_acks 4));
          [exact (mrxd_den_atom E0 36 _ E36) | change (8 * Z.of_N 4) with 32; lia | lia |].
        exact (tw_read_val segs _ TMAP_A Bwc TW.OFF_OW TA_OW TW.SZ_OW 204 4 TMAP_A_ok Htw TMAP_A_OW
          ltac:(lia) ltac:(unfold TW.SZ_OW; lia)).
    + unfold mrxd_bms, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U290. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E0 _ (TA_g_cfg + 36) 0 4 (SOff 37 0) (TW.u_at Bwc TW.A_Cfg_backoff_ms 4));
        [exact (mrxd_den_atom E0 37 _ E37) | change (8 * Z.of_N 4) with 32; lia | lia |].
      rewrite Z.add_0_r.
      exact (tw_read_val segs _ TMAP_A Bwc TW.OFF_g_cfg TA_g_cfg TW.SZ_g_cfg 36 4 TMAP_A_ok Htw TMAP_A_g_cfg
        ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)).
  - apply pairwise_disjoint_of_extents.
    unfold mrxd_stk, mrxd_dcvR, mrxd_dcR, mrxd_fail, mrxd_acks, mrxd_bms, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U19, U253, U290.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; first [exact I | lia].
  - unfold data_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp, U19, U253, E18, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I;
      first [lia | exact M16 | rewrite EM; reflexivity | rewrite EO; reflexivity]. }
assert (SHOK : sh_ok segs MRXD_Bx [] E0 (mrestrict (w_H Wc) mem2)) by (unfold sh_ok; apply Forall_nil).
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (PI := PI_transport)) as BR.
rewrite <- (mrxd_pc OFF_DATA).
(* run 1, 0x84c88 .. 0x84cbc: send, retry, &OW, OW.acks + 1, M.fail = 0; it stops at `beqz a3`. *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
{ mrxd_awr2 U19 U253'. }
mrxd_md mdA.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 88 <= a < TA_M + 92) -> ~ (TA_OW + 204 <= a < TA_OW + 208) ->
  aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _ (fun x => (TA_M + 88 <= x < TA_M + 92) \/ (TA_OW + 204 <= x < TA_OW + 208)) HFr);
    [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U19, ?U253', ?U290' in Hx; lia). }
clear HF HFr HG. rename ms into ms1.
psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
- (* retry = 0: no backoff, never the duplicate *)
  rewrite DR in Hc. cbn [branch_taken sv_denot] in Hc. rewrite EPI.mrxk_eqb in Hc by lia. apply Z.eqb_eq in Hc.
  assert (TR0 : TC.truth (EPI.mrx_retry fr) = false) by (unfold TC.truth; rewrite Hc; reflexivity).
  clear Hc.
  (* run 2, 0x84cc0 .. 0x84ce8: M.desk_counter_valid, a4 = send; it stops at `beqz a0`. *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
  { mrxd_awr2 U19 U253'. }
  mrxd_md mdB.
  assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 88 <= a < TA_M + 92) -> ~ (TA_OW + 204 <= a < TA_OW + 208) ->
    aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
  { intros a Ha H1 H2. rewrite <- (KA1 a Ha H1 H2).
    apply (kept_of_frame _ _ _ _ _ (fun x => (TA_M + 88 <= x < TA_M + 92) \/ (TA_OW + 204 <= x < TA_OW + 208)) HFr);
      [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
    intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U19, ?U253', ?U290' in Hx; lia). }
  clear HF HFr HG KA1. rename ms into ms2.
  psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
  (* either way (the second `beqz a3` is decided by the first), to D5 *)
  all: clear Hc.
  all: paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D5); [mrxd_awr2 U19 U253' |].
  all: mrxd_md mdC.
  all: assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 88 <= a < TA_M + 92) -> ~ (TA_OW + 204 <= a < TA_OW + 208) ->
    aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a)
    by (intros a Ha H1 H2; rewrite <- (KA2 a Ha H1 H2);
        apply (kept_of_frame _ _ _ _ _ (fun x => (TA_M + 88 <= x < TA_M + 92) \/ (TA_OW + 204 <= x < TA_OW + 208)) HFr);
        [ intros b wlo whi x Hin Hx; cbv beta; mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U19, ?U253', ?U290' in Hx; lia)
        | exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)] ]).
  all: clear HF HFr HG.
  all: mrxd_chunk HS 4%nat 0%nat U253' (TW.OW_acks Bwc + 1) DACK VA.
  all: mrxd_chunk HS 3%nat 0%nat U19 0 (@eq_refl _ (Z_to_bv 64 0)) VF.
  all: assert (HTW : tw_at TMAP_A (aview segs (w_H Wc) (ms_mem ms)) (mrxd_B4 fr Bwc))
    by (rewrite (mrxd_B4_0 fr Bwc TR0); unfold mrxd_B1; apply (mrxd_world1 Bwc _ _ _ Htw VA VF);
        intros x Hx N1 N2; pose proof (TMAP_A_hull x Hx) as Hh; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh;
        apply KA; lia).
  all: assert (HFB : mrxd_fb fr Wc (ms_mem ms))
    by (apply (mrxd_fb_kept Wc mem2 (ms_mem ms) Hfb0 Hfa0 ltac:(lia));
        [ intros Hl31; destruct (mrxd_fa30_out fr _ Hap Hl31 eq_refl) as (N1 & N2 & N3 & N4); apply KA; lia
        | intros s Hs; apply KA; unfold SHADOW_OFF in Hs; lia ]).
  all: assert (HM5 : EPI.mrx_data5 fr (mrxd_B4 fr Bwc) = Some (B3, tt))
    by (apply (mrxd_data4_d5 fr _ B3); [rewrite TR0, andb_false_r; reflexivity | exact Hm4]).
  all: pmkst HS.
  all: rewrite (mrxd_pcl OFF_D5 14996 eq_refl).
  all: mrxd_regs3 HS EE regs2 F2 F3 F4.
  all: mrxd_keep HS EE regs2 (8%bv : bv 5) 8%nat Q8.
  all: mrxd_keep HS EE regs2 (18%bv : bv 5) 18%nat Q18.
  all: mrxd_keep HS EE regs2 (19%bv : bv 5) 19%nat Q19.
  all: mrxd_keep HS EE regs2 (20%bv : bv 5) 20%nat Q20.
  all: mrxd_reg HS (12%bv : bv 5) (Z_to_bv 64 TA_OW) Q12 ltac:(exact (mrxd_den_atom E0 _ _ E253)).
  all: mrxd_reg HS (13%bv : bv 5) (Z_to_bv 64 (EPI.mrx_retry fr)) Q13 ltac:(exact DR).
  all: mrxd_reg HS (14%bv : bv 5) (Z_to_bv 64 (bv_swrap 32 (EPI.mrx_send fr))) Q14 ltac:(exact DSd).
  all: exact (mrxd_to_d5 Wc (mrxd_B4 fr Bwc) regs2 mem2 (ms_regs ms) (ms_mem ms) mdC B3 HK5 HJ Hmo Hsp Hgp Htp
    F2 F3 F4 Hsv ltac:(intros a Ha; apply KA; lia) HTW HFB Hhdr Ham Hfa0 (eq_trans Q8 R8) Q12 Q13 Q14
    (eq_trans Q18 R18) (eq_trans Q19 R19) (eq_trans Q20 R20) HM5 Htk Hr).
- (* retry <> 0: the backoff *)
  rewrite DR in Hc. cbn [branch_taken sv_denot] in Hc. rewrite EPI.mrxk_eqb in Hc by lia. apply Z.eqb_neq in Hc.
  assert (TR1 : TC.truth (EPI.mrx_retry fr) = true)
    by (unfold TC.truth; rewrite (proj2 (Z.eqb_neq _ _) Hc); reflexivity).
  clear Hc.
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
    let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.
  (* M.backoff_until's 8 bytes join the state *)
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
    pose proof (st_ok_pi_add_region Ex ss (restrict Hh m) mrxd_bk HS eq_refl
      ltac:(unfold mrxd_bk, region_ok;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
            rewrite U19; split; [lia|]; split; [lia|];
            split; [intros o Ho; apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw); apply mrxd_inG; lia
                   | constructor])
      ltac:(cbn [ss_mem YP09.all_disjoint]; unfold YP09.extent_disjoint, mrxd_bk;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
            rewrite ?Usp, ?U19, ?U253', ?U290'; repeat split; lia)) as HSb end.
  clear HS.
  lazymatch type of HSb with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
    let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HSb end.
  rename HSb into HS.
  (* run 2, 0x84cc4 .. 0x84ce8: the backoff stored at M + 56, M.desk_counter_valid, a4 = send; it stops at `beqz a0`. *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
  { mrxd_awr2 U19 U253'. }
  mrxd_md mdB.
  assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 88 <= a < TA_M + 92) -> ~ (TA_OW + 204 <= a < TA_OW + 208) ->
    ~ (TA_M + 56 <= a < TA_M + 64) -> aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
  { intros a Ha H1 H2 H3. rewrite <- (KA1 a Ha H1 H2).
    apply (kept_of_frame _ _ _ _ _ (fun x => (TA_M + 88 <= x < TA_M + 92) \/ (TA_OW + 204 <= x < TA_OW + 208) \/
      (TA_M + 56 <= x < TA_M + 64)) HFr);
      [| exact Ha | intros [Hx|[Hx|Hx]]; [exact (H1 Hx) | exact (H2 Hx) | exact (H3 Hx)]].
    intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U19, ?U253', ?U290' in Hx; lia). }
  clear HF HFr HG KA1. rename ms into ms2.
  psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
  + (* M.desk_counter_valid = 0: to D5 *)
    rewrite DDV in Hc. cbn [branch_taken sv_denot] in Hc. rewrite EPI.mrxk_eqb in Hc by lia. apply Z.eqb_eq in Hc.
    rename Hc into DV0.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D5).
    { mrxd_awr2 U19 U253'. }
    mrxd_md mdC.
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 88 <= a < TA_M + 92) -> ~ (TA_OW + 204 <= a < TA_OW + 208) ->
      ~ (TA_M + 56 <= a < TA_M + 64) -> aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
    { intros a Ha H1 H2 H3. rewrite <- (KA2 a Ha H1 H2 H3).
      apply (kept_of_frame _ _ _ _ _ (fun x => (TA_M + 88 <= x < TA_M + 92) \/ (TA_OW + 204 <= x < TA_OW + 208) \/
        (TA_M + 56 <= x < TA_M + 64)) HFr);
        [| exact Ha | intros [Hx|[Hx|Hx]]; [exact (H1 Hx) | exact (H2 Hx) | exact (H3 Hx)]].
      intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U19, ?U253', ?U290' in Hx; lia). }
    clear HF HFr HG.
    mrxd_chunk HS 5%nat 0%nat U253' (TW.OW_acks Bwc + 1) DACK VA.
    mrxd_chunk HS 4%nat 0%nat U19 0 (@eq_refl _ (Z_to_bv 64 0)) VF.
    mrxd_chunk HS 0%nat 0%nat U19 (TS0.u64 (TW.g_now Bwc + TC.h_ms_m (TW.Cfg_backoff_ms Bwc))) DBK VB.
    assert (HTW : tw_at TMAP_A (aview segs (w_H Wc) (ms_mem ms)) (mrxd_B4 fr Bwc)).
    { rewrite (mrxd_B4_1 fr Bwc TR1), FBK. unfold mrxd_B1. apply (mrxd_world4 Bwc _ _ _ _ Htw VA VF VB).
      intros x Hx N1 N2 N3. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
      apply KA; lia. }
    assert (HFB : mrxd_fb fr Wc (ms_mem ms)).
    { apply (mrxd_fb_kept Wc mem2 (ms_mem ms) Hfb0 Hfa0 ltac:(lia)).
      - intros Hl31. destruct (mrxd_fa30_out fr _ Hap Hl31 eq_refl) as (N1 & N2 & N3 & N4). apply KA; lia.
      - intros s Hs. apply KA; unfold SHADOW_OFF in Hs; lia. }
    assert (HM5 : EPI.mrx_data5 fr (mrxd_B4 fr Bwc) = Some (B3, tt)).
    { apply (mrxd_data4_d5 fr _ B3); [|exact Hm4]. rewrite FV, DV0. reflexivity. }
    pmkst HS. rewrite (mrxd_pcl OFF_D5 14996 eq_refl).
    mrxd_regs3 HS EE regs2 F2 F3 F4.
    mrxd_keep HS EE regs2 (8%bv : bv 5) 8%nat Q8. mrxd_keep HS EE regs2 (18%bv : bv 5) 18%nat Q18.
    mrxd_keep HS EE regs2 (19%bv : bv 5) 19%nat Q19. mrxd_keep HS EE regs2 (20%bv : bv 5) 20%nat Q20.
    mrxd_reg HS (12%bv : bv 5) (Z_to_bv 64 TA_OW) Q12 ltac:(exact (mrxd_den_atom E0 _ _ E253)).
    mrxd_reg HS (13%bv : bv 5) (Z_to_bv 64 (EPI.mrx_retry fr)) Q13 ltac:(exact DR).
    mrxd_reg HS (14%bv : bv 5) (Z_to_bv 64 (bv_swrap 32 (EPI.mrx_send fr))) Q14 ltac:(exact DSd).
    exact (mrxd_to_d5 Wc (mrxd_B4 fr Bwc) regs2 mem2 (ms_regs ms) (ms_mem ms) mdC B3 HK5 HJ Hmo Hsp Hgp Htp
      F2 F3 F4 Hsv ltac:(intros a Ha; apply KA; lia) HTW HFB Hhdr Ham Hfa0 (eq_trans Q8 R8) Q12 Q13 Q14
      (eq_trans Q18 R18) (eq_trans Q19 R19) (eq_trans Q20 R20) HM5 Htk Hr).
  + (* M.desk_counter_valid <> 0: the counter test *)
    rewrite DDV in Hc. cbn [branch_taken sv_denot] in Hc. rewrite EPI.mrxk_eqb in Hc by lia. apply Z.eqb_neq in Hc.
    rename Hc into DV1.
    (* run 3, 0x84cec .. 0x84cf4: M.desk_counter; it stops at `beq a4, a0`. *)
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
    { mrxd_awr2 U19 U253'. }
    mrxd_md mdC.
    assert (KA3 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 88 <= a < TA_M + 92) -> ~ (TA_OW + 204 <= a < TA_OW + 208) ->
      ~ (TA_M + 56 <= a < TA_M + 64) -> aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
    { intros a Ha H1 H2 H3. rewrite <- (KA2 a Ha H1 H2 H3).
      apply (kept_of_frame _ _ _ _ _ (fun x => (TA_M + 88 <= x < TA_M + 92) \/ (TA_OW + 204 <= x < TA_OW + 208) \/
        (TA_M + 56 <= x < TA_M + 64)) HFr);
        [| exact Ha | intros [Hx|[Hx|Hx]]; [exact (H1 Hx) | exact (H2 Hx) | exact (H3 Hx)]].
      intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U19, ?U253', ?U290' in Hx; lia). }
    clear HF HFr HG KA2. rename ms into ms3.
    psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
    * (* send = M.desk_counter: the duplicate, to TICK *)
      rewrite DSd, DDC in Hc. cbn [branch_taken] in Hc. rewrite EPI.mrx_eqb_sw in Hc by lia. apply Z.eqb_eq in Hc.
      assert (EB3 : B3 = mrxd_B4 fr Bwc).
      { apply (mrxd_data4_tick fr _ B3); [|exact Hm4].
        rewrite FV, FC, TR1. unfold TC.truth. rewrite (proj2 (Z.eqb_neq _ _) DV1), Hc, Z.eqb_refl. reflexivity. }
      subst B3.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
      { mrxd_awr2 U19 U253'. }
      mrxd_md mdD.
      assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 88 <= a < TA_M + 92) -> ~ (TA_OW + 204 <= a < TA_OW + 208) ->
        ~ (TA_M + 56 <= a < TA_M + 64) -> aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
      { intros a Ha H1 H2 H3. rewrite <- (KA3 a Ha H1 H2 H3).
        apply (kept_of_frame _ _ _ _ _ (fun x => (TA_M + 88 <= x < TA_M + 92) \/ (TA_OW + 204 <= x < TA_OW + 208) \/
          (TA_M + 56 <= x < TA_M + 64)) HFr);
          [| exact Ha | intros [Hx|[Hx|Hx]]; [exact (H1 Hx) | exact (H2 Hx) | exact (H3 Hx)]].
        intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U19, ?U253', ?U290' in Hx; lia). }
      clear HF HFr HG.
      mrxd_chunk HS 5%nat 0%nat U253' (TW.OW_acks Bwc + 1) DACK VA.
      mrxd_chunk HS 4%nat 0%nat U19 0 (@eq_refl _ (Z_to_bv 64 0)) VF.
      mrxd_chunk HS 0%nat 0%nat U19 (TS0.u64 (TW.g_now Bwc + TC.h_ms_m (TW.Cfg_backoff_ms Bwc))) DBK VB.
      assert (HTW : tw_at TMAP_A (aview segs (w_H Wc) (ms_mem ms)) (mrxd_B4 fr Bwc)).
      { rewrite (mrxd_B4_1 fr Bwc TR1), FBK. unfold mrxd_B1. apply (mrxd_world4 Bwc _ _ _ _ Htw VA VF VB).
        intros x Hx N1 N2 N3. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
        apply KA; lia. }
      pmkst HS. rewrite (mrxd_pcl OFF_TICK 15288 eq_refl).
      mrxd_regs3 HS EE regs2 F2 F3 F4.
      apply (mrxd_exit (MRX_PC OFF_TICK) (R_TICK Bw' r) Wc (mrxd_B4 fr Bwc) regs2 mem2 (ms_regs ms) (ms_mem ms) mdD
        HKT HJ Hmo Hsp Hgp Htp F2 F3 F4 Hsv ltac:(intros a Ha; apply KA; lia) HTW).
      unfold R_TICK. split; [exact Htk | exact Hr].
    * (* send <> M.desk_counter: to D5 *)
      rewrite DSd, DDC in Hc. cbn [branch_taken] in Hc. rewrite EPI.mrx_eqb_sw in Hc by lia. apply Z.eqb_neq in Hc.
      rename Hc into SNE.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D5).
      { mrxd_awr2 U19 U253'. }
      mrxd_md mdD.
      assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 88 <= a < TA_M + 92) -> ~ (TA_OW + 204 <= a < TA_OW + 208) ->
        ~ (TA_M + 56 <= a < TA_M + 64) -> aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
      { intros a Ha H1 H2 H3. rewrite <- (KA3 a Ha H1 H2 H3).
        apply (kept_of_frame _ _ _ _ _ (fun x => (TA_M + 88 <= x < TA_M + 92) \/ (TA_OW + 204 <= x < TA_OW + 208) \/
          (TA_M + 56 <= x < TA_M + 64)) HFr);
          [| exact Ha | intros [Hx|[Hx|Hx]]; [exact (H1 Hx) | exact (H2 Hx) | exact (H3 Hx)]].
        intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U19, ?U253', ?U290' in Hx; lia). }
      clear HF HFr HG.
      mrxd_chunk HS 5%nat 0%nat U253' (TW.OW_acks Bwc + 1) DACK VA.
      mrxd_chunk HS 4%nat 0%nat U19 0 (@eq_refl _ (Z_to_bv 64 0)) VF.
      mrxd_chunk HS 0%nat 0%nat U19 (TS0.u64 (TW.g_now Bwc + TC.h_ms_m (TW.Cfg_backoff_ms Bwc))) DBK VB.
      assert (HTW : tw_at TMAP_A (aview segs (w_H Wc) (ms_mem ms)) (mrxd_B4 fr Bwc)).
      { rewrite (mrxd_B4_1 fr Bwc TR1), FBK. unfold mrxd_B1. apply (mrxd_world4 Bwc _ _ _ _ Htw VA VF VB).
        intros x Hx N1 N2 N3. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
        apply KA; lia. }
      assert (HFB : mrxd_fb fr Wc (ms_mem ms)).
      { apply (mrxd_fb_kept Wc mem2 (ms_mem ms) Hfb0 Hfa0 ltac:(lia)).
        - intros Hl31. destruct (mrxd_fa30_out fr _ Hap Hl31 eq_refl) as (N1 & N2 & N3 & N4). apply KA; lia.
        - intros s Hs. apply KA; unfold SHADOW_OFF in Hs; lia. }
      assert (HM5 : EPI.mrx_data5 fr (mrxd_B4 fr Bwc) = Some (B3, tt)).
      { apply (mrxd_data4_d5 fr _ B3); [|exact Hm4].
        rewrite FC, (proj2 (Z.eqb_neq _ _) SNE), andb_false_r. reflexivity. }
      pmkst HS. rewrite (mrxd_pcl OFF_D5 14996 eq_refl).
      mrxd_regs3 HS EE regs2 F2 F3 F4.
      mrxd_keep HS EE regs2 (8%bv : bv 5) 8%nat Q8. mrxd_keep HS EE regs2 (18%bv : bv 5) 18%nat Q18.
      mrxd_keep HS EE regs2 (19%bv : bv 5) 19%nat Q19. mrxd_keep HS EE regs2 (20%bv : bv 5) 20%nat Q20.
      mrxd_reg HS (12%bv : bv 5) (Z_to_bv 64 TA_OW) Q12 ltac:(exact (mrxd_den_atom E0 _ _ E253)).
      mrxd_reg HS (13%bv : bv 5) (Z_to_bv 64 (EPI.mrx_retry fr)) Q13 ltac:(exact DR).
      mrxd_reg HS (14%bv : bv 5) (Z_to_bv 64 (bv_swrap 32 (EPI.mrx_send fr))) Q14 ltac:(exact DSd).
      exact (mrxd_to_d5 Wc (mrxd_B4 fr Bwc) regs2 mem2 (ms_regs ms) (ms_mem ms) mdD B3 HK5 HJ Hmo Hsp Hgp Htp
        F2 F3 F4 Hsv ltac:(intros a Ha; apply KA; lia) HTW HFB Hhdr Ham Hfa0 (eq_trans Q8 R8) Q12 Q13 Q14
        (eq_trans Q18 R18) (eq_trans Q19 R19) (eq_trans Q20 R20) HM5 Htk Hr).
Qed.

End seg.
