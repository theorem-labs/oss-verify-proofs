(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 1406 of its 1512 lines of code are new or changed and 924 lines of the source are left out. *)
(* m_rx_seg_data: the DATA segment of the image-B walk of m_rx (statement lib/B/Prog/m_rx_cg.v, kit
   lib/B/Prog/m_rx_seg_kit.v). Exported: mrx_seg_data, from the TICK cut's continuation to the DATA cut's: from the
   DATA cut (0x84df4 = +0x1d8, cmd DATA, the model's UMR.mr_data) the code reaches the TICK cut (0x84fc0 = +0x3a4) at
   the model's world.

   This file cuts the segment twice more, with cuts of the kit's form (mrx_at / mrx_K at MRX_PC off with a local R):
     D5 0x84e48 (+0x22c)  the desk counter and the first body byte, the model from UMR.mr_data3 (R_D5);
     D6 0x84e80 (+0x264)  OW.dn[OW.ndata] and OW.ndata, the model from UMR.mr_dn (R_D6).
   Each part is the kit's symbolic run (TransportGRunB.v paj_run_to_x over the inner journal) from a state built at
   its cut, split at each branch the run cannot decide, and closed at the next cut's mrx_K:
     DATA (+0x1d8 .. +0x228): a2 = &OW; OW.acks + 1, whose overflow branch to the trap word is refuted by the model
       (int_inc is None at INT_MAX: UMR.mr_inc_trap); a3 = f.retry (the struct's 2 bytes at sp + 30); OW.acks + 1
       stored at OW + 204, 0 at M + 88 (fail); retry <> 0: g_cfg.backoff_ms * 1000 + g_now stored at M + 56
       (backoff_until; the region of these 8 bytes joins the state on that side only); M.desk_counter_valid <> 0,
       retry <> 0 and f.send = M.desk_counter goes to TICK (the model's duplicate), else to D5.
     D5 (+0x22c .. +0x260): 1 stored at M + 76, f.send at M + 80; f.body_len <> 1 goes to D6. body_len = 1 (a case
       of the proof, before the run): f.body = fa + 30 (a fact of its atom puts it in [30, 2 ^ 47 - 2], so the null
       check is decided), the frame byte fa + 30 is a read-only region and the run's shadow entry is [fa + 30,
       fa + 31) (addressable: trans_src_ok_rd of the frame at the current state, n >= 31); the check of the 1-byte
       load is decided by it, so __asan_report_load1 (0x8500c) is not reached; byte 0 goes to TICK, else to D6.
     D6 (+0x264 .. +0x30c): k = OW.ndata (signed); 1 < k: k + 1 (its overflow branch refuted by the model) stored at
       OW + 220, to TICK. Else 0 <= k (the model's None below 0), so k = 0 or k = 1, pinned; OW.dn[k]'s 22 bytes join
       the state as a writable region of G and the null and pointer-overflow tests of x = OW + 256 + 24 k and the
       four checked stores at x (+ 0, + 8, + 16, + 20) are decided by the run's facts and its shadow entry of OW's
       304 bytes (zero shadow, trans_mrx_cells), so the trap word and __asan_report_store8 / 4 / 2 are not reached;
       k + 1 stored at OW + 220; to TICK.
   At each cut the world relation is the kit's mrx_tw_start / mrx_tw_step / mrx_tw_end over the part's stores (their
   bytes read from the chunks of the last state); every other byte is kept (a run writes only its regions' windows),
   so the frame, the struct and the saved slots carry over (the written bytes are bytes of mrx_wr). The image-free
   pieces (the world B1 after OW.acks and M.fail, its g_now and g_cfg.backoff_ms, the denotations of loaded atoms) are
   image A's lib/A/Prog/m_rx_seg_data.v's (AD); the model's cut is lib/U/Prog/T/m_rx.v's (UMR). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  m_set_cg m_wake_cg m_maybe_online_cg m_tick_cg spec_read_frame_cg host_offset_cg desk_named_cg check_state_data_cg
  m_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require m_rx.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_kit m_rx_seg_data.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  TransportGRunB TransportGFrameB CanKit YC1g YC1h m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
Module UMR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T.m_rx.
Module AK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_kit.
Module AD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_data.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The model                                                           *)
(* ------------------------------------------------------------------ *)

(* The worlds of UMR.mr_data: AD.mrxd_B1 after OW.acks and M.fail (image-free), B4 after the backoff, B5 after the
   desk counter, B6 after OW.dn[k]. *)
Definition mrxd_B4 (fr : TI.tframe) (n : Z) (Bw : list byte) : list byte :=
  if TC.truth (DSpec.sf_retry (mrx_f fr n)) then TW.set_M_backoff_until (AD.mrxd_B1 Bw) (AD.mrxd_bkv (AD.mrxd_B1 Bw))
  else AD.mrxd_B1 Bw.
Definition mrxd_B5 (fr : TI.tframe) (n : Z) (Bw : list byte) : list byte :=
  TW.set_M_desk_counter_valid (TW.set_M_desk_counter Bw (DSpec.sf_send (mrx_f fr n))) 1.
Definition mrxd_B6 (fr : TI.tframe) (n : Z) (Bw : list byte) (k : Z) : list byte :=
  TC.set_OW_dn_retry (TC.set_OW_dn_counter (TC.set_OW_dn_len
    (TC.set_OW_dn_body Bw k (TI.tf_addr fr + DSpec.sf_body (mrx_f fr n)))
    k (DSpec.sf_body_len (mrx_f fr n))) k (DSpec.sf_send (mrx_f fr n))) k (DSpec.sf_retry (mrx_f fr n)).

(* The first body byte, as the model reads it (at SPEC_OK the body is at 30). *)
Definition mrxd_b30 (fr : TI.tframe) : Z := DSpec.bz (nth 30 (TI.tf_bytes fr) (DSpec.b8 0)).

Lemma mrxd_data_inv : forall fr n Bw B3, UMR.mr_data fr n Bw = Some (B3, tt) ->
  TW.OW_acks Bw <> TC.INT_MAX /\ UMR.mr_data2 fr n (mrxd_B4 fr n Bw) = Some (B3, tt).
Proof.
intros fr n Bw B3 H. unfold UMR.mr_data, TC.int_inc in H. revert H.
destruct (Z.eqb_spec (TW.OW_acks Bw) TC.INT_MAX) as [E|E]; intros H; [discriminate H|].
split; [exact E | exact H].
Qed.

Lemma mrxd_data2_tick : forall fr n B4 B3,
  TC.truth (TW.M_desk_counter_valid B4) && (DSpec.sf_send (mrx_f fr n) =? TW.M_desk_counter B4) &&
    TC.truth (DSpec.sf_retry (mrx_f fr n)) = true ->
  UMR.mr_data2 fr n B4 = Some (B3, tt) -> B3 = B4.
Proof.
intros fr n B4 B3 Hc H. unfold UMR.mr_data2 in H. cbv zeta in H. rewrite Hc in H.
destruct (mrx_some_inv _ _ _ _ _ _ H) as [E _]. symmetry. exact E.
Qed.

Lemma mrxd_data2_d3 : forall fr n B4 B3,
  TC.truth (TW.M_desk_counter_valid B4) && (DSpec.sf_send (mrx_f fr n) =? TW.M_desk_counter B4) &&
    TC.truth (DSpec.sf_retry (mrx_f fr n)) = false ->
  UMR.mr_data2 fr n B4 = Some (B3, tt) -> UMR.mr_data3 fr n B4 = Some (B3, tt).
Proof. intros fr n B4 B3 Hc H. unfold UMR.mr_data2 in H. cbv zeta in H. rewrite Hc in H. exact H. Qed.

Lemma mrxd_at8 : forall fr n, DSpec.sf_body (mrx_f fr n) = 30 ->
  DSpec.at8 (skipn (Z.to_nat (DSpec.sf_body (mrx_f fr n))) (TI.tf_bytes fr)) 0 = mrxd_b30 fr.
Proof.
intros fr n Hb. rewrite Hb. change (Z.to_nat 30) with 30%nat. unfold DSpec.at8, mrxd_b30.
rewrite UMR.mr_nth_skipn. reflexivity.
Qed.

Lemma mrxd_data3_tick : forall fr n B4 B3, DSpec.sf_body (mrx_f fr n) = 30 ->
  DSpec.sf_body_len (mrx_f fr n) = 1 -> mrxd_b30 fr = 0 ->
  UMR.mr_data3 fr n B4 = Some (B3, tt) -> B3 = mrxd_B5 fr n B4.
Proof.
intros fr n B4 B3 Hb H1 H2 H. unfold UMR.mr_data3 in H. cbv zeta in H. rewrite (mrxd_at8 fr n Hb), H1, H2 in H.
replace ((1 =? 1) && (0 =? 0)) with true in H by reflexivity.
destruct (mrx_some_inv _ _ _ _ _ _ H) as [E _]. symmetry. exact E.
Qed.

Lemma mrxd_data3_dn : forall fr n B4 B3, DSpec.sf_body (mrx_f fr n) = 30 ->
  ((DSpec.sf_body_len (mrx_f fr n) =? 1) && (mrxd_b30 fr =? 0)) = false ->
  UMR.mr_data3 fr n B4 = Some (B3, tt) -> UMR.mr_dn fr n (mrxd_B5 fr n B4) = Some (B3, tt).
Proof.
intros fr n B4 B3 Hb Hc H. unfold UMR.mr_data3 in H. cbv zeta in H. rewrite (mrxd_at8 fr n Hb), Hc in H. exact H.
Qed.

Lemma mrxd_dn_hi : forall fr n B5 B3, 2 <= TW.OW_ndata B5 -> UMR.mr_dn fr n B5 = Some (B3, tt) ->
  TW.OW_ndata B5 <> TC.INT_MAX /\ B3 = TW.set_OW_ndata B5 (TW.OW_ndata B5 + 1).
Proof.
intros fr n B5 B3 Hk H. unfold UMR.mr_dn, TC.int_inc in H. cbv zeta in H.
replace (TW.OW_ndata B5 <? 2) with false in H by (symmetry; apply Z.ltb_ge; lia). cbv beta iota in H. revert H.
destruct (Z.eqb_spec (TW.OW_ndata B5) TC.INT_MAX) as [E|E]; intros H; [discriminate H|].
destruct (mrx_some_inv _ _ _ _ _ _ H) as [E2 _]. split; [exact E | symmetry; exact E2].
Qed.

Lemma mrxd_dn_lo : forall fr n B5 B3, TW.OW_ndata B5 < 2 -> UMR.mr_dn fr n B5 = Some (B3, tt) ->
  0 <= TW.OW_ndata B5 /\ B3 = TW.set_OW_ndata (mrxd_B6 fr n B5 (TW.OW_ndata B5)) (TW.OW_ndata B5 + 1).
Proof.
intros fr n B5 B3 Hk H. unfold UMR.mr_dn, TC.int_inc in H. cbv zeta in H.
replace (TW.OW_ndata B5 <? 2) with true in H by (symmetry; apply Z.ltb_lt; lia). revert H.
destruct (Z.ltb_spec (TW.OW_ndata B5) 0) as [L|L]; intros H; [discriminate H|].
replace (TW.OW_ndata B5 =? TC.INT_MAX) with false in H by (symmetry; apply Z.eqb_neq; unfold TC.INT_MAX; lia).
destruct (mrx_some_inv _ _ _ _ _ _ H) as [E2 _]. split; [exact L | symmetry; exact E2].
Qed.

(* M.desk_counter_valid and M.desk_counter of B4 are B's (the stores are at M + 88, OW + 204, M + 56). *)
Lemma mrxd_B4_u : forall fr n Bw k', length Bw = Z.to_nat TW.W_LEN -> TW.OFF_M + 76 <= k' -> k' + 4 <= TW.OFF_M + 84 ->
  TW.u_at (mrxd_B4 fr n Bw) k' 4 = TW.u_at Bw k' 4.
Proof.
intros fr n Bw k' HL H1 H2. pose proof (AD.mrxd_B1_len Bw HL) as L1.
assert (L0 : length (TW.upd Bw (TW.OFF_OW + 204) (TW.put 4 (TW.OW_acks Bw + 1))) = Z.to_nat TW.W_LEN)
  by (apply AD.mrxd_len_put; [exact HL | unfold TW.OFF_OW; lia | unfold TW.OFF_OW, TW.W_LEN; lia]).
assert (E1 : TW.u_at (AD.mrxd_B1 Bw) k' 4 = TW.u_at Bw k' 4).
{ unfold AD.mrxd_B1, TW.set_M_fail, TW.set_OW_acks, TW.A_M_fail, TW.A_OW_acks.
  rewrite (AD.mrxd_u_out _ _ 4 _ _ 4 L0) by (unfold TW.OFF_M, TW.W_LEN in *; cbn; lia).
  rewrite (AD.mrxd_u_out _ _ 4 _ _ 4 HL) by (unfold TW.OFF_M, TW.OFF_OW, TW.W_LEN in *; cbn; lia).
  reflexivity. }
unfold mrxd_B4. destruct (TC.truth (DSpec.sf_retry (mrx_f fr n))); [|exact E1].
unfold TW.set_M_backoff_until, TW.A_M_backoff_until.
rewrite (AD.mrxd_u_out _ _ 8 _ _ 4 L1) by (unfold TW.OFF_M, TW.W_LEN in *; cbn; lia). exact E1.
Qed.

Lemma mrxd_B4_0 : forall fr n Bw, TC.truth (DSpec.sf_retry (mrx_f fr n)) = false -> mrxd_B4 fr n Bw = AD.mrxd_B1 Bw.
Proof. intros fr n Bw H. unfold mrxd_B4. rewrite H. reflexivity. Qed.
Lemma mrxd_B4_1 : forall fr n Bw, TC.truth (DSpec.sf_retry (mrx_f fr n)) = true ->
  mrxd_B4 fr n Bw = TW.set_M_backoff_until (AD.mrxd_B1 Bw) (AD.mrxd_bkv (AD.mrxd_B1 Bw)).
Proof. intros fr n Bw H. unfold mrxd_B4. rewrite H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Bytes and the values the code computes                              *)
(* ------------------------------------------------------------------ *)

(* addiw x, a, c: the 32-bit sum, sign-extended. *)
Lemma mrxd_den_addw : forall E a x c, sv_denot E a = Z_to_bv 64 x ->
  sv_denot E (SAluw ALU_ADD a (SLit c)) = Z_to_bv 64 (bv_swrap 32 (x + c)).
Proof.
intros E a x c H. cbn [sv_denot alu32 alu low32]. rewrite H. rewrite LMem.sext_small. f_equal.
unfold bv_signed. rewrite bv_add_unsigned.
rewrite !(LMem.extract_low_mod 32) by lia. rewrite !Z_to_bv_unsigned.
apply UMR.mr_swrap32_mod. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite !UMR.mr_mod32_64. rewrite Zmod_mod. rewrite <- Zplus_mod. reflexivity.
Qed.

(* g_cfg.backoff_ms * 1000 + g_now (lwu; li 1000; mul; add). *)
Lemma mrxd_bk_den : forall E (ng nb : nat) g u, ew E ng = Z_to_bv 64 g -> ew E nb = Z_to_bv 64 u ->
  0 <= g < 2 ^ 64 -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SExt false 32 (SOff nb 0)) (SLit 1000)) (SOff ng 0)) =
  Z_to_bv 64 (TS0.u64 (g + TC.h_ms_m u)).
Proof.
intros E ng nb g u Hg Hb Rg Ru.
change (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SExt false 32 (SOff nb 0)) (SLit 1000)) (SOff ng 0))) with
  (alu64 ALU_ADD (mul_div M_MUL (sv_denot E (SExt false 32 (SOff nb 0))) (sv_denot E (SLit 1000)))
     (sv_denot E (SOff ng 0))).
rewrite (AD.mrxd_den_zext E nb u 32 Hb Ru ltac:(lia)), (AD.mrxd_den_atom E ng g Hg).
cbn [sv_denot alu64 alu mul_div]. apply bv_eq.
rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned.
unfold TS0.u64, TC.h_ms_m, TS0.u64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small u (2 ^ 64)) by lia. rewrite (Z.mod_small 1000 (2 ^ 64)) by lia.
rewrite (Z.mod_small g (2 ^ 64)) by lia. rewrite Zmod_mod.
rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. f_equal. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* The bytes the segment writes                                        *)
(* ------------------------------------------------------------------ *)

(* M.backoff_until, M.desk_counter_valid, M.desk_counter, M.fail, OW.acks, OW.ndata and OW.dn[0 .. 1]. *)
Definition mrxd_W (x : Z) : Prop :=
  (TB_M + 56 <= x < TB_M + 64) \/ (TB_M + 76 <= x < TB_M + 84) \/ (TB_M + 88 <= x < TB_M + 92) \/
  (TB_OW + 204 <= x < TB_OW + 208) \/ (TB_OW + 220 <= x < TB_OW + 224) \/
  (exists k, 0 <= k <= 1 /\ TB_OW + 256 + 24 * k <= x < TB_OW + 278 + 24 * k).

Lemma mrxd_wr : forall x, mrxd_W x -> mrx_wr x.
Proof.
intros x [H|[H|[H|[H|[H|(k & Hk & H)]]]]]; unfold mrx_wr.
- do 8 right; left. unfold twb_fld, TW.A_M_backoff_until, TW.OFF_M. lia.
- destruct (Z_lt_le_dec x (TB_M + 80)).
  + do 9 right; left. unfold twb_fld, TW.A_M_desk_counter_valid, TW.OFF_M. lia.
  + do 10 right; left. unfold twb_fld, TW.A_M_desk_counter, TW.OFF_M. lia.
- do 11 right; left. unfold twb_fld, TW.A_M_fail, TW.OFF_M. lia.
- do 16 right; left. unfold twb_fld, TW.A_OW_acks, TW.OFF_OW. lia.
- do 20 right; left. unfold twb_fld, TW.A_OW_ndata, TW.OFF_OW. lia.
- do 26 right. exists k. split; [unfold TW.OW_dn_N; lia|]. unfold twb_fld, TC.A_OW_dn_body, TW.OFF_OW. lia.
Qed.

(* M's and OW's payload bytes are bytes of G. *)
Lemma mrxd_inG : forall a, (TB_M <= a < TB_M + 1648) \/ (TB_OW <= a < TB_OW + 304) -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. destruct Ha as [Ha|Ha].
- exists (TB_M, TW.SZ_M). split; [exact (TMAP_B_in_G _ _ _ TMAP_B_M) | unfold in_zr, TW.SZ_M; cbn [fst snd]; lia].
- exists (TB_OW, TW.SZ_OW). split; [exact (TMAP_B_in_G _ _ _ TMAP_B_OW) | unfold in_zr, TW.SZ_OW; cbn [fst snd]; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* The world after each part's stores                                  *)
(* ------------------------------------------------------------------ *)

Lemma mrxd_world1 : forall Bw rdF rd0 ak,
  tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 204 + Z.of_nat j) = Some (YO0f.le_byte ak 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 88 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_OW + 204 <= x < TB_OW + 208) -> ~ (TB_M + 88 <= x < TB_M + 92) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_M_fail (TW.set_OW_acks Bw ak) 0).
Proof.
intros Bw rdF rd0 ak Htw VA VF Hk. unfold TW.set_M_fail, TW.set_OW_acks.
pose proof (mrx_tw_start rdF rd0 Bw Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 204 TW.A_OW_acks 4 ak H0 TMAP_B_OW
  ltac:(unfold TW.A_OW_acks; lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) VA) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 88 TW.A_M_fail 4 0 H1 TMAP_B_M
  ltac:(unfold TW.A_M_fail; lia) ltac:(lia) ltac:(unfold TW.SZ_M; lia) VF) as H2.
apply (mrx_tw_end rdF rd0 _ _ H2). intros x Hx HP. mrx_unP HP. apply Hk; [exact Hx | lia | lia].
Qed.

Lemma mrxd_world4 : forall Bw rdF rd0 ak bk,
  tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 204 + Z.of_nat j) = Some (YO0f.le_byte ak 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 88 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 8)%nat -> rdF (TB_M + 56 + Z.of_nat j) = Some (YO0f.le_byte bk 8 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_OW + 204 <= x < TB_OW + 208) -> ~ (TB_M + 88 <= x < TB_M + 92) ->
     ~ (TB_M + 56 <= x < TB_M + 64) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_M_backoff_until (TW.set_M_fail (TW.set_OW_acks Bw ak) 0) bk).
Proof.
intros Bw rdF rd0 ak bk Htw VA VF VB Hk. unfold TW.set_M_backoff_until, TW.set_M_fail, TW.set_OW_acks.
pose proof (mrx_tw_start rdF rd0 Bw Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 204 TW.A_OW_acks 4 ak H0 TMAP_B_OW
  ltac:(unfold TW.A_OW_acks; lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) VA) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 88 TW.A_M_fail 4 0 H1 TMAP_B_M
  ltac:(unfold TW.A_M_fail; lia) ltac:(lia) ltac:(unfold TW.SZ_M; lia) VF) as H2.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 56 TW.A_M_backoff_until 8 bk H2 TMAP_B_M
  ltac:(unfold TW.A_M_backoff_until; lia) ltac:(lia) ltac:(unfold TW.SZ_M; lia) VB) as H3.
apply (mrx_tw_end rdF rd0 _ _ H3). intros x Hx HP. mrx_unP HP. apply Hk; [exact Hx | lia | lia | lia].
Qed.

(* The world after D5's stores: M.desk_counter = send, M.desk_counter_valid = 1. *)
Lemma mrxd_world5 : forall Bw rdF rd0 send,
  tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 80 + Z.of_nat j) = Some (YO0f.le_byte send 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 76 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_M + 76 <= x < TB_M + 84) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_M_desk_counter_valid (TW.set_M_desk_counter Bw send) 1).
Proof.
intros Bw rdF rd0 send Htw VC VV Hk.
unfold TW.set_M_desk_counter_valid, TW.set_M_desk_counter.
pose proof (mrx_tw_start rdF rd0 Bw Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 80 TW.A_M_desk_counter 4 send H0 TMAP_B_M
  ltac:(unfold TW.A_M_desk_counter; lia) ltac:(lia) ltac:(unfold TW.SZ_M; lia) VC) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 76 TW.A_M_desk_counter_valid 4 1 H1 TMAP_B_M
  ltac:(unfold TW.A_M_desk_counter_valid; lia) ltac:(lia) ltac:(unfold TW.SZ_M; lia) VV) as H2.
apply (mrx_tw_end rdF rd0 _ _ H2). intros x Hx HP. mrx_unP HP. apply Hk; [exact Hx | lia].
Qed.

(* The world after D6's stores at k = i (0 or 1): OW.dn[i]'s four fields and OW.ndata. *)
Lemma mrxd_world6 : forall Bw rdF rd0 i body blen send retry nd,
  tw_at TMAP_B rd0 Bw -> 0 <= i <= 1 ->
  (forall j, (j < 8)%nat -> rdF (TB_OW + (256 + 24 * i) + Z.of_nat j) = Some (YO0f.le_byte body 8 j)) ->
  (forall j, (j < 8)%nat -> rdF (TB_OW + (264 + 24 * i) + Z.of_nat j) = Some (YO0f.le_byte blen 8 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + (272 + 24 * i) + Z.of_nat j) = Some (YO0f.le_byte send 4 j)) ->
  (forall j, (j < 2)%nat -> rdF (TB_OW + (276 + 24 * i) + Z.of_nat j) = Some (YO0f.le_byte retry 2 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 220 + Z.of_nat j) = Some (YO0f.le_byte nd 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_OW + 220 <= x < TB_OW + 224) ->
     ~ (TB_OW + 256 + 24 * i <= x < TB_OW + 278 + 24 * i) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_OW_ndata (TC.set_OW_dn_retry (TC.set_OW_dn_counter (TC.set_OW_dn_len
    (TC.set_OW_dn_body Bw i body) i blen) i send) i retry) nd).
Proof.
intros Bw rdF rd0 i body blen send retry nd Htw Hi VB VL VS VR VN Hk.
unfold TW.set_OW_ndata, TC.set_OW_dn_retry, TC.set_OW_dn_counter, TC.set_OW_dn_len, TC.set_OW_dn_body.
pose proof (mrx_tw_start rdF rd0 Bw Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW (256 + 24 * i) (TC.A_OW_dn_body i) 8 body H0 TMAP_B_OW
  ltac:(unfold TC.A_OW_dn_body; lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) VB) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW (264 + 24 * i) (TC.A_OW_dn_len i) 8 blen H1 TMAP_B_OW
  ltac:(unfold TC.A_OW_dn_len; lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) VL) as H2.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW (272 + 24 * i) (TC.A_OW_dn_counter i) 4 send H2 TMAP_B_OW
  ltac:(unfold TC.A_OW_dn_counter; lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) VS) as H3.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW (276 + 24 * i) (TC.A_OW_dn_retry i) 2 retry H3 TMAP_B_OW
  ltac:(unfold TC.A_OW_dn_retry; lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) VR) as H4.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 220 TW.A_OW_ndata 4 nd H4 TMAP_B_OW
  ltac:(unfold TW.A_OW_ndata; lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) VN) as H5.
apply (mrx_tw_end rdF rd0 _ _ H5). intros x Hx HP. mrx_unP HP. apply Hk; [exact Hx | lia | lia].
Qed.

(* The world after OW.ndata alone. *)
Lemma mrxd_world_nd : forall Bw rdF rd0 nd,
  tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 220 + Z.of_nat j) = Some (YO0f.le_byte nd 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_OW + 220 <= x < TB_OW + 224) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_OW_ndata Bw nd).
Proof.
intros Bw rdF rd0 nd Htw VN Hk. unfold TW.set_OW_ndata.
pose proof (mrx_tw_start rdF rd0 Bw Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 220 TW.A_OW_ndata 4 nd H0 TMAP_B_OW
  ltac:(unfold TW.A_OW_ndata; lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) VN) as H1.
apply (mrx_tw_end rdF rd0 _ _ H1). intros x Hx HP. mrx_unP HP. apply Hk; [exact Hx | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* The cuts of this file and the symbolic states                       *)
(* ------------------------------------------------------------------ *)

Definition OFF_D5 : Z := 0x22c.
Definition OFF_D6 : Z := 0x264.

(* The shadow base is s2. *)
Definition MRXD_Bx : sv := SOff 18 0.
Definition MRXD_SP : afact := mkAF (2 ^ 46) (2 ^ 47) 4.

(* D6: atom 32 = OW.ndata's 4 bytes as an unsigned int, atom 33 = f.body; a1 is pinned to 1. *)
Definition d6_nd : YP09.region := YP09.mkRegion (Some 12%nat) 220 224 220 224 [YP09.mkChunk 220 (CVal 4 (SOff 32 0))].
Definition d6_stk : YP09.region := YP09.mkRegion (Some 2%nat) 48 56 0 0 [YP09.mkChunk 48 (CVal 8 (SOff 33 0))].
Definition d6_dn (k : Z) : YP09.region :=
  YP09.mkRegion (Some 12%nat) (256 + 24 * k) (278 + 24 * k) (256 + 24 * k) (278 + 24 * k) [].
Definition d6_facts : facts :=
  mkFacts [(2%nat, MRXD_SP); (12%nat, mkAF TB_OW TB_OW 5); (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_d6 : sstate := mkSS (AF_m_rx + OFF_D6) sr_atoms [d6_nd; d6_stk] None d6_facts.
Definition SH6 : list shent := [mkSHE 12 0 304].

(* D5: atoms 32 = f.send, 33 = f.body, 34 = f.body_len, 35 = the frame byte fa + 30. M.desk_counter_valid and
   M.desk_counter are written. body_len = 1: the frame byte is a read-only region at atom 33, the shadow entry
   [fa + 30, fa + 31). *)
Definition d5_stk : YP09.region :=
  YP09.mkRegion (Some 2%nat) 32 64 0 0
    [YP09.mkChunk 32 (CVal 4 (SOff 32 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0)); YP09.mkChunk 56 (CVal 8 (SOff 34 0))].
Definition d5_dcv : YP09.region := YP09.mkRegion (Some 9%nat) 76 80 76 80 [].
Definition d5_dc : YP09.region := YP09.mkRegion (Some 9%nat) 80 84 80 84 [].
Definition d5_fb : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition d5n_facts : facts :=
  mkFacts [(2%nat, MRXD_SP); (9%nat, mkAF TB_M TB_M 5); (12%nat, mkAF TB_OW TB_OW 5);
           (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition d5o_facts : facts :=
  mkFacts [(2%nat, MRXD_SP); (9%nat, mkAF TB_M TB_M 5); (12%nat, mkAF TB_OW TB_OW 5);
           (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 30 (2 ^ 47 - 2) 0)] [] [].
Definition ss_d5n : sstate := mkSS (AF_m_rx + OFF_D5) sr_atoms [d5_stk; d5_dcv; d5_dc] None d5n_facts.
Definition ss_d5o : sstate := mkSS (AF_m_rx + OFF_D5) sr_atoms [d5_stk; d5_dcv; d5_dc; d5_fb] None d5o_facts.
Definition SH5 : list shent := [mkSHE 33 0 1].

(* DATA: atoms 32 = f.retry (2 bytes), 33 = f.send, and the 4 bytes as unsigned ints of 34 = M.desk_counter_valid,
   35 = M.desk_counter, 36 = OW.acks, 37 = g_cfg.backoff_ms. M.backoff_until's 8 bytes (mrxd_bk) join the state on
   the retry <> 0 side. *)
Definition mrxd_stk : YP09.region :=
  YP09.mkRegion (Some 2%nat) 30 36 0 0 [YP09.mkChunk 30 (CVal 2 (SOff 32 0)); YP09.mkChunk 32 (CVal 4 (SOff 33 0))].
Definition mrxd_dcvR : YP09.region := YP09.mkRegion (Some 9%nat) 76 80 0 0 [YP09.mkChunk 76 (CVal 4 (SOff 34 0))].
Definition mrxd_dcR : YP09.region := YP09.mkRegion (Some 9%nat) 80 84 0 0 [YP09.mkChunk 80 (CVal 4 (SOff 35 0))].
Definition mrxd_fail : YP09.region := YP09.mkRegion (Some 9%nat) 88 92 88 92 [].
Definition mrxd_acks : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 12)) 204 208 204 208 [YP09.mkChunk 204 (CVal 4 (SOff 36 0))].
Definition mrxd_bms : YP09.region := YP09.mkRegion (Some (A_OBJ 52)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 37 0))].
Definition mrxd_bk : YP09.region := YP09.mkRegion (Some 9%nat) 56 64 56 64 [].
Definition data_facts : facts :=
  mkFacts [(2%nat, MRXD_SP); (9%nat, mkAF TB_M TB_M 5); (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (A_OBJ 12, mkAF TB_OW TB_OW 5)] [] [].
Definition ss_data : sstate :=
  mkSS (AF_m_rx + OFF_DATA) sr_atoms [mrxd_stk; mrxd_dcvR; mrxd_dcR; mrxd_fail; mrxd_acks; mrxd_bms] None data_facts.

(* ------------------------------------------------------------------ *)
(* Ltac helpers                                                        *)
(* ------------------------------------------------------------------ *)

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

Ltac mrxd_awr U :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia | rewrite ?U in Ha; right; left; apply mrxd_inG; lia ] |]);
  apply awr_ok_x_nil.
Ltac mrxd_awr2 U1 U2 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia | rewrite ?U1, ?U2 in Ha; right; left; apply mrxd_inG; lia ] |]);
  apply awr_ok_x_nil.

(* The bytes of the chunk number c of region number idx of the state of HS, base rewritten by UB. *)
Ltac mrxd_chunk HS idx c UB v Hden V :=
  let RG := fresh "RG" in let HC := fresh "HC" in let HC1 := fresh "HCk" in
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict ?Hh ?m) =>
    pose proof (st_ok_pi_region_nth EF _ (restrict Hh m) idx _ HS eq_refl) as RG end;
  cbn [ms_mem restrict] in RG;
  destruct RG as (_ & _ & _ & HC);
  cbn [YP09.r_base YP09.r_chunks base_val] in HC;
  rewrite UB in HC;
  pose proof (AD.mrxd_Forall_nth _ _ c _ HC eq_refl) as HC1;
  pose proof (mrx_chunk_rd _ _ _ _ _ _ _ v HC1 Hden ltac:(cbn; lia)) as V;
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V;
  clear HC HC1.

(* After a run: the model term of the goal named md. *)
Ltac mrxd_md md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md := m) in *; clearbody md end.

(* The valuation of HS named En, with its agreement with E0 below the image atoms. *)
Ltac mrxd_env HS E0 En HE :=
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (En := EF) in * end;
  assert (HE : forall q, (q < 1024)%nat -> ew En q = ew E0 q)
    by (intros q Hq; unfold En; repeat rewrite ew_ewset_other by lia; reflexivity).

Section seg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis HMRX : trans_mrx_cells B.
Hypothesis HRO : trans_ro_rd_unowned B.
Hypothesis HNE : trans_rom_no_errno B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok tfibsegs B TG.G_HARNESS_B.
Hypothesis HGNE : gx_noerrno B TG.G_HARNESS_B.
Hypothesis HSRF : forall fx' : YK11.FPState, @transport_spec_read_frame_cg fx' rc B MT (transportb_sigma TB_spec_read_frame).
Hypothesis HBCMP : forall fx' : YK11.FPState, @abcmp_realizes fx' rc tfibsegs B (transportb_sigma TB___interceptor_trampoline_bcmp).
Hypothesis HMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc tfibsegs B OCpy (transportb_sigma TB___asan_memcpy).
Hypothesis HHOFF : forall fx' : YK11.FPState, @transport_host_offset_cg fx' rc B MT (transportb_sigma TB_host_offset).
Hypothesis HMSET : forall fx' : YK11.FPState, @transport_m_set_cg fx' rc B MT (transportb_sigma TB_m_set).
Hypothesis HDN : forall fx' : YK11.FPState, @transport_desk_named_cg fx' rc B MT (transportb_sigma TB_desk_named).
Hypothesis HMW : forall fx' : YK11.FPState, @transport_m_wake_cg fx' rc B MT (transportb_sigma TB_m_wake).
Hypothesis HMO : forall fx' : YK11.FPState, @transport_m_maybe_online_cg fx' rc B MT (transportb_sigma TB_m_maybe_online).
Hypothesis HMT : forall fx' : YK11.FPState, @transport_m_tick_cg fx' rc B MT (transportb_sigma TB_m_tick).
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
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* D5 (+0x22c, after the duplicate test): s1 = &M, a2 = &OW, a3 = retry, s2 = the shadow base; the frame and the
   struct at the current state; the model from UMR.mr_data3, then m_tick. *)
Definition R_D5 : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    mrx_cur B fr n sp1 ly2 S2 Wc mem2 /\
    YK11.getr regs2 9 = w64 TB_M /\ YK11.getr regs2 12 = w64 TB_OW /\
    YK11.getr regs2 13 = w64 (DSpec.sf_retry (mrx_f fr n)) /\ YK11.getr regs2 18 = w64 SHADOW_OFF /\
    exists B3, UMR.mr_data3 fr n Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* D6 (+0x264): a1 = 1, a2 = &OW, a3 = retry, a4 = send (sign-extended), a6 = body_len, s2 = the shadow base; the frame
   and the struct; the model from UMR.mr_dn, then m_tick. *)
Definition R_D6 : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    mrx_cur B fr n sp1 ly2 S2 Wc mem2 /\
    YK11.getr regs2 11 = w64 1 /\ YK11.getr regs2 12 = w64 TB_OW /\
    YK11.getr regs2 13 = w64 (DSpec.sf_retry (mrx_f fr n)) /\
    YK11.getr regs2 14 = w64 (bv_swrap 32 (DSpec.sf_send (mrx_f fr n))) /\
    YK11.getr regs2 16 = w64 (DSpec.sf_body_len (mrx_f fr n)) /\ YK11.getr regs2 18 = w64 SHADOW_OFF /\
    exists B3, UMR.mr_dn fr n Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

Lemma mrxd_vals : VAL (A_OBJ 12) = TB_OW /\ VAL (A_OBJ 52) = TB_g_cfg + 36.
Proof. vm_compute. split; reflexivity. Qed.

Lemma mrxd_ew : forall (regs : bvmap 5 word) extra k (q : bv 5) v, YK11.getr regs q = Z_to_bv 64 v ->
  Z.of_nat k = bv_unsigned q -> ew (Eimg (PI := PI_transportb) (Ereg regs extra)) k = Z_to_bv 64 v.
Proof. intros regs extra k q v Hq Hk. rewrite (ew_Eimg_Ereg_nat regs extra k q Hk). exact Hq. Qed.

Lemma mrxd_agree : forall (regs : bvmap 5 word) extra E',
  (forall q, (q < 1024)%nat -> ew E' q = ew (Eimg (PI := PI_transportb) (Ereg regs extra)) q) ->
  ed E' = ed (Ereg regs extra) -> env_agree 32 (Ereg regs extra) E'.
Proof.
intros regs extra E' H Hd. split; [|exact Hd].
intros k Hk. rewrite H by lia. apply Eimg_low. unfold A_TEXT. lia.
Qed.

Lemma mrxd_pcl : forall off k, AF_m_rx + off = k -> BASE + k = MRX_PC off.
Proof. intros off k <-. symmetry. apply mrx_pcv. Qed.

(* The callee-saved registers the runs keep (they write only a0 .. a7). *)
Ltac mrxd_hp HS regs ex HE HP :=
  lazymatch type of HS with st_ok_pi ?sg _ ?Ex _ (restrict ?Hh ?msx) =>
    assert (HP : aregs_preserved regs (ms_regs msx))
      by (apply (aregs_preserved_of_st_ok sg Hh Ex _ msx regs ex HS);
          [ apply mrxd_agree; [intros q Hq; rewrite HE by lia; reflexivity | reflexivity]
          | vm_compute; reflexivity ]) end.

(* OW.dn[i]'s 22 bytes, a writable region of G at any memory. *)
Lemma mrxd_dn_ok : forall E (m : word -> option byte) i, bv_unsigned (ew E 12) = TB_OW -> 0 <= i <= 1 ->
  region_ok segs E m (d6_dn i).
Proof.
intros E m i HU Hi. assert (EO : TB_OW = 6237408) by reflexivity.
unfold d6_dn, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HU. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_OW + o) G_HARNESS_B_rw). apply mrxd_inG. lia.
Qed.

(* OW's 304 bytes are addressable at every AR state (trans_mrx_cells: OW's 38 granules have shadow 0). *)
Lemma mrxd_ra_ow : forall ly S (Wx : world segs) mem md, @AR rc segs B ly S Wx mem md ->
  range_addressable (aview segs (w_H Wx) mem) SHADOW_OFF TB_OW 304.
Proof.
intros ly S Wx mem md HAR x Hx. destruct HMRX as (HZ & _).
assert (EO : TB_OW = 6237408) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold shadow_of_addr.
exists 0. split; [|left; reflexivity].
assert (Hz := decode_zshadow_rd B ly S Wx mem md TB_OW (TB_OW + TW.SZ_OW) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
replace (SHADOW_OFF + x / 8) with (BCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold BCells.shadow_addr, BCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Lemma mrxd_shok6 : forall ly S (Wx : world segs) mem md (E : env), @AR rc segs B ly S Wx mem md ->
  bv_unsigned (ew E 12) = TB_OW -> ew E 18 = Z_to_bv 64 SHADOW_OFF ->
  sh_ok segs MRXD_Bx SH6 E (mrestrict (w_H Wx) mem).
Proof.
intros ly S Wx mem md E HAR U12 E18.
assert (EO : TB_OW = 6237408) by reflexivity.
unfold sh_ok, SH6. constructor; [|constructor].
apply (shent_ok_of_range segs (w_H Wx) mem E MRXD_Bx 12 TB_OW 304 TB_OW 0 304 (mrxd_ra_ow ly S Wx mem md HAR)).
- unfold U, MRXD_Bx. cbn [sv_denot]. rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U12.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

Lemma mrxd_shok5 : forall (Wx : world segs) mem (E : env) q,
  range_addressable (aview segs (w_H Wx) mem) SHADOW_OFF q 1 -> amem_range q 1 ->
  bv_unsigned (ew E 33) = q -> ew E 18 = Z_to_bv 64 SHADOW_OFF ->
  sh_ok segs MRXD_Bx SH5 E (mrestrict (w_H Wx) mem).
Proof.
intros Wx mem E q Hra Ham U33 E18.
unfold sh_ok, SH5. constructor; [|constructor].
apply (shent_ok_of_range segs (w_H Wx) mem E MRXD_Bx 33 q 1 q 0 1 Hra).
- unfold U, MRXD_Bx. cbn [sv_denot]. rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U33.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
  unfold SHADOW_OFF. lia.
Qed.

(* The frame, the struct and the stack frame are kept by a run that writes only bytes of mrx_wr. *)
Lemma mrxd_kept : forall ly2 S2 (Wc : world segs) mem mem',
  mrx_cur B fr n sp1 ly2 S2 Wc mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mrx_wr a -> aview segs (w_H Wc) mem' a = aview segs (w_H Wc) mem a) ->
  mrx_cur B fr n sp1 ly2 S2 Wc mem' /\
  (forall a, sp1 - MRX_FRAME <= a < sp1 -> aview segs (w_H Wc) mem' a = aview segs (w_H Wc) mem a).
Proof.
intros ly2 S2 Wc mem mem' (Hok & Hfrs & Hsf) KA.
pose proof HST as (_ & _ & Hceil & Hlo & Hhi & _ & _ & _ & _ & _ & _ & Hfa0 & _ & Hfa64 & _ & _ & Hap & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (STK : MRX_STK = 8384) by (vm_compute; reflexivity). assert (FR : MRX_FRAME = 112) by reflexivity.
assert (KS : forall a, sp1 - MRX_FRAME <= a < sp1 -> aview segs (w_H Wc) mem' a = aview segs (w_H Wc) mem a).
{ intros a Ha. apply KA; [lia|]. intros Hw. pose proof (mrx_wr_hull a Hw) as Hh.
  unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. lia. }
split; [|exact KS].
split; [exact Hok|]. split.
- apply (mrx_frs_wr B fr ly2 S2 Wc mem mem' Hfrs Hap ltac:(lia) Hfa64). exact KA.
- apply (mrx_sf_kept Wc Wc mem mem' sp1 fr n Hsf). intros a Ha. apply KS. lia.
Qed.

(* The cut at a run's end: the continuation of the next cut applied to its mrx_at. *)
Lemma mrxd_exit : forall pc (R : mrx_R) (Wc : world segs) Bwc ly2 S2 regs2 mem2 regsF memF mdF,
  K pc R ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc memF mdF 0 ->
  frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> mo_le MT Sc S2 0 ->
  YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK11.getr regs2 3 = YK11.getr regs0 3 -> YK11.getr regs2 4 = YK11.getr regs0 4 ->
  mrx_hi regs0 regs2 -> aregs_preserved regs2 regsF ->
  @mrx_saved Wc mem2 sp1 regs0 ->
  (forall a, sp1 - MRX_FRAME <= a < sp1 -> aview segs (w_H Wc) memF a = aview segs (w_H Wc) mem2 a) ->
  tw_at TMAP_B (aview segs (w_H Wc) memF) Bwc ->
  R Wc Bwc ly2 S2 regsF memF ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 pc) memF (YK11.seg_rom segs)) mdF)
    (mrx_ipost B MT sp1 regs0 lyc Sc W memc mdc Bw' r).
Proof.
intros pc R Wc Bwc ly2 S2 regs2 mem2 regsF memF mdF HK HJ Hfr Hperm Hmo Hsp Hgp Htp Hhi HP Hsv Hkp Htw HR.
apply (HK Wc Bwc).
apply (mrx_at_intro B MT sp1 regs0 lyc Sc W memc mdc pc R Wc Bwc ly2 S2 regsF memF mdF HJ Hfr Hperm Hmo).
- rewrite <- Hsp. exact (HP 2 ltac:(unfold acallee_saved; lia)).
- rewrite <- Hgp. exact (HP 3 ltac:(unfold acallee_saved; lia)).
- rewrite <- Htp. exact (HP 4 ltac:(unfold acallee_saved; lia)).
- intros q Hq. rewrite <- (Hhi q Hq). exact (HP q ltac:(unfold acallee_saved; lia)).
- apply (mrx_saved_kept Wc Wc mem2 memF sp1 regs0 Hsv). intros a Ha. apply Hkp. unfold MRX_FRAME. lia.
- exact Htw.
- exact HR.
Qed.

(* The D6 cut at a run's end (from D5): the frame and the struct kept, the registers D6 reads. *)
Lemma mrxd_to_d6 : forall (Wc : world segs) Bwc ly2 S2 regs2 mem2 regsF memF mdF B3,
  K (MRX_PC OFF_D6) R_D6 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc memF mdF 0 ->
  frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> mo_le MT Sc S2 0 ->
  YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK11.getr regs2 3 = YK11.getr regs0 3 -> YK11.getr regs2 4 = YK11.getr regs0 4 ->
  mrx_hi regs0 regs2 -> aregs_preserved regs2 regsF ->
  @mrx_saved Wc mem2 sp1 regs0 -> mrx_cur B fr n sp1 ly2 S2 Wc mem2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mrx_wr a -> aview segs (w_H Wc) memF a = aview segs (w_H Wc) mem2 a) ->
  tw_at TMAP_B (aview segs (w_H Wc) memF) Bwc ->
  YK11.getr regs2 18 = w64 SHADOW_OFF ->
  YK11.getr regsF 11 = w64 1 -> YK11.getr regsF 12 = w64 TB_OW ->
  YK11.getr regsF 13 = w64 (DSpec.sf_retry (mrx_f fr n)) ->
  YK11.getr regsF 14 = w64 (bv_swrap 32 (DSpec.sf_send (mrx_f fr n))) ->
  YK11.getr regsF 16 = w64 (DSpec.sf_body_len (mrx_f fr n)) ->
  UMR.mr_dn fr n Bwc = Some (B3, tt) -> TC.m_tick_m B3 = Some (Bw', tt) -> r = 1 ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 (MRX_PC OFF_D6)) memF (YK11.seg_rom segs)) mdF)
    (mrx_ipost B MT sp1 regs0 lyc Sc W memc mdc Bw' r).
Proof.
intros Wc Bwc ly2 S2 regs2 mem2 regsF memF mdF B3 HK HJ Hfr Hperm Hmo Hsp Hgp Htp Hhi HP Hsv Hcur KW Htw R18
  Q11 Q12 Q13 Q14 Q16 Hm Htk Hr.
destruct (mrxd_kept ly2 S2 Wc mem2 memF Hcur KW) as (Hcur' & KS).
apply (mrxd_exit (MRX_PC OFF_D6) R_D6 Wc Bwc ly2 S2 regs2 mem2 regsF memF mdF HK HJ Hfr Hperm Hmo Hsp Hgp Htp Hhi HP
  Hsv KS Htw).
unfold R_D6. split; [exact Hcur'|]. split; [exact Q11|]. split; [exact Q12|]. split; [exact Q13|].
split; [exact Q14|]. split; [exact Q16|].
split; [rewrite <- R18; exact (HP 18 ltac:(unfold acallee_saved; lia))|].
exists B3. split; [exact Hm|]. split; [exact Htk | exact Hr].
Qed.

(* The D5 cut at a run's end (from DATA). *)
Lemma mrxd_to_d5 : forall (Wc : world segs) Bwc ly2 S2 regs2 mem2 regsF memF mdF B3,
  K (MRX_PC OFF_D5) R_D5 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc memF mdF 0 ->
  frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> mo_le MT Sc S2 0 ->
  YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK11.getr regs2 3 = YK11.getr regs0 3 -> YK11.getr regs2 4 = YK11.getr regs0 4 ->
  mrx_hi regs0 regs2 -> aregs_preserved regs2 regsF ->
  @mrx_saved Wc mem2 sp1 regs0 -> mrx_cur B fr n sp1 ly2 S2 Wc mem2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mrx_wr a -> aview segs (w_H Wc) memF a = aview segs (w_H Wc) mem2 a) ->
  tw_at TMAP_B (aview segs (w_H Wc) memF) Bwc ->
  YK11.getr regs2 9 = w64 TB_M -> YK11.getr regs2 18 = w64 SHADOW_OFF ->
  YK11.getr regsF 12 = w64 TB_OW -> YK11.getr regsF 13 = w64 (DSpec.sf_retry (mrx_f fr n)) ->
  UMR.mr_data3 fr n Bwc = Some (B3, tt) -> TC.m_tick_m B3 = Some (Bw', tt) -> r = 1 ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 (MRX_PC OFF_D5)) memF (YK11.seg_rom segs)) mdF)
    (mrx_ipost B MT sp1 regs0 lyc Sc W memc mdc Bw' r).
Proof.
intros Wc Bwc ly2 S2 regs2 mem2 regsF memF mdF B3 HK HJ Hfr Hperm Hmo Hsp Hgp Htp Hhi HP Hsv Hcur KW Htw R9 R18
  Q12 Q13 Hm Htk Hr.
destruct (mrxd_kept ly2 S2 Wc mem2 memF Hcur KW) as (Hcur' & KS).
apply (mrxd_exit (MRX_PC OFF_D5) R_D5 Wc Bwc ly2 S2 regs2 mem2 regsF memF mdF HK HJ Hfr Hperm Hmo Hsp Hgp Htp Hhi HP
  Hsv KS Htw).
unfold R_D5. split; [exact Hcur'|].
split; [rewrite <- R9; exact (HP 9 ltac:(unfold acallee_saved; lia))|]. split; [exact Q12|]. split; [exact Q13|].
split; [rewrite <- R18; exact (HP 18 ltac:(unfold acallee_saved; lia))|].
exists B3. split; [exact Hm|]. split; [exact Htk | exact Hr].
Qed.

Lemma mrxd_b30_nth : (30 < length (TI.tf_bytes fr))%nat ->
  nth (Z.to_nat 30) (map DSpec.bz (TI.tf_bytes fr)) 0 = mrxd_b30 fr.
Proof.
intros Hl. unfold mrxd_b30. change (Z.to_nat 30) with 30%nat. rewrite <- (map_nth DSpec.bz).
apply nth_indep. rewrite length_map. exact Hl.
Qed.

(* ------------------------------------------------------------------ *)
(* D6: OW.dn[OW.ndata], OW.ndata                                       *)
(* ------------------------------------------------------------------ *)

Lemma mrxd_seg_d6 : K (MRX_PC OFF_TICK) (R_TICK Bw' r) -> K (MRX_PC OFF_D6) R_D6.
Proof.
intros HKT. unfold mrx_K at 1. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hperm & Hmo & Hsp & Hgp & Htp & Hhi & Hsv & Htw & HR).
destruct HR as (Hcur & R11 & R12 & R13 & R14 & R16 & R18 & B3 & Hm & Htk & Hr).
pose proof Hcur as (Hok & Hfrs & Hsf).
pose proof HST as (Hsp1 & Hsp16 & Hceil & Hlo & Hhi47 & _ & _ & _ & _ & _ & _ & Hfa0 & Hfan & Hfa64 & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
pose proof (mrx_ok_fields fr n Hok) as (Fd & Fs & Fb & F30 & Fl0 & Fln & Fc & Fr & Fsn & Fa).
assert (Hnm : n <= mlen fr) by (destruct Hok as (Hn & _); lia).
assert (EO : TB_OW = 6237408) by reflexivity.
assert (FR : MRX_FRAME = 112) by reflexivity.
assert (STK : MRX_STK = 8384) by (vm_compute; reflexivity).
assert (M16 : (sp1 - MRX_FRAME) mod 16 = 0).
{ rewrite FR. replace (sp1 - 112) with (sp1 + (-7) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
pose proof (TWL.u_at_range Bwc TW.A_OW_ndata 4) as Rnd. change (8 * Z.of_nat 4) with 32 in Rnd.
pose proof (TWL.s32_range Bwc TW.A_OW_ndata) as Snd. change (TW.s32_at Bwc TW.A_OW_ndata) with (TW.OW_ndata Bwc) in Snd.
(* the valuation *)
set (E0 := Eimg (PI := PI_transportb) (Ereg regs2 [Z_to_bv 64 (TW.u_at Bwc TW.A_OW_ndata 4);
  Z_to_bv 64 (TI.tf_addr fr + DSpec.sf_body (mrx_f fr n))])).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (E32 : ew E0 32 = Z_to_bv 64 (TW.u_at Bwc TW.A_OW_ndata 4))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 (TI.tf_addr fr + DSpec.sf_body (mrx_f fr n)))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E12 : ew E0 12 = Z_to_bv 64 TB_OW) by exact (mrxd_ew regs2 _ 12 _ _ R12 eq_refl).
assert (Esp : ew E0 2 = Z_to_bv 64 (sp1 - MRX_FRAME)) by exact (mrxd_ew regs2 _ 2 _ _ Hsp eq_refl).
assert (E18 : ew E0 18 = Z_to_bv 64 SHADOW_OFF) by exact (mrxd_ew regs2 _ 18 _ _ R18 eq_refl).
assert (E13 : ew E0 13 = Z_to_bv 64 (DSpec.sf_retry (mrx_f fr n))) by exact (mrxd_ew regs2 _ 13 _ _ R13 eq_refl).
assert (E14 : ew E0 14 = Z_to_bv 64 (bv_swrap 32 (DSpec.sf_send (mrx_f fr n))))
  by exact (mrxd_ew regs2 _ 14 _ _ R14 eq_refl).
assert (E16 : ew E0 16 = Z_to_bv 64 (DSpec.sf_body_len (mrx_f fr n))) by exact (mrxd_ew regs2 _ 16 _ _ R16 eq_refl).
assert (U12 : bv_unsigned (ew E0 12) = TB_OW) by (rewrite E12; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E0 2) = sp1 - MRX_FRAME) by (rewrite Esp; apply unsigned_lit_small; lia).
(* the entry state *)
assert (HS0 : st_ok_pi segs VAL E0 ss_d6
  (restrict (w_H Wc) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + (AF_m_rx + OFF_D6))) mem2 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold ss_d6.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold d6_nd, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U12. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_OW + o) G_HARNESS_B_rw). apply mrxd_inG. lia.
      * constructor; [|constructor].
        apply (chunk_ok_val segs E0 _ TB_OW 220 4 (SOff 32 0) (TW.u_at Bwc TW.A_OW_ndata 4));
          [exact (AD.mrxd_den_atom E0 32 _ E32) | cbn; lia | lia |].
        exact (tw_read_val segs _ TMAP_B Bwc TW.OFF_OW TB_OW TW.SZ_OW 220 4 TMAP_B_ok Htw TMAP_B_OW
          ltac:(lia) ltac:(unfold TW.SZ_OW; lia)).
    + unfold d6_stk, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E0 _ (sp1 - MRX_FRAME) 48 8 (SOff 33 0) (TI.tf_addr fr + DSpec.sf_body (mrx_f fr n)));
        [exact (AD.mrxd_den_atom E0 33 _ E33) | change (8 * Z.of_N 8) with 64; lia | lia |].
      pose proof (mrx_sf_body _ _ _ _ Hsf) as V. rewrite (mrx_sf_ptr fr n _ Hok) in V. exact V.
  - apply pairwise_disjoint_of_extents. unfold d6_nd, d6_stk, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U12, Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; first [exact I | lia].
  - unfold d6_facts, MRXD_SP, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp, U12, E18, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | exact M16 | reflexivity]. }
pose proof (st_ok_pi_pin_reg' E0 ss_d6 _ (11%bv : bv 5) 1 HS0 R11 eq_refl) as HS.
clear HS0.
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
  let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.
assert (SHOK : sh_ok segs MRXD_Bx SH6 E0 (mrestrict (w_H Wc) mem2))
  by exact (mrxd_shok6 _ _ _ _ _ E0 HAR U12 E18).
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (PI := PI_transportb)) as BR.
rewrite (mrx_pcv OFF_D6).
(* run 1, +0x264 .. +0x268: k = OW.ndata; it stops at `blt a1, a5`. *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
{ mrxd_awr U12. }
mrxd_md mdA.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_OW + 220 <= a < TB_OW + 224) ->
  aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
{ intros a Ha H1. apply (kept_of_frame _ _ _ _ _ (fun x => TB_OW + 220 <= x < TB_OW + 224) HFr); [|exact Ha|exact H1].
  intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?U12, ?Usp in Hx; lia). }
clear HF HFr HG.
rename ms into ms1.
assert (DK : sv_denot E0 (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.OW_ndata Bwc))
  by exact (AD.mrxd_den_sext32 E0 32 _ E32 Rnd).
psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
- (* 1 < k: no OW.dn store; k + 1 (its overflow test refuted by the model) *)
  rewrite DK in Hc. cbn [branch_taken sv_denot] in Hc. rewrite EPI.mrxk_lts in Hc by lia. apply Z.ltb_lt in Hc.
  destruct (mrxd_dn_hi fr n Bwc B3 ltac:(lia) Hm) as (HnM & ->).
  (* run 2, +0x300 .. +0x304: k + 1; it stops at the overflow test `blt a0, a5`. *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
  { mrxd_awr U12. }
  mrxd_md mdB.
  assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_OW + 220 <= a < TB_OW + 224) ->
    aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
  { intros a Ha H1. rewrite <- (KA1 a Ha H1).
    apply (kept_of_frame _ _ _ _ _ (fun x => TB_OW + 220 <= x < TB_OW + 224) HFr); [|exact Ha|exact H1].
    intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?U12, ?Usp in Hx; lia). }
  clear HF HFr HG KA1. rename ms into ms2.
  assert (DA : sv_denot E0 (SAluw ALU_ADD (SExt true 32 (SOff 32 0)) (SLit 1)) =
    Z_to_bv 64 (bv_swrap 32 (TW.OW_ndata Bwc + 1))) by exact (mrxd_den_addw E0 _ _ 1 DK).
  pose proof (UMR.mr_swrap32_range (TW.OW_ndata Bwc + 1)) as RW.
  clear Hc.
  psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
  + (* the trap word: k = INT_MAX, where the model is None *)
    exfalso. rewrite DA, DK in Hc. cbn [branch_taken] in Hc. rewrite EPI.mrxk_lts in Hc by lia.
    rewrite UMR.mr_inc_trap in Hc by lia. apply Z.eqb_eq in Hc. exact (HnM Hc).
  + (* run 3, +0x308 .. +0x30c: k + 1 at OW + 220; to TICK. *)
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
    { mrxd_awr U12. }
    mrxd_md mdC.
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_OW + 220 <= a < TB_OW + 224) ->
      aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
    { intros a Ha H1. rewrite <- (KA2 a Ha H1).
      apply (kept_of_frame _ _ _ _ _ (fun x => TB_OW + 220 <= x < TB_OW + 224) HFr); [|exact Ha|exact H1].
      intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?U12, ?Usp in Hx; lia). }
    clear HF HFr HG.
    mrxd_env HS E0 E3 HE3.
    assert (U12' : bv_unsigned (ew E3 12) = TB_OW) by (rewrite HE3 by lia; exact U12).
    assert (DA' : sv_denot E3 (SAluw ALU_ADD (SExt true 32 (SOff 32 0)) (SLit 1)) =
      Z_to_bv 64 (bv_swrap 32 (TW.OW_ndata Bwc + 1)))
      by (apply mrxd_den_addw; apply (AD.mrxd_den_sext32 E3 32 _ ltac:(rewrite HE3 by lia; exact E32) Rnd)).
    mrxd_chunk HS 0%nat 0%nat U12' (bv_swrap 32 (TW.OW_ndata Bwc + 1)) DA' VN.
    assert (HTW : tw_at TMAP_B (aview segs (w_H Wc) (ms_mem ms)) (TW.set_OW_ndata Bwc (TW.OW_ndata Bwc + 1))).
    { apply (mrxd_world_nd Bwc _ _ _ Htw).
      - intros j Hj. rewrite <- (AD.mrxd_le_sw32 (TW.OW_ndata Bwc + 1) j). exact (VN j Hj).
      - intros x Hx N1. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
        apply KA; lia. }
    mrxd_hp HS regs2 [Z_to_bv 64 (TW.u_at Bwc TW.A_OW_ndata 4); Z_to_bv 64 (TI.tf_addr fr + DSpec.sf_body (mrx_f fr n))]
      HE3 HP.
    pmkst HS. rewrite (mrxd_pcl OFF_TICK 15648 eq_refl).
    apply (mrxd_exit (MRX_PC OFF_TICK) (R_TICK Bw' r) Wc _ ly2 S2 regs2 mem2 (ms_regs ms) (ms_mem ms) mdC HKT HJ
      Hfr Hperm Hmo Hsp Hgp Htp Hhi HP Hsv ltac:(intros a Ha; apply KA; lia) HTW).
    unfold R_TICK. split; [exact Htk | exact Hr].
- (* k <= 1: 0 <= k by the model; OW.dn[k] *)
  rewrite DK in Hc. cbn [branch_taken sv_denot] in Hc. rewrite EPI.mrxk_lts in Hc by lia. apply Z.ltb_ge in Hc.
  destruct (mrxd_dn_lo fr n Bwc B3 ltac:(lia) Hm) as (Hk0 & ->).
  assert (Hcase : TW.OW_ndata Bwc = 0 \/ TW.OW_ndata Bwc = 1) by lia.
  clear Hc.
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
          rewrite ?U12, ?Usp; repeat split; lia)) as HS end end.
  all: clear HSp.
  all: lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
    let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.
  (* run 2, +0x268 .. +0x30c: x = OW + 256 + 24 k, its null and overflow tests, the four checked stores (decided
     by SH6), k + 1 at OW + 220; to TICK *)
  all: paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK); [mrxd_awr U12 |].
  all: mrxd_md mdB.
  all: lazymatch goal with Hi : TW.OW_ndata _ = ?i |- _ =>
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_OW + 220 <= a < TB_OW + 224) ->
      ~ (TB_OW + 256 + 24 * i <= a < TB_OW + 278 + 24 * i) ->
      aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a)
    by (intros a Ha H1 H2; rewrite <- (KA1 a Ha H1);
        apply (kept_of_frame _ _ _ _ _
          (fun x => (TB_OW + 220 <= x < TB_OW + 224) \/ (TB_OW + 256 + 24 * i <= x < TB_OW + 278 + 24 * i)) HFr);
        [ intros b wlo whi x Hin Hx; cbv beta; mrxd_win Hin Hx ltac:(rewrite ?U12, ?Usp in Hx; lia)
        | exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)] ]) end.
  all: clear HF HFr HG.
  all: mrxd_env HS E0 E2 HE2.
  all: assert (U12' : bv_unsigned (ew E2 12) = TB_OW) by (rewrite HE2 by lia; exact U12).
  all: assert (D13 : sv_denot E2 (SOff 13 0) = Z_to_bv 64 (DSpec.sf_retry (mrx_f fr n)))
    by (apply AD.mrxd_den_atom; rewrite HE2 by lia; exact E13).
  all: assert (D14 : sv_denot E2 (SOff 14 0) = Z_to_bv 64 (bv_swrap 32 (DSpec.sf_send (mrx_f fr n))))
    by (apply AD.mrxd_den_atom; rewrite HE2 by lia; exact E14).
  all: assert (D16 : sv_denot E2 (SOff 16 0) = Z_to_bv 64 (DSpec.sf_body_len (mrx_f fr n)))
    by (apply AD.mrxd_den_atom; rewrite HE2 by lia; exact E16).
  all: assert (D33 : sv_denot E2 (SOff 33 0) = Z_to_bv 64 (TI.tf_addr fr + DSpec.sf_body (mrx_f fr n)))
    by (apply AD.mrxd_den_atom; rewrite HE2 by lia; exact E33).
  all: lazymatch goal with Hi : TW.OW_ndata _ = ?i |- _ =>
    assert (DNi : sv_denot E2 (SLit (i + 1)) = Z_to_bv 64 (i + 1)) by reflexivity end.
  all: mrxd_chunk HS 0%nat 0%nat U12' (DSpec.sf_retry (mrx_f fr n)) D13 VRT.
  all: mrxd_chunk HS 0%nat 1%nat U12' (bv_swrap 32 (DSpec.sf_send (mrx_f fr n))) D14 VSN.
  all: mrxd_chunk HS 0%nat 2%nat U12' (DSpec.sf_body_len (mrx_f fr n)) D16 VLN.
  all: mrxd_chunk HS 0%nat 3%nat U12' (TI.tf_addr fr + DSpec.sf_body (mrx_f fr n)) D33 VBD.
  all: lazymatch goal with Hi : TW.OW_ndata _ = ?i |- _ => mrxd_chunk HS 1%nat 0%nat U12' (i + 1) DNi VND end.
  all: lazymatch goal with Hi : TW.OW_ndata _ = ?i |- _ =>
    assert (HTW : tw_at TMAP_B (aview segs (w_H Wc) (ms_mem ms)) (TW.set_OW_ndata (mrxd_B6 fr n Bwc i) (i + 1)))
    by (unfold mrxd_B6; apply (mrxd_world6 Bwc _ _ i _ _ _ _ _ Htw ltac:(lia));
        [ intros j Hj; exact (VBD j Hj)
        | intros j Hj; exact (VLN j Hj)
        | intros j Hj; rewrite <- (AD.mrxd_le_sw32 (DSpec.sf_send (mrx_f fr n)) j); exact (VSN j Hj)
        | intros j Hj; exact (VRT j Hj)
        | intros j Hj; exact (VND j Hj)
        | intros x Hx N1 N2; pose proof (TMAP_B_hull x Hx) as Hh;
          unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh; apply KA; lia ]) end.
  all: rewrite Hi in Htk.
  all: mrxd_hp HS regs2 [Z_to_bv 64 (TW.u_at Bwc TW.A_OW_ndata 4); Z_to_bv 64 (TI.tf_addr fr + DSpec.sf_body (mrx_f fr n))]
    HE2 HP.
  all: pmkst HS.
  all: rewrite (mrxd_pcl OFF_TICK 15648 eq_refl).
  all: apply (mrxd_exit (MRX_PC OFF_TICK) (R_TICK Bw' r) Wc _ ly2 S2 regs2 mem2 (ms_regs ms) (ms_mem ms) mdB HKT HJ
    Hfr Hperm Hmo Hsp Hgp Htp Hhi HP Hsv ltac:(intros a Ha; apply KA; lia) HTW).
  all: unfold R_TICK; split; [exact Htk | exact Hr].
Qed.

(* ------------------------------------------------------------------ *)
(* D5: the desk counter, the keepalive test                            *)
(* ------------------------------------------------------------------ *)

Lemma mrxd_seg_d5 : K (MRX_PC OFF_TICK) (R_TICK Bw' r) -> K (MRX_PC OFF_D6) R_D6 -> K (MRX_PC OFF_D5) R_D5.
Proof.
intros HKT HK6. unfold mrx_K at 1. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hperm & Hmo & Hsp & Hgp & Htp & Hhi & Hsv & Htw & HR).
destruct HR as (Hcur & R9 & R12 & R13 & R18 & B3 & Hm & Htk & Hr).
pose proof Hcur as (Hok & Hfrs & Hsf).
pose proof Hfrs as (Hg & Hsrc & _).
pose proof HST as (Hsp1 & Hsp16 & Hceil & Hlo & Hhi47 & _ & _ & _ & _ & _ & _ & Hfa0 & Hfan & Hfa64 & _ & Hpl & Hap & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
pose proof (mrx_ok_fields fr n Hok) as (Fd & Fs & Fb & F30 & Fl0 & Fln & Fc & Fr & Fsn & Fa).
assert (Hnm : n <= mlen fr) by (destruct Hok as (Hn & _); lia).
assert (EM : TB_M = 6155744) by reflexivity. assert (EO : TB_OW = 6237408) by reflexivity.
assert (FR : MRX_FRAME = 112) by reflexivity.
assert (STK : MRX_STK = 8384) by (vm_compute; reflexivity).
assert (M16 : (sp1 - MRX_FRAME) mod 16 = 0).
{ rewrite FR. replace (sp1 - 112) with (sp1 + (-7) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
pose proof (trans_src_ok_rd B LAWS ly2 S2 Wc mem2 md2 (TI.tf_addr fr) (mlen fr) HAR Hsrc ltac:(lia)) as Hrd.
pose proof Hrd as (_ & _ & _ & Ham & _ & H63).
assert (Ham' : TI.tf_addr fr + mlen fr <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
(* the valuation: 32 = f.send, 33 = f.body, 34 = f.body_len, 35 = the frame byte fa + 30 *)
set (E0 := Eimg (PI := PI_transportb) (Ereg regs2 [Z_to_bv 64 (DSpec.sf_send (mrx_f fr n));
  Z_to_bv 64 (TI.tf_addr fr + DSpec.sf_body (mrx_f fr n)); Z_to_bv 64 (DSpec.sf_body_len (mrx_f fr n));
  Z_to_bv 64 (mrxd_b30 fr)])).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (E32 : ew E0 32 = Z_to_bv 64 (DSpec.sf_send (mrx_f fr n)))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 (TI.tf_addr fr + DSpec.sf_body (mrx_f fr n)))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 (DSpec.sf_body_len (mrx_f fr n)))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E0 35 = Z_to_bv 64 (mrxd_b30 fr))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E9 : ew E0 9 = Z_to_bv 64 TB_M) by exact (mrxd_ew regs2 _ 9 _ _ R9 eq_refl).
assert (E12 : ew E0 12 = Z_to_bv 64 TB_OW) by exact (mrxd_ew regs2 _ 12 _ _ R12 eq_refl).
assert (Esp : ew E0 2 = Z_to_bv 64 (sp1 - MRX_FRAME)) by exact (mrxd_ew regs2 _ 2 _ _ Hsp eq_refl).
assert (E18 : ew E0 18 = Z_to_bv 64 SHADOW_OFF) by exact (mrxd_ew regs2 _ 18 _ _ R18 eq_refl).
assert (E13 : ew E0 13 = Z_to_bv 64 (DSpec.sf_retry (mrx_f fr n))) by exact (mrxd_ew regs2 _ 13 _ _ R13 eq_refl).
assert (U9 : bv_unsigned (ew E0 9) = TB_M) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E0 12) = TB_OW) by (rewrite E12; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E0 2) = sp1 - MRX_FRAME) by (rewrite Esp; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E0 33) = TI.tf_addr fr + 30) by (rewrite E33, Fb; apply unsigned_lit_small; lia).
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (PI := PI_transportb)) as BR.
rewrite (mrx_pcv OFF_D5).
destruct (Z.eq_dec (DSpec.sf_body_len (mrx_f fr n)) 1) as [BL1|BLn].
2: {
(* body_len <> 1: the two stores, then D6 *)
assert (HS : st_ok_pi segs VAL E0 ss_d5n
  (restrict (w_H Wc) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + (AF_m_rx + OFF_D5))) mem2 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold ss_d5n.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold d5_stk, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val segs E0 _ (sp1 - MRX_FRAME) 32 4 (SOff 32 0) (DSpec.sf_send (mrx_f fr n)));
          [exact (AD.mrxd_den_atom E0 32 _ E32) | change (8 * Z.of_N 4) with 32; lia | lia |].
        exact (mrx_sf_send _ _ _ _ Hsf).
      * apply (chunk_ok_val segs E0 _ (sp1 - MRX_FRAME) 48 8 (SOff 33 0)
          (TI.tf_addr fr + DSpec.sf_body (mrx_f fr n)));
          [exact (AD.mrxd_den_atom E0 33 _ E33) | change (8 * Z.of_N 8) with 64; lia | lia |].
        pose proof (mrx_sf_body _ _ _ _ Hsf) as V. rewrite (mrx_sf_ptr fr n _ Hok) in V. exact V.
      * apply (chunk_ok_val segs E0 _ (sp1 - MRX_FRAME) 56 8 (SOff 34 0) (DSpec.sf_body_len (mrx_f fr n)));
          [exact (AD.mrxd_den_atom E0 34 _ E34) | change (8 * Z.of_N 8) with 64; lia | lia |].
        exact (mrx_sf_blen _ _ _ _ Hsf).
    + unfold d5_dcv, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw). apply mrxd_inG. lia.
    + unfold d5_dc, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw). apply mrxd_inG. lia.
  - apply pairwise_disjoint_of_extents. unfold d5_stk, d5_dcv, d5_dc, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; first [exact I | lia].
  - unfold d5n_facts, MRXD_SP, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U9, U12, E18, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | exact M16 | reflexivity]. }
assert (SHOK : sh_ok segs MRXD_Bx [] E0 (mrestrict (w_H Wc) mem2)) by (unfold sh_ok; apply Forall_nil).
(* run 1, +0x22c .. +0x240: f.send, f.body_len, the two stores; it stops at `bne a6, a1`. *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D6).
{ mrxd_awr U9. }
mrxd_md mdA.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 76 <= a < TB_M + 84) ->
  aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
{ intros a Ha H1. apply (kept_of_frame _ _ _ _ _ (fun x => TB_M + 76 <= x < TB_M + 84) HFr); [|exact Ha|exact H1].
  intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?U9, ?Usp in Hx; lia). }
clear HF HFr HG. rename ms into ms1.
psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
2: { rewrite (AD.mrxd_den_atom E0 34 _ E34) in Hc. cbn [branch_taken sv_denot] in Hc.
     rewrite EPI.mrxk_eqb in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc. exfalso. exact (BLn Hc). }
clear Hc.
(* run 2: to D6 *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D6).
{ mrxd_awr U9. }
mrxd_md mdB.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 76 <= a < TB_M + 84) ->
  aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
{ intros a Ha H1. rewrite <- (KA1 a Ha H1).
  apply (kept_of_frame _ _ _ _ _ (fun x => TB_M + 76 <= x < TB_M + 84) HFr); [|exact Ha|exact H1].
  intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?U9, ?Usp in Hx; lia). }
clear HF HFr HG.
mrxd_env HS E0 E1 HE1.
assert (U9' : bv_unsigned (ew E1 9) = TB_M) by (rewrite HE1 by lia; exact U9).
assert (D32 : sv_denot E1 (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (bv_swrap 32 (DSpec.sf_send (mrx_f fr n))))
  by (apply AD.mrxd_den_sext32; [rewrite HE1 by lia; exact E32 | exact Fsn]).
mrxd_chunk HS 1%nat 0%nat U9' 1 (@eq_refl _ (Z_to_bv 64 1)) V76.
mrxd_chunk HS 2%nat 0%nat U9' (bv_swrap 32 (DSpec.sf_send (mrx_f fr n))) D32 V80.
assert (HTW : tw_at TMAP_B (aview segs (w_H Wc) (ms_mem ms)) (mrxd_B5 fr n Bwc)).
{ unfold mrxd_B5. apply (mrxd_world5 Bwc _ _ _ Htw).
  - intros j Hj. rewrite <- (AD.mrxd_le_sw32 (DSpec.sf_send (mrx_f fr n)) j). exact (V80 j Hj).
  - exact V76.
  - intros x Hx N1. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KA; lia. }
assert (HM6 : UMR.mr_dn fr n (mrxd_B5 fr n Bwc) = Some (B3, tt)).
{ apply (mrxd_data3_dn fr n Bwc B3 Fb); [|exact Hm]. rewrite (proj2 (Z.eqb_neq _ _) BLn). reflexivity. }
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ mrx_wr a -> aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a)
  by (intros a Ha Hn; apply KA; [exact Ha | intros Hx; apply Hn; apply mrxd_wr; right; left; exact Hx]).
mrxd_hp HS regs2 [Z_to_bv 64 (DSpec.sf_send (mrx_f fr n)); Z_to_bv 64 (TI.tf_addr fr + DSpec.sf_body (mrx_f fr n));
  Z_to_bv 64 (DSpec.sf_body_len (mrx_f fr n)); Z_to_bv 64 (mrxd_b30 fr)] HE1 HP.
mrxd_reg HS (11%bv : bv 5) (w64 1) Q11 ltac:(reflexivity).
mrxd_reg HS (12%bv : bv 5) (w64 TB_OW) Q12 ltac:(apply AD.mrxd_den_atom; rewrite HE1 by lia; exact E12).
mrxd_reg HS (13%bv : bv 5) (w64 (DSpec.sf_retry (mrx_f fr n))) Q13
  ltac:(apply AD.mrxd_den_atom; rewrite HE1 by lia; exact E13).
mrxd_reg HS (14%bv : bv 5) (w64 (bv_swrap 32 (DSpec.sf_send (mrx_f fr n)))) Q14 ltac:(exact D32).
mrxd_reg HS (16%bv : bv 5) (w64 (DSpec.sf_body_len (mrx_f fr n))) Q16
  ltac:(apply AD.mrxd_den_atom; rewrite HE1 by lia; exact E34).
pmkst HS. rewrite (mrxd_pcl OFF_D6 15328 eq_refl).
exact (mrxd_to_d6 Wc _ ly2 S2 regs2 mem2 (ms_regs ms) (ms_mem ms) mdB B3 HK6 HJ Hfr Hperm Hmo Hsp Hgp Htp Hhi HP Hsv
  Hcur KW HTW R18 Q11 Q12 Q13 Q14 Q16 HM6 Htk Hr).
}
(* body_len = 1: the stores, the checked load of fa + 30, then TICK (0) or D6 *)
assert (Hl31 : 31 <= n) by lia.
assert (Hlen30 : (30 < length (TI.tf_bytes fr))%nat) by (unfold AK.mlen in Hnm; lia).
destruct (garr8_nthZ segs _ _ _ 30 Hg ltac:(lia)
  ltac:(rewrite length_map; change (Z.to_nat 30) with 30%nat; exact Hlen30)) as [Hv30 Hr30].
rewrite (mrxd_b30_nth Hlen30) in Hv30, Hr30.
pose proof (trans_rd_ok_sub Wc mem2 _ _ (TI.tf_addr fr + 30) 1 Hrd ltac:(lia) ltac:(unfold AK.mlen in *; lia)
  ltac:(lia)) as (_ & Hra30 & _ & Ham30 & _).
assert (HfaM : ~ (TB_M + 76 <= TI.tf_addr fr + 30 < TB_M + 84)).
{ intros Hx. apply (Hap (TI.tf_addr fr + 30)); [apply mrxd_wr; right; left; exact Hx | unfold AK.mlen in Hnm; lia]. }
assert (HS : st_ok_pi segs VAL E0 ss_d5o
  (restrict (w_H Wc) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + (AF_m_rx + OFF_D5))) mem2 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold ss_d5o.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + unfold d5_stk, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val segs E0 _ (sp1 - MRX_FRAME) 32 4 (SOff 32 0) (DSpec.sf_send (mrx_f fr n)));
          [exact (AD.mrxd_den_atom E0 32 _ E32) | change (8 * Z.of_N 4) with 32; lia | lia |].
        exact (mrx_sf_send _ _ _ _ Hsf).
      * apply (chunk_ok_val segs E0 _ (sp1 - MRX_FRAME) 48 8 (SOff 33 0)
          (TI.tf_addr fr + DSpec.sf_body (mrx_f fr n)));
          [exact (AD.mrxd_den_atom E0 33 _ E33) | change (8 * Z.of_N 8) with 64; lia | lia |].
        pose proof (mrx_sf_body _ _ _ _ Hsf) as V. rewrite (mrx_sf_ptr fr n _ Hok) in V. exact V.
      * apply (chunk_ok_val segs E0 _ (sp1 - MRX_FRAME) 56 8 (SOff 34 0) (DSpec.sf_body_len (mrx_f fr n)));
          [exact (AD.mrxd_den_atom E0 34 _ E34) | change (8 * Z.of_N 8) with 64; lia | lia |].
        exact (mrx_sf_blen _ _ _ _ Hsf).
    + unfold d5_dcv, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw). apply mrxd_inG. lia.
    + unfold d5_dc, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw). apply mrxd_inG. lia.
    + unfold d5_fb, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E0 _ (TI.tf_addr fr + 30) 0 1 (SOff 35 0) (mrxd_b30 fr));
        [exact (AD.mrxd_den_atom E0 35 _ E35) | change (8 * Z.of_N 1) with 8; lia | lia |].
      rewrite Z.add_0_r. exact Hv30.
  - apply pairwise_disjoint_of_extents. unfold d5_stk, d5_dcv, d5_dc, d5_fb, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U9, U33.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; first [exact I | lia].
  - unfold d5o_facts, MRXD_SP, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U9, U12, U33, E18, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | exact M16 | reflexivity]. }
pose proof (mrxd_shok5 Wc mem2 E0 (TI.tf_addr fr + 30) Hra30 Ham30 U33 E18) as SHOK.
(* run 1, +0x22c .. +0x240: the two stores; it stops at `bne a6, a1`. *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D6).
{ mrxd_awr U9. }
mrxd_md mdA.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 76 <= a < TB_M + 84) ->
  aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
{ intros a Ha H1. apply (kept_of_frame _ _ _ _ _ (fun x => TB_M + 76 <= x < TB_M + 84) HFr); [|exact Ha|exact H1].
  intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?U9, ?Usp, ?U33 in Hx; lia). }
clear HF HFr HG. rename ms into ms1.
psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
{ rewrite (AD.mrxd_den_atom E0 34 _ E34) in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite EPI.mrxk_eqb in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc. exfalso. exact (Hc BL1). }
clear Hc.
(* run 2, +0x244 .. +0x260: f.body, its null test (decided by its fact), the check of fa + 30 (decided by SH5), the
   load; it stops at `beqz a0`. *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D6).
{ mrxd_awr U9. }
mrxd_md mdB.
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 76 <= a < TB_M + 84) ->
  aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
{ intros a Ha H1. rewrite <- (KA1 a Ha H1).
  apply (kept_of_frame _ _ _ _ _ (fun x => TB_M + 76 <= x < TB_M + 84) HFr); [|exact Ha|exact H1].
  intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?U9, ?Usp, ?U33 in Hx; lia). }
clear HF HFr HG KA1. rename ms into ms2.
mrxd_env HS E0 E1 HE1.
assert (U9' : bv_unsigned (ew E1 9) = TB_M) by (rewrite HE1 by lia; exact U9).
assert (DB : sv_denot E1 (SExt false 8 (SOff 35 0)) = Z_to_bv 64 (mrxd_b30 fr))
  by (apply AD.mrxd_den_zext; [rewrite HE1 by lia; exact E35 | change (2 ^ Z.of_N 8) with 256; lia | lia]).
psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
all: rewrite DB in Hc; cbn [branch_taken sv_denot] in Hc; rewrite EPI.mrxk_eqb in Hc by lia.
- (* fa[30] = 0: the keepalive, to TICK *)
  apply Z.eqb_eq in Hc.
  assert (EB3 : B3 = mrxd_B5 fr n Bwc) by exact (mrxd_data3_tick fr n Bwc B3 Fb BL1 Hc Hm).
  subst B3.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
  { mrxd_awr U9'. }
  mrxd_md mdC.
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 76 <= a < TB_M + 84) ->
    aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
  { intros a Ha H1. rewrite <- (KA2 a Ha H1).
    apply (kept_of_frame _ _ _ _ _ (fun x => TB_M + 76 <= x < TB_M + 84) HFr); [|exact Ha|exact H1].
    intros b wlo whi x Hin Hx. cbv beta.
    mrxd_win Hin Hx ltac:(rewrite ?HE1 in Hx by lia; rewrite ?U9, ?Usp, ?U33 in Hx; lia). }
  clear HF HFr HG.
  mrxd_env HS E1 E2 HE21.
  assert (HE2 : forall q, (q < 1024)%nat -> ew E2 q = ew E0 q) by (intros q Hq; rewrite (HE21 q Hq); exact (HE1 q Hq)).
  assert (U9'' : bv_unsigned (ew E2 9) = TB_M) by (rewrite HE2 by lia; exact U9).
  assert (D32 : sv_denot E2 (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (bv_swrap 32 (DSpec.sf_send (mrx_f fr n))))
    by (apply AD.mrxd_den_sext32; [rewrite HE2 by lia; exact E32 | exact Fsn]).
  mrxd_chunk HS 1%nat 0%nat U9'' 1 (@eq_refl _ (Z_to_bv 64 1)) V76.
  mrxd_chunk HS 2%nat 0%nat U9'' (bv_swrap 32 (DSpec.sf_send (mrx_f fr n))) D32 V80.
  assert (HTW : tw_at TMAP_B (aview segs (w_H Wc) (ms_mem ms)) (mrxd_B5 fr n Bwc)).
  { unfold mrxd_B5. apply (mrxd_world5 Bwc _ _ _ Htw).
    - intros j Hj. rewrite <- (AD.mrxd_le_sw32 (DSpec.sf_send (mrx_f fr n)) j). exact (V80 j Hj).
    - exact V76.
    - intros x Hx N1. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      apply KA; lia. }
  mrxd_hp HS regs2 [Z_to_bv 64 (DSpec.sf_send (mrx_f fr n)); Z_to_bv 64 (TI.tf_addr fr + DSpec.sf_body (mrx_f fr n));
    Z_to_bv 64 (DSpec.sf_body_len (mrx_f fr n)); Z_to_bv 64 (mrxd_b30 fr)] HE2 HP.
  pmkst HS. rewrite (mrxd_pcl OFF_TICK 15648 eq_refl).
  apply (mrxd_exit (MRX_PC OFF_TICK) (R_TICK Bw' r) Wc _ ly2 S2 regs2 mem2 (ms_regs ms) (ms_mem ms) mdC HKT HJ
    Hfr Hperm Hmo Hsp Hgp Htp Hhi HP Hsv ltac:(intros a Ha; apply KA; lia) HTW).
  unfold R_TICK. split; [exact Htk | exact Hr].
- (* fa[30] <> 0: to D6 *)
  apply Z.eqb_neq in Hc.
  assert (HM6 : UMR.mr_dn fr n (mrxd_B5 fr n Bwc) = Some (B3, tt)).
  { apply (mrxd_data3_dn fr n Bwc B3 Fb); [|exact Hm].
    rewrite BL1, (proj2 (Z.eqb_neq _ _) Hc). reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D6).
  { mrxd_awr U9'. }
  mrxd_md mdC.
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 76 <= a < TB_M + 84) ->
    aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
  { intros a Ha H1. rewrite <- (KA2 a Ha H1).
    apply (kept_of_frame _ _ _ _ _ (fun x => TB_M + 76 <= x < TB_M + 84) HFr); [|exact Ha|exact H1].
    intros b wlo whi x Hin Hx. cbv beta.
    mrxd_win Hin Hx ltac:(rewrite ?HE1 in Hx by lia; rewrite ?U9, ?Usp, ?U33 in Hx; lia). }
  clear HF HFr HG.
  mrxd_env HS E1 E2 HE21.
  assert (HE2 : forall q, (q < 1024)%nat -> ew E2 q = ew E0 q) by (intros q Hq; rewrite (HE21 q Hq); exact (HE1 q Hq)).
  assert (U9'' : bv_unsigned (ew E2 9) = TB_M) by (rewrite HE2 by lia; exact U9).
  assert (D32 : sv_denot E2 (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (bv_swrap 32 (DSpec.sf_send (mrx_f fr n))))
    by (apply AD.mrxd_den_sext32; [rewrite HE2 by lia; exact E32 | exact Fsn]).
  mrxd_chunk HS 1%nat 0%nat U9'' 1 (@eq_refl _ (Z_to_bv 64 1)) V76.
  mrxd_chunk HS 2%nat 0%nat U9'' (bv_swrap 32 (DSpec.sf_send (mrx_f fr n))) D32 V80.
  assert (HTW : tw_at TMAP_B (aview segs (w_H Wc) (ms_mem ms)) (mrxd_B5 fr n Bwc)).
  { unfold mrxd_B5. apply (mrxd_world5 Bwc _ _ _ Htw).
    - intros j Hj. rewrite <- (AD.mrxd_le_sw32 (DSpec.sf_send (mrx_f fr n)) j). exact (V80 j Hj).
    - exact V76.
    - intros x Hx N1. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      apply KA; lia. }
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ mrx_wr a ->
    aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a)
    by (intros a Ha Hn; apply KA; [exact Ha | intros Hx; apply Hn; apply mrxd_wr; right; left; exact Hx]).
  mrxd_hp HS regs2 [Z_to_bv 64 (DSpec.sf_send (mrx_f fr n)); Z_to_bv 64 (TI.tf_addr fr + DSpec.sf_body (mrx_f fr n));
    Z_to_bv 64 (DSpec.sf_body_len (mrx_f fr n)); Z_to_bv 64 (mrxd_b30 fr)] HE2 HP.
  mrxd_reg HS (11%bv : bv 5) (w64 1) Q11 ltac:(reflexivity).
  mrxd_reg HS (12%bv : bv 5) (w64 TB_OW) Q12 ltac:(apply AD.mrxd_den_atom; rewrite HE2 by lia; exact E12).
  mrxd_reg HS (13%bv : bv 5) (w64 (DSpec.sf_retry (mrx_f fr n))) Q13
    ltac:(apply AD.mrxd_den_atom; rewrite HE2 by lia; exact E13).
  mrxd_reg HS (14%bv : bv 5) (w64 (bv_swrap 32 (DSpec.sf_send (mrx_f fr n)))) Q14 ltac:(exact D32).
  mrxd_reg HS (16%bv : bv 5) (w64 (DSpec.sf_body_len (mrx_f fr n))) Q16
    ltac:(apply AD.mrxd_den_atom; rewrite HE2 by lia; exact E34).
  pmkst HS. rewrite (mrxd_pcl OFF_D6 15328 eq_refl).
  exact (mrxd_to_d6 Wc _ ly2 S2 regs2 mem2 (ms_regs ms) (ms_mem ms) mdC B3 HK6 HJ Hfr Hperm Hmo Hsp Hgp Htp Hhi HP Hsv
    Hcur KW HTW R18 Q11 Q12 Q13 Q14 Q16 HM6 Htk Hr).
Qed.

(* ------------------------------------------------------------------ *)
(* DATA: OW.acks, M.fail, the backoff, the duplicate test              *)
(* ------------------------------------------------------------------ *)

Lemma mrx_seg_data : K (MRX_PC OFF_TICK) (R_TICK Bw' r) -> K (MRX_PC OFF_DATA) (R_DATA B fr n sp1 Bw' r).
Proof using All.
intros HKT.
pose proof (mrxd_seg_d5 HKT (mrxd_seg_d6 HKT)) as HK5.
unfold mrx_K at 1. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hperm & Hmo & Hsp & Hgp & Htp & Hhi & Hsv & Htw & HR).
destruct HR as (Hcur & Hcmd & R11 & R9 & R18 & B3 & Hm & Htk & Hr).
pose proof Hcur as (Hok & Hfrs & Hsf).
pose proof HST as (Hsp1 & Hsp16 & Hceil & Hlo & Hhi47 & _ & _ & _ & _ & _ & _ & Hfa0 & Hfan & Hfa64 & _).
pose proof (mrx_ok_fields fr n Hok) as (Fd & Fs & Fb & F30 & Fl0 & Fln & Fc & Fr & Fsn & Fa).
assert (EM : TB_M = 6155744) by reflexivity. assert (EO : TB_OW = 6237408) by reflexivity.
assert (EG : TB_g_cfg = 6155520) by reflexivity.
assert (FR : MRX_FRAME = 112) by reflexivity.
assert (STK : MRX_STK = 8384) by (vm_compute; reflexivity).
assert (M16 : (sp1 - MRX_FRAME) mod 16 = 0).
{ rewrite FR. replace (sp1 - 112) with (sp1 + (-7) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
(* the model *)
destruct (mrxd_data_inv fr n Bwc B3 Hm) as (HnI & Hm2). clear Hm.
pose proof (tw_len _ _ _ Htw) as LB.
assert (FV : TW.M_desk_counter_valid (mrxd_B4 fr n Bwc) = TW.M_desk_counter_valid Bwc).
{ unfold TW.M_desk_counter_valid, TW.s32_at.
  rewrite (mrxd_B4_u fr n Bwc _ LB) by (unfold TW.A_M_desk_counter_valid; lia). reflexivity. }
assert (FC : TW.M_desk_counter (mrxd_B4 fr n Bwc) = TW.M_desk_counter Bwc).
{ unfold TW.M_desk_counter. apply (mrxd_B4_u fr n Bwc _ LB); unfold TW.A_M_desk_counter; lia. }
assert (FBK : AD.mrxd_bkv (AD.mrxd_B1 Bwc) = TS0.u64 (TW.g_now Bwc + TC.h_ms_m (TW.Cfg_backoff_ms Bwc))).
{ unfold AD.mrxd_bkv. rewrite (AD.mrxd_B1_now Bwc LB), (AD.mrxd_B1_bms Bwc LB). reflexivity. }
clear LB.
(* the values *)
pose proof (TWL.u_at_range Bwc TW.A_M_desk_counter_valid 4) as R34.
pose proof (TWL.u_at_range Bwc TW.A_M_desk_counter 4) as R35.
pose proof (TWL.u_at_range Bwc TW.A_OW_acks 4) as R36.
pose proof (TWL.u_at_range Bwc TW.A_Cfg_backoff_ms 4) as R37.
pose proof (TWL.u_at_range Bwc TW.OFF_g_now 8) as Rnow.
change (8 * Z.of_nat 4) with 32 in R34, R35, R36, R37. change (8 * Z.of_nat 8) with 64 in Rnow.
change (TW.u_at Bwc TW.A_M_desk_counter 4) with (TW.M_desk_counter Bwc) in R35.
pose proof (TWL.s32_range Bwc TW.A_M_desk_counter_valid) as S34.
change (TW.s32_at Bwc TW.A_M_desk_counter_valid) with (TW.M_desk_counter_valid Bwc) in S34.
pose proof (TWL.s32_range Bwc TW.A_OW_acks) as S36.
change (TW.s32_at Bwc TW.A_OW_acks) with (TW.OW_acks Bwc) in S36.
(* the valuation: 32 = f.retry, 33 = f.send, 34 = M.desk_counter_valid, 35 = M.desk_counter, 36 = OW.acks,
   37 = g_cfg.backoff_ms *)
set (E0 := Eimg (PI := PI_transportb) (Ereg regs2 [Z_to_bv 64 (DSpec.sf_retry (mrx_f fr n));
  Z_to_bv 64 (DSpec.sf_send (mrx_f fr n));
  Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_counter_valid 4); Z_to_bv 64 (TW.M_desk_counter Bwc);
  Z_to_bv 64 (TW.u_at Bwc TW.A_OW_acks 4); Z_to_bv 64 (TW.u_at Bwc TW.A_Cfg_backoff_ms 4)])).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (E32 : ew E0 32 = Z_to_bv 64 (DSpec.sf_retry (mrx_f fr n)))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 (DSpec.sf_send (mrx_f fr n)))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_counter_valid 4))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E0 35 = Z_to_bv 64 (TW.M_desk_counter Bwc))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E0 36 = Z_to_bv 64 (TW.u_at Bwc TW.A_OW_acks 4))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
assert (E37 : ew E0 37 = Z_to_bv 64 (TW.u_at Bwc TW.A_Cfg_backoff_ms 4))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 5)).
destruct mrxd_vals as (V12 & V52).
assert (E253 : ew E0 (A_OBJ 12) = Z_to_bv 64 TB_OW)
  by (unfold E0; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V12; reflexivity).
assert (E293 : ew E0 (A_OBJ 52) = Z_to_bv 64 (TB_g_cfg + 36))
  by (unfold E0; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V52; reflexivity).
assert (U253 : bv_unsigned (ew E0 (A_OBJ 12)) = TB_OW) by (rewrite E253; apply unsigned_lit_small; lia).
assert (U253' : bv_unsigned (ew E0 253%nat) = TB_OW) by exact U253.
assert (U293 : bv_unsigned (ew E0 (A_OBJ 52)) = TB_g_cfg + 36) by (rewrite E293; apply unsigned_lit_small; lia).
assert (U293' : bv_unsigned (ew E0 293%nat) = TB_g_cfg + 36) by exact U293.
assert (E9 : ew E0 9 = Z_to_bv 64 TB_M) by exact (mrxd_ew regs2 _ 9 _ _ R9 eq_refl).
assert (E11 : ew E0 11 = Z_to_bv 64 (TW.g_now Bwc)) by exact (mrxd_ew regs2 _ 11 _ _ R11 eq_refl).
assert (Esp : ew E0 2 = Z_to_bv 64 (sp1 - MRX_FRAME)) by exact (mrxd_ew regs2 _ 2 _ _ Hsp eq_refl).
assert (E18 : ew E0 18 = Z_to_bv 64 SHADOW_OFF) by exact (mrxd_ew regs2 _ 18 _ _ R18 eq_refl).
assert (U9 : bv_unsigned (ew E0 9) = TB_M) by (rewrite E9; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E0 2) = sp1 - MRX_FRAME) by (rewrite Esp; apply unsigned_lit_small; lia).
(* the values the code computes *)
assert (DA3 : sv_denot E0 (SExt true 32 (SOff 36 0)) = Z_to_bv 64 (TW.OW_acks Bwc))
  by exact (AD.mrxd_den_sext32 E0 36 _ E36 R36).
assert (DA : sv_denot E0 (SAluw ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)) =
  Z_to_bv 64 (bv_swrap 32 (TW.OW_acks Bwc + 1))) by exact (mrxd_den_addw E0 _ _ 1 DA3).
assert (DR : sv_denot E0 (SExt false 16 (SOff 32 0)) = Z_to_bv 64 (DSpec.sf_retry (mrx_f fr n)))
  by (apply AD.mrxd_den_zext; [exact E32 | change (2 ^ Z.of_N 16) with 65536; lia | lia]).
assert (DDV : sv_denot E0 (SExt true 32 (SOff 34 0)) = Z_to_bv 64 (TW.M_desk_counter_valid Bwc))
  by exact (AD.mrxd_den_sext32 E0 34 _ E34 R34).
assert (DDC : sv_denot E0 (SExt true 32 (SOff 35 0)) = Z_to_bv 64 (bv_swrap 32 (TW.M_desk_counter Bwc)))
  by exact (AD.mrxd_den_sext32 E0 35 _ E35 R35).
assert (DSN : sv_denot E0 (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (bv_swrap 32 (DSpec.sf_send (mrx_f fr n))))
  by exact (AD.mrxd_den_sext32 E0 33 _ E33 Fsn).
assert (DBK : sv_denot E0 (SAlu ALU_ADD (SMd M_MUL (SExt false 32 (SOff 37 0)) (SLit 1000)) (SOff 11 0)) =
  Z_to_bv 64 (TS0.u64 (TW.g_now Bwc + TC.h_ms_m (TW.Cfg_backoff_ms Bwc))))
  by exact (mrxd_bk_den E0 11 37 _ _ E11 E37 Rnow R37).
pose proof (UMR.mr_swrap32_range (TW.OW_acks Bwc + 1)) as RW.
(* the entry state *)
assert (HS : st_ok_pi segs VAL E0 ss_data
  (restrict (w_H Wc) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + (AF_m_rx + OFF_DATA))) mem2 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold ss_data.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + unfold mrxd_stk, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val segs E0 _ (sp1 - MRX_FRAME) 30 2 (SOff 32 0) (DSpec.sf_retry (mrx_f fr n)));
          [exact (AD.mrxd_den_atom E0 32 _ E32) | change (8 * Z.of_N 2) with 16; lia | lia |].
        exact (mrx_sf_retry _ _ _ _ Hsf).
      * apply (chunk_ok_val segs E0 _ (sp1 - MRX_FRAME) 32 4 (SOff 33 0) (DSpec.sf_send (mrx_f fr n)));
          [exact (AD.mrxd_den_atom E0 33 _ E33) | change (8 * Z.of_N 4) with 32; lia | lia |].
        exact (mrx_sf_send _ _ _ _ Hsf).
    + unfold mrxd_dcvR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E0 _ TB_M 76 4 (SOff 34 0) (TW.u_at Bwc TW.A_M_desk_counter_valid 4));
        [exact (AD.mrxd_den_atom E0 34 _ E34) | change (8 * Z.of_N 4) with 32; lia | lia |].
      exact (tw_read_val segs _ TMAP_B Bwc TW.OFF_M TB_M TW.SZ_M 76 4 TMAP_B_ok Htw TMAP_B_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold mrxd_dcR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E0 _ TB_M 80 4 (SOff 35 0) (TW.M_desk_counter Bwc));
        [exact (AD.mrxd_den_atom E0 35 _ E35) | change (8 * Z.of_N 4) with 32; lia | lia |].
      exact (tw_read_val segs _ TMAP_B Bwc TW.OFF_M TB_M TW.SZ_M 80 4 TMAP_B_ok Htw TMAP_B_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold mrxd_fail, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw). apply mrxd_inG. lia.
    + unfold mrxd_acks, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U253. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_OW + o) G_HARNESS_B_rw). apply mrxd_inG. lia.
      * constructor; [|constructor].
        apply (chunk_ok_val segs E0 _ TB_OW 204 4 (SOff 36 0) (TW.u_at Bwc TW.A_OW_acks 4));
          [exact (AD.mrxd_den_atom E0 36 _ E36) | change (8 * Z.of_N 4) with 32; lia | lia |].
        exact (tw_read_val segs _ TMAP_B Bwc TW.OFF_OW TB_OW TW.SZ_OW 204 4 TMAP_B_ok Htw TMAP_B_OW
          ltac:(lia) ltac:(unfold TW.SZ_OW; lia)).
    + unfold mrxd_bms, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U293. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E0 _ (TB_g_cfg + 36) 0 4 (SOff 37 0) (TW.u_at Bwc TW.A_Cfg_backoff_ms 4));
        [exact (AD.mrxd_den_atom E0 37 _ E37) | change (8 * Z.of_N 4) with 32; lia | lia |].
      rewrite Z.add_0_r.
      exact (tw_read_val segs _ TMAP_B Bwc TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 36 4 TMAP_B_ok Htw TMAP_B_g_cfg
        ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)).
  - apply pairwise_disjoint_of_extents.
    unfold mrxd_stk, mrxd_dcvR, mrxd_dcR, mrxd_fail, mrxd_acks, mrxd_bms, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U9, U253, U293.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; first [exact I | lia].
  - unfold data_facts, MRXD_SP, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U9, U253, E18, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | exact M16 | reflexivity]. }
assert (SHOK : sh_ok segs MRXD_Bx [] E0 (mrestrict (w_H Wc) mem2)) by (unfold sh_ok; apply Forall_nil).
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (PI := PI_transportb)) as BR.
rewrite (mrx_pcv OFF_DATA).
(* run 1, +0x1d8 .. +0x1e8: a2 = &OW, OW.acks + 1; it stops at the overflow test `blt a0, a3`. *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
{ mrxd_awr2 U9 U253'. }
mrxd_md mdA.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 88 <= a < TB_M + 92) -> ~ (TB_OW + 204 <= a < TB_OW + 208) ->
  aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _ (fun x => (TB_M + 88 <= x < TB_M + 92) \/ (TB_OW + 204 <= x < TB_OW + 208)) HFr);
    [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U9, ?U253', ?U293' in Hx; lia). }
clear HF HFr HG. rename ms into ms1.
psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
{ (* the trap word: OW.acks = INT_MAX, where the model is None *)
  exfalso. rewrite DA, DA3 in Hc. cbn [branch_taken] in Hc. rewrite EPI.mrxk_lts in Hc by lia.
  rewrite UMR.mr_inc_trap in Hc by lia. apply Z.eqb_eq in Hc. exact (HnI Hc). }
clear Hc.
(* run 2, +0x1ec .. +0x1f8: a3 = f.retry, OW.acks + 1 stored, M.fail = 0; it stops at `beqz a3`. *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
{ mrxd_awr2 U9 U253'. }
mrxd_md mdB.
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 88 <= a < TB_M + 92) -> ~ (TB_OW + 204 <= a < TB_OW + 208) ->
  aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
{ intros a Ha H1 H2. rewrite <- (KA1 a Ha H1 H2).
  apply (kept_of_frame _ _ _ _ _ (fun x => (TB_M + 88 <= x < TB_M + 92) \/ (TB_OW + 204 <= x < TB_OW + 208)) HFr);
    [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U9, ?U253', ?U293' in Hx; lia). }
clear HF HFr HG KA1. rename ms into ms2.
psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
all: rewrite DR in Hc; cbn [branch_taken sv_denot] in Hc; rewrite EPI.mrxk_eqb in Hc by lia.
- (* retry = 0: no backoff, never the duplicate *)
  apply Z.eqb_eq in Hc.
  assert (TR0 : TC.truth (DSpec.sf_retry (mrx_f fr n)) = false) by (unfold TC.truth; rewrite Hc; reflexivity).
  clear Hc.
  (* run 3, +0x214 .. +0x218: M.desk_counter_valid; it stops at `beqz a0`. *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
  { mrxd_awr2 U9 U253'. }
  mrxd_md mdC.
  assert (KA3 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 88 <= a < TB_M + 92) -> ~ (TB_OW + 204 <= a < TB_OW + 208) ->
    aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
  { intros a Ha H1 H2. rewrite <- (KA2 a Ha H1 H2).
    apply (kept_of_frame _ _ _ _ _ (fun x => (TB_M + 88 <= x < TB_M + 92) \/ (TB_OW + 204 <= x < TB_OW + 208)) HFr);
      [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
    intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U9, ?U253', ?U293' in Hx; lia). }
  clear HF HFr HG KA2. rename ms into ms3.
  psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
  (* either way (the second `beqz a3` is decided by the first), to D5 *)
  all: clear Hc.
  all: paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D5); [mrxd_awr2 U9 U253' |].
  all: mrxd_md mdD.
  all: assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 88 <= a < TB_M + 92) -> ~ (TB_OW + 204 <= a < TB_OW + 208) ->
    aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a)
    by (intros a Ha H1 H2; rewrite <- (KA3 a Ha H1 H2);
        apply (kept_of_frame _ _ _ _ _ (fun x => (TB_M + 88 <= x < TB_M + 92) \/ (TB_OW + 204 <= x < TB_OW + 208)) HFr);
        [ intros b wlo whi x Hin Hx; cbv beta; mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U9, ?U253', ?U293' in Hx; lia)
        | exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)] ]).
  all: clear HF HFr HG.
  all: mrxd_env HS E0 E1 HE1.
  all: assert (U9' : bv_unsigned (ew E1 9) = TB_M) by (rewrite HE1 by lia; exact U9).
  all: assert (U253'' : bv_unsigned (ew E1 253%nat) = TB_OW) by (rewrite HE1 by lia; exact U253').
  all: assert (DA' : sv_denot E1 (SAluw ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)) =
    Z_to_bv 64 (bv_swrap 32 (TW.OW_acks Bwc + 1)))
    by (apply mrxd_den_addw; apply (AD.mrxd_den_sext32 E1 36 _ ltac:(rewrite HE1 by lia; exact E36) R36)).
  all: mrxd_chunk HS 4%nat 0%nat U253'' (bv_swrap 32 (TW.OW_acks Bwc + 1)) DA' VA.
  all: mrxd_chunk HS 3%nat 0%nat U9' 0 (@eq_refl _ (Z_to_bv 64 0)) VF.
  all: assert (HTW : tw_at TMAP_B (aview segs (w_H Wc) (ms_mem ms)) (mrxd_B4 fr n Bwc))
    by (rewrite (mrxd_B4_0 fr n Bwc TR0); unfold AD.mrxd_B1; apply (mrxd_world1 Bwc _ _ _ Htw);
        [ intros j Hj; rewrite <- (AD.mrxd_le_sw32 (TW.OW_acks Bwc + 1) j); exact (VA j Hj)
        | exact VF
        | intros x Hx N1 N2; pose proof (TMAP_B_hull x Hx) as Hh; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh;
          apply KA; lia ]).
  all: assert (HM3 : UMR.mr_data3 fr n (mrxd_B4 fr n Bwc) = Some (B3, tt))
    by (apply (mrxd_data2_d3 fr n _ B3); [rewrite TR0, andb_false_r; reflexivity | exact Hm2]).
  all: assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ mrx_wr a ->
    aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a)
    by (intros a Ha Hn; apply KA;
        [ exact Ha | intros Hx; apply Hn; apply mrxd_wr; right; right; left; exact Hx
        | intros Hx; apply Hn; apply mrxd_wr; right; right; right; left; exact Hx ]).
  all: mrxd_hp HS regs2 [Z_to_bv 64 (DSpec.sf_retry (mrx_f fr n)); Z_to_bv 64 (DSpec.sf_send (mrx_f fr n));
    Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_counter_valid 4); Z_to_bv 64 (TW.M_desk_counter Bwc);
    Z_to_bv 64 (TW.u_at Bwc TW.A_OW_acks 4); Z_to_bv 64 (TW.u_at Bwc TW.A_Cfg_backoff_ms 4)] HE1 HP.
  all: mrxd_reg HS (12%bv : bv 5) (w64 TB_OW) Q12 ltac:(apply AD.mrxd_den_atom; rewrite HE1 by lia; exact E253).
  all: mrxd_reg HS (13%bv : bv 5) (w64 (DSpec.sf_retry (mrx_f fr n))) Q13
    ltac:(apply AD.mrxd_den_zext; [rewrite HE1 by lia; exact E32 | change (2 ^ Z.of_N 16) with 65536; lia | lia]).
  all: pmkst HS.
  all: rewrite (mrxd_pcl OFF_D5 15272 eq_refl).
  all: exact (mrxd_to_d5 Wc _ ly2 S2 regs2 mem2 (ms_regs ms) (ms_mem ms) mdD B3 HK5 HJ Hfr Hperm Hmo Hsp Hgp Htp Hhi HP
    Hsv Hcur KW HTW R9 R18 Q12 Q13 HM3 Htk Hr).
- (* retry <> 0: the backoff *)
  apply Z.eqb_neq in Hc.
  assert (TR1 : TC.truth (DSpec.sf_retry (mrx_f fr n)) = true)
    by (unfold TC.truth; rewrite (proj2 (Z.eqb_neq _ _) Hc); reflexivity).
  clear Hc.
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
    let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.
  (* M.backoff_until's 8 bytes join the state *)
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
    pose proof (st_ok_pi_add_region Ex ss (restrict Hh m) mrxd_bk HS eq_refl
      ltac:(unfold mrxd_bk, region_ok;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
            rewrite U9; split; [lia|]; split; [lia|];
            split; [intros o Ho; apply (gx_rw_writable segs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw); apply mrxd_inG; lia
                   | constructor])
      ltac:(cbn [ss_mem YP09.all_disjoint]; unfold YP09.extent_disjoint, mrxd_bk;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
            rewrite ?Usp, ?U9, ?U253', ?U293'; repeat split; lia)) as HSb end.
  clear HS.
  lazymatch type of HSb with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
    let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HSb end.
  rename HSb into HS.
  (* run 3, +0x1fc .. +0x218: the backoff stored at M + 56, M.desk_counter_valid; it stops at `beqz a0`. *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
  { mrxd_awr2 U9 U253'. }
  mrxd_md mdC.
  assert (KA3 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 88 <= a < TB_M + 92) -> ~ (TB_OW + 204 <= a < TB_OW + 208) ->
    ~ (TB_M + 56 <= a < TB_M + 64) -> aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
  { intros a Ha H1 H2 H3. rewrite <- (KA2 a Ha H1 H2).
    apply (kept_of_frame _ _ _ _ _ (fun x => (TB_M + 88 <= x < TB_M + 92) \/ (TB_OW + 204 <= x < TB_OW + 208) \/
      (TB_M + 56 <= x < TB_M + 64)) HFr);
      [| exact Ha | intros [Hx|[Hx|Hx]]; [exact (H1 Hx) | exact (H2 Hx) | exact (H3 Hx)]].
    intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U9, ?U253', ?U293' in Hx; lia). }
  clear HF HFr HG KA2. rename ms into ms3.
  psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
  all: rewrite DDV in Hc; cbn [branch_taken sv_denot] in Hc; rewrite EPI.mrxk_eqb in Hc by lia.
  + (* M.desk_counter_valid = 0: to D5 *)
    apply Z.eqb_eq in Hc. rename Hc into DV0.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D5).
    { mrxd_awr2 U9 U253'. }
    mrxd_md mdD.
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 88 <= a < TB_M + 92) -> ~ (TB_OW + 204 <= a < TB_OW + 208) ->
      ~ (TB_M + 56 <= a < TB_M + 64) -> aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
    { intros a Ha H1 H2 H3. rewrite <- (KA3 a Ha H1 H2 H3).
      apply (kept_of_frame _ _ _ _ _ (fun x => (TB_M + 88 <= x < TB_M + 92) \/ (TB_OW + 204 <= x < TB_OW + 208) \/
        (TB_M + 56 <= x < TB_M + 64)) HFr);
        [| exact Ha | intros [Hx|[Hx|Hx]]; [exact (H1 Hx) | exact (H2 Hx) | exact (H3 Hx)]].
      intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U9, ?U253', ?U293' in Hx; lia). }
    clear HF HFr HG.
    mrxd_env HS E0 E1 HE1.
    assert (U9' : bv_unsigned (ew E1 9) = TB_M) by (rewrite HE1 by lia; exact U9).
    assert (U253'' : bv_unsigned (ew E1 253%nat) = TB_OW) by (rewrite HE1 by lia; exact U253').
    assert (DA' : sv_denot E1 (SAluw ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)) =
      Z_to_bv 64 (bv_swrap 32 (TW.OW_acks Bwc + 1)))
      by (apply mrxd_den_addw; apply (AD.mrxd_den_sext32 E1 36 _ ltac:(rewrite HE1 by lia; exact E36) R36)).
    assert (DBK' : sv_denot E1 (SAlu ALU_ADD (SMd M_MUL (SExt false 32 (SOff 37 0)) (SLit 1000)) (SOff 11 0)) =
      Z_to_bv 64 (TS0.u64 (TW.g_now Bwc + TC.h_ms_m (TW.Cfg_backoff_ms Bwc))))
      by exact (mrxd_bk_den E1 11 37 _ _ (eq_trans (HE1 11%nat ltac:(lia)) E11) (eq_trans (HE1 37%nat ltac:(lia)) E37)
                  Rnow R37).
    mrxd_chunk HS 5%nat 0%nat U253'' (bv_swrap 32 (TW.OW_acks Bwc + 1)) DA' VA.
    mrxd_chunk HS 4%nat 0%nat U9' 0 (@eq_refl _ (Z_to_bv 64 0)) VF.
    mrxd_chunk HS 0%nat 0%nat U9' (TS0.u64 (TW.g_now Bwc + TC.h_ms_m (TW.Cfg_backoff_ms Bwc))) DBK' VB.
    assert (HTW : tw_at TMAP_B (aview segs (w_H Wc) (ms_mem ms)) (mrxd_B4 fr n Bwc)).
    { rewrite (mrxd_B4_1 fr n Bwc TR1), FBK. unfold AD.mrxd_B1. apply (mrxd_world4 Bwc _ _ _ _ Htw).
      - intros j Hj. rewrite <- (AD.mrxd_le_sw32 (TW.OW_acks Bwc + 1) j). exact (VA j Hj).
      - exact VF.
      - exact VB.
      - intros x Hx N1 N2 N3. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
        apply KA; lia. }
    assert (HM3 : UMR.mr_data3 fr n (mrxd_B4 fr n Bwc) = Some (B3, tt)).
    { apply (mrxd_data2_d3 fr n _ B3); [|exact Hm2]. rewrite FV, DV0. reflexivity. }
    assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ mrx_wr a ->
      aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a)
      by (intros a Ha Hn; apply KA;
          [ exact Ha | intros Hx; apply Hn; apply mrxd_wr; right; right; left; exact Hx
          | intros Hx; apply Hn; apply mrxd_wr; right; right; right; left; exact Hx
          | intros Hx; apply Hn; apply mrxd_wr; left; exact Hx ]).
    mrxd_hp HS regs2 [Z_to_bv 64 (DSpec.sf_retry (mrx_f fr n)); Z_to_bv 64 (DSpec.sf_send (mrx_f fr n));
      Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_counter_valid 4); Z_to_bv 64 (TW.M_desk_counter Bwc);
      Z_to_bv 64 (TW.u_at Bwc TW.A_OW_acks 4); Z_to_bv 64 (TW.u_at Bwc TW.A_Cfg_backoff_ms 4)] HE1 HP.
    mrxd_reg HS (12%bv : bv 5) (w64 TB_OW) Q12 ltac:(apply AD.mrxd_den_atom; rewrite HE1 by lia; exact E253).
    mrxd_reg HS (13%bv : bv 5) (w64 (DSpec.sf_retry (mrx_f fr n))) Q13
      ltac:(apply AD.mrxd_den_zext; [rewrite HE1 by lia; exact E32 | change (2 ^ Z.of_N 16) with 65536; lia | lia]).
    pmkst HS. rewrite (mrxd_pcl OFF_D5 15272 eq_refl).
    exact (mrxd_to_d5 Wc _ ly2 S2 regs2 mem2 (ms_regs ms) (ms_mem ms) mdD B3 HK5 HJ Hfr Hperm Hmo Hsp Hgp Htp Hhi HP
      Hsv Hcur KW HTW R9 R18 Q12 Q13 HM3 Htk Hr).
  + (* M.desk_counter_valid <> 0: the counter test *)
    apply Z.eqb_neq in Hc. rename Hc into DV1.
    (* run 4, +0x21c .. +0x228: M.desk_counter, f.send; it stops at `beq a1, a0`. *)
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
    { mrxd_awr2 U9 U253'. }
    mrxd_md mdD.
    assert (KA4 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 88 <= a < TB_M + 92) -> ~ (TB_OW + 204 <= a < TB_OW + 208) ->
      ~ (TB_M + 56 <= a < TB_M + 64) -> aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
    { intros a Ha H1 H2 H3. rewrite <- (KA3 a Ha H1 H2 H3).
      apply (kept_of_frame _ _ _ _ _ (fun x => (TB_M + 88 <= x < TB_M + 92) \/ (TB_OW + 204 <= x < TB_OW + 208) \/
        (TB_M + 56 <= x < TB_M + 64)) HFr);
        [| exact Ha | intros [Hx|[Hx|Hx]]; [exact (H1 Hx) | exact (H2 Hx) | exact (H3 Hx)]].
      intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U9, ?U253', ?U293' in Hx; lia). }
    clear HF HFr HG KA3. rename ms into ms4.
    psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
    all: rewrite DSN, DDC in Hc; cbn [branch_taken] in Hc; rewrite EPI.mrx_eqb_sw in Hc by lia.
    * (* send = M.desk_counter: the duplicate, to TICK *)
      apply Z.eqb_eq in Hc.
      assert (EB3 : B3 = mrxd_B4 fr n Bwc).
      { apply (mrxd_data2_tick fr n _ B3); [|exact Hm2].
        rewrite FV, FC, TR1. unfold TC.truth. rewrite (proj2 (Z.eqb_neq _ _) DV1), Hc, Z.eqb_refl. reflexivity. }
      subst B3.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
      { mrxd_awr2 U9 U253'. }
      mrxd_md mdE.
      assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 88 <= a < TB_M + 92) -> ~ (TB_OW + 204 <= a < TB_OW + 208) ->
        ~ (TB_M + 56 <= a < TB_M + 64) -> aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
      { intros a Ha H1 H2 H3. rewrite <- (KA4 a Ha H1 H2 H3).
        apply (kept_of_frame _ _ _ _ _ (fun x => (TB_M + 88 <= x < TB_M + 92) \/ (TB_OW + 204 <= x < TB_OW + 208) \/
          (TB_M + 56 <= x < TB_M + 64)) HFr);
          [| exact Ha | intros [Hx|[Hx|Hx]]; [exact (H1 Hx) | exact (H2 Hx) | exact (H3 Hx)]].
        intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U9, ?U253', ?U293' in Hx; lia). }
      clear HF HFr HG.
      mrxd_env HS E0 E1 HE1.
      assert (U9' : bv_unsigned (ew E1 9) = TB_M) by (rewrite HE1 by lia; exact U9).
      assert (U253'' : bv_unsigned (ew E1 253%nat) = TB_OW) by (rewrite HE1 by lia; exact U253').
      assert (DA' : sv_denot E1 (SAluw ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)) =
        Z_to_bv 64 (bv_swrap 32 (TW.OW_acks Bwc + 1)))
        by (apply mrxd_den_addw; apply (AD.mrxd_den_sext32 E1 36 _ ltac:(rewrite HE1 by lia; exact E36) R36)).
      assert (DBK' : sv_denot E1 (SAlu ALU_ADD (SMd M_MUL (SExt false 32 (SOff 37 0)) (SLit 1000)) (SOff 11 0)) =
        Z_to_bv 64 (TS0.u64 (TW.g_now Bwc + TC.h_ms_m (TW.Cfg_backoff_ms Bwc))))
        by exact (mrxd_bk_den E1 11 37 _ _ (eq_trans (HE1 11%nat ltac:(lia)) E11)
                    (eq_trans (HE1 37%nat ltac:(lia)) E37) Rnow R37).
      mrxd_chunk HS 5%nat 0%nat U253'' (bv_swrap 32 (TW.OW_acks Bwc + 1)) DA' VA.
      mrxd_chunk HS 4%nat 0%nat U9' 0 (@eq_refl _ (Z_to_bv 64 0)) VF.
      mrxd_chunk HS 0%nat 0%nat U9' (TS0.u64 (TW.g_now Bwc + TC.h_ms_m (TW.Cfg_backoff_ms Bwc))) DBK' VB.
      assert (HTW : tw_at TMAP_B (aview segs (w_H Wc) (ms_mem ms)) (mrxd_B4 fr n Bwc)).
      { rewrite (mrxd_B4_1 fr n Bwc TR1), FBK. unfold AD.mrxd_B1. apply (mrxd_world4 Bwc _ _ _ _ Htw).
        - intros j Hj. rewrite <- (AD.mrxd_le_sw32 (TW.OW_acks Bwc + 1) j). exact (VA j Hj).
        - exact VF.
        - exact VB.
        - intros x Hx N1 N2 N3. pose proof (TMAP_B_hull x Hx) as Hh.
          unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KA; lia. }
      mrxd_hp HS regs2 [Z_to_bv 64 (DSpec.sf_retry (mrx_f fr n)); Z_to_bv 64 (DSpec.sf_send (mrx_f fr n));
        Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_counter_valid 4); Z_to_bv 64 (TW.M_desk_counter Bwc);
        Z_to_bv 64 (TW.u_at Bwc TW.A_OW_acks 4); Z_to_bv 64 (TW.u_at Bwc TW.A_Cfg_backoff_ms 4)] HE1 HP.
      pmkst HS. rewrite (mrxd_pcl OFF_TICK 15648 eq_refl).
      apply (mrxd_exit (MRX_PC OFF_TICK) (R_TICK Bw' r) Wc _ ly2 S2 regs2 mem2 (ms_regs ms) (ms_mem ms) mdE HKT HJ
        Hfr Hperm Hmo Hsp Hgp Htp Hhi HP Hsv ltac:(intros a Ha; apply KA; lia) HTW).
      unfold R_TICK. split; [exact Htk | exact Hr].
    * (* send <> M.desk_counter: to D5 *)
      apply Z.eqb_neq in Hc. rename Hc into SNE.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_D5).
      { mrxd_awr2 U9 U253'. }
      mrxd_md mdE.
      assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 88 <= a < TB_M + 92) -> ~ (TB_OW + 204 <= a < TB_OW + 208) ->
        ~ (TB_M + 56 <= a < TB_M + 64) -> aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a).
      { intros a Ha H1 H2 H3. rewrite <- (KA4 a Ha H1 H2 H3).
        apply (kept_of_frame _ _ _ _ _ (fun x => (TB_M + 88 <= x < TB_M + 92) \/ (TB_OW + 204 <= x < TB_OW + 208) \/
          (TB_M + 56 <= x < TB_M + 64)) HFr);
          [| exact Ha | intros [Hx|[Hx|Hx]]; [exact (H1 Hx) | exact (H2 Hx) | exact (H3 Hx)]].
        intros b wlo whi x Hin Hx. cbv beta. mrxd_win Hin Hx ltac:(rewrite ?Usp, ?U9, ?U253', ?U293' in Hx; lia). }
      clear HF HFr HG.
      mrxd_env HS E0 E1 HE1.
      assert (U9' : bv_unsigned (ew E1 9) = TB_M) by (rewrite HE1 by lia; exact U9).
      assert (U253'' : bv_unsigned (ew E1 253%nat) = TB_OW) by (rewrite HE1 by lia; exact U253').
      assert (DA' : sv_denot E1 (SAluw ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)) =
        Z_to_bv 64 (bv_swrap 32 (TW.OW_acks Bwc + 1)))
        by (apply mrxd_den_addw; apply (AD.mrxd_den_sext32 E1 36 _ ltac:(rewrite HE1 by lia; exact E36) R36)).
      assert (DBK' : sv_denot E1 (SAlu ALU_ADD (SMd M_MUL (SExt false 32 (SOff 37 0)) (SLit 1000)) (SOff 11 0)) =
        Z_to_bv 64 (TS0.u64 (TW.g_now Bwc + TC.h_ms_m (TW.Cfg_backoff_ms Bwc))))
        by exact (mrxd_bk_den E1 11 37 _ _ (eq_trans (HE1 11%nat ltac:(lia)) E11)
                    (eq_trans (HE1 37%nat ltac:(lia)) E37) Rnow R37).
      mrxd_chunk HS 5%nat 0%nat U253'' (bv_swrap 32 (TW.OW_acks Bwc + 1)) DA' VA.
      mrxd_chunk HS 4%nat 0%nat U9' 0 (@eq_refl _ (Z_to_bv 64 0)) VF.
      mrxd_chunk HS 0%nat 0%nat U9' (TS0.u64 (TW.g_now Bwc + TC.h_ms_m (TW.Cfg_backoff_ms Bwc))) DBK' VB.
      assert (HTW : tw_at TMAP_B (aview segs (w_H Wc) (ms_mem ms)) (mrxd_B4 fr n Bwc)).
      { rewrite (mrxd_B4_1 fr n Bwc TR1), FBK. unfold AD.mrxd_B1. apply (mrxd_world4 Bwc _ _ _ _ Htw).
        - intros j Hj. rewrite <- (AD.mrxd_le_sw32 (TW.OW_acks Bwc + 1) j). exact (VA j Hj).
        - exact VF.
        - exact VB.
        - intros x Hx N1 N2 N3. pose proof (TMAP_B_hull x Hx) as Hh.
          unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KA; lia. }
      assert (HM3 : UMR.mr_data3 fr n (mrxd_B4 fr n Bwc) = Some (B3, tt)).
      { apply (mrxd_data2_d3 fr n _ B3); [|exact Hm2].
        rewrite FC, (proj2 (Z.eqb_neq _ _) SNE), andb_false_r. reflexivity. }
      assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ mrx_wr a ->
        aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a)
        by (intros a Ha Hn; apply KA;
            [ exact Ha | intros Hx; apply Hn; apply mrxd_wr; right; right; left; exact Hx
            | intros Hx; apply Hn; apply mrxd_wr; right; right; right; left; exact Hx
            | intros Hx; apply Hn; apply mrxd_wr; left; exact Hx ]).
      mrxd_hp HS regs2 [Z_to_bv 64 (DSpec.sf_retry (mrx_f fr n)); Z_to_bv 64 (DSpec.sf_send (mrx_f fr n));
        Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_counter_valid 4); Z_to_bv 64 (TW.M_desk_counter Bwc);
        Z_to_bv 64 (TW.u_at Bwc TW.A_OW_acks 4); Z_to_bv 64 (TW.u_at Bwc TW.A_Cfg_backoff_ms 4)] HE1 HP.
      mrxd_reg HS (12%bv : bv 5) (w64 TB_OW) Q12 ltac:(apply AD.mrxd_den_atom; rewrite HE1 by lia; exact E253).
      mrxd_reg HS (13%bv : bv 5) (w64 (DSpec.sf_retry (mrx_f fr n))) Q13
        ltac:(apply AD.mrxd_den_zext; [rewrite HE1 by lia; exact E32 | change (2 ^ Z.of_N 16) with 65536; lia | lia]).
      pmkst HS. rewrite (mrxd_pcl OFF_D5 15272 eq_refl).
      exact (mrxd_to_d5 Wc _ ly2 S2 regs2 mem2 (ms_regs ms) (ms_mem ms) mdE B3 HK5 HJ Hfr Hperm Hmo Hsp Hgp Htp Hhi HP
        Hsv Hcur KW HTW R9 R18 Q12 Q13 HM3 Htk Hr).
Qed.

End seg.
