(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 714 of its 805 lines of code are new or changed and 939 lines of the source are left out. *)
(* m_rx_seg_body: the BODY segment of the image-B walk of m_rx (lib/B/Prog/m_rx_seg_kit.v), from the cut BODY
   (+0x100 = 0x84d1c) to the cuts EPI (M.state = S_CLOSED), TICK, SET (cmd e3 at S_ONLINE / S_WAKING, after the
   inlined m_lost's stores of M.desk_counter_valid and M.fly.on), DATA, HOST (cmd e1, body_len >= 33), ANNT (cmd e0,
   body_len >= 33, s0 = -1) and ACK.
   The code (m_rx_cg.v header): +0x100 - +0x108 a0 = M.state, `beq a0, 3` to +0x02c (a0 = 0, the epilogue);
   +0x10c - +0x120 a1 = g_now, a2 = f.cmd (sp + 40), the 8-byte store of g_now at M + 32 (M.last_rx), `bge 0xdf, cmd`;
   +0x124 - +0x12c `bgeu cmd - 0xe0, 2`; +0x130 - +0x140 f.body_len (sp + 56) < 33 to TICK, cmd <> 0xe1 to +0x310
   (s0 = -1, ANNT), else HOST; +0x154 - +0x15c cmd = 0 to DATA, cmd <> 0xa0 to TICK, else ACK; +0x1ac - +0x1c8
   cmd <> 0xe3 to TICK, M.state - 1 > 1 (unsigned) to TICK, else the 4-byte stores of 0 at M + 76 and M + 96 and
   a1 = 7, SET.
   The model: lib/U/Prog/T/m_rx.v mr_k and mr_sw, cut by the same tests (mbm_* below). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require m_rx.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRunB TransportGFrameB CanKit
YC1g YC1h m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_body.
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
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
Module UMR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T.m_rx.
Module AK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_kit.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module AB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_body.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the cut                                       *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the cut (2 = sp = sp1 - 112, 9 = s1 = &M, 18 = s2 = the shadow base), 32 the 4
   bytes of M.state, 33 g_now, 34 f.cmd, 35 f.body_len. Regions: the struct's two fields at sp + 40 and sp + 56,
   M.state (based on s1), g_now (object 28); added on the paths that store them: M.last_rx, M.desk_counter_valid and
   M.fly.on. *)
Definition mb_sp : YP09.region := YP09.mkRegion (Some 2%nat) 40 64 0 0
  [YP09.mkChunk 40 (YP09.CVal 1 (SOff 34 0)); YP09.mkChunk 56 (YP09.CVal 8 (SOff 35 0))].
Definition mb_st : YP09.region := YP09.mkRegion (Some 9%nat) 12 16 0 0 [YP09.mkChunk 12 (YP09.CVal 4 (SOff 32 0))].
Definition mb_now : YP09.region := YP09.mkRegion (Some (A_OBJ 28)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff 33 0))].
Definition mb_lrx : YP09.region := YP09.mkRegion (Some 9%nat) 32 40 32 40 [].
Definition mb_dcv : YP09.region := YP09.mkRegion (Some 9%nat) 76 80 76 80 [].
Definition mb_fly : YP09.region := YP09.mkRegion (Some 9%nat) 96 100 96 100 [].
Definition mb_regions : smem := [mb_sp; mb_st; mb_now].
Definition mb_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF TB_M TB_M 5); (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (34%nat, mkAF 0 255 0)] [] [].
Definition ss_mb : sstate := mkSS (AF_m_rx + OFF_BODY) sr_atoms mb_regions None mb_facts.
Definition MB_SH : list shent := [].
Definition MB_Bx : sv := SOff 18 0.

Definition mb_vals (fr : TI.tframe) (n : Z) (Bw : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4); Z_to_bv 64 (TW.g_now Bw);
   Z_to_bv 64 (DSpec.sf_cmd (mrx_f fr n)); Z_to_bv 64 (DSpec.sf_body_len (mrx_f fr n))].

(* The registers no run of the segment writes. *)
Definition MB_KEEP : list (bv 5) :=
  [Z_to_bv 5 2; Z_to_bv 5 3; Z_to_bv 5 4; Z_to_bv 5 9; Z_to_bv 5 18; Z_to_bv 5 19; Z_to_bv 5 20; Z_to_bv 5 21;
   Z_to_bv 5 22; Z_to_bv 5 23; Z_to_bv 5 24; Z_to_bv 5 25; Z_to_bv 5 26; Z_to_bv 5 27].
Ltac mb_in := unfold MB_KEEP; cbn [In]; repeat first [left; reflexivity | right].

Lemma mb_hi_in : forall q, 19 <= q <= 27 -> In (Z_to_bv 5 q) MB_KEEP.
Proof.
intros q Hq.
assert (H : q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]; subst q; mb_in.
Qed.

(* The windows the runs may write, by stage. *)
Definition mbX0 (a : Z) : Prop := False.
Definition mbX1 (a : Z) : Prop := TB_M + 32 <= a < TB_M + 40.
Definition mbX2 (a : Z) : Prop := mbX1 a \/ TB_M + 76 <= a < TB_M + 80 \/ TB_M + 96 <= a < TB_M + 100.

Lemma mb_inG : forall a, TB_M <= a < TB_M + 1648 -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TB_M, TW.SZ_M).
split; [exact (TMAP_B_in_G _ _ _ TMAP_B_M) | unfold in_zr, TW.SZ_M; cbn [fst snd]; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* Values the code forms, at a valuation                               *)
(* ------------------------------------------------------------------ *)

(* The image-free value and branch lemmas of image A's BODY segment are used by name (AB.mbd_sext, AB.mbd_off,
   AB.mbl_eq, AB.mbl_ne, AB.mbl_ge, AB.mbl_ltu, AB.mbl_geu_ann). *)

(* addiw a0, a0, -1 on the sign-extended M.state (+0x1b4), at the atom k of M.state's 4 bytes. *)
Lemma mbd_state12 : forall E k u, ew E k = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SAluw ALU_ADD (SExt true 32 (SOff k 0)) (SLit (-1))) =
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 u)) + -1)).
Proof.
intros E k u Hk Hu. rewrite denot_lit_U, U_of_S, S_SAluw, AB.mb_z2bv_wrap. cbn [zalu_raw].
rewrite U_SExt, U_SLit, U_SOff, Hk, unsigned_lit_small, Z.add_0_r by lia.
change (Z.of_N 32) with 32. f_equal. apply AB.mb_swrap32_congr.
rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
Z.div_mod_to_equations. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The model                                                           *)
(* ------------------------------------------------------------------ *)

Lemma mbm_closed : forall I fr n Bw B' r', TW.M_state Bw = TC.S_CLOSED -> UMR.mr_k I fr n Bw = Some (B', r') ->
  B' = Bw /\ r' = 0.
Proof.
intros I fr n Bw B' r' H Hk. unfold UMR.mr_k in Hk. rewrite H, Z.eqb_refl in Hk. cbv beta iota in Hk.
destruct (mrx_some_inv _ _ _ _ _ _ Hk) as [E1 E2]. split; [exact (eq_sym E1) | exact (eq_sym E2)].
Qed.

Lemma mbm_open : forall I fr n Bw B' r', TW.M_state Bw <> TC.S_CLOSED -> UMR.mr_k I fr n Bw = Some (B', r') ->
  exists B3, UMR.mr_sw I fr n (TW.set_M_last_rx Bw (TW.g_now Bw)) = Some (B3, tt) /\
    TC.m_tick_m B3 = Some (B', tt) /\ r' = 1.
Proof.
intros I fr n Bw B' r' H Hk. unfold UMR.mr_k in Hk. rewrite (proj2 (Z.eqb_neq _ _) H) in Hk. revert Hk.
destruct (UMR.mr_sw I fr n (TW.set_M_last_rx Bw (TW.g_now Bw))) as [[B3 []]|] eqn:SW; intros Hk;
  cbv beta iota in Hk; [|discriminate Hk].
revert Hk. destruct (TC.m_tick_m B3) as [[B4 []]|] eqn:TK; intros Hk; cbv beta iota in Hk; [|discriminate Hk].
destruct (mrx_some_inv _ _ _ _ _ _ Hk) as [E1 E2]. subst B4 r'.
exists B3. split; [first [reflexivity | exact SW]|]. split; [first [reflexivity | exact TK] | reflexivity].
Qed.

Lemma mbm_sw_data : forall I fr n B2, DSpec.sf_cmd (mrx_f fr n) = 0 -> UMR.mr_sw I fr n B2 = UMR.mr_data fr n B2.
Proof.
intros I fr n B2 H. unfold UMR.mr_sw. cbv zeta. rewrite H.
change ((0 =? TC.SPEC_CMD_E0) || (0 =? TC.SPEC_CMD_E1)) with false. change (0 =? TC.SPEC_CMD_ACK) with false.
change (0 =? TC.SPEC_CMD_DATA) with true. cbv beta iota. reflexivity.
Qed.
Lemma mbm_sw_ack : forall I fr n B2, DSpec.sf_cmd (mrx_f fr n) = 160 -> UMR.mr_sw I fr n B2 = UMR.mr_ack fr n B2.
Proof.
intros I fr n B2 H. unfold UMR.mr_sw. cbv zeta. rewrite H.
change ((160 =? TC.SPEC_CMD_E0) || (160 =? TC.SPEC_CMD_E1)) with false. change (160 =? TC.SPEC_CMD_ACK) with true.
cbv beta iota. reflexivity.
Qed.
Lemma mbm_sw_e3 : forall I fr n B2, DSpec.sf_cmd (mrx_f fr n) = 227 -> UMR.mr_sw I fr n B2 = UMR.mr_e3 B2.
Proof.
intros I fr n B2 H. unfold UMR.mr_sw. cbv zeta. rewrite H.
change ((227 =? TC.SPEC_CMD_E0) || (227 =? TC.SPEC_CMD_E1)) with false. change (227 =? TC.SPEC_CMD_ACK) with false.
change (227 =? TC.SPEC_CMD_DATA) with false. change (227 =? TC.SPEC_CMD_E3) with true.
cbv beta iota. reflexivity.
Qed.
Lemma mbm_sw_ann : forall I fr n B2, DSpec.sf_cmd (mrx_f fr n) = 224 \/ DSpec.sf_cmd (mrx_f fr n) = 225 ->
  UMR.mr_sw I fr n B2 = UMR.mr_ann I fr n B2.
Proof.
intros I fr n B2 [H|H]; unfold UMR.mr_sw; cbv zeta; rewrite H.
- change ((224 =? TC.SPEC_CMD_E0) || (224 =? TC.SPEC_CMD_E1)) with true. cbv beta iota. reflexivity.
- change ((225 =? TC.SPEC_CMD_E0) || (225 =? TC.SPEC_CMD_E1)) with true. cbv beta iota. reflexivity.
Qed.
Lemma mbm_sw_none : forall I fr n B2, DSpec.sf_cmd (mrx_f fr n) <> 0 -> DSpec.sf_cmd (mrx_f fr n) <> 160 ->
  DSpec.sf_cmd (mrx_f fr n) <> 224 -> DSpec.sf_cmd (mrx_f fr n) <> 225 -> DSpec.sf_cmd (mrx_f fr n) <> 227 ->
  UMR.mr_sw I fr n B2 = Some (B2, tt).
Proof.
intros I fr n B2 H0 Ha He0 He1 He3. unfold UMR.mr_sw. cbv zeta.
unfold TC.SPEC_CMD_E0, TC.SPEC_CMD_E1, TC.SPEC_CMD_ACK, TC.SPEC_CMD_DATA, TC.SPEC_CMD_E3.
rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) He0),
  (proj2 (Z.eqb_neq _ _) He1), (proj2 (Z.eqb_neq _ _) He3).
cbn [orb]. reflexivity.
Qed.

Lemma mbm_ann_short : forall I fr n B2, DSpec.sf_body_len (mrx_f fr n) < TC.SPEC_ANN_MIN ->
  UMR.mr_ann I fr n B2 = Some (B2, tt).
Proof.
intros I fr n B2 H. unfold UMR.mr_ann. cbv zeta. rewrite (proj2 (Z.ltb_lt _ _) H). cbv beta iota. reflexivity.
Qed.
Lemma mbm_ann_e0 : forall I fr n B2, TC.SPEC_ANN_MIN <= DSpec.sf_body_len (mrx_f fr n) ->
  DSpec.sf_cmd (mrx_f fr n) = 224 -> UMR.mr_ann I fr n B2 = UMR.mr_ann2 I fr n (-1) B2.
Proof.
intros I fr n B2 H He. unfold UMR.mr_ann. cbv zeta. rewrite (proj2 (Z.ltb_ge _ _) H), He.
change (224 =? TC.SPEC_CMD_E1) with false. cbv beta iota. reflexivity.
Qed.

(* The reads of the world after M.last_rx. *)
Lemma mbm_B2 : forall B1, length B1 = Z.to_nat TW.W_LEN ->
  length (TW.set_M_last_rx B1 (TW.g_now B1)) = Z.to_nat TW.W_LEN /\
  TW.M_state (TW.set_M_last_rx B1 (TW.g_now B1)) = TW.M_state B1 /\
  TW.g_now (TW.set_M_last_rx B1 (TW.g_now B1)) = TW.g_now B1.
Proof.
intros B1 L. split; [|split]; UMR.mr_unf; [UMR.mr_wl L | UMR.mr_push L; reflexivity | UMR.mr_push L; reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* The world relation at the exits                                     *)
(* ------------------------------------------------------------------ *)

Lemma mb_tw_in_rng : forall x, tw_in TMAP_B x -> 0 <= x < 2 ^ 64.
Proof.
intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. lia.
Qed.

Ltac mb_unP HP := mrx_unP HP; try change (Z.of_nat 8) with 8 in *; try change (Z.of_nat 4) with 4 in *.

(* M.last_rx = g_now. *)
Lemma mb_w2 : forall rd0 rdF Bw, tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 8)%nat -> rdF (TB_M + 32 + Z.of_nat j) = Some (YO0f.le_byte (TW.g_now Bw) 8 j)) ->
  (forall x, tw_in TMAP_B x -> ~ mbX1 x -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_M_last_rx Bw (TW.g_now Bw)).
Proof.
intros rd0 rdF Bw H V1 Hk. unfold TW.set_M_last_rx.
pose proof (mrx_tw_start rdF rd0 Bw H) as H0.
pose proof (mrx_tw_step rdF rd0 _ Bw TW.OFF_M TB_M TW.SZ_M 32 TW.A_M_last_rx 8 (TW.g_now Bw) H0 TMAP_B_M
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_M; lia) V1) as H1.
apply (mrx_tw_end rdF rd0 _ _ H1). intros x Hx HP. mb_unP HP. apply Hk; [exact Hx | unfold mbX1; lia].
Qed.

(* and the inlined m_lost's stores of 0 at M.desk_counter_valid and M.fly.on. *)
Lemma mb_w3 : forall rd0 rdF Bw, tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 8)%nat -> rdF (TB_M + 32 + Z.of_nat j) = Some (YO0f.le_byte (TW.g_now Bw) 8 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 76 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ mbX2 x -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_M_fly_on (TW.set_M_desk_counter_valid (TW.set_M_last_rx Bw (TW.g_now Bw)) 0) 0).
Proof.
intros rd0 rdF Bw H V1 V2 V3 Hk. unfold TW.set_M_fly_on, TW.set_M_desk_counter_valid, TW.set_M_last_rx.
pose proof (mrx_tw_start rdF rd0 Bw H) as H0.
pose proof (mrx_tw_step rdF rd0 _ Bw TW.OFF_M TB_M TW.SZ_M 32 TW.A_M_last_rx 8 (TW.g_now Bw) H0 TMAP_B_M
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_M; lia) V1) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 76 TW.A_M_desk_counter_valid 4 0 H1 TMAP_B_M
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_M; lia) V2) as H2.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 96 TW.A_M_fly_on 4 0 H2 TMAP_B_M
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_M; lia) V3) as H3.
apply (mrx_tw_end rdF rd0 _ _ H3). intros x Hx HP. mb_unP HP.
apply Hk; [exact Hx | unfold mbX2, mbX1; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* Run tactics                                                         *)
(* ------------------------------------------------------------------ *)

Ltac mb_awr U9 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first
      [ lia
      | rewrite U9 in Ha; right; left; apply mb_inG; unfold TB_M in *; lia ] |]);
  apply awr_ok_x_nil.

(* What the walk keeps, from the cut's memory mem0 to a memory m: the view outside the windows X. *)
Definition mb_KA {fx : YK11.FPState} {rc : YM05.RunCeil} (Wc : world tfibsegs) (X : Z -> Prop)
    (mem0 m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview tfibsegs (w_H Wc) m a = aview tfibsegs (w_H Wc) mem0 a.

Lemma mb_KA_step {fx : YK11.FPState} {rc : YM05.RunCeil} : forall E rs (Wc : world tfibsegs) (X : Z -> Prop) mem0
    (m m' : word -> option byte),
  mb_KA Wc X mem0 m -> frame_of E rs (mrestrict (w_H Wc) m) (mrestrict (w_H Wc) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> X a) ->
  mb_KA Wc X mem0 m'.
Proof.
intros E rs Wc X mem0 m m' KA HFr Hw a Ha HX.
rewrite (YC4b.kept_of_frame E rs (w_H Wc) m m' X HFr Hw a Ha HX). exact (KA a Ha HX).
Qed.

Lemma mb_KA_mono {fx : YK11.FPState} {rc : YM05.RunCeil} : forall (Wc : world tfibsegs) (X X' : Z -> Prop) mem0 m,
  (forall a, X a -> X' a) -> mb_KA Wc X mem0 m -> mb_KA Wc X' mem0 m.
Proof. intros Wc X X' mem0 m HX KA a Ha HN. apply KA; [exact Ha | intros H; apply HN; exact (HX a H)]. Qed.

Ltac mb_win Usp U9 UNOW :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp, ?U9, ?UNOW in Hx;
     unfold mbX2, mbX1, mbX0;
     lia |]);
  destruct Hin.

(* After a run: the model generalized, the kept facts carried to the run's last memory. *)
Ltac mb_after KA X Usp U9 UNOW :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt;
    try clear m0 end;
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    let KA' := fresh "KAn" in
    pose proof (mb_KA_step _ _ _ X _ _ _ KA HFr) as KA';
    lazymatch type of KA' with ?P -> _ =>
      let Hw := fresh "Hw" in assert (Hw : P) by (mb_win Usp U9 UNOW); specialize (KA' Hw); clear Hw end;
    clear KA HFr; rename KA' into KA end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  lazymatch goal with HG : mem_grows _ _ |- _ => clear HG end.

(* A new region of the state: disjoint from the state's regions (their bases rewritten to numbers). *)
Ltac mb_disj Usp U9 UNOW :=
  cbn [ss_mem YP09.all_disjoint]; unfold mb_lrx, mb_dcv, mb_fly;
  repeat match goal with |- _ /\ _ => split end; try exact I;
  unfold YP09.extent_disjoint;
  try change (A_OBJ 28) with 269%nat;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?Usp, ?U9, ?UNOW;
  unfold TB_M, TB_g_now, MRX_FRAME in *;
  lia.
Ltac mb_add HS R Hok Usp U9 UNOW :=
  lazymatch type of HS with st_ok_pi ?sg0 ?vl0 ?Ex0 ?ss0 ?m0 =>
    let ss0' := eval vm_compute in ss0 in change (st_ok_pi sg0 vl0 Ex0 ss0' m0) in HS end;
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
    let HSa := fresh "HSa" in
    pose proof (st_ok_pi_add_region Ex ss m R HS eq_refl Hok ltac:(mb_disj Usp U9 UNOW)) as HSa;
    clear HS; rename HSa into HS;
    lazymatch type of HS with st_ok_pi ?sg2 ?vl2 ?Ex2 ?ss2 ?m2 =>
      let ss' := eval vm_compute in ss2 in change (st_ok_pi sg2 vl2 Ex2 ss' m2) in HS end end.
Ltac mb_add0 HS R L U Usp U9 UNOW :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ ?m => mb_add HS R (L Ex (ms_mem m) U) Usp U9 UNOW end.
Ltac mb_mono KA L :=
  let KA' := fresh "KAm" in pose proof (mb_KA_mono _ _ _ _ _ L KA) as KA'; clear KA; rename KA' into KA.
(* One run of the walk (to its stop, or to the pc stop), with the write rights and the kept view; the walk's
   hypotheses are found by their types. *)
Ltac mb_step X :=
  lazymatch goal with
  | RUN : context [sym_runN_pi_tok _ _ _ _ _ _ _ _], HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
    HJ : @W_journalG.ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, KA : mb_KA _ _ _ _,
    Usp : bv_unsigned (ew _ 2%nat) = _, U9 : bv_unsigned (ew _ 9%nat) = TB_M,
    UNOW : bv_unsigned (ew _ 269%nat) = TB_g_now |- _ =>
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan; [ mb_awr U9 | mb_after KA X Usp U9 UNOW ]
  end.
Ltac mb_stepto X stop :=
  lazymatch goal with
  | RUNTO : context [sym_run_toN_pi_tok _ _ _ _ _ _ _ _ _], HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
    HJ : @W_journalG.ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, KA : mb_KA _ _ _ _,
    Usp : bv_unsigned (ew _ 2%nat) = _, U9 : bv_unsigned (ew _ 9%nat) = TB_M,
    UNOW : bv_unsigned (ew _ 269%nat) = TB_g_now |- _ =>
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan stop; [ mb_awr U9 | mb_after KA X Usp U9 UNOW ]
  end.
Ltac mb_br :=
  lazymatch goal with
  | RUN : context [sym_runN_pi_tok _ _ _ _ _ _ _ _], BR : context [add_cond _ _], HS : st_ok_pi _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan
  end.
(* The value of register q in the machine state of the symbolic state HS: its symbolic value, computed, then the
   proof pf of its denotation (q, v and pf typed in place). *)
Tactic Notation "mb_reg" constr(HS) uconstr(q) uconstr(v) ident(H) uconstr(pf) :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) q) in
      assert (H : YK11.getr (ms_regs msx) q = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx q HS) _); change (sv_denot Ex e = v); exact pf)
  end.

(* The registers the run kept, by the symbolic state. *)
Tactic Notation "mb_rk" constr(HS) constr(E0) constr(regs2) constr(vals) constr(AGR) ident(RK) :=
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict ?Hh ?m) =>
    pose proof (regs_kept_of_st_ok_pi E0 ss (restrict Hh m) regs2 vals MB_KEEP HS AGR eq_refl) as RK;
    cbn [ms_regs restrict] in RK end.

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

Definition mb_E (regs : bvmap 5 word) (Bw : list byte) : env := Eimg (PI := PI_transportb) (Ereg regs (mb_vals fr n Bw)).

Lemma mb_vals_img : VAL (A_OBJ 28) = TB_g_now.
Proof. vm_compute. reflexivity. Qed.

Lemma mb_stk : 112 <= MRX_STK.
Proof. vm_compute. discriminate. Qed.

(* The entry state of the segment. *)
Lemma mb_entry : forall (Wc : world segs) regs2 mem2 Bw,
  tw_at TMAP_B (aview segs (w_H Wc) mem2) Bw ->
  YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME) -> YK11.getr regs2 9 = w64 TB_M ->
  YK11.getr regs2 18 = w64 SHADOW_OFF ->
  mrx_ok fr n -> mrx_sf Wc mem2 sp1 fr n ->
  st_ok_pi segs VAL (mb_E regs2 Bw) ss_mb
    (restrict (w_H Wc) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + (AF_m_rx + OFF_BODY))) mem2 (YK11.seg_rom segs))).
Proof.
  intros Wc regs2 mem2 Bw Htw R2 R9 R18 HOK HSF.
  pose proof HST as (Hsp0 & Hsp16 & Hceil & H46 & H47 & _).
  pose proof mb_stk as HSTK.
  pose proof mb_vals_img as V28.
  destruct (mrx_ok_fields fr n HOK) as (_ & _ & _ & _ & Fbl0 & Fbln & Fcmd & _).
  pose proof HST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfa0 & _ & Hfam & _).
  pose proof HOK as (Hn & _).
  set (E := mb_E regs2 Bw).
  assert (EOB : ew E (A_OBJ 28) = Z_to_bv 64 (VAL (A_OBJ 28)))
    by (unfold E, mb_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (EE : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E k = YK11.getr regs2 q)
    by (intros k q Hk; unfold E, mb_E; apply ew_Eimg_Ereg_nat; exact Hk).
  assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (mb_vals fr n Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, mb_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  cbn [Nat.add nth mb_vals] in E32, E33, E34, E35.
  assert (Usp : base_val E (Some 2%nat) = sp1 - MRX_FRAME).
  { cbn [base_val]. rewrite (EE 2%nat 2%bv eq_refl), R2. apply unsigned_lit_small. unfold MRX_FRAME. lia. }
  assert (U9 : base_val E (Some 9%nat) = TB_M).
  { cbn [base_val]. rewrite (EE 9%nat 9%bv eq_refl), R9. apply unsigned_lit_small. unfold TB_M. lia. }
  assert (U28 : base_val E (Some (A_OBJ 28)) = TB_g_now).
  { cbn [base_val]. rewrite EOB, V28. apply unsigned_lit_small. unfold TB_g_now. lia. }
  assert (DEN : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff k 0) = Z_to_bv 64 v)
    by (intros k v Hk Hv; cbn [sv_denot]; rewrite Hk, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  pose proof (TWL.u_at_range Bw TW.A_M_state 4) as R32. pose proof (TWL.u_at_range Bw TW.OFF_g_now 8) as R33.
  change (8 * Z.of_nat 4) with 32 in R32. change (8 * Z.of_nat 8) with 64 in R33.
  assert (Rbl : 0 <= DSpec.sf_body_len (mrx_f fr n) < 2 ^ 64) by lia.
  unfold mrx_sf in HSF.
  rewrite restrict_mkst_fx. unfold ss_mb.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold mb_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold mb_sp, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite Usp. unfold MRX_FRAME in *.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val segs E _ (sp1 - 112) 40 1 (SOff 34 0) (DSpec.sf_cmd (mrx_f fr n)));
          [apply DEN; [exact E34 | lia] | cbn; lia | lia |].
        exact (mrx_sf_cmd _ (sp1 - 112) (TI.tf_addr fr) (mrx_f fr n) HSF).
      * apply (chunk_ok_val segs E _ (sp1 - 112) 56 8 (SOff 35 0) (DSpec.sf_body_len (mrx_f fr n)));
          [apply DEN; [exact E35 | exact Rbl] | cbn; lia | lia |].
        exact (mrx_sf_blen _ (sp1 - 112) (TI.tf_addr fr) (mrx_f fr n) HSF).
    + unfold mb_st, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite U9. split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ TB_M 12 4 (SOff 32 0) (TW.u_at Bw TW.A_M_state 4));
        [apply DEN; [exact E32 | lia] | exact R32 | lia |].
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 12 4 TMAP_B_ok Htw TMAP_B_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold mb_now, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite U28. split; [unfold TB_g_now; lia|]. split; [unfold TB_g_now; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ TB_g_now 0 8 (SOff 33 0) (TW.g_now Bw));
        [apply DEN; [exact E33 | exact R33] | exact R33 | lia |].
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_now TB_g_now TW.SZ_g_now 0 8 TMAP_B_ok Htw TMAP_B_g_now
        ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)).
  - unfold mb_regions, mb_sp, mb_st, mb_now.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite Usp, U9, U28.
    unfold TB_M, TB_g_now, MRX_FRAME in *. repeat split; lia.
  - unfold mb_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EE 2%nat 2%bv eq_refl), (EE 9%nat 9%bv eq_refl), (EE 18%nat 18%bv eq_refl),
      R2, R9, R18, E34.
    unfold w64.
    rewrite (unsigned_lit_small (sp1 - MRX_FRAME)) by (unfold MRX_FRAME; lia).
    rewrite (unsigned_lit_small TB_M) by (unfold TB_M; lia).
    rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    rewrite (unsigned_lit_small (DSpec.sf_cmd (mrx_f fr n))) by lia.
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold MRX_FRAME.
    repeat match goal with |- _ /\ _ => split end; try exact I;
      first [lia | unfold TB_M; reflexivity | reflexivity
            | rewrite Zminus_mod, Hsp16; reflexivity].
Qed.

(* An exit: the cut pc with its facts R, from the run's last state. *)
Lemma mb_exit : forall (Wc : world segs) ly2 S2 pc pc' R regsF memF mdF Bn,
  pc' = pc -> K pc R ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc
    memF mdF 0 ->
  frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> mo_le MT Sc S2 0 ->
  YK11.getr regsF 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK11.getr regsF 3 = YK11.getr regs0 3 -> YK11.getr regsF 4 = YK11.getr regs0 4 ->
  mrx_hi regs0 regsF ->
  mrx_saved Wc memF sp1 regs0 ->
  tw_at TMAP_B (aview segs (w_H Wc) memF) Bn ->
  R Wc Bn ly2 S2 regsF memF ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 pc') memF (YK11.seg_rom segs)) mdF)
    (@mrx_ipost fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r).
Proof.
intros Wc ly2 S2 pc pc' R regsF memF mdF Bn -> HK HJ HF HP HM H2 H3 H4 HH HSv HT HR.
apply (HK Wc Bn). eapply mrx_at_intro;
  [exact HJ | exact HF | exact HP | exact HM | exact H2 | exact H3 | exact H4 | exact HH | exact HSv | exact HT
  | exact HR].
Qed.

Lemma mb_hi : forall regs2 regsF, mrx_hi regs0 regs2 ->
  (forall q, In q MB_KEEP -> YK11.getr regsF q = YK11.getr regs2 q) -> mrx_hi regs0 regsF.
Proof. intros regs2 regsF H RK q Hq. rewrite <- (H q Hq). exact (RK _ (mb_hi_in q Hq)). Qed.

Lemma mb_X02 : forall a, mbX0 a -> mbX2 a. Proof. intros a []. Qed.
Lemma mb_X01 : forall a, mbX0 a -> mbX1 a. Proof. intros a []. Qed.
Lemma mb_X12 : forall a, mbX1 a -> mbX2 a. Proof. intros a H. left. exact H. Qed.

(* Every window byte is a byte the call may store (mrx_wr), in M. *)
Lemma mb_X2_wr : forall a, mbX2 a -> mrx_wr a /\ TB_M <= a < TB_M + 100.
Proof.
intros a H. split; [| unfold mbX2, mbX1 in H; lia].
unfold mbX2, mbX1 in H. unfold mrx_wr, twb_fld.
destruct H as [H|[H|H]].
- do 5 right; left. unfold TW.A_M_last_rx, TW.OFF_M. lia.
- do 9 right; left. unfold TW.A_M_desk_counter_valid, TW.OFF_M. lia.
- do 12 right; left. unfold TW.A_M_fly_on, TW.OFF_M. lia.
Qed.

Lemma mb_agree : forall regs Bw, env_agree 32 (Ereg regs (mb_vals fr n Bw)) (mb_E regs Bw).
Proof. intros regs Bw. split; [intros k Hk; unfold mb_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* A writable window of M (based on s1), lo .. hi inside M's payload. *)
Lemma mb_wok : forall E m lo hi, bv_unsigned (ew E 9%nat) = TB_M -> 0 <= lo -> hi <= 1648 ->
  region_ok segs E m (YP09.mkRegion (Some 9%nat) lo hi lo hi []).
Proof.
intros E m lo hi H Hlo Hhi. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H. split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw). apply mb_inG. lia.
Qed.
Lemma mb_lrx_ok : forall E m, bv_unsigned (ew E 9%nat) = TB_M -> region_ok segs E m mb_lrx.
Proof. intros E m H. exact (mb_wok E m 32 40 H ltac:(lia) ltac:(lia)). Qed.
Lemma mb_dcv_ok : forall E m, bv_unsigned (ew E 9%nat) = TB_M -> region_ok segs E m mb_dcv.
Proof. intros E m H. exact (mb_wok E m 76 80 H ltac:(lia) ltac:(lia)). Qed.
Lemma mb_fly_ok : forall E m, bv_unsigned (ew E 9%nat) = TB_M -> region_ok segs E m mb_fly.
Proof. intros E m H. exact (mb_wok E m 96 100 H ltac:(lia) ltac:(lia)). Qed.

(* What the cut's facts keep across runs that write only the windows. *)
Lemma mb_saved_kept : forall (Wc : world segs) mem2 m, mb_KA Wc mbX2 mem2 m ->
  mrx_saved Wc mem2 sp1 regs0 -> mrx_saved Wc m sp1 regs0.
Proof.
intros Wc mem2 m KA HSv. pose proof HST as (_ & _ & _ & H46 & H47 & _). pose proof mb_stk as HSTK.
apply (mrx_saved_kept Wc Wc mem2 m sp1 regs0 HSv). intros a Ha.
apply KA; [lia | intros HX; pose proof (proj2 (mb_X2_wr a HX)); unfold TB_M in *; lia].
Qed.

Lemma mb_sf_kept : forall (Wc : world segs) mem2 m, mb_KA Wc mbX2 mem2 m ->
  mrx_sf Wc mem2 sp1 fr n -> mrx_sf Wc m sp1 fr n.
Proof.
intros Wc mem2 m KA HSF. pose proof HST as (_ & _ & _ & H46 & H47 & _). pose proof mb_stk as HSTK.
apply (mrx_sf_kept Wc Wc mem2 m sp1 fr n HSF). intros a Ha. unfold MRX_FRAME in Ha.
apply KA; [lia | intros HX; pose proof (proj2 (mb_X2_wr a HX)); unfold TB_M in *; lia].
Qed.

Lemma mb_frs_kept : forall (Wc : world segs) ly2 S2 mem2 m, mb_KA Wc mbX2 mem2 m ->
  mrx_frs B fr ly2 S2 Wc mem2 -> mrx_frs B fr ly2 S2 Wc m.
Proof.
intros Wc ly2 S2 mem2 m KA HF.
pose proof HST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfa0 & _ & Hfam & _ & _ & Hapart & _).
eapply mrx_frs_wr; [exact HF | exact Hapart | lia | exact Hfam |].
intros a Ha HN. apply KA; [exact Ha | intros HX; exact (HN (proj1 (mb_X2_wr a HX)))].
Qed.

Lemma mb_cur : forall (Wc : world segs) ly2 S2 mem2 m, mb_KA Wc mbX2 mem2 m ->
  mrx_cur B fr n sp1 ly2 S2 Wc mem2 -> mrx_cur B fr n sp1 ly2 S2 Wc m.
Proof.
intros Wc ly2 S2 mem2 m KA (H1 & H2 & H3).
split; [exact H1|]. split; [exact (mb_frs_kept _ _ _ _ _ KA H2) | exact (mb_sf_kept _ _ _ KA H3)].
Qed.

(* The bytes of chunk c of region i of the run's last state. *)
Lemma mb_chunk : forall E (Wc : world segs) ss ms i rg c off w e v base,
  st_ok_pi segs VAL E ss (restrict (w_H Wc) ms) -> nth_error (ss_mem ss) i = Some rg ->
  base_val E (YP09.r_base rg) = base -> nth_error (YP09.r_chunks rg) c = Some (YP09.mkChunk off (YP09.CVal w e)) ->
  sv_denot E e = Z_to_bv 64 v -> (N.to_nat w <= 8)%nat ->
  forall j, (j < N.to_nat w)%nat ->
  aview segs (w_H Wc) (ms_mem ms) (base + off + Z.of_nat j) = Some (YO0f.le_byte v (N.to_nat w) j).
Proof.
intros E Wc ss ms i rg c off w e v base HS Hi Hb Hc He Hw j Hj.
pose proof (st_ok_pi_region_nth E ss (restrict (w_H Wc) ms) i rg HS Hi) as RG.
cbn [ms_mem restrict] in RG.
destruct RG as (_ & _ & _ & HC). rewrite Hb in HC. rewrite Forall_forall in HC.
pose proof (HC _ (nth_error_In _ _ Hc)) as HC1.
eapply mrx_chunk_rd; [exact HC1 | exact He | exact Hw | exact Hj].
Qed.

(* The close of an exit at the world after M.last_rx (KA over mbX1, M.last_rx the state's region 0): every fact of
   the cut but R; KA4 names the kept view over mbX2. *)
Ltac mb_fin1 RK pc R KK Bn Wc ly2 S2 mem2 B1 Htw KA U9 D33 HJ Hfrm Hperm Hmo Hsp Hgp Htp Hhi Hsav regs2 E0 :=
  let VL := fresh "VL" in
  pose proof (mb_KA_mono _ _ _ _ _ mb_X12 KA) as KA4;
  lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?m) |- _ =>
    pose proof (mb_chunk E0 Wc ss m 0%nat _ 0%nat 32 8%N (SOff 33 0) (TW.g_now B1) TB_M HS eq_refl U9 eq_refl
      D33 ltac:(cbn; lia)) as VL;
    apply (mb_exit Wc ly2 S2 (MRX_PC pc) _ R (ms_regs m) (ms_mem m) _ Bn);
    [ rewrite (mrx_pcv pc); reflexivity | exact KK | exact HJ | exact Hfrm | exact Hperm | exact Hmo
    | exact (eq_trans (RK (Z_to_bv 5 2) ltac:(mb_in)) Hsp)
    | exact (eq_trans (RK (Z_to_bv 5 3) ltac:(mb_in)) Hgp)
    | exact (eq_trans (RK (Z_to_bv 5 4) ltac:(mb_in)) Htp)
    | exact (mb_hi regs2 _ Hhi RK)
    | exact (mb_saved_kept Wc mem2 _ KA4 Hsav)
    | exact (mb_w2 (aview segs (w_H Wc) mem2) _ B1 Htw VL (fun x Hx HN => KA x (mb_tw_in_rng x Hx) HN))
    | ]
  end.

(* The BODY segment. *)
Lemma mrx_seg_body :
  K (MRX_PC OFF_EPI) (R_EPI Bw' r) -> K (MRX_PC OFF_TICK) (R_TICK Bw' r) ->
  K (MRX_PC OFF_SET) (R_SET Bw' r) -> K (MRX_PC OFF_DATA) (R_DATA B fr n sp1 Bw' r) ->
  K (MRX_PC OFF_HOST) (R_HOST B fr n sp1 Bw' r) -> K (MRX_PC OFF_ANNT) (R_ANNT B fr n sp1 Bw' r) ->
  K (MRX_PC OFF_ACK) (R_ACK B fr n sp1 Bw' r) -> K (MRX_PC OFF_BODY) (R_BODY B fr n sp1 Bw' r).
Proof using All.
intros KEPI KTICK KSET KDATA KHOST KANNT KACK.
unfold mrx_K. intros Wc B1 c Hat.
unfold mrx_at in Hat.
destruct Hat as (ly2 & S2 & regs2 & mem2 & md2 & Hc0 & HJ & Hfrm & Hperm & Hmo & Hsp & Hgp & Htp & Hhi & Hsav & Htw
  & HR).
subst c.
unfold R_BODY in HR.
destruct HR as (HCUR & R9 & R18 & HMK).
pose proof HCUR as (HOK & HFRS & HSF).
pose proof HST as (Hsp0 & Hsp16 & Hceil & H46 & H47 & Hra & Hra4 & Hgp0 & Htp0 & Ha0 & Ha1 & Hfa0 & Hfan & Hfam
  & Hsrc & Hwinfr & Hapart & Hnev & HAR).
pose proof mb_stk as HSTK.
pose proof HOK as (Hn & Hcode).
destruct (mrx_ok_fields fr n HOK) as (Fdst & Fsrc & Fbody & F30 & Fbl0 & Fbln & Fcmd & Fret & Fsnd & Fack).
assert (Hbl64 : 0 <= DSpec.sf_body_len (mrx_f fr n) < 2 ^ 64) by lia.
assert (LB1 : length B1 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw).
destruct (mbm_B2 B1 LB1) as (LB2 & BS & BN).
pose proof (TWL.s32_range B1 TW.A_M_state) as RS. change (TW.s32_at B1 TW.A_M_state) with (TW.M_state B1) in RS.
pose proof (TWL.u_at_range B1 TW.A_M_state 4) as R32. pose proof (TWL.u_at_range B1 TW.OFF_g_now 8) as R33.
change (8 * Z.of_nat 4) with 32 in R32. change (8 * Z.of_nat 8) with 64 in R33.
pose proof mb_vals_img as V28.
set (E0 := mb_E regs2 B1).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, mb_E; apply Eimg_env).
assert (EE : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E0 k = YK11.getr regs2 q)
  by (intros k q Hk; unfold E0, mb_E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E0 2%nat) = sp1 - MRX_FRAME).
{ rewrite (EE 2%nat 2%bv eq_refl), Hsp. apply unsigned_lit_small. unfold MRX_FRAME. lia. }
assert (U9 : bv_unsigned (ew E0 9%nat) = TB_M).
{ rewrite (EE 9%nat 9%bv eq_refl), R9. apply unsigned_lit_small. unfold TB_M. lia. }
assert (UNOW : bv_unsigned (ew E0 269%nat) = TB_g_now).
{ unfold E0, mb_E. rewrite (Eimg_img _ 269%nat) by (unfold A_TEXT, A_LIM; lia).
  change 269%nat with (A_OBJ 28). rewrite V28. apply unsigned_lit_small. unfold TB_g_now. lia. }
pose proof (mb_entry Wc regs2 mem2 B1 Htw Hsp R9 R18 HOK HSF) as HS.
fold E0 in HS.
assert (SHOK : sh_ok segs MB_Bx MB_SH E0 (mrestrict (w_H Wc) mem2)) by (unfold sh_ok, MB_SH; apply Forall_nil).
assert (KA : mb_KA Wc mbX0 mem2 mem2) by (intros a _ _; reflexivity).
assert (EX : forall j, (j < 4)%nat -> ew E0 (32 + j) = nth j (mb_vals fr n B1) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, mb_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth mb_vals] in E32, E33, E34, E35.
clear EX.
(* the values the code forms *)
assert (D32 : sv_denot E0 (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.M_state B1))
  by exact (AB.mbd_sext E0 32 _ E32 R32).
assert (D33 : sv_denot E0 (SOff 33 0) = Z_to_bv 64 (TW.g_now B1))
  by (rewrite (AB.mbd_off E0 33 _ 0 E33 R33), Z.add_0_r; reflexivity).
assert (D34 : sv_denot E0 (SOff 34 0) = Z_to_bv 64 (DSpec.sf_cmd (mrx_f fr n)))
  by (rewrite (AB.mbd_off E0 34 _ 0 E34 ltac:(lia)), Z.add_0_r; reflexivity).
assert (D34m : sv_denot E0 (SOff 34 (-224)) = Z_to_bv 64 (DSpec.sf_cmd (mrx_f fr n) + -224))
  by exact (AB.mbd_off E0 34 _ (-224) E34 ltac:(lia)).
assert (D35 : sv_denot E0 (SOff 35 0) = Z_to_bv 64 (DSpec.sf_body_len (mrx_f fr n)))
  by (rewrite (AB.mbd_off E0 35 _ 0 E35 Hbl64), Z.add_0_r; reflexivity).
assert (DST : sv_denot E0 (SAluw ALU_ADD (SExt true 32 (SOff 32 0)) (SLit (-1))) =
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (TW.M_state B1)) + -1)))
  by exact (mbd_state12 E0 32 _ E32 R32).
pose proof (@paj_run_x fx rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
rewrite (mrx_pcv OFF_BODY).
(* +0x100 - +0x108: a0 = M.state, `beq a0, 3` *)
mb_step mbX0.
mb_br.
{ (* S_CLOSED: +0x02c, a0 = 0, the epilogue *)
  rewrite D32 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_eq in Hc by lia. apply Z.eqb_eq in Hc.
  destruct (mbm_closed timg_B fr n B1 Bw' r Hc HMK) as [HBw Hr0].
  mb_stepto mbX0 (AF_m_rx + OFF_EPI).
  pmkst HS.
  mb_rk HS E0 regs2 (mb_vals fr n B1) (mb_agree regs2 B1) RK.
  mb_reg HS 10%bv (w64 0) RX10 ltac:(reflexivity).
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
    apply (mb_exit Wc ly2 S2 (MRX_PC OFF_EPI) _ (R_EPI Bw' r) (ms_regs m) (ms_mem m) _ B1) end.
  - rewrite (mrx_pcv OFF_EPI). reflexivity.
  - exact KEPI.
  - exact HJ.
  - exact Hfrm.
  - exact Hperm.
  - exact Hmo.
  - exact (eq_trans (RK (Z_to_bv 5 2) ltac:(mb_in)) Hsp).
  - exact (eq_trans (RK (Z_to_bv 5 3) ltac:(mb_in)) Hgp).
  - exact (eq_trans (RK (Z_to_bv 5 4) ltac:(mb_in)) Htp).
  - exact (mb_hi regs2 _ Hhi RK).
  - exact (mb_saved_kept Wc mem2 _ (mb_KA_mono _ _ _ _ _ mb_X02 KA) Hsav).
  - apply (tw_kept TMAP_B (aview segs (w_H Wc) mem2) _ B1 Htw). intros x Hx.
    exact (KA x (mb_tw_in_rng x Hx) (fun H => H)).
  - unfold R_EPI. split; [exact (eq_sym HBw) | rewrite Hr0; exact RX10]. }
rewrite D32 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_eq in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into HNC.
destruct (mbm_open timg_B fr n B1 Bw' r HNC HMK) as (B3 & SW & TK & Er).
set (B2 := TW.set_M_last_rx B1 (TW.g_now B1)) in *.
(* M.last_rx joins the state *)
mb_mono KA mb_X01.
mb_add0 HS mb_lrx mb_lrx_ok U9 Usp U9 UNOW.
(* +0x108 - +0x120: a1 = g_now, a2 = cmd, M.last_rx = g_now, `bge 0xdf, cmd` *)
mb_step mbX1.
mb_br.
{ (* cmd <= 0xdf *)
  rewrite D34 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_ge in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc.
  rename Hc into HcL.
  (* +0x154: `beqz cmd` *)
  mb_step mbX1.
  mb_br.
  { (* cmd 0: DATA *)
    rewrite D34 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_eq in Hc by lia. apply Z.eqb_eq in Hc. rename Hc into Hc0.
    rewrite (mbm_sw_data timg_B fr n B2 Hc0) in SW.
    mb_stepto mbX1 (AF_m_rx + OFF_DATA).
    pmkst HS.
    mb_rk HS E0 regs2 (mb_vals fr n B1) (mb_agree regs2 B1) RK.
    mb_reg HS 11%bv (w64 (TW.g_now B1)) RX11 ltac:(exact D33).
    mb_fin1 RK OFF_DATA (R_DATA B fr n sp1 Bw' r) KDATA B2 Wc ly2 S2 mem2 B1 Htw KA U9 D33 HJ Hfrm Hperm Hmo Hsp Hgp
      Htp Hhi Hsav regs2 E0.
    unfold R_DATA. split; [exact (mb_cur Wc ly2 S2 mem2 _ KA4 HCUR)|]. split; [exact Hc0|].
    split; [rewrite BN; exact RX11|]. split; [exact (eq_trans (RK (Z_to_bv 5 9) ltac:(mb_in)) R9)|].
    split; [exact (eq_trans (RK (Z_to_bv 5 18) ltac:(mb_in)) R18)|].
    exists B3. split; [exact SW|]. split; [exact TK | exact Er]. }
  rewrite D34 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_eq in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Hn0.
  (* +0x158 - +0x15c: `bne cmd, 0xa0` *)
  mb_step mbX1.
  mb_br.
  { (* cmd other: TICK *)
    rewrite D34 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_ne in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
    rename Hc into Hna.
    rewrite (mbm_sw_none timg_B fr n B2 Hn0 Hna ltac:(lia) ltac:(lia) ltac:(lia)) in SW.
    destruct (mrx_some_inv _ _ _ _ _ _ SW) as [EB _]. subst B3.
    mb_stepto mbX1 (AF_m_rx + OFF_TICK).
    pmkst HS.
    mb_rk HS E0 regs2 (mb_vals fr n B1) (mb_agree regs2 B1) RK.
    mb_fin1 RK OFF_TICK (R_TICK Bw' r) KTICK B2 Wc ly2 S2 mem2 B1 Htw KA U9 D33 HJ Hfrm Hperm Hmo Hsp Hgp
      Htp Hhi Hsav regs2 E0.
    unfold R_TICK. split; [exact TK | exact Er]. }
  rewrite D34 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_ne in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
  rename Hc into Hca.
  (* cmd ACK *)
  rewrite (mbm_sw_ack timg_B fr n B2 Hca) in SW.
  mb_stepto mbX1 (AF_m_rx + OFF_ACK).
  pmkst HS.
  mb_rk HS E0 regs2 (mb_vals fr n B1) (mb_agree regs2 B1) RK.
  mb_reg HS 10%bv (w64 (TW.M_state B1)) RX10 ltac:(exact D32).
  mb_fin1 RK OFF_ACK (R_ACK B fr n sp1 Bw' r) KACK B2 Wc ly2 S2 mem2 B1 Htw KA U9 D33 HJ Hfrm Hperm Hmo Hsp Hgp
    Htp Hhi Hsav regs2 E0.
  unfold R_ACK. split; [exact (mb_cur Wc ly2 S2 mem2 _ KA4 HCUR)|]. split; [exact Hca|].
  split; [rewrite BS; exact RX10|]. split; [exact (eq_trans (RK (Z_to_bv 5 9) ltac:(mb_in)) R9)|].
  exists B3. split; [exact SW|]. split; [exact TK | exact Er]. }
(* cmd > 0xdf: +0x124 - +0x12c, `bgeu cmd - 0xe0, 2` *)
rewrite D34 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_ge in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc.
rename Hc into HcH.
mb_step mbX1.
mb_br.
{ (* not e0 / e1: +0x1ac - +0x1b0, `bne cmd, 0xe3` *)
  rewrite D34m in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_geu_ann in Hc by lia.
  apply negb_true_iff, orb_false_iff in Hc. destruct Hc as [He0 He1]. apply Z.eqb_neq in He0, He1.
  mb_step mbX1.
  mb_br.
  { (* cmd other: TICK *)
    rewrite D34 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_ne in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
    rename Hc into He3.
    rewrite (mbm_sw_none timg_B fr n B2 ltac:(lia) ltac:(lia) He0 He1 He3) in SW.
    destruct (mrx_some_inv _ _ _ _ _ _ SW) as [EB _]. subst B3.
    mb_stepto mbX1 (AF_m_rx + OFF_TICK).
    pmkst HS.
    mb_rk HS E0 regs2 (mb_vals fr n B1) (mb_agree regs2 B1) RK.
    mb_fin1 RK OFF_TICK (R_TICK Bw' r) KTICK B2 Wc ly2 S2 mem2 B1 Htw KA U9 D33 HJ Hfrm Hperm Hmo Hsp Hgp
      Htp Hhi Hsav regs2 E0.
    unfold R_TICK. split; [exact TK | exact Er]. }
  rewrite D34 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_ne in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
  rename Hc into He3.
  rewrite (mbm_sw_e3 timg_B fr n B2 He3) in SW. unfold UMR.mr_e3 in SW. rewrite BS in SW.
  unfold TC.S_ONLINE, TC.S_WAKING in SW.
  (* cmd e3: +0x1b4 - +0x1bc, `bltu 1, M.state - 1` *)
  mb_step mbX1.
  mb_br.
  { (* M.state not S_ONLINE / S_WAKING: TICK *)
    rewrite DST in Hc. cbn [sv_denot] in Hc. cbn [branch_taken] in Hc. rewrite EPI.mrx_state12 in Hc by exact RS.
    apply negb_true_iff in Hc. rename Hc into Hst.
    rewrite Hst in SW. cbv beta iota in SW.
    destruct (mrx_some_inv _ _ _ _ _ _ SW) as [EB _]. subst B3.
    mb_stepto mbX1 (AF_m_rx + OFF_TICK).
    pmkst HS.
    mb_rk HS E0 regs2 (mb_vals fr n B1) (mb_agree regs2 B1) RK.
    mb_fin1 RK OFF_TICK (R_TICK Bw' r) KTICK B2 Wc ly2 S2 mem2 B1 Htw KA U9 D33 HJ Hfrm Hperm Hmo Hsp Hgp
      Htp Hhi Hsav regs2 E0.
    unfold R_TICK. split; [exact TK | exact Er]. }
  rewrite DST in Hc. cbn [sv_denot] in Hc. cbn [branch_taken] in Hc. rewrite EPI.mrx_state12 in Hc by exact RS.
  apply negb_false_iff in Hc. rename Hc into Hst.
  rewrite Hst in SW. cbv beta iota in SW. unfold TC.m_lost_m in SW.
  (* the inlined m_lost: M.desk_counter_valid and M.fly.on join the state *)
  mb_mono KA mb_X12.
  mb_add0 HS mb_dcv mb_dcv_ok U9 Usp U9 UNOW.
  mb_add0 HS mb_fly mb_fly_ok U9 Usp U9 UNOW.
  (* +0x1c0 - +0x1c8: the two stores of 0, a1 = 7 *)
  mb_stepto mbX2 (AF_m_rx + OFF_SET).
  pmkst HS.
  mb_rk HS E0 regs2 (mb_vals fr n B1) (mb_agree regs2 B1) RK.
  mb_reg HS 11%bv (w64 7) RX11 ltac:(reflexivity).
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
    pose proof (mb_chunk E0 Wc ss m 2%nat _ 0%nat 32 8%N (SOff 33 0) (TW.g_now B1) TB_M HS eq_refl U9 eq_refl
      D33 ltac:(cbn; lia)) as VL;
    pose proof (mb_chunk E0 Wc ss m 1%nat _ 0%nat 76 4%N (SLit 0) 0 TB_M HS eq_refl U9 eq_refl eq_refl
      ltac:(cbn; lia)) as VD;
    pose proof (mb_chunk E0 Wc ss m 0%nat _ 0%nat 96 4%N (SLit 0) 0 TB_M HS eq_refl U9 eq_refl eq_refl
      ltac:(cbn; lia)) as VF;
    apply (mb_exit Wc ly2 S2 (MRX_PC OFF_SET) _ (R_SET Bw' r) (ms_regs m) (ms_mem m) _
      (TW.set_M_desk_counter_valid (TW.set_M_fly_on B2 0) 0)) end.
  - rewrite (mrx_pcv OFF_SET). reflexivity.
  - exact KSET.
  - exact HJ.
  - exact Hfrm.
  - exact Hperm.
  - exact Hmo.
  - exact (eq_trans (RK (Z_to_bv 5 2) ltac:(mb_in)) Hsp).
  - exact (eq_trans (RK (Z_to_bv 5 3) ltac:(mb_in)) Hgp).
  - exact (eq_trans (RK (Z_to_bv 5 4) ltac:(mb_in)) Htp).
  - exact (mb_hi regs2 _ Hhi RK).
  - exact (mb_saved_kept Wc mem2 _ KA Hsav).
  - rewrite <- (UMR.mr_dcv_fly B2 LB2).
    exact (mb_w3 (aview segs (w_H Wc) mem2) _ B1 Htw VL VD VF (fun x Hx HN => KA x (mb_tw_in_rng x Hx) HN)).
  - unfold R_SET. exists 7, B3. split; [exact RX11|]. split; [lia|]. split; [exact SW|]. split; [exact TK | exact Er]. }
(* e0 / e1: +0x130 - +0x138, `bltu body_len, 33` *)
rewrite D34m in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_geu_ann in Hc by lia. apply negb_false_iff in Hc.
assert (Hce : DSpec.sf_cmd (mrx_f fr n) = 224 \/ DSpec.sf_cmd (mrx_f fr n) = 225)
  by (apply orb_true_iff in Hc; destruct Hc as [H|H]; apply Z.eqb_eq in H; [left|right]; exact H).
clear Hc.
rewrite (mbm_sw_ann timg_B fr n B2 Hce) in SW.
mb_step mbX1.
mb_br.
{ (* body_len < 33: TICK *)
  rewrite D35 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_ltu in Hc by lia. apply Z.ltb_lt in Hc. rename Hc into Hbl.
  rewrite (mbm_ann_short timg_B fr n B2 ltac:(unfold TC.SPEC_ANN_MIN; lia)) in SW.
  destruct (mrx_some_inv _ _ _ _ _ _ SW) as [EB _]. subst B3.
  mb_stepto mbX1 (AF_m_rx + OFF_TICK).
  pmkst HS.
  mb_rk HS E0 regs2 (mb_vals fr n B1) (mb_agree regs2 B1) RK.
  mb_fin1 RK OFF_TICK (R_TICK Bw' r) KTICK B2 Wc ly2 S2 mem2 B1 Htw KA U9 D33 HJ Hfrm Hperm Hmo Hsp Hgp
    Htp Hhi Hsav regs2 E0.
  unfold R_TICK. split; [exact TK | exact Er]. }
rewrite D35 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_ltu in Hc by lia. apply Z.ltb_ge in Hc. rename Hc into Hbl.
(* +0x13c - +0x140: `bne cmd, 0xe1` *)
mb_step mbX1.
mb_br.
{ (* cmd e0: +0x310, s0 = -1, ANNT *)
  rewrite D34 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_ne in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
  assert (He0 : DSpec.sf_cmd (mrx_f fr n) = 224) by (destruct Hce as [H|H]; [exact H | exfalso; exact (Hc H)]).
  clear Hc.
  rewrite (mbm_ann_e0 timg_B fr n B2 ltac:(unfold TC.SPEC_ANN_MIN; lia) He0) in SW.
  mb_stepto mbX1 (AF_m_rx + OFF_ANNT).
  pmkst HS.
  mb_rk HS E0 regs2 (mb_vals fr n B1) (mb_agree regs2 B1) RK.
  mb_reg HS 8%bv (w64 (-1)) RX8 ltac:(cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity).
  mb_fin1 RK OFF_ANNT (R_ANNT B fr n sp1 Bw' r) KANNT B2 Wc ly2 S2 mem2 B1 Htw KA U9 D33 HJ Hfrm Hperm Hmo Hsp Hgp
    Htp Hhi Hsav regs2 E0.
  unfold R_ANNT. exists (-1).
  split; [exact (mb_cur Wc ly2 S2 mem2 _ KA4 HCUR)|]. split; [left; exact He0|].
  split; [unfold TC.SPEC_ANN_MIN; lia|]. split; [lia|]. split; [intros _; reflexivity|].
  split; [exact RX8|]. split; [exact (eq_trans (RK (Z_to_bv 5 9) ltac:(mb_in)) R9)|].
  exists B3. split; [exact SW|]. split; [exact TK | exact Er]. }
(* cmd e1: HOST *)
rewrite D34 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_ne in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
rename Hc into He1.
mb_stepto mbX1 (AF_m_rx + OFF_HOST).
pmkst HS.
mb_rk HS E0 regs2 (mb_vals fr n B1) (mb_agree regs2 B1) RK.
mb_fin1 RK OFF_HOST (R_HOST B fr n sp1 Bw' r) KHOST B2 Wc ly2 S2 mem2 B1 Htw KA U9 D33 HJ Hfrm Hperm Hmo Hsp Hgp
  Htp Hhi Hsav regs2 E0.
unfold R_HOST. split; [exact (mb_cur Wc ly2 S2 mem2 _ KA4 HCUR)|]. split; [exact He1|].
split; [unfold TC.SPEC_ANN_MIN; lia|]. split; [exact (eq_trans (RK (Z_to_bv 5 9) ltac:(mb_in)) R9)|].
exists B3. split; [exact SW|]. split; [exact TK | exact Er].
Qed.

End seg.
