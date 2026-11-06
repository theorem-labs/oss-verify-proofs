(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 650 of its 744 lines of code are new or changed and 936 lines of the source are left out. *)
(* m_rx_seg_ack: the ACK segment of the image-B walk of m_rx (lib/B/Prog/m_rx_seg_kit.v), code +0x160 .. +0x1a8
   (0x84d7c .. 0x84dc4): from the cut ACK to the cut TICK (M.fly.on = 0, f.ack <> M.fly.counter, M.state <> S_WAKING)
   and to the cut MO (S_WAKING), through the 4-byte stores of OW.acked + 1, OW.acked_counter, OW.acked_retry,
   M.fly.on = 0 and M.e2_acked = 1. The branch to the trap word (+0x3e4, OW.acked + 1 below OW.acked: OW.acked =
   INT_MAX) is refuted by the model: int_inc is None there (lib/U/Prog/T/m_rx.v mr_ack_norm, mr_inc_trap). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_body.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  TransportGRunB TransportGFrameB CanKit YC1g YC1h m_rx_seg_kit.
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

(* Atoms: 0 .. 31 the registers at the cut (s1 = &M, a0 = M.state), 32 .. 34 the 4 bytes of M.fly.on,
   M.fly.counter, M.fly.retries, 35 those of OW.acked, 36 f.ack (the struct's 4 bytes at sp + 36). Regions at the cut:
   M.fly (based on s1, atom 9; the window of M.fly.on) and f.ack (based on sp); added on the path that stores them:
   OW.acked, OW.acked_counter with OW.acked_retry (object 12), M.e2_acked. No instrumented check in this range: no
   shadow entry. *)
Definition ma_fly : YP09.region := YP09.mkRegion (Some 9%nat) 96 112 96 100
  [YP09.mkChunk 96 (YP09.CVal 4 (SOff 32 0)); YP09.mkChunk 104 (YP09.CVal 4 (SOff 33 0));
   YP09.mkChunk 108 (YP09.CVal 4 (SOff 34 0))].
Definition ma_sf : YP09.region := YP09.mkRegion (Some 2%nat) 36 40 0 0 [YP09.mkChunk 36 (YP09.CVal 4 (SOff 36 0))].
Definition ma_ack : YP09.region := YP09.mkRegion (Some (A_OBJ 12)) 216 220 216 220
  [YP09.mkChunk 216 (YP09.CVal 4 (SOff 35 0))].
Definition ma_acc : YP09.region := YP09.mkRegion (Some (A_OBJ 12)) 224 232 224 232 [].
Definition ma_e2 : YP09.region := YP09.mkRegion (Some 9%nat) 16 20 16 20 [].
Definition ma_regions : smem := [ma_fly; ma_sf].
Definition ma_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF TB_M TB_M 5); (A_OBJ 12, mkAF TB_OW TB_OW 5)] [] [].
Definition ss_ma : sstate := mkSS (AF_m_rx + OFF_ACK) sr_atoms ma_regions None ma_facts.
Definition MA_SH : list shent := [].
Definition MA_Bx : sv := SLit 0.

Definition ma_vals (fr : TI.tframe) (n : Z) (Bw : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at Bw TW.A_M_fly_on 4); Z_to_bv 64 (TW.u_at Bw TW.A_M_fly_counter 4);
   Z_to_bv 64 (TW.u_at Bw TW.A_M_fly_retries 4); Z_to_bv 64 (TW.u_at Bw TW.A_OW_acked 4);
   Z_to_bv 64 (DSpec.sf_ack (mrx_f fr n))].

(* The windows the runs may write, by stage. *)
Definition maX0 (a : Z) : Prop := TB_M + 96 <= a < TB_M + 100.
Definition maX1 (a : Z) : Prop := maX0 a \/ TB_OW + 216 <= a < TB_OW + 220 \/ TB_OW + 224 <= a < TB_OW + 232.
Definition maX2 (a : Z) : Prop := maX1 a \/ TB_M + 16 <= a < TB_M + 20.

Lemma ma_X01 : forall a, maX0 a -> maX1 a. Proof. intros a H. left. exact H. Qed.
Lemma ma_X12 : forall a, maX1 a -> maX2 a. Proof. intros a H. left. exact H. Qed.
Lemma ma_X02 : forall a, maX0 a -> maX2 a. Proof. intros a H. left; left. exact H. Qed.
Lemma ma_X2_rng : forall a, maX2 a -> TB_M <= a < TB_OW + 304.
Proof. intros a H. unfold maX2, maX1, maX0 in H. unfold TB_M, TB_OW in *. lia. Qed.

Lemma ma_inG : forall a, (TB_M <= a < TB_M + TW.SZ_M) \/ (TB_OW <= a < TB_OW + TW.SZ_OW) -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. destruct Ha as [Ha|Ha].
- exists (TB_M, TW.SZ_M). split; [exact (TMAP_B_in_G _ _ _ TMAP_B_M) | unfold in_zr; cbn [fst snd]; lia].
- exists (TB_OW, TW.SZ_OW). split; [exact (TMAP_B_in_G _ _ _ TMAP_B_OW) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* Values the code forms, at a valuation                               *)
(* ------------------------------------------------------------------ *)

(* addiw a3, a4, 1 on the sign-extended OW.acked (+0x180). *)
Lemma ma_addw1 : forall E k u, ew E k = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SAluw ALU_ADD (SExt true 32 (SOff k 0)) (SLit 1)) =
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 u)) + 1)).
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

Lemma ma_ack_off : forall fr n B2, length B2 = Z.to_nat TW.W_LEN -> TW.M_fly_on B2 = 0 ->
  UMR.mr_ack fr n B2 = Some (B2, tt).
Proof.
intros fr n B2 L H. rewrite (UMR.mr_ack_norm fr n B2 L), H. change (negb (0 =? 0)) with false. cbn [andb]. AB.mb_refl.
Qed.

Lemma ma_ack_ne : forall fr n B2, length B2 = Z.to_nat TW.W_LEN ->
  DSpec.sf_ack (mrx_f fr n) <> TW.M_fly_counter B2 -> UMR.mr_ack fr n B2 = Some (B2, tt).
Proof.
intros fr n B2 L H. rewrite (UMR.mr_ack_norm fr n B2 L), (proj2 (Z.eqb_neq _ _) H), andb_false_r.
cbv beta iota. AB.mb_refl.
Qed.

Lemma ma_ack_eq : forall fr n B2 B3, length B2 = Z.to_nat TW.W_LEN -> TW.M_fly_on B2 <> 0 ->
  DSpec.sf_ack (mrx_f fr n) = TW.M_fly_counter B2 -> UMR.mr_ack fr n B2 = Some (B3, tt) ->
  TW.OW_acked B2 <> TC.INT_MAX /\
  (TW.M_state B2 = 1 -> TC.m_maybe_online_m (TW.set_M_e2_acked (AB.mb_B6 B2) 1) = Some (B3, tt)) /\
  (TW.M_state B2 <> 1 -> B3 = AB.mb_B6 B2).
Proof.
intros fr n B2 B3 L H1 H2 Hk. rewrite (UMR.mr_ack_norm fr n B2 L) in Hk.
rewrite (proj2 (Z.eqb_neq _ _) H1), H2, Z.eqb_refl in Hk. cbn [negb andb] in Hk.
revert Hk.
destruct (Z.eqb_spec (TW.OW_acked B2) TC.INT_MAX) as [EI|NI]; intros Hk; cbv beta iota in Hk; [discriminate Hk|].
unfold AB.mb_B6. split; [exact NI|]. split.
- intros Hs. rewrite Hs, Z.eqb_refl in Hk. cbv beta iota in Hk. exact Hk.
- intros Hs. rewrite (proj2 (Z.eqb_neq _ _) Hs) in Hk. cbv beta iota in Hk.
  destruct (mrx_some_inv _ _ _ _ _ _ Hk) as [Hb _]. symmetry. exact Hb.
Qed.

(* ------------------------------------------------------------------ *)
(* The world relation at the exits                                     *)
(* ------------------------------------------------------------------ *)

Lemma ma_tw_in_rng : forall x, tw_in TMAP_B x -> 0 <= x < 2 ^ 64.
Proof.
intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. lia.
Qed.

Ltac ma_unP HP := mrx_unP HP; try change (Z.of_nat 4) with 4 in *.

(* The stores of cmd ACK: OW.acked, OW.acked_counter, OW.acked_retry, M.fly.on. *)
Lemma ma_w6 : forall rd0 rdF Bw a c rt, tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 216 + Z.of_nat j) = Some (YO0f.le_byte a 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 224 + Z.of_nat j) = Some (YO0f.le_byte c 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 228 + Z.of_nat j) = Some (YO0f.le_byte rt 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ maX1 x -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_M_fly_on (TW.set_OW_acked_retry (TW.set_OW_acked_counter (TW.set_OW_acked Bw a) c) rt) 0).
Proof.
intros rd0 rdF Bw a c rt H V2 V3 V4 V5 Hk.
unfold TW.set_M_fly_on, TW.set_OW_acked_retry, TW.set_OW_acked_counter, TW.set_OW_acked.
pose proof (mrx_tw_start rdF rd0 Bw H) as H0.
pose proof (mrx_tw_step rdF rd0 _ Bw TW.OFF_OW TB_OW TW.SZ_OW 216 TW.A_OW_acked 4 a H0 TMAP_B_OW
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; lia) V2) as H2.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 224 TW.A_OW_acked_counter 4 c H2 TMAP_B_OW
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; lia) V3) as H3.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 228 TW.A_OW_acked_retry 4 rt H3 TMAP_B_OW
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; lia) V4) as H4.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 96 TW.A_M_fly_on 4 0 H4 TMAP_B_M
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_M; lia) V5) as H5.
apply (mrx_tw_end rdF rd0 _ _ H5). intros x Hx HP. ma_unP HP.
apply Hk; [exact Hx | unfold maX1, maX0; lia].
Qed.

(* ... and M.e2_acked = 1. *)
Lemma ma_w7 : forall rd0 rdF Bw a c rt, tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 216 + Z.of_nat j) = Some (YO0f.le_byte a 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 224 + Z.of_nat j) = Some (YO0f.le_byte c 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 228 + Z.of_nat j) = Some (YO0f.le_byte rt 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 16 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ maX2 x -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_M_e2_acked (TW.set_M_fly_on (TW.set_OW_acked_retry (TW.set_OW_acked_counter
    (TW.set_OW_acked Bw a) c) rt) 0) 1).
Proof.
intros rd0 rdF Bw a c rt H V2 V3 V4 V5 V6 Hk.
unfold TW.set_M_e2_acked, TW.set_M_fly_on, TW.set_OW_acked_retry, TW.set_OW_acked_counter, TW.set_OW_acked.
pose proof (mrx_tw_start rdF rd0 Bw H) as H0.
pose proof (mrx_tw_step rdF rd0 _ Bw TW.OFF_OW TB_OW TW.SZ_OW 216 TW.A_OW_acked 4 a H0 TMAP_B_OW
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; lia) V2) as H2.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 224 TW.A_OW_acked_counter 4 c H2 TMAP_B_OW
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; lia) V3) as H3.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 228 TW.A_OW_acked_retry 4 rt H3 TMAP_B_OW
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; lia) V4) as H4.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 96 TW.A_M_fly_on 4 0 H4 TMAP_B_M
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_M; lia) V5) as H5.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 16 TW.A_M_e2_acked 4 1 H5 TMAP_B_M
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_M; lia) V6) as H6.
apply (mrx_tw_end rdF rd0 _ _ H6). intros x Hx HP. ma_unP HP.
apply Hk; [exact Hx | unfold maX2, maX1, maX0; lia].
Qed.

(* An unwritten window byte read from a chunk holding the world's value. *)
Lemma ma_keep4 : forall (rd0 rdF : Z -> option Z) Bw o b n k x,
  tw_at TMAP_B rd0 Bw -> In (o, b, n) TMAP_B -> 0 <= k -> k + 4 <= n ->
  (forall j, (j < 4)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw (o + k) 4) 4 j)) ->
  b + k <= x < b + k + 4 -> rdF x = rd0 x.
Proof.
intros rd0 rdF Bw o b n k x H Hin Hk Hkn V Hx.
replace x with (b + k + Z.of_nat (Z.to_nat (x - (b + k)))) by lia.
rewrite (V (Z.to_nat (x - (b + k))) ltac:(lia)).
rewrite (tw_read TMAP_B rd0 Bw o b n k 4 (Z.to_nat (x - (b + k))) TMAP_B_ok H Hin Hk ltac:(lia) ltac:(lia)).
AB.mb_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* The runs                                                            *)
(* ------------------------------------------------------------------ *)

Ltac ma_awr U9 UOW :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first
      [ lia
      | rewrite U9 in Ha; right; left; apply ma_inG; unfold TB_M, TB_OW, TW.SZ_M, TW.SZ_OW in *; lia
      | rewrite UOW in Ha; right; left; apply ma_inG; unfold TB_M, TB_OW, TW.SZ_M, TW.SZ_OW in *; lia ] |]);
  apply awr_ok_x_nil.

(* What the walk keeps, from the cut's memory mem0 to a memory m: the view outside the windows X. *)
Definition ma_KA {fx : YK11.FPState} {rc : YM05.RunCeil} (Wc : world tfibsegs) (X : Z -> Prop)
    (mem0 m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview tfibsegs (w_H Wc) m a = aview tfibsegs (w_H Wc) mem0 a.

Lemma ma_KA_step {fx : YK11.FPState} {rc : YM05.RunCeil} : forall E rs (Wc : world tfibsegs) (X : Z -> Prop) mem0
    (m m' : word -> option byte),
  ma_KA Wc X mem0 m -> frame_of E rs (mrestrict (w_H Wc) m) (mrestrict (w_H Wc) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> X a) ->
  ma_KA Wc X mem0 m'.
Proof.
intros E rs Wc X mem0 m m' KA HFr Hw a Ha HX.
rewrite (YC4b.kept_of_frame E rs (w_H Wc) m m' X HFr Hw a Ha HX). exact (KA a Ha HX).
Qed.

Lemma ma_KA_mono {fx : YK11.FPState} {rc : YM05.RunCeil} : forall (Wc : world tfibsegs) (X X' : Z -> Prop) mem0 m,
  (forall a, X a -> X' a) -> ma_KA Wc X mem0 m -> ma_KA Wc X' mem0 m.
Proof. intros Wc X X' mem0 m HX KA a Ha HN. apply KA; [exact Ha | intros H; apply HN; exact (HX a H)]. Qed.

Ltac ma_win Usp U9 UOW :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp, ?U9, ?UOW in Hx;
     unfold maX2, maX1, maX0;
     lia |]);
  destruct Hin.

(* After a run: the model generalized, the kept facts carried to the run's last memory. *)
Ltac ma_after KA X Usp U9 UOW :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    let md := fresh "mdw" in set (md := mdx) in *; clearbody md end;
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    let KA' := fresh "KAn" in
    pose proof (ma_KA_step _ _ _ X _ _ _ KA HFr) as KA';
    lazymatch type of KA' with ?P -> _ =>
      let Hw := fresh "Hw" in assert (Hw : P) by (ma_win Usp U9 UOW); specialize (KA' Hw); clear Hw end;
    clear KA HFr; rename KA' into KA end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  lazymatch goal with HG : mem_grows _ _ |- _ => clear HG end.

(* A new region of the state: disjoint from the state's regions (their bases rewritten to numbers). *)
Ltac ma_disj Usp U9 UOW :=
  cbn [ss_mem YP09.all_disjoint]; unfold ma_fly, ma_sf, ma_ack, ma_acc, ma_e2;
  repeat match goal with |- _ /\ _ => split end; try exact I;
  unfold YP09.extent_disjoint;
  try change (A_OBJ 12) with 253%nat;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?Usp, ?U9, ?UOW;
  unfold TB_M, TB_OW, MRX_FRAME in *;
  lia.
Ltac ma_add HS R Hok Usp U9 UOW :=
  lazymatch type of HS with st_ok_pi ?sg0 ?vl0 ?Ex0 ?ss0 ?m0 =>
    let ss0' := eval vm_compute in ss0 in change (st_ok_pi sg0 vl0 Ex0 ss0' m0) in HS end;
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
    let HSa := fresh "HSa" in
    pose proof (st_ok_pi_add_region Ex ss m R HS eq_refl Hok ltac:(ma_disj Usp U9 UOW)) as HSa;
    clear HS; rename HSa into HS;
    lazymatch type of HS with st_ok_pi ?sg2 ?vl2 ?Ex2 ?ss2 ?m2 =>
      let ss' := eval vm_compute in ss2 in change (st_ok_pi sg2 vl2 Ex2 ss' m2) in HS end end.
Ltac ma_add0 HS R L U Usp U9 UOW :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ ?m => ma_add HS R (L Ex (ms_mem m) U) Usp U9 UOW end.
Ltac ma_mono KA L :=
  let KA' := fresh "KAm" in pose proof (ma_KA_mono _ _ _ _ _ L KA) as KA'; clear KA; rename KA' into KA.
(* One run of the walk (to its stop, or to the pc stop), with the write rights and the kept view; the walk's
   hypotheses are found by their types. *)
Ltac ma_step X :=
  lazymatch goal with
  | RUN : context [sym_runN_pi_tok _ _ _ _ _ _ _ _], HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
    HJ : @W_journalG.ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, KA : ma_KA _ _ _ _,
    Usp : bv_unsigned (ew _ 2%nat) = _, U9 : bv_unsigned (ew _ 9%nat) = TB_M,
    UOW : bv_unsigned (ew _ 253%nat) = TB_OW |- _ =>
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan; [ ma_awr U9 UOW | ma_after KA X Usp U9 UOW ]
  end.
Ltac ma_stepto X stop :=
  lazymatch goal with
  | RUNTO : context [sym_run_toN_pi_tok _ _ _ _ _ _ _ _ _], HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
    HJ : @W_journalG.ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, KA : ma_KA _ _ _ _,
    Usp : bv_unsigned (ew _ 2%nat) = _, U9 : bv_unsigned (ew _ 9%nat) = TB_M,
    UOW : bv_unsigned (ew _ 253%nat) = TB_OW |- _ =>
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan stop; [ ma_awr U9 UOW | ma_after KA X Usp U9 UOW ]
  end.
Ltac ma_br :=
  lazymatch goal with
  | RUN : context [sym_runN_pi_tok _ _ _ _ _ _ _ _], BR : context [add_cond _ _], HS : st_ok_pi _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan
  end.

(* The registers the run kept, by the symbolic state: sp, gp, tp and s3 .. s11. *)
Tactic Notation "ma_rk" constr(HS) constr(E0) constr(regs2) constr(vals) constr(AGR) ident(RK) :=
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict ?Hh ?m) =>
    pose proof (regs_kept_of_st_ok_pi E0 ss (restrict Hh m) regs2 vals
      [2%bv; 3%bv; 4%bv; Z_to_bv 5 19; Z_to_bv 5 20; Z_to_bv 5 21; Z_to_bv 5 22; Z_to_bv 5 23;
       Z_to_bv 5 24; Z_to_bv 5 25; Z_to_bv 5 26; Z_to_bv 5 27] HS AGR eq_refl) as RK;
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

Definition ma_E (regs : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs (ma_vals fr n Bw)).

Lemma ma_ow_val : VAL (A_OBJ 12) = TB_OW.
Proof. vm_compute. reflexivity. Qed.

Lemma ma_stk : 112 <= MRX_STK.
Proof. vm_compute. discriminate. Qed.

(* The entry state of the segment. *)
Lemma ma_entry : forall (Wc : world segs) regs2 mem2 Bw,
  tw_at TMAP_B (aview segs (w_H Wc) mem2) Bw ->
  YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME) -> YK11.getr regs2 9 = w64 TB_M ->
  mrx_sf Wc mem2 sp1 fr n -> 0 <= DSpec.sf_ack (mrx_f fr n) < 2 ^ 32 ->
  st_ok_pi segs VAL (ma_E regs2 Bw) ss_ma
    (restrict (w_H Wc) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + (AF_m_rx + OFF_ACK))) mem2 (YK11.seg_rom segs))).
Proof.
  intros Wc regs2 mem2 Bw Htw R2 R9 HSF RA.
  pose proof HST as (Hsp0 & Hsp16 & Hceil & H46 & H47 & _).
  pose proof ma_stk as HSTK.
  pose proof ma_ow_val as V12.
  set (E := ma_E regs2 Bw).
  assert (EOB : forall j, (j < 95)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E, ma_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (EE : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E k = YK11.getr regs2 q)
    by (intros k q Hk; unfold E, ma_E; apply ew_Eimg_Ereg_nat; exact Hk).
  assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (ma_vals fr n Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, ma_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 4%nat ltac:(lia)) as E36.
  cbn [Nat.add nth ma_vals] in E32, E33, E34, E36.
  assert (Usp : base_val E (Some 2%nat) = sp1 - MRX_FRAME).
  { cbn [base_val]. rewrite (EE 2%nat 2%bv eq_refl), R2. apply unsigned_lit_small. unfold MRX_FRAME. lia. }
  assert (U9 : base_val E (Some 9%nat) = TB_M).
  { cbn [base_val]. rewrite (EE 9%nat 9%bv eq_refl), R9. apply unsigned_lit_small. unfold TB_M. lia. }
  assert (DEN : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff k 0) = Z_to_bv 64 v)
    by (intros k v Hk Hv; cbn [sv_denot]; rewrite Hk, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  pose proof (TWL.u_at_range Bw TW.A_M_fly_on 4) as R32. pose proof (TWL.u_at_range Bw TW.A_M_fly_counter 4) as R33.
  pose proof (TWL.u_at_range Bw TW.A_M_fly_retries 4) as R34.
  change (8 * Z.of_nat 4) with 32 in R32, R33, R34.
  rewrite restrict_mkst_fx. unfold ss_ma.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold ma_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold ma_fly, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite U9. split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw). apply ma_inG. left.
        unfold TW.SZ_M. lia.
      * apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
        -- apply (chunk_ok_val segs E _ TB_M 96 4 (SOff 32 0) (TW.u_at Bw TW.A_M_fly_on 4));
             [apply DEN; [exact E32 | lia] | exact R32 | lia |].
           exact (tw_read_val segs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 96 4 TMAP_B_ok Htw TMAP_B_M
             ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
        -- apply (chunk_ok_val segs E _ TB_M 104 4 (SOff 33 0) (TW.u_at Bw TW.A_M_fly_counter 4));
             [apply DEN; [exact E33 | lia] | exact R33 | lia |].
           exact (tw_read_val segs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 104 4 TMAP_B_ok Htw TMAP_B_M
             ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
        -- apply (chunk_ok_val segs E _ TB_M 108 4 (SOff 34 0) (TW.u_at Bw TW.A_M_fly_retries 4));
             [apply DEN; [exact E34 | lia] | exact R34 | lia |].
           exact (tw_read_val segs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 108 4 TMAP_B_ok Htw TMAP_B_M
             ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold ma_sf, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite Usp. unfold MRX_FRAME in *.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (sp1 - 112) 36 4 (SOff 36 0) (DSpec.sf_ack (mrx_f fr n)));
        [apply DEN; [exact E36 | lia] | exact RA | lia |].
      exact (mrx_sf_ack (mrestrict (w_H Wc) mem2) (sp1 - 112) (TI.tf_addr fr) (mrx_f fr n) HSF).
  - unfold ma_regions, ma_fly, ma_sf.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite Usp, U9.
    unfold TB_M, MRX_FRAME in *. repeat split; lia.
  - unfold ma_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    pose proof (EOB 12%nat ltac:(lia)) as E253. rewrite V12 in E253. change (A_OBJ 12) with 253%nat in E253.
    change (A_OBJ 12) with 253%nat.
    rewrite (EE 2%nat 2%bv eq_refl), (EE 9%nat 9%bv eq_refl), R2, R9, E253.
    unfold w64.
    rewrite (unsigned_lit_small (sp1 - MRX_FRAME)) by (unfold MRX_FRAME; lia).
    rewrite (unsigned_lit_small TB_M) by (unfold TB_M; lia).
    rewrite (unsigned_lit_small TB_OW) by (unfold TB_OW; lia).
    change (2 ^ 4) with 16. change (2 ^ 5) with 32.
    unfold MRX_FRAME.
    repeat match goal with |- _ /\ _ => split end; try exact I;
      first [lia | unfold TB_M; reflexivity | unfold TB_OW; reflexivity | reflexivity
            | rewrite Zminus_mod, Hsp16; reflexivity].
Qed.

(* A value read through the view at mem0 is read at m where m keeps the view. *)
Lemma ma_val_kept : forall (Wc : world segs) (X : Z -> Prop) mem0 m a (k : nat) v,
  ma_KA Wc X mem0 m -> 0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> (forall i, a <= i < a + Z.of_nat k -> ~ X i) ->
  val_mem segs (mrestrict (w_H Wc) mem0) a k v -> val_mem segs (mrestrict (w_H Wc) m) a k v.
Proof.
intros Wc X mem0 m a k v KA Ha Hak HX HV j Hj.
pose proof (HV j Hj) as Hb.
pose proof (KA (a + Z.of_nat j) ltac:(lia) (HX (a + Z.of_nat j) ltac:(lia))) as E.
unfold aview in E. rewrite Hb in E. cbn [option_map] in E.
destruct (mbyte segs (mrestrict (w_H Wc) m) (a + Z.of_nat j)) as [bt|] eqn:Eb; cbn [option_map] in E;
  [|discriminate E].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma ma_ack_ok : forall E (Wc : world segs) m Bw,
  bv_unsigned (ew E 253%nat) = TB_OW ->
  ew E 35%nat = Z_to_bv 64 (TW.u_at Bw TW.A_OW_acked 4) ->
  val_mem segs (mrestrict (w_H Wc) m) (TB_OW + 216) 4 (TW.u_at Bw TW.A_OW_acked 4) ->
  region_ok segs E (mrestrict (w_H Wc) m) ma_ack.
Proof.
intros E Wc m Bw H E35 V1. unfold ma_ack, region_ok.
change (A_OBJ 12) with 253%nat.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H. split; [unfold TB_OW; lia|]. split; [unfold TB_OW; lia|]. split.
- intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_OW + o) G_HARNESS_B_rw). apply ma_inG. right.
  unfold TW.SZ_OW. lia.
- apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs E _ TB_OW 216 4 (SOff 35 0) (TW.u_at Bw TW.A_OW_acked 4));
    [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | exact (TWL.u_at_range Bw TW.A_OW_acked 4) | lia | exact V1].
Qed.

Lemma ma_acc_ok : forall E m, bv_unsigned (ew E 253%nat) = TB_OW -> region_ok segs E m ma_acc.
Proof.
intros E m H. unfold ma_acc, region_ok.
change (A_OBJ 12) with 253%nat.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H. split; [unfold TB_OW; lia|]. split; [unfold TB_OW; lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_OW + o) G_HARNESS_B_rw). apply ma_inG. right.
unfold TW.SZ_OW. lia.
Qed.

Lemma ma_e2_ok : forall E m, bv_unsigned (ew E 9%nat) = TB_M -> region_ok segs E m ma_e2.
Proof.
intros E m H. unfold ma_e2, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H. split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw). apply ma_inG. left.
unfold TW.SZ_M. lia.
Qed.

Lemma ma_agree : forall regs Bw, env_agree 32 (Ereg regs (ma_vals fr n Bw)) (ma_E regs Bw).
Proof. intros regs Bw. split; [intros k Hk; unfold ma_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* An exit: the cut pc with its facts R, from the run's last state. *)
Lemma ma_exit : forall (Wc : world segs) ly2 S2 pc pc' R regsF memF mdF Bn,
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

(* The saved slots, kept across runs that write only the windows. *)
Lemma ma_saved_kept : forall (Wc : world segs) mem2 m, ma_KA Wc maX2 mem2 m ->
  mrx_saved Wc mem2 sp1 regs0 -> mrx_saved Wc m sp1 regs0.
Proof.
intros Wc mem2 m KA HSv. pose proof HST as (_ & _ & _ & H46 & H47 & _). pose proof ma_stk as HSTK.
apply (mrx_saved_kept Wc Wc mem2 m sp1 regs0 HSv). intros a Ha.
apply KA; [lia | intros HX; pose proof (ma_X2_rng a HX); unfold TB_OW in *; lia].
Qed.

(* The bytes of chunk c of region i of the run's last state. *)
Lemma ma_chunk : forall E (Wc : world segs) ss ms i rg c off w e v base,
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

(* The world's bytes when M.fly.on's window kept its value (no store yet). *)
Lemma ma_rest0 : forall (Wc : world segs) mem2 m Bw,
  tw_at TMAP_B (aview segs (w_H Wc) mem2) Bw -> ma_KA Wc maX0 mem2 m ->
  (forall j, (j < 4)%nat -> aview segs (w_H Wc) m (TB_M + 96 + Z.of_nat j) =
     Some (YO0f.le_byte (TW.u_at Bw (TW.OFF_M + 96) 4) 4 j)) ->
  forall x, tw_in TMAP_B x -> aview segs (w_H Wc) m x = aview segs (w_H Wc) mem2 x.
Proof.
intros Wc mem2 m Bw Htw KA VF x Hx.
destruct (Z_lt_le_dec x (TB_M + 96)) as [Hl|Hl]; [| destruct (Z_lt_le_dec x (TB_M + 100)) as [Hl2|Hl2]].
- apply KA; [exact (ma_tw_in_rng x Hx) | unfold maX0; lia].
- exact (ma_keep4 _ _ Bw TW.OFF_M TB_M TW.SZ_M 96 x Htw TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia) VF
    ltac:(lia)).
- apply KA; [exact (ma_tw_in_rng x Hx) | unfold maX0; lia].
Qed.

(* x19 .. x27 at the exit: the run kept them. *)
Lemma ma_hi_of : forall (regsF regs2 : bvmap 5 word),
  (forall rr, In rr [2%bv; 3%bv; 4%bv; Z_to_bv 5 19; Z_to_bv 5 20; Z_to_bv 5 21; Z_to_bv 5 22; Z_to_bv 5 23;
       Z_to_bv 5 24; Z_to_bv 5 25; Z_to_bv 5 26; Z_to_bv 5 27] ->
     YK11.getr regsF rr = YK11.getr regs2 rr) ->
  mrx_hi regs0 regs2 -> mrx_hi regs0 regsF.
Proof.
intros regsF regs2 RK HH q Hq. rewrite <- (HH q Hq). apply RK.
assert (Hq2 : q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
clear Hq.
destruct Hq2 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; AB.mb_in.
Qed.

(* The ACK segment: from the cut ACK (+0x160) to TICK (M.fly.on = 0, f.ack <> M.fly.counter, M.state <> S_WAKING)
   or MO (S_WAKING); the overflow branch to the trap word is refuted by the model. *)
Lemma mrx_seg_ack : K (MRX_PC OFF_TICK) (R_TICK Bw' r) -> K (MRX_PC OFF_MO) (R_MO Bw' r) ->
  K (MRX_PC OFF_ACK) (R_ACK B fr n sp1 Bw' r).
Proof using All.
intros KTICK KMO.
unfold mrx_K. intros Wc B2 c Hat.
destruct Hat as (ly2 & S2 & regs2 & mem2 & md2 & Hc0 & HJ & Hfrm & Hperm & Hmo & Hsp & Hgp & Htp & Hhi & Hsav
  & Htw & HR).
subst c.
destruct HR as ((Hok & _ & HSF) & Hcmd & R10 & R9 & B3 & HACK & TK & Er).
pose proof HST as (Hsp0 & Hsp16 & Hceil & H46 & H47 & _).
pose proof ma_stk as HSTK.
assert (LB2 : length B2 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw).
pose proof (mrx_ok_fields fr n Hok) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RA).
pose proof (TWL.s32_range B2 TW.A_M_state) as RS. change (TW.s32_at B2 TW.A_M_state) with (TW.M_state B2) in RS.
pose proof (TWL.s32_range B2 TW.A_M_fly_on) as RF. change (TW.s32_at B2 TW.A_M_fly_on) with (TW.M_fly_on B2) in RF.
pose proof (TWL.s32_range B2 TW.A_OW_acked) as RAK.
change (TW.s32_at B2 TW.A_OW_acked) with (TW.OW_acked B2) in RAK.
pose proof (TWL.u_at_range B2 TW.A_M_fly_on 4) as R32. pose proof (TWL.u_at_range B2 TW.A_M_fly_counter 4) as R33.
pose proof (TWL.u_at_range B2 TW.A_M_fly_retries 4) as R34. pose proof (TWL.u_at_range B2 TW.A_OW_acked 4) as R35.
change (8 * Z.of_nat 4) with 32 in R32, R33, R34, R35.
assert (RC : 0 <= TW.M_fly_counter B2 < 2 ^ 32) by exact R33.
pose proof ma_ow_val as V12.
set (E0 := ma_E regs2 B2).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ma_E; apply Eimg_env).
assert (EE : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E0 k = YK11.getr regs2 q)
  by (intros k q Hk; unfold E0, ma_E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E0 2%nat) = sp1 - MRX_FRAME).
{ rewrite (EE 2%nat 2%bv eq_refl), Hsp. apply unsigned_lit_small. unfold MRX_FRAME. lia. }
assert (U9 : bv_unsigned (ew E0 9%nat) = TB_M).
{ rewrite (EE 9%nat 9%bv eq_refl), R9. apply unsigned_lit_small. unfold TB_M. lia. }
assert (UOW : bv_unsigned (ew E0 253%nat) = TB_OW).
{ unfold E0, ma_E. rewrite (Eimg_img _ 253%nat) by (unfold A_TEXT, A_LIM; lia).
  change 253%nat with (A_OBJ 12). rewrite V12. apply unsigned_lit_small. unfold TB_OW. lia. }
pose proof (ma_entry Wc regs2 mem2 B2 Htw Hsp R9 HSF RA) as HS.
fold E0 in HS.
assert (SHOK : sh_ok segs MA_Bx MA_SH E0 (mrestrict (w_H Wc) mem2)) by (unfold sh_ok, MA_SH; apply Forall_nil).
assert (KA : ma_KA Wc maX0 mem2 mem2) by (intros a _ _; reflexivity).
assert (EX : forall j, (j < 5)%nat -> ew E0 (32 + j) = nth j (ma_vals fr n B2) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, ma_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36.
cbn [Nat.add nth ma_vals] in E32, E33, E34, E35, E36.
clear EX.
assert (Vack0 : val_mem segs (mrestrict (w_H Wc) mem2) (TB_OW + 216) 4 (TW.u_at B2 TW.A_OW_acked 4))
  by exact (tw_read_val segs _ TMAP_B B2 TW.OFF_OW TB_OW TW.SZ_OW 216 4 TMAP_B_ok Htw TMAP_B_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)).
(* the values the code forms *)
assert (D32 : sv_denot E0 (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.M_fly_on B2))
  by exact (AB.mbd_sext E0 32 _ E32 R32).
assert (D33 : sv_denot E0 (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (bv_swrap 32 (TW.M_fly_counter B2)))
  by exact (AB.mbd_sext E0 33 _ E33 R33).
assert (D34 : sv_denot E0 (SExt true 32 (SOff 34 0)) = Z_to_bv 64 (bv_swrap 32 (TW.M_fly_retries B2)))
  by exact (AB.mbd_sext E0 34 _ E34 R34).
assert (D35 : sv_denot E0 (SExt true 32 (SOff 35 0)) = Z_to_bv 64 (TW.OW_acked B2))
  by exact (AB.mbd_sext E0 35 _ E35 R35).
assert (D36 : sv_denot E0 (SExt true 32 (SOff 36 0)) = Z_to_bv 64 (bv_swrap 32 (DSpec.sf_ack (mrx_f fr n))))
  by exact (AB.mbd_sext E0 36 _ E36 RA).
assert (DA1 : sv_denot E0 (SAluw ALU_ADD (SExt true 32 (SOff 35 0)) (SLit 1)) =
  Z_to_bv 64 (bv_swrap 32 (TW.OW_acked B2 + 1))).
{ rewrite (ma_addw1 E0 35 _ E35 R35), UMR.mr_swrap32_lit_add. unfold TW.OW_acked, TW.s32_at. AB.mb_refl. }
assert (D10 : sv_denot E0 (SOff 10 0) = Z_to_bv 64 (TW.M_state B2)).
{ cbn [sv_denot]. rewrite (EE 10%nat 10%bv eq_refl), R10, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (D32' : sv_denot E0 (SOff 32 0) = Z_to_bv 64 (TW.u_at B2 TW.A_M_fly_on 4))
  by (rewrite (AB.mbd_off E0 32 _ 0 E32 ltac:(lia)), Z.add_0_r; reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
rewrite (mrx_pcv OFF_ACK).
(* +0x160 - +0x164: a1 = M.fly.on, `beqz` *)
ma_step maX0.
ma_br.
{ (* M.fly.on = 0: m_tick *)
  rewrite D32 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_eq in Hc by lia. apply Z.eqb_eq in Hc. rename Hc into Hfl.
  rewrite (ma_ack_off fr n B2 LB2 Hfl) in HACK.
  destruct (mrx_some_inv _ _ _ _ _ _ HACK) as [EB _]. subst B3.
  ma_stepto maX0 (AF_m_rx + OFF_TICK).
  pmkst HS.
  ma_rk HS E0 regs2 (ma_vals fr n B2) (ma_agree regs2 B2) RK.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
    pose proof (ma_chunk E0 Wc ss m 0%nat _ 0%nat 96 4%N (SOff 32 0) (TW.u_at B2 TW.A_M_fly_on 4) TB_M HS eq_refl
      U9 eq_refl D32' ltac:(cbn; lia)) as VF;
    apply (ma_exit Wc ly2 S2 (MRX_PC OFF_TICK) _ (R_TICK Bw' r) (ms_regs m) (ms_mem m) _ B2) end.
  - rewrite (mrx_pcv OFF_TICK). reflexivity.
  - exact KTICK.
  - exact HJ.
  - exact Hfrm.
  - exact Hperm.
  - exact Hmo.
  - exact (eq_trans (RK 2%bv ltac:(AB.mb_in)) Hsp).
  - exact (eq_trans (RK 3%bv ltac:(AB.mb_in)) Hgp).
  - exact (eq_trans (RK 4%bv ltac:(AB.mb_in)) Htp).
  - exact (ma_hi_of _ _ RK Hhi).
  - exact (ma_saved_kept Wc mem2 _ (ma_KA_mono _ _ _ _ _ ma_X02 KA) Hsav).
  - apply (tw_kept TMAP_B (aview segs (w_H Wc) mem2) _ B2 Htw). exact (ma_rest0 Wc mem2 _ B2 Htw KA VF).
  - unfold R_TICK. split; [exact TK | exact Er]. }
rewrite D32 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_eq in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Hfl.
(* +0x168 - +0x170: a1 = f.ack, a2 = M.fly.counter, `bne` *)
ma_step maX0.
ma_br.
{ (* f.ack <> M.fly.counter: m_tick *)
  rewrite D36, D33 in Hc. rewrite AB.mbl_ne_sw in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
  rename Hc into Hne.
  rewrite (ma_ack_ne fr n B2 LB2 Hne) in HACK.
  destruct (mrx_some_inv _ _ _ _ _ _ HACK) as [EB _]. subst B3.
  ma_stepto maX0 (AF_m_rx + OFF_TICK).
  pmkst HS.
  ma_rk HS E0 regs2 (ma_vals fr n B2) (ma_agree regs2 B2) RK.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
    pose proof (ma_chunk E0 Wc ss m 0%nat _ 0%nat 96 4%N (SOff 32 0) (TW.u_at B2 TW.A_M_fly_on 4) TB_M HS eq_refl
      U9 eq_refl D32' ltac:(cbn; lia)) as VF;
    apply (ma_exit Wc ly2 S2 (MRX_PC OFF_TICK) _ (R_TICK Bw' r) (ms_regs m) (ms_mem m) _ B2) end.
  - rewrite (mrx_pcv OFF_TICK). reflexivity.
  - exact KTICK.
  - exact HJ.
  - exact Hfrm.
  - exact Hperm.
  - exact Hmo.
  - exact (eq_trans (RK 2%bv ltac:(AB.mb_in)) Hsp).
  - exact (eq_trans (RK 3%bv ltac:(AB.mb_in)) Hgp).
  - exact (eq_trans (RK 4%bv ltac:(AB.mb_in)) Htp).
  - exact (ma_hi_of _ _ RK Hhi).
  - exact (ma_saved_kept Wc mem2 _ (ma_KA_mono _ _ _ _ _ ma_X02 KA) Hsav).
  - apply (tw_kept TMAP_B (aview segs (w_H Wc) mem2) _ B2 Htw). exact (ma_rest0 Wc mem2 _ B2 Htw KA VF).
  - unfold R_TICK. split; [exact TK | exact Er]. }
rewrite D36, D33 in Hc. rewrite AB.mbl_ne_sw in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Heq.
destruct (ma_ack_eq fr n B2 B3 LB2 Hfl Heq HACK) as (NI & HMO6 & HB6).
(* OW.acked, OW.acked_counter and OW.acked_retry join the state *)
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
  pose proof (ma_val_kept Wc maX0 mem2 (ms_mem m) (TB_OW + 216) 4 _ KA ltac:(unfold TB_OW; lia)
    ltac:(unfold TB_OW; lia) ltac:(unfold maX0, TB_M, TB_OW; intros; lia) Vack0) as Vack end.
ma_mono KA ma_X01.
ma_add HS ma_ack (ma_ack_ok E0 Wc _ B2 UOW E35 Vack) Usp U9 UOW.
ma_add0 HS ma_acc ma_acc_ok UOW Usp U9 UOW.
clear Vack.
(* +0x174 - +0x184: a2 = &OW, a4 = OW.acked, a3 = OW.acked + 1 (addiw), `blt a3, a4` to the trap word *)
ma_step maX1.
ma_br.
{ (* OW.acked = INT_MAX: int_inc is None there, so the model premise refutes the branch *)
  exfalso. rewrite DA1, D35 in Hc.
  cbn [branch_taken] in Hc.
  rewrite UMR.mr_lts in Hc by (pose proof (UMR.mr_swrap32_range (TW.OW_acked B2 + 1)); lia).
  rewrite UMR.mr_inc_trap in Hc by lia. apply Z.eqb_eq in Hc. apply NI. unfold TC.INT_MAX. exact Hc. }
clear Hc.
(* +0x188 - +0x1a0: a5 = M.fly.retries, a4 = 1, the stores of OW.acked + 1, f.ack, M.fly.retries and 0 at M.fly.on,
   `bne a0, a4` *)
ma_step maX1.
ma_br.
{ (* M.state <> S_WAKING: m_tick *)
  rewrite D10 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_ne in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
  rename Hc into Hs1.
  pose proof (HB6 Hs1) as EB3. subst B3.
  ma_stepto maX1 (AF_m_rx + OFF_TICK).
  pmkst HS.
  ma_rk HS E0 regs2 (ma_vals fr n B2) (ma_agree regs2 B2) RK.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
    pose proof (ma_chunk E0 Wc ss m 1%nat _ 0%nat 216 4%N _ (bv_swrap 32 (TW.OW_acked B2 + 1)) TB_OW HS eq_refl UOW
      eq_refl DA1 ltac:(cbn; lia)) as VA;
    pose proof (ma_chunk E0 Wc ss m 0%nat _ 1%nat 224 4%N _ (bv_swrap 32 (DSpec.sf_ack (mrx_f fr n))) TB_OW HS
      eq_refl UOW eq_refl D36 ltac:(cbn; lia)) as VC;
    pose proof (ma_chunk E0 Wc ss m 0%nat _ 0%nat 228 4%N _ (bv_swrap 32 (TW.M_fly_retries B2)) TB_OW HS eq_refl
      UOW eq_refl D34 ltac:(cbn; lia)) as VR;
    pose proof (ma_chunk E0 Wc ss m 2%nat _ 0%nat 96 4%N (SLit 0) 0 TB_M HS eq_refl U9 eq_refl eq_refl
      ltac:(cbn; lia)) as VF;
    apply (ma_exit Wc ly2 S2 (MRX_PC OFF_TICK) _ (R_TICK Bw' r) (ms_regs m) (ms_mem m) _ (AB.mb_B6 B2)) end.
  - rewrite (mrx_pcv OFF_TICK). reflexivity.
  - exact KTICK.
  - exact HJ.
  - exact Hfrm.
  - exact Hperm.
  - exact Hmo.
  - exact (eq_trans (RK 2%bv ltac:(AB.mb_in)) Hsp).
  - exact (eq_trans (RK 3%bv ltac:(AB.mb_in)) Hgp).
  - exact (eq_trans (RK 4%bv ltac:(AB.mb_in)) Htp).
  - exact (ma_hi_of _ _ RK Hhi).
  - exact (ma_saved_kept Wc mem2 _ (ma_KA_mono _ _ _ _ _ ma_X12 KA) Hsav).
  - unfold AB.mb_B6.
    apply (ma_w6 (aview segs (w_H Wc) mem2) _ B2 (TW.OW_acked B2 + 1) (TW.M_fly_counter B2) (TW.M_fly_retries B2)
      Htw).
    + intros j Hj. rewrite (VA j Hj). f_equal. apply AB.mb_le_byte_mod. apply EPI.mrx_swrap_mod.
    + intros j Hj. rewrite (VC j Hj), Heq. f_equal. apply AB.mb_le_byte_mod. apply EPI.mrx_swrap_mod.
    + intros j Hj. rewrite (VR j Hj). f_equal. apply AB.mb_le_byte_mod. apply EPI.mrx_swrap_mod.
    + exact VF.
    + intros x Hx HN. exact (KA x (ma_tw_in_rng x Hx) HN).
  - unfold R_TICK. split; [exact TK | exact Er]. }
rewrite D10 in Hc. cbn [sv_denot] in Hc. rewrite AB.mbl_ne in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
rename Hc into Hs1.
pose proof (HMO6 Hs1) as HMOB.
(* S_WAKING: +0x1a4 - +0x1a8, M.e2_acked = 1, `j` to MO (the call of m_maybe_online) *)
ma_mono KA ma_X12.
ma_add0 HS ma_e2 ma_e2_ok U9 Usp U9 UOW.
ma_stepto maX2 (AF_m_rx + OFF_MO).
pmkst HS.
ma_rk HS E0 regs2 (ma_vals fr n B2) (ma_agree regs2 B2) RK.
lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
  pose proof (ma_chunk E0 Wc ss m 2%nat _ 0%nat 216 4%N _ (bv_swrap 32 (TW.OW_acked B2 + 1)) TB_OW HS eq_refl UOW
    eq_refl DA1 ltac:(cbn; lia)) as VA;
  pose proof (ma_chunk E0 Wc ss m 1%nat _ 1%nat 224 4%N _ (bv_swrap 32 (DSpec.sf_ack (mrx_f fr n))) TB_OW HS
    eq_refl UOW eq_refl D36 ltac:(cbn; lia)) as VC;
  pose proof (ma_chunk E0 Wc ss m 1%nat _ 0%nat 228 4%N _ (bv_swrap 32 (TW.M_fly_retries B2)) TB_OW HS eq_refl
    UOW eq_refl D34 ltac:(cbn; lia)) as VR;
  pose proof (ma_chunk E0 Wc ss m 3%nat _ 0%nat 96 4%N (SLit 0) 0 TB_M HS eq_refl U9 eq_refl eq_refl
    ltac:(cbn; lia)) as VF;
  pose proof (ma_chunk E0 Wc ss m 0%nat _ 0%nat 16 4%N (SLit 1) 1 TB_M HS eq_refl U9 eq_refl eq_refl
    ltac:(cbn; lia)) as VE;
  apply (ma_exit Wc ly2 S2 (MRX_PC OFF_MO) _ (R_MO Bw' r) (ms_regs m) (ms_mem m) _
    (TW.set_M_e2_acked (AB.mb_B6 B2) 1)) end.
- rewrite (mrx_pcv OFF_MO). reflexivity.
- exact KMO.
- exact HJ.
- exact Hfrm.
- exact Hperm.
- exact Hmo.
- exact (eq_trans (RK 2%bv ltac:(AB.mb_in)) Hsp).
- exact (eq_trans (RK 3%bv ltac:(AB.mb_in)) Hgp).
- exact (eq_trans (RK 4%bv ltac:(AB.mb_in)) Htp).
- exact (ma_hi_of _ _ RK Hhi).
- exact (ma_saved_kept Wc mem2 _ KA Hsav).
- unfold AB.mb_B6.
  apply (ma_w7 (aview segs (w_H Wc) mem2) _ B2 (TW.OW_acked B2 + 1) (TW.M_fly_counter B2) (TW.M_fly_retries B2)
    Htw).
  + intros j Hj. rewrite (VA j Hj). f_equal. apply AB.mb_le_byte_mod. apply EPI.mrx_swrap_mod.
  + intros j Hj. rewrite (VC j Hj), Heq. f_equal. apply AB.mb_le_byte_mod. apply EPI.mrx_swrap_mod.
  + intros j Hj. rewrite (VR j Hj). f_equal. apply AB.mb_le_byte_mod. apply EPI.mrx_swrap_mod.
  + exact VF.
  + exact VE.
  + intros x Hx HN. exact (KA x (ma_tw_in_rng x Hx) HN).
- unfold R_MO. exists B3. split; [exact HMOB|]. split; [exact TK | exact Er].
Qed.

End seg.
