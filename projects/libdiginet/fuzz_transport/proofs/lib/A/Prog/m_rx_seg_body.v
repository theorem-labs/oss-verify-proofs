(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v; 1274 of its 1393 lines of code are new or changed and 911 lines of the source are left out. *)
(* m_rx_seg_body: the BODY segment of the image-A walk of m_rx (lib/A/Prog/m_rx_seg_kit.v): from the cut BODY
   (0x84b70) to the cuts EPI, TICK, MO, LOST, DATA, HOST and ANNT. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
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
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the cut                                       *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the cut, 32 the shadow base (no shadow entry: no instrumented check here), 33 the
   4 bytes of M.state, 34 g_now, 35 .. 37 the 4 bytes of M.fly.on, M.fly.counter, M.fly.retries, 38 those of
   OW.acked, 39 / 40 the frame bytes 25 / 24 spilled at sp + 16 / sp + 24. Regions: the two spills, M.state (based on
   s3 = &M, atom 19), g_now (object 27); added on the paths that touch them: M.last_rx, M.fly (on / counter / retries),
   OW.acked, OW.acked_counter with OW.acked_retry (object 12), M.e2_acked. *)
Definition mb_sp : YP09.region := YP09.mkRegion (Some 2%nat) 16 32 0 0
  [YP09.mkChunk 16 (YP09.CVal 8 (SOff 39 0)); YP09.mkChunk 24 (YP09.CVal 8 (SOff 40 0))].
Definition mb_st : YP09.region := YP09.mkRegion (Some 19%nat) 12 16 0 0 [YP09.mkChunk 12 (YP09.CVal 4 (SOff 33 0))].
Definition mb_now : YP09.region := YP09.mkRegion (Some (A_OBJ 27)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff 34 0))].
Definition mb_lrx : YP09.region := YP09.mkRegion (Some 19%nat) 32 40 32 40 [].
Definition mb_fly : YP09.region := YP09.mkRegion (Some 19%nat) 96 112 96 100
  [YP09.mkChunk 96 (YP09.CVal 4 (SOff 35 0)); YP09.mkChunk 104 (YP09.CVal 4 (SOff 36 0));
   YP09.mkChunk 108 (YP09.CVal 4 (SOff 37 0))].
Definition mb_ack : YP09.region := YP09.mkRegion (Some (A_OBJ 12)) 216 220 216 220
  [YP09.mkChunk 216 (YP09.CVal 4 (SOff 38 0))].
Definition mb_acc : YP09.region := YP09.mkRegion (Some (A_OBJ 12)) 224 232 224 232 [].
Definition mb_e2 : YP09.region := YP09.mkRegion (Some 19%nat) 16 20 16 20 [].
Definition mb_regions : smem := [mb_sp; mb_st; mb_now].
Definition mb_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (19%nat, mkAF TA_M TA_M 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (A_OBJ 12, mkAF TA_OW TA_OW 5)] [] [].
Definition ss_mb : sstate := mkSS (AF_m_rx + OFF_BODY) sr_atoms mb_regions None mb_facts.
Definition MB_SH : list shent := [].
Definition MB_Bx : sv := SOff 32 0.

Definition mb_vals (fr : TI.tframe) (Bw : list byte) : list word :=
  [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4); Z_to_bv 64 (TW.g_now Bw);
   Z_to_bv 64 (TW.u_at Bw TW.A_M_fly_on 4); Z_to_bv 64 (TW.u_at Bw TW.A_M_fly_counter 4);
   Z_to_bv 64 (TW.u_at Bw TW.A_M_fly_retries 4); Z_to_bv 64 (TW.u_at Bw TW.A_OW_acked 4);
   Z_to_bv 64 (mfb fr 25); Z_to_bv 64 (mfb fr 24)].

(* The windows the runs may write, by stage. *)
Definition mbX0 (a : Z) : Prop := False.
Definition mbX1 (a : Z) : Prop := TA_M + 32 <= a < TA_M + 40.
Definition mbX2 (a : Z) : Prop := mbX1 a \/ TA_M + 96 <= a < TA_M + 100.
Definition mbX3 (a : Z) : Prop := mbX2 a \/ TA_OW + 216 <= a < TA_OW + 220 \/ TA_OW + 224 <= a < TA_OW + 232.
Definition mbX4 (a : Z) : Prop := mbX3 a \/ TA_M + 16 <= a < TA_M + 20.

Lemma mb_inG : forall a, (TA_M <= a < TA_M + 1648) \/ (TA_OW <= a < TA_OW + 304) -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. destruct Ha as [Ha|Ha].
- exists (TA_M, TW.SZ_M). split; [exact (TMAP_A_in_G _ _ _ TMAP_A_M) | unfold in_zr, TW.SZ_M; cbn [fst snd]; lia].
- exists (TA_OW, TW.SZ_OW). split; [exact (TMAP_A_in_G _ _ _ TMAP_A_OW) | unfold in_zr, TW.SZ_OW; cbn [fst snd]; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* Values the code forms, at a valuation                               *)
(* ------------------------------------------------------------------ *)

Lemma mb_land_split : forall a b k, 0 <= k -> 0 <= b < 2 ^ k -> Z.land (a * 2 ^ k) b = 0.
Proof.
intros a b k Hk Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec i k) as [Hl|Hl].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.bits_0; apply andb_false_r|].
  assert (Hl2 : Z.log2 b < k) by (apply Z.log2_lt_pow2; lia).
  rewrite (Z.bits_above_log2 b i) by lia. apply andb_false_r.
Qed.

Lemma mb_lor_add : forall a b k, 0 <= k -> 0 <= b < 2 ^ k -> Z.lor (a * 2 ^ k) b = a * 2 ^ k + b.
Proof.
intros a b k Hk Hb. pose proof (mb_land_split a b k Hk Hb) as H0.
rewrite <- (Z.lxor_lor _ _ H0). rewrite (Z.add_nocarry_lxor _ _ H0). reflexivity.
Qed.

Lemma mb_z2bv_wrap : forall z, Z_to_bv 64 (bv_wrap 64 z) = Z_to_bv 64 z.
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. apply Zmod_mod. Qed.

Lemma mb_z2bv_zcanon : forall z, Z_to_bv 64 (zcanon z) = Z_to_bv 64 z.
Proof. intros z. rewrite zcanon_wrap. apply mb_z2bv_wrap. Qed.

Lemma mb_swrap32_congr : forall x y, x mod 2 ^ 32 = y mod 2 ^ 32 -> bv_swrap 32 x = bv_swrap 32 y.
Proof.
intros x y H. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite (Zplus_mod x), (Zplus_mod y), H. reflexivity.
Qed.

Lemma mb_le_byte_mod : forall x y j, x mod 2 ^ 32 = y mod 2 ^ 32 -> YO0f.le_byte x 4 j = YO0f.le_byte y 4 j.
Proof. intros x y j H. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32. rewrite H. reflexivity. Qed.

(* The sign-extended 4-byte load of an atom holding the unsigned int u. *)
Lemma mbd_sext : forall E k u, ew E k = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff k 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E k u Hk Hu. cbn [sv_denot]. rewrite Hk, Z.add_0_r, Z_to_bv_bv_unsigned.
change (sext 64 (bv_extract 0 32 (Z_to_bv 64 u))) with (Z_to_bv 64 (bv_signed (bv_extract 0 32 (Z_to_bv 64 u)))).
f_equal. rewrite (LMem.signed_of_extract 32 (Z_to_bv 64 u)) by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma mbd_off : forall E k v z, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff k z) = Z_to_bv 64 (v + z).
Proof. intros E k v z Hk Hv. cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hv. reflexivity. Qed.

Lemma mbd_add_den : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma mbd_add : forall E k u z, ew E k = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff k 0)) (SLit z)) = Z_to_bv 64 (bv_swrap 32 u + z).
Proof.
intros E k u z Hk Hu.
change (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff k 0)) (SLit z)))
  with (alu64 ALU_ADD (sv_denot E (SExt true 32 (SOff k 0))) (Z_to_bv 64 z)).
rewrite (mbd_sext E k u Hk Hu). apply mbd_add_den.
Qed.

(* addiw a0, a5, -1 on the sign-extended M.state (0x84c70). *)
Lemma mbd_state12 : forall E u, ew E 33%nat = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SAluw ALU_ADD (SExt true 32 (SOff 33 0)) (SLit (-1))) =
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 u)) + -1)).
Proof.
intros E u Hk Hu. rewrite denot_lit_U, U_of_S, S_SAluw, mb_z2bv_wrap. cbn [zalu_raw].
rewrite U_SExt, U_SLit, U_SOff, Hk, unsigned_lit_small, Z.add_0_r by lia.
change (Z.of_N 32) with 32. f_equal. apply mb_swrap32_congr.
rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
Z.div_mod_to_equations. lia.
Qed.

(* The ack field the code assembles at 0x84c0c - 0x84c2c (slliw byte 22, 24; slli byte 23, 16; ld spill 24, slli 8;
   ld spill 16; or): the sign-extended 32-bit big-endian word. *)
Definition mb_ackx : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 26 0) (SLit 16)) (SAluw ALU_SLL (SOff 22 0) (SLit 24)))
    (SAlu ALU_OR (SAlu ALU_SLL (SOff 40 0) (SLit 8)) (SOff 39 0)).

Lemma mbd_ack : forall E x22 x23 x24 x25,
  ew E 22%nat = Z_to_bv 64 x22 -> ew E 26%nat = Z_to_bv 64 x23 -> ew E 40%nat = Z_to_bv 64 x24 ->
  ew E 39%nat = Z_to_bv 64 x25 ->
  0 <= x22 < 256 -> 0 <= x23 < 256 -> 0 <= x24 < 256 -> 0 <= x25 < 256 ->
  sv_denot E mb_ackx = Z_to_bv 64 (bv_swrap 32 (x22 * 2 ^ 24 + x23 * 2 ^ 16 + x24 * 2 ^ 8 + x25)).
Proof.
intros E x22 x23 x24 x25 E22 E26 E40 E39 R22 R23 R24 R25.
assert (UO : forall k x, ew E k = Z_to_bv 64 x -> 0 <= x < 256 -> U E (SOff k 0) = x).
{ intros k x Hk Hx. rewrite U_SOff, Hk, unsigned_lit_small, Z.add_0_r by lia. apply zcanon_id. unfold M64. lia. }
assert (HQ : bv_wrap 64 (bv_swrap 32 (x22 * 2 ^ 24)) = (if x22 <? 128 then x22 else x22 + 2 ^ 40 - 2 ^ 8) * 2 ^ 24).
{ unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.ltb_spec x22 128); Z.div_mod_to_equations; lia. }
rewrite denot_lit_U. unfold mb_ackx.
rewrite !U_SAlu. rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw].
rewrite !U_SLit, (UO 26%nat x23 E26 R23), (UO 22%nat x22 E22 R22), (UO 40%nat x24 E40 R24), (UO 39%nat x25 E39 R25).
change (Z.land (zcanon 16) 63) with 16. change (Z.land (zcanon 8) 63) with 8.
change (Z.land (zcanon 24 mod 2 ^ 32) 31) with 24.
rewrite !Z.shiftl_mul_pow2 by lia.
rewrite (Z.mod_small x22 (2 ^ 32)) by lia. rewrite HQ.
rewrite (zcanon_id (x23 * 2 ^ 16)), (zcanon_id (x24 * 2 ^ 8)) by (unfold M64; lia).
rewrite (mb_lor_add x24 x25 8) by lia.
rewrite (Z.lor_comm (x23 * 2 ^ 16)).
set (q := if x22 <? 128 then x22 else x22 + 2 ^ 40 - 2 ^ 8).
rewrite (mb_lor_add q (x23 * 2 ^ 16) 24) by lia.
assert (Hq : 0 <= q < 2 ^ 40) by (unfold q; destruct (Z.ltb_spec x22 128); lia).
rewrite (zcanon_id (q * 2 ^ 24 + x23 * 2 ^ 16)) by (unfold M64; lia).
rewrite (zcanon_id (x24 * 2 ^ 8 + x25)) by (unfold M64; lia).
replace (q * 2 ^ 24 + x23 * 2 ^ 16) with ((q * 2 ^ 8 + x23) * 2 ^ 16) by ring.
rewrite (mb_lor_add (q * 2 ^ 8 + x23) (x24 * 2 ^ 8 + x25) 16) by lia.
rewrite <- mb_z2bv_zcanon. rewrite <- (mb_z2bv_zcanon (bv_swrap 32 _)). f_equal.
unfold zcanon, M64, q, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec x22 128); Z.div_mod_to_equations; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Branch conditions on literals                                       *)
(* ------------------------------------------------------------------ *)

Lemma mbl_eq : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  branch_taken BC_EQ (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. exact (EPI.mrxk_eqb a b Ha Hb). Qed.
Lemma mbl_ne : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  branch_taken BC_NE (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a =? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. rewrite (EPI.mrxk_eqb a b Ha Hb). reflexivity. Qed.
Lemma mbl_ge : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  branch_taken BC_GE (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. rewrite (EPI.mrxk_lts a b Ha Hb). reflexivity. Qed.
Lemma mbl_ltu : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  branch_taken BC_LTU (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. exact (EPI.mrxk_ltu a b Ha Hb). Qed.
Lemma mbl_geu_ann : forall c, 0 <= c < 256 ->
  branch_taken BC_GEU (Z_to_bv 64 (c + -224)) (Z_to_bv 64 2) = negb ((c =? 224) || (c =? 225)).
Proof.
intros c Hc. cbn [branch_taken]. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). f_equal.
destruct (Z.eqb_spec c 224) as [E1|E1]; [subst c; reflexivity|].
destruct (Z.eqb_spec c 225) as [E2|E2]; [subst c; reflexivity|]. cbn [orb].
apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.
Lemma mbl_ne_sw : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  branch_taken BC_NE (Z_to_bv 64 (bv_swrap 32 a)) (Z_to_bv 64 (bv_swrap 32 b)) = negb (a =? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. rewrite (EPI.mrx_eqb_sw a b Ha Hb). reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The model                                                           *)
(* ------------------------------------------------------------------ *)

(* A goal a = a closed only when both sides are the same term (no conversion on worlds). *)
Ltac mb_refl := lazymatch goal with |- ?a = ?a => exact (eq_refl a) end.

Lemma mbm_pair_inv : forall (x y : list byte) (a b : Z), Some (x, a) = Some (y, b) -> y = x /\ b = a.
Proof. intros x y a b H. injection H as H1 H2. split; symmetry; assumption. Qed.
Lemma mbm_some_inv : forall x y : list byte, Some (x, tt) = Some (y, tt) -> y = x.
Proof. intros x y H. injection H as H. symmetry. exact H. Qed.

Lemma mbm_closed : forall I fr Bw B' r', TW.M_state Bw = TC.S_CLOSED -> EPI.mrx_k I fr Bw = Some (B', r') ->
  B' = Bw /\ r' = 0.
Proof.
intros I fr Bw B' r' H Hk. unfold EPI.mrx_k in Hk. rewrite H, Z.eqb_refl in Hk. cbv beta iota in Hk.
exact (mbm_pair_inv _ _ _ _ Hk).
Qed.

Lemma mbm_open : forall I fr Bw B' r', TW.M_state Bw <> TC.S_CLOSED -> EPI.mrx_k I fr Bw = Some (B', r') ->
  exists B3, EPI.mrx_sw I fr (TW.set_M_last_rx Bw (TW.g_now Bw)) = Some (B3, tt) /\
    TC.m_tick_m B3 = Some (B', tt) /\ r' = 1.
Proof.
intros I fr Bw B' r' H Hk. unfold EPI.mrx_k in Hk. rewrite (proj2 (Z.eqb_neq _ _) H) in Hk. revert Hk.
destruct (EPI.mrx_sw I fr (TW.set_M_last_rx Bw (TW.g_now Bw))) as [[B3 []]|] eqn:SW; intros Hk;
  cbv beta iota in Hk; [|discriminate Hk].
revert Hk. destruct (TC.m_tick_m B3) as [[B4 []]|] eqn:TK; intros Hk; cbv beta iota in Hk; [|discriminate Hk].
destruct (mbm_pair_inv _ _ _ _ Hk) as [-> ->]. exists B3.
split; [first [mb_refl | exact SW]|]. split; [first [mb_refl | exact TK] | mb_refl].
Qed.


Lemma mbm_sw_data : forall I fr B2, mfb fr 28 = 0 -> EPI.mrx_sw I fr B2 = EPI.mrx_data fr B2.
Proof.
intros I fr B2 H. unfold EPI.mrx_sw. change (EPI.mrx_fc fr) with (mfb fr 28). rewrite H.
change ((0 =? TC.SPEC_CMD_E0) || (0 =? TC.SPEC_CMD_E1)) with false. change (0 =? TC.SPEC_CMD_ACK) with false.
change (0 =? TC.SPEC_CMD_DATA) with true. cbv beta iota. mb_refl.
Qed.
Lemma mbm_sw_ack : forall I fr B2, mfb fr 28 = 0xa0 -> EPI.mrx_sw I fr B2 = EPI.mrx_ackb fr B2.
Proof.
intros I fr B2 H. unfold EPI.mrx_sw. change (EPI.mrx_fc fr) with (mfb fr 28). rewrite H.
change ((160 =? TC.SPEC_CMD_E0) || (160 =? TC.SPEC_CMD_E1)) with false. change (160 =? TC.SPEC_CMD_ACK) with true.
cbv beta iota. mb_refl.
Qed.
Lemma mbm_sw_e3 : forall I fr B2, mfb fr 28 = 0xe3 -> EPI.mrx_sw I fr B2 =
  if (TW.M_state B2 =? TC.S_ONLINE) || (TW.M_state B2 =? TC.S_WAKING) then TC.m_lost_m B2 TC.R_DESK_DISCONNECT
  else Some (B2, tt).
Proof.
intros I fr B2 H. unfold EPI.mrx_sw. change (EPI.mrx_fc fr) with (mfb fr 28). rewrite H.
change ((227 =? TC.SPEC_CMD_E0) || (227 =? TC.SPEC_CMD_E1)) with false. change (227 =? TC.SPEC_CMD_ACK) with false.
change (227 =? TC.SPEC_CMD_DATA) with false. change (227 =? TC.SPEC_CMD_E3) with true.
cbv beta iota. mb_refl.
Qed.
Lemma mbm_sw_ann : forall I fr B2, mfb fr 28 = 0xe0 \/ mfb fr 28 = 0xe1 -> EPI.mrx_sw I fr B2 = EPI.mrx_ann I fr B2.
Proof.
intros I fr B2 [H|H]; unfold EPI.mrx_sw; change (EPI.mrx_fc fr) with (mfb fr 28); rewrite H.
- change ((224 =? TC.SPEC_CMD_E0) || (224 =? TC.SPEC_CMD_E1)) with true. cbv beta iota. mb_refl.
- change ((225 =? TC.SPEC_CMD_E0) || (225 =? TC.SPEC_CMD_E1)) with true. cbv beta iota. mb_refl.
Qed.
Lemma mbm_sw_none : forall I fr B2, mfb fr 28 <> 0 -> mfb fr 28 <> 0xa0 -> mfb fr 28 <> 0xe0 -> mfb fr 28 <> 0xe1 ->
  mfb fr 28 <> 0xe3 -> EPI.mrx_sw I fr B2 = Some (B2, tt).
Proof.
intros I fr B2 H0 Ha He0 He1 He3. unfold EPI.mrx_sw. change (EPI.mrx_fc fr) with (mfb fr 28).
unfold TC.SPEC_CMD_E0, TC.SPEC_CMD_E1, TC.SPEC_CMD_ACK, TC.SPEC_CMD_DATA, TC.SPEC_CMD_E3.
rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) He0),
  (proj2 (Z.eqb_neq _ _) He1), (proj2 (Z.eqb_neq _ _) He3).
cbn [orb]. mb_refl.
Qed.

Lemma mbm_ann_short : forall I fr B2, EPI.mrx_blen fr < TC.SPEC_ANN_MIN -> EPI.mrx_ann I fr B2 = Some (B2, tt).
Proof. intros I fr B2 H. unfold EPI.mrx_ann. rewrite (proj2 (Z.ltb_lt _ _) H). cbv beta iota. mb_refl. Qed.
Lemma mbm_ann_e0 : forall I fr B2, TC.SPEC_ANN_MIN <= EPI.mrx_blen fr -> mfb fr 28 = 0xe0 ->
  EPI.mrx_ann I fr B2 = EPI.mrx_ann_tail I fr B2 (-1).
Proof.
intros I fr B2 H He. unfold EPI.mrx_ann. rewrite (proj2 (Z.ltb_ge _ _) H).
change (EPI.mrx_fc fr) with (mfb fr 28). rewrite He. change (224 =? TC.SPEC_CMD_E1) with false.
cbv beta iota. mb_refl.
Qed.

Lemma mbm_ack_off : forall fr B2, TW.M_fly_on B2 = 0 -> EPI.mrx_ackb fr B2 = Some (B2, tt).
Proof.
intros fr B2 H. unfold EPI.mrx_ackb, TC.truth. rewrite H. change (negb (0 =? 0)) with false. cbn [andb]. mb_refl.
Qed.
Lemma mbm_ack_ne : forall fr B2, EPI.mrx_ack fr <> TW.M_fly_counter B2 -> EPI.mrx_ackb fr B2 = Some (B2, tt).
Proof.
intros fr B2 H. unfold EPI.mrx_ackb. rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. cbv beta iota. mb_refl.
Qed.

(* Reads of a world through a store elsewhere. *)
Ltac mbm_unf := unfold TW.A_M_state, TW.A_M_e2_acked, TW.A_M_last_rx, TW.A_M_fly_on, TW.A_M_fly_counter,
  TW.A_M_fly_retries, TW.A_OW_acked, TW.A_OW_acked_counter, TW.A_OW_acked_retry, TW.OFF_M, TW.OFF_OW,
  TW.OFF_g_now, TW.W_LEN in *.
Lemma mbm_lenp : forall Bw k (n : nat) v, Z.of_nat (length Bw) = TW.W_LEN -> 0 <= k -> k + Z.of_nat n <= TW.W_LEN ->
  Z.of_nat (length (TW.upd Bw k (TW.put n v))) = TW.W_LEN.
Proof. intros Bw k n v HL Hk Hn. rewrite TWL.length_upd_put; [exact HL | exact Hk | lia]. Qed.
Lemma mbm_u_out : forall Bw k (n : nat) v k' (m : nat), Z.of_nat (length Bw) = TW.W_LEN -> 0 <= k -> 0 <= k' ->
  k + Z.of_nat n <= TW.W_LEN -> (k' + Z.of_nat m <= k \/ k + Z.of_nat n <= k') ->
  TW.u_at (TW.upd Bw k (TW.put n v)) k' m = TW.u_at Bw k' m.
Proof. intros. apply TWL.u_at_upd_out; rewrite ?TWL.length_put; lia. Qed.
Ltac mbm_len HL := repeat (apply mbm_lenp; [ | mbm_unf; lia | mbm_unf; lia]); exact HL.
(* Each read u_at (upd B k (put n v)) k' m found syntactically is rewritten with the lemma fully instantiated (no
   unification against world terms). *)
Ltac mbm_rw HL :=
  repeat lazymatch goal with
  | |- context [TW.u_at (TW.upd ?B ?k (TW.put ?n ?v)) ?k' ?m] =>
      let HB := fresh "HB" in
      assert (HB : Z.of_nat (length B) = TW.W_LEN) by (mbm_len HL);
      rewrite (mbm_u_out B k n v k' m HB ltac:(mbm_unf; lia) ltac:(mbm_unf; lia) ltac:(mbm_unf; lia)
        ltac:(mbm_unf; lia));
      clear HB
  end.

(* The world after the stores of cmd ACK (fuzz_transport.c:333-337), from the world B2 after M.last_rx. *)
Definition mb_B6 (B2 : list byte) : list byte :=
  TW.set_M_fly_on (TW.set_OW_acked_retry (TW.set_OW_acked_counter (TW.set_OW_acked B2 (TW.OW_acked B2 + 1))
    (TW.M_fly_counter B2)) (TW.M_fly_retries B2)) 0.

Lemma mbm_ack_eq : forall fr B2 B3, Z.of_nat (length B2) = TW.W_LEN -> TW.M_fly_on B2 <> 0 ->
  EPI.mrx_ack fr = TW.M_fly_counter B2 -> EPI.mrx_ackb fr B2 = Some (B3, tt) ->
  TW.OW_acked B2 <> TC.INT_MAX /\
  (TW.M_state B2 = 1 -> TC.m_maybe_online_m (TW.set_M_e2_acked (mb_B6 B2) 1) = Some (B3, tt)) /\
  (TW.M_state B2 <> 1 -> B3 = mb_B6 B2).
Proof.
intros fr B2 B3 HL H1 H2 Hk. unfold EPI.mrx_ackb, TC.truth in Hk.
rewrite (proj2 (Z.eqb_neq _ _) H1), H2, Z.eqb_refl in Hk. cbn [negb andb] in Hk.
revert Hk. unfold TC.int_inc.
destruct (Z.eqb_spec (TW.OW_acked B2) TC.INT_MAX) as [EI|NI]; intros Hk; cbv beta iota zeta in Hk; [discriminate Hk|].
assert (EC : TW.M_fly_counter (TW.set_OW_acked B2 (TW.OW_acked B2 + 1)) = TW.M_fly_counter B2)
  by (unfold TW.M_fly_counter, TW.set_OW_acked; mbm_rw HL; mb_refl).
rewrite EC in Hk.
assert (ER : TW.M_fly_retries (TW.set_OW_acked_counter (TW.set_OW_acked B2 (TW.OW_acked B2 + 1)) (TW.M_fly_counter B2))
  = TW.M_fly_retries B2)
  by (unfold TW.M_fly_retries, TW.set_OW_acked_counter, TW.set_OW_acked; mbm_rw HL; mb_refl).
rewrite ER in Hk.
assert (ES : TW.M_state (TW.set_M_fly_on (TW.set_OW_acked_retry (TW.set_OW_acked_counter (TW.set_OW_acked B2
  (TW.OW_acked B2 + 1)) (TW.M_fly_counter B2)) (TW.M_fly_retries B2)) 0) = TW.M_state B2)
  by (unfold TW.M_state, TW.s32_at, TW.set_M_fly_on, TW.set_OW_acked_retry, TW.set_OW_acked_counter, TW.set_OW_acked;
      mbm_rw HL; mb_refl).
rewrite ES in Hk. unfold TC.S_WAKING in Hk. unfold mb_B6.
split; [exact NI|]. split.
- intros Hs. rewrite Hs, Z.eqb_refl in Hk. cbv beta iota in Hk. exact Hk.
- intros Hs. rewrite (proj2 (Z.eqb_neq _ _) Hs) in Hk. cbv beta iota in Hk. exact (mbm_some_inv _ _ Hk).
Qed.

(* The reads of the world after M.last_rx. *)
Lemma mbm_B2 : forall B1, Z.of_nat (length B1) = TW.W_LEN ->
  Z.of_nat (length (TW.set_M_last_rx B1 (TW.g_now B1))) = TW.W_LEN /\
  TW.M_state (TW.set_M_last_rx B1 (TW.g_now B1)) = TW.M_state B1 /\
  TW.g_now (TW.set_M_last_rx B1 (TW.g_now B1)) = TW.g_now B1 /\
  TW.M_fly_on (TW.set_M_last_rx B1 (TW.g_now B1)) = TW.M_fly_on B1 /\
  TW.M_fly_counter (TW.set_M_last_rx B1 (TW.g_now B1)) = TW.M_fly_counter B1 /\
  TW.M_fly_retries (TW.set_M_last_rx B1 (TW.g_now B1)) = TW.M_fly_retries B1 /\
  TW.OW_acked (TW.set_M_last_rx B1 (TW.g_now B1)) = TW.OW_acked B1.
Proof.
intros B1 HL. unfold TW.set_M_last_rx.
split; [mbm_len HL|].
unfold TW.M_state, TW.g_now, TW.M_fly_on, TW.M_fly_counter, TW.M_fly_retries, TW.OW_acked, TW.s32_at.
mbm_rw HL. repeat split; mb_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* The world relation at the exits                                     *)
(* ------------------------------------------------------------------ *)

Lemma mb_tw_in_rng : forall x, tw_in TMAP_A x -> 0 <= x < 2 ^ 64.
Proof.
intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. lia.
Qed.

Ltac mb_unP HP := mrx_unP HP; try change (Z.of_nat 8) with 8 in *; try change (Z.of_nat 4) with 4 in *.

(* M.last_rx = g_now. *)
Lemma mb_w2 : forall rd0 rdF Bw, tw_at TMAP_A rd0 Bw ->
  (forall j, (j < 8)%nat -> rdF (TA_M + 32 + Z.of_nat j) = Some (YO0f.le_byte (TW.g_now Bw) 8 j)) ->
  (forall x, tw_in TMAP_A x -> ~ mbX1 x -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.set_M_last_rx Bw (TW.g_now Bw)).
Proof.
intros rd0 rdF Bw H V1 Hk. unfold TW.set_M_last_rx.
pose proof (mrx_tw_start rdF rd0 Bw H) as H0.
pose proof (mrx_tw_step rdF rd0 _ Bw TW.OFF_M TA_M TW.SZ_M 32 TW.A_M_last_rx 8 (TW.g_now Bw) H0 TMAP_A_M
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_M; lia) V1) as H1.
apply (mrx_tw_end rdF rd0 _ _ H1). intros x Hx HP. mb_unP HP. apply Hk; [exact Hx | unfold mbX1; lia].
Qed.

(* and the stores of cmd ACK. *)
Lemma mb_w6 : forall rd0 rdF Bw a c rt, tw_at TMAP_A rd0 Bw ->
  (forall j, (j < 8)%nat -> rdF (TA_M + 32 + Z.of_nat j) = Some (YO0f.le_byte (TW.g_now Bw) 8 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 216 + Z.of_nat j) = Some (YO0f.le_byte a 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 224 + Z.of_nat j) = Some (YO0f.le_byte c 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 228 + Z.of_nat j) = Some (YO0f.le_byte rt 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ mbX3 x -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.set_M_fly_on (TW.set_OW_acked_retry (TW.set_OW_acked_counter (TW.set_OW_acked
    (TW.set_M_last_rx Bw (TW.g_now Bw)) a) c) rt) 0).
Proof.
intros rd0 rdF Bw a c rt H V1 V2 V3 V4 V5 Hk.
unfold TW.set_M_fly_on, TW.set_OW_acked_retry, TW.set_OW_acked_counter, TW.set_OW_acked, TW.set_M_last_rx.
pose proof (mrx_tw_start rdF rd0 Bw H) as H0.
pose proof (mrx_tw_step rdF rd0 _ Bw TW.OFF_M TA_M TW.SZ_M 32 TW.A_M_last_rx 8 (TW.g_now Bw) H0 TMAP_A_M
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_M; lia) V1) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 216 TW.A_OW_acked 4 a H1 TMAP_A_OW
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; lia) V2) as H2.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 224 TW.A_OW_acked_counter 4 c H2 TMAP_A_OW
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; lia) V3) as H3.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 228 TW.A_OW_acked_retry 4 rt H3 TMAP_A_OW
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; lia) V4) as H4.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 96 TW.A_M_fly_on 4 0 H4 TMAP_A_M
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_M; lia) V5) as H5.
apply (mrx_tw_end rdF rd0 _ _ H5). intros x Hx HP. mb_unP HP.
apply Hk; [exact Hx | unfold mbX3, mbX2, mbX1; lia].
Qed.

(* and M.e2_acked = 1. *)
Lemma mb_w7 : forall rd0 rdF Bw a c rt, tw_at TMAP_A rd0 Bw ->
  (forall j, (j < 8)%nat -> rdF (TA_M + 32 + Z.of_nat j) = Some (YO0f.le_byte (TW.g_now Bw) 8 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 216 + Z.of_nat j) = Some (YO0f.le_byte a 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 224 + Z.of_nat j) = Some (YO0f.le_byte c 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 228 + Z.of_nat j) = Some (YO0f.le_byte rt 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ mbX4 x -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.set_M_e2_acked (TW.set_M_fly_on (TW.set_OW_acked_retry (TW.set_OW_acked_counter
    (TW.set_OW_acked (TW.set_M_last_rx Bw (TW.g_now Bw)) a) c) rt) 0) 1).
Proof.
intros rd0 rdF Bw a c rt H V1 V2 V3 V4 V5 V6 Hk.
unfold TW.set_M_e2_acked, TW.set_M_fly_on, TW.set_OW_acked_retry, TW.set_OW_acked_counter, TW.set_OW_acked,
  TW.set_M_last_rx.
pose proof (mrx_tw_start rdF rd0 Bw H) as H0.
pose proof (mrx_tw_step rdF rd0 _ Bw TW.OFF_M TA_M TW.SZ_M 32 TW.A_M_last_rx 8 (TW.g_now Bw) H0 TMAP_A_M
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_M; lia) V1) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 216 TW.A_OW_acked 4 a H1 TMAP_A_OW
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; lia) V2) as H2.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 224 TW.A_OW_acked_counter 4 c H2 TMAP_A_OW
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; lia) V3) as H3.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 228 TW.A_OW_acked_retry 4 rt H3 TMAP_A_OW
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; lia) V4) as H4.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 96 TW.A_M_fly_on 4 0 H4 TMAP_A_M
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_M; lia) V5) as H5.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 16 TW.A_M_e2_acked 4 1 H5 TMAP_A_M
  eq_refl ltac:(lia) ltac:(unfold TW.SZ_M; lia) V6) as H6.
apply (mrx_tw_end rdF rd0 _ _ H6). intros x Hx HP. mb_unP HP.
apply Hk; [exact Hx | unfold mbX4, mbX3, mbX2, mbX1; lia].
Qed.

(* An unwritten window byte read from a chunk holding the world's value. *)
Lemma mb_keep4 : forall (rd0 rdF : Z -> option Z) Bw o b n k x,
  tw_at TMAP_A rd0 Bw -> In (o, b, n) TMAP_A -> 0 <= k -> k + 4 <= n ->
  (forall j, (j < 4)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw (o + k) 4) 4 j)) ->
  b + k <= x < b + k + 4 -> rdF x = rd0 x.
Proof.
intros rd0 rdF Bw o b n k x H Hin Hk Hkn V Hx.
replace x with (b + k + Z.of_nat (Z.to_nat (x - (b + k)))) by lia.
rewrite (V (Z.to_nat (x - (b + k))) ltac:(lia)).
rewrite (tw_read TMAP_A rd0 Bw o b n k 4 (Z.to_nat (x - (b + k))) TMAP_A_ok H Hin Hk ltac:(lia) ltac:(lia)).
mb_refl.
Qed.

Ltac mb_awr U19 UOW :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first
      [ lia
      | rewrite U19 in Ha; right; left; apply mb_inG; unfold TA_M, TA_OW in *; lia
      | rewrite UOW in Ha; right; left; apply mb_inG; unfold TA_M, TA_OW in *; lia ] |]);
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

Ltac mb_win Usp U19 UOW UNOW :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp, ?U19, ?UOW, ?UNOW in Hx;
     unfold mbX4, mbX3, mbX2, mbX1, mbX0;
     lia |]);
  destruct Hin.

(* After a run: the model generalized, the kept facts carried to the run's last memory. *)
Ltac mb_after KA X Usp U19 UOW UNOW :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt;
    try clear m0 end;
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    let KA' := fresh "KAn" in
    pose proof (mb_KA_step _ _ _ X _ _ _ KA HFr) as KA';
    lazymatch type of KA' with ?P -> _ =>
      let Hw := fresh "Hw" in assert (Hw : P) by (mb_win Usp U19 UOW UNOW); specialize (KA' Hw); clear Hw end;
    clear KA HFr; rename KA' into KA end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  lazymatch goal with HG : mem_grows _ _ |- _ => clear HG end.

(* A new region of the state: disjoint from the state's regions (their bases rewritten to numbers). *)
Ltac mb_disj Usp U19 UOW UNOW :=
  cbn [ss_mem YP09.all_disjoint]; unfold mb_lrx, mb_fly, mb_ack, mb_acc, mb_e2;
  repeat match goal with |- _ /\ _ => split end; try exact I;
  unfold YP09.extent_disjoint;
  try change (A_OBJ 12) with 253%nat;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?Usp, ?U19, ?UOW, ?UNOW;
  unfold TA_M, TA_OW, TA_g_now, MRX_FRAME in *;
  lia.
Ltac mb_add HS R Hok Usp U19 UOW UNOW :=
  lazymatch type of HS with st_ok_pi ?sg0 ?vl0 ?Ex0 ?ss0 ?m0 =>
    let ss0' := eval vm_compute in ss0 in change (st_ok_pi sg0 vl0 Ex0 ss0' m0) in HS end;
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
    let HSa := fresh "HSa" in
    pose proof (st_ok_pi_add_region Ex ss m R HS eq_refl Hok ltac:(mb_disj Usp U19 UOW UNOW)) as HSa;
    clear HS; rename HSa into HS;
    lazymatch type of HS with st_ok_pi ?sg2 ?vl2 ?Ex2 ?ss2 ?m2 =>
      let ss' := eval vm_compute in ss2 in change (st_ok_pi sg2 vl2 Ex2 ss' m2) in HS end end.
Ltac mb_add0 HS R L U Usp U19 UOW UNOW :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ ?m => mb_add HS R (L Ex (ms_mem m) U) Usp U19 UOW UNOW end.
Ltac mb_mono KA L :=
  let KA' := fresh "KAm" in pose proof (mb_KA_mono _ _ _ _ _ L KA) as KA'; clear KA; rename KA' into KA.
(* One run of the walk (to its stop, or to the pc stop), with the write rights and the kept view; the walk's
   hypotheses are found by their types. *)
Ltac mb_step X :=
  lazymatch goal with
  | RUN : context [sym_runN_pi_tok _ _ _ _ _ _ _ _], HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
    HJ : @W_journalG.ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, KA : mb_KA _ _ _ _,
    Usp : bv_unsigned (ew _ 2%nat) = _, U19 : bv_unsigned (ew _ 19%nat) = TA_M,
    UOW : bv_unsigned (ew _ 253%nat) = TA_OW, UNOW : bv_unsigned (ew _ 268%nat) = TA_g_now |- _ =>
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan; [ mb_awr U19 UOW | mb_after KA X Usp U19 UOW UNOW ]
  end.
Ltac mb_stepto X stop :=
  lazymatch goal with
  | RUNTO : context [sym_run_toN_pi_tok _ _ _ _ _ _ _ _ _], HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
    HJ : @W_journalG.ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, KA : mb_KA _ _ _ _,
    Usp : bv_unsigned (ew _ 2%nat) = _, U19 : bv_unsigned (ew _ 19%nat) = TA_M,
    UOW : bv_unsigned (ew _ 253%nat) = TA_OW, UNOW : bv_unsigned (ew _ 268%nat) = TA_g_now |- _ =>
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan stop; [ mb_awr U19 UOW | mb_after KA X Usp U19 UOW UNOW ]
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
Ltac mb_in := cbn [In]; repeat first [left; reflexivity | right].

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

Definition mb_E (regs : bvmap 5 word) (Bw : list byte) : env := Eimg (PI := PI_transport) (Ereg regs (mb_vals fr Bw)).

Lemma mb_vals_img : VAL (A_OBJ 27) = TA_g_now /\ VAL (A_OBJ 12) = TA_OW /\ BASE + AF_m_rx = transport_sigma TS_m_rx.
Proof. vm_compute. repeat split. Qed.

Lemma mb_pc : forall off, MRX_PC off = BASE + (AF_m_rx + off).
Proof. intros off. unfold MRX_PC. destruct mb_vals_img as (_ & _ & H). lia. Qed.

Lemma mb_stk : 144 <= MRX_STK.
Proof. vm_compute. discriminate. Qed.

(* The entry state of the segment. *)
Lemma mb_entry : forall (Wc : world segs) regs2 mem2 Bw,
  tw_at TMAP_A (aview segs (w_H Wc) mem2) Bw ->
  YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME) -> YK11.getr regs2 19 = w64 TA_M ->
  mrx_spill Wc mem2 sp1 16 fr 25 -> mrx_spill Wc mem2 sp1 24 fr 24 ->
  0 <= mfb fr 25 < 256 -> 0 <= mfb fr 24 < 256 ->
  st_ok_pi segs VAL (mb_E regs2 Bw) ss_mb
    (restrict (w_H Wc) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + (AF_m_rx + OFF_BODY))) mem2 (YK11.seg_rom segs))).
Proof.
  intros Wc regs2 mem2 Bw Htw R2 R19 S16 S24 B25 B24.
  pose proof HST as (Hsp0 & Hsp16 & Hceil & H46 & H47 & _).
  pose proof mb_stk as HSTK.
  destruct mb_vals_img as (V27 & V12 & _).
  set (E := mb_E regs2 Bw).
  assert (EOB : forall j, (j < 95)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E, mb_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (EE : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E k = YK11.getr regs2 q)
    by (intros k q Hk; unfold E, mb_E; apply ew_Eimg_Ereg_nat; exact Hk).
  assert (EX : forall j, (j < 9)%nat -> ew E (32 + j) = nth j (mb_vals fr Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, mb_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 7%nat ltac:(lia)) as E39.
  pose proof (EX 8%nat ltac:(lia)) as E40.
  cbn [Nat.add nth mb_vals] in E32, E33, E34, E39, E40.
  assert (Usp : base_val E (Some 2%nat) = sp1 - MRX_FRAME).
  { cbn [base_val]. rewrite (EE 2%nat 2%bv eq_refl), R2. apply unsigned_lit_small. unfold MRX_FRAME. lia. }
  assert (U19 : base_val E (Some 19%nat) = TA_M).
  { cbn [base_val]. rewrite (EE 19%nat 19%bv eq_refl), R19. apply unsigned_lit_small. unfold TA_M. lia. }
  assert (U27 : base_val E (Some (A_OBJ 27)) = TA_g_now).
  { cbn [base_val]. rewrite (EOB 27%nat ltac:(lia)), V27. apply unsigned_lit_small. unfold TA_g_now. lia. }
  assert (DEN : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff k 0) = Z_to_bv 64 v)
    by (intros k v Hk Hv; cbn [sv_denot]; rewrite Hk, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  pose proof (TWL.u_at_range Bw TW.A_M_state 4) as R33. pose proof (TWL.u_at_range Bw TW.OFF_g_now 8) as R34.
  change (8 * Z.of_nat 4) with 32 in R33. change (8 * Z.of_nat 8) with 64 in R34.
  rewrite restrict_mkst_fx. unfold ss_mb.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold mb_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold mb_sp, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite Usp. unfold MRX_FRAME.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val segs E _ (sp1 - 144) 16 8 (SOff 39 0) (mfb fr 25));
          [apply DEN; [exact E39 | lia] | zside | zside |].
        exact (val_mem_of_rdword segs (w_H Wc) mem2 _ _ S16).
      * apply (chunk_ok_val segs E _ (sp1 - 144) 24 8 (SOff 40 0) (mfb fr 24));
          [apply DEN; [exact E40 | lia] | zside | zside |].
        exact (val_mem_of_rdword segs (w_H Wc) mem2 _ _ S24).
    + unfold mb_st, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite U19. split; [unfold TA_M; lia|]. split; [unfold TA_M; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ TA_M 12 4 (SOff 33 0) (TW.u_at Bw TW.A_M_state 4));
        [apply DEN; [exact E33 | lia] | exact R33 | lia |].
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 12 4 TMAP_A_ok Htw TMAP_A_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold mb_now, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite U27. split; [unfold TA_g_now; lia|]. split; [unfold TA_g_now; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ TA_g_now 0 8 (SOff 34 0) (TW.g_now Bw));
        [apply DEN; [exact E34 | exact R34] | exact R34 | lia |].
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8 TMAP_A_ok Htw TMAP_A_g_now
        ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)).
  - unfold mb_regions, mb_sp, mb_st, mb_now.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite Usp, U19, U27.
    unfold TA_M, TA_g_now, MRX_FRAME in *. repeat split; lia.
  - unfold mb_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EE 2%nat 2%bv eq_refl), (EE 19%nat 19%bv eq_refl), R2, R19, E32, (EOB 12%nat ltac:(lia)), V12.
    unfold w64.
    rewrite (unsigned_lit_small (sp1 - MRX_FRAME)) by (unfold MRX_FRAME; lia).
    rewrite (unsigned_lit_small TA_M) by (unfold TA_M; lia).
    rewrite (unsigned_lit_small TA_OW) by (unfold TA_OW; lia).
    rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold MRX_FRAME.
    repeat match goal with |- _ /\ _ => split end; try exact I;
      first [lia | unfold TA_M; reflexivity | unfold TA_OW; reflexivity | reflexivity
            | rewrite Zminus_mod, Hsp16; reflexivity].
Qed.

(* A value read through the view at mem0 is read at m where m keeps the view. *)
Lemma mb_val_kept : forall (Wc : world segs) (X : Z -> Prop) mem0 m a (k : nat) v,
  mb_KA Wc X mem0 m -> 0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> (forall i, a <= i < a + Z.of_nat k -> ~ X i) ->
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

Lemma mb_lrx_ok : forall E m, bv_unsigned (ew E 19%nat) = TA_M -> region_ok segs E m mb_lrx.
Proof.
intros E m H. unfold mb_lrx, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H. split; [unfold TA_M; lia|]. split; [unfold TA_M; lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply mb_inG. left. lia.
Qed.

Lemma mb_e2_ok : forall E m, bv_unsigned (ew E 19%nat) = TA_M -> region_ok segs E m mb_e2.
Proof.
intros E m H. unfold mb_e2, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H. split; [unfold TA_M; lia|]. split; [unfold TA_M; lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply mb_inG. left. lia.
Qed.

Lemma mb_acc_ok : forall E m, bv_unsigned (ew E 253%nat) = TA_OW -> region_ok segs E m mb_acc.
Proof.
intros E m H. unfold mb_acc, region_ok.
change (A_OBJ 12) with 253%nat.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw). apply mb_inG. right. lia.
Qed.

Lemma mb_fly_ok : forall E (Wc : world segs) m Bw,
  bv_unsigned (ew E 19%nat) = TA_M ->
  ew E 35%nat = Z_to_bv 64 (TW.u_at Bw TW.A_M_fly_on 4) ->
  ew E 36%nat = Z_to_bv 64 (TW.u_at Bw TW.A_M_fly_counter 4) ->
  ew E 37%nat = Z_to_bv 64 (TW.u_at Bw TW.A_M_fly_retries 4) ->
  val_mem segs (mrestrict (w_H Wc) m) (TA_M + 96) 4 (TW.u_at Bw TW.A_M_fly_on 4) ->
  val_mem segs (mrestrict (w_H Wc) m) (TA_M + 104) 4 (TW.u_at Bw TW.A_M_fly_counter 4) ->
  val_mem segs (mrestrict (w_H Wc) m) (TA_M + 108) 4 (TW.u_at Bw TW.A_M_fly_retries 4) ->
  region_ok segs E (mrestrict (w_H Wc) m) mb_fly.
Proof.
intros E Wc m Bw H E35 E36 E37 V1 V2 V3. unfold mb_fly, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H. split; [unfold TA_M; lia|]. split; [unfold TA_M; lia|]. split.
- intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply mb_inG. left. lia.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + apply (chunk_ok_val segs E _ TA_M 96 4 (SOff 35 0) (TW.u_at Bw TW.A_M_fly_on 4));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | exact (TWL.u_at_range Bw TW.A_M_fly_on 4) | lia | exact V1].
  + apply (chunk_ok_val segs E _ TA_M 104 4 (SOff 36 0) (TW.u_at Bw TW.A_M_fly_counter 4));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | exact (TWL.u_at_range Bw TW.A_M_fly_counter 4) | lia | exact V2].
  + apply (chunk_ok_val segs E _ TA_M 108 4 (SOff 37 0) (TW.u_at Bw TW.A_M_fly_retries 4));
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | exact (TWL.u_at_range Bw TW.A_M_fly_retries 4) | lia | exact V3].
Qed.

Lemma mb_ack_ok : forall E (Wc : world segs) m Bw,
  bv_unsigned (ew E 253%nat) = TA_OW ->
  ew E 38%nat = Z_to_bv 64 (TW.u_at Bw TW.A_OW_acked 4) ->
  val_mem segs (mrestrict (w_H Wc) m) (TA_OW + 216) 4 (TW.u_at Bw TW.A_OW_acked 4) ->
  region_ok segs E (mrestrict (w_H Wc) m) mb_ack.
Proof.
intros E Wc m Bw H E38 V1. unfold mb_ack, region_ok.
change (A_OBJ 12) with 253%nat.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split.
- intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw). apply mb_inG. right. lia.
- apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs E _ TA_OW 216 4 (SOff 38 0) (TW.u_at Bw TW.A_OW_acked 4));
    [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | exact (TWL.u_at_range Bw TW.A_OW_acked 4) | lia | exact V1].
Qed.

Lemma mb_X01 : forall a, mbX0 a -> mbX1 a. Proof. intros a []. Qed.
Lemma mb_X12 : forall a, mbX1 a -> mbX2 a. Proof. intros a H. left. exact H. Qed.
Lemma mb_X23 : forall a, mbX2 a -> mbX3 a. Proof. intros a H. left. exact H. Qed.
Lemma mb_X34 : forall a, mbX3 a -> mbX4 a. Proof. intros a H. left. exact H. Qed.

Lemma mb_X04 : forall a, mbX0 a -> mbX4 a. Proof. intros a []. Qed.
Lemma mb_X14 : forall a, mbX1 a -> mbX4 a. Proof. intros a H. left; left; left; exact H. Qed.
Lemma mb_X24 : forall a, mbX2 a -> mbX4 a. Proof. intros a H. left; left; exact H. Qed.

(* Every window byte is a byte the call may store (mrx_wr), in M or OW. *)
Lemma mb_X4_wr : forall a, mbX4 a -> mrx_wr a /\ TA_M <= a < TA_OW + 304.
Proof.
intros a H. split; [| unfold mbX4, mbX3, mbX2, mbX1 in H; unfold TA_M, TA_OW in *; lia].
unfold mbX4, mbX3, mbX2, mbX1 in H. unfold mrx_wr, twa_fld.
destruct H as [[[H|H]|[H|H]]|H].
- do 5 right; left. unfold TW.A_M_last_rx, TW.OFF_M. lia.
- do 12 right; left. unfold TW.A_M_fly_on, TW.OFF_M. lia.
- do 19 right; left. unfold TW.A_OW_acked, TW.OFF_OW. lia.
- destruct (Z_lt_le_dec a (TA_OW + 228)).
  + do 21 right; left. unfold TW.A_OW_acked_counter, TW.OFF_OW. lia.
  + do 22 right; left. unfold TW.A_OW_acked_retry, TW.OFF_OW. lia.
- do 3 right; left. unfold TW.A_M_e2_acked, TW.OFF_M. lia.
Qed.

Lemma mb_agree : forall regs Bw, env_agree 32 (Ereg regs (mb_vals fr Bw)) (mb_E regs Bw).
Proof. intros regs Bw. split; [intros k Hk; unfold mb_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* An exit: the cut pc with its facts R, from the run's last state. *)
Lemma mb_exit : forall (Wc : world segs) pc pc' R regsF memF mdF Bn,
  pc' = pc -> K pc R ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc Wc
    memF mdF 0 ->
  YK11.getr regsF 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK11.getr regsF 3 = YK11.getr regs0 3 -> YK11.getr regsF 4 = YK11.getr regs0 4 ->
  mrx_saved Wc memF sp1 regs0 ->
  tw_at TMAP_A (aview segs (w_H Wc) memF) Bn ->
  R Wc Bn lyc Sc regsF memF ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 pc') memF (YK11.seg_rom segs)) mdF)
    (@mrx_ipost fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r).
Proof.
intros Wc pc pc' R regsF memF mdF Bn -> HK HJ H2 H3 H4 HSv HT HR.
apply (HK Wc Bn). eapply mrx_at_intro;
  [exact HJ | reflexivity | apply Permutation_refl | exact (mo_le_refl MT MTL Sc)
  | exact H2 | exact H3 | exact H4 | exact HSv | exact HT | exact HR].
Qed.

(* What the cut's facts keep across runs that write only the windows. *)
Lemma mb_saved_kept : forall (Wc : world segs) mem2 m, mb_KA Wc mbX4 mem2 m ->
  mrx_saved Wc mem2 sp1 regs0 -> mrx_saved Wc m sp1 regs0.
Proof.
intros Wc mem2 m KA HSv. pose proof HST as (_ & _ & _ & H46 & H47 & _). pose proof mb_stk as HSTK.
apply (mrx_saved_kept Wc Wc mem2 m sp1 regs0 HSv). intros a Ha.
apply KA; [lia | intros HX; pose proof (proj2 (mb_X4_wr a HX)); unfold TA_OW in *; lia].
Qed.

Lemma mb_spill_kept' : forall (Wc : world segs) mem2 m o k, mb_KA Wc mbX4 mem2 m -> 0 <= o -> o + 8 <= 144 ->
  mrx_spill Wc mem2 sp1 o fr k -> mrx_spill Wc m sp1 o fr k.
Proof.
intros Wc mem2 m o k KA Ho Ho8 HSp. pose proof HST as (_ & _ & _ & H46 & H47 & _). pose proof mb_stk as HSTK.
apply (mrx_spill_kept Wc Wc mem2 m sp1 o fr k HSp). intros a Ha. unfold MRX_FRAME in Ha.
apply KA; [lia | intros HX; pose proof (proj2 (mb_X4_wr a HX)); unfold TA_OW in *; lia].
Qed.

Lemma mb_hregs_kept : forall (Wc : world segs) mem2 m regs2 regsF,
  mrx_hregs fr Wc sp1 regs2 mem2 -> mb_KA Wc mbX4 mem2 m ->
  (forall q, In q [18%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] -> YK11.getr regsF q = YK11.getr regs2 q) ->
  mrx_hregs fr Wc sp1 regsF m.
Proof.
intros Wc mem2 m regs2 regsF (H18 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & S16 & S24 & S32) KA RK.
unfold mrx_hregs.
split; [exact (eq_trans (RK 18%bv ltac:(mb_in)) H18)|].
split; [exact (eq_trans (RK 21%bv ltac:(mb_in)) H21)|].
split; [exact (eq_trans (RK 22%bv ltac:(mb_in)) H22)|].
split; [exact (eq_trans (RK 23%bv ltac:(mb_in)) H23)|].
split; [exact (eq_trans (RK 24%bv ltac:(mb_in)) H24)|].
split; [exact (eq_trans (RK 25%bv ltac:(mb_in)) H25)|].
split; [exact (eq_trans (RK 26%bv ltac:(mb_in)) H26)|].
split; [exact (eq_trans (RK 27%bv ltac:(mb_in)) H27)|].
split; [exact (mb_spill_kept' Wc mem2 m 16 25 KA ltac:(lia) ltac:(lia) S16)|].
split; [exact (mb_spill_kept' Wc mem2 m 24 24 KA ltac:(lia) ltac:(lia) S24)|].
exact (mb_spill_kept' Wc mem2 m 32 21 KA ltac:(lia) ltac:(lia) S32).
Qed.

Lemma mb_frs_kept : forall (Wc : world segs) mem2 m, mb_KA Wc mbX4 mem2 m -> mrx_frs fr Wc mem2 -> mrx_frs fr Wc m.
Proof.
intros Wc mem2 m KA (HG & HD & HR).
pose proof HST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hapart & _).
destruct HD as (HD1 & HD2 & HD3 & HD4 & HD5 & HD6).
assert (NF : forall a, TI.tf_addr fr <= a < TI.tf_addr fr + mlen fr -> ~ mbX4 a).
{ intros a Ha HX. apply (Hapart a (proj1 (mb_X4_wr a HX))). unfold mlen in Ha. exact Ha. }
assert (NS : forall a, SHADOW_OFF - 8 <= a -> ~ mbX4 a).
{ intros a Ha HX. pose proof (proj2 (mb_X4_wr a HX)) as Hb. unfold SHADOW_OFF, TA_OW, TA_M in *. lia. }
split; [|split].
- unfold YI00.garr8 in *. intros j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
  rewrite length_map in Hj. unfold mlen in *.
  apply (mb_val_kept Wc mbX4 mem2 m (TI.tf_addr fr + Z.of_nat j) 1 _ KA); [lia | lia | | exact Hv].
  intros i Hi. apply NF. unfold mlen. lia.
- split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha. rewrite (KA a ltac:(lia) (NF a ltac:(lia))). exact (HD1 a Ha).
  + intros x Hx. destruct (HD2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    unfold shadow_of_addr in *.
    assert (Hd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    rewrite (KA (SHADOW_OFF + x / 8)); [exact Hs | unfold SHADOW_OFF; lia | apply NS; lia].
  + intros s Hs. unfold shadow_addr in Hs.
    assert (Hnl : 0 <= mlen fr) by (unfold mlen; lia).
    set (q := TI.tf_addr fr) in *. set (nl := mlen fr) in *.
    assert (Hq8 : 0 <= q / 8) by (apply Z.div_pos; lia).
    assert (Hq8' : (q + nl - 1) / 8 <= q + nl) by (apply Z.div_le_upper_bound; lia).
    pose proof (Z.div_mod (SHADOW_OFF + q / 8) 8 ltac:(lia)) as DM1.
    pose proof (Z.mod_pos_bound (SHADOW_OFF + q / 8) 8 ltac:(lia)) as MB1.
    pose proof (Z.div_mod (SHADOW_OFF + (q + nl - 1) / 8) 8 ltac:(lia)) as DM2.
    pose proof (Z.mod_pos_bound (SHADOW_OFF + (q + nl - 1) / 8) 8 ltac:(lia)) as MB2.
    rewrite (KA s); [exact (HD3 s Hs) | unfold SHADOW_OFF in *; lia | apply NS; unfold SHADOW_OFF in *; lia].
  + exact HD4.
  + exact HD5.
  + exact HD6.
- intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Hb.
  rewrite (KA a ltac:(lia) ltac:(intros HX; pose proof (proj2 (mb_X4_wr a HX)); unfold TA_M in *; lia)).
  exact (HR a Ha).
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

(* The rest of the payload bytes when M.fly.on's window kept its value. *)
Lemma mb_rest2 : forall (Wc : world segs) mem2 m Bw,
  tw_at TMAP_A (aview segs (w_H Wc) mem2) Bw -> mb_KA Wc mbX2 mem2 m ->
  (forall j, (j < 4)%nat -> aview segs (w_H Wc) m (TA_M + 96 + Z.of_nat j) =
     Some (YO0f.le_byte (TW.u_at Bw (TW.OFF_M + 96) 4) 4 j)) ->
  forall x, tw_in TMAP_A x -> ~ mbX1 x -> aview segs (w_H Wc) m x = aview segs (w_H Wc) mem2 x.
Proof.
intros Wc mem2 m Bw Htw KA VF x Hx HN.
destruct (Z_lt_le_dec x (TA_M + 96)) as [Hl|Hl]; [| destruct (Z_lt_le_dec x (TA_M + 100)) as [Hl2|Hl2]].
- apply KA; [exact (mb_tw_in_rng x Hx) | unfold mbX2; intros [H|H]; [exact (HN H) | lia]].
- exact (mb_keep4 _ _ Bw TW.OFF_M TA_M TW.SZ_M 96 x Htw TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia) VF
    ltac:(lia)).
- apply KA; [exact (mb_tw_in_rng x Hx) | unfold mbX2; intros [H|H]; [exact (HN H) | lia]].
Qed.

(* The registers the run kept, by the symbolic state (the list l typed against the lemma's list (bv 5)). *)
Tactic Notation "mb_rk" constr(HS) constr(E0) constr(regs2) constr(vals) constr(AGR) uconstr(l) ident(RK) :=
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict ?Hh ?m) =>
    pose proof (regs_kept_of_st_ok_pi E0 ss (restrict Hh m) regs2 vals l HS AGR eq_refl) as RK;
    cbn [ms_regs restrict] in RK end.

(* The BODY segment: from the cut BODY (0x84b70) to EPI (S_CLOSED), DATA (cmd 0), TICK, MO (cmd ACK at S_WAKING),
   LOST (cmd e3 at S_ONLINE / S_WAKING), ANNT (cmd e0) or HOST (cmd e1). *)
Lemma mrx_seg_body :
  K (MRX_PC OFF_EPI) (R_EPI Bw' r) ->
  K (MRX_PC OFF_TICK) (R_TICK Bw' r) ->
  K (MRX_PC OFF_MO) (R_MO Bw' r) ->
  K (MRX_PC OFF_LOST) (R_LOST Bw' r) ->
  K (MRX_PC OFF_DATA) (R_DATA fr n sp1 lyc Sc Bw' r) ->
  K (MRX_PC OFF_HOST) (R_HOST fr n sp1 lyc Sc Bw' r) ->
  K (MRX_PC OFF_ANNT) (R_ANNT fr n sp1 lyc Sc Bw' r) ->
  K (MRX_PC OFF_BODY) (R_BODY fr n sp1 lyc Sc Bw' r).
Proof using All.
intros KEPI KTICK KMO KLOST KDATA KHOST KANNT.
unfold mrx_K. intros Wc B1 c Hat.
unfold mrx_at in Hat.
destruct Hat as (ly2 & S2 & regs2 & mem2 & md2 & Hc0 & HJ & Hfrm & Hperm & Hmo & Hsp & Hgp & Htp & Hsav & Htw & HR).
subst c.
unfold R_BODY in HR.
destruct HR as (-> & -> & HFRS & HHDR & R8 & R9 & R19 & R20 & HHR & HSP8 & HMK).
pose proof HHR as (R18 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & SP16 & SP24 & SP32).
pose proof HST as (Hsp0 & Hsp16 & Hceil & H46 & H47 & Hra & Hra4 & Hgp0 & Htp0 & Ha0 & Ha1 & Hfa0 & Hfan & Hsrc
  & Hwinfr & Hapart & Hnev & HAR).
pose proof HHDR as (Hnl & Het & Hnb).
pose proof mb_stk as HSTK.
assert (Hlen30 : 30 <= Z.of_nat (length (TI.tf_bytes fr))) by (unfold mlen in Hnl; lia).
assert (Rb : forall k, 0 <= k < 30 -> 0 <= mfb fr k < 256).
{ intros k Hk. unfold mfb. rewrite (EPI.mrx_byte_at (TI.tf_bytes fr) k) by lia. apply EPI.mrx_byte_range. }
pose proof (Rb 28 ltac:(lia)) as Rc. pose proof (Rb 22 ltac:(lia)) as Rb22. pose proof (Rb 23 ltac:(lia)) as Rb23.
pose proof (Rb 24 ltac:(lia)) as Rb24. pose proof (Rb 25 ltac:(lia)) as Rb25.
assert (LB1 : Z.of_nat (length B1) = TW.W_LEN)
  by (rewrite (tw_len _ _ _ Htw), Z2Nat.id; [reflexivity | unfold TW.W_LEN; lia]).
destruct (mbm_B2 B1 LB1) as (LB2 & BS & BN & BF & BC & BRT & BA).
pose proof (TWL.s32_range B1 TW.A_M_state) as RS. change (TW.s32_at B1 TW.A_M_state) with (TW.M_state B1) in RS.
pose proof (TWL.s32_range B1 TW.A_M_fly_on) as RF. change (TW.s32_at B1 TW.A_M_fly_on) with (TW.M_fly_on B1) in RF.
pose proof (TWL.u_at_range B1 TW.A_M_state 4) as R33. pose proof (TWL.u_at_range B1 TW.OFF_g_now 8) as R34.
pose proof (TWL.u_at_range B1 TW.A_M_fly_on 4) as R35. pose proof (TWL.u_at_range B1 TW.A_M_fly_counter 4) as R36.
pose proof (TWL.u_at_range B1 TW.A_M_fly_retries 4) as R37. pose proof (TWL.u_at_range B1 TW.A_OW_acked 4) as R38.
change (8 * Z.of_nat 4) with 32 in R33, R35, R36, R37, R38. change (8 * Z.of_nat 8) with 64 in R34.
assert (RA : 0 <= EPI.mrx_ack fr < 2 ^ 32) by (unfold EPI.mrx_ack; apply EPI.mrx_be32_range; lia).
assert (EA : EPI.mrx_ack fr = mfb fr 22 * 2 ^ 24 + mfb fr 23 * 2 ^ 16 + mfb fr 24 * 2 ^ 8 + mfb fr 25).
{ unfold EPI.mrx_ack, mfb. rewrite EPI.mrx_be32 by lia. rewrite !EPI.mrx_byte_at by lia. reflexivity. }
pose proof (EPI.mrx_be16_range (TW.zs (TI.tf_bytes fr)) 14) as Rnb.
destruct mb_vals_img as (V27 & V12 & _).
set (E0 := mb_E regs2 B1).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, mb_E; apply Eimg_env).
assert (EE : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E0 k = YK11.getr regs2 q)
  by (intros k q Hk; unfold E0, mb_E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E0 2%nat) = sp1 - MRX_FRAME).
{ rewrite (EE 2%nat 2%bv eq_refl), Hsp. apply unsigned_lit_small. unfold MRX_FRAME. lia. }
assert (U19 : bv_unsigned (ew E0 19%nat) = TA_M).
{ rewrite (EE 19%nat 19%bv eq_refl), R19. apply unsigned_lit_small. unfold TA_M. lia. }
assert (UOW : bv_unsigned (ew E0 253%nat) = TA_OW).
{ unfold E0, mb_E. rewrite (Eimg_img _ 253%nat) by (unfold A_TEXT, A_LIM; lia).
  change 253%nat with (A_OBJ 12). rewrite V12. apply unsigned_lit_small. unfold TA_OW. lia. }
assert (UNOW : bv_unsigned (ew E0 268%nat) = TA_g_now).
{ unfold E0, mb_E. rewrite (Eimg_img _ 268%nat) by (unfold A_TEXT, A_LIM; lia).
  change 268%nat with (A_OBJ 27). rewrite V27. apply unsigned_lit_small. unfold TA_g_now. lia. }
pose proof (mb_entry Wc regs2 mem2 B1 Htw Hsp R19 SP16 SP24 Rb25 Rb24) as HS.
fold E0 in HS.
assert (SHOK : sh_ok segs MB_Bx MB_SH E0 (mrestrict (w_H Wc) mem2)) by (unfold sh_ok, MB_SH; apply Forall_nil).
assert (KA : mb_KA Wc mbX0 mem2 mem2) by (intros a _ _; reflexivity).
assert (EX : forall j, (j < 9)%nat -> ew E0 (32 + j) = nth j (mb_vals fr B1) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, mb_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36.
pose proof (EX 5%nat ltac:(lia)) as E37. pose proof (EX 6%nat ltac:(lia)) as E38.
pose proof (EX 7%nat ltac:(lia)) as E39. pose proof (EX 8%nat ltac:(lia)) as E40.
cbn [Nat.add nth mb_vals] in E33, E34, E35, E36, E37, E38, E39, E40.
clear EX.
assert (Vfly0 : val_mem segs (mrestrict (w_H Wc) mem2) (TA_M + 96) 4 (TW.u_at B1 TW.A_M_fly_on 4))
  by exact (tw_read_val segs _ TMAP_A B1 TW.OFF_M TA_M TW.SZ_M 96 4 TMAP_A_ok Htw TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
assert (Vcnt0 : val_mem segs (mrestrict (w_H Wc) mem2) (TA_M + 104) 4 (TW.u_at B1 TW.A_M_fly_counter 4))
  by exact (tw_read_val segs _ TMAP_A B1 TW.OFF_M TA_M TW.SZ_M 104 4 TMAP_A_ok Htw TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
assert (Vret0 : val_mem segs (mrestrict (w_H Wc) mem2) (TA_M + 108) 4 (TW.u_at B1 TW.A_M_fly_retries 4))
  by exact (tw_read_val segs _ TMAP_A B1 TW.OFF_M TA_M TW.SZ_M 108 4 TMAP_A_ok Htw TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
assert (Vack0 : val_mem segs (mrestrict (w_H Wc) mem2) (TA_OW + 216) 4 (TW.u_at B1 TW.A_OW_acked 4))
  by exact (tw_read_val segs _ TMAP_A B1 TW.OFF_OW TA_OW TW.SZ_OW 216 4 TMAP_A_ok Htw TMAP_A_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)).
assert (E22 : ew E0 22%nat = Z_to_bv 64 (mfb fr 22)) by (rewrite (EE 22%nat 22%bv eq_refl), R22; reflexivity).
assert (E26 : ew E0 26%nat = Z_to_bv 64 (mfb fr 23)) by (rewrite (EE 26%nat 26%bv eq_refl), R26; reflexivity).
assert (E25 : ew E0 25%nat = Z_to_bv 64 (mfb fr 28)) by (rewrite (EE 25%nat 25%bv eq_refl), R25; reflexivity).
assert (E20 : ew E0 20%nat = Z_to_bv 64 (DSpec.spec_be16 (TW.zs (TI.tf_bytes fr)) 14))
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity).
assert (E8 : ew E0 8%nat = Z_to_bv 64 (TI.tf_addr fr)) by (rewrite (EE 8%nat 8%bv eq_refl), R8; reflexivity).
(* the values the code forms *)
assert (D33 : sv_denot E0 (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (TW.M_state B1))
  by exact (mbd_sext E0 33 _ E33 R33).
assert (D35 : sv_denot E0 (SExt true 32 (SOff 35 0)) = Z_to_bv 64 (TW.M_fly_on B1))
  by exact (mbd_sext E0 35 _ E35 R35).
assert (D36 : sv_denot E0 (SExt true 32 (SOff 36 0)) = Z_to_bv 64 (bv_swrap 32 (TW.M_fly_counter B1)))
  by exact (mbd_sext E0 36 _ E36 R36).
assert (D37 : sv_denot E0 (SExt true 32 (SOff 37 0)) = Z_to_bv 64 (bv_swrap 32 (TW.M_fly_retries B1)))
  by exact (mbd_sext E0 37 _ E37 R37).
assert (DA1 : sv_denot E0 (SAlu ALU_ADD (SExt true 32 (SOff 38 0)) (SLit 1)) = Z_to_bv 64 (TW.OW_acked B1 + 1))
  by exact (mbd_add E0 38 _ 1 E38 R38).
assert (DS0 : sv_denot E0 (SAlu ALU_ADD (SExt true 32 (SOff 33 0)) (SLit 0)) = Z_to_bv 64 (TW.M_state B1 + 0))
  by exact (mbd_add E0 33 _ 0 E33 R33).
assert (D25 : sv_denot E0 (SOff 25 0) = Z_to_bv 64 (mfb fr 28))
  by (rewrite (mbd_off E0 25 _ 0 E25 ltac:(lia)), Z.add_0_r; reflexivity).
assert (D25m : sv_denot E0 (SOff 25 (-224)) = Z_to_bv 64 (mfb fr 28 + -224))
  by exact (mbd_off E0 25 _ (-224) E25 ltac:(lia)).
assert (D20m : sv_denot E0 (SOff 20 (-16)) = Z_to_bv 64 (DSpec.spec_be16 (TW.zs (TI.tf_bytes fr)) 14 + -16))
  by exact (mbd_off E0 20 _ (-16) E20 ltac:(lia)).
assert (D8 : sv_denot E0 (SOff 8 30) = Z_to_bv 64 (TI.tf_addr fr + 30)) by exact (mbd_off E0 8 _ 30 E8 ltac:(lia)).
assert (D34 : sv_denot E0 (SOff 34 0) = Z_to_bv 64 (TW.g_now B1))
  by (rewrite (mbd_off E0 34 _ 0 E34 R34), Z.add_0_r; reflexivity).
assert (D35' : sv_denot E0 (SOff 35 0) = Z_to_bv 64 (TW.u_at B1 TW.A_M_fly_on 4))
  by (rewrite (mbd_off E0 35 _ 0 E35 ltac:(lia)), Z.add_0_r; reflexivity).
assert (DACK : sv_denot E0 (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 26 0) (SLit 16))
    (SAluw ALU_SLL (SOff 22 0) (SLit 24))) (SAlu ALU_OR (SAlu ALU_SLL (SOff 40 0) (SLit 8)) (SOff 39 0)))
  = Z_to_bv 64 (bv_swrap 32 (EPI.mrx_ack fr))).
{ rewrite EA. exact (mbd_ack E0 _ _ _ _ E22 E26 E40 E39 Rb22 Rb23 Rb24 Rb25). }
assert (DST : sv_denot E0 (SAluw ALU_ADD (SExt true 32 (SOff 33 0)) (SLit (-1))) =
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (TW.M_state B1)) + -1)))
  by exact (mbd_state12 E0 _ E33 R33).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
rewrite (mb_pc OFF_BODY).
(* 0x84b70 - 0x84b78: a5 = M.state, `beq a5, 3` *)
mb_step mbX0.
mb_br.
{ (* S_CLOSED: 0x84968, a0 = 0, the epilogue *)
  rewrite D33 in Hc. cbn [sv_denot] in Hc. rewrite mbl_eq in Hc by lia. apply Z.eqb_eq in Hc.
  destruct (mbm_closed timg_A fr B1 Bw' r Hc HMK) as [HBw Hr0].
  mb_stepto mbX0 (AF_m_rx + OFF_EPI).
  pmkst HS.
  mb_rk HS E0 regs2 (mb_vals fr B1) (mb_agree regs2 B1) [2%bv; 3%bv; 4%bv] RK.
  mb_reg HS 10%bv (w64 0) RX10 ltac:(reflexivity).
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
    apply (mb_exit Wc (MRX_PC OFF_EPI) _ (R_EPI Bw' r) (ms_regs m) (ms_mem m) _ B1) end.
  - rewrite (mb_pc OFF_EPI). reflexivity.
  - exact KEPI.
  - exact HJ.
  - exact (eq_trans (RK 2%bv ltac:(mb_in)) Hsp).
  - exact (eq_trans (RK 3%bv ltac:(mb_in)) Hgp).
  - exact (eq_trans (RK 4%bv ltac:(mb_in)) Htp).
  - exact (mb_saved_kept Wc mem2 _ (mb_KA_mono _ _ _ _ _ mb_X04 KA) Hsav).
  - apply (tw_kept TMAP_A (aview segs (w_H Wc) mem2) _ B1 Htw). intros x Hx.
    exact (KA x (mb_tw_in_rng x Hx) (fun H => H)).
  - unfold R_EPI. split; [exact (eq_sym HBw) | rewrite Hr0; exact RX10]. }
rewrite D33 in Hc. cbn [sv_denot] in Hc. rewrite mbl_eq in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into HNC.
destruct (mbm_open timg_A fr B1 Bw' r HNC HMK) as (B3 & SW & TK & Er).
set (B2 := TW.set_M_last_rx B1 (TW.g_now B1)) in *.
(* M.last_rx joins the state *)
mb_mono KA mb_X01.
mb_add0 HS mb_lrx mb_lrx_ok U19 Usp U19 UOW UNOW.
(* 0x84b7c - 0x84b94: a0 = g_now, s0 = fa + 30, s4 = body_len, M.last_rx = g_now, `bge 0xdf, s9` *)
mb_step mbX1.
mb_br.
{ (* cmd <= 0xdf *)
  rewrite D25 in Hc. cbn [sv_denot] in Hc. rewrite mbl_ge in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc.
  rename Hc into HcL.
  (* 0x84bf8: `beqz s9` *)
  mb_step mbX1.
  mb_br.
  { (* cmd 0: DATA *)
    rewrite D25 in Hc. cbn [sv_denot] in Hc. rewrite mbl_eq in Hc by lia. apply Z.eqb_eq in Hc. rename Hc into Hc0.
    rewrite (mbm_sw_data timg_A fr B2 Hc0) in SW.
    mb_stepto mbX1 (AF_m_rx + OFF_DATA).
    pmkst HS.
    mb_rk HS E0 regs2 (mb_vals fr B1) (mb_agree regs2 B1)
      [2%bv; 3%bv; 4%bv; 18%bv; 19%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] RK.
    mb_reg HS 10%bv (w64 (TW.g_now B1)) RX10 ltac:(exact D34).
    mb_reg HS 8%bv (w64 (TI.tf_addr fr + 30)) RX8 ltac:(exact D8).
    mb_reg HS 20%bv (w64 (EPI.mrx_blen fr)) RX20 ltac:(exact D20m).
    pose proof (mb_KA_mono _ _ _ _ _ mb_X14 KA) as KA4.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
      pose proof (mb_chunk E0 Wc ss m 0%nat _ 0%nat 32 8%N (SOff 34 0) (TW.g_now B1) TA_M HS eq_refl U19 eq_refl
        D34 ltac:(cbn; lia)) as VL;
      apply (mb_exit Wc (MRX_PC OFF_DATA) _ (R_DATA fr n sp1 lyc Sc Bw' r) (ms_regs m) (ms_mem m) _ B2) end.
    - rewrite (mb_pc OFF_DATA). reflexivity.
    - exact KDATA.
    - exact HJ.
    - exact (eq_trans (RK 2%bv ltac:(mb_in)) Hsp).
    - exact (eq_trans (RK 3%bv ltac:(mb_in)) Hgp).
    - exact (eq_trans (RK 4%bv ltac:(mb_in)) Htp).
    - exact (mb_saved_kept Wc mem2 _ KA4 Hsav).
    - exact (mb_w2 (aview segs (w_H Wc) mem2) _ B1 Htw VL (fun x Hx HN => KA x (mb_tw_in_rng x Hx) HN)).
    - unfold R_DATA. split; [reflexivity|]. split; [reflexivity|].
      split; [exact (mb_frs_kept Wc mem2 _ KA4 HFRS)|]. split; [exact HHDR|]. split; [exact Hc0|].
      split; [rewrite BN; exact RX10|]. split; [exact RX8|].
      split; [exact (eq_trans (RK 19%bv ltac:(mb_in)) R19)|]. split; [exact RX20|].
      split; [exact (mb_hregs_kept Wc mem2 _ regs2 _ HHR KA4
                 (fun q Hq => RK q ltac:(cbn [In] in Hq |- *; tauto)))|].
      split; [exact (mb_spill_kept' Wc mem2 _ 8 18 KA4 ltac:(lia) ltac:(lia) HSP8)|].
      exists B3. split; [exact SW|]. split; [exact TK | exact Er]. }
  rewrite D25 in Hc. cbn [sv_denot] in Hc. rewrite mbl_eq in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Hn0.
  (* 0x84bfc - 0x84c00: `bne s9, 0xa0` *)
  mb_step mbX1.
  mb_br.
  { (* cmd other: m_tick *)
    rewrite D25 in Hc. cbn [sv_denot] in Hc. rewrite mbl_ne in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
    rename Hc into Hna.
    rewrite (mbm_sw_none timg_A fr B2 Hn0 Hna ltac:(lia) ltac:(lia) ltac:(lia)) in SW.
    apply mbm_some_inv in SW. subst B3.
    mb_stepto mbX1 (AF_m_rx + OFF_TICK).
    pmkst HS.
    mb_rk HS E0 regs2 (mb_vals fr B1) (mb_agree regs2 B1) [2%bv; 3%bv; 4%bv] RK.
    pose proof (mb_KA_mono _ _ _ _ _ mb_X14 KA) as KA4.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
      pose proof (mb_chunk E0 Wc ss m 0%nat _ 0%nat 32 8%N (SOff 34 0) (TW.g_now B1) TA_M HS eq_refl U19 eq_refl
        D34 ltac:(cbn; lia)) as VL;
      apply (mb_exit Wc (MRX_PC OFF_TICK) _ (R_TICK Bw' r) (ms_regs m) (ms_mem m) _ B2) end.
    - rewrite (mb_pc OFF_TICK). reflexivity.
    - exact KTICK.
    - exact HJ.
    - exact (eq_trans (RK 2%bv ltac:(mb_in)) Hsp).
    - exact (eq_trans (RK 3%bv ltac:(mb_in)) Hgp).
    - exact (eq_trans (RK 4%bv ltac:(mb_in)) Htp).
    - exact (mb_saved_kept Wc mem2 _ KA4 Hsav).
    - exact (mb_w2 (aview segs (w_H Wc) mem2) _ B1 Htw VL (fun x Hx HN => KA x (mb_tw_in_rng x Hx) HN)).
    - unfold R_TICK. split; [exact TK | exact Er]. }
  rewrite D25 in Hc. cbn [sv_denot] in Hc. rewrite mbl_ne in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
  rename Hc into Hca.
  rewrite (mbm_sw_ack timg_A fr B2 Hca) in SW.
  (* cmd ACK: M.fly joins the state *)
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
    pose proof (mb_val_kept Wc mbX1 mem2 (ms_mem m) (TA_M + 96) 4 _ KA ltac:(unfold TA_M; lia)
      ltac:(unfold TA_M; lia) ltac:(unfold mbX1; intros; lia) Vfly0) as Vfly;
    pose proof (mb_val_kept Wc mbX1 mem2 (ms_mem m) (TA_M + 104) 4 _ KA ltac:(unfold TA_M; lia)
      ltac:(unfold TA_M; lia) ltac:(unfold mbX1; intros; lia) Vcnt0) as Vcnt;
    pose proof (mb_val_kept Wc mbX1 mem2 (ms_mem m) (TA_M + 108) 4 _ KA ltac:(unfold TA_M; lia)
      ltac:(unfold TA_M; lia) ltac:(unfold mbX1; intros; lia) Vret0) as Vret end.
  mb_mono KA mb_X12.
  mb_add HS mb_fly (mb_fly_ok E0 Wc _ B1 U19 E35 E36 E37 Vfly Vcnt Vret) Usp U19 UOW UNOW.
  clear Vfly Vcnt Vret.
  (* 0x84c04 - 0x84c08: M.fly.on, `beqz` *)
  mb_step mbX2.
  mb_br.
  { (* M.fly.on = 0: m_tick *)
    rewrite D35 in Hc. cbn [sv_denot] in Hc. rewrite mbl_eq in Hc by lia. apply Z.eqb_eq in Hc. rename Hc into Hfl.
    rewrite (mbm_ack_off fr B2 ltac:(rewrite BF; exact Hfl)) in SW.
    apply mbm_some_inv in SW. subst B3.
    mb_stepto mbX2 (AF_m_rx + OFF_TICK).
    pmkst HS.
    mb_rk HS E0 regs2 (mb_vals fr B1) (mb_agree regs2 B1) [2%bv; 3%bv; 4%bv] RK.
    pose proof (mb_KA_mono _ _ _ _ _ mb_X24 KA) as KA4.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
      pose proof (mb_chunk E0 Wc ss m 1%nat _ 0%nat 32 8%N (SOff 34 0) (TW.g_now B1) TA_M HS eq_refl U19 eq_refl
        D34 ltac:(cbn; lia)) as VL;
      pose proof (mb_chunk E0 Wc ss m 0%nat _ 0%nat 96 4%N (SOff 35 0) (TW.u_at B1 TW.A_M_fly_on 4) TA_M HS eq_refl
        U19 eq_refl D35' ltac:(cbn; lia)) as VF;
      apply (mb_exit Wc (MRX_PC OFF_TICK) _ (R_TICK Bw' r) (ms_regs m) (ms_mem m) _ B2) end.
    - rewrite (mb_pc OFF_TICK). reflexivity.
    - exact KTICK.
    - exact HJ.
    - exact (eq_trans (RK 2%bv ltac:(mb_in)) Hsp).
    - exact (eq_trans (RK 3%bv ltac:(mb_in)) Hgp).
    - exact (eq_trans (RK 4%bv ltac:(mb_in)) Htp).
    - exact (mb_saved_kept Wc mem2 _ KA4 Hsav).
    - exact (mb_w2 (aview segs (w_H Wc) mem2) _ B1 Htw VL (mb_rest2 Wc mem2 _ B1 Htw KA VF)).
    - unfold R_TICK. split; [exact TK | exact Er]. }
  rewrite D35 in Hc. cbn [sv_denot] in Hc. rewrite mbl_eq in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Hfl.
  (* 0x84c0c - 0x84c30: the ack field against M.fly.counter, `bne` *)
  assert (RCn : 0 <= TW.M_fly_counter B1 < 2 ^ 32) by exact R36.
  mb_step mbX2.
  mb_br.
  { (* ack <> counter: m_tick *)
    rewrite DACK, D36 in Hc. rewrite mbl_ne_sw in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
    rename Hc into Hne.
    rewrite (mbm_ack_ne fr B2 ltac:(rewrite BC; exact Hne)) in SW.
    apply mbm_some_inv in SW. subst B3.
    mb_stepto mbX2 (AF_m_rx + OFF_TICK).
    pmkst HS.
    mb_rk HS E0 regs2 (mb_vals fr B1) (mb_agree regs2 B1) [2%bv; 3%bv; 4%bv] RK.
    pose proof (mb_KA_mono _ _ _ _ _ mb_X24 KA) as KA4.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
      pose proof (mb_chunk E0 Wc ss m 1%nat _ 0%nat 32 8%N (SOff 34 0) (TW.g_now B1) TA_M HS eq_refl U19 eq_refl
        D34 ltac:(cbn; lia)) as VL;
      pose proof (mb_chunk E0 Wc ss m 0%nat _ 0%nat 96 4%N (SOff 35 0) (TW.u_at B1 TW.A_M_fly_on 4) TA_M HS eq_refl
        U19 eq_refl D35' ltac:(cbn; lia)) as VF;
      apply (mb_exit Wc (MRX_PC OFF_TICK) _ (R_TICK Bw' r) (ms_regs m) (ms_mem m) _ B2) end.
    - rewrite (mb_pc OFF_TICK). reflexivity.
    - exact KTICK.
    - exact HJ.
    - exact (eq_trans (RK 2%bv ltac:(mb_in)) Hsp).
    - exact (eq_trans (RK 3%bv ltac:(mb_in)) Hgp).
    - exact (eq_trans (RK 4%bv ltac:(mb_in)) Htp).
    - exact (mb_saved_kept Wc mem2 _ KA4 Hsav).
    - exact (mb_w2 (aview segs (w_H Wc) mem2) _ B1 Htw VL (mb_rest2 Wc mem2 _ B1 Htw KA VF)).
    - unfold R_TICK. split; [exact TK | exact Er]. }
  rewrite DACK, D36 in Hc. rewrite mbl_ne_sw in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
  rename Hc into Heq.
  destruct (mbm_ack_eq fr B2 B3 LB2 ltac:(rewrite BF; exact Hfl) ltac:(rewrite BC; exact Heq) SW)
    as (NI & HMO6 & HB6).
  assert (DACKC : sv_denot E0 (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 26 0) (SLit 16))
      (SAluw ALU_SLL (SOff 22 0) (SLit 24))) (SAlu ALU_OR (SAlu ALU_SLL (SOff 40 0) (SLit 8)) (SOff 39 0)))
    = Z_to_bv 64 (bv_swrap 32 (TW.M_fly_counter B1))) by (rewrite DACK, Heq; reflexivity).
  (* OW.acked, OW.acked_counter and OW.acked_retry join the state *)
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
    pose proof (mb_val_kept Wc mbX2 mem2 (ms_mem m) (TA_OW + 216) 4 _ KA ltac:(unfold TA_OW; lia)
      ltac:(unfold TA_OW; lia) ltac:(unfold mbX2, mbX1, TA_M, TA_OW; intros; lia) Vack0) as Vack end.
  mb_mono KA mb_X23.
  mb_add HS mb_ack (mb_ack_ok E0 Wc _ B1 UOW E38 Vack) Usp U19 UOW UNOW.
  mb_add0 HS mb_acc mb_acc_ok UOW Usp U19 UOW UNOW.
  clear Vack.
  (* 0x84c34 - 0x84c5c: the stores of OW.acked + 1, ack, M.fly.retries and M.fly.on = 0, `bne a5, 1` *)
  mb_step mbX3.
  mb_br.
  { (* M.state <> S_WAKING: m_tick *)
    rewrite D33 in Hc. cbn [sv_denot] in Hc. rewrite mbl_ne in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
    rename Hc into Hs1.
    pose proof (HB6 ltac:(rewrite BS; exact Hs1)) as EB3. subst B3.
    mb_stepto mbX3 (AF_m_rx + OFF_TICK).
    pmkst HS.
    mb_rk HS E0 regs2 (mb_vals fr B1) (mb_agree regs2 B1) [2%bv; 3%bv; 4%bv] RK.
    pose proof (mb_KA_mono _ _ _ _ _ mb_X34 KA) as KA4.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
      pose proof (mb_chunk E0 Wc ss m 3%nat _ 0%nat 32 8%N (SOff 34 0) (TW.g_now B1) TA_M HS eq_refl U19 eq_refl
        D34 ltac:(cbn; lia)) as VL;
      pose proof (mb_chunk E0 Wc ss m 1%nat _ 0%nat 216 4%N _ (TW.OW_acked B1 + 1) TA_OW HS eq_refl UOW eq_refl
        DA1 ltac:(cbn; lia)) as VA;
      pose proof (mb_chunk E0 Wc ss m 0%nat _ 1%nat 224 4%N _ (bv_swrap 32 (TW.M_fly_counter B1)) TA_OW HS eq_refl
        UOW eq_refl DACKC ltac:(cbn; lia)) as VC;
      pose proof (mb_chunk E0 Wc ss m 0%nat _ 0%nat 228 4%N _ (bv_swrap 32 (TW.M_fly_retries B1)) TA_OW HS eq_refl
        UOW eq_refl D37 ltac:(cbn; lia)) as VR;
      pose proof (mb_chunk E0 Wc ss m 2%nat _ 0%nat 96 4%N (SLit 0) 0 TA_M HS eq_refl U19 eq_refl eq_refl
        ltac:(cbn; lia)) as VF;
      apply (mb_exit Wc (MRX_PC OFF_TICK) _ (R_TICK Bw' r) (ms_regs m) (ms_mem m) _ (mb_B6 B2)) end.
    - rewrite (mb_pc OFF_TICK). reflexivity.
    - exact KTICK.
    - exact HJ.
    - exact (eq_trans (RK 2%bv ltac:(mb_in)) Hsp).
    - exact (eq_trans (RK 3%bv ltac:(mb_in)) Hgp).
    - exact (eq_trans (RK 4%bv ltac:(mb_in)) Htp).
    - exact (mb_saved_kept Wc mem2 _ KA4 Hsav).
    - unfold mb_B6. rewrite BA, BC, BRT.
      apply (mb_w6 (aview segs (w_H Wc) mem2) _ B1 (TW.OW_acked B1 + 1) (TW.M_fly_counter B1) (TW.M_fly_retries B1)
        Htw VL VA).
      + intros j Hj. rewrite (VC j Hj). f_equal. apply mb_le_byte_mod. apply EPI.mrx_swrap_mod.
      + intros j Hj. rewrite (VR j Hj). f_equal. apply mb_le_byte_mod. apply EPI.mrx_swrap_mod.
      + exact VF.
      + intros x Hx HN. exact (KA x (mb_tw_in_rng x Hx) HN).
    - unfold R_TICK. split; [exact TK | exact Er]. }
  rewrite D33 in Hc. cbn [sv_denot] in Hc. rewrite mbl_ne in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
  rename Hc into Hs1.
  pose proof (HMO6 ltac:(rewrite BS; exact Hs1)) as HMOB.
  (* S_WAKING: 0x84c60, M.e2_acked = 1, m_maybe_online *)
  mb_mono KA mb_X34.
  mb_add0 HS mb_e2 mb_e2_ok U19 Usp U19 UOW UNOW.
  mb_stepto mbX4 (AF_m_rx + OFF_MO).
  pmkst HS.
  mb_rk HS E0 regs2 (mb_vals fr B1) (mb_agree regs2 B1) [2%bv; 3%bv; 4%bv] RK.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
    pose proof (mb_chunk E0 Wc ss m 4%nat _ 0%nat 32 8%N (SOff 34 0) (TW.g_now B1) TA_M HS eq_refl U19 eq_refl
      D34 ltac:(cbn; lia)) as VL;
    pose proof (mb_chunk E0 Wc ss m 2%nat _ 0%nat 216 4%N _ (TW.OW_acked B1 + 1) TA_OW HS eq_refl UOW eq_refl
      DA1 ltac:(cbn; lia)) as VA;
    pose proof (mb_chunk E0 Wc ss m 1%nat _ 1%nat 224 4%N _ (bv_swrap 32 (TW.M_fly_counter B1)) TA_OW HS eq_refl
      UOW eq_refl DACKC ltac:(cbn; lia)) as VC;
    pose proof (mb_chunk E0 Wc ss m 1%nat _ 0%nat 228 4%N _ (bv_swrap 32 (TW.M_fly_retries B1)) TA_OW HS eq_refl
      UOW eq_refl D37 ltac:(cbn; lia)) as VR;
    pose proof (mb_chunk E0 Wc ss m 3%nat _ 0%nat 96 4%N (SLit 0) 0 TA_M HS eq_refl U19 eq_refl eq_refl
      ltac:(cbn; lia)) as VF;
    pose proof (mb_chunk E0 Wc ss m 0%nat _ 0%nat 16 4%N (SLit 1) 1 TA_M HS eq_refl U19 eq_refl eq_refl
      ltac:(cbn; lia)) as VE;
    apply (mb_exit Wc (MRX_PC OFF_MO) _ (R_MO Bw' r) (ms_regs m) (ms_mem m) _ (TW.set_M_e2_acked (mb_B6 B2) 1)) end.
  - rewrite (mb_pc OFF_MO). reflexivity.
  - exact KMO.
  - exact HJ.
  - exact (eq_trans (RK 2%bv ltac:(mb_in)) Hsp).
  - exact (eq_trans (RK 3%bv ltac:(mb_in)) Hgp).
  - exact (eq_trans (RK 4%bv ltac:(mb_in)) Htp).
  - exact (mb_saved_kept Wc mem2 _ KA Hsav).
  - unfold mb_B6. rewrite BA, BC, BRT.
    apply (mb_w7 (aview segs (w_H Wc) mem2) _ B1 (TW.OW_acked B1 + 1) (TW.M_fly_counter B1) (TW.M_fly_retries B1)
      Htw VL VA).
    + intros j Hj. rewrite (VC j Hj). f_equal. apply mb_le_byte_mod. apply EPI.mrx_swrap_mod.
    + intros j Hj. rewrite (VR j Hj). f_equal. apply mb_le_byte_mod. apply EPI.mrx_swrap_mod.
    + exact VF.
    + exact VE.
    + intros x Hx HN. exact (KA x (mb_tw_in_rng x Hx) HN).
  - unfold R_MO. exists B3. split; [exact HMOB|]. split; [exact TK | exact Er]. }
(* cmd > 0xdf: 0x84b98 - 0x84ba0, `bgeu cmd - 0xe0, 2` *)
rewrite D25 in Hc. cbn [sv_denot] in Hc. rewrite mbl_ge in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc.
rename Hc into HcH.
mb_step mbX1.
mb_br.
{ (* not e0 / e1: 0x84c68, `bne s9, 0xe3` *)
  rewrite D25m in Hc. cbn [sv_denot] in Hc. rewrite mbl_geu_ann in Hc by lia.
  apply negb_true_iff, orb_false_iff in Hc. destruct Hc as [He0 He1]. apply Z.eqb_neq in He0, He1.
  mb_step mbX1.
  mb_br.
  { (* cmd other: m_tick *)
    rewrite D25 in Hc. cbn [sv_denot] in Hc. rewrite mbl_ne in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
    rename Hc into He3.
    rewrite (mbm_sw_none timg_A fr B2 ltac:(lia) ltac:(lia) He0 He1 He3) in SW.
    apply mbm_some_inv in SW. subst B3.
    mb_stepto mbX1 (AF_m_rx + OFF_TICK).
    pmkst HS.
    mb_rk HS E0 regs2 (mb_vals fr B1) (mb_agree regs2 B1) [2%bv; 3%bv; 4%bv] RK.
    pose proof (mb_KA_mono _ _ _ _ _ mb_X14 KA) as KA4.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
      pose proof (mb_chunk E0 Wc ss m 0%nat _ 0%nat 32 8%N (SOff 34 0) (TW.g_now B1) TA_M HS eq_refl U19 eq_refl
        D34 ltac:(cbn; lia)) as VL;
      apply (mb_exit Wc (MRX_PC OFF_TICK) _ (R_TICK Bw' r) (ms_regs m) (ms_mem m) _ B2) end.
    - rewrite (mb_pc OFF_TICK). reflexivity.
    - exact KTICK.
    - exact HJ.
    - exact (eq_trans (RK 2%bv ltac:(mb_in)) Hsp).
    - exact (eq_trans (RK 3%bv ltac:(mb_in)) Hgp).
    - exact (eq_trans (RK 4%bv ltac:(mb_in)) Htp).
    - exact (mb_saved_kept Wc mem2 _ KA4 Hsav).
    - exact (mb_w2 (aview segs (w_H Wc) mem2) _ B1 Htw VL (fun x Hx HN => KA x (mb_tw_in_rng x Hx) HN)).
    - unfold R_TICK. split; [exact TK | exact Er]. }
  rewrite D25 in Hc. cbn [sv_denot] in Hc. rewrite mbl_ne in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
  rename Hc into He3.
  rewrite (mbm_sw_e3 timg_A fr B2 He3), BS in SW. unfold TC.S_ONLINE, TC.S_WAKING in SW.
  (* cmd e3: 0x84c70 - 0x84c78, `bltu 1, M.state - 1` *)
  mb_step mbX1.
  mb_br.
  { (* M.state not S_ONLINE / S_WAKING: m_tick *)
    rewrite DST in Hc. cbn [sv_denot] in Hc. cbn [branch_taken] in Hc. rewrite EPI.mrx_state12 in Hc by exact RS.
    apply negb_true_iff in Hc. rename Hc into Hst.
    rewrite Hst in SW. cbv beta iota in SW.
    apply mbm_some_inv in SW. subst B3.
    mb_stepto mbX1 (AF_m_rx + OFF_TICK).
    pmkst HS.
    mb_rk HS E0 regs2 (mb_vals fr B1) (mb_agree regs2 B1) [2%bv; 3%bv; 4%bv] RK.
    pose proof (mb_KA_mono _ _ _ _ _ mb_X14 KA) as KA4.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
      pose proof (mb_chunk E0 Wc ss m 0%nat _ 0%nat 32 8%N (SOff 34 0) (TW.g_now B1) TA_M HS eq_refl U19 eq_refl
        D34 ltac:(cbn; lia)) as VL;
      apply (mb_exit Wc (MRX_PC OFF_TICK) _ (R_TICK Bw' r) (ms_regs m) (ms_mem m) _ B2) end.
    - rewrite (mb_pc OFF_TICK). reflexivity.
    - exact KTICK.
    - exact HJ.
    - exact (eq_trans (RK 2%bv ltac:(mb_in)) Hsp).
    - exact (eq_trans (RK 3%bv ltac:(mb_in)) Hgp).
    - exact (eq_trans (RK 4%bv ltac:(mb_in)) Htp).
    - exact (mb_saved_kept Wc mem2 _ KA4 Hsav).
    - exact (mb_w2 (aview segs (w_H Wc) mem2) _ B1 Htw VL (fun x Hx HN => KA x (mb_tw_in_rng x Hx) HN)).
    - unfold R_TICK. split; [exact TK | exact Er]. }
  rewrite DST in Hc. cbn [sv_denot] in Hc. cbn [branch_taken] in Hc. rewrite EPI.mrx_state12 in Hc by exact RS.
  apply negb_false_iff in Hc. rename Hc into Hst.
  rewrite Hst in SW. cbv beta iota in SW. unfold TC.R_DESK_DISCONNECT in SW.
  (* 0x84c7c: a0 = 7 (R_DESK_DISCONNECT), m_lost *)
  mb_stepto mbX1 (AF_m_rx + OFF_LOST).
  pmkst HS.
  mb_rk HS E0 regs2 (mb_vals fr B1) (mb_agree regs2 B1) [2%bv; 3%bv; 4%bv] RK.
  mb_reg HS 10%bv (w64 7) RX10 ltac:(reflexivity).
  pose proof (mb_KA_mono _ _ _ _ _ mb_X14 KA) as KA4.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
    pose proof (mb_chunk E0 Wc ss m 0%nat _ 0%nat 32 8%N (SOff 34 0) (TW.g_now B1) TA_M HS eq_refl U19 eq_refl
      D34 ltac:(cbn; lia)) as VL;
    apply (mb_exit Wc (MRX_PC OFF_LOST) _ (R_LOST Bw' r) (ms_regs m) (ms_mem m) _ B2) end.
  - rewrite (mb_pc OFF_LOST). reflexivity.
  - exact KLOST.
  - exact HJ.
  - exact (eq_trans (RK 2%bv ltac:(mb_in)) Hsp).
  - exact (eq_trans (RK 3%bv ltac:(mb_in)) Hgp).
  - exact (eq_trans (RK 4%bv ltac:(mb_in)) Htp).
  - exact (mb_saved_kept Wc mem2 _ KA4 Hsav).
  - exact (mb_w2 (aview segs (w_H Wc) mem2) _ B1 Htw VL (fun x Hx HN => KA x (mb_tw_in_rng x Hx) HN)).
  - unfold R_LOST. exists 7, B3. split; [exact RX10|]. split; [lia|]. split; [exact SW|]. split; [exact TK | exact Er]. }
(* e0 / e1: 0x84ba4 - 0x84ba8, `bltu body_len, 33` *)
rewrite D25m in Hc. cbn [sv_denot] in Hc. rewrite mbl_geu_ann in Hc by lia. apply negb_false_iff in Hc.
assert (Hce : mfb fr 28 = 0xe0 \/ mfb fr 28 = 0xe1)
  by (apply orb_true_iff in Hc; destruct Hc as [H|H]; apply Z.eqb_eq in H; [left|right]; exact H).
clear Hc.
rewrite (mbm_sw_ann timg_A fr B2 Hce) in SW.
mb_step mbX1.
mb_br.
{ (* body_len < 33: m_tick *)
  rewrite D20m in Hc. cbn [sv_denot] in Hc. rewrite mbl_ltu in Hc by lia. apply Z.ltb_lt in Hc. rename Hc into Hbl.
  rewrite (mbm_ann_short timg_A fr B2 ltac:(unfold EPI.mrx_blen, TC.SPEC_ANN_MIN; lia)) in SW.
  apply mbm_some_inv in SW. subst B3.
  mb_stepto mbX1 (AF_m_rx + OFF_TICK).
  pmkst HS.
  mb_rk HS E0 regs2 (mb_vals fr B1) (mb_agree regs2 B1) [2%bv; 3%bv; 4%bv] RK.
  pose proof (mb_KA_mono _ _ _ _ _ mb_X14 KA) as KA4.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
    pose proof (mb_chunk E0 Wc ss m 0%nat _ 0%nat 32 8%N (SOff 34 0) (TW.g_now B1) TA_M HS eq_refl U19 eq_refl
      D34 ltac:(cbn; lia)) as VL;
    apply (mb_exit Wc (MRX_PC OFF_TICK) _ (R_TICK Bw' r) (ms_regs m) (ms_mem m) _ B2) end.
  - rewrite (mb_pc OFF_TICK). reflexivity.
  - exact KTICK.
  - exact HJ.
  - exact (eq_trans (RK 2%bv ltac:(mb_in)) Hsp).
  - exact (eq_trans (RK 3%bv ltac:(mb_in)) Hgp).
  - exact (eq_trans (RK 4%bv ltac:(mb_in)) Htp).
  - exact (mb_saved_kept Wc mem2 _ KA4 Hsav).
  - exact (mb_w2 (aview segs (w_H Wc) mem2) _ B1 Htw VL (fun x Hx HN => KA x (mb_tw_in_rng x Hx) HN)).
  - unfold R_TICK. split; [exact TK | exact Er]. }
rewrite D20m in Hc. cbn [sv_denot] in Hc. rewrite mbl_ltu in Hc by lia. apply Z.ltb_ge in Hc. rename Hc into Hbl.
(* 0x84bac - 0x84bb8: s7 = M.state, s4 = -1, `bne s9, 0xe1` *)
mb_step mbX1.
mb_br.
{ (* cmd e0: ANNT with off = -1 *)
  rewrite D25 in Hc. cbn [sv_denot] in Hc. rewrite mbl_ne in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
  assert (He0 : mfb fr 28 = 0xe0) by (destruct Hce as [H|H]; [exact H | exfalso; exact (Hc H)]).
  clear Hc.
  rewrite (mbm_ann_e0 timg_A fr B2 ltac:(unfold EPI.mrx_blen, TC.SPEC_ANN_MIN; lia) He0) in SW.
  mb_stepto mbX1 (AF_m_rx + OFF_ANNT).
  pmkst HS.
  mb_rk HS E0 regs2 (mb_vals fr B1) (mb_agree regs2 B1) [2%bv; 3%bv; 4%bv; 19%bv; 25%bv] RK.
  mb_reg HS 8%bv (w64 (TI.tf_addr fr + 30)) RX8 ltac:(exact D8).
  mb_reg HS 20%bv (w64 (-1)) RX20 ltac:(cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity).
  mb_reg HS 23%bv (w64 (TW.M_state B1)) RX23 ltac:(rewrite DS0, Z.add_0_r; reflexivity).
  pose proof (mb_KA_mono _ _ _ _ _ mb_X14 KA) as KA4.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
    pose proof (mb_chunk E0 Wc ss m 0%nat _ 0%nat 32 8%N (SOff 34 0) (TW.g_now B1) TA_M HS eq_refl U19 eq_refl
      D34 ltac:(cbn; lia)) as VL;
    apply (mb_exit Wc (MRX_PC OFF_ANNT) _ (R_ANNT fr n sp1 lyc Sc Bw' r) (ms_regs m) (ms_mem m) _ B2) end.
  - rewrite (mb_pc OFF_ANNT). reflexivity.
  - exact KANNT.
  - exact HJ.
  - exact (eq_trans (RK 2%bv ltac:(mb_in)) Hsp).
  - exact (eq_trans (RK 3%bv ltac:(mb_in)) Hgp).
  - exact (eq_trans (RK 4%bv ltac:(mb_in)) Htp).
  - exact (mb_saved_kept Wc mem2 _ KA4 Hsav).
  - exact (mb_w2 (aview segs (w_H Wc) mem2) _ B1 Htw VL (fun x Hx HN => KA x (mb_tw_in_rng x Hx) HN)).
  - unfold R_ANNT. exists (-1).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact (mb_frs_kept Wc mem2 _ KA4 HFRS)|].
    split; [exact HHDR|]. split; [left; exact He0|].
    split; [unfold EPI.mrx_blen, TC.SPEC_ANN_MIN; lia|]. split; [lia|]. split; [intros _; reflexivity|].
    split; [exact RX8|]. split; [exact (eq_trans (RK 19%bv ltac:(mb_in)) R19)|]. split; [exact RX20|].
    split; [rewrite BS; exact RX23|]. split; [exact (eq_trans (RK 25%bv ltac:(mb_in)) R25)|].
    exists B3. split; [exact SW|]. split; [exact TK | exact Er]. }
(* cmd e1: HOST *)
rewrite D25 in Hc. cbn [sv_denot] in Hc. rewrite mbl_ne in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
rename Hc into He1.
mb_stepto mbX1 (AF_m_rx + OFF_HOST).
pmkst HS.
mb_rk HS E0 regs2 (mb_vals fr B1) (mb_agree regs2 B1) [2%bv; 3%bv; 4%bv; 19%bv; 25%bv] RK.
mb_reg HS 8%bv (w64 (TI.tf_addr fr + 30)) RX8 ltac:(exact D8).
mb_reg HS 20%bv (w64 (-1)) RX20 ltac:(cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity).
mb_reg HS 23%bv (w64 (TW.M_state B1)) RX23 ltac:(rewrite DS0, Z.add_0_r; reflexivity).
pose proof (mb_KA_mono _ _ _ _ _ mb_X14 KA) as KA4.
lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?m) =>
  pose proof (mb_chunk E0 Wc ss m 0%nat _ 0%nat 32 8%N (SOff 34 0) (TW.g_now B1) TA_M HS eq_refl U19 eq_refl
    D34 ltac:(cbn; lia)) as VL;
  apply (mb_exit Wc (MRX_PC OFF_HOST) _ (R_HOST fr n sp1 lyc Sc Bw' r) (ms_regs m) (ms_mem m) _ B2) end.
- rewrite (mb_pc OFF_HOST). reflexivity.
- exact KHOST.
- exact HJ.
- exact (eq_trans (RK 2%bv ltac:(mb_in)) Hsp).
- exact (eq_trans (RK 3%bv ltac:(mb_in)) Hgp).
- exact (eq_trans (RK 4%bv ltac:(mb_in)) Htp).
- exact (mb_saved_kept Wc mem2 _ KA4 Hsav).
- exact (mb_w2 (aview segs (w_H Wc) mem2) _ B1 Htw VL (fun x Hx HN => KA x (mb_tw_in_rng x Hx) HN)).
- unfold R_HOST.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact (mb_frs_kept Wc mem2 _ KA4 HFRS)|].
  split; [exact HHDR|]. split; [exact He1|]. split; [unfold EPI.mrx_blen, TC.SPEC_ANN_MIN; lia|].
  split; [exact RX8|]. split; [exact (eq_trans (RK 19%bv ltac:(mb_in)) R19)|]. split; [exact RX20|].
  split; [rewrite BS; exact RX23|]. split; [exact (eq_trans (RK 25%bv ltac:(mb_in)) R25)|].
  exists B3. split; [exact SW|]. split; [exact TK | exact Er].
Qed.

End seg.
