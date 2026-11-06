(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 494 of its 552 lines of code are new or changed and 1866 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/build_and_receive_seg_rel.v, with its module paths and module names changed; 1080 of its 1171 lines of code are new or changed and 461 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_minit: the segment MINIT of the image-A walk of fuzz_transport.asan's
   LLVMFuzzerTestOneInput, Lemma lc_minit_ok : lc_minit_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), from the cut
   SCAL (+0x318, lc_st_scal) to the cut INIT (+0x390, lc_st_init). The lemma takes the kit statement K1
   (lc_rom_view_stmt) as an argument.

   The code (lib/A/Prog/DgnTransportList.v slots 198 .. 227):
     +0x318 .. +0x32c  s3 = M, a0 = M + 8, a1 = 0, a2 = 1640, `jal __asan_memset`;
     +0x330 .. +0x348  `sw s6, 0(s3)` (M.desk_known), `sd s3, 184(s1)`, a0 = M + 4, a1 = DESK, a2 = 6,
                       `jal __asan_memcpy`;
     +0x34c .. +0x38c  the pages of g_nq, g_ncmd and g_rx into a1, a2, a0, `sd a1, 24(s1)`, `sw zero` at g_nq,
                       `sd a2, 80(s1)`, `sw zero` at g_ncmd, `sd zero` at g_rx, a0 = g_s, a3 = notice,
                       `sd a0, 112(s1)`, a1 = s5 (g_cfg), a2 = s4 (io, F + 176), a4 = 0,
                       `jal diginet_session_init`.
   No instrumented check is on the segment.

   The walk:
     run 1, run 2, run 3  the three stretches between the calls, each a run of lib/A/Prog/TransportGRunA.v paj_run_x
                          over the walk's G journal from a fresh symbolic state (the registers at the run's start as
                          atoms 0 .. 31). The stores into M, g_nq, g_ncmd and g_rx are bytes of G, the spill stores
                          bytes of the walk's stack window (W_journalG.v awr_ok_x).
     __asan_memset, __asan_memcpy  TransportGCg.v gx_intrin_at. The destinations are bytes of M (G). M's shadow is
                          the record fact trans_llvmf_cells (its zero range and the redzone cells of the hull). DESK's
                          shadow is LLVMFuzzerTestOneInput_st.v lc_sh_any, its bytes the image's (K1, lc_rom_bytes).
     diginet_session_init  the premise lp_sinit, a G-form callee in the same journal. io is at F + 176 in the walk's
                          side-stack frame (its shadow bytes 22 .. 25 are 0). The world is lc_pro_minit of the cut's
                          world (lm_tw_minit: the memset, the store, the copy and the three stores, row by row), and
                          the model's result is TSess0.v diginet_session_init_m, which is always Some.
   The cut INIT: the core moves from SCAL over the whole segment by lm_core_kept (st.v lc_core_kept with the spill
   area [sp1, sp1 + 192) in the written window); the spill slots of lf_spill_init are read from the runs' chunks; the
   frame's shadow is kept; the meter is the callee's (no charge). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
PaBase DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
diginet_session_config_default_cg diginet_session_config_default diginet_session_init_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TSess0 TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require InitOk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module IOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.InitOk.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* ------------------------------------------------------------------ *)
(* 0. The segment's constants and the image's values                   *)
(* ------------------------------------------------------------------ *)

(* The return offsets of the calls of __asan_memset (+0x32c) and __asan_memcpy (+0x348); that of
   diginet_session_init is the cut INIT (LO_INIT). *)
Definition LM_RET1 : Z := 0x330.
Definition LM_RET2 : Z := 0x34c.
Definition LM_B0 : Z * Z := (0, 0).
Definition LM_Bx : sv := SLit 0.

Section vals. Context {rc : YM05.RunCeil}.
(* The listing's objects and pages the segment names: DESK, M, g_s, notice; the pages of g_nq, g_ncmd and g_rx. *)
Lemma lm_vals : VAL (A_OBJ 7) = TRANS_DESK /\ VAL (A_OBJ 8) = TA_M /\ VAL (A_OBJ 9) = TA_g_s /\
  VAL (A_OBJ 10) = TI.ti_notice timg_A /\ VAL (A_HI 14) = transport_hi 14 /\ VAL (A_HI 15) = transport_hi 15 /\
  VAL (A_HI 16) = TA_g_rx - 1000 /\ transport_hi 14 + 944 = TA_g_nq /\ transport_hi 15 + 972 = TA_g_ncmd.
Proof. vm_compute. repeat split. Qed.

Lemma lm_pc_init : Z_to_bv 64 (BASE + LO_INIT) = w64 (transport_text + LO_INIT).
Proof. unfold w64. f_equal; vm_compute; reflexivity. Qed.
End vals.

(* ------------------------------------------------------------------ *)
(* 1. Bytes                                                            *)
(* ------------------------------------------------------------------ *)

Lemma lm_le0 : forall (n j : nat), YO0f.le_byte 0 n j = 0.
Proof.
intros n j. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l.
reflexivity.
Qed.

(* Byte j of a word holding v, as the little-endian byte of v's n low bytes (n <= 8). *)
Lemma lm_bow : forall v (n j : nat), (j < n)%nat -> (n <= 8)%nat ->
  bv_unsigned (byte_of_word (Z_to_bv 64 v) (Z.of_nat j)) = YO0f.le_byte v n j.
Proof.
intros v n j Hj Hn. unfold byte_of_word, YO0f.le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). change (2 ^ Z.of_N 64) with (2 ^ 64).
change 256 with (2 ^ 8).
apply Z.bits_inj'. intros m Hm.
destruct (Z_lt_le_dec m 8) as [Hl|Hl].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma lm_swrap_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
change (bv_modulus 32) with 4294967296. rewrite Z.mod_small by lia. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The model: the world after the stores                            *)
(* ------------------------------------------------------------------ *)

Lemma lm_len_upd : forall (bs v : list byte) k, length bs = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= TW.W_LEN -> length (TW.upd bs k v) = Z.to_nat TW.W_LEN.
Proof.
intros bs v k HL Hk Hv. rewrite TWL.length_upd; [exact HL | exact Hk |].
rewrite HL, Z2Nat.id by (unfold TW.W_LEN; lia). exact Hv.
Qed.

Lemma lm_len_le : forall (bs : list byte) k, length bs = Z.to_nat TW.W_LEN -> k <= TW.W_LEN ->
  k <= Z.of_nat (length bs).
Proof. intros bs k HL Hk. rewrite HL, Z2Nat.id by (unfold TW.W_LEN; lia). exact Hk. Qed.

Lemma lm_s32_out : forall (bs v : list byte) k k', length bs = Z.to_nat TW.W_LEN -> 0 <= k -> 0 <= k' ->
  (k' + 4 <= k \/ k + Z.of_nat (length v) <= k') -> k + Z.of_nat (length v) <= TW.W_LEN ->
  TW.s32_at (TW.upd bs k v) k' = TW.s32_at bs k'.
Proof.
intros bs v k k' HL Hk Hk' Hd Hv. apply TWL.s32_at_upd_out; [exact Hk | exact Hk' | exact Hd |].
exact (lm_len_le bs _ HL Hv).
Qed.

(* A closed side condition on offsets and lengths, decided. *)
Ltac lm_side :=
  rewrite ?TWL.length_put, ?repeat_length;
  first [ apply Z.leb_le; vm_compute; reflexivity
        | left; apply Z.leb_le; vm_compute; reflexivity
        | right; apply Z.leb_le; vm_compute; reflexivity ].
(* The length of a chain of writes on a world of W_LEN bytes (HL). *)
Ltac lm_len HL :=
  lazymatch goal with
  | |- length (TW.upd _ _ _) = _ => apply lm_len_upd; [lm_len HL | lm_side | lm_side]
  | |- _ => exact HL
  end.

(* The desk_mac_set field of the prologue's world (behind M's zero fill) is the flags byte's bit 2. *)
Lemma lm_dms : forall (D B1 : list byte), length B1 = Z.to_nat TW.W_LEN ->
  TW.Cfg_desk_mac_set (TW.upd (lc_pro_scal D B1) TW.OFF_M (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_M))) =
  Z.land (Z.shiftr (lc_flags D) 2) 1.
Proof.
intros D B1 HL. unfold lc_pro_scal, lc_flags. cbv zeta.
destruct (TOP.fuzz_u8_m D (TOP.fuzz_in_m (Z.of_nat (length D)))) as [c1 flags].
destruct (TOP.fuzz_u8_m D c1) as [c2 v1].
destruct (TOP.fuzz_u8_m D c2) as [c3 v2].
destruct (TOP.fuzz_u16_m D c3) as [c4 v3].
destruct (TOP.fuzz_u8_m D c4) as [c5 v4].
destruct (TOP.fuzz_u16_m D c5) as [c6 v5].
destruct (TOP.fuzz_u16_m D c6) as [c7 v6].
destruct (TOP.fuzz_u16_m D c7) as [c8 v7].
destruct (TOP.fuzz_u8_m D c8) as [c9 v8].
destruct (TOP.fuzz_u16_m D c9) as [c10 v9].
cbv beta iota delta [snd].
unfold TW.Cfg_desk_mac_set, TW.set_g_last_counter, TW.set_g_fail_next, TW.set_g_now, TW.set_g_raw,
  TW.set_Cfg_max_body, TW.set_Cfg_max_cmds, TW.set_Cfg_display_gap_us, TW.set_Cfg_wake_timeout_ms,
  TW.set_Cfg_offline_ms, TW.set_Cfg_backoff_ms, TW.set_Cfg_keepalive_ms, TW.set_Cfg_ack_timeout_ms,
  TW.set_Cfg_max_retries, TW.set_Cfg_desk_mac, TW.set_Cfg_desk_mac_set, TW.set_Cfg_sum_mode,
  TW.set_Cfg_auto_wake, TW.set_Cfg_host_mac.
repeat (rewrite lm_s32_out; [| lm_len HL | lm_side | lm_side | lm_side | lm_side]).
rewrite TWL.s32_at_upd_put; [| lm_side | apply lm_len_le; [lm_len HL | lm_side]].
apply lm_swrap_small. rewrite IOK.land1. pose proof (Z.mod_pos_bound (Z.shiftr flags 2) 2 ltac:(lia)). lia.
Qed.

(* lc_pro_minit as the six writes TWorldG.v's lemmas take. *)
Lemma lm_minit_eq : forall (B19 : list byte) v,
  TW.Cfg_desk_mac_set (TW.upd B19 TW.OFF_M (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_M))) = v ->
  lc_pro_minit B19 =
  TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd B19 (TW.OFF_M + 0) (repeat (Z_to_bv 8 0) (Z.to_nat TW.SZ_M)))
    (TW.OFF_M + 0) (TW.put 4 v)) (TW.OFF_M + 4) TC.DESK) (TW.OFF_g_nq + 0) (TW.put 4 0))
    (TW.OFF_g_ncmd + 0) (TW.put 4 0)) (TW.OFF_g_rx + 0) (TW.put 8 0).
Proof.
intros B19 v Hv. unfold lc_pro_minit. cbv zeta. rewrite Hv.
unfold TW.set_g_rx, TW.set_g_ncmd, TW.set_g_nq, TW.set_M_desk, TW.set_M_desk_known, TW.A_M_desk,
  TW.A_M_desk_known, DSpec.b8.
rewrite !Z.add_0_r. reflexivity.
Qed.

(* diginet_session_init_m always answers. *)
Lemma lm_sinit_some : forall (Bw : list byte) a b c d e f, TS0.diginet_session_init_m Bw a b c d e f = None -> False.
Proof.
intros Bw a b c d e f H. unfold TS0.diginet_session_init_m in H. cbv zeta in H.
repeat match type of H with context [if ?x then _ else _] => destruct x end; discriminate H.
Qed.

(* Readers of the world relation: A on [lo, hi), B elsewhere. *)
Definition lm_ifin (lo hi x : Z) (A B : option Z) : option Z :=
  if Z_le_gt_dec lo x then (if Z_lt_ge_dec x hi then A else B) else B.
Lemma lm_ifin_t : forall lo hi x A B, lo <= x < hi -> lm_ifin lo hi x A B = A.
Proof.
intros lo hi x A B Hx. unfold lm_ifin. destruct (Z_le_gt_dec lo x); [|lia]. destruct (Z_lt_ge_dec x hi); [reflexivity | lia].
Qed.
Lemma lm_ifin_f : forall lo hi x A B, ~ (lo <= x < hi) -> lm_ifin lo hi x A B = B.
Proof.
intros lo hi x A B Hx. unfold lm_ifin. destruct (Z_le_gt_dec lo x); [|reflexivity].
destruct (Z_lt_ge_dec x hi); [lia | reflexivity].
Qed.

Ltac lm_unf := unfold TA_M, TA_g_nq, TA_g_ncmd, TA_g_rx, TW.SZ_M in *.

(* The world relation after M's zero fill, the store at M, the copy at M + 4 and the three stores, from the relation
   at the world before and the bytes the view rd' shows there. *)
Lemma lm_tw_minit : forall (rd rd' : Z -> option Z) (B19 : list byte) v,
  tw_at TMAP_A rd B19 ->
  (forall j, (j < 4)%nat -> rd' (TA_M + 0 + Z.of_nat j) = Some (YO0f.le_byte v 4 j)) ->
  (forall i, 0 <= i < Z.of_nat (length TC.DESK) ->
     rd' (TA_M + 4 + i) = Some (bv_unsigned (nth (Z.to_nat i) TC.DESK (Z_to_bv 8 0)))) ->
  (forall i, 10 <= i < TW.SZ_M -> rd' (TA_M + i) = Some 0) ->
  (forall i, 0 <= i < 4 -> rd' (TA_g_nq + i) = Some 0) ->
  (forall i, 0 <= i < 4 -> rd' (TA_g_ncmd + i) = Some 0) ->
  (forall i, 0 <= i < 8 -> rd' (TA_g_rx + i) = Some 0) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_M <= x < TA_M + TW.SZ_M) -> ~ (TA_g_nq <= x < TA_g_nq + 4) ->
     ~ (TA_g_ncmd <= x < TA_g_ncmd + 4) -> ~ (TA_g_rx <= x < TA_g_rx + 8) -> rd' x = rd x) ->
  tw_at TMAP_A rd'
    (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd B19 (TW.OFF_M + 0) (repeat (Z_to_bv 8 0) (Z.to_nat TW.SZ_M)))
      (TW.OFF_M + 0) (TW.put 4 v)) (TW.OFF_M + 4) TC.DESK) (TW.OFF_g_nq + 0) (TW.put 4 0))
      (TW.OFF_g_ncmd + 0) (TW.put 4 0)) (TW.OFF_g_rx + 0) (TW.put 8 0)).
Proof.
intros rd rd' B19 v Htw HM0 HM4 HMz Hnq Hnc Hrx Hout.
assert (LD : length TC.DESK = 6%nat) by reflexivity.
pose (rdE := fun x => lm_ifin TA_g_rx (TA_g_rx + 8) x (rd x) (rd' x)).
pose (rdD := fun x => lm_ifin TA_g_ncmd (TA_g_ncmd + 4) x (rd x) (rdE x)).
pose (rdC := fun x => lm_ifin TA_g_nq (TA_g_nq + 4) x (rd x) (rdD x)).
pose (rdB := fun x => lm_ifin (TA_M + 4) (TA_M + 10) x (Some 0) (rdC x)).
pose (rdA := fun x => lm_ifin TA_M (TA_M + 4) x (Some 0) (rdB x)).
assert (HA : tw_at TMAP_A rdA (TW.upd B19 (TW.OFF_M + 0) (repeat (Z_to_bv 8 0) (Z.to_nat TW.SZ_M)))).
{ apply (tw_fill_set TMAP_A rd rdA B19 TW.OFF_M TA_M TW.SZ_M 0 0 TW.SZ_M TMAP_A_ok Htw TMAP_A_M);
    [lia | unfold TW.SZ_M; lia | lia | |].
  - intros i Hi. change (0 mod 256) with 0. unfold rdA, rdB, rdC, rdD, rdE.
    destruct (Z_lt_le_dec i 4) as [H4 | H4]; [rewrite lm_ifin_t by lia; reflexivity |].
    rewrite (lm_ifin_f TA_M) by lia.
    destruct (Z_lt_le_dec i 10) as [H10 | H10]; [rewrite lm_ifin_t by lia; reflexivity |].
    rewrite (lm_ifin_f (TA_M + 4)) by lia.
    rewrite (lm_ifin_f TA_g_nq) by (lm_unf; lia). rewrite (lm_ifin_f TA_g_ncmd) by (lm_unf; lia).
    rewrite (lm_ifin_f TA_g_rx) by (lm_unf; lia).
    replace (TA_M + 0 + i) with (TA_M + i) by lia. apply HMz. lia.
  - intros x Hx Hn. unfold TW.SZ_M in Hn. unfold rdA, rdB, rdC, rdD, rdE.
    rewrite (lm_ifin_f TA_M) by lia. rewrite (lm_ifin_f (TA_M + 4)) by lia.
    destruct (Z_le_gt_dec TA_g_nq x) as [N1 | N1]; [destruct (Z_lt_ge_dec x (TA_g_nq + 4)) as [N2 | N2]|].
    + rewrite lm_ifin_t by lia. reflexivity.
    + rewrite (lm_ifin_f TA_g_nq) by lia.
      destruct (Z_le_gt_dec TA_g_ncmd x) as [M1 | M1]; [destruct (Z_lt_ge_dec x (TA_g_ncmd + 4)) as [M2 | M2]|].
      * rewrite lm_ifin_t by lia. reflexivity.
      * rewrite (lm_ifin_f TA_g_ncmd) by lia.
        destruct (Z_le_gt_dec TA_g_rx x) as [P1 | P1]; [destruct (Z_lt_ge_dec x (TA_g_rx + 8)) as [P2 | P2]|].
        -- rewrite lm_ifin_t by lia. reflexivity.
        -- rewrite (lm_ifin_f TA_g_rx) by lia. apply Hout; [exact Hx | | | |]; lm_unf; lia.
        -- rewrite (lm_ifin_f TA_g_rx) by lia. apply Hout; [exact Hx | | | |]; lm_unf; lia.
      * rewrite (lm_ifin_f TA_g_ncmd) by lia.
        destruct (Z_le_gt_dec TA_g_rx x) as [P1 | P1]; [destruct (Z_lt_ge_dec x (TA_g_rx + 8)) as [P2 | P2]|].
        -- lm_unf; lia.
        -- rewrite (lm_ifin_f TA_g_rx) by lia. apply Hout; [exact Hx | | | |]; lm_unf; lia.
        -- rewrite (lm_ifin_f TA_g_rx) by lia. apply Hout; [exact Hx | | | |]; lm_unf; lia.
    + rewrite (lm_ifin_f TA_g_nq) by lia. rewrite (lm_ifin_f TA_g_ncmd) by (lm_unf; lia).
      rewrite (lm_ifin_f TA_g_rx) by (lm_unf; lia).
      apply Hout; [exact Hx | | | |]; lm_unf; lia. }
assert (HB : tw_at TMAP_A rdB
  (TW.upd (TW.upd B19 (TW.OFF_M + 0) (repeat (Z_to_bv 8 0) (Z.to_nat TW.SZ_M))) (TW.OFF_M + 0) (TW.put 4 v))).
{ apply (tw_write TMAP_A rdA rdB _ TW.OFF_M TA_M TW.SZ_M 0 4 v TMAP_A_ok HA TMAP_A_M);
    [lia | unfold TW.SZ_M; lia | |].
  - intros j Hj. unfold rdB, rdC, rdD, rdE.
    rewrite (lm_ifin_f (TA_M + 4)) by lia. rewrite (lm_ifin_f TA_g_nq) by (lm_unf; lia).
    rewrite (lm_ifin_f TA_g_ncmd) by (lm_unf; lia). rewrite (lm_ifin_f TA_g_rx) by (lm_unf; lia).
    exact (HM0 j Hj).
  - intros x Hx Hn. unfold rdA. rewrite (lm_ifin_f TA_M) by lia. reflexivity. }
assert (HC : tw_at TMAP_A rdC
  (TW.upd (TW.upd (TW.upd B19 (TW.OFF_M + 0) (repeat (Z_to_bv 8 0) (Z.to_nat TW.SZ_M))) (TW.OFF_M + 0)
    (TW.put 4 v)) (TW.OFF_M + 4) TC.DESK)).
{ apply (tw_fill TMAP_A rdB rdC _ TW.OFF_M TA_M TW.SZ_M 4 TC.DESK TMAP_A_ok HB TMAP_A_M);
    [lia | rewrite LD; unfold TW.SZ_M; lia | |].
  - intros i Hi. rewrite LD in Hi. unfold rdC, rdD, rdE.
    rewrite (lm_ifin_f TA_g_nq) by (lm_unf; lia).
    rewrite (lm_ifin_f TA_g_ncmd) by (lm_unf; lia). rewrite (lm_ifin_f TA_g_rx) by (lm_unf; lia).
    apply HM4. rewrite LD. lia.
  - intros x Hx Hn. rewrite LD in Hn. unfold rdB. rewrite (lm_ifin_f (TA_M + 4)) by lia. reflexivity. }
assert (HD : tw_at TMAP_A rdD
  (TW.upd (TW.upd (TW.upd (TW.upd B19 (TW.OFF_M + 0) (repeat (Z_to_bv 8 0) (Z.to_nat TW.SZ_M))) (TW.OFF_M + 0)
    (TW.put 4 v)) (TW.OFF_M + 4) TC.DESK) (TW.OFF_g_nq + 0) (TW.put 4 0))).
{ apply (tw_write TMAP_A rdC rdD _ TW.OFF_g_nq TA_g_nq TW.SZ_g_nq 0 4 0 TMAP_A_ok HC TMAP_A_g_nq);
    [lia | unfold TW.SZ_g_nq; lia | |].
  - intros j Hj. rewrite lm_le0. unfold rdD, rdE.
    rewrite (lm_ifin_f TA_g_ncmd) by (lm_unf; lia). rewrite (lm_ifin_f TA_g_rx) by (lm_unf; lia).
    replace (TA_g_nq + 0 + Z.of_nat j) with (TA_g_nq + Z.of_nat j) by lia. apply Hnq. lia.
  - intros x Hx Hn. unfold rdC. rewrite (lm_ifin_f TA_g_nq) by lia. reflexivity. }
assert (HE : tw_at TMAP_A rdE
  (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd B19 (TW.OFF_M + 0) (repeat (Z_to_bv 8 0) (Z.to_nat TW.SZ_M)))
    (TW.OFF_M + 0) (TW.put 4 v)) (TW.OFF_M + 4) TC.DESK) (TW.OFF_g_nq + 0) (TW.put 4 0))
    (TW.OFF_g_ncmd + 0) (TW.put 4 0))).
{ apply (tw_write TMAP_A rdD rdE _ TW.OFF_g_ncmd TA_g_ncmd TW.SZ_g_ncmd 0 4 0 TMAP_A_ok HD TMAP_A_g_ncmd);
    [lia | unfold TW.SZ_g_ncmd; lia | |].
  - intros j Hj. rewrite lm_le0. unfold rdE.
    rewrite (lm_ifin_f TA_g_rx) by (lm_unf; lia).
    replace (TA_g_ncmd + 0 + Z.of_nat j) with (TA_g_ncmd + Z.of_nat j) by lia. apply Hnc. lia.
  - intros x Hx Hn. unfold rdD. rewrite (lm_ifin_f TA_g_ncmd) by lia. reflexivity. }
apply (tw_write TMAP_A rdE rd' _ TW.OFF_g_rx TA_g_rx TW.SZ_g_rx 0 8 0 TMAP_A_ok HE TMAP_A_g_rx);
  [lia | unfold TW.SZ_g_rx; lia | |].
- intros j Hj. rewrite lm_le0.
  replace (TA_g_rx + 0 + Z.of_nat j) with (TA_g_rx + Z.of_nat j) by lia. apply Hrx. lia.
- intros x Hx Hn. unfold rdE. rewrite (lm_ifin_f TA_g_rx) by lia. reflexivity.
Qed.

(* A payload byte of a row of the world table is a byte of G. *)
Lemma lm_inG_row : forall o b n a, In (o, b, n) TMAP_A -> b <= a < b + n -> inG TG.G_HARNESS a.
Proof.
intros o b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma lm_inG_M : forall a, TA_M <= a < TA_M + TW.SZ_M -> inG TG.G_HARNESS a.
Proof. intros a Ha. exact (lm_inG_row _ _ _ a TMAP_A_M Ha). Qed.

(* DESK's six bytes are read-only bytes the walk reads (TRANS_RO_RD). *)
Lemma lm_desk_ro : forall i, 0 <= i < 6 -> trans_in_ro_rd (TRANS_DESK + i).
Proof.
intros i Hi. unfold trans_in_ro_rd. apply Exists_exists. exists (TRANS_DESK, 6). split.
- unfold TRANS_RO_RD, TRANS_RO_GLOBALS. apply in_or_app. right. cbn [In]. do 2 right. left. reflexivity.
- unfold in_zr. cbn [fst snd]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The symbolic states of the three runs                            *)
(* ------------------------------------------------------------------ *)

(* run 2, from +0x330: s3 (atom 19) = M, s1 (atom 9) = sp1; the store at M and the slot sp1 + 184. *)
Definition lm_rM : YP09.region := YP09.mkRegion (Some 19%nat) 0 4 0 4 [].
Definition lm_r184 : YP09.region := YP09.mkRegion (Some 9%nat) 184 192 184 192 [].
Definition lm_ss2 : sstate :=
  mkSS LM_RET1 sr_atoms [lm_rM; lm_r184] None
    (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF TA_M TA_M 5)] [] []).
(* run 3, from +0x34c: the three stores through the pages of g_nq, g_ncmd and g_rx, the slots sp1 + 24, + 80, + 112. *)
Definition lm_rnq : YP09.region := YP09.mkRegion (Some (A_HI 14)) 944 948 944 948 [].
Definition lm_rnc : YP09.region := YP09.mkRegion (Some (A_HI 15)) 972 976 972 976 [].
Definition lm_rrx : YP09.region := YP09.mkRegion (Some (A_HI 16)) 1000 1008 1000 1008 [].
Definition lm_r24 : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 24 32 [].
Definition lm_r80 : YP09.region := YP09.mkRegion (Some 9%nat) 80 88 80 88 [].
Definition lm_r112 : YP09.region := YP09.mkRegion (Some 9%nat) 112 120 112 120 [].
Definition lm_ss3 : sstate :=
  mkSS LM_RET2 sr_atoms [lm_rnq; lm_rnc; lm_rrx; lm_r24; lm_r80; lm_r112] None
    (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (A_HI 14, mkAF (transport_hi 14) (transport_hi 14) 4);
              (A_HI 15, mkAF (transport_hi 15) (transport_hi 15) 2);
              (A_HI 16, mkAF (TA_g_rx - 1000) (TA_g_rx - 1000) 3)] [] []).

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac lm_reg HS r v H tac :=
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
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac lm_region HS i HR :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
(* The awr obligation's regions, computed. *)
Ltac lm_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The windows of a run, each closed by tac. *)
Ltac lm_win tac :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in
  let x := fresh "x" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.
Ltac lm_name HS x :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?m) => rename m into x
  | st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into x
  end.

Section ent. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.

Definition lm_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).

Lemma lm_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (lm_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold lm_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma lm_env_img : forall regs, img_env VAL A_LIM (lm_E regs).
Proof. intros regs. unfold lm_E. apply Eimg_env. Qed.
Lemma lm_agree : forall regs, env_agree 32 (Ereg regs []) (lm_E regs).
Proof.
intros regs. split.
- intros n Hn. unfold lm_E. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity.
- reflexivity.
Qed.
Lemma lm_img_val : forall regs (a : nat) v, (A_TEXT <= a < A_LIM)%nat -> VAL a = v -> bv_unsigned (ew (lm_E regs) a) = v.
Proof. intros regs a v Ha Hv. rewrite (lm_env_img regs a Ha). exact Hv. Qed.

(* The callee-saved registers the segment carries (sp, gp, tp, s0, s1, s2, s4, s5, s6, s9, s10, s11), unchanged. *)
Definition lm_rk (r0 r1 : bvmap 5 word) : Prop :=
  forall n, n = 2 \/ n = 3 \/ n = 4 \/ n = 8 \/ n = 9 \/ n = 18 \/ n = 20 \/ n = 21 \/ n = 22 \/ n = 25 \/ n = 26 \/
    n = 27 -> YK11.getr r1 (Z_to_bv 5 n) = YK11.getr r0 (Z_to_bv 5 n).
Lemma lm_rk_cs : forall n : Z, n = 2 \/ n = 3 \/ n = 4 \/ n = 8 \/ n = 9 \/ n = 18 \/ n = 20 \/ n = 21 \/ n = 22 \/
  n = 25 \/ n = 26 \/ n = 27 -> acallee_saved n.
Proof. intros n Hn. unfold acallee_saved. repeat (destruct Hn as [-> | Hn]; [lia|]). subst n. lia. Qed.
Lemma lm_rk_pres : forall r0 r1 r2, lm_rk r0 r1 -> aregs_preserved r1 r2 -> lm_rk r0 r2.
Proof. intros r0 r1 r2 H1 H2 n Hn. rewrite (H2 n (lm_rk_cs n Hn)). exact (H1 n Hn). Qed.

(* A symbolic state with no region holds of any machine state at its pc. *)
Lemma lm_entry0 : forall (W : world segs) regs mem (pc : Z),
  st_ok_pi segs VAL (lm_E regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The entry state of run 2. *)
Lemma lm_entry2 : forall (W : world segs) regs mem (spv : Z),
  YK11.getr regs 9 = w64 spv -> YK11.getr regs 19 = w64 TA_M ->
  2 ^ 46 <= spv -> spv + 192 <= 2 ^ 47 -> spv mod 32 = 0 ->
  (forall a, spv + 184 <= a < spv + 192 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (lm_E regs) lm_ss2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LM_RET1)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem spv R9 R19 H1 H2 H3 Hp.
  rewrite restrict_mkst_fx. unfold lm_ss2.
  assert (U9 : bv_unsigned (ew (lm_E regs) 9) = spv)
    by (rewrite (lm_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U19 : bv_unsigned (ew (lm_E regs) 19) = TA_M)
    by (rewrite (lm_ew_reg regs 19 19%bv eq_refl), R19; apply unsigned_lit_small; unfold TA_M; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [lm_rM lm_r184 YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U19. split; [unfold TA_M; lia|]. split; [unfold TA_M; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply lm_inG_M.
      unfold TW.SZ_M. lia.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hp. lia.
  - apply pairwise_disjoint_of_extents. unfold lm_rM, lm_r184, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold TA_M.
    repeat split; first [exact I | lia].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U19. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold TA_M; first [lia | reflexivity].
Qed.

(* The entry state of run 3. *)
Lemma lm_entry3 : forall (W : world segs) regs mem (spv : Z),
  YK11.getr regs 9 = w64 spv ->
  2 ^ 46 <= spv -> spv + 192 <= 2 ^ 47 -> spv mod 32 = 0 ->
  (forall a, spv + 24 <= a < spv + 120 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (lm_E regs) lm_ss3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LM_RET2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem spv R9 H1 H2 H3 Hp.
  rewrite restrict_mkst_fx. unfold lm_ss3.
  destruct lm_vals as (_ & _ & _ & _ & V14 & V15 & V16 & E14 & E15).
  assert (U9 : bv_unsigned (ew (lm_E regs) 9) = spv)
    by (rewrite (lm_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U14 : bv_unsigned (ew (lm_E regs) (A_HI 14)) = transport_hi 14)
    by (rewrite (lm_env_img regs (A_HI 14) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)); exact V14).
  assert (U15 : bv_unsigned (ew (lm_E regs) (A_HI 15)) = transport_hi 15)
    by (rewrite (lm_env_img regs (A_HI 15) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)); exact V15).
  assert (U16 : bv_unsigned (ew (lm_E regs) (A_HI 16)) = TA_g_rx - 1000)
    by (rewrite (lm_env_img regs (A_HI 16) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)); exact V16).
  pose proof lf_spill_pages as (_ & _ & _ & _ & P14 & P15).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [lm_rnq lm_rnc lm_rrx lm_r24 lm_r80 lm_r112
           YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U14. split; [rewrite P14; lia|]. split; [rewrite P14; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (transport_hi 14 + o) G_HARNESS_rw).
      apply (lm_inG_row _ _ _ _ TMAP_A_g_nq). unfold TW.SZ_g_nq. lia.
    + rewrite U15. split; [rewrite P15; lia|]. split; [rewrite P15; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (transport_hi 15 + o) G_HARNESS_rw).
      apply (lm_inG_row _ _ _ _ TMAP_A_g_ncmd). unfold TW.SZ_g_ncmd. lia.
    + rewrite U16. split; [unfold TA_g_rx; lia|]. split; [unfold TA_g_rx; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_g_rx - 1000 + o) G_HARNESS_rw).
      apply (lm_inG_row _ _ _ _ TMAP_A_g_rx). unfold TW.SZ_g_rx. lia.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hp. lia.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hp. lia.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hp. lia.
  - apply pairwise_disjoint_of_extents. unfold lm_rnq, lm_rnc, lm_rrx, lm_r24, lm_r80, lm_r112, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U14, U15, U16.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite P14, P15. unfold TA_g_rx.
    repeat split; first [exact I | lia].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U14, U15, U16. rewrite P14, P15.
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold TA_g_rx; first [lia | reflexivity].
Qed.

(* A symbolic register whose value is an atom: the machine register is that atom's value. *)
Lemma lm_reg_atom : forall (W : world segs) E ss ms (n : nat) (r : bv 5) v,
  st_ok segs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = v ->
  YK11.getr (ms_regs ms) r = v.
Proof.
intros W E ss ms n r v HS Hg He. rewrite (st_ok_restrict_reg segs (w_H W) E ss ms r HS), Hg. cbn [sv_denot].
rewrite He, Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

(* The bytes of a chunk, read through the view. *)
Lemma lm_chunk_rd : forall E (H : word -> bool) (mm : word -> option byte) base off (w : N) e j,
  YP09.chunk_ok segs E (mrestrict H mm) base (YP09.mkChunk off (CVal w e)) -> 0 <= j < Z.of_N w ->
  aview segs H mm (base + off + j) = Some (bv_unsigned (byte_of_word (sv_denot E e) j)).
Proof.
intros E H mm base off w e j HC Hj. unfold YP09.chunk_ok in HC.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC.
destruct (HC j Hj) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. injection Hb1 as <-.
change (aview segs H mm (base + off + j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict H mm) (base + off + j))).
rewrite Hb2. reflexivity.
Qed.

(* An 8-byte chunk of a word, read as a word of the view. *)
Lemma lm_chunk_rdword : forall E (H : word -> bool) m base off e (v : word),
  YP09.chunk_ok segs E (mrestrict H m) base (YP09.mkChunk off (CVal 8 e)) -> sv_denot E e = v ->
  rdword (aview segs H m) (base + off) = Some (bv_unsigned v).
Proof.
intros E H m base off e v Hc He.
pose proof (bv_unsigned_in_range 64 v) as Rv. change (bv_modulus 64) with (2 ^ 64) in Rv.
apply AF0x.val_mem_rdword; [exact Rv|].
exact (val_of_chunk_ok segs E (mrestrict H m) base off 8%N e (bv_unsigned v) Hc
  ltac:(rewrite He; symmetry; apply Z_to_bv_bv_unsigned) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* A byte array is kept where every one of its bytes is (LLVMFuzzerTestOneInput_st.v lc_garr8_kept). *)
Lemma lm_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) base l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview segs H' m' (base + j) = aview segs H m (base + j)) ->
  garr8 segs (mrestrict H m) base l -> garr8 segs (mrestrict H' m') base l.
Proof.
intros H H' m m' base l HK HG. apply (garr8_frame segs _ _ _ _ HG). intros a Ha.
apply (mbyte_of_aview segs). replace a with (base + (a - base)) by lia. apply HK. lia.
Qed.

(* The bytes of a byte array are visible. *)
Lemma lm_garr8_vis : forall (H : word -> bool) m q (l : list Z) a, garr8 segs (mrestrict H m) q l ->
  q <= a < q + Z.of_nat (length l) -> aview segs H m a <> None.
Proof.
intros H m q l a HG Ha. destruct (HG (Z.to_nat (a - q)) ltac:(lia)) as [Hv _].
specialize (Hv 0%nat ltac:(lia)). unfold aview.
replace a with (q + Z.of_nat (Z.to_nat (a - q)) + Z.of_nat 0) by lia. rewrite Hv. discriminate.
Qed.
End ent.
(* A run that writes none of those registers keeps them: each is its atom at the run's end. *)
Ltac lm_rk_one HS rg :=
  lazymatch goal with |- YK11.getr (ms_regs ?m) ?r = ?v =>
    refine (lm_reg_atom _ (lm_E rg) _ m _ r v HS _ _); [reflexivity | apply lm_ew_reg; reflexivity] end.
Ltac lm_rk_run HS rg :=
  let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
  repeat (destruct Hn as [-> | Hn]; [lm_rk_one HS rg |]);
  subst n; lm_rk_one HS rg.

(* ------------------------------------------------------------------ *)
(* 4. M's shadow, and the core across the segment                      *)
(* ------------------------------------------------------------------ *)

Section minit. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

(* M's bytes are addressable at every AR state: their shadow is the record's zero range. *)
Lemma lm_M_ra : forall ly S (W : world segs) mem md q n, trans_llvmf_cells B -> @AR rc segs B ly S W mem md ->
  TA_M <= q -> q + n <= TA_M + TW.SZ_M -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF q n.
Proof.
intros ly S W mem md q n (HZ & _) HAR Hq Hn x Hx.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
exists 0. split; [|left; reflexivity].
unfold shadow_of_addr.
assert (Hz := decode_zshadow_rd B ly S W mem md TA_M (TA_M + TW.SZ_M) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(unfold TA_M in *; lia) ltac:(unfold TA_M, TW.SZ_M in *; lia) HZ).
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* A constant byte cell of the record is visible at every AR state. *)
Lemma lm_cell_vis : forall ly S (W : world segs) mem md a v,
  @AR rc segs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> aview segs (w_H W) mem a <> None.
Proof.
intros ly S W mem md a v HAR HC. destruct HAR as (Mm & _).
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mm) _ HC) as Hh.
unfold cell_holds in Hh. cbn [c_at c_w YG0f.c_val z1 c1 aeval] in Hh.
specialize (Hh 0%nat ltac:(lia)). cbn [Z.of_nat] in Hh. rewrite Z.add_0_r in Hh.
rewrite Hh. discriminate.
Qed.

(* The shadow bytes of M's 64-byte hull [0x5df140, 0x5df800): g_last_counter's last granule, three guard granules,
   M's 206 zero granules and six guard granules. *)
Lemma lm_M_vis : forall ly S (W : world segs) mem md, trans_llvmf_cells B -> @AR rc segs B ly S W mem md ->
  forall s, 2148220456 <= s < 2148220672 -> aview segs (w_H W) mem s <> None.
Proof.
intros ly S W mem md HL HAR s Hs.
pose proof HL as (HZ & _ & _ & HC). destruct (HC ly) as (C4 & C9).
destruct (Z_lt_le_dec s 2148220460) as [H1 | H1].
- assert (E : s = 2148220456 \/ s = 2148220457 \/ s = 2148220458 \/ s = 2148220459) by lia.
  destruct E as [-> | [-> | [-> | ->]]].
  + apply (lm_cell_vis ly S W mem md _ 4 HAR).
    replace 2148220456 with (FCells.shadow_addr TA_g_last_counter) by reflexivity. exact C4.
  + apply (lm_cell_vis ly S W mem md _ 0xf9 HAR).
    replace 2148220457 with (FCells.shadow_addr 0x5df148) by reflexivity.
    apply C9. rewrite trans_llvmf_f9_at. cbn [In]. left; reflexivity.
  + apply (lm_cell_vis ly S W mem md _ 0xf9 HAR).
    replace 2148220458 with (FCells.shadow_addr 0x5df150) by reflexivity.
    apply C9. rewrite trans_llvmf_f9_at. cbn [In]. do 1 right; left; reflexivity.
  + apply (lm_cell_vis ly S W mem md _ 0xf9 HAR).
    replace 2148220459 with (FCells.shadow_addr 0x5df158) by reflexivity.
    apply C9. rewrite trans_llvmf_f9_at. cbn [In]. do 2 right; left; reflexivity.
- destruct (Z_lt_le_dec s 2148220666) as [H2 | H2].
  + assert (Hz := decode_zshadow_rd B ly S W mem md TA_M (TA_M + TW.SZ_M) (TA_M + 8 * (s - 2148220460)) HAR
      ltac:(unfold TA_M; replace (6156640 + 8 * (s - 2148220460)) with ((769580 + (s - 2148220460)) * 8) by ring;
            apply Z_mod_mult)
      ltac:(lia) ltac:(unfold TW.SZ_M; lia) HZ).
    replace s with (FCells.shadow_addr (TA_M + 8 * (s - 2148220460))); [rewrite Hz; discriminate|].
    unfold FCells.shadow_addr, FCells.ASAN_K, TA_M.
    replace (6156640 + 8 * (s - 2148220460)) with ((769580 + (s - 2148220460)) * 8) by ring.
    rewrite Z.div_mul by lia. lia.
  + assert (E : s = 2148220666 \/ s = 2148220667 \/ s = 2148220668 \/ s = 2148220669 \/ s = 2148220670 \/
                s = 2148220671) by lia.
    destruct E as [-> | [-> | [-> | [-> | [-> | ->]]]]]; apply (lm_cell_vis ly S W mem md _ 0xf9 HAR).
    * replace 2148220666 with (FCells.shadow_addr 0x5df7d0) by reflexivity.
      apply C9. rewrite trans_llvmf_f9_at. cbn [In]. do 3 right; left; reflexivity.
    * replace 2148220667 with (FCells.shadow_addr 0x5df7d8) by reflexivity.
      apply C9. rewrite trans_llvmf_f9_at. cbn [In]. do 4 right; left; reflexivity.
    * replace 2148220668 with (FCells.shadow_addr 0x5df7e0) by reflexivity.
      apply C9. rewrite trans_llvmf_f9_at. cbn [In]. do 5 right; left; reflexivity.
    * replace 2148220669 with (FCells.shadow_addr 0x5df7e8) by reflexivity.
      apply C9. rewrite trans_llvmf_f9_at. cbn [In]. do 6 right; left; reflexivity.
    * replace 2148220670 with (FCells.shadow_addr 0x5df7f0) by reflexivity.
      apply C9. rewrite trans_llvmf_f9_at. cbn [In]. do 7 right; left; reflexivity.
    * replace 2148220671 with (FCells.shadow_addr 0x5df7f8) by reflexivity.
      apply C9. rewrite trans_llvmf_f9_at. cbn [In]. do 8 right; left; reflexivity.
Qed.

(* The shadow hull of a range of M is visible. *)
Lemma lm_M_hull : forall ly S (W : world segs) mem md q n, trans_llvmf_cells B -> @AR rc segs B ly S W mem md ->
  TA_M <= q -> 0 < n -> q + n <= TA_M + TW.SZ_M -> shadow_hull_vis (aview segs (w_H W) mem) q n.
Proof.
intros ly S W mem md q n HL HAR Hq Hn Hqn s Hs.
apply (lm_M_vis ly S W mem md HL HAR).
unfold shadow_addr, SHADOW_OFF in Hs. unfold TA_M, TW.SZ_M in *.
pose proof (Z.div_mod q 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (q + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (q + n - 1) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (2147450880 + q / 8) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (2147450880 + q / 8) 8 ltac:(lia)) as M3.
pose proof (Z.div_mod (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)) as M4.
lia.
Qed.

(* The journal of lc_core (its first conjunct) at another state. *)
Definition lm_jr (cx : lcx) ly2 S2 (W2 : world segs) mem2 md2 e2 : Prop :=
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 W2 mem2 md2 e2.

(* Every byte of the walk's stack window is present at any memory of the G journal. *)
Lemma lm_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly' S' W' mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* LLVMFuzzerTestOneInput_st.v lc_core_kept for a stretch that also writes the spill area [sp1, sp1 + 192) and keeps
   only the registers lc_core reads (sp, gp, tp, s0, s1). *)
Lemma lm_core_kept : forall cx ly' S' W' regs' mem' md' e (X : Z) ly2 S2 (W2 : world segs) regs2 mem2 md2 e2,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W' regs' mem' md' e ->
  lm_jr cx ly2 S2 W2 mem2 md2 e2 ->
  frames S2 = frames S' ->
  Permutation (ablocks B ly2 S2) (ablocks B ly' S') ->
  (forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 ->
     YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)) ->
  0 <= X <= LLVMF_STK - 336 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx + 192) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  (forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
     aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W') mem' (b + i)) ->
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  @lc_core rc B cx ly2 S2 W2 regs2 mem2 md2 e2.
Proof.
intros cx ly' S' W' regs' mem' md' e X ly2 S2 W2 regs2 mem2 md2 e2 LAWS HB HC HJ2 HFR2 HP2 HPR HX KA KB KF.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
destruct HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
pose proof HJ2 as (_ & _ & (memS2 & HJd2 & _) & _).
pose proof HJd2 as (HAR2 & Hly2 & _).
destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
change (2 ^ 47) with 140737488355328 in H47.
pose proof asan_consts as ((CVlo & CVhi) & _).
assert (KAhi : forall a, lc_sp1 cx + 192 <= a <= lc_sp0 cx ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a).
{ intros a Ha. apply KA; [change (2 ^ 64) with 18446744073709551616; lia | lia]. }
assert (KFb : forall a, lc_F cx <= a < lc_F cx + LF_FBYTES ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) by (intros a Ha; apply KF; left; exact Ha).
split; [exact HJ2|].
split; [rewrite HFR2; exact Hfrs|].
split; [exact EF2|].
split; [exact (Permutation_trans HP2 HPERM)|].
split; [exact (eq_trans (HPR 2 (or_introl eq_refl)) Rsp)|].
split; [exact (eq_trans (HPR 8 (or_intror (or_intror (or_intror (or_introl eq_refl))))) R8)|].
split; [exact (eq_trans (HPR 9 (or_intror (or_intror (or_intror (or_intror eq_refl))))) R9)|].
split; [exact (eq_trans (HPR 3 (or_intror (or_introl eq_refl))) Rgp)|].
split; [exact (eq_trans (HPR 4 (or_intror (or_intror (or_introl eq_refl)))) Rtp)|].
split; [exact Hsp1|]. split; [exact Hsp1al|].
split.
{ unfold lc_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros o Ho.
  assert (Hor : 8 <= fst o <= 104).
  { unfold LF_SAVED in Ho. repeat (destruct Ho as [<- | Ho]; [cbn; lia|]). destruct Ho. }
  rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W2) mem2) (lc_sp0 cx - fst o))
    by (intros j Hj; apply KAhi; unfold LF_FRAME in Hsp1; lia).
  exact (HSAV o Ho). }
split; [exact HF4096|]. split; [exact HFal|]. split; [exact HFceil|].
split.
{ intros a Ha. apply (apresent_transfer segs (w_H W') (w_H W2) mem' mem2 a).
  - unfold LF_FBYTES in *. change (2 ^ 64) with 18446744073709551616. lia.
  - apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) a HARg HFin).
    rewrite HFaddr. change (fs_frame_bytes LF_CID) with LF_FBYTES. exact Ha.
  - exact (KFb a Ha).
  - exact (HFpres a Ha). }
split; [rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W2) mem2) (lc_F cx + LF_FBYTES - 8))
          by (intros j Hj; apply KFb; unfold LF_FBYTES in *; lia); exact HFL|].
destruct HIN as (HPAYg & HPAYv).
destruct (Z_lt_le_dec 0 (l_n cx)) as [Hn0 | Hn0].
- pose proof (HINg Hn0) as InP.
  pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
  split.
  + apply (lc_garr8_kept (w_H W') (w_H W2) mem' mem2 (l_p cx) _); [|exact HPAYg].
    intros j Hj. rewrite length_map in Hj. destruct Hn as (_ & Hnl). rewrite <- Hnl in Hj.
    exact (KB _ _ j InP ltac:(lia)).
  + intros i Hi. rewrite (KB _ _ i InP ltac:(lia)). exact (HPAYv i Hi).
- destruct Hn as (Hn1 & Hnl). split.
  + destruct (l_pl cx) as [|b0 pl0] eqn:Epl; [apply garr8_nil|]. exfalso. cbn [length] in Hnl. lia.
  + intros i Hi. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The segment                                                      *)
(* ------------------------------------------------------------------ *)

Lemma lc_minit_ok (K1 : lc_rom_view_stmt B MT XL RLO RHI) : lc_minit_stmt B MT XL RLO RHI.
Proof.
unfold lc_minit_stmt. intros HP cx W' c' HB HST.
pose proof HP as [_ HCELLS _ _ _ HLL HGU HGN HRU HRE _ _ LAWS MTL _ _ _ _ _ _ _ _ _ HMC _ HMS HSIN
  _ _ _ _ _ _ _ _ _ _ _ _ _ _].
destruct HST as (ly' & S' & regs' & mem' & md' & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMET & HCUR &
  R22 & R21 & R20 & HW0 & HCD & HTW).
pose proof (K1 HP cx ly' S' W' regs' mem' md' 0 HB HC) as HROM.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' 0 HB HC) as GEO.
destruct GEO as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
destruct HFR as [R18 R26]. destruct HCUR as [R25 R27]. destruct HMET as [HMO HMOK]. destruct HW0 as [HTW0 HL0].
pose proof HB as HB'. unfold lc_base, tfib_lib_pre_x in HB'.
destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
pose proof (G_HARNESS_gx_ok B HGU) as HGX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
destruct (frames_bounds segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) HARg HFin) as (FB1 & FB2 & FB3).
rewrite HFaddr in FB1, FB2, FB3. change (fs_frame_bytes LF_CID) with 256 in FB2, FB3.
set (sp0 := lc_sp0 cx) in *. set (sp1 := lc_sp1 cx) in *. set (F := lc_F cx) in *.
unfold LF_FRAME in Hsp1. unfold LF_FBYTES in HFceil, HFpres, HFL. unfold LLVMF_STK in Hslo.
assert (EST : ESTACK = 4096) by reflexivity.
(* the model *)
assert (HL1 : length B1 = Z.to_nat TW.W_LEN).
{ rewrite (scfg_model Bw0 B1 HL0 HCD). rewrite TWL.length_upd; [exact HL0 | unfold TW.OFF_g_cfg; lia |].
  rewrite scfg_len60, HL0, Z2Nat.id by (unfold TW.W_LEN; lia). unfold TW.OFF_g_cfg, TW.W_LEN. lia. }
pose proof (lm_dms (l_pl cx) B1 HL1) as HDMS.
pose proof (lm_minit_eq (lc_pro_scal (l_pl cx) B1) _ HDMS) as HMEQ.
set (dms := Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) in *.
assert (Hdms : 0 <= dms < 2) by (unfold dms; rewrite IOK.land1; apply Z.mod_pos_bound; lia).
destruct (TS0.diginet_session_init_m (lc_pro_minit (lc_pro_scal (l_pl cx) B1)) 0 (TI.ti_io_send timg_A)
  (TI.ti_io_recv timg_A) (TI.ti_io_now timg_A) (TI.ti_notice timg_A) 0) as [[B25 r] |] eqn:EI;
  [| exfalso; exact (lm_sinit_some _ _ _ _ _ _ _ EI)].
(* ---- run 1, +0x318 .. +0x32c ---- *)
pose proof (@lm_entry0 (l_fx cx) rc W' regs' mem' LO_SCAL) as HS.
assert (HEI : img_env VAL A_LIM (lm_E regs')) by apply lm_env_img.
assert (SHOK : sh_ok segs LM_Bx (@nil shent) (lm_E regs') (mrestrict (w_H W') mem')) by constructor.
pose proof (@paj_run_x (l_fx cx) rc AE2k.tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUN.
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + LO_SCAL)) mem'
    (YK11.seg_rom segs)) md') Q) end.
paj_run_tok RUN HS HJ SHOK LM_B0.
{ lm_awr_rs. apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md') mat md') in *. clearbody md1. clear mat.
lm_name HS ms1.
assert (K1m : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms1) a = aview segs (w_H W') mem' a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [lm_win ltac:(idtac) | exact Ha | intros []]. }
assert (G1m : forall a, apresent (w_H W') mem' a -> apresent (w_H W') (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (RK1 : lm_rk regs' (ms_regs ms1)) by (lm_rk_run HS regs').
destruct lm_vals as (VO7 & VO8 & VO9 & VO10 & VH14 & VH15 & VH16 & E14 & E15).
assert (Hsp1lo : 2 ^ 46 <= sp1) by (change (2 ^ 46) with 70368744177664; lia).
assert (Hsp0hi : sp0 <= 2 ^ 47) by (change (2 ^ 47) with 140737488355328 in *; lia).
assert (H16 : (sp1 - sp0) mod 16 = 0).
{ pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
  replace (sp1 - sp0) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by lia. apply Z_mod_mult. }
lm_reg HS (Z_to_bv 5 10) (w64 (TA_M + 8)) Q10
  ltac:(cbn [sv_denot]; rewrite (lm_img_val regs' 249 TA_M ltac:(unfold A_TEXT, A_LIM; lia) VO8); reflexivity).
lm_reg HS (Z_to_bv 5 11) (w64 0) Q11 ltac:(reflexivity).
lm_reg HS (Z_to_bv 5 12) (w64 1640) Q12 ltac:(reflexivity).
lm_reg HS (Z_to_bv 5 19) (w64 TA_M) Q19
  ltac:(cbn [sv_denot]; rewrite (lm_img_val regs' 249 TA_M ltac:(unfold A_TEXT, A_LIM; lia) VO8); reflexivity).
lm_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LM_RET1)) Q1 ltac:(apply codeptr_val; apply lm_env_img).
assert (Q2 : YK11.getr (ms_regs ms1) (2%bv : bv 5) = w64 sp1) by exact (eq_trans (RK1 2 ltac:(lia)) Rsp).
assert (Q3 : YK11.getr (ms_regs ms1) (3%bv : bv 5) = w64 (as_gp B)) by exact (eq_trans (RK1 3 ltac:(lia)) Rgp).
assert (Q4 : YK11.getr (ms_regs ms1) (4%bv : bv 5) = w64 (as_tp B)) by exact (eq_trans (RK1 4 ltac:(lia)) Rtp).
assert (HSP1 : spZ (ms_regs ms1) = sp1) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
(* ---- +0x32c: __asan_memset (M + 8, 0, 1640) ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc AE2k.tfib_sink_head segs B LAWS transport_segs_low OSet
    (transport_sigma TS___asan_memset) (HMS (l_fx cx)) TG.G_HARNESS W' (ms_regs ms1) (ms_mem ms1)
    _ _ _ _ _ _ _ _ _ ly' S' md1 0 (TA_M + 8) 0 1640 (sp1 - sp0) (Z_to_bv 64 (BASE + LM_RET1))
    HGX G_HARNESS_rw HJ Q10 Q11 Q12).
  - lia.
  - unfold TA_M; lia.
  - unfold TA_M; lia.
  - rewrite HSP1. lia.
  - exact H16.
  - lia.
  - unfold LLVMF_STK. rewrite EST. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold LM_RET1; lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right. apply lm_inG_M.
    unfold TW.SZ_M. lia.
  - left. unfold kLowMemEnd, TA_M. lia.
  - apply (lm_M_ra _ _ _ _ _ _ _ HLL HAR1); unfold TW.SZ_M; lia.
  - intros _. apply (lm_M_hull _ _ _ _ _ _ _ HLL HAR1); unfold TW.SZ_M; lia.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset2 & Heff2 & Hgr2).
assert (K2m : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 8 <= a < TA_M + 1648) -> ~ (sp1 - ESTACK <= a < sp1) ->
  aview segs (w_H W') mem2 a = aview segs (w_H W') (ms_mem ms1) a).
{ intros a Ha H1 H2. apply Heff2; [exact Ha | lia | lia]. }
clear Heff2.
assert (RK2 : lm_rk regs' regs2) by exact (lm_rk_pres _ _ _ RK1 HP2).
assert (P9 : YK11.getr regs2 9 = w64 sp1) by exact (eq_trans (RK2 9 ltac:(lia)) R9).
assert (P19 : YK11.getr regs2 19 = w64 TA_M) by exact (eq_trans (HP2 19 ltac:(unfold acallee_saved; lia)) Q19).
(* ---- run 2, +0x330 .. +0x348 ---- *)
repeat match goal with H : img_env _ _ _ |- _ => clear H end. clear HS SHOK.
pose proof (@lm_entry2 (l_fx cx) rc W' regs2 mem2 sp1 P9 P19 Hsp1lo ltac:(lia) Hsp1al
  ltac:(intros a Ha; apply (lm_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); unfold LLVMF_STK; lia)) as HS.
assert (HEI : img_env VAL A_LIM (lm_E regs2)) by apply lm_env_img.
assert (SHOK : sh_ok segs LM_Bx (@nil shent) (lm_E regs2) (mrestrict (w_H W') mem2)) by constructor.
assert (U9 : bv_unsigned (ew (lm_E regs2) 9) = sp1)
  by (rewrite (lm_ew_reg regs2 9 9%bv eq_refl), P9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew (lm_E regs2) 19) = TA_M)
  by (rewrite (lm_ew_reg regs2 19 19%bv eq_refl), P19; apply unsigned_lit_small; unfold TA_M; lia).
paj_run_tok RUN HS HJ2 SHOK LM_B0.
{ lm_awr_rs.
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19 in Ha; apply lm_inG_M;
     unfold TW.SZ_M; lia |].
  apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha;
     left; split; [unfold awr_byte; left; unfold LLVMF_STK; lia | lia] |].
  apply awr_ok_x_nil. }
set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
lm_name HS ms2.
assert (K3m : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M <= a < TA_M + 4) -> ~ (sp1 + 184 <= a < sp1 + 192) ->
  aview segs (w_H W') (ms_mem ms2) a = aview segs (w_H W') mem2 a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _ (fun x => (TA_M <= x < TA_M + 4) \/ (sp1 + 184 <= x < sp1 + 192)) HFr);
    [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  lm_win ltac:(rewrite ?U9, ?U19 in Hx; first [left; lia | right; lia]). }
assert (G3m : forall a, apresent (w_H W') mem2 a -> apresent (w_H W') (ms_mem ms2) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (RK3 : lm_rk regs' (ms_regs ms2)).
{ apply (lm_rk_pres _ regs2); [exact RK2|].
  apply (aregs_preserved_of_st_ok segs (w_H W') (lm_E regs2) _ ms2 regs2 [] HS);
    [apply lm_agree | vm_compute; reflexivity]. }
lm_region HS 0%nat RG0. lm_region HS 1%nat RG1.
destruct RG0 as (_ & _ & _ & HC0). cbn [YP09.r_base YP09.r_chunks base_val] in HC0. rewrite U19 in HC0.
apply Forall_inv in HC0.
destruct RG1 as (_ & _ & _ & HC1). cbn [YP09.r_base YP09.r_chunks base_val] in HC1. rewrite U9 in HC1.
apply Forall_inv in HC1.
assert (P22 : YK11.getr regs2 22 = w64 dms) by exact (eq_trans (RK2 22 ltac:(lia)) R22).
assert (VM0 : forall j, (j < 4)%nat ->
  aview segs (w_H W') (ms_mem ms2) (TA_M + 0 + Z.of_nat j) = Some (YO0f.le_byte dms 4 j)).
{ intros j Hj. rewrite (lm_chunk_rd _ _ _ _ _ _ _ _ HC0) by (cbn; lia).
  cbn [sv_denot]. rewrite (eq_trans (lm_ew_reg regs2 22 22%bv eq_refl) P22), Z.add_0_r.
  unfold w64 at 1. rewrite Z_to_bv_bv_unsigned. f_equal. exact (lm_bow dms 4 j Hj ltac:(lia)). }
assert (VS184 : rdword (aview segs (w_H W') (ms_mem ms2)) (sp1 + 184) = Some TA_M).
{ replace (Some TA_M) with (Some (bv_unsigned (w64 TA_M))) by (unfold w64; rewrite unsigned_lit_small by (unfold TA_M; lia); reflexivity).
  apply (lm_chunk_rdword _ _ _ _ _ _ (w64 TA_M) HC1).
  cbn [sv_denot]. rewrite (eq_trans (lm_ew_reg regs2 19 19%bv eq_refl) P19), Z.add_0_r.
  apply Z_to_bv_bv_unsigned. }
clear HC0 HC1.
(* DESK's bytes at the memory of the call: the image's *)
assert (KD3 : forall i, 0 <= i < 6 -> aview segs (w_H W') (ms_mem ms2) (TRANS_DESK + i) =
  Some (bv_unsigned (nth (Z.to_nat i) TC.DESK (Z_to_bv 8 0)))).
{ intros i Hi.
  rewrite K3m by (unfold TA_M, TRANS_DESK; lia).
  rewrite K2m by (unfold TRANS_DESK, TA_M; lia).
  rewrite K1m by (unfold TRANS_DESK; lia).
  rewrite HROM by (apply lm_desk_ro; exact Hi).
  replace (TRANS_DESK + i) with (TRANS_DESK + Z.of_nat (Z.to_nat i)) by lia.
  apply lc_rom_bytes; [unfold lc_rom_tab; cbn [In]; right; left; reflexivity | change (length TC.DESK) with 6%nat; lia]. }
lm_reg HS (Z_to_bv 5 10) (w64 (TA_M + 4)) Q10b ltac:(cbn [sv_denot]; rewrite U19; reflexivity).
lm_reg HS (Z_to_bv 5 11) (w64 TRANS_DESK) Q11b
  ltac:(cbn [sv_denot]; rewrite (lm_img_val regs2 248 TRANS_DESK ltac:(unfold A_TEXT, A_LIM; lia) VO7), Z.add_0_r;
        reflexivity).
lm_reg HS (Z_to_bv 5 12) (w64 6) Q12b ltac:(reflexivity).
lm_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LM_RET2)) Q1b ltac:(apply codeptr_val; apply lm_env_img).
assert (Q2b : YK11.getr (ms_regs ms2) (2%bv : bv 5) = w64 sp1) by exact (eq_trans (RK3 2 ltac:(lia)) Rsp).
assert (Q3b : YK11.getr (ms_regs ms2) (3%bv : bv 5) = w64 (as_gp B)) by exact (eq_trans (RK3 3 ltac:(lia)) Rgp).
assert (Q4b : YK11.getr (ms_regs ms2) (4%bv : bv 5) = w64 (as_tp B)) by exact (eq_trans (RK3 4 ltac:(lia)) Rtp).
assert (HSP2 : spZ (ms_regs ms2) = sp1) by (unfold spZ; rewrite Q2b; unfold w64; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR3.
pose proof (lc_sh_any B ly' HCELLS HLL (TRANS_DESK, 6)
  ltac:(unfold lc_ro_ranges; cbn [In]; right; left; reflexivity)) as SHD. cbn [fst snd] in SHD.
(* ---- +0x348: __asan_memcpy (M + 4, DESK, 6) ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc AE2k.tfib_sink_head segs B LAWS transport_segs_low OCpy
    (transport_sigma TS___asan_memcpy) (HMC (l_fx cx)) TG.G_HARNESS W' (ms_regs ms2) (ms_mem ms2)
    _ _ _ _ _ _ _ _ _ ly' S' md3 0 (TA_M + 4) TRANS_DESK 6 (sp1 - sp0) (Z_to_bv 64 (BASE + LM_RET2))
    HGX G_HARNESS_rw HJ2 Q10b Q11b Q12b).
  - lia.
  - unfold TA_M; lia.
  - unfold TA_M; lia.
  - rewrite HSP2. lia.
  - exact H16.
  - lia.
  - unfold LLVMF_STK. rewrite EST. lia.
  - exact Q3b.
  - exact Q4b.
  - exact Q1b.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold LM_RET2; lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ2|]. intros a Ha. right. apply lm_inG_M.
    unfold TW.SZ_M. lia.
  - left. unfold kLowMemEnd, TA_M. lia.
  - apply (lm_M_ra _ _ _ _ _ _ _ HLL HAR3); unfold TW.SZ_M; lia.
  - intros _. apply (lm_M_hull _ _ _ _ _ _ _ HLL HAR3); unfold TW.SZ_M; lia.
  - split; [unfold TRANS_DESK; lia|]. split; [unfold TRANS_DESK; lia|]. split.
    + intros a Ha. split.
      * replace a with (TRANS_DESK + (a - TRANS_DESK)) by lia. rewrite KD3 by lia. discriminate.
      * rewrite HSP2. unfold TRANS_DESK in Ha. lia.
    + split; [right; unfold TRANS_DESK, TA_M; lia|]. split; [left; unfold kLowMemEnd, TRANS_DESK; lia|].
      destruct (SHD ly' S' W' (ms_mem ms2) md3 HAR3) as [RA HU]. split; [exact RA | intros _; exact HU]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & _ & Hcpy4 & Heff4 & Hgr4).
assert (K4m : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 4 <= a < TA_M + 10) -> ~ (sp1 - ESTACK <= a < sp1) ->
  aview segs (w_H W') mem4 a = aview segs (w_H W') (ms_mem ms2) a).
{ intros a Ha H1 H2. apply Heff4; [exact Ha | lia | lia]. }
clear Heff4.
assert (RK4 : lm_rk regs' regs4) by exact (lm_rk_pres _ _ _ RK3 HP4).
assert (P9c : YK11.getr regs4 9 = w64 sp1) by exact (eq_trans (RK4 9 ltac:(lia)) R9).
(* ---- run 3, +0x34c .. +0x38c ---- *)
repeat match goal with H : img_env _ _ _ |- _ => clear H end. clear HS SHOK.
pose proof (@lm_entry3 (l_fx cx) rc W' regs4 mem4 sp1 P9c Hsp1lo ltac:(lia) Hsp1al
  ltac:(intros a Ha; apply (lm_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4); unfold LLVMF_STK; lia)) as HS.
assert (HEI : img_env VAL A_LIM (lm_E regs4)) by apply lm_env_img.
assert (SHOK : sh_ok segs LM_Bx (@nil shent) (lm_E regs4) (mrestrict (w_H W') mem4)) by constructor.
assert (U9c : bv_unsigned (ew (lm_E regs4) 9) = sp1)
  by (rewrite (lm_ew_reg regs4 9 9%bv eq_refl), P9c; apply unsigned_lit_small; lia).
assert (U414 : bv_unsigned (ew (lm_E regs4) 414%nat) = transport_hi 14)
  by exact (lm_img_val regs4 414 _ ltac:(unfold A_TEXT, A_LIM; lia) VH14).
assert (U415 : bv_unsigned (ew (lm_E regs4) 415%nat) = transport_hi 15)
  by exact (lm_img_val regs4 415 _ ltac:(unfold A_TEXT, A_LIM; lia) VH15).
assert (U416 : bv_unsigned (ew (lm_E regs4) 416%nat) = TA_g_rx - 1000)
  by exact (lm_img_val regs4 416 _ ltac:(unfold A_TEXT, A_LIM; lia) VH16).
paj_run_tok RUN HS HJ4 SHOK LM_B0.
{ lm_awr_rs.
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U414 in Ha;
     apply (lm_inG_row _ _ _ _ TMAP_A_g_nq); unfold TW.SZ_g_nq; lia |].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U415 in Ha;
     apply (lm_inG_row _ _ _ _ TMAP_A_g_ncmd); unfold TW.SZ_g_ncmd; lia |].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U416 in Ha;
     apply (lm_inG_row _ _ _ _ TMAP_A_g_rx); unfold TW.SZ_g_rx; lia |].
  do 3 (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9c in Ha;
     left; split; [unfold awr_byte; left; unfold LLVMF_STK; lia | lia] |]).
  apply awr_ok_x_nil. }
set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
lm_name HS ms3.
assert (K5m : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_g_nq <= a < TA_g_nq + 4) -> ~ (TA_g_ncmd <= a < TA_g_ncmd + 4) ->
  ~ (TA_g_rx <= a < TA_g_rx + 8) -> ~ (sp1 + 24 <= a < sp1 + 32) -> ~ (sp1 + 80 <= a < sp1 + 88) ->
  ~ (sp1 + 112 <= a < sp1 + 120) -> aview segs (w_H W') (ms_mem ms3) a = aview segs (w_H W') mem4 a).
{ intros a Ha H1 H2 H3 H4 H5 H6.
  apply (kept_of_frame _ _ _ _ _ (fun x => (TA_g_nq <= x < TA_g_nq + 4) \/ (TA_g_ncmd <= x < TA_g_ncmd + 4) \/
    (TA_g_rx <= x < TA_g_rx + 8) \/ (sp1 + 24 <= x < sp1 + 32) \/ (sp1 + 80 <= x < sp1 + 88) \/
    (sp1 + 112 <= x < sp1 + 120)) HFr); [| exact Ha | tauto].
  lm_win ltac:(rewrite ?U9c, ?U414, ?U415, ?U416 in Hx;
    first [left; lia | right; left; lia | right; right; left; lia | do 3 right; left; lia | do 4 right; left; lia |
           do 5 right; lia]). }
assert (G5m : forall a, apresent (w_H W') mem4 a -> apresent (w_H W') (ms_mem ms3) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (RK5 : lm_rk regs' (ms_regs ms3)).
{ apply (lm_rk_pres _ regs4); [exact RK4|].
  apply (aregs_preserved_of_st_ok segs (w_H W') (lm_E regs4) _ ms3 regs4 [] HS);
    [apply lm_agree | vm_compute; reflexivity]. }
pose proof lf_spill_pages as (_ & _ & _ & _ & P14 & P15).
lm_region HS 0%nat RH0. lm_region HS 1%nat RH1. lm_region HS 2%nat RH2.
lm_region HS 3%nat RH3. lm_region HS 4%nat RH4. lm_region HS 5%nat RH5.
destruct RH0 as (_ & _ & _ & HD0). cbn [YP09.r_base YP09.r_chunks base_val] in HD0. rewrite U414 in HD0.
apply Forall_inv in HD0.
destruct RH1 as (_ & _ & _ & HD1). cbn [YP09.r_base YP09.r_chunks base_val] in HD1. rewrite U415 in HD1.
apply Forall_inv in HD1.
destruct RH2 as (_ & _ & _ & HD2). cbn [YP09.r_base YP09.r_chunks base_val] in HD2. rewrite U416 in HD2.
apply Forall_inv in HD2.
destruct RH3 as (_ & _ & _ & HD3). cbn [YP09.r_base YP09.r_chunks base_val] in HD3. rewrite U9c in HD3.
apply Forall_inv in HD3.
destruct RH4 as (_ & _ & _ & HD4). cbn [YP09.r_base YP09.r_chunks base_val] in HD4. rewrite U9c in HD4.
apply Forall_inv in HD4.
destruct RH5 as (_ & _ & _ & HD5). cbn [YP09.r_base YP09.r_chunks base_val] in HD5. rewrite U9c in HD5.
apply Forall_inv in HD5.
assert (VNQ : forall i, 0 <= i < 4 -> aview segs (w_H W') (ms_mem ms3) (TA_g_nq + i) = Some 0).
{ intros i Hi. rewrite <- E14. rewrite (lm_chunk_rd _ _ _ _ _ _ _ _ HD0) by (cbn; lia). cbn [sv_denot].
  replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (lm_bow 0 4 (Z.to_nat i)) by lia. rewrite lm_le0.
  reflexivity. }
assert (VNC : forall i, 0 <= i < 4 -> aview segs (w_H W') (ms_mem ms3) (TA_g_ncmd + i) = Some 0).
{ intros i Hi. rewrite <- E15. rewrite (lm_chunk_rd _ _ _ _ _ _ _ _ HD1) by (cbn; lia). cbn [sv_denot].
  replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (lm_bow 0 4 (Z.to_nat i)) by lia. rewrite lm_le0.
  reflexivity. }
assert (VRX : forall i, 0 <= i < 8 -> aview segs (w_H W') (ms_mem ms3) (TA_g_rx + i) = Some 0).
{ intros i Hi. replace (TA_g_rx + i) with (TA_g_rx - 1000 + 1000 + i) by lia.
  rewrite (lm_chunk_rd _ _ _ _ _ _ _ _ HD2) by (cbn; lia). cbn [sv_denot].
  replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (lm_bow 0 8 (Z.to_nat i)) by lia. rewrite lm_le0.
  reflexivity. }
assert (VS24 : rdword (aview segs (w_H W') (ms_mem ms3)) (sp1 + 24) = Some (transport_hi 14)).
{ replace (Some (transport_hi 14)) with (Some (bv_unsigned (w64 (transport_hi 14))))
    by (unfold w64; rewrite unsigned_lit_small by (rewrite P14; lia); reflexivity).
  apply (lm_chunk_rdword _ _ _ _ _ _ _ HD3). cbn [sv_denot]. rewrite U414, Z.add_0_r. reflexivity. }
assert (VS80 : rdword (aview segs (w_H W') (ms_mem ms3)) (sp1 + 80) = Some (transport_hi 15)).
{ replace (Some (transport_hi 15)) with (Some (bv_unsigned (w64 (transport_hi 15))))
    by (unfold w64; rewrite unsigned_lit_small by (rewrite P15; lia); reflexivity).
  apply (lm_chunk_rdword _ _ _ _ _ _ _ HD4). cbn [sv_denot]. rewrite U415, Z.add_0_r. reflexivity. }
assert (VS112 : rdword (aview segs (w_H W') (ms_mem ms3)) (sp1 + 112) = Some TA_g_s).
{ replace (Some TA_g_s) with (Some (bv_unsigned (w64 TA_g_s)))
    by (unfold w64; rewrite unsigned_lit_small by (unfold TA_g_s; lia); reflexivity).
  apply (lm_chunk_rdword _ _ _ _ _ _ _ HD5). cbn [sv_denot].
  rewrite (lm_img_val regs4 250 TA_g_s ltac:(unfold A_TEXT, A_LIM; lia) VO9), Z.add_0_r. reflexivity. }
clear HD0 HD1 HD2 HD3 HD4 HD5.
(* the bytes the segment kept, from the cut SCAL to the call of diginet_session_init *)
assert (KA5 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M <= a < TA_M + TW.SZ_M) -> ~ (TA_g_nq <= a < TA_g_nq + 4) ->
  ~ (TA_g_ncmd <= a < TA_g_ncmd + 4) -> ~ (TA_g_rx <= a < TA_g_rx + 8) -> ~ (sp1 - ESTACK <= a < sp1 + 192) ->
  aview segs (w_H W') (ms_mem ms3) a = aview segs (w_H W') mem' a).
{ intros a Ha H1 H2 H3 H4 H5. unfold TW.SZ_M in H1.
  rewrite K5m by lia. rewrite K4m by lia. rewrite K3m by lia. rewrite K2m by lia. apply K1m. exact Ha. }
assert (KSP5 : forall a, sp1 <= a < sp1 + 192 -> ~ (sp1 + 24 <= a < sp1 + 32) -> ~ (sp1 + 80 <= a < sp1 + 88) ->
  ~ (sp1 + 112 <= a < sp1 + 120) -> ~ (sp1 + 184 <= a < sp1 + 192) ->
  aview segs (w_H W') (ms_mem ms3) a = aview segs (w_H W') mem' a).
{ intros a Ha H1 H2 H3 H4.
  rewrite K5m by (unfold TA_g_nq, TA_g_ncmd, TA_g_rx; lia). rewrite K4m by (unfold TA_M; lia).
  rewrite K3m by (unfold TA_M; lia). rewrite K2m by (unfold TA_M; lia). apply K1m. lia. }
assert (VS184' : rdword (aview segs (w_H W') (ms_mem ms3)) (sp1 + 184) = Some TA_M).
{ rewrite <- VS184. apply rdword_ext. intros j Hj.
  rewrite K5m by (unfold TA_g_nq, TA_g_ncmd, TA_g_rx; lia). apply K4m; unfold TA_M; lia. }
assert (Hsh : lc_SH cx = SHADOW_OFF + F / 8) by reflexivity.
assert (HFd : 0 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (KF5 : forall a, F <= a < F + 256 \/ lc_SH cx <= a < lc_SH cx + 32 ->
  aview segs (w_H W') (ms_mem ms3) a = aview segs (w_H W') mem' a).
{ intros a Ha. destruct Ha as [Ha | Ha].
  - apply KA5; [lia | | | | | lia]; intros Hx;
      (apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) a HARg HFin);
       [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; lia | apply trans_g_img]).
    + apply lm_inG_M. exact Hx.
    + apply (lm_inG_row _ _ _ _ TMAP_A_g_nq). unfold TW.SZ_g_nq. exact Hx.
    + apply (lm_inG_row _ _ _ _ TMAP_A_g_ncmd). unfold TW.SZ_g_ncmd. exact Hx.
    + apply (lm_inG_row _ _ _ _ TMAP_A_g_rx). unfold TW.SZ_g_rx. exact Hx.
  - rewrite Hsh in Ha. apply KA5; unfold TA_M, TA_g_nq, TA_g_ncmd, TA_g_rx, TW.SZ_M, SHADOW_OFF in *; lia. }
assert (HFSH5 : forall i, 0 <= i < 32 ->
  aview segs (w_H W') (ms_mem ms3) (lc_SH cx + i) = Some (nth (Z.to_nat i) (lf_shm false false) 0)).
{ intros i Hi. rewrite KF5 by lia. exact (HFSH i Hi). }
(* the world at the call: lc_pro_minit of the cut's world *)
assert (HTW5 : tw_at TMAP_A (aview segs (w_H W') (ms_mem ms3)) (lc_pro_minit (lc_pro_scal (l_pl cx) B1))).
{ rewrite HMEQ. apply (lm_tw_minit (aview segs (w_H W') mem') _ _ dms HTW).
  - intros j Hj. rewrite K5m by (unfold TA_M, TA_g_nq, TA_g_ncmd, TA_g_rx; lia).
    rewrite K4m by (unfold TA_M; lia). exact (VM0 j Hj).
  - intros i Hi. change (Z.of_nat (length TC.DESK)) with 6 in Hi.
    rewrite K5m by (unfold TA_M, TA_g_nq, TA_g_ncmd, TA_g_rx; lia). rewrite Hcpy4 by lia. exact (KD3 i Hi).
  - intros i Hi. unfold TW.SZ_M in Hi. rewrite K5m by (unfold TA_M, TA_g_nq, TA_g_ncmd, TA_g_rx; lia).
    rewrite K4m by (unfold TA_M; lia). rewrite K3m by (unfold TA_M; lia).
    replace (TA_M + i) with (TA_M + 8 + (i - 8)) by lia. rewrite Hset2 by lia. reflexivity.
  - exact VNQ.
  - exact VNC.
  - exact VRX.
  - intros x Hx H1 H2 H3 H4. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KA5; [lia | exact H1 | exact H2 | exact H3 | exact H4 | lia]. }
(* io at F + 176, in the walk's side-stack frame *)
assert (LIO : length (TW.zs (sinit_io_bytes 0 (TI.ti_io_send timg_A) (TI.ti_io_recv timg_A) (TI.ti_io_now timg_A)))
  = 32%nat) by reflexivity.
assert (PGARR : garr8 segs (mrestrict (w_H W') (ms_mem ms3)) (F + 176)
  (TW.zs (sinit_io_bytes 0 (TI.ti_io_send timg_A) (TI.ti_io_recv timg_A) (TI.ti_io_now timg_A)))).
{ apply (lm_garr8_kept (w_H W') (w_H W') mem' (ms_mem ms3) (F + 176) _); [|exact HIO].
  intros j Hj. rewrite LIO in Hj. apply KF5. left. lia. }
assert (HFk : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HF8 : F / 8 = 8 * (F / 64)).
{ rewrite HFk at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.div_mul. lia. }
assert (PSRC : trans_src_ok B ly' S' W' (ms_mem ms3) (F + 176) SINIT_IO_LEN).
{ unfold SINIT_IO_LEN. right. split.
  - left. exists LF_CID, (l_fpos cx). split; [rewrite Hfrs; left; reflexivity|].
    rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. lia.
  - split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha. apply (lm_garr8_vis (w_H W') (ms_mem ms3) (F + 176) _ a PGARR). rewrite LIO. lia.
    + intros x Hx. exists 0. split; [| left; reflexivity]. unfold shadow_of_addr.
      pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
      replace (SHADOW_OFF + x / 8) with (lc_SH cx + (x / 8 - F / 8)) by (rewrite Hsh; lia).
      assert (Hi : x / 8 - F / 8 = 22 \/ x / 8 - F / 8 = 23 \/ x / 8 - F / 8 = 24 \/ x / 8 - F / 8 = 25) by lia.
      rewrite HFSH5 by lia. destruct Hi as [-> | [-> | [-> | ->]]]; reflexivity.
    + intros s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
      pose proof (Z.div_mod (F + 176) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (F + 176) 8 ltac:(lia)) as M1.
      pose proof (Z.div_mod (F + 176 + 32 - 1) 8 ltac:(lia)) as D2.
      pose proof (Z.mod_pos_bound (F + 176 + 32 - 1) 8 ltac:(lia)) as M2.
      pose proof (Z.div_mod (2147450880 + (F + 176) / 8) 8 ltac:(lia)) as D3.
      pose proof (Z.mod_pos_bound (2147450880 + (F + 176) / 8) 8 ltac:(lia)) as M3.
      pose proof (Z.div_mod (2147450880 + (F + 176 + 32 - 1) / 8) 8 ltac:(lia)) as D4.
      pose proof (Z.mod_pos_bound (2147450880 + (F + 176 + 32 - 1) / 8) 8 ltac:(lia)) as M4.
      replace s with (lc_SH cx + (s - lc_SH cx)) by lia.
      rewrite HFSH5 by (rewrite Hsh; unfold SHADOW_OFF; lia). discriminate.
    + apply (amem_range_sub_app F 256 (F + 176) 32 FB3 FB2); lia.
    + lia.
    + lia. }
assert (PAP : F + 176 + SINIT_IO_LEN <= SINIT_S \/ SINIT_S + TW.SZ_g_s <= F + 176).
{ unfold SINIT_IO_LEN, SINIT_S. unfold TW.SZ_g_s.
  destruct (Z_le_gt_dec (F + 176 + 32) TA_g_s) as [H1 | H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (TA_g_s + 18264) (F + 176)) as [H2 | H2]; [right; exact H2|].
  exfalso. apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) (Z.max (F + 176) TA_g_s) HARg HFin).
  - rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. lia.
  - apply trans_g_img. apply (lm_inG_row _ _ _ _ TMAP_A_g_s). unfold TW.SZ_g_s. lia. }
(* the registers at the call of diginet_session_init *)
lm_reg HS (Z_to_bv 5 10) (w64 SINIT_S) Q10c
  ltac:(cbn [sv_denot]; rewrite (lm_img_val regs4 250 TA_g_s ltac:(unfold A_TEXT, A_LIM; lia) VO9), Z.add_0_r;
        reflexivity).
lm_reg HS (Z_to_bv 5 11) (w64 SINIT_CFG) Q11c
  ltac:(cbn [sv_denot]; rewrite (eq_trans (lm_ew_reg regs4 21 21%bv eq_refl) (eq_trans (RK4 21 ltac:(lia)) R21)),
        Z.add_0_r; apply Z_to_bv_bv_unsigned).
lm_reg HS (Z_to_bv 5 12) (w64 (F + 176)) Q12c
  ltac:(cbn [sv_denot]; rewrite (eq_trans (lm_ew_reg regs4 20 20%bv eq_refl) (eq_trans (RK4 20 ltac:(lia)) R20)),
        Z.add_0_r; apply Z_to_bv_bv_unsigned).
lm_reg HS (Z_to_bv 5 13) (w64 (TI.ti_notice timg_A)) Q13c
  ltac:(cbn [sv_denot]; rewrite (lm_img_val regs4 251 _ ltac:(unfold A_TEXT, A_LIM; lia) VO10), Z.add_0_r;
        reflexivity).
lm_reg HS (Z_to_bv 5 14) (w64 0) Q14c ltac:(reflexivity).
lm_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LO_INIT)) Q1c ltac:(apply codeptr_val; apply lm_env_img).
assert (Q2c : YK11.getr (ms_regs ms3) (2%bv : bv 5) = w64 sp1) by exact (eq_trans (RK5 2 ltac:(lia)) Rsp).
assert (Q3c : YK11.getr (ms_regs ms3) (3%bv : bv 5) = w64 (as_gp B)) by exact (eq_trans (RK5 3 ltac:(lia)) Rgp).
assert (Q4c : YK11.getr (ms_regs ms3) (4%bv : bv 5) = w64 (as_tp B)) by exact (eq_trans (RK5 4 ltac:(lia)) Rtp).
assert (HSP3 : spZ (ms_regs ms3) = sp1) by (unfold spZ; rewrite Q2c; unfold w64; apply unsigned_lit_small; lia).
assert (EBR : BASE + LO_INIT = 0x815f4) by (vm_compute; reflexivity).
assert (PRET : YK0s.ret_ok (YK11.getr (ms_regs ms3) 1)).
{ rewrite Q1c. apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold LO_INIT; lia | reflexivity]. }
assert (PRA : 4096 <= raZ (ms_regs ms3)) by (unfold raZ; rewrite Q1c, EBR, unsigned_lit_small by lia; lia).
assert (PSP16 : spZ (ms_regs ms3) mod 16 = 0).
{ rewrite HSP3. pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1.
  replace sp1 with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
assert (PWIN : sp0 - LLVMF_STK <= spZ (ms_regs ms3) - SINIT_STK)
  by (rewrite HSP3; unfold LLVMF_STK, SINIT_STK, SINIT_FRAME; rewrite EST; lia).
assert (PSP0 : spZ (ms_regs ms3) <= sp0) by (rewrite HSP3; lia).
assert (POFF : decode_off_win (ms_regs ms3) SINIT_STK (F + 176) SINIT_IO_LEN).
{ unfold decode_off_win, SINIT_STK, SINIT_FRAME, SINIT_IO_LEN. rewrite HSP3, EST. left. lia. }
assert (PNEV : st_nev (l_S cx) + 0 + SINIT_EV <= EV_MAX) by (unfold SINIT_EV, EV_LIB in *; lia).
assert (PIO : 0 <= TI.ti_io_send timg_A < 2 ^ 64 /\ 0 <= TI.ti_io_recv timg_A < 2 ^ 64 /\
  0 <= TI.ti_io_now timg_A < 2 ^ 64 /\ 0 <= TI.ti_notice timg_A < 2 ^ 64)
  by (unfold timg_A; cbn [TI.ti_io_send TI.ti_io_recv TI.ti_io_now TI.ti_notice]; lia).
destruct PIO as (PIO1 & PIO2 & PIO3 & PIO4).
(* ---- +0x38c: diginet_session_init (g_s, g_cfg, io, notice, 0) ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transport_sigma TS_diginet_session_init)) mm rom)
    mdx) Q) end.
eapply SRr_mono.
{ exact (HSIN (l_fx cx) LLVMF_STK sp0 _ (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) _ ly' S' W' (ms_mem ms3) md5
    0 (ms_regs ms3) (F + 176) 0 (TI.ti_io_send timg_A) (TI.ti_io_recv timg_A) (TI.ti_io_now timg_A)
    (TI.ti_notice timg_A) 0 r (lc_pro_minit (lc_pro_scal (l_pl cx) B1)) B25
    HJ4 PRET PRA Q3c Q4c Q10c Q11c Q12c Q13c Q14c PSP16 PWIN PSP0 HTW5 EI
    ltac:(lia) PIO1 PIO2 PIO3 PIO4 ltac:(lia) ltac:(lia)
    ltac:(rewrite HFk; replace (64 * (F / 64) + 176) with ((8 * (F / 64) + 22) * 8) by ring; apply Z_mod_mult)
    PSRC PGARR POFF PAP PNEV). }
cbv beta. intros W6 c6 _ HPOST.
unfold transport_sinit_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly6 & S6 & regs6 & mem6 & md6 & e6 & Ec6 & He6 & HJ6 & HP6 & Hfr6 & Hperm6 & HK6 & Hmo6 &
  HA06 & HTW6).
assert (Ee6 : e6 = 0) by (unfold SINIT_EV in He6; lia). subst e6. rewrite Z.add_0_r in HJ6.
subst c6.
rewrite HSP3 in HK6. destruct HK6 as (K61 & K62 & K63 & K64 & K65 & K66).
assert (KF6 : forall a, F <= a < F + 256 \/ lc_SH cx <= a < lc_SH cx + 32 ->
  aview segs (w_H W6) mem6 a = aview segs (w_H W') mem' a).
{ intros a Ha. rewrite <- (KF5 a Ha). apply (K64 LF_CID (l_fpos cx) a HFin).
  - destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite HFaddr;
      change (fs_frame_bytes LF_CID) with 256; [lia | unfold shadow_addr; rewrite <- Hsh; change (256 / 8) with 32; lia].
  - intros (_ & Hw). destruct Ha as [Ha | Ha].
    + apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) a HARg HFin);
        [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; lia |].
      apply trans_g_img. apply (lm_inG_row _ _ _ _ TMAP_A_g_s). unfold SINIT_S in Hw. exact Hw.
    + rewrite Hsh in Ha. unfold SINIT_S, TA_g_s, TW.SZ_g_s, SHADOW_OFF in *. lia. }
(* ---- the cut INIT ---- *)
unfold lc_st_init.
exists ly6, S6, regs6, mem6, md6, Bw0, B25, r.
split.
{ unfold lc_cfg. rewrite Q1c, lm_pc_init. reflexivity. }
split.
{ apply (lm_core_kept cx ly' S' W' regs' mem' md' 0 SINIT_STK ly6 S6 W6 regs6 mem6 md6 0 LAWS HB HC HJ6 Hfr6
    Hperm6).
  - intros nq Hq. destruct Hq as [-> | [-> | [-> | [-> | ->]]]];
      (lazymatch goal with |- YK11.getr _ (Z_to_bv 5 ?k) = _ =>
         rewrite (HP6 k ltac:(unfold acallee_saved; lia)) end; apply RK5; lia).
  - unfold SINIT_STK, SINIT_FRAME, LLVMF_STK. rewrite EST. lia.
  - intros a Ha Hq. rewrite K61 by lia.
    apply KA5; [lia | unfold TA_M, TW.SZ_M; lia | unfold TA_g_nq; lia | unfold TA_g_ncmd; lia |
      unfold TA_g_rx; lia | unfold SINIT_STK, SINIT_FRAME in Hq; rewrite EST; lia].
  - intros b m i Hb Hi.
    destruct (al_blocks _ _ LAWS ly' S' W' mem' md' b m HARg Hb) as (_ & Hb4 & Hbc & _).
    assert (NI : ~ in_img segs (b + i)) by exact (blk_img segs B LAWS ly' S' W' mem' md' b m (b + i) HARg Hb ltac:(lia)).
    rewrite (K62 b m i Hb Hi).
    + apply KA5; [lia | | | | | lia]; intros Hx; apply NI; apply trans_g_img.
      * apply lm_inG_M. exact Hx.
      * apply (lm_inG_row _ _ _ _ TMAP_A_g_nq). unfold TW.SZ_g_nq. exact Hx.
      * apply (lm_inG_row _ _ _ _ TMAP_A_g_ncmd). unfold TW.SZ_g_ncmd. exact Hx.
      * apply (lm_inG_row _ _ _ _ TMAP_A_g_rx). unfold TW.SZ_g_rx. exact Hx.
    + intros (_ & Hw). apply NI. apply trans_g_img. apply (lm_inG_row _ _ _ _ TMAP_A_g_s). unfold SINIT_S in Hw.
      exact Hw.
  - intros a Ha. apply KF6. unfold LF_FBYTES in Ha. exact Ha. }
split.
{ split; [exact (eq_trans (HP6 18 ltac:(unfold acallee_saved; lia)) (eq_trans (RK5 18 ltac:(lia)) R18)) |
          exact (eq_trans (HP6 26 ltac:(unfold acallee_saved; lia)) (eq_trans (RK5 26 ltac:(lia)) R26))]. }
split.
{ unfold lc_spills, lf_spill_init. change (lc_sp1 cx) with sp1. apply Forall_app. split.
  - unfold lc_spills in HSP. change (lc_sp1 cx) with sp1 in HSP.
    rewrite Forall_forall in HSP |- *. intros o Ho. pose proof (HSP o Ho) as Ho'.
    unfold lf_spill_scal, lf_spill_sm in Ho. cbn [app In] in Ho.
    destruct Ho as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
      cbn [fst snd] in Ho' |- *; rewrite <- Ho'; apply rdword_ext; intros j Hj;
      rewrite K61 by (unfold SINIT_STK, SINIT_FRAME; rewrite ?EST; lia); apply KSP5; lia.
  - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + rewrite <- VS184'. apply rdword_ext. intros j Hj. apply K61; unfold SINIT_STK, SINIT_FRAME; rewrite ?EST; lia.
    + rewrite <- VS24. apply rdword_ext. intros j Hj. apply K61; unfold SINIT_STK, SINIT_FRAME; rewrite ?EST; lia.
    + rewrite <- VS80. apply rdword_ext. intros j Hj. apply K61; unfold SINIT_STK, SINIT_FRAME; rewrite ?EST; lia.
    + rewrite <- VS112. apply rdword_ext. intros j Hj. apply K61; unfold SINIT_STK, SINIT_FRAME; rewrite ?EST; lia. }
split.
{ intros i Hi. rewrite KF6 by lia. exact (HFSH i Hi). }
split.
{ split.
  - rewrite <- (Z.add_0_r (0 * lf_rcost MT)). exact (mo_le_trans MT MTL _ _ _ _ _ HMO Hmo6).
  - apply (mo_ok_step MT MTL S' S6 0 _); [rewrite Z.add_0_l; exact HMOK | exact Hmo6]. }
split.
{ split; [exact (eq_trans (HP6 25 ltac:(unfold acallee_saved; lia)) (eq_trans (RK5 25 ltac:(lia)) R25)) |
          exact (eq_trans (HP6 27 ltac:(unfold acallee_saved; lia)) (eq_trans (RK5 27 ltac:(lia)) R27))]. }
split; [exact HA06|].
split; [split; [exact HTW0 | exact HL0]|].
split; [unfold lc_pro_m; rewrite HCD; exact EI|].
exact HTW6.
Qed.


End minit.
