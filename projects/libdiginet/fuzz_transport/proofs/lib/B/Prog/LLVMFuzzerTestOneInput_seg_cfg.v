(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AFip.v (segA: the run of a
   wrapper over its own instruction table, the application of a runtime-entry contract at a call site and the
   rebuilding of the symbolic state after the call), A/AFis.v (at_ST's frame and window conjuncts,
   kept_of_frame, chunk_val_at) and A/AF0x.v (st_ok_pin_reg, the val_mem / apresent / fpchain helpers) to
   libreac/fuzz_decode's calloc wrapper in image A (fuzz_decode.asan); module paths changed, and every address,
   cell and offset below is decode's own. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/DecodeCallocWrap.v, with its module paths and module names changed; 3365 of its 3449 lines of code are new or changed and 788 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_cfg: proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's image-B walk).
   lc_cfg_ok (K1 : lc_rom_view_stmt B MT XL RLO RHI) (K2 : lc_src_ro_stmt B MT XL RLO RHI) : lc_cfg_stmt B MT XL RLO RHI
   (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), the segment CFG of fuzz_transport.asan-ubsan's LLVMFuzzerTestOneInput,
   from the return of diginet_session_config_default (+0x358, lc_st_cfgd) to the point before the memset of M (+0x4b0,
   lc_st_scal). Section ok takes the stage, lc_cfg_stage_stmt of LLVMFuzzerTestOneInput_seg_cfg_cut.v, as its
   hypothesis STAGE.

   The code (offsets from the entry 0x812a0). The segment meets its stage at +0x3a0 (the cut file's lc_st_cfgc):
     stage  +0x358 .. +0x39c   the two __asan_memcpy calls (HOST and DESK into g_cfg [0, 12)) and the three flag bits
                               into g_cfg [12, 24): the statement STAGE;
     run C  +0x3a0 .. +0x4ac   the fourteen config bytes at the cursor, each a UBSan test of the cursor and a checked
                               load, their stores into g_cfg [24, 60), the four spill slots (104, 152, 184, 40 of s1)
                               and the stores of g_raw, g_now, g_fail_next (one byte) and g_last_counter. The code
                               leaves the chain after the j-th byte when the cursor has j bytes, so run C is one run
                               per exit (sixteen: 0 .. 13 bytes with s7 pinned, 14 bytes, and 15 or more), with the
                               bytes left fixed; cf_runC splits on the exit, never on the loads.

   The checked loads. The cursor's shadow byte is read by the code itself (`srli; add; lb`), so each load is a region
   of the run at the shadow address, named by an alias fact, whose value the block's shadow law fixes: granule
   p / 8 answers 0 when the block has eight bytes and the block's length otherwise, granule p / 8 + 1 answers 0 when
   the block has sixteen and length - 8 otherwise (AR_laws al_shadow). Fixing the bytes left fixes both, so the
   engine decides every `beqz` / `bnez` on a shadow byte, and the out-of-line slow paths (`andi .., 7; blt / bge`)
   are decided by the alias facts of the cursor's low three bits: the fourteen report calls 0x82e18 .. 0x82ff8 and
   the fourteen branches to the UBSan trap word 0x82de4 are unreached.

   The world. Run C makes the last thirteen of lc_pro_scal's eighteen updates (cf_scal_eq) over the stage's world
   lc_cfg_b1, so the world moves by thirteen TWorldG.v tw_write steps over a reader patched range by range (cf_rdp),
   closed by cf_wclose. lc_core moves by st.v lc_core_kept_run: the segment writes no byte the core reads. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YO09 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBCg TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_config_default_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st
LLVMFuzzerTestOneInput_seg_cfg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TSess0 TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require InitOk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module IOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.InitOk.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model: the config bytes at the cursor after the flags byte   *)
(* ------------------------------------------------------------------ *)

(* Byte j after the flags byte, read through the cursor (o, n): the input byte while j < n, else 0. *)
Definition cf_b (D : list byte) (o n j : Z) : Z := if j <? n then DSpec.at8 D (Z.to_nat (o + j)) else 0.

Lemma cf_at8 : forall D i, 0 <= DSpec.at8 D i < 256.
Proof.
intros D i. unfold DSpec.at8, DSpec.bz. pose proof (bv_unsigned_in_range 8 (nth i D (DSpec.b8 0))) as R.
unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma cf_b_rng : forall D o n j, 0 <= cf_b D o n j < 256.
Proof. intros D o n j. unfold cf_b. destruct (j <? n); [apply cf_at8 | lia]. Qed.

Lemma cf_b_hi : forall D o n j, n <= j -> cf_b D o n j = 0.
Proof. intros D o n j H. unfold cf_b. destruct (Z.ltb_spec j n); [lia | reflexivity]. Qed.

(* fuzz_u8_m at the cursor after j bytes of (o, n): byte j, the cursor after j + 1 bytes. *)
Lemma cf_u8_step : forall D o n j j', 0 <= n -> 0 <= j -> j' = j + 1 ->
  TOP.fuzz_u8_m D (TOP.FuzzIn (o + Z.min n j) (n - Z.min n j)) =
  (TOP.FuzzIn (o + Z.min n j') (n - Z.min n j'), cf_b D o n j).
Proof.
intros D o n j j' Hn Hj ->. unfold TOP.fuzz_u8_m, cf_b. cbn [TOP.fi_off TOP.fi_n].
destruct (Z.ltb_spec j n) as [Hlt | Hge].
- rewrite (Z.min_r n j) by lia. rewrite (Z.min_r n (j + 1)) by lia.
  destruct (Z.eqb_spec (n - j) 0) as [E | E]; [lia|].
  f_equal. f_equal; lia.
- rewrite (Z.min_l n j) by lia. rewrite (Z.min_l n (j + 1)) by lia. rewrite Z.sub_diag. reflexivity.
Qed.

Lemma cf_lor8 : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> Z.lor (x * 2 ^ 8) y = x * 2 ^ 8 + y.
Proof.
intros x y Hx Hy. symmetry. apply Z.add_nocarry_lor.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec i 8) as [Hl|Hl].
- replace (x * 2 ^ 8) with (Z.shiftl x 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  rewrite Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r x (i - 8)) by lia. reflexivity.
- rewrite <- (Z.mod_small y (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia.
  apply andb_false_r.
Qed.

Lemma cf_lor : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 -> Z.lor lo (Z.shiftl hi 8) mod 2 ^ 16 = lo + 256 * hi.
Proof.
intros lo hi Hl Hh. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm, (cf_lor8 hi lo Hh Hl).
change (2 ^ 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.

(* fuzz_u16_m at the cursor after j bytes: bytes j and j + 1, little-endian, the cursor after j + 2 bytes. *)
Lemma cf_u16_step : forall D o n j j1 j', 0 <= n -> 0 <= j -> j1 = j + 1 -> j' = j + 2 ->
  TOP.fuzz_u16_m D (TOP.FuzzIn (o + Z.min n j) (n - Z.min n j)) =
  (TOP.FuzzIn (o + Z.min n j') (n - Z.min n j'), cf_b D o n j + 256 * cf_b D o n j1).
Proof.
intros D o n j j1 j' Hn Hj -> ->. unfold TOP.fuzz_u16_m.
rewrite (cf_u8_step D o n j (j + 1)) by lia. cbv beta iota.
rewrite (cf_u8_step D o n (j + 1) (j + 2)) by lia. cbv beta iota.
rewrite cf_lor by apply cf_b_rng. reflexivity.
Qed.

(* The cursor after the flags byte is a cursor of D with n >= 0. *)
Lemma cf_c1_n : forall D, 0 <= TOP.fi_n (lc_c1 D).
Proof.
intros D. unfold lc_c1, TOP.fuzz_u8_m, TOP.fuzz_in_m. cbn [TOP.fi_n TOP.fi_off].
destruct (Z.eqb_spec (Z.of_nat (length D)) 0); cbn [fst TOP.fi_n]; lia.
Qed.

(* The cursor after the flags byte, and the j-th config byte read through it. *)
Definition cf_o (D : list byte) : Z := TOP.fi_off (lc_c1 D).
Definition cf_n (D : list byte) : Z := TOP.fi_n (lc_c1 D).
Definition cf_v (D : list byte) (j : Z) : Z := cf_b D (cf_o D) (cf_n D) j.

Lemma cf_v_rng : forall D j, 0 <= cf_v D j < 256.
Proof. intros D j. apply cf_b_rng. Qed.
Lemma cf_v_hi : forall D j, cf_n D <= j -> cf_v D j = 0.
Proof. intros D j H. apply cf_b_hi. exact H. Qed.

(* The thirteen updates run C makes, in the order lc_pro_scal makes them, over the stage's world. *)
Definition cf_mk2 (Bb : list byte) (mr ack ka bo off wk dg mc mb raw : Z) : list byte :=
  let B7 := TW.set_Cfg_max_retries Bb mr in
  let B8 := TW.set_Cfg_ack_timeout_ms B7 ack in
  let B9 := TW.set_Cfg_keepalive_ms B8 ka in
  let B10 := TW.set_Cfg_backoff_ms B9 bo in
  let B11 := TW.set_Cfg_offline_ms B10 off in
  let B12 := TW.set_Cfg_wake_timeout_ms B11 wk in
  let B13 := TW.set_Cfg_display_gap_us B12 dg in
  let B14 := TW.set_Cfg_max_cmds B13 mc in
  let B15 := TW.set_Cfg_max_body B14 mb in
  let B16 := TW.set_g_raw B15 raw in
  let B17 := TW.set_g_now B16 1000000 in
  let B18 := TW.set_g_fail_next B17 0 in
  TW.set_g_last_counter B18 0.

(* lc_pro_scal at the bytes cf_v of the cursor after the flags byte. *)
Lemma cf_scal_eq : forall D B1,
  lc_pro_scal D B1 =
  cf_mk2 (lc_cfg_b1 D B1)
    (cf_v D 0 mod 8)
    ((1 + cf_v D 1) mod 2 ^ 32)
    ((1 + (cf_v D 2 + 256 * cf_v D 3)) mod 2 ^ 32)
    (cf_v D 4)
    ((1 + (cf_v D 5 + 256 * cf_v D 6)) mod 2 ^ 32)
    ((1 + (cf_v D 7 + 256 * cf_v D 8)) mod 2 ^ 32)
    (cf_v D 9 + 256 * cf_v D 10)
    ((1 + cf_v D 11 mod 255) mod 2 ^ 32)
    ((DSpec.SPEC_CMD_MAX + (cf_v D 12 + 256 * cf_v D 13)
        mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)
    (Z.land (Z.shiftr (lc_flags D) 3) 1).
Proof.
intros D B1. pose proof (cf_c1_n D) as Hn0.
unfold lc_pro_scal, cf_mk2, lc_cfg_b1, cf_v, cf_o, cf_n, lc_flags, lc_c1 in *. cbv zeta. revert Hn0.
destruct (TOP.fuzz_u8_m D (TOP.fuzz_in_m (Z.of_nat (length D)))) as [[o n] flags].
cbn [fst snd TOP.fi_off TOP.fi_n]. intros Hn0.
replace (TOP.FuzzIn o n) with (TOP.FuzzIn (o + Z.min n 0) (n - Z.min n 0)) by (f_equal; lia).
rewrite (cf_u8_step D o n 0 1) by lia. cbv beta iota.
rewrite (cf_u8_step D o n 1 2) by lia. cbv beta iota.
rewrite (cf_u16_step D o n 2 3 4) by lia. cbv beta iota.
rewrite (cf_u8_step D o n 4 5) by lia. cbv beta iota.
rewrite (cf_u16_step D o n 5 6 7) by lia. cbv beta iota.
rewrite (cf_u16_step D o n 7 8 9) by lia. cbv beta iota.
rewrite (cf_u16_step D o n 9 10 11) by lia. cbv beta iota.
rewrite (cf_u8_step D o n 11 12) by lia. cbv beta iota.
rewrite (cf_u16_step D o n 12 13 14) by lia. cbv beta iota.
reflexivity.
Qed.

(* The loop's cursor: the cursor after the flags byte, advanced by at most 14 bytes. *)
Lemma cf_cursor : forall D,
  IOK.prologue_cursor D = TOP.FuzzIn (cf_o D + Z.min (cf_n D) 14) (cf_n D - Z.min (cf_n D) 14).
Proof.
intros D. pose proof (cf_c1_n D) as Hn0.
unfold IOK.prologue_cursor, cf_o, cf_n, lc_c1 in *. cbv zeta. revert Hn0.
destruct (TOP.fuzz_u8_m D (TOP.fuzz_in_m (Z.of_nat (length D)))) as [[o n] flags].
cbn [fst snd TOP.fi_off TOP.fi_n]. intros Hn0.
replace (TOP.FuzzIn o n) with (TOP.FuzzIn (o + Z.min n 0) (n - Z.min n 0)) by (f_equal; lia).
rewrite (cf_u8_step D o n 0 1) by lia. cbv beta iota.
rewrite (cf_u8_step D o n 1 2) by lia. cbv beta iota.
rewrite (cf_u16_step D o n 2 3 4) by lia. cbv beta iota.
rewrite (cf_u8_step D o n 4 5) by lia. cbv beta iota.
rewrite (cf_u16_step D o n 5 6 7) by lia. cbv beta iota.
rewrite (cf_u16_step D o n 7 8 9) by lia. cbv beta iota.
rewrite (cf_u16_step D o n 9 10 11) by lia. cbv beta iota.
rewrite (cf_u8_step D o n 11 12) by lia. cbv beta iota.
rewrite (cf_u16_step D o n 12 13 14) by lia. cbv beta iota.
reflexivity.
Qed.

Lemma cf_on : forall D,
  (cf_o D = 0 /\ cf_n D = 0 /\ length D = 0%nat) \/
  (cf_o D = 1 /\ cf_n D = Z.of_nat (length D) - 1 /\ (0 < length D)%nat).
Proof.
intros D. unfold cf_o, cf_n, lc_c1, TOP.fuzz_u8_m, TOP.fuzz_in_m. cbn [TOP.fi_n TOP.fi_off].
destruct (Z.eqb_spec (Z.of_nat (length D)) 0) as [E|E]; cbn [fst TOP.fi_n TOP.fi_off].
- left. split; [reflexivity|]. split; [exact E | lia].
- right. split; [reflexivity|]. split; [reflexivity | lia].
Qed.

Lemma cf_flags_rng : forall D, 0 <= lc_flags D < 256.
Proof.
intros D. unfold lc_flags, TOP.fuzz_u8_m. destruct (TOP.fi_n (TOP.fuzz_in_m (Z.of_nat (length D))) =? 0).
- cbn [snd]. lia.
- cbn [snd]. apply cf_at8.
Qed.

(* the fourteen config bytes, as the run's valuation names them *)
Definition cf_bs (D : list byte) : list Z := map (fun j : nat => cf_v D (Z.of_nat j)) (seq 0 14).
Lemma cf_bs_len : forall D, length (cf_bs D) = 14%nat.
Proof. intros D. unfold cf_bs. rewrite length_map, length_seq. reflexivity. Qed.
Lemma cf_bs_nth : forall D j, (j < 14)%nat -> nth j (cf_bs D) 0 = cf_v D (Z.of_nat j).
Proof.
intros D j Hj. unfold cf_bs.
do 14 (destruct j as [|j]; [reflexivity|]). lia.
Qed.
Lemma cf_bs_rng : forall D, Forall (fun b : Z => 0 <= b < 256) (cf_bs D).
Proof.
intros D. apply Forall_forall. intros x Hx. unfold cf_bs in Hx. apply in_map_iff in Hx as (j & <- & _).
apply cf_v_rng.
Qed.

Lemma cf_nth_map : forall (D : list byte) i, (i < length D)%nat ->
  nth i (map (fun b : byte => bv_unsigned b) D) 0 = DSpec.at8 D i.
Proof.
induction D as [|b D IH]; intros i Hi; [cbn in Hi; lia|].
destruct i as [|i]; [reflexivity|]. cbn [map nth]. apply IH. cbn in Hi. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The code's values of the derived fields, decided over the bytes  *)
(* ------------------------------------------------------------------ *)

(* the three flag bits: `slli .., 0x3e / 0x3d / 0x3c` then `srli .., 0x3f` *)
Lemma cf_bit_chk :
  tw_allz (fun v =>
    (Z.eqb (zalu64 ALU_SRL (zalu64 ALU_SLL v 62) 63)
           (if Z.land v 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO)) &&
    (Z.eqb (zalu64 ALU_SRL (zalu64 ALU_SLL v 61) 63) (Z.land (Z.shiftr v 2) 1)) &&
    (Z.eqb (zalu64 ALU_SRL (zalu64 ALU_SLL v 60) 63) (Z.land (Z.shiftr v 3) 1)) &&
    (Z.eqb (zalu64 ALU_AND v 1) (Z.land v 1)))%bool 0 (Z.to_nat 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cf_bit : forall v, 0 <= v < 256 ->
  zalu64 ALU_SRL (zalu64 ALU_SLL v 62) 63 =
    (if Z.land v 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) /\
  zalu64 ALU_SRL (zalu64 ALU_SLL v 61) 63 = Z.land (Z.shiftr v 2) 1 /\
  zalu64 ALU_SRL (zalu64 ALU_SLL v 60) 63 = Z.land (Z.shiftr v 3) 1 /\
  zalu64 ALU_AND v 1 = Z.land v 1.
Proof.
intros v Hv.
pose proof (tw_allz_ok _ (Z.to_nat 256) 0 cf_bit_chk v ltac:(rewrite Z2Nat.id by lia; lia)) as H.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
split; [apply Z.eqb_eq; exact H1|]. split; [apply Z.eqb_eq; exact H2|].
split; [apply Z.eqb_eq; exact H3 | apply Z.eqb_eq; exact H4].
Qed.

(* max_cmds: `andi a0, a0, 0xff; addi a1, a0, -0xff; seqz a1, a1; addi a1, a1, -1; and a0, a0, a1; addi a0, a0, 1` *)
Definition cf_mc_f (x : Z) : Z :=
  zalu64 ALU_ADD
    (zalu64 ALU_AND (zalu64 ALU_AND x 255)
       (zalu64 ALU_ADD (zalu64 ALU_SLTU (zalu64 ALU_ADD (zalu64 ALU_AND x 255) (-255)) 1) (-1))) 1.
Lemma cf_mc_chk : tw_allz (fun v => Z.eqb (cf_mc_f v) ((1 + v mod 255) mod 2 ^ 32)) 0 (Z.to_nat 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cf_mc : forall v, 0 <= v < 256 -> cf_mc_f v = (1 + v mod 255) mod 2 ^ 32.
Proof.
intros v Hv. apply Z.eqb_eq.
exact (tw_allz_ok _ (Z.to_nat 256) 0 cf_mc_chk v ltac:(rewrite Z2Nat.id by lia; lia)).
Qed.

(* max_body: `mul a2, a1, 0x59b7; srli a2, a2, 25; mul a0, a2, 0x5b5; subw a1, a1, a0; addi a1, a1, 0x18;
   slli a1, a1, 0x30; srli a1, a1, 0x30` is 24 + v mod 1461 for v < 2 ^ 16. *)
Definition cf_mb_f (x : Z) : Z :=
  zalu64 ALU_SRL
    (zalu64 ALU_SLL
       (zalu64 ALU_ADD
          (zalu64 ALU_SUB x (zmd64 M_MUL (zalu64 ALU_SRL (zmd64 M_MUL x 22967) 25) 1461)) 24) 48) 48.
Lemma cf_mb_chk :
  tw_allz (fun v => Z.eqb (cf_mb_f v)
    ((DSpec.SPEC_CMD_MAX + v mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)) 0 (Z.to_nat 65536) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cf_mb : forall v, 0 <= v < 65536 ->
  cf_mb_f v = (DSpec.SPEC_CMD_MAX + v mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32.
Proof.
intros v Hv. apply Z.eqb_eq.
exact (tw_allz_ok _ (Z.to_nat 65536) 0 cf_mb_chk v ltac:(rewrite Z2Nat.id by lia; lia)).
Qed.

(* the two bytes of a u16 field, as the code joins them, and `or a1, zero, a0` *)
Lemma cf_u16_chk :
  tw_allz (fun v =>
    (Z.eqb (zalu64 ALU_ADD (zalu64 ALU_OR (v mod 256) (zalu64 ALU_SLL (v / 256) 8)) 1) ((1 + v) mod 2 ^ 32)) &&
    (Z.eqb (zalu64 ALU_OR (zalu64 ALU_SLL (v / 256) 8) (v mod 256)) v) &&
    (Z.eqb (zalu64 ALU_OR 0 (v mod 256)) (v mod 256)))%bool 0 (Z.to_nat 65536) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cf_u16_split : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  (x + y * 256) mod 256 = x /\ (x + y * 256) / 256 = y.
Proof.
intros x y Hx Hy. split.
- rewrite Z.mod_add by lia. apply Z.mod_small. lia.
- rewrite Z.div_add by lia. rewrite (Z.div_small x 256) by lia. lia.
Qed.

Lemma cf_u16_or : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  zalu64 ALU_ADD (zalu64 ALU_OR x (zalu64 ALU_SLL y 8)) 1 = (1 + (x + 256 * y)) mod 2 ^ 32.
Proof.
intros x y Hx Hy. destruct (cf_u16_split x y Hx Hy) as [Em Ed].
pose proof (tw_allz_ok _ (Z.to_nat 65536) 0 cf_u16_chk (x + y * 256)
  ltac:(rewrite Z2Nat.id by lia; lia)) as H.
apply andb_prop in H as [H _]. apply andb_prop in H as [H1 _]. apply Z.eqb_eq in H1.
rewrite Em, Ed in H1. replace (x + 256 * y) with (x + y * 256) by lia. exact H1.
Qed.

Lemma cf_u16_or' : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  zalu64 ALU_OR (zalu64 ALU_SLL y 8) x = x + 256 * y.
Proof.
intros x y Hx Hy. destruct (cf_u16_split x y Hx Hy) as [Em Ed].
pose proof (tw_allz_ok _ (Z.to_nat 65536) 0 cf_u16_chk (x + y * 256)
  ltac:(rewrite Z2Nat.id by lia; lia)) as H.
apply andb_prop in H as [H _]. apply andb_prop in H as [_ H2]. apply Z.eqb_eq in H2.
rewrite Em, Ed in H2. lia.
Qed.

Lemma cf_or0 : forall x, 0 <= x < 256 -> zalu64 ALU_OR 0 x = x.
Proof.
intros x Hx. destruct (cf_u16_split x 0 Hx ltac:(lia)) as [Em _].
pose proof (tw_allz_ok _ (Z.to_nat 65536) 0 cf_u16_chk (x + 0 * 256)
  ltac:(rewrite Z2Nat.id by lia; lia)) as H.
apply andb_prop in H as [_ H3]. apply Z.eqb_eq in H3. rewrite Em in H3. exact H3.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The world across the segment                                     *)
(* ------------------------------------------------------------------ *)

(* The bytes written so far, as a list of (base, length) ranges, and the reader that is the segment's last memory on
   them and the cut's memory elsewhere. Each store of the walk extends the list by its own range, so the kept side of
   TWorldG.v tw_write / tw_fill holds by the list's own shape. *)
Definition cf_in (l : list (Z * Z)) (a : Z) : bool :=
  existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l.
Definition cf_rdp (l : list (Z * Z)) (rd' rd : Z -> option Z) : Z -> option Z :=
  fun a => if cf_in l a then rd' a else rd a.

Lemma cf_rdp_hd : forall b n l rd' rd a, b <= a < b + n -> cf_rdp ((b, n) :: l) rd' rd a = rd' a.
Proof.
intros b n l rd' rd a Ha. unfold cf_rdp, cf_in. cbn [existsb fst snd].
rewrite (proj2 (Z.leb_le b a) ltac:(lia)), (proj2 (Z.ltb_lt a (b + n)) ltac:(lia)). reflexivity.
Qed.

Lemma cf_rdp_tl : forall b n l rd' rd a, ~ (b <= a < b + n) -> cf_rdp ((b, n) :: l) rd' rd a = cf_rdp l rd' rd a.
Proof.
intros b n l rd' rd a Ha. unfold cf_rdp, cf_in. cbn [existsb fst snd].
destruct (Z.leb_spec b a) as [H1|H1]; destruct (Z.ltb_spec a (b + n)) as [H2|H2];
  cbn [andb orb]; first [reflexivity | lia].
Qed.

(* One store of m bytes of v at offset k of the row (o, b, n). *)
Lemma cf_wstep : forall (l : list (Z * Z)) (rd rd' : Z -> option Z) Bw o b n k (m : nat) (v : Z),
  In (o, b, n) TMAP_B -> 0 <= k -> k + Z.of_nat m <= n ->
  tw_at TMAP_B (cf_rdp l rd' rd) Bw ->
  (forall j, (j < m)%nat -> rd' (b + k + Z.of_nat j) = Some (YO0f.le_byte v m j)) ->
  tw_at TMAP_B (cf_rdp ((b + k, Z.of_nat m) :: l) rd' rd) (TW.upd Bw (o + k) (TW.put m v)).
Proof.
intros l rd rd' Bw o b n k m v Hin Hk Hkm Hat Hv.
apply (tw_write TMAP_B (cf_rdp l rd' rd) _ Bw o b n k m v TMAP_B_ok Hat Hin Hk Hkm).
- intros j Hj. pose proof (inj_lt j m Hj) as Hjz. pose proof (Nat2Z.is_nonneg j) as Hj0.
  rewrite (cf_rdp_hd (b + k) (Z.of_nat m) l rd' rd (b + k + Z.of_nat j) ltac:(lia)). exact (Hv j Hj).
- intros x Hx Hn. exact (cf_rdp_tl (b + k) (Z.of_nat m) l rd' rd x Hn).
Qed.

(* Once every written range is in the list, the patched reader is the last memory's. *)
Lemma cf_wclose : forall l (rd rd' : Z -> option Z) Bw,
  tw_at TMAP_B (cf_rdp l rd' rd) Bw ->
  (forall x, tw_in TMAP_B x -> cf_in l x = false -> rd' x = rd x) ->
  tw_at TMAP_B rd' Bw.
Proof.
intros l rd rd' Bw Hat Hk. apply (tw_kept TMAP_B (cf_rdp l rd' rd) rd' Bw Hat).
intros x Hx. unfold cf_rdp. destruct (cf_in l x) eqn:E; [reflexivity | exact (Hk x Hx E)].
Qed.

(* A value read back from a region's chunk, as the view's bytes. *)
Lemma cf_vb : forall (Hh : word -> bool) (mm : word -> option byte) a (w : nat) v,
  YI04.val_mem tfibsegs (mrestrict Hh mm) a w v ->
  forall j, (j < w)%nat -> aview tfibsegs Hh mm (a + Z.of_nat j) = Some (YO0f.le_byte v w j).
Proof.
intros Hh mm a w v HV j Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 8) with 256. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* The bytes of G the segment writes: g_cfg's sixty and the four scalar globals. *)
Definition cf_gwr (a : Z) : Prop :=
  (TB_g_cfg + 24 <= a < TB_g_cfg + 60) \/ (TB_g_raw <= a < TB_g_raw + 4) \/ (TB_g_now <= a < TB_g_now + 8) \/
  (TB_g_fail_next <= a < TB_g_fail_next + 1) \/ (TB_g_last_counter <= a < TB_g_last_counter + 4).

(* The thirteen ranges run C writes, in the order the model updates them (the walk's own list). *)
Definition cf_L : list (Z * Z) :=
  [(TB_g_last_counter, 4); (TB_g_fail_next, 1); (TB_g_now, 8); (TB_g_raw, 4);
   (TB_g_cfg + 56, 4); (TB_g_cfg + 52, 4); (TB_g_cfg + 48, 4); (TB_g_cfg + 44, 4); (TB_g_cfg + 40, 4);
   (TB_g_cfg + 36, 4); (TB_g_cfg + 24, 4); (TB_g_cfg + 28, 4); (TB_g_cfg + 32, 4)].

(* the first range of the list that holds x; the scan is linear in the list *)
Ltac cf_hit :=
  repeat (apply orb_true_iff;
          ((left; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia) || right)).

Lemma cf_gwr_in : forall x, cf_gwr x -> cf_in cf_L x = true.
Proof.
intros x Hg. unfold cf_in, cf_L. cbn [existsb fst snd].
unfold cf_gwr, TB_g_cfg, TB_g_raw, TB_g_now, TB_g_fail_next, TB_g_last_counter in *.
destruct Hg as [C|[C|[C|[C|C]]]]; [|cf_hit..].
destruct (Z_lt_le_dec x (6155520 + 28)) as [?|?]; [cf_hit|].
destruct (Z_lt_le_dec x (6155520 + 32)) as [?|?]; [cf_hit|].
destruct (Z_lt_le_dec x (6155520 + 36)) as [?|?]; [cf_hit|].
destruct (Z_lt_le_dec x (6155520 + 40)) as [?|?]; [cf_hit|].
destruct (Z_lt_le_dec x (6155520 + 44)) as [?|?]; [cf_hit|].
destruct (Z_lt_le_dec x (6155520 + 48)) as [?|?]; [cf_hit|].
destruct (Z_lt_le_dec x (6155520 + 52)) as [?|?]; [cf_hit|].
destruct (Z_lt_le_dec x (6155520 + 56)) as [?|?]; [cf_hit|cf_hit].
Qed.

Lemma cf_in_false : forall x, cf_in cf_L x = false -> ~ cf_gwr x.
Proof. intros x H Hg. rewrite (cf_gwr_in x Hg) in H. discriminate. Qed.

(* The world after run C's thirteen updates, over the world the stage leaves. *)
Lemma cf_tw : forall (rd rd' : Z -> option Z) (Bb : list byte) mr ack ka bo off wk dg mc mb raw,
  tw_at TMAP_B rd Bb ->
  (forall j, (j < 4)%nat -> rd' (TB_g_cfg + 24 + Z.of_nat j) = Some (YO0f.le_byte ka 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_cfg + 28 + Z.of_nat j) = Some (YO0f.le_byte ack 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_cfg + 32 + Z.of_nat j) = Some (YO0f.le_byte mr 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_cfg + 36 + Z.of_nat j) = Some (YO0f.le_byte bo 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_cfg + 40 + Z.of_nat j) = Some (YO0f.le_byte off 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_cfg + 44 + Z.of_nat j) = Some (YO0f.le_byte wk 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_cfg + 48 + Z.of_nat j) = Some (YO0f.le_byte dg 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_cfg + 52 + Z.of_nat j) = Some (YO0f.le_byte mc 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_cfg + 56 + Z.of_nat j) = Some (YO0f.le_byte mb 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_raw + 0 + Z.of_nat j) = Some (YO0f.le_byte raw 4 j)) ->
  (forall j, (j < 8)%nat -> rd' (TB_g_now + 0 + Z.of_nat j) = Some (YO0f.le_byte 1000000 8 j)) ->
  (forall j, (j < 1)%nat -> rd' (TB_g_fail_next + 0 + Z.of_nat j) = Some (YO0f.le_byte 0 1 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_last_counter + 0 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ cf_gwr x -> rd' x = rd x) ->
  tw_at TMAP_B rd' (cf_mk2 Bb mr ack ka bo off wk dg mc mb raw).
Proof.
intros rd rd' Bb mr ack ka bo off wk dg mc mb raw HTW
  Hka Hack Hmr Hbo Hoff Hwk Hdg Hmc Hmb Hraw Hnow Hfail Hlast Hkept.
assert (H0 : tw_at TMAP_B (cf_rdp [] rd' rd) Bb).
{ apply (tw_kept TMAP_B rd); [exact HTW|]. intros x Hx. unfold cf_rdp, cf_in. reflexivity. }
unfold cf_mk2. cbv zeta.
unfold TW.set_Cfg_max_retries, TW.set_Cfg_ack_timeout_ms, TW.set_Cfg_keepalive_ms,
  TW.set_Cfg_backoff_ms, TW.set_Cfg_offline_ms, TW.set_Cfg_wake_timeout_ms, TW.set_Cfg_display_gap_us,
  TW.set_Cfg_max_cmds, TW.set_Cfg_max_body, TW.set_g_raw, TW.set_g_now, TW.set_g_fail_next,
  TW.set_g_last_counter,
  TW.A_Cfg_max_retries, TW.A_Cfg_ack_timeout_ms, TW.A_Cfg_keepalive_ms, TW.A_Cfg_backoff_ms,
  TW.A_Cfg_offline_ms, TW.A_Cfg_wake_timeout_ms, TW.A_Cfg_display_gap_us, TW.A_Cfg_max_cmds, TW.A_Cfg_max_body.
pose proof (cf_wstep _ rd rd' _ TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 32 4 mr TMAP_B_g_cfg
  ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia) H0 ltac:(intros j Hj; apply Hmr; exact Hj)) as H6.
pose proof (cf_wstep _ rd rd' _ TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 28 4 ack TMAP_B_g_cfg
  ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia) H6 ltac:(intros j Hj; apply Hack; exact Hj)) as H7.
pose proof (cf_wstep _ rd rd' _ TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 24 4 ka TMAP_B_g_cfg
  ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia) H7 ltac:(intros j Hj; apply Hka; exact Hj)) as H8.
pose proof (cf_wstep _ rd rd' _ TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 36 4 bo TMAP_B_g_cfg
  ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia) H8 ltac:(intros j Hj; apply Hbo; exact Hj)) as H9.
pose proof (cf_wstep _ rd rd' _ TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 40 4 off TMAP_B_g_cfg
  ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia) H9 ltac:(intros j Hj; apply Hoff; exact Hj)) as H10.
pose proof (cf_wstep _ rd rd' _ TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 44 4 wk TMAP_B_g_cfg
  ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia) H10 ltac:(intros j Hj; apply Hwk; exact Hj)) as H11.
pose proof (cf_wstep _ rd rd' _ TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 48 4 dg TMAP_B_g_cfg
  ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia) H11 ltac:(intros j Hj; apply Hdg; exact Hj)) as H12.
pose proof (cf_wstep _ rd rd' _ TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 52 4 mc TMAP_B_g_cfg
  ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia) H12 ltac:(intros j Hj; apply Hmc; exact Hj)) as H13.
pose proof (cf_wstep _ rd rd' _ TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 56 4 mb TMAP_B_g_cfg
  ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia) H13 ltac:(intros j Hj; apply Hmb; exact Hj)) as H14.
pose proof (cf_wstep _ rd rd' _ TW.OFF_g_raw TB_g_raw TW.SZ_g_raw 0 4 raw TMAP_B_g_raw
  ltac:(lia) ltac:(unfold TW.SZ_g_raw; lia) H14 ltac:(intros j Hj; apply Hraw; exact Hj)) as H15.
pose proof (cf_wstep _ rd rd' _ TW.OFF_g_now TB_g_now TW.SZ_g_now 0 8 1000000 TMAP_B_g_now
  ltac:(lia) ltac:(unfold TW.SZ_g_now; lia) H15 ltac:(intros j Hj; apply Hnow; exact Hj)) as H16.
pose proof (cf_wstep _ rd rd' _ TW.OFF_g_fail_next TB_g_fail_next 1 0 1 0 TMAP_B_g_fail_next
  ltac:(lia) ltac:(lia) H16 ltac:(intros j Hj; apply Hfail; exact Hj)) as H17.
pose proof (cf_wstep _ rd rd' _ TW.OFF_g_last_counter TB_g_last_counter TW.SZ_g_last_counter 0 4 0
  TMAP_B_g_last_counter ltac:(lia) ltac:(unfold TW.SZ_g_last_counter; lia) H17
  ltac:(intros j Hj; apply Hlast; exact Hj)) as H18.
apply (cf_wclose _ rd rd' _ H18).
intros x Hx Hf. exact (Hkept x Hx (cf_in_false x Hf)).
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The seats of the runs                                            *)
(* ------------------------------------------------------------------ *)

(* The cut at +0x3a0 is the cut file's CF_RC2; the runs' shadow base is s10. *)
Definition cf_Bx : sv := SOff 26 0.

(* g_cfg's bytes run C writes ([24, 60)), the four spill slots it stores (40, 104, 152, 184 of s1) and the four
   scalar globals at their auipc pages. *)
Definition cf_rg_cfg : YP09.region := YP09.mkRegion (Some 21%nat) 24 60 24 60 [].
Definition cf_rg_sp (k : Z) : YP09.region := YP09.mkRegion (Some 9%nat) k (k + 8) k (k + 8) [].
Definition cf_rg_raw : YP09.region := YP09.mkRegion (Some (A_HI 8)) 0x674 0x678 0x674 0x678 [].
Definition cf_rg_now : YP09.region := YP09.mkRegion (Some (A_HI 9)) 0x68c 0x694 0x68c 0x694 [].
Definition cf_rg_fail : YP09.region := YP09.mkRegion (Some (A_HI 10)) 0x678 0x679 0x678 0x679 [].
Definition cf_rg_last : YP09.region := YP09.mkRegion (Some (A_HI 11)) 0x684 0x688 0x684 0x688 [].
Definition cf_wregs : smem :=
  [cf_rg_cfg; cf_rg_sp 40; cf_rg_sp 104; cf_rg_sp 152; cf_rg_sp 184;
   cf_rg_raw; cf_rg_now; cf_rg_fail; cf_rg_last].
(* the k config bytes at the cursor (atoms 32 .. 31 + k), read only *)
Definition cf_rg_in (k : nat) : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0 (Z.of_nat k) 0 0
    (map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (32 + j) 0))) (seq 0 k)).
(* the shadow byte of the cursor's granule (atom 46 or 48), its value fixed by the block's shadow law *)
Definition cf_rg_sh (m : nat) (v : Z) : YP09.region :=
  YP09.mkRegion (Some m) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit v))].

Definition cf_hi_atoms : list (nat * afact) :=
  [(A_HI 8, mkAF (transportb_hi 8) (transportb_hi 8) 0);
   (A_HI 9, mkAF (transportb_hi 9) (transportb_hi 9) 0);
   (A_HI 10, mkAF (transportb_hi 10) (transportb_hi 10) 0);
   (A_HI 11, mkAF (transportb_hi 11) (transportb_hi 11) 0)].
Definition cf_atomsG (fn : afact) : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
   (21%nat, mkAF TB_g_cfg TB_g_cfg 5); (23%nat, fn); (24%nat, mkAF 0 255 0);
   (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] ++ cf_hi_atoms.
Definition cf_atomsC (fn : afact) : list (nat * afact) :=
  cf_atomsG fn ++
  [(19%nat, mkAF 4096 140737479966720 0); (46%nat, mkAF SHADOW_OFF (2 ^ 46) 0);
   (48%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] ++
  map (fun j => ((32 + j)%nat, mkAF 0 255 0)) (seq 0 14).

(* the shadow address of the cursor + i (granule 0 below seven, granule 1 above) and its low three bits *)
Definition cf_alias : list (sv * sv) :=
  map (fun i => (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 (Z.of_nat i)) (SLit 3)) (SOff 26 0),
                 SOff (if (i <? 7)%nat then 46 else 48)%nat 0)) (seq 0 14) ++
  map (fun i => (SAlu ALU_AND (SOff 19 (Z.of_nat i)) (SLit 7), SLit ((1 + Z.of_nat i) mod 8))) (seq 0 14).

Definition cf_ss0 : sstate :=
  mkSS CF_RC2 (sr_set sr_atoms (Z_to_bv 5 23) (SLit 0)) cf_wregs None
    (mkFacts (cf_atomsG (mkAF 0 0 0)) [] []).
(* run C's regions: the nine writable ones, then the cursor's k bytes and its shadow bytes *)
Definition cf_rgsC (k : nat) (s0 s1 : Z) : smem :=
  cf_wregs ++ cf_rg_in k :: cf_rg_sh 46 s0 :: (if (8 <=? k)%nat then [cf_rg_sh 48 s1] else []).
Definition cf_ssK (k : nat) (s0 s1 : Z) : sstate :=
  mkSS CF_RC2 (sr_set sr_atoms (Z_to_bv 5 23) (SLit (Z.of_nat k))) (cf_rgsC k s0 s1) None
    (mkFacts (cf_atomsC (mkAF (Z.of_nat k) (Z.of_nat k) 0)) [] cf_alias).
Definition cf_ssN (s1 : Z) : sstate :=
  mkSS CF_RC2 sr_atoms (cf_rgsC 14 0 s1) None (mkFacts (cf_atomsC (mkAF 14 (2 ^ 26) 0)) [] cf_alias).

(* The valuation of a run: the registers, then the fourteen config bytes (atoms 32 .. 45) and the two shadow
   addresses (46 and 48; atom 47 is unused). *)
Definition cf_ex (bs : list Z) (sa0 sa1 : Z) : list word :=
  map (fun b : Z => w64 b) bs ++ [w64 sa0; w64 0; w64 sa1].
Lemma cf_ex_b : forall bs sa0 sa1 j, length bs = 14%nat -> (j < 14)%nat ->
  nth j (cf_ex bs sa0 sa1) (Z_to_bv 64 0) = w64 (nth j bs 0).
Proof.
intros bs sa0 sa1 j HL Hj. unfold cf_ex. rewrite app_nth1 by (rewrite length_map; lia).
exact (map_nth (fun b : Z => w64 b) bs 0 j).
Qed.
Lemma cf_ex_a0 : forall bs sa0 sa1, length bs = 14%nat ->
  nth 14 (cf_ex bs sa0 sa1) (Z_to_bv 64 0) = w64 sa0.
Proof.
intros bs sa0 sa1 HL. unfold cf_ex. rewrite app_nth2 by (rewrite length_map; lia).
rewrite length_map, HL. reflexivity.
Qed.
Lemma cf_ex_a1 : forall bs sa0 sa1, length bs = 14%nat ->
  nth 16 (cf_ex bs sa0 sa1) (Z_to_bv 64 0) = w64 sa1.
Proof.
intros bs sa0 sa1 HL. unfold cf_ex. rewrite app_nth2 by (rewrite length_map; lia).
rewrite length_map, HL. reflexivity.
Qed.

(* the granule of the cursor + i, at a cursor one byte above an eight-aligned block *)
Lemma cf_gran : forall c i, 0 <= c -> c mod 8 = 1 -> 0 <= i <= 13 ->
  (c + i) / 8 = (if i <? 7 then c / 8 else c / 8 + 1).
Proof.
intros c i Hc Hm Hi.
pose proof (Z.div_mod c 8 ltac:(lia)) as D. rewrite Hm in D.
replace (c + i) with ((c / 8) * 8 + (1 + i)) by lia.
rewrite Z.div_add_l by lia.
destruct (Z.ltb_spec i 7) as [Hlt | Hge].
- rewrite (Z.div_small (1 + i) 8) by lia. lia.
- replace (1 + i) with (1 * 8 + (i - 7)) by lia. rewrite Z.div_add_l by lia.
  rewrite (Z.div_small (i - 7) 8) by lia. lia.
Qed.

(* the bytes from 16 below g_cfg to the end of g_last_counter lie in the image *)
Lemma cf_gimg_chk : forallb (fun r => decode_seg_covers (fst r) (snd r))
  [(TB_g_cfg - 16, TB_g_last_counter + 4 - (TB_g_cfg - 16))] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cf_gimg : forall a, TB_g_cfg - 16 <= a < TB_g_last_counter + 4 -> in_img tfibsegs a.
Proof.
intros a Ha. apply (decode_seg_covers_img _ a cf_gimg_chk). apply Exists_cons_hd.
unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma cf_vm1 : forall (H : word -> bool) (m : word -> option byte) a v,
  aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. replace k with 0%nat by lia. rewrite Z.add_0_r.
destruct (aview_byte tfibsegs H m _ _ Hv) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap, YO0f.le_byte. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !Z.mod_small by lia. symmetry. exact Hbv.
Qed.

Section seat. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The valuation of a run: the registers, then the fourteen config bytes (atoms 32 .. 45) and the two shadow
   addresses (46 and 48; atom 47 is unused). *)
Definition cf_E (regs : bvmap 5 word) (bs : list Z) (sa0 sa1 : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs (cf_ex bs sa0 sa1)).

(* `srli .., 3` then `add .., s10`: the shadow address of the cursor + i. *)
Lemma cf_den_shadow : forall E n m F SHB (i : Z),
  ew E n = Z_to_bv 64 F -> ew E m = Z_to_bv 64 SHB ->
  0 <= F -> 0 <= i -> F + i < 2 ^ 64 -> 0 <= SHB -> SHB + (F + i) / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n i) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (SHB + (F + i) / 8).
Proof.
intros E n m F SHB i Hn Hm HF Hi HFi HS1 HS2.
assert (HD : 0 <= (F + i) / 8) by (apply Z.div_pos; lia).
assert (Un : U E (SOff n i) = F + i)
  by (rewrite U_SOff, Hn, (unsigned_lit_small F ltac:(lia)); apply zcanon_id; unfold M64; lia).
assert (Um : U E (SOff m 0) = SHB)
  by (rewrite U_SOff, Hm, (unsigned_lit_small SHB ltac:(lia)), Z.add_0_r; apply zcanon_id; unfold M64; lia).
rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite Un, Um, U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((F + i) / 8)) by (unfold M64; lia).
rewrite (Z.add_comm ((F + i) / 8) SHB). apply zcanon_id. unfold M64. lia.
Qed.

(* `andi .., 7`: the cursor's low three bits. *)
Lemma cf_den_and : forall E n (c i : Z), ew E n = Z_to_bv 64 c -> 0 <= c -> 0 <= i -> c + i < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n i) (SLit 7)) = Z_to_bv 64 ((c + i) mod 8).
Proof.
intros E n c i Hn Hc Hi Hci.
assert (Un : U E (SOff n i) = c + i)
  by (rewrite U_SOff, Hn, (unsigned_lit_small c ltac:(lia)); apply zcanon_id; unfold M64; lia).
pose proof (Z.mod_pos_bound (c + i) 8 ltac:(lia)) as Hmb.
rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite Un, U_SLit.
rewrite (zcanon_id 7) by (unfold M64; lia).
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. lia.
Qed.

(* the three alias facts of the run's seat *)
Lemma cf_al0 : forall E c sa0 (i : Z),
  ew E 19 = Z_to_bv 64 c -> ew E 26 = Z_to_bv 64 SHADOW_OFF -> ew E 46 = Z_to_bv 64 sa0 ->
  4096 <= c -> c mod 8 = 1 -> c + 14 <= 140737479966720 -> sa0 = SHADOW_OFF + c / 8 -> 0 <= i <= 6 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 i) (SLit 3)) (SOff 26 0)) = sv_denot E (SOff 46 0).
Proof.
intros E c sa0 i E19 E26 E46 Hc1 Hc8 Hc2 Hsa Hi.
assert (Hq0 : 0 <= c / 8) by (apply Z.div_pos; lia).
assert (Hq1 : c / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
rewrite (cf_den_shadow E 19 26 c SHADOW_OFF i E19 E26 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(unfold SHADOW_OFF; lia) ltac:(rewrite (cf_gran c i ltac:(lia) Hc8 ltac:(lia));
    destruct (Z.ltb_spec i 7); unfold SHADOW_OFF; lia)).
rewrite (cf_gran c i ltac:(lia) Hc8 ltac:(lia)).
destruct (Z.ltb_spec i 7) as [Hlt | Hge]; [|lia].
rewrite (denot_lit_U E (SOff 46 0)), U_SOff, E46, (unsigned_lit_small sa0) by (unfold SHADOW_OFF in *; lia).
rewrite Z.add_0_r, (zcanon_id sa0) by (unfold M64, SHADOW_OFF in *; lia).
rewrite Hsa. reflexivity.
Qed.

Lemma cf_al1 : forall E c sa1 (i : Z),
  ew E 19 = Z_to_bv 64 c -> ew E 26 = Z_to_bv 64 SHADOW_OFF -> ew E 48 = Z_to_bv 64 sa1 ->
  4096 <= c -> c mod 8 = 1 -> c + 14 <= 140737479966720 -> sa1 = SHADOW_OFF + c / 8 + 1 -> 7 <= i <= 13 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 i) (SLit 3)) (SOff 26 0)) = sv_denot E (SOff 48 0).
Proof.
intros E c sa1 i E19 E26 E48 Hc1 Hc8 Hc2 Hsa Hi.
assert (Hq0 : 0 <= c / 8) by (apply Z.div_pos; lia).
assert (Hq1 : c / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
rewrite (cf_den_shadow E 19 26 c SHADOW_OFF i E19 E26 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(unfold SHADOW_OFF; lia) ltac:(rewrite (cf_gran c i ltac:(lia) Hc8 ltac:(lia));
    destruct (Z.ltb_spec i 7); unfold SHADOW_OFF; lia)).
rewrite (cf_gran c i ltac:(lia) Hc8 ltac:(lia)).
destruct (Z.ltb_spec i 7) as [Hlt | Hge]; [lia|].
rewrite (denot_lit_U E (SOff 48 0)), U_SOff, E48, (unsigned_lit_small sa1) by (unfold SHADOW_OFF in *; lia).
rewrite Z.add_0_r, (zcanon_id sa1) by (unfold M64, SHADOW_OFF in *; lia).
rewrite Hsa. f_equal. lia.
Qed.

Lemma cf_al7 : forall E c (i : Z),
  ew E 19 = Z_to_bv 64 c -> 4096 <= c -> c mod 8 = 1 -> c + 14 <= 140737479966720 -> 0 <= i <= 13 ->
  sv_denot E (SAlu ALU_AND (SOff 19 i) (SLit 7)) = sv_denot E (SLit ((1 + i) mod 8)).
Proof.
intros E c i E19 Hc1 Hc8 Hc2 Hi.
rewrite (cf_den_and E 19 c i E19 ltac:(lia) ltac:(lia) ltac:(lia)).
replace ((c + i) mod 8) with ((1 + i) mod 8); [reflexivity|].
rewrite <- (Zplus_mod_idemp_l c i 8), Hc8. reflexivity.
Qed.

(* the bytes of G the segment writes are bytes of G *)
Lemma cf_inG : forall a, cf_gwr a -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. unfold cf_gwr in Ha.
destruct Ha as [H|[H|[H|[H|H]]]].
- exists (TB_g_cfg, TW.SZ_g_cfg).
  split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_cfg) | unfold in_zr, TW.SZ_g_cfg; cbn [fst snd]; lia].
- exists (TB_g_raw, TW.SZ_g_raw).
  split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_raw) | unfold in_zr, TW.SZ_g_raw; cbn [fst snd]; lia].
- exists (TB_g_now, TW.SZ_g_now).
  split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_now) | unfold in_zr, TW.SZ_g_now; cbn [fst snd]; lia].
- exists (TB_g_fail_next, 1).
  split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_fail_next) | unfold in_zr; cbn [fst snd]; lia].
- exists (TB_g_last_counter, TW.SZ_g_last_counter).
  split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_last_counter)
         | unfold in_zr, TW.SZ_g_last_counter; cbn [fst snd]; lia].
Qed.

(* a region of bytes of G: writable at every memory *)
Lemma cf_gw_ok : forall E (m : word -> option byte) (n : nat) (b lo hi : Z),
  bv_unsigned (ew E n) = b -> 0 <= b + lo -> b + hi <= 2 ^ 64 ->
  (forall o, lo <= o < hi -> cf_gwr (b + o)) ->
  region_ok segs E m (YP09.mkRegion (Some n) lo hi lo hi []).
Proof.
intros E m n b lo hi HU H1 H2 HG. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HU. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (b + o) G_HARNESS_B_rw).
apply cf_inG. exact (HG o Ho).
Qed.

(* a region of the realigned stack: writable where the frame is present *)
Lemma cf_sp_ok : forall E (W : world segs) (m : word -> option byte) (sp lo hi : Z),
  bv_unsigned (ew E 9) = sp -> 0 <= sp + lo -> sp + hi <= 2 ^ 64 ->
  (forall a, sp + lo <= a < sp + hi -> apresent (w_H W) m a) ->
  region_ok segs E (mrestrict (w_H W) m) (YP09.mkRegion (Some 9%nat) lo hi lo hi []).
Proof.
intros E W m sp lo hi HU H1 H2 HP. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HU. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable segs). apply HP. lia.
Qed.

(* the shadow byte of a granule, read only *)
Lemma cf_sh_ok : forall E (W : world segs) (m : word -> option byte) (n : nat) (a v : Z),
  bv_unsigned (ew E n) = a -> 0 <= a -> a + 1 <= 2 ^ 64 -> 0 <= v < 256 ->
  val_mem segs (mrestrict (w_H W) m) a 1 v ->
  region_ok segs E (mrestrict (w_H W) m) (cf_rg_sh n v).
Proof.
intros E W m n a v HU H1 H2 Hv HV. unfold cf_rg_sh, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HU. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val segs _ _ a 0 1 (SLit v) v);
  [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HV].
Qed.

(* the k config bytes at the cursor, read only *)
Lemma cf_in_ok : forall (W : world segs) (m : word -> option byte) regs bs sa0 sa1 (c : Z) (k : nat),
  length bs = 14%nat -> (k <= 14)%nat -> Forall (fun b : Z => 0 <= b < 256) bs ->
  bv_unsigned (ew (cf_E regs bs sa0 sa1) 19) = c -> 0 <= c -> c + 14 <= 2 ^ 64 ->
  (forall j, (j < k)%nat -> val_mem segs (mrestrict (w_H W) m) (c + Z.of_nat j) 1 (nth j bs 0)) ->
  region_ok segs (cf_E regs bs sa0 sa1) (mrestrict (w_H W) m) (cf_rg_in k).
Proof.
intros W m regs bs sa0 sa1 c k HL Hk HB U19 H1 H2 HV.
unfold cf_rg_in, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros ch Hch. apply in_map_iff in Hch as (j & <- & Hj). apply in_seq in Hj.
assert (Hjb : (j < 14)%nat) by lia.
assert (Hrng : 0 <= nth j bs 0 < 256).
{ rewrite Forall_forall in HB. apply HB. apply nth_In. rewrite HL. lia. }
assert (Ub : bv_unsigned (ew (cf_E regs bs sa0 sa1) (32 + j)) = nth j bs 0).
{ unfold cf_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  rewrite (cf_ex_b bs sa0 sa1 j HL Hjb). apply unsigned_lit_small. lia. }
apply (chunk_ok_val segs _ _ c (Z.of_nat j) 1 (SOff (32 + j) 0) (nth j bs 0));
  [cbn [sv_denot]; rewrite Ub, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | exact (HV j ltac:(lia))].
Qed.

(* an atom whose value is known *)
Lemma cf_af : forall E n v lo hi al, bv_unsigned (ew E n) = v -> lo <= v <= hi -> v mod 2 ^ al = 0 ->
  0 <= al <= 64 -> afact_ok E n (mkAF lo hi al).
Proof.
intros E n v lo hi al HU H1 H2 H3. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU.
split; [lia|]. split; [exact H2 | lia].
Qed.

(* the atoms every seat of the segment shares *)
Lemma cf_atomsG_ok : forall E (sp fl : Z) (fn : afact),
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 9) = sp -> bv_unsigned (ew E 21) = TB_g_cfg ->
  bv_unsigned (ew E 24) = fl -> bv_unsigned (ew E 26) = SHADOW_OFF ->
  bv_unsigned (ew E (A_HI 8)) = transportb_hi 8 -> bv_unsigned (ew E (A_HI 9)) = transportb_hi 9 ->
  bv_unsigned (ew E (A_HI 10)) = transportb_hi 10 -> bv_unsigned (ew E (A_HI 11)) = transportb_hi 11 ->
  2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 32 = 0 -> 0 <= fl < 256 -> afact_ok E 23 fn ->
  atoms_ok E (cf_atomsG fn).
Proof.
intros E sp fl fn U2 U9 U21 U24 U26 H8 H9 H10 H11 Hsp Hsp32 Hfl Hfn.
unfold cf_atomsG, cf_hi_atoms. cbn [app atoms_ok].
split; [exact (cf_af E 2 sp (2 ^ 46) (2 ^ 47) 5 U2 ltac:(lia) ltac:(change (2 ^ 5) with 32; exact Hsp32) ltac:(lia))|].
split; [exact (cf_af E 9 sp (2 ^ 46) (2 ^ 47) 5 U9 ltac:(lia) ltac:(change (2 ^ 5) with 32; exact Hsp32) ltac:(lia))|].
split; [exact (cf_af E 21 TB_g_cfg TB_g_cfg TB_g_cfg 5 U21 ltac:(lia)
                 ltac:(change (2 ^ 5) with 32; unfold TB_g_cfg; reflexivity) ltac:(lia))|].
split; [exact Hfn|].
split; [exact (cf_af E 24 fl 0 255 0 U24 ltac:(lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 26 SHADOW_OFF SHADOW_OFF SHADOW_OFF 0 U26 ltac:(unfold SHADOW_OFF; lia)
                 ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E (A_HI 8) (transportb_hi 8) (transportb_hi 8) (transportb_hi 8) 0 H8 ltac:(lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E (A_HI 9) (transportb_hi 9) (transportb_hi 9) (transportb_hi 9) 0 H9 ltac:(lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E (A_HI 10) (transportb_hi 10) (transportb_hi 10) (transportb_hi 10) 0 H10 ltac:(lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E (A_HI 11) (transportb_hi 11) (transportb_hi 11) (transportb_hi 11) 0 H11 ltac:(lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia)) | exact I].
Qed.

(* the atoms of run C: the shared ones, the cursor, the two shadow addresses and the fourteen bytes *)
Lemma cf_atomsC_ok : forall E (sp c fl : Z) (sa0 sa1 : Z) (bs : list Z) (fn : afact),
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 9) = sp -> bv_unsigned (ew E 21) = TB_g_cfg ->
  bv_unsigned (ew E 24) = fl -> bv_unsigned (ew E 26) = SHADOW_OFF ->
  bv_unsigned (ew E (A_HI 8)) = transportb_hi 8 -> bv_unsigned (ew E (A_HI 9)) = transportb_hi 9 ->
  bv_unsigned (ew E (A_HI 10)) = transportb_hi 10 -> bv_unsigned (ew E (A_HI 11)) = transportb_hi 11 ->
  bv_unsigned (ew E 19) = c -> bv_unsigned (ew E 46) = sa0 -> bv_unsigned (ew E 48) = sa1 ->
  (forall n j, n = (32 + j)%nat -> (j < 14)%nat -> bv_unsigned (ew E n) = nth j bs 0) ->
  (forall j, (j < 14)%nat -> 0 <= nth j bs 0 <= 255) ->
  2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 32 = 0 -> 0 <= fl < 256 ->
  4096 <= c <= 140737479966720 -> SHADOW_OFF <= sa0 <= 2 ^ 46 -> SHADOW_OFF <= sa1 <= 2 ^ 46 ->
  afact_ok E 23 fn ->
  atoms_ok E (cf_atomsC fn).
Proof.
intros E sp c fl sa0 sa1 bs fn U2 U9 U21 U24 U26 H8 H9 H10 H11 U19 U46 U48 UB HBn
  Hsp Hsp32 Hfl Hc Hsa0 Hsa1 Hfn.
assert (HG := cf_atomsG_ok E sp fl fn U2 U9 U21 U24 U26 H8 H9 H10 H11 Hsp Hsp32 Hfl Hfn).
unfold cf_atomsG, cf_hi_atoms in HG. cbn [app atoms_ok] in HG.
destruct HG as (G2 & G9 & G21 & G23 & G24 & G26 & GH8 & GH9 & GH10 & GH11 & _).
unfold cf_atomsC, cf_atomsG, cf_hi_atoms. cbn [app map seq atoms_ok Nat.add].
split; [exact G2|]. split; [exact G9|]. split; [exact G21|]. split; [exact G23|].
split; [exact G24|]. split; [exact G26|]. split; [exact GH8|]. split; [exact GH9|].
split; [exact GH10|]. split; [exact GH11|].
split; [exact (cf_af E 19 c 4096 140737479966720 0 U19 ltac:(lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 46 sa0 SHADOW_OFF (2 ^ 46) 0 U46 ltac:(lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 48 sa1 SHADOW_OFF (2 ^ 46) 0 U48 ltac:(lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 32%nat (nth 0%nat bs 0) 0 255 0 (UB 32%nat 0%nat eq_refl ltac:(lia))
           ltac:(apply HBn; lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 33%nat (nth 1%nat bs 0) 0 255 0 (UB 33%nat 1%nat eq_refl ltac:(lia))
           ltac:(apply HBn; lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 34%nat (nth 2%nat bs 0) 0 255 0 (UB 34%nat 2%nat eq_refl ltac:(lia))
           ltac:(apply HBn; lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 35%nat (nth 3%nat bs 0) 0 255 0 (UB 35%nat 3%nat eq_refl ltac:(lia))
           ltac:(apply HBn; lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 36%nat (nth 4%nat bs 0) 0 255 0 (UB 36%nat 4%nat eq_refl ltac:(lia))
           ltac:(apply HBn; lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 37%nat (nth 5%nat bs 0) 0 255 0 (UB 37%nat 5%nat eq_refl ltac:(lia))
           ltac:(apply HBn; lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 38%nat (nth 6%nat bs 0) 0 255 0 (UB 38%nat 6%nat eq_refl ltac:(lia))
           ltac:(apply HBn; lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 39%nat (nth 7%nat bs 0) 0 255 0 (UB 39%nat 7%nat eq_refl ltac:(lia))
           ltac:(apply HBn; lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 40%nat (nth 8%nat bs 0) 0 255 0 (UB 40%nat 8%nat eq_refl ltac:(lia))
           ltac:(apply HBn; lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 41%nat (nth 9%nat bs 0) 0 255 0 (UB 41%nat 9%nat eq_refl ltac:(lia))
           ltac:(apply HBn; lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 42%nat (nth 10%nat bs 0) 0 255 0 (UB 42%nat 10%nat eq_refl ltac:(lia))
           ltac:(apply HBn; lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 43%nat (nth 11%nat bs 0) 0 255 0 (UB 43%nat 11%nat eq_refl ltac:(lia))
           ltac:(apply HBn; lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 44%nat (nth 12%nat bs 0) 0 255 0 (UB 44%nat 12%nat eq_refl ltac:(lia))
           ltac:(apply HBn; lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia))|].
split; [exact (cf_af E 45%nat (nth 13%nat bs 0) 0 255 0 (UB 45%nat 13%nat eq_refl ltac:(lia))
           ltac:(apply HBn; lia) ltac:(cbn; apply Z.mod_1_r) ltac:(lia)) | exact I].
Qed.

(* the twenty-eight alias facts of run C's seat *)
Lemma cf_aliasC_ok : forall E (c sa0 sa1 : Z),
  ew E 19 = Z_to_bv 64 c -> ew E 26 = Z_to_bv 64 SHADOW_OFF -> ew E 46 = Z_to_bv 64 sa0 ->
  ew E 48 = Z_to_bv 64 sa1 ->
  4096 <= c -> c mod 8 = 1 -> c + 14 <= 140737479966720 ->
  sa0 = SHADOW_OFF + c / 8 -> sa1 = SHADOW_OFF + c / 8 + 1 ->
  alias_ok E cf_alias.
Proof.
intros E c sa0 sa1 E19 E26 E46 E48 Hc1 Hc8 Hc2 Hsa0 Hsa1.
unfold cf_alias. cbn [app map seq alias_ok Z.of_nat Nat.ltb Nat.leb].
split; [exact (cf_al0 E c sa0 0 E19 E26 E46 Hc1 Hc8 Hc2 Hsa0 ltac:(lia))|].
split; [exact (cf_al0 E c sa0 1 E19 E26 E46 Hc1 Hc8 Hc2 Hsa0 ltac:(lia))|].
split; [exact (cf_al0 E c sa0 2 E19 E26 E46 Hc1 Hc8 Hc2 Hsa0 ltac:(lia))|].
split; [exact (cf_al0 E c sa0 3 E19 E26 E46 Hc1 Hc8 Hc2 Hsa0 ltac:(lia))|].
split; [exact (cf_al0 E c sa0 4 E19 E26 E46 Hc1 Hc8 Hc2 Hsa0 ltac:(lia))|].
split; [exact (cf_al0 E c sa0 5 E19 E26 E46 Hc1 Hc8 Hc2 Hsa0 ltac:(lia))|].
split; [exact (cf_al0 E c sa0 6 E19 E26 E46 Hc1 Hc8 Hc2 Hsa0 ltac:(lia))|].
split; [exact (cf_al1 E c sa1 7 E19 E26 E48 Hc1 Hc8 Hc2 Hsa1 ltac:(lia))|].
split; [exact (cf_al1 E c sa1 8 E19 E26 E48 Hc1 Hc8 Hc2 Hsa1 ltac:(lia))|].
split; [exact (cf_al1 E c sa1 9 E19 E26 E48 Hc1 Hc8 Hc2 Hsa1 ltac:(lia))|].
split; [exact (cf_al1 E c sa1 10 E19 E26 E48 Hc1 Hc8 Hc2 Hsa1 ltac:(lia))|].
split; [exact (cf_al1 E c sa1 11 E19 E26 E48 Hc1 Hc8 Hc2 Hsa1 ltac:(lia))|].
split; [exact (cf_al1 E c sa1 12 E19 E26 E48 Hc1 Hc8 Hc2 Hsa1 ltac:(lia))|].
split; [exact (cf_al1 E c sa1 13 E19 E26 E48 Hc1 Hc8 Hc2 Hsa1 ltac:(lia))|].
split; [exact (cf_al7 E c 0 E19 Hc1 Hc8 Hc2 ltac:(lia))|].
split; [exact (cf_al7 E c 1 E19 Hc1 Hc8 Hc2 ltac:(lia))|].
split; [exact (cf_al7 E c 2 E19 Hc1 Hc8 Hc2 ltac:(lia))|].
split; [exact (cf_al7 E c 3 E19 Hc1 Hc8 Hc2 ltac:(lia))|].
split; [exact (cf_al7 E c 4 E19 Hc1 Hc8 Hc2 ltac:(lia))|].
split; [exact (cf_al7 E c 5 E19 Hc1 Hc8 Hc2 ltac:(lia))|].
split; [exact (cf_al7 E c 6 E19 Hc1 Hc8 Hc2 ltac:(lia))|].
split; [exact (cf_al7 E c 7 E19 Hc1 Hc8 Hc2 ltac:(lia))|].
split; [exact (cf_al7 E c 8 E19 Hc1 Hc8 Hc2 ltac:(lia))|].
split; [exact (cf_al7 E c 9 E19 Hc1 Hc8 Hc2 ltac:(lia))|].
split; [exact (cf_al7 E c 10 E19 Hc1 Hc8 Hc2 ltac:(lia))|].
split; [exact (cf_al7 E c 11 E19 Hc1 Hc8 Hc2 ltac:(lia))|].
split; [exact (cf_al7 E c 12 E19 Hc1 Hc8 Hc2 ltac:(lia))|].
split; [exact (cf_al7 E c 13 E19 Hc1 Hc8 Hc2 ltac:(lia)) | exact I].
Qed.

(* the nine writable regions of run C, at any seat that names them *)
Lemma cf_wregs_ok : forall E (W : world segs) (m : word -> option byte) (sp : Z),
  bv_unsigned (ew E 9) = sp -> bv_unsigned (ew E 21) = TB_g_cfg ->
  bv_unsigned (ew E (A_HI 8)) = transportb_hi 8 -> bv_unsigned (ew E (A_HI 9)) = transportb_hi 9 ->
  bv_unsigned (ew E (A_HI 10)) = transportb_hi 10 -> bv_unsigned (ew E (A_HI 11)) = transportb_hi 11 ->
  2 ^ 46 <= sp <= 2 ^ 47 ->
  (forall a, sp + 40 <= a < sp + 192 -> apresent (w_H W) m a) ->
  Forall (region_ok segs E (mrestrict (w_H W) m)) cf_wregs.
Proof.
intros E W m sp U9 U21 UH8 UH9 UH10 UH11 Hsp HPres.
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
unfold cf_wregs. repeat apply Forall_cons; try apply Forall_nil.
- apply (cf_gw_ok E _ 21%nat TB_g_cfg 24 60 U21 ltac:(unfold TB_g_cfg; lia) ltac:(unfold TB_g_cfg; lia)).
  intros o Ho. unfold cf_gwr. left. lia.
- exact (cf_sp_ok E W m sp 40 48 U9 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply HPres; lia)).
- exact (cf_sp_ok E W m sp 104 112 U9 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply HPres; lia)).
- exact (cf_sp_ok E W m sp 152 160 U9 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply HPres; lia)).
- exact (cf_sp_ok E W m sp 184 192 U9 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply HPres; lia)).
- apply (cf_gw_ok E _ (A_HI 8) (transportb_hi 8) 0x674 0x678 UH8
           ltac:(rewrite P8; lia) ltac:(rewrite P8; lia)).
  intros o Ho. unfold cf_gwr, TB_g_raw. right; left. rewrite P8. lia.
- apply (cf_gw_ok E _ (A_HI 9) (transportb_hi 9) 0x68c 0x694 UH9
           ltac:(rewrite P9; lia) ltac:(rewrite P9; lia)).
  intros o Ho. unfold cf_gwr, TB_g_now. right; right; left. rewrite P9. lia.
- apply (cf_gw_ok E _ (A_HI 10) (transportb_hi 10) 0x678 0x679 UH10
           ltac:(rewrite P10; lia) ltac:(rewrite P10; lia)).
  intros o Ho. unfold cf_gwr, TB_g_fail_next. right; right; right; left. rewrite P10. lia.
- apply (cf_gw_ok E _ (A_HI 11) (transportb_hi 11) 0x684 0x688 UH11
           ltac:(rewrite P11; lia) ltac:(rewrite P11; lia)).
  intros o Ho. unfold cf_gwr, TB_g_last_counter. right; right; right; right. rewrite P11. lia.
Qed.

Lemma cf_wregs_disj : forall E (sp : Z),
  bv_unsigned (ew E 9) = sp -> bv_unsigned (ew E 21) = TB_g_cfg ->
  bv_unsigned (ew E (A_HI 8)) = transportb_hi 8 -> bv_unsigned (ew E (A_HI 9)) = transportb_hi 9 ->
  bv_unsigned (ew E (A_HI 10)) = transportb_hi 10 -> bv_unsigned (ew E (A_HI 11)) = transportb_hi 11 ->
  2 ^ 46 <= sp <= 2 ^ 47 -> pairwise_disjoint E cf_wregs.
Proof.
intros E sp U9 U21 UH8 UH9 UH10 UH11 Hsp.
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
apply pairwise_disjoint_of_extents.
unfold cf_wregs, cf_rg_cfg, cf_rg_sp, cf_rg_raw, cf_rg_now, cf_rg_fail, cf_rg_last, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold TB_g_cfg in *.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* The seat of run C: g_cfg [24, 60), the four spill slots and the four scalar globals writable; the cursor's k bytes
   and the shadow bytes of its granules (the second one only when the code reads it, k >= 8) read only. *)
Lemma cf_seatC : forall (W : world segs) regs mem (sp c fl n1 : Z) (k : nat) (s0 s1 : Z) (bs : list Z)
    (fn : afact),
  YK11.getr regs 2 = w64 sp -> YK11.getr regs 9 = w64 sp -> YK11.getr regs 19 = w64 c ->
  YK11.getr regs 21 = w64 TB_g_cfg -> YK11.getr regs 23 = w64 n1 -> YK11.getr regs 24 = w64 fl ->
  YK11.getr regs 26 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 32 = 0 ->
  4096 <= c -> c + 14 <= 140737479966720 -> c mod 8 = 1 ->
  0 <= n1 < 2 ^ 26 -> 0 <= fl < 256 -> 0 <= s0 < 256 -> ((8 <= k)%nat -> 0 <= s1 < 256) ->
  (k <= 14)%nat -> length bs = 14%nat -> Forall (fun b : Z => 0 <= b < 256) bs ->
  afact_ok (cf_E regs bs (SHADOW_OFF + c / 8) (SHADOW_OFF + c / 8 + 1)) 23 fn ->
  (forall j, (j < k)%nat -> val_mem segs (mrestrict (w_H W) mem) (c + Z.of_nat j) 1 (nth j bs 0)) ->
  val_mem segs (mrestrict (w_H W) mem) (SHADOW_OFF + c / 8) 1 s0 ->
  ((8 <= k)%nat -> val_mem segs (mrestrict (w_H W) mem) (SHADOW_OFF + c / 8 + 1) 1 s1) ->
  (forall a, sp + 40 <= a < sp + 192 -> apresent (w_H W) mem a) ->
  (c + 14 <= TB_g_cfg \/ TB_g_last_counter + 4 <= c) ->
  (c + 14 <= kLowShadowBeg \/ kHighMemBeg <= c) ->
  c + 14 <= sp - ESTACK ->
  regions_wf (cf_rgsC k s0 s1) = true ->
  st_ok_pi segs VAL (cf_E regs bs (SHADOW_OFF + c / 8) (SHADOW_OFF + c / 8 + 1))
    (mkSS CF_RC2 sr_atoms (cf_rgsC k s0 s1) None (mkFacts (cf_atomsC fn) [] cf_alias))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CF_RC2)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem sp c fl n1 k s0 s1 bs fn R2 R9 R19 R21 R23 R24 R26
  Hsp Hsp32 Hc1 Hc2 Hc8 Hn1 Hfl Hs0 Hs1 Hk HL HB Hfn HVb HV0 HV1 HPres HAG HAS HAST Hwf.
assert (Hq0 : 0 <= c / 8) by (apply Z.div_pos; lia).
assert (Hq1 : c / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
set (sa1 := SHADOW_OFF + c / 8 + 1). set (sa0 := SHADOW_OFF + c / 8).
set (E := cf_E regs bs sa0 sa1).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall n j, n = (32 + j)%nat -> (j < 17)%nat ->
          ew E n = nth j (cf_ex bs sa0 sa1) (Z_to_bv 64 0)).
{ intros n j -> Hj. unfold E, cf_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E19 : ew E 19 = Z_to_bv 64 c) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (E46 : ew E 46 = Z_to_bv 64 sa0)
  by (rewrite (EX 46%nat 14%nat eq_refl ltac:(lia)), (cf_ex_a0 bs sa0 sa1 HL); reflexivity).
assert (E48 : ew E 48 = Z_to_bv 64 sa1)
  by (rewrite (EX 48%nat 16%nat eq_refl ltac:(lia)), (cf_ex_a1 bs sa0 sa1 HL); reflexivity).
assert (HBn : forall j, (j < 14)%nat -> 0 <= nth j bs 0 <= 255).
{ rewrite Forall_forall in HB. intros j Hj.
  assert (Hin : In (nth j bs 0) bs) by (apply nth_In; rewrite HL; lia).
  pose proof (HB (nth j bs 0) Hin). lia. }
assert (UB : forall n j, n = (32 + j)%nat -> (j < 14)%nat -> bv_unsigned (ew E n) = nth j bs 0).
{ intros n j -> Hj. rewrite (EX (32 + j)%nat j eq_refl ltac:(lia)), (cf_ex_b bs sa0 sa1 j HL Hj).
  apply unsigned_lit_small. pose proof (HBn j Hj). lia. }
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = sp) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = c) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U24 : bv_unsigned (ew E 24) = fl)
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U46 : bv_unsigned (ew E 46) = sa0)
  by (rewrite E46; apply unsigned_lit_small; unfold sa0, SHADOW_OFF; lia).
assert (U48 : bv_unsigned (ew E 48) = sa1)
  by (rewrite E48; apply unsigned_lit_small; unfold sa1, SHADOW_OFF; lia).
assert (UH8 : bv_unsigned (ew E (A_HI 8)) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UH9 : bv_unsigned (ew E (A_HI 9)) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UH10 : bv_unsigned (ew E (A_HI 10)) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UH11 : bv_unsigned (ew E (A_HI 11)) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); vm_compute; reflexivity).
rewrite restrict_mkst_fx.
apply (pa_entry_st_ok_full (PI := PI_transportb)).
- unfold E, cf_E. apply regs_ok_Eimg_Ereg.
- exact Hwf.
- unfold cf_rgsC. apply Forall_app. split.
  + exact (cf_wregs_ok E W mem sp U9 U21 UH8 UH9 UH10 UH11 Hsp ltac:(intros a Ha; apply HPres; lia)).
  + apply Forall_cons; [exact (cf_in_ok W mem regs bs sa0 sa1 c k HL Hk HB U19 ltac:(lia) ltac:(lia) HVb)|].
    apply Forall_cons;
      [exact (cf_sh_ok E W mem 46 sa0 s0 U46 ltac:(unfold sa0, SHADOW_OFF; lia)
                ltac:(unfold sa0, SHADOW_OFF; lia) Hs0 HV0)|].
    destruct (Nat.leb_spec 8 k) as [H8|H8]; [|apply Forall_nil].
    apply Forall_cons; [|apply Forall_nil].
    exact (cf_sh_ok E W mem 48 sa1 s1 U48 ltac:(unfold sa1, SHADOW_OFF; lia)
             ltac:(unfold sa1, SHADOW_OFF; lia) (Hs1 H8) (HV1 H8)).
- pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
  apply pairwise_disjoint_of_extents.
  unfold cf_rgsC, cf_wregs, cf_rg_in, cf_rg_sh, cf_rg_cfg, cf_rg_sp, cf_rg_raw, cf_rg_now, cf_rg_fail, cf_rg_last,
    extent_of_region.
  assert (HkZ : 0 <= Z.of_nat k <= 14) by lia.
  assert (Hsa0' : sa0 = 2147450880 + c / 8) by (unfold sa0, SHADOW_OFF; reflexivity).
  assert (Hsa1' : sa1 = 2147450880 + c / 8 + 1) by (unfold sa1, SHADOW_OFF; reflexivity).
  unfold TB_g_cfg, TB_g_last_counter, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ESTACK in *.
  destruct (8 <=? k)%nat; cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val];
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
  rewrite ?U9, ?U21, ?UH8, ?UH9, ?UH10, ?UH11, ?U19, ?U46, ?U48, ?P8, ?P9, ?P10, ?P11;
  destruct HAG as [HAG|HAG]; destruct HAS as [HAS|HAS];
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- split; [|split; [exact I|]].
  + cbn [f_atoms]. exact (cf_atomsC_ok E sp c fl sa0 sa1 bs fn U2 U9 U21 U24 U26 UH8 UH9 UH10 UH11
      U19 U46 U48 UB HBn Hsp Hsp32 Hfl ltac:(lia) ltac:(unfold sa0, SHADOW_OFF; lia)
      ltac:(unfold sa1, SHADOW_OFF; lia) Hfn).
  + cbn [f_alias]. exact (cf_aliasC_ok E c sa0 sa1 E19 E26 E46 E48 Hc1 Hc8 Hc2 eq_refl eq_refl).
Qed.

(* a seat with the shared atoms and no alias fact: run C at the empty cursor *)
Lemma cf_seatG : forall (W : world segs) regs mem (sp fl : Z) (pc : Z) (rs : smem)
    (bs : list Z) (sa0 sa1 : Z) (fn : afact),
  YK11.getr regs 2 = w64 sp -> YK11.getr regs 9 = w64 sp -> YK11.getr regs 21 = w64 TB_g_cfg ->
  YK11.getr regs 24 = w64 fl -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 32 = 0 -> 0 <= fl < 256 ->
  afact_ok (cf_E regs bs sa0 sa1) 23 fn ->
  regions_wf rs = true ->
  Forall (region_ok segs (cf_E regs bs sa0 sa1) (mrestrict (w_H W) mem)) rs ->
  pairwise_disjoint (cf_E regs bs sa0 sa1) rs ->
  st_ok_pi segs VAL (cf_E regs bs sa0 sa1) (mkSS pc sr_atoms rs None (mkFacts (cf_atomsG fn) [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem sp fl pc rs bs sa0 sa1 fn R2 R9 R21 R24 R26 Hsp Hsp32 Hfl Hfn Hwf Hrs Hdj.
set (E := cf_E regs bs sa0 sa1) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = sp) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U24 : bv_unsigned (ew E 24) = fl)
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (UH8 : bv_unsigned (ew E (A_HI 8)) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UH9 : bv_unsigned (ew E (A_HI 9)) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UH10 : bv_unsigned (ew E (A_HI 10)) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UH11 : bv_unsigned (ew E (A_HI 11)) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); vm_compute; reflexivity).
rewrite restrict_mkst_fx.
apply (pa_entry_st_ok_full (PI := PI_transportb)).
- unfold E, cf_E. apply regs_ok_Eimg_Ereg.
- exact Hwf.
- exact Hrs.
- exact Hdj.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms].
  exact (cf_atomsG_ok E sp fl fn U2 U9 U21 U24 U26 UH8 UH9 UH10 UH11 Hsp Hsp32 Hfl Hfn).
Qed.

End seat.

(* ------------------------------------------------------------------ *)
(* 5. The core across the segment and the cut at its end               *)
(* ------------------------------------------------------------------ *)

Section cfg. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The bytes run C may write: g_cfg and the four scalar globals, the window below s1, and the four spill slots it
   stores. *)
Definition cf_wr (cx : lcx) (a : Z) : Prop :=
  cf_gwr a \/ (lc_sp1 cx - ESTACK <= a < lc_sp1 cx) \/
  (lc_sp1 cx + 40 <= a < lc_sp1 cx + 48) \/ (lc_sp1 cx + 104 <= a < lc_sp1 cx + 112) \/
  (lc_sp1 cx + 152 <= a < lc_sp1 cx + 160) \/ (lc_sp1 cx + 184 <= a < lc_sp1 cx + 192).

(* What the core and the slot's pre fix about the stack, the frame and the input. *)
Lemma cf_num : forall cx ly' S' (W' : world segs) regs' mem' md' e,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W' regs' mem' md' e ->
  alloc_ceiling + 32432 <= lc_sp1 cx /\ lc_sp0 cx - 336 <= lc_sp1 cx <= lc_sp0 cx - 320 /\
  lc_sp1 cx mod 32 = 0 /\ lc_sp0 cx <= 2 ^ 47 /\ lc_sp0 cx mod 16 = 0 /\
  4096 <= lc_F cx /\ lc_F cx mod 64 = 0 /\ lc_F cx + 256 <= alloc_ceiling /\
  (forall a, lc_F cx <= a < lc_F cx + 256 -> ~ in_img segs a) /\
  0 <= l_n cx < 2 ^ 26 /\ l_n cx = Z.of_nat (length (l_pl cx)) /\
  (0 < l_n cx -> In (l_p cx, l_n cx) (ablocks B ly' S') /\ 4096 <= l_p cx /\ l_p cx + l_n cx <= alloc_ceiling /\
     l_p cx mod 8 = 0 /\ in_app (l_p cx) (l_n cx) /\
     (forall a, l_p cx <= a < l_p cx + l_n cx -> ~ in_img segs a)) /\
  @AR rc segs B ly' S' W' mem' md'.
Proof.
intros cx ly' S' W' regs' mem' md' e LAWS HB HC.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & Hsp1al & _ & HF4096 & HFal & HFceil & _).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
unfold LF_FBYTES, LF_FRAME in *.
split; [exact Hsp1c|]. split; [lia|]. split; [exact Hsp1al|]. split; [lia|]. split; [exact Hsp0al|].
split; [exact HF4096|]. split; [exact HFal|]. split; [exact HFceil|].
split.
{ intros a Ha. apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) a HAR HFin).
  rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. exact Ha. }
split; [exact (proj1 Hn)|]. split; [exact (proj2 Hn)|].
split; [|exact HAR].
intros Hn0. pose proof (HINg Hn0) as Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4 & Hpc & Hpapp & _).
destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as ((Hp8 & _ & _) & _).
assert (RQ : req_size (l_n cx) = l_n cx) by (unfold req_size; destruct (Z.eqb_spec (l_n cx) 0); lia).
rewrite RQ in Hpc, Hpapp.
split; [exact Hin|]. split; [exact Hp4|]. split; [exact Hpc|]. split; [exact Hp8|]. split; [exact Hpapp|].
intros a Ha. apply (blk_img segs B LAWS ly' S' W' mem' md' (l_p cx) (l_n cx) a HAR Hin). rewrite RQ. exact Ha.
Qed.

(* The bytes the core, the kept spill slots, the frame's shadow and io read lie outside cf_wr. *)
Lemma cf_apart : forall cx ly' S' (W' : world segs) regs' mem' md' e,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W' regs' mem' md' e ->
  forall a, (lc_sp0 cx - 104 <= a < lc_sp0 cx) \/ (lc_F cx <= a < lc_F cx + 256) \/
            (0 < l_n cx /\ l_p cx <= a < l_p cx + l_n cx) \/ (lc_SH cx <= a < lc_SH cx + 32) \/
            (lc_sp1 cx + 128 <= a < lc_sp1 cx + 144) ->
    ~ cf_wr cx a /\ 0 <= a < 2 ^ 64.
Proof.
intros cx ly' S' W' regs' mem' md' e LAWS HB HC.
destruct (cf_num cx ly' S' W' regs' mem' md' e LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
assert (HF8 : 0 <= lc_F cx / 8 < 2 ^ 44)
  by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
assert (HGl : forall x, cf_gwr x -> 0 <= x < 6500000).
{ intros x Hx. unfold cf_gwr, TB_g_cfg, TB_g_raw, TB_g_now, TB_g_fail_next, TB_g_last_counter in Hx. lia. }
intros a Ha. unfold cf_wr, lc_SH, SHADOW_OFF, ESTACK in *.
destruct Ha as [Ha | [Ha | [[Hn0 Ha] | [Ha | Ha]]]].
- split; [intros [C|[C|[C|[C|[C|C]]]]]; try lia; pose proof (HGl a C); lia | lia].
- split; [|lia]. intros [C|[C|[C|[C|[C|C]]]]]; try lia.
  apply (N9 a Ha). apply trans_g_img. apply cf_inG. exact C.
- destruct (N12 Hn0) as (_ & Gp4 & Gpc & _ & _ & Gpimg).
  split; [|lia]. intros [C|[C|[C|[C|[C|C]]]]]; try lia.
  apply (Gpimg a Ha). apply trans_g_img. apply cf_inG. exact C.
- split; [intros [C|[C|[C|[C|[C|C]]]]]; try lia; pose proof (HGl a C); lia | lia].
- split; [intros [C|[C|[C|[C|[C|C]]]]]; try lia; pose proof (HGl a C); lia | lia].
Qed.

(* The world at the end of run C: its thirteen ranges, over the world the stage leaves, the rest kept. *)
Lemma cf_wfin : forall (D : list byte) (W : world segs) (mem memF : word -> option byte) (B1 : list byte),
  tw_at TMAP_B (aview segs (w_H W) mem) (lc_cfg_b1 D B1) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) memF (TB_g_cfg + 24 + Z.of_nat j) =
     Some (YO0f.le_byte ((1 + (cf_v D 2 + 256 * cf_v D 3)) mod 2 ^ 32) 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) memF (TB_g_cfg + 28 + Z.of_nat j) =
     Some (YO0f.le_byte ((1 + cf_v D 1) mod 2 ^ 32) 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) memF (TB_g_cfg + 32 + Z.of_nat j) =
     Some (YO0f.le_byte (cf_v D 0 mod 8) 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) memF (TB_g_cfg + 36 + Z.of_nat j) =
     Some (YO0f.le_byte (cf_v D 4) 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) memF (TB_g_cfg + 40 + Z.of_nat j) =
     Some (YO0f.le_byte ((1 + (cf_v D 5 + 256 * cf_v D 6)) mod 2 ^ 32) 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) memF (TB_g_cfg + 44 + Z.of_nat j) =
     Some (YO0f.le_byte ((1 + (cf_v D 7 + 256 * cf_v D 8)) mod 2 ^ 32) 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) memF (TB_g_cfg + 48 + Z.of_nat j) =
     Some (YO0f.le_byte (cf_v D 9 + 256 * cf_v D 10) 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) memF (TB_g_cfg + 52 + Z.of_nat j) =
     Some (YO0f.le_byte ((1 + cf_v D 11 mod 255) mod 2 ^ 32) 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) memF (TB_g_cfg + 56 + Z.of_nat j) =
     Some (YO0f.le_byte ((DSpec.SPEC_CMD_MAX + (cf_v D 12 + 256 * cf_v D 13)
             mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32) 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) memF (TB_g_raw + 0 + Z.of_nat j) =
     Some (YO0f.le_byte (Z.land (Z.shiftr (lc_flags D) 3) 1) 4 j)) ->
  (forall j, (j < 8)%nat -> aview segs (w_H W) memF (TB_g_now + 0 + Z.of_nat j) =
     Some (YO0f.le_byte 1000000 8 j)) ->
  (forall j, (j < 1)%nat -> aview segs (w_H W) memF (TB_g_fail_next + 0 + Z.of_nat j) =
     Some (YO0f.le_byte 0 1 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) memF (TB_g_last_counter + 0 + Z.of_nat j) =
     Some (YO0f.le_byte 0 4 j)) ->
  (forall a, tw_in TMAP_B a -> ~ cf_gwr a ->
     aview segs (w_H W) memF a = aview segs (w_H W) mem a) ->
  tw_at TMAP_B (aview segs (w_H W) memF) (lc_pro_scal D B1).
Proof.
intros D W mem memF B1 HTW Hka Hack Hmr Hbo Hoff Hwk Hdg Hmc Hmb Hraw Hnow Hfail Hlast Hkept.
rewrite (cf_scal_eq D B1).
exact (cf_tw (aview segs (w_H W) mem) (aview segs (w_H W) memF) (lc_cfg_b1 D B1) _ _ _ _ _ _ _ _ _ _
  HTW Hka Hack Hmr Hbo Hoff Hwk Hdg Hmc Hmb Hraw Hnow Hfail Hlast Hkept).
Qed.

(* The cut at +0x4b0, from the facts run C leaves. *)
Lemma cf_close : forall (cx : lcx) ly' S' (W : world segs) regs' mem' md' Bw0 B1 regsF memF mdF,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs' mem' md' 0 -> lc_fr cx regs' ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem') ->
  lc_fsh cx (aview segs (w_H W) mem') false false -> lc_io cx W mem' -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W memF mdF 0 ->
  (forall r, In r [2; 3; 4; 8; 9] -> YK11.getr regsF (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)) ->
  YK11.getr regsF 18 = YK11.getr regs' 18 -> YK11.getr regsF 26 = YK11.getr regs' 26 ->
  YK11.getr regsF 25 = w64 (l_p cx + TOP.fi_off (IOK.prologue_cursor (l_pl cx))) ->
  YK11.getr regsF 23 = w64 (TOP.fi_n (IOK.prologue_cursor (l_pl cx))) ->
  YK11.getr regsF 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  YK11.getr regsF 21 = w64 TB_g_cfg -> YK11.getr regsF 20 = w64 (lc_F cx + 176) ->
  YK11.getr regsF 27 = w64 0x6000 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a -> aview segs (w_H W) memF a = aview segs (w_H W) mem' a) ->
  (forall a, apresent (w_H W) mem' a -> apresent (w_H W) memF a) ->
  rdword (aview segs (w_H W) memF) (lc_sp1 cx + 104) = Some (transportb_hi 8) ->
  rdword (aview segs (w_H W) memF) (lc_sp1 cx + 152) = Some (transportb_hi 9) ->
  rdword (aview segs (w_H W) memF) (lc_sp1 cx + 184) = Some (transportb_hi 10) ->
  rdword (aview segs (w_H W) memF) (lc_sp1 cx + 40) = Some (transportb_hi 11) ->
  tw_at TMAP_B (aview segs (w_H W) memF) (lc_pro_scal (l_pl cx) B1) ->
  @lc_st_scal rc B MT cx W (lc_cfg cx LO_SCAL regsF memF mdF).
Proof.
intros cx ly' S' W regs' mem' md' Bw0 B1 regsF memF mdF LAWS HB HC HFR HSP HFSH HIO HMT HW0 HSC HJF
  HR R18 R26 R25 R23 R22 R21 R20 R27 KV GP Q104 Q152 Q184 Q40 HTWF.
pose proof (cf_apart cx ly' S' W regs' mem' md' 0 LAWS HB HC) as AP.
exists ly', S', regsF, memF, mdF, Bw0, B1.
split; [reflexivity|].
split.
{ apply (lc_core_kept_run B MT XL RLO RHI cx ly' S' W regs' mem' md' 0 ly' S' W regsF memF mdF 0 HB HC HJF
    eq_refl (Permutation_refl _)).
  - exact HR.
  - intros a Ha. destruct (AP a ltac:(left; exact Ha)) as [Hw Hr]. exact (KV a Hr Hw).
  - intros i Hi. destruct (AP (l_p cx + i) ltac:(right; right; left; split; lia)) as [Hw Hr].
    exact (KV _ Hr Hw).
  - intros a Ha. destruct (AP a ltac:(right; left; unfold LF_FBYTES in *; lia)) as [Hw Hr].
    exact (KV a Hr Hw).
  - intros a Ha Hp. exact (GP a Hp). }
destruct HFR as (F18 & F26).
split; [split; [rewrite R18; exact F18 | rewrite R26; exact F26]|].
split.
{ unfold lc_spills, lf_spill_scal, lf_spill_sm in *. cbn [app] in HSP |- *.
  rewrite Forall_forall in HSP.
  pose proof (HSP (128, lc_F cx) ltac:(cbn [In]; tauto)) as H128.
  pose proof (HSP (136, lc_F cx) ltac:(cbn [In]; tauto)) as H136.
  cbn [fst snd] in H128, H136.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - rewrite (rdword_ext (aview segs (w_H W) mem') (aview segs (w_H W) memF) (lc_sp1 cx + 128))
      by (intros j Hj; destruct (AP (lc_sp1 cx + 128 + j) ltac:(right; right; right; right; lia)) as [Hw Hr];
          exact (KV _ Hr Hw)).
    exact H128.
  - rewrite (rdword_ext (aview segs (w_H W) mem') (aview segs (w_H W) memF) (lc_sp1 cx + 136))
      by (intros j Hj; destruct (AP (lc_sp1 cx + 136 + j) ltac:(right; right; right; right; lia)) as [Hw Hr];
          exact (KV _ Hr Hw)).
    exact H136.
  - exact Q104.
  - exact Q152.
  - exact Q184.
  - exact Q40. }
split.
{ apply (lc_fsh_kept cx (aview segs (w_H W) mem')); [|exact HFSH].
  intros a Ha. destruct (AP a ltac:(right; right; right; left; exact Ha)) as [Hw Hr]. exact (KV a Hr Hw). }
split.
{ unfold lc_io in *. apply (lc_garr8_kept (w_H W) (w_H W) mem' memF (lc_F cx + 176) _); [|exact HIO].
  intros j Hj.
  lazymatch type of Hj with context [length ?l] =>
    assert (Lio : length l = 32%nat) by (vm_compute; reflexivity); rewrite Lio in Hj end.
  destruct (AP (lc_F cx + 176 + j) ltac:(right; left; unfold LF_FBYTES in *; lia)) as [Hw Hr].
  exact (KV _ Hr Hw). }
split; [exact HMT|].
split; [exact (conj R25 R23)|].
split; [exact R22|]. split; [exact R21|]. split; [exact R20|]. split; [exact R27|].
split; [exact HW0|]. split; [exact HSC | exact HTWF].
Qed.
End cfg.

(* ------------------------------------------------------------------ *)
(* 6. Run C: the seats at each exit, the run, the cut at +0x4b0        *)
(* ------------------------------------------------------------------ *)

Section seatk. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* the realigned frame is present (the journal's window below sp0) *)
Lemma cf_pres : forall cx ly' S' (W : world segs) regs mem md e,
  @lc_core rc B cx ly' S' W regs mem md e ->
  forall a, lc_sp0 cx - LLVMF_STK <= a < lc_sp0 cx -> apresent (w_H W) mem a.
Proof.
intros cx ly' S' W regs mem md e HC a Ha.
destruct HC as ((_ & _ & (memS & HJ & _) & _) & _).
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
apply Hpres. lia.
Qed.

(* What the core gives when the cursor has bytes left: the block holds the flags byte and the cursor's bytes,
   the cursor is one byte into it, its bytes are the config bytes and its granules' shadow is the block's. *)
Lemma cf_blk : forall cx ly' S' (W : world segs) regs mem md,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W regs mem md 0 ->
  0 < cf_n (l_pl cx) ->
  cf_o (l_pl cx) = 1 /\ l_n cx = cf_n (l_pl cx) + 1 /\
  4096 <= l_p cx /\ l_p cx mod 8 = 0 /\ l_p cx + 16 <= alloc_ceiling /\
  (l_p cx + 15 < TB_g_cfg \/ TB_g_last_counter + 4 <= l_p cx) /\
  (l_p cx + 16 <= kLowShadowBeg \/ kHighMemBeg <= l_p cx) /\
  (forall j, Z.of_nat j < cf_n (l_pl cx) -> (j < 14)%nat ->
     val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j (cf_bs (l_pl cx)) 0)) /\
  (forall i, 0 <= i < (l_n cx + 7) / 8 ->
     val_mem segs (mrestrict (w_H W) mem) (SHADOW_OFF + (l_p cx + 1) / 8 + i) 1
       (if i <? l_n cx / 8 then 0 else l_n cx mod 8)).
Proof.
intros cx ly' S' W regs mem md LAWS HB HC Hn.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
destruct (cf_on (l_pl cx)) as [(Ho & Hn0 & HL) | (Ho & HnL & HL)]; [lia|].
assert (Hln : l_n cx = cf_n (l_pl cx) + 1) by lia.
destruct (N12 ltac:(lia)) as (Hin & Hp4 & Hpc & Hp8 & Happ & Himg).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (Hp16 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & Hc4096).
pose proof Hp16 as Hq. apply Z.mod_divide in Hq; [|lia]. destruct Hq as [q1 Hq1].
assert (Hp16' : l_p cx + 16 <= alloc_ceiling).
{ apply Z.mod_divide in Hc4096; [|lia]. destruct Hc4096 as [q2 Hq2]. lia. }
assert (HQ : (l_p cx + 1) / 8 = l_p cx / 8).
{ rewrite Hq1. replace (q1 * 16 + 1) with ((2 * q1) * 8 + 1) by ring.
  replace (q1 * 16) with ((2 * q1) * 8) by ring.
  rewrite Z.div_add_l, Z.div_mul by lia. rewrite (Z.div_small 1 8) by lia. lia. }
split; [exact Ho|]. split; [exact Hln|]. split; [exact Hp4|]. split; [exact Hp8|]. split; [exact Hp16'|].
split.
{ destruct (Z_lt_le_dec (l_p cx) (TB_g_cfg - 16)) as [H1|H1]; [left; lia|].
  destruct (Z_lt_le_dec (l_p cx) (TB_g_last_counter + 4)) as [H2|H2]; [|right; exact H2].
  exfalso. apply (Himg (l_p cx) ltac:(lia)). apply cf_gimg. lia. }
split.
{ destruct Happ as (_ & [H1 | (H1 & _)]); [left | right; exact H1].
  unfold kLowShadowBeg in *. lia. }
split.
{ intros j Hj Hj14. pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIN & _).
  pose proof (HIN (S j) ltac:(rewrite length_map; lia)) as (HV & _).
  rewrite (cf_nth_map (l_pl cx) (S j) ltac:(lia)) in HV.
  replace (l_p cx + Z.of_nat (S j)) with (l_p cx + 1 + Z.of_nat j) in HV by lia.
  rewrite (cf_bs_nth (l_pl cx) j Hj14). unfold cf_v, cf_b. rewrite Ho.
  rewrite (proj2 (Z.ltb_lt _ _) Hj). replace (Z.to_nat (1 + Z.of_nat j)) with (S j) by lia. exact HV. }
intros i Hi. destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as ((_ & _ & Hsh) & _).
assert (RQ : req_size (l_n cx) = l_n cx) by (unfold req_size; destruct (Z.eqb_spec (l_n cx) 0); lia).
rewrite RQ in Hsh. apply cf_vm1. rewrite HQ. exact (Hsh i Hi).
Qed.

(* The seat of run C when the cursor has k bytes, 1 <= k <= 13: s7 pinned to k. *)
Lemma cf_seatK : forall (cx : lcx) ly' S' (W : world segs) regs mem md (k : nat) (s0 s1 : Z),
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W regs mem md 0 -> lc_fr cx regs ->
  lc_cur cx regs 19 23 (lc_c1 (l_pl cx)) -> YK11.getr regs 24 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 21 = w64 TB_g_cfg ->
  (1 <= k <= 13)%nat -> cf_n (l_pl cx) = Z.of_nat k ->
  s0 = (if 8 <=? Z.of_nat k + 1 then 0 else Z.of_nat k + 1) ->
  ((8 <= k)%nat -> s1 = Z.of_nat k - 7) ->
  regions_wf (cf_rgsC k s0 s1) = true ->
  @st_ok_pi segs VAL (l_fx cx) (cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1))
    (cf_ssK k s0 s1)
    (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_RC2)) mem (YK11.seg_rom segs))).
Proof.
intros cx ly' S' W regs mem md k s0 s1 LAWS HB HC HFR HCUR R24 R21 Hk HN Hs0 Hs1 Hwf.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
destruct (cf_blk cx ly' S' W regs mem md LAWS HB HC ltac:(lia))
  as (Ho & Hln & Hp4 & Hp8 & Hpc & HG & HSh & HBY & HSV).
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
destruct HFR as (R18 & R26).
destruct HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19. rewrite Ho in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23. rewrite HN in R23.
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
assert (Hc8 : (l_p cx + 1) mod 8 = 1).
{ rewrite Z.add_mod, Hp8 by lia. reflexivity. }
assert (V0 : (if 0 <? l_n cx / 8 then 0 else l_n cx mod 8) = s0).
{ rewrite Hs0, Hln, HN. destruct (Z.leb_spec 8 (Z.of_nat k + 1)) as [H|H].
  - rewrite (proj2 (Z.ltb_lt 0 ((Z.of_nat k + 1) / 8))) by (apply Z.div_str_pos; lia). reflexivity.
  - rewrite (Z.div_small (Z.of_nat k + 1) 8) by lia. cbn [Z.ltb Z.compare]. apply Z.mod_small. lia. }
assert (V1 : (8 <= k)%nat -> (if 1 <? l_n cx / 8 then 0 else l_n cx mod 8) = s1).
{ intros H8. rewrite (Hs1 H8), Hln, HN.
  rewrite <- (Z.div_unique (Z.of_nat k + 1) 8 1 (Z.of_nat k + 1 - 8)) by lia.
  rewrite <- (Z.mod_unique (Z.of_nat k + 1) 8 1 (Z.of_nat k + 1 - 8)) by lia. cbn. lia. }
assert (EP : getr (ms_regs (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_RC2)) mem
  (YK11.seg_rom segs)))) (Z_to_bv 5 23) = Z_to_bv 64 (Z.of_nat k)) by exact R23.
refine (st_ok_pi_pin_reg' (PI := PI_transportb)
  (cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1))
  (mkSS CF_RC2 sr_atoms (cf_rgsC k s0 s1) None (mkFacts (cf_atomsC (mkAF (Z.of_nat k) (Z.of_nat k) 0)) [] cf_alias))
  _ (Z_to_bv 5 23) (Z.of_nat k) _ EP eq_refl).
apply (cf_seatC W regs mem (lc_sp1 cx) (l_p cx + 1) (lc_flags (l_pl cx)) (Z.of_nat k) k s0 s1
  (cf_bs (l_pl cx)) (mkAF (Z.of_nat k) (Z.of_nat k) 0) R2 R9 R19 R21 R23 R24 R26).
- lia.
- exact N3.
- lia.
- lia.
- exact Hc8.
- lia.
- exact HFL.
- rewrite <- V0. destruct (0 <? l_n cx / 8); [lia | pose proof (Z.mod_pos_bound (l_n cx) 8 ltac:(lia)); lia].
- intros H8. rewrite (Hs1 H8). lia.
- lia.
- apply cf_bs_len.
- apply cf_bs_rng.
- apply (cf_af _ 23 (Z.of_nat k)); [|lia | cbn; apply Z.mod_1_r | lia].
  unfold cf_E. rewrite (can_ew_Eimg_Ereg_nat regs _ 23%nat (Z_to_bv 5 23) eq_refl), R23.
  apply unsigned_lit_small. lia.
- intros j Hj. exact (HBY j ltac:(lia) ltac:(lia)).
- rewrite <- V0. replace (SHADOW_OFF + (l_p cx + 1) / 8) with (SHADOW_OFF + (l_p cx + 1) / 8 + 0) by lia.
  apply HSV. split; [lia|]. apply Z.div_str_pos. lia.
- intros H8. rewrite <- (V1 H8). apply HSV. split; [lia|].
  match goal with |- 1 < ?a / 8 => assert (2 <= a / 8) by (apply (Z.div_le_lower_bound _ 8 2); lia); lia end.
- intros a Ha. apply (cf_pres cx ly' S' W regs mem md 0 HC). unfold LLVMF_STK. lia.
- destruct HG as [HG|HG]; [left | right]; lia.
- destruct HSh as [HSh|HSh]; [left | right]; lia.
- unfold ESTACK. lia.
- exact Hwf.
Qed.

(* The seat of run C when the cursor has fourteen bytes or more: s7 not pinned, its range [14, 2 ^ 26]. *)
Lemma cf_seatN : forall (cx : lcx) ly' S' (W : world segs) regs mem md (s1 : Z),
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W regs mem md 0 -> lc_fr cx regs ->
  lc_cur cx regs 19 23 (lc_c1 (l_pl cx)) -> YK11.getr regs 24 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 21 = w64 TB_g_cfg ->
  14 <= cf_n (l_pl cx) ->
  s1 = (if 16 <=? cf_n (l_pl cx) + 1 then 0 else cf_n (l_pl cx) + 1 - 8) ->
  regions_wf (cf_rgsC 14 0 s1) = true ->
  @st_ok_pi segs VAL (l_fx cx) (cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1))
    (cf_ssN s1)
    (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_RC2)) mem (YK11.seg_rom segs))).
Proof.
intros cx ly' S' W regs mem md s1 LAWS HB HC HFR HCUR R24 R21 HN Hs1 Hwf.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
destruct (cf_blk cx ly' S' W regs mem md LAWS HB HC ltac:(lia))
  as (Ho & Hln & Hp4 & Hp8 & Hpc & HG & HSh & HBY & HSV).
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
destruct HFR as (R18 & R26).
destruct HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19. rewrite Ho in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
assert (Hc8 : (l_p cx + 1) mod 8 = 1).
{ rewrite Z.add_mod, Hp8 by lia. reflexivity. }
assert (V0 : (if 0 <? l_n cx / 8 then 0 else l_n cx mod 8) = 0).
{ rewrite (proj2 (Z.ltb_lt 0 (l_n cx / 8))) by (apply Z.div_str_pos; lia). reflexivity. }
assert (V1 : (if 1 <? l_n cx / 8 then 0 else l_n cx mod 8) = s1).
{ rewrite Hs1, Hln. destruct (Z.leb_spec 16 (cf_n (l_pl cx) + 1)) as [H|H].
  - rewrite (proj2 (Z.ltb_lt 1 ((cf_n (l_pl cx) + 1) / 8))) by (match goal with |- 1 < ?a / 8 => assert (2 <= a / 8) by (apply (Z.div_le_lower_bound _ 8 2); lia); lia end).
    reflexivity.
  - rewrite <- (Z.div_unique (cf_n (l_pl cx) + 1) 8 1 (cf_n (l_pl cx) + 1 - 8)) by lia.
    rewrite <- (Z.mod_unique (cf_n (l_pl cx) + 1) 8 1 (cf_n (l_pl cx) + 1 - 8)) by lia. reflexivity. }
apply (cf_seatC W regs mem (lc_sp1 cx) (l_p cx + 1) (lc_flags (l_pl cx)) (cf_n (l_pl cx)) 14 0 s1
  (cf_bs (l_pl cx)) (mkAF 14 (2 ^ 26) 0) R2 R9 R19 R21 R23 R24 R26).
- lia.
- exact N3.
- lia.
- lia.
- exact Hc8.
- lia.
- exact HFL.
- lia.
- intros _. rewrite <- V1. destruct (1 <? l_n cx / 8); [lia | pose proof (Z.mod_pos_bound (l_n cx) 8 ltac:(lia)); lia].
- lia.
- apply cf_bs_len.
- apply cf_bs_rng.
- apply (cf_af _ 23 (cf_n (l_pl cx))); [|lia | cbn; apply Z.mod_1_r | lia].
  unfold cf_E. rewrite (can_ew_Eimg_Ereg_nat regs _ 23%nat (Z_to_bv 5 23) eq_refl), R23.
  apply unsigned_lit_small. lia.
- intros j Hj. exact (HBY j ltac:(lia) ltac:(lia)).
- rewrite <- V0. replace (SHADOW_OFF + (l_p cx + 1) / 8) with (SHADOW_OFF + (l_p cx + 1) / 8 + 0) by lia.
  apply HSV. split; [lia|]. apply Z.div_str_pos. lia.
- intros _. rewrite <- V1. apply HSV. split; [lia|].
  match goal with |- 1 < ?a / 8 => assert (2 <= a / 8) by (apply (Z.div_le_lower_bound _ 8 2); lia); lia end.
- intros a Ha. apply (cf_pres cx ly' S' W regs mem md 0 HC). unfold LLVMF_STK. lia.
- destruct HG as [HG|HG]; [left | right]; lia.
- destruct HSh as [HSh|HSh]; [left | right]; lia.
- unfold ESTACK. lia.
- exact Hwf.
Qed.

(* The seat of run C when the cursor has no byte: no cursor region, s7 pinned to 0. *)
Lemma cf_seat0 : forall (cx : lcx) ly' S' (W : world segs) regs mem md,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W regs mem md 0 -> lc_fr cx regs ->
  lc_cur cx regs 19 23 (lc_c1 (l_pl cx)) -> YK11.getr regs 24 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 21 = w64 TB_g_cfg ->
  cf_n (l_pl cx) = 0 ->
  @st_ok_pi segs VAL (l_fx cx) (cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1))
    cf_ss0
    (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_RC2)) mem (YK11.seg_rom segs))).
Proof.
intros cx ly' S' W regs mem md LAWS HB HC HFR HCUR R24 R21 HN.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
destruct HFR as (R18 & R26).
destruct HCUR as (R19 & R23).
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23. rewrite HN in R23.
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (UH8 : bv_unsigned (ew E (A_HI 8)) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UH9 : bv_unsigned (ew E (A_HI 9)) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UH10 : bv_unsigned (ew E (A_HI 10)) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UH11 : bv_unsigned (ew E (A_HI 11)) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (EP : getr (ms_regs (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_RC2)) mem
  (YK11.seg_rom segs)))) (Z_to_bv 5 23) = Z_to_bv 64 0) by exact R23.
refine (st_ok_pi_pin_reg' (PI := PI_transportb) E
  (mkSS CF_RC2 sr_atoms cf_wregs None (mkFacts (cf_atomsG (mkAF 0 0 0)) [] [])) _ (Z_to_bv 5 23) 0 _ EP eq_refl).
apply (cf_seatG W regs mem (lc_sp1 cx) (lc_flags (l_pl cx)) CF_RC2 cf_wregs (cf_bs (l_pl cx))
  (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1) (mkAF 0 0 0) R2 R9 R21 R24 R26).
- lia.
- exact N3.
- exact HFL.
- apply (cf_af _ 23 0); [|lia | cbn; apply Z.mod_1_r | lia].
  fold E. rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23. reflexivity.
- vm_compute. reflexivity.
- fold E. apply (cf_wregs_ok E W mem (lc_sp1 cx) U9 U21 UH8 UH9 UH10 UH11); [lia|].
  intros a Ha. apply (cf_pres cx ly' S' W regs mem md 0 HC). unfold LLVMF_STK. lia.
- fold E. apply (cf_wregs_disj E (lc_sp1 cx) U9 U21 UH8 UH9 UH10 UH11). lia.
Qed.
End seatk.

(* ---- the values the run leaves, as the model's ---- *)
Lemma cf_dn_off : forall E n k x, bv_unsigned (ew E n) = x -> sv_denot E (SOff n k) = Z_to_bv 64 (x + k).
Proof. intros E n k x H. cbn [sv_denot]. rewrite H. reflexivity. Qed.
Lemma cf_dn_alu : forall E op a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  sv_denot E (SAlu op a b) = Z_to_bv 64 (zalu64 op x y).
Proof. intros E op a b x y Ha Hb. cbn [sv_denot]. rewrite Ha, Hb. apply zalu64_sound. Qed.
Lemma cf_dn_mul : forall E op a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  sv_denot E (SMd op a b) = Z_to_bv 64 (zmd64 op x y).
Proof. intros E op a b x y Ha Hb. cbn [sv_denot]. rewrite Ha, Hb. apply zmd64_sound. Qed.
Lemma cf_dn_lit : forall E z, sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.

Ltac cf_dn :=
  lazymatch goal with
  | |- sv_denot ?E (SLit ?z) = _ => apply cf_dn_lit
  | |- sv_denot ?E (SOff ?n ?k) = _ => eapply cf_dn_off; eassumption
  | |- sv_denot ?E (SAlu ?op ?a ?b) = _ => eapply cf_dn_alu; cf_dn
  | |- sv_denot ?E (SMd ?op ?a ?b) = _ => eapply cf_dn_mul; cf_dn
  end.

Lemma cf_and7_chk : tw_allz (fun v => Z.eqb (zalu64 ALU_AND v 7) (v mod 8)) 0 (Z.to_nat 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cf_and7 : forall v, 0 <= v < 256 -> zalu64 ALU_AND v 7 = v mod 8.
Proof.
intros v Hv. apply Z.eqb_eq.
exact (tw_allz_ok _ (Z.to_nat 256) 0 cf_and7_chk v ltac:(rewrite Z2Nat.id by lia; lia)).
Qed.

Lemma cf_s32_lit : forall E x, x = 0 -> sv_denot E (SLit 0) = Z_to_bv 64 (x mod 8).
Proof. intros E x ->. reflexivity. Qed.
Lemma cf_s32 : forall E n x, bv_unsigned (ew E n) = x -> 0 <= x < 256 ->
  sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 7)) = Z_to_bv 64 (x mod 8).
Proof.
intros E n x Hn Hx. erewrite cf_dn_alu; [| apply (cf_dn_off E n 0 x Hn) | apply cf_dn_lit].
rewrite Z.add_0_r, (cf_and7 x Hx). reflexivity.
Qed.
Lemma cf_s28_lit : forall E x, x = 0 -> sv_denot E (SLit 1) = Z_to_bv 64 ((1 + x) mod 2 ^ 32).
Proof. intros E x ->. reflexivity. Qed.
Lemma cf_s28 : forall E n x, bv_unsigned (ew E n) = x -> 0 <= x < 256 ->
  sv_denot E (SOff n 1) = Z_to_bv 64 ((1 + x) mod 2 ^ 32).
Proof. intros E n x Hn Hx. rewrite (cf_dn_off E n 1 x Hn). f_equal. rewrite Z.mod_small by lia. lia. Qed.
Lemma cf_su_lit : forall E x y, x = 0 -> y = 0 -> sv_denot E (SLit 1) = Z_to_bv 64 ((1 + (x + 256 * y)) mod 2 ^ 32).
Proof. intros E x y -> ->. reflexivity. Qed.
Lemma cf_su_lo : forall E n x y, bv_unsigned (ew E n) = x -> 0 <= x < 256 -> y = 0 ->
  sv_denot E (SOff n 1) = Z_to_bv 64 ((1 + (x + 256 * y)) mod 2 ^ 32).
Proof. intros E n x y Hn Hx ->. rewrite (cf_dn_off E n 1 x Hn). f_equal. rewrite Z.mod_small by lia. lia. Qed.
Lemma cf_su : forall E n m x y, bv_unsigned (ew E n) = x -> bv_unsigned (ew E m) = y ->
  0 <= x < 256 -> 0 <= y < 256 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_OR (SOff n 0) (SAlu ALU_SLL (SOff m 0) (SLit 8))) (SLit 1)) =
  Z_to_bv 64 ((1 + (x + 256 * y)) mod 2 ^ 32).
Proof.
intros E n m x y Hn Hm Hx Hy. etransitivity; [cf_dn|]. rewrite !Z.add_0_r, (cf_u16_or x y Hx Hy). reflexivity.
Qed.
Lemma cf_s36_lit : forall E x, x = 0 -> sv_denot E (SLit 0) = Z_to_bv 64 x.
Proof. intros E x ->. reflexivity. Qed.
Lemma cf_s36 : forall E n x, bv_unsigned (ew E n) = x -> sv_denot E (SOff n 0) = Z_to_bv 64 x.
Proof. intros E n x Hn. rewrite (cf_dn_off E n 0 x Hn), Z.add_0_r. reflexivity. Qed.
Lemma cf_s48_lit : forall E x y, x = 0 -> y = 0 -> sv_denot E (SLit 0) = Z_to_bv 64 (x + 256 * y).
Proof. intros E x y -> ->. reflexivity. Qed.
Lemma cf_s48_lo : forall E n x y, bv_unsigned (ew E n) = x -> y = 0 ->
  sv_denot E (SOff n 0) = Z_to_bv 64 (x + 256 * y).
Proof. intros E n x y Hn ->. rewrite (cf_dn_off E n 0 x Hn). f_equal; lia. Qed.
Lemma cf_s48 : forall E n m x y, bv_unsigned (ew E n) = x -> bv_unsigned (ew E m) = y ->
  0 <= x < 256 -> 0 <= y < 256 ->
  sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff m 0) (SLit 8)) (SOff n 0)) = Z_to_bv 64 (x + 256 * y).
Proof.
intros E n m x y Hn Hm Hx Hy. etransitivity; [cf_dn|]. rewrite !Z.add_0_r, (cf_u16_or' x y Hx Hy). reflexivity.
Qed.
Lemma cf_s52_lit : forall E x, x = 0 -> sv_denot E (SLit 1) = Z_to_bv 64 ((1 + x mod 255) mod 2 ^ 32).
Proof. intros E x ->. reflexivity. Qed.
Lemma cf_s52 : forall E n x, bv_unsigned (ew E n) = x -> 0 <= x < 256 ->
  sv_denot E
    (SAlu ALU_ADD
       (SAlu ALU_AND (SAlu ALU_AND (SOff n 0) (SLit 255))
          (SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_ADD (SAlu ALU_AND (SOff n 0) (SLit 255)) (SLit (-255))) (SLit 1))
             (SLit (-1))))
       (SLit 1)) =
  Z_to_bv 64 ((1 + x mod 255) mod 2 ^ 32).
Proof.
intros E n x Hn Hx. etransitivity; [cf_dn|]. rewrite !Z.add_0_r. pose proof (cf_mc x Hx) as M.
unfold cf_mc_f in M. rewrite M. reflexivity.
Qed.
Lemma cf_s56_lit : forall E x y, x = 0 -> y = 0 ->
  sv_denot E (SLit 24) =
  Z_to_bv 64 ((DSpec.SPEC_CMD_MAX + (x + 256 * y) mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32).
Proof. intros E x y -> ->. vm_compute. reflexivity. Qed.
Lemma cf_s56_lo : forall E n x y, bv_unsigned (ew E n) = x -> 0 <= x < 256 -> y = 0 ->
  sv_denot E
    (SAlu ALU_SRL
       (SAlu ALU_SLL
          (SAlu ALU_ADD
             (SAlu ALU_SUB (SAlu ALU_OR (SLit 0) (SOff n 0))
                (SMd M_MUL (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_OR (SLit 0) (SOff n 0)) (SLit 22967)) (SLit 25))
                   (SLit 1461)))
             (SLit 24))
          (SLit 48))
       (SLit 48)) =
  Z_to_bv 64 ((DSpec.SPEC_CMD_MAX + (x + 256 * y) mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32).
Proof.
intros E n x y Hn Hx ->. etransitivity; [cf_dn|]. rewrite !Z.add_0_r, (cf_or0 x Hx).
pose proof (cf_mb x ltac:(lia)) as M. unfold cf_mb_f in M. rewrite M; rewrite ?Z.mul_0_r, ?Z.add_0_r; try reflexivity.
Qed.
Lemma cf_s56 : forall E n m x y, bv_unsigned (ew E n) = x -> bv_unsigned (ew E m) = y ->
  0 <= x < 256 -> 0 <= y < 256 ->
  sv_denot E
    (SAlu ALU_SRL
       (SAlu ALU_SLL
          (SAlu ALU_ADD
             (SAlu ALU_SUB (SAlu ALU_OR (SAlu ALU_SLL (SOff m 0) (SLit 8)) (SOff n 0))
                (SMd M_MUL
                   (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_OR (SAlu ALU_SLL (SOff m 0) (SLit 8)) (SOff n 0)) (SLit 22967))
                      (SLit 25))
                   (SLit 1461)))
             (SLit 24))
          (SLit 48))
       (SLit 48)) =
  Z_to_bv 64 ((DSpec.SPEC_CMD_MAX + (x + 256 * y) mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32).
Proof.
intros E n m x y Hn Hm Hx Hy. etransitivity; [cf_dn|]. rewrite !Z.add_0_r, (cf_u16_or' x y Hx Hy).
pose proof (cf_mb (x + 256 * y) ltac:(lia)) as M. unfold cf_mb_f in M. rewrite M. reflexivity.
Qed.
Lemma cf_sraw : forall E n f, bv_unsigned (ew E n) = f -> 0 <= f < 256 ->
  sv_denot E (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 60)) (SLit 63)) = Z_to_bv 64 (Z.land (Z.shiftr f 3) 1).
Proof.
intros E n f Hn Hf. etransitivity; [cf_dn|]. rewrite !Z.add_0_r.
destruct (cf_bit f Hf) as (_ & _ & Hb & _). rewrite Hb. reflexivity.
Qed.

(* a side condition of a value lemma *)
Ltac cf_side := first
  [ match goal with H : bv_unsigned (ew ?E ?n) = ?x |- bv_unsigned (ew ?E ?n) = ?x => exact H end
  | match goal with
    | UB : forall j, (j < 14)%nat -> bv_unsigned (ew ?E (32 + j)) = _ |- bv_unsigned (ew ?E ?n) = _ =>
        let j := eval cbv in (n - 32)%nat in exact (UB j ltac:(lia))
    end
  | apply cf_v_rng
  | apply cf_flags_rng
  | (apply cf_v_hi; lia)
  | lia ].
(* the value of a chunk, as the model's *)
Ltac cf_fld := first
  [ (apply cf_s32_lit; cf_side) | (apply cf_s32; cf_side) | (apply cf_s28_lit; cf_side) | (apply cf_s28; cf_side)
  | (apply cf_su_lit; cf_side) | (apply cf_su_lo; cf_side) | (apply cf_su; cf_side)
  | (apply cf_s36_lit; cf_side) | (apply cf_s36; cf_side)
  | (apply cf_s48_lit; cf_side) | (apply cf_s48_lo; cf_side) | (apply cf_s48; cf_side)
  | (apply cf_s52_lit; cf_side) | (apply cf_s52; cf_side)
  | (apply cf_s56_lit; cf_side) | (apply cf_s56_lo; cf_side) | (apply cf_s56; cf_side)
  | (apply cf_sraw; cf_side) | apply cf_dn_lit ].

Lemma cf_land1 : forall x, 0 <= x -> 0 <= Z.land x 1 <= 1.
Proof.
intros x Hx. split; [apply Z.land_nonneg; left; exact Hx|].
replace (Z.land x 1) with (x mod 2 ^ 1) by (rewrite <- (Z.land_ones x 1) by lia; reflexivity).
pose proof (Z.mod_pos_bound x (2 ^ 1) ltac:(lia)). lia.
Qed.

Lemma cf_le8 : forall z, 0 <= z < 2 ^ 64 ->
  let b := fun k => YO0f.le_byte z 8 k in
  b 0%nat + 256 * (b 1%nat + 256 * (b 2%nat + 256 * (b 3%nat + 256 * (b 4%nat + 256 * (b 5%nat + 256 *
    (b 6%nat + 256 * b 7%nat)))))) = z.
Proof.
intros z Hz. cbn beta. unfold YO0f.le_byte. rewrite !Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256.
change (2 ^ (8 * Z.of_nat 2)) with (256 * 256). change (2 ^ (8 * Z.of_nat 3)) with (256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 4)) with (256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 5)) with (256 * 256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 6)) with (256 * 256 * 256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 7)) with (256 * 256 * 256 * 256 * 256 * 256 * 256).
rewrite Z.div_1_r. rewrite <- !Z.div_div by lia.
assert (H7 : z / 256 / 256 / 256 / 256 / 256 / 256 / 256 < 256).
{ change (2 ^ 64) with (256 * 256 * 256 * 256 * 256 * 256 * 256 * 256) in Hz.
  repeat (apply Z.div_lt_upper_bound; [lia|]). lia. }
rewrite (Z.mod_small (z / 256 / 256 / 256 / 256 / 256 / 256 / 256))
  by (split; [repeat (apply Z.div_pos; [|lia]); lia | exact H7]).
pose proof (Z.div_mod z 256 ltac:(lia)) as E0.
pose proof (Z.div_mod (z / 256) 256 ltac:(lia)) as E1.
pose proof (Z.div_mod (z / 256 / 256) 256 ltac:(lia)) as E2.
pose proof (Z.div_mod (z / 256 / 256 / 256) 256 ltac:(lia)) as E3.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E4.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E5.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E6.
lia.
Qed.

(* an eight-byte value of the restricted memory is a word of the view *)
Lemma cf_rdw : forall (H : word -> bool) (m : word -> option byte) a v,
  val_mem tfibsegs (mrestrict H m) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview tfibsegs H m) a = Some v.
Proof.
intros H m a v HV Hv. pose proof (cf_vb H m a 8 v HV) as B. unfold rdword.
replace a with (a + Z.of_nat 0) at 1 by lia.
replace (a + 1) with (a + Z.of_nat 1) by lia. replace (a + 2) with (a + Z.of_nat 2) by lia.
replace (a + 3) with (a + Z.of_nat 3) by lia. replace (a + 4) with (a + Z.of_nat 4) by lia.
replace (a + 5) with (a + Z.of_nat 5) by lia. replace (a + 6) with (a + Z.of_nat 6) by lia.
replace (a + 7) with (a + Z.of_nat 7) by lia.
rewrite !B by lia. f_equal. exact (cf_le8 v Hv).
Qed.

(* the range of a value read back *)
Ltac cf_rng :=
  lazymatch goal with |- 0 <= ?v < 2 ^ (8 * Z.of_N ?w) =>
    let p := eval vm_compute in (8 * Z.of_N w) in change (0 <= v < 2 ^ p) end;
  repeat match goal with |- context [cf_v ?D ?j] =>
    lazymatch goal with _ : 0 <= cf_v D j < 256 |- _ => fail | _ => pose proof (cf_v_rng D j) end end;
  repeat match goal with |- context [Z.land (Z.shiftr ?f 3) 1] =>
    lazymatch goal with _ : 0 <= Z.land (Z.shiftr f 3) 1 <= 1 |- _ => fail | _ =>
      pose proof (cf_land1 (Z.shiftr f 3) ltac:(apply Z.shiftr_nonneg; apply (proj1 (cf_flags_rng _)))) end end;
  first [ apply Z.mod_pos_bound; lia | lia
        | let P8 := fresh "P8" in let P9 := fresh "P9" in let P10 := fresh "P10" in let P11 := fresh "P11" in
          pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _); lia ].

(* the bytes a chunk of the run's last state leaves at its base + off *)
Ltac cf_rbk RG off U :=
  lazymatch type of RG with YP09.region_ok _ _ _ (YP09.mkRegion (Some ?nb) _ _ _ _ ?cs) =>
    lazymatch cs with context [YP09.mkChunk off (CVal ?w ?e)] =>
      refine (can_field_of_region _ _ nb _ cs _ _ _ _ off w e _ RG U _ _ _ _);
      [ cbn [In]; repeat (first [left; reflexivity | right])
      | cf_fld
      | cf_rng
      | cbn; lia ] end end.

(* the window of the run's regions lies in cf_wr *)
Ltac cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 :=
  first [ exfalso; lia
        | rewrite ?U9, ?U21, ?U408, ?U409, ?U410, ?U411 in *; rewrite ?P8, ?P9, ?P10, ?P11 in *;
          unfold cf_wr, cf_gwr, TB_g_cfg, TB_g_raw, TB_g_now, TB_g_fail_next, TB_g_last_counter in *; lia ].

(* the write rights of run C *)
Ltac cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ exfalso; lia
            | rewrite U9 in Ha; left; split; [unfold awr_byte, LLVMF_STK; left; lia | lia]
            | rewrite U21 in Ha; right; left; apply cf_inG; unfold TB_g_cfg in Ha; unfold cf_gwr, TB_g_cfg; lia
            | rewrite U408, P8 in Ha; right; left; apply cf_inG; unfold cf_gwr, TB_g_raw; lia
            | rewrite U409, P9 in Ha; right; left; apply cf_inG; unfold cf_gwr, TB_g_now; lia
            | rewrite U410, P10 in Ha; right; left; apply cf_inG; unfold cf_gwr, TB_g_fail_next; lia
            | rewrite U411, P11 in Ha; right; left; apply cf_inG; unfold cf_gwr, TB_g_last_counter; lia ] |]);
  apply awr_ok_x_nil.

(* a register of the run's last state, its symbolic value computed *)
Ltac cf_reg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?valx ?Ex ?ssx (restrict ?Hh ?msx) =>
      pose proof (st_ok_pi_restrict_reg (PI := PI_transportb) Hh Ex ssx msx r HS) as H;
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (YK11.getr (ms_regs msx) r = sv_denot Ex e) in H
  end.

Section runc. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The cut at +0x4b0 from what run C leaves: the registers, the bytes it wrote, the rest kept. *)
Lemma cf_fin : forall (cx : lcx) ly' S' (W : world segs) regs mem md Bw0 B1 regsF memF mdF,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs mem md 0 -> lc_fr cx regs ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem) ->
  lc_fsh cx (aview segs (w_H W) mem) false false -> lc_io cx W mem -> lc_meter MT cx S' 0 ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  YK11.getr regs 21 = w64 TB_g_cfg -> YK11.getr regs 20 = w64 (lc_F cx + 176) ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) ->
  lc_tw W mem (lc_cfg_b1 (l_pl cx) B1) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W memF mdF 0 ->
  (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] -> YK11.getr regsF r = YK11.getr regs r) ->
  YK11.getr regsF 25 = w64 (l_p cx + (cf_o (l_pl cx) + Z.min (cf_n (l_pl cx)) 14)) ->
  YK11.getr regsF 23 = w64 (cf_n (l_pl cx) - Z.min (cf_n (l_pl cx)) 14) ->
  YK11.getr regsF 27 = w64 0x6000 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a -> aview segs (w_H W) memF a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) memF a) ->
  val_mem segs (mrestrict (w_H W) memF) (lc_sp1 cx + 104) 8 (transportb_hi 8) ->
  val_mem segs (mrestrict (w_H W) memF) (lc_sp1 cx + 152) 8 (transportb_hi 9) ->
  val_mem segs (mrestrict (w_H W) memF) (lc_sp1 cx + 184) 8 (transportb_hi 10) ->
  val_mem segs (mrestrict (w_H W) memF) (lc_sp1 cx + 40) 8 (transportb_hi 11) ->
  val_mem segs (mrestrict (w_H W) memF) (TB_g_cfg + 24) 4
    ((1 + (cf_v (l_pl cx) 2 + 256 * cf_v (l_pl cx) 3)) mod 2 ^ 32) ->
  val_mem segs (mrestrict (w_H W) memF) (TB_g_cfg + 28) 4 ((1 + cf_v (l_pl cx) 1) mod 2 ^ 32) ->
  val_mem segs (mrestrict (w_H W) memF) (TB_g_cfg + 32) 4 (cf_v (l_pl cx) 0 mod 8) ->
  val_mem segs (mrestrict (w_H W) memF) (TB_g_cfg + 36) 4 (cf_v (l_pl cx) 4) ->
  val_mem segs (mrestrict (w_H W) memF) (TB_g_cfg + 40) 4
    ((1 + (cf_v (l_pl cx) 5 + 256 * cf_v (l_pl cx) 6)) mod 2 ^ 32) ->
  val_mem segs (mrestrict (w_H W) memF) (TB_g_cfg + 44) 4
    ((1 + (cf_v (l_pl cx) 7 + 256 * cf_v (l_pl cx) 8)) mod 2 ^ 32) ->
  val_mem segs (mrestrict (w_H W) memF) (TB_g_cfg + 48) 4 (cf_v (l_pl cx) 9 + 256 * cf_v (l_pl cx) 10) ->
  val_mem segs (mrestrict (w_H W) memF) (TB_g_cfg + 52) 4 ((1 + cf_v (l_pl cx) 11 mod 255) mod 2 ^ 32) ->
  val_mem segs (mrestrict (w_H W) memF) (TB_g_cfg + 56) 4
    ((DSpec.SPEC_CMD_MAX + (cf_v (l_pl cx) 12 + 256 * cf_v (l_pl cx) 13)
        mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32) ->
  val_mem segs (mrestrict (w_H W) memF) (transportb_hi 8 + 1652) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1) ->
  val_mem segs (mrestrict (w_H W) memF) (transportb_hi 9 + 1676) 8 1000000 ->
  val_mem segs (mrestrict (w_H W) memF) (transportb_hi 10 + 1656) 1 0 ->
  val_mem segs (mrestrict (w_H W) memF) (transportb_hi 11 + 1668) 4 0 ->
  @lc_st_scal rc B MT cx W (lc_cfg cx LO_SCAL regsF memF mdF).
Proof.
intros cx ly' S' W regs mem md Bw0 B1 regsF memF mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21 R20 HW0 HSC HTW HJF
  KR R25 R23 R27 KV GP Q104 Q152 Q184 Q40 F24 F28 F32 F36 F40 F44 F48 F52 F56 FRAW FNOW FFAIL FLAST.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC) as (N1 & N2 & N3 & N4 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
assert (KIN : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] -> YK11.getr regsF r = YK11.getr regs r) by exact KR.
apply (cf_close B MT XL RLO RHI cx ly' S' W regs mem md Bw0 B1 regsF memF mdF LAWS HB HC HFR HSP HFSH HIO HMT HW0 HSC
  HJF).
- intros r Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; apply KIN; cbn [In];
    repeat (first [left; apply bv_eq; reflexivity | right]).
- apply KIN. cbn [In]. repeat (first [left; apply bv_eq; reflexivity | right]).
- apply KIN. cbn [In]. repeat (first [left; apply bv_eq; reflexivity | right]).
- rewrite (cf_cursor (l_pl cx)). cbn [TOP.fi_off]. exact R25.
- rewrite (cf_cursor (l_pl cx)). cbn [TOP.fi_n]. exact R23.
- etransitivity; [apply KIN; cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]) | exact R22].
- etransitivity; [apply KIN; cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]) | exact R21].
- etransitivity; [apply KIN; cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]) | exact R20].
- exact R27.
- exact KV.
- exact GP.
- apply cf_rdw; [exact Q104 | rewrite P8; lia].
- apply cf_rdw; [exact Q152 | rewrite P9; lia].
- apply cf_rdw; [exact Q184 | rewrite P10; lia].
- apply cf_rdw; [exact Q40 | rewrite P11; lia].
- apply (cf_wfin (l_pl cx) W mem memF B1 HTW).
  + intros j Hj. exact (cf_vb (w_H W) memF _ 4 _ F24 j Hj).
  + intros j Hj. exact (cf_vb (w_H W) memF _ 4 _ F28 j Hj).
  + intros j Hj. exact (cf_vb (w_H W) memF _ 4 _ F32 j Hj).
  + intros j Hj. exact (cf_vb (w_H W) memF _ 4 _ F36 j Hj).
  + intros j Hj. exact (cf_vb (w_H W) memF _ 4 _ F40 j Hj).
  + intros j Hj. exact (cf_vb (w_H W) memF _ 4 _ F44 j Hj).
  + intros j Hj. exact (cf_vb (w_H W) memF _ 4 _ F48 j Hj).
  + intros j Hj. exact (cf_vb (w_H W) memF _ 4 _ F52 j Hj).
  + intros j Hj. exact (cf_vb (w_H W) memF _ 4 _ F56 j Hj).
  + intros j Hj. replace (TB_g_raw + 0) with (transportb_hi 8 + 1652) by (rewrite P8; reflexivity).
    exact (cf_vb (w_H W) memF _ 4 _ FRAW j Hj).
  + intros j Hj. replace (TB_g_now + 0) with (transportb_hi 9 + 1676) by (rewrite P9; reflexivity).
    exact (cf_vb (w_H W) memF _ 8 _ FNOW j Hj).
  + intros j Hj. replace (TB_g_fail_next + 0) with (transportb_hi 10 + 1656) by (rewrite P10; reflexivity).
    exact (cf_vb (w_H W) memF _ 1 _ FFAIL j Hj).
  + intros j Hj. replace (TB_g_last_counter + 0) with (transportb_hi 11 + 1668) by (rewrite P11; reflexivity).
    exact (cf_vb (w_H W) memF _ 4 _ FLAST j Hj).
  + intros a Ha Hg. pose proof Ha as (o & b & n & Hin & Hx).
    assert (HaG : inG TG.G_HARNESS_B a).
    { unfold inG. apply Exists_exists. exists (b, n).
      split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia]. }
    pose proof (transportb_segs_low a (trans_g_img a HaG)) as Hl. unfold kLowMemEnd in Hl.
    apply KV; [lia|]. intros [C|[C|[C|[C|[C|C]]]]]; [exact (Hg C) | unfold ESTACK in C; lia..].
Qed.

(* The statement of run C at the exits whose bytes left satisfy P. *)
Definition cf_Cstmt (P : Z -> Prop) : Prop :=
  forall cx W c, @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
    lc_st_cfgc B MT cx W c -> P (cf_n (l_pl cx)) -> SRr segs W c (lc_st_scal B MT cx).

(* Run C, one lemma per exit: the cursor's bytes left, 0 .. 13, then 14 bytes and 15 or more. *)
Lemma cf_C0 : cf_Cstmt (fun n => n = 0).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seat0 B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC HFR HCUR R24 R21 HN) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

Lemma cf_C1 : cf_Cstmt (fun n => n = 1).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seatK B MT XL RLO RHI cx ly' S' W regs mem md 1 2 0 LAWS HB HC HFR HCUR R24 R21 ltac:(lia) HN
  eq_refl ltac:(intros; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

Lemma cf_C2 : cf_Cstmt (fun n => n = 2).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seatK B MT XL RLO RHI cx ly' S' W regs mem md 2 3 0 LAWS HB HC HFR HCUR R24 R21 ltac:(lia) HN
  eq_refl ltac:(intros; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

Lemma cf_C3 : cf_Cstmt (fun n => n = 3).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seatK B MT XL RLO RHI cx ly' S' W regs mem md 3 4 0 LAWS HB HC HFR HCUR R24 R21 ltac:(lia) HN
  eq_refl ltac:(intros; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

Lemma cf_C4 : cf_Cstmt (fun n => n = 4).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seatK B MT XL RLO RHI cx ly' S' W regs mem md 4 5 0 LAWS HB HC HFR HCUR R24 R21 ltac:(lia) HN
  eq_refl ltac:(intros; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

Lemma cf_C5 : cf_Cstmt (fun n => n = 5).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seatK B MT XL RLO RHI cx ly' S' W regs mem md 5 6 0 LAWS HB HC HFR HCUR R24 R21 ltac:(lia) HN
  eq_refl ltac:(intros; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

Lemma cf_C6 : cf_Cstmt (fun n => n = 6).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seatK B MT XL RLO RHI cx ly' S' W regs mem md 6 7 0 LAWS HB HC HFR HCUR R24 R21 ltac:(lia) HN
  eq_refl ltac:(intros; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

Lemma cf_C7 : cf_Cstmt (fun n => n = 7).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seatK B MT XL RLO RHI cx ly' S' W regs mem md 7 0 0 LAWS HB HC HFR HCUR R24 R21 ltac:(lia) HN
  eq_refl ltac:(intros; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

Lemma cf_C8 : cf_Cstmt (fun n => n = 8).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seatK B MT XL RLO RHI cx ly' S' W regs mem md 8 0 1 LAWS HB HC HFR HCUR R24 R21 ltac:(lia) HN
  eq_refl ltac:(intros; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

Lemma cf_C9 : cf_Cstmt (fun n => n = 9).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seatK B MT XL RLO RHI cx ly' S' W regs mem md 9 0 2 LAWS HB HC HFR HCUR R24 R21 ltac:(lia) HN
  eq_refl ltac:(intros; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

Lemma cf_C10 : cf_Cstmt (fun n => n = 10).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seatK B MT XL RLO RHI cx ly' S' W regs mem md 10 0 3 LAWS HB HC HFR HCUR R24 R21 ltac:(lia) HN
  eq_refl ltac:(intros; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

Lemma cf_C11 : cf_Cstmt (fun n => n = 11).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seatK B MT XL RLO RHI cx ly' S' W regs mem md 11 0 4 LAWS HB HC HFR HCUR R24 R21 ltac:(lia) HN
  eq_refl ltac:(intros; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

Lemma cf_C12 : cf_Cstmt (fun n => n = 12).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seatK B MT XL RLO RHI cx ly' S' W regs mem md 12 0 5 LAWS HB HC HFR HCUR R24 R21 ltac:(lia) HN
  eq_refl ltac:(intros; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

Lemma cf_C13 : cf_Cstmt (fun n => n = 13).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seatK B MT XL RLO RHI cx ly' S' W regs mem md 13 0 6 LAWS HB HC HFR HCUR R24 R21 ltac:(lia) HN
  eq_refl ltac:(intros; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

Lemma cf_C14 : cf_Cstmt (fun n => n = 14).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seatN B MT XL RLO RHI cx ly' S' W regs mem md 7 LAWS HB HC HFR HCUR R24 R21 ltac:(lia)
  ltac:(rewrite HN; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

Lemma cf_C15 : cf_Cstmt (fun n => 15 <= n).
Proof.
unfold cf_Cstmt; intros cx W c HP HB HCC HN; cbv beta in HN.
destruct HCC as (ly' & S' & regs & mem & md & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMT & HCUR & R24 & R21
  & R20 & R22 & HW0 & HSC & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (proj1 HC) as HJ.
destruct (cf_num B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & N10 & N11 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof lf_spill_pages as (P8 & P9 & P10 & P11 & _ & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
pose proof HC as (_ & _ & _ & _ & R2 & _ & R9 & _).
pose proof HCUR as (R19 & R23).
change (TOP.fi_off (lc_c1 (l_pl cx))) with (cf_o (l_pl cx)) in R19.
change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in R23.
try (destruct (cf_blk B MT XL RLO RHI cx ly' S' W regs mem md LAWS HB HC ltac:(lia)) as (Ho & Hln & Hp4 & _ & Hpc & _);
     rewrite Ho in R19).
pose proof (cf_seatN B MT XL RLO RHI cx ly' S' W regs mem md 0 LAWS HB HC HFR HCUR R24 R21 ltac:(lia)
  ltac:(destruct (Z.leb_spec 16 (cf_n (l_pl cx) + 1)); lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := cf_E regs (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8) (SHADOW_OFF + (l_p cx + 1) / 8 + 1)) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, cf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
try (assert (U19 : bv_unsigned (ew E 19) = l_p cx + 1)
       by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; apply unsigned_lit_small; lia)).
assert (U21 : bv_unsigned (ew E 21) = TB_g_cfg)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U23 : bv_unsigned (ew E 23) = cf_n (l_pl cx))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small;
      pose proof (cf_c1_n (l_pl cx)); destruct (cf_on (l_pl cx)) as [(_ & ? & _)|(_ & ? & _)]; lia).
assert (U24 : bv_unsigned (ew E 24) = lc_flags (l_pl cx))
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U408 : bv_unsigned (ew E 408) = transportb_hi 8)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U409 : bv_unsigned (ew E 409) = transportb_hi 9)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U410 : bv_unsigned (ew E 410) = transportb_hi 10)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U411 : bv_unsigned (ew E 411) = transportb_hi 11)
  by (unfold E, cf_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (UB : forall j, (j < 14)%nat -> bv_unsigned (ew E (32 + j)) = cf_v (l_pl cx) (Z.of_nat j))
  by (intros j Hj; unfold E, cf_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra;
      rewrite (cf_ex_b _ _ _ j (cf_bs_len _) Hj), (cf_bs_nth _ j Hj); apply unsigned_lit_small;
      pose proof (cf_v_rng (l_pl cx) (Z.of_nat j)); lia).
assert (HA : env_agree 32 (Ereg regs (cf_ex (cf_bs (l_pl cx)) (SHADOW_OFF + (l_p cx + 1) / 8)
  (SHADOW_OFF + (l_p cx + 1) / 8 + 1))) E)
  by (split; [intros n Hn; unfold E, cf_E; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
             | reflexivity]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, cf_E; apply Eimg_env).
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg; rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SCAL.
{ cf_awr U9 U21 U408 U409 U410 U411 P8 P9 P10 P11. }
set (mdF := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdF; clear mat.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wr cx) HFr); [|exact Ha | exact Hn];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; cf_win U9 U21 U408 U409 U410 U411 P8 P9 P10 P11 |]);
      destruct Hin).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) E _ _ regs _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] HS HA ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
cf_reg HS (25%bv : bv 5) Q25; cf_reg HS (23%bv : bv 5) Q23; cf_reg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) E _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
pmkst HS.
assert (EPS : Z_to_bv 64 (BASE + LO_SCAL) = w64 (transportb_text + LO_SCAL))
  by (unfold w64; f_equal; vm_compute; reflexivity).
apply SRr_ret; change (Z_to_bv 64 (BASE + 1200)) with (Z_to_bv 64 (BASE + LO_SCAL)); rewrite EPS.
apply (cf_fin cx ly' S' W regs mem md Bw0 B1 (ms_regs ms) (ms_mem ms) mdF LAWS HB HC HFR HSP HFSH HIO HMT R22 R21
  R20 HW0 HSC HTW HJ KR);
[ rewrite Q25; first
    [ rewrite (cf_dn_off E 19 _ _ U19); unfold w64; f_equal; lia
    | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19;
      unfold w64; f_equal; lia ]
| rewrite Q23; first [ rewrite HN; reflexivity | rewrite (cf_dn_off E 23 _ _ U23); unfold w64; f_equal; lia ]
| rewrite Q27; reflexivity
| exact KV
| exact GP
| cf_rbk RG2 104 U9 | cf_rbk RG3 152 U9 | cf_rbk RG4 184 U9 | cf_rbk RG1 40 U9
| cf_rbk RG0 24 U21 | cf_rbk RG0 28 U21 | cf_rbk RG0 32 U21 | cf_rbk RG0 36 U21 | cf_rbk RG0 40 U21
| cf_rbk RG0 44 U21 | cf_rbk RG0 48 U21 | cf_rbk RG0 52 U21 | cf_rbk RG0 56 U21
| cf_rbk RG5 1652 U408 | cf_rbk RG6 1676 U409 | cf_rbk RG7 1656 U410 | cf_rbk RG8 1668 U411 ].
Qed.

(* Run C: the case split on its exit. *)
Lemma cf_runC : cf_Cstmt (fun _ => True).
Proof.
intros cx W c HP HB HCC _. pose proof (cf_c1_n (l_pl cx)) as H0. change (TOP.fi_n (lc_c1 (l_pl cx))) with (cf_n (l_pl cx)) in H0.
assert (HK : cf_n (l_pl cx) = 0 \/ cf_n (l_pl cx) = 1 \/ cf_n (l_pl cx) = 2 \/ cf_n (l_pl cx) = 3 \/
  cf_n (l_pl cx) = 4 \/ cf_n (l_pl cx) = 5 \/ cf_n (l_pl cx) = 6 \/ cf_n (l_pl cx) = 7 \/ cf_n (l_pl cx) = 8 \/
  cf_n (l_pl cx) = 9 \/ cf_n (l_pl cx) = 10 \/ cf_n (l_pl cx) = 11 \/ cf_n (l_pl cx) = 12 \/
  cf_n (l_pl cx) = 13 \/ cf_n (l_pl cx) = 14 \/ 15 <= cf_n (l_pl cx)) by lia.
destruct HK as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]].
- exact (cf_C0 cx W c HP HB HCC H).
- exact (cf_C1 cx W c HP HB HCC H).
- exact (cf_C2 cx W c HP HB HCC H).
- exact (cf_C3 cx W c HP HB HCC H).
- exact (cf_C4 cx W c HP HB HCC H).
- exact (cf_C5 cx W c HP HB HCC H).
- exact (cf_C6 cx W c HP HB HCC H).
- exact (cf_C7 cx W c HP HB HCC H).
- exact (cf_C8 cx W c HP HB HCC H).
- exact (cf_C9 cx W c HP HB HCC H).
- exact (cf_C10 cx W c HP HB HCC H).
- exact (cf_C11 cx W c HP HB HCC H).
- exact (cf_C12 cx W c HP HB HCC H).
- exact (cf_C13 cx W c HP HB HCC H).
- exact (cf_C14 cx W c HP HB HCC H).
- exact (cf_C15 cx W c HP HB HCC H).
Qed.
End runc.

(* ------------------------------------------------------------------ *)
(* 7. The segment                                                      *)
(* ------------------------------------------------------------------ *)

Section ok. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

(* The stage, +0x358 .. +0x39c (the two __asan_memcpy calls and the three flag bits), as the cut file states it. *)
Hypothesis STAGE : @lc_cfg_stage_stmt rc B MT XL RLO RHI.

Lemma lc_cfg_ok (K1 : lc_rom_view_stmt B MT XL RLO RHI) (K2 : lc_src_ro_stmt B MT XL RLO RHI) :
  lc_cfg_stmt B MT XL RLO RHI.
Proof.
intros HP cx W' c' HB HD.
eapply SRr_bind; [exact (STAGE K1 K2 HP cx W' c' HB HD)|].
intros W2 c2 _ HC2. exact (cf_runC B MT XL RLO RHI cx W2 c2 HP HB HC2 I).
Qed.
End ok.
