(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the interface of the image-A walk of reac-repacer/fuzz_uci's LLVMFuzzerTestOneInput, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_segs.v (the context record, a state predicate per cut point, one statement per segment, the composition by SRr_bind / SRr_mono and the srealizes entry of cgif's lib/A/ACfh.v): the cut points, the registers and the frame are fuzz_uci.asan's, the slot is the core's lib/A/ACfn.v tfib_lib_contract_x_all, and the loop of five turns is composed by an induction on the turn. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/LLVMFuzzerTestOneInput_segs.v, with its module paths and module names changed; 937 of its 976 lines of code are new or changed and 163 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/LLVMFuzzerTestOneInput_segs.v, with its module paths and module names changed; 7155 of its 7226 lines of code are new or changed and 905 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_cfg: proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's image-A walk).
   lc_cfg_ok : lc_rom_view_stmt -> lc_src_ro_stmt -> lc_cfg_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the
   segment CFG of fuzz_transport.asan's LLVMFuzzerTestOneInput, from the return of diginet_session_config_default
   (+0x1cc, lc_st_cfgd) to the point before the memset of M (+0x318, lc_st_scal). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YO09 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG AE2y.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_config_default_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require SlostHead.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TSess0 TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require InitOk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module IOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.InitOk.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
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

(* lc_pro_scal at the bytes cf_b of the cursor after the flags byte. *)
Definition cf_world (D : list byte) (B1 : list byte) : list byte :=
  let flags := lc_flags D in
  let o := TOP.fi_off (lc_c1 D) in
  let n := TOP.fi_n (lc_c1 D) in
  let B2 := TW.set_Cfg_host_mac B1 TC.HOST in
  let B3 := TW.set_Cfg_auto_wake B2 (Z.land flags 1) in
  let B4 := TW.set_Cfg_sum_mode B3
              (if Z.land flags 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) in
  let B5 := TW.set_Cfg_desk_mac_set B4 (Z.land (Z.shiftr flags 2) 1) in
  let B6 := TW.set_Cfg_desk_mac B5 TC.DESK in
  let B7 := TW.set_Cfg_max_retries B6 (cf_b D o n 0 mod 8) in
  let B8 := TW.set_Cfg_ack_timeout_ms B7 ((1 + cf_b D o n 1) mod 2^32) in
  let B9 := TW.set_Cfg_keepalive_ms B8 ((1 + (cf_b D o n 2 + 256 * cf_b D o n 3)) mod 2^32) in
  let B10 := TW.set_Cfg_backoff_ms B9 (cf_b D o n 4) in
  let B11 := TW.set_Cfg_offline_ms B10 ((1 + (cf_b D o n 5 + 256 * cf_b D o n 6)) mod 2^32) in
  let B12 := TW.set_Cfg_wake_timeout_ms B11 ((1 + (cf_b D o n 7 + 256 * cf_b D o n 8)) mod 2^32) in
  let B13 := TW.set_Cfg_display_gap_us B12 (cf_b D o n 9 + 256 * cf_b D o n 10) in
  let B14 := TW.set_Cfg_max_cmds B13 ((1 + cf_b D o n 11 mod 255) mod 2^32) in
  let B15 := TW.set_Cfg_max_body B14
               ((DSpec.SPEC_CMD_MAX + (cf_b D o n 12 + 256 * cf_b D o n 13)
                  mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2^32) in
  let B16 := TW.set_g_raw B15 (Z.land (Z.shiftr flags 3) 1) in
  let B17 := TW.set_g_now B16 1000000 in
  let B18 := TW.set_g_fail_next B17 0 in
  TW.set_g_last_counter B18 0.

Lemma cf_scal_eq : forall D B1, lc_pro_scal D B1 = cf_world D B1.
Proof.
intros D B1. pose proof (cf_c1_n D) as Hn0.
unfold lc_pro_scal, cf_world, lc_flags, lc_c1 in *. cbv zeta. revert Hn0.
destruct (TOP.fuzz_u8_m D (TOP.fuzz_in_m (Z.of_nat (length D)))) as [[o n] flags]. cbn [fst snd TOP.fi_off TOP.fi_n]. intros Hn0.
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
  IOK.prologue_cursor D =
  TOP.FuzzIn (TOP.fi_off (lc_c1 D) + Z.min (TOP.fi_n (lc_c1 D)) 14)
             (TOP.fi_n (lc_c1 D) - Z.min (TOP.fi_n (lc_c1 D)) 14).
Proof.
intros D. pose proof (cf_c1_n D) as Hn0.
unfold IOK.prologue_cursor, lc_c1 in *. cbv zeta. revert Hn0.
destruct (TOP.fuzz_u8_m D (TOP.fuzz_in_m (Z.of_nat (length D)))) as [[o n] flags]. cbn [fst snd TOP.fi_off TOP.fi_n]. intros Hn0.
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

(* The code's values of the derived fields, decided over every byte value. *)
(* max_body: `mul a0, a1, 0x59b7; srli a0, a0, 25; mul a0, a0, 1461; subw a1, a1, a0` is v mod 1461 for v < 2 ^ 16. *)
Lemma cf_mod1461_chk :
  tw_allz (fun v => Z.eqb (v - (v * 22967) / 2 ^ 25 * 1461) (v mod 1461)) 0 (Z.to_nat 65536) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cf_mod1461 : forall v, 0 <= v < 65536 -> v - (v * 22967) / 2 ^ 25 * 1461 = v mod 1461.
Proof.
intros v Hv. apply Z.eqb_eq. exact (tw_allz_ok _ (Z.to_nat 65536) 0 cf_mod1461_chk v ltac:(rewrite Z2Nat.id by lia; lia)).
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The world across the segment                                     *)
(* ------------------------------------------------------------------ *)

(* The bytes written so far, as a list of (base, length) ranges, and the reader that is the segment's last memory on
   them and the cut's memory elsewhere. Each store of the walk extends the list by its own range, so the kept side of
   TWorldG.v tw_write / tw_fill holds by the list's own shape. *)
Definition cf_in (l : list (Z * Z)) (a : Z) : bool :=
  existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l.
Definition cf_rdp (l : list (Z * Z)) (rd' rd : Z -> option Z) : Z -> option Z :=
  fun a => if cf_in l a then rd' a else rd a.

Lemma cf_rdp_nil : forall rd' rd, cf_rdp [] rd' rd = rd.
Proof. intros rd' rd. apply functional_extensionality. intros a. reflexivity. Qed.

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
  In (o, b, n) TMAP_A -> 0 <= k -> k + Z.of_nat m <= n ->
  tw_at TMAP_A (cf_rdp l rd' rd) Bw ->
  (forall j, (j < m)%nat -> rd' (b + k + Z.of_nat j) = Some (YO0f.le_byte v m j)) ->
  tw_at TMAP_A (cf_rdp ((b + k, Z.of_nat m) :: l) rd' rd) (TW.upd Bw (o + k) (TW.put m v)).
Proof.
intros l rd rd' Bw o b n k m v Hin Hk Hkm Hat Hv.
apply (tw_write TMAP_A (cf_rdp l rd' rd) _ Bw o b n k m v TMAP_A_ok Hat Hin Hk Hkm).
- intros j Hj. pose proof (inj_lt j m Hj) as Hjz. pose proof (Nat2Z.is_nonneg j) as Hj0.
  rewrite (cf_rdp_hd (b + k) (Z.of_nat m) l rd' rd (b + k + Z.of_nat j) ltac:(lia)). exact (Hv j Hj).
- intros x Hx Hn. exact (cf_rdp_tl (b + k) (Z.of_nat m) l rd' rd x Hn).
Qed.

(* One span filled with the byte list src at offset k of the row (o, b, n): the __asan_memcpy post's form. *)
Lemma cf_fstep : forall (l : list (Z * Z)) (rd rd' : Z -> option Z) Bw o b n k (src : list byte),
  In (o, b, n) TMAP_A -> 0 <= k -> k + Z.of_nat (length src) <= n ->
  tw_at TMAP_A (cf_rdp l rd' rd) Bw ->
  (forall i, 0 <= i < Z.of_nat (length src) ->
     rd' (b + k + i) = Some (bv_unsigned (nth (Z.to_nat i) src (Z_to_bv 8 0)))) ->
  tw_at TMAP_A (cf_rdp ((b + k, Z.of_nat (length src)) :: l) rd' rd) (TW.upd Bw (o + k) src).
Proof.
intros l rd rd' Bw o b n k src Hin Hk Hkm Hat Hv.
apply (tw_fill TMAP_A (cf_rdp l rd' rd) _ Bw o b n k src TMAP_A_ok Hat Hin Hk Hkm).
- intros i Hi. rewrite (cf_rdp_hd (b + k) (Z.of_nat (length src)) l rd' rd (b + k + i) ltac:(lia)).
  exact (Hv i Hi).
- intros x Hx Hn. exact (cf_rdp_tl (b + k) (Z.of_nat (length src)) l rd' rd x Hn).
Qed.

(* Once every written range is in the list, the patched reader is the last memory's. *)
Lemma cf_wclose : forall l (rd rd' : Z -> option Z) Bw,
  tw_at TMAP_A (cf_rdp l rd' rd) Bw ->
  (forall x, tw_in TMAP_A x -> cf_in l x = false -> rd' x = rd x) ->
  tw_at TMAP_A rd' Bw.
Proof.
intros l rd rd' Bw Hat Hk. apply (tw_kept TMAP_A (cf_rdp l rd' rd) rd' Bw Hat).
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

(* ------------------------------------------------------------------ *)
(* 3. The symbolic states of the runs                                  *)
(* ------------------------------------------------------------------ *)

(* The offsets of the cuts inside the segment: the two __asan_memcpy returns and the point after the first config
   byte's checked load. *)
Definition CF_RC1 : Z := 0x1e0.
Definition CF_RC2 : Z := 0x214.
Definition CF_SC : Z := 0x22c.
Definition cf_Bx : sv := SOff 26 0.

(* g_cfg's bytes the runs write ([12, 24) before the second memcpy, [24, 60) after it), the four spill slots the
   segment stores (48, 120, 160, 176 of s1) and the four scalar globals, each at its auipc page (atoms A_HI 8 .. 11). *)
Definition cf_rg_cfgb : YP09.region := YP09.mkRegion (Some 21%nat) 12 24 12 24 [].
Definition cf_rg_cfg : YP09.region := YP09.mkRegion (Some 21%nat) 24 60 24 60 [].
Definition cf_rg_sp48 : YP09.region := YP09.mkRegion (Some 9%nat) 48 56 48 56 [].
Definition cf_rg_sp120 : YP09.region := YP09.mkRegion (Some 9%nat) 120 128 120 128 [].
Definition cf_rg_sp160 : YP09.region := YP09.mkRegion (Some 9%nat) 160 168 160 168 [].
Definition cf_rg_sp176 : YP09.region := YP09.mkRegion (Some 9%nat) 176 184 176 184 [].
Definition cf_rg_raw : YP09.region := YP09.mkRegion (Some (A_HI 8)) (-1076) (-1072) (-1076) (-1072) [].
Definition cf_rg_now : YP09.region := YP09.mkRegion (Some (A_HI 9)) (-1052) (-1044) (-1052) (-1044) [].
Definition cf_rg_fail : YP09.region := YP09.mkRegion (Some (A_HI 10)) (-1076) (-1075) (-1076) (-1075) [].
Definition cf_rg_last : YP09.region := YP09.mkRegion (Some (A_HI 11)) (-1064) (-1060) (-1064) (-1060) [].
(* The k config bytes at the cursor (atoms 32 .. 31 + k), read only. *)
Definition cf_rg_in (k : nat) : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0 (Z.of_nat k) 0 0
    (map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (32 + j) 0))) (seq 0 k)).
(* The shadow byte of the cursor, named by an alias fact (the port of seg_hdr.v lh_rg_sp, 50e228257540:198). *)
Definition cf_rg_sh : YP09.region :=
  YP09.mkRegion (Some 46%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 47 0))].

Definition cf_atoms (k : nat) : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF 4096 140737479966720 0); (21%nat, mkAF TA_g_cfg TA_g_cfg 0);
   (23%nat, mkAF 0 255 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (A_HI 8, mkAF (transport_hi 8) (transport_hi 8) 0); (A_HI 9, mkAF (transport_hi 9) (transport_hi 9) 0);
   (A_HI 10, mkAF (transport_hi 10) (transport_hi 10) 0); (A_HI 11, mkAF (transport_hi 11) (transport_hi 11) 0)]
  ++ map (fun j => ((32 + j)%nat, mkAF 0 255 0)) (seq 0 k).
Definition cf_wregs : smem :=
  [cf_rg_cfg; cf_rg_sp48; cf_rg_sp120; cf_rg_sp160; cf_rg_sp176; cf_rg_raw; cf_rg_now; cf_rg_fail; cf_rg_last].
Definition cf_SH (k : nat) : list shent := [mkSHE 19 0 (Z.of_nat k)].

(* The seat of the run of the empty cursor (+0x214 with s11 = 0, straight to +0x318): no byte is read, so the
   cursor's atom carries no fact and the input has no region. *)
Definition cf_atoms0 : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (21%nat, mkAF TA_g_cfg TA_g_cfg 0); (23%nat, mkAF 0 255 0);
   (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (A_HI 8, mkAF (transport_hi 8) (transport_hi 8) 0); (A_HI 9, mkAF (transport_hi 9) (transport_hi 9) 0);
   (A_HI 10, mkAF (transport_hi 10) (transport_hi 10) 0); (A_HI 11, mkAF (transport_hi 11) (transport_hi 11) 0)].
Definition cf_ss0 : sstate :=
  mkSS CF_RC2 (sr_set sr_atoms (Z_to_bv 5 27) (SLit 0)) cf_wregs None (mkFacts cf_atoms0 [] []).
(* The seat of the first config byte's checked load (+0x214 .. +0x22c), any cursor with a byte left. *)
Definition cf_ssb : sstate :=
  mkSS CF_RC2 sr_atoms [cf_rg_sh] None
    (mkFacts [(19%nat, mkAF 4096 140737479966720 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
              (27%nat, mkAF 1 (2 ^ 26) 0); (46%nat, mkAF SHADOW_OFF (2 ^ 46) 0); (47%nat, mkAF 0 7 0)] []
       [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 26 0), SOff 46 0)]).
(* The seat of the run from +0x22c with k bytes left at the cursor (k <= 13: s11 pinned; k = 14: s11 >= 14). *)
Definition cf_ssp (k : nat) : sstate :=
  mkSS CF_SC (sr_set sr_atoms (Z_to_bv 5 27) (SLit (Z.of_nat k))) (cf_rg_in k :: cf_wregs) None
    (mkFacts (cf_atoms k) [] []).
Definition cf_ssw : sstate :=
  mkSS CF_SC sr_atoms (cf_rg_in 14 :: cf_wregs) None
    (mkFacts ((27%nat, mkAF 14 (2 ^ 26) 0) :: cf_atoms 14) [] []).

(* ------------------------------------------------------------------ *)
(* 4. The core's facts other than its journal                          *)
(* ------------------------------------------------------------------ *)

Section cfg. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The bytes the segment writes: g_cfg's 60, the four scalar globals, the stack window of the two __asan_memcpy
   calls and the four spill slots the prologue stores here (48, 120, 160, 176 of s1). *)
Definition cf_wr (cx : lcx) (a : Z) : Prop :=
  (TA_g_cfg <= a < TA_g_cfg + 60) \/ (TA_g_raw <= a < TA_g_raw + 4) \/ (TA_g_now <= a < TA_g_now + 8) \/
  (TA_g_fail_next <= a < TA_g_fail_next + 1) \/ (TA_g_last_counter <= a < TA_g_last_counter + 4) \/
  (lc_sp1 cx - ESTACK <= a < lc_sp1 cx) \/
  (lc_sp1 cx + 48 <= a < lc_sp1 cx + 56) \/ (lc_sp1 cx + 120 <= a < lc_sp1 cx + 128) \/
  (lc_sp1 cx + 160 <= a < lc_sp1 cx + 168) \/ (lc_sp1 cx + 176 <= a < lc_sp1 cx + 184).

(* The bytes a run of the config bytes writes (+0x214 / +0x22c .. +0x318): g_cfg's tail, the four scalar globals
   and the four spill slots. *)
Definition cf_wrun (cx : lcx) (a : Z) : Prop :=
  (TA_g_cfg + 24 <= a < TA_g_cfg + 60) \/ (TA_g_raw <= a < TA_g_raw + 4) \/ (TA_g_now <= a < TA_g_now + 8) \/
  (TA_g_fail_next <= a < TA_g_fail_next + 1) \/ (TA_g_last_counter <= a < TA_g_last_counter + 4) \/
  (lc_sp1 cx + 48 <= a < lc_sp1 cx + 56) \/ (lc_sp1 cx + 120 <= a < lc_sp1 cx + 128) \/
  (lc_sp1 cx + 160 <= a < lc_sp1 cx + 168) \/ (lc_sp1 cx + 176 <= a < lc_sp1 cx + 184).

(* lc_core without its journal: the walk keeps the journal it is given and carries the rest (the port of
   lib/A/Prog/LLVMFuzzerTestOneInput_seg_hdr.v lh_rest, 50e228257540:506). *)
Definition cf_rest (cx : lcx) (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) : Prop :=
  frames S' = [(LF_CID, l_fpos cx)] /\ ly_F ly' = ly_F (l_ly cx) /\
  Permutation (ablocks B ly' S') (ablocks B (l_ly cx) (l_S cx)) /\
  YK11.getr regs' 2 = w64 (lc_sp1 cx) /\ YK11.getr regs' 8 = w64 (lc_sp0 cx) /\ YK11.getr regs' 9 = w64 (lc_sp1 cx) /\
  YK11.getr regs' 3 = w64 (as_gp B) /\ YK11.getr regs' 4 = w64 (as_tp B) /\
  lc_sp0 cx - 336 <= lc_sp1 cx <= lc_sp0 cx - LF_FRAME /\ lc_sp1 cx mod 32 = 0 /\
  lc_saved cx (aview segs (w_H W') mem') /\
  4096 <= lc_F cx /\ lc_F cx mod 64 = 0 /\ lc_F cx + LF_FBYTES <= alloc_ceiling /\
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES -> apresent (w_H W') mem' a) /\
  rdword (aview segs (w_H W') mem') (lc_F cx + LF_FBYTES - 8) = Some (lc_FL cx) /\
  lc_input cx W' mem'.

Lemma cf_rest_of : forall cx ly' S' (W' : world segs) regs' mem' md' e,
  @lc_core rc B cx ly' S' W' regs' mem' md' e -> cf_rest cx ly' S' W' regs' mem'.
Proof. intros cx ly' S' W' regs' mem' md' e H. exact (proj2 H). Qed.

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

(* The bytes the core, the kept spill slots, the frame's shadow and io read lie outside cf_wr; a payload byte of the
   world lies in G's hull and off the stack. *)
Lemma cf_apart : forall cx ly' S' (W' : world segs) regs' mem' md' e,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W' regs' mem' md' e ->
  (forall a, (lc_sp0 cx - 104 <= a < lc_sp0 cx) \/ (lc_F cx <= a < lc_F cx + 256) \/
             (0 < l_n cx /\ l_p cx <= a < l_p cx + l_n cx) \/ (lc_SH cx <= a < lc_SH cx + 32) \/
             (lc_sp1 cx + 128 <= a < lc_sp1 cx + 136) \/ (lc_sp1 cx + 152 <= a < lc_sp1 cx + 160) ->
     ~ cf_wr cx a /\ 0 <= a < 2 ^ 64) /\
  (forall x, tw_in TMAP_A x -> TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI /\ 0 <= x < 2 ^ 64).
Proof.
intros cx ly' S' W' regs' mem' md' e LAWS HB HC.
destruct (cf_num cx ly' S' W' regs' mem' md' e LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
assert (HF8 : 0 <= lc_F cx / 8 < 2 ^ 44)
  by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
assert (HGl : forall x, TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI -> 0 <= x < 6500000)
  by (intros x Hx; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hx; lia).
split.
{ intros a Ha. unfold cf_wr, lc_SH, SHADOW_OFF, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter,
    ESTACK in *.
  destruct Ha as [Ha | [Ha | [[Hn0 Ha] | [Ha | [Ha | Ha]]]]].
  - split; [intros [C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]; lia | lia].
  - split; [|lia]. intros [C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]; try lia.
    all: apply (N9 a Ha); apply trans_g_img; unfold W_journalG.inG; apply Exists_exists.
    + exists (TA_g_cfg, TW.SZ_g_cfg).
      split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_cfg) | unfold in_zr, TA_g_cfg, TW.SZ_g_cfg; cbn [fst snd]; lia].
    + exists (TA_g_raw, TW.SZ_g_raw).
      split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_raw) | unfold in_zr, TA_g_raw, TW.SZ_g_raw; cbn [fst snd]; lia].
    + exists (TA_g_now, TW.SZ_g_now).
      split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_now) | unfold in_zr, TA_g_now, TW.SZ_g_now; cbn [fst snd]; lia].
    + exists (TA_g_fail_next, 1).
      split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_fail_next) | unfold in_zr, TA_g_fail_next; cbn [fst snd]; lia].
    + exists (TA_g_last_counter, TW.SZ_g_last_counter).
      split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_last_counter)
             | unfold in_zr, TA_g_last_counter, TW.SZ_g_last_counter; cbn [fst snd]; lia].
  - destruct (N12 Hn0) as (_ & Gp4 & Gpc & _ & _ & Gpimg).
    split; [|lia]. intros [C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]; try lia.
    all: apply (Gpimg a Ha); apply trans_g_img; unfold W_journalG.inG; apply Exists_exists.
    + exists (TA_g_cfg, TW.SZ_g_cfg).
      split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_cfg) | unfold in_zr, TA_g_cfg, TW.SZ_g_cfg; cbn [fst snd]; lia].
    + exists (TA_g_raw, TW.SZ_g_raw).
      split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_raw) | unfold in_zr, TA_g_raw, TW.SZ_g_raw; cbn [fst snd]; lia].
    + exists (TA_g_now, TW.SZ_g_now).
      split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_now) | unfold in_zr, TA_g_now, TW.SZ_g_now; cbn [fst snd]; lia].
    + exists (TA_g_fail_next, 1).
      split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_fail_next) | unfold in_zr, TA_g_fail_next; cbn [fst snd]; lia].
    + exists (TA_g_last_counter, TW.SZ_g_last_counter).
      split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_last_counter)
             | unfold in_zr, TA_g_last_counter, TW.SZ_g_last_counter; cbn [fst snd]; lia].
  - split; [intros [C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]; lia | lia].
  - split; [intros [C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]; lia | lia].
  - split; [intros [C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]; lia | lia]. }
intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. pose proof (HGl x Hh). lia.
Qed.

(* A run or a call that keeps every byte outside cf_wr, the registers sp, s0, s1, gp, tp and presence keeps cf_rest. *)
Lemma cf_rest_step : forall cx ly' S' (W : world segs) regs' mem' md' e regs2 mem2,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W regs' mem' md' e ->
  YK11.getr regs2 2 = YK11.getr regs' 2 -> YK11.getr regs2 8 = YK11.getr regs' 8 ->
  YK11.getr regs2 9 = YK11.getr regs' 9 -> YK11.getr regs2 3 = YK11.getr regs' 3 ->
  YK11.getr regs2 4 = YK11.getr regs' 4 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem' a) ->
  (forall a, apresent (w_H W) mem' a -> apresent (w_H W) mem2 a) ->
  cf_rest cx ly' S' W regs2 mem2.
Proof.
intros cx ly' S' W regs' mem' md' e regs2 mem2 LAWS HB HC E2 E8 E9 E3 E4 KP GP.
destruct (cf_apart cx ly' S' W regs' mem' md' e LAWS HB HC) as (AP & _).
destruct (cf_num cx ly' S' W regs' mem' md' e LAWS HB HC)
  as (N1 & N2 & _ & _ & _ & _ & _ & _ & _ & _ & Hnl & _).
destruct HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
refine (conj Hfrs (conj HlyF (conj HPERM (conj (eq_trans E2 Rsp) (conj (eq_trans E8 R8) (conj (eq_trans E9 R9)
  (conj (eq_trans E3 Rgp) (conj (eq_trans E4 Rtp) (conj Hsp1 (conj Hsp1al (conj _ (conj HF4096 (conj HFal
  (conj HFceil (conj _ (conj _ _)))))))))))))))).
- unfold lc_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros o Ho.
  assert (Hor : 8 <= fst o <= 104).
  { unfold LF_SAVED in Ho. repeat (destruct Ho as [<- | Ho]; [cbn; lia|]). destruct Ho. }
  rewrite (rdword_ext (aview segs (w_H W) mem') (aview segs (w_H W) mem2) (lc_sp0 cx - fst o))
    by (intros j Hj; destruct (AP (lc_sp0 cx - fst o + j) ltac:(left; lia)) as [Hw Hr]; exact (KP _ Hr Hw)).
  exact (HSAV o Ho).
- intros a Ha. exact (GP a (HFpres a Ha)).
- rewrite (rdword_ext (aview segs (w_H W) mem') (aview segs (w_H W) mem2) (lc_F cx + LF_FBYTES - 8))
    by (intros j Hj; unfold LF_FBYTES in *;
        destruct (AP (lc_F cx + 256 - 8 + j) ltac:(right; left; lia)) as [Hw Hr]; exact (KP _ Hr Hw)).
  exact HFL.
- destruct HIN as (HPAYg & HPAYv).
  destruct (Z_lt_le_dec 0 (l_n cx)) as [Hn0 | Hn0].
  + split.
    * apply (lc_garr8_kept (w_H W) (w_H W) mem' mem2 (l_p cx) _); [|exact HPAYg].
      intros j Hj. rewrite length_map in Hj.
      rewrite <- Hnl in Hj.
      destruct (AP (l_p cx + j) ltac:(right; right; left; split; lia)) as [Hw Hr]. exact (KP _ Hr Hw).
    * intros i Hi. destruct (AP (l_p cx + i) ltac:(right; right; left; split; lia)) as [Hw Hr].
      rewrite (KP _ Hr Hw). exact (HPAYv i Hi).
  + split.
    * assert (Hz : Z.of_nat (length (l_pl cx)) = 0) by lia.
      assert (Epl : l_pl cx = []) by (apply length_zero_iff_nil; apply Nat2Z.inj; rewrite Hz; reflexivity).
      rewrite Epl. apply garr8_nil.
    * intros i Hi. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The valuations, the shadow of g_cfg and the read-only sources    *)
(* ------------------------------------------------------------------ *)

(* The valuation of a run: the registers as atoms 0 .. 31, then the extra atoms from 32 up. *)
Definition cf_E (regs : bvmap 5 word) (ex : list word) : env := Eimg (PI := PI_transport) (Ereg regs ex).
Lemma cf_E_reg : forall regs ex n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (cf_E regs ex) n = YK11.getr regs r.
Proof. intros regs ex n r Hn. unfold cf_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma cf_E_x : forall regs ex j, (j < 200)%nat -> ew (cf_E regs ex) (32 + j) = nth j ex (Z_to_bv 64 0).
Proof. intros regs ex j Hj. unfold cf_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma cf_E_img : forall regs ex, img_env VAL A_LIM (cf_E regs ex).
Proof. intros regs ex. unfold cf_E. apply Eimg_env. Qed.
Lemma cf_E_obj : forall regs ex j, (A_TEXT <= j < A_LIM)%nat -> ew (cf_E regs ex) j = Z_to_bv 64 (VAL j).
Proof. intros regs ex j Hj. unfold cf_E. apply Eimg_img. exact Hj. Qed.
Lemma cf_u64 : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 v) = v.
Proof. intros v Hv. apply unsigned_lit_small. exact Hv. Qed.
Lemma cf_agree : forall regs ex E, env_agree 512 (cf_E regs ex) E -> env_agree 32 (Ereg regs ex) E.
Proof.
intros regs ex E [H1 H2]. split; [|rewrite H2; reflexivity].
intros n Hn. rewrite (H1 n ltac:(lia)). unfold cf_E. apply Eimg_low. unfold A_TEXT. lia.
Qed.

(* g_cfg's 60 bytes are addressable at every AR state: the shadow of its 7 whole granules is 0 and the shadow byte
   of its last granule is 4 (the port of lib/A/Prog/diginet_session_config_default.v scfg_ra, f6acfcb0c1b8:305). *)
Lemma cf_cfg_ra : forall ly S (W : world segs) mem md,
  trans_scfg_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF TA_g_cfg 60.
Proof.
intros ly S W mem md [HZ HC] HAR x Hx.
assert (EC : SCFG_C = 6156416) by reflexivity.
assert (EG : TA_g_cfg = 6156416) by reflexivity.
rewrite EG in Hx.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold shadow_of_addr.
destruct (Z_lt_le_dec x (SCFG_C + 56)) as [Hlt|Hge].
- exists 0. split; [|left; reflexivity].
  assert (Hz := decode_zshadow_rd B ly S W mem md SCFG_C (SCFG_C + 56) (8 * (x / 8)) HAR
    ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
  replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
  unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
- exists 4. split; [|right; split; lia].
  specialize (HC ly). destruct HAR as (Mm & _).
  pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mm) _ HC) as Hh.
  unfold cell_holds in Hh. cbn [c_at c_w YG0f.c_val z1 c1 aeval] in Hh.
  specialize (Hh 0%nat ltac:(lia)). cbn [Z.of_nat] in Hh. rewrite Z.add_0_r in Hh.
  change (YG0f.le_byte 4 1 0) with 4 in Hh.
  replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (SCFG_C + 56)); [exact Hh|].
  unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF.
  replace ((SCFG_C + 56) / 8) with 769559 by (rewrite EC; reflexivity). rewrite EC in *. lia.
Qed.

(* The shadow hull of a range of g_cfg is visible: its shadow bytes are g_cfg's eight (the port of
   diginet_session_config_default.v scfg_hull, f6acfcb0c1b8:331). *)
Lemma cf_cfg_hull : forall ly S (W : world segs) mem md a n,
  trans_scfg_cells B -> @AR rc segs B ly S W mem md ->
  TA_g_cfg <= a -> 0 < n -> a + n <= TA_g_cfg + 60 ->
  shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof.
intros ly S W mem md a n HSC HAR H1 Hn H2 s Hs.
pose proof (cf_cfg_ra ly S W mem md HSC HAR) as HRA.
assert (EG : TA_g_cfg = 6156416) by reflexivity. rewrite EG in H1, H2.
unfold shadow_addr, SHADOW_OFF in Hs.
assert (Ha8 : 769552 <= a / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hb8 : (a + n - 1) / 8 < 769560) by (apply Z.div_lt_upper_bound; lia).
assert (Hlo : 268527554 <= (2147450880 + a / 8) / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hhi : (2147450880 + (a + n - 1) / 8) / 8 < 268527555) by (apply Z.div_lt_upper_bound; lia).
assert (Hs2 : 2148220432 <= s < 2148220440) by lia.
assert (Hx : TA_g_cfg <= 6156416 + 8 * (s - 2148220432) < TA_g_cfg + 60) by (rewrite EG; lia).
destruct (HRA _ Hx) as (v & Hv & _).
unfold shadow_of_addr, SHADOW_OFF in Hv.
replace (2147450880 + (6156416 + 8 * (s - 2148220432)) / 8) with s in Hv; [rewrite Hv; discriminate|].
replace (6156416 + 8 * (s - 2148220432)) with ((769552 + (s - 2148220432)) * 8) by lia.
rewrite Z.div_mul by lia. lia.
Qed.

(* Every byte of g_cfg is a byte of G. *)
Lemma cf_cfg_inG : forall a, TA_g_cfg <= a < TA_g_cfg + 60 -> W_journalG.inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold W_journalG.inG. apply Exists_exists. exists (TA_g_cfg, TW.SZ_g_cfg).
split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_cfg) | unfold in_zr, TW.SZ_g_cfg; cbn [fst snd]; lia].
Qed.

(* A byte of TRANS_RO_RD read through K1 (the port of seg_head.v lh_rom_mbyte). *)
Lemma cf_rom_byte : forall (W : world segs) m a v,
  trans_rom_view_rd W m -> trans_in_ro_rd a ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 a)) = Some v ->
  aview segs (w_H W) m a = Some v.
Proof. intros W m a v HRO Ha Hv. rewrite (HRO a Ha). exact Hv. Qed.

Lemma cf_ro_host : forall a, TRANS_HOST <= a < TRANS_HOST + 6 -> trans_in_ro_rd a.
Proof.
intros a Ha. unfold trans_in_ro_rd. apply Exists_exists. exists (TRANS_HOST, 6).
split; [unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [app In]; tauto | unfold in_zr; cbn [fst snd]; exact Ha].
Qed.
Lemma cf_ro_desk : forall a, TRANS_DESK <= a < TRANS_DESK + 6 -> trans_in_ro_rd a.
Proof.
intros a Ha. unfold trans_in_ro_rd. apply Exists_exists. exists (TRANS_DESK, 6).
split; [unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [app In]; tauto | unfold in_zr; cbn [fst snd]; exact Ha].
Qed.

(* HOST's and DESK's bytes at a state where K1 holds (st.v lc_rom_bytes at the rows of lc_rom_tab). *)
Lemma cf_host_bytes : forall (W : world segs) m, trans_rom_view_rd W m ->
  forall i, 0 <= i < 6 -> aview segs (w_H W) m (TRANS_HOST + i) =
    Some (bv_unsigned (nth (Z.to_nat i) TC.HOST (Z_to_bv 8 0))).
Proof.
intros W m HRO i Hi.
refine (cf_rom_byte W m (TRANS_HOST + i) _ HRO (cf_ro_host (TRANS_HOST + i) _) _); [lia|].
replace (TRANS_HOST + i) with (TRANS_HOST + Z.of_nat (Z.to_nat i)) by lia.
apply (lc_rom_bytes TRANS_HOST TC.HOST ltac:(unfold lc_rom_tab; cbn [In]; tauto)).
assert (L : length TC.HOST = 6%nat) by reflexivity. rewrite L.
apply (proj2 (Nat2Z.inj_lt (Z.to_nat i) 6)). rewrite Z2Nat.id by lia.
replace (Z.of_nat 6) with 6 by reflexivity. lia.
Qed.
Lemma cf_desk_bytes : forall (W : world segs) m, trans_rom_view_rd W m ->
  forall i, 0 <= i < 6 -> aview segs (w_H W) m (TRANS_DESK + i) =
    Some (bv_unsigned (nth (Z.to_nat i) TC.DESK (Z_to_bv 8 0))).
Proof.
intros W m HRO i Hi.
refine (cf_rom_byte W m (TRANS_DESK + i) _ HRO (cf_ro_desk (TRANS_DESK + i) _) _); [lia|].
replace (TRANS_DESK + i) with (TRANS_DESK + Z.of_nat (Z.to_nat i)) by lia.
apply (lc_rom_bytes TRANS_DESK TC.DESK ltac:(unfold lc_rom_tab; cbn [In]; tauto)).
assert (L : length TC.DESK = 6%nat) by reflexivity. rewrite L.
apply (proj2 (Nat2Z.inj_lt (Z.to_nat i) 6)). rewrite Z2Nat.id by lia.
replace (Z.of_nat 6) with 6 by reflexivity. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 6. The running facts of the segment and its last state              *)
(* ------------------------------------------------------------------ *)

Definition cf_J (cx : lcx) (ly' : alayout) (S' : astate) (W : world segs) (mem : word -> option byte)
    (md : Model) : Prop :=
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx)
    (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W mem md 0.
Definition cf_KV (cx : lcx) (W : world segs) (mem0 mem : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a -> aview segs (w_H W) mem a = aview segs (w_H W) mem0 a.
Definition cf_GP (W : world segs) (mem0 mem : word -> option byte) : Prop :=
  forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mem a.
(* A span of the view holding a byte list, and a field of m bytes holding v. *)
Definition cf_bl (W : world segs) (mem : word -> option byte) (base : Z) (src : list byte) : Prop :=
  forall i, 0 <= i < Z.of_nat (length src) ->
    aview segs (w_H W) mem (base + i) = Some (bv_unsigned (nth (Z.to_nat i) src (Z_to_bv 8 0))).
Definition cf_bw (W : world segs) (mem : word -> option byte) (a : Z) (m : nat) (v : Z) : Prop :=
  forall j, (j < m)%nat -> aview segs (w_H W) mem (a + Z.of_nat j) = Some (YO0f.le_byte v m j).
(* The registers every point of the segment keeps. *)
Definition cf_regs (cx : lcx) (regs' : bvmap 5 word) : Prop :=
  YK11.getr regs' 2 = w64 (lc_sp1 cx) /\ YK11.getr regs' 8 = w64 (lc_sp0 cx) /\
  YK11.getr regs' 9 = w64 (lc_sp1 cx) /\ YK11.getr regs' 3 = w64 (as_gp B) /\
  YK11.getr regs' 4 = w64 (as_tp B) /\ YK11.getr regs' 18 = w64 (lc_SH cx) /\
  YK11.getr regs' 26 = w64 SHADOW_OFF /\ YK11.getr regs' 21 = w64 TA_g_cfg /\
  YK11.getr regs' 20 = w64 (lc_F cx + 176).
(* The config byte at index j of the cursor after the flags byte. *)
Definition cf_cb (D : list byte) (j : Z) : Z := cf_b D (TOP.fi_off (lc_c1 D)) (TOP.fi_n (lc_c1 D)) j.

Lemma cf_in_true : forall l x b n, In (b, n) l -> b <= x < b + n -> cf_in l x = true.
Proof.
intros l x b n Hin Hr. unfold cf_in. apply existsb_exists. exists (b, n).
split; [exact Hin|]. cbn [fst snd]. apply andb_true_intro.
split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* The 18 writes of the segment, in the model's order, give the world lc_pro_scal of config_default's world. *)
Lemma cf_world_at : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 B1 memF,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_tw W mem0 B1 -> cf_KV cx W mem0 memF ->
  cf_bl W memF (TA_g_cfg + 0) TC.HOST -> cf_bl W memF (TA_g_cfg + 6) TC.DESK ->
  cf_bw W memF (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W memF (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W memF (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_bw W memF (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32) ->
  cf_bw W memF (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32) ->
  cf_bw W memF (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8) ->
  cf_bw W memF (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4) ->
  cf_bw W memF (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32) ->
  cf_bw W memF (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32) ->
  cf_bw W memF (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10) ->
  cf_bw W memF (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32) ->
  cf_bw W memF (TA_g_cfg + 56) 4
    ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
        mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32) ->
  cf_bw W memF TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1) ->
  cf_bw W memF TA_g_now 8 1000000 ->
  cf_bw W memF TA_g_fail_next 1 0 ->
  cf_bw W memF TA_g_last_counter 4 0 ->
  lc_tw W memF (cf_world (l_pl cx) B1).
Proof.
intros cx ly' S' W regs0 mem0 md0 B1 memF LAWS HB HC HTW KV
  H0 H6 H12 H16 H20 H24 H28 H32 H36 H40 H44 H48 H52 H56 HR HN HF HL.
unfold lc_tw in HTW |- *. unfold cf_world. cbv zeta.
set (rd := aview segs (w_H W) mem0) in *. set (rd' := aview segs (w_H W) memF) in *.
rewrite <- (cf_rdp_nil rd' rd) in HTW.
pose proof (cf_fstep _ rd rd' _ _ _ _ 0 TC.HOST TMAP_A_g_cfg ltac:(lia)
  ltac:(assert (HH : Z.of_nat (length TC.HOST) = 6) by reflexivity; unfold TW.SZ_g_cfg; lia) HTW H0) as S1.
pose proof (cf_wstep _ rd rd' _ _ _ _ 16 4 _ TMAP_A_g_cfg ltac:(lia)
  ltac:(cbn [Z.of_nat]; unfold TW.SZ_g_cfg; lia) S1 H16) as S2.
pose proof (cf_wstep _ rd rd' _ _ _ _ 20 4 _ TMAP_A_g_cfg ltac:(lia)
  ltac:(cbn [Z.of_nat]; unfold TW.SZ_g_cfg; lia) S2 H20) as S3.
pose proof (cf_wstep _ rd rd' _ _ _ _ 12 4 _ TMAP_A_g_cfg ltac:(lia)
  ltac:(cbn [Z.of_nat]; unfold TW.SZ_g_cfg; lia) S3 H12) as S4.
pose proof (cf_fstep _ rd rd' _ _ _ _ 6 TC.DESK TMAP_A_g_cfg ltac:(lia)
  ltac:(assert (HH : Z.of_nat (length TC.DESK) = 6) by reflexivity; unfold TW.SZ_g_cfg; lia) S4 H6) as S5.
pose proof (cf_wstep _ rd rd' _ _ _ _ 32 4 _ TMAP_A_g_cfg ltac:(lia)
  ltac:(cbn [Z.of_nat]; unfold TW.SZ_g_cfg; lia) S5 H32) as S6.
pose proof (cf_wstep _ rd rd' _ _ _ _ 28 4 _ TMAP_A_g_cfg ltac:(lia)
  ltac:(cbn [Z.of_nat]; unfold TW.SZ_g_cfg; lia) S6 H28) as S7.
pose proof (cf_wstep _ rd rd' _ _ _ _ 24 4 _ TMAP_A_g_cfg ltac:(lia)
  ltac:(cbn [Z.of_nat]; unfold TW.SZ_g_cfg; lia) S7 H24) as S8.
pose proof (cf_wstep _ rd rd' _ _ _ _ 36 4 _ TMAP_A_g_cfg ltac:(lia)
  ltac:(cbn [Z.of_nat]; unfold TW.SZ_g_cfg; lia) S8 H36) as S9.
pose proof (cf_wstep _ rd rd' _ _ _ _ 40 4 _ TMAP_A_g_cfg ltac:(lia)
  ltac:(cbn [Z.of_nat]; unfold TW.SZ_g_cfg; lia) S9 H40) as S10.
pose proof (cf_wstep _ rd rd' _ _ _ _ 44 4 _ TMAP_A_g_cfg ltac:(lia)
  ltac:(cbn [Z.of_nat]; unfold TW.SZ_g_cfg; lia) S10 H44) as S11.
pose proof (cf_wstep _ rd rd' _ _ _ _ 48 4 _ TMAP_A_g_cfg ltac:(lia)
  ltac:(cbn [Z.of_nat]; unfold TW.SZ_g_cfg; lia) S11 H48) as S12.
pose proof (cf_wstep _ rd rd' _ _ _ _ 52 4 _ TMAP_A_g_cfg ltac:(lia)
  ltac:(cbn [Z.of_nat]; unfold TW.SZ_g_cfg; lia) S12 H52) as S13.
pose proof (cf_wstep _ rd rd' _ _ _ _ 56 4 _ TMAP_A_g_cfg ltac:(lia)
  ltac:(cbn [Z.of_nat]; unfold TW.SZ_g_cfg; lia) S13 H56) as S14.
pose proof (cf_wstep _ rd rd' _ _ _ _ 0 4 _ TMAP_A_g_raw ltac:(lia)
  ltac:(cbn [Z.of_nat]; unfold TW.SZ_g_raw; lia) S14 HR) as S15.
pose proof (cf_wstep _ rd rd' _ _ _ _ 0 8 _ TMAP_A_g_now ltac:(lia)
  ltac:(cbn [Z.of_nat]; unfold TW.SZ_g_now; lia) S15 HN) as S16.
pose proof (cf_wstep _ rd rd' _ _ _ _ 0 1 _ TMAP_A_g_fail_next ltac:(lia)
  ltac:(cbn [Z.of_nat]; lia) S16 HF) as S17.
pose proof (cf_wstep _ rd rd' _ _ _ _ 0 4 _ TMAP_A_g_last_counter ltac:(lia)
  ltac:(cbn [Z.of_nat]; unfold TW.SZ_g_last_counter; lia) S17 HL) as S18.
lazymatch type of S18 with tw_at _ (cf_rdp ?L _ _) _ => apply (cf_wclose L rd rd') end; [exact S18|].
intros x Hx E.
destruct (cf_apart cx ly' S' W regs0 mem0 md0 0 LAWS HB HC) as (_ & AG).
destruct (AG x Hx) as (Hhull & Hx64).
apply KV; [exact Hx64|]. intros Hwr.
assert (Hin5 : (TA_g_cfg <= x < TA_g_cfg + 60) \/ (TA_g_raw <= x < TA_g_raw + 4) \/
               (TA_g_now <= x < TA_g_now + 8) \/ (TA_g_fail_next <= x < TA_g_fail_next + 1) \/
               (TA_g_last_counter <= x < TA_g_last_counter + 4)).
{ unfold cf_wr in Hwr. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hhull.
  destruct (cf_num cx ly' S' W regs0 mem0 md0 0 LAWS HB HC) as (N1 & _).
  pose proof (@alloc_ceiling_value rc) as ((Hcmin & _) & _).
  unfold ESTACK in Hwr. unfold TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
assert (HT : cf_in
  [(TA_g_last_counter + 0, Z.of_nat 4); (TA_g_fail_next + 0, Z.of_nat 1); (TA_g_now + 0, Z.of_nat 8);
   (TA_g_raw + 0, Z.of_nat 4); (TA_g_cfg + 56, Z.of_nat 4); (TA_g_cfg + 52, Z.of_nat 4);
   (TA_g_cfg + 48, Z.of_nat 4); (TA_g_cfg + 44, Z.of_nat 4); (TA_g_cfg + 40, Z.of_nat 4);
   (TA_g_cfg + 36, Z.of_nat 4); (TA_g_cfg + 24, Z.of_nat 4); (TA_g_cfg + 28, Z.of_nat 4);
   (TA_g_cfg + 32, Z.of_nat 4); (TA_g_cfg + 6, Z.of_nat (length TC.DESK)); (TA_g_cfg + 12, Z.of_nat 4);
   (TA_g_cfg + 20, Z.of_nat 4); (TA_g_cfg + 16, Z.of_nat 4); (TA_g_cfg + 0, Z.of_nat (length TC.HOST))] x = true).
{ assert (LH : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  assert (LD : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  change (Z.of_nat 4) with 4. change (Z.of_nat 1) with 1. change (Z.of_nat 8) with 8.
  rewrite LH, LD.
  destruct Hin5 as [Hc | [Hc | [Hc | [Hc | Hc]]]].
  - assert (Hcase : (TA_g_cfg + 0 <= x < TA_g_cfg + 0 + 6) \/ (TA_g_cfg + 6 <= x < TA_g_cfg + 6 + 6) \/
      (TA_g_cfg + 12 <= x < TA_g_cfg + 12 + 4) \/ (TA_g_cfg + 16 <= x < TA_g_cfg + 16 + 4) \/
      (TA_g_cfg + 20 <= x < TA_g_cfg + 20 + 4) \/ (TA_g_cfg + 24 <= x < TA_g_cfg + 24 + 4) \/
      (TA_g_cfg + 28 <= x < TA_g_cfg + 28 + 4) \/ (TA_g_cfg + 32 <= x < TA_g_cfg + 32 + 4) \/
      (TA_g_cfg + 36 <= x < TA_g_cfg + 36 + 4) \/ (TA_g_cfg + 40 <= x < TA_g_cfg + 40 + 4) \/
      (TA_g_cfg + 44 <= x < TA_g_cfg + 44 + 4) \/ (TA_g_cfg + 48 <= x < TA_g_cfg + 48 + 4) \/
      (TA_g_cfg + 52 <= x < TA_g_cfg + 52 + 4) \/ (TA_g_cfg + 56 <= x < TA_g_cfg + 56 + 4)) by lia.
    repeat (destruct Hcase as [Hk | Hcase];
      [refine (cf_in_true _ x _ _ _ Hk); cbn [In]; tauto |]).
    refine (cf_in_true _ x _ _ _ Hcase); cbn [In]; tauto.
  - refine (cf_in_true _ x (TA_g_raw + 0) 4 _ ltac:(lia)); cbn [In]; tauto.
  - refine (cf_in_true _ x (TA_g_now + 0) 8 _ ltac:(lia)); cbn [In]; tauto.
  - refine (cf_in_true _ x (TA_g_fail_next + 0) 1 _ ltac:(lia)); cbn [In]; tauto.
  - refine (cf_in_true _ x (TA_g_last_counter + 0) 4 _ ltac:(lia)); cbn [In]; tauto. }
rewrite HT in E. discriminate E.
Qed.

(* ------------------------------------------------------------------ *)
(* 7. +0x1cc .. +0x214: the two memcpys and the three flag stores      *)
(* ------------------------------------------------------------------ *)

(* The state at the return of the second __asan_memcpy (+0x214): g_cfg's first 24 bytes written. *)
Definition cf_st2 (cx : lcx) (ly' : alayout) (S' : astate) (W : world segs) (mem0 : word -> option byte)
  : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = lc_cfg cx CF_RC2 regs' mem' md' /\ cf_J cx ly' S' W mem' md' /\ cf_KV cx W mem0 mem' /\
    cf_GP W mem0 mem' /\
    cf_bl W mem' (TA_g_cfg + 0) TC.HOST /\ cf_bl W mem' (TA_g_cfg + 6) TC.DESK /\
    cf_bw W mem' (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) /\
    cf_bw W mem' (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) /\
    cf_bw W mem' (TA_g_cfg + 20) 4
      (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) /\
    cf_regs cx regs' /\ YK11.getr regs' 23 = w64 (lc_flags (l_pl cx)) /\
    YK11.getr regs' 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) /\
    lc_cur cx regs' 19 27 (lc_c1 (l_pl cx)).

(* The value of a symbolic word as the word of a Z, one constructor at a time. *)
Lemma cf_den_lit : forall E z, sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.
Lemma cf_den_off : forall E n k x, bv_unsigned (ew E n) = x -> sv_denot E (SOff n k) = Z_to_bv 64 (x + k).
Proof. intros E n k x H. cbn [sv_denot]. rewrite H. reflexivity. Qed.
Lemma cf_den_alu : forall E op a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  sv_denot E (SAlu op a b) = Z_to_bv 64 (zalu64 op x y).
Proof. intros E op a b x y Ha Hb. cbn [sv_denot]. rewrite Ha, Hb. apply zalu64_sound. Qed.
Lemma cf_den_mul : forall E op a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  sv_denot E (SMd op a b) = Z_to_bv 64 (zmd64 op x y).
Proof. intros E op a b x y Ha Hb. cbn [sv_denot]. rewrite Ha, Hb. apply zmd64_sound. Qed.
Lemma cf_word_eq : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. exact H. Qed.
(* ------------------------------------------------------------------ *)
(* 5a. The stored config values, decided over the bytes they read      *)
(* ------------------------------------------------------------------ *)

Definition cf_all1 (f : Z -> bool) : bool := tw_allz f 0 (Z.to_nat 256).
Lemma cf_all1_ok : forall f, cf_all1 f = true -> forall x, 0 <= x < 256 -> f x = true.
Proof.
intros f H x Hx. exact (tw_allz_ok f (Z.to_nat 256) 0 H x ltac:(rewrite Z2Nat.id by lia; lia)).
Qed.
Definition cf_all2 (f : Z -> Z -> bool) : bool :=
  tw_allz (fun x => tw_allz (f x) 0 (Z.to_nat 256)) 0 (Z.to_nat 256).
Lemma cf_all2_ok : forall f, cf_all2 f = true ->
  forall x y, 0 <= x < 256 -> 0 <= y < 256 -> f x y = true.
Proof.
intros f H x y Hx Hy.
pose proof (tw_allz_ok _ (Z.to_nat 256) 0 H x ltac:(rewrite Z2Nat.id by lia; lia)) as Hx'.
exact (tw_allz_ok (f x) (Z.to_nat 256) 0 Hx' y ltac:(rewrite Z2Nat.id by lia; lia)).
Qed.

(* max_retries: `andi a0, a0, 7` of the byte. *)
Lemma cf_f32 : forall b, 0 <= b < 256 -> zalu64 ALU_AND b 7 = b mod 8.
Proof.
intros b Hb.
apply Z.eqb_eq.
exact (cf_all1_ok (fun b => Z.eqb (zalu64 ALU_AND b 7) (b mod 8)) ltac:(vm_compute; reflexivity) b Hb).
Qed.
(* ack / keepalive / offline / wake at two bytes: `or` of the pair, then `addi x, x, 1`. *)
Lemma cf_f16a : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  zalu64 ALU_ADD (zalu64 ALU_OR x (zalu64 ALU_SLL y 8)) 1 = (1 + (x + 256 * y)) mod 2 ^ 32.
Proof.
intros x y Hx Hy. apply Z.eqb_eq.
exact (cf_all2_ok (fun x y =>
  Z.eqb (zalu64 ALU_ADD (zalu64 ALU_OR x (zalu64 ALU_SLL y 8)) 1) ((1 + (x + 256 * y)) mod 2 ^ 32))
  ltac:(vm_compute; reflexivity) x y Hx Hy).
Qed.
(* display_gap_us: `or` of the pair, no increment. *)
Lemma cf_f16b : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  zalu64 ALU_OR (zalu64 ALU_SLL y 8) x = x + 256 * y.
Proof.
intros x y Hx Hy. apply Z.eqb_eq.
exact (cf_all2_ok (fun x y => Z.eqb (zalu64 ALU_OR (zalu64 ALU_SLL y 8) x) (x + 256 * y))
  ltac:(vm_compute; reflexivity) x y Hx Hy).
Qed.
(* max_cmds: `zext.b; addi -255; seqz; addi -1; and; addi 1` is 1 + b mod 255. *)
Lemma cf_f52 : forall b, 0 <= b < 256 ->
  zalu64 ALU_ADD (zalu64 ALU_AND (zalu64 ALU_AND b 255)
    (zalu64 ALU_ADD (zalu64 ALU_SLTU (zalu64 ALU_ADD (zalu64 ALU_AND b 255) (-255)) 1) (-1))) 1
  = (1 + b mod 255) mod 2 ^ 32.
Proof.
intros b Hb. apply Z.eqb_eq.
exact (cf_all1_ok (fun b => Z.eqb
  (zalu64 ALU_ADD (zalu64 ALU_AND (zalu64 ALU_AND b 255)
     (zalu64 ALU_ADD (zalu64 ALU_SLTU (zalu64 ALU_ADD (zalu64 ALU_AND b 255) (-255)) 1) (-1))) 1)
  ((1 + b mod 255) mod 2 ^ 32)) ltac:(vm_compute; reflexivity) b Hb).
Qed.
(* max_body: SPEC_CMD_MAX + v mod 1461, by the mul-shift reduction, zero-extended to 16 bits. *)
Lemma cf_f56a : forall x, 0 <= x < 256 ->
  zalu64 ALU_SRL (zalu64 ALU_SLL (zalu64 ALU_ADD (zalu64 ALU_SUB (zalu64 ALU_OR 0 x)
    (zmd64 M_MUL (zalu64 ALU_SRL (zmd64 M_MUL (zalu64 ALU_OR 0 x) 22967) 25) 1461)) 24) 48) 48 = (DSpec.SPEC_CMD_MAX + x mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32.
Proof.
intros x Hx. apply Z.eqb_eq.
exact (cf_all1_ok (fun x => Z.eqb (zalu64 ALU_SRL (zalu64 ALU_SLL (zalu64 ALU_ADD (zalu64 ALU_SUB (zalu64 ALU_OR 0 x)
    (zmd64 M_MUL (zalu64 ALU_SRL (zmd64 M_MUL (zalu64 ALU_OR 0 x) 22967) 25) 1461)) 24) 48) 48) ((DSpec.SPEC_CMD_MAX + x mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)) ltac:(vm_compute; reflexivity) x Hx).
Qed.
Lemma cf_f56b : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  zalu64 ALU_SRL (zalu64 ALU_SLL (zalu64 ALU_ADD (zalu64 ALU_SUB (zalu64 ALU_OR (zalu64 ALU_SLL y 8) x)
    (zmd64 M_MUL (zalu64 ALU_SRL (zmd64 M_MUL (zalu64 ALU_OR (zalu64 ALU_SLL y 8) x) 22967) 25) 1461)) 24) 48) 48 = (DSpec.SPEC_CMD_MAX + (x + 256 * y) mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32.
Proof.
intros x y Hx Hy. apply Z.eqb_eq.
exact (cf_all2_ok (fun x y => Z.eqb (zalu64 ALU_SRL (zalu64 ALU_SLL (zalu64 ALU_ADD (zalu64 ALU_SUB (zalu64 ALU_OR (zalu64 ALU_SLL y 8) x)
    (zmd64 M_MUL (zalu64 ALU_SRL (zmd64 M_MUL (zalu64 ALU_OR (zalu64 ALU_SLL y 8) x) 22967) 25) 1461)) 24) 48) 48) ((DSpec.SPEC_CMD_MAX + (x + 256 * y) mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)) ltac:(vm_compute; reflexivity) x y Hx Hy).
Qed.

(* A value that fits in 32 bits, seen through the two wrappings. *)
Lemma cf_small : forall x y, 0 <= x < 2 ^ 32 -> x = y -> x mod 2 ^ 64 = (y mod 2 ^ 32) mod 2 ^ 64.
Proof. intros x y Hx <-. rewrite (Z.mod_small x (2 ^ 32)) by lia. reflexivity. Qed.


Lemma cf_land1 : forall x, 0 <= x -> 0 <= Z.land x 1 <= 1.
Proof.
intros x Hx. split; [apply Z.land_nonneg; left; exact Hx|].
replace (Z.land x 1) with (x mod 2 ^ 1) by (rewrite <- (Z.land_ones x 1) by lia; reflexivity).
change (2 ^ 1) with 2. pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia.
Qed.

(* The bit extractions of the flags byte the code does, decided over every byte value. *)
Lemma cf_bits_chk :
  tw_allz (fun f =>
    (zalu64 ALU_SRL (zalu64 ALU_SLL f 61) 63 =? Z.land (Z.shiftr f 2) 1) &&
    (zalu64 ALU_SRL (zalu64 ALU_SLL f 62) 63 =? (if Z.land f 2 =? 0 then 0 else 1)) &&
    (zalu64 ALU_SRL (zalu64 ALU_SLL f 60) 63 =? Z.land (Z.shiftr f 3) 1) &&
    (zalu64 ALU_AND f 1 =? Z.land f 1)) 0 (Z.to_nat 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cf_bits : forall f, 0 <= f < 256 ->
  zalu64 ALU_SRL (zalu64 ALU_SLL f 61) 63 = Z.land (Z.shiftr f 2) 1 /\
  zalu64 ALU_SRL (zalu64 ALU_SLL f 62) 63 = (if Z.land f 2 =? 0 then 0 else 1) /\
  zalu64 ALU_SRL (zalu64 ALU_SLL f 60) 63 = Z.land (Z.shiftr f 3) 1 /\
  zalu64 ALU_AND f 1 = Z.land f 1.
Proof.
intros f Hf.
pose proof (tw_allz_ok _ (Z.to_nat 256) 0 cf_bits_chk f ltac:(rewrite Z2Nat.id by lia; lia)) as C.
rewrite !andb_true_iff in C. destruct C as (((C1 & C2) & C3) & C4).
split; [apply Z.eqb_eq; exact C1|]. split; [apply Z.eqb_eq; exact C2|].
split; [apply Z.eqb_eq; exact C3 | apply Z.eqb_eq; exact C4].
Qed.


(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac cf_rd HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?valx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* The write obligation of a run whose regions write no byte. *)
Ltac cf_awr_ro :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
          [let a := fresh "a" in let Ha := fresh "Ha" in
           intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

Lemma cf_agree_extK : forall E0 E K ws, (512 <= K)%nat -> env_agree 512 E0 E -> env_agree 512 E0 (extK E K ws).
Proof.
intros E0 E K ws HK [H1 H2]. destruct (env_agree_extK E K ws) as [A1 A2].
split; [intros n Hn; rewrite (A1 n ltac:(lia)); exact (H1 n Hn) | rewrite A2; exact H2].
Qed.

(* An object atom (an image address the run materialised) at a valuation that agrees with a seat's below 512. *)
Lemma cf_den_obj : forall regs ex E n k, (A_TEXT <= n < A_LIM)%nat -> (n < 512)%nat ->
  env_agree 512 (cf_E regs ex) E -> sv_denot E (SOff n k) = Z_to_bv 64 (VAL n + k).
Proof.
intros regs ex E n k Hn H512 HA. cbn [sv_denot].
first [rewrite (proj1 HA n H512) | rewrite <- (proj1 HA n H512)]. rewrite (cf_E_obj regs ex n Hn).
apply cf_word_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* The denotation of a symbolic word, from the values of its atoms at the seat's valuation. *)
Ltac cf_den :=
  lazymatch goal with
  | |- sv_denot ?E (SLit ?z) = _ => apply cf_den_lit
  | |- sv_denot ?E (SOff ?n ?k) = _ =>
      first
        [ eapply cf_den_off;
          first [ match goal with H : bv_unsigned (ew E n) = _ |- _ => exact H end
                | match goal with
                  | HA : env_agree 512 ?E0 E |- _ =>
                      first [rewrite (proj1 HA n ltac:(lia)) | rewrite <- (proj1 HA n ltac:(lia))];
                      match goal with H : bv_unsigned (ew E0 n) = _ |- _ => exact H end
                  end ]
        | match goal with
          | HA : env_agree 512 ?E0 E |- _ =>
              eapply (cf_den_obj _ _ E n k ltac:(unfold A_TEXT, A_LIM; lia) ltac:(lia) HA)
          end ]
  | |- sv_denot ?E (SAlu ?op ?a ?b) = _ => eapply cf_den_alu; cf_den
  | |- sv_denot ?E (SMd ?op ?a ?b) = _ => eapply cf_den_mul; cf_den
  end.

(* The run's valuation agrees with the seat's below atom 512. *)
Lemma cf_agree_ewset : forall E0 E n w, (512 <= n)%nat -> env_agree 512 E0 E ->
  env_agree 512 E0 (ewset E n w).
Proof.
intros E0 E n w Hn [H1 H2]. split.
- intros m Hm. cbn [ew ewset].
  repeat match goal with
  | |- context [Nat.eqb ?a ?b] => let Eq := fresh in destruct (Nat.eqb_spec a b) as [Eq | Eq]; [exfalso; lia|]
  end.
  exact (H1 m Hm).
- cbn [ed ewset]. exact H2.
Qed.

Ltac cf_ag_go :=
  first
    [ apply env_agree_refl
    | apply cf_agree_extK; [lia | cf_ag_go]
    | apply cf_agree_ewset; [lia | cf_ag_go]
    | apply env_agree_havoc_ge; [lia | cf_ag_go] ].
Ltac cf_ag E0 :=
  lazymatch goal with
  | HSx : OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?Ex _ _ |- _ =>
      assert (env_agree 512 E0 Ex) by cf_ag_go
  | HSx : st_ok_pi _ _ ?Ex _ _ |- _ =>
      assert (env_agree 512 E0 Ex) by cf_ag_go
  end.

(* A register value, from the denotations of its atoms. *)
Ltac cf_rval :=
  try unfold w64; etransitivity; [cf_den|]; apply cf_word_eq;
  unfold zalu64, zmd64, zalu_raw, zmd_raw, zcanon, M64; rewrite ?Z.add_0_r;
  first [reflexivity | f_equal; lia | vm_compute; reflexivity | Z.div_mod_to_equations; lia].

(* A code pointer the run left in a register. *)
Ltac cf_code := apply codeptr_val; assumption.
(* The seats of the two runs: +0x1cc (no region) and +0x1e0 (g_cfg's three flag words). *)
Definition cf_ssa : sstate :=
  mkSS LO_CFGD sr_atoms [] None (mkFacts [(21%nat, mkAF TA_g_cfg TA_g_cfg 0)] [] []).
Definition cf_ssb1 : sstate :=
  mkSS CF_RC1 sr_atoms [cf_rg_cfgb] None
    (mkFacts [(21%nat, mkAF TA_g_cfg TA_g_cfg 0); (23%nat, mkAF 0 255 0)] [] []).

Lemma cf_flags_rng : forall D, 0 <= lc_flags D < 256.
Proof.
intros D. unfold lc_flags, TOP.fuzz_u8_m. destruct (Z.eqb_spec (TOP.fi_n (TOP.fuzz_in_m (Z.of_nat (length D)))) 0).
- cbn [snd]. lia.
- cbn [snd]. unfold DSpec.at8, DSpec.bz.
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (TOP.fi_off (TOP.fuzz_in_m (Z.of_nat (length D))))) D
    (DSpec.b8 0))) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma cf_stage_ab : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_rom_view_stmt rc B MT XL RLO RHI -> @lc_src_ro_stmt rc B MT XL RLO RHI ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 -> cf_regs cx regs0 ->
  YK11.getr regs0 23 = w64 (lc_flags (l_pl cx)) -> lc_cur cx regs0 19 27 (lc_c1 (l_pl cx)) ->
  SRr segs W (lc_cfg cx LO_CFGD regs0 mem0 md0) (cf_st2 cx ly' S' W mem0).
Proof.
intros cx ly' S' W regs0 mem0 md0 HP HB K1 K2 HC HRG R23 HCUR.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lp_scfg_cells _ _ _ _ _ HP) as HSC.
pose proof HRG as (R2 & R8 & R9 & R3 & R4 & R18 & R26 & R21 & R20).
destruct (cf_num cx ly' S' W regs0 mem0 md0 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (proj1 HC) as HJ0.
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
assert (Hsp16 : (lc_sp1 cx - lc_sp0 cx) mod 16 = 0).
{ apply Z.mod_divide in N3; [|lia]. apply Z.mod_divide in N5; [|lia].
  destruct N3 as [k Hk]. destruct N5 as [j Hj]. rewrite Hk, Hj.
  replace (k * 32 - j * 16) with ((2 * k - j) * 16) by ring. apply Z.mod_mul. lia. }
assert (Usp : spZ regs0 = lc_sp1 cx) by (unfold spZ; rewrite R2; apply cf_u64; lia).
assert (EPCA : w64 (transport_text + LO_CFGD) = Z_to_bv 64 (BASE + LO_CFGD))
  by (unfold w64; f_equal; vm_compute; reflexivity).
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUN.
unfold lc_cfg. rewrite EPCA.
(* ---- run A, +0x1cc .. +0x1dc: the arguments of the first __asan_memcpy ---- *)
set (E0 := cf_E regs0 []).
assert (HEI : img_env VAL A_LIM E0) by apply cf_E_img.
assert (U21 : bv_unsigned (ew E0 21) = TA_g_cfg)
  by (unfold E0; rewrite (cf_E_reg regs0 [] 21%nat 21%bv eq_refl), R21; apply cf_u64; unfold TA_g_cfg; lia).
assert (U247 : bv_unsigned (ew E0 247) = TRANS_HOST).
{ unfold E0. rewrite (cf_E_obj regs0 [] 247%nat ltac:(unfold A_TEXT, A_LIM; lia)).
  assert (EV : VAL 247%nat = TRANS_HOST) by (vm_compute; reflexivity).
  rewrite EV. apply cf_u64. unfold TRANS_HOST. lia. }
assert (HS : @st_ok_pi segs VAL (l_fx cx) E0 cf_ssa
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs0 (Z_to_bv 64 (BASE + LO_CFGD)) mem0 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold cf_ssa.
  apply (@pa_entry_st_ok_full (l_fx cx) rc transport_listing PI_transport).
  - unfold E0, cf_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U21. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (SHOK : sh_ok segs cf_Bx (@nil shent) E0 (mrestrict (w_H W) mem0)) by constructor.
paj_run_tok RUN HS HJ0 SHOK YC4b.Bspan.
{ cf_awr_ro. }
set (md1 := with_vm_backing (m_vm_lazy md0) mat md0) in *. clearbody md1. clear mat.
cf_ag E0.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem0 a).
{ intros a Ha. apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [|exact Ha | intros []].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin. destruct Hin. }
assert (GA1 : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
cf_rd HS (Z_to_bv 5 10) (w64 TA_g_cfg) Ra0 ltac:(cf_rval).
cf_rd HS (Z_to_bv 5 11) (w64 TRANS_HOST) Ra1 ltac:(cf_rval).
cf_rd HS (Z_to_bv 5 12) (w64 6) Ra2 ltac:(cf_rval).
cf_rd HS (1%bv : bv 5) (Z_to_bv 64 (BASE + CF_RC1)) Rra ltac:(cf_code).
assert (KRA : aregs_preserved regs0 (ms_regs ms)).
{ apply (AE2y.aregs_preserved_of_st_ok (w_H W) _ _ ms regs0 [] HS);
    [apply cf_agree; apply env_agree_refl | vm_compute; reflexivity]. }
pmkst HS.
assert (Q2 : YK11.getr (ms_regs ms) 2 = w64 (lc_sp1 cx)) by exact (eq_trans (KRA 2 ltac:(unfold acallee_saved; lia)) R2).
assert (Q3 : YK11.getr (ms_regs ms) 3 = w64 (as_gp B)) by exact (eq_trans (KRA 3 ltac:(unfold acallee_saved; lia)) R3).
assert (Q4 : YK11.getr (ms_regs ms) 4 = w64 (as_tp B)) by exact (eq_trans (KRA 4 ltac:(unfold acallee_saved; lia)) R4).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARm.
assert (HCm : @lc_core rc B cx ly' S' W (ms_regs ms) (ms_mem ms) md1 0).
{ split; [exact HJ0|].
  exact (cf_rest_step cx ly' S' W regs0 mem0 md0 0 (ms_regs ms) (ms_mem ms) LAWS HB HC
    (eq_trans Q2 (eq_sym R2)) (KRA 8 ltac:(unfold acallee_saved; lia)) (KRA 9 ltac:(unfold acallee_saved; lia))
    (eq_trans Q3 (eq_sym R3)) (eq_trans Q4 (eq_sym R4)) (fun a Ha _ => KA1 a Ha) GA1). }
pose proof (K1 HP cx ly' S' W (ms_regs ms) (ms_mem ms) md1 0 HB HCm) as HROm.
pose proof (K2 HP cx ly' S' W (ms_regs ms) (ms_mem ms) md1 0 TRANS_HOST 6 HB HCm
  ltac:(cbn [In]; tauto)) as HSRC.
destruct (trans_src_ok_rd B LAWS ly' S' W (ms_mem ms) md1 TRANS_HOST 6 HARm HSRC ltac:(lia))
  as (RV & RRA & RHULL & RAM & _ & _).
(* ---- the first __asan_memcpy (g_cfg, HOST, 6) ---- *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transport_segs_low OCpy
    (transport_sigma TS___asan_memcpy) (lp_memcpy B MT XL RLO RHI HP (l_fx cx)) TG.G_HARNESS W (ms_regs ms)
    (ms_mem ms) _ _ _ _ _ _ _ _ _ ly' S' md1 0 TA_g_cfg TRANS_HOST 6 (lc_sp1 cx - lc_sp0 cx)
    (Z_to_bv 64 (BASE + CF_RC1)) HGX G_HARNESS_rw HJ0 Ra0 Ra1 Ra2).
  - lia.
  - unfold TA_g_cfg. lia.
  - unfold TA_g_cfg. lia.
  - unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact Hsp16.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact Q3.
  - exact Q4.
  - exact Rra.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold CF_RC1; lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ0|]. intros a Ha. right. apply cf_cfg_inG. lia.
  - unfold amem_range, kLowMemEnd, TA_g_cfg. left. lia.
  - apply (range_addressable_sub _ _ TA_g_cfg 60);
      [exact (cf_cfg_ra ly' S' W (ms_mem ms) md1 HSC HARm) | lia | lia].
  - intros _. exact (cf_cfg_hull ly' S' W (ms_mem ms) md1 TA_g_cfg 6 HSC HARm ltac:(lia) ltac:(lia) ltac:(lia)).
  - cbv iota beta. split; [unfold TRANS_HOST; lia|]. split; [unfold TRANS_HOST; lia|].
    split; [intros a Ha; split; [exact (RV a Ha)|]; unfold spZ; rewrite Q2; unfold w64;
            rewrite unsigned_lit_small by lia; unfold ESTACK, TRANS_HOST in *; lia|].
    split; [right; unfold TA_g_cfg, TRANS_HOST; lia|].
    split; [exact RAM|]. split; [exact RRA|]. intros _. exact RHULL. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPR2 & Rb0 & Hcpy1 & Heff1 & Hpres1).
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wr cx a -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem0 a).
{ intros a Ha Hn. rewrite (Heff1 a Ha ltac:(intros C; apply Hn; unfold cf_wr; left; unfold TA_g_cfg in *; lia)
    ltac:(intros C; apply Hn; unfold cf_wr; right; right; right; right; right; left; unfold ESTACK in *; lia)).
  exact (KA1 a Ha). }
assert (GA2 : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mem2 a)
  by (intros a Ha; exact (Hpres1 a (GA1 a Ha))).
assert (HC2 : @lc_core rc B cx ly' S' W regs2 mem2 md2 0).
{ split; [exact HJ2|].
  exact (cf_rest_step cx ly' S' W regs0 mem0 md0 0 regs2 mem2 LAWS HB HC
    (eq_trans (eq_trans (HPR2 2 ltac:(unfold acallee_saved; lia)) Q2) (eq_sym R2))
    (eq_trans (HPR2 8 ltac:(unfold acallee_saved; lia)) (KRA 8 ltac:(unfold acallee_saved; lia)))
    (eq_trans (HPR2 9 ltac:(unfold acallee_saved; lia)) (KRA 9 ltac:(unfold acallee_saved; lia)))
    (eq_trans (eq_trans (HPR2 3 ltac:(unfold acallee_saved; lia)) Q3) (eq_sym R3))
    (eq_trans (eq_trans (HPR2 4 ltac:(unfold acallee_saved; lia)) Q4) (eq_sym R4))
    KA2 GA2). }
assert (HOST2 : cf_bl W mem2 (TA_g_cfg + 0) TC.HOST).
{ intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity. rewrite L6 in Hi.
  replace (TA_g_cfg + 0 + i) with (TA_g_cfg + i) by lia.
  rewrite (Hcpy1 i ltac:(lia)). exact (cf_host_bytes W (ms_mem ms) HROm i ltac:(lia)). }
(* ---- run B, +0x1e0 .. +0x210: the three flag words and the arguments of the second __asan_memcpy ---- *)
assert (P2 : YK11.getr regs2 2 = w64 (lc_sp1 cx))
  by exact (eq_trans (HPR2 2 ltac:(unfold acallee_saved; lia)) Q2).
assert (P3 : YK11.getr regs2 3 = w64 (as_gp B))
  by exact (eq_trans (HPR2 3 ltac:(unfold acallee_saved; lia)) Q3).
assert (P4 : YK11.getr regs2 4 = w64 (as_tp B))
  by exact (eq_trans (HPR2 4 ltac:(unfold acallee_saved; lia)) Q4).
assert (P8 : YK11.getr regs2 8 = w64 (lc_sp0 cx))
  by exact (eq_trans (HPR2 8 ltac:(unfold acallee_saved; lia)) (eq_trans (KRA 8 ltac:(unfold acallee_saved; lia)) R8)).
assert (P9 : YK11.getr regs2 9 = w64 (lc_sp1 cx))
  by exact (eq_trans (HPR2 9 ltac:(unfold acallee_saved; lia)) (eq_trans (KRA 9 ltac:(unfold acallee_saved; lia)) R9)).
assert (P18 : YK11.getr regs2 18 = w64 (lc_SH cx))
  by exact (eq_trans (HPR2 18 ltac:(unfold acallee_saved; lia)) (eq_trans (KRA 18 ltac:(unfold acallee_saved; lia)) R18)).
assert (P26 : YK11.getr regs2 26 = w64 SHADOW_OFF)
  by exact (eq_trans (HPR2 26 ltac:(unfold acallee_saved; lia)) (eq_trans (KRA 26 ltac:(unfold acallee_saved; lia)) R26)).
assert (P21 : YK11.getr regs2 21 = w64 TA_g_cfg)
  by exact (eq_trans (HPR2 21 ltac:(unfold acallee_saved; lia)) (eq_trans (KRA 21 ltac:(unfold acallee_saved; lia)) R21)).
assert (P20 : YK11.getr regs2 20 = w64 (lc_F cx + 176))
  by exact (eq_trans (HPR2 20 ltac:(unfold acallee_saved; lia)) (eq_trans (KRA 20 ltac:(unfold acallee_saved; lia)) R20)).
assert (P23 : YK11.getr regs2 23 = w64 (lc_flags (l_pl cx)))
  by exact (eq_trans (HPR2 23 ltac:(unfold acallee_saved; lia)) (eq_trans (KRA 23 ltac:(unfold acallee_saved; lia)) R23)).
destruct HCUR as (HC19 & HC27).
assert (P19 : YK11.getr regs2 19 = w64 (l_p cx + TOP.fi_off (lc_c1 (l_pl cx))))
  by exact (eq_trans (HPR2 19 ltac:(unfold acallee_saved; lia)) (eq_trans (KRA 19 ltac:(unfold acallee_saved; lia)) HC19)).
assert (P27 : YK11.getr regs2 27 = w64 (TOP.fi_n (lc_c1 (l_pl cx))))
  by exact (eq_trans (HPR2 27 ltac:(unfold acallee_saved; lia))
      (eq_trans (KRA 27 ltac:(unfold acallee_saved; lia)) HC27)).
clear dependent ms.
set (E1 := cf_E regs2 []).
assert (HEI1 : img_env VAL A_LIM E1) by apply cf_E_img.
assert (V21 : bv_unsigned (ew E1 21) = TA_g_cfg)
  by (unfold E1; rewrite (cf_E_reg regs2 [] 21%nat 21%bv eq_refl), P21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V23 : bv_unsigned (ew E1 23) = lc_flags (l_pl cx))
  by (unfold E1; rewrite (cf_E_reg regs2 [] 23%nat 23%bv eq_refl), P23; apply cf_u64; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (HS1 : @st_ok_pi segs VAL (l_fx cx) E1 cf_ssb1
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs2 (Z_to_bv 64 (BASE + CF_RC1)) mem2 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold cf_ssb1.
  apply (@pa_entry_st_ok_full (l_fx cx) rc transport_listing PI_transport).
  - unfold E1, cf_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold cf_rg_cfgb, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite V21.
    split; [unfold TA_g_cfg; lia|]. split; [unfold TA_g_cfg; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_g_cfg + o) G_HARNESS_rw). apply cf_cfg_inG. lia.
  - apply pairwise_disjoint_of_extents. unfold cf_rg_cfgb, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite V21, V23. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (SHOK1 : sh_ok segs cf_Bx (@nil shent) E1 (mrestrict (w_H W) mem2)) by constructor.
paj_run_tok RUN HS1 HJ2 SHOK1 YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite V21 in Ha.
  apply cf_cfg_inG. lia. }
set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
cf_ag E1.
assert (KA3 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_g_cfg + 12 <= a < TA_g_cfg + 24) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun x => TA_g_cfg + 12 <= x < TA_g_cfg + 24) HFr); [|exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin. destruct Hin as [Hin | []]. injection Hin as <- <- <-.
  cbn [base_val] in Hx. rewrite V21 in Hx. lia. }
assert (GA3 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KRB : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 23%bv; 26%bv;
    Z_to_bv 5 27] -> YK11.getr (ms_regs ms) r = YK11.getr regs2 r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs2 [] _ HS1 _ _ r Hr);
    [apply cf_agree; apply env_agree_refl | vm_compute; reflexivity]. }
(* the three flag words, read back from the run's region *)
pose proof (YC4b.st_ok_region_nth E1 _ (restrict (w_H W) ms) 0 _ HS1 eq_refl) as RG0.
cbn [ms_mem restrict] in RG0.
assert (HB12 : cf_bw W (ms_mem ms) (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1)).
{ intros j Hj.
  refine (cf_vb (w_H W) (ms_mem ms) (TA_g_cfg + 12) 4 _ _ j Hj).
  refine (can_field_of_region E1 _ 21%nat TA_g_cfg _ _ _ _ _ 12 4%N
            (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 61)) (SLit 63)) _ RG0 V21 _ _ _ _).
  - cbn [In]. right. right. left. reflexivity.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (Cb & _ & _ & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 2) ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (HB16 : cf_bw W (ms_mem ms) (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1)).
{ intros j Hj.
  refine (cf_vb (w_H W) (ms_mem ms) (TA_g_cfg + 16) 4 _ _ j Hj).
  refine (can_field_of_region E1 _ 21%nat TA_g_cfg _ _ _ _ _ 16 4%N
            (SAlu ALU_AND (SOff 23 0) (SLit 1)) _ RG0 V21 _ _ _ _).
  - cbn [In]. right. left. reflexivity.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & _ & Cb). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (lc_flags (l_pl cx)) ltac:(lia)). lia.
  - cbn. lia. }
assert (HB20 : cf_bw W (ms_mem ms) (TA_g_cfg + 20) 4
  (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO)).
{ intros j Hj.
  refine (cf_vb (w_H W) (ms_mem ms) (TA_g_cfg + 20) 4 _ _ j Hj).
  refine (can_field_of_region E1 _ 21%nat TA_g_cfg _ _ _ _ _ 20 4%N
            (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 62)) (SLit 63)) _ RG0 V21 _ _ _ _).
  - cbn [In]. left. reflexivity.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & Cb & _ & _). rewrite Cb.
    unfold TS0.DIGINET_SUM_BODY, TC.DIGINET_SUM_ZERO. reflexivity.
  - cbn [Z.of_N]. unfold TS0.DIGINET_SUM_BODY, TC.DIGINET_SUM_ZERO.
    destruct (Z.land (lc_flags (l_pl cx)) 2 =? 0); lia.
  - cbn. lia. }
(* the registers at the second call and the state the memcpy is applied to *)
cf_rd HS1 (Z_to_bv 5 10) (w64 (TA_g_cfg + 6)) Rc0 ltac:(cf_rval).
cf_rd HS1 (Z_to_bv 5 11) (w64 TRANS_DESK) Rc1 ltac:(cf_rval).
cf_rd HS1 (Z_to_bv 5 12) (w64 6) Rc2 ltac:(cf_rval).
cf_rd HS1 (1%bv : bv 5) (Z_to_bv 64 (BASE + CF_RC2)) Rcra ltac:(cf_code).
cf_rd HS1 (Z_to_bv 5 22) (w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1)) Rs6
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; rewrite ?Z.add_0_r;
        destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (Cb & _ & _ & _); rewrite Cb; reflexivity).
pmkst HS1.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR3.
assert (HCm2 : @lc_core rc B cx ly' S' W (ms_regs ms) (ms_mem ms) md3 0).
{ split; [exact HJ2|].
  refine (cf_rest_step cx ly' S' W regs2 mem2 md2 0 (ms_regs ms) (ms_mem ms) LAWS HB _
    (KRB 2%bv ltac:(cbn; tauto)) (KRB 8%bv ltac:(cbn; tauto)) (KRB 9%bv ltac:(cbn; tauto))
    (KRB 3%bv ltac:(cbn; tauto)) (KRB 4%bv ltac:(cbn; tauto)) _ GA3).
  - exact HC2.
  - intros a Ha Hn. apply KA3; [exact Ha|].
    intros C. apply Hn. unfold cf_wr. left. unfold TA_g_cfg in *. lia. }
pose proof (K2 HP cx ly' S' W (ms_regs ms) (ms_mem ms) md3 0 TRANS_DESK 6 HB HCm2
  ltac:(cbn [In]; tauto)) as HSRC2.
destruct (trans_src_ok_rd B LAWS ly' S' W (ms_mem ms) md3 TRANS_DESK 6 HAR3 HSRC2 ltac:(lia))
  as (RV2 & RRA2 & RHULL2 & RAM2 & _ & _).
pose proof (K1 HP cx ly' S' W (ms_regs ms) (ms_mem ms) md3 0 HB HCm2) as HROm2.
(* ---- the second __asan_memcpy (g_cfg + 6, DESK, 6) ---- *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transport_segs_low OCpy
    (transport_sigma TS___asan_memcpy) (lp_memcpy B MT XL RLO RHI HP (l_fx cx)) TG.G_HARNESS W (ms_regs ms)
    (ms_mem ms) _ _ _ _ _ _ _ _ _ ly' S' md3 0 (TA_g_cfg + 6) TRANS_DESK 6 (lc_sp1 cx - lc_sp0 cx)
    (Z_to_bv 64 (BASE + CF_RC2)) HGX G_HARNESS_rw HJ2 Rc0 Rc1 Rc2).
  - lia.
  - unfold TA_g_cfg. lia.
  - unfold TA_g_cfg. lia.
  - unfold spZ. rewrite (KRB 2%bv ltac:(cbn; tauto)), P2. unfold w64.
    rewrite unsigned_lit_small by lia. lia.
  - exact Hsp16.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact (eq_trans (KRB 3%bv ltac:(cbn; tauto)) P3).
  - exact (eq_trans (KRB 4%bv ltac:(cbn; tauto)) P4).
  - exact Rcra.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold CF_RC2; lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ2|]. intros a Ha. right. apply cf_cfg_inG. lia.
  - unfold amem_range, kLowMemEnd, TA_g_cfg. left. lia.
  - apply (range_addressable_sub _ _ TA_g_cfg 60);
      [exact (cf_cfg_ra ly' S' W (ms_mem ms) md3 HSC HAR3) | lia | lia].
  - intros _. exact (cf_cfg_hull ly' S' W (ms_mem ms) md3 (TA_g_cfg + 6) 6 HSC HAR3 ltac:(lia) ltac:(lia)
      ltac:(lia)).
  - cbv iota beta. split; [unfold TRANS_DESK; lia|]. split; [unfold TRANS_DESK; lia|].
    split; [intros a Ha; split; [exact (RV2 a Ha)|]; unfold spZ;
            rewrite (KRB 2%bv ltac:(cbn; tauto)), P2; unfold w64;
            rewrite unsigned_lit_small by lia; unfold ESTACK, TRANS_DESK in *; lia|].
    split; [right; unfold TA_g_cfg, TRANS_DESK; lia|].
    split; [exact RAM2|]. split; [exact RRA2|]. intros _. exact RHULL2. }
cbv beta. intros W3 c3 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HPR4 & Rd0 & Hcpy2 & Heff2 & Hpres2).
assert (KM4 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_g_cfg + 6 <= a < TA_g_cfg + 12) ->
  ~ (lc_sp1 cx - ESTACK <= a < lc_sp1 cx) -> aview segs (w_H W) mem4 a = aview segs (w_H W) (ms_mem ms) a).
{ intros a Ha H1 H2. apply Heff2; [exact Ha | lia | unfold ESTACK in *; lia]. }
apply SRr_ret. split; [reflexivity|].
exists regs4, mem4, md4.
assert (EPCB : w64 (transport_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
split; [unfold lc_cfg; rewrite EPCB; reflexivity|].
split; [exact HJ4|].
split.
{ intros a Ha Hn. rewrite (KM4 a Ha ltac:(intros C; apply Hn; unfold cf_wr; left; unfold TA_g_cfg in *; lia)
    ltac:(intros C; apply Hn; unfold cf_wr; right; right; right; right; right; left; lia)).
  rewrite (KA3 a Ha ltac:(intros C; apply Hn; unfold cf_wr; left; unfold TA_g_cfg in *; lia)).
  exact (KA2 a Ha Hn). }
split; [intros a Ha; exact (Hpres2 a (GA3 a (GA2 a Ha)))|].
split.
{ intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity. rewrite L6 in Hi.
  rewrite (KM4 (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg; lia) ltac:(unfold TA_g_cfg; lia)
    ltac:(unfold ESTACK, TA_g_cfg in *; lia)).
  rewrite (KA3 (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg; lia) ltac:(unfold TA_g_cfg; lia)).
  exact (HOST2 i ltac:(rewrite L6; lia)). }
split.
{ intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity. rewrite L6 in Hi.
  rewrite (Hcpy2 i ltac:(lia)). exact (cf_desk_bytes W (ms_mem ms) HROm2 i ltac:(lia)). }
split.
{ intros j Hj. rewrite (KM4 (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg; lia)
    ltac:(unfold TA_g_cfg; lia) ltac:(unfold ESTACK, TA_g_cfg in *; lia)). exact (HB12 j Hj). }
split.
{ intros j Hj. rewrite (KM4 (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg; lia)
    ltac:(unfold TA_g_cfg; lia) ltac:(unfold ESTACK, TA_g_cfg in *; lia)). exact (HB16 j Hj). }
split.
{ intros j Hj. rewrite (KM4 (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg; lia)
    ltac:(unfold TA_g_cfg; lia) ltac:(unfold ESTACK, TA_g_cfg in *; lia)). exact (HB20 j Hj). }
split.
{ unfold cf_regs.
  split; [exact (eq_trans (HPR4 2 ltac:(unfold acallee_saved; lia))
                   (eq_trans (KRB 2%bv ltac:(cbn; tauto)) P2))|].
  split; [exact (eq_trans (HPR4 8 ltac:(unfold acallee_saved; lia))
                   (eq_trans (KRB 8%bv ltac:(cbn; tauto)) P8))|].
  split; [exact (eq_trans (HPR4 9 ltac:(unfold acallee_saved; lia))
                   (eq_trans (KRB 9%bv ltac:(cbn; tauto)) P9))|].
  split; [exact (eq_trans (HPR4 3 ltac:(unfold acallee_saved; lia))
                   (eq_trans (KRB 3%bv ltac:(cbn; tauto)) P3))|].
  split; [exact (eq_trans (HPR4 4 ltac:(unfold acallee_saved; lia))
                   (eq_trans (KRB 4%bv ltac:(cbn; tauto)) P4))|].
  split; [exact (eq_trans (HPR4 18 ltac:(unfold acallee_saved; lia))
                   (eq_trans (KRB 18%bv ltac:(cbn; tauto)) P18))|].
  split; [exact (eq_trans (HPR4 26 ltac:(unfold acallee_saved; lia))
                   (eq_trans (KRB 26%bv ltac:(cbn; tauto)) P26))|].
  split; [exact (eq_trans (HPR4 21 ltac:(unfold acallee_saved; lia))
                   (eq_trans (KRB 21%bv ltac:(cbn; tauto)) P21))
         | exact (eq_trans (HPR4 20 ltac:(unfold acallee_saved; lia))
                   (eq_trans (KRB 20%bv ltac:(cbn; tauto)) P20))]. }
split; [exact (eq_trans (HPR4 23 ltac:(unfold acallee_saved; lia))
                 (eq_trans (KRB 23%bv ltac:(cbn; tauto)) P23))|].
split; [exact (eq_trans (HPR4 22 ltac:(unfold acallee_saved; lia)) Rs6)|].
split; [exact (eq_trans (HPR4 19 ltac:(unfold acallee_saved; lia))
                 (eq_trans (KRB 19%bv ltac:(cbn; tauto)) P19))
       | exact (eq_trans (HPR4 27 ltac:(unfold acallee_saved; lia))
                 (eq_trans (KRB (Z_to_bv 5 27) ltac:(cbn; tauto)) P27))].
Qed.
(* ------------------------------------------------------------------ *)
(* 8. +0x22c .. +0x318: the seat of a run with k config bytes          *)
(* ------------------------------------------------------------------ *)

Lemma cf_E_hi : forall regs ex j, (8 <= j <= 11)%nat ->
  bv_unsigned (ew (cf_E regs ex) (A_HI j)) = transport_hi j.
Proof.
intros regs ex j Hj.
rewrite (cf_E_obj regs ex (A_HI j) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)).
assert (Hc : j = 8%nat \/ j = 9%nat \/ j = 10%nat \/ j = 11%nat) by lia.
destruct Hc as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity.
Qed.

(* Every byte of a scalar global is a byte of G. *)
Lemma cf_glob_inG : forall a,
  TA_g_raw <= a < TA_g_raw + 4 \/ TA_g_now <= a < TA_g_now + 8 \/
  TA_g_fail_next <= a < TA_g_fail_next + 1 \/ TA_g_last_counter <= a < TA_g_last_counter + 4 ->
  W_journalG.inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold W_journalG.inG. apply Exists_exists.
destruct Ha as [Ha | [Ha | [Ha | Ha]]].
- exists (TA_g_raw, TW.SZ_g_raw).
  split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_raw) | unfold in_zr, TW.SZ_g_raw; cbn [fst snd]; lia].
- exists (TA_g_now, TW.SZ_g_now).
  split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_now) | unfold in_zr, TW.SZ_g_now; cbn [fst snd]; lia].
- exists (TA_g_fail_next, 1).
  split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_fail_next) | unfold in_zr; cbn [fst snd]; lia].
- exists (TA_g_last_counter, TW.SZ_g_last_counter).
  split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_last_counter)
         | unfold in_zr, TW.SZ_g_last_counter; cbn [fst snd]; lia].
Qed.

Lemma cf_atoms_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
induction l1 as [|[n f] l1 IH]; cbn [app atoms_ok]; [tauto|].
intros l2 (H1 & H2) H3. exact (conj H1 (IH l2 H2 H3)).
Qed.

Lemma cf_atoms_bytes : forall E (l : list nat),
  (forall j, In j l -> 0 <= bv_unsigned (ew E (32 + j)) <= 255) ->
  atoms_ok E (map (fun j => ((32 + j)%nat, mkAF 0 255 0)) l).
Proof.
induction l as [|j l IH]; cbn [map atoms_ok]; [intros _; exact I|].
intros H. split.
- unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Z.pow_0_r, Z.mod_1_r.
  split; [exact (H j ltac:(left; reflexivity))|]. split; [reflexivity | lia].
- apply IH. intros i Hi. exact (H i ltac:(right; exact Hi)).
Qed.

(* The k input bytes at the cursor, read only. *)
Lemma cf_in_region : forall E (H : word -> bool) m p k (bs : list Z),
  bv_unsigned (ew E 19) = p -> 0 <= p -> p + Z.of_nat k <= 2 ^ 64 ->
  (forall j, (j < k)%nat -> bv_unsigned (ew E (32 + j)) = nth j bs 0) ->
  (forall j, (j < k)%nat -> 0 <= nth j bs 0 < 256) ->
  (forall j, (j < k)%nat -> YI04.val_mem segs (mrestrict H m) (p + Z.of_nat j) 1 (nth j bs 0)) ->
  region_ok segs E (mrestrict H m) (cf_rg_in k).
Proof.
intros E H m p k bs U19 Hp Hk Hden Hrng Hval.
unfold cf_rg_in, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
apply (chunk_ok_val segs E (mrestrict H m) p (Z.of_nat j) 1%N (SOff (32 + j) 0) (nth j bs 0)).
- cbn [sv_denot]. rewrite (Hden j ltac:(lia)), Z.add_0_r. reflexivity.
- cbn [Z.of_N]. change (2 ^ (8 * 1)) with 256. exact (Hrng j ltac:(lia)).
- cbn. lia.
- exact (Hval j ltac:(lia)).
Qed.

Lemma cf_in_wf : forall k, regions_wf (cf_rg_in k :: cf_wregs) = true.
Proof.
intros k. cbn [regions_wf]. apply andb_true_intro. split; [|vm_compute; reflexivity].
unfold cf_rg_in, region_wf. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
apply andb_true_intro. split.
- apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_intro. left. apply Z.leb_le. lia.
- apply forallb_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
  unfold chunk_inside. cbn.
  repeat (apply andb_true_intro; split); first [reflexivity | apply Z.leb_le; lia].
Qed.
(* The seat of a run of the config bytes: the k bytes at the cursor read only, g_cfg's tail, the four spill slots
   and the four scalar globals writable. *)
Lemma cf_seat : forall (cx : lcx) ly' S' (W : world segs) regs mem md (ex : list word) k (bs : list Z) sr pc (G : facts),
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md ->
  regs_ok (cf_E regs ex) sr regs ->
  facts_ok (cf_E regs ex) G ->
  YK11.getr regs 9 = w64 (lc_sp1 cx) -> YK11.getr regs 19 = w64 (l_p cx + 1) ->
  YK11.getr regs 21 = w64 TA_g_cfg ->
  0 < l_n cx -> Z.of_nat k <= l_n cx - 1 ->
  (forall j, (j < k)%nat -> bv_unsigned (ew (cf_E regs ex) (32 + j)) = nth j bs 0) ->
  (forall j, (j < k)%nat -> 0 <= nth j bs 0 < 256) ->
  (forall j, (j < k)%nat ->
     YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j bs 0)) ->
  @st_ok_pi segs VAL (l_fx cx) (cf_E regs ex)
    (mkSS pc sr (cf_rg_in k :: cf_wregs) None G)
    (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros cx ly' S' W regs mem md ex k bs sr pc G LAWS HB HC HJ HRO HFO R9 R19 R21 Hn0 Hk Hden Hrng Hval.
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
destruct (N12 Hn0) as (_ & Gp4 & Gpc & _ & _ & Gpimg).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
(* the input block is not a byte of G, so the two ranges do not meet *)
assert (HD : forall a n, 0 < n -> (forall x, a <= x < a + n -> W_journalG.inG TG.G_HARNESS x) ->
  l_p cx + l_n cx <= a \/ a + n <= l_p cx).
{ intros a n Hn Hg.
  destruct (Z_le_gt_dec (l_p cx + l_n cx) a) as [H1 | H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (a + n) (l_p cx)) as [H2 | H2]; [right; exact H2|].
  exfalso. apply (Gpimg (Z.max (l_p cx) a) ltac:(lia)). apply trans_g_img. apply Hg. lia. }
pose proof (HD TA_g_cfg 60 ltac:(lia) (fun x Hx => cf_cfg_inG x Hx)) as D1.
pose proof (HD TA_g_raw 4 ltac:(lia) (fun x Hx => cf_glob_inG x (or_introl Hx))) as D2.
pose proof (HD TA_g_now 8 ltac:(lia) (fun x Hx => cf_glob_inG x (or_intror (or_introl Hx)))) as D3.
pose proof (HD TA_g_fail_next 1 ltac:(lia)
  (fun x Hx => cf_glob_inG x (or_intror (or_intror (or_introl Hx))))) as D4.
pose proof (HD TA_g_last_counter 4 ltac:(lia)
  (fun x Hx => cf_glob_inG x (or_intror (or_intror (or_intror Hx))))) as D5.
unfold TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in D1, D2, D3, D4, D5.
assert (U9 : bv_unsigned (ew (cf_E regs ex) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs ex 9%nat 9%bv eq_refl), R9; apply cf_u64; lia).
assert (U19 : bv_unsigned (ew (cf_E regs ex) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs ex 19%nat 19%bv eq_refl), R19; apply cf_u64; lia).
assert (U21 : bv_unsigned (ew (cf_E regs ex) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs ex 21%nat 21%bv eq_refl), R21; apply cf_u64; unfold TA_g_cfg; lia).
pose proof (cf_E_hi regs ex 8%nat ltac:(lia)) as U8h.
pose proof (cf_E_hi regs ex 9%nat ltac:(lia)) as U9h.
pose proof (cf_E_hi regs ex 10%nat ltac:(lia)) as U10h.
pose proof (cf_E_hi regs ex 11%nat ltac:(lia)) as U11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in U8h. rewrite EH9 in U9h. rewrite EH10 in U10h. rewrite EH11 in U11h.
assert (Hpres : forall a, lc_sp1 cx <= a < lc_sp1 cx + 184 -> apresent (w_H W) mem a).
{ intros a Ha. apply (SlostHead.slh_jpres B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). unfold LLVMF_STK in *. lia. }
rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full (l_fx cx) rc transport_listing PI_transport).
- exact HRO.
- exact (cf_in_wf k).
- apply Forall_cons; [exact (cf_in_region _ (w_H W) mem (l_p cx + 1) k bs U19 ltac:(lia) ltac:(lia)
    Hden Hrng Hval)|].
  unfold cf_wregs, cf_rg_cfg, cf_rg_sp48, cf_rg_sp120, cf_rg_sp160, cf_rg_sp176, cf_rg_raw, cf_rg_now,
    cf_rg_fail, cf_rg_last.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite ?U21, ?U9, ?U8h, ?U9h, ?U10h, ?U11h.
  + split; [unfold TA_g_cfg; lia|]. split; [unfold TA_g_cfg; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_g_cfg + o) G_HARNESS_rw). apply cf_cfg_inG. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (6157588 + o) G_HARNESS_rw).
    apply cf_glob_inG. left. unfold TA_g_raw. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (6157596 + o) G_HARNESS_rw).
    apply cf_glob_inG. right; left. unfold TA_g_now. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (6157652 + o) G_HARNESS_rw).
    apply cf_glob_inG. right; right; left. unfold TA_g_fail_next. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (6157672 + o) G_HARNESS_rw).
    apply cf_glob_inG. right; right; right. unfold TA_g_last_counter. lia.
- apply pairwise_disjoint_of_extents.
  unfold cf_rg_in, cf_wregs, cf_rg_cfg, cf_rg_sp48, cf_rg_sp120, cf_rg_sp160, cf_rg_sp176, cf_rg_raw,
    cf_rg_now, cf_rg_fail, cf_rg_last, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite ?U19, ?U21, ?U9, ?U8h, ?U9h, ?U10h, ?U11h.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold TA_g_cfg in *. repeat split; first [exact I | lia].
- exact HFO.
Qed.

(* ------------------------------------------------------------------ *)
(* 9. +0x318: the segment's last state                                 *)
(* ------------------------------------------------------------------ *)

Lemma cf_close : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regsF memF mdF,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  cf_J cx ly' S' W memF mdF -> cf_KV cx W mem0 memF -> cf_GP W mem0 memF ->
  cf_bl W memF (TA_g_cfg + 0) TC.HOST -> cf_bl W memF (TA_g_cfg + 6) TC.DESK ->
  cf_bw W memF (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W memF (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W memF (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_bw W memF (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32) ->
  cf_bw W memF (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32) ->
  cf_bw W memF (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8) ->
  cf_bw W memF (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4) ->
  cf_bw W memF (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32) ->
  cf_bw W memF (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32) ->
  cf_bw W memF (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10) ->
  cf_bw W memF (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32) ->
  cf_bw W memF (TA_g_cfg + 56) 4
    ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
        mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32) ->
  cf_bw W memF TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1) ->
  cf_bw W memF TA_g_now 8 1000000 -> cf_bw W memF TA_g_fail_next 1 0 ->
  cf_bw W memF TA_g_last_counter 4 0 ->
  rdword (aview segs (w_H W) memF) (lc_sp1 cx + 120) = Some (transport_hi 8) ->
  rdword (aview segs (w_H W) memF) (lc_sp1 cx + 176) = Some (transport_hi 9) ->
  rdword (aview segs (w_H W) memF) (lc_sp1 cx + 160) = Some (transport_hi 10) ->
  rdword (aview segs (w_H W) memF) (lc_sp1 cx + 48) = Some (transport_hi 11) ->
  cf_regs cx regsF ->
  YK11.getr regsF 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regsF 25 27 (IOK.prologue_cursor (l_pl cx)) ->
  @lc_st_scal rc B MT cx W (lc_cfg cx LO_SCAL regsF memF mdF).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regsF memF mdF LAWS HB HC HSP HFS HIO HMT HW0 ECD HTW
  HJ KV GP H0 H6 H12 H16 H20 H24 H28 H32 H36 H40 H44 H48 H52 H56 HR HN HF HL
  SP120 SP176 SP160 SP48 HRG R22 HCUR.
destruct (cf_apart cx ly' S' W regs0 mem0 md0 0 LAWS HB HC) as (AP & _).
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
pose proof HC as (_ & _ & _ & _ & C2 & C8 & C9 & C3 & C4 & _).
exists ly', S', regsF, memF, mdF, Bw0, B1.
split; [reflexivity|].
split.
{ split; [exact HJ|].
  exact (cf_rest_step cx ly' S' W regs0 mem0 md0 0 regsF memF LAWS HB HC
    (eq_trans G2 (eq_sym C2)) (eq_trans G8 (eq_sym C8)) (eq_trans G9 (eq_sym C9))
    (eq_trans G3 (eq_sym C3)) (eq_trans G4 (eq_sym C4)) KV GP). }
split; [exact (conj G18 G26)|].
(* the spill slots: 128 and 152 are kept, the four pages are the run's *)
split.
{ pose proof HSP as HSP'. unfold lc_spills, lf_spill_sm in HSP'.
  inversion HSP' as [|q1 r1 Q128 HSP2]; subst. inversion HSP2 as [|q2 r2 Q152 _]; subst.
  cbn [fst snd] in Q128, Q152.
  unfold lc_spills, lf_spill_scal, lf_spill_sm.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - rewrite (rdword_ext (aview segs (w_H W) mem0) (aview segs (w_H W) memF) (lc_sp1 cx + 128))
      by (intros j Hj; destruct (AP (lc_sp1 cx + 128 + j) ltac:(right; right; right; right; left; lia))
            as [Hw Hr]; exact (KV _ Hr Hw)).
    exact Q128.
  - rewrite (rdword_ext (aview segs (w_H W) mem0) (aview segs (w_H W) memF) (lc_sp1 cx + 152))
      by (intros j Hj; destruct (AP (lc_sp1 cx + 152 + j) ltac:(right; right; right; right; right; lia))
            as [Hw Hr]; exact (KV _ Hr Hw)).
    exact Q152.
  - exact SP120.
  - exact SP176.
  - exact SP160.
  - exact SP48. }
(* the frame's shadow and io are kept *)
split.
{ apply (lc_fsh_kept cx (aview segs (w_H W) mem0)); [|exact HFS].
  intros a Ha. destruct (AP a ltac:(right; right; right; left; lia)) as [Hw Hr]. exact (KV _ Hr Hw). }
split.
{ unfold lc_io in *. apply (lc_garr8_kept (w_H W) (w_H W) mem0 memF (lc_F cx + 176) _); [|exact HIO].
  intros j Hj.
  lazymatch type of Hj with
  | 0 <= j < Z.of_nat (length ?l) =>
      let L := eval vm_compute in (Z.of_nat (length l)) in change (0 <= j < L) in Hj
  end.
  destruct (AP (lc_F cx + 176 + j) ltac:(right; left; unfold LF_FBYTES in *; lia)) as [Hw Hr].
  exact (KV _ Hr Hw). }
split; [exact HMT|].
split; [exact HCUR|].
split; [exact R22|].
split; [exact G21|].
split; [exact G20|].
split; [exact HW0|].
split; [exact ECD|].
rewrite cf_scal_eq.
exact (cf_world_at cx ly' S' W regs0 mem0 md0 B1 memF LAWS HB HC HTW KV
  H0 H6 H12 H16 H20 H24 H28 H32 H36 H40 H44 H48 H52 H56 HR HN HF HL).
Qed.



(* s11 pinned to the literal number of config bytes left. *)
Lemma cf_regs_pin : forall regs ex z, YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 z ->
  regs_ok (cf_E regs ex) (sr_set sr_atoms (Z_to_bv 5 27) (SLit z)) regs.
Proof.
intros regs ex z Hz r. destruct (bv_eqb r (Z_to_bv 5 27)) eqn:E.
- apply bv_eqb_eq in E. subst r. rewrite sr_get_set_same by (vm_compute; reflexivity).
  cbn [sv_denot]. exact Hz.
- rewrite sr_get_set_other by (intros ->; rewrite bv_eqb_refl in E; discriminate).
  exact (regs_ok_Eimg_Ereg regs ex r).
Qed.

Lemma cf_facts : forall (cx : lcx) regs ex k (bs : list Z),
  YK11.getr regs 9 = w64 (lc_sp1 cx) -> 2 ^ 46 <= lc_sp1 cx <= 2 ^ 47 -> lc_sp1 cx mod 32 = 0 ->
  YK11.getr regs 19 = w64 (l_p cx + 1) -> 4096 <= l_p cx + 1 <= 140737479966720 ->
  YK11.getr regs 21 = w64 TA_g_cfg ->
  YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  (forall j, (j < k)%nat -> bv_unsigned (ew (cf_E regs ex) (32 + j)) = nth j bs 0) ->
  (forall j, (j < k)%nat -> 0 <= nth j bs 0 < 256) ->
  facts_ok (cf_E regs ex) (mkFacts (cf_atoms k) [] []).
Proof.
intros cx regs ex k bs R9 Hsp Hsp32 R19 Hp R21 R23 R26 Hden Hrng.
pose proof (cf_flags_rng (l_pl cx)) as HFL.
assert (U9 : bv_unsigned (ew (cf_E regs ex) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs ex 9%nat 9%bv eq_refl), R9; apply cf_u64; lia).
assert (U19 : bv_unsigned (ew (cf_E regs ex) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs ex 19%nat 19%bv eq_refl), R19; apply cf_u64; lia).
assert (U21 : bv_unsigned (ew (cf_E regs ex) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs ex 21%nat 21%bv eq_refl), R21; apply cf_u64; unfold TA_g_cfg; lia).
assert (U23 : bv_unsigned (ew (cf_E regs ex) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs ex 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs ex) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs ex 26%nat 26%bv eq_refl), R26; apply cf_u64; unfold SHADOW_OFF; lia).
pose proof (cf_E_hi regs ex 8%nat ltac:(lia)) as U8h.
pose proof (cf_E_hi regs ex 9%nat ltac:(lia)) as U9h.
pose proof (cf_E_hi regs ex 10%nat ltac:(lia)) as U10h.
pose proof (cf_E_hi regs ex 11%nat ltac:(lia)) as U11h.
split; [|split; [exact I | exact I]].
unfold cf_atoms. apply cf_atoms_app.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite ?U9, ?U19, ?U21, ?U23, ?U26, ?U8h, ?U9h, ?U10h, ?U11h, ?Z.pow_0_r, ?Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end;
    try exact I; try reflexivity;
    try (first [change (2 ^ 5) with 32 | idtac];
         first [unfold TA_g_cfg, SHADOW_OFF in * | idtac]; lia).
- apply cf_atoms_bytes. intros j Hj. apply in_seq in Hj.
  rewrite (Hden j ltac:(lia)). pose proof (Hrng j ltac:(lia)). lia.
Qed.

(* The seat of the run with no config byte: only the written regions. *)
Lemma cf_seat0 : forall (cx : lcx) ly' S' (W : world segs) regs mem md (ex : list word) sr pc,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md ->
  regs_ok (cf_E regs ex) sr regs ->
  facts_ok (cf_E regs ex) (mkFacts cf_atoms0 [] []) ->
  YK11.getr regs 9 = w64 (lc_sp1 cx) -> YK11.getr regs 21 = w64 TA_g_cfg ->
  @st_ok_pi segs VAL (l_fx cx) (cf_E regs ex)
    (mkSS pc sr cf_wregs None (mkFacts cf_atoms0 [] []))
    (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros cx ly' S' W regs mem md ex sr pc LAWS HB HC HJ HRO HFO R9 R21.
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
assert (U9 : bv_unsigned (ew (cf_E regs ex) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs ex 9%nat 9%bv eq_refl), R9; apply cf_u64; lia).
assert (U21 : bv_unsigned (ew (cf_E regs ex) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs ex 21%nat 21%bv eq_refl), R21; apply cf_u64; unfold TA_g_cfg; lia).
pose proof (cf_E_hi regs ex 8%nat ltac:(lia)) as U8h.
pose proof (cf_E_hi regs ex 9%nat ltac:(lia)) as U9h.
pose proof (cf_E_hi regs ex 10%nat ltac:(lia)) as U10h.
pose proof (cf_E_hi regs ex 11%nat ltac:(lia)) as U11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in U8h. rewrite EH9 in U9h. rewrite EH10 in U10h. rewrite EH11 in U11h.
assert (Hpres : forall a, lc_sp1 cx <= a < lc_sp1 cx + 184 -> apresent (w_H W) mem a).
{ intros a Ha. apply (SlostHead.slh_jpres B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). unfold LLVMF_STK in *. lia. }
rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full (l_fx cx) rc transport_listing PI_transport).
- exact HRO.
- vm_compute. reflexivity.
- unfold cf_wregs, cf_rg_cfg, cf_rg_sp48, cf_rg_sp120, cf_rg_sp160, cf_rg_sp176, cf_rg_raw, cf_rg_now,
    cf_rg_fail, cf_rg_last.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite ?U21, ?U9, ?U8h, ?U9h, ?U10h, ?U11h.
  + split; [unfold TA_g_cfg; lia|]. split; [unfold TA_g_cfg; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_g_cfg + o) G_HARNESS_rw). apply cf_cfg_inG. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (6157588 + o) G_HARNESS_rw).
    apply cf_glob_inG. left. unfold TA_g_raw. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (6157596 + o) G_HARNESS_rw).
    apply cf_glob_inG. right; left. unfold TA_g_now. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (6157652 + o) G_HARNESS_rw).
    apply cf_glob_inG. right; right; left. unfold TA_g_fail_next. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (6157672 + o) G_HARNESS_rw).
    apply cf_glob_inG. right; right; right. unfold TA_g_last_counter. lia.
- apply pairwise_disjoint_of_extents.
  unfold cf_wregs, cf_rg_cfg, cf_rg_sp48, cf_rg_sp120, cf_rg_sp160, cf_rg_sp176, cf_rg_raw,
    cf_rg_now, cf_rg_fail, cf_rg_last, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite ?U21, ?U9, ?U8h, ?U9h, ?U10h, ?U11h.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold TA_g_cfg in *. repeat split; first [exact I | lia].
- exact HFO.
Qed.

Lemma cf_facts0 : forall (cx : lcx) regs ex,
  YK11.getr regs 9 = w64 (lc_sp1 cx) -> 2 ^ 46 <= lc_sp1 cx <= 2 ^ 47 -> lc_sp1 cx mod 32 = 0 ->
  YK11.getr regs 21 = w64 TA_g_cfg ->
  YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  facts_ok (cf_E regs ex) (mkFacts cf_atoms0 [] []).
Proof.
intros cx regs ex R9 Hsp Hsp32 R21 R23 R26.
pose proof (cf_flags_rng (l_pl cx)) as HFL.
assert (U9 : bv_unsigned (ew (cf_E regs ex) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs ex 9%nat 9%bv eq_refl), R9; apply cf_u64; lia).
assert (U21 : bv_unsigned (ew (cf_E regs ex) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs ex 21%nat 21%bv eq_refl), R21; apply cf_u64; unfold TA_g_cfg; lia).
assert (U23 : bv_unsigned (ew (cf_E regs ex) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs ex 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs ex) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs ex 26%nat 26%bv eq_refl), R26; apply cf_u64; unfold SHADOW_OFF; lia).
pose proof (cf_E_hi regs ex 8%nat ltac:(lia)) as U8h.
pose proof (cf_E_hi regs ex 9%nat ltac:(lia)) as U9h.
pose proof (cf_E_hi regs ex 10%nat ltac:(lia)) as U10h.
pose proof (cf_E_hi regs ex 11%nat ltac:(lia)) as U11h.
split; [|split; [exact I | exact I]].
cbn [f_atoms]. unfold cf_atoms0. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite ?U9, ?U21, ?U23, ?U26, ?U8h, ?U9h, ?U10h, ?U11h, ?Z.pow_0_r, ?Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end;
  try exact I; try reflexivity;
  try (first [change (2 ^ 5) with 32 | idtac];
       first [unfold TA_g_cfg, SHADOW_OFF in * | idtac]; lia).
Qed.


(* A config word of the run's g_cfg region, at a case where every byte beyond the cursor is zero. *)
Ltac cf_zs Hz :=
  rewrite ?(Hz 0 ltac:(lia)), ?(Hz 1 ltac:(lia)), ?(Hz 2 ltac:(lia)), ?(Hz 3 ltac:(lia)),
          ?(Hz 4 ltac:(lia)), ?(Hz 5 ltac:(lia)), ?(Hz 6 ltac:(lia)), ?(Hz 7 ltac:(lia)),
          ?(Hz 8 ltac:(lia)), ?(Hz 9 ltac:(lia)), ?(Hz 10 ltac:(lia)), ?(Hz 11 ltac:(lia)),
          ?(Hz 12 ltac:(lia)), ?(Hz 13 ltac:(lia)).
Ltac cf_lit_rng := cbn [Z.of_N]; split; [vm_compute; discriminate | vm_compute; reflexivity].
Ltac cf_f0 Hz RG U21 off e :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj; refine (cf_vb _ _ _ 4 _ _ j Hj);
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ off 4%N e _ RG U21 _ _ _ _);
  [ cbn [In]; tauto | cf_zs Hz; cf_rval | cf_zs Hz; cf_lit_rng | cbn; lia ].
(* A scalar global of the run, at the page atom n whose value is b. *)
Ltac cf_gl RG U n off wn wN e tac :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj; refine (cf_vb _ _ _ wn _ _ j Hj);
  refine (can_field_of_region _ _ n _ _ _ _ _ _ off wN e _ RG U _ _ _ _);
  [ cbn [In]; tauto | tac | cf_lit_rng | cbn; lia ].
(* A spill slot of the run: the page the prologue stores. *)
Ltac cf_sp RG U9 off e :=
  apply AF0x.val_mem_rdword; [split; [vm_compute; discriminate | vm_compute; reflexivity]|];
  refine (can_field_of_region _ _ 9%nat _ _ _ _ _ _ off 8%N e _ RG U9 _ _ _ _);
  [ cbn [In]; tauto | cf_rval | cf_lit_rng | cbn; lia ].

(* The cursor after the flags byte of a non-empty input. *)
Lemma cf_c1_pos : forall D, TOP.fi_n (lc_c1 D) <> 0 ->
  TOP.fi_off (lc_c1 D) = 1 /\ TOP.fi_n (lc_c1 D) = Z.of_nat (length D) - 1 /\ 0 < Z.of_nat (length D).
Proof.
intros D H. unfold lc_c1, TOP.fuzz_u8_m, TOP.fuzz_in_m in *. cbn [TOP.fi_n TOP.fi_off] in *.
destruct (Z.eqb_spec (Z.of_nat (length D)) 0) as [E | E]; cbn [fst snd TOP.fi_off TOP.fi_n] in *.
- lia.
- pose proof (Nat2Z.is_nonneg (length D)). repeat split; lia.
Qed.

(* The byte atoms of a seat: the extra valuation holds the cursor's bytes. *)
Lemma cf_ex_val : forall regs (bs : list Z) j, (j < 200)%nat -> 0 <= nth j bs 0 < 256 ->
  bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (32 + j)) = nth j bs 0.
Proof.
intros regs bs j Hj Hr. rewrite (cf_E_x regs _ j Hj).
rewrite (map_nth (fun v : Z => Z_to_bv 64 v) bs 0 j). apply cf_u64. lia.
Qed.

(* Byte i after the cursor is the input's byte i + 1. *)
Lemma cf_in_bytes : forall (cx : lcx) ly' S' (W : world segs) regs mem md i,
  @lc_core rc B cx ly' S' W regs mem md 0 -> (S i < length (l_pl cx))%nat ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat i) 1 (cf_cb (l_pl cx) (Z.of_nat i)).
Proof.
intros cx ly' S' W regs mem md i HC Hi.
destruct (cf_rest_of cx ly' S' W regs mem md 0 HC)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HPAY & _)).
assert (Hlen : (S i < length (map (fun b : byte => bv_unsigned b) (l_pl cx)))%nat)
  by (rewrite length_map; exact Hi).
destruct (HPAY (S i) Hlen) as (V & Hb).
pose proof (inj_lt _ _ Hi) as HiZ. rewrite Nat2Z.inj_succ in HiZ.
pose proof (Nat2Z.is_nonneg i) as Hi0.
assert (Hc : TOP.fi_n (lc_c1 (l_pl cx)) <> 0).
{ unfold lc_c1, TOP.fuzz_u8_m, TOP.fuzz_in_m. cbn [TOP.fi_n TOP.fi_off].
  destruct (Z.eqb_spec (Z.of_nat (length (l_pl cx))) 0); cbn [fst snd TOP.fi_n]; lia. }
destruct (cf_c1_pos (l_pl cx) Hc) as (Coff & Cn & _).
assert (EV : cf_cb (l_pl cx) (Z.of_nat i) = nth (S i) (map (fun b : byte => bv_unsigned b) (l_pl cx)) 0).
{ unfold cf_cb, cf_b. rewrite Coff, Cn.
  rewrite (proj2 (Z.ltb_lt (Z.of_nat i) (Z.of_nat (length (l_pl cx)) - 1)) ltac:(lia)).
  unfold DSpec.at8, DSpec.bz.
  replace (Z.to_nat (1 + Z.of_nat i)) with (S i) by lia.
  rewrite <- (map_nth (fun b : byte => bv_unsigned b) (l_pl cx) (DSpec.b8 0) (S i)).
  change (bv_unsigned (DSpec.b8 0)) with 0. reflexivity. }
rewrite EV. replace (l_p cx + 1 + Z.of_nat i) with (l_p cx + Z.of_nat (S i)) by lia. exact V.
Qed.
(* The input block is addressable, and its k bytes at the cursor make the run's shadow entry. *)
Lemma cf_ra_blk : forall (cx : lcx) ly' S' (W : world segs) regs mem md,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W regs mem md 0 ->
  0 < l_n cx -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF (l_p cx) (l_n cx).
Proof.
intros cx ly' S' W regs mem md LAWS HB HC Hn0.
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N12 & HAR).
destruct (N12 Hn0) as (Hin & _).
destruct (al_shadow _ _ LAWS ly' S' W mem md (l_p cx) (l_n cx) HAR Hin) as (Hbs & _).
assert (RQ : req_size (l_n cx) = l_n cx)
  by (unfold req_size; destruct (Z.eqb_spec (l_n cx) 0); lia).
eapply block_shadow_range; [exact Hbs | lia | rewrite RQ; lia].
Qed.

Lemma cf_shok : forall (cx : lcx) ly' S' (W : world segs) regs mem md ex k,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W regs mem md 0 ->
  0 < l_n cx -> Z.of_nat k <= l_n cx - 1 ->
  bv_unsigned (ew (cf_E regs ex) 19) = l_p cx + 1 ->
  bv_unsigned (ew (cf_E regs ex) 26) = SHADOW_OFF ->
  sh_ok segs cf_Bx (cf_SH k) (cf_E regs ex) (mrestrict (w_H W) mem).
Proof.
intros cx ly' S' W regs mem md ex k LAWS HB HC Hn0 Hk U19 U26.
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N12 & HAR).
destruct (N12 Hn0) as (_ & Gp4 & Gpc & _ & Gapp & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (Nat2Z.is_nonneg k) as Hk0.
unfold sh_ok, cf_SH. constructor; [|constructor].
apply (shent_ok_of_range segs (w_H W) mem (cf_E regs ex) cf_Bx 19 (l_p cx) (l_n cx) (l_p cx + 1) 0 (Z.of_nat k)
  (cf_ra_blk cx ly' S' W regs mem md LAWS HB HC Hn0)).
- unfold U, cf_Bx. cbn [sv_denot]. rewrite U26, Z.add_0_r. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia.
- unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. lia.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* The two bounds the chunk values need. *)
Lemma cf_m32 : forall v, 0 <= v mod 2 ^ 32 < 2 ^ (8 * Z.of_N 4).
Proof. intros v. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). apply Z.mod_pos_bound. lia. Qed.
Lemma cf_m8 : forall v, 0 <= v mod 8 < 2 ^ (8 * Z.of_N 4).
Proof.
intros v. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
pose proof (Z.mod_pos_bound v 8 ltac:(lia)). lia.
Qed.

(* `andi a1, s3, 7` of a cursor one past an eight-aligned block, against a shadow byte in (1, 8): the branch to the
   report call 0x82b70 is not taken (the port of seg_hdr.v lh_bge, 50e228257540:229). *)
Lemma cf_land7g : forall x, 0 <= x < 2 ^ 64 -> zalu64 ALU_AND x 7 = x mod 8.
Proof.
intros x Hx. unfold zalu64, zalu_raw, zcanon, M64.
rewrite (Z.mod_small x (2 ^ 64)) by lia. rewrite (Z.mod_small 7 (2 ^ 64)) by lia.
replace 7 with (Z.ones 3) by reflexivity. rewrite Z.land_ones by lia.
change (2 ^ 3) with 8. rewrite (Z.mod_small (x mod 8) (2 ^ 64)); [reflexivity|].
pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
Qed.

Lemma cf_bge : forall E pa sb b, bv_unsigned (ew E 19) = pa -> 0 <= pa < 2 ^ 47 -> pa mod 8 = 1 ->
  bv_unsigned (ew E 47) = sb -> 1 < sb < 8 ->
  branch_taken BC_GE (sv_denot E (SAlu ALU_AND (SOff 19 0) (SLit 7))) (sv_denot E (SOff 47 0)) = b ->
  b = false.
Proof.
intros E pa sb b U19 Hpa Hm U47 Hsb <-.
rewrite (cf_den_alu E ALU_AND (SOff 19 0) (SLit 7) (pa + 0) 7
  (cf_den_off E 19 0 pa U19) (cf_den_lit E 7)).
rewrite (cf_den_off E 47 0 sb U47).
rewrite Z.add_0_r. rewrite (cf_land7g pa ltac:(lia)), Hm.
assert (Hc : sb = 2 \/ sb = 3 \/ sb = 4 \/ sb = 5 \/ sb = 6 \/ sb = 7) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity.
Qed.

(* `beqz` of an atom holding v (the port of seg_hdr.v lh_beqz, 50e228257540:216). *)
Lemma cf_beqz : forall E (m : nat) v b, bv_unsigned (ew E m) = v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff m 0)) (sv_denot E (SLit 0)) = b -> (v =? 0) = b.
Proof.
intros E m v b Hm Hv Hb. rewrite <- Hb.
rewrite (cf_den_off E m 0 v Hm), (cf_den_lit E 0), Z.add_0_r.
cbn [branch_taken]. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 10. The run of the empty cursor: +0x214 .. +0x318 with s11 = 0      *)
(* ------------------------------------------------------------------ *)

Lemma cf_case0 : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md -> cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_bl W mem (TA_g_cfg + 0) TC.HOST -> cf_bl W mem (TA_g_cfg + 6) TC.DESK ->
  cf_bw W mem (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W mem (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W mem (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> TOP.fi_n (lc_c1 (l_pl cx)) = 0 ->
  SRr segs W (lc_cfg cx CF_RC2 regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regs mem md HP HB HC0 HSP HFS HIO HMT HW0 ECD HTW
  HC HJ KV GP H0 H6 H12 H16 H20 HRG R23 R22 HCUR Hk0.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
assert (Hz : forall j, 0 <= j -> cf_cb (l_pl cx) j = 0).
{ intros j Hj. unfold cf_cb, cf_b. rewrite Hk0. destruct (Z.ltb_spec j 0); [lia | reflexivity]. }
assert (EPC : w64 (transport_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (HEI : img_env VAL A_LIM (cf_E regs [])) by apply cf_E_img.
assert (R27 : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 0) by (rewrite C27, Hk0; reflexivity).
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs []) cf_ss0
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_RC2)) mem (YK11.seg_rom segs)))).
{ unfold cf_ss0. apply (cf_seat0 cx ly' S' W regs mem md [] _ CF_RC2 LAWS HB HC HJ).
  - apply cf_regs_pin. exact R27.
  - exact (cf_facts0 cx regs [] G9 ltac:(lia) N3 G21 R23 G26).
  - exact G9.
  - exact G21. }
assert (SHOK : sh_ok segs cf_Bx (@nil shent) (cf_E regs []) (mrestrict (w_H W) mem)) by constructor.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x318.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  assert (V21 : bv_unsigned (ew (cf_E regs []) 21) = TA_g_cfg)
    by (rewrite (cf_E_reg regs [] 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
  assert (V9 : bv_unsigned (ew (cf_E regs []) 9) = lc_sp1 cx)
    by (rewrite (cf_E_reg regs [] 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
  pose proof (cf_E_hi regs [] 8%nat ltac:(lia)) as V8h. change (A_HI 8) with 408%nat in V8h.
  pose proof (cf_E_hi regs [] 9%nat ltac:(lia)) as V9h. change (A_HI 9) with 409%nat in V9h.
  pose proof (cf_E_hi regs [] 10%nat ltac:(lia)) as V10h. change (A_HI 10) with 410%nat in V10h.
  pose proof (cf_E_hi regs [] 11%nat ltac:(lia)) as V11h. change (A_HI 11) with 411%nat in V11h.
  assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
  assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
  assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
  assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
  rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V21 in Ha;
     apply cf_cfg_inG; lia|].
  apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|].
  apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|].
  apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|].
  apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V8h in Ha;
     apply cf_glob_inG; left; unfold TA_g_raw; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9h in Ha;
     apply cf_glob_inG; right; left; unfold TA_g_now; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V10h in Ha;
     apply cf_glob_inG; right; right; left; unfold TA_g_fail_next; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V11h in Ha;
     apply cf_glob_inG; right; right; right; unfold TA_g_last_counter; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
cf_ag (cf_E regs []).
assert (V21 : bv_unsigned (ew (cf_E regs []) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs [] 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V9 : bv_unsigned (ew (cf_E regs []) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs [] 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
pose proof (cf_E_hi regs [] 8%nat ltac:(lia)) as V8h. change (A_HI 8) with 408%nat in V8h.
pose proof (cf_E_hi regs [] 9%nat ltac:(lia)) as V9h. change (A_HI 9) with 409%nat in V9h.
pose proof (cf_E_hi regs [] 10%nat ltac:(lia)) as V10h. change (A_HI 10) with 410%nat in V10h.
pose proof (cf_E_hi regs [] 11%nat ltac:(lia)) as V11h. change (A_HI 11) with 411%nat in V11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
(* the bytes outside the segment's writes are the cut's *)
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wrun cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hw. apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wrun cx) HFr); [|exact Ha | exact Hw].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin. cbn [base_val] in Hx.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-|]); [..|destruct Hin].
  - cbn [base_val] in Hx; rewrite V21 in Hx. unfold cf_wrun. left. unfold TA_g_cfg in *. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; right; right. lia.
  - cbn [base_val] in Hx; rewrite V8h in Hx. unfold cf_wrun. right; left. unfold TA_g_raw. lia.
  - cbn [base_val] in Hx; rewrite V9h in Hx. unfold cf_wrun. right; right; left. unfold TA_g_now. lia.
  - cbn [base_val] in Hx; rewrite V10h in Hx. unfold cf_wrun. right; right; right; left. unfold TA_g_fail_next. lia.
  - cbn [base_val] in Hx; rewrite V11h in Hx. unfold cf_wrun. right; right; right; right; left. unfold TA_g_last_counter. lia. }
assert (KA : cf_KV cx W mem0 (ms_mem ms)).
{ intros a Ha Hw. rewrite (KF a Ha ltac:(intros C; apply Hw; unfold cf_wrun, cf_wr in *; lia)).
  exact (KV a Ha Hw). }
assert (GA : cf_GP W mem0 (ms_mem ms))
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GP a Ha))).
(* the nine config words, the four globals and the four spill slots the run wrote *)
pose proof (YC4b.st_ok_region_nth (cf_E regs []) _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth (cf_E regs []) _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (YC4b.st_ok_region_nth (cf_E regs []) _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (YC4b.st_ok_region_nth (cf_E regs []) _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (YC4b.st_ok_region_nth (cf_E regs []) _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (YC4b.st_ok_region_nth (cf_E regs []) _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (YC4b.st_ok_region_nth (cf_E regs []) _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (YC4b.st_ok_region_nth (cf_E regs []) _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (YC4b.st_ok_region_nth (cf_E regs []) _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8.
assert (F24 : cf_bw W (ms_mem ms) (TA_g_cfg + 24) 4
  ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32)) by (cf_f0 Hz RG0 V21 24 (SLit 1)).
assert (F28 : cf_bw W (ms_mem ms) (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32))
  by (cf_f0 Hz RG0 V21 28 (SLit 1)).
assert (F32 : cf_bw W (ms_mem ms) (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8))
  by (cf_f0 Hz RG0 V21 32 (SLit 0)).
assert (F36 : cf_bw W (ms_mem ms) (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4))
  by (cf_f0 Hz RG0 V21 36 (SLit 0)).
assert (F40 : cf_bw W (ms_mem ms) (TA_g_cfg + 40) 4
  ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32)) by (cf_f0 Hz RG0 V21 40 (SLit 1)).
assert (F44 : cf_bw W (ms_mem ms) (TA_g_cfg + 44) 4
  ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32)) by (cf_f0 Hz RG0 V21 44 (SLit 1)).
assert (F48 : cf_bw W (ms_mem ms) (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10))
  by (cf_f0 Hz RG0 V21 48 (SLit 0)).
assert (F52 : cf_bw W (ms_mem ms) (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32))
  by (cf_f0 Hz RG0 V21 52 (SLit 1)).
assert (F56 : cf_bw W (ms_mem ms) (TA_g_cfg + 56) 4
  ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
      mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)) by (cf_f0 Hz RG0 V21 56 (SLit 24)).
assert (V23 : bv_unsigned (ew (cf_E regs []) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs [] 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
assert (GRAW : cf_bw W (ms_mem ms) TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 408%nat _ _ _ _ _ _ (-1076) 4%N
    (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 60)) (SLit 63)) _ RG5 V8h _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 3)
      ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (GNOW : cf_bw W (ms_mem ms) TA_g_now 8 1000000)
  by (cf_gl RG6 V9h 409%nat (-1052) 8%nat 8%N (SLit 1000000) ltac:(cf_rval)).
assert (GFAIL : cf_bw W (ms_mem ms) TA_g_fail_next 1 0)
  by (cf_gl RG7 V10h 410%nat (-1076) 1%nat 1%N (SLit 0) ltac:(cf_rval)).
assert (GLAST : cf_bw W (ms_mem ms) TA_g_last_counter 4 0)
  by (cf_gl RG8 V11h 411%nat (-1064) 4%nat 4%N (SLit 0) ltac:(cf_rval)).
assert (SP48 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 48) = Some (transport_hi 11))
  by (cf_sp RG1 V9 48 (SOff 411 0)).
assert (SP120 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 120) = Some (transport_hi 8))
  by (cf_sp RG2 V9 120 (SOff 408 0)).
assert (SP160 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 160) = Some (transport_hi 10))
  by (cf_sp RG3 V9 160 (SOff 410 0)).
assert (SP176 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 176) = Some (transport_hi 9))
  by (cf_sp RG4 V9 176 (SOff 409 0)).
(* the kept g_cfg head *)
assert (KG : forall a, TA_g_cfg <= a < TA_g_cfg + 24 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply KF; [unfold TA_g_cfg in *; lia|].
  unfold cf_wrun, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
(* the registers *)
assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs [] _ HS _ _ r Hr);
    [apply cf_agree; assumption | vm_compute; reflexivity]. }
cf_rd HS (Z_to_bv 5 25) (YK11.getr regs 19) Y25
  ltac:(cbn [sv_denot];
        rewrite (cf_E_reg regs [] 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cf_rd HS (Z_to_bv 5 27) (w64 0) Y27 ltac:(reflexivity).
pmkst HS.
apply SRr_ret.
apply (cf_close cx ly' S' W regs0 mem0 md0 Bw0 B1 (ms_regs ms) (ms_mem ms) md1 LAWS HB HC0 HSP HFS HIO HMT
  HW0 ECD HTW HJ KA GA).
- intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H0 i Hi).
- intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H6 i Hi).
- intros j Hj. rewrite (KG (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H12 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H16 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H20 j Hj).
- exact F24.
- exact F28.
- exact F32.
- exact F36.
- exact F40.
- exact F44.
- exact F48.
- exact F52.
- exact F56.
- exact GRAW.
- exact GNOW.
- exact GFAIL.
- exact GLAST.
- exact SP120.
- exact SP176.
- exact SP160.
- exact SP48.
- unfold cf_regs.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
    (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
    (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
  exact HRG.
- rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- unfold lc_cur. rewrite cf_cursor. cbn [TOP.fi_off TOP.fi_n]. rewrite Hk0.
  change (Z.min 0 14) with 0. rewrite Z.add_0_r, Z.sub_0_r.
  split; [rewrite Y25; exact C19 | exact Y27].
Qed.

(* ------------------------------------------------------------------ *)
(* 11. The runs of a cursor with k config bytes: +0x22c .. +0x318      *)
(* ------------------------------------------------------------------ *)

Lemma cf_case1 : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md -> cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_bl W mem (TA_g_cfg + 0) TC.HOST -> cf_bl W mem (TA_g_cfg + 6) TC.DESK ->
  cf_bw W mem (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W mem (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W mem (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> TOP.fi_n (lc_c1 (l_pl cx)) = 1 ->
  SRr segs W (lc_cfg cx CF_SC regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regs mem md HP HB HC0 HSP HFS HIO HMT HW0 ECD HTW
  HC HJ KV GP H0 H6 H12 H16 H20 HRG R23 R22 HCUR Hk.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
destruct (cf_c1_pos (l_pl cx) ltac:(lia)) as (Coff & Cn & Clen).
assert (Hn0 : 0 < l_n cx) by lia.
assert (R19 : YK11.getr regs (Z_to_bv 5 19) = w64 (l_p cx + 1)) by (rewrite C19, Coff; reflexivity).
assert (R27 : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 1) by (rewrite C27, Hk; reflexivity).
assert (Hz : forall j, 1 <= j -> cf_cb (l_pl cx) j = 0).
{ intros j Hj. unfold cf_cb, cf_b. rewrite Hk.
  destruct (Z.ltb_spec j 1); [lia | reflexivity]. }
assert (HB0 : 0 <= cf_cb (l_pl cx) 0 < 256) by (unfold cf_cb; apply cf_b_rng).
set (bs := [cf_cb (l_pl cx) 0]).
assert (HBrng : forall j, (j < 1)%nat -> 0 <= nth j bs 0 < 256).
{ intros j Hj. unfold bs. destruct j as [|]; cbn [nth]; first [exact HB0 | exact HB0 | lia]. }
assert (HBval : forall j, (j < 1)%nat ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j bs 0)).
{ intros j Hj.
  replace (nth j bs 0) with (cf_cb (l_pl cx) (Z.of_nat j))
    by (unfold bs; destruct j as [|]; cbn [nth Z.of_nat]; reflexivity || lia).
  apply (cf_in_bytes cx ly' S' W regs mem md j HC). lia. }
assert (HBden : forall j, (j < 1)%nat ->
  bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (32 + j)) = nth j bs 0)
  by (intros j Hj; apply cf_ex_val; [lia | exact (HBrng j Hj)]).
assert (UB0 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 32)
  = cf_cb (l_pl cx) 0)
  by (pose proof (HBden 0%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (EPC : w64 (transport_text + CF_SC) = Z_to_bv 64 (BASE + CF_SC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (HEI : img_env VAL A_LIM (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))) by apply cf_E_img.
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (cf_ssp 1)
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_SC)) mem (YK11.seg_rom segs)))).
{ unfold cf_ssp. apply (cf_seat cx ly' S' W regs mem md _ 1 bs _ CF_SC _ LAWS HB HC HJ).
  - apply cf_regs_pin. exact R27.
  - exact (cf_facts cx regs _ 1 bs G9 ltac:(lia) N3 R19 ltac:(lia) G21 R23 G26 HBden HBrng).
  - exact G9.
  - exact R19.
  - exact G21.
  - exact Hn0.
  - lia.
  - exact HBden.
  - exact HBrng.
  - exact HBval. }
assert (U19 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs _ 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs _ 26%nat 26%bv eq_refl), G26; apply cf_u64; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs cf_Bx (cf_SH 1) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))
  (mrestrict (w_H W) mem))
  by exact (cf_shok cx ly' S' W regs mem md _ 1 LAWS HB HC Hn0 ltac:(lia) U19 U26).
assert (V21 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs _ 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs _ 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
assert (V23 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs _ 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 8%nat ltac:(lia)) as V8h.
change (A_HI 8) with 408%nat in V8h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 9%nat ltac:(lia)) as V9h.
change (A_HI 9) with 409%nat in V9h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 10%nat ltac:(lia)) as V10h.
change (A_HI 10) with 410%nat in V10h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 11%nat ltac:(lia)) as V11h.
change (A_HI 11) with 411%nat in V11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x318.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V21 in Ha;
     apply cf_cfg_inG; lia|].
  do 4 (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|]).
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V8h in Ha;
     apply cf_glob_inG; left; unfold TA_g_raw; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9h in Ha;
     apply cf_glob_inG; right; left; unfold TA_g_now; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V10h in Ha;
     apply cf_glob_inG; right; right; left; unfold TA_g_fail_next; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V11h in Ha;
     apply cf_glob_inG; right; right; right; unfold TA_g_last_counter; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
cf_ag (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)).
lazymatch goal with
| HA : env_agree 512 (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) ?ER |- _ =>
  assert (W21 : bv_unsigned (ew ER 21) = TA_g_cfg)
    by (first [ exact V21
              | rewrite <- (proj1 HA 21%nat ltac:(lia)); exact V21
              | rewrite (proj1 HA 21%nat ltac:(lia)); exact V21 ]);
  assert (W9 : bv_unsigned (ew ER 9) = lc_sp1 cx)
    by (first [ exact V9
              | rewrite <- (proj1 HA 9%nat ltac:(lia)); exact V9
              | rewrite (proj1 HA 9%nat ltac:(lia)); exact V9 ]);
  assert (W8h : bv_unsigned (ew ER 408) = 6157588)
    by (first [ exact V8h
              | rewrite <- (proj1 HA 408%nat ltac:(lia)); exact V8h
              | rewrite (proj1 HA 408%nat ltac:(lia)); exact V8h ]);
  assert (W9h : bv_unsigned (ew ER 409) = 6157596)
    by (first [ exact V9h
              | rewrite <- (proj1 HA 409%nat ltac:(lia)); exact V9h
              | rewrite (proj1 HA 409%nat ltac:(lia)); exact V9h ]);
  assert (W10h : bv_unsigned (ew ER 410) = 6157652)
    by (first [ exact V10h
              | rewrite <- (proj1 HA 410%nat ltac:(lia)); exact V10h
              | rewrite (proj1 HA 410%nat ltac:(lia)); exact V10h ]);
  assert (W11h : bv_unsigned (ew ER 411) = 6157672)
    by (first [ exact V11h
              | rewrite <- (proj1 HA 411%nat ltac:(lia)); exact V11h
              | rewrite (proj1 HA 411%nat ltac:(lia)); exact V11h ])
end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wrun cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hw. apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wrun cx) HFr); [|exact Ha | exact Hw].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-|]); [..|destruct Hin].
  - cbn [base_val] in Hx. lia.
  - cbn [base_val] in Hx; rewrite V21 in Hx. unfold cf_wrun. left. unfold TA_g_cfg in *. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; right. lia.
  - cbn [base_val] in Hx; rewrite V8h in Hx. unfold cf_wrun. right; left. unfold TA_g_raw. lia.
  - cbn [base_val] in Hx; rewrite V9h in Hx. unfold cf_wrun. right; right; left. unfold TA_g_now. lia.
  - cbn [base_val] in Hx; rewrite V10h in Hx. unfold cf_wrun.
    right; right; right; left. unfold TA_g_fail_next. lia.
  - cbn [base_val] in Hx; rewrite V11h in Hx. unfold cf_wrun.
    right; right; right; right; left. unfold TA_g_last_counter. lia. }
assert (KA : cf_KV cx W mem0 (ms_mem ms)).
{ intros a Ha Hw. rewrite (KF a Ha ltac:(intros C; apply Hw; unfold cf_wrun, cf_wr in *; lia)).
  exact (KV a Ha Hw). }
assert (GA : cf_GP W mem0 (ms_mem ms))
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GP a Ha))).
assert (KG : forall a, TA_g_cfg <= a < TA_g_cfg + 24 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply KF; [unfold TA_g_cfg in *; lia|].
  unfold cf_wrun, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 9 _ HS eq_refl) as RG9.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
assert (F24 : cf_bw W (ms_mem ms) (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 24 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 2 ltac:(lia)). rewrite (Hz 3 ltac:(lia)). cf_rval.
  -  rewrite (Hz 2 ltac:(lia)). rewrite (Hz 3 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F28 : cf_bw W (ms_mem ms) (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 28 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 1 ltac:(lia)). cf_rval.
  -  rewrite (Hz 1 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F32 : cf_bw W (ms_mem ms) (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 32 4%N (SAlu ALU_AND (SOff 32 0) (SLit 7)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f32 _ HB0). reflexivity.
  - apply cf_m8.
  - cbn. lia. }
assert (F36 : cf_bw W (ms_mem ms) (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 36 4%N (SLit 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 4 ltac:(lia)). cf_rval.
  -  rewrite (Hz 4 ltac:(lia)). cbn [Z.of_N]. lia.
  - cbn. lia. }
assert (F40 : cf_bw W (ms_mem ms) (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 40 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 5 ltac:(lia)). rewrite (Hz 6 ltac:(lia)). cf_rval.
  -  rewrite (Hz 5 ltac:(lia)). rewrite (Hz 6 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F44 : cf_bw W (ms_mem ms) (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 44 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 7 ltac:(lia)). rewrite (Hz 8 ltac:(lia)). cf_rval.
  -  rewrite (Hz 7 ltac:(lia)). rewrite (Hz 8 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F48 : cf_bw W (ms_mem ms) (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 48 4%N (SLit 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cf_rval.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cbn [Z.of_N]. lia.
  - cbn. lia. }
assert (F52 : cf_bw W (ms_mem ms) (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 52 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 11 ltac:(lia)). cf_rval.
  -  rewrite (Hz 11 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F56 : cf_bw W (ms_mem ms) (TA_g_cfg + 56) 4 ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
      mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 56 4%N (SLit 24) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). cf_rval.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (GRAW : cf_bw W (ms_mem ms) TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 408%nat _ _ _ _ _ _ (-1076) 4%N
    (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 60)) (SLit 63)) _ RG6 W8h _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 3)
      ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (GNOW : cf_bw W (ms_mem ms) TA_g_now 8 1000000)
  by (cf_gl RG7 W9h 409%nat (-1052) 8%nat 8%N (SLit 1000000) ltac:(cf_rval)).
assert (GFAIL : cf_bw W (ms_mem ms) TA_g_fail_next 1 0)
  by (cf_gl RG8 W10h 410%nat (-1076) 1%nat 1%N (SLit 0) ltac:(cf_rval)).
assert (GLAST : cf_bw W (ms_mem ms) TA_g_last_counter 4 0)
  by (cf_gl RG9 W11h 411%nat (-1064) 4%nat 4%N (SLit 0) ltac:(cf_rval)).
assert (SP48 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 48) = Some (transport_hi 11))
  by (cf_sp RG2 W9 48 (SOff 411 0)).
assert (SP120 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 120) = Some (transport_hi 8))
  by (cf_sp RG3 W9 120 (SOff 408 0)).
assert (SP160 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 160) = Some (transport_hi 10))
  by (cf_sp RG4 W9 160 (SOff 410 0)).
assert (SP176 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 176) = Some (transport_hi 9))
  by (cf_sp RG5 W9 176 (SOff 409 0)).
assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs (map (fun v : Z => Z_to_bv 64 v) bs) _ HS _ _ r Hr);
    [apply cf_agree; assumption | vm_compute; reflexivity]. }
cf_rd HS (Z_to_bv 5 25) (w64 (l_p cx + 1 + 1)) Y25
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; first [reflexivity | f_equal; lia]).
cf_rd HS (Z_to_bv 5 27) (w64 0) Y27 ltac:(reflexivity).
pmkst HS.
apply SRr_ret.
apply (cf_close cx ly' S' W regs0 mem0 md0 Bw0 B1 (ms_regs ms) (ms_mem ms) md1 LAWS HB HC0 HSP HFS HIO HMT
  HW0 ECD HTW HJ KA GA).
- intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H0 i Hi).
- intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H6 i Hi).
- intros j Hj. rewrite (KG (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H12 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H16 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H20 j Hj).
- exact F24.
- exact F28.
- exact F32.
- exact F36.
- exact F40.
- exact F44.
- exact F48.
- exact F52.
- exact F56.
- exact GRAW.
- exact GNOW.
- exact GFAIL.
- exact GLAST.
- exact SP120.
- exact SP176.
- exact SP160.
- exact SP48.
- unfold cf_regs.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
    (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
    (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
  exact HRG.
- rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- unfold lc_cur. rewrite cf_cursor. cbn [TOP.fi_off TOP.fi_n]. rewrite Coff.
  rewrite Hk. change (Z.min 1 14) with 1.
  split; [rewrite Y25; unfold w64; f_equal; lia | rewrite Y27; unfold w64; f_equal; lia].
Qed.

Lemma cf_case2 : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md -> cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_bl W mem (TA_g_cfg + 0) TC.HOST -> cf_bl W mem (TA_g_cfg + 6) TC.DESK ->
  cf_bw W mem (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W mem (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W mem (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> TOP.fi_n (lc_c1 (l_pl cx)) = 2 ->
  SRr segs W (lc_cfg cx CF_SC regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regs mem md HP HB HC0 HSP HFS HIO HMT HW0 ECD HTW
  HC HJ KV GP H0 H6 H12 H16 H20 HRG R23 R22 HCUR Hk.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
destruct (cf_c1_pos (l_pl cx) ltac:(lia)) as (Coff & Cn & Clen).
assert (Hn0 : 0 < l_n cx) by lia.
assert (R19 : YK11.getr regs (Z_to_bv 5 19) = w64 (l_p cx + 1)) by (rewrite C19, Coff; reflexivity).
assert (R27 : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 2) by (rewrite C27, Hk; reflexivity).
assert (Hz : forall j, 2 <= j -> cf_cb (l_pl cx) j = 0).
{ intros j Hj. unfold cf_cb, cf_b. rewrite Hk.
  destruct (Z.ltb_spec j 2); [lia | reflexivity]. }
assert (HB0 : 0 <= cf_cb (l_pl cx) 0 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB1 : 0 <= cf_cb (l_pl cx) 1 < 256) by (unfold cf_cb; apply cf_b_rng).
set (bs := [cf_cb (l_pl cx) 0; cf_cb (l_pl cx) 1]).
assert (HBrng : forall j, (j < 2)%nat -> 0 <= nth j bs 0 < 256).
{ intros j Hj. unfold bs. destruct j as [|[|]]; cbn [nth]; first [exact HB0 | exact HB0 | exact HB1 | lia]. }
assert (HBval : forall j, (j < 2)%nat ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j bs 0)).
{ intros j Hj.
  replace (nth j bs 0) with (cf_cb (l_pl cx) (Z.of_nat j))
    by (unfold bs; destruct j as [|[|]]; cbn [nth Z.of_nat]; reflexivity || lia).
  apply (cf_in_bytes cx ly' S' W regs mem md j HC). lia. }
assert (HBden : forall j, (j < 2)%nat ->
  bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (32 + j)) = nth j bs 0)
  by (intros j Hj; apply cf_ex_val; [lia | exact (HBrng j Hj)]).
assert (UB0 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 32)
  = cf_cb (l_pl cx) 0)
  by (pose proof (HBden 0%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB1 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 33)
  = cf_cb (l_pl cx) 1)
  by (pose proof (HBden 1%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (EPC : w64 (transport_text + CF_SC) = Z_to_bv 64 (BASE + CF_SC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (HEI : img_env VAL A_LIM (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))) by apply cf_E_img.
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (cf_ssp 2)
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_SC)) mem (YK11.seg_rom segs)))).
{ unfold cf_ssp. apply (cf_seat cx ly' S' W regs mem md _ 2 bs _ CF_SC _ LAWS HB HC HJ).
  - apply cf_regs_pin. exact R27.
  - exact (cf_facts cx regs _ 2 bs G9 ltac:(lia) N3 R19 ltac:(lia) G21 R23 G26 HBden HBrng).
  - exact G9.
  - exact R19.
  - exact G21.
  - exact Hn0.
  - lia.
  - exact HBden.
  - exact HBrng.
  - exact HBval. }
assert (U19 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs _ 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs _ 26%nat 26%bv eq_refl), G26; apply cf_u64; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs cf_Bx (cf_SH 2) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))
  (mrestrict (w_H W) mem))
  by exact (cf_shok cx ly' S' W regs mem md _ 2 LAWS HB HC Hn0 ltac:(lia) U19 U26).
assert (V21 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs _ 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs _ 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
assert (V23 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs _ 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 8%nat ltac:(lia)) as V8h.
change (A_HI 8) with 408%nat in V8h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 9%nat ltac:(lia)) as V9h.
change (A_HI 9) with 409%nat in V9h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 10%nat ltac:(lia)) as V10h.
change (A_HI 10) with 410%nat in V10h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 11%nat ltac:(lia)) as V11h.
change (A_HI 11) with 411%nat in V11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x318.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V21 in Ha;
     apply cf_cfg_inG; lia|].
  do 4 (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|]).
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V8h in Ha;
     apply cf_glob_inG; left; unfold TA_g_raw; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9h in Ha;
     apply cf_glob_inG; right; left; unfold TA_g_now; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V10h in Ha;
     apply cf_glob_inG; right; right; left; unfold TA_g_fail_next; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V11h in Ha;
     apply cf_glob_inG; right; right; right; unfold TA_g_last_counter; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
cf_ag (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)).
lazymatch goal with
| HA : env_agree 512 (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) ?ER |- _ =>
  assert (W21 : bv_unsigned (ew ER 21) = TA_g_cfg)
    by (first [ exact V21
              | rewrite <- (proj1 HA 21%nat ltac:(lia)); exact V21
              | rewrite (proj1 HA 21%nat ltac:(lia)); exact V21 ]);
  assert (W9 : bv_unsigned (ew ER 9) = lc_sp1 cx)
    by (first [ exact V9
              | rewrite <- (proj1 HA 9%nat ltac:(lia)); exact V9
              | rewrite (proj1 HA 9%nat ltac:(lia)); exact V9 ]);
  assert (W8h : bv_unsigned (ew ER 408) = 6157588)
    by (first [ exact V8h
              | rewrite <- (proj1 HA 408%nat ltac:(lia)); exact V8h
              | rewrite (proj1 HA 408%nat ltac:(lia)); exact V8h ]);
  assert (W9h : bv_unsigned (ew ER 409) = 6157596)
    by (first [ exact V9h
              | rewrite <- (proj1 HA 409%nat ltac:(lia)); exact V9h
              | rewrite (proj1 HA 409%nat ltac:(lia)); exact V9h ]);
  assert (W10h : bv_unsigned (ew ER 410) = 6157652)
    by (first [ exact V10h
              | rewrite <- (proj1 HA 410%nat ltac:(lia)); exact V10h
              | rewrite (proj1 HA 410%nat ltac:(lia)); exact V10h ]);
  assert (W11h : bv_unsigned (ew ER 411) = 6157672)
    by (first [ exact V11h
              | rewrite <- (proj1 HA 411%nat ltac:(lia)); exact V11h
              | rewrite (proj1 HA 411%nat ltac:(lia)); exact V11h ])
end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wrun cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hw. apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wrun cx) HFr); [|exact Ha | exact Hw].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-|]); [..|destruct Hin].
  - cbn [base_val] in Hx. lia.
  - cbn [base_val] in Hx; rewrite V21 in Hx. unfold cf_wrun. left. unfold TA_g_cfg in *. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; right. lia.
  - cbn [base_val] in Hx; rewrite V8h in Hx. unfold cf_wrun. right; left. unfold TA_g_raw. lia.
  - cbn [base_val] in Hx; rewrite V9h in Hx. unfold cf_wrun. right; right; left. unfold TA_g_now. lia.
  - cbn [base_val] in Hx; rewrite V10h in Hx. unfold cf_wrun.
    right; right; right; left. unfold TA_g_fail_next. lia.
  - cbn [base_val] in Hx; rewrite V11h in Hx. unfold cf_wrun.
    right; right; right; right; left. unfold TA_g_last_counter. lia. }
assert (KA : cf_KV cx W mem0 (ms_mem ms)).
{ intros a Ha Hw. rewrite (KF a Ha ltac:(intros C; apply Hw; unfold cf_wrun, cf_wr in *; lia)).
  exact (KV a Ha Hw). }
assert (GA : cf_GP W mem0 (ms_mem ms))
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GP a Ha))).
assert (KG : forall a, TA_g_cfg <= a < TA_g_cfg + 24 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply KF; [unfold TA_g_cfg in *; lia|].
  unfold cf_wrun, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 9 _ HS eq_refl) as RG9.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
assert (F24 : cf_bw W (ms_mem ms) (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 24 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 2 ltac:(lia)). rewrite (Hz 3 ltac:(lia)). cf_rval.
  -  rewrite (Hz 2 ltac:(lia)). rewrite (Hz 3 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F28 : cf_bw W (ms_mem ms) (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 28 4%N (SOff 33 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  apply cf_m32.
  - cbn. lia. }
assert (F32 : cf_bw W (ms_mem ms) (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 32 4%N (SAlu ALU_AND (SOff 32 0) (SLit 7)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f32 _ HB0). reflexivity.
  - apply cf_m8.
  - cbn. lia. }
assert (F36 : cf_bw W (ms_mem ms) (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 36 4%N (SLit 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 4 ltac:(lia)). cf_rval.
  -  rewrite (Hz 4 ltac:(lia)). cbn [Z.of_N]. lia.
  - cbn. lia. }
assert (F40 : cf_bw W (ms_mem ms) (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 40 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 5 ltac:(lia)). rewrite (Hz 6 ltac:(lia)). cf_rval.
  -  rewrite (Hz 5 ltac:(lia)). rewrite (Hz 6 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F44 : cf_bw W (ms_mem ms) (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 44 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 7 ltac:(lia)). rewrite (Hz 8 ltac:(lia)). cf_rval.
  -  rewrite (Hz 7 ltac:(lia)). rewrite (Hz 8 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F48 : cf_bw W (ms_mem ms) (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 48 4%N (SLit 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cf_rval.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cbn [Z.of_N]. lia.
  - cbn. lia. }
assert (F52 : cf_bw W (ms_mem ms) (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 52 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 11 ltac:(lia)). cf_rval.
  -  rewrite (Hz 11 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F56 : cf_bw W (ms_mem ms) (TA_g_cfg + 56) 4 ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
      mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 56 4%N (SLit 24) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). cf_rval.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (GRAW : cf_bw W (ms_mem ms) TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 408%nat _ _ _ _ _ _ (-1076) 4%N
    (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 60)) (SLit 63)) _ RG6 W8h _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 3)
      ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (GNOW : cf_bw W (ms_mem ms) TA_g_now 8 1000000)
  by (cf_gl RG7 W9h 409%nat (-1052) 8%nat 8%N (SLit 1000000) ltac:(cf_rval)).
assert (GFAIL : cf_bw W (ms_mem ms) TA_g_fail_next 1 0)
  by (cf_gl RG8 W10h 410%nat (-1076) 1%nat 1%N (SLit 0) ltac:(cf_rval)).
assert (GLAST : cf_bw W (ms_mem ms) TA_g_last_counter 4 0)
  by (cf_gl RG9 W11h 411%nat (-1064) 4%nat 4%N (SLit 0) ltac:(cf_rval)).
assert (SP48 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 48) = Some (transport_hi 11))
  by (cf_sp RG2 W9 48 (SOff 411 0)).
assert (SP120 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 120) = Some (transport_hi 8))
  by (cf_sp RG3 W9 120 (SOff 408 0)).
assert (SP160 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 160) = Some (transport_hi 10))
  by (cf_sp RG4 W9 160 (SOff 410 0)).
assert (SP176 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 176) = Some (transport_hi 9))
  by (cf_sp RG5 W9 176 (SOff 409 0)).
assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs (map (fun v : Z => Z_to_bv 64 v) bs) _ HS _ _ r Hr);
    [apply cf_agree; assumption | vm_compute; reflexivity]. }
cf_rd HS (Z_to_bv 5 25) (w64 (l_p cx + 1 + 2)) Y25
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; first [reflexivity | f_equal; lia]).
cf_rd HS (Z_to_bv 5 27) (w64 0) Y27 ltac:(reflexivity).
pmkst HS.
apply SRr_ret.
apply (cf_close cx ly' S' W regs0 mem0 md0 Bw0 B1 (ms_regs ms) (ms_mem ms) md1 LAWS HB HC0 HSP HFS HIO HMT
  HW0 ECD HTW HJ KA GA).
- intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H0 i Hi).
- intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H6 i Hi).
- intros j Hj. rewrite (KG (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H12 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H16 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H20 j Hj).
- exact F24.
- exact F28.
- exact F32.
- exact F36.
- exact F40.
- exact F44.
- exact F48.
- exact F52.
- exact F56.
- exact GRAW.
- exact GNOW.
- exact GFAIL.
- exact GLAST.
- exact SP120.
- exact SP176.
- exact SP160.
- exact SP48.
- unfold cf_regs.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
    (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
    (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
  exact HRG.
- rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- unfold lc_cur. rewrite cf_cursor. cbn [TOP.fi_off TOP.fi_n]. rewrite Coff.
  rewrite Hk. change (Z.min 2 14) with 2.
  split; [rewrite Y25; unfold w64; f_equal; lia | rewrite Y27; unfold w64; f_equal; lia].
Qed.

Lemma cf_case3 : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md -> cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_bl W mem (TA_g_cfg + 0) TC.HOST -> cf_bl W mem (TA_g_cfg + 6) TC.DESK ->
  cf_bw W mem (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W mem (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W mem (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> TOP.fi_n (lc_c1 (l_pl cx)) = 3 ->
  SRr segs W (lc_cfg cx CF_SC regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regs mem md HP HB HC0 HSP HFS HIO HMT HW0 ECD HTW
  HC HJ KV GP H0 H6 H12 H16 H20 HRG R23 R22 HCUR Hk.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
destruct (cf_c1_pos (l_pl cx) ltac:(lia)) as (Coff & Cn & Clen).
assert (Hn0 : 0 < l_n cx) by lia.
assert (R19 : YK11.getr regs (Z_to_bv 5 19) = w64 (l_p cx + 1)) by (rewrite C19, Coff; reflexivity).
assert (R27 : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 3) by (rewrite C27, Hk; reflexivity).
assert (Hz : forall j, 3 <= j -> cf_cb (l_pl cx) j = 0).
{ intros j Hj. unfold cf_cb, cf_b. rewrite Hk.
  destruct (Z.ltb_spec j 3); [lia | reflexivity]. }
assert (HB0 : 0 <= cf_cb (l_pl cx) 0 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB1 : 0 <= cf_cb (l_pl cx) 1 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB2 : 0 <= cf_cb (l_pl cx) 2 < 256) by (unfold cf_cb; apply cf_b_rng).
set (bs := [cf_cb (l_pl cx) 0; cf_cb (l_pl cx) 1; cf_cb (l_pl cx) 2]).
assert (HBrng : forall j, (j < 3)%nat -> 0 <= nth j bs 0 < 256).
{ intros j Hj. unfold bs. destruct j as [|[|[|]]]; cbn [nth]; first [exact HB0 | exact HB0 | exact HB1 | exact HB2 | lia]. }
assert (HBval : forall j, (j < 3)%nat ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j bs 0)).
{ intros j Hj.
  replace (nth j bs 0) with (cf_cb (l_pl cx) (Z.of_nat j))
    by (unfold bs; destruct j as [|[|[|]]]; cbn [nth Z.of_nat]; reflexivity || lia).
  apply (cf_in_bytes cx ly' S' W regs mem md j HC). lia. }
assert (HBden : forall j, (j < 3)%nat ->
  bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (32 + j)) = nth j bs 0)
  by (intros j Hj; apply cf_ex_val; [lia | exact (HBrng j Hj)]).
assert (UB0 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 32)
  = cf_cb (l_pl cx) 0)
  by (pose proof (HBden 0%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB1 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 33)
  = cf_cb (l_pl cx) 1)
  by (pose proof (HBden 1%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB2 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 34)
  = cf_cb (l_pl cx) 2)
  by (pose proof (HBden 2%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (EPC : w64 (transport_text + CF_SC) = Z_to_bv 64 (BASE + CF_SC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (HEI : img_env VAL A_LIM (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))) by apply cf_E_img.
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (cf_ssp 3)
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_SC)) mem (YK11.seg_rom segs)))).
{ unfold cf_ssp. apply (cf_seat cx ly' S' W regs mem md _ 3 bs _ CF_SC _ LAWS HB HC HJ).
  - apply cf_regs_pin. exact R27.
  - exact (cf_facts cx regs _ 3 bs G9 ltac:(lia) N3 R19 ltac:(lia) G21 R23 G26 HBden HBrng).
  - exact G9.
  - exact R19.
  - exact G21.
  - exact Hn0.
  - lia.
  - exact HBden.
  - exact HBrng.
  - exact HBval. }
assert (U19 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs _ 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs _ 26%nat 26%bv eq_refl), G26; apply cf_u64; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs cf_Bx (cf_SH 3) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))
  (mrestrict (w_H W) mem))
  by exact (cf_shok cx ly' S' W regs mem md _ 3 LAWS HB HC Hn0 ltac:(lia) U19 U26).
assert (V21 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs _ 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs _ 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
assert (V23 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs _ 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 8%nat ltac:(lia)) as V8h.
change (A_HI 8) with 408%nat in V8h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 9%nat ltac:(lia)) as V9h.
change (A_HI 9) with 409%nat in V9h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 10%nat ltac:(lia)) as V10h.
change (A_HI 10) with 410%nat in V10h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 11%nat ltac:(lia)) as V11h.
change (A_HI 11) with 411%nat in V11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x318.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V21 in Ha;
     apply cf_cfg_inG; lia|].
  do 4 (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|]).
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V8h in Ha;
     apply cf_glob_inG; left; unfold TA_g_raw; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9h in Ha;
     apply cf_glob_inG; right; left; unfold TA_g_now; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V10h in Ha;
     apply cf_glob_inG; right; right; left; unfold TA_g_fail_next; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V11h in Ha;
     apply cf_glob_inG; right; right; right; unfold TA_g_last_counter; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
cf_ag (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)).
lazymatch goal with
| HA : env_agree 512 (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) ?ER |- _ =>
  assert (W21 : bv_unsigned (ew ER 21) = TA_g_cfg)
    by (first [ exact V21
              | rewrite <- (proj1 HA 21%nat ltac:(lia)); exact V21
              | rewrite (proj1 HA 21%nat ltac:(lia)); exact V21 ]);
  assert (W9 : bv_unsigned (ew ER 9) = lc_sp1 cx)
    by (first [ exact V9
              | rewrite <- (proj1 HA 9%nat ltac:(lia)); exact V9
              | rewrite (proj1 HA 9%nat ltac:(lia)); exact V9 ]);
  assert (W8h : bv_unsigned (ew ER 408) = 6157588)
    by (first [ exact V8h
              | rewrite <- (proj1 HA 408%nat ltac:(lia)); exact V8h
              | rewrite (proj1 HA 408%nat ltac:(lia)); exact V8h ]);
  assert (W9h : bv_unsigned (ew ER 409) = 6157596)
    by (first [ exact V9h
              | rewrite <- (proj1 HA 409%nat ltac:(lia)); exact V9h
              | rewrite (proj1 HA 409%nat ltac:(lia)); exact V9h ]);
  assert (W10h : bv_unsigned (ew ER 410) = 6157652)
    by (first [ exact V10h
              | rewrite <- (proj1 HA 410%nat ltac:(lia)); exact V10h
              | rewrite (proj1 HA 410%nat ltac:(lia)); exact V10h ]);
  assert (W11h : bv_unsigned (ew ER 411) = 6157672)
    by (first [ exact V11h
              | rewrite <- (proj1 HA 411%nat ltac:(lia)); exact V11h
              | rewrite (proj1 HA 411%nat ltac:(lia)); exact V11h ])
end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wrun cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hw. apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wrun cx) HFr); [|exact Ha | exact Hw].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-|]); [..|destruct Hin].
  - cbn [base_val] in Hx. lia.
  - cbn [base_val] in Hx; rewrite V21 in Hx. unfold cf_wrun. left. unfold TA_g_cfg in *. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; right. lia.
  - cbn [base_val] in Hx; rewrite V8h in Hx. unfold cf_wrun. right; left. unfold TA_g_raw. lia.
  - cbn [base_val] in Hx; rewrite V9h in Hx. unfold cf_wrun. right; right; left. unfold TA_g_now. lia.
  - cbn [base_val] in Hx; rewrite V10h in Hx. unfold cf_wrun.
    right; right; right; left. unfold TA_g_fail_next. lia.
  - cbn [base_val] in Hx; rewrite V11h in Hx. unfold cf_wrun.
    right; right; right; right; left. unfold TA_g_last_counter. lia. }
assert (KA : cf_KV cx W mem0 (ms_mem ms)).
{ intros a Ha Hw. rewrite (KF a Ha ltac:(intros C; apply Hw; unfold cf_wrun, cf_wr in *; lia)).
  exact (KV a Ha Hw). }
assert (GA : cf_GP W mem0 (ms_mem ms))
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GP a Ha))).
assert (KG : forall a, TA_g_cfg <= a < TA_g_cfg + 24 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply KF; [unfold TA_g_cfg in *; lia|].
  unfold cf_wrun, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 9 _ HS eq_refl) as RG9.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
assert (F24 : cf_bw W (ms_mem ms) (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 24 4%N (SOff 34 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 3 ltac:(lia)). etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  rewrite (Hz 3 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F28 : cf_bw W (ms_mem ms) (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 28 4%N (SOff 33 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  apply cf_m32.
  - cbn. lia. }
assert (F32 : cf_bw W (ms_mem ms) (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 32 4%N (SAlu ALU_AND (SOff 32 0) (SLit 7)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f32 _ HB0). reflexivity.
  - apply cf_m8.
  - cbn. lia. }
assert (F36 : cf_bw W (ms_mem ms) (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 36 4%N (SLit 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 4 ltac:(lia)). cf_rval.
  -  rewrite (Hz 4 ltac:(lia)). cbn [Z.of_N]. lia.
  - cbn. lia. }
assert (F40 : cf_bw W (ms_mem ms) (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 40 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 5 ltac:(lia)). rewrite (Hz 6 ltac:(lia)). cf_rval.
  -  rewrite (Hz 5 ltac:(lia)). rewrite (Hz 6 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F44 : cf_bw W (ms_mem ms) (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 44 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 7 ltac:(lia)). rewrite (Hz 8 ltac:(lia)). cf_rval.
  -  rewrite (Hz 7 ltac:(lia)). rewrite (Hz 8 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F48 : cf_bw W (ms_mem ms) (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 48 4%N (SLit 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cf_rval.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cbn [Z.of_N]. lia.
  - cbn. lia. }
assert (F52 : cf_bw W (ms_mem ms) (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 52 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 11 ltac:(lia)). cf_rval.
  -  rewrite (Hz 11 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F56 : cf_bw W (ms_mem ms) (TA_g_cfg + 56) 4 ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
      mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 56 4%N (SLit 24) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). cf_rval.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (GRAW : cf_bw W (ms_mem ms) TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 408%nat _ _ _ _ _ _ (-1076) 4%N
    (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 60)) (SLit 63)) _ RG6 W8h _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 3)
      ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (GNOW : cf_bw W (ms_mem ms) TA_g_now 8 1000000)
  by (cf_gl RG7 W9h 409%nat (-1052) 8%nat 8%N (SLit 1000000) ltac:(cf_rval)).
assert (GFAIL : cf_bw W (ms_mem ms) TA_g_fail_next 1 0)
  by (cf_gl RG8 W10h 410%nat (-1076) 1%nat 1%N (SLit 0) ltac:(cf_rval)).
assert (GLAST : cf_bw W (ms_mem ms) TA_g_last_counter 4 0)
  by (cf_gl RG9 W11h 411%nat (-1064) 4%nat 4%N (SLit 0) ltac:(cf_rval)).
assert (SP48 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 48) = Some (transport_hi 11))
  by (cf_sp RG2 W9 48 (SOff 411 0)).
assert (SP120 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 120) = Some (transport_hi 8))
  by (cf_sp RG3 W9 120 (SOff 408 0)).
assert (SP160 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 160) = Some (transport_hi 10))
  by (cf_sp RG4 W9 160 (SOff 410 0)).
assert (SP176 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 176) = Some (transport_hi 9))
  by (cf_sp RG5 W9 176 (SOff 409 0)).
assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs (map (fun v : Z => Z_to_bv 64 v) bs) _ HS _ _ r Hr);
    [apply cf_agree; assumption | vm_compute; reflexivity]. }
cf_rd HS (Z_to_bv 5 25) (w64 (l_p cx + 1 + 3)) Y25
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; first [reflexivity | f_equal; lia]).
cf_rd HS (Z_to_bv 5 27) (w64 0) Y27 ltac:(reflexivity).
pmkst HS.
apply SRr_ret.
apply (cf_close cx ly' S' W regs0 mem0 md0 Bw0 B1 (ms_regs ms) (ms_mem ms) md1 LAWS HB HC0 HSP HFS HIO HMT
  HW0 ECD HTW HJ KA GA).
- intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H0 i Hi).
- intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H6 i Hi).
- intros j Hj. rewrite (KG (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H12 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H16 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H20 j Hj).
- exact F24.
- exact F28.
- exact F32.
- exact F36.
- exact F40.
- exact F44.
- exact F48.
- exact F52.
- exact F56.
- exact GRAW.
- exact GNOW.
- exact GFAIL.
- exact GLAST.
- exact SP120.
- exact SP176.
- exact SP160.
- exact SP48.
- unfold cf_regs.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
    (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
    (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
  exact HRG.
- rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- unfold lc_cur. rewrite cf_cursor. cbn [TOP.fi_off TOP.fi_n]. rewrite Coff.
  rewrite Hk. change (Z.min 3 14) with 3.
  split; [rewrite Y25; unfold w64; f_equal; lia | rewrite Y27; unfold w64; f_equal; lia].
Qed.

Lemma cf_case4 : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md -> cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_bl W mem (TA_g_cfg + 0) TC.HOST -> cf_bl W mem (TA_g_cfg + 6) TC.DESK ->
  cf_bw W mem (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W mem (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W mem (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> TOP.fi_n (lc_c1 (l_pl cx)) = 4 ->
  SRr segs W (lc_cfg cx CF_SC regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regs mem md HP HB HC0 HSP HFS HIO HMT HW0 ECD HTW
  HC HJ KV GP H0 H6 H12 H16 H20 HRG R23 R22 HCUR Hk.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
destruct (cf_c1_pos (l_pl cx) ltac:(lia)) as (Coff & Cn & Clen).
assert (Hn0 : 0 < l_n cx) by lia.
assert (R19 : YK11.getr regs (Z_to_bv 5 19) = w64 (l_p cx + 1)) by (rewrite C19, Coff; reflexivity).
assert (R27 : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 4) by (rewrite C27, Hk; reflexivity).
assert (Hz : forall j, 4 <= j -> cf_cb (l_pl cx) j = 0).
{ intros j Hj. unfold cf_cb, cf_b. rewrite Hk.
  destruct (Z.ltb_spec j 4); [lia | reflexivity]. }
assert (HB0 : 0 <= cf_cb (l_pl cx) 0 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB1 : 0 <= cf_cb (l_pl cx) 1 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB2 : 0 <= cf_cb (l_pl cx) 2 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB3 : 0 <= cf_cb (l_pl cx) 3 < 256) by (unfold cf_cb; apply cf_b_rng).
set (bs := [cf_cb (l_pl cx) 0; cf_cb (l_pl cx) 1; cf_cb (l_pl cx) 2; cf_cb (l_pl cx) 3]).
assert (HBrng : forall j, (j < 4)%nat -> 0 <= nth j bs 0 < 256).
{ intros j Hj. unfold bs. destruct j as [|[|[|[|]]]]; cbn [nth]; first [exact HB0 | exact HB0 | exact HB1 | exact HB2 | exact HB3 | lia]. }
assert (HBval : forall j, (j < 4)%nat ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j bs 0)).
{ intros j Hj.
  replace (nth j bs 0) with (cf_cb (l_pl cx) (Z.of_nat j))
    by (unfold bs; destruct j as [|[|[|[|]]]]; cbn [nth Z.of_nat]; reflexivity || lia).
  apply (cf_in_bytes cx ly' S' W regs mem md j HC). lia. }
assert (HBden : forall j, (j < 4)%nat ->
  bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (32 + j)) = nth j bs 0)
  by (intros j Hj; apply cf_ex_val; [lia | exact (HBrng j Hj)]).
assert (UB0 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 32)
  = cf_cb (l_pl cx) 0)
  by (pose proof (HBden 0%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB1 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 33)
  = cf_cb (l_pl cx) 1)
  by (pose proof (HBden 1%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB2 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 34)
  = cf_cb (l_pl cx) 2)
  by (pose proof (HBden 2%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB3 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 35)
  = cf_cb (l_pl cx) 3)
  by (pose proof (HBden 3%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (EPC : w64 (transport_text + CF_SC) = Z_to_bv 64 (BASE + CF_SC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (HEI : img_env VAL A_LIM (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))) by apply cf_E_img.
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (cf_ssp 4)
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_SC)) mem (YK11.seg_rom segs)))).
{ unfold cf_ssp. apply (cf_seat cx ly' S' W regs mem md _ 4 bs _ CF_SC _ LAWS HB HC HJ).
  - apply cf_regs_pin. exact R27.
  - exact (cf_facts cx regs _ 4 bs G9 ltac:(lia) N3 R19 ltac:(lia) G21 R23 G26 HBden HBrng).
  - exact G9.
  - exact R19.
  - exact G21.
  - exact Hn0.
  - lia.
  - exact HBden.
  - exact HBrng.
  - exact HBval. }
assert (U19 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs _ 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs _ 26%nat 26%bv eq_refl), G26; apply cf_u64; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs cf_Bx (cf_SH 4) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))
  (mrestrict (w_H W) mem))
  by exact (cf_shok cx ly' S' W regs mem md _ 4 LAWS HB HC Hn0 ltac:(lia) U19 U26).
assert (V21 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs _ 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs _ 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
assert (V23 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs _ 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 8%nat ltac:(lia)) as V8h.
change (A_HI 8) with 408%nat in V8h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 9%nat ltac:(lia)) as V9h.
change (A_HI 9) with 409%nat in V9h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 10%nat ltac:(lia)) as V10h.
change (A_HI 10) with 410%nat in V10h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 11%nat ltac:(lia)) as V11h.
change (A_HI 11) with 411%nat in V11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x318.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V21 in Ha;
     apply cf_cfg_inG; lia|].
  do 4 (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|]).
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V8h in Ha;
     apply cf_glob_inG; left; unfold TA_g_raw; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9h in Ha;
     apply cf_glob_inG; right; left; unfold TA_g_now; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V10h in Ha;
     apply cf_glob_inG; right; right; left; unfold TA_g_fail_next; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V11h in Ha;
     apply cf_glob_inG; right; right; right; unfold TA_g_last_counter; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
cf_ag (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)).
lazymatch goal with
| HA : env_agree 512 (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) ?ER |- _ =>
  assert (W21 : bv_unsigned (ew ER 21) = TA_g_cfg)
    by (first [ exact V21
              | rewrite <- (proj1 HA 21%nat ltac:(lia)); exact V21
              | rewrite (proj1 HA 21%nat ltac:(lia)); exact V21 ]);
  assert (W9 : bv_unsigned (ew ER 9) = lc_sp1 cx)
    by (first [ exact V9
              | rewrite <- (proj1 HA 9%nat ltac:(lia)); exact V9
              | rewrite (proj1 HA 9%nat ltac:(lia)); exact V9 ]);
  assert (W8h : bv_unsigned (ew ER 408) = 6157588)
    by (first [ exact V8h
              | rewrite <- (proj1 HA 408%nat ltac:(lia)); exact V8h
              | rewrite (proj1 HA 408%nat ltac:(lia)); exact V8h ]);
  assert (W9h : bv_unsigned (ew ER 409) = 6157596)
    by (first [ exact V9h
              | rewrite <- (proj1 HA 409%nat ltac:(lia)); exact V9h
              | rewrite (proj1 HA 409%nat ltac:(lia)); exact V9h ]);
  assert (W10h : bv_unsigned (ew ER 410) = 6157652)
    by (first [ exact V10h
              | rewrite <- (proj1 HA 410%nat ltac:(lia)); exact V10h
              | rewrite (proj1 HA 410%nat ltac:(lia)); exact V10h ]);
  assert (W11h : bv_unsigned (ew ER 411) = 6157672)
    by (first [ exact V11h
              | rewrite <- (proj1 HA 411%nat ltac:(lia)); exact V11h
              | rewrite (proj1 HA 411%nat ltac:(lia)); exact V11h ])
end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wrun cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hw. apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wrun cx) HFr); [|exact Ha | exact Hw].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-|]); [..|destruct Hin].
  - cbn [base_val] in Hx. lia.
  - cbn [base_val] in Hx; rewrite V21 in Hx. unfold cf_wrun. left. unfold TA_g_cfg in *. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; right. lia.
  - cbn [base_val] in Hx; rewrite V8h in Hx. unfold cf_wrun. right; left. unfold TA_g_raw. lia.
  - cbn [base_val] in Hx; rewrite V9h in Hx. unfold cf_wrun. right; right; left. unfold TA_g_now. lia.
  - cbn [base_val] in Hx; rewrite V10h in Hx. unfold cf_wrun.
    right; right; right; left. unfold TA_g_fail_next. lia.
  - cbn [base_val] in Hx; rewrite V11h in Hx. unfold cf_wrun.
    right; right; right; right; left. unfold TA_g_last_counter. lia. }
assert (KA : cf_KV cx W mem0 (ms_mem ms)).
{ intros a Ha Hw. rewrite (KF a Ha ltac:(intros C; apply Hw; unfold cf_wrun, cf_wr in *; lia)).
  exact (KV a Ha Hw). }
assert (GA : cf_GP W mem0 (ms_mem ms))
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GP a Ha))).
assert (KG : forall a, TA_g_cfg <= a < TA_g_cfg + 24 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply KF; [unfold TA_g_cfg in *; lia|].
  unfold cf_wrun, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 9 _ HS eq_refl) as RG9.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
assert (F24 : cf_bw W (ms_mem ms) (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 24 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 34 0) (SAlu ALU_SLL (SOff 35 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB2 HB3). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F28 : cf_bw W (ms_mem ms) (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 28 4%N (SOff 33 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  apply cf_m32.
  - cbn. lia. }
assert (F32 : cf_bw W (ms_mem ms) (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 32 4%N (SAlu ALU_AND (SOff 32 0) (SLit 7)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f32 _ HB0). reflexivity.
  - apply cf_m8.
  - cbn. lia. }
assert (F36 : cf_bw W (ms_mem ms) (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 36 4%N (SLit 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 4 ltac:(lia)). cf_rval.
  -  rewrite (Hz 4 ltac:(lia)). cbn [Z.of_N]. lia.
  - cbn. lia. }
assert (F40 : cf_bw W (ms_mem ms) (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 40 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 5 ltac:(lia)). rewrite (Hz 6 ltac:(lia)). cf_rval.
  -  rewrite (Hz 5 ltac:(lia)). rewrite (Hz 6 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F44 : cf_bw W (ms_mem ms) (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 44 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 7 ltac:(lia)). rewrite (Hz 8 ltac:(lia)). cf_rval.
  -  rewrite (Hz 7 ltac:(lia)). rewrite (Hz 8 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F48 : cf_bw W (ms_mem ms) (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 48 4%N (SLit 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cf_rval.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cbn [Z.of_N]. lia.
  - cbn. lia. }
assert (F52 : cf_bw W (ms_mem ms) (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 52 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 11 ltac:(lia)). cf_rval.
  -  rewrite (Hz 11 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F56 : cf_bw W (ms_mem ms) (TA_g_cfg + 56) 4 ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
      mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 56 4%N (SLit 24) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). cf_rval.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (GRAW : cf_bw W (ms_mem ms) TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 408%nat _ _ _ _ _ _ (-1076) 4%N
    (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 60)) (SLit 63)) _ RG6 W8h _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 3)
      ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (GNOW : cf_bw W (ms_mem ms) TA_g_now 8 1000000)
  by (cf_gl RG7 W9h 409%nat (-1052) 8%nat 8%N (SLit 1000000) ltac:(cf_rval)).
assert (GFAIL : cf_bw W (ms_mem ms) TA_g_fail_next 1 0)
  by (cf_gl RG8 W10h 410%nat (-1076) 1%nat 1%N (SLit 0) ltac:(cf_rval)).
assert (GLAST : cf_bw W (ms_mem ms) TA_g_last_counter 4 0)
  by (cf_gl RG9 W11h 411%nat (-1064) 4%nat 4%N (SLit 0) ltac:(cf_rval)).
assert (SP48 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 48) = Some (transport_hi 11))
  by (cf_sp RG2 W9 48 (SOff 411 0)).
assert (SP120 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 120) = Some (transport_hi 8))
  by (cf_sp RG3 W9 120 (SOff 408 0)).
assert (SP160 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 160) = Some (transport_hi 10))
  by (cf_sp RG4 W9 160 (SOff 410 0)).
assert (SP176 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 176) = Some (transport_hi 9))
  by (cf_sp RG5 W9 176 (SOff 409 0)).
assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs (map (fun v : Z => Z_to_bv 64 v) bs) _ HS _ _ r Hr);
    [apply cf_agree; assumption | vm_compute; reflexivity]. }
cf_rd HS (Z_to_bv 5 25) (w64 (l_p cx + 1 + 4)) Y25
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; first [reflexivity | f_equal; lia]).
cf_rd HS (Z_to_bv 5 27) (w64 0) Y27 ltac:(reflexivity).
pmkst HS.
apply SRr_ret.
apply (cf_close cx ly' S' W regs0 mem0 md0 Bw0 B1 (ms_regs ms) (ms_mem ms) md1 LAWS HB HC0 HSP HFS HIO HMT
  HW0 ECD HTW HJ KA GA).
- intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H0 i Hi).
- intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H6 i Hi).
- intros j Hj. rewrite (KG (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H12 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H16 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H20 j Hj).
- exact F24.
- exact F28.
- exact F32.
- exact F36.
- exact F40.
- exact F44.
- exact F48.
- exact F52.
- exact F56.
- exact GRAW.
- exact GNOW.
- exact GFAIL.
- exact GLAST.
- exact SP120.
- exact SP176.
- exact SP160.
- exact SP48.
- unfold cf_regs.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
    (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
    (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
  exact HRG.
- rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- unfold lc_cur. rewrite cf_cursor. cbn [TOP.fi_off TOP.fi_n]. rewrite Coff.
  rewrite Hk. change (Z.min 4 14) with 4.
  split; [rewrite Y25; unfold w64; f_equal; lia | rewrite Y27; unfold w64; f_equal; lia].
Qed.

Lemma cf_case5 : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md -> cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_bl W mem (TA_g_cfg + 0) TC.HOST -> cf_bl W mem (TA_g_cfg + 6) TC.DESK ->
  cf_bw W mem (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W mem (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W mem (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> TOP.fi_n (lc_c1 (l_pl cx)) = 5 ->
  SRr segs W (lc_cfg cx CF_SC regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regs mem md HP HB HC0 HSP HFS HIO HMT HW0 ECD HTW
  HC HJ KV GP H0 H6 H12 H16 H20 HRG R23 R22 HCUR Hk.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
destruct (cf_c1_pos (l_pl cx) ltac:(lia)) as (Coff & Cn & Clen).
assert (Hn0 : 0 < l_n cx) by lia.
assert (R19 : YK11.getr regs (Z_to_bv 5 19) = w64 (l_p cx + 1)) by (rewrite C19, Coff; reflexivity).
assert (R27 : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 5) by (rewrite C27, Hk; reflexivity).
assert (Hz : forall j, 5 <= j -> cf_cb (l_pl cx) j = 0).
{ intros j Hj. unfold cf_cb, cf_b. rewrite Hk.
  destruct (Z.ltb_spec j 5); [lia | reflexivity]. }
assert (HB0 : 0 <= cf_cb (l_pl cx) 0 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB1 : 0 <= cf_cb (l_pl cx) 1 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB2 : 0 <= cf_cb (l_pl cx) 2 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB3 : 0 <= cf_cb (l_pl cx) 3 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB4 : 0 <= cf_cb (l_pl cx) 4 < 256) by (unfold cf_cb; apply cf_b_rng).
set (bs := [cf_cb (l_pl cx) 0; cf_cb (l_pl cx) 1; cf_cb (l_pl cx) 2; cf_cb (l_pl cx) 3; cf_cb (l_pl cx) 4]).
assert (HBrng : forall j, (j < 5)%nat -> 0 <= nth j bs 0 < 256).
{ intros j Hj. unfold bs. destruct j as [|[|[|[|[|]]]]]; cbn [nth]; first [exact HB0 | exact HB0 | exact HB1 | exact HB2 | exact HB3 | exact HB4 | lia]. }
assert (HBval : forall j, (j < 5)%nat ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j bs 0)).
{ intros j Hj.
  replace (nth j bs 0) with (cf_cb (l_pl cx) (Z.of_nat j))
    by (unfold bs; destruct j as [|[|[|[|[|]]]]]; cbn [nth Z.of_nat]; reflexivity || lia).
  apply (cf_in_bytes cx ly' S' W regs mem md j HC). lia. }
assert (HBden : forall j, (j < 5)%nat ->
  bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (32 + j)) = nth j bs 0)
  by (intros j Hj; apply cf_ex_val; [lia | exact (HBrng j Hj)]).
assert (UB0 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 32)
  = cf_cb (l_pl cx) 0)
  by (pose proof (HBden 0%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB1 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 33)
  = cf_cb (l_pl cx) 1)
  by (pose proof (HBden 1%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB2 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 34)
  = cf_cb (l_pl cx) 2)
  by (pose proof (HBden 2%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB3 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 35)
  = cf_cb (l_pl cx) 3)
  by (pose proof (HBden 3%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB4 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 36)
  = cf_cb (l_pl cx) 4)
  by (pose proof (HBden 4%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (EPC : w64 (transport_text + CF_SC) = Z_to_bv 64 (BASE + CF_SC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (HEI : img_env VAL A_LIM (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))) by apply cf_E_img.
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (cf_ssp 5)
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_SC)) mem (YK11.seg_rom segs)))).
{ unfold cf_ssp. apply (cf_seat cx ly' S' W regs mem md _ 5 bs _ CF_SC _ LAWS HB HC HJ).
  - apply cf_regs_pin. exact R27.
  - exact (cf_facts cx regs _ 5 bs G9 ltac:(lia) N3 R19 ltac:(lia) G21 R23 G26 HBden HBrng).
  - exact G9.
  - exact R19.
  - exact G21.
  - exact Hn0.
  - lia.
  - exact HBden.
  - exact HBrng.
  - exact HBval. }
assert (U19 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs _ 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs _ 26%nat 26%bv eq_refl), G26; apply cf_u64; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs cf_Bx (cf_SH 5) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))
  (mrestrict (w_H W) mem))
  by exact (cf_shok cx ly' S' W regs mem md _ 5 LAWS HB HC Hn0 ltac:(lia) U19 U26).
assert (V21 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs _ 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs _ 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
assert (V23 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs _ 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 8%nat ltac:(lia)) as V8h.
change (A_HI 8) with 408%nat in V8h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 9%nat ltac:(lia)) as V9h.
change (A_HI 9) with 409%nat in V9h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 10%nat ltac:(lia)) as V10h.
change (A_HI 10) with 410%nat in V10h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 11%nat ltac:(lia)) as V11h.
change (A_HI 11) with 411%nat in V11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x318.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V21 in Ha;
     apply cf_cfg_inG; lia|].
  do 4 (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|]).
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V8h in Ha;
     apply cf_glob_inG; left; unfold TA_g_raw; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9h in Ha;
     apply cf_glob_inG; right; left; unfold TA_g_now; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V10h in Ha;
     apply cf_glob_inG; right; right; left; unfold TA_g_fail_next; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V11h in Ha;
     apply cf_glob_inG; right; right; right; unfold TA_g_last_counter; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
cf_ag (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)).
lazymatch goal with
| HA : env_agree 512 (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) ?ER |- _ =>
  assert (W21 : bv_unsigned (ew ER 21) = TA_g_cfg)
    by (first [ exact V21
              | rewrite <- (proj1 HA 21%nat ltac:(lia)); exact V21
              | rewrite (proj1 HA 21%nat ltac:(lia)); exact V21 ]);
  assert (W9 : bv_unsigned (ew ER 9) = lc_sp1 cx)
    by (first [ exact V9
              | rewrite <- (proj1 HA 9%nat ltac:(lia)); exact V9
              | rewrite (proj1 HA 9%nat ltac:(lia)); exact V9 ]);
  assert (W8h : bv_unsigned (ew ER 408) = 6157588)
    by (first [ exact V8h
              | rewrite <- (proj1 HA 408%nat ltac:(lia)); exact V8h
              | rewrite (proj1 HA 408%nat ltac:(lia)); exact V8h ]);
  assert (W9h : bv_unsigned (ew ER 409) = 6157596)
    by (first [ exact V9h
              | rewrite <- (proj1 HA 409%nat ltac:(lia)); exact V9h
              | rewrite (proj1 HA 409%nat ltac:(lia)); exact V9h ]);
  assert (W10h : bv_unsigned (ew ER 410) = 6157652)
    by (first [ exact V10h
              | rewrite <- (proj1 HA 410%nat ltac:(lia)); exact V10h
              | rewrite (proj1 HA 410%nat ltac:(lia)); exact V10h ]);
  assert (W11h : bv_unsigned (ew ER 411) = 6157672)
    by (first [ exact V11h
              | rewrite <- (proj1 HA 411%nat ltac:(lia)); exact V11h
              | rewrite (proj1 HA 411%nat ltac:(lia)); exact V11h ])
end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wrun cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hw. apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wrun cx) HFr); [|exact Ha | exact Hw].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-|]); [..|destruct Hin].
  - cbn [base_val] in Hx. lia.
  - cbn [base_val] in Hx; rewrite V21 in Hx. unfold cf_wrun. left. unfold TA_g_cfg in *. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; right. lia.
  - cbn [base_val] in Hx; rewrite V8h in Hx. unfold cf_wrun. right; left. unfold TA_g_raw. lia.
  - cbn [base_val] in Hx; rewrite V9h in Hx. unfold cf_wrun. right; right; left. unfold TA_g_now. lia.
  - cbn [base_val] in Hx; rewrite V10h in Hx. unfold cf_wrun.
    right; right; right; left. unfold TA_g_fail_next. lia.
  - cbn [base_val] in Hx; rewrite V11h in Hx. unfold cf_wrun.
    right; right; right; right; left. unfold TA_g_last_counter. lia. }
assert (KA : cf_KV cx W mem0 (ms_mem ms)).
{ intros a Ha Hw. rewrite (KF a Ha ltac:(intros C; apply Hw; unfold cf_wrun, cf_wr in *; lia)).
  exact (KV a Ha Hw). }
assert (GA : cf_GP W mem0 (ms_mem ms))
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GP a Ha))).
assert (KG : forall a, TA_g_cfg <= a < TA_g_cfg + 24 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply KF; [unfold TA_g_cfg in *; lia|].
  unfold cf_wrun, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 9 _ HS eq_refl) as RG9.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
assert (F24 : cf_bw W (ms_mem ms) (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 24 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 34 0) (SAlu ALU_SLL (SOff 35 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB2 HB3). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F28 : cf_bw W (ms_mem ms) (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 28 4%N (SOff 33 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  apply cf_m32.
  - cbn. lia. }
assert (F32 : cf_bw W (ms_mem ms) (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 32 4%N (SAlu ALU_AND (SOff 32 0) (SLit 7)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f32 _ HB0). reflexivity.
  - apply cf_m8.
  - cbn. lia. }
assert (F36 : cf_bw W (ms_mem ms) (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 36 4%N (SOff 36 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  cf_rval.
  -  cbn [Z.of_N]. pose proof HB4. lia.
  - cbn. lia. }
assert (F40 : cf_bw W (ms_mem ms) (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 40 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 5 ltac:(lia)). rewrite (Hz 6 ltac:(lia)). cf_rval.
  -  rewrite (Hz 5 ltac:(lia)). rewrite (Hz 6 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F44 : cf_bw W (ms_mem ms) (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 44 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 7 ltac:(lia)). rewrite (Hz 8 ltac:(lia)). cf_rval.
  -  rewrite (Hz 7 ltac:(lia)). rewrite (Hz 8 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F48 : cf_bw W (ms_mem ms) (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 48 4%N (SLit 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cf_rval.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cbn [Z.of_N]. lia.
  - cbn. lia. }
assert (F52 : cf_bw W (ms_mem ms) (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 52 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 11 ltac:(lia)). cf_rval.
  -  rewrite (Hz 11 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F56 : cf_bw W (ms_mem ms) (TA_g_cfg + 56) 4 ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
      mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 56 4%N (SLit 24) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). cf_rval.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (GRAW : cf_bw W (ms_mem ms) TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 408%nat _ _ _ _ _ _ (-1076) 4%N
    (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 60)) (SLit 63)) _ RG6 W8h _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 3)
      ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (GNOW : cf_bw W (ms_mem ms) TA_g_now 8 1000000)
  by (cf_gl RG7 W9h 409%nat (-1052) 8%nat 8%N (SLit 1000000) ltac:(cf_rval)).
assert (GFAIL : cf_bw W (ms_mem ms) TA_g_fail_next 1 0)
  by (cf_gl RG8 W10h 410%nat (-1076) 1%nat 1%N (SLit 0) ltac:(cf_rval)).
assert (GLAST : cf_bw W (ms_mem ms) TA_g_last_counter 4 0)
  by (cf_gl RG9 W11h 411%nat (-1064) 4%nat 4%N (SLit 0) ltac:(cf_rval)).
assert (SP48 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 48) = Some (transport_hi 11))
  by (cf_sp RG2 W9 48 (SOff 411 0)).
assert (SP120 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 120) = Some (transport_hi 8))
  by (cf_sp RG3 W9 120 (SOff 408 0)).
assert (SP160 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 160) = Some (transport_hi 10))
  by (cf_sp RG4 W9 160 (SOff 410 0)).
assert (SP176 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 176) = Some (transport_hi 9))
  by (cf_sp RG5 W9 176 (SOff 409 0)).
assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs (map (fun v : Z => Z_to_bv 64 v) bs) _ HS _ _ r Hr);
    [apply cf_agree; assumption | vm_compute; reflexivity]. }
cf_rd HS (Z_to_bv 5 25) (w64 (l_p cx + 1 + 5)) Y25
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; first [reflexivity | f_equal; lia]).
cf_rd HS (Z_to_bv 5 27) (w64 0) Y27 ltac:(reflexivity).
pmkst HS.
apply SRr_ret.
apply (cf_close cx ly' S' W regs0 mem0 md0 Bw0 B1 (ms_regs ms) (ms_mem ms) md1 LAWS HB HC0 HSP HFS HIO HMT
  HW0 ECD HTW HJ KA GA).
- intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H0 i Hi).
- intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H6 i Hi).
- intros j Hj. rewrite (KG (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H12 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H16 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H20 j Hj).
- exact F24.
- exact F28.
- exact F32.
- exact F36.
- exact F40.
- exact F44.
- exact F48.
- exact F52.
- exact F56.
- exact GRAW.
- exact GNOW.
- exact GFAIL.
- exact GLAST.
- exact SP120.
- exact SP176.
- exact SP160.
- exact SP48.
- unfold cf_regs.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
    (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
    (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
  exact HRG.
- rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- unfold lc_cur. rewrite cf_cursor. cbn [TOP.fi_off TOP.fi_n]. rewrite Coff.
  rewrite Hk. change (Z.min 5 14) with 5.
  split; [rewrite Y25; unfold w64; f_equal; lia | rewrite Y27; unfold w64; f_equal; lia].
Qed.

Lemma cf_case6 : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md -> cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_bl W mem (TA_g_cfg + 0) TC.HOST -> cf_bl W mem (TA_g_cfg + 6) TC.DESK ->
  cf_bw W mem (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W mem (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W mem (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> TOP.fi_n (lc_c1 (l_pl cx)) = 6 ->
  SRr segs W (lc_cfg cx CF_SC regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regs mem md HP HB HC0 HSP HFS HIO HMT HW0 ECD HTW
  HC HJ KV GP H0 H6 H12 H16 H20 HRG R23 R22 HCUR Hk.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
destruct (cf_c1_pos (l_pl cx) ltac:(lia)) as (Coff & Cn & Clen).
assert (Hn0 : 0 < l_n cx) by lia.
assert (R19 : YK11.getr regs (Z_to_bv 5 19) = w64 (l_p cx + 1)) by (rewrite C19, Coff; reflexivity).
assert (R27 : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 6) by (rewrite C27, Hk; reflexivity).
assert (Hz : forall j, 6 <= j -> cf_cb (l_pl cx) j = 0).
{ intros j Hj. unfold cf_cb, cf_b. rewrite Hk.
  destruct (Z.ltb_spec j 6); [lia | reflexivity]. }
assert (HB0 : 0 <= cf_cb (l_pl cx) 0 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB1 : 0 <= cf_cb (l_pl cx) 1 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB2 : 0 <= cf_cb (l_pl cx) 2 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB3 : 0 <= cf_cb (l_pl cx) 3 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB4 : 0 <= cf_cb (l_pl cx) 4 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB5 : 0 <= cf_cb (l_pl cx) 5 < 256) by (unfold cf_cb; apply cf_b_rng).
set (bs := [cf_cb (l_pl cx) 0; cf_cb (l_pl cx) 1; cf_cb (l_pl cx) 2; cf_cb (l_pl cx) 3; cf_cb (l_pl cx) 4; cf_cb (l_pl cx) 5]).
assert (HBrng : forall j, (j < 6)%nat -> 0 <= nth j bs 0 < 256).
{ intros j Hj. unfold bs. destruct j as [|[|[|[|[|[|]]]]]]; cbn [nth]; first [exact HB0 | exact HB0 | exact HB1 | exact HB2 | exact HB3 | exact HB4 | exact HB5 | lia]. }
assert (HBval : forall j, (j < 6)%nat ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j bs 0)).
{ intros j Hj.
  replace (nth j bs 0) with (cf_cb (l_pl cx) (Z.of_nat j))
    by (unfold bs; destruct j as [|[|[|[|[|[|]]]]]]; cbn [nth Z.of_nat]; reflexivity || lia).
  apply (cf_in_bytes cx ly' S' W regs mem md j HC). lia. }
assert (HBden : forall j, (j < 6)%nat ->
  bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (32 + j)) = nth j bs 0)
  by (intros j Hj; apply cf_ex_val; [lia | exact (HBrng j Hj)]).
assert (UB0 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 32)
  = cf_cb (l_pl cx) 0)
  by (pose proof (HBden 0%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB1 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 33)
  = cf_cb (l_pl cx) 1)
  by (pose proof (HBden 1%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB2 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 34)
  = cf_cb (l_pl cx) 2)
  by (pose proof (HBden 2%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB3 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 35)
  = cf_cb (l_pl cx) 3)
  by (pose proof (HBden 3%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB4 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 36)
  = cf_cb (l_pl cx) 4)
  by (pose proof (HBden 4%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB5 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 37)
  = cf_cb (l_pl cx) 5)
  by (pose proof (HBden 5%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (EPC : w64 (transport_text + CF_SC) = Z_to_bv 64 (BASE + CF_SC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (HEI : img_env VAL A_LIM (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))) by apply cf_E_img.
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (cf_ssp 6)
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_SC)) mem (YK11.seg_rom segs)))).
{ unfold cf_ssp. apply (cf_seat cx ly' S' W regs mem md _ 6 bs _ CF_SC _ LAWS HB HC HJ).
  - apply cf_regs_pin. exact R27.
  - exact (cf_facts cx regs _ 6 bs G9 ltac:(lia) N3 R19 ltac:(lia) G21 R23 G26 HBden HBrng).
  - exact G9.
  - exact R19.
  - exact G21.
  - exact Hn0.
  - lia.
  - exact HBden.
  - exact HBrng.
  - exact HBval. }
assert (U19 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs _ 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs _ 26%nat 26%bv eq_refl), G26; apply cf_u64; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs cf_Bx (cf_SH 6) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))
  (mrestrict (w_H W) mem))
  by exact (cf_shok cx ly' S' W regs mem md _ 6 LAWS HB HC Hn0 ltac:(lia) U19 U26).
assert (V21 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs _ 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs _ 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
assert (V23 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs _ 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 8%nat ltac:(lia)) as V8h.
change (A_HI 8) with 408%nat in V8h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 9%nat ltac:(lia)) as V9h.
change (A_HI 9) with 409%nat in V9h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 10%nat ltac:(lia)) as V10h.
change (A_HI 10) with 410%nat in V10h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 11%nat ltac:(lia)) as V11h.
change (A_HI 11) with 411%nat in V11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x318.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V21 in Ha;
     apply cf_cfg_inG; lia|].
  do 4 (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|]).
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V8h in Ha;
     apply cf_glob_inG; left; unfold TA_g_raw; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9h in Ha;
     apply cf_glob_inG; right; left; unfold TA_g_now; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V10h in Ha;
     apply cf_glob_inG; right; right; left; unfold TA_g_fail_next; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V11h in Ha;
     apply cf_glob_inG; right; right; right; unfold TA_g_last_counter; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
cf_ag (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)).
lazymatch goal with
| HA : env_agree 512 (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) ?ER |- _ =>
  assert (W21 : bv_unsigned (ew ER 21) = TA_g_cfg)
    by (first [ exact V21
              | rewrite <- (proj1 HA 21%nat ltac:(lia)); exact V21
              | rewrite (proj1 HA 21%nat ltac:(lia)); exact V21 ]);
  assert (W9 : bv_unsigned (ew ER 9) = lc_sp1 cx)
    by (first [ exact V9
              | rewrite <- (proj1 HA 9%nat ltac:(lia)); exact V9
              | rewrite (proj1 HA 9%nat ltac:(lia)); exact V9 ]);
  assert (W8h : bv_unsigned (ew ER 408) = 6157588)
    by (first [ exact V8h
              | rewrite <- (proj1 HA 408%nat ltac:(lia)); exact V8h
              | rewrite (proj1 HA 408%nat ltac:(lia)); exact V8h ]);
  assert (W9h : bv_unsigned (ew ER 409) = 6157596)
    by (first [ exact V9h
              | rewrite <- (proj1 HA 409%nat ltac:(lia)); exact V9h
              | rewrite (proj1 HA 409%nat ltac:(lia)); exact V9h ]);
  assert (W10h : bv_unsigned (ew ER 410) = 6157652)
    by (first [ exact V10h
              | rewrite <- (proj1 HA 410%nat ltac:(lia)); exact V10h
              | rewrite (proj1 HA 410%nat ltac:(lia)); exact V10h ]);
  assert (W11h : bv_unsigned (ew ER 411) = 6157672)
    by (first [ exact V11h
              | rewrite <- (proj1 HA 411%nat ltac:(lia)); exact V11h
              | rewrite (proj1 HA 411%nat ltac:(lia)); exact V11h ])
end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wrun cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hw. apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wrun cx) HFr); [|exact Ha | exact Hw].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-|]); [..|destruct Hin].
  - cbn [base_val] in Hx. lia.
  - cbn [base_val] in Hx; rewrite V21 in Hx. unfold cf_wrun. left. unfold TA_g_cfg in *. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; right. lia.
  - cbn [base_val] in Hx; rewrite V8h in Hx. unfold cf_wrun. right; left. unfold TA_g_raw. lia.
  - cbn [base_val] in Hx; rewrite V9h in Hx. unfold cf_wrun. right; right; left. unfold TA_g_now. lia.
  - cbn [base_val] in Hx; rewrite V10h in Hx. unfold cf_wrun.
    right; right; right; left. unfold TA_g_fail_next. lia.
  - cbn [base_val] in Hx; rewrite V11h in Hx. unfold cf_wrun.
    right; right; right; right; left. unfold TA_g_last_counter. lia. }
assert (KA : cf_KV cx W mem0 (ms_mem ms)).
{ intros a Ha Hw. rewrite (KF a Ha ltac:(intros C; apply Hw; unfold cf_wrun, cf_wr in *; lia)).
  exact (KV a Ha Hw). }
assert (GA : cf_GP W mem0 (ms_mem ms))
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GP a Ha))).
assert (KG : forall a, TA_g_cfg <= a < TA_g_cfg + 24 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply KF; [unfold TA_g_cfg in *; lia|].
  unfold cf_wrun, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 9 _ HS eq_refl) as RG9.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
assert (F24 : cf_bw W (ms_mem ms) (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 24 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 34 0) (SAlu ALU_SLL (SOff 35 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB2 HB3). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F28 : cf_bw W (ms_mem ms) (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 28 4%N (SOff 33 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  apply cf_m32.
  - cbn. lia. }
assert (F32 : cf_bw W (ms_mem ms) (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 32 4%N (SAlu ALU_AND (SOff 32 0) (SLit 7)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f32 _ HB0). reflexivity.
  - apply cf_m8.
  - cbn. lia. }
assert (F36 : cf_bw W (ms_mem ms) (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 36 4%N (SOff 36 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  cf_rval.
  -  cbn [Z.of_N]. pose proof HB4. lia.
  - cbn. lia. }
assert (F40 : cf_bw W (ms_mem ms) (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 40 4%N (SOff 37 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 6 ltac:(lia)). etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  rewrite (Hz 6 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F44 : cf_bw W (ms_mem ms) (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 44 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 7 ltac:(lia)). rewrite (Hz 8 ltac:(lia)). cf_rval.
  -  rewrite (Hz 7 ltac:(lia)). rewrite (Hz 8 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F48 : cf_bw W (ms_mem ms) (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 48 4%N (SLit 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cf_rval.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cbn [Z.of_N]. lia.
  - cbn. lia. }
assert (F52 : cf_bw W (ms_mem ms) (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 52 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 11 ltac:(lia)). cf_rval.
  -  rewrite (Hz 11 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F56 : cf_bw W (ms_mem ms) (TA_g_cfg + 56) 4 ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
      mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 56 4%N (SLit 24) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). cf_rval.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (GRAW : cf_bw W (ms_mem ms) TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 408%nat _ _ _ _ _ _ (-1076) 4%N
    (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 60)) (SLit 63)) _ RG6 W8h _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 3)
      ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (GNOW : cf_bw W (ms_mem ms) TA_g_now 8 1000000)
  by (cf_gl RG7 W9h 409%nat (-1052) 8%nat 8%N (SLit 1000000) ltac:(cf_rval)).
assert (GFAIL : cf_bw W (ms_mem ms) TA_g_fail_next 1 0)
  by (cf_gl RG8 W10h 410%nat (-1076) 1%nat 1%N (SLit 0) ltac:(cf_rval)).
assert (GLAST : cf_bw W (ms_mem ms) TA_g_last_counter 4 0)
  by (cf_gl RG9 W11h 411%nat (-1064) 4%nat 4%N (SLit 0) ltac:(cf_rval)).
assert (SP48 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 48) = Some (transport_hi 11))
  by (cf_sp RG2 W9 48 (SOff 411 0)).
assert (SP120 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 120) = Some (transport_hi 8))
  by (cf_sp RG3 W9 120 (SOff 408 0)).
assert (SP160 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 160) = Some (transport_hi 10))
  by (cf_sp RG4 W9 160 (SOff 410 0)).
assert (SP176 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 176) = Some (transport_hi 9))
  by (cf_sp RG5 W9 176 (SOff 409 0)).
assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs (map (fun v : Z => Z_to_bv 64 v) bs) _ HS _ _ r Hr);
    [apply cf_agree; assumption | vm_compute; reflexivity]. }
cf_rd HS (Z_to_bv 5 25) (w64 (l_p cx + 1 + 6)) Y25
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; first [reflexivity | f_equal; lia]).
cf_rd HS (Z_to_bv 5 27) (w64 0) Y27 ltac:(reflexivity).
pmkst HS.
apply SRr_ret.
apply (cf_close cx ly' S' W regs0 mem0 md0 Bw0 B1 (ms_regs ms) (ms_mem ms) md1 LAWS HB HC0 HSP HFS HIO HMT
  HW0 ECD HTW HJ KA GA).
- intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H0 i Hi).
- intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H6 i Hi).
- intros j Hj. rewrite (KG (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H12 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H16 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H20 j Hj).
- exact F24.
- exact F28.
- exact F32.
- exact F36.
- exact F40.
- exact F44.
- exact F48.
- exact F52.
- exact F56.
- exact GRAW.
- exact GNOW.
- exact GFAIL.
- exact GLAST.
- exact SP120.
- exact SP176.
- exact SP160.
- exact SP48.
- unfold cf_regs.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
    (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
    (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
  exact HRG.
- rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- unfold lc_cur. rewrite cf_cursor. cbn [TOP.fi_off TOP.fi_n]. rewrite Coff.
  rewrite Hk. change (Z.min 6 14) with 6.
  split; [rewrite Y25; unfold w64; f_equal; lia | rewrite Y27; unfold w64; f_equal; lia].
Qed.

Lemma cf_case7 : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md -> cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_bl W mem (TA_g_cfg + 0) TC.HOST -> cf_bl W mem (TA_g_cfg + 6) TC.DESK ->
  cf_bw W mem (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W mem (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W mem (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> TOP.fi_n (lc_c1 (l_pl cx)) = 7 ->
  SRr segs W (lc_cfg cx CF_SC regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regs mem md HP HB HC0 HSP HFS HIO HMT HW0 ECD HTW
  HC HJ KV GP H0 H6 H12 H16 H20 HRG R23 R22 HCUR Hk.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
destruct (cf_c1_pos (l_pl cx) ltac:(lia)) as (Coff & Cn & Clen).
assert (Hn0 : 0 < l_n cx) by lia.
assert (R19 : YK11.getr regs (Z_to_bv 5 19) = w64 (l_p cx + 1)) by (rewrite C19, Coff; reflexivity).
assert (R27 : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 7) by (rewrite C27, Hk; reflexivity).
assert (Hz : forall j, 7 <= j -> cf_cb (l_pl cx) j = 0).
{ intros j Hj. unfold cf_cb, cf_b. rewrite Hk.
  destruct (Z.ltb_spec j 7); [lia | reflexivity]. }
assert (HB0 : 0 <= cf_cb (l_pl cx) 0 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB1 : 0 <= cf_cb (l_pl cx) 1 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB2 : 0 <= cf_cb (l_pl cx) 2 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB3 : 0 <= cf_cb (l_pl cx) 3 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB4 : 0 <= cf_cb (l_pl cx) 4 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB5 : 0 <= cf_cb (l_pl cx) 5 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB6 : 0 <= cf_cb (l_pl cx) 6 < 256) by (unfold cf_cb; apply cf_b_rng).
set (bs := [cf_cb (l_pl cx) 0; cf_cb (l_pl cx) 1; cf_cb (l_pl cx) 2; cf_cb (l_pl cx) 3; cf_cb (l_pl cx) 4; cf_cb (l_pl cx) 5; cf_cb (l_pl cx) 6]).
assert (HBrng : forall j, (j < 7)%nat -> 0 <= nth j bs 0 < 256).
{ intros j Hj. unfold bs. destruct j as [|[|[|[|[|[|[|]]]]]]]; cbn [nth]; first [exact HB0 | exact HB0 | exact HB1 | exact HB2 | exact HB3 | exact HB4 | exact HB5 | exact HB6 | lia]. }
assert (HBval : forall j, (j < 7)%nat ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j bs 0)).
{ intros j Hj.
  replace (nth j bs 0) with (cf_cb (l_pl cx) (Z.of_nat j))
    by (unfold bs; destruct j as [|[|[|[|[|[|[|]]]]]]]; cbn [nth Z.of_nat]; reflexivity || lia).
  apply (cf_in_bytes cx ly' S' W regs mem md j HC). lia. }
assert (HBden : forall j, (j < 7)%nat ->
  bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (32 + j)) = nth j bs 0)
  by (intros j Hj; apply cf_ex_val; [lia | exact (HBrng j Hj)]).
assert (UB0 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 32)
  = cf_cb (l_pl cx) 0)
  by (pose proof (HBden 0%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB1 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 33)
  = cf_cb (l_pl cx) 1)
  by (pose proof (HBden 1%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB2 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 34)
  = cf_cb (l_pl cx) 2)
  by (pose proof (HBden 2%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB3 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 35)
  = cf_cb (l_pl cx) 3)
  by (pose proof (HBden 3%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB4 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 36)
  = cf_cb (l_pl cx) 4)
  by (pose proof (HBden 4%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB5 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 37)
  = cf_cb (l_pl cx) 5)
  by (pose proof (HBden 5%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB6 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 38)
  = cf_cb (l_pl cx) 6)
  by (pose proof (HBden 6%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (EPC : w64 (transport_text + CF_SC) = Z_to_bv 64 (BASE + CF_SC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (HEI : img_env VAL A_LIM (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))) by apply cf_E_img.
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (cf_ssp 7)
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_SC)) mem (YK11.seg_rom segs)))).
{ unfold cf_ssp. apply (cf_seat cx ly' S' W regs mem md _ 7 bs _ CF_SC _ LAWS HB HC HJ).
  - apply cf_regs_pin. exact R27.
  - exact (cf_facts cx regs _ 7 bs G9 ltac:(lia) N3 R19 ltac:(lia) G21 R23 G26 HBden HBrng).
  - exact G9.
  - exact R19.
  - exact G21.
  - exact Hn0.
  - lia.
  - exact HBden.
  - exact HBrng.
  - exact HBval. }
assert (U19 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs _ 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs _ 26%nat 26%bv eq_refl), G26; apply cf_u64; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs cf_Bx (cf_SH 7) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))
  (mrestrict (w_H W) mem))
  by exact (cf_shok cx ly' S' W regs mem md _ 7 LAWS HB HC Hn0 ltac:(lia) U19 U26).
assert (V21 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs _ 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs _ 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
assert (V23 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs _ 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 8%nat ltac:(lia)) as V8h.
change (A_HI 8) with 408%nat in V8h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 9%nat ltac:(lia)) as V9h.
change (A_HI 9) with 409%nat in V9h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 10%nat ltac:(lia)) as V10h.
change (A_HI 10) with 410%nat in V10h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 11%nat ltac:(lia)) as V11h.
change (A_HI 11) with 411%nat in V11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x318.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V21 in Ha;
     apply cf_cfg_inG; lia|].
  do 4 (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|]).
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V8h in Ha;
     apply cf_glob_inG; left; unfold TA_g_raw; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9h in Ha;
     apply cf_glob_inG; right; left; unfold TA_g_now; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V10h in Ha;
     apply cf_glob_inG; right; right; left; unfold TA_g_fail_next; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V11h in Ha;
     apply cf_glob_inG; right; right; right; unfold TA_g_last_counter; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
cf_ag (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)).
lazymatch goal with
| HA : env_agree 512 (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) ?ER |- _ =>
  assert (W21 : bv_unsigned (ew ER 21) = TA_g_cfg)
    by (first [ exact V21
              | rewrite <- (proj1 HA 21%nat ltac:(lia)); exact V21
              | rewrite (proj1 HA 21%nat ltac:(lia)); exact V21 ]);
  assert (W9 : bv_unsigned (ew ER 9) = lc_sp1 cx)
    by (first [ exact V9
              | rewrite <- (proj1 HA 9%nat ltac:(lia)); exact V9
              | rewrite (proj1 HA 9%nat ltac:(lia)); exact V9 ]);
  assert (W8h : bv_unsigned (ew ER 408) = 6157588)
    by (first [ exact V8h
              | rewrite <- (proj1 HA 408%nat ltac:(lia)); exact V8h
              | rewrite (proj1 HA 408%nat ltac:(lia)); exact V8h ]);
  assert (W9h : bv_unsigned (ew ER 409) = 6157596)
    by (first [ exact V9h
              | rewrite <- (proj1 HA 409%nat ltac:(lia)); exact V9h
              | rewrite (proj1 HA 409%nat ltac:(lia)); exact V9h ]);
  assert (W10h : bv_unsigned (ew ER 410) = 6157652)
    by (first [ exact V10h
              | rewrite <- (proj1 HA 410%nat ltac:(lia)); exact V10h
              | rewrite (proj1 HA 410%nat ltac:(lia)); exact V10h ]);
  assert (W11h : bv_unsigned (ew ER 411) = 6157672)
    by (first [ exact V11h
              | rewrite <- (proj1 HA 411%nat ltac:(lia)); exact V11h
              | rewrite (proj1 HA 411%nat ltac:(lia)); exact V11h ])
end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wrun cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hw. apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wrun cx) HFr); [|exact Ha | exact Hw].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-|]); [..|destruct Hin].
  - cbn [base_val] in Hx. lia.
  - cbn [base_val] in Hx; rewrite V21 in Hx. unfold cf_wrun. left. unfold TA_g_cfg in *. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; right. lia.
  - cbn [base_val] in Hx; rewrite V8h in Hx. unfold cf_wrun. right; left. unfold TA_g_raw. lia.
  - cbn [base_val] in Hx; rewrite V9h in Hx. unfold cf_wrun. right; right; left. unfold TA_g_now. lia.
  - cbn [base_val] in Hx; rewrite V10h in Hx. unfold cf_wrun.
    right; right; right; left. unfold TA_g_fail_next. lia.
  - cbn [base_val] in Hx; rewrite V11h in Hx. unfold cf_wrun.
    right; right; right; right; left. unfold TA_g_last_counter. lia. }
assert (KA : cf_KV cx W mem0 (ms_mem ms)).
{ intros a Ha Hw. rewrite (KF a Ha ltac:(intros C; apply Hw; unfold cf_wrun, cf_wr in *; lia)).
  exact (KV a Ha Hw). }
assert (GA : cf_GP W mem0 (ms_mem ms))
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GP a Ha))).
assert (KG : forall a, TA_g_cfg <= a < TA_g_cfg + 24 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply KF; [unfold TA_g_cfg in *; lia|].
  unfold cf_wrun, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 9 _ HS eq_refl) as RG9.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
assert (F24 : cf_bw W (ms_mem ms) (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 24 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 34 0) (SAlu ALU_SLL (SOff 35 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB2 HB3). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F28 : cf_bw W (ms_mem ms) (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 28 4%N (SOff 33 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  apply cf_m32.
  - cbn. lia. }
assert (F32 : cf_bw W (ms_mem ms) (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 32 4%N (SAlu ALU_AND (SOff 32 0) (SLit 7)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f32 _ HB0). reflexivity.
  - apply cf_m8.
  - cbn. lia. }
assert (F36 : cf_bw W (ms_mem ms) (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 36 4%N (SOff 36 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  cf_rval.
  -  cbn [Z.of_N]. pose proof HB4. lia.
  - cbn. lia. }
assert (F40 : cf_bw W (ms_mem ms) (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 40 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 37 0) (SAlu ALU_SLL (SOff 38 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB5 HB6). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F44 : cf_bw W (ms_mem ms) (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 44 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 7 ltac:(lia)). rewrite (Hz 8 ltac:(lia)). cf_rval.
  -  rewrite (Hz 7 ltac:(lia)). rewrite (Hz 8 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F48 : cf_bw W (ms_mem ms) (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 48 4%N (SLit 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cf_rval.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cbn [Z.of_N]. lia.
  - cbn. lia. }
assert (F52 : cf_bw W (ms_mem ms) (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 52 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 11 ltac:(lia)). cf_rval.
  -  rewrite (Hz 11 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F56 : cf_bw W (ms_mem ms) (TA_g_cfg + 56) 4 ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
      mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 56 4%N (SLit 24) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). cf_rval.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (GRAW : cf_bw W (ms_mem ms) TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 408%nat _ _ _ _ _ _ (-1076) 4%N
    (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 60)) (SLit 63)) _ RG6 W8h _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 3)
      ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (GNOW : cf_bw W (ms_mem ms) TA_g_now 8 1000000)
  by (cf_gl RG7 W9h 409%nat (-1052) 8%nat 8%N (SLit 1000000) ltac:(cf_rval)).
assert (GFAIL : cf_bw W (ms_mem ms) TA_g_fail_next 1 0)
  by (cf_gl RG8 W10h 410%nat (-1076) 1%nat 1%N (SLit 0) ltac:(cf_rval)).
assert (GLAST : cf_bw W (ms_mem ms) TA_g_last_counter 4 0)
  by (cf_gl RG9 W11h 411%nat (-1064) 4%nat 4%N (SLit 0) ltac:(cf_rval)).
assert (SP48 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 48) = Some (transport_hi 11))
  by (cf_sp RG2 W9 48 (SOff 411 0)).
assert (SP120 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 120) = Some (transport_hi 8))
  by (cf_sp RG3 W9 120 (SOff 408 0)).
assert (SP160 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 160) = Some (transport_hi 10))
  by (cf_sp RG4 W9 160 (SOff 410 0)).
assert (SP176 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 176) = Some (transport_hi 9))
  by (cf_sp RG5 W9 176 (SOff 409 0)).
assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs (map (fun v : Z => Z_to_bv 64 v) bs) _ HS _ _ r Hr);
    [apply cf_agree; assumption | vm_compute; reflexivity]. }
cf_rd HS (Z_to_bv 5 25) (w64 (l_p cx + 1 + 7)) Y25
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; first [reflexivity | f_equal; lia]).
cf_rd HS (Z_to_bv 5 27) (w64 0) Y27 ltac:(reflexivity).
pmkst HS.
apply SRr_ret.
apply (cf_close cx ly' S' W regs0 mem0 md0 Bw0 B1 (ms_regs ms) (ms_mem ms) md1 LAWS HB HC0 HSP HFS HIO HMT
  HW0 ECD HTW HJ KA GA).
- intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H0 i Hi).
- intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H6 i Hi).
- intros j Hj. rewrite (KG (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H12 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H16 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H20 j Hj).
- exact F24.
- exact F28.
- exact F32.
- exact F36.
- exact F40.
- exact F44.
- exact F48.
- exact F52.
- exact F56.
- exact GRAW.
- exact GNOW.
- exact GFAIL.
- exact GLAST.
- exact SP120.
- exact SP176.
- exact SP160.
- exact SP48.
- unfold cf_regs.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
    (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
    (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
  exact HRG.
- rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- unfold lc_cur. rewrite cf_cursor. cbn [TOP.fi_off TOP.fi_n]. rewrite Coff.
  rewrite Hk. change (Z.min 7 14) with 7.
  split; [rewrite Y25; unfold w64; f_equal; lia | rewrite Y27; unfold w64; f_equal; lia].
Qed.

Lemma cf_case8 : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md -> cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_bl W mem (TA_g_cfg + 0) TC.HOST -> cf_bl W mem (TA_g_cfg + 6) TC.DESK ->
  cf_bw W mem (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W mem (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W mem (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> TOP.fi_n (lc_c1 (l_pl cx)) = 8 ->
  SRr segs W (lc_cfg cx CF_SC regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regs mem md HP HB HC0 HSP HFS HIO HMT HW0 ECD HTW
  HC HJ KV GP H0 H6 H12 H16 H20 HRG R23 R22 HCUR Hk.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
destruct (cf_c1_pos (l_pl cx) ltac:(lia)) as (Coff & Cn & Clen).
assert (Hn0 : 0 < l_n cx) by lia.
assert (R19 : YK11.getr regs (Z_to_bv 5 19) = w64 (l_p cx + 1)) by (rewrite C19, Coff; reflexivity).
assert (R27 : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 8) by (rewrite C27, Hk; reflexivity).
assert (Hz : forall j, 8 <= j -> cf_cb (l_pl cx) j = 0).
{ intros j Hj. unfold cf_cb, cf_b. rewrite Hk.
  destruct (Z.ltb_spec j 8); [lia | reflexivity]. }
assert (HB0 : 0 <= cf_cb (l_pl cx) 0 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB1 : 0 <= cf_cb (l_pl cx) 1 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB2 : 0 <= cf_cb (l_pl cx) 2 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB3 : 0 <= cf_cb (l_pl cx) 3 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB4 : 0 <= cf_cb (l_pl cx) 4 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB5 : 0 <= cf_cb (l_pl cx) 5 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB6 : 0 <= cf_cb (l_pl cx) 6 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB7 : 0 <= cf_cb (l_pl cx) 7 < 256) by (unfold cf_cb; apply cf_b_rng).
set (bs := [cf_cb (l_pl cx) 0; cf_cb (l_pl cx) 1; cf_cb (l_pl cx) 2; cf_cb (l_pl cx) 3; cf_cb (l_pl cx) 4; cf_cb (l_pl cx) 5; cf_cb (l_pl cx) 6; cf_cb (l_pl cx) 7]).
assert (HBrng : forall j, (j < 8)%nat -> 0 <= nth j bs 0 < 256).
{ intros j Hj. unfold bs. destruct j as [|[|[|[|[|[|[|[|]]]]]]]]; cbn [nth]; first [exact HB0 | exact HB0 | exact HB1 | exact HB2 | exact HB3 | exact HB4 | exact HB5 | exact HB6 | exact HB7 | lia]. }
assert (HBval : forall j, (j < 8)%nat ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j bs 0)).
{ intros j Hj.
  replace (nth j bs 0) with (cf_cb (l_pl cx) (Z.of_nat j))
    by (unfold bs; destruct j as [|[|[|[|[|[|[|[|]]]]]]]]; cbn [nth Z.of_nat]; reflexivity || lia).
  apply (cf_in_bytes cx ly' S' W regs mem md j HC). lia. }
assert (HBden : forall j, (j < 8)%nat ->
  bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (32 + j)) = nth j bs 0)
  by (intros j Hj; apply cf_ex_val; [lia | exact (HBrng j Hj)]).
assert (UB0 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 32)
  = cf_cb (l_pl cx) 0)
  by (pose proof (HBden 0%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB1 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 33)
  = cf_cb (l_pl cx) 1)
  by (pose proof (HBden 1%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB2 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 34)
  = cf_cb (l_pl cx) 2)
  by (pose proof (HBden 2%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB3 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 35)
  = cf_cb (l_pl cx) 3)
  by (pose proof (HBden 3%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB4 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 36)
  = cf_cb (l_pl cx) 4)
  by (pose proof (HBden 4%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB5 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 37)
  = cf_cb (l_pl cx) 5)
  by (pose proof (HBden 5%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB6 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 38)
  = cf_cb (l_pl cx) 6)
  by (pose proof (HBden 6%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB7 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 39)
  = cf_cb (l_pl cx) 7)
  by (pose proof (HBden 7%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (EPC : w64 (transport_text + CF_SC) = Z_to_bv 64 (BASE + CF_SC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (HEI : img_env VAL A_LIM (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))) by apply cf_E_img.
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (cf_ssp 8)
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_SC)) mem (YK11.seg_rom segs)))).
{ unfold cf_ssp. apply (cf_seat cx ly' S' W regs mem md _ 8 bs _ CF_SC _ LAWS HB HC HJ).
  - apply cf_regs_pin. exact R27.
  - exact (cf_facts cx regs _ 8 bs G9 ltac:(lia) N3 R19 ltac:(lia) G21 R23 G26 HBden HBrng).
  - exact G9.
  - exact R19.
  - exact G21.
  - exact Hn0.
  - lia.
  - exact HBden.
  - exact HBrng.
  - exact HBval. }
assert (U19 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs _ 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs _ 26%nat 26%bv eq_refl), G26; apply cf_u64; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs cf_Bx (cf_SH 8) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))
  (mrestrict (w_H W) mem))
  by exact (cf_shok cx ly' S' W regs mem md _ 8 LAWS HB HC Hn0 ltac:(lia) U19 U26).
assert (V21 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs _ 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs _ 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
assert (V23 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs _ 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 8%nat ltac:(lia)) as V8h.
change (A_HI 8) with 408%nat in V8h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 9%nat ltac:(lia)) as V9h.
change (A_HI 9) with 409%nat in V9h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 10%nat ltac:(lia)) as V10h.
change (A_HI 10) with 410%nat in V10h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 11%nat ltac:(lia)) as V11h.
change (A_HI 11) with 411%nat in V11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x318.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V21 in Ha;
     apply cf_cfg_inG; lia|].
  do 4 (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|]).
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V8h in Ha;
     apply cf_glob_inG; left; unfold TA_g_raw; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9h in Ha;
     apply cf_glob_inG; right; left; unfold TA_g_now; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V10h in Ha;
     apply cf_glob_inG; right; right; left; unfold TA_g_fail_next; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V11h in Ha;
     apply cf_glob_inG; right; right; right; unfold TA_g_last_counter; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
cf_ag (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)).
lazymatch goal with
| HA : env_agree 512 (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) ?ER |- _ =>
  assert (W21 : bv_unsigned (ew ER 21) = TA_g_cfg)
    by (first [ exact V21
              | rewrite <- (proj1 HA 21%nat ltac:(lia)); exact V21
              | rewrite (proj1 HA 21%nat ltac:(lia)); exact V21 ]);
  assert (W9 : bv_unsigned (ew ER 9) = lc_sp1 cx)
    by (first [ exact V9
              | rewrite <- (proj1 HA 9%nat ltac:(lia)); exact V9
              | rewrite (proj1 HA 9%nat ltac:(lia)); exact V9 ]);
  assert (W8h : bv_unsigned (ew ER 408) = 6157588)
    by (first [ exact V8h
              | rewrite <- (proj1 HA 408%nat ltac:(lia)); exact V8h
              | rewrite (proj1 HA 408%nat ltac:(lia)); exact V8h ]);
  assert (W9h : bv_unsigned (ew ER 409) = 6157596)
    by (first [ exact V9h
              | rewrite <- (proj1 HA 409%nat ltac:(lia)); exact V9h
              | rewrite (proj1 HA 409%nat ltac:(lia)); exact V9h ]);
  assert (W10h : bv_unsigned (ew ER 410) = 6157652)
    by (first [ exact V10h
              | rewrite <- (proj1 HA 410%nat ltac:(lia)); exact V10h
              | rewrite (proj1 HA 410%nat ltac:(lia)); exact V10h ]);
  assert (W11h : bv_unsigned (ew ER 411) = 6157672)
    by (first [ exact V11h
              | rewrite <- (proj1 HA 411%nat ltac:(lia)); exact V11h
              | rewrite (proj1 HA 411%nat ltac:(lia)); exact V11h ])
end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wrun cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hw. apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wrun cx) HFr); [|exact Ha | exact Hw].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-|]); [..|destruct Hin].
  - cbn [base_val] in Hx. lia.
  - cbn [base_val] in Hx; rewrite V21 in Hx. unfold cf_wrun. left. unfold TA_g_cfg in *. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; right. lia.
  - cbn [base_val] in Hx; rewrite V8h in Hx. unfold cf_wrun. right; left. unfold TA_g_raw. lia.
  - cbn [base_val] in Hx; rewrite V9h in Hx. unfold cf_wrun. right; right; left. unfold TA_g_now. lia.
  - cbn [base_val] in Hx; rewrite V10h in Hx. unfold cf_wrun.
    right; right; right; left. unfold TA_g_fail_next. lia.
  - cbn [base_val] in Hx; rewrite V11h in Hx. unfold cf_wrun.
    right; right; right; right; left. unfold TA_g_last_counter. lia. }
assert (KA : cf_KV cx W mem0 (ms_mem ms)).
{ intros a Ha Hw. rewrite (KF a Ha ltac:(intros C; apply Hw; unfold cf_wrun, cf_wr in *; lia)).
  exact (KV a Ha Hw). }
assert (GA : cf_GP W mem0 (ms_mem ms))
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GP a Ha))).
assert (KG : forall a, TA_g_cfg <= a < TA_g_cfg + 24 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply KF; [unfold TA_g_cfg in *; lia|].
  unfold cf_wrun, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 9 _ HS eq_refl) as RG9.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
assert (F24 : cf_bw W (ms_mem ms) (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 24 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 34 0) (SAlu ALU_SLL (SOff 35 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB2 HB3). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F28 : cf_bw W (ms_mem ms) (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 28 4%N (SOff 33 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  apply cf_m32.
  - cbn. lia. }
assert (F32 : cf_bw W (ms_mem ms) (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 32 4%N (SAlu ALU_AND (SOff 32 0) (SLit 7)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f32 _ HB0). reflexivity.
  - apply cf_m8.
  - cbn. lia. }
assert (F36 : cf_bw W (ms_mem ms) (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 36 4%N (SOff 36 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  cf_rval.
  -  cbn [Z.of_N]. pose proof HB4. lia.
  - cbn. lia. }
assert (F40 : cf_bw W (ms_mem ms) (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 40 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 37 0) (SAlu ALU_SLL (SOff 38 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB5 HB6). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F44 : cf_bw W (ms_mem ms) (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 44 4%N (SOff 39 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 8 ltac:(lia)). etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  rewrite (Hz 8 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F48 : cf_bw W (ms_mem ms) (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 48 4%N (SLit 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cf_rval.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cbn [Z.of_N]. lia.
  - cbn. lia. }
assert (F52 : cf_bw W (ms_mem ms) (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 52 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 11 ltac:(lia)). cf_rval.
  -  rewrite (Hz 11 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F56 : cf_bw W (ms_mem ms) (TA_g_cfg + 56) 4 ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
      mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 56 4%N (SLit 24) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). cf_rval.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (GRAW : cf_bw W (ms_mem ms) TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 408%nat _ _ _ _ _ _ (-1076) 4%N
    (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 60)) (SLit 63)) _ RG6 W8h _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 3)
      ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (GNOW : cf_bw W (ms_mem ms) TA_g_now 8 1000000)
  by (cf_gl RG7 W9h 409%nat (-1052) 8%nat 8%N (SLit 1000000) ltac:(cf_rval)).
assert (GFAIL : cf_bw W (ms_mem ms) TA_g_fail_next 1 0)
  by (cf_gl RG8 W10h 410%nat (-1076) 1%nat 1%N (SLit 0) ltac:(cf_rval)).
assert (GLAST : cf_bw W (ms_mem ms) TA_g_last_counter 4 0)
  by (cf_gl RG9 W11h 411%nat (-1064) 4%nat 4%N (SLit 0) ltac:(cf_rval)).
assert (SP48 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 48) = Some (transport_hi 11))
  by (cf_sp RG2 W9 48 (SOff 411 0)).
assert (SP120 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 120) = Some (transport_hi 8))
  by (cf_sp RG3 W9 120 (SOff 408 0)).
assert (SP160 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 160) = Some (transport_hi 10))
  by (cf_sp RG4 W9 160 (SOff 410 0)).
assert (SP176 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 176) = Some (transport_hi 9))
  by (cf_sp RG5 W9 176 (SOff 409 0)).
assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs (map (fun v : Z => Z_to_bv 64 v) bs) _ HS _ _ r Hr);
    [apply cf_agree; assumption | vm_compute; reflexivity]. }
cf_rd HS (Z_to_bv 5 25) (w64 (l_p cx + 1 + 8)) Y25
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; first [reflexivity | f_equal; lia]).
cf_rd HS (Z_to_bv 5 27) (w64 0) Y27 ltac:(reflexivity).
pmkst HS.
apply SRr_ret.
apply (cf_close cx ly' S' W regs0 mem0 md0 Bw0 B1 (ms_regs ms) (ms_mem ms) md1 LAWS HB HC0 HSP HFS HIO HMT
  HW0 ECD HTW HJ KA GA).
- intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H0 i Hi).
- intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H6 i Hi).
- intros j Hj. rewrite (KG (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H12 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H16 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H20 j Hj).
- exact F24.
- exact F28.
- exact F32.
- exact F36.
- exact F40.
- exact F44.
- exact F48.
- exact F52.
- exact F56.
- exact GRAW.
- exact GNOW.
- exact GFAIL.
- exact GLAST.
- exact SP120.
- exact SP176.
- exact SP160.
- exact SP48.
- unfold cf_regs.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
    (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
    (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
  exact HRG.
- rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- unfold lc_cur. rewrite cf_cursor. cbn [TOP.fi_off TOP.fi_n]. rewrite Coff.
  rewrite Hk. change (Z.min 8 14) with 8.
  split; [rewrite Y25; unfold w64; f_equal; lia | rewrite Y27; unfold w64; f_equal; lia].
Qed.

Lemma cf_case9 : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md -> cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_bl W mem (TA_g_cfg + 0) TC.HOST -> cf_bl W mem (TA_g_cfg + 6) TC.DESK ->
  cf_bw W mem (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W mem (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W mem (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> TOP.fi_n (lc_c1 (l_pl cx)) = 9 ->
  SRr segs W (lc_cfg cx CF_SC regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regs mem md HP HB HC0 HSP HFS HIO HMT HW0 ECD HTW
  HC HJ KV GP H0 H6 H12 H16 H20 HRG R23 R22 HCUR Hk.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
destruct (cf_c1_pos (l_pl cx) ltac:(lia)) as (Coff & Cn & Clen).
assert (Hn0 : 0 < l_n cx) by lia.
assert (R19 : YK11.getr regs (Z_to_bv 5 19) = w64 (l_p cx + 1)) by (rewrite C19, Coff; reflexivity).
assert (R27 : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 9) by (rewrite C27, Hk; reflexivity).
assert (Hz : forall j, 9 <= j -> cf_cb (l_pl cx) j = 0).
{ intros j Hj. unfold cf_cb, cf_b. rewrite Hk.
  destruct (Z.ltb_spec j 9); [lia | reflexivity]. }
assert (HB0 : 0 <= cf_cb (l_pl cx) 0 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB1 : 0 <= cf_cb (l_pl cx) 1 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB2 : 0 <= cf_cb (l_pl cx) 2 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB3 : 0 <= cf_cb (l_pl cx) 3 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB4 : 0 <= cf_cb (l_pl cx) 4 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB5 : 0 <= cf_cb (l_pl cx) 5 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB6 : 0 <= cf_cb (l_pl cx) 6 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB7 : 0 <= cf_cb (l_pl cx) 7 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB8 : 0 <= cf_cb (l_pl cx) 8 < 256) by (unfold cf_cb; apply cf_b_rng).
set (bs := [cf_cb (l_pl cx) 0; cf_cb (l_pl cx) 1; cf_cb (l_pl cx) 2; cf_cb (l_pl cx) 3; cf_cb (l_pl cx) 4; cf_cb (l_pl cx) 5; cf_cb (l_pl cx) 6; cf_cb (l_pl cx) 7; cf_cb (l_pl cx) 8]).
assert (HBrng : forall j, (j < 9)%nat -> 0 <= nth j bs 0 < 256).
{ intros j Hj. unfold bs. destruct j as [|[|[|[|[|[|[|[|[|]]]]]]]]]; cbn [nth]; first [exact HB0 | exact HB0 | exact HB1 | exact HB2 | exact HB3 | exact HB4 | exact HB5 | exact HB6 | exact HB7 | exact HB8 | lia]. }
assert (HBval : forall j, (j < 9)%nat ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j bs 0)).
{ intros j Hj.
  replace (nth j bs 0) with (cf_cb (l_pl cx) (Z.of_nat j))
    by (unfold bs; destruct j as [|[|[|[|[|[|[|[|[|]]]]]]]]]; cbn [nth Z.of_nat]; reflexivity || lia).
  apply (cf_in_bytes cx ly' S' W regs mem md j HC). lia. }
assert (HBden : forall j, (j < 9)%nat ->
  bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (32 + j)) = nth j bs 0)
  by (intros j Hj; apply cf_ex_val; [lia | exact (HBrng j Hj)]).
assert (UB0 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 32)
  = cf_cb (l_pl cx) 0)
  by (pose proof (HBden 0%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB1 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 33)
  = cf_cb (l_pl cx) 1)
  by (pose proof (HBden 1%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB2 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 34)
  = cf_cb (l_pl cx) 2)
  by (pose proof (HBden 2%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB3 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 35)
  = cf_cb (l_pl cx) 3)
  by (pose proof (HBden 3%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB4 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 36)
  = cf_cb (l_pl cx) 4)
  by (pose proof (HBden 4%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB5 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 37)
  = cf_cb (l_pl cx) 5)
  by (pose proof (HBden 5%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB6 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 38)
  = cf_cb (l_pl cx) 6)
  by (pose proof (HBden 6%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB7 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 39)
  = cf_cb (l_pl cx) 7)
  by (pose proof (HBden 7%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB8 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 40)
  = cf_cb (l_pl cx) 8)
  by (pose proof (HBden 8%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (EPC : w64 (transport_text + CF_SC) = Z_to_bv 64 (BASE + CF_SC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (HEI : img_env VAL A_LIM (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))) by apply cf_E_img.
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (cf_ssp 9)
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_SC)) mem (YK11.seg_rom segs)))).
{ unfold cf_ssp. apply (cf_seat cx ly' S' W regs mem md _ 9 bs _ CF_SC _ LAWS HB HC HJ).
  - apply cf_regs_pin. exact R27.
  - exact (cf_facts cx regs _ 9 bs G9 ltac:(lia) N3 R19 ltac:(lia) G21 R23 G26 HBden HBrng).
  - exact G9.
  - exact R19.
  - exact G21.
  - exact Hn0.
  - lia.
  - exact HBden.
  - exact HBrng.
  - exact HBval. }
assert (U19 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs _ 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs _ 26%nat 26%bv eq_refl), G26; apply cf_u64; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs cf_Bx (cf_SH 9) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))
  (mrestrict (w_H W) mem))
  by exact (cf_shok cx ly' S' W regs mem md _ 9 LAWS HB HC Hn0 ltac:(lia) U19 U26).
assert (V21 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs _ 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs _ 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
assert (V23 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs _ 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 8%nat ltac:(lia)) as V8h.
change (A_HI 8) with 408%nat in V8h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 9%nat ltac:(lia)) as V9h.
change (A_HI 9) with 409%nat in V9h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 10%nat ltac:(lia)) as V10h.
change (A_HI 10) with 410%nat in V10h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 11%nat ltac:(lia)) as V11h.
change (A_HI 11) with 411%nat in V11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x318.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V21 in Ha;
     apply cf_cfg_inG; lia|].
  do 4 (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|]).
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V8h in Ha;
     apply cf_glob_inG; left; unfold TA_g_raw; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9h in Ha;
     apply cf_glob_inG; right; left; unfold TA_g_now; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V10h in Ha;
     apply cf_glob_inG; right; right; left; unfold TA_g_fail_next; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V11h in Ha;
     apply cf_glob_inG; right; right; right; unfold TA_g_last_counter; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
cf_ag (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)).
lazymatch goal with
| HA : env_agree 512 (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) ?ER |- _ =>
  assert (W21 : bv_unsigned (ew ER 21) = TA_g_cfg)
    by (first [ exact V21
              | rewrite <- (proj1 HA 21%nat ltac:(lia)); exact V21
              | rewrite (proj1 HA 21%nat ltac:(lia)); exact V21 ]);
  assert (W9 : bv_unsigned (ew ER 9) = lc_sp1 cx)
    by (first [ exact V9
              | rewrite <- (proj1 HA 9%nat ltac:(lia)); exact V9
              | rewrite (proj1 HA 9%nat ltac:(lia)); exact V9 ]);
  assert (W8h : bv_unsigned (ew ER 408) = 6157588)
    by (first [ exact V8h
              | rewrite <- (proj1 HA 408%nat ltac:(lia)); exact V8h
              | rewrite (proj1 HA 408%nat ltac:(lia)); exact V8h ]);
  assert (W9h : bv_unsigned (ew ER 409) = 6157596)
    by (first [ exact V9h
              | rewrite <- (proj1 HA 409%nat ltac:(lia)); exact V9h
              | rewrite (proj1 HA 409%nat ltac:(lia)); exact V9h ]);
  assert (W10h : bv_unsigned (ew ER 410) = 6157652)
    by (first [ exact V10h
              | rewrite <- (proj1 HA 410%nat ltac:(lia)); exact V10h
              | rewrite (proj1 HA 410%nat ltac:(lia)); exact V10h ]);
  assert (W11h : bv_unsigned (ew ER 411) = 6157672)
    by (first [ exact V11h
              | rewrite <- (proj1 HA 411%nat ltac:(lia)); exact V11h
              | rewrite (proj1 HA 411%nat ltac:(lia)); exact V11h ])
end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wrun cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hw. apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wrun cx) HFr); [|exact Ha | exact Hw].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-|]); [..|destruct Hin].
  - cbn [base_val] in Hx. lia.
  - cbn [base_val] in Hx; rewrite V21 in Hx. unfold cf_wrun. left. unfold TA_g_cfg in *. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; right. lia.
  - cbn [base_val] in Hx; rewrite V8h in Hx. unfold cf_wrun. right; left. unfold TA_g_raw. lia.
  - cbn [base_val] in Hx; rewrite V9h in Hx. unfold cf_wrun. right; right; left. unfold TA_g_now. lia.
  - cbn [base_val] in Hx; rewrite V10h in Hx. unfold cf_wrun.
    right; right; right; left. unfold TA_g_fail_next. lia.
  - cbn [base_val] in Hx; rewrite V11h in Hx. unfold cf_wrun.
    right; right; right; right; left. unfold TA_g_last_counter. lia. }
assert (KA : cf_KV cx W mem0 (ms_mem ms)).
{ intros a Ha Hw. rewrite (KF a Ha ltac:(intros C; apply Hw; unfold cf_wrun, cf_wr in *; lia)).
  exact (KV a Ha Hw). }
assert (GA : cf_GP W mem0 (ms_mem ms))
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GP a Ha))).
assert (KG : forall a, TA_g_cfg <= a < TA_g_cfg + 24 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply KF; [unfold TA_g_cfg in *; lia|].
  unfold cf_wrun, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 9 _ HS eq_refl) as RG9.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
assert (F24 : cf_bw W (ms_mem ms) (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 24 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 34 0) (SAlu ALU_SLL (SOff 35 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB2 HB3). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F28 : cf_bw W (ms_mem ms) (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 28 4%N (SOff 33 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  apply cf_m32.
  - cbn. lia. }
assert (F32 : cf_bw W (ms_mem ms) (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 32 4%N (SAlu ALU_AND (SOff 32 0) (SLit 7)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f32 _ HB0). reflexivity.
  - apply cf_m8.
  - cbn. lia. }
assert (F36 : cf_bw W (ms_mem ms) (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 36 4%N (SOff 36 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  cf_rval.
  -  cbn [Z.of_N]. pose proof HB4. lia.
  - cbn. lia. }
assert (F40 : cf_bw W (ms_mem ms) (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 40 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 37 0) (SAlu ALU_SLL (SOff 38 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB5 HB6). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F44 : cf_bw W (ms_mem ms) (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 44 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 39 0) (SAlu ALU_SLL (SOff 40 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB7 HB8). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F48 : cf_bw W (ms_mem ms) (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 48 4%N (SLit 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cf_rval.
  -  rewrite (Hz 9 ltac:(lia)). rewrite (Hz 10 ltac:(lia)). cbn [Z.of_N]. lia.
  - cbn. lia. }
assert (F52 : cf_bw W (ms_mem ms) (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 52 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 11 ltac:(lia)). cf_rval.
  -  rewrite (Hz 11 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F56 : cf_bw W (ms_mem ms) (TA_g_cfg + 56) 4 ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
      mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 56 4%N (SLit 24) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). cf_rval.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (GRAW : cf_bw W (ms_mem ms) TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 408%nat _ _ _ _ _ _ (-1076) 4%N
    (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 60)) (SLit 63)) _ RG6 W8h _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 3)
      ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (GNOW : cf_bw W (ms_mem ms) TA_g_now 8 1000000)
  by (cf_gl RG7 W9h 409%nat (-1052) 8%nat 8%N (SLit 1000000) ltac:(cf_rval)).
assert (GFAIL : cf_bw W (ms_mem ms) TA_g_fail_next 1 0)
  by (cf_gl RG8 W10h 410%nat (-1076) 1%nat 1%N (SLit 0) ltac:(cf_rval)).
assert (GLAST : cf_bw W (ms_mem ms) TA_g_last_counter 4 0)
  by (cf_gl RG9 W11h 411%nat (-1064) 4%nat 4%N (SLit 0) ltac:(cf_rval)).
assert (SP48 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 48) = Some (transport_hi 11))
  by (cf_sp RG2 W9 48 (SOff 411 0)).
assert (SP120 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 120) = Some (transport_hi 8))
  by (cf_sp RG3 W9 120 (SOff 408 0)).
assert (SP160 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 160) = Some (transport_hi 10))
  by (cf_sp RG4 W9 160 (SOff 410 0)).
assert (SP176 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 176) = Some (transport_hi 9))
  by (cf_sp RG5 W9 176 (SOff 409 0)).
assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs (map (fun v : Z => Z_to_bv 64 v) bs) _ HS _ _ r Hr);
    [apply cf_agree; assumption | vm_compute; reflexivity]. }
cf_rd HS (Z_to_bv 5 25) (w64 (l_p cx + 1 + 9)) Y25
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; first [reflexivity | f_equal; lia]).
cf_rd HS (Z_to_bv 5 27) (w64 0) Y27 ltac:(reflexivity).
pmkst HS.
apply SRr_ret.
apply (cf_close cx ly' S' W regs0 mem0 md0 Bw0 B1 (ms_regs ms) (ms_mem ms) md1 LAWS HB HC0 HSP HFS HIO HMT
  HW0 ECD HTW HJ KA GA).
- intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H0 i Hi).
- intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H6 i Hi).
- intros j Hj. rewrite (KG (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H12 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H16 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H20 j Hj).
- exact F24.
- exact F28.
- exact F32.
- exact F36.
- exact F40.
- exact F44.
- exact F48.
- exact F52.
- exact F56.
- exact GRAW.
- exact GNOW.
- exact GFAIL.
- exact GLAST.
- exact SP120.
- exact SP176.
- exact SP160.
- exact SP48.
- unfold cf_regs.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
    (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
    (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
  exact HRG.
- rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- unfold lc_cur. rewrite cf_cursor. cbn [TOP.fi_off TOP.fi_n]. rewrite Coff.
  rewrite Hk. change (Z.min 9 14) with 9.
  split; [rewrite Y25; unfold w64; f_equal; lia | rewrite Y27; unfold w64; f_equal; lia].
Qed.

Lemma cf_case10 : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md -> cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_bl W mem (TA_g_cfg + 0) TC.HOST -> cf_bl W mem (TA_g_cfg + 6) TC.DESK ->
  cf_bw W mem (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W mem (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W mem (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> TOP.fi_n (lc_c1 (l_pl cx)) = 10 ->
  SRr segs W (lc_cfg cx CF_SC regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regs mem md HP HB HC0 HSP HFS HIO HMT HW0 ECD HTW
  HC HJ KV GP H0 H6 H12 H16 H20 HRG R23 R22 HCUR Hk.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
destruct (cf_c1_pos (l_pl cx) ltac:(lia)) as (Coff & Cn & Clen).
assert (Hn0 : 0 < l_n cx) by lia.
assert (R19 : YK11.getr regs (Z_to_bv 5 19) = w64 (l_p cx + 1)) by (rewrite C19, Coff; reflexivity).
assert (R27 : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 10) by (rewrite C27, Hk; reflexivity).
assert (Hz : forall j, 10 <= j -> cf_cb (l_pl cx) j = 0).
{ intros j Hj. unfold cf_cb, cf_b. rewrite Hk.
  destruct (Z.ltb_spec j 10); [lia | reflexivity]. }
assert (HB0 : 0 <= cf_cb (l_pl cx) 0 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB1 : 0 <= cf_cb (l_pl cx) 1 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB2 : 0 <= cf_cb (l_pl cx) 2 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB3 : 0 <= cf_cb (l_pl cx) 3 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB4 : 0 <= cf_cb (l_pl cx) 4 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB5 : 0 <= cf_cb (l_pl cx) 5 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB6 : 0 <= cf_cb (l_pl cx) 6 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB7 : 0 <= cf_cb (l_pl cx) 7 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB8 : 0 <= cf_cb (l_pl cx) 8 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB9 : 0 <= cf_cb (l_pl cx) 9 < 256) by (unfold cf_cb; apply cf_b_rng).
set (bs := [cf_cb (l_pl cx) 0; cf_cb (l_pl cx) 1; cf_cb (l_pl cx) 2; cf_cb (l_pl cx) 3; cf_cb (l_pl cx) 4; cf_cb (l_pl cx) 5; cf_cb (l_pl cx) 6; cf_cb (l_pl cx) 7; cf_cb (l_pl cx) 8; cf_cb (l_pl cx) 9]).
assert (HBrng : forall j, (j < 10)%nat -> 0 <= nth j bs 0 < 256).
{ intros j Hj. unfold bs. destruct j as [|[|[|[|[|[|[|[|[|[|]]]]]]]]]]; cbn [nth]; first [exact HB0 | exact HB0 | exact HB1 | exact HB2 | exact HB3 | exact HB4 | exact HB5 | exact HB6 | exact HB7 | exact HB8 | exact HB9 | lia]. }
assert (HBval : forall j, (j < 10)%nat ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j bs 0)).
{ intros j Hj.
  replace (nth j bs 0) with (cf_cb (l_pl cx) (Z.of_nat j))
    by (unfold bs; destruct j as [|[|[|[|[|[|[|[|[|[|]]]]]]]]]]; cbn [nth Z.of_nat]; reflexivity || lia).
  apply (cf_in_bytes cx ly' S' W regs mem md j HC). lia. }
assert (HBden : forall j, (j < 10)%nat ->
  bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (32 + j)) = nth j bs 0)
  by (intros j Hj; apply cf_ex_val; [lia | exact (HBrng j Hj)]).
assert (UB0 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 32)
  = cf_cb (l_pl cx) 0)
  by (pose proof (HBden 0%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB1 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 33)
  = cf_cb (l_pl cx) 1)
  by (pose proof (HBden 1%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB2 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 34)
  = cf_cb (l_pl cx) 2)
  by (pose proof (HBden 2%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB3 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 35)
  = cf_cb (l_pl cx) 3)
  by (pose proof (HBden 3%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB4 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 36)
  = cf_cb (l_pl cx) 4)
  by (pose proof (HBden 4%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB5 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 37)
  = cf_cb (l_pl cx) 5)
  by (pose proof (HBden 5%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB6 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 38)
  = cf_cb (l_pl cx) 6)
  by (pose proof (HBden 6%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB7 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 39)
  = cf_cb (l_pl cx) 7)
  by (pose proof (HBden 7%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB8 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 40)
  = cf_cb (l_pl cx) 8)
  by (pose proof (HBden 8%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 41)
  = cf_cb (l_pl cx) 9)
  by (pose proof (HBden 9%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (EPC : w64 (transport_text + CF_SC) = Z_to_bv 64 (BASE + CF_SC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (HEI : img_env VAL A_LIM (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))) by apply cf_E_img.
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (cf_ssp 10)
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_SC)) mem (YK11.seg_rom segs)))).
{ unfold cf_ssp. apply (cf_seat cx ly' S' W regs mem md _ 10 bs _ CF_SC _ LAWS HB HC HJ).
  - apply cf_regs_pin. exact R27.
  - exact (cf_facts cx regs _ 10 bs G9 ltac:(lia) N3 R19 ltac:(lia) G21 R23 G26 HBden HBrng).
  - exact G9.
  - exact R19.
  - exact G21.
  - exact Hn0.
  - lia.
  - exact HBden.
  - exact HBrng.
  - exact HBval. }
assert (U19 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs _ 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs _ 26%nat 26%bv eq_refl), G26; apply cf_u64; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs cf_Bx (cf_SH 10) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))
  (mrestrict (w_H W) mem))
  by exact (cf_shok cx ly' S' W regs mem md _ 10 LAWS HB HC Hn0 ltac:(lia) U19 U26).
assert (V21 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs _ 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs _ 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
assert (V23 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs _ 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 8%nat ltac:(lia)) as V8h.
change (A_HI 8) with 408%nat in V8h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 9%nat ltac:(lia)) as V9h.
change (A_HI 9) with 409%nat in V9h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 10%nat ltac:(lia)) as V10h.
change (A_HI 10) with 410%nat in V10h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 11%nat ltac:(lia)) as V11h.
change (A_HI 11) with 411%nat in V11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x318.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V21 in Ha;
     apply cf_cfg_inG; lia|].
  do 4 (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|]).
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V8h in Ha;
     apply cf_glob_inG; left; unfold TA_g_raw; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9h in Ha;
     apply cf_glob_inG; right; left; unfold TA_g_now; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V10h in Ha;
     apply cf_glob_inG; right; right; left; unfold TA_g_fail_next; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V11h in Ha;
     apply cf_glob_inG; right; right; right; unfold TA_g_last_counter; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
cf_ag (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)).
lazymatch goal with
| HA : env_agree 512 (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) ?ER |- _ =>
  assert (W21 : bv_unsigned (ew ER 21) = TA_g_cfg)
    by (first [ exact V21
              | rewrite <- (proj1 HA 21%nat ltac:(lia)); exact V21
              | rewrite (proj1 HA 21%nat ltac:(lia)); exact V21 ]);
  assert (W9 : bv_unsigned (ew ER 9) = lc_sp1 cx)
    by (first [ exact V9
              | rewrite <- (proj1 HA 9%nat ltac:(lia)); exact V9
              | rewrite (proj1 HA 9%nat ltac:(lia)); exact V9 ]);
  assert (W8h : bv_unsigned (ew ER 408) = 6157588)
    by (first [ exact V8h
              | rewrite <- (proj1 HA 408%nat ltac:(lia)); exact V8h
              | rewrite (proj1 HA 408%nat ltac:(lia)); exact V8h ]);
  assert (W9h : bv_unsigned (ew ER 409) = 6157596)
    by (first [ exact V9h
              | rewrite <- (proj1 HA 409%nat ltac:(lia)); exact V9h
              | rewrite (proj1 HA 409%nat ltac:(lia)); exact V9h ]);
  assert (W10h : bv_unsigned (ew ER 410) = 6157652)
    by (first [ exact V10h
              | rewrite <- (proj1 HA 410%nat ltac:(lia)); exact V10h
              | rewrite (proj1 HA 410%nat ltac:(lia)); exact V10h ]);
  assert (W11h : bv_unsigned (ew ER 411) = 6157672)
    by (first [ exact V11h
              | rewrite <- (proj1 HA 411%nat ltac:(lia)); exact V11h
              | rewrite (proj1 HA 411%nat ltac:(lia)); exact V11h ])
end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wrun cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hw. apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wrun cx) HFr); [|exact Ha | exact Hw].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-|]); [..|destruct Hin].
  - cbn [base_val] in Hx. lia.
  - cbn [base_val] in Hx; rewrite V21 in Hx. unfold cf_wrun. left. unfold TA_g_cfg in *. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; right. lia.
  - cbn [base_val] in Hx; rewrite V8h in Hx. unfold cf_wrun. right; left. unfold TA_g_raw. lia.
  - cbn [base_val] in Hx; rewrite V9h in Hx. unfold cf_wrun. right; right; left. unfold TA_g_now. lia.
  - cbn [base_val] in Hx; rewrite V10h in Hx. unfold cf_wrun.
    right; right; right; left. unfold TA_g_fail_next. lia.
  - cbn [base_val] in Hx; rewrite V11h in Hx. unfold cf_wrun.
    right; right; right; right; left. unfold TA_g_last_counter. lia. }
assert (KA : cf_KV cx W mem0 (ms_mem ms)).
{ intros a Ha Hw. rewrite (KF a Ha ltac:(intros C; apply Hw; unfold cf_wrun, cf_wr in *; lia)).
  exact (KV a Ha Hw). }
assert (GA : cf_GP W mem0 (ms_mem ms))
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GP a Ha))).
assert (KG : forall a, TA_g_cfg <= a < TA_g_cfg + 24 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply KF; [unfold TA_g_cfg in *; lia|].
  unfold cf_wrun, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 9 _ HS eq_refl) as RG9.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
assert (F24 : cf_bw W (ms_mem ms) (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 24 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 34 0) (SAlu ALU_SLL (SOff 35 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB2 HB3). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F28 : cf_bw W (ms_mem ms) (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 28 4%N (SOff 33 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  apply cf_m32.
  - cbn. lia. }
assert (F32 : cf_bw W (ms_mem ms) (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 32 4%N (SAlu ALU_AND (SOff 32 0) (SLit 7)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f32 _ HB0). reflexivity.
  - apply cf_m8.
  - cbn. lia. }
assert (F36 : cf_bw W (ms_mem ms) (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 36 4%N (SOff 36 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  cf_rval.
  -  cbn [Z.of_N]. pose proof HB4. lia.
  - cbn. lia. }
assert (F40 : cf_bw W (ms_mem ms) (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 40 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 37 0) (SAlu ALU_SLL (SOff 38 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB5 HB6). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F44 : cf_bw W (ms_mem ms) (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 44 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 39 0) (SAlu ALU_SLL (SOff 40 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB7 HB8). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F48 : cf_bw W (ms_mem ms) (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 48 4%N (SOff 41 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 10 ltac:(lia)). cf_rval.
  -  rewrite (Hz 10 ltac:(lia)). cbn [Z.of_N]. pose proof HB9. lia.
  - cbn. lia. }
assert (F52 : cf_bw W (ms_mem ms) (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 52 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 11 ltac:(lia)). cf_rval.
  -  rewrite (Hz 11 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F56 : cf_bw W (ms_mem ms) (TA_g_cfg + 56) 4 ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
      mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 56 4%N (SLit 24) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). cf_rval.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (GRAW : cf_bw W (ms_mem ms) TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 408%nat _ _ _ _ _ _ (-1076) 4%N
    (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 60)) (SLit 63)) _ RG6 W8h _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 3)
      ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (GNOW : cf_bw W (ms_mem ms) TA_g_now 8 1000000)
  by (cf_gl RG7 W9h 409%nat (-1052) 8%nat 8%N (SLit 1000000) ltac:(cf_rval)).
assert (GFAIL : cf_bw W (ms_mem ms) TA_g_fail_next 1 0)
  by (cf_gl RG8 W10h 410%nat (-1076) 1%nat 1%N (SLit 0) ltac:(cf_rval)).
assert (GLAST : cf_bw W (ms_mem ms) TA_g_last_counter 4 0)
  by (cf_gl RG9 W11h 411%nat (-1064) 4%nat 4%N (SLit 0) ltac:(cf_rval)).
assert (SP48 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 48) = Some (transport_hi 11))
  by (cf_sp RG2 W9 48 (SOff 411 0)).
assert (SP120 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 120) = Some (transport_hi 8))
  by (cf_sp RG3 W9 120 (SOff 408 0)).
assert (SP160 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 160) = Some (transport_hi 10))
  by (cf_sp RG4 W9 160 (SOff 410 0)).
assert (SP176 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 176) = Some (transport_hi 9))
  by (cf_sp RG5 W9 176 (SOff 409 0)).
assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs (map (fun v : Z => Z_to_bv 64 v) bs) _ HS _ _ r Hr);
    [apply cf_agree; assumption | vm_compute; reflexivity]. }
cf_rd HS (Z_to_bv 5 25) (w64 (l_p cx + 1 + 10)) Y25
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; first [reflexivity | f_equal; lia]).
cf_rd HS (Z_to_bv 5 27) (w64 0) Y27 ltac:(reflexivity).
pmkst HS.
apply SRr_ret.
apply (cf_close cx ly' S' W regs0 mem0 md0 Bw0 B1 (ms_regs ms) (ms_mem ms) md1 LAWS HB HC0 HSP HFS HIO HMT
  HW0 ECD HTW HJ KA GA).
- intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H0 i Hi).
- intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H6 i Hi).
- intros j Hj. rewrite (KG (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H12 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H16 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H20 j Hj).
- exact F24.
- exact F28.
- exact F32.
- exact F36.
- exact F40.
- exact F44.
- exact F48.
- exact F52.
- exact F56.
- exact GRAW.
- exact GNOW.
- exact GFAIL.
- exact GLAST.
- exact SP120.
- exact SP176.
- exact SP160.
- exact SP48.
- unfold cf_regs.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
    (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
    (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
  exact HRG.
- rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- unfold lc_cur. rewrite cf_cursor. cbn [TOP.fi_off TOP.fi_n]. rewrite Coff.
  rewrite Hk. change (Z.min 10 14) with 10.
  split; [rewrite Y25; unfold w64; f_equal; lia | rewrite Y27; unfold w64; f_equal; lia].
Qed.

Lemma cf_case11 : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md -> cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_bl W mem (TA_g_cfg + 0) TC.HOST -> cf_bl W mem (TA_g_cfg + 6) TC.DESK ->
  cf_bw W mem (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W mem (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W mem (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> TOP.fi_n (lc_c1 (l_pl cx)) = 11 ->
  SRr segs W (lc_cfg cx CF_SC regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regs mem md HP HB HC0 HSP HFS HIO HMT HW0 ECD HTW
  HC HJ KV GP H0 H6 H12 H16 H20 HRG R23 R22 HCUR Hk.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
destruct (cf_c1_pos (l_pl cx) ltac:(lia)) as (Coff & Cn & Clen).
assert (Hn0 : 0 < l_n cx) by lia.
assert (R19 : YK11.getr regs (Z_to_bv 5 19) = w64 (l_p cx + 1)) by (rewrite C19, Coff; reflexivity).
assert (R27 : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 11) by (rewrite C27, Hk; reflexivity).
assert (Hz : forall j, 11 <= j -> cf_cb (l_pl cx) j = 0).
{ intros j Hj. unfold cf_cb, cf_b. rewrite Hk.
  destruct (Z.ltb_spec j 11); [lia | reflexivity]. }
assert (HB0 : 0 <= cf_cb (l_pl cx) 0 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB1 : 0 <= cf_cb (l_pl cx) 1 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB2 : 0 <= cf_cb (l_pl cx) 2 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB3 : 0 <= cf_cb (l_pl cx) 3 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB4 : 0 <= cf_cb (l_pl cx) 4 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB5 : 0 <= cf_cb (l_pl cx) 5 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB6 : 0 <= cf_cb (l_pl cx) 6 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB7 : 0 <= cf_cb (l_pl cx) 7 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB8 : 0 <= cf_cb (l_pl cx) 8 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB9 : 0 <= cf_cb (l_pl cx) 9 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB10 : 0 <= cf_cb (l_pl cx) 10 < 256) by (unfold cf_cb; apply cf_b_rng).
set (bs := [cf_cb (l_pl cx) 0; cf_cb (l_pl cx) 1; cf_cb (l_pl cx) 2; cf_cb (l_pl cx) 3; cf_cb (l_pl cx) 4; cf_cb (l_pl cx) 5; cf_cb (l_pl cx) 6; cf_cb (l_pl cx) 7; cf_cb (l_pl cx) 8; cf_cb (l_pl cx) 9; cf_cb (l_pl cx) 10]).
assert (HBrng : forall j, (j < 11)%nat -> 0 <= nth j bs 0 < 256).
{ intros j Hj. unfold bs. destruct j as [|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]; cbn [nth]; first [exact HB0 | exact HB0 | exact HB1 | exact HB2 | exact HB3 | exact HB4 | exact HB5 | exact HB6 | exact HB7 | exact HB8 | exact HB9 | exact HB10 | lia]. }
assert (HBval : forall j, (j < 11)%nat ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j bs 0)).
{ intros j Hj.
  replace (nth j bs 0) with (cf_cb (l_pl cx) (Z.of_nat j))
    by (unfold bs; destruct j as [|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]; cbn [nth Z.of_nat]; reflexivity || lia).
  apply (cf_in_bytes cx ly' S' W regs mem md j HC). lia. }
assert (HBden : forall j, (j < 11)%nat ->
  bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (32 + j)) = nth j bs 0)
  by (intros j Hj; apply cf_ex_val; [lia | exact (HBrng j Hj)]).
assert (UB0 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 32)
  = cf_cb (l_pl cx) 0)
  by (pose proof (HBden 0%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB1 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 33)
  = cf_cb (l_pl cx) 1)
  by (pose proof (HBden 1%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB2 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 34)
  = cf_cb (l_pl cx) 2)
  by (pose proof (HBden 2%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB3 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 35)
  = cf_cb (l_pl cx) 3)
  by (pose proof (HBden 3%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB4 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 36)
  = cf_cb (l_pl cx) 4)
  by (pose proof (HBden 4%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB5 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 37)
  = cf_cb (l_pl cx) 5)
  by (pose proof (HBden 5%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB6 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 38)
  = cf_cb (l_pl cx) 6)
  by (pose proof (HBden 6%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB7 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 39)
  = cf_cb (l_pl cx) 7)
  by (pose proof (HBden 7%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB8 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 40)
  = cf_cb (l_pl cx) 8)
  by (pose proof (HBden 8%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 41)
  = cf_cb (l_pl cx) 9)
  by (pose proof (HBden 9%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB10 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 42)
  = cf_cb (l_pl cx) 10)
  by (pose proof (HBden 10%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (EPC : w64 (transport_text + CF_SC) = Z_to_bv 64 (BASE + CF_SC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (HEI : img_env VAL A_LIM (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))) by apply cf_E_img.
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (cf_ssp 11)
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_SC)) mem (YK11.seg_rom segs)))).
{ unfold cf_ssp. apply (cf_seat cx ly' S' W regs mem md _ 11 bs _ CF_SC _ LAWS HB HC HJ).
  - apply cf_regs_pin. exact R27.
  - exact (cf_facts cx regs _ 11 bs G9 ltac:(lia) N3 R19 ltac:(lia) G21 R23 G26 HBden HBrng).
  - exact G9.
  - exact R19.
  - exact G21.
  - exact Hn0.
  - lia.
  - exact HBden.
  - exact HBrng.
  - exact HBval. }
assert (U19 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs _ 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs _ 26%nat 26%bv eq_refl), G26; apply cf_u64; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs cf_Bx (cf_SH 11) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))
  (mrestrict (w_H W) mem))
  by exact (cf_shok cx ly' S' W regs mem md _ 11 LAWS HB HC Hn0 ltac:(lia) U19 U26).
assert (V21 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs _ 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs _ 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
assert (V23 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs _ 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 8%nat ltac:(lia)) as V8h.
change (A_HI 8) with 408%nat in V8h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 9%nat ltac:(lia)) as V9h.
change (A_HI 9) with 409%nat in V9h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 10%nat ltac:(lia)) as V10h.
change (A_HI 10) with 410%nat in V10h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 11%nat ltac:(lia)) as V11h.
change (A_HI 11) with 411%nat in V11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x318.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V21 in Ha;
     apply cf_cfg_inG; lia|].
  do 4 (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|]).
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V8h in Ha;
     apply cf_glob_inG; left; unfold TA_g_raw; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9h in Ha;
     apply cf_glob_inG; right; left; unfold TA_g_now; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V10h in Ha;
     apply cf_glob_inG; right; right; left; unfold TA_g_fail_next; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V11h in Ha;
     apply cf_glob_inG; right; right; right; unfold TA_g_last_counter; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
cf_ag (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)).
lazymatch goal with
| HA : env_agree 512 (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) ?ER |- _ =>
  assert (W21 : bv_unsigned (ew ER 21) = TA_g_cfg)
    by (first [ exact V21
              | rewrite <- (proj1 HA 21%nat ltac:(lia)); exact V21
              | rewrite (proj1 HA 21%nat ltac:(lia)); exact V21 ]);
  assert (W9 : bv_unsigned (ew ER 9) = lc_sp1 cx)
    by (first [ exact V9
              | rewrite <- (proj1 HA 9%nat ltac:(lia)); exact V9
              | rewrite (proj1 HA 9%nat ltac:(lia)); exact V9 ]);
  assert (W8h : bv_unsigned (ew ER 408) = 6157588)
    by (first [ exact V8h
              | rewrite <- (proj1 HA 408%nat ltac:(lia)); exact V8h
              | rewrite (proj1 HA 408%nat ltac:(lia)); exact V8h ]);
  assert (W9h : bv_unsigned (ew ER 409) = 6157596)
    by (first [ exact V9h
              | rewrite <- (proj1 HA 409%nat ltac:(lia)); exact V9h
              | rewrite (proj1 HA 409%nat ltac:(lia)); exact V9h ]);
  assert (W10h : bv_unsigned (ew ER 410) = 6157652)
    by (first [ exact V10h
              | rewrite <- (proj1 HA 410%nat ltac:(lia)); exact V10h
              | rewrite (proj1 HA 410%nat ltac:(lia)); exact V10h ]);
  assert (W11h : bv_unsigned (ew ER 411) = 6157672)
    by (first [ exact V11h
              | rewrite <- (proj1 HA 411%nat ltac:(lia)); exact V11h
              | rewrite (proj1 HA 411%nat ltac:(lia)); exact V11h ])
end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wrun cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hw. apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wrun cx) HFr); [|exact Ha | exact Hw].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-|]); [..|destruct Hin].
  - cbn [base_val] in Hx. lia.
  - cbn [base_val] in Hx; rewrite V21 in Hx. unfold cf_wrun. left. unfold TA_g_cfg in *. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; right. lia.
  - cbn [base_val] in Hx; rewrite V8h in Hx. unfold cf_wrun. right; left. unfold TA_g_raw. lia.
  - cbn [base_val] in Hx; rewrite V9h in Hx. unfold cf_wrun. right; right; left. unfold TA_g_now. lia.
  - cbn [base_val] in Hx; rewrite V10h in Hx. unfold cf_wrun.
    right; right; right; left. unfold TA_g_fail_next. lia.
  - cbn [base_val] in Hx; rewrite V11h in Hx. unfold cf_wrun.
    right; right; right; right; left. unfold TA_g_last_counter. lia. }
assert (KA : cf_KV cx W mem0 (ms_mem ms)).
{ intros a Ha Hw. rewrite (KF a Ha ltac:(intros C; apply Hw; unfold cf_wrun, cf_wr in *; lia)).
  exact (KV a Ha Hw). }
assert (GA : cf_GP W mem0 (ms_mem ms))
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GP a Ha))).
assert (KG : forall a, TA_g_cfg <= a < TA_g_cfg + 24 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply KF; [unfold TA_g_cfg in *; lia|].
  unfold cf_wrun, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 9 _ HS eq_refl) as RG9.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
assert (F24 : cf_bw W (ms_mem ms) (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 24 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 34 0) (SAlu ALU_SLL (SOff 35 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB2 HB3). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F28 : cf_bw W (ms_mem ms) (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 28 4%N (SOff 33 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  apply cf_m32.
  - cbn. lia. }
assert (F32 : cf_bw W (ms_mem ms) (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 32 4%N (SAlu ALU_AND (SOff 32 0) (SLit 7)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f32 _ HB0). reflexivity.
  - apply cf_m8.
  - cbn. lia. }
assert (F36 : cf_bw W (ms_mem ms) (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 36 4%N (SOff 36 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  cf_rval.
  -  cbn [Z.of_N]. pose proof HB4. lia.
  - cbn. lia. }
assert (F40 : cf_bw W (ms_mem ms) (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 40 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 37 0) (SAlu ALU_SLL (SOff 38 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB5 HB6). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F44 : cf_bw W (ms_mem ms) (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 44 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 39 0) (SAlu ALU_SLL (SOff 40 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB7 HB8). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F48 : cf_bw W (ms_mem ms) (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 48 4%N (SAlu ALU_OR (SAlu ALU_SLL (SOff 42 0) (SLit 8)) (SOff 41 0)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16b _ _ HB9 HB10). reflexivity.
  - cbn [Z.of_N]. pose proof HB9. pose proof HB10. lia.
  - cbn. lia. }
assert (F52 : cf_bw W (ms_mem ms) (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 52 4%N (SLit 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 11 ltac:(lia)). cf_rval.
  -  rewrite (Hz 11 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (F56 : cf_bw W (ms_mem ms) (TA_g_cfg + 56) 4 ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
      mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 56 4%N (SLit 24) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). cf_rval.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (GRAW : cf_bw W (ms_mem ms) TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 408%nat _ _ _ _ _ _ (-1076) 4%N
    (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 60)) (SLit 63)) _ RG6 W8h _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 3)
      ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (GNOW : cf_bw W (ms_mem ms) TA_g_now 8 1000000)
  by (cf_gl RG7 W9h 409%nat (-1052) 8%nat 8%N (SLit 1000000) ltac:(cf_rval)).
assert (GFAIL : cf_bw W (ms_mem ms) TA_g_fail_next 1 0)
  by (cf_gl RG8 W10h 410%nat (-1076) 1%nat 1%N (SLit 0) ltac:(cf_rval)).
assert (GLAST : cf_bw W (ms_mem ms) TA_g_last_counter 4 0)
  by (cf_gl RG9 W11h 411%nat (-1064) 4%nat 4%N (SLit 0) ltac:(cf_rval)).
assert (SP48 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 48) = Some (transport_hi 11))
  by (cf_sp RG2 W9 48 (SOff 411 0)).
assert (SP120 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 120) = Some (transport_hi 8))
  by (cf_sp RG3 W9 120 (SOff 408 0)).
assert (SP160 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 160) = Some (transport_hi 10))
  by (cf_sp RG4 W9 160 (SOff 410 0)).
assert (SP176 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 176) = Some (transport_hi 9))
  by (cf_sp RG5 W9 176 (SOff 409 0)).
assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs (map (fun v : Z => Z_to_bv 64 v) bs) _ HS _ _ r Hr);
    [apply cf_agree; assumption | vm_compute; reflexivity]. }
cf_rd HS (Z_to_bv 5 25) (w64 (l_p cx + 1 + 11)) Y25
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; first [reflexivity | f_equal; lia]).
cf_rd HS (Z_to_bv 5 27) (w64 0) Y27 ltac:(reflexivity).
pmkst HS.
apply SRr_ret.
apply (cf_close cx ly' S' W regs0 mem0 md0 Bw0 B1 (ms_regs ms) (ms_mem ms) md1 LAWS HB HC0 HSP HFS HIO HMT
  HW0 ECD HTW HJ KA GA).
- intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H0 i Hi).
- intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H6 i Hi).
- intros j Hj. rewrite (KG (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H12 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H16 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H20 j Hj).
- exact F24.
- exact F28.
- exact F32.
- exact F36.
- exact F40.
- exact F44.
- exact F48.
- exact F52.
- exact F56.
- exact GRAW.
- exact GNOW.
- exact GFAIL.
- exact GLAST.
- exact SP120.
- exact SP176.
- exact SP160.
- exact SP48.
- unfold cf_regs.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
    (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
    (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
  exact HRG.
- rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- unfold lc_cur. rewrite cf_cursor. cbn [TOP.fi_off TOP.fi_n]. rewrite Coff.
  rewrite Hk. change (Z.min 11 14) with 11.
  split; [rewrite Y25; unfold w64; f_equal; lia | rewrite Y27; unfold w64; f_equal; lia].
Qed.

Lemma cf_case12 : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md -> cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_bl W mem (TA_g_cfg + 0) TC.HOST -> cf_bl W mem (TA_g_cfg + 6) TC.DESK ->
  cf_bw W mem (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W mem (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W mem (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> TOP.fi_n (lc_c1 (l_pl cx)) = 12 ->
  SRr segs W (lc_cfg cx CF_SC regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regs mem md HP HB HC0 HSP HFS HIO HMT HW0 ECD HTW
  HC HJ KV GP H0 H6 H12 H16 H20 HRG R23 R22 HCUR Hk.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
destruct (cf_c1_pos (l_pl cx) ltac:(lia)) as (Coff & Cn & Clen).
assert (Hn0 : 0 < l_n cx) by lia.
assert (R19 : YK11.getr regs (Z_to_bv 5 19) = w64 (l_p cx + 1)) by (rewrite C19, Coff; reflexivity).
assert (R27 : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 12) by (rewrite C27, Hk; reflexivity).
assert (Hz : forall j, 12 <= j -> cf_cb (l_pl cx) j = 0).
{ intros j Hj. unfold cf_cb, cf_b. rewrite Hk.
  destruct (Z.ltb_spec j 12); [lia | reflexivity]. }
assert (HB0 : 0 <= cf_cb (l_pl cx) 0 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB1 : 0 <= cf_cb (l_pl cx) 1 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB2 : 0 <= cf_cb (l_pl cx) 2 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB3 : 0 <= cf_cb (l_pl cx) 3 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB4 : 0 <= cf_cb (l_pl cx) 4 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB5 : 0 <= cf_cb (l_pl cx) 5 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB6 : 0 <= cf_cb (l_pl cx) 6 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB7 : 0 <= cf_cb (l_pl cx) 7 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB8 : 0 <= cf_cb (l_pl cx) 8 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB9 : 0 <= cf_cb (l_pl cx) 9 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB10 : 0 <= cf_cb (l_pl cx) 10 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB11 : 0 <= cf_cb (l_pl cx) 11 < 256) by (unfold cf_cb; apply cf_b_rng).
set (bs := [cf_cb (l_pl cx) 0; cf_cb (l_pl cx) 1; cf_cb (l_pl cx) 2; cf_cb (l_pl cx) 3; cf_cb (l_pl cx) 4; cf_cb (l_pl cx) 5; cf_cb (l_pl cx) 6; cf_cb (l_pl cx) 7; cf_cb (l_pl cx) 8; cf_cb (l_pl cx) 9; cf_cb (l_pl cx) 10; cf_cb (l_pl cx) 11]).
assert (HBrng : forall j, (j < 12)%nat -> 0 <= nth j bs 0 < 256).
{ intros j Hj. unfold bs. destruct j as [|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]; cbn [nth]; first [exact HB0 | exact HB0 | exact HB1 | exact HB2 | exact HB3 | exact HB4 | exact HB5 | exact HB6 | exact HB7 | exact HB8 | exact HB9 | exact HB10 | exact HB11 | lia]. }
assert (HBval : forall j, (j < 12)%nat ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j bs 0)).
{ intros j Hj.
  replace (nth j bs 0) with (cf_cb (l_pl cx) (Z.of_nat j))
    by (unfold bs; destruct j as [|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]; cbn [nth Z.of_nat]; reflexivity || lia).
  apply (cf_in_bytes cx ly' S' W regs mem md j HC). lia. }
assert (HBden : forall j, (j < 12)%nat ->
  bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (32 + j)) = nth j bs 0)
  by (intros j Hj; apply cf_ex_val; [lia | exact (HBrng j Hj)]).
assert (UB0 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 32)
  = cf_cb (l_pl cx) 0)
  by (pose proof (HBden 0%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB1 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 33)
  = cf_cb (l_pl cx) 1)
  by (pose proof (HBden 1%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB2 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 34)
  = cf_cb (l_pl cx) 2)
  by (pose proof (HBden 2%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB3 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 35)
  = cf_cb (l_pl cx) 3)
  by (pose proof (HBden 3%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB4 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 36)
  = cf_cb (l_pl cx) 4)
  by (pose proof (HBden 4%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB5 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 37)
  = cf_cb (l_pl cx) 5)
  by (pose proof (HBden 5%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB6 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 38)
  = cf_cb (l_pl cx) 6)
  by (pose proof (HBden 6%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB7 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 39)
  = cf_cb (l_pl cx) 7)
  by (pose proof (HBden 7%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB8 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 40)
  = cf_cb (l_pl cx) 8)
  by (pose proof (HBden 8%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 41)
  = cf_cb (l_pl cx) 9)
  by (pose proof (HBden 9%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB10 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 42)
  = cf_cb (l_pl cx) 10)
  by (pose proof (HBden 10%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB11 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 43)
  = cf_cb (l_pl cx) 11)
  by (pose proof (HBden 11%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (EPC : w64 (transport_text + CF_SC) = Z_to_bv 64 (BASE + CF_SC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (HEI : img_env VAL A_LIM (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))) by apply cf_E_img.
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (cf_ssp 12)
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_SC)) mem (YK11.seg_rom segs)))).
{ unfold cf_ssp. apply (cf_seat cx ly' S' W regs mem md _ 12 bs _ CF_SC _ LAWS HB HC HJ).
  - apply cf_regs_pin. exact R27.
  - exact (cf_facts cx regs _ 12 bs G9 ltac:(lia) N3 R19 ltac:(lia) G21 R23 G26 HBden HBrng).
  - exact G9.
  - exact R19.
  - exact G21.
  - exact Hn0.
  - lia.
  - exact HBden.
  - exact HBrng.
  - exact HBval. }
assert (U19 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs _ 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs _ 26%nat 26%bv eq_refl), G26; apply cf_u64; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs cf_Bx (cf_SH 12) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))
  (mrestrict (w_H W) mem))
  by exact (cf_shok cx ly' S' W regs mem md _ 12 LAWS HB HC Hn0 ltac:(lia) U19 U26).
assert (V21 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs _ 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs _ 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
assert (V23 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs _ 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 8%nat ltac:(lia)) as V8h.
change (A_HI 8) with 408%nat in V8h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 9%nat ltac:(lia)) as V9h.
change (A_HI 9) with 409%nat in V9h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 10%nat ltac:(lia)) as V10h.
change (A_HI 10) with 410%nat in V10h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 11%nat ltac:(lia)) as V11h.
change (A_HI 11) with 411%nat in V11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x318.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V21 in Ha;
     apply cf_cfg_inG; lia|].
  do 4 (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|]).
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V8h in Ha;
     apply cf_glob_inG; left; unfold TA_g_raw; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9h in Ha;
     apply cf_glob_inG; right; left; unfold TA_g_now; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V10h in Ha;
     apply cf_glob_inG; right; right; left; unfold TA_g_fail_next; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V11h in Ha;
     apply cf_glob_inG; right; right; right; unfold TA_g_last_counter; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
cf_ag (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)).
lazymatch goal with
| HA : env_agree 512 (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) ?ER |- _ =>
  assert (W21 : bv_unsigned (ew ER 21) = TA_g_cfg)
    by (first [ exact V21
              | rewrite <- (proj1 HA 21%nat ltac:(lia)); exact V21
              | rewrite (proj1 HA 21%nat ltac:(lia)); exact V21 ]);
  assert (W9 : bv_unsigned (ew ER 9) = lc_sp1 cx)
    by (first [ exact V9
              | rewrite <- (proj1 HA 9%nat ltac:(lia)); exact V9
              | rewrite (proj1 HA 9%nat ltac:(lia)); exact V9 ]);
  assert (W8h : bv_unsigned (ew ER 408) = 6157588)
    by (first [ exact V8h
              | rewrite <- (proj1 HA 408%nat ltac:(lia)); exact V8h
              | rewrite (proj1 HA 408%nat ltac:(lia)); exact V8h ]);
  assert (W9h : bv_unsigned (ew ER 409) = 6157596)
    by (first [ exact V9h
              | rewrite <- (proj1 HA 409%nat ltac:(lia)); exact V9h
              | rewrite (proj1 HA 409%nat ltac:(lia)); exact V9h ]);
  assert (W10h : bv_unsigned (ew ER 410) = 6157652)
    by (first [ exact V10h
              | rewrite <- (proj1 HA 410%nat ltac:(lia)); exact V10h
              | rewrite (proj1 HA 410%nat ltac:(lia)); exact V10h ]);
  assert (W11h : bv_unsigned (ew ER 411) = 6157672)
    by (first [ exact V11h
              | rewrite <- (proj1 HA 411%nat ltac:(lia)); exact V11h
              | rewrite (proj1 HA 411%nat ltac:(lia)); exact V11h ])
end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wrun cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hw. apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wrun cx) HFr); [|exact Ha | exact Hw].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-|]); [..|destruct Hin].
  - cbn [base_val] in Hx. lia.
  - cbn [base_val] in Hx; rewrite V21 in Hx. unfold cf_wrun. left. unfold TA_g_cfg in *. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; right. lia.
  - cbn [base_val] in Hx; rewrite V8h in Hx. unfold cf_wrun. right; left. unfold TA_g_raw. lia.
  - cbn [base_val] in Hx; rewrite V9h in Hx. unfold cf_wrun. right; right; left. unfold TA_g_now. lia.
  - cbn [base_val] in Hx; rewrite V10h in Hx. unfold cf_wrun.
    right; right; right; left. unfold TA_g_fail_next. lia.
  - cbn [base_val] in Hx; rewrite V11h in Hx. unfold cf_wrun.
    right; right; right; right; left. unfold TA_g_last_counter. lia. }
assert (KA : cf_KV cx W mem0 (ms_mem ms)).
{ intros a Ha Hw. rewrite (KF a Ha ltac:(intros C; apply Hw; unfold cf_wrun, cf_wr in *; lia)).
  exact (KV a Ha Hw). }
assert (GA : cf_GP W mem0 (ms_mem ms))
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GP a Ha))).
assert (KG : forall a, TA_g_cfg <= a < TA_g_cfg + 24 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply KF; [unfold TA_g_cfg in *; lia|].
  unfold cf_wrun, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 9 _ HS eq_refl) as RG9.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
assert (F24 : cf_bw W (ms_mem ms) (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 24 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 34 0) (SAlu ALU_SLL (SOff 35 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB2 HB3). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F28 : cf_bw W (ms_mem ms) (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 28 4%N (SOff 33 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  apply cf_m32.
  - cbn. lia. }
assert (F32 : cf_bw W (ms_mem ms) (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 32 4%N (SAlu ALU_AND (SOff 32 0) (SLit 7)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f32 _ HB0). reflexivity.
  - apply cf_m8.
  - cbn. lia. }
assert (F36 : cf_bw W (ms_mem ms) (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 36 4%N (SOff 36 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  cf_rval.
  -  cbn [Z.of_N]. pose proof HB4. lia.
  - cbn. lia. }
assert (F40 : cf_bw W (ms_mem ms) (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 40 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 37 0) (SAlu ALU_SLL (SOff 38 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB5 HB6). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F44 : cf_bw W (ms_mem ms) (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 44 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 39 0) (SAlu ALU_SLL (SOff 40 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB7 HB8). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F48 : cf_bw W (ms_mem ms) (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 48 4%N (SAlu ALU_OR (SAlu ALU_SLL (SOff 42 0) (SLit 8)) (SOff 41 0)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16b _ _ HB9 HB10). reflexivity.
  - cbn [Z.of_N]. pose proof HB9. pose proof HB10. lia.
  - cbn. lia. }
assert (F52 : cf_bw W (ms_mem ms) (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 52 4%N (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_AND (SOff 43 0) (SLit 255)) (SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_ADD (SAlu ALU_AND (SOff 43 0) (SLit 255)) (SLit (-255))) (SLit 1)) (SLit (-1)))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f52 _ HB11). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F56 : cf_bw W (ms_mem ms) (TA_g_cfg + 56) 4 ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
      mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 56 4%N (SLit 24) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). cf_rval.
  -  rewrite (Hz 12 ltac:(lia)). rewrite (Hz 13 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (GRAW : cf_bw W (ms_mem ms) TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 408%nat _ _ _ _ _ _ (-1076) 4%N
    (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 60)) (SLit 63)) _ RG6 W8h _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 3)
      ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (GNOW : cf_bw W (ms_mem ms) TA_g_now 8 1000000)
  by (cf_gl RG7 W9h 409%nat (-1052) 8%nat 8%N (SLit 1000000) ltac:(cf_rval)).
assert (GFAIL : cf_bw W (ms_mem ms) TA_g_fail_next 1 0)
  by (cf_gl RG8 W10h 410%nat (-1076) 1%nat 1%N (SLit 0) ltac:(cf_rval)).
assert (GLAST : cf_bw W (ms_mem ms) TA_g_last_counter 4 0)
  by (cf_gl RG9 W11h 411%nat (-1064) 4%nat 4%N (SLit 0) ltac:(cf_rval)).
assert (SP48 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 48) = Some (transport_hi 11))
  by (cf_sp RG2 W9 48 (SOff 411 0)).
assert (SP120 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 120) = Some (transport_hi 8))
  by (cf_sp RG3 W9 120 (SOff 408 0)).
assert (SP160 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 160) = Some (transport_hi 10))
  by (cf_sp RG4 W9 160 (SOff 410 0)).
assert (SP176 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 176) = Some (transport_hi 9))
  by (cf_sp RG5 W9 176 (SOff 409 0)).
assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs (map (fun v : Z => Z_to_bv 64 v) bs) _ HS _ _ r Hr);
    [apply cf_agree; assumption | vm_compute; reflexivity]. }
cf_rd HS (Z_to_bv 5 25) (w64 (l_p cx + 1 + 12)) Y25
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; first [reflexivity | f_equal; lia]).
cf_rd HS (Z_to_bv 5 27) (w64 0) Y27 ltac:(reflexivity).
pmkst HS.
apply SRr_ret.
apply (cf_close cx ly' S' W regs0 mem0 md0 Bw0 B1 (ms_regs ms) (ms_mem ms) md1 LAWS HB HC0 HSP HFS HIO HMT
  HW0 ECD HTW HJ KA GA).
- intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H0 i Hi).
- intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H6 i Hi).
- intros j Hj. rewrite (KG (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H12 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H16 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H20 j Hj).
- exact F24.
- exact F28.
- exact F32.
- exact F36.
- exact F40.
- exact F44.
- exact F48.
- exact F52.
- exact F56.
- exact GRAW.
- exact GNOW.
- exact GFAIL.
- exact GLAST.
- exact SP120.
- exact SP176.
- exact SP160.
- exact SP48.
- unfold cf_regs.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
    (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
    (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
  exact HRG.
- rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- unfold lc_cur. rewrite cf_cursor. cbn [TOP.fi_off TOP.fi_n]. rewrite Coff.
  rewrite Hk. change (Z.min 12 14) with 12.
  split; [rewrite Y25; unfold w64; f_equal; lia | rewrite Y27; unfold w64; f_equal; lia].
Qed.

Lemma cf_case13 : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md -> cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_bl W mem (TA_g_cfg + 0) TC.HOST -> cf_bl W mem (TA_g_cfg + 6) TC.DESK ->
  cf_bw W mem (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W mem (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W mem (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> TOP.fi_n (lc_c1 (l_pl cx)) = 13 ->
  SRr segs W (lc_cfg cx CF_SC regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regs mem md HP HB HC0 HSP HFS HIO HMT HW0 ECD HTW
  HC HJ KV GP H0 H6 H12 H16 H20 HRG R23 R22 HCUR Hk.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
destruct (cf_c1_pos (l_pl cx) ltac:(lia)) as (Coff & Cn & Clen).
assert (Hn0 : 0 < l_n cx) by lia.
assert (R19 : YK11.getr regs (Z_to_bv 5 19) = w64 (l_p cx + 1)) by (rewrite C19, Coff; reflexivity).
assert (R27 : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 13) by (rewrite C27, Hk; reflexivity).
assert (Hz : forall j, 13 <= j -> cf_cb (l_pl cx) j = 0).
{ intros j Hj. unfold cf_cb, cf_b. rewrite Hk.
  destruct (Z.ltb_spec j 13); [lia | reflexivity]. }
assert (HB0 : 0 <= cf_cb (l_pl cx) 0 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB1 : 0 <= cf_cb (l_pl cx) 1 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB2 : 0 <= cf_cb (l_pl cx) 2 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB3 : 0 <= cf_cb (l_pl cx) 3 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB4 : 0 <= cf_cb (l_pl cx) 4 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB5 : 0 <= cf_cb (l_pl cx) 5 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB6 : 0 <= cf_cb (l_pl cx) 6 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB7 : 0 <= cf_cb (l_pl cx) 7 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB8 : 0 <= cf_cb (l_pl cx) 8 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB9 : 0 <= cf_cb (l_pl cx) 9 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB10 : 0 <= cf_cb (l_pl cx) 10 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB11 : 0 <= cf_cb (l_pl cx) 11 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB12 : 0 <= cf_cb (l_pl cx) 12 < 256) by (unfold cf_cb; apply cf_b_rng).
set (bs := [cf_cb (l_pl cx) 0; cf_cb (l_pl cx) 1; cf_cb (l_pl cx) 2; cf_cb (l_pl cx) 3; cf_cb (l_pl cx) 4; cf_cb (l_pl cx) 5; cf_cb (l_pl cx) 6; cf_cb (l_pl cx) 7; cf_cb (l_pl cx) 8; cf_cb (l_pl cx) 9; cf_cb (l_pl cx) 10; cf_cb (l_pl cx) 11; cf_cb (l_pl cx) 12]).
assert (HBrng : forall j, (j < 13)%nat -> 0 <= nth j bs 0 < 256).
{ intros j Hj. unfold bs. destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]; cbn [nth]; first [exact HB0 | exact HB0 | exact HB1 | exact HB2 | exact HB3 | exact HB4 | exact HB5 | exact HB6 | exact HB7 | exact HB8 | exact HB9 | exact HB10 | exact HB11 | exact HB12 | lia]. }
assert (HBval : forall j, (j < 13)%nat ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j bs 0)).
{ intros j Hj.
  replace (nth j bs 0) with (cf_cb (l_pl cx) (Z.of_nat j))
    by (unfold bs; destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]; cbn [nth Z.of_nat]; reflexivity || lia).
  apply (cf_in_bytes cx ly' S' W regs mem md j HC). lia. }
assert (HBden : forall j, (j < 13)%nat ->
  bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (32 + j)) = nth j bs 0)
  by (intros j Hj; apply cf_ex_val; [lia | exact (HBrng j Hj)]).
assert (UB0 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 32)
  = cf_cb (l_pl cx) 0)
  by (pose proof (HBden 0%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB1 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 33)
  = cf_cb (l_pl cx) 1)
  by (pose proof (HBden 1%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB2 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 34)
  = cf_cb (l_pl cx) 2)
  by (pose proof (HBden 2%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB3 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 35)
  = cf_cb (l_pl cx) 3)
  by (pose proof (HBden 3%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB4 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 36)
  = cf_cb (l_pl cx) 4)
  by (pose proof (HBden 4%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB5 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 37)
  = cf_cb (l_pl cx) 5)
  by (pose proof (HBden 5%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB6 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 38)
  = cf_cb (l_pl cx) 6)
  by (pose proof (HBden 6%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB7 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 39)
  = cf_cb (l_pl cx) 7)
  by (pose proof (HBden 7%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB8 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 40)
  = cf_cb (l_pl cx) 8)
  by (pose proof (HBden 8%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 41)
  = cf_cb (l_pl cx) 9)
  by (pose proof (HBden 9%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB10 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 42)
  = cf_cb (l_pl cx) 10)
  by (pose proof (HBden 10%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB11 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 43)
  = cf_cb (l_pl cx) 11)
  by (pose proof (HBden 11%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB12 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 44)
  = cf_cb (l_pl cx) 12)
  by (pose proof (HBden 12%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (EPC : w64 (transport_text + CF_SC) = Z_to_bv 64 (BASE + CF_SC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (HEI : img_env VAL A_LIM (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))) by apply cf_E_img.
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (cf_ssp 13)
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_SC)) mem (YK11.seg_rom segs)))).
{ unfold cf_ssp. apply (cf_seat cx ly' S' W regs mem md _ 13 bs _ CF_SC _ LAWS HB HC HJ).
  - apply cf_regs_pin. exact R27.
  - exact (cf_facts cx regs _ 13 bs G9 ltac:(lia) N3 R19 ltac:(lia) G21 R23 G26 HBden HBrng).
  - exact G9.
  - exact R19.
  - exact G21.
  - exact Hn0.
  - lia.
  - exact HBden.
  - exact HBrng.
  - exact HBval. }
assert (U19 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs _ 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs _ 26%nat 26%bv eq_refl), G26; apply cf_u64; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs cf_Bx (cf_SH 13) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))
  (mrestrict (w_H W) mem))
  by exact (cf_shok cx ly' S' W regs mem md _ 13 LAWS HB HC Hn0 ltac:(lia) U19 U26).
assert (V21 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs _ 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs _ 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
assert (V23 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs _ 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 8%nat ltac:(lia)) as V8h.
change (A_HI 8) with 408%nat in V8h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 9%nat ltac:(lia)) as V9h.
change (A_HI 9) with 409%nat in V9h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 10%nat ltac:(lia)) as V10h.
change (A_HI 10) with 410%nat in V10h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 11%nat ltac:(lia)) as V11h.
change (A_HI 11) with 411%nat in V11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x318.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V21 in Ha;
     apply cf_cfg_inG; lia|].
  do 4 (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|]).
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V8h in Ha;
     apply cf_glob_inG; left; unfold TA_g_raw; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9h in Ha;
     apply cf_glob_inG; right; left; unfold TA_g_now; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V10h in Ha;
     apply cf_glob_inG; right; right; left; unfold TA_g_fail_next; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V11h in Ha;
     apply cf_glob_inG; right; right; right; unfold TA_g_last_counter; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
cf_ag (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)).
lazymatch goal with
| HA : env_agree 512 (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) ?ER |- _ =>
  assert (W21 : bv_unsigned (ew ER 21) = TA_g_cfg)
    by (first [ exact V21
              | rewrite <- (proj1 HA 21%nat ltac:(lia)); exact V21
              | rewrite (proj1 HA 21%nat ltac:(lia)); exact V21 ]);
  assert (W9 : bv_unsigned (ew ER 9) = lc_sp1 cx)
    by (first [ exact V9
              | rewrite <- (proj1 HA 9%nat ltac:(lia)); exact V9
              | rewrite (proj1 HA 9%nat ltac:(lia)); exact V9 ]);
  assert (W8h : bv_unsigned (ew ER 408) = 6157588)
    by (first [ exact V8h
              | rewrite <- (proj1 HA 408%nat ltac:(lia)); exact V8h
              | rewrite (proj1 HA 408%nat ltac:(lia)); exact V8h ]);
  assert (W9h : bv_unsigned (ew ER 409) = 6157596)
    by (first [ exact V9h
              | rewrite <- (proj1 HA 409%nat ltac:(lia)); exact V9h
              | rewrite (proj1 HA 409%nat ltac:(lia)); exact V9h ]);
  assert (W10h : bv_unsigned (ew ER 410) = 6157652)
    by (first [ exact V10h
              | rewrite <- (proj1 HA 410%nat ltac:(lia)); exact V10h
              | rewrite (proj1 HA 410%nat ltac:(lia)); exact V10h ]);
  assert (W11h : bv_unsigned (ew ER 411) = 6157672)
    by (first [ exact V11h
              | rewrite <- (proj1 HA 411%nat ltac:(lia)); exact V11h
              | rewrite (proj1 HA 411%nat ltac:(lia)); exact V11h ])
end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wrun cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hw. apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wrun cx) HFr); [|exact Ha | exact Hw].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-|]); [..|destruct Hin].
  - cbn [base_val] in Hx. lia.
  - cbn [base_val] in Hx; rewrite V21 in Hx. unfold cf_wrun. left. unfold TA_g_cfg in *. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; right. lia.
  - cbn [base_val] in Hx; rewrite V8h in Hx. unfold cf_wrun. right; left. unfold TA_g_raw. lia.
  - cbn [base_val] in Hx; rewrite V9h in Hx. unfold cf_wrun. right; right; left. unfold TA_g_now. lia.
  - cbn [base_val] in Hx; rewrite V10h in Hx. unfold cf_wrun.
    right; right; right; left. unfold TA_g_fail_next. lia.
  - cbn [base_val] in Hx; rewrite V11h in Hx. unfold cf_wrun.
    right; right; right; right; left. unfold TA_g_last_counter. lia. }
assert (KA : cf_KV cx W mem0 (ms_mem ms)).
{ intros a Ha Hw. rewrite (KF a Ha ltac:(intros C; apply Hw; unfold cf_wrun, cf_wr in *; lia)).
  exact (KV a Ha Hw). }
assert (GA : cf_GP W mem0 (ms_mem ms))
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GP a Ha))).
assert (KG : forall a, TA_g_cfg <= a < TA_g_cfg + 24 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply KF; [unfold TA_g_cfg in *; lia|].
  unfold cf_wrun, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 9 _ HS eq_refl) as RG9.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
assert (F24 : cf_bw W (ms_mem ms) (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 24 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 34 0) (SAlu ALU_SLL (SOff 35 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB2 HB3). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F28 : cf_bw W (ms_mem ms) (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 28 4%N (SOff 33 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  apply cf_m32.
  - cbn. lia. }
assert (F32 : cf_bw W (ms_mem ms) (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 32 4%N (SAlu ALU_AND (SOff 32 0) (SLit 7)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f32 _ HB0). reflexivity.
  - apply cf_m8.
  - cbn. lia. }
assert (F36 : cf_bw W (ms_mem ms) (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 36 4%N (SOff 36 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  cf_rval.
  -  cbn [Z.of_N]. pose proof HB4. lia.
  - cbn. lia. }
assert (F40 : cf_bw W (ms_mem ms) (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 40 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 37 0) (SAlu ALU_SLL (SOff 38 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB5 HB6). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F44 : cf_bw W (ms_mem ms) (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 44 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 39 0) (SAlu ALU_SLL (SOff 40 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB7 HB8). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F48 : cf_bw W (ms_mem ms) (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 48 4%N (SAlu ALU_OR (SAlu ALU_SLL (SOff 42 0) (SLit 8)) (SOff 41 0)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16b _ _ HB9 HB10). reflexivity.
  - cbn [Z.of_N]. pose proof HB9. pose proof HB10. lia.
  - cbn. lia. }
assert (F52 : cf_bw W (ms_mem ms) (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 52 4%N (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_AND (SOff 43 0) (SLit 255)) (SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_ADD (SAlu ALU_AND (SOff 43 0) (SLit 255)) (SLit (-255))) (SLit 1)) (SLit (-1)))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f52 _ HB11). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F56 : cf_bw W (ms_mem ms) (TA_g_cfg + 56) 4 ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
      mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 56 4%N (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_SUB (SAlu ALU_OR (SLit 0) (SOff 44 0)) (SMd M_MUL (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_OR (SLit 0) (SOff 44 0)) (SLit 22967)) (SLit 25)) (SLit 1461))) (SLit 24)) (SLit 48)) (SLit 48)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  rewrite (Hz 13 ltac:(lia)). etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f56a _ HB12). reflexivity.
  -  rewrite (Hz 13 ltac:(lia)). apply cf_m32.
  - cbn. lia. }
assert (GRAW : cf_bw W (ms_mem ms) TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 408%nat _ _ _ _ _ _ (-1076) 4%N
    (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 60)) (SLit 63)) _ RG6 W8h _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 3)
      ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (GNOW : cf_bw W (ms_mem ms) TA_g_now 8 1000000)
  by (cf_gl RG7 W9h 409%nat (-1052) 8%nat 8%N (SLit 1000000) ltac:(cf_rval)).
assert (GFAIL : cf_bw W (ms_mem ms) TA_g_fail_next 1 0)
  by (cf_gl RG8 W10h 410%nat (-1076) 1%nat 1%N (SLit 0) ltac:(cf_rval)).
assert (GLAST : cf_bw W (ms_mem ms) TA_g_last_counter 4 0)
  by (cf_gl RG9 W11h 411%nat (-1064) 4%nat 4%N (SLit 0) ltac:(cf_rval)).
assert (SP48 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 48) = Some (transport_hi 11))
  by (cf_sp RG2 W9 48 (SOff 411 0)).
assert (SP120 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 120) = Some (transport_hi 8))
  by (cf_sp RG3 W9 120 (SOff 408 0)).
assert (SP160 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 160) = Some (transport_hi 10))
  by (cf_sp RG4 W9 160 (SOff 410 0)).
assert (SP176 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 176) = Some (transport_hi 9))
  by (cf_sp RG5 W9 176 (SOff 409 0)).
assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs (map (fun v : Z => Z_to_bv 64 v) bs) _ HS _ _ r Hr);
    [apply cf_agree; assumption | vm_compute; reflexivity]. }
cf_rd HS (Z_to_bv 5 25) (w64 (l_p cx + 1 + 13)) Y25
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; first [reflexivity | f_equal; lia]).
cf_rd HS (Z_to_bv 5 27) (w64 0) Y27 ltac:(reflexivity).
pmkst HS.
apply SRr_ret.
apply (cf_close cx ly' S' W regs0 mem0 md0 Bw0 B1 (ms_regs ms) (ms_mem ms) md1 LAWS HB HC0 HSP HFS HIO HMT
  HW0 ECD HTW HJ KA GA).
- intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H0 i Hi).
- intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H6 i Hi).
- intros j Hj. rewrite (KG (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H12 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H16 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H20 j Hj).
- exact F24.
- exact F28.
- exact F32.
- exact F36.
- exact F40.
- exact F44.
- exact F48.
- exact F52.
- exact F56.
- exact GRAW.
- exact GNOW.
- exact GFAIL.
- exact GLAST.
- exact SP120.
- exact SP176.
- exact SP160.
- exact SP48.
- unfold cf_regs.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
    (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
    (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
  exact HRG.
- rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- unfold lc_cur. rewrite cf_cursor. cbn [TOP.fi_off TOP.fi_n]. rewrite Coff.
  rewrite Hk. change (Z.min 13 14) with 13.
  split; [rewrite Y25; unfold w64; f_equal; lia | rewrite Y27; unfold w64; f_equal; lia].
Qed.

Lemma cf_case14 : forall (cx : lcx) ly' S' (W : world segs) regs0 mem0 md0 Bw0 B1 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs0 mem0 md0 0 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem0) ->
  lc_fsh cx (aview segs (w_H W) mem0) false false -> lc_io cx W mem0 -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) -> lc_tw W mem0 B1 ->
  @lc_core rc B cx ly' S' W regs mem md 0 ->
  cf_J cx ly' S' W mem md -> cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_bl W mem (TA_g_cfg + 0) TC.HOST -> cf_bl W mem (TA_g_cfg + 6) TC.DESK ->
  cf_bw W mem (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  cf_bw W mem (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1) ->
  cf_bw W mem (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regs 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> 14 <= TOP.fi_n (lc_c1 (l_pl cx)) ->
  SRr segs W (lc_cfg cx CF_SC regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W regs0 mem0 md0 Bw0 B1 regs mem md HP HB HC0 HSP HFS HIO HMT HW0 ECD HTW
  HC HJ KV GP H0 H6 H12 H16 H20 HRG R23 R22 HCUR Hk.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof (cf_flags_rng (l_pl cx)) as HFL.
destruct (cf_c1_pos (l_pl cx) ltac:(lia)) as (Coff & Cn & Clen).
assert (Hn0 : 0 < l_n cx) by lia.
assert (R19 : YK11.getr regs (Z_to_bv 5 19) = w64 (l_p cx + 1)) by (rewrite C19, Coff; reflexivity).
assert (HB0 : 0 <= cf_cb (l_pl cx) 0 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB1 : 0 <= cf_cb (l_pl cx) 1 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB2 : 0 <= cf_cb (l_pl cx) 2 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB3 : 0 <= cf_cb (l_pl cx) 3 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB4 : 0 <= cf_cb (l_pl cx) 4 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB5 : 0 <= cf_cb (l_pl cx) 5 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB6 : 0 <= cf_cb (l_pl cx) 6 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB7 : 0 <= cf_cb (l_pl cx) 7 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB8 : 0 <= cf_cb (l_pl cx) 8 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB9 : 0 <= cf_cb (l_pl cx) 9 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB10 : 0 <= cf_cb (l_pl cx) 10 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB11 : 0 <= cf_cb (l_pl cx) 11 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB12 : 0 <= cf_cb (l_pl cx) 12 < 256) by (unfold cf_cb; apply cf_b_rng).
assert (HB13 : 0 <= cf_cb (l_pl cx) 13 < 256) by (unfold cf_cb; apply cf_b_rng).
set (bs := [cf_cb (l_pl cx) 0; cf_cb (l_pl cx) 1; cf_cb (l_pl cx) 2; cf_cb (l_pl cx) 3; cf_cb (l_pl cx) 4; cf_cb (l_pl cx) 5; cf_cb (l_pl cx) 6; cf_cb (l_pl cx) 7; cf_cb (l_pl cx) 8; cf_cb (l_pl cx) 9; cf_cb (l_pl cx) 10; cf_cb (l_pl cx) 11; cf_cb (l_pl cx) 12; cf_cb (l_pl cx) 13]).
assert (HBrng : forall j, (j < 14)%nat -> 0 <= nth j bs 0 < 256).
{ intros j Hj. unfold bs. destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]]; cbn [nth]; first [exact HB0 | exact HB0 | exact HB1 | exact HB2 | exact HB3 | exact HB4 | exact HB5 | exact HB6 | exact HB7 | exact HB8 | exact HB9 | exact HB10 | exact HB11 | exact HB12 | exact HB13 | lia]. }
assert (HBval : forall j, (j < 14)%nat ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (l_p cx + 1 + Z.of_nat j) 1 (nth j bs 0)).
{ intros j Hj.
  replace (nth j bs 0) with (cf_cb (l_pl cx) (Z.of_nat j))
    by (unfold bs; destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]]; cbn [nth Z.of_nat]; reflexivity || lia).
  apply (cf_in_bytes cx ly' S' W regs mem md j HC). lia. }
assert (HBden : forall j, (j < 14)%nat ->
  bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (32 + j)) = nth j bs 0)
  by (intros j Hj; apply cf_ex_val; [lia | exact (HBrng j Hj)]).
assert (UB0 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 32)
  = cf_cb (l_pl cx) 0)
  by (pose proof (HBden 0%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB1 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 33)
  = cf_cb (l_pl cx) 1)
  by (pose proof (HBden 1%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB2 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 34)
  = cf_cb (l_pl cx) 2)
  by (pose proof (HBden 2%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB3 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 35)
  = cf_cb (l_pl cx) 3)
  by (pose proof (HBden 3%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB4 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 36)
  = cf_cb (l_pl cx) 4)
  by (pose proof (HBden 4%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB5 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 37)
  = cf_cb (l_pl cx) 5)
  by (pose proof (HBden 5%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB6 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 38)
  = cf_cb (l_pl cx) 6)
  by (pose proof (HBden 6%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB7 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 39)
  = cf_cb (l_pl cx) 7)
  by (pose proof (HBden 7%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB8 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 40)
  = cf_cb (l_pl cx) 8)
  by (pose proof (HBden 8%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 41)
  = cf_cb (l_pl cx) 9)
  by (pose proof (HBden 9%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB10 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 42)
  = cf_cb (l_pl cx) 10)
  by (pose proof (HBden 10%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB11 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 43)
  = cf_cb (l_pl cx) 11)
  by (pose proof (HBden 11%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB12 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 44)
  = cf_cb (l_pl cx) 12)
  by (pose proof (HBden 12%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (UB13 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 45)
  = cf_cb (l_pl cx) 13)
  by (pose proof (HBden 13%nat ltac:(lia)) as HU; cbn [nth Nat.add] in HU; exact HU).
assert (EPC : w64 (transport_text + CF_SC) = Z_to_bv 64 (BASE + CF_SC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (HEI : img_env VAL A_LIM (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))) by apply cf_E_img.
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) (cf_ssw)
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_SC)) mem (YK11.seg_rom segs)))).
{ unfold cf_ssw. apply (cf_seat cx ly' S' W regs mem md _ 14 bs _ CF_SC _ LAWS HB HC HJ).
  - apply regs_ok_Eimg_Ereg.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms]. cbn [atoms_ok]. split.
    + unfold afact_ok. cbn [af_lo af_hi af_al2].
      assert (U27 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 27)
        = TOP.fi_n (lc_c1 (l_pl cx)))
        by (rewrite (cf_E_reg regs _ 27%nat (Z_to_bv 5 27) ltac:(vm_compute; reflexivity)), C27; apply cf_u64; lia).
      rewrite U27, Z.pow_0_r, Z.mod_1_r. repeat split; try reflexivity; lia.
    + exact (proj1 (cf_facts cx regs _ 14 bs G9 ltac:(lia) N3 R19 ltac:(lia) G21 R23 G26 HBden HBrng)).
  - exact G9.
  - exact R19.
  - exact G21.
  - exact Hn0.
  - lia.
  - exact HBden.
  - exact HBrng.
  - exact HBval. }
assert (U19 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs _ 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19; apply cf_u64; lia).
assert (U27g : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 27) = TOP.fi_n (lc_c1 (l_pl cx)))
  by (rewrite (cf_E_reg regs _ 27%nat (Z_to_bv 5 27) ltac:(vm_compute; reflexivity)), C27; apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs _ 26%nat 26%bv eq_refl), G26; apply cf_u64; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs cf_Bx (cf_SH 14) (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs))
  (mrestrict (w_H W) mem))
  by exact (cf_shok cx ly' S' W regs mem md _ 14 LAWS HB HC Hn0 ltac:(lia) U19 U26).
assert (V21 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 21) = TA_g_cfg)
  by (rewrite (cf_E_reg regs _ 21%nat 21%bv eq_refl), G21; apply cf_u64; unfold TA_g_cfg; lia).
assert (V9 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 9) = lc_sp1 cx)
  by (rewrite (cf_E_reg regs _ 9%nat 9%bv eq_refl), G9; apply cf_u64; lia).
assert (V23 : bv_unsigned (ew (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) 23) = lc_flags (l_pl cx))
  by (rewrite (cf_E_reg regs _ 23%nat 23%bv eq_refl), R23; apply cf_u64; lia).
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 8%nat ltac:(lia)) as V8h.
change (A_HI 8) with 408%nat in V8h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 9%nat ltac:(lia)) as V9h.
change (A_HI 9) with 409%nat in V9h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 10%nat ltac:(lia)) as V10h.
change (A_HI 10) with 410%nat in V10h.
pose proof (cf_E_hi regs (map (fun v : Z => Z_to_bv 64 v) bs) 11%nat ltac:(lia)) as V11h.
change (A_HI 11) with 411%nat in V11h.
assert (EH8 : transport_hi 8 = 6157588) by reflexivity.
assert (EH9 : transport_hi 9 = 6157596) by reflexivity.
assert (EH10 : transport_hi 10 = 6157652) by reflexivity.
assert (EH11 : transport_hi 11 = 6157672) by reflexivity.
rewrite EH8 in V8h. rewrite EH9 in V9h. rewrite EH10 in V10h. rewrite EH11 in V11h.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x318.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V21 in Ha;
     apply cf_cfg_inG; lia|].
  do 4 (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9 in Ha;
     left; split; [left; unfold LLVMF_STK; lia | lia]|]).
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V8h in Ha;
     apply cf_glob_inG; left; unfold TA_g_raw; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V9h in Ha;
     apply cf_glob_inG; right; left; unfold TA_g_now; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V10h in Ha;
     apply cf_glob_inG; right; right; left; unfold TA_g_fail_next; lia|].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite V11h in Ha;
     apply cf_glob_inG; right; right; right; unfold TA_g_last_counter; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
cf_ag (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)).
lazymatch goal with
| HA : env_agree 512 (cf_E regs (map (fun v : Z => Z_to_bv 64 v) bs)) ?ER |- _ =>
  assert (W21 : bv_unsigned (ew ER 21) = TA_g_cfg)
    by (first [ exact V21
              | rewrite <- (proj1 HA 21%nat ltac:(lia)); exact V21
              | rewrite (proj1 HA 21%nat ltac:(lia)); exact V21 ]);
  assert (W9 : bv_unsigned (ew ER 9) = lc_sp1 cx)
    by (first [ exact V9
              | rewrite <- (proj1 HA 9%nat ltac:(lia)); exact V9
              | rewrite (proj1 HA 9%nat ltac:(lia)); exact V9 ]);
  assert (W8h : bv_unsigned (ew ER 408) = 6157588)
    by (first [ exact V8h
              | rewrite <- (proj1 HA 408%nat ltac:(lia)); exact V8h
              | rewrite (proj1 HA 408%nat ltac:(lia)); exact V8h ]);
  assert (W9h : bv_unsigned (ew ER 409) = 6157596)
    by (first [ exact V9h
              | rewrite <- (proj1 HA 409%nat ltac:(lia)); exact V9h
              | rewrite (proj1 HA 409%nat ltac:(lia)); exact V9h ]);
  assert (W10h : bv_unsigned (ew ER 410) = 6157652)
    by (first [ exact V10h
              | rewrite <- (proj1 HA 410%nat ltac:(lia)); exact V10h
              | rewrite (proj1 HA 410%nat ltac:(lia)); exact V10h ]);
  assert (W11h : bv_unsigned (ew ER 411) = 6157672)
    by (first [ exact V11h
              | rewrite <- (proj1 HA 411%nat ltac:(lia)); exact V11h
              | rewrite (proj1 HA 411%nat ltac:(lia)); exact V11h ])
end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ cf_wrun cx a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hw. apply (YC4b.kept_of_frame _ _ _ _ _ (cf_wrun cx) HFr); [|exact Ha | exact Hw].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-|]); [..|destruct Hin].
  - cbn [base_val] in Hx. lia.
  - cbn [base_val] in Hx; rewrite V21 in Hx. unfold cf_wrun. left. unfold TA_g_cfg in *. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun. right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; left. lia.
  - cbn [base_val] in Hx; rewrite V9 in Hx. unfold cf_wrun.
    right; right; right; right; right; right; right; right. lia.
  - cbn [base_val] in Hx; rewrite V8h in Hx. unfold cf_wrun. right; left. unfold TA_g_raw. lia.
  - cbn [base_val] in Hx; rewrite V9h in Hx. unfold cf_wrun. right; right; left. unfold TA_g_now. lia.
  - cbn [base_val] in Hx; rewrite V10h in Hx. unfold cf_wrun.
    right; right; right; left. unfold TA_g_fail_next. lia.
  - cbn [base_val] in Hx; rewrite V11h in Hx. unfold cf_wrun.
    right; right; right; right; left. unfold TA_g_last_counter. lia. }
assert (KA : cf_KV cx W mem0 (ms_mem ms)).
{ intros a Ha Hw. rewrite (KF a Ha ltac:(intros C; apply Hw; unfold cf_wrun, cf_wr in *; lia)).
  exact (KV a Ha Hw). }
assert (GA : cf_GP W mem0 (ms_mem ms))
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GP a Ha))).
assert (KG : forall a, TA_g_cfg <= a < TA_g_cfg + 24 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply KF; [unfold TA_g_cfg in *; lia|].
  unfold cf_wrun, TA_g_cfg, TA_g_raw, TA_g_now, TA_g_fail_next, TA_g_last_counter in *. lia. }
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 0 _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 2 _ HS eq_refl) as RG2.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 4 _ HS eq_refl) as RG4.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 5 _ HS eq_refl) as RG5.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 6 _ HS eq_refl) as RG6.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 7 _ HS eq_refl) as RG7.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 8 _ HS eq_refl) as RG8.
pose proof (YC4b.st_ok_region_nth _ _ (restrict (w_H W) ms) 9 _ HS eq_refl) as RG9.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
assert (F24 : cf_bw W (ms_mem ms) (TA_g_cfg + 24) 4 ((1 + (cf_cb (l_pl cx) 2 + 256 * cf_cb (l_pl cx) 3)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 24 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 34 0) (SAlu ALU_SLL (SOff 35 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB2 HB3). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F28 : cf_bw W (ms_mem ms) (TA_g_cfg + 28) 4 ((1 + cf_cb (l_pl cx) 1) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 28 4%N (SOff 33 1) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    apply cf_small; lia.
  -  apply cf_m32.
  - cbn. lia. }
assert (F32 : cf_bw W (ms_mem ms) (TA_g_cfg + 32) 4 (cf_cb (l_pl cx) 0 mod 8)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 32 4%N (SAlu ALU_AND (SOff 32 0) (SLit 7)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f32 _ HB0). reflexivity.
  - apply cf_m8.
  - cbn. lia. }
assert (F36 : cf_bw W (ms_mem ms) (TA_g_cfg + 36) 4 (cf_cb (l_pl cx) 4)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 36 4%N (SOff 36 0) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  cf_rval.
  -  cbn [Z.of_N]. pose proof HB4. lia.
  - cbn. lia. }
assert (F40 : cf_bw W (ms_mem ms) (TA_g_cfg + 40) 4 ((1 + (cf_cb (l_pl cx) 5 + 256 * cf_cb (l_pl cx) 6)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 40 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 37 0) (SAlu ALU_SLL (SOff 38 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB5 HB6). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F44 : cf_bw W (ms_mem ms) (TA_g_cfg + 44) 4 ((1 + (cf_cb (l_pl cx) 7 + 256 * cf_cb (l_pl cx) 8)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 44 4%N (SAlu ALU_ADD (SAlu ALU_OR (SOff 39 0) (SAlu ALU_SLL (SOff 40 0) (SLit 8))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16a _ _ HB7 HB8). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F48 : cf_bw W (ms_mem ms) (TA_g_cfg + 48) 4 (cf_cb (l_pl cx) 9 + 256 * cf_cb (l_pl cx) 10)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 48 4%N (SAlu ALU_OR (SAlu ALU_SLL (SOff 42 0) (SLit 8)) (SOff 41 0)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  -  etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f16b _ _ HB9 HB10). reflexivity.
  - cbn [Z.of_N]. pose proof HB9. pose proof HB10. lia.
  - cbn. lia. }
assert (F52 : cf_bw W (ms_mem ms) (TA_g_cfg + 52) 4 ((1 + cf_cb (l_pl cx) 11 mod 255) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 52 4%N (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_AND (SOff 43 0) (SLit 255)) (SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_ADD (SAlu ALU_AND (SOff 43 0) (SLit 255)) (SLit (-255))) (SLit 1)) (SLit (-1)))) (SLit 1)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f52 _ HB11). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (F56 : cf_bw W (ms_mem ms) (TA_g_cfg + 56) 4 ((DSpec.SPEC_CMD_MAX + (cf_cb (l_pl cx) 12 + 256 * cf_cb (l_pl cx) 13)
      mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2 ^ 32)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 21%nat TA_g_cfg _ _ _ _ _ 56 4%N (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_SUB (SAlu ALU_OR (SAlu ALU_SLL (SOff 45 0) (SLit 8)) (SOff 44 0)) (SMd M_MUL (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_OR (SAlu ALU_SLL (SOff 45 0) (SLit 8)) (SOff 44 0)) (SLit 22967)) (SLit 25)) (SLit 1461))) (SLit 24)) (SLit 48)) (SLit 48)) _ RG1 W21 _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    rewrite (cf_f56b _ _ HB12 HB13). reflexivity.
  -  apply cf_m32.
  - cbn. lia. }
assert (GRAW : cf_bw W (ms_mem ms) TA_g_raw 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 3) 1)).
{ intros j Hj. refine (cf_vb _ _ _ 4 _ _ j Hj).
  refine (can_field_of_region _ _ 408%nat _ _ _ _ _ _ (-1076) 4%N
    (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 60)) (SLit 63)) _ RG6 W8h _ _ _ _).
  - cbn [In]. tauto.
  - etransitivity; [cf_den|]. apply cf_word_eq. rewrite ?Z.add_0_r.
    destruct (cf_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb & _). rewrite Cb. reflexivity.
  - cbn [Z.of_N]. pose proof (cf_land1 (Z.shiftr (lc_flags (l_pl cx)) 3)
      ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (GNOW : cf_bw W (ms_mem ms) TA_g_now 8 1000000)
  by (cf_gl RG7 W9h 409%nat (-1052) 8%nat 8%N (SLit 1000000) ltac:(cf_rval)).
assert (GFAIL : cf_bw W (ms_mem ms) TA_g_fail_next 1 0)
  by (cf_gl RG8 W10h 410%nat (-1076) 1%nat 1%N (SLit 0) ltac:(cf_rval)).
assert (GLAST : cf_bw W (ms_mem ms) TA_g_last_counter 4 0)
  by (cf_gl RG9 W11h 411%nat (-1064) 4%nat 4%N (SLit 0) ltac:(cf_rval)).
assert (SP48 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 48) = Some (transport_hi 11))
  by (cf_sp RG2 W9 48 (SOff 411 0)).
assert (SP120 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 120) = Some (transport_hi 8))
  by (cf_sp RG3 W9 120 (SOff 408 0)).
assert (SP160 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 160) = Some (transport_hi 10))
  by (cf_sp RG4 W9 160 (SOff 410 0)).
assert (SP176 : rdword (aview segs (w_H W) (ms_mem ms)) (lc_sp1 cx + 176) = Some (transport_hi 9))
  by (cf_sp RG5 W9 176 (SOff 409 0)).
assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 26%bv] ->
  YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs (map (fun v : Z => Z_to_bv 64 v) bs) _ HS _ _ r Hr);
    [apply cf_agree; assumption | vm_compute; reflexivity]. }
cf_rd HS (Z_to_bv 5 25) (w64 (l_p cx + 1 + 14)) Y25
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; first [reflexivity | f_equal; lia]).
cf_rd HS (Z_to_bv 5 27) (w64 (TOP.fi_n (lc_c1 (l_pl cx)) - 14)) Y27
  ltac:(unfold w64; etransitivity; [cf_den|]; apply cf_word_eq; first [reflexivity | f_equal; lia]).
pmkst HS.
apply SRr_ret.
apply (cf_close cx ly' S' W regs0 mem0 md0 Bw0 B1 (ms_regs ms) (ms_mem ms) md1 LAWS HB HC0 HSP HFS HIO HMT
  HW0 ECD HTW HJ KA GA).
- intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H0 i Hi).
- intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
  rewrite (KG (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (H6 i Hi).
- intros j Hj. rewrite (KG (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H12 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H16 j Hj).
- intros j Hj. rewrite (KG (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)). exact (H20 j Hj).
- exact F24.
- exact F28.
- exact F32.
- exact F36.
- exact F40.
- exact F44.
- exact F48.
- exact F52.
- exact F56.
- exact GRAW.
- exact GNOW.
- exact GFAIL.
- exact GLAST.
- exact SP120.
- exact SP176.
- exact SP160.
- exact SP48.
- unfold cf_regs.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
    (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
    (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
  exact HRG.
- rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- unfold lc_cur. rewrite cf_cursor. cbn [TOP.fi_off TOP.fi_n]. rewrite Coff.
  rewrite (Z.min_r (TOP.fi_n (lc_c1 (l_pl cx))) 14) by lia.
  split; [rewrite Y25; unfold w64; f_equal; lia | rewrite Y27; unfold w64; f_equal; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 12. +0x214 .. +0x22c: the first config byte's checked load          *)
(* ------------------------------------------------------------------ *)

(* The run writes nothing: it reads the cursor's shadow byte (a region named by an alias fact), and on the slow path
   +0x18fc .. +0x1904 the report call 0x82b70 is unreached, because the cursor sits one past an eight-aligned block
   whose shadow byte is 0 or above its offset in the granule. *)
Lemma cf_runb : forall (cx : lcx) ly' S' (W : world segs) mem0 regs mem md,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs mem md 0 -> cf_J cx ly' S' W mem md ->
  cf_KV cx W mem0 mem -> cf_GP W mem0 mem ->
  cf_regs cx regs -> YK11.getr regs 23 = w64 (lc_flags (l_pl cx)) ->
  lc_cur cx regs 19 27 (lc_c1 (l_pl cx)) -> TOP.fi_n (lc_c1 (l_pl cx)) <> 0 ->
  (forall regs' mem' md',
     @lc_core rc B cx ly' S' W regs' mem' md' 0 -> cf_J cx ly' S' W mem' md' ->
     cf_KV cx W mem0 mem' -> cf_GP W mem0 mem' ->
     (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     cf_regs cx regs' -> YK11.getr regs' 23 = w64 (lc_flags (l_pl cx)) ->
     YK11.getr regs' 22 = YK11.getr regs 22 ->
     lc_cur cx regs' 19 27 (lc_c1 (l_pl cx)) ->
     SRr segs W (lc_cfg cx CF_SC regs' mem' md') (@lc_st_scal rc B MT cx)) ->
  SRr segs W (lc_cfg cx CF_RC2 regs mem md) (@lc_st_scal rc B MT cx).
Proof.
intros cx ly' S' W mem0 regs mem md HP HB HC HJ KV GP HRG R23 HCUR Hnz FIN.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G26 & G21 & G20).
destruct HCUR as (C19 & C27).
destruct (cf_num cx ly' S' W regs mem md 0 LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & HAR).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
destruct (cf_c1_pos (l_pl cx) Hnz) as (Coff & Cn & Clen).
assert (Hn0 : 0 < l_n cx) by lia.
destruct (N12 Hn0) as (Hblk & Gp4 & Gpc & Gp8 & Gapp & _).
assert (R19 : YK11.getr regs (Z_to_bv 5 19) = w64 (l_p cx + 1)) by (rewrite C19, Coff; reflexivity).
assert (R27 : YK11.getr regs (Z_to_bv 5 27) = w64 (TOP.fi_n (lc_c1 (l_pl cx)))) by exact C27.
(* the shadow byte of the cursor's granule *)
destruct (cf_ra_blk cx ly' S' W regs mem md LAWS HB HC Hn0 (l_p cx + 1) ltac:(lia)) as (sb & Hsbv & Hsbok).
unfold shadow_of_addr in Hsbv.
assert (Hsbr : 0 <= sb <= 7) by (unfold saddr_ok in Hsbok; lia).
assert (Hp18 : (l_p cx + 1) mod 8 = 1).
{ rewrite Zplus_mod, Gp8. reflexivity. }
pose proof (AE2y.val_mem1_of_aview (w_H W) mem (SHADOW_OFF + (l_p cx + 1) / 8) sb Hsbv) as VS.
assert (HP8 : 0 <= (l_p cx + 1) / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
set (exb := map (fun v : Z => Z_to_bv 64 v)
  [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; SHADOW_OFF + (l_p cx + 1) / 8; sb]).
assert (U19 : bv_unsigned (ew (cf_E regs exb) 19) = l_p cx + 1)
  by (rewrite (cf_E_reg regs exb 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19;
      apply cf_u64; lia).
assert (U26 : bv_unsigned (ew (cf_E regs exb) 26) = SHADOW_OFF)
  by (rewrite (cf_E_reg regs exb 26%nat 26%bv eq_refl), G26; apply cf_u64; unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew (cf_E regs exb) 27) = TOP.fi_n (lc_c1 (l_pl cx)))
  by (rewrite (cf_E_reg regs exb 27%nat (Z_to_bv 5 27) ltac:(vm_compute; reflexivity)), R27;
      apply cf_u64; lia).
assert (U46 : bv_unsigned (ew (cf_E regs exb) 46) = SHADOW_OFF + (l_p cx + 1) / 8).
{ change 46%nat with (32 + 14)%nat. rewrite (cf_E_x regs exb 14%nat ltac:(lia)).
  unfold exb. cbn [nth map]. apply cf_u64. unfold SHADOW_OFF. lia. }
assert (U47 : bv_unsigned (ew (cf_E regs exb) 47) = sb).
{ change 47%nat with (32 + 15)%nat. rewrite (cf_E_x regs exb 15%nat ltac:(lia)).
  unfold exb. cbn [nth map]. apply cf_u64. lia. }
assert (E19 : ew (cf_E regs exb) 19 = Z_to_bv 64 (l_p cx + 1))
  by (rewrite <- U19; symmetry; apply Z_to_bv_bv_unsigned).
assert (E26 : ew (cf_E regs exb) 26 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite <- U26; symmetry; apply Z_to_bv_bv_unsigned).
assert (EPC : w64 (transport_text + CF_RC2) = Z_to_bv 64 (BASE + CF_RC2))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transport)) as BR.
assert (HEI : img_env VAL A_LIM (cf_E regs exb)) by apply cf_E_img.
assert (HS : @st_ok_pi segs VAL (l_fx cx) (cf_E regs exb) cf_ssb
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + CF_RC2)) mem (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold cf_ssb.
  apply (@pa_entry_st_ok_full (l_fx cx) rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold cf_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U46. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs _ _ (SHADOW_OFF + (l_p cx + 1) / 8) 0 1%N (SOff 47 0) sb);
      [cbn [sv_denot]; rewrite U47, Z.add_0_r; reflexivity
       | cbn [Z.of_N]; change (2 ^ (8 * 1)) with 256; lia | cbn; lia | rewrite Z.add_0_r; exact VS].
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19, U26, U27, U46, U47.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I;
      try (unfold SHADOW_OFF in *; lia).
    rewrite (can_denot_shadow (cf_E regs exb) 19 26 (l_p cx + 1) SHADOW_OFF E19 E26 ltac:(lia)
      ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)).
    cbn [sv_denot]. rewrite U46, Z.add_0_r. reflexivity. }
assert (SHOK : sh_ok segs cf_Bx (@nil shent) (cf_E regs exb) (mrestrict (w_H W) mem)) by constructor.
assert (KVr : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) mem a = aview segs (w_H W) mem a)
  by (intros; reflexivity).
assert (GPr : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem a) by (intros a Ha; exact Ha).
(* +0x214 .. +0x224: the cursor's shadow byte *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ cf_awr_ro. }
assert (KV1 : forall a, 0 <= a < 2 ^ 64 ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha. apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [|exact Ha | intros []].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hx; lia|]).
  destruct Hin. }
pose proof HG as GQ1. clear HF HFr HG.
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
rename ms into ms1. set (mm1 := ms_mem ms1) in *. set (rr1 := ms_regs ms1) in *.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* the shadow byte is 0: the fast path to +0x22c *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x22c.
  { cf_awr_ro. }
  assert (KV2 : forall a, 0 <= a < 2 ^ 64 ->
    aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mm1 a).
  { intros a Ha. apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [|exact Ha | intros []].
    intros b wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hx; lia|]).
  destruct Hin. }
  pose proof HG as GQ2. clear HF HFr HG.
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  set (mm2 := ms_mem ms) in *. set (rr2 := ms_regs ms) in *.
  (* the state at +0x22c: nothing written, the callee-saved registers kept *)
  assert (KVa : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) mm2 a = aview segs (w_H W) mem a)
    by (intros a Ha; rewrite (KV2 a Ha); exact (KV1 a Ha)).
  assert (GPa : forall a, apresent (w_H W) mem a -> apresent (w_H W) mm2 a)
    by (intros a Ha; exact (apresent_grows _ _ _ a GQ2 (apresent_grows _ _ _ a GQ1 Ha))).
  assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 23%bv;
      26%bv; Z_to_bv 5 19; Z_to_bv 5 27] -> YK11.getr rr2 r = YK11.getr regs r).
  { intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs exb _ HS _ _ r Hr);
      [apply cf_agree; cf_ag_go | vm_compute; reflexivity]. }
  pmkst HS.
  apply (FIN rr2 mm2 md2).
  + split; [exact HJ|].
    exact (cf_rest_step cx ly' S' W regs mem md 0 rr2 mm2 LAWS HB HC
      (KR 2%bv ltac:(cbn; tauto)) (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))
      (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto)) (fun a Ha _ => KVa a Ha) GPa).
  + exact HJ.
  + intros a Ha Hw. rewrite (KVa a Ha). exact (KV a Ha Hw).
  + intros a Ha. exact (GPa a (GP a Ha)).
  + exact KVa.
  + unfold cf_regs.
    rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
      (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
      (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
    exact HRG.
  + rewrite (KR 23%bv ltac:(cbn; tauto)). exact R23.
  + exact (KR 22%bv ltac:(cbn; tauto)).
  + split; [rewrite (KR (Z_to_bv 5 19) ltac:(cbn; tauto)); exact C19
           | rewrite (KR (Z_to_bv 5 27) ltac:(cbn; tauto)); exact C27].

- (* the shadow byte is in (1, 8): the slow path +0x18fc .. +0x1904 *)
  pose proof (cf_beqz (cf_E regs exb) 47 sb false U47 ltac:(lia) Hc) as Hs0.
  apply Z.eqb_neq in Hs0. clear Hc.
  assert (Hsb1 : 1 < sb < 8).
  { unfold saddr_ok in Hsbok. destruct Hsbok as [E0 | (Hlt & Hhi)]; [lia|]. rewrite Hp18 in Hlt. lia. }
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { cf_awr_ro. }
  assert (KV2 : forall a, 0 <= a < 2 ^ 64 ->
    aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mm1 a).
  { intros a Ha. apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [|exact Ha | intros []].
    intros b wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hx; lia|]).
  destruct Hin. }
  pose proof HG as GQ2. clear HF HFr HG.
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  rename ms into ms2. set (mm2 := ms_mem ms2) in *. set (rr2 := ms_regs ms2) in *.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  { exfalso.
    pose proof (cf_bge (cf_E regs exb) (l_p cx + 1) sb true U19 ltac:(lia) Hp18 U47 Hsb1 Hc).
    discriminate. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x22c.
  { cf_awr_ro. }
  assert (KV3 : forall a, 0 <= a < 2 ^ 64 ->
    aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mm2 a).
  { intros a Ha. apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [|exact Ha | intros []].
    intros b wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hx; lia|]).
  destruct Hin. }
  pose proof HG as GQ3. clear HF HFr HG.
  set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
  set (mm3 := ms_mem ms) in *. set (rr3 := ms_regs ms) in *.
  (* the state at +0x22c: nothing written, the callee-saved registers kept *)
  assert (KVa : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) mm3 a = aview segs (w_H W) mem a)
    by (intros a Ha; rewrite (KV3 a Ha), (KV2 a Ha); exact (KV1 a Ha)).
  assert (GPa : forall a, apresent (w_H W) mem a -> apresent (w_H W) mm3 a)
    by (intros a Ha; exact (apresent_grows _ _ _ a GQ3 (apresent_grows _ _ _ a GQ2 (apresent_grows _ _ _ a GQ1 Ha)))).
  assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 23%bv;
      26%bv; Z_to_bv 5 19; Z_to_bv 5 27] -> YK11.getr rr3 r = YK11.getr regs r).
  { intros r Hr. refine (regs_kept_of_st_ok _ _ _ (restrict (w_H W) ms) regs exb _ HS _ _ r Hr);
      [apply cf_agree; cf_ag_go | vm_compute; reflexivity]. }
  pmkst HS.
  apply (FIN rr3 mm3 md3).
  + split; [exact HJ|].
    exact (cf_rest_step cx ly' S' W regs mem md 0 rr3 mm3 LAWS HB HC
      (KR 2%bv ltac:(cbn; tauto)) (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))
      (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto)) (fun a Ha _ => KVa a Ha) GPa).
  + exact HJ.
  + intros a Ha Hw. rewrite (KVa a Ha). exact (KV a Ha Hw).
  + intros a Ha. exact (GPa a (GP a Ha)).
  + exact KVa.
  + unfold cf_regs.
    rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)),
      (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 18%bv ltac:(cbn; tauto)),
      (KR 26%bv ltac:(cbn; tauto)), (KR 21%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)).
    exact HRG.
  + rewrite (KR 23%bv ltac:(cbn; tauto)). exact R23.
  + exact (KR 22%bv ltac:(cbn; tauto)).
  + split; [rewrite (KR (Z_to_bv 5 19) ltac:(cbn; tauto)); exact C19
           | rewrite (KR (Z_to_bv 5 27) ltac:(cbn; tauto)); exact C27].
Qed.

(* ------------------------------------------------------------------ *)
(* 13. The segment                                                     *)
(* ------------------------------------------------------------------ *)

Lemma lc_cfg_ok (K1 : @lc_rom_view_stmt rc B MT XL RLO RHI) (K2 : @lc_src_ro_stmt rc B MT XL RLO RHI) :
  @lc_cfg_stmt rc B MT XL RLO RHI.
Proof.
unfold lc_cfg_stmt. intros HP cx W' c' HB HCFGD.
destruct HCFGD as (ly' & S' & regs' & mem' & md' & Bw0 & B1 & -> & HC & HFR & HSP & HFS & HIO & HMT
  & HCUR & R23 & R21 & R20 & HW0 & ECD & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof HC as (_ & _ & _ & _ & C2 & C8 & C9 & C3 & C4 & _).
destruct HFR as (F18 & F26).
assert (HRG : cf_regs cx regs')
  by (unfold cf_regs; repeat split; assumption).
(* +0x1cc .. +0x214 *)
eapply SRr_bind;
  [exact (cf_stage_ab cx ly' S' W' regs' mem' md' HP HB K1 K2 HC HRG R23 HCUR)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & KV2 & GP2 & HH & HD & F12 & F16 & F20
  & HRG2 & R23b & R22b & HCUR2).
pose proof HRG2 as (Q2 & Q8 & Q9 & Q3 & Q4 & Q18 & Q26 & Q21 & Q20).
assert (HC2 : @lc_core rc B cx ly' S' W' regs2 mem2 md2 0).
{ split; [exact HJ2|].
  exact (cf_rest_step cx ly' S' W' regs' mem' md' 0 regs2 mem2 LAWS HB HC
    (eq_trans Q2 (eq_sym C2)) (eq_trans Q8 (eq_sym C8)) (eq_trans Q9 (eq_sym C9))
    (eq_trans Q3 (eq_sym C3)) (eq_trans Q4 (eq_sym C4)) KV2 GP2). }
destruct (Z.eq_dec (TOP.fi_n (lc_c1 (l_pl cx))) 0) as [Hz0 | Hnz].
- exact (cf_case0 cx ly' S' W' regs' mem' md' Bw0 B1 regs2 mem2 md2 HP HB HC HSP HFS HIO HMT
    HW0 ECD HTW HC2 HJ2 KV2 GP2 HH HD F12 F16 F20 HRG2 R23b R22b HCUR2 Hz0).
- apply (cf_runb cx ly' S' W' mem' regs2 mem2 md2 HP HB HC2 HJ2 KV2 GP2 HRG2 R23b HCUR2 Hnz).
  intros regs3 mem3 md3 HC3 HJ3 KV3 GP3 KEQ HRG3 R23c R22c HCUR3.
  assert (HH3 : cf_bl W' mem3 (TA_g_cfg + 0) TC.HOST).
  { intros i Hi. assert (L6 : Z.of_nat (length TC.HOST) = 6) by reflexivity.
    rewrite (KEQ (TA_g_cfg + 0 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (HH i Hi). }
  assert (HD3 : cf_bl W' mem3 (TA_g_cfg + 6) TC.DESK).
  { intros i Hi. assert (L6 : Z.of_nat (length TC.DESK) = 6) by reflexivity.
    rewrite (KEQ (TA_g_cfg + 6 + i) ltac:(unfold TA_g_cfg in *; lia)). exact (HD i Hi). }
  assert (F123 : cf_bw W' mem3 (TA_g_cfg + 12) 4 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1)).
  { intros j Hj. rewrite (KEQ (TA_g_cfg + 12 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)).
    exact (F12 j Hj). }
  assert (F163 : cf_bw W' mem3 (TA_g_cfg + 16) 4 (Z.land (lc_flags (l_pl cx)) 1)).
  { intros j Hj. rewrite (KEQ (TA_g_cfg + 16 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)).
    exact (F16 j Hj). }
  assert (F203 : cf_bw W' mem3 (TA_g_cfg + 20) 4
    (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO)).
  { intros j Hj. rewrite (KEQ (TA_g_cfg + 20 + Z.of_nat j) ltac:(unfold TA_g_cfg in *; lia)).
    exact (F20 j Hj). }
  assert (R22d : YK11.getr regs3 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1))
    by exact (eq_trans R22c R22b).
  pose proof (cf_c1_n (l_pl cx)) as Hc1n.
  destruct (Z_le_gt_dec 14 (TOP.fi_n (lc_c1 (l_pl cx)))) as [Hge | Hlt].
  + exact (cf_case14 cx ly' S' W' regs' mem' md' Bw0 B1 regs3 mem3 md3 HP HB HC HSP HFS HIO HMT
      HW0 ECD HTW HC3 HJ3 KV3 GP3 HH3 HD3 F123 F163 F203 HRG3 R23c R22d HCUR3 Hge).
  + assert (Hc : TOP.fi_n (lc_c1 (l_pl cx)) = 1 \/ TOP.fi_n (lc_c1 (l_pl cx)) = 2 \/
      TOP.fi_n (lc_c1 (l_pl cx)) = 3 \/ TOP.fi_n (lc_c1 (l_pl cx)) = 4 \/
      TOP.fi_n (lc_c1 (l_pl cx)) = 5 \/ TOP.fi_n (lc_c1 (l_pl cx)) = 6 \/
      TOP.fi_n (lc_c1 (l_pl cx)) = 7 \/ TOP.fi_n (lc_c1 (l_pl cx)) = 8 \/
      TOP.fi_n (lc_c1 (l_pl cx)) = 9 \/ TOP.fi_n (lc_c1 (l_pl cx)) = 10 \/
      TOP.fi_n (lc_c1 (l_pl cx)) = 11 \/ TOP.fi_n (lc_c1 (l_pl cx)) = 12 \/
      TOP.fi_n (lc_c1 (l_pl cx)) = 13) by lia.
    destruct Hc as [E | [E | [E | [E | [E | [E | [E | [E | [E | [E | [E | [E | E]]]]]]]]]]]].
    * apply (cf_case1 cx ly' S' W' regs' mem' md' Bw0 B1 regs3 mem3 md3 HP HB HC HSP HFS HIO HMT
        HW0 ECD HTW HC3 HJ3 KV3 GP3 HH3 HD3 F123 F163 F203 HRG3 R23c R22d HCUR3 E).
    * apply (cf_case2 cx ly' S' W' regs' mem' md' Bw0 B1 regs3 mem3 md3 HP HB HC HSP HFS HIO HMT
        HW0 ECD HTW HC3 HJ3 KV3 GP3 HH3 HD3 F123 F163 F203 HRG3 R23c R22d HCUR3 E).
    * apply (cf_case3 cx ly' S' W' regs' mem' md' Bw0 B1 regs3 mem3 md3 HP HB HC HSP HFS HIO HMT
        HW0 ECD HTW HC3 HJ3 KV3 GP3 HH3 HD3 F123 F163 F203 HRG3 R23c R22d HCUR3 E).
    * apply (cf_case4 cx ly' S' W' regs' mem' md' Bw0 B1 regs3 mem3 md3 HP HB HC HSP HFS HIO HMT
        HW0 ECD HTW HC3 HJ3 KV3 GP3 HH3 HD3 F123 F163 F203 HRG3 R23c R22d HCUR3 E).
    * apply (cf_case5 cx ly' S' W' regs' mem' md' Bw0 B1 regs3 mem3 md3 HP HB HC HSP HFS HIO HMT
        HW0 ECD HTW HC3 HJ3 KV3 GP3 HH3 HD3 F123 F163 F203 HRG3 R23c R22d HCUR3 E).
    * apply (cf_case6 cx ly' S' W' regs' mem' md' Bw0 B1 regs3 mem3 md3 HP HB HC HSP HFS HIO HMT
        HW0 ECD HTW HC3 HJ3 KV3 GP3 HH3 HD3 F123 F163 F203 HRG3 R23c R22d HCUR3 E).
    * apply (cf_case7 cx ly' S' W' regs' mem' md' Bw0 B1 regs3 mem3 md3 HP HB HC HSP HFS HIO HMT
        HW0 ECD HTW HC3 HJ3 KV3 GP3 HH3 HD3 F123 F163 F203 HRG3 R23c R22d HCUR3 E).
    * apply (cf_case8 cx ly' S' W' regs' mem' md' Bw0 B1 regs3 mem3 md3 HP HB HC HSP HFS HIO HMT
        HW0 ECD HTW HC3 HJ3 KV3 GP3 HH3 HD3 F123 F163 F203 HRG3 R23c R22d HCUR3 E).
    * apply (cf_case9 cx ly' S' W' regs' mem' md' Bw0 B1 regs3 mem3 md3 HP HB HC HSP HFS HIO HMT
        HW0 ECD HTW HC3 HJ3 KV3 GP3 HH3 HD3 F123 F163 F203 HRG3 R23c R22d HCUR3 E).
    * apply (cf_case10 cx ly' S' W' regs' mem' md' Bw0 B1 regs3 mem3 md3 HP HB HC HSP HFS HIO HMT
        HW0 ECD HTW HC3 HJ3 KV3 GP3 HH3 HD3 F123 F163 F203 HRG3 R23c R22d HCUR3 E).
    * apply (cf_case11 cx ly' S' W' regs' mem' md' Bw0 B1 regs3 mem3 md3 HP HB HC HSP HFS HIO HMT
        HW0 ECD HTW HC3 HJ3 KV3 GP3 HH3 HD3 F123 F163 F203 HRG3 R23c R22d HCUR3 E).
    * apply (cf_case12 cx ly' S' W' regs' mem' md' Bw0 B1 regs3 mem3 md3 HP HB HC HSP HFS HIO HMT
        HW0 ECD HTW HC3 HJ3 KV3 GP3 HH3 HD3 F123 F163 F203 HRG3 R23c R22d HCUR3 E).
    * apply (cf_case13 cx ly' S' W' regs' mem' md' Bw0 B1 regs3 mem3 md3 HP HB HC HSP HFS HIO HMT
        HW0 ECD HTW HC3 HJ3 KV3 GP3 HH3 HD3 F123 F163 F203 HRG3 R23c R22d HCUR3 E).
Qed.

End cfg.
