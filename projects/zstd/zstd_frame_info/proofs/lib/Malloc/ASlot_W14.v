(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import Malloc_fp MallocKit_A2 F_malloc_bigw F_malloc_big.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocKit_A3.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma land_high_low x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.land (x * 2^k) y = 0.
Proof.
  intros Hx Hk Hy. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n k) as [LT|GE].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0040>22555333611.1158285538305.1061382040793.116944168077.11 00000700;00?00CS2Hy2NZS2LTS2GES2Hy".
rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit y n) with false; [apply Bool.andb_false_r|].
    symmetry. destruct (Z.eq_dec y 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ k); [|lia]. apply Z.log2_lt_pow2; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma lor_shl_small x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.lor (x * 2^k) y = x * 2^k + y.
Proof. intros. apply lor_disjoint_add. apply land_high_low; assumption. Qed.

#[using="Type"] Lemma lor_small_shl x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.lor y (x * 2^k) = x * 2^k + y.
Proof. intros. rewrite Z.lor_comm. apply lor_shl_small; assumption. Qed.

#[using="Type"] Lemma lor_32 c : 0 <= c < 32 -> Z.lor c 32 = c + 32.
Proof. intros. change 32 with (1 * 2^5) at 1. Local Ltac2 Set LiaHints.tbl := fun () => "0040=18282174835.329311285958.356924295054.36758013062.3 000001002005006SSS1HS".
rewrite lor_small_shl by lia. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma land_pg_mask q : 0 <= q < 2^52 -> Z.land (4096 * q) 18446744073709547520 = 4096 * q.
Proof.
  intros Hq. Local Ltac2 Set LiaHints.tbl := fun () => "0040=13243987229.317210505389.345081156397.359206986038.3000004005006007S2HqSSS".
replace (4096 * q) with (Z.shiftl q 12) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  change 18446744073709547520 with (Z.shiftl (Z.ones 52) 12).
  rewrite <- Z.shiftl_land. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma hdr_byte_facts x ai : 0 <= x < 256 -> 0 <= ai < 32 ->
  0 <= Z.lor (Z.land x 18446744073709551584) ai < 256 /\ Z.land (Z.lor (Z.land x 18446744073709551584) ai) 31 = ai.
Proof.
  intros Hx Hai.
  assert (E : Z.land x 18446744073709551584 = Z.land x 224).
  { Local Ltac2 Set LiaHints.tbl := fun () => "0080=24997267206.725793536646.726800064025.629311285958.744738322902.756087464873.663370424053.567153861609.500000500;00<00=00B00F00G00KS3HaiS2Hx1HSSS3HaiS2HxSS2Hx".
replace x with (Z.land x 255) at 1 by (change 255 with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    rewrite <- !Z.land_assoc. reflexivity. }
  rewrite E. pose proof (land_upper x 224 ltac:(lia) ltac:(lia)).
  split.
  - change 256 with (2^8). apply lor_lt_pow2; lia.
  - rewrite Z.land_lor_distr_l. rewrite <- Z.land_assoc. change (Z.land 224 31) with 0. rewrite Z.land_0_r. rewrite Z.lor_0_l.
    change 31 with (Z.ones 5). rewrite Z.land_ones, Z.mod_small by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma tail_low16 sc cnt q : 0 <= sc < 48 -> 1 <= cnt <= 32 -> 0 <= q < 16 ->
  Z.lor (Z.lor (Z.land sc 63 * 2^6) (Z.lor (Z.land (cnt - 1) 31) 32)) (Z.land (4096 * q) 18446744073709547520)
  = (cnt - 1) + 32 + 64 * sc + 4096 * q.
Proof.
  intros Hsc Hc Hq.
  Local Ltac2 Set LiaHints.tbl := fun () => "00=0=10250819684.713243987229.717210505389.718042793893.719702666657.729317572413.739170541418.741721150785.746849625707.757862860525.759206986038.763967159373.76755911037.7 00000500900:00?00G00H00L00P00Q00U00V00W00XS3HscS2HqSS3HscS3Hsc2HcSS2HqS2HcSS2HcSSS".
replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  rewrite land_pg_mask by lia.
  replace 32 with (1 * 2^5) at 1 by reflexivity. rewrite (lor_small_shl 1 5 (cnt - 1)) by lia.
  rewrite (lor_shl_small sc 6) by (cbn; lia).
  replace (4096 * q) with (q * 2^12) by (cbn; lia). rewrite (lor_small_shl q 12) by (cbn; lia). cbn. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma firstn_le_bytes n k z : firstn n (Z_to_le_bytes (n + k) z) = Z_to_le_bytes n z.
Proof. revert z. induction n as [|n IH]; intros z; [reflexivity|]. cbn [Z_to_le_bytes Nat.add firstn]. f_equal. apply IH. Qed.

#[using="Type"] Lemma skipn_le_bytes n k z : skipn n (Z_to_le_bytes (n + k) z) = Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof.
  revert z. induction n as [|n IH]; intros z.
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [Z_to_le_bytes Nat.add skipn]. rewrite IH. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0020=51859486093.553891794422.5000001002SS".
rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma tail_word_bytes (s0r : word) (L W W' : Z) :
  0 <= W < 2^64 -> 0 <= W' < 2^64 -> 0 <= L < 65536 ->
  bv_unsigned s0r mod 65536 = L -> W' mod 65536 = L -> Z.shiftr W' 16 = Z.shiftr W 16 ->
  le2 s0r ++ skipn 2 (le8 (wz W)) = le8 (wz W').
Proof.
  intros HW HW' HL HS HM HH.
  unfold le2, le8, word_to_le_bytes, wz. Local Ltac2 Set LiaHints.tbl := fun () => "0030>10425950486.1125140793750.1165068768018.1100000400900:S2HWS3HW'S".
rewrite !unsigned_lit by lia.
  change 8%nat with (2 + 6)%nat. rewrite skipn_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul].
  rewrite <- (firstn_skipn 2 (Z_to_le_bytes (2 + 6) W')). rewrite firstn_le_bytes, skipn_le_bytes.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]. rewrite HH. f_equal.
  rewrite <- (Z_to_le_bytes_mod 2 (bv_unsigned s0r) 16) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 2 W' 16) by (cbn; lia).
  change (2^16) with 65536. rewrite HS, HM. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma word_low16_bytes W : 0 <= W < 2^64 -> firstn 2 (le8 (wz W)) = le2 (wz (W mod 65536)).
Proof.
  intros HW. unfold le2, le8, word_to_le_bytes, wz. Local Ltac2 Set LiaHints.tbl := fun () => "0030=10425952647.322642338259.365068766083.3000004008009S2HWS2HWS".
rewrite !unsigned_lit by (try lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  change 8%nat with (2 + 6)%nat. rewrite firstn_le_bytes.
  change 65536 with (2^16). rewrite Z_to_le_bytes_mod by (cbn; lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma sllw2_word i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (i mod 32))) = wz (sxv (2 ^ (i + 1))).
Proof.
  intros Hi. Local Ltac2 Set LiaHints.tbl := fun () => "0040=10351595562.310709356901.363045839500.36755912037.3 00000400500900:S2HiSS2HiS".
rewrite Z.mod_small by lia. change 2 with (2^1) at 1. rewrite Z.shiftl_mul_pow2, <- Z.pow_add_r by lia.
  replace (1 + i) with (i + 1) by lia. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma subw_sxv_word a b : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv a)) - bv_unsigned (wz (sxv b)))) = wz (sxv (a - b)).
Proof.
  rewrite !wz_unsigned by (apply sxv_range). unfold wz, sxv.
  rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (bv_swrap 32 a mod 2 ^ 64 - bv_swrap 32 b mod 2 ^ 64))). f_equal.
  rewrite !swrap32_eq'. Local Ltac2 Set LiaHints.tbl := fun () => "0010=63831224076.3000001S".
mlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma cell_read_hdr_havoc_old : forall st b o,
  snd b mod 16 = 0 -> 0 <= o < 12 ->
  (forall v t, (r_cells (get_shadow st (fst b))) !! (snd b + o) = Some (v, t) -> (t < s_tick st)%N) ->
  exists h, cell_read (get_shadow (hdr_havoc b st) (fst b)) (snd b + o) = Unknown h.
Proof.
  intros st b o B16 Ho OLD. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id].
  unfold cell_read. cbn [r_cells r_hav r_havp].
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=33731297336.740979608525.758482627134.700000800<00DS3B162HoS2HoS3B162Ho".
replace ((snd b + o) / 16) with (snd b / 16) by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  rewrite lookup_insert_eq. cbn [default from_option id].
  replace ((snd b + o) mod 16) with o by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  unfold hav_add. unfold stale. cbn [existsb fst snd].
  replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
  destruct (r_cells (get_shadow st (fst b)) !! (snd b + o)) as [[v t]|] eqn:E.
  - specialize (OLD v t eq_refl). replace (t <? s_tick st)%N with true by (symmetry; apply N.ltb_lt; exact OLD).
    cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
  - cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
  (r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.

(* [comment removed for export] *)
Definition stA : mstate := hdr_havoc p stT.
Definition stB : mstate := set_usage sc (usage stT sc + cnt) stA.
Definition recA : meta := mkMeta None None (Some p) AV FR 0 0 0 ml.
Definition stC : mstate := put_meta mt recA stB.
Definition stD : mstate := put_group p (Some mt) ai stC.
Definition recF : meta := mkMeta (Some mt) (Some mt) (Some p) (AV - 1) FR (cnt - 1) 1 sc ml.
Definition stE : mstate := put_meta mt recF stD.
Definition stFin : mstate := set_active sc (Some mt) stE.

(* [comment removed for export] *)
Definition st_model : mstate :=
  let st := hdr_havoc p stT in
  let st1 := set_usage sc (usage st sc + cnt) st in
  let avail := mask_upto ai in
  let freed := mask_upto (cnt - 1) - avail in
  let st2 := upd_meta mt (fun r =>
               m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
               (m_set_mem (Some p) (m_set_freed freed (m_set_avail avail r)))))) st1 in
  let st3 := put_group p (Some mt) ai st2 in
  let st4 := add_slots mt p (get_stride (get_meta_rec st3 mt)) cnt st3 in
  let st5 := upd_meta mt (fun r => m_set_avail (m_avail r - 1) r) st4 in
  let st6 := upd_meta mt (fun r => m_set_prev (Some mt) (m_set_next (Some mt) r)) st5 in
  set_active sc (Some mt) st6.

#[using="stT cnt ai mt p G P AV FR P0"] Lemma mask_upto_range k : 0 <= k <= 31 -> 1 <= mask_upto k < 2^32 /\ 2^k <= mask_upto k.
Proof.
  intros Hkk. unfold mask_upto. Local Ltac2 Set LiaHints.tbl := fun () => "0060>25671427541.333482648185.34 41418083475.3241422282358.3351792502754.326753815139.32 00000800E00I00M00U00YS2P03HkkS2P03Hkk1H2H0S2P0S2P0S2P03HkkS2P0".
rewrite Z.pow_add_r by lia. change (2^1) with 2.
  assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
  assert (2^k <= 2^31) by (apply Z.pow_le_mono_r; lia).
  change (2^32) with (2 * 2^31). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="stT mt p G P CNT AI P0"] Lemma AV_FR_range : 1 <= AV < 2^32 /\ 0 <= FR < 2^32 /\ 0 <= AV - 1 < 2^32.
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "0050>15790603493.3241416074060.3443223934777.3553949108762.3058878855052.3400000800<00O00Z00aS3CNT2P0S2P0S3CNT2AI2P02A12C11HS3CNT2AI2P0S2AI2P0".
pose proof (mask_upto_range ai ltac:(lia)) as [A1 A2]. pose proof (mask_upto_range (cnt - 1) ltac:(lia)) as [C1 C2].
  assert (mask_upto ai <= mask_upto (cnt - 1)).
  { unfold mask_upto. apply Z.sub_le_mono_r. apply Z.pow_le_mono_r; lia. }
  unfold AV, FR. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rec_set_slots st v q : get_meta_rec (set_slots v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_put_group st b g a q : get_meta_rec (put_group b g a st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_hdr_havoc st b q : get_meta_rec (hdr_havoc b st) q = get_meta_rec st q. Proof. reflexivity. Qed.

#[using="G P SC CNT REC P0"] Lemma st_model_eq_rec q : get_meta_rec st_model q = get_meta_rec stFin q.
Proof.
  unfold st_model, stFin, stE, stD, stC, stB, stA. cbv zeta. unfold upd_meta, add_slots.
  rewrite !rec_set_active.
  destruct (decide (q = mt)) as [->|NE].
  - rewrite !get_meta_rec_put_same, rec_set_slots, rec_put_group, get_meta_rec_put_same, rec_set_usage, rec_hdr_havoc, REC.
    unfold recF. cbv [m_set_prev m_set_next m_set_avail m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen].
    Local Ltac2 Set LiaHints.tbl := fun () => "0040>18042335451.3029317249091.3057862664595.3063966968627.3000000700;00C00GS2SC2P0S2P0S3CNT2P0S2P0".
replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    change (Z.land 1 1) with 1. reflexivity.
  - rewrite !get_meta_rec_put_other, rec_set_slots, !rec_put_group, !get_meta_rec_put_other by congruence. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition tailW : list (Z * Z) :=
  [(CTX + 464 + 8 * sc, CTX + 464 + 8 * sc + 8); (G, G + 40); (P, P + 9); (CTX + 80 + 8 * sc, CTX + 80 + 8 * sc + 8)]%Z.
End TAIL.


End CANSEC1.
