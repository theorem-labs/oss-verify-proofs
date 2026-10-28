(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Lemma hdr_short_walk : forall (usp len : Z) (gp t0 t1 t2 v a1 a2 a3 a4 a5 a6 a7 s1 p1 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  0 <= len <= 5 -> stderr_cells m -> mem_inv asegs m ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xb135c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
                          (Z_to_bv 64 S_SHORT) (Z_to_bv 64 31) (Z_to_bv 64 1) (Z_to_bv 64 STDERR_FILE) a4 a5 a6 a7 p1 (Z_to_bv 64 len)
                          s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fwrite m))
    (MS (mkR (Z_to_bv 64 0xb1264) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1 v
             a1 a2 a3 a4 a5 a6 a7 p1 (Z_to_bv 64 len) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb1264) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros Hl [SC1 SC2] MI. unfold GOT_STDERR, STDERR_VAR in SC1, SC2.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EL : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  step. step. if_true.
  do 9 step.
  apply evt_done. unfold entry_st. reflexivity.
Qed.

Lemma diag_free_walk : forall (usp : Z) (gp t0 t1 t2 v a1 a2 a3 a4 a5 a6 a7 s0 s1 p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  mem_inv asegs m ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xb1364) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1
                          s1 a1 a2 a3 a4 a5 a6 a7 p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m))
    (MS (mkR (Z_to_bv 64 0xb135c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 v
             a1 a2 a3 a4 a5 a6 a7 p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb135c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 2 step.
  apply evt_done. unfold entry_st. reflexivity.
Qed.

Lemma main_ret_walk : forall (usp : Z) (gp s0 s1 p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : word -> option byte) (lo : Z)
    (c0 c1 c2 c3 c4 c5 c6 c7 : word) junk,
  stk asegs m lo (usp - 80) -> SEGTOP_A <= lo -> lo + 0x100000 <= usp -> usp mod 16 = 0 -> usp <= 2^47 ->
  rw_cells asegs m (usp - 80) [CB 8 junk; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 (Z_to_bv 64 MAIN_RA)] ->
  mem_inv asegs m ->
  evt asegs (fun ms' => ms' = entry_st (Z_to_bv 64 0x14acd8) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2
                                    c0 c1 s0 a1 a2 a3 a4 a5 a6 a7
                                    c2 c3 c4 c5 c6 c7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_exit m
       /\ stk asegs m lo usp)
    (MS (mkR (Z_to_bv 64 0xb1364) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7
             p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb1364) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST SL LO U16 UT FR MI.
  pose proof ST as (STa & STb & _). unfold SEGTOP_A in SL.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; lia).
  do 12 step.
  rewrite (ret_pc_even MAIN_RA) by (unfold MAIN_RA; lia).
  unfold MAIN_RA. step.
  release_frame FR ST usp.
  apply evt_done. split; [| exact ST].
  unfold entry_st. replace (usp - 80 + 80) with usp by lia. reflexivity.
Qed.

Lemma byte_range' : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Definition sx8 (c : Z) : Z := if c <? 128 then c else c - 256.
Lemma signed_byte : forall b : byte, bv_signed b = sx8 (bv_unsigned b).
Proof.
  intros b. pose proof (byte_range' b) as R. unfold bv_signed, sx8. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn -[bv_unsigned Z.modulo Z.add Z.sub Z.ltb Z.mul]. change (2 ^ 8 / 2) with 128. change (2 ^ 8) with 256.
  destruct (Z.ltb_spec (bv_unsigned b) 128).
  - rewrite Z.mod_small; lia.
  - replace (bv_unsigned b + 128) with ((bv_unsigned b - 128) + 1 * 256) by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small; lia.
Qed.

Lemma land15_mod' : forall x, Z.land x 32767 = x mod 32768.
Proof. intros. change 32767 with (Z.ones 15). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_shiftl_small' : forall a b k, 0 <= k -> 0 <= a < 2^k -> Z.land (Z.shiftl b k) a = 0.
Proof.
  intros a b k Hk Ha. rewrite Z.shiftl_mul_pow2 by lia.
  replace a with (Z.land a (Z.ones k)) by (rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  rewrite (Z.land_comm a), Z.land_assoc, Z.land_ones by lia. rewrite Z_mod_mult. apply Z.land_0_l.
Qed.
Lemma lor_shiftl_add' : forall a b k, 0 <= k -> 0 <= a < 2^k -> Z.lor (Z.shiftl b k) a = a + b * 2^k.
Proof.
  intros a b k Hk Ha. rewrite <- Z.lxor_lor by (apply land_shiftl_small'; lia).
  rewrite <- Z.add_nocarry_lxor by (apply land_shiftl_small'; lia). rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.
Lemma lor_mul_add' : forall a b k, 0 <= k -> 0 <= a < 2^k -> Z.lor (b * 2^k) a = a + b * 2^k.
Proof. intros a b k Hk Ha. rewrite <- Z.shiftl_mul_pow2 by lia. rewrite lor_shiftl_add' by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma cfg_inner : forall d0 d1 : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned (sxb d1) ≪ 57)) ≫ 49))) (bv_unsigned (zxb d0))
  = Z.land (bv_unsigned d0 + bv_unsigned d1 * 256) 32767.
Proof.
  intros d0 d1. pose proof (byte_range' d0) as R0. pose proof (byte_range' d1) as R1.
  set (u0 := bv_unsigned d0) in *. set (u1 := bv_unsigned d1) in *.
  assert (E1 : bv_unsigned (sxb d1) = sx8 u1 mod 2^64) by (unfold sxb; rewrite unsigned_lit_wrap, signed_byte; reflexivity).
  assert (E0 : bv_unsigned (zxb d0) = u0) by (unfold zxb; rewrite unsigned_lit by lia; reflexivity).
  rewrite E0, E1. rewrite !unsigned_lit_wrap. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  assert (E : (sx8 u1 mod 2 ^ 64 * 2 ^ 57) mod 2 ^ 64 / 2 ^ 49 = (u1 mod 128) * 2^8).
  { unfold sx8. destruct (Z.ltb_spec u1 128).
    - rewrite (Z.mod_small u1 (2^64)) by lia. rewrite (Z.mod_small u1 128) by lia.
      rewrite Z.mod_small by (split; [lia|]; change (2^64) with (2^7 * 2^57); apply Z.mul_lt_mono_pos_r; lia).
      change (2^57) with (2^49 * 2^8). rewrite Z.mul_assoc, (Z.mul_comm u1), <- Z.mul_assoc. rewrite Z.mul_comm.
      rewrite Z.div_mul by lia. lia.
    - replace ((u1 - 256) mod 2^64) with (2^64 - 256 + u1) by (Z.div_mod_to_equations; nia).
      replace ((2 ^ 64 - 256 + u1) * 2 ^ 57) with ((u1 - 128) * 2^57 + (2^57 - 1) * 2^64) by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
      replace (u1 mod 128) with (u1 - 128) by (Z.div_mod_to_equations; lia).
      change (2^57) with (2^8 * 2^49). rewrite Z.mul_assoc. rewrite Z.div_mul by lia. reflexivity. }
  rewrite E. rewrite (Z.mod_small (u1 mod 128 * 2^8)) by (pose proof (Z.mod_pos_bound u1 128); nia).
  rewrite lor_mul_add' by lia. rewrite land15_mod'. Z.div_mod_to_equations. lia.
Qed.

Lemma hdr_over_walk : forall (usp buf len : Z) (d0 d1 : byte) (rest : list byte)
    (gp t0 t1 t2 v a1 a2 a3 a4 a5 a6 a7 p1 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : word -> option byte),
  6 <= len < 2^40 -> 0 < buf -> buf + len < 2^64 -> bytes_at asegs m buf (d0 :: d1 :: rest) ->
  len < 6 + Z.land (bv_unsigned d0 + bv_unsigned d1 * 256) 32767 ->
  stderr_cells m -> mem_inv asegs m ->
  evt asegs (fun ms => exists (b0 b1 : word),
                 ms = entry_st (Z_to_bv 64 0xb135c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf)
                          (Z_to_bv 64 S_OVER) (Z_to_bv 64 31) (Z_to_bv 64 1) (Z_to_bv 64 STDERR_FILE) a4 a5 a6 a7 b0 (Z_to_bv 64 len)
                          s4 b1 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fwrite m)
    (MS (mkR (Z_to_bv 64 0xb1264) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) v
             a1 a2 a3 a4 a5 a6 a7 p1 (Z_to_bv 64 len) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb1264) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros Hl Hb Hbl BD Hover [SC1 SC2] MI. unfold GOT_STDERR, STDERR_VAR in SC1, SC2.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EL : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (EB : bv_unsigned (Z_to_bv 64 buf) = buf) by (apply unsigned_lit; lia).
  step. step. if_false.
  pose proof (u8ro_read asegs m _ _ 1 d1 (wa (buf + 1)) BD eq_refl ltac:(lia) eq_refl) as R1.
  step. clear R1.
  pose proof (u8ro_read asegs m _ _ 0 d0 (wa (buf + 0)) BD eq_refl ltac:(lia) eq_refl) as R0.
  step. clear R0.
  step. step. step.
  rewrite cfg_inner.
  assert (LR : 0 <= Z.land (bv_unsigned d0 + bv_unsigned d1 * 256) 32767 < 32768).
  { pose proof (byte_range' d0). pose proof (byte_range' d1). rewrite land15_mod'. apply Z.mod_pos_bound. lia. }
  set (L := Z.land (bv_unsigned d0 + bv_unsigned d1 * 256) 32767) in *.
  step.
  assert (E6 : bv_unsigned (Z_to_bv 64 (L + 6)) = L + 6) by (apply unsigned_lit; lia).
  step. if_true.
  do 8 step.
  apply evt_done. do 2 eexists. unfold entry_st. reflexivity.
Qed.

Lemma skipn4' : forall (l : list byte) n, (n + 4 <= length l)%nat -> exists q0 q1 q2 q3 r, skipn n l = q0 :: q1 :: q2 :: q3 :: r.
Proof.
  intros l n H. pose proof (length_skipn n l) as L.
  destruct (skipn n l) as [|q0 [|q1 [|q2 [|q3 r]]]]; cbn in L; try lia. do 5 eexists. reflexivity.
Qed.

Lemma hdr_good_walk : forall (usp buf len : Z) (d0 d1 : byte) (rest : list byte)
    (gp t0 t1 t2 v a1 a2 a3 a4 a5 a6 a7 p1 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : word -> option byte),
  6 <= len < 2^40 -> 0 < buf -> buf + len < 2^64 -> bytes_at asegs m buf (d0 :: d1 :: rest) ->
  Z.of_nat (length (d0 :: d1 :: rest)) = len ->
  6 + Z.land (bv_unsigned d0 + bv_unsigned d1 * 256) 32767 <= len ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (b0 : word),
                 ms = entry_st (Z_to_bv 64 0xb12dc) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 (buf + 2))
                          (Z_to_bv 64 buf) (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 (Z.land (bv_unsigned d0 + bv_unsigned d1 * 256) 32767))
                          (Z_to_bv 64 (buf + 6 + Z.land (bv_unsigned d0 + bv_unsigned d1 * 256) 32767))
                          (Z_to_bv 64 (len - 6 - Z.land (bv_unsigned d0 + bv_unsigned d1 * 256) 32767)) b0 a5 a6 a7
                          (Z_to_bv 64 (Z.land (bv_unsigned d0 + bv_unsigned d1 * 256) 32767))
                          (Z_to_bv 64 (buf + 6 + Z.land (bv_unsigned d0 + bv_unsigned d1 * 256) 32767))
                          (Z_to_bv 64 (len - 6 - Z.land (bv_unsigned d0 + bv_unsigned d1 * 256) 32767)) (sxb d1) s6 s7
                          s8 s9 s10 s11 t3 t4 t5 t6 F fc 0xb1438 m)
    (MS (mkR (Z_to_bv 64 0xb1264) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) v
             a1 a2 a3 a4 a5 a6 a7 p1 (Z_to_bv 64 len) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb1264) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros Hl Hb Hbl BD HLEN Hgood MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EL : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (EB : bv_unsigned (Z_to_bv 64 buf) = buf) by (apply unsigned_lit; lia).
  step. step. if_false.
  pose proof (u8ro_read asegs m _ _ 1 d1 (wa (buf + 1)) BD eq_refl ltac:(lia) eq_refl) as R1.
  step. clear R1.
  pose proof (u8ro_read asegs m _ _ 0 d0 (wa (buf + 0)) BD eq_refl ltac:(lia) eq_refl) as R0.
  step. clear R0.
  step. step. step.
  rewrite cfg_inner.
  assert (LR : 0 <= Z.land (bv_unsigned d0 + bv_unsigned d1 * 256) 32767 < 32768).
  { pose proof (byte_range' d0). pose proof (byte_range' d1). rewrite land15_mod'. apply Z.mod_pos_bound. lia. }
  set (L := Z.land (bv_unsigned d0 + bv_unsigned d1 * 256) 32767) in *.
  step.
  assert (E6 : bv_unsigned (Z_to_bv 64 (L + 6)) = L + 6) by (apply unsigned_lit; lia).
  step. if_false.
  step. step.

  destruct (skipn4' (d0 :: d1 :: rest) (Z.to_nat (2 + L)) ltac:(lia)) as (q0 & q1 & q2 & q3 & rest' & EQ4).
  assert (QB : bytes_at asegs m (buf + 2 + L) (q0 :: q1 :: q2 :: q3 :: rest')).
  { rewrite <- EQ4. pose proof BD as BD'. rewrite <- (firstn_skipn (Z.to_nat (2 + L)) (d0 :: d1 :: rest)) in BD'.
    apply bytes_at_app in BD'. destruct BD' as [_ X]. rewrite length_firstn in X.
    replace (buf + Z.of_nat (Nat.min (Z.to_nat (2 + L)) (length (d0 :: d1 :: rest)))) with (buf + 2 + L) in X by lia. exact X. }
  pose proof (u8ro_read asegs m _ _ 1 q1 (wa (buf + 2 + L + 1)) QB eq_refl ltac:(lia) eq_refl) as R1.
  step. clear R1.
  pose proof (u8ro_read asegs m _ _ 0 q0 (wa (buf + 2 + L)) QB eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as R0.
  step. clear R0.
  pose proof (u8ro_read asegs m _ _ 2 q2 (wa (buf + 2 + L + 2)) QB eq_refl ltac:(lia) eq_refl) as R2.
  step. clear R2.
  pose proof (u8ro_read asegs m _ _ 3 q3 (wa (buf + 2 + L + 3)) QB eq_refl ltac:(lia) eq_refl) as R3.
  step. clear R3.
  do 9 step.
  step. step.
  do 5 step.
  apply evt_done. eexists. unfold entry_st.
  replace (buf + 2 + L + 4) with (buf + 6 + L) by lia.
  rewrite (unsigned_lit L) by lia. replace (len + - L + -6) with (len - 6 - L) by lia.
  reflexivity.
Qed.

Lemma sxb_signed : forall b : byte, bv_signed (sxb b) = bv_signed b.
Proof.
  intros b. unfold sxb. rewrite Z_to_bv_signed. apply bv_swrap_small.
  pose proof (bv_signed_in_range 8 b ltac:(lia)) as R. change (bv_half_modulus 8) with 128 in R.
  change (bv_half_modulus 64) with (2^63). lia.
Qed.

Lemma tr_ret_walk : forall (usp : Z) (d1 : byte) (gp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 p1 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  bv_unsigned d1 < 128 -> mem_inv asegs m ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xb1364) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 v s1
                          s1 a1 a2 a3 a4 a5 a6 a7 p1 s3 s4 (sxb d1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m))
    (MS (mkR (Z_to_bv 64 0xb12dc) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 v
             a1 a2 a3 a4 a5 a6 a7 p1 s3 s4 (sxb d1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb12dc) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros Hd MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_signed (sxb d1) = bv_unsigned d1) by (rewrite sxb_signed, signed_byte; unfold sx8; destruct (Z.ltb_spec (bv_unsigned d1) 128); lia).
  pose proof (byte_range' d1) as R1.
  step. if_false.
  do 4 step.
  apply evt_done. unfold entry_st. reflexivity.
Qed.

Lemma tr_ret_walk_count : forall (usp : Z) (d1 : byte) (gp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 p1 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  128 <= bv_unsigned d1 -> mem_inv asegs m ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xb1364) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 0) s1
                          s1 (Z_to_bv 64 251) a2 a3 a4 a5 a6 a7 p1 s3 s4 (sxb d1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m))
    (MS (mkR (Z_to_bv 64 0xb12dc) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 v
             a1 a2 a3 a4 a5 a6 a7 p1 s3 s4 (sxb d1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb12dc) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros Hd MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (byte_range' d1) as R1.
  assert (ES : bv_signed (sxb d1) = bv_unsigned d1 - 256) by (rewrite sxb_signed, signed_byte; unfold sx8; destruct (Z.ltb_spec (bv_unsigned d1) 128); lia).
  step. if_true.
  do 6 step. if_true.
  do 2 step.
  apply evt_done. unfold entry_st. reflexivity.
Qed.
