(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset_stmt U_normalize_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_pow5_stmt U_pow10_stmt U_shl_stmt U_hi64_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_hi64_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_positive_digit_comp_d_stmt U_negative_digit_comp_d_stmt U_positive_digit_comp_f_stmt U_negative_digit_comp_f_stmt U_slow_path_double_stmt U_slow_path_float_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_from_chars_double.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_from_chars_float.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_from_chars_double_stmt U_from_chars_float_stmt U_from_chars_int_stmt U_ciir_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_normalize_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset_stmt.U_compare_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow10_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_shl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_hi64_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_hi64_stmt.U_ctlz_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_positive_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_negative_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_positive_digit_comp_f_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_negative_digit_comp_f_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_double_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_float_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_parse_infnan_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_float.U_parse_infnan_f_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_float_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_int_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_ciir_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset.

Module U_compare.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset_stmt.U_compare_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Loop.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word).
  Variables (xv yv : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (xs ys : list word) (len : Z).
  Hypothesis Hxl : length xs = 62%nat.
  Hypothesis Hyl : length ys = 62%nat.
  Hypothesis LEN : (0 <= len <= 62)%Z.
  Hypothesis XL : u64arr USEGS m (bv_unsigned xv) xs.
  Hypothesis YL : u64arr USEGS m (bv_unsigned yv) ys.
  Hypothesis XC : rw_cells USEGS m (bv_unsigned xv + 496) [C2 (Z_to_bv 64 len)].
  Hypothesis YC : rw_cells USEGS m (bv_unsigned yv + 496) [C2 (Z_to_bv 64 len)].

  Notation X := (bv_unsigned xv).
  Notation Y := (bv_unsigned yv).
  Notation POST := (compare_post ra sp gp tp s0 s1 yv s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m).
  Notation NOTX := (Z_to_bv 64 (Z.lxor X 18446744073709551615)).
  Notation NOTY := (Z_to_bv 64 (Z.lxor Y 18446744073709551615)).

  (* [comment removed for export] *)
  Definition loop_ok (k : nat) : Prop :=
    forall (idx : Z) (t1 t2 t3 : word),
      (Z.to_nat idx = k)%nat -> (0 <= idx <= len)%Z ->
      evt USEGS POST
        (MS (mkR ra sp gp tp (Z_to_bv 64 (8 * idx - 8)) t1 t2 s0 s1 (Z_to_bv 64 1) yv xv (Z_to_bv 64 len) NOTX NOTY
                 (Z_to_bv 64 (-16)) (Z_to_bv 64 64) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x27d74) fc None m (seg_rom USEGS)).

  #[using="xs ys Hxl Hyl LEN XL YL XC YC"] Lemma cmp_loop : forall k, loop_ok k.
  Proof. LiaFast.lf_pins (fun (xs ys Hxl Hyl LEN XL YL XC YC : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; unfold loop_ok; intros idx t1 t2 t3 Hk Hidx.
    - (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc; [| exfalso; lia].
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      unfold compare_post. finish. all: first [apply munch_refl | apply wmono_refl | exact I].
    - pose proof (bv_unsigned_in_range 64 xv) as RA. unfold bv_modulus in RA.
      pose proof (bv_unsigned_in_range 64 yv) as RB. unfold bv_modulus in RB.
      pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hxl in BdX.
      pose proof (u64arr_bound _ _ _ _ YL) as BdY. rewrite Hyl in BdY.
      pose proof (rw_cells_bound _ _ _ _ XC) as BLX. cbn [cells_size csize Nat.add] in BLX.
      pose proof (rw_cells_bound _ _ _ _ YC) as BLY. cbn [cells_size csize Nat.add] in BLY.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc; [exfalso; lia|].
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      destruct (nth_error xs (Z.to_nat (idx - 1))) as [wx|] eqn:Hnx. 2:{ exfalso. apply nth_error_None in Hnx. lia. }
      destruct (nth_error ys (Z.to_nat (idx - 1))) as [wy|] eqn:Hny. 2:{ exfalso. apply nth_error_None in Hny. lia. }
      pose proof (u64arr_read USEGS m X xs (idx - 1) wx _ XL Hnx ltac:(lia) eq_refl) as RDX.
      replace (wa (X + 8 * (idx - 1))) with (Z_to_bv 64 (X + (8 * idx - 8))) in RDX by (unfold wa; f_equal; lia).
      step. (* [comment removed for export] *)
      clear RDX.
      pose proof (u64arr_read USEGS m Y ys (idx - 1) wy _ YL Hny ltac:(lia) eq_refl) as RDY.
      replace (wa (Y + 8 * (idx - 1))) with (Z_to_bv 64 (Y + (8 * idx - 8))) in RDY by (unfold wa; f_equal; lia).
      step. (* [comment removed for export] *)
      clear RDY.
      step. (* [comment removed for export] *)
      if_cases Hgt.
      { step. (* [comment removed for export] *) unfold compare_post. finish. all: first [apply munch_refl | apply wmono_refl | exact I]. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hge.
      + replace (8 * idx - 8 + -8)%Z with (8 * (idx - 1) - 8)%Z by lia.
        eapply (IH (idx - 1)%Z); lia.
      + step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        unfold compare_post. finish. all: first [apply munch_refl | apply wmono_refl | exact I].
  Qed.
End Loop.

Lemma compare_spec : compare_stmt.
Proof.
  unfold compare_stmt. intros until ylen. intros XL Hxl XC XLEN YL Hyl YC YLEN.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite zx16_lit by lia.
  step. (* [comment removed for export] *)
  rewrite zx16_lit by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases H1.
  { step. (* [comment removed for export] *) unfold compare_post. finish. all: first [apply munch_refl | apply wmono_refl | exact I]. }
  cond_cleanup H1.
  step. (* [comment removed for export] *)
  if_cases H2.
  { step. (* [comment removed for export] *) step. (* [comment removed for export] *) unfold compare_post. finish. all: first [apply munch_refl | apply wmono_refl | exact I]. }
  cond_cleanup H2.
  assert (EQL : ylen = xlen) by lia. rewrite EQL in YC.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite (unsigned_lit xlen) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  replace (xlen * 2 ^ 3 + -8)%Z with (8 * xlen - 8)%Z by lia.
  eapply (cmp_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 a0 a1 F fc m xs ys xlen
            Hxl Hyl XLEN XL YL XC YC (Z.to_nat xlen) xlen); lia.
Qed.
End U_compare.


Module U_normalize.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac U_normalize_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Loop.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
  Variables (vec : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (len : Z).
  Hypothesis Hlen : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.

  Notation A := (bv_unsigned vec).
  Notation POST := (normalize_post ra sp gp tp t0 t1 t2 s0 s1 vec a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ws len m0).
  Notation NOTA := (Z_to_bv 64 (Z.lxor A 18446744073709551615)).

  (* [comment removed for export] *)
  Definition loop_ok (k : nat) : Prop :=
    forall (l : Z) (a5 : word) (m : word -> option byte),
      (Z.to_nat l = k)%nat -> (1 <= l <= len)%Z ->
      u64arr USEGS m A ws ->
      rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 l)] ->
      norm_len ws (Z.to_nat len) = norm_len ws (Z.to_nat l) ->
      munch (normalize_W A) m0 m -> wmono USEGS m0 m ->
      evt USEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 vec (Z_to_bv 64 len) NOTA (Z_to_bv 64 64) (Z_to_bv 64 l) a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x276c0) fc None m (seg_rom USEGS)).

  #[using="Hlen LEN"] Lemma norm_loop : forall k, loop_ok k.
  Proof. LiaFast.lf_pins (fun (Hlen LEN : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; unfold loop_ok; intros l a5 m Hk Hl LIMBS LC NL MU WM.
    { exfalso. lia. }
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bd. rewrite Hlen in Bd.
    pose proof (rw_cells_bound _ _ _ _ LC) as BL. cbn [cells_size csize Nat.add] in BL.
    cbv delta [normalize_W] in MU.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit l) by lia. rewrite shl48_shr48 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (l + -1)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    replace ((l + -1) * 2 ^ 3)%Z with (8 * (l - 1))%Z by lia.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    destruct (nth_error ws (Z.to_nat (l - 1))) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : nth (Z.to_nat (l - 1)) ws w0 = w) by (apply nth_error_nth; exact Hn).
    pose proof (u64arr_read USEGS m A ws (l - 1) w (Z_to_bv 64 (A + 8 * (l - 1))) LIMBS Hn ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    assert (Hk1 : Z.to_nat l = S (Z.to_nat (l - 1))) by lia.
    rewrite Hk1 in NL. cbn [norm_len] in NL. unfold limbZ in NL. rewrite Hw in NL.
    step. (* [comment removed for export] *)
    if_cases Hnz.
    - cond_cleanup Hnz.
      replace (bv_unsigned w =? 0)%Z with false in NL by (symmetry; apply Z.eqb_neq; lia).
      step. (* [comment removed for export] *)
      unfold normalize_post. rewrite NL. replace (Z.of_nat (S (Z.to_nat (l - 1)))) with l by lia.
      finish.
    - cond_cleanup Hnz.
      replace (bv_unsigned w =? 0)%Z with true in NL by (symmetry; apply Z.eqb_eq; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc.
      + cond_cleanup Hc. rewrite Z.shiftl_mul_pow2 in Hc by lia. rewrite Z.mod_small in Hc by lia.
        replace (l + -1)%Z with (l - 1)%Z by lia.
        eapply (IH (l - 1)%Z); try eassumption; try lia.
      + cond_cleanup Hc. rewrite Z.shiftl_mul_pow2 in Hc by lia. rewrite Z.mod_small in Hc by lia.
        assert (Hl1 : l = 1%Z) by lia.
        step. (* [comment removed for export] *)
        unfold normalize_post. rewrite NL. subst l. change (Z.to_nat (1 - 1)) with 0%nat. cbn [norm_len Z.of_nat].
        change (1 + -1)%Z with 0%Z.
        finish.
  Qed.
End Loop.

Lemma normalize_spec : normalize_stmt.
Proof.
  unfold normalize_stmt. intros until len. intros LIMBS Hlen LC LEN.
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  pose proof (munch_refl (normalize_W (bv_unsigned a0)) m) as MU.
  pose proof (wmono_refl USEGS m) as WM.
  step. (* [comment removed for export] *)
  rewrite zx16_lit by lia.
  step. (* [comment removed for export] *)
  if_cases Hz.
  { cond_cleanup Hz. step. (* [comment removed for export] *)
    unfold normalize_post. subst len. change (Z.to_nat 0) with 0%nat. cbn [norm_len Z.of_nat]. finish. }
  cond_cleanup Hz.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  eapply (norm_loop ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 F fc m ws len
            Hlen ltac:(lia) (Z.to_nat len) len); try eassumption; try lia.
Qed.
End U_normalize.


Module U_memmove_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition memmove_entry : Z := 0x604ac.

Definition memmove_post
    (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (n : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + n)]%Z m m'
    /\ wmono USEGS m m'
    /\ u8arr USEGS m' (bv_unsigned a0) bs.

Definition memmove_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs old : list byte),
    bytes_at USEGS m (bv_unsigned a1) bs ->
    u8arr USEGS m (bv_unsigned a0) old ->
    length old = length bs ->
    Z.of_nat (length bs) = bv_unsigned a2 ->
    (bv_unsigned a0 mod 8 = 0)%Z -> (bv_unsigned a1 mod 8 = 0)%Z -> (bv_unsigned a2 mod 8 = 0)%Z ->
    (bv_unsigned a2 < 2^63)%Z ->
    (bv_unsigned a0 + bv_unsigned a2 < 2^64)%Z ->
    (bv_unsigned a1 + bv_unsigned a2 < 2^64)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt USEGS (memmove_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a2) bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x604ac) fc None m (seg_rom USEGS)).
End U_memmove_stmt.

Module U_memmove.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memcpy_stmt U_memcpy.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memcpy_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memcpy OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_lib_closed.U_memmove_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma mm_disj : forall D S N, (0 <= D -> 0 <= S -> 0 <= N < 2^63 -> D + N < 2^64 -> S + N < 2^64 -> D <> S ->
  (S - (N + D)) mod 2^64 <= (0 - (Z.shiftl N 1) mod 2^64) mod 2^64 -> D + N <= S \/ S + N <= D)%Z.
Proof.
  intros D S N HD HS HN H1 H2 H3 H. rewrite Z.shiftl_mul_pow2 in H by lia. change (2^1)%Z with 2%Z in H.
  Z.div_mod_to_equations. lia.
Qed.

Lemma land7_lxor_aligned : forall S D, (0 <= S < 2^64 -> 0 <= D < 2^64 -> S mod 8 = 0 -> D mod 8 = 0 ->
  Z.land (bv_unsigned (Z_to_bv 64 (Z.lxor S D))) 7 = 0)%Z.
Proof.
  intros S D HS HD H1 H2. rewrite unsigned_lit by (apply Z_lxor_range; lia).
  assert (E : forall x, (0 <= x -> x mod 8 = 0 -> forall i, 0 <= i < 3 -> Z.testbit x i = false)%Z).
  { intros x Hx Hm i Hi. replace x with ((x / 8) * 2^3)%Z by lia. apply Z.mul_pow2_bits_low. lia. }
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 3).
  - rewrite (E S), (E D) by lia. reflexivity.
  - replace (Z.testbit 7 i) with false; [apply andb_false_r|]. symmetry. change 7%Z with (Z.ones 3). apply Z.ones_spec_high. lia.
Qed.

Lemma land7_aligned : forall D, (0 <= D -> D mod 8 = 0 -> Z.land D 7 = 0)%Z.
Proof. intros D HD H. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

(* [comment removed for export] *)
Lemma split8_front : forall {A} (l : list A), (8 <= length l)%nat ->
  exists b0 b1 b2 b3 b4 b5 b6 b7 l', l = [b0;b1;b2;b3;b4;b5;b6;b7] ++ l'.
Proof.
  intros A l H. destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 l']]]]]]]]; cbn in H; try lia.
  exists b0, b1, b2, b3, b4, b5, b6, b7, l'. reflexivity.
Qed.

Lemma split8_back : forall {A} (l : list A), (8 <= length l)%nat ->
  exists l' b0 b1 b2 b3 b4 b5 b6 b7, l = l' ++ [b0;b1;b2;b3;b4;b5;b6;b7] /\ length l' = (length l - 8)%nat.
Proof.
  intros A l H.
  pose proof (firstn_skipn (length l - 8) l) as E.
  assert (L : length (skipn (length l - 8) l) = 8%nat) by (rewrite skipn_length; lia).
  destruct (skipn (length l - 8) l) as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|x l']]]]]]]]]; cbn in L; try lia.
  exists (firstn (length l - 8) l), b0, b1, b2, b3, b4, b5, b6, b7. split; [symmetry; exact E|].
  rewrite firstn_length. lia.
Qed.

Section Proof.
  Let memcpy_spec : memcpy_stmt := U_memcpy.memcpy_spec.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte).
  Notation D := (bv_unsigned a0). Notation S := (bv_unsigned a1). Notation N := (bv_unsigned a2).
  Notation POST := (memmove_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc N bs m).
  Hypothesis LBS : Z.of_nat (length bs) = N.
  Hypothesis BD : (0 <= D /\ D + N < 2^64)%Z.
  Hypothesis BS : (0 <= S /\ S + N < 2^64)%Z.
  Hypothesis AL2 : (N mod 8 = 0)%Z.

  (* [comment removed for export] *)
  #[using="LBS BD BS AL2"] Lemma loopF : forall (k : nat) (K : Z) (mq : word -> option byte) (done todo rest : list byte) (a5 a6 a7 : word),
    (Z.to_nat (N - K) <= k)%nat ->
    u8arr USEGS mq D done -> u8arr USEGS mq (D + K) todo -> bytes_at USEGS mq (S + K) rest ->
    Z.of_nat (length done) = K -> length todo = length rest -> done ++ rest = bs ->
    munch [(D, D + N)]%Z m mq -> wmono USEGS m mq ->
    (D + 8 <= S)%Z -> (0 <= K)%Z -> (K + 8 <= N)%Z -> (K mod 8 = 0)%Z ->
    forall (w2 w3 w4 : word), w2 = Z_to_bv 64 (N - K) -> w3 = Z_to_bv 64 (D + K) -> w4 = Z_to_bv 64 (S + K) ->
    evt USEGS POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 7) w2 w3 w4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x6060c) fc None mq (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (LBS BD BS AL2 : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; intros K mq done todo rest a5 a6 a7 Hk DONE TODO SRCR Ld Lt Hbs MU WM DS K0 K8 KAL w2 w3 w4 -> -> ->; [lia|].
    pose proof (bytes_at_bound _ _ _ _ SRCR) as Br.
    assert (Lr : (8 <= length rest)%nat).
    { apply (f_equal (@length byte)) in Hbs. rewrite app_length in Hbs. lia. }
    destruct (split8_front rest Lr) as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & rest' & ->).
    destruct (split8_front todo ltac:(lia)) as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & todo' & ->).
    (* [comment removed for export] *)
    pose proof (bytes_at_read USEGS mq (S + K) _ 0 8 SRCR ltac:(lia) ltac:(cbn; lia)) as RD.
    change (firstn 8 (skipn (Z.to_nat 0) ([b0; b1; b2; b3; b4; b5; b6; b7] ++ rest'))) with [b0; b1; b2; b3; b4; b5; b6; b7] in RD.
    rewrite Z.add_0_r in RD.
    rewrite <- (le8_le_bytes_to_word8 b0 b1 b2 b3 b4 b5 b6 b7) in RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (proj1 (u8arr_app USEGS mq (D + K) [c0; c1; c2; c3; c4; c5; c6; c7] todo')) in TODO.
    destruct TODO as [HEAD TODO]. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in TODO.
    pose proof (u8arr_store_ok USEGS mq (D + K) _ 0 _ HEAD ltac:(cbn; lia) eq_refl) as SOK0.
    pose proof (wr_at_store_ok USEGS mq (D + K) 8 0 8 (proj2 HEAD) ltac:(lia) ltac:(lia)) as SOK.
    clear SOK0. rewrite Z.add_0_r in SOK.
    step. (* [comment removed for export] *)
    rewrite le8_le_bytes_to_word8.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mq ?a ?l8) _) =>
      change (write_to_mem mq a l8) with (write_to_mem mq (wa (D + K)) l8);
      pose proof (u8arr_write_all USEGS mq (D + K) _ l8 HEAD eq_refl) as HEAD';
      apply (u8arr_frame USEGS mq D done (D + K) l8) in DONE; [| lia | cbn; lia | cbn; lia];
      apply (u8arr_frame USEGS mq _ todo' (D + K) l8) in TODO; [| lia | cbn; lia | cbn; lia];
      apply bytes_at_app in SRCR; destruct SRCR as [_ SRCR]; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in SRCR;
      apply (bytes_at_write_other USEGS mq (D + K) l8) in SRCR; [| lia | cbn; lia | cbn; lia];
      apply (munch_write _ m mq (D + K) l8) in MU; [| lia | cbn; lia | cbn; lia];
      apply (wmono_write USEGS m mq (wa (D + K)) l8) in WM;
      remember (write_to_mem mq (wa (D + K)) l8) as mq' eqn:Heqm; clear Heqm HEAD SOK; try clear mq
    end.
    (* [comment removed for export] *)
    rewrite <- Ld in HEAD'.
    pose proof (proj2 (u8arr_app USEGS mq' D done [b0; b1; b2; b3; b4; b5; b6; b7]) (conj DONE HEAD')) as DONE'.
    clear DONE HEAD'. rename DONE' into DONE.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hc.
    - cond_cleanup Hc.
      replace (N - K + -8)%Z with (N - (K + 8))%Z by lia.
      replace (D + K + 8)%Z with (D + (K + 8))%Z by lia.
      replace (S + K + 8)%Z with (S + (K + 8))%Z by lia.
      eapply (IH (K + 8)%Z mq' (done ++ [b0; b1; b2; b3; b4; b5; b6; b7]) todo' rest'); try lia; try reflexivity.
      all: try (Z.div_mod_to_equations; lia).
      + exact DONE.
      + replace (D + (K + 8))%Z with (D + K + Z.of_nat 8)%Z by lia. exact TODO.
      + replace (S + (K + 8))%Z with (S + K + Z.of_nat 8)%Z by lia. exact SRCR.
      + rewrite app_length. cbn [length]. lia.
      + cbn in Lt. lia.
      + rewrite <- app_assoc. exact Hbs.
      + exact MU.
      + exact WM.
    - (* [comment removed for export] *)
      cond_cleanup Hc.
      assert (K8N : (K + 8 = N)%Z) by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz. 2:{ cond_cleanup Hz. exfalso; lia. }
      step. (* [comment removed for export] *)
      assert (Hr : rest' = []).
      { apply (f_equal (@length byte)) in Hbs. rewrite !app_length in Hbs. cbn [length] in Hbs.
        destruct rest'; [reflexivity| cbn [length] in Hbs; lia]. }
      subst rest'. rewrite app_nil_r in Hbs. subst bs.
      apply evt_done. unfold memmove_post.
      do 15 eexists. split; [reflexivity|].
      split. { exact MU. }
      split. { exact WM. }
      exact DONE.
  Qed.


  (* [comment removed for export] *)
  #[using="LBS BD AL2"] Lemma loopB : forall (k : nat) (rem : Z) (mq : word -> option byte) (todo done rest : list byte) (a3 a7 : word),
    (Z.to_nat rem <= k)%nat ->
    u8arr USEGS mq D todo -> u8arr USEGS mq (D + rem) done -> bytes_at USEGS mq S rest ->
    Z.of_nat (length rest) = rem -> length todo = length rest -> rest ++ done = bs ->
    munch [(D, D + N)]%Z m mq -> wmono USEGS m mq ->
    (S + 8 <= D)%Z -> (8 <= rem <= N)%Z -> (rem mod 8 = 0)%Z ->
    forall (w2 : word), w2 = Z_to_bv 64 rem ->
    evt USEGS POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 w2 a3 (Z_to_bv 64 (S + -8)) (Z_to_bv 64 (D + -8)) (Z_to_bv 64 7) a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x605d8) fc None mq (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (LBS BD AL2 : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; intros rem mq todo done rest a3 a7 Hk TODO DONE SRCR Lr Lt Hbs MU WM DS R8 RAL w2 ->; [lia|].
    pose proof (bytes_at_bound _ _ _ _ SRCR) as Br.
    destruct (split8_back rest ltac:(lia)) as (rest' & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & -> & Lr').
    destruct (split8_back todo ltac:(lia)) as (todo' & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & -> & Lt').
    rewrite ?app_length in Lr'. rewrite ?app_length in Lt'. rewrite ?app_length in Lr. rewrite ?app_length in Lt. rewrite ?app_length in Lt.
    cbn [length] in Lr', Lt', Lr, Lt.
    (* [comment removed for export] *)
    pose proof (proj1 (bytes_at_app USEGS mq S rest' [b0; b1; b2; b3; b4; b5; b6; b7]) SRCR) as [SRCR' RDW].
    pose proof (bytes_at_read USEGS mq (S + Z.of_nat (length rest')) _ 0 8 RDW ltac:(lia) ltac:(cbn; lia)) as RD.
    change (firstn 8 (skipn (Z.to_nat 0) [b0; b1; b2; b3; b4; b5; b6; b7])) with [b0; b1; b2; b3; b4; b5; b6; b7] in RD.
    rewrite Z.add_0_r in RD.
    rewrite <- (le8_le_bytes_to_word8 b0 b1 b2 b3 b4 b5 b6 b7) in RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    clear RD RDW.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (proj1 (u8arr_app USEGS mq D todo' [c0; c1; c2; c3; c4; c5; c6; c7])) in TODO.
    destruct TODO as [TODO HEAD].
    pose proof (wr_at_store_ok USEGS mq (D + Z.of_nat (length todo')) 8 0 8 (proj2 HEAD) ltac:(lia) ltac:(lia)) as SOK.
    rewrite Z.add_0_r in SOK.
    assert (LT : Z.of_nat (length todo') = (rem - 8)%Z) by lia.
    replace (D + Z.of_nat (length todo'))%Z with (D + -8 + rem)%Z in SOK by lia.
    step. (* [comment removed for export] *)
    rewrite le8_le_bytes_to_word8.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mq ?a ?l8) _) =>
      replace (write_to_mem mq a l8) with (write_to_mem mq (wa (D + Z.of_nat (length todo'))) l8) by (f_equal; unfold wa; f_equal; lia);
      pose proof (u8arr_write_all USEGS mq (D + Z.of_nat (length todo')) _ l8 HEAD eq_refl) as HEAD';
      apply (u8arr_frame USEGS mq D todo' (D + Z.of_nat (length todo')) l8) in TODO; [| lia | cbn; lia | cbn; lia];
      apply (u8arr_frame USEGS mq _ done (D + Z.of_nat (length todo')) l8) in DONE; [| lia | cbn; lia | cbn; lia];
      apply (bytes_at_write_other USEGS mq (D + Z.of_nat (length todo')) l8) in SRCR'; [| lia | cbn; lia | cbn; lia];
      apply (munch_write _ m mq (D + Z.of_nat (length todo')) l8) in MU; [| lia | cbn; lia | cbn; lia];
      apply (wmono_write USEGS m mq (wa (D + Z.of_nat (length todo'))) l8) in WM;
      clear SRCR; remember (write_to_mem mq (wa (D + Z.of_nat (length todo'))) l8) as mq' eqn:Heqm; clear Heqm HEAD SOK; try clear mq
    end.
    (* [comment removed for export] *)
    replace (D + rem)%Z with (D + Z.of_nat (length todo') + Z.of_nat (length [b0; b1; b2; b3; b4; b5; b6; b7]))%Z in DONE by (cbn [length]; lia).
    pose proof (proj2 (u8arr_app USEGS mq' _ [b0; b1; b2; b3; b4; b5; b6; b7] done) (conj HEAD' DONE)) as DONE'.
    clear DONE HEAD'. rename DONE' into DONE.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hc.
    - cond_cleanup Hc.
      replace (rem + -8)%Z with (rem - 8)%Z by lia.
      eapply (IH (rem - 8)%Z mq' todo' ([b0; b1; b2; b3; b4; b5; b6; b7] ++ done) rest'); try lia; try reflexivity.
      all: try (Z.div_mod_to_equations; lia).
      + exact TODO.
      + replace (D + (rem - 8))%Z with (D + Z.of_nat (length todo'))%Z by lia. exact DONE.
      + exact SRCR'.
      + rewrite <- app_assoc in Hbs. exact Hbs.
      + exact MU.
      + exact WM.
    - cond_cleanup Hc.
      assert (R8e : rem = 8%Z) by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz. 2:{ cond_cleanup Hz. exfalso; lia. }
      step. (* [comment removed for export] *)
      assert (Hr : rest' = []) by (destruct rest'; [reflexivity| cbn [length] in Lr; lia]).
      assert (Ht : todo' = []) by (destruct todo'; [reflexivity| cbn [length] in LT; lia]).
      subst rest' todo'. cbn [app] in Hbs. subst bs.
      cbn [length] in DONE. change (Z.of_nat 0) with 0%Z in DONE. rewrite Z.add_0_r in DONE.
      apply evt_done. unfold memmove_post.
      do 15 eexists. split; [reflexivity|].
      split. { exact MU. }
      split. { exact WM. }
      exact DONE.
  Qed.

  #[using="memcpy_spec LBS BD BS AL2"] Lemma memmove_main : forall (a3 a4 a5 a6 a7 : word) (old : list byte),
    bytes_at USEGS m S bs -> u8arr USEGS m D old -> length old = length bs ->
    (D mod 8 = 0)%Z -> (S mod 8 = 0)%Z -> (N < 2^63)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
    evt USEGS POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x604ac) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (memcpy_spec LBS BD BS AL2 : LiaFast.U) => LiaFast.u0).
    intros a3 a4 a5 a6 a7 old SRC DST LEN AL0 AL1 N63 RA.
    pose proof (munch_refl [(D, D + N)]%Z m) as MU. pose proof (wmono_refl USEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2.
    step. (* [comment removed for export] *)
    if_cases Heq.
    { (* [comment removed for export] *)
      cond_cleanup Heq. step.
      apply evt_done. unfold memmove_post. do 15 eexists. split; [reflexivity|].
      split. { exact MU. } split. { exact WM. }
      destruct DST as [_ W]. rewrite LEN, LBS in W. split; [rewrite Heq; exact SRC | rewrite LBS; exact W]. }
    cond_cleanup Heq.
    step. step. step. step.
    step. (* [comment removed for export] *)
    if_cases Hmc.
    { cond_cleanup Hmc.
      pose proof (mm_disj D S N ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Heq Hmc) as DISJ.
      clear Hmc.
      step. (* [comment removed for export] *)
      call memcpy_spec.
      1:{ exact SRC. } 1:{ exact DST. } 1:{ exact LEN. } 1:{ exact LBS. } 1:{ exact DISJ. } 1:{ lia. } 1:{ lia. } 1:{ exact RA. }
      apply evt_done. unfold memmove_post. do 15 eexists. split; [reflexivity|].
      split. { exact MU. } split. { exact WM. } assumption. }
    clear Hmc.
    step. step. (* [comment removed for export] *)
    rewrite (land7_lxor_aligned S D) by lia.
    step. (* [comment removed for export] *)
    if_cases Hdir.
    - (* [comment removed for export] *)
      cond_cleanup Hdir.
      step. (* [comment removed for export] *)
      if_cases Hz; [clear Hz| cond_cleanup Hz; exfalso; lia].
      step. step. (* [comment removed for export] *)
      rewrite (unsigned_lit (D + N)) by lia. rewrite (land7_aligned (D + N)) by (try lia; Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      if_cases Hz; [clear Hz| cond_cleanup Hz; exfalso; lia].
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H8.
      + cond_cleanup H8. assert (N0 : N = 0%Z) by (Z.div_mod_to_equations; lia).
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hz; [clear Hz| cond_cleanup Hz; exfalso; lia].
        step. (* [comment removed for export] *)
        assert (Hb : bs = []) by (destruct bs; [reflexivity| cbn [length] in LBS; lia]).
        assert (Ho : old = []) by (destruct old; [reflexivity| rewrite Hb in LEN; cbn [length] in LEN; lia]).
        subst old.
        apply evt_done. unfold memmove_post. do 15 eexists. split; [reflexivity|].
        split. { exact MU. } split. { exact WM. } rewrite Hb. exact DST.
      + cond_cleanup H8.
        step. step. step. (* [comment removed for export] *)
        eapply (loopB (Z.to_nat N) N m old [] bs); try eassumption; try lia.
        all: try (symmetry; apply Z_to_bv_bv_unsigned).
        all: try (rewrite app_nil_r; reflexivity).
        split. { apply bytes_at_nil. lia. } { split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. }
    - (* [comment removed for export] *)
      cond_cleanup Hdir.
      step. (* [comment removed for export] *)
      if_cases Hz; [clear Hz| cond_cleanup Hz; exfalso; lia].
      step. (* [comment removed for export] *)
      rewrite (land7_aligned D) by lia.
      step. (* [comment removed for export] *)
      if_cases Hz; [clear Hz| cond_cleanup Hz; exfalso; lia].
      step. step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H8.
      + cond_cleanup H8. assert (N0 : N = 0%Z) by (Z.div_mod_to_equations; lia).
        step. (* [comment removed for export] *)
        if_cases Hz; [clear Hz| cond_cleanup Hz; exfalso; lia].
        step. (* [comment removed for export] *)
        assert (Hb : bs = []) by (destruct bs; [reflexivity| cbn [length] in LBS; lia]).
        assert (Ho : old = []) by (destruct old; [reflexivity| rewrite Hb in LEN; cbn [length] in LEN; lia]).
        subst old.
        apply evt_done. unfold memmove_post. do 15 eexists. split; [reflexivity|].
        split. { exact MU. } split. { exact WM. } rewrite Hb. exact DST.
      + cond_cleanup H8.
        step. (* [comment removed for export] *)
        eapply (loopF (Z.to_nat N) 0%Z m [] old bs); try lia.
        all: try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).
        all: try (rewrite Z.add_0_r; eassumption).
        all: try eassumption. all: try reflexivity.
        (* [comment removed for export] *)
        split. { apply bytes_at_nil. lia. } { split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. }
  Qed.
End Proof.

Lemma memmove_spec : memmove_stmt.
Proof.
  unfold memmove_stmt. intros until old. intros SRC DST LEN N AL0 AL1 AL2 N63 NW0 NW1 RA.
  pose proof (bytes_at_bound _ _ _ _ SRC) as Bs. pose proof (u8arr_bound _ _ _ _ DST) as Bd. rewrite LEN in Bd.
  eapply memmove_main; try eassumption; lia.
Qed.
End U_memmove.

Module U_copy_impl.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl Ubsan_chk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_long_mul.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.Ubsan_chk OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_lib_closed.U_memmove_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_lib_closed.U_memmove OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul.U_copy_impl_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma copy_impl_spec : copy_impl_stmt.
Proof.
  unfold copy_impl_stmt. intros until old. intros ST Ha1 Hn Hn8 SRC Lbs DST Lold A08 D8 A0p Dp Dn RA SEPD SEPS.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + (bv_unsigned a1 - bv_unsigned a0))]%Z m) as MU.
  replace (bv_unsigned a1 - bv_unsigned a0)%Z with n in MU by lia.
  pose proof (wmono_refl USEGS m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0.
  pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2.
  assert (SPB : (0 <= bv_unsigned sp - 32)%Z) by (destruct ST as (? & ? & ?); lia).
  carve_frame 32%nat ST.
  do 5 step. (* [comment removed for export] *)
  step. step. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  replace (bv_unsigned a1 - bv_unsigned a0)%Z with n by lia.
  step. (* [comment removed for export] *)
  if_cases Hz.
  - (* [comment removed for export] *)
    cond_cleanup Hz.
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    kill_check.
    step. step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    kill_check.
    step. (* [comment removed for export] *)
    do 6 step.
    release_frame FR ST (bv_unsigned sp).
    unfold copy_impl_post. replace (bv_unsigned a1 - bv_unsigned a0)%Z with n by lia.
    replace (n + bv_unsigned a2)%Z with (bv_unsigned a2 + n)%Z by lia.
    finish. all: try eassumption. all: try lia.
    assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in Lbs; lia]).
    assert (old = []) as -> by (destruct old; [reflexivity| cbn in Lold; lia]).
    all: try exact DST. all: try assumption.
    all: replace (bv_unsigned a0) with (bv_unsigned a1) by lia; rewrite (Z_to_bv_bv_unsigned a1); reflexivity.
  - cond_cleanup Hz.
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite (land7_lor_aligned (bv_unsigned a2) (bv_unsigned a0)) by lia.
    step. (* [comment removed for export] *)
    kill_check.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit n ltac:(lia)) as ULn.
    step. (* [comment removed for export] *)
    call memmove_spec.
    1:{ exact SRC. } 1:{ exact DST. } 1:{ exact Lold. }
    1:{ rewrite ULn. exact Lbs. }
    1:{ exact D8. } 1:{ exact A08. } 1:{ rewrite ULn. exact Hn8. }
    1:{ rewrite ULn. lia. } 1:{ rewrite ULn. lia. } 1:{ rewrite ULn. lia. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    rewrite ?ULn in *.
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    kill_check.
    step. step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    kill_check.
    step. (* [comment removed for export] *)
    do 6 step.
    match goal with H : stk USEGS _ _ _ |- _ => rename H into ST' end.
    release_frame FR ST' (bv_unsigned sp).
    unfold copy_impl_post. replace (bv_unsigned a1 - bv_unsigned a0)%Z with n by lia.
    replace (n + bv_unsigned a2)%Z with (bv_unsigned a2 + n)%Z by lia.
    finish. all: try eassumption. all: try lia.
    all: try (split; assumption).
Qed.
End U_copy_impl.

Module U_copy_bwd_impl.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl Ubsan_chk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_ciir_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.Ubsan_chk OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_lib_closed.U_memmove_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_lib_closed.U_memmove OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_ciir_stmt.U_copy_bwd_impl_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Lemma copy_bwd_impl_spec : copy_bwd_impl_stmt.
Proof.
  unfold copy_bwd_impl_stmt. intros until old. intros ST Ha1 Ha2 Hn Hn8 SRC Lbs DST Lold A08 D8 A0p Dp RA SEPD SEPS.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0), bv_unsigned a2)]%Z m) as MU.
  replace (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))%Z with D in MU by lia.
  pose proof (wmono_refl USEGS m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0.
  pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2.
  pose proof (bytes_at_bound _ _ _ _ SRC) as Bs. destruct DST as [DB DW]. pose proof (bytes_at_bound _ _ _ _ DB) as Bd.
  assert (DST : u8arr USEGS m D old) by (split; assumption). clear DB DW.
  rewrite Lold in Bd.
  carve_frame 32%nat ST.
  do 4 step. (* [comment removed for export] *)
  step. step. step. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  replace (bv_unsigned a1 - bv_unsigned a0)%Z with n by lia.
  zstep. (* [comment removed for export] *)
  replace (bv_unsigned a2 - n)%Z with D by lia.
  step. step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  kill_check.
  zstep. (* [comment removed for export] *)
  rewrite lm_signed_lit by lia. rewrite (Z.shiftr_div_pow2 n 3) by lia. change (2 ^ 3)%Z with 8%Z.
  step. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  assert (Hq : (0 <= n / 8 < 2 ^ 37)%Z). { split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia. }
  rewrite (Z.shiftr_div_pow2 _ 61) by lia. rewrite (Z.div_small (n / 8 + 1152921504606846975) (2 ^ 61)) by lia.
  step. (* [comment removed for export] *)
  kill_check.
  step. (* [comment removed for export] *)
  kill_check.
  zstep. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned a2 + ?x)%Z] =>
    replace (Z_to_bv 64 (bv_unsigned a2 + x)%Z) with (Z_to_bv 64 D)
      by (apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3)%Z with 8%Z; Z.div_mod_to_equations; lia) end.
  step. (* [comment removed for export] *)
  if_cases Hz.
  - (* [comment removed for export] *)
    cond_cleanup Hz.
    step. step. (* [comment removed for export] *)
    do 5 step.
    release_frame FR ST (bv_unsigned sp).
    unfold copy_bwd_impl_post. replace (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))%Z with D by lia.
    finish.
    all: try eassumption. all: try lia.
    (* [comment removed for export] *)
    assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in Lbs; lia]).
    assert (old = []) as -> by (destruct old; [reflexivity| cbn in Lold; lia]). all: try exact DST. all: try assumption.
  - cond_cleanup Hz.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite (land7_lor_aligned D (bv_unsigned a0)) by lia.
    step. (* [comment removed for export] *)
    kill_check.
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit D ltac:(lia)) as ULD. pose proof (unsigned_lit n ltac:(lia)) as ULn.
    step. (* [comment removed for export] *)
    call memmove_spec.
    1:{ exact SRC. }
    1:{ eapply u8arr_at_eq; [exact DST| rewrite unsigned_lit by lia; lia]. }
    1:{ exact Lold. }
    1:{ rewrite ULn. exact Lbs. }
    1:{ rewrite ULD. exact D8. } 1:{ exact A08. } 1:{ rewrite ULn. exact Hn8. }
    1:{ rewrite ULn. lia. } 1:{ rewrite ULD, ULn. lia. } 1:{ rewrite ULn. lia. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    rewrite ?ULD, ?ULn in *.
    step. step. (* [comment removed for export] *)
    do 5 step.
    match goal with H : stk USEGS _ _ _ |- _ => rename H into ST' end.
    release_frame FR ST' (bv_unsigned sp).
    unfold copy_bwd_impl_post. replace (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))%Z with D by lia.
    finish.
    all: try eassumption. all: try lia.
    all: split; assumption.
Qed.
End U_copy_bwd_impl.

Module U_copy_bwd.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl Ubsan_chk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_ciir_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_ciir_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.Ubsan_chk OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_ciir_stmt.U_copy_bwd_impl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_lib_closed.U_copy_bwd_impl OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_ciir_stmt.U_copy_bwd_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma copy_bwd_spec : copy_bwd_stmt.
Proof.
  unfold copy_bwd_stmt. intros until old. intros ST Ha1 Ha2 Hn Hn8 SRC Lbs DST Lold A08 D8 A0p Dp RA SEPD SEPS.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0), bv_unsigned a2)]%Z m) as MU.
  replace (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))%Z with D in MU by lia.
  pose proof (wmono_refl USEGS m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0.
  pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2.
  assert (SPB : (0 <= bv_unsigned sp - 64)%Z) by (destruct ST as (? & ? & ?); lia).
  carve_frame 32%nat ST.
  do 4 step. (* [comment removed for export] *)
  step. step. (* [comment removed for export] *)
  pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as ULs.
  step. (* [comment removed for export] *)
  call copy_bwd_impl_spec.
  1:{ rewrite ULs. replace (bv_unsigned sp + -32 - 32)%Z with (bv_unsigned sp - 64)%Z by lia. exact ST. }
  1:{ exact Ha1. } 1:{ exact Ha2. } 1:{ exact Hn. } 1:{ exact Hn8. } 1:{ exact SRC. } 1:{ exact Lbs. } 1:{ exact DST. } 1:{ exact Lold. }
  1:{ exact A08. } 1:{ exact D8. } 1:{ exact A0p. } 1:{ exact Dp. }
  1:{ rewrite unsigned_lit by lia. reflexivity. }
  1:{ rewrite ULs. lia. } 1:{ rewrite ULs. lia. }
  rewrite ?ULs in *.
  replace (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))%Z with D in * by lia.
  step. step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  kill_check.
  zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  kill_check.
  step. step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  kill_check.
  zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hc.
  { exfalso. cond_cleanup Hc. replace (bv_unsigned a2) with (D + n)%Z in Hc by lia.
    destruct (Z.eq_dec n 0) as [N0|N1].
    - rewrite N0, Z.add_0_r, Z.sub_diag, Z.mod_0_l, Z.lxor_0_l in Hc by lia. decide_ltb_in Hc. discriminate.
    - replace ((D - (D + n)) mod 18446744073709551616)%Z with (18446744073709551616 - n)%Z in Hc
        by (symmetry; symmetry; apply (Z.mod_unique_pos _ _ (-1)); lia).
      rewrite lxor_high' in Hc by lia. decide_ltb_in Hc. discriminate. }
  clear Hc.
  do 5 step. (* [comment removed for export] *)
  match goal with H : stk USEGS _ _ _ |- _ => rename H into ST' end.
  replace (bv_unsigned sp + -32 - 32)%Z with (bv_unsigned sp - 64)%Z in ST' by lia.
  release_frame FR ST' (bv_unsigned sp).
  unfold copy_bwd_post. replace (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))%Z with D by lia.
  finish.
  all: try eassumption. all: try lia.
  all: try (split; assumption).
Qed.
End U_copy_bwd.

Module U_shl_limbs.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs.StoreFast.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl Ubsan_chk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_ciir_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_shl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.Ubsan_chk OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_ciir_stmt.U_copy_bwd_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_lib_closed.U_copy_bwd OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_shl.U_shl_limbs_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Local Ltac post_call segs m ::=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch ?W m ?m' =>
      let W' := eval hnf in W in change (munch W' m m') in MUc;
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Lemma list_eq_repeat : forall (l : list word) (x : word) n,
  length l = n -> (forall j, (j < n)%nat -> nth j l w0 = x) -> l = repeat x n.
Proof.
  intros l x n Hl H. revert l Hl H. induction n as [|n IH]; intros l Hl H.
  - destruct l; [reflexivity| cbn in Hl; lia].
  - destruct l as [|y l]; [cbn in Hl; lia|]. cbn. f_equal.
    + exact (H 0%nat ltac:(lia)).
    + apply IH; [cbn in Hl; lia|]. intros j Hj. exact (H (S j) ltac:(lia)).
Qed.

Section Fill.
  Variables (x1 x2 x3 x4 x5 x6 x7 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (va : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (n : Z).
  Notation A := (bv_unsigned va).
  Hypothesis Hn : (0 < n <= 62)%Z.
  Hypothesis HA : (0 < A /\ A + 498 <= 2 ^ 64)%Z.

  (* [comment removed for export] *)
  Definition fill_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (a0 a3 : word) (m' : word -> option byte),
      ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 va x9 a0 (Z_to_bv 64 (-8)) (Z_to_bv 64 1) a3 x14 x15 x16 x17
                   x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x27aa4) fc None m' (seg_rom USEGS)
      /\ munch [(A, A + 8 * n)]%Z m m'
      /\ wmono USEGS m m'
      /\ u64arr USEGS m' A (repeat (Z_to_bv 64 0) (Z.to_nat n)).

  Definition fill_ok (k : nat) : Prop :=
    forall (i : nat) (p : word) (cur : list word) (m : word -> option byte),
      (Z.to_nat n - i = k)%nat -> (i < Z.to_nat n)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      u64arr USEGS m A cur -> length cur = Z.to_nat n ->
      (forall j, (j < i)%nat -> nth j cur w0 = Z_to_bv 64 0) ->
      munch [(A, A + 8 * n)]%Z m0 m -> wmono USEGS m0 m ->
      evt USEGS (fill_post m0)
        (MS (mkR x1 x2 x3 x4 x5 x6 x7 va x9 (Z_to_bv 64 (n + 1 - Z.of_nat i)) (Z_to_bv 64 (-8)) (Z_to_bv 64 1) p x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x27a90) fc None m (seg_rom USEGS)).

  #[using="Hn HA"] Lemma fill_body : forall k, fill_ok k -> fill_ok (S k).
  Proof. LiaFast.lf_pins (fun (Hn HA : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold fill_ok. intros i p cur m Hk Hi Hp CUR Hcur Hz MU WM.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    pose proof (u64arr_store_ok USEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write USEGS m A cur (Z.of_nat i) (Z_to_bv 64 0) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    change (le8 (Z_to_bv 64 0)) with (Z_to_le_bytes 8 0) in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    kill_check.
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hmore.
    - cond_cleanup Hmore. rewrite ?lm_signed_lit in Hmore by lia.
      replace (n + 1 - Z.of_nat i + -1)%Z with (n + 1 - Z.of_nat (S i))%Z by lia.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8)) (upd cur i (Z_to_bv 64 0))); try eassumption; try lia.
      all: first [ rewrite unsigned_lit by lia; lia
                 | rewrite upd_length; exact Hcur
                 | intros j Hj; destruct (Nat.eq_dec j i) as [->|NE]; [apply nth_upd_same; rewrite Hcur; lia| rewrite nth_upd_other by lia; apply Hz; lia] ].
    - cond_cleanup Hmore. rewrite ?lm_signed_lit in Hmore by lia.
      apply evt_done. unfold fill_post. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      replace (repeat (Z_to_bv 64 0) (Z.to_nat n)) with (upd cur i (Z_to_bv 64 0)); [exact CUR'|].
      apply list_eq_repeat. { rewrite upd_length. exact Hcur. }
      intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]. { apply nth_upd_same. rewrite Hcur. lia. }
      rewrite nth_upd_other by lia. apply Hz. lia.
  Qed.

  #[using="Hn HA"] Lemma fill_loop : forall k, fill_ok k.
  Proof. LiaFast.lf_pins (fun (Hn HA : LiaFast.U) => LiaFast.u0). induction k as [|k IH]. - unfold fill_ok; intros; exfalso; lia. - apply fill_body; exact IH. Qed.

  #[using="Hn HA"] Lemma fill_run : forall (p : word) (cur : list word),
    bv_unsigned p = A -> u64arr USEGS m0 A cur -> length cur = Z.to_nat n ->
    evt USEGS (fill_post m0)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 va x9 (Z_to_bv 64 (n + 1)) (Z_to_bv 64 (-8)) (Z_to_bv 64 1) p x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x27a90) fc None m0 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (Hn HA : LiaFast.U) => LiaFast.u0).
    intros p cur Hp CUR Hcur. replace (n + 1)%Z with (n + 1 - Z.of_nat 0)%Z by lia.
    eapply (fill_loop (Z.to_nat n) 0%nat p cur); try eassumption; try lia.
    all: first [intros j Hj; exfalso; lia | apply munch_refl | apply wmono_refl].
  Qed.
End Fill.

Section Main.
  Hypothesis copy_bwd_spec : copy_bwd_stmt.

  #[using="copy_bwd_spec"] Lemma shl_limbs_spec : shl_limbs_stmt.
  Proof. LiaFast.lf_pins (fun (copy_bwd_spec : LiaFast.U) => LiaFast.u0).
    unfold shl_limbs_stmt. intros until len. intros ST LIMBS L62 LENC Hlen A8 A0p Hn SEP.
    pose proof (munch_refl (shl_limbs_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU.
    cbv delta [shl_limbs_W] in MU.
    pose proof (wmono_refl USEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a1) as Rn. unfold bv_modulus in Rn.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    assert (SPB : (0 <= bv_unsigned sp - 112)%Z) by (destruct ST as (? & ? & ?); lia).
    remember (bv_unsigned a1) as n eqn:En.
    carve_frame 48%nat ST.
    do 6 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite zx16_lit_small by lia.
    zstep. (* [comment removed for export] *)
    rewrite <- ?En.
    (* [comment removed for export] *)
    assert (EXIT : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word) (m' : word -> option byte)
                          (ws' : list word) (len' : Z),
      u64arr USEGS m' (bv_unsigned a0) ws' -> length ws' = 62%nat ->
      rw_cells USEGS m' (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len')] -> (0 <= len' <= 62)%Z ->
      ((n + len <= 62)%Z -> bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) * 2 ^ (64 * n))%Z
                            /\ (bnorm ws (Z.to_nat len) -> bnorm ws' (Z.to_nat len'))) ->
      rw_cells USEGS m' (bv_unsigned sp + -48) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk USEGS m' (bv_unsigned sp - 112) (bv_unsigned sp + -48) ->
      munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 498)]%Z m m' -> wmono USEGS m m' ->
      evt USEGS (shl_limbs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) n ws len m)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 a0 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (n + len)) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x27ab0) fc None m' (seg_rom USEGS))).
    { intros * XA' L' LENC' Hl' VALC FR' ST' MU' WM'.
      step. (* [comment removed for export] *)
      rewrite v_sltiu_b2z. rewrite ?unsigned_lit by lia.
      pose proof (zb_b2z_range (n + len <? 63)%Z) as Rb.
      do 7 step.
      release_frame FR' ST' (bv_unsigned sp).
      unfold shl_limbs_post. finish.
      all: try eassumption. all: try lia.
      - intros Hb. apply VALC. destruct (Z.ltb_spec0 (n + len) 63); cbn in Hb; lia.
      - intros Hc. replace (n + len <? 63)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. (* [comment removed for export] *)
    if_cases Hz.
    - cond_cleanup Hz.
      eapply EXIT; try eassumption; try lia.
      all: intros _; rewrite Hz; change (Z.to_nat 0) with 0%nat; rewrite !bval_0; split; [ring| intros B; exact B].
    - cond_cleanup Hz.
      destruct (Z_of_nat_complete len ltac:(lia)) as [ln El].
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov.
      + cond_cleanup Hov.
        eapply EXIT; try eassumption; try lia. all: intros Hc; exfalso; lia.
      + cond_cleanup Hov.
        destruct (Z_of_nat_complete n ltac:(lia)) as [dn Ed].
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        kill_check.
        zstep. (* [comment removed for export] *)
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
        zstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        kill_check.
        zstep. (* [comment removed for export] *)
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        kill_check.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        kill_check.
        zstep. (* [comment removed for export] *)
        zstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        (* [comment removed for export] *)
        rewrite <- ?En.
        name_mem mc1.
        pose proof (u64arr_prefix_bytes USEGS mc1 _ ws ln ltac:(rewrite L62; lia) LIMBS) as SRC.
        destruct (u64arr_split3 USEGS mc1 _ ws dn ln ltac:(rewrite L62; lia) LIMBS) as (U1 & U2 & U3).
        pose proof (u8arr_of_u64arr USEGS _ _ _ U2) as DST.
        destruct (u64arr_len_split3 ws dn ln ltac:(rewrite L62; lia)) as (Ews & Ld & Ll & Lr). rewrite L62 in Lr.
        clear LIMBS U2.
        pose proof (unsigned_lit (bv_unsigned a0 + n * 8) ltac:(lia)) as UL1.
        pose proof (unsigned_lit (bv_unsigned a0 + len * 8) ltac:(lia)) as UL2.
        pose proof (unsigned_lit (bv_unsigned a0 + n * 8 + len * 8) ltac:(lia)) as UL3.
        pose proof (unsigned_lit (bv_unsigned sp + -48) ltac:(lia)) as ULs.
        step. (* [comment removed for export] *)
        eapply evt_cut; [ eapply copy_bwd_spec with (n := (8 * len)%Z) (D := (bv_unsigned a0 + 8 * n)%Z) | post_call USEGS mc1 ].
        1:{ rewrite ULs. replace (bv_unsigned sp + -48 - 64)%Z with (bv_unsigned sp - 112)%Z by lia. exact ST. }
        1:{ rewrite UL2. lia. } 1:{ rewrite UL3. lia. } 1:{ lia. } 1:{ rewrite Z.mul_comm. apply Z_mod_mult. }
        1:{ exact SRC. } 1:{ rewrite u64s_length, firstn_length, L62. lia. }
        1:{ eapply u8arr_at_eq; [exact DST| lia]. } 1:{ rewrite !u64s_length, Ll, firstn_length, L62. lia. }
        1:{ exact A8. } 1:{ rewrite Z.add_mod, A8, Z.mul_comm, Z_mod_mult by lia. reflexivity. } 1:{ lia. } 1:{ lia. }
        1:{ rewrite unsigned_lit by lia. reflexivity. }
        1:{ rewrite ULs. lia. } 1:{ rewrite ULs. lia. }
        rewrite ?UL1, ?UL2, ?UL3, ?ULs in *.
        name_mem mc2.
        match goal with H : u8arr USEGS mc2 _ (u64s (firstn ln ws)) |- _ =>
          pose proof (u64arr_of_u8arr USEGS mc2 _ ln (u64s (firstn ln ws)) H
                      ltac:(rewrite u64s_length, firstn_length, L62; lia)) as MID; clear H end.
        rewrite words_of_bytes_u64s in MID.
        replace (bv_unsigned a0 + n * 8 + len * 8 - (bv_unsigned a0 + len * 8 - bv_unsigned a0))%Z with (bv_unsigned a0 + 8 * Z.of_nat dn)%Z in MID by lia.
        step. (* [comment removed for export] *)
        kill_check.
        assert (Lm : length (firstn ln ws) = ln) by (rewrite firstn_length, L62; lia).
        step. (* [comment removed for export] *)
        if_cases Hn0.
        * cond_cleanup Hn0.
          (* [comment removed for export] *)
          assert (dn = 0%nat) as Dn0 by lia. rewrite Dn0 in U3, MID. cbn [Nat.add] in U3.
          assert (CUR2 : u64arr USEGS mc2 (bv_unsigned a0) (firstn ln ws ++ skipn ln ws)).
          { apply u64arr_app. rewrite Lm. split.
            - eapply u64arr_at_eq; [exact MID| lia].
            - eapply u64arr_at_eq; [exact U3| lia]. }
          rewrite firstn_skipn in CUR2.
          step. (* [comment removed for export] *)
          rewrite sx16_lit_small by lia.
          zstep. (* [comment removed for export] *)
          rewrite <- ?En.
          step. (* [comment removed for export] *)
          replace (len + n)%Z with len by lia.
          eapply EXIT; try eassumption; try lia.
          all: first [ assumption
                     | eapply stk_at_eq; [eassumption | lia | lia]
                     | intros _; replace n with 0%Z by lia; rewrite ?Z.add_0_r, Z.mul_0_r, Z.pow_0_r, Z.mul_1_r; split; [reflexivity| intros B; exact B] ].
        * cond_cleanup Hn0.
          zstep. (* [comment removed for export] *)
          rewrite <- ?En.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          name_mem mc3.
          eapply evt_cut; [ eapply (fill_run) with (va := a0) (n := n) | post_call USEGS mc3 ].
          all: try lia.
          1:{ exact U1. } 1:{ rewrite Ld. lia. }
          name_mem mc4.
          assert (Z1 : u64arr USEGS mc4 (bv_unsigned a0) (repeat (Z_to_bv 64 0) (Z.to_nat n))) by (split; assumption).
          assert (CUR2 : u64arr USEGS mc4 (bv_unsigned a0) (repeat (Z_to_bv 64 0) dn ++ firstn ln ws ++ skipn (dn + ln) ws)).
          { eapply (u64arr_join3 USEGS mc4 _ _ _ _ dn ln); [rewrite repeat_length; reflexivity | exact Lm | | exact MID | exact U3].
            replace dn with (Z.to_nat n) by lia. exact Z1. }
          set (ws2 := repeat (Z_to_bv 64 0) dn ++ firstn ln ws ++ skipn (dn + ln) ws) in CUR2.
          assert (L2 : length ws2 = 62%nat). { subst ws2. rewrite !app_length, repeat_length, Lm, Lr. lia. }
          clear Z1 MID U3.
          step. (* [comment removed for export] *)
          rewrite sx16_lit_small by lia.
          zstep. (* [comment removed for export] *)
          rewrite <- ?En.
          step. (* [comment removed for export] *)
          eapply EXIT; try eassumption; try lia.
          all: try (eapply stk_at_eq; [eassumption | lia | lia]).
          intros _.
          assert (Hhi : forall j, (j < ln)%nat -> nth (dn + j) ws2 w0 = nth j ws w0).
          { intros j Hj. subst ws2. rewrite nth_repeat_app_hi. rewrite app_nth1 by (rewrite Lm; exact Hj).
            rewrite <- (firstn_skipn ln ws) at 2. rewrite app_nth1 by (rewrite Lm; exact Hj). reflexivity. }
          split.
          -- replace (Z.to_nat (len + n)) with (dn + ln)%nat by lia.
             rewrite (bval_shift_limbs ws ws2 ln dn).
             ++ replace ln with (Z.to_nat len) by lia. rewrite <- Ed. reflexivity.
             ++ intros j Hj. unfold limbZ. subst ws2. rewrite nth_repeat_app_lo by exact Hj. apply unsigned_lit. lia.
             ++ exact Hhi.
          -- intros BN. right. replace (Z.to_nat (len + n) - 1)%nat with (dn + (ln - 1))%nat by lia.
             unfold limbZ. rewrite Hhi by lia.
             pose proof (bnorm_top ws (Z.to_nat len) ltac:(lia) BN) as T. unfold limbZ in T.
             replace (Z.to_nat len - 1)%nat with (ln - 1)%nat in T by lia. exact T.
  Qed.
End Main.
End U_shl_limbs.

Module U_pow_closed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_large_add_from_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_large_add_from.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_large_add_from.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_normalize_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_large_add_from_stmt U_large_add_from.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_long_mul.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_long_mul.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_long_mul.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_long_mul.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_long_mul.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_ciir_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_ciir_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_shl.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_shl.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_shl.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_shl_stmt U_shl U_long_mul_stmt U_long_mul.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_pow5.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_pow5.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_pow5_stmt U_pow5 U_pow10_stmt U_pow10 U_hi64_stmt U_hi64.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_hi64.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_hi64.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_hi64_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_positive_digit_comp_d.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_lib_closed.U_memmove_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_lib_closed.U_memmove OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_large_add_from_stmt.U_span_index_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_large_add_from.U_span_index OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_bigadd.U_resize_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_large_add_from.U_resize OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_normalize_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_lib_closed.U_normalize OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_large_add_from_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_large_add_from OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul.U_copy_impl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_lib_closed.U_copy_impl OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul.U_copy_fwd_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul.U_copy_fwd OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul.U_extend_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul.U_extend OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_ciir_stmt.U_copy_bwd_impl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_lib_closed.U_copy_bwd_impl OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_ciir_stmt.U_copy_bwd_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_lib_closed.U_copy_bwd OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_shl.U_shl_limbs_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_lib_closed.U_shl_limbs OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_shl.U_shl_bits_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_shl.U_shl_bits OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_shl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow5.U_large_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow5.U_large_mul OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow5 OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow10_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow10 OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_hi64_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_hi64 OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_hi64.U_nonzero_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_hi64.U_nonzero OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_hi64_stmt.U_ctlz_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_positive_digit_comp_d.U_ctlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)

Lemma U_large_add_from_closed : large_add_from_stmt.
Proof. exact (large_add_from_spec resize_spec span_index_spec). Qed.

Lemma U_copy_fwd_closed : copy_fwd_stmt.
Proof. exact (copy_fwd_spec copy_impl_spec). Qed.

Lemma U_extend_closed : extend_stmt.
Proof. exact (extend_spec U_copy_fwd_closed). Qed.

Definition U_copy_bwd_closed : copy_bwd_stmt := copy_bwd_spec.   (* [comment removed for export] *)

Lemma U_shl_limbs_closed : shl_limbs_stmt.
Proof. exact (shl_limbs_spec U_copy_bwd_closed). Qed.

Lemma U_shl_closed : shl_stmt.
Proof. exact (U_shl.shl_spec shl_bits_spec U_shl_limbs_closed). Qed.

Lemma U_long_mul_closed : long_mul_stmt.
Proof. exact (long_mul_spec span_index_spec U_extend_closed U_large_add_from_closed normalize_spec). Qed.

Lemma U_large_mul_closed : large_mul_stmt.
Proof. exact (OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow5.U_large_mul.large_mul_spec U_long_mul_closed). Qed.

Lemma U_pow5_closed : pow5_stmt.
Proof. exact (pow5_spec U_large_mul_closed). Qed.

Lemma U_pow10_closed : pow10_stmt.
Proof. exact (pow10_spec U_pow5_closed U_shl_closed). Qed.

Definition U_shl_bits_closed : shl_bits_stmt := shl_bits_spec.
Definition U_hi64_closed : hi64_stmt := hi64_spec.
Definition U_nonzero_closed : nonzero_stmt := nonzero_spec.
Definition U_ctlz_closed : ctlz_stmt := ctlz_spec.
End U_pow_closed.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_positive_digit_comp_d U_negative_digit_comp_d U_positive_digit_comp_f U_negative_digit_comp_f U_slow_path_double U_slow_path_float.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_from_chars_double.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_from_chars_float.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_from_chars_double U_from_chars_float U_ciir U_from_chars_int.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)

Definition U_positive_digit_comp_d_closed : positive_digit_comp_d_stmt :=
  U_positive_digit_comp_d.positive_digit_comp_d_spec
    U_pow_closed.U_pow10_closed U_pow_closed.U_hi64_closed U_pow_closed.U_ctlz_closed.
Definition U_negative_digit_comp_d_closed : negative_digit_comp_d_stmt :=
  U_negative_digit_comp_d.negative_digit_comp_d_spec
    U_memset.memset_spec U_normalize.normalize_spec U_pow_closed.U_pow5_closed U_pow_closed.U_shl_closed
    U_compare.compare_spec.
Definition U_positive_digit_comp_f_closed : positive_digit_comp_f_stmt :=
  U_positive_digit_comp_f.positive_digit_comp_f_spec
    U_pow_closed.U_pow10_closed U_pow_closed.U_hi64_closed U_pow_closed.U_ctlz_closed.
Definition U_negative_digit_comp_f_closed : negative_digit_comp_f_stmt :=
  U_negative_digit_comp_f.negative_digit_comp_f_spec
    U_memset.memset_spec U_normalize.normalize_spec U_pow_closed.U_pow5_closed U_pow_closed.U_shl_closed
    U_compare.compare_spec.

Definition U_slow_path_double_closed : slow_path_double_stmt :=
  U_slow_path_double.slow_path_double_spec U_positive_digit_comp_d_closed U_negative_digit_comp_d_closed.
Definition U_slow_path_float_closed : slow_path_float_stmt :=
  U_slow_path_float.slow_path_float_spec U_positive_digit_comp_f_closed U_negative_digit_comp_f_closed.

Definition U_from_chars_double_closed : from_chars_double_stmt :=
  U_from_chars_double.from_chars_double_spec OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_parse_infnan_d.parse_infnan_d_spec U_slow_path_double_closed.

Definition U_from_chars_float_closed : from_chars_float_stmt :=
  U_from_chars_float.from_chars_float_spec OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_float.U_parse_infnan_f.parse_infnan_f_spec U_slow_path_float_closed.



Definition U_from_chars_int_closed : from_chars_int_stmt := U_from_chars_int.from_chars_int_spec.
Definition U_ciir_closed : ciir_stmt := U_ciir.ciir_spec.
