(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_memset_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_stmt P_pow5_stmt P_pow10_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow5_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_hi64_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_hi64_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_positive_digit_comp_d_stmt P_negative_digit_comp_d_stmt P_positive_digit_comp_f_stmt P_negative_digit_comp_f_stmt P_slow_path_double_stmt P_slow_path_float_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_from_chars_double.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_from_chars_float.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_from_chars_double_stmt P_from_chars_float_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memset_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_small_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5_stmt.P_shl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_hi64_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_hi64_stmt.P_ctlz_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_positive_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_negative_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_positive_digit_comp_f_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_negative_digit_comp_f_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_float_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_parse_infnan_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_float.P_parse_infnan_f_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_float_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_from_chars_int_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_memset.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spf_DC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spf_DC.

Module P_large_add_from_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation PSEGS := Plain.M.loaded_segments.

Definition large_add_from_entry : Z := 0x266c0.
Definition large_add_from_frame : Z := 48.

(* [comment removed for export] *)
Definition large_add_from_W (sp A : Z) : list ivl := [(sp - 48, sp); (A, A + 498)]%Z.

Definition large_add_from_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A Y ylen start : Z) (ws ys : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                    (ws' : list word) (len' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom PSEGS)
    /\ munch (large_add_from_W (bv_unsigned sp) A) m m'
    /\ wmono PSEGS m m'
    /\ stk PSEGS m' (bv_unsigned sp - 48) (bv_unsigned sp)
    /\ u64arr PSEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ u64arr PSEGS m' Y ys
    /\ (Z.max len (ylen + start) <= len' <= Z.max len (ylen + start) + 1 /\ len' <= 62)%Z
    /\ bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) + bval ys (Z.to_nat ylen) * 2 ^ (64 * start))%Z.

Definition large_add_from_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z) (ys : list word) (ylen start : Z),
    stk PSEGS m (bv_unsigned sp - 48) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (* [comment removed for export] *)
    u64arr PSEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells PSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> (bv_unsigned a0 mod 8 = 0)%Z ->
    (* [comment removed for export] *)
    u64arr PSEGS m (bv_unsigned a1) ys -> length ys = 62%nat ->
    a2 = Z_to_bv 64 ylen -> (0 <= ylen <= 62)%Z ->
    (bv_unsigned a1 mod 8 = 0)%Z -> (bv_unsigned a1 <> 0)%Z -> (bv_unsigned a1 + 496 < 2^64)%Z ->
    a3 = Z_to_bv 64 start -> (0 <= start)%Z -> (ylen + start <= 62)%Z ->
    (* [comment removed for export] *)
    (bval ws (Z.to_nat len) + bval ys (Z.to_nat ylen) * 2 ^ (64 * start) < BIG_CAP)%Z ->
    (* [comment removed for export] *)
    (bv_unsigned a0 + 498 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 496 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    (bv_unsigned a0 + 498 <= bv_unsigned a1 \/ bv_unsigned a1 + 496 <= bv_unsigned a0)%Z ->
    evt PSEGS (large_add_from_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) (bv_unsigned a1) ylen start ws ys len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x266c0) fc None m (seg_rom PSEGS)).
End P_large_add_from_stmt.

Module P_large_add_from.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_memset_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_bigadd OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_bigadd.U_resize_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memset_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_lib_closed.P_large_add_from_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.

Section Proof.
  Set Default Proof Using "All".
  Hypothesis memset_spec : memset_stmt.
  Variables (ra sp gp tp s0i s1i s2i s3i s4i s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (xv yv : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws ys : list word) (len ylen start : Z) (nl ny ns : nat).
  Hypothesis Hnl : len = Z.of_nat nl.
  Hypothesis Hny : ylen = Z.of_nat ny.
  Hypothesis Hns : start = Z.of_nat ns.
  Hypothesis Hxl : length ws = 62%nat.
  Hypothesis Hyl : length ys = 62%nat.
  Hypothesis XLEN : (0 <= len <= 62)%Z.
  Hypothesis YLEN : (0 <= ylen <= 62)%Z.
  Hypothesis START : (0 <= start)%Z.
  Hypothesis FIT : (ylen + start <= 62)%Z.
  Hypothesis XAL : (bv_unsigned xv mod 8 = 0)%Z.
  Hypothesis YAL : (bv_unsigned yv mod 8 = 0)%Z.
  Hypothesis YNZ : (bv_unsigned yv <> 0)%Z.
  Hypothesis YEND : (bv_unsigned yv + 496 < 2^64)%Z.
  Hypothesis ALIGN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis CAP : boxed (bval ws nl + bval ys ny * 2 ^ (64 * start) < BIG_CAP)%Z.
  Hypothesis SEP1 : (bv_unsigned xv + 498 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned xv)%Z.
  Hypothesis SEP2 : (bv_unsigned yv + 496 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned yv)%Z.
  Hypothesis SEP3 : (bv_unsigned xv + 498 <= bv_unsigned yv \/ bv_unsigned yv + 496 <= bv_unsigned xv)%Z.

  Notation X := (bv_unsigned xv).
  Notation Y := (bv_unsigned yv).
  Notation SP := (bv_unsigned sp).
  Notation W := [((SP - 48)%Z, SP); (X, (X + 498)%Z)].
  Notation POST := (large_add_from_post ra sp gp tp s0i s1i s2i s3i s4i s5 s6 s7 s8 s9 s10 s11 F fc X Y ylen start ws ys len m0).
  Notation FRAME m := (rw_cells PSEGS m (SP + -48) [C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 xv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 yv) as RB; unfold bv_modulus in RB;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp.

  (* [comment removed for export] *)
  Definition epi_ok : Prop :=
    forall (rar t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3r s4r t3 t4 t5 t6 : word) (m : word -> option byte) (ws' : list word) (len' : Z),
      FRAME m -> stk PSEGS m (SP + -48) (SP + -48) ->
      u64arr PSEGS m X ws' -> length ws' = 62%nat ->
      rw_cells PSEGS m (X + 496) [C2 (Z_to_bv 64 len')] ->
      u64arr PSEGS m Y ys ->
      munch W m0 m -> wmono PSEGS m0 m ->
      (Z.max len (ylen + start) <= len' <= Z.max len (ylen + start) + 1 /\ len' <= 62)%Z ->
      boxed (bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) + bval ys (Z.to_nat ylen) * 2 ^ (64 * start)))%Z ->
      evt PSEGS POST
        (MS (mkR rar (Z_to_bv 64 (SP + -48)) gp tp t0 t1 t2 xv (Z_to_bv 64 start) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ylen) s3r s4r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x267f8) fc None m (seg_rom PSEGS)).

  Lemma epilogue : epi_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    unfold epi_ok. intros until len'. intros FR ST XL Hxl' XC YL MU WM HB HV. bounds.
    do 7 step.
    step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold large_add_from_post. finish.
    { exact XL. } { exact Hxl'. } { exact XC. } all: try lia. exact HV.
  Qed.

  (* [comment removed for export] *)
  Section RS.
  Variables (N : Z) (nN : nat) (x0 : list word).
  Hypothesis HnN : N = Z.of_nat nN.
  Hypothesis HN : N = Z.max len (ylen + start).
  Hypothesis Hx0l : length x0 = 62%nat.
  Hypothesis HX0 : boxed (bval x0 nN = bval ws nl).

  (* [comment removed for export] *)
  Definition rip_ok (k : nat) : Prop :=
    forall (j : nat) (rar t0 t1 t2 a4 a5 a6 a7 s3r s4r t3 t4 t5 t6 : word) (cur : list word) (m : word -> option byte),
      (nN - j = k)%nat -> (ny + ns <= j <= nN)%nat ->
      FRAME m -> stk PSEGS m (SP + -48) (SP + -48) ->
      u64arr PSEGS m X cur -> length cur = 62%nat -> rw_cells PSEGS m (X + 496) [C2 (Z_to_bv 64 N)] -> u64arr PSEGS m Y ys ->
      boxed (rip_inv x0 cur ys ns ny j) ->
      munch W m0 m -> wmono PSEGS m0 m ->
      evt PSEGS POST
        (MS (mkR rar (Z_to_bv 64 (SP + -48)) gp tp t0 t1 t2 xv (Z_to_bv 64 start) (Z_to_bv 64 1)
                 (Z_to_bv 64 (Z.of_nat j - N - 1)) (Z_to_bv 64 N) (Z_to_bv 64 (X + 8 * Z.of_nat j)) a4 a5 a6 a7
                 (Z_to_bv 64 ylen) s3r s4r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x267ac) fc None m (seg_rom PSEGS)).

  Lemma rip_loop : epi_ok -> forall k, rip_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros EPI. induction k as [|k IH]; unfold rip_ok; intros j rar t0 t1 t2 a4 a5 a6 a7 s3r s4r t3 t4 t5 t6 cur m Hk Hj FR ST XL Hcur XC YL RI MU WM; bounds.
    - (* [comment removed for export] *)
      assert (HjN : j = nN) by lia. subst j. rewrite <- HnN.
      pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hcur in BdX.
      pose proof (rw_cells_bound _ _ _ _ XC) as BLX. cbn [cells_size csize Nat.add] in BLX.
      assert (ROOM : (N <= 61)%Z).
      { pose proof (rip_room x0 cur ys _ _ _ RI) as R. unfold boxed in HX0, CAP. rewrite HX0, <- Hns in R. specialize (R CAP). lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [| exfalso; lia]. clear Hz.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit N) by lia. rewrite Z.shiftl_mul_pow2 by lia. replace (N * 2 ^ 3)%Z with (8 * N)%Z by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (u64arr_store_ok PSEGS m X cur N (Z_to_bv 64 (X + 8 * N)) XL ltac:(lia) eq_refl) as SOK.
      step. (* [comment removed for export] *)
      change (Z_to_le_bytes 8 1) with (le8 (Z_to_bv 64 1)).
      pose proof (u64arr_write PSEGS m X cur N (Z_to_bv 64 1) XL ltac:(lia)) as XL'.
      store_done.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply EPI; try eassumption.
      + rewrite upd_length. exact Hcur.
      + lia.
      + unfold boxed in *. replace (Z.to_nat (N + 1)) with (S nN) by lia. replace (Z.to_nat N) with nN by lia.
        rewrite (rip_inv_push x0 cur ys _ _ _ RI) by (rewrite ?Hx0l, ?Hcur; lia).
        rewrite HX0, <- Hns. rewrite Hnl, Hny, !Nat2Z.id. reflexivity.
    - destruct (Nat.eq_dec j nN) as [->|Hne].
      { eapply (IH nN rar); try eassumption; lia. }
      pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hcur in BdX.
      pose proof (rw_cells_bound _ _ _ _ XC) as BLX. cbn [cells_size csize Nat.add] in BLX.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz.
      { exfalso. first [ lia | revert Hz; replace (Z.of_nat j - N - 1 + 1)%Z with ((Z.of_nat j - N + 2^64) + (-1) * 2^64)%Z by lia;
        change 18446744073709551616%Z with (2^64)%Z; rewrite Z.mod_add, Z.mod_small by lia; lia ]. }
      clear Hz.
      destruct (nth_error cur j) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
      assert (Hw : nth j cur w0 = w) by (apply nth_error_nth; exact Hn).
      assert (Hlimb : limbZ x0 j = bv_unsigned w).
      { unfold boxed in RI. destruct RI as (_ & RIag & _). unfold limbZ. rewrite <- (RIag j) by lia. rewrite Hw. reflexivity. }
      pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
      pose proof (u64arr_read PSEGS m X cur (Z.of_nat j) w (Z_to_bv 64 (X + 8 * Z.of_nat j)) XL ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) eq_refl) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (u64arr_store_ok PSEGS m X cur (Z.of_nat j) (Z_to_bv 64 (X + 8 * Z.of_nat j)) XL ltac:(lia) eq_refl) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write PSEGS m X cur (Z.of_nat j) (Z_to_bv 64 (bv_unsigned w + 1)) XL ltac:(lia)) as XL'.
      rewrite Nat2Z.id in XL'.
      store_done.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc.
      + (* [comment removed for export] *)
        assert (Hwr : (bv_unsigned w + 1 = 2^64)%Z).
        { destruct (Z.eq_dec (bv_unsigned w + 1) (2^64)); [assumption|]. exfalso.
          first [ rewrite Z.mod_small in Hc by lia; lia | lia ]. }
        clear Hc.
        replace (Z.of_nat j - N - 1 + 1)%Z with (Z.of_nat (S j) - N - 1)%Z by lia.
        replace (X + 8 * Z.of_nat j + 8)%Z with (X + 8 * Z.of_nat (S j))%Z by lia.
        eapply (IH (S j) rar); try eassumption; try lia.
        { rewrite upd_length. exact Hcur. }
        unfold boxed in RI |- *. rewrite <- Hlimb. apply rip_inv_wrap; [exact RI | rewrite Hx0l; lia | lia].
      + (* [comment removed for export] *)
        assert (Hnw : (bv_unsigned w + 1 < 2^64)%Z).
        { destruct (Z.lt_ge_cases (bv_unsigned w + 1) (2^64)); [assumption|]. exfalso.
          change 18446744073709551616%Z with (2^64)%Z in Hc.
          rewrite <- (Z.mod_unique_pos (bv_unsigned w + 1) (2^64) 1 (bv_unsigned w + 1 - 2^64)) in Hc by lia. lia. }
        clear Hc.
        step. (* [comment removed for export] *)
        eapply EPI; try eassumption.
        * rewrite upd_length. exact Hcur.
        * lia.
        * unfold boxed in RI, HX0 |- *. rewrite <- Hlimb. replace (Z.to_nat N) with nN by lia.
          rewrite (rip_inv_stop x0 cur ys _ _ _ nN RI) by (rewrite ?Hx0l; lia).
          rewrite HX0, <- Hns. rewrite Hnl, Hny, !Nat2Z.id. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition tail_ok (k : nat) : Prop :=
    forall (i : nat) (rar px py t0 t1 t2 a5 a6 a7 s4r t3 t4 t5 t6 : word) (c : Z) (cur : list word) (m : word -> option byte),
      (ny - S i = k)%nat -> (S i <= ny)%nat ->
      bv_unsigned px = (X + 8 * (start + Z.of_nat i))%Z -> bv_unsigned py = (Y + 8 * Z.of_nat i)%Z ->
      FRAME m -> stk PSEGS m (SP + -48) (SP + -48) ->
      u64arr PSEGS m X cur -> length cur = 62%nat -> rw_cells PSEGS m (X + 496) [C2 (Z_to_bv 64 N)] -> u64arr PSEGS m Y ys ->
      boxed (ladd_inv x0 cur ys ns (S i) c) ->
      munch W m0 m -> wmono PSEGS m0 m ->
      evt PSEGS POST
        (MS (mkR rar (Z_to_bv 64 (SP + -48)) gp tp t0 t1 t2 xv (Z_to_bv 64 start) (Z_to_bv 64 1)
                 (Z_to_bv 64 c) (Z_to_bv 64 N) px (Z_to_bv 64 (Y + 8 * ylen)) a5 a6 a7
                 (Z_to_bv 64 ylen) (Z_to_bv 64 (bv_unsigned py + 8)) s4r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x26780) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition add_ok (k : nat) : Prop :=
    forall (i : nat) (rar px py t0 t1 t2 a5 a6 a7 s4r t3 t4 t5 t6 : word) (c : Z) (cur : list word) (m : word -> option byte),
      (ny - i = k)%nat -> (i < ny)%nat ->
      bv_unsigned px = (X + 8 * (start + Z.of_nat i))%Z -> bv_unsigned py = (Y + 8 * Z.of_nat i)%Z ->
      FRAME m -> stk PSEGS m (SP + -48) (SP + -48) ->
      u64arr PSEGS m X cur -> length cur = 62%nat -> rw_cells PSEGS m (X + 496) [C2 (Z_to_bv 64 N)] -> u64arr PSEGS m Y ys ->
      boxed (ladd_inv x0 cur ys ns i c) ->
      munch W m0 m -> wmono PSEGS m0 m ->
      evt PSEGS POST
        (MS (mkR rar (Z_to_bv 64 (SP + -48)) gp tp t0 t1 t2 xv (Z_to_bv 64 start) (Z_to_bv 64 1)
                 (Z_to_bv 64 c) (Z_to_bv 64 N) px (Z_to_bv 64 (Y + 8 * ylen)) a5 a6 a7
                 (Z_to_bv 64 ylen) py s4r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x26748) fc None m (seg_rom PSEGS)).

  Lemma add_tail : epi_ok -> (forall k, rip_ok k) -> forall k, add_ok k -> tail_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros EPI RIP k IH. unfold tail_ok.
    intros i rar px py t0 t1 t2 a5 a6 a7 s4r t3 t4 t5 t6 c cur m Hk Hi Hpx Hpy FR ST XL Hcur XC YL LI MU WM; bounds.
    assert (LIc : c = 0%Z \/ c = 1%Z) by (unfold boxed in LI; destruct LI as (_ & _ & _ & Hc); exact Hc).
    pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hcur in BdX.
    pose proof (u64arr_bound _ _ _ _ YL) as BdY. rewrite Hyl in BdY.
    pose proof (rw_cells_bound _ _ _ _ XC) as BLX. cbn [cells_size csize Nat.add] in BLX.
    pose proof (bv_unsigned_in_range 64 px) as Rpx. unfold bv_modulus in Rpx.
    pose proof (bv_unsigned_in_range 64 py) as Rpy. unfold bv_modulus in Rpy.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - (* [comment removed for export] *)
      eapply (IH (S i) rar (Z_to_bv 64 (bv_unsigned px + 8)) (Z_to_bv 64 (bv_unsigned py + 8))); try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite unsigned_lit by lia. lia.
    - (* [comment removed for export] *)
      assert (Hn : S i = ny) by lia. clear Hb.
      step. (* [comment removed for export] *)
      destruct LIc as [Hc0 | Hc1]; subst c.
      + (* [comment removed for export] *)
        if_true.
        eapply EPI; try eassumption; try lia.
        unfold boxed in LI, HX0 |- *.
        pose proof (ladd_finish x0 cur ys _ _ _ nN LI ltac:(lia)) as HV.
        rewrite Hn, HX0, <- Hns in HV. rewrite Hnl, Hny, !Nat2Z.id.
        replace (Z.to_nat N) with nN by lia. lia.
      + (* [comment removed for export] *)
        if_false.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_not_taken.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite (unsigned_lit (ylen + start)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite (unsigned_lit N) by lia.
        replace (Z_to_bv 64 (X + (ylen + start) * 2 ^ 3)) with (Z_to_bv 64 (X + 8 * Z.of_nat (ny + ns))) by (f_equal; lia).
        replace (Z_to_bv 64 (Z.lxor N 18446744073709551615 + (ylen + start))) with (Z_to_bv 64 (Z.of_nat (ny + ns) - N - 1)).
        2:{ apply Z_to_bv_eqm. rewrite zb_lxor_ones by lia.
            replace (18446744073709551615 - N + (ylen + start))%Z with ((Z.of_nat (ny + ns) - N - 1) + 1 * 2^64)%Z by lia.
            rewrite Z.mod_add by lia. reflexivity. }
        eapply (RIP (nN - (ny + ns))%nat (ny + ns)%nat rar); try eassumption; try lia.
        unfold boxed in LI |- *. replace (ny + ns)%nat with (ns + ny)%nat by lia.
        apply rip_inv_start. rewrite <- Hn. exact LI.
  Qed.

  Lemma add_loop : epi_ok -> (forall k, rip_ok k) -> forall k, add_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros EPI RIP. induction k as [|k IH]; unfold add_ok;
      intros i rar px py t0 t1 t2 a5 a6 a7 s4r t3 t4 t5 t6 c cur m Hk Hi Hpx Hpy FR ST XL Hcur XC YL LI MU WM; bounds.
    { exfalso; lia. }
    pose proof (add_tail EPI RIP k IH) as TAIL.
    assert (LIc : c = 0%Z \/ c = 1%Z) by (unfold boxed in LI; destruct LI as (_ & _ & _ & Hc); exact Hc).
    pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hcur in BdX.
    pose proof (u64arr_bound _ _ _ _ YL) as BdY. rewrite Hyl in BdY.
    pose proof (rw_cells_bound _ _ _ _ XC) as BLX. cbn [cells_size csize Nat.add] in BLX.
    pose proof (bv_unsigned_in_range 64 px) as Rpx. unfold bv_modulus in Rpx.
    pose proof (bv_unsigned_in_range 64 py) as Rpy. unfold bv_modulus in Rpy.
    destruct (nth_error cur (ns + i)) as [wx|] eqn:Hnx. 2:{ exfalso. apply nth_error_None in Hnx. lia. }
    assert (Hwx : nth (ns + i) cur w0 = wx) by (apply nth_error_nth; exact Hnx).
    destruct (nth_error ys i) as [wy|] eqn:Hny'. 2:{ exfalso. apply nth_error_None in Hny'. lia. }
    assert (Hwy : nth i ys w0 = wy) by (apply nth_error_nth; exact Hny').
    pose proof (bv_unsigned_in_range 64 wx) as Rwx. unfold bv_modulus in Rwx.
    pose proof (bv_unsigned_in_range 64 wy) as Rwy. unfold bv_modulus in Rwy.
    assert (Ex : limbZ x0 (ns + i) = bv_unsigned wx).
    { unfold boxed in LI. destruct LI as (_ & LIag & _). unfold limbZ. rewrite <- (LIag (ns + i)%nat) by lia. rewrite Hwx. reflexivity. }
    assert (Ey : limbZ ys i = bv_unsigned wy) by (unfold limbZ; rewrite Hwy; reflexivity).
    assert (LI2 : forall cc, cc = c ->
              boxed (ladd_inv x0 (upd cur (ns + i) (Z_to_bv 64 (bv_unsigned wx + bv_unsigned wy + cc))) ys ns (S i)
                       (if bv_unsigned wx + bv_unsigned wy + cc <? 2 ^ 64 then 0 else 1)%Z)).
    { intros cc ->. unfold boxed in LI |- *. rewrite <- Ex, <- Ey. apply (ladd_inv_step x0 cur ys ns i c LI). rewrite Hx0l. lia. }
    pose proof (u64arr_read PSEGS m X cur (Z.of_nat (ns + i)) wx px XL ltac:(rewrite Nat2Z.id; exact Hnx) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    pose proof (u64arr_read PSEGS m Y ys (Z.of_nat i) wy py YL ltac:(rewrite Nat2Z.id; exact Hny') ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_store_ok PSEGS m X cur (Z.of_nat (ns + i)) px XL ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    destruct LIc as [Hc0 | Hc1]; subst c.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_false.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (u64arr_write PSEGS m X cur (Z.of_nat (ns + i)) (Z_to_bv 64 (bv_unsigned wx + bv_unsigned wy)) XL ltac:(lia)) as XL'.
      replace (X + 8 * Z.of_nat (ns + i))%Z with (bv_unsigned px + 0)%Z in XL' by lia. rewrite Nat2Z.id in XL'.
      store_done.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (ladd_carry0 wx (bv_unsigned wy)) by lia.
      eapply TAIL; try eassumption; try lia.
      { rewrite upd_length. exact Hcur. }
      specialize (LI2 0%Z eq_refl). rewrite !Z.add_0_r in LI2. rewrite !Z.add_0_r. exact LI2.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_true.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (u64arr_write PSEGS m X cur (Z.of_nat (ns + i)) (Z_to_bv 64 (bv_unsigned wx + bv_unsigned wy + 1)) XL ltac:(lia)) as XL'.
      replace (X + 8 * Z.of_nat (ns + i))%Z with (bv_unsigned px + 0)%Z in XL' by lia. rewrite Nat2Z.id in XL'.
      store_done.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (ladd_carry1 wx (bv_unsigned wy)) by lia.
      eapply TAIL; try eassumption; try lia.
      { rewrite upd_length. exact Hcur. }
      exact (LI2 1%Z eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma from_2483c : epi_ok -> (forall k, add_ok k) ->
    forall (rar t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s4r t3 t4 t5 t6 : word) (m : word -> option byte),
      FRAME m -> stk PSEGS m (SP + -48) (SP + -48) ->
      u64arr PSEGS m X x0 -> rw_cells PSEGS m (X + 496) [C2 (Z_to_bv 64 N)] -> u64arr PSEGS m Y ys ->
      munch W m0 m -> wmono PSEGS m0 m ->
      evt PSEGS POST
        (MS (mkR rar (Z_to_bv 64 (SP + -48)) gp tp t0 t1 t2 xv (Z_to_bv 64 start) a0 a1 (Z_to_bv 64 N) a3 a4 a5 a6 a7
                 (Z_to_bv 64 ylen) yv s4r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2672c) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros EPI ADD. intros until m. intros FR ST XL XC YL MU WM; bounds.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hx0l in BdX.
    pose proof (u64arr_bound _ _ _ _ YL) as BdY. rewrite Hyl in BdY.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz; cond_cleanup Hz.
    - (* [comment removed for export] *)
      eapply EPI; try eassumption; try lia.
      unfold boxed in HX0 |- *. replace (Z.to_nat N) with nN by lia. rewrite HX0, Hnl, Hny, !Nat2Z.id.
      replace ny with 0%nat by lia. cbn [bval]. lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit start), (unsigned_lit ylen) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
      replace (Z_to_bv 64 (Y + ylen * 2 ^ 3)) with (Z_to_bv 64 (Y + 8 * ylen)) by (f_equal; lia).
      eapply (ADD ny 0%nat rar (Z_to_bv 64 (X + start * 2 ^ 3)) yv); try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + unfold boxed. apply ladd_inv_init.
  Qed.

  End RS.


  (* [comment removed for export] *)
  Lemma from_2480c : epi_ok ->
    forall (rar t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte),
      (len < ylen + start)%Z ->
      FRAME m -> stk PSEGS m (SP + -48) (SP + -48) ->
      u64arr PSEGS m X ws -> rw_cells PSEGS m (X + 496) [C2 (Z_to_bv 64 len)] -> u64arr PSEGS m Y ys ->
      munch W m0 m -> wmono PSEGS m0 m ->
      evt PSEGS POST
        (MS (mkR rar (Z_to_bv 64 (SP + -48)) gp tp t0 t1 t2 xv (Z_to_bv 64 start) a0 a1 (Z_to_bv 64 len) a3 a4 a5 a6 a7
                 (Z_to_bv 64 ylen) yv s4i s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x266fc) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros EPI. intros until m. intros HLT FR ST XL XC YL MU WM; bounds.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hxl in BdX.
    pose proof (u64arr_bound _ _ _ _ YL) as BdY. rewrite Hyl in BdY.
    pose proof (rw_cells_bound _ _ _ _ XC) as BLX. cbn [cells_size csize Nat.add] in BLX.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit len), (unsigned_lit (ylen + start)) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
    rewrite (unsigned_lit (ylen + start - len)) by lia.
    replace (Z_to_bv 64 (X + len * 2 ^ 3)) with (Z_to_bv 64 (X + 8 * len)) by (f_equal; lia).
    (* [comment removed for export] *)
    set (k := (ny + ns - nl)%nat).
    remember (firstn nl ws) as wlo eqn:Ewlo.
    remember (firstn k (skipn nl ws)) as wmid eqn:Ewmid.
    remember (skipn k (skipn nl ws)) as whi eqn:Ewhi.
    assert (Llo : length wlo = nl) by (subst wlo; rewrite firstn_length; lia).
    assert (Lmid : length wmid = k) by (subst wmid; rewrite firstn_length, skipn_length; lia).
    assert (Lhi : length whi = (62 - nl - k)%nat) by (subst whi; rewrite !skipn_length; lia).
    assert (Ews : ws = wlo ++ wmid ++ whi) by (subst wlo wmid whi; rewrite !firstn_skipn; reflexivity).
    rewrite Ews in XL. apply (proj1 (u64arr_app _ _ _ _ _)) in XL. destruct XL as [XLlo XLr].
    apply (proj1 (u64arr_app _ _ _ _ _)) in XLr. destruct XLr as [XLmid XLhi].
    rewrite Llo in XLmid, XLhi. rewrite Lmid in XLhi.
    replace (X + 8 * Z.of_nat nl)%Z with (X + 8 * len)%Z in XLmid, XLhi by lia.
    pose proof (u8arr_of_u64arr _ _ _ _ XLmid) as OLD. clear XLmid.
    (* [comment removed for export] *)
    pose proof (unsigned_lit (X + 8 * len) ltac:(lia)) as U1.
    pose proof (unsigned_lit ((ylen + start - len) * 2 ^ 3) ltac:(lia)) as U2.
    step. (* [comment removed for export] *)
    call memset_spec.
    { reflexivity. }
    { rewrite unsigned_lit by lia. exact OLD. }
    { rewrite u64s_length, Lmid. rewrite unsigned_lit by lia. lia. }
    { rewrite unsigned_lit by lia. rewrite Z.add_mod, XAL, Z.mul_comm, Z.mod_mul by lia. reflexivity. }
    lazymatch goal with
    | HB : bytes_at PSEGS ?m' _ (repeat _ _), HW : wr_at PSEGS _ _ _ |- _ =>
      rewrite U1, U2 in HB, HW;
      replace (Z.to_nat ((ylen + start - len) * 2 ^ 3)) with (8 * k)%nat in HB, HW by lia;
      pose proof (u64arr_of_u8arr PSEGS m' (X + 8 * len) k _ (conj HB HW) ltac:(rewrite repeat_length; reflexivity)) as XLmid;
      clear HB HW
    end.
    rewrite words_of_bytes_zero in XLmid.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
      assert (XL' : u64arr PSEGS m' X (wlo ++ repeat (Z_to_bv 64 0) k ++ whi))
    end.
    { apply (proj2 (u64arr_app _ _ _ _ _)). split; [exact XLlo|].
      rewrite Llo. replace (X + 8 * Z.of_nat nl)%Z with (X + 8 * len)%Z by lia.
      apply (proj2 (u64arr_app _ _ _ _ _)). split; [exact XLmid|].
      rewrite repeat_length. exact XLhi. }
    clear XLlo XLmid XLhi.
    assert (Hx0l : length (wlo ++ repeat (Z_to_bv 64 0) k ++ whi) = 62%nat) by (rewrite !app_length, repeat_length; lia).
    pose proof (repeat_length (Z_to_bv 64 0) k) as Lrep.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    assert (HX0 : boxed (bval (wlo ++ repeat (Z_to_bv 64 0) k ++ whi) (ny + ns)%nat = bval ws nl)).
    { unfold boxed. replace (ny + ns)%nat with (nl + k)%nat by lia.
      rewrite <- (bval_zfill0 ws nl k) by (rewrite Hxl; lia). unfold zfill. subst wlo whi k.
      rewrite skipn_skipn. replace (ny + ns - nl + nl)%nat with (nl + (ny + ns - nl))%nat by lia. reflexivity. }
    assert (HnN : (ylen + start)%Z = Z.of_nat (ny + ns)) by lia.
    assert (HN : (ylen + start)%Z = Z.max len (ylen + start)) by lia.
    pose proof (rip_loop (ylen + start)%Z (ny + ns)%nat _ HnN HN Hx0l HX0 EPI) as RIP.
    pose proof (add_loop (ylen + start)%Z (ny + ns)%nat _ HnN HN Hx0l HX0 EPI RIP) as ADD.
    eapply (from_2483c (ylen + start)%Z (ny + ns)%nat _ HnN HN Hx0l HX0 EPI ADD); eassumption.
  Qed.
  (* [comment removed for export] *)
  Lemma body_ok : epi_ok ->
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      stk PSEGS m0 (SP - 48) SP ->
      u64arr PSEGS m0 X ws -> rw_cells PSEGS m0 (X + 496) [C2 (Z_to_bv 64 len)] -> u64arr PSEGS m0 Y ys ->
      evt PSEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0i s1i xv yv (Z_to_bv 64 ylen) (Z_to_bv 64 start) a4 a5 a6 a7
                 s2i s3i s4i s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x266c0) fc None m0 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros EPI. intros until t6. intros ST XL XC YL. bounds.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hxl in BdX.
    pose proof (u64arr_bound _ _ _ _ YL) as BdY. rewrite Hyl in BdY.
    pose proof (rw_cells_bound _ _ _ _ XC) as BLX. cbn [cells_size csize Nat.add] in BLX.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl PSEGS m0) as WM.
    carve_frame 48%nat ST.
    do 7 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite zx16_lit by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H1; cond_cleanup H1.
    2: { (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H2; cond_cleanup H2.
      { (* [comment removed for export] *)
        assert (HX0 : boxed (bval ws nl = bval ws nl)) by (unfold boxed; reflexivity).
        assert (HN : len = Z.max len (ylen + start)) by lia.
        pose proof (rip_loop len nl ws Hnl HN Hxl HX0 EPI) as RIP.
        pose proof (add_loop len nl ws Hnl HN Hxl HX0 EPI RIP) as ADD.
        eapply (from_2483c len nl ws Hnl HN Hxl HX0 EPI ADD); eassumption. }
      eapply (from_2480c EPI); try eassumption. lia. }
    eapply (from_2480c EPI); try eassumption. lia.
  Qed.
End Proof.

Section Top.
  Hypothesis memset_spec : memset_stmt.

  Lemma large_add_from_spec : large_add_from_stmt.
  Proof.
    unfold large_add_from_stmt. intros until start.
    intros ST ALIGN XL Hxl XC XLEN XAL YL Hyl Ha2 YLEN YAL YNZ YEND Ha3 START FIT CAP SEP1 SEP2 SEP3.
    subst a2 a3.
    eapply (body_ok memset_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m ws ys len ylen start
              (Z.to_nat len) (Z.to_nat ylen) (Z.to_nat start)); try eassumption; try lia.
    all: try exact CAP.
    eapply (epilogue memset_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m ws ys len ylen start
              (Z.to_nat len) (Z.to_nat ylen) (Z.to_nat start)); try eassumption; try lia.
    all: try exact CAP.
  Qed.
End Top.
End P_large_add_from.

Module P_long_mul_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs.StoreFast.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl P_memcpy_stmt P_memcpy.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow5.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memcpy_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memcpy OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_lib_closed.P_large_add_from_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow5.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_long_mul_A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma P_LP5_tbl : table_b PSEGS 0x15aa0 8 (fun v => le8 (Z_to_bv 64 v)) LARGE_POW5 = true.
Proof. vm_compute. reflexivity. Qed.

Section Iter.
  (* [comment removed for export] *)
  Hypothesis large_add_from_spec : large_add_from_stmt.
  Variables (sp va gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (ws zw : list word) (len : Z) (j1 : list byte).
  Notation A := (bv_unsigned va).
  Notation SP' := (bv_unsigned sp + -1120)%Z.
  Notation X := (bval ws (Z.to_nat len)).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis A8 : (A mod 8 = 0)%Z.
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SEP : (A + 498 <= bv_unsigned sp - 1168 \/ bv_unsigned sp <= A)%Z.
  Hypothesis SPLO : (0x22000 <= bv_unsigned sp - 1168)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.
  Hypothesis AROD : (A + 498 <= 0x10000 \/ 0x22000 <= A)%Z.
  Hypothesis NORM : bnorm ws (Z.to_nat len).
  Hypothesis CAP : (X * 5 ^ 135 < BIG_CAP)%Z.
  Hypothesis Lzw : length zw = 62%nat.
  Hypothesis Hzw : forall j, (j < Z.to_nat len)%nat -> nth j zw w0 = nth j ws w0.

  Definition iter_W : list ivl := [(bv_unsigned sp - 1168, bv_unsigned sp + -1120); (bv_unsigned sp + -1112, bv_unsigned sp + -614); (A, A + 498)]%Z.

  Definition iter_post (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word)
                      (m' : word -> option byte) (wsk : list word) (lenk : Z) (ziw : list word) (zil : Z),
      ms' = MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 0x15aa0) x10 x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 5) (Z_to_bv 64 (8 * len)) (Z_to_bv 64 5) (Z_to_bv 64 len) (Z_to_bv 64 (bv_unsigned sp + -1112))
                   (Z_to_bv 64 (len * 281474976710656)) (Z_to_bv 64 62) (Z_to_bv 64 len) (Z_to_bv 64 61) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x26648) fc None m' (seg_rom PSEGS)
      /\ munch iter_W m0 m'
      /\ wmono PSEGS m0 m'
      /\ u64arr PSEGS m' A wsk /\ length wsk = 62%nat
      /\ rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 lenk)] /\ (0 <= lenk <= 62)%Z
      /\ bval wsk (Z.to_nat lenk) = (X * 5 ^ 135)%Z
      /\ u64arr PSEGS m' (bv_unsigned sp + -1112) ziw /\ length ziw = 62%nat
      /\ rw_cells PSEGS m' (bv_unsigned sp + -616) [C2 (Z_to_bv 64 zil); CB 6 j1]
      /\ u64arr PSEGS m' (bv_unsigned sp + -608) zw
      /\ stk PSEGS m' (bv_unsigned sp - 1168) SP'
      /\ pristine m' 0x10000 0x22000.

  (* [comment removed for export] *)
  Definition iter_ok (n : nat) : Prop :=
    forall (m0 : word -> option byte) (k : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (wsk : list word) (lenk : Z) (ziw : list word) (zil : Z),
      (Z.to_nat (5 - k) = n)%nat -> (1 <= k <= 4)%Z ->
      u64arr PSEGS m A wsk -> length wsk = 62%nat ->
      rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bval wsk (Z.to_nat lenk) = (X * zsum LARGE_POW5 (Z.to_nat k))%Z ->
      u64arr PSEGS m (bv_unsigned sp + -1112) ziw -> length ziw = 62%nat ->
      rw_cells PSEGS m (bv_unsigned sp + -616) [C2 (Z_to_bv 64 zil); CB 6 j1] ->
      u64arr PSEGS m (bv_unsigned sp + -608) zw ->
      stk PSEGS m (bv_unsigned sp - 1168) SP' ->
      pristine m 0x10000 0x22000 ->
      munch iter_W m0 m -> wmono PSEGS m0 m ->
      evt PSEGS (iter_post m0)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 0x15aa0) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 5) (Z_to_bv 64 (8 * len)) (Z_to_bv 64 k) (Z_to_bv 64 len) (Z_to_bv 64 (bv_unsigned sp + -1112))
                 (Z_to_bv 64 (len * 281474976710656)) (Z_to_bv 64 62) (Z_to_bv 64 len) (Z_to_bv 64 61) x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26584) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  #[using="large_add_from_spec L62 A8 AL SEP SPLO Rsp HA AROD CAP Lzw"] Lemma from_24734 : forall (n : nat), iter_ok n ->
    forall (k yk : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m0 m : word -> option byte) (wsk : list word) (lenk : Z) (ziw : list word) (zil : Z),
      (Z.to_nat (5 - (k + 1)) = n)%nat -> (1 <= k <= 4)%Z ->
      yk = nth (Z.to_nat k) LARGE_POW5 0%Z ->
      u64arr PSEGS m A wsk -> length wsk = 62%nat ->
      rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bval wsk (Z.to_nat lenk) = (X * zsum LARGE_POW5 (Z.to_nat k))%Z ->
      u64arr PSEGS m (bv_unsigned sp + -1112) ziw -> length ziw = 62%nat ->
      rw_cells PSEGS m (bv_unsigned sp + -616) [C2 (Z_to_bv 64 zil); CB 6 j1] ->
      (0 <= zil)%Z -> (zil + k <= 62)%Z ->
      bval ziw (Z.to_nat zil) = (yk * X)%Z ->
      u64arr PSEGS m (bv_unsigned sp + -608) zw ->
      stk PSEGS m (bv_unsigned sp - 1168) SP' ->
      pristine m 0x10000 0x22000 ->
      munch iter_W m0 m -> wmono PSEGS m0 m ->
      evt PSEGS (iter_post m0)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 0x15aa0) (Z_to_bv 64 zil) x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 5) (Z_to_bv 64 (8 * len)) (Z_to_bv 64 k) (Z_to_bv 64 len) (Z_to_bv 64 (bv_unsigned sp + -1112))
                 (Z_to_bv 64 (len * 281474976710656)) (Z_to_bv 64 62) (Z_to_bv 64 len) (Z_to_bv 64 61) (Z_to_bv 64 yk) x28 x29 x30 x31)
            F (Z_to_bv 64 0x26624) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (large_add_from_spec L62 A8 AL SEP SPLO Rsp HA AROD CAP Lzw : LiaFast.U) => LiaFast.u0).
    intros n IH k yk x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m0 m wsk lenk ziw zil
           Hn Hk Hyk XA Lx LENC Hlenk VAL ZIA Lzi ZIL Hzil0 ROOM VZI ZA ST PR MU WM.
    cbv delta [iter_W] in MU.
    pose proof (LP5_nth_range (Z.to_nat k) ltac:(lia)) as Ryk. rewrite <- Hyk in Ryk.
    pose proof (LP5_zsum_step_le (Z.to_nat k) ltac:(lia)) as STEP. rewrite <- Hyk in STEP. rewrite Z2Nat.id in STEP by lia.
    pose proof (LP5_zsum_mono (Z.to_nat k) ltac:(lia)) as MONO.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite (Z.mod_small zil 65536) by lia.
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit SP' ltac:(lia)) as ULs. pose proof (unsigned_lit (bv_unsigned sp + -1112) ltac:(lia)) as ULy.
    step. (* [comment removed for export] *)
    call large_add_from_spec.
    1:{ eapply stk_at_eq; [exact ST | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia]. }
    1:{ rewrite unsigned_lit by lia. Z.div_mod_to_equations. lia. }
    1:{ exact XA. } 1:{ exact Lx. } 1:{ exact LENC. } 1:{ exact Hlenk. } 1:{ exact A8. }
    1:{ eapply u64arr_at_eq; [exact ZIA | rewrite unsigned_lit by lia; lia]. } 1:{ exact Lzi. }
    1:{ reflexivity. } 1:{ lia. }
    1:{ rewrite unsigned_lit by lia. Z.div_mod_to_equations. lia. } 1:{ rewrite unsigned_lit by lia. lia. } 1:{ rewrite unsigned_lit by lia. lia. }
    1:{ reflexivity. } 1:{ lia. } 1:{ lia. }
    1:{ rewrite VAL, VZI. unfold BIG_CAP in *. apply (cap_step X _ yk _ (5 ^ 135)); try lia; apply Z.pow_nonneg; lia. }
    1:{ rewrite !unsigned_lit by lia. lia. } 1:{ rewrite !unsigned_lit by lia. lia. } 1:{ rewrite !unsigned_lit by lia. lia. }
    rewrite ?ULs, ?ULy in *.
    step. (* [comment removed for export] *)
    if_not_taken.
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hmore.
    - cond_cleanup Hmore.
      replace (SP' - 48)%Z with (bv_unsigned sp - 1168)%Z in * by lia.
      eapply (IH m0 (k + 1)%Z); try eassumption; try lia.
      all: lazymatch goal with
           | |- bval _ _ = _ =>
               match goal with H : bval ?a ?b = (bval ?c ?d + bval ?e ?f * _)%Z |- _ => rewrite H end;
               rewrite VAL, VZI; replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia; rewrite zsum_S, <- Hyk; rewrite Z2Nat.id by lia; ring
           | |- munch _ _ _ => cbv delta [iter_W]; assumption
           | |- stk _ _ _ _ => assumption
           end.
    - cond_cleanup Hmore.
      apply evt_done. unfold iter_post.
      do 17 eexists. eexists _, _, _, ziw, zil.
      split. { assert (k = 4)%Z as -> by lia. reflexivity. }
      split. { cbv delta [iter_W]. assumption. } split. { assumption. }
      split. { eassumption. } split. { assumption. } split. { eassumption. } split. { lia. }
      split. { match goal with H : bval ?w (Z.to_nat ?l) = (bval wsk _ + _)%Z |- bval ?w _ = _ => rewrite H end.
               rewrite VAL, VZI. rewrite <- LP5_zsum_5. assert (k = 4)%Z as -> by lia.
               change 5%nat with (S (Z.to_nat 4)). rewrite zsum_S, <- Hyk. change (Z.of_nat (Z.to_nat 4)) with 4%Z. ring. }
      split. { assumption. } split. { assumption. } split. { assumption. } split. { assumption. }
      split. { replace (SP' - 48)%Z with (bv_unsigned sp - 1168)%Z in * by lia. assumption. }
      assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="large_add_from_spec L62 Hlen A8 AL SEP SPLO Rsp HA AROD NORM CAP Lzw"] Lemma from_246cc : forall (n : nat), iter_ok n ->
    forall (k yk : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m0 m : word -> option byte) (wsk : list word) (lenk : Z) (ziw : list word) (zil : Z),
      (Z.to_nat (5 - (k + 1)) = n)%nat -> (1 <= k <= 4)%Z ->
      yk = nth (Z.to_nat k) LARGE_POW5 0%Z ->
      u64arr PSEGS m A wsk -> length wsk = 62%nat ->
      rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bval wsk (Z.to_nat lenk) = (X * zsum LARGE_POW5 (Z.to_nat k))%Z ->
      u64arr PSEGS m (bv_unsigned sp + -1112) ziw -> length ziw = 62%nat ->
      (forall j, (j < Z.to_nat len)%nat -> nth j ziw w0 = nth j ws w0) ->
      rw_cells PSEGS m (bv_unsigned sp + -616) [C2 (Z_to_bv 64 zil); CB 6 j1] ->
      u64arr PSEGS m (bv_unsigned sp + -608) zw ->
      stk PSEGS m (bv_unsigned sp - 1168) SP' ->
      pristine m 0x10000 0x22000 ->
      munch iter_W m0 m -> wmono PSEGS m0 m ->
      evt PSEGS (iter_post m0)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 0x15aa0) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 5) (Z_to_bv 64 (8 * len)) (Z_to_bv 64 k) (Z_to_bv 64 len) (Z_to_bv 64 (bv_unsigned sp + -1112))
                 (Z_to_bv 64 (len * 281474976710656)) (Z_to_bv 64 62) (Z_to_bv 64 len) (Z_to_bv 64 61) (Z_to_bv 64 yk) x28 x29 x30 x31)
            F (Z_to_bv 64 0x265bc) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (large_add_from_spec L62 Hlen A8 AL SEP SPLO Rsp HA AROD NORM CAP Lzw : LiaFast.U) => LiaFast.u0).
    intros n IH k yk x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m0 m wsk lenk ziw zil
           Hn Hk Hyk XA Lx LENC Hlenk VAL ZIA Lzi AGR ZIL ZA ST PR MU WM.
    cbv delta [iter_W] in MU.
    pose proof (LP5_nth_range (Z.to_nat k) ltac:(lia)) as Ryk. rewrite <- Hyk in Ryk.
    pose proof (LP5_zsum_step_le (Z.to_nat k) ltac:(lia)) as STEP. rewrite <- Hyk in STEP. rewrite Z2Nat.id in STEP by lia.
    pose proof (LP5_zsum_mono (Z.to_nat k) ltac:(lia)) as MONO.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    assert (XZ : bval ziw (Z.to_nat len) = X) by (apply bval_agree; exact AGR).
    assert (P64k : (1 <= 2 ^ (64 * k))%Z). { pose proof (pow64_pos (Z.to_nat k)) as P. rewrite Z2Nat.id in P by lia. lia. }
    pose proof (cap_yk X _ yk _ (5 ^ 135) BIG_CAP X0 (proj1 MONO) ltac:(lia) P64k STEP CAP) as [CAP1 CAP2].
    unfold BIG_CAP in CAP2.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite ?Z.add_0_l. rewrite (Z.mod_small len 65536) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz.
    - (* [comment removed for export] *)
      cond_cleanup Hz.
      step. (* [comment removed for export] *)
      match goal with H : rw_cells PSEGS _ (bv_unsigned sp + -616) _ |- _ =>
        replace (Z_to_bv 64 len) with (Z_to_bv 64 0) in H by (rewrite Hz; reflexivity) end.
      eapply (from_24734 n IH k yk); try eassumption; try lia.
      all: lazymatch goal with
           | |- munch _ _ _ => cbv delta [iter_W]; assumption
           | |- bval _ _ = _ => rewrite Hz in XZ |- *; change (Z.to_nat 0) with 0%nat in *; rewrite bval_0; rewrite <- XZ, bval_0; ring
           end.
    - cond_cleanup Hz.
      step. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
      zstep. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      replace (bv_unsigned sp + -1112 + len * 8)%Z with (bv_unsigned sp + -1112 + 8 * len)%Z by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      call (smul2_run x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 88736) (Z_to_bv 64 len) (Z_to_bv 64 len) (Z_to_bv 64 (len * 8))
                (Z_to_bv 64 5) (Z_to_bv 64 (8 * len)) (Z_to_bv 64 k) (Z_to_bv 64 len) (Z_to_bv 64 (bv_unsigned sp + -1112))
                (Z_to_bv 64 (len * 281474976710656)) (Z_to_bv 64 62) (Z_to_bv 64 len) (Z_to_bv 64 61) x28 x29 x30 x31
                F fc mc (bv_unsigned sp + -1112) yk ziw len Lzi ltac:(lia) ltac:(lia) ltac:(lia) _ _ ziw ZIA Lzi (fun j => eq_refl))
      end.
      rename x into c'.
      match goal with H : smul_inv _ _ _ _ _ |- _ => rename H into INV end.
      match goal with H : u64arr PSEGS _ (bv_unsigned sp + -1112) ?cur |- _ => rename H into CUR end.
      pose proof INV as (Hv & Hag & Hc' & Hlc).
      step. (* [comment removed for export] *)
      if_cases Hcz.
      + (* [comment removed for export] *)
        cond_cleanup Hcz.
        eapply (from_24734 n IH k yk); try eassumption; try lia.
        all: lazymatch goal with
             | |- munch _ _ _ => cbv delta [iter_W]; assumption
             | |- bval _ _ = _ =>
                 rewrite <- XZ; symmetry; apply (smul_inv_finish_nocarry ziw _ yk); rewrite <- Hcz; exact INV
             | |- (_ <= 62)%Z =>
                 (* [comment removed for export] *)
                 destruct NORM as [N0|NT]; [lia|];
                 pose proof (bnorm_lower ws (Z.to_nat len) (or_intror NT) ltac:(lia)) as LO;
                 replace (Z.of_nat (Z.to_nat len - 1)) with (len - 1)%Z in LO by lia;
                 pose proof (room_nocarry X yk k (len - 1) ltac:(lia) ltac:(lia) LO ltac:(lia) CAP2); lia
             end.
      + (* [comment removed for export] *)
        cond_cleanup Hcz.
        pose proof (smul_carry_room ziw _ yk _ _ INV ltac:(lia) ltac:(rewrite XZ; exact CAP1)) as ROOM1.
        step. (* [comment removed for export] *)
        if_not_taken.
        zstep. (* [comment removed for export] *)
        replace (bv_unsigned sp + -1112 + len * 8)%Z with (bv_unsigned sp + -1112 + 8 * len)%Z by lia.
        zstep. (* [comment removed for export] *)
        pose proof (u64arr_store_ok PSEGS _ _ _ len (Z_to_bv 64 (bv_unsigned sp + -1112 + 8 * len)) CUR ltac:(rewrite Hlc, Lzi; lia) eq_refl) as SOK.
        step. (* [comment removed for export] *)
        pose proof (u64arr_write PSEGS _ _ _ len (Z_to_bv 64 c') CUR ltac:(rewrite Hlc, Lzi; lia)) as CUR2.
        store_done.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        eapply (from_24734 n IH k yk); try eassumption; try lia.
        all: lazymatch goal with
             | |- munch _ _ _ => cbv delta [iter_W]; assumption
             | |- length _ = _ => rewrite upd_length, Hlc; exact Lzi
             | |- bval _ _ = _ =>
                 replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia; rewrite <- XZ;
                 apply (smul_inv_finish_carry ziw _ yk); [exact INV| rewrite Lzi; lia]
             | |- (_ <= 62)%Z =>
                 (* [comment removed for export] *)
                 rewrite XZ in Hv; rewrite Z2Nat.id in Hv by lia;
                 pose proof (room_carry _ c' (yk * X) k len ltac:(lia) ltac:(lia) (bval_nonneg _ _) ltac:(lia) Hv CAP2); lia
             end.
  Qed.

  #[using="large_add_from_spec L62 Hlen A8 AL SEP SPLO Rsp HA AROD NORM CAP Lzw Hzw"] Lemma iter_body : forall n, iter_ok n -> iter_ok (S n).
  Proof. LiaFast.lf_pins (fun (large_add_from_spec L62 Hlen A8 AL SEP SPLO Rsp HA AROD NORM CAP Lzw Hzw : LiaFast.U) => LiaFast.u0).
    intros n IH. unfold iter_ok.
    intros m0 k x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 m wsk lenk ziw zil
           Hn Hk XA Lx LENC Hlenk VAL ZIA Lzi ZIL ZA ST PR MU WM.
    cbv delta [iter_W] in MU.
    pose proof (LP5_nth_range (Z.to_nat k) ltac:(lia)) as Ryk.
    remember (nth (Z.to_nat k) LARGE_POW5 0%Z) as yk eqn:Hyk.
    zstep. (* [comment removed for export] *)
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
    zstep. (* [comment removed for export] *)
    pose proof (table_read PSEGS (fun v => le8 (Z_to_bv 64 v)) LARGE_POW5 0x15aa0 8 m 0x10000 0x22000
                  P_LP5_tbl PR ltac:(lia) ltac:(cbn; lia) k ltac:(cbn; lia)) as RD.
    change (Z.of_nat 8) with 8%Z in RD. rewrite <- Hyk in RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    if_cases Hz.
    - (* [comment removed for export] *)
      cond_cleanup Hz.
      step. (* [comment removed for export] *)
      eapply (from_246cc n IH k yk); try eassumption; try lia.
      all: lazymatch goal with
           | |- munch _ _ _ => cbv delta [iter_W]; assumption
           | |- forall j, _ -> _ => intros j Hj; exfalso; nia
           end.
    - cond_cleanup Hz.
      assert (Hl0 : (0 < len)%Z) by nia.
      zstep. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      destruct (Z_of_nat_complete len ltac:(lia)) as [ln El].
      name_mem mc1.
      pose proof (u64arr_prefix_bytes PSEGS mc1 _ zw ln ltac:(rewrite Lzw; lia) ZA) as SRC.
      destruct (u64arr_split3 PSEGS mc1 _ ziw 0 ln ltac:(rewrite Lzi; lia) ZIA) as (_ & U2 & U3).
      pose proof (u8arr_of_u64arr PSEGS _ _ _ U2) as DST.
      destruct (u64arr_len_split3 ziw 0 ln ltac:(rewrite Lzi; lia)) as (_ & _ & Ll & Lr). rewrite Lzi in Lr.
      cbn [firstn skipn Nat.add app] in DST, U3, Ll, Lr.
      clear ZIA U2.
      pose proof (unsigned_lit (bv_unsigned sp + -1112) ltac:(lia)) as UL1.
      pose proof (unsigned_lit (bv_unsigned sp + -608) ltac:(lia)) as UL2.
      pose proof (unsigned_lit (8 * len) ltac:(lia)) as UL3.
      step. (* [comment removed for export] *)
      call memcpy_spec.
      1:{ eapply bytes_at_at_eq; [exact SRC| rewrite unsigned_lit by lia; lia]. }
      1:{ eapply u8arr_at_eq; [exact DST| rewrite unsigned_lit by lia; lia]. }
      1:{ rewrite !u64s_length, Ll, firstn_length, Lzw. lia. }
      1:{ rewrite UL3, u64s_length, firstn_length, Lzw. lia. }
      1:{ rewrite UL1, UL2, UL3. lia. }
      1:{ rewrite UL1, UL3. lia. }
      1:{ rewrite UL2, UL3. lia. }
      1:{ rewrite unsigned_lit by lia. reflexivity. }
      rewrite ?UL1, ?UL2, ?UL3 in *.
      name_mem m2.
      pose proof (u64arr_of_u8arr PSEGS m2 (bv_unsigned sp + -1112) ln (u64s (firstn ln zw)) MI
                    ltac:(rewrite u64s_length, firstn_length, Lzw; lia)) as MID.
      rewrite words_of_bytes_u64s in MID. clear MI POST.
      assert (Lm : length (firstn ln zw) = ln) by (rewrite firstn_length, Lzw; lia).
      assert (ZIA2 : u64arr PSEGS m2 (bv_unsigned sp + -1112) (firstn ln zw ++ skipn ln ziw)).
      { apply u64arr_app. rewrite Lm. split; [exact MID|].
        eapply u64arr_at_eq; [exact U3| lia]. }
      clear MID U3.
      step. (* [comment removed for export] *)
      rewrite zx16_lit_small by lia.
      step. (* [comment removed for export] *)
      eapply (from_246cc n IH k yk); try eassumption; try lia.
      all: lazymatch goal with
           | |- munch _ _ _ => cbv delta [iter_W]; assumption
           | |- length _ = _ => rewrite app_length, Lm, Lr; lia
           | |- forall j, _ -> _ => intros j Hj; rewrite app_nth1 by (rewrite Lm; lia);
                                   rewrite <- (firstn_skipn ln zw) in Hzw; rewrite <- (Hzw j Hj); symmetry; apply app_nth1; rewrite Lm; lia
           end.
  Qed.

  #[using="large_add_from_spec L62 Hlen A8 AL SEP SPLO Rsp HA AROD NORM CAP Lzw Hzw"] Lemma iter_loop : forall n, iter_ok n.
  Proof. LiaFast.lf_pins (fun (large_add_from_spec L62 Hlen A8 AL SEP SPLO Rsp HA AROD NORM CAP Lzw Hzw : LiaFast.U) => LiaFast.u0). induction n as [|n IHn]. - unfold iter_ok; intros; exfalso; lia. - apply iter_body; exact IHn. Qed.
End Iter.
End P_long_mul_B.

Module P_long_mul.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs.StoreFast.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl ImgFacts P_memcpy_stmt P_memcpy.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow5.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow5.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.ImgFacts OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memcpy_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memcpy OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_lib_closed.P_large_add_from_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_long_mul_A OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_lib_closed.P_long_mul_B.
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

Definition boxed (P : Prop) : Prop := P.

Section Main.
  Hypothesis large_add_from_spec : large_add_from_stmt.

  Section From60.
  Variables (ra sp gp tp a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s0 s1 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (ws zw : list word) (len : Z) (j0 j1 j3 : list byte).
  Notation A := (bv_unsigned a0).
  Notation SP' := (bv_unsigned sp + -1120)%Z.
  Notation X := (bval ws (Z.to_nat len)).
  Notation POST := (long_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A ws len m).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis A8 : (A mod 8 = 0)%Z.
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SEP : (A + 498 <= bv_unsigned sp - 1168 \/ bv_unsigned sp <= A)%Z.
  Hypothesis SPLO : (0x22000 <= bv_unsigned sp - 1168)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.
  Hypothesis AROD : (A + 498 <= 0x10000 \/ 0x22000 <= A)%Z.
  Hypothesis NORM : bnorm ws (Z.to_nat len).
  Hypothesis CAP : (X * 5 ^ 135 < BIG_CAP)%Z.
  Hypothesis Lzw : length zw = 62%nat.
  Hypothesis Hzw : forall j, (j < Z.to_nat len)%nat -> nth j zw w0 = nth j ws w0.

  (* [comment removed for export] *)
  #[using="large_add_from_spec L62 Hlen A8 AL SEP SPLO Rsp HA AROD NORM CAP Lzw Hzw"] Lemma from_24660 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (m1 : word -> option byte) (wsk : list word) (lenk : Z) (ziw : list word) (j5 : list byte),
      u64arr PSEGS m1 A wsk -> length wsk = 62%nat ->
      rw_cells PSEGS m1 (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bval wsk (Z.to_nat lenk) = (X * nth 0 LARGE_POW5 0%Z)%Z ->
      u64arr PSEGS m1 (bv_unsigned sp + -1112) ziw -> length ziw = 62%nat ->
      rw_cells PSEGS m1 (bv_unsigned sp + -616) [CB 2 j0; CB 6 j1] ->
      u64arr PSEGS m1 (bv_unsigned sp + -608) zw ->
      rw_cells PSEGS m1 (bv_unsigned sp + -112) [C2 (Z_to_bv 64 len); CB 6 j3] ->
      rw_cells PSEGS m1 (bv_unsigned sp + -1120) [CB 8 j5] ->
      rw_cells PSEGS m1 (bv_unsigned sp + -104)
        [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk PSEGS m1 (bv_unsigned sp - 1168) SP' ->
      pristine m1 0x10000 0x22000 ->
      munch [(bv_unsigned sp - 1168, bv_unsigned sp); (A, A + 498)]%Z m m1 -> wmono PSEGS m m1 ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 a0 (Z_to_bv 64 0x15aa0) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 5) x19 x20 (Z_to_bv 64 len) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26550) fc None m1 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (large_add_from_spec L62 Hlen A8 AL SEP SPLO Rsp HA AROD NORM CAP Lzw Hzw : LiaFast.U) => LiaFast.u0).
    intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m1 wsk lenk ziw j5
           XA Lx LENC Hlenk VAL1 ZIA Lzi ZIL ZA ZL FR0 FRsv ST PR MU WM.
    destruct (rw_cells_CB2_C2 _ _ _ _ _ ZIL) as (zil & Hzil & ZIL'). clear ZIL. rename ZIL' into ZIL.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_taken.
    zstep. (* [comment removed for export] *)
    rewrite shl51_shr48m by lia.
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite (Z.shiftl_mul_pow2 len 48) by lia. change (2 ^ 48)%Z with 281474976710656%Z.
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite (Z.shiftr_div_pow2 _ 48) by lia. change (2 ^ 48)%Z with 281474976710656%Z. rewrite Z.div_mul by lia.
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    name_mem m4.
    call (iter_loop large_add_from_spec sp a0 gp tp F fc ws zw len j1 L62 Hlen A8 AL SEP SPLO Rsp HA AROD NORM CAP Lzw Hzw
             (Z.to_nat 4) m4 1%Z).
    all: try lia.
    1:{ exact XA. } 1:{ exact Lx. } 1:{ exact LENC. } 1:{ exact Hlenk. }
    1:{ rewrite VAL1. change (Z.to_nat 1) with 1%nat. rewrite zsum_S. cbn [zsum Z.of_nat Z.mul]. rewrite Z.pow_0_r. ring. }
    1:{ exact ZIA. } 1:{ exact Lzi. } 1:{ exact ZIL. } 1:{ exact ZA. } 1:{ exact ST. } 1:{ exact PR. }
    1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    (* [comment removed for export] *)
    name_mem m5.
    match goal with H : rw_cells PSEGS m5 (A + 496) [C2 (Z_to_bv 64 ?l)] |- _ => rename H into LENC5; rename l into len5 end.
    match goal with H : u64arr PSEGS m5 A ?w |- _ => rename H into XA5; rename w into ws5 end.
    step. (* [comment removed for export] *)
    rewrite zx16_lit_small by lia.
    match goal with H : length ws5 = 62%nat |- _ => rename H into L5 end.
    call norm_run.
    all: try lia.
    1:{ exact L5. } 1:{ exact XA5. } 1:{ exact LENC5. }
    name_mem m6.
    (* [comment removed for export] *)
    do 15 step.
    (* [comment removed for export] *)
    match goal with H : stk PSEGS m6 _ _ |- _ => rename H into ST6 end.
    release_frame FR0 ST6 (bv_unsigned sp + -1112)%Z.
    match goal with H : u64arr PSEGS m6 (bv_unsigned sp + -1112) ?w |- _ =>
      pose proof (rw_cells_of_u64arr _ _ _ _ H) as ZIc; clear H;
      match goal with L : length w = 62%nat |- _ => rewrite L in ZIc end end.
    release_frame ZIc ST6 (bv_unsigned sp + -616)%Z.
    match goal with H : rw_cells PSEGS m6 (bv_unsigned sp + -616) _ |- _ => release_frame H ST6 (bv_unsigned sp + -608)%Z end.
    match goal with H : u64arr PSEGS m6 (bv_unsigned sp + -608) ?w |- _ =>
      pose proof (rw_cells_of_u64arr _ _ _ _ H) as ZAc; clear H; rewrite Lzw in ZAc end.
    release_frame ZAc ST6 (bv_unsigned sp + -112)%Z.
    release_frame ZL ST6 (bv_unsigned sp + -104)%Z.
    release_frame FRsv ST6 (bv_unsigned sp).
    unfold long_mul_post. finish.
    all: try eassumption. all: try lia.
  Qed.
  End From60.

  #[using="large_add_from_spec"] Lemma long_mul_spec : long_mul_stmt.
  Proof. LiaFast.lf_pins (fun (large_add_from_spec : LiaFast.U) => LiaFast.u0).
    unfold long_mul_stmt. intros until len. intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 NORM Ha1 Ha2 CAP SEP.
    subst a1 a2. cbv delta [P_LARGE_POW5_ADDR].
    pose proof (munch_refl [(bv_unsigned sp - 1168, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 498)]%Z m) as MU.
    pose proof (wmono_refl PSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    pose proof (u64arr_outside_rodata_P m _ _ PR LIMBS ltac:(rewrite L62; lia)) as AROD. rewrite L62 in AROD.
    pose proof (rw_cells_outside_rodata_P m _ _ PR LENC ltac:(cbn; lia)) as CROD. cbn [cells_size csize Nat.add] in CROD.
    assert (HA : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + 498 <= 2 ^ 64)%Z) by lia.
    assert (AROD' : (bv_unsigned a0 + 498 <= 0x10000 \/ 0x22000 <= bv_unsigned a0)%Z) by lia.
    clear Bl Bc AROD CROD. rename AROD' into AROD.
    (* [comment removed for export] *)
    carve_frame 1120%nat ST.
    apply (rw_cells_split_CB PSEGS m _ [] 1120%nat junk [] [8;496;2;6;496;2;6;104]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    chunk_split FR 7%nat FRlo FRsv.
    chunk_split FRlo 1%nat FR0 FR1. chunk_split FR1 1%nat ZI FR2. chunk_split FR2 2%nat ZIL FR3.
    chunk_split FR3 1%nat ZZ ZL.
    match type of ZI with context [CB 496 ?j] => remember j as zij eqn:E1 in ZI; clear E1 end.
    match type of ZZ with context [CB 496 ?j] => remember j as zj eqn:E1 in ZZ; clear E1 end.
    match type of FRsv with context [CB 104 ?j] => remember j as svj eqn:E1 in FRsv; clear E1 end.
    match type of ZIL with context [CB 6 ?j] => remember j as j1 eqn:E1 in ZIL; clear E1 end.
    match type of ZIL with context [CB 2 ?j] => remember j as j0 eqn:E1 in ZIL; clear E1 end.
    match type of ZL with context [CB 6 ?j] => remember j as j3 eqn:E1 in ZL; clear E1 end.
    match type of ZL with context [CB 2 ?j] => remember j as j4 eqn:E1 in ZL; clear E1 end.
    match type of FR0 with context [CB 8 ?j] => remember j as j5 eqn:E1 in FR0; clear E1 end.
    clear junk.
    change (CB 496 zij) with (CB (8 * 62) zij) in ZI. change (CB 496 zj) with (CB (8 * 62) zj) in ZZ.
    destruct (u64arr_of_rw_cells PSEGS _ _ 62 _ ZI) as (ziw & Lzi & ZIA). clear ZI.
    destruct (u64arr_of_rw_cells PSEGS _ _ 62 _ ZZ) as (zw0 & Lz0 & ZA). clear ZZ.
    do 14 step. (* [comment removed for export] *)
    step. step. step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite zx16_lit_small by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    if_cases Hz.
    - (* [comment removed for export] *)
      cond_cleanup Hz.
      step. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      if_taken.
      rewrite Z.add_0_l in *.
      eapply (from_24660 ra sp gp tp a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 s1 F fc m ws zw0 len j0 j1 j3);
        try eassumption; try lia.
      all: first [ intros j Hj; exfalso; lia
                 | rewrite Hz; change (Z.to_nat 0) with 0%nat; rewrite bval_0; ring ].
    - (* [comment removed for export] *)
      cond_cleanup Hz.
      destruct (Z_of_nat_complete len ltac:(lia)) as [ln El].
      zstep. (* [comment removed for export] *)
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
      zstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      name_mem mc1.
      pose proof (u64arr_prefix_bytes PSEGS mc1 _ ws ln ltac:(rewrite L62; lia) LIMBS) as SRC.
      destruct (u64arr_split3 PSEGS mc1 _ zw0 0 ln ltac:(rewrite Lz0; lia) ZA) as (_ & U2 & U3).
      pose proof (u8arr_of_u64arr PSEGS _ _ _ U2) as DST.
      destruct (u64arr_len_split3 zw0 0 ln ltac:(rewrite Lz0; lia)) as (_ & _ & Ll & Lr). rewrite Lz0 in Lr.
      cbn [firstn skipn Nat.add app] in DST, U3, Ll, Lr.
      clear ZA U2.
      pose proof (unsigned_lit (bv_unsigned sp + -608) ltac:(lia)) as UL2.
      pose proof (unsigned_lit (len * 8) ltac:(lia)) as UL3.
      step. (* [comment removed for export] *)
      call memcpy_spec.
      1:{ exact SRC. }
      1:{ eapply u8arr_at_eq; [exact DST| rewrite unsigned_lit by lia; lia]. }
      1:{ rewrite !u64s_length, Ll, firstn_length, L62. lia. }
      1:{ rewrite UL3, u64s_length, firstn_length, L62. lia. }
      1:{ rewrite UL2, UL3. lia. }
      1:{ rewrite UL2, UL3. lia. }
      1:{ rewrite UL3. lia. }
      1:{ rewrite unsigned_lit by lia. reflexivity. }
      rewrite ?UL2, ?UL3 in *.
      name_mem mc2.
      pose proof (u64arr_of_u8arr PSEGS mc2 (bv_unsigned sp + -608) ln (u64s (firstn ln ws)) MI
                    ltac:(rewrite u64s_length, firstn_length, L62; lia)) as MID.
      rewrite words_of_bytes_u64s in MID. clear MI POST.
      assert (Lm : length (firstn ln ws) = ln) by (rewrite firstn_length, L62; lia).
      assert (ZA2 : u64arr PSEGS mc2 (bv_unsigned sp + -608) (firstn ln ws ++ skipn ln zw0)).
      { apply u64arr_app. rewrite Lm. split; [exact MID|]. eapply u64arr_at_eq; [exact U3| lia]. }
      assert (Lzw : length (firstn ln ws ++ skipn ln zw0) = 62%nat) by (rewrite app_length, Lm, Lr; lia).
      assert (Hzw : forall j, (j < Z.to_nat len)%nat -> nth j (firstn ln ws ++ skipn ln zw0) w0 = nth j ws w0).
      { intros j Hj. rewrite app_nth1 by (rewrite Lm; lia). rewrite <- (firstn_skipn ln ws) at 2. symmetry. apply app_nth1. rewrite Lm; lia. }
      remember (firstn ln ws ++ skipn ln zw0) as zw eqn:Ezw. clear Ezw MID U3 Lm Lr Ll.
      step. (* [comment removed for export] *)
      rewrite zx16_lit_small by lia.
      step. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      rewrite ?Z.add_0_l.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      if_not_taken.
      (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
      zstep. (* [comment removed for export] *)
      replace (bv_unsigned a0 + len * 8)%Z with (bv_unsigned a0 + 8 * len)%Z by lia.
      step. (* [comment removed for export] *)
      pose proof (LP5_nth_range 0 ltac:(lia)) as Ry0. cbn [nth LARGE_POW5] in Ry0.
      name_mem mc3.
      call (@smul1_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               F fc mc3 (bv_unsigned a0) 1414648277510068013 ws len L62 ltac:(lia) ltac:(lia) HA a0).
      all: try lia.
      1:{ exact LIMBS. } 1:{ exact L62. } 1:{ intros j; reflexivity. }
      match goal with H : smul_inv _ _ _ _ ?c |- _ => rename H into INV1; rename c into c1 end.
      match goal with H : u64arr PSEGS _ (bv_unsigned a0) ?cur |- _ => rename H into CUR1 end.
      pose proof INV1 as (Hv1 & Hag1 & Hc1 & Hlc1).
      pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
      assert (CAP1 : (1414648277510068013 * bval ws (Z.to_nat len) < BIG_CAP)%Z).
      { pose proof (LP5_zsum_step_le 0 ltac:(lia)) as ST0. cbn [zsum nth LARGE_POW5 Z.of_nat Z.mul] in ST0.
        unfold BIG_CAP in *. nia. }
      step. (* [comment removed for export] *)
      if_cases Hcz.
      + (* [comment removed for export] *)
        cond_cleanup Hcz.
        eapply (from_24660 ra sp gp tp a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 s1 F fc m ws zw len j0 j1 j3);
          try eassumption; try lia.
        cbn [nth LARGE_POW5]. rewrite (Z.mul_comm (bval ws _)). apply (smul_inv_finish_nocarry ws _ _ (Z.to_nat len)).
        rewrite <- Hcz. exact INV1.
      + (* [comment removed for export] *)
        cond_cleanup Hcz.
        pose proof (smul_carry_room ws _ _ _ _ INV1 ltac:(lia) CAP1) as ROOM1.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_not_taken.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          pose proof (u64arr_store_ok PSEGS mc _ _ len (Z_to_bv 64 (bv_unsigned a0 + 8 * len)) CUR1 ltac:(rewrite Hlc1, L62; lia) eq_refl) as SOK end.
        step. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
          pose proof (u64arr_write PSEGS mc _ _ len (Z_to_bv 64 c1) CUR1 ltac:(rewrite Hlc1, L62; lia)) as CUR2 end.
        store_done.
        zstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        eapply (from_24660 ra sp gp tp a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 s1 F fc m ws zw len j0 j1 j3);
          try eassumption; try lia.
        * rewrite upd_length, Hlc1. exact L62.
        * cbn [nth LARGE_POW5]. replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia.
          rewrite (Z.mul_comm (bval ws _)). apply (smul_inv_finish_carry ws _ _ (Z.to_nat len)); [exact INV1| rewrite L62; lia].
  Qed.
End Main.
End P_long_mul.

Module P_pow_closed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_memset_stmt P_memset.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow5.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow5.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow5.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow5_stmt P_pow5.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow10.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow10.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow5_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow10.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow10_stmt P_pow10 P_hi64_stmt P_hi64.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_hi64_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_positive_digit_comp_d.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memset_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_lib_closed.P_large_add_from_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_lib_closed.P_large_add_from OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_lib_closed.P_long_mul OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_large_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_large_mul OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5 OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10.P_shl_bits_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10.P_shl_bits OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5_stmt.P_shl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10.P_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10 OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_hi64_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_hi64 OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_hi64_stmt.P_ctlz_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_positive_digit_comp_d.P_ctlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)

Lemma P_large_add_from_closed : large_add_from_stmt.
Proof. exact (large_add_from_spec memset_spec). Qed.

Lemma P_long_mul_closed : long_mul_stmt.
Proof. exact (long_mul_spec P_large_add_from_closed). Qed.

Lemma P_large_mul_closed : large_mul_stmt.
Proof. exact (OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_large_mul.large_mul_spec P_long_mul_closed). Qed.

Lemma P_pow5_closed : pow5_stmt.
Proof. exact (pow5_spec P_large_mul_closed). Qed.

Lemma P_pow10_closed : pow10_stmt.
Proof. exact (pow10_spec P_pow5_closed). Qed.

Definition P_shl_bits_closed : shl_bits_stmt := shl_bits_spec.
Definition P_shl_closed : shl_stmt := OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10.P_shl.shl_spec.
Definition P_hi64_closed : hi64_stmt := hi64_spec.
Definition P_ctlz_closed : ctlz_stmt := ctlz_spec.
End P_pow_closed.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_positive_digit_comp_d P_negative_digit_comp_d P_positive_digit_comp_f P_negative_digit_comp_f P_slow_path_double P_slow_path_float.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_from_chars_double.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_from_chars_float.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_from_chars_double P_from_chars_float.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)

Definition P_parse_mantissa_closed : parse_mantissa_stmt :=
  OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spf_DC.P_parse_mantissa.parse_mantissa_spec OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spf_DC.P_small_mul.small_mul_spec.

Definition P_positive_digit_comp_d_closed : positive_digit_comp_d_stmt :=
  P_positive_digit_comp_d.positive_digit_comp_d_spec
    P_pow_closed.P_pow10_closed P_pow_closed.P_hi64_closed P_pow_closed.P_ctlz_closed.
Definition P_negative_digit_comp_d_closed : negative_digit_comp_d_stmt :=
  P_negative_digit_comp_d.negative_digit_comp_d_spec
    P_memset.memset_spec P_pow_closed.P_pow5_closed P_pow_closed.P_shl_closed.
Definition P_positive_digit_comp_f_closed : positive_digit_comp_f_stmt :=
  P_positive_digit_comp_f.positive_digit_comp_f_spec
    P_pow_closed.P_pow10_closed P_pow_closed.P_hi64_closed P_pow_closed.P_ctlz_closed.
Definition P_negative_digit_comp_f_closed : negative_digit_comp_f_stmt :=
  P_negative_digit_comp_f.negative_digit_comp_f_spec
    P_memset.memset_spec P_pow_closed.P_pow5_closed P_pow_closed.P_shl_closed.

Definition P_slow_path_double_closed : slow_path_double_stmt :=
  P_slow_path_double.slow_path_double_spec P_memset.memset_spec P_parse_mantissa_closed
    P_positive_digit_comp_d_closed P_negative_digit_comp_d_closed.
Definition P_slow_path_float_closed : slow_path_float_stmt :=
  P_slow_path_float.slow_path_float_spec P_positive_digit_comp_f_closed P_negative_digit_comp_f_closed.

Definition P_from_chars_double_closed : from_chars_double_stmt :=
  P_from_chars_double.from_chars_double_spec OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_parse_infnan_d.parse_infnan_d_spec P_slow_path_double_closed.
Definition P_from_chars_float_closed : from_chars_float_stmt :=
  P_from_chars_float.from_chars_float_spec OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_float.P_parse_infnan_f.parse_infnan_f_spec P_slow_path_float_closed.



Definition P_from_chars_int_closed : from_chars_int_stmt := OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_from_chars_int.from_chars_int_spec.
