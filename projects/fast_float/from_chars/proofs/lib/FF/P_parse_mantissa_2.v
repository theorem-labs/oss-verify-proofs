(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Wbig_tac Wbig_bigadd.

Module P_small_mul_stmt.
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

Definition small_mul_entry : Z := 0x25fd0.

Definition small_mul_W (A : Z) : list ivl := [(A, A + 498)]%Z.

Definition small_mul_post
    (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (A y : Z) (ws : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 a1 a2 a3 a4 a5 a6 a7 : word) (m' : word -> option byte) (ws' : list word) (len' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom PSEGS)
    /\ munch (small_mul_W A) m m'
    /\ wmono PSEGS m m'
    /\ u64arr PSEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (len <= len' <= len + 1 /\ len' <= 62)%Z
    /\ bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) * y)%Z
    /\ (y <> 0%Z -> bnorm ws (Z.to_nat len) -> bnorm ws' (Z.to_nat len')).

Definition small_mul_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z),
    u64arr PSEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells PSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z ->
    (bval ws (Z.to_nat len) * bv_unsigned a1 < BIG_CAP)%Z ->
    evt PSEGS (small_mul_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 F fc (bv_unsigned a0) (bv_unsigned a1) ws len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x25fd0) fc None m (seg_rom PSEGS)).
End P_small_mul_stmt.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_bigadd OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_small_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_stmt.

Module P_parse_mantissa_1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_bigadd OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_small_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition boxed (P : Prop) : Prop := P.

Section Proof.
  Set Default Proof Using "All".
  Hypothesis small_mul_spec : small_mul_stmt.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i : word).
  Variables (resv numv mdw dv : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (iptr fptr : word) (ibs fbs : list byte).
  Variables (ilen flen maxd : Z).
  Hypothesis Hilen : ilen = Z.of_nat (length ibs).
  Hypothesis Hflen : flen = Z.of_nat (length fbs).
  Hypothesis Hmaxd : maxd = bv_unsigned mdw.
  Hypothesis Hws : length ws = 62%nat.
  Hypothesis MAXD : (0 < maxd <= 769)%Z.
  Hypothesis XAL : (bv_unsigned resv mod 8 = 0)%Z.
  Hypothesis ALIGN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis INZ : (bv_unsigned iptr <> 0)%Z.
  Hypothesis IEND : (bv_unsigned iptr + ilen < 2^64)%Z.
  Hypothesis ILEN : (0 <= ilen < 2^40)%Z.
  Hypothesis FEND : (bv_unsigned fptr + flen < 2^64)%Z.
  Hypothesis FLEN : (0 <= flen < 2^40)%Z.
  Hypothesis FNULL : boxed (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z.
  Hypothesis FBS0 : boxed (bytes_at PSEGS m0 (bv_unsigned fptr) fbs).
  Hypothesis LAY0 : (0x22000 <= bv_unsigned sp - 144)%Z.
  Hypothesis LAY1 : (bv_unsigned sp <= bv_unsigned numv + 32)%Z.
  Hypothesis LAY2 : (bv_unsigned numv + 64 <= bv_unsigned resv)%Z.
  Hypothesis LAY3 : (bv_unsigned resv + 498 <= bv_unsigned dv)%Z.
  Hypothesis LAY4 : (bv_unsigned dv + 8 <= bv_unsigned iptr \/ 16 <= bv_unsigned iptr /\ bv_unsigned iptr + Z.of_nat (length ibs) <= bv_unsigned sp - 144)%Z.
  Hypothesis LAY5 : boxed (bv_unsigned fptr <> 0 -> bv_unsigned dv + 8 <= bv_unsigned fptr \/ 16 <= bv_unsigned fptr /\ bv_unsigned fptr + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z.

  Notation A := (bv_unsigned resv).
  Notation D := (bv_unsigned dv).
  Notation NP := (bv_unsigned numv).
  Notation IP := (bv_unsigned iptr).
  Notation FP := (bv_unsigned fptr).
  Notation SP := (bv_unsigned sp).
  Notation W := [((SP - 144)%Z, SP); (A, (A + 498)%Z); (D, (D + 8)%Z)].
  Notation POST := (parse_mantissa_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i F fc A D maxd ws m0).
  Notation FRHI m := (rw_cells PSEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells PSEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 resv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 dv) as RDv; unfold bv_modulus in RDv;
    pose proof (bv_unsigned_in_range 64 numv) as RN; unfold bv_modulus in RN;
    pose proof (bv_unsigned_in_range 64 iptr) as RI; unfold bv_modulus in RI;
    pose proof (bv_unsigned_in_range 64 fptr) as RF; unfold bv_modulus in RF;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp.

  (* [comment removed for export] *)
  Definition end_ok : Prop :=
    forall (lo : list cell) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      rw_cells PSEGS m (SP + -144) lo -> Z.of_nat (cells_size lo) = 40%Z ->
      FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono PSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd + 1)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 3)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25be4) fc None m (seg_rom PSEGS)).

  Lemma end_proof : end_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    unfold end_ok. intros until K. intros FRLO LOSZ FRH ST XL Hcur XC DG MU WM LEN DGB V KB. bounds.
    do 14 step.
    step. (* [comment removed for export] *)
    release_frame FRLO ST (bv_unsigned sp + -104)%Z.
    release_frame FRH ST (bv_unsigned sp).
    unfold parse_mantissa_post. finish.
    { exact XL. } { exact Hcur. } { exact XC. } { exact DG. } all: try lia.
    - unfold boxed in V. destruct V as [BN _]. exact BN.
    - unfold boxed in V. destruct V as [_ BV].
      eapply Z.lt_le_trans; [exact BV|]. apply Z.pow_le_mono_r; lia.
  Qed.

  (* [comment removed for export] *)
  Definition diginc_ok : Prop :=
    forall (lo : list cell) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      rw_cells PSEGS m (SP + -144) lo -> Z.of_nat (cells_size lo) = 40%Z ->
      FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono PSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 3)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25bd8) fc None m (seg_rom PSEGS)).

  Lemma diginc_proof : end_ok -> diginc_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END. unfold diginc_ok. intros until K. intros FRLO LOSZ FRH ST XL Hcur XC DG MU WM LEN DGB V KB. bounds.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply END; try eassumption; try lia.
    all: enough (dg / 19 <= (dg + 1) / 19)%Z by lia; apply Z.div_le_mono; lia.
  Qed.

  Notation FRLO3 w8 w16 w24 m := (rw_cells PSEGS m (SP + -144) [C8 numv; C8 w8; C8 w16; C8 w24; C8 resv]).
  (* [comment removed for export] *)
  Notation ADDV ws1 n1 y K := (boxed (bnorm ws1 n1 /\ (0 <= y)%Z /\ (bval ws1 n1 + y < 2 ^ (64 * K))%Z /\ (0 <= K <= 61)%Z)).

  Lemma cap_of_K : forall v K, (v < 2 ^ (64 * K))%Z -> (0 <= K <= 62)%Z -> (v < BIG_CAP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros v K Hv HK. unfold BIG_CAP. eapply Z.lt_le_trans; [exact Hv|]. apply Z.pow_le_mono_r; lia.
  Qed.

  (* [comment removed for export] *)
  Definition rupush_ok : Prop :=
    forall (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (ws1 cur : list word) (n1 : nat) (dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 (Z.of_nat n1))] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono PSEGS m0 m ->
      (0 <= dg <= maxd)%Z -> (0 <= K <= dg / 19 + 3)%Z ->
      length ws1 = 62%nat -> boxed (sad_inv ws1 cur 1 n1 1) -> ADDV ws1 n1 1 K ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 (Z_to_bv 64 (Z.of_nat n1)) x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25bb4) fc None m (seg_rom PSEGS)).

  Lemma rupush_proof : diginc_ok -> rupush_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros DIG. unfold rupush_ok. intros until K. intros FRLO FRH ST XL Hcur XC DG MU WM DGB KB Hws1 SI AV. bounds.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hcur in BdX.
    assert (ROOM : (n1 < 62)%nat).
    { unfold boxed in SI, AV. destruct AV as (_ & _ & BV & HK). eapply (sad_room ws1 cur 1 n1 1 SI); [lia|].
      eapply cap_of_K; [exact BV| lia]. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (Z.of_nat n1)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    replace (Z_to_bv 64 (A + Z.of_nat n1 * 2 ^ 3)) with (Z_to_bv 64 (A + 8 * Z.of_nat n1)) by (f_equal; lia).
    pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat n1) (Z_to_bv 64 (A + 8 * Z.of_nat n1)) XL ltac:(lia) eq_refl) as SOK.
    step. (* [comment removed for export] *)
    change (Z_to_le_bytes 8 1) with (le8 (Z_to_bv 64 1)).
    pose proof (u64arr_write PSEGS m A cur (Z.of_nat n1) (Z_to_bv 64 1) XL ltac:(lia)) as XL'.
    rewrite Nat2Z.id in XL'.
    store_done.
    step. (* [comment removed for export] *)
    replace (Z.of_nat n1 + 1)%Z with (Z.of_nat (S n1)) by lia.
    eapply (DIG [C8 numv; C8 w8; C8 w16; C8 w24; C8 resv]); try eassumption; try lia.
    { reflexivity. }
    { rewrite upd_length. exact Hcur. }
    unfold boxed in SI, AV |- *. destruct AV as (BN & _ & BV & HK). replace (Z.to_nat (Z.of_nat n1 + 1)) with (S n1) by lia. split.
    - apply bnorm_push; [rewrite Hcur; lia|]. rewrite unsigned_lit by lia. lia.
    - rewrite (sad_inv_push ws1 cur 1 n1 1 SI) by (rewrite ?Hws1; lia). exact BV.
  Qed.

  (* [comment removed for export] *)
  Definition ru1add_ok (k : nat) : Prop :=
    forall (j : nat) (w8 w16 w24 : word) (x1 x5 x6 x7 p x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (ws1 cur : list word) (n1 : nat) (dg K : Z),
      (n1 - j = k)%nat -> (j <= n1)%nat -> (n1 <= 62)%nat -> bv_unsigned p = (A + 8 * Z.of_nat j)%Z ->
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 (Z.of_nat n1))] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono PSEGS m0 m ->
      (0 <= dg <= maxd)%Z -> (0 <= K <= dg / 19 + 3)%Z ->
      length ws1 = 62%nat -> boxed (sad_inv ws1 cur 1 j 1) -> ADDV ws1 n1 1 K ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv p (Z_to_bv 64 (Z.of_nat n1)) (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j + 1))
                 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25a98) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Lemma ru1add_proof : diginc_ok -> rupush_ok -> forall k, ru1add_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros DIG PUSH. induction k as [|k IH]; unfold ru1add_ok; intros until K;
      intros Hk Hj Hn1 Hp FRLO FRH ST XL Hcur XC DG MU WM DGB KB Hws1 SI AV; bounds.
    - assert (Hjn : j = n1) by lia. subst j.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [clear Hz| exfalso; lia].
      eapply PUSH; eassumption.
    - destruct (Nat.eq_dec j n1) as [->|Hne]. { eapply (IH n1); try eassumption; lia. }
      pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hcur in BdX.
      pose proof (bv_unsigned_in_range 64 p) as Rp. unfold bv_modulus in Rp.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [exfalso; lia|]. clear Hz.
      destruct (nth_error cur j) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
      assert (Hw : nth j cur w0 = w) by (apply nth_error_nth; exact Hn).
      assert (Hlimb : limbZ ws1 j = bv_unsigned w).
      { unfold boxed in SI. destruct SI as (_ & Hag & _). unfold limbZ. rewrite <- (Hag j) by lia. rewrite Hw. reflexivity. }
      pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
      pose proof (u64arr_read PSEGS m A cur (Z.of_nat j) w p XL ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat j) p XL ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write PSEGS m A cur (Z.of_nat j) (Z_to_bv 64 (bv_unsigned w + 1)) XL ltac:(lia)) as XL'.
      replace (A + 8 * Z.of_nat j)%Z with (bv_unsigned p + 0)%Z in XL' by lia. rewrite Nat2Z.id in XL'.
      store_done.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc.
      + assert (Hwr : (bv_unsigned w + 1 = 2^64)%Z).
        { destruct (Z.eq_dec (bv_unsigned w + 1) (2^64)); [assumption|]. exfalso. first [ rewrite Z.mod_small in Hc by lia; lia | lia ]. }
        clear Hc.
        replace (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j)) with (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat (S j) + 1)) by (f_equal; lia).
        eapply (IH (S j) w8 w16 w24 x1 x5 x6 x7 (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
        { rewrite unsigned_lit by lia. lia. }
        { rewrite upd_length. exact Hcur. }
        unfold boxed in SI |- *. rewrite <- Hlimb. apply sad_inv_wrap; [exact SI | rewrite Hws1; lia | lia | lia].
      + assert (Hnw : (bv_unsigned w + 1 < 2^64)%Z).
        { destruct (Z.lt_ge_cases (bv_unsigned w + 1) (2^64)); [assumption|]. exfalso.
          change 18446744073709551616%Z with (2^64)%Z in Hc.
          rewrite <- (Z.mod_unique_pos (bv_unsigned w + 1) (2^64) 1 (bv_unsigned w + 1 - 2^64)) in Hc by lia. lia. }
        clear Hc.
        step. (* [comment removed for export] *)
        eapply (DIG [C8 numv; C8 w8; C8 w16; C8 w24; C8 resv]); try eassumption; try lia.
        { reflexivity. }
        { rewrite upd_length. exact Hcur. }
        unfold boxed in SI, AV |- *. destruct AV as (BN & _ & BV & HK). rewrite Nat2Z.id, <- Hlimb. split.
        * apply (sad_bnorm_stop ws1 cur 1 j 1 n1 SI); rewrite ?Hws1; try lia. exact BN.
        * rewrite (sad_inv_stop ws1 cur 1 j 1 n1 SI) by (rewrite ?Hws1; lia). exact BV.
  Qed.
  (* [comment removed for export] *)
  Definition ru2add_ok (k : nat) : Prop :=
    forall (j : nat) (w8 w16 w24 : word) (x1 x5 x6 x7 p x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (ws1 cur : list word) (n1 : nat) (dg K : Z),
      (n1 - j = k)%nat -> (j <= n1)%nat -> (n1 <= 62)%nat -> bv_unsigned p = (A + 8 * Z.of_nat j)%Z ->
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 (Z.of_nat n1))] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono PSEGS m0 m ->
      (0 <= dg <= maxd)%Z -> (0 <= K <= dg / 19 + 3)%Z ->
      length ws1 = 62%nat -> boxed (sad_inv ws1 cur 1 j 1) -> ADDV ws1 n1 1 K ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv p (Z_to_bv 64 (Z.of_nat n1)) (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j + 1))
                 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25b90) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Lemma ru2add_proof : diginc_ok -> rupush_ok -> forall k, ru2add_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros DIG PUSH. induction k as [|k IH]; unfold ru2add_ok; intros until K;
      intros Hk Hj Hn1 Hp FRLO FRH ST XL Hcur XC DG MU WM DGB KB Hws1 SI AV; bounds.
    - assert (Hjn : j = n1) by lia. subst j.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [clear Hz| exfalso; lia].
      eapply PUSH; eassumption.
    - destruct (Nat.eq_dec j n1) as [->|Hne]. { eapply (IH n1); try eassumption; lia. }
      pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hcur in BdX.
      pose proof (bv_unsigned_in_range 64 p) as Rp. unfold bv_modulus in Rp.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [exfalso; lia|]. clear Hz.
      destruct (nth_error cur j) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
      assert (Hw : nth j cur w0 = w) by (apply nth_error_nth; exact Hn).
      assert (Hlimb : limbZ ws1 j = bv_unsigned w).
      { unfold boxed in SI. destruct SI as (_ & Hag & _). unfold limbZ. rewrite <- (Hag j) by lia. rewrite Hw. reflexivity. }
      pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
      pose proof (u64arr_read PSEGS m A cur (Z.of_nat j) w p XL ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat j) p XL ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write PSEGS m A cur (Z.of_nat j) (Z_to_bv 64 (bv_unsigned w + 1)) XL ltac:(lia)) as XL'.
      replace (A + 8 * Z.of_nat j)%Z with (bv_unsigned p + 0)%Z in XL' by lia. rewrite Nat2Z.id in XL'.
      store_done.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc; cycle 1.
      + step. (* [comment removed for export] *)
        assert (Hwr : (bv_unsigned w + 1 = 2^64)%Z).
        { destruct (Z.eq_dec (bv_unsigned w + 1) (2^64)); [assumption|]. exfalso. first [ rewrite Z.mod_small in Hc by lia; lia | lia ]. }
        clear Hc.
        replace (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j)) with (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat (S j) + 1)) by (f_equal; lia).
        eapply (IH (S j) w8 w16 w24 x1 x5 x6 x7 (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
        { rewrite unsigned_lit by lia. lia. }
        { rewrite upd_length. exact Hcur. }
        unfold boxed in SI |- *. rewrite <- Hlimb. apply sad_inv_wrap; [exact SI | rewrite Hws1; lia | lia | lia].
      + assert (Hnw : (bv_unsigned w + 1 < 2^64)%Z).
        { destruct (Z.lt_ge_cases (bv_unsigned w + 1) (2^64)); [assumption|]. exfalso.
          change 18446744073709551616%Z with (2^64)%Z in Hc.
          rewrite <- (Z.mod_unique_pos (bv_unsigned w + 1) (2^64) 1 (bv_unsigned w + 1 - 2^64)) in Hc by lia. lia. }
        clear Hc.
        eapply (DIG [C8 numv; C8 w8; C8 w16; C8 w24; C8 resv]); try eassumption; try lia.
        { reflexivity. }
        { rewrite upd_length. exact Hcur. }
        unfold boxed in SI, AV |- *. destruct AV as (BN & _ & BV & HK). rewrite Nat2Z.id, <- Hlimb. split.
        * apply (sad_bnorm_stop ws1 cur 1 j 1 n1 SI); rewrite ?Hws1; try lia. exact BN.
        * rewrite (sad_inv_stop ws1 cur 1 j 1 n1 SI) by (rewrite ?Hws1; lia). exact BV.
  Qed.

  (* [comment removed for export] *)
  Definition ru_ok (pc : Z) : Prop :=
    forall (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono PSEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 pc) fc None m (seg_rom PSEGS)).

  Lemma ru1_proof : (forall k, ru1add_ok k) -> ru_ok 0x25a80.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros ADD; unfold ru_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG MU WM LEN DGB V KB; bounds.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur len).
    { exact XL. } { exact Hcur. } { exact XC. } { lia. }
    { unfold boxed in V; destruct V as [_ BV]; rewrite unsigned_lit by lia.
      apply (cap_mul _ _ K); try lia. pose proof (bval_nonneg cur (Z.to_nat len)). lia. }
    lazymatch goal with
    | XL' : u64arr PSEGS ?m' A ?cur', XC' : rw_cells PSEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len <= ?len' <= len + 1 /\ _)%Z, HV : bval _ _ = (bval cur (Z.to_nat len) * _)%Z, HN : (_ -> bnorm cur _ -> bnorm _ _) |- _ =>
      rename XL' into XL1; rename XC' into XC1; rename HB into HB1; rename HV into HV1; rename HN into HN1;
      set (cur1 := cur') in *; set (len1 := len') in *
    end.
    pose proof (bv_unsigned_in_range 64 resv).
    step. (* [comment removed for export] *)
    rewrite zx16_lit by lia.
    step. (* [comment removed for export] *)
    replace (Z_to_bv 64 len1) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len1))) by (f_equal; lia).
    replace (Z_to_bv 64 (len1 + 1)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len1) - Z.of_nat 0 + 1)) by (f_equal; lia).
    eapply (ADD (Z.to_nat len1) 0%nat w8 w16 w24 _ _ _ _ resv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur1 cur1 (Z.to_nat len1) dg (K + 1)%Z);
      try eassumption; try lia.
    { replace (Z.of_nat (Z.to_nat len1)) with len1 by lia. exact XC1. }
    { unfold boxed. apply sad_inv_init. }
    unfold boxed in V |- *. destruct V as [BN BV]. rewrite unsigned_lit in HV1, HN1 by lia.
    split; [apply HN1; [lia| exact BN] |]. split; [lia|]. split; [| lia].
    rewrite HV1. pose proof (bval_nonneg cur (Z.to_nat len)).
    apply (addnative_bound (bval cur (Z.to_nat len)) 10 1 K); lia.
  Qed.
  Lemma ru2_proof : (forall k, ru2add_ok k) -> ru_ok 0x25b78.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros ADD; unfold ru_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG MU WM LEN DGB V KB; bounds.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur len).
    { exact XL. } { exact Hcur. } { exact XC. } { lia. }
    { unfold boxed in V; destruct V as [_ BV]; rewrite unsigned_lit by lia.
      apply (cap_mul _ _ K); try lia. pose proof (bval_nonneg cur (Z.to_nat len)). lia. }
    lazymatch goal with
    | XL' : u64arr PSEGS ?m' A ?cur', XC' : rw_cells PSEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len <= ?len' <= len + 1 /\ _)%Z, HV : bval _ _ = (bval cur (Z.to_nat len) * _)%Z, HN : (_ -> bnorm cur _ -> bnorm _ _) |- _ =>
      rename XL' into XL1; rename XC' into XC1; rename HB into HB1; rename HV into HV1; rename HN into HN1;
      set (cur1 := cur') in *; set (len1 := len') in *
    end.
    pose proof (bv_unsigned_in_range 64 resv).
    step. (* [comment removed for export] *)
    rewrite zx16_lit by lia.
    step. (* [comment removed for export] *)
    replace (Z_to_bv 64 len1) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len1))) by (f_equal; lia).
    replace (Z_to_bv 64 (len1 + 1)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len1) - Z.of_nat 0 + 1)) by (f_equal; lia).
    eapply (ADD (Z.to_nat len1) 0%nat w8 w16 w24 _ _ _ _ resv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur1 cur1 (Z.to_nat len1) dg (K + 1)%Z);
      try eassumption; try lia.
    { replace (Z.of_nat (Z.to_nat len1)) with len1 by lia. exact XC1. }
    { unfold boxed. apply sad_inv_init. }
    unfold boxed in V |- *. destruct V as [BN BV]. rewrite unsigned_lit in HV1, HN1 by lia.
    split; [apply HN1; [lia| exact BN] |]. split; [lia|]. split; [| lia].
    rewrite HV1. pose proof (bval_nonneg cur (Z.to_nat len)).
    apply (addnative_bound (bval cur (Z.to_nat len)) 10 1 K); lia.
  Qed.
  Definition ftb1_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at PSEGS m FP fbs -> (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 (Z_to_bv 64 48) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (FP + flen)) x20 p x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25b64) fc None m (seg_rom PSEGS)).

  Definition ftb8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at PSEGS m FP fbs -> (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 (Z_to_bv 64 (flen - Z.of_nat off)) (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 7) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (FP + flen)) x20 p x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25af4) fc None m (seg_rom PSEGS)).

  Definition ftb_ok : Prop :=
    forall (off : nat) (p : word) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at PSEGS m FP fbs -> (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (FP + flen)) x20 p x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25adc) fc None m (seg_rom PSEGS)).

  Definition ftaend_ok : Prop :=
    forall (fw : word) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 fw x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25a7c) fc None m (seg_rom PSEGS)).

  Definition fta1_ok (k : nat) : Prop :=
    forall (off : nat) (p fw : word) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at PSEGS m FP fbs -> (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 fw (Z_to_bv 64 (FP + flen)) p (Z_to_bv 64 48) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25a6c) fc None m (seg_rom PSEGS)).

  Definition fta8_ok (k : nat) : Prop :=
    forall (off : nat) (p fw : word) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at PSEGS m FP fbs -> (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 fw fptr p (Z_to_bv 64 flen) (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 7) (Z_to_bv 64 (flen - Z.of_nat off)) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x259f8) fc None m (seg_rom PSEGS)).

  Definition fta_ok : Prop :=
    forall (fw : word) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at PSEGS m FP fbs -> (FP <> 0)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 fw fptr numv x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x259d4) fc None m (seg_rom PSEGS)).

  Definition itb_ok : Prop :=
    forall (fw : word) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 fw x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x259c8) fc None m (seg_rom PSEGS)).

  Definition ita_ok : Prop :=
    forall (u : unit) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x259b0) fc None m (seg_rom PSEGS)).

  Definition it1_ok (k : nat) : Prop :=
    forall (off : nat) (q : word) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned q = (IP + Z.of_nat off + 1)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 (Z_to_bv 64 48) x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (IP + ilen)) q x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25990) fc None m (seg_rom PSEGS)).

  Definition it8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (length ibs - off <= k)%nat -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 (Z_to_bv 64 (ilen - Z.of_nat off)) (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 7) x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (IP + ilen)) p x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2591c) fc None m (seg_rom PSEGS)).

  Definition it_ok : Prop :=
    forall (off : nat) (p : word) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (IP + ilen)) p x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25904) fc None m (seg_rom PSEGS)).

  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr PSEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).

  Lemma ftb1_proof : end_ok -> ru_ok 0x25b78 -> forall k, ftb1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END RU2. induction k as [|k IH]; unfold ftb1_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB FBS Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block PSEGS m FP fbs off 1 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc.
    { clear Hc. eapply RU2; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { clear He. eapply (END [C8 numv; C8 w8; C8 w16; C8 w24; C8 resv]); try eassumption; try lia. reflexivity. }
    step. (* [comment removed for export] *)
    eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1))); try eassumption; try lia.
    all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma ftb8_proof : end_ok -> ru_ok 0x25b78 -> (forall k, ftb1_ok k) -> forall k, ftb8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END RU2 T1. induction k as [|k IH]; unfold ftb8_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB FBS Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block PSEGS m FP fbs off 8 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    do 22 step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc.
    { clear Hc. eapply RU2; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (flen - Z.of_nat off + -8)) with (Z_to_bv 64 (flen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { clear He. eapply (END [C8 numv; C8 w8; C8 w16; C8 w24; C8 resv]); try eassumption; try lia. reflexivity. }
      step. (* [comment removed for export] *)
      eapply (T1 (length fbs - (off + 8))%nat (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma ftb_proof : end_ok -> (forall k, ftb1_ok k) -> (forall k, ftb8_ok k) -> ftb_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END T1 T8. unfold ftb_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB FBS Hoff Hp; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (FP + flen)) by lia.
    replace (Z_to_bv 64 (FP + flen - bv_unsigned p)) with (Z_to_bv 64 (flen - Z.of_nat off)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { clear He. eapply (END [C8 numv; C8 w8; C8 w16; C8 w24; C8 resv]); try eassumption; try lia. reflexivity. }
      step. (* [comment removed for export] *)
      eapply (T1 (length fbs - off)%nat off p); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T8 (length fbs - off)%nat off p); try eassumption; try lia.
  Qed.

  Lemma ftaend_proof : end_ok -> ru_ok 0x25a80 -> ftaend_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END RU1. unfold ftaend_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB; pre.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    - eapply (END [C8 numv; C8 w8; C8 w16; C8 w24; C8 resv]); try eassumption; try lia. reflexivity.
    - eapply RU1; try eassumption; lia.
  Qed.

  Lemma fta1_proof : ftaend_ok -> ru_ok 0x25a80 -> forall k, fta1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FE RU1. induction k as [|k IH]; unfold fta1_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB FBS Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block PSEGS m FP fbs off 1 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc.
    { clear Hc. eapply RU1; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) fw); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - eapply FE; try eassumption; lia.
  Qed.

  Lemma fta8_proof : ftaend_ok -> ru_ok 0x25a80 -> (forall k, fta1_ok k) -> forall k, fta8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FE RU1 T1. induction k as [|k IH]; unfold fta8_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB FBS Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block PSEGS m FP fbs off 8 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    do 22 step.
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc.
    { clear Hc. eapply RU1; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (flen - Z.of_nat off + -8)) with (Z_to_bv 64 (flen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) fw); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { eapply FE; try eassumption; lia. }
      step. (* [comment removed for export] *)
      eapply (T1 (length fbs - (off + 8))%nat (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) fw); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma fta_proof : ftaend_ok -> (forall k, fta1_ok k) -> (forall k, fta8_ok k) -> fta_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FE T1 T8. unfold fta_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB FBS FNZ; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { eapply FE; try eassumption; lia. }
      step. (* [comment removed for export] *)
      eapply (T1 (length fbs) 0%nat fptr fw); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 flen) with (Z_to_bv 64 (flen - Z.of_nat 0)) at 2 by (f_equal; lia).
      eapply (T8 (length fbs) 0%nat fptr fw); try eassumption; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fbs_now : forall m, munch W m0 m -> (FP <> 0)%Z -> bytes_at PSEGS m FP fbs.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in FBS0, LAY5. specialize (LAY5 FNZ).
    pose proof (bytes_at_bound _ _ _ _ FBS0) as BF.
    eapply (bytes_at_transport PSEGS _ m0 m); [exact FBS0 | exact MU |].
    cbn [disjoint_from]. lia.
  Qed.

  Lemma itb_proof : ftaend_ok -> fta_ok -> itb_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FE FA. unfold itb_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB; pre.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz; cond_cleanup Hz.
    - eapply FE; try eassumption; lia.
    - eapply FA; try eassumption; try lia. apply fbs_now; assumption.
  Qed.

  Lemma ita_proof : end_ok -> fta_ok -> ita_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FA. unfold ita_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB; pre.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz; cond_cleanup Hz.
    - eapply (END [C8 numv; C8 w8; C8 w16; C8 w24; C8 resv]); try eassumption; try lia. reflexivity.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply FA; try eassumption; try lia. apply fbs_now; assumption.
  Qed.

  Lemma it1_proof : itb_ok -> forall k, it1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros TB. induction k as [|k IH]; unfold it1_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB Hk Hoff Hq; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 q) as Rq; unfold bv_modulus in Rq.
    pose proof (ro_block PSEGS m IP ibs off 1 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned q + -1)%Z in BLK by lia.
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    - eapply TB; try eassumption; lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb; cond_cleanup Hb.
      + eapply (IH (S off) (Z_to_bv 64 (bv_unsigned q + 1))); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; lia.
      + step. (* [comment removed for export] *)
        eapply TB; try eassumption; lia.
  Qed.

  Lemma it8_proof : itb_ok -> ita_ok -> (forall k, it1_ok k) -> forall k, it8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros TB TA T1. induction k as [|k IH]; unfold it8_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block PSEGS m IP ibs off 8 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    do 22 step.
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { step. (* [comment removed for export] *) eapply TB; try eassumption; lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (ilen - Z.of_nat off + -8)) with (Z_to_bv 64 (ilen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { eapply TA; try eassumption; try lia. exact tt. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length ibs - (off + 8))%nat (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 9))); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma it_proof : ita_ok -> (forall k, it1_ok k) -> (forall k, it8_ok k) -> it_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros TA T1 T8. unfold it_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB Hoff Hp; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (IP + ilen)) by lia.
    replace (Z_to_bv 64 (IP + ilen - bv_unsigned p)) with (Z_to_bv 64 (ilen - Z.of_nat off)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { eapply TA; try eassumption; try lia. exact tt. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length ibs - off)%nat off (Z_to_bv 64 (bv_unsigned p + 1))); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T8 (length ibs - off)%nat off p); try eassumption; try lia.
  Qed.

  (* [comment removed for export] *)
  Definition itadd_ok (k : nat) : Prop :=
    forall (K : Z) (j : nat) (p cw : word) (cv : Z) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (ws1 cur : list word) (n1 : nat) (y dg : Z),
      (forall (y10 y11 y12 y13 y14 yc : word) (m' : word -> option byte) (cur2 : list word) (len2 : Z),
          FRLO3 w8 w16 w24 m' -> FRHI m' -> stk PSEGS m' (SP + -144) (SP + -144) ->
          u64arr PSEGS m' A cur2 -> length cur2 = 62%nat -> rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 len2)] ->
          rw_cells PSEGS m' D [C8 (Z_to_bv 64 dg)] -> NUMF m' -> bytes_at PSEGS m' IP ibs ->
          munch W m0 m' -> wmono PSEGS m0 m' -> pristine m' 0x10000 0x22000 ->
          (0 <= len2 <= 62)%Z -> VAL cur2 len2 K ->
          evt PSEGS POST (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 y10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21 x22 x23 yc x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x25904) fc None m' (seg_rom PSEGS))) ->
      (n1 - j <= k)%nat -> (j <= n1)%nat -> (n1 <= 62)%nat -> bv_unsigned p = (A + 8 * Z.of_nat j)%Z ->
      bv_unsigned cw = cv -> (cv <> 0)%Z -> (j = 0%nat -> cv = y) -> ((0 < j)%nat -> cv = 1%Z) ->
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 (Z.of_nat n1))] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= dg <= maxd)%Z -> (0 <= K)%Z ->
      length ws1 = 62%nat -> ADDV ws1 n1 y K ->
      boxed (sad_inv ws1 cur y j cv) ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 (Z_to_bv 64 (Z.of_nat n1)) (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j + 1)) p x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 cw x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x257d8) fc None m (seg_rom PSEGS)).

  Lemma itadd_proof : forall k, itadd_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    induction k as [|k IH]; unfold itadd_ok; intros until dg;
      intros CONT Hk Hj Hn1 Hp Hcw Hcv Hcv0 Hcv1 FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR DGB HK Hws1 AV SI; pre.
    all: pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    all: pose proof (bv_unsigned_in_range 64 cw) as Rcw; unfold bv_modulus in Rcw.
    - assert (Hjn : j = n1) by lia. subst j.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [clear Hz| exfalso; lia].
      (* [comment removed for export] *)
      assert (ROOM : (n1 < 62)%nat).
      { unfold boxed in SI, AV. destruct AV as (_ & _ & BV & HK2). eapply (sad_room ws1 cur y n1 cv SI); [lia|].
        eapply cap_of_K; [exact BV| lia]. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (Z.of_nat n1)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 (A + Z.of_nat n1 * 2 ^ 3)) with (Z_to_bv 64 (A + 8 * Z.of_nat n1)) by (f_equal; lia).
      pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat n1) (Z_to_bv 64 (A + 8 * Z.of_nat n1)) XL ltac:(lia) eq_refl) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write PSEGS m A cur (Z.of_nat n1) cw XL ltac:(lia)) as XL'.
      rewrite Nat2Z.id in XL'.
      store_done.
      rewrite <- (Z_to_bv_bv_unsigned cw), Hcw in XL'.
      step. (* [comment removed for export] *)
      
      eapply CONT; try eassumption; try lia.
      all: lazymatch goal with
           | |- length _ = _ => rewrite upd_length; exact Hcur
           | |- boxed _ =>
             unfold boxed in SI, AV |- *; destruct AV as (BN & Hy & BV & HK2); replace (Z.to_nat (Z.of_nat n1 + 1)) with (S n1) by lia; split;
             [ apply bnorm_push; [rewrite Hcur; lia|]; rewrite unsigned_lit by lia; exact Hcv
             | rewrite (sad_inv_push ws1 cur y n1 cv SI) by (rewrite ?Hws1; lia); exact BV ]
           end.
    - destruct (Nat.eq_dec j n1) as [->|Hne]. { eapply (IH K n1 p cw cv); try eassumption; lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [exfalso; lia| clear Hz].
      destruct (nth_error cur j) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
      assert (Hw : nth j cur w0 = w) by (apply nth_error_nth; exact Hn).
      assert (Hlimb : limbZ ws1 j = bv_unsigned w).
      { unfold boxed in SI. destruct SI as (_ & Hag & _). unfold limbZ. rewrite <- (Hag j) by lia. rewrite Hw. reflexivity. }
      pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
      pose proof (u64arr_read PSEGS m A cur (Z.of_nat j) w p XL ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat j) p XL ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write PSEGS m A cur (Z.of_nat j) (Z_to_bv 64 (bv_unsigned w + bv_unsigned cw)) XL ltac:(lia)) as XL'.
      replace (A + 8 * Z.of_nat j)%Z with (bv_unsigned p + 0)%Z in XL' by lia. rewrite Nat2Z.id in XL'.
      store_done.
      rewrite Hcw in XL'.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite Hcw.
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc; rewrite ?unsigned_lit_wrap in Hc.
      + pose proof (addc_wrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hc) as Hge. clear Hc.
        replace (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j)) with (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat (S j) + 1)) by (f_equal; lia).
        eapply (IH K (S j) (Z_to_bv 64 (bv_unsigned p + 8)) (Z_to_bv 64 1) 1%Z); try eassumption; try lia.
        all: lazymatch goal with
             | |- bv_unsigned _ = _ => rewrite unsigned_lit by lia; first [reflexivity | lia]
             | |- length _ = _ => rewrite upd_length; exact Hcur
             | |- boxed _ => unfold boxed in SI |- *; rewrite <- Hlimb; apply sad_inv_wrap; [exact SI | rewrite Hws1; lia | lia | lia]
             end.
      + pose proof (addc_nowrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hc) as Hlt. clear Hc.
        step. (* [comment removed for export] *)
        eapply CONT; try eassumption; try lia.
        all: lazymatch goal with
             | |- length _ = _ => rewrite upd_length; exact Hcur
             | |- boxed _ =>
               unfold boxed in SI, AV |- *; destruct AV as (BN & Hy & BV & HK2); rewrite Nat2Z.id, <- Hlimb; split;
               [ apply (sad_bnorm_stop ws1 cur y j cv n1 SI); rewrite ?Hws1; try lia; exact BN
               | rewrite (sad_inv_stop ws1 cur y j cv n1 SI) by (rewrite ?Hws1; lia); exact BV ]
             end.
  Qed.

  (* [comment removed for export] *)
  Definition ftadd_ok (k : nat) : Prop :=
    forall (K : Z) (j : nat) (p cw : word) (cv : Z) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (ws1 cur : list word) (n1 : nat) (y dg : Z),
      (forall (y10 y11 y12 y13 y14 yc : word) (m' : word -> option byte) (cur2 : list word) (len2 : Z),
          FRLO3 w8 w16 w24 m' -> FRHI m' -> stk PSEGS m' (SP + -144) (SP + -144) ->
          u64arr PSEGS m' A cur2 -> length cur2 = 62%nat -> rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 len2)] ->
          rw_cells PSEGS m' D [C8 (Z_to_bv 64 dg)] -> NUMF m' -> bytes_at PSEGS m' IP ibs ->
          munch W m0 m' -> wmono PSEGS m0 m' -> pristine m' 0x10000 0x22000 ->
          (0 <= len2 <= 62)%Z -> VAL cur2 len2 K ->
          evt PSEGS POST (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 y10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21 x22 yc x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x25adc) fc None m' (seg_rom PSEGS))) ->
      (n1 - j <= k)%nat -> (j <= n1)%nat -> (n1 <= 62)%nat -> bv_unsigned p = (A + 8 * Z.of_nat j)%Z ->
      bv_unsigned cw = cv -> (cv <> 0)%Z -> (j = 0%nat -> cv = y) -> ((0 < j)%nat -> cv = 1%Z) ->
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 (Z.of_nat n1))] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= dg <= maxd)%Z -> (0 <= K)%Z ->
      length ws1 = 62%nat -> ADDV ws1 n1 y K ->
      boxed (sad_inv ws1 cur y j cv) ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 (Z_to_bv 64 (Z.of_nat n1)) (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j + 1)) p x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 cw x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25894) fc None m (seg_rom PSEGS)).

  Lemma ftadd_proof : forall k, ftadd_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    induction k as [|k IH]; unfold ftadd_ok; intros until dg;
      intros CONT Hk Hj Hn1 Hp Hcw Hcv Hcv0 Hcv1 FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR DGB HK Hws1 AV SI; pre.
    all: pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    all: pose proof (bv_unsigned_in_range 64 cw) as Rcw; unfold bv_modulus in Rcw.
    - assert (Hjn : j = n1) by lia. subst j.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [clear Hz| exfalso; lia].
      (* [comment removed for export] *)
      assert (ROOM : (n1 < 62)%nat).
      { unfold boxed in SI, AV. destruct AV as (_ & _ & BV & HK2). eapply (sad_room ws1 cur y n1 cv SI); [lia|].
        eapply cap_of_K; [exact BV| lia]. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (Z.of_nat n1)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 (A + Z.of_nat n1 * 2 ^ 3)) with (Z_to_bv 64 (A + 8 * Z.of_nat n1)) by (f_equal; lia).
      pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat n1) (Z_to_bv 64 (A + 8 * Z.of_nat n1)) XL ltac:(lia) eq_refl) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write PSEGS m A cur (Z.of_nat n1) cw XL ltac:(lia)) as XL'.
      rewrite Nat2Z.id in XL'.
      store_done.
      rewrite <- (Z_to_bv_bv_unsigned cw), Hcw in XL'.
      step. (* [comment removed for export] *)
      
      eapply CONT; try eassumption; try lia.
      all: lazymatch goal with
           | |- length _ = _ => rewrite upd_length; exact Hcur
           | |- boxed _ =>
             unfold boxed in SI, AV |- *; destruct AV as (BN & Hy & BV & HK2); replace (Z.to_nat (Z.of_nat n1 + 1)) with (S n1) by lia; split;
             [ apply bnorm_push; [rewrite Hcur; lia|]; rewrite unsigned_lit by lia; exact Hcv
             | rewrite (sad_inv_push ws1 cur y n1 cv SI) by (rewrite ?Hws1; lia); exact BV ]
           end.
    - destruct (Nat.eq_dec j n1) as [->|Hne]. { eapply (IH K n1 p cw cv); try eassumption; lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [exfalso; lia| clear Hz].
      destruct (nth_error cur j) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
      assert (Hw : nth j cur w0 = w) by (apply nth_error_nth; exact Hn).
      assert (Hlimb : limbZ ws1 j = bv_unsigned w).
      { unfold boxed in SI. destruct SI as (_ & Hag & _). unfold limbZ. rewrite <- (Hag j) by lia. rewrite Hw. reflexivity. }
      pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
      pose proof (u64arr_read PSEGS m A cur (Z.of_nat j) w p XL ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat j) p XL ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write PSEGS m A cur (Z.of_nat j) (Z_to_bv 64 (bv_unsigned w + bv_unsigned cw)) XL ltac:(lia)) as XL'.
      replace (A + 8 * Z.of_nat j)%Z with (bv_unsigned p + 0)%Z in XL' by lia. rewrite Nat2Z.id in XL'.
      store_done.
      rewrite Hcw in XL'.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite Hcw.
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc; rewrite ?unsigned_lit_wrap in Hc.
      + pose proof (addc_wrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hc) as Hge. clear Hc.
        replace (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j)) with (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat (S j) + 1)) by (f_equal; lia).
        eapply (IH K (S j) (Z_to_bv 64 (bv_unsigned p + 8)) (Z_to_bv 64 1) 1%Z); try eassumption; try lia.
        all: lazymatch goal with
             | |- bv_unsigned _ = _ => rewrite unsigned_lit by lia; first [reflexivity | lia]
             | |- length _ = _ => rewrite upd_length; exact Hcur
             | |- boxed _ => unfold boxed in SI |- *; rewrite <- Hlimb; apply sad_inv_wrap; [exact SI | rewrite Hws1; lia | lia | lia]
             end.
      + pose proof (addc_nowrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hc) as Hlt. clear Hc.
        step. (* [comment removed for export] *)
        eapply CONT; try eassumption; try lia.
        all: lazymatch goal with
             | |- length _ = _ => rewrite upd_length; exact Hcur
             | |- boxed _ =>
               unfold boxed in SI, AV |- *; destruct AV as (BN & Hy & BV & HK2); rewrite Nat2Z.id, <- Hlimb; split;
               [ apply (sad_bnorm_stop ws1 cur y j cv n1 SI); rewrite ?Hws1; try lia; exact BN
               | rewrite (sad_inv_stop ws1 cur y j cv n1 SI) by (rewrite ?Hws1; lia); exact BV ]
             end.
  Qed.

  (* [comment removed for export] *)
  Definition iadd_ok (k : nat) : Prop :=
    forall (K : Z) (j : nat) (p cw : word) (cv : Z) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (ws1 cur : list word) (n1 : nat) (y dg : Z),
      (forall (y10 y11 y12 y13 y14 yc : word) (m' : word -> option byte) (cur2 : list word) (len2 : Z),
          FRLO3 w8 w16 w24 m' -> FRHI m' -> stk PSEGS m' (SP + -144) (SP + -144) ->
          u64arr PSEGS m' A cur2 -> length cur2 = 62%nat -> rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 len2)] ->
          rw_cells PSEGS m' D [C8 (Z_to_bv 64 dg)] -> NUMF m' -> bytes_at PSEGS m' IP ibs ->
          munch W m0 m' -> wmono PSEGS m0 m' -> pristine m' 0x10000 0x22000 ->
          (0 <= len2 <= 62)%Z -> VAL cur2 len2 K ->
          evt PSEGS POST (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 y10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21 x22 x23 yc x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x255ac) fc None m' (seg_rom PSEGS))) ->
      (n1 - j <= k)%nat -> (j <= n1)%nat -> (n1 <= 62)%nat -> bv_unsigned p = (A + 8 * Z.of_nat j)%Z ->
      bv_unsigned cw = cv -> (cv <> 0)%Z -> (j = 0%nat -> cv = y) -> ((0 < j)%nat -> cv = 1%Z) ->
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 (Z.of_nat n1))] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= dg <= maxd)%Z -> (0 <= K)%Z ->
      length ws1 = 62%nat -> ADDV ws1 n1 y K ->
      boxed (sad_inv ws1 cur y j cv) ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 (Z_to_bv 64 (Z.of_nat n1)) (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j + 1)) p x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 cw x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25568) fc None m (seg_rom PSEGS)).

  Lemma iadd_proof : forall k, iadd_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    induction k as [|k IH]; unfold iadd_ok; intros until dg;
      intros CONT Hk Hj Hn1 Hp Hcw Hcv Hcv0 Hcv1 FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR DGB HK Hws1 AV SI; pre.
    all: pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    all: pose proof (bv_unsigned_in_range 64 cw) as Rcw; unfold bv_modulus in Rcw.
    - assert (Hjn : j = n1) by lia. subst j.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [clear Hz| exfalso; lia].
      (* [comment removed for export] *)
      assert (ROOM : (n1 < 62)%nat).
      { unfold boxed in SI, AV. destruct AV as (_ & _ & BV & HK2). eapply (sad_room ws1 cur y n1 cv SI); [lia|].
        eapply cap_of_K; [exact BV| lia]. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (Z.of_nat n1)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 (A + Z.of_nat n1 * 2 ^ 3)) with (Z_to_bv 64 (A + 8 * Z.of_nat n1)) by (f_equal; lia).
      pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat n1) (Z_to_bv 64 (A + 8 * Z.of_nat n1)) XL ltac:(lia) eq_refl) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write PSEGS m A cur (Z.of_nat n1) cw XL ltac:(lia)) as XL'.
      rewrite Nat2Z.id in XL'.
      store_done.
      rewrite <- (Z_to_bv_bv_unsigned cw), Hcw in XL'.
      step. (* [comment removed for export] *)
      
      eapply CONT; try eassumption; try lia.
      all: lazymatch goal with
           | |- length _ = _ => rewrite upd_length; exact Hcur
           | |- boxed _ =>
             unfold boxed in SI, AV |- *; destruct AV as (BN & Hy & BV & HK2); replace (Z.to_nat (Z.of_nat n1 + 1)) with (S n1) by lia; split;
             [ apply bnorm_push; [rewrite Hcur; lia|]; rewrite unsigned_lit by lia; exact Hcv
             | rewrite (sad_inv_push ws1 cur y n1 cv SI) by (rewrite ?Hws1; lia); exact BV ]
           end.
    - destruct (Nat.eq_dec j n1) as [->|Hne]. { eapply (IH K n1 p cw cv); try eassumption; lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [exfalso; lia| clear Hz].
      destruct (nth_error cur j) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
      assert (Hw : nth j cur w0 = w) by (apply nth_error_nth; exact Hn).
      assert (Hlimb : limbZ ws1 j = bv_unsigned w).
      { unfold boxed in SI. destruct SI as (_ & Hag & _). unfold limbZ. rewrite <- (Hag j) by lia. rewrite Hw. reflexivity. }
      pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
      pose proof (u64arr_read PSEGS m A cur (Z.of_nat j) w p XL ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat j) p XL ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write PSEGS m A cur (Z.of_nat j) (Z_to_bv 64 (bv_unsigned w + bv_unsigned cw)) XL ltac:(lia)) as XL'.
      replace (A + 8 * Z.of_nat j)%Z with (bv_unsigned p + 0)%Z in XL' by lia. rewrite Nat2Z.id in XL'.
      store_done.
      rewrite Hcw in XL'.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite Hcw.
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc; rewrite ?unsigned_lit_wrap in Hc.
      + pose proof (addc_wrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hc) as Hge. clear Hc.
        replace (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j)) with (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat (S j) + 1)) by (f_equal; lia).
        eapply (IH K (S j) (Z_to_bv 64 (bv_unsigned p + 8)) (Z_to_bv 64 1) 1%Z); try eassumption; try lia.
        all: lazymatch goal with
             | |- bv_unsigned _ = _ => rewrite unsigned_lit by lia; first [reflexivity | lia]
             | |- length _ = _ => rewrite upd_length; exact Hcur
             | |- boxed _ => unfold boxed in SI |- *; rewrite <- Hlimb; apply sad_inv_wrap; [exact SI | rewrite Hws1; lia | lia | lia]
             end.
      + pose proof (addc_nowrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hc) as Hlt. clear Hc.
        step. (* [comment removed for export] *)
        eapply CONT; try eassumption; try lia.
        all: lazymatch goal with
             | |- length _ = _ => rewrite upd_length; exact Hcur
             | |- boxed _ =>
               unfold boxed in SI, AV |- *; destruct AV as (BN & Hy & BV & HK2); rewrite Nat2Z.id, <- Hlimb; split;
               [ apply (sad_bnorm_stop ws1 cur y j cv n1 SI); rewrite ?Hws1; try lia; exact BN
               | rewrite (sad_inv_stop ws1 cur y j cv n1 SI) by (rewrite ?Hws1; lia); exact BV ]
             end.
  Qed.

  (* [comment removed for export] *)
  Definition fadd_ok (k : nat) : Prop :=
    forall (K : Z) (j : nat) (p cw : word) (cv : Z) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (ws1 cur : list word) (n1 : nat) (y dg : Z),
      (forall (y10 y11 y12 y13 y14 yc : word) (m' : word -> option byte) (cur2 : list word) (len2 : Z),
          FRLO3 w8 w16 w24 m' -> FRHI m' -> stk PSEGS m' (SP + -144) (SP + -144) ->
          u64arr PSEGS m' A cur2 -> length cur2 = 62%nat -> rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 len2)] ->
          rw_cells PSEGS m' D [C8 (Z_to_bv 64 dg)] -> NUMF m' -> bytes_at PSEGS m' IP ibs ->
          munch W m0 m' -> wmono PSEGS m0 m' -> pristine m' 0x10000 0x22000 ->
          (0 <= len2 <= 62)%Z -> VAL cur2 len2 K ->
          evt PSEGS POST (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 y10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21 x22 yc x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x257c0) fc None m' (seg_rom PSEGS))) ->
      (n1 - j <= k)%nat -> (j <= n1)%nat -> (n1 <= 62)%nat -> bv_unsigned p = (A + 8 * Z.of_nat j)%Z ->
      bv_unsigned cw = cv -> (cv <> 0)%Z -> (j = 0%nat -> cv = y) -> ((0 < j)%nat -> cv = 1%Z) ->
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 (Z.of_nat n1))] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= dg <= maxd)%Z -> (0 <= K)%Z ->
      length ws1 = 62%nat -> ADDV ws1 n1 y K ->
      boxed (sad_inv ws1 cur y j cv) ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 (Z_to_bv 64 (Z.of_nat n1)) (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j + 1)) p x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 cw x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2577c) fc None m (seg_rom PSEGS)).

  Lemma fadd_proof : forall k, fadd_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    induction k as [|k IH]; unfold fadd_ok; intros until dg;
      intros CONT Hk Hj Hn1 Hp Hcw Hcv Hcv0 Hcv1 FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR DGB HK Hws1 AV SI; pre.
    all: pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    all: pose proof (bv_unsigned_in_range 64 cw) as Rcw; unfold bv_modulus in Rcw.
    - assert (Hjn : j = n1) by lia. subst j.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [clear Hz| exfalso; lia].
      (* [comment removed for export] *)
      assert (ROOM : (n1 < 62)%nat).
      { unfold boxed in SI, AV. destruct AV as (_ & _ & BV & HK2). eapply (sad_room ws1 cur y n1 cv SI); [lia|].
        eapply cap_of_K; [exact BV| lia]. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (Z.of_nat n1)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 (A + Z.of_nat n1 * 2 ^ 3)) with (Z_to_bv 64 (A + 8 * Z.of_nat n1)) by (f_equal; lia).
      pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat n1) (Z_to_bv 64 (A + 8 * Z.of_nat n1)) XL ltac:(lia) eq_refl) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write PSEGS m A cur (Z.of_nat n1) cw XL ltac:(lia)) as XL'.
      rewrite Nat2Z.id in XL'.
      store_done.
      rewrite <- (Z_to_bv_bv_unsigned cw), Hcw in XL'.
      step. (* [comment removed for export] *)
      
      eapply CONT; try eassumption; try lia.
      all: lazymatch goal with
           | |- length _ = _ => rewrite upd_length; exact Hcur
           | |- boxed _ =>
             unfold boxed in SI, AV |- *; destruct AV as (BN & Hy & BV & HK2); replace (Z.to_nat (Z.of_nat n1 + 1)) with (S n1) by lia; split;
             [ apply bnorm_push; [rewrite Hcur; lia|]; rewrite unsigned_lit by lia; exact Hcv
             | rewrite (sad_inv_push ws1 cur y n1 cv SI) by (rewrite ?Hws1; lia); exact BV ]
           end.
    - destruct (Nat.eq_dec j n1) as [->|Hne]. { eapply (IH K n1 p cw cv); try eassumption; lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz; [exfalso; lia| clear Hz].
      destruct (nth_error cur j) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
      assert (Hw : nth j cur w0 = w) by (apply nth_error_nth; exact Hn).
      assert (Hlimb : limbZ ws1 j = bv_unsigned w).
      { unfold boxed in SI. destruct SI as (_ & Hag & _). unfold limbZ. rewrite <- (Hag j) by lia. rewrite Hw. reflexivity. }
      pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
      pose proof (u64arr_read PSEGS m A cur (Z.of_nat j) w p XL ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat j) p XL ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
      step. (* [comment removed for export] *)
      pose proof (u64arr_write PSEGS m A cur (Z.of_nat j) (Z_to_bv 64 (bv_unsigned w + bv_unsigned cw)) XL ltac:(lia)) as XL'.
      replace (A + 8 * Z.of_nat j)%Z with (bv_unsigned p + 0)%Z in XL' by lia. rewrite Nat2Z.id in XL'.
      store_done.
      rewrite Hcw in XL'.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite Hcw.
      step. (* [comment removed for export] *)
      if_cases Hc; cond_cleanup Hc; rewrite ?unsigned_lit_wrap in Hc.
      + pose proof (addc_wrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hc) as Hge. clear Hc.
        replace (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat j)) with (Z_to_bv 64 (Z.of_nat n1 - Z.of_nat (S j) + 1)) by (f_equal; lia).
        eapply (IH K (S j) (Z_to_bv 64 (bv_unsigned p + 8)) (Z_to_bv 64 1) 1%Z); try eassumption; try lia.
        all: lazymatch goal with
             | |- bv_unsigned _ = _ => rewrite unsigned_lit by lia; first [reflexivity | lia]
             | |- length _ = _ => rewrite upd_length; exact Hcur
             | |- boxed _ => unfold boxed in SI |- *; rewrite <- Hlimb; apply sad_inv_wrap; [exact SI | rewrite Hws1; lia | lia | lia]
             end.
      + pose proof (addc_nowrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hc) as Hlt. clear Hc.
        step. (* [comment removed for export] *)
        eapply CONT; try eassumption; try lia.
        all: lazymatch goal with
             | |- length _ = _ => rewrite upd_length; exact Hcur
             | |- boxed _ =>
               unfold boxed in SI, AV |- *; destruct AV as (BN & Hy & BV & HK2); rewrite Nat2Z.id, <- Hlimb; split;
               [ apply (sad_bnorm_stop ws1 cur y j cv n1 SI); rewrite ?Hws1; try lia; exact BN
               | rewrite (sad_inv_stop ws1 cur y j cv n1 SI) by (rewrite ?Hws1; lia); exact BV ]
             end.
  Qed.
End Proof.
End P_parse_mantissa_1.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.
Import ListNotations.

Module P_from_chars_int_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation PSEGS := Plain.M.loaded_segments.

Definition from_chars_int_entry : Z := 0x29090.
Definition from_chars_int_FR : Z := 96.
(* [comment removed for export] *)
Definition FCI_FMT : Z := 5.
Definition FCI_OPT2 : Z := 42949673006.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition from_chars_int_W (sp res : word) : list ivl :=
  [(bv_unsigned sp - 96, bv_unsigned sp); (bv_unsigned res, bv_unsigned res + 4)]%Z.

Definition from_chars_int_post_hw
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (res : word)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom PSEGS)
    /\ munch (from_chars_int_W sp res) m m'
    /\ wmono PSEGS m m'
    /\ rw_cells PSEGS m' (bv_unsigned res) [C4 r']
    /\ stk PSEGS m' (bv_unsigned sp - 96) (bv_unsigned sp).

Definition from_chars_int_stmt_hw : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (bs : list byte) (rold : word),
    (* [comment removed for export] *)
    a3 = Z_to_bv 64 FCI_FMT ->
    a4 = Z_to_bv 64 FCI_OPT2 ->
    (* [comment removed for export] *)
    bytes_at PSEGS m (bv_unsigned a0) bs ->
    (Z.of_nat (length bs) = bv_unsigned a1 - bv_unsigned a0)%Z ->
    (bv_unsigned a0 <= bv_unsigned a1)%Z ->
    (* [comment removed for export] *)
    rw_cells PSEGS m (bv_unsigned a2) [C4 rold] ->
    stk PSEGS m (bv_unsigned sp - 96) (bv_unsigned sp) ->
    pristine m 0x10000 0x22000 ->
    (* [comment removed for export] *)
    (bv_unsigned a2 + 4 <= bv_unsigned a0 \/ bv_unsigned a1 <= bv_unsigned a2)%Z ->
    (bv_unsigned sp <= bv_unsigned a2 \/ bv_unsigned a2 + 4 <= bv_unsigned sp - 96)%Z ->
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a1 <= bv_unsigned sp - 96)%Z ->
    (bv_unsigned a2 + 4 <= 0x10000 \/ 0x22000 <= bv_unsigned a2)%Z ->
    (0x22000 <= bv_unsigned sp - 96)%Z ->
    evt PSEGS (from_chars_int_post_hw ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a2 m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x29090) fc None m (seg_rom PSEGS)).

(* [comment removed for export] *)
Definition from_chars_int_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (res : word)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (r' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom PSEGS)
    /\ munch (from_chars_int_W sp res) m m'
    /\ wmono PSEGS m m'
    /\ frm0 fc'
    /\ rw_cells PSEGS m' (bv_unsigned res) [C4 r']
    /\ stk PSEGS m' (bv_unsigned sp - 96) (bv_unsigned sp).

Definition from_chars_int_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (bs : list byte) (rold : word),
    (* [comment removed for export] *)
    a3 = Z_to_bv 64 FCI_FMT ->
    a4 = Z_to_bv 64 FCI_OPT2 ->
    (* [comment removed for export] *)
    bytes_at PSEGS m (bv_unsigned a0) bs ->
    (Z.of_nat (length bs) = bv_unsigned a1 - bv_unsigned a0)%Z ->
    (bv_unsigned a0 <= bv_unsigned a1)%Z ->
    (* [comment removed for export] *)
    rw_cells PSEGS m (bv_unsigned a2) [C4 rold] ->
    stk PSEGS m (bv_unsigned sp - 96) (bv_unsigned sp) ->
    pristine m 0x10000 0x22000 ->
    (* [comment removed for export] *)
    (bv_unsigned a2 + 4 <= bv_unsigned a0 \/ bv_unsigned a1 <= bv_unsigned a2)%Z ->
    (bv_unsigned sp <= bv_unsigned a2 \/ bv_unsigned a2 + 4 <= bv_unsigned sp - 96)%Z ->
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a1 <= bv_unsigned sp - 96)%Z ->
    (bv_unsigned a2 + 4 <= 0x10000 \/ 0x22000 <= bv_unsigned a2)%Z ->
    (0x22000 <= bv_unsigned sp - 96)%Z ->
        frm0 fc ->
    evt PSEGS (from_chars_int_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x29090) fc None m (seg_rom PSEGS)).

Lemma from_chars_int_stmt_of_hw : from_chars_int_stmt_hw -> from_chars_int_stmt.
Proof.
  intros HW. unfold from_chars_int_stmt_hw in HW. unfold from_chars_int_stmt. intros until rold. intros.
  match goal with Hf : frm0 fc |- _ => rename Hf into FRM end.
  apply (evt_mono PSEGS (from_chars_int_post_hw ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a2 m)); [apply (HW ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs rold); assumption|].
  unfold from_chars_int_post_hw, from_chars_int_post.
  intros ms' (q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & q14 & q15 & r' & m' & E & A & B & C & D).
  exists q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, F, fc, r', m'.
  split; [exact E|]. split; [exact A|]. split; [exact B|]. split; [exact FRM|]. split; [exact C | exact D].
Qed.
End P_from_chars_int_stmt.

Module P_from_chars_int.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_tac.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_from_chars_int_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Fixpoint image_u8s (A : Z) (n : nat) : list Z :=
  match n with O => [] | S n' => match image_bytes PSEGS A 1 with Some [b] => bv_unsigned b | _ => 0%Z end :: image_u8s (A + 1) n' end.
Definition DIGTAB : list Z := Eval vm_compute in (image_u8s 0x15db0 256).
Lemma DIGTAB_ok : table_b PSEGS 0x15db0 1 (fun v => [Z_to_bv 8 v]) DIGTAB = true.
Proof. vm_compute. reflexivity. Qed.
Lemma DIGTAB_len : length DIGTAB = 256%nat.
Proof. reflexivity. Qed.

Section Proof.
  (* [comment removed for export] *)
  Variables (ra sp gp tp a0 a1 a2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte) (bs : list byte) (rold : word).
  Hypothesis LEN : (Z.of_nat (length bs) = bv_unsigned a1 - bv_unsigned a0)%Z.
  Hypothesis LE : (bv_unsigned a0 <= bv_unsigned a1)%Z.
  Hypothesis SEP1 : (bv_unsigned a2 + 4 <= bv_unsigned a0 \/ bv_unsigned a1 <= bv_unsigned a2)%Z.
  Hypothesis SEP2 : (bv_unsigned sp <= bv_unsigned a2 \/ bv_unsigned a2 + 4 <= bv_unsigned sp - 96)%Z.
  Hypothesis SEP3 : (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a1 <= bv_unsigned sp - 96)%Z.
  Hypothesis RO2 : (bv_unsigned a2 + 4 <= 0x10000 \/ 0x22000 <= bv_unsigned a2)%Z.
  Hypothesis RO3 : (0x22000 <= bv_unsigned sp - 96)%Z.
  Hypothesis Ra1 : (bv_unsigned a1 < 2^64)%Z.
  Hypothesis Rsp : (bv_unsigned sp < 2^64)%Z.
  (* [comment removed for export] *)
  Notation FRCELLS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0].
  Hypothesis FR : rw_cells PSEGS m1 (bv_unsigned sp + -96) FRCELLS.
  Hypothesis OBJ : rw_cells PSEGS m1 (bv_unsigned a2) [C4 rold].
  Hypothesis DATA : bytes_at PSEGS m1 (bv_unsigned a0) bs.
  Hypothesis PR : pristine m1 0x10000 0x22000.
  Hypothesis ST : stk PSEGS m1 (bv_unsigned sp + -96) (bv_unsigned sp + -96).
  Hypothesis MU : munch (from_chars_int_W sp a2) m m1.
  Hypothesis WM : wmono PSEGS m m1.

  Notation W := (from_chars_int_W sp a2).
  Ltac fin := finish; try match goal with H : rw_cells _ _ _ [C4 _] |- rw_cells _ _ _ [C4 _] => exact H end.
  Notation POST := (from_chars_int_post_hw ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a2 m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -96)).

  (* [comment removed for export] *)
  #[using="bs"] Lemma exit_ec : forall (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (m' : word -> option byte) (r' : word),
      rw_cells PSEGS m' (bv_unsigned sp + -96) FRCELLS ->
      rw_cells PSEGS m' (bv_unsigned a2) [C4 r'] ->
      stk PSEGS m' (bv_unsigned sp + -96) (bv_unsigned sp + -96) ->
      munch W m m' -> wmono PSEGS m m' ->
      evt PSEGS POST
        (MS (mkR ra SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x293dc) fc None m' (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (bs : LiaFast.U) => LiaFast.u0).
    intros until r'. intros FR' OBJ' ST' MU' WM'.
    step. (* [comment removed for export] *)
    do 12 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FR' ST' (bv_unsigned sp).
    unfold from_chars_int_post_hw. fin.
  Qed.

  #[using="bs"] Lemma exit_e8 : forall (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (m' : word -> option byte) (r' : word),
      rw_cells PSEGS m' (bv_unsigned sp + -96) FRCELLS ->
      rw_cells PSEGS m' (bv_unsigned a2) [C4 r'] ->
      stk PSEGS m' (bv_unsigned sp + -96) (bv_unsigned sp + -96) ->
      munch W m m' -> wmono PSEGS m m' ->
      evt PSEGS POST
        (MS (mkR ra SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x293d8) fc None m' (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (bs : LiaFast.U) => LiaFast.u0).
    intros until r'. intros FR' OBJ' ST' MU' WM'.
    step. (* [comment removed for export] *)
    eapply exit_ec; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="a0 a1 bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 FR OBJ DATA PR ST MU WM"] Lemma exit_sw : forall (x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      evt PSEGS POST
        (MS (mkR ra SP' gp tp x5 x6 x7 x8 x9 x10 x11 a2 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x293d0) fc None m1 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (a0 a1 bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros. unfold from_chars_int_W in MU.
    pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply exit_e8; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM"] Lemma L_digits : forall (sd pe x5 x6 x8 x9 x10 x11 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= bv_unsigned pe)%Z -> (bv_unsigned pe <= bv_unsigned a1)%Z ->
      evt PSEGS POST
        (MS (mkR ra SP' gp tp x5 x6 pe x8 x9 x10 x11 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x29318) fc None m1 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros until x31. intros H1 H2 H3.
    pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
    pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
    unfold FCI_OPT2.
    do 8 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases B1.
    { clear B1. eapply exit_e8; eassumption. }
    cond_cleanup B1.
    step. (* [comment removed for export] *)
    if_cases B2.
    - clear B2.
      do 5 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B3. { clear B3. eapply exit_e8; eassumption. }
      clear B3. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      if_cases B4. { clear B4. apply exit_sw. }
      clear B4. step. (* [comment removed for export] *) step. (* [comment removed for export] *) apply exit_sw.
    - cond_cleanup B2.
      step. (* [comment removed for export] *)
      destruct (nth_error bs (Z.to_nat (bv_unsigned sd - bv_unsigned a0))) as [c|] eqn:Hc.
      2:{ exfalso. apply nth_error_None in Hc. lia. }
      pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs (bv_unsigned sd - bv_unsigned a0) c _ DATA Hc ltac:(lia) eq_refl) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      do 5 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (bv_unsigned_in_range 8 c) as Rc. unfold bv_modulus in Rc. cbn in Rc.
      pose proof (table_read PSEGS _ _ _ _ m1 _ _ DIGTAB_ok PR ltac:(lia) ltac:(rewrite DIGTAB_len; cbn; lia)
                    (bv_unsigned (zxb c)) ltac:(unfold zxb; rewrite unsigned_lit by lia; rewrite DIGTAB_len; lia)) as RD.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B5. { clear B5. eapply exit_e8; eassumption. }
      clear B5.
      do 5 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B6. { clear B6. eapply exit_e8; eassumption. }
      clear B6.
      do 5 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B3. { clear B3. eapply exit_e8; eassumption. }
      clear B3. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      if_cases B4. { clear B4. apply exit_sw. }
      clear B4. step. (* [comment removed for export] *) step. (* [comment removed for export] *) apply exit_sw.
  Qed.

  (* [comment removed for export] *)
  #[using="a0 a1 bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 FR OBJ DATA PR ST MU WM"] Lemma zero_digits : forall (x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      evt PSEGS POST
        (MS (mkR ra SP' gp tp x5 x6 x7 x8 x9 x10 x11 a2 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x293c4) fc None m1 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (a0 a1 bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros.
    step. (* [comment removed for export] *)
    if_cases B1.
    - clear B1. eapply exit_ec; eassumption.
    - clear B1. step. (* [comment removed for export] *) step. (* [comment removed for export] *) apply exit_sw.
  Qed.

  (* [comment removed for export] *)
  #[using="bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM"] Lemma postA : forall (sd x5 x6 x7 x8 x9 x10 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= bv_unsigned a1)%Z ->
      evt PSEGS POST
        (MS (mkR ra SP' gp tp x5 x6 x7 x8 x9 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x29310) fc None m1 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros until x31. intros H1 H2.
    pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases B1.
    - clear B1. apply zero_digits.
    - clear B1. apply L_digits; lia.
  Qed.

  (* [comment removed for export] *)
  Definition char_loop_ok (j : nat) : Prop :=
    forall (q : Z) (sd x5 x6 x8 x9 x10 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31 : word),
      (Z.to_nat (bv_unsigned a1 - q) <= j)%nat ->
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= q)%Z -> (q < bv_unsigned a1)%Z ->
      evt PSEGS POST
        (MS (mkR ra SP' gp tp x5 x6 (Z_to_bv 64 q) x8 x9 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                 x28 (Z_to_bv 64 0x15db0) x30 x31)
            F (Z_to_bv 64 0x292f0) fc None m1 (seg_rom PSEGS)).

  #[using="bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM"] Lemma char_loop : forall j, char_loop_ok j.
  Proof. LiaFast.lf_pins (fun (bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    induction j as [|j IH]; unfold char_loop_ok; intros until x31; intros MEAS H1 H2 H3.
    - exfalso. lia.
    - pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
      pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
      destruct (nth_error bs (Z.to_nat (q - bv_unsigned a0))) as [c|] eqn:Hc.
      2:{ exfalso. apply nth_error_None in Hc. lia. }
      pose proof (bv_unsigned_in_range 8 c) as Rc. unfold bv_modulus in Rc. cbn in Rc.
      pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs (q - bv_unsigned a0) c _ DATA Hc ltac:(lia) eq_refl) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      pose proof (table_read PSEGS _ _ _ _ m1 _ _ DIGTAB_ok PR ltac:(lia) ltac:(rewrite DIGTAB_len; cbn; lia)
                    (bv_unsigned (zxb c)) ltac:(unfold zxb; rewrite unsigned_lit by lia; rewrite DIGTAB_len; lia)) as RD.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      if_cases B1.
      { clear B1. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        if_cases B2.
        - clear B2. apply L_digits; rewrite ?unsigned_lit by lia; lia.
        - clear B2. apply zero_digits. }
      clear B1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B3.
      + cond_cleanup B3. eapply (IH (q + 1)%Z); lia.
      + cond_cleanup B3.
        replace (Z_to_bv 64 (q + 1)) with a1 by (apply bv_eq; rewrite unsigned_lit by lia; lia).
        apply postA; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM"] Lemma char_entry : forall (q : Z) (sd x5 x6 x8 x9 x10 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= q)%Z -> (q < bv_unsigned a1)%Z ->
      evt PSEGS POST
        (MS (mkR ra SP' gp tp x5 x6 (Z_to_bv 64 q) x8 x9 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                 x28 x29 x30 x31)
            F (Z_to_bv 64 0x292e4) fc None m1 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros until x31. intros H1 H2 H3.
    pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
    step. step. step. (* [comment removed for export] *)
    eapply (char_loop _ q); try lia. apply Nat.le_refl.
  Qed.

  (* [comment removed for export] *)
  #[using="bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM"] Lemma swar4_check : forall (q : Z) (sd x5 x6 x8 x9 x10 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= q)%Z -> (q + 4 <= bv_unsigned a1)%Z ->
      evt PSEGS POST
        (MS (mkR ra SP' gp tp x5 x6 (Z_to_bv 64 q) x8 x9 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                 x28 x29 x30 x31)
            F (Z_to_bv 64 0x292b4) fc None m1 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros until x31. intros H1 H2 H3.
    pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
    pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
    do 10 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases B1.
    - clear B1.
      do 15 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B2.
      + cond_cleanup B2. apply char_entry; lia.
      + cond_cleanup B2. step. (* [comment removed for export] *)
        replace (Z_to_bv 64 (q + 4)) with a1 by (apply bv_eq; rewrite unsigned_lit by lia; lia).
        apply postA; lia.
    - clear B1.
      step. (* [comment removed for export] *)
      if_cases B2.
      + cond_cleanup B2.
        replace (Z_to_bv 64 q) with a1 by (apply bv_eq; rewrite unsigned_lit by lia; lia).
        apply postA; lia.
      + cond_cleanup B2. apply char_entry; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM"] Lemma swar4_entry : forall (q L : Z) (sd x5 x6 x8 x9 x10 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word),
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= q)%Z -> (L = bv_unsigned a1 - q)%Z -> (0 <= L)%Z ->
      evt PSEGS POST
        (MS (mkR ra SP' gp tp x5 x6 (Z_to_bv 64 q) x8 x9 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                 (Z_to_bv 64 L) x29 x30 x31)
            F (Z_to_bv 64 0x29284) fc None m1 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros until x31. intros H1 H2 HL HL0.
    pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
    pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases B1.
    - clear B1. step. (* [comment removed for export] *)
      if_cases B2.
      + cond_cleanup B2.
        replace (Z_to_bv 64 q) with a1 by (apply bv_eq; rewrite unsigned_lit by lia; lia).
        apply postA; lia.
      + cond_cleanup B2. apply char_entry; lia.
    - cond_cleanup B1.
      assert (H4 : (4 <= L)%Z).
      { eapply Z.le_trans; [exact B1|]. rewrite zb_signed, unsigned_lit by lia. destruct (Z.ltb _ _); lia. }
      clear B1.
      destruct (nth_error bs (Z.to_nat (q - bv_unsigned a0))) as [b0|] eqn:Hb0. 2:{ exfalso. apply nth_error_None in Hb0. lia. }
      destruct (nth_error bs (Z.to_nat (q + 1 - bv_unsigned a0))) as [b1|] eqn:Hb1. 2:{ exfalso. apply nth_error_None in Hb1. lia. }
      destruct (nth_error bs (Z.to_nat (q + 2 - bv_unsigned a0))) as [b2|] eqn:Hb2. 2:{ exfalso. apply nth_error_None in Hb2. lia. }
      destruct (nth_error bs (Z.to_nat (q + 3 - bv_unsigned a0))) as [b3|] eqn:Hb3. 2:{ exfalso. apply nth_error_None in Hb3. lia. }
      pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs (q + 1 - bv_unsigned a0) b1 _ DATA Hb1 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs (q - bv_unsigned a0) b0 _ DATA Hb0 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs (q + 2 - bv_unsigned a0) b2 _ DATA Hb2 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs (q + 3 - bv_unsigned a0) b3 _ DATA Hb3 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      do 6 step. (* [comment removed for export] *)
      apply swar4_check; lia.
  Qed.

  (* [comment removed for export] *)
  Definition swar8_ok (j : nat) : Prop :=
    forall (q L : Z) (sd x5 x10 x16 x17 x22 x23 x24 x25 x26 x27 : word),
      (Z.to_nat L <= j)%nat ->
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= q)%Z -> (L = bv_unsigned a1 - q)%Z -> (8 <= L)%Z ->
      evt PSEGS POST
        (MS (mkR ra SP' gp tp x5 (Z_to_bv 64 10) (Z_to_bv 64 q) (Z_to_bv 64 9259542123273814144) (Z_to_bv 64 100000000)
                 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) (Z_to_bv 64 22) x16 x17
                 (Z_to_bv 64 1095216660735) (Z_to_bv 64 4294967296000100) (Z_to_bv 64 42949672960001) (Z_to_bv 64 7)
                 x22 x23 x24 x25 x26 x27
                 (Z_to_bv 64 L) (Z_to_bv 64 10) (Z_to_bv 64 5063812098665367110) (Z_to_bv 64 14974415777481871312))
            F (Z_to_bv 64 0x291c0) fc None m1 (seg_rom PSEGS)).

  #[using="bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM"] Lemma swar8_loop : forall j, swar8_ok j.
  Proof. LiaFast.lf_pins (fun (bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    induction j as [|j IH]; unfold swar8_ok; intros until x27; intros MEAS H1 H2 HL H8.
    - exfalso. lia.
    - pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
      pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
      destruct (nth_error bs (Z.to_nat (q - bv_unsigned a0))) as [b0|] eqn:Hb0. 2:{ exfalso. apply nth_error_None in Hb0. lia. }
      destruct (nth_error bs (Z.to_nat (q + 1 - bv_unsigned a0))) as [b1|] eqn:Hb1. 2:{ exfalso. apply nth_error_None in Hb1. lia. }
      destruct (nth_error bs (Z.to_nat (q + 2 - bv_unsigned a0))) as [b2|] eqn:Hb2. 2:{ exfalso. apply nth_error_None in Hb2. lia. }
      destruct (nth_error bs (Z.to_nat (q + 3 - bv_unsigned a0))) as [b3|] eqn:Hb3. 2:{ exfalso. apply nth_error_None in Hb3. lia. }
      destruct (nth_error bs (Z.to_nat (q + 4 - bv_unsigned a0))) as [b4|] eqn:Hb4. 2:{ exfalso. apply nth_error_None in Hb4. lia. }
      destruct (nth_error bs (Z.to_nat (q + 5 - bv_unsigned a0))) as [b5|] eqn:Hb5. 2:{ exfalso. apply nth_error_None in Hb5. lia. }
      destruct (nth_error bs (Z.to_nat (q + 6 - bv_unsigned a0))) as [b6|] eqn:Hb6. 2:{ exfalso. apply nth_error_None in Hb6. lia. }
      destruct (nth_error bs (Z.to_nat (q + 7 - bv_unsigned a0))) as [b7|] eqn:Hb7. 2:{ exfalso. apply nth_error_None in Hb7. lia. }
      pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs (q + 1 - bv_unsigned a0) b1 _ DATA Hb1 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs (q + 2 - bv_unsigned a0) b2 _ DATA Hb2 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs (q + 3 - bv_unsigned a0) b3 _ DATA Hb3 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs (q - bv_unsigned a0) b0 _ DATA Hb0 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      do 4 step. (* [comment removed for export] *)
      pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs (q + 4 - bv_unsigned a0) b4 _ DATA Hb4 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs (q + 5 - bv_unsigned a0) b5 _ DATA Hb5 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      step. (* [comment removed for export] *)
      pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs (q + 6 - bv_unsigned a0) b6 _ DATA Hb6 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs (q + 7 - bv_unsigned a0) b7 _ DATA Hb7 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      do 13 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B1.
      { clear B1. apply swar4_check; lia. }
      clear B1.
      do 14 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B2.
      + cond_cleanup B2.
        assert (H16 : (8 <= L + -8)%Z).
        { assert (T : (bv_signed (Z_to_bv 64 (L + -8)) <= L + -8)%Z) by (rewrite zb_signed, unsigned_lit by lia; destruct (Z.ltb _ _); lia). lia. }
        eapply (IH (q + 8)%Z (L + -8)%Z); lia.
      + clear B2. step. (* [comment removed for export] *)
        eapply (swar4_entry (q + 8)%Z (L + -8)%Z); lia.
  Qed.

  (* [comment removed for export] *)
  #[using="bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM"] Lemma swar4_entry_w : forall (sd x5 x6 x8 x9 x10 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word),
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= bv_unsigned a1)%Z ->
      evt PSEGS POST
        (MS (mkR ra SP' gp tp x5 x6 sd x8 x9 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                 (Z_to_bv 64 (bv_unsigned a1 - bv_unsigned sd)) x29 x30 x31)
            F (Z_to_bv 64 0x29284) fc None m1 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros until x31. intros H1 H2.
    pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
    rewrite <- (Z_to_bv_bv_unsigned sd).
    eapply (swar4_entry (bv_unsigned sd)); rewrite ?unsigned_lit by lia; lia.
  Qed.

  #[using="bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM"] Lemma swar8_w : forall (sd x5 x10 x16 x17 x22 x23 x24 x25 x26 x27 : word),
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd + 8 <= bv_unsigned a1)%Z ->
      evt PSEGS POST
        (MS (mkR ra SP' gp tp x5 (Z_to_bv 64 10) sd (Z_to_bv 64 9259542123273814144) (Z_to_bv 64 100000000)
                 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) (Z_to_bv 64 22) x16 x17
                 (Z_to_bv 64 1095216660735) (Z_to_bv 64 4294967296000100) (Z_to_bv 64 42949672960001) (Z_to_bv 64 7)
                 x22 x23 x24 x25 x26 x27
                 (Z_to_bv 64 (bv_unsigned a1 - bv_unsigned sd)) (Z_to_bv 64 10) (Z_to_bv 64 5063812098665367110) (Z_to_bv 64 14974415777481871312))
            F (Z_to_bv 64 0x291c0) fc None m1 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros until x27. intros H1 H2.
    pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
    rewrite <- (Z_to_bv_bv_unsigned sd).
    eapply (swar8_loop _ (bv_unsigned sd)); rewrite ?unsigned_lit by lia; try lia.
    apply Nat.le_refl.
  Qed.

  (* [comment removed for export] *)
  #[using="bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM"] Lemma after_zeros : forall (sd x5 x7 x10 x16 x17 x28 x29 x30 x31 : word),
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= bv_unsigned a1)%Z ->
      evt PSEGS POST
        (MS (mkR ra SP' gp tp x5 (Z_to_bv 64 10) x7 s0 s1 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) (Z_to_bv 64 22) x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x29158) fc None m1 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (bs rold LEN SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros until x31. intros H1 H2.
    pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
    pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) if_false.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases B1.
    - clear B1. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      apply swar4_entry_w; lia.
    - cond_cleanup B1.
      assert (H8 : (8 <= bv_unsigned a1 - bv_unsigned sd)%Z).
      { assert (T : (bv_signed (Z_to_bv 64 (bv_unsigned a1 - bv_unsigned sd)) <= bv_unsigned a1 - bv_unsigned sd)%Z)
          by (rewrite zb_signed, unsigned_lit by lia; destruct (Z.ltb _ _); lia). lia. }
      clear B1.
      do 20 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      apply swar8_w; lia.
  Qed.

  (* [comment removed for export] *)
  Definition zero_ok (j : nat) : Prop :=
    forall (z : Z) (x5 x7 x10 x16 x28 x29 x30 x31 : word),
      (Z.to_nat (bv_unsigned a1 - z) <= j)%nat ->
      (bv_unsigned a0 <= z)%Z -> (z < bv_unsigned a1)%Z ->
      evt PSEGS POST
        (MS (mkR ra SP' gp tp x5 (Z_to_bv 64 10) x7 s0 s1 x10 a1 a2 (Z_to_bv 64 z) (Z_to_bv 64 FCI_OPT2) (Z_to_bv 64 22) x16 (Z_to_bv 64 48)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x29144) fc None m1 (seg_rom PSEGS)).

  #[using="bs rold LEN LE SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM"] Lemma zero_loop : forall j, zero_ok j.
  Proof. LiaFast.lf_pins (fun (bs rold LEN LE SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    induction j as [|j IH]; unfold zero_ok; intros until x31; intros MEAS H1 H2.
    - exfalso. lia.
    - pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
      destruct (nth_error bs (Z.to_nat (z - bv_unsigned a0))) as [c|] eqn:Hc.
      2:{ exfalso. apply nth_error_None in Hc. lia. }
      pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs (z - bv_unsigned a0) c _ DATA Hc ltac:(lia) eq_refl) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      if_cases B1.
      { clear B1. apply after_zeros; rewrite ?unsigned_lit by lia; lia. }
      clear B1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B2.
      + cond_cleanup B2. eapply (IH (z + 1)%Z); lia.
      + cond_cleanup B2. step. (* [comment removed for export] *)
        apply after_zeros; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="bs rold LEN LE SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM"] Lemma body : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
      evt PSEGS POST
        (MS (mkR ra SP' gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 FCI_FMT) (Z_to_bv 64 FCI_OPT2) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x290c4) fc None m1 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (bs rold LEN LE SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros. unfold FCI_FMT.
    pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) if_true.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases B0.
    { clear B0. eapply exit_ec; eassumption. }
    cond_cleanup B0.
    unfold FCI_OPT2.
    step. step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) if_false.
    fold FCI_OPT2.
    destruct (nth_error bs 0) as [c0|] eqn:Hc0. 2:{ exfalso. apply nth_error_None in Hc0. lia. }
    pose proof (u8ro_read PSEGS m1 (bv_unsigned a0) bs 0 c0 _ DATA Hc0 ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *) clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases B1.
    - clear B1. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B2.
      + cond_cleanup B2. apply after_zeros; rewrite ?unsigned_lit by lia; lia.
      + cond_cleanup B2. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        eapply (zero_loop _ (bv_unsigned a0 + 1)%Z); try lia. apply Nat.le_refl.
    - clear B1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) if_true.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) if_not_taken.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      rewrite <- (Z_to_bv_bv_unsigned a0).
      eapply (zero_loop _ (bv_unsigned a0)); try lia. apply Nat.le_refl.
  Qed.
End Proof.

Lemma from_chars_int_spec_hw : from_chars_int_stmt_hw.
Proof.
  unfold from_chars_int_stmt_hw. intros until rold. intros Ha3 Ha4 DATA LEN LE OBJ ST PR SEP1 SEP2 SEP3 RO2 RO3.
  subst a3 a4.
  pose proof (munch_refl (from_chars_int_W sp a2) m) as MU. 
  pose proof (wmono_refl PSEGS m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
  pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2.
  pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
  unfold from_chars_int_W in MU.
  carve_frame 96%nat ST.
  do 13 step. (* [comment removed for export] *)
  eapply body; try eassumption; try lia.
Qed.

Lemma from_chars_int_spec : from_chars_int_stmt.
Proof. exact (from_chars_int_stmt_of_hw from_chars_int_spec_hw). Qed.
End P_from_chars_int.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section Proof.
  Set Default Proof Using "All".
  Hypothesis small_mul_spec : small_mul_stmt.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i : word).
  Variables (resv numv mdw dv : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (iptr fptr : word) (ibs fbs : list byte).
  Variables (ilen flen maxd : Z).
  Hypothesis Hilen : ilen = Z.of_nat (length ibs).
  Hypothesis Hflen : flen = Z.of_nat (length fbs).
  Hypothesis Hmaxd : maxd = bv_unsigned mdw.
  Hypothesis Hws : length ws = 62%nat.
  Hypothesis MAXD : (0 < maxd <= 769)%Z.
  Hypothesis XAL : (bv_unsigned resv mod 8 = 0)%Z.
  Hypothesis ALIGN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis INZ : (bv_unsigned iptr <> 0)%Z.
  Hypothesis IEND : (bv_unsigned iptr + ilen < 2^64)%Z.
  Hypothesis ILEN : (0 <= ilen < 2^40)%Z.
  Hypothesis FEND : (bv_unsigned fptr + flen < 2^64)%Z.
  Hypothesis FLEN : (0 <= flen < 2^40)%Z.
  Hypothesis FNULL : boxed (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z.
  Hypothesis FBS0 : boxed (bytes_at PSEGS m0 (bv_unsigned fptr) fbs).
  Hypothesis LAY0 : (0x22000 <= bv_unsigned sp - 144)%Z.
  Hypothesis LAY1 : (bv_unsigned sp <= bv_unsigned numv + 32)%Z.
  Hypothesis LAY2 : (bv_unsigned numv + 64 <= bv_unsigned resv)%Z.
  Hypothesis LAY3 : (bv_unsigned resv + 498 <= bv_unsigned dv)%Z.
  Hypothesis LAY4 : (bv_unsigned dv + 8 <= bv_unsigned iptr \/ 16 <= bv_unsigned iptr /\ bv_unsigned iptr + Z.of_nat (length ibs) <= bv_unsigned sp - 144)%Z.
  Hypothesis LAY5 : boxed (bv_unsigned fptr <> 0 -> bv_unsigned dv + 8 <= bv_unsigned fptr \/ 16 <= bv_unsigned fptr /\ bv_unsigned fptr + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z.

  Notation A := (bv_unsigned resv).
  Notation D := (bv_unsigned dv).
  Notation NP := (bv_unsigned numv).
  Notation IP := (bv_unsigned iptr).
  Notation FP := (bv_unsigned fptr).
  Notation SP := (bv_unsigned sp).
  Notation W := [((SP - 144)%Z, SP); (A, (A + 498)%Z); (D, (D + 8)%Z)].
  Notation POST := (parse_mantissa_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i F fc A D maxd ws m0).
  Notation FRHI m := (rw_cells PSEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells PSEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 resv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 dv) as RDv; unfold bv_modulus in RDv;
    pose proof (bv_unsigned_in_range 64 numv) as RN; unfold bv_modulus in RN;
    pose proof (bv_unsigned_in_range 64 iptr) as RI; unfold bv_modulus in RI;
    pose proof (bv_unsigned_in_range 64 fptr) as RF; unfold bv_modulus in RF;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp.

  #[local] Definition end_ok := Eval cbv beta delta [P_parse_mantissa_1.end_ok] in (@P_parse_mantissa_1.end_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv dv F fc m0 ws maxd).
  #[local] Definition end_proof := (@P_parse_mantissa_1.end_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition diginc_ok := Eval cbv beta delta [P_parse_mantissa_1.diginc_ok] in (@P_parse_mantissa_1.diginc_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv dv F fc m0 ws maxd).
  #[local] Definition diginc_proof := (@P_parse_mantissa_1.diginc_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  Notation FRLO3 w8 w16 w24 m := (rw_cells PSEGS m (SP + -144) [C8 numv; C8 w8; C8 w16; C8 w24; C8 resv]).
  Notation ADDV ws1 n1 y K := (boxed (bnorm ws1 n1 /\ (0 <= y)%Z /\ (bval ws1 n1 + y < 2 ^ (64 * K))%Z /\ (0 <= K <= 61)%Z)).

  #[local] Definition cap_of_K := (@P_parse_mantissa_1.cap_of_K small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition rupush_ok := Eval cbv beta delta [P_parse_mantissa_1.rupush_ok] in (@P_parse_mantissa_1.rupush_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws maxd).
  #[local] Definition rupush_proof := (@P_parse_mantissa_1.rupush_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ru1add_ok := Eval cbv beta delta [P_parse_mantissa_1.ru1add_ok] in (@P_parse_mantissa_1.ru1add_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws maxd).
  #[local] Definition ru1add_proof := (@P_parse_mantissa_1.ru1add_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ru2add_ok := Eval cbv beta delta [P_parse_mantissa_1.ru2add_ok] in (@P_parse_mantissa_1.ru2add_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws maxd).
  #[local] Definition ru2add_proof := (@P_parse_mantissa_1.ru2add_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ru_ok := Eval cbv beta delta [P_parse_mantissa_1.ru_ok] in (@P_parse_mantissa_1.ru_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws maxd).
  #[local] Definition ru1_proof := (@P_parse_mantissa_1.ru1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ru2_proof := (@P_parse_mantissa_1.ru2_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftb1_ok := Eval cbv beta delta [P_parse_mantissa_1.ftb1_ok] in (@P_parse_mantissa_1.ftb1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition ftb8_ok := Eval cbv beta delta [P_parse_mantissa_1.ftb8_ok] in (@P_parse_mantissa_1.ftb8_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition ftb_ok := Eval cbv beta delta [P_parse_mantissa_1.ftb_ok] in (@P_parse_mantissa_1.ftb_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition ftaend_ok := Eval cbv beta delta [P_parse_mantissa_1.ftaend_ok] in (@P_parse_mantissa_1.ftaend_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition fta1_ok := Eval cbv beta delta [P_parse_mantissa_1.fta1_ok] in (@P_parse_mantissa_1.fta1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fta8_ok := Eval cbv beta delta [P_parse_mantissa_1.fta8_ok] in (@P_parse_mantissa_1.fta8_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fta_ok := Eval cbv beta delta [P_parse_mantissa_1.fta_ok] in (@P_parse_mantissa_1.fta_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition itb_ok := Eval cbv beta delta [P_parse_mantissa_1.itb_ok] in (@P_parse_mantissa_1.itb_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition ita_ok := Eval cbv beta delta [P_parse_mantissa_1.ita_ok] in (@P_parse_mantissa_1.ita_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition it1_ok := Eval cbv beta delta [P_parse_mantissa_1.it1_ok] in (@P_parse_mantissa_1.it1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition it8_ok := Eval cbv beta delta [P_parse_mantissa_1.it8_ok] in (@P_parse_mantissa_1.it8_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition it_ok := Eval cbv beta delta [P_parse_mantissa_1.it_ok] in (@P_parse_mantissa_1.it_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr PSEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).

  #[local] Definition ftb1_proof := (@P_parse_mantissa_1.ftb1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftb8_proof := (@P_parse_mantissa_1.ftb8_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftb_proof := (@P_parse_mantissa_1.ftb_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftaend_proof := (@P_parse_mantissa_1.ftaend_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fta1_proof := (@P_parse_mantissa_1.fta1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fta8_proof := (@P_parse_mantissa_1.fta8_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fta_proof := (@P_parse_mantissa_1.fta_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fbs_now := (@P_parse_mantissa_1.fbs_now small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition itb_proof := (@P_parse_mantissa_1.itb_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ita_proof := (@P_parse_mantissa_1.ita_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition it1_proof := (@P_parse_mantissa_1.it1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition it8_proof := (@P_parse_mantissa_1.it8_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition it_proof := (@P_parse_mantissa_1.it_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition itadd_ok := Eval cbv beta delta [P_parse_mantissa_1.itadd_ok] in (@P_parse_mantissa_1.itadd_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition itadd_proof := (@P_parse_mantissa_1.itadd_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftadd_ok := Eval cbv beta delta [P_parse_mantissa_1.ftadd_ok] in (@P_parse_mantissa_1.ftadd_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition ftadd_proof := (@P_parse_mantissa_1.ftadd_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition iadd_ok := Eval cbv beta delta [P_parse_mantissa_1.iadd_ok] in (@P_parse_mantissa_1.iadd_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition iadd_proof := (@P_parse_mantissa_1.iadd_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fadd_ok := Eval cbv beta delta [P_parse_mantissa_1.fadd_ok] in (@P_parse_mantissa_1.fadd_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition fadd_proof := (@P_parse_mantissa_1.fadd_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  Definition itrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> ADDV cur (Z.to_nat len) (bv_unsigned vw) K -> (0 <= K <= dg / 19 + 2)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (IP + ilen)) p x23 vw x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x257c8) fc None m (seg_rom PSEGS)).

  Definition ftrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (w8 w16 w24 : word) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLO3 w8 w16 w24 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> ADDV cur (Z.to_nat len) (bv_unsigned vw) K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at PSEGS m FP fbs -> (FP <> 0)%Z -> (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (FP + flen)) x20 p x22 vw x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25884) fc None m (seg_rom PSEGS)).

  Lemma itrunc_proof : it_ok -> (forall k, itadd_ok k) -> itrunc_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IT ADD. unfold itrunc_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB AV KB Hoff Hp; pre.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    step. (* [comment removed for export] *)
    if_cases Hz; cond_cleanup Hz.
    - (* [comment removed for export] *)
      eapply IT; try eassumption; try lia.
      unfold boxed in AV |- *. destruct AV as (BN & _ & BV & _). split; [exact BN| lia].
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite zx16_lit by lia.
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 len) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len))) by (f_equal; lia).
      replace (Z_to_bv 64 (len + 1)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len) - Z.of_nat 0 + 1)) by (f_equal; lia).
      eapply (ADD (Z.to_nat len) K 0%nat resv vw (bv_unsigned vw)); try eassumption; try lia.
      + (* [comment removed for export] *)
        intros. eapply IT; try eassumption; try lia.
      + replace (Z.of_nat (Z.to_nat len)) with len by lia. exact XC.
      + unfold boxed. apply sad_inv_init.
  Qed.

  Lemma ftrunc_proof : ftb_ok -> (forall k, ftadd_ok k) -> ftrunc_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FT ADD. unfold ftrunc_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB AV KB FBS FNZ Hoff Hp; pre.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    step. (* [comment removed for export] *)
    if_cases Hz; cond_cleanup Hz.
    - eapply FT; try eassumption; try lia.
      unfold boxed in AV |- *. destruct AV as (BN & _ & BV & _). split; [exact BN| lia].
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite zx16_lit by lia.
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 len) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len))) by (f_equal; lia).
      replace (Z_to_bv 64 (len + 1)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len) - Z.of_nat 0 + 1)) by (f_equal; lia).
      eapply (ADD (Z.to_nat len) K 0%nat resv vw (bv_unsigned vw)); try eassumption; try lia.
      + intros. eapply FT; try eassumption; try lia. apply fbs_now; assumption.
      + replace (Z.of_nat (Z.to_nat len)) with len by lia. exact XC.
      + unfold boxed. apply sad_inv_init.
  Qed.
  Definition fback_ok (kk : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 88576) m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs -> bytes_at PSEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 37)%Z -> ((off < length fbs)%nat -> 19 * K <= dg + 18)%Z -> (dg < maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off <= Z.of_nat kk)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 (Z_to_bv 64 8) dv (Z_to_bv 64 17) x10 x11 x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 (FP + flen)) (Z_to_bv 64 10) p (Z_to_bv 64 1095216660735) x23 x24 (Z_to_bv 64 100000000) (Z_to_bv 64 4294967296000100) (Z_to_bv 64 42949672960001) (Z_to_bv 64 14974415777481871312) x29 x30 x31)
            F (Z_to_bv 64 0x257c0) fc None m (seg_rom PSEGS)).

  Definition fmul_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 88576) m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs -> bytes_at PSEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (cnt = 19 \/ off = length fbs \/ dg = maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 17) (Z_to_bv 64 cnt) x11 x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 (FP + flen)) (Z_to_bv 64 10) p (Z_to_bv 64 1095216660735) vw (Z_to_bv 64 dg) (Z_to_bv 64 100000000) (Z_to_bv 64 4294967296000100) (Z_to_bv 64 42949672960001) x28 x29 x30 x31)
            F (Z_to_bv 64 0x25748) fc None m (seg_rom PSEGS)).

  Definition f1_ok (kk : nat) (k : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 88576) m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs -> bytes_at PSEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 18)%Z -> (Z.to_nat (19 - cnt) <= k)%nat -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (dg < maxd)%Z -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 17) (Z_to_bv 64 cnt) x11 x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 (FP + flen)) (Z_to_bv 64 10) p (Z_to_bv 64 1095216660735) vw (Z_to_bv 64 dg) (Z_to_bv 64 100000000) (Z_to_bv 64 4294967296000100) (Z_to_bv 64 42949672960001) x28 x29 x30 x31)
            F (Z_to_bv 64 0x25718) fc None m (seg_rom PSEGS)).

  Definition f1entry_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 88576) m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs -> bytes_at PSEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 16)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (cnt = 0 -> (off < length fbs)%nat /\ dg < maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 17) (Z_to_bv 64 cnt) x11 x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 (FP + flen)) (Z_to_bv 64 10) p (Z_to_bv 64 1095216660735) vw (Z_to_bv 64 dg) (Z_to_bv 64 100000000) (Z_to_bv 64 4294967296000100) (Z_to_bv 64 42949672960001) x28 x29 x30 x31)
            F (Z_to_bv 64 0x25710) fc None m (seg_rom PSEGS)).

  Definition f8body_ok (kk : nat) (zf : Z) : Prop :=
    forall (off : nat) (p vw : word) (cnt0 : Z) (K : Z) (w8 : word) (x1 x5 x6 x14 x15 x16 x17 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 88576) m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs -> bytes_at PSEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0 + 18)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 (Z_to_bv 64 8) dv (Z_to_bv 64 17) (Z_to_bv 64 cnt0) (Z_to_bv 64 (flen - Z.of_nat off - 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) x14 x15 x16 x17 mdw (Z_to_bv 64 (FP + flen)) (Z_to_bv 64 10) p (Z_to_bv 64 1095216660735) vw (Z_to_bv 64 dg) (Z_to_bv 64 100000000) (Z_to_bv 64 4294967296000100) (Z_to_bv 64 42949672960001) (Z_to_bv 64 14974415777481871312) x29 x30 x31)
            F (Z_to_bv 64 0x25648) fc None m (seg_rom PSEGS)).

  Definition fout_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 88576) m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs -> bytes_at PSEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z -> (dg < maxd)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 (Z_to_bv 64 8) dv (Z_to_bv 64 17) x10 x11 x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 (FP + flen)) (Z_to_bv 64 10) p (Z_to_bv 64 1095216660735) x23 x24 (Z_to_bv 64 100000000) (Z_to_bv 64 4294967296000100) (Z_to_bv 64 42949672960001) (Z_to_bv 64 14974415777481871312) x29 x30 x31)
            F (Z_to_bv 64 0x2561c) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition TBL10 : list Z := Eval vm_compute in (map (fun k => 10 ^ Z.of_nat k)%Z (seq 0 20)).
  Lemma TBL10_ok : table_b PSEGS 88576 8 (fun v => le8 (Z_to_bv 64 v)) TBL10 = true.
  Proof. LiaFast.lf_pins LiaFast.lf_all. vm_compute. reflexivity. Qed.
  Lemma TBL10_nth : forall c, (0 <= c <= 19)%Z -> (1 <= nth (Z.to_nat c) TBL10 0 < 2^64)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros c Hc.
    assert (H : forall n, (n < 20)%nat -> (1 <= nth n TBL10 0 < 2^64)%Z).
    { intros n Hn. do 20 (destruct n as [|n]; [cbn; lia|]). lia. }
    apply H. lia.
  Qed.

  Ltac introsF := intros FRLO FRH ST XL Hcur XC DG NUM IBS FBS FNZ FPD MU WM PR LEN DGB Hw8.

  Lemma fback_proof : forall kk, end_ok -> fout_ok kk -> fback_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk END FOUT. unfold fback_ok; intros until dg; introsF; intros V HK HK1 HK2 DGM Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - eapply (FOUT off p K); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      eapply (END [C8 numv; C8 w8; C8 (Z_to_bv 64 14974415777481871312); C8 (Z_to_bv 64 88576); C8 resv]); try eassumption; try lia.
      { reflexivity. }
      all: enough (K <= (dg + 37) / 19 /\ (dg + 37) / 19 <= dg / 19 + 3)%Z by lia.
      all: split; [apply Z.div_le_lower_bound; lia|].
      all: Z.div_mod_to_equations; lia.
  Qed.

  Lemma fmul_proof : forall kk, ftrunc_ok -> fback_ok kk -> (forall k, fadd_ok k) -> fmul_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FT FB FADD. unfold fmul_ok; intros until dg; introsF; intros V HK Hcnt Hcd HKd EXIT Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit cnt) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    replace (Z_to_bv 64 (88576 + cnt * 2 ^ 3)) with (Z_to_bv 64 (88576 + 8 * cnt)) by (f_equal; lia).
    pose proof (table_read PSEGS _ _ _ _ m _ _ TBL10_ok PR ltac:(lia) ltac:(cbn; lia) cnt ltac:(cbn; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    pose proof (TBL10_nth cnt ltac:(lia)) as Hy. set (y := nth (Z.to_nat cnt) TBL10 0%Z) in *.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    unfold boxed in V. destruct V as [BN BV].
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur len).
    { exact XL. } { exact Hcur. } { exact XC. } { lia. }
    { rewrite unsigned_lit by lia. apply (cap_mul _ _ K); try lia. pose proof (bval_nonneg cur (Z.to_nat len)). lia. }
    lazymatch goal with
    | XL' : u64arr PSEGS ?m' A ?cur', XC' : rw_cells PSEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len <= ?len' <= len + 1 /\ _)%Z, HV : bval _ _ = (bval cur (Z.to_nat len) * _)%Z, HN : (_ -> bnorm cur _ -> bnorm _ _) |- _ =>
      rename XL' into XL1; rename XC' into XC1; rename HB into HB1; rename HV into HV1; rename HN into HN1;
      set (cur1 := cur') in *; set (len1 := len') in *
    end.
    rewrite unsigned_lit in HV1, HN1 by lia.
    assert (AV : ADDV cur1 (Z.to_nat len1) (bv_unsigned vw) (K + 1)).
    { unfold boxed. split; [apply HN1; [lia| exact BN]|]. split; [lia|]. split; [| lia].
      rewrite HV1. pose proof (bval_nonneg cur (Z.to_nat len)). apply addnative_bound; lia. }
    step. (* [comment removed for export] *)
    if_cases Ht; cond_cleanup Ht.
    - eapply (FT off p vw w8); try eassumption; try lia.
      all: try (apply fbs_now; [assumption| exact FNZ]).
      all: enough (K + 1 <= (dg + 36) / 19 /\ (dg + 36) / 19 <= dg / 19 + 2)%Z by lia.
      all: split; [apply Z.div_le_lower_bound; lia|]; Z.div_mod_to_equations; lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz.
      + eapply (FB off p (K + 1)%Z w8); try eassumption; try lia.
        all: try (apply fbs_now; [assumption| exact FNZ]).
        all: unfold boxed in AV |- *; destruct AV as (BN2 & _ & BV2 & _); split; [exact BN2| lia].
      + step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite zx16_lit by lia.
        step. (* [comment removed for export] *)
        replace (Z_to_bv 64 len1) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len1))) by (f_equal; lia).
        replace (Z_to_bv 64 (len1 + 1)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len1) - Z.of_nat 0 + 1)) by (f_equal; lia).
        eapply (FADD (Z.to_nat len1) (K + 1)%Z 0%nat resv vw (bv_unsigned vw)); try eassumption; try lia.
        * intros. eapply (FB off p (K + 1)%Z w8); try eassumption; try lia. all: apply fbs_now; assumption.
        * replace (Z.of_nat (Z.to_nat len1)) with len1 by lia. exact XC1.
        * unfold boxed. apply sad_inv_init.
  Qed.

  Lemma f1_proof : forall kk, fmul_ok kk -> forall k, f1_ok kk k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FM. induction k as [|k IH]; unfold f1_ok; intros until dg; introsF; intros V HK Hcnt Hk Hcd HKd DGM Hoff Hp Hkk; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block PSEGS m FP fbs off 1 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H19; cond_cleanup H19.
    { eapply (FM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K w8); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia. }
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply (FM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K w8); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia. }
    step. (* [comment removed for export] *)
    if_cases Hm; cond_cleanup Hm.
    - eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K w8); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
    - eapply (FM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K w8); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
  Qed.

  Lemma f1entry_proof : forall kk, fmul_ok kk -> (forall k, f1_ok kk k) -> f1entry_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FM F1. unfold f1entry_ok; intros until dg; introsF; intros V HK Hcnt Hcd HKd H0 Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply (FM off p vw cnt K w8); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    if_cases Hg; cond_cleanup Hg.
    { eapply (FM off p vw cnt K w8); try eassumption; try lia. }
    eapply (F1 (Z.to_nat (19 - cnt)) off p vw cnt K w8); try eassumption; try lia.
  Qed.

  Ltac f8_body_steps p FBS off :=
    pose proof (ro_block PSEGS _ FP fbs off 8 FBS ltac:(lia)) as BLK;
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia;
    do 45 step;
    clear BLK.

  Lemma f8body0_proof : forall kk, f1entry_ok kk -> f8body_ok kk 0.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FE. unfold f8body_ok; intros until dg; introsF; intros V HK Hz Hcd HKd DGM Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    f8_body_steps p FBS off.
    step. (* [comment removed for export] *)
    if_cases Hc. { exfalso. exact (f8flag0 _ Hc). } clear Hc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (FE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
    all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma f8body1_proof : forall kk, f1entry_ok kk -> f8body_ok kk 0 -> f8body_ok kk 1.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FE F80. unfold f8body_ok; intros until dg; introsF; intros V HK Hz Hcd HKd DGM Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    f8_body_steps p FBS off.
    step. (* [comment removed for export] *)
    if_cases Hc.
    - pose proof (f8flag1 (flen - Z.of_nat off - 8) ltac:(lia) Hc) as H16. clear Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb; cond_cleanup Hb.
      + eapply (FE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ 8%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; lia.
      + replace (Z_to_bv 64 (flen - Z.of_nat off - 8 + -8)) with (Z_to_bv 64 (flen - Z.of_nat (off + 8) - 8)) by (f_equal; lia).
        replace (Z_to_bv 64 (maxd - dg + -8)) with (Z_to_bv 64 (maxd - (dg + 8))) by (f_equal; lia).
        eapply (F80 (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ 8%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; lia.
    - pose proof (f8flag1' (flen - Z.of_nat off - 8) ltac:(lia) Hc) as H16. clear Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (FE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma fout_proof : end_ok -> ftrunc_ok -> (forall k, fadd_ok k) -> forall k, fout_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FT FADD. induction k as [|k IH]; unfold fout_ok; intros until dg; introsF; intros V HK HKd DGM Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (fback_proof k END IH) as FB.
    pose proof (fmul_proof k FT FB FADD) as FM.
    pose proof (f1_proof k FM) as F1.
    pose proof (f1entry_proof k FM F1) as FE.
    pose proof (f8body0_proof k FE) as F80.
    pose proof (f8body1_proof k FE F80) as F81.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (FP + flen)) by lia.
    replace (Z_to_bv 64 (FP + flen - bv_unsigned p)) with (Z_to_bv 64 (flen - Z.of_nat off)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (FE off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite Hw8. replace (Z_to_bv 64 (FP + flen - 8 - bv_unsigned p)) with (Z_to_bv 64 (flen - Z.of_nat off - 8)) by (f_equal; lia).
      step. (* [comment removed for export] *)
      rewrite <- Hmaxd. 
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit dg) in * by lia.
      if_cases Hc; cond_cleanup Hc.
      + eapply (FE off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia.
      + eapply (F81 off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia.
  Qed.
  Notation FRLOJ j1 j2 m := (rw_cells PSEGS m (SP + -144) [C8 numv; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 88576); C8 resv]).

  Definition fconst_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j1 j2 : list byte) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at PSEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 (FP + flen)) x20 p x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x255cc) fc None m (seg_rom PSEGS)).

  Definition fz1_ok (k : nat) : Prop :=
    forall (off : nat) (p fendw : word) (K : Z) (j1 j2 : list byte) (x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at PSEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> bv_unsigned fendw = (FP + flen)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 fendw (Z_to_bv 64 48) x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 (FP + flen)) x20 p x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x258cc) fc None m (seg_rom PSEGS)).

  Definition fzmid_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j1 j2 : list byte) (x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at PSEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 p x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 (FP + flen)) x20 p x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x258bc) fc None m (seg_rom PSEGS)).

  Definition fz8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (j1 j2 : list byte) (x1 x5 x6 x7 x9 x14 x15 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at PSEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 (Z_to_bv 64 (flen - Z.of_nat off)) p (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 7) x14 x15 x16 x17 mdw (Z_to_bv 64 (FP + flen)) x20 p x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25814) fc None m (seg_rom PSEGS)).

  Definition fz_ok : Prop :=
    forall (u : unit) (K : Z) (j1 j2 : list byte) (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at PSEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 (Z_to_bv 64 flen) x11 x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 (FP + flen)) x20 fptr x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x257fc) fc None m (seg_rom PSEGS)).

  Definition fset_ok : Prop :=
    forall (u : unit) (K : Z) (j1 j2 : list byte) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j1 j2 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17 mdw x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x255b0) fc None m (seg_rom PSEGS)).

  Ltac introsE := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V HK HKd.

  Lemma fconst_proof : end_ok -> (forall k, fout_ok k) -> fconst_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FOUT. unfold fconst_ok; intros until dg; introsE; intros FBS FNZ FPD Hoff Hp; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply (END [C8 numv; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 88576); C8 resv]); try eassumption; try lia. all: try reflexivity.
      all: enough (K <= (dg + 18) / 19 /\ (dg + 18) / 19 <= dg / 19 + 3)%Z by lia.
      all: split; [apply Z.div_le_lower_bound; lia|]; Z.div_mod_to_equations; lia. }
    do 19 step.
    eapply (FOUT (length fbs - off)%nat off p K (Z_to_bv 64 (FP + flen + -8))); try eassumption; try lia.
    rewrite unsigned_lit by lia. lia.
  Qed.

  Lemma fz1_proof : fconst_ok -> forall k, fz1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FC. induction k as [|k IH]; unfold fz1_ok; intros until dg; introsE; intros FBS FNZ FPD Hk Hoff Hp Hfe; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (bv_unsigned_in_range 64 fendw) as Rf; unfold bv_modulus in Rf.
    pose proof (ro_block PSEGS m FP fbs off 1 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { eapply (FC off p K j1 j2); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) fendw K j1 j2); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (FC (length fbs) fendw K j1 j2); try eassumption; try lia.
  Qed.

  Lemma fzmid_proof : end_ok -> (forall k, fz1_ok k) -> fzmid_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FZ1. unfold fzmid_ok; intros until dg; introsE; intros FBS FNZ FPD Hoff Hp; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply (END [C8 numv; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 88576); C8 resv]); try eassumption; try lia. all: try reflexivity.
      all: enough (K <= (dg + 18) / 19 /\ (dg + 18) / 19 <= dg / 19 + 3)%Z by lia.
      all: split; [apply Z.div_le_lower_bound; lia|]; Z.div_mod_to_equations; lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (FZ1 (length fbs - off)%nat off p _ K j1 j2); try eassumption; try lia.
    rewrite (unsigned_lit (FP + flen)) by lia. rewrite !unsigned_lit by lia. lia.
  Qed.

  Lemma fz8_proof : fzmid_ok -> forall k, fz8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FM. induction k as [|k IH]; unfold fz8_ok; intros until dg; introsE; intros FBS FNZ FPD Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block PSEGS m FP fbs off 8 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    do 22 step.
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { eapply (FM off p K j1 j2); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (flen - Z.of_nat off + -8)) with (Z_to_bv 64 (flen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) K j1 j2); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      eapply (FM (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) K j1 j2); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
  Qed.

  Lemma fz_proof : fzmid_ok -> (forall k, fz8_ok k) -> fz_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FM FZ8. unfold fz_ok; intros until dg; introsE; intros FBS FNZ FPD; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. (* [comment removed for export] *)
      eapply (FM 0%nat fptr K j1 j2); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 flen) with (Z_to_bv 64 (flen - Z.of_nat 0)) by (f_equal; lia).
      eapply (FZ8 (length fbs) 0%nat fptr K j1 j2); try eassumption; try lia.
  Qed.

  Lemma fset_proof : end_ok -> fz_ok -> fconst_ok -> fset_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FZ FC. unfold fset_ok; intros until dg; introsE; pre.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz; cond_cleanup Hz.
    { eapply (END [C8 numv; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 88576); C8 resv]); try eassumption; try lia. all: try reflexivity.
      all: enough (K <= (dg + 18) / 19 /\ (dg + 18) / 19 <= dg / 19 + 3)%Z by lia.
      all: split; [apply Z.div_le_lower_bound; lia|]; Z.div_mod_to_equations; lia. }
    pose proof (fbs_now m MU Hz) as FBS. pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    assert (FPD : (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z) by (unfold boxed in LAY5; apply LAY5; exact Hz).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd; cond_cleanup Hd.
    - eapply (FZ tt K j1 j2); try eassumption; try lia.
    - eapply (FC 0%nat fptr K j1 j2); try eassumption; try lia.
  Qed.
  Definition iback_ok (kk : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 88576) m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z -> ((off < length ibs)%nat -> 19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off <= Z.of_nat kk)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 (Z_to_bv 64 8) dv (Z_to_bv 64 17) x10 x11 x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 42949672960001) (Z_to_bv 64 10) (Z_to_bv 64 (IP + ilen)) p (Z_to_bv 64 1095216660735) x24 x25 (Z_to_bv 64 100000000) (Z_to_bv 64 4294967296000100) (Z_to_bv 64 14974415777481871312) x29 x30 x31)
            F (Z_to_bv 64 0x255ac) fc None m (seg_rom PSEGS)).

  Definition imul_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 88576) m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 19 \/ off = length ibs \/ dg = maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 17) (Z_to_bv 64 cnt) x11 x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 42949672960001) (Z_to_bv 64 10) (Z_to_bv 64 (IP + ilen)) p (Z_to_bv 64 1095216660735) vw (Z_to_bv 64 dg) (Z_to_bv 64 100000000) (Z_to_bv 64 4294967296000100) x28 x29 x30 x31)
            F (Z_to_bv 64 0x25534) fc None m (seg_rom PSEGS)).

  Definition i1_ok (kk : nat) (k : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 88576) m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 18)%Z -> (Z.to_nat (19 - cnt) <= k)%nat -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (dg < maxd)%Z -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 17) (Z_to_bv 64 cnt) x11 x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 42949672960001) (Z_to_bv 64 10) (Z_to_bv 64 (IP + ilen)) p (Z_to_bv 64 1095216660735) vw (Z_to_bv 64 dg) (Z_to_bv 64 100000000) (Z_to_bv 64 4294967296000100) x28 x29 x30 x31)
            F (Z_to_bv 64 0x25504) fc None m (seg_rom PSEGS)).

  Definition i1entry_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (w8 : word) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 88576) m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 16)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 0 -> (off < length ibs)%nat /\ dg < maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 17) (Z_to_bv 64 cnt) x11 x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 42949672960001) (Z_to_bv 64 10) (Z_to_bv 64 (IP + ilen)) p (Z_to_bv 64 1095216660735) vw (Z_to_bv 64 dg) (Z_to_bv 64 100000000) (Z_to_bv 64 4294967296000100) x28 x29 x30 x31)
            F (Z_to_bv 64 0x254fc) fc None m (seg_rom PSEGS)).

  Definition i8body_ok (kk : nat) (zf : Z) : Prop :=
    forall (off : nat) (p vw : word) (cnt0 : Z) (K : Z) (w8 : word) (x1 x5 x6 x14 x15 x16 x17 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 88576) m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 (Z_to_bv 64 8) dv (Z_to_bv 64 17) (Z_to_bv 64 cnt0) (Z_to_bv 64 (ilen - Z.of_nat off - 8)) (Z_to_bv 64 (maxd - dg)) (Z_to_bv 64 zf) x14 x15 x16 x17 mdw (Z_to_bv 64 42949672960001) (Z_to_bv 64 10) (Z_to_bv 64 (IP + ilen)) p (Z_to_bv 64 1095216660735) vw (Z_to_bv 64 dg) (Z_to_bv 64 100000000) (Z_to_bv 64 4294967296000100) (Z_to_bv 64 14974415777481871312) x29 x30 x31)
            F (Z_to_bv 64 0x25434) fc None m (seg_rom PSEGS)).

  Definition iout_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (w8 : word) (x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLO3 w8 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 88576) m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A cur -> length cur = 62%nat -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w8 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 (Z_to_bv 64 8) dv (Z_to_bv 64 17) x10 x11 x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 42949672960001) (Z_to_bv 64 10) (Z_to_bv 64 (IP + ilen)) p (Z_to_bv 64 1095216660735) x24 x25 (Z_to_bv 64 100000000) (Z_to_bv 64 4294967296000100) (Z_to_bv 64 14974415777481871312) x29 x30 x31)
            F (Z_to_bv 64 0x25408) fc None m (seg_rom PSEGS)).

  Ltac introsI := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB Hw8.

  Lemma frlo3_to_J : forall m a b, FRLO3 a b (Z_to_bv 64 88576) m -> FRLOJ (le8 a) (le8 b) m.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m a b [[W B] R]. split; [split|].
    - cbn. repeat split; try reflexivity; try apply length_le8. all: exact I.
    - exact B.
    - exact R.
  Qed.

  Lemma iback_proof : forall kk, fset_ok -> iout_ok kk -> iback_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FS IOUT. unfold iback_ok; intros until dg; introsI; intros V HK HK1 HK2 DGM Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - eapply (IOUT off p K w8); try eassumption; try lia.
    - eapply (FS tt K (le8 w8) (le8 (Z_to_bv 64 14974415777481871312))); try eassumption; try lia.
      apply frlo3_to_J. exact FRLO.
  Qed.

  Lemma imul_proof : forall kk, itrunc_ok -> iback_ok kk -> (forall k, iadd_ok k) -> imul_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IT IB IADD. unfold imul_ok; intros until dg; introsI; intros V HK Hcnt Hcd HKd EXIT Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit cnt) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    replace (Z_to_bv 64 (88576 + cnt * 2 ^ 3)) with (Z_to_bv 64 (88576 + 8 * cnt)) by (f_equal; lia).
    pose proof (table_read PSEGS _ _ _ _ m _ _ TBL10_ok PR ltac:(lia) ltac:(cbn; lia) cnt ltac:(cbn; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    pose proof (TBL10_nth cnt ltac:(lia)) as Hy. set (y := nth (Z.to_nat cnt) TBL10 0%Z) in *.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    unfold boxed in V. destruct V as [BN BV].
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur len).
    { exact XL. } { exact Hcur. } { exact XC. } { lia. }
    { rewrite unsigned_lit by lia. apply (cap_mul _ _ K); try lia. pose proof (bval_nonneg cur (Z.to_nat len)). lia. }
    lazymatch goal with
    | XL' : u64arr PSEGS ?m' A ?cur', XC' : rw_cells PSEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len <= ?len' <= len + 1 /\ _)%Z, HV : bval _ _ = (bval cur (Z.to_nat len) * _)%Z, HN : (_ -> bnorm cur _ -> bnorm _ _) |- _ =>
      rename XL' into XL1; rename XC' into XC1; rename HB into HB1; rename HV into HV1; rename HN into HN1;
      set (cur1 := cur') in *; set (len1 := len') in *
    end.
    rewrite unsigned_lit in HV1, HN1 by lia.
    assert (AV : ADDV cur1 (Z.to_nat len1) (bv_unsigned vw) (K + 1)).
    { unfold boxed. split; [apply HN1; [lia| exact BN]|]. split; [lia|]. split; [| lia].
      rewrite HV1. pose proof (bval_nonneg cur (Z.to_nat len)). apply addnative_bound; lia. }
    step. (* [comment removed for export] *)
    if_cases Ht; cond_cleanup Ht.
    - eapply (IT off p vw w8); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz; cond_cleanup Hz.
      + eapply (IB off p (K + 1)%Z w8); try eassumption; try lia.
        all: unfold boxed in AV |- *; destruct AV as (BN2 & _ & BV2 & _); split; [exact BN2| lia].
      + step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite zx16_lit by lia.
        step. (* [comment removed for export] *)
        replace (Z_to_bv 64 len1) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len1))) by (f_equal; lia).
        replace (Z_to_bv 64 (len1 + 1)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat len1) - Z.of_nat 0 + 1)) by (f_equal; lia).
        eapply (IADD (Z.to_nat len1) (K + 1)%Z 0%nat resv vw (bv_unsigned vw)); try eassumption; try lia.
        * intros. eapply (IB off p (K + 1)%Z w8); try eassumption; try lia.
        * replace (Z.of_nat (Z.to_nat len1)) with len1 by lia. exact XC1.
        * unfold boxed. apply sad_inv_init.
  Qed.

End Proof.
