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
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Wbig_tac Wbig_bigadd.

Module U_small_mul_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition small_mul_entry : Z := 0x26c94.

Definition small_mul_W (A : Z) : list ivl := [(A, A + 498)]%Z.

Definition small_mul_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (A y : Z) (ws : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 : word) (m' : word -> option byte) (ws' : list word) (len' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch (small_mul_W A) m m'
    /\ wmono USEGS m m'
    /\ u64arr USEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells USEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (len <= len' <= len + 1 /\ len' <= 62)%Z
    /\ bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) * y)%Z
    /\ (y <> 0%Z -> bnorm ws (Z.to_nat len) -> bnorm ws' (Z.to_nat len')).

Definition small_mul_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z),
    u64arr USEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells USEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z ->
    (bval ws (Z.to_nat len) * bv_unsigned a1 < BIG_CAP)%Z ->
    evt USEGS (small_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 F fc (bv_unsigned a0) (bv_unsigned a1) ws len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x26c94) fc None m (seg_rom USEGS)).
End U_small_mul_stmt.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_small_add_stmt.

Module U_parse_mantissa_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition parse_mantissa_entry : Z := 0x25f08.
Definition parse_mantissa_frame : Z := 144.

(* [comment removed for export] *)
Definition parse_mantissa_W (sp A D : Z) : list ivl := [(sp - 144, sp); (A, A + 498); (D, D + 8)]%Z.

Definition parse_mantissa_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A D maxd : Z) (ws : list word)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                    (ws' : list word) (len' digits : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch (parse_mantissa_W (bv_unsigned sp) A D) m m'
    /\ wmono USEGS m m'
    /\ stk USEGS m' (bv_unsigned sp - 144) (bv_unsigned sp)
    /\ u64arr USEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells USEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ rw_cells USEGS m' D [C8 (Z_to_bv 64 digits)]
    /\ (0 <= len' <= 62)%Z
    /\ (0 <= digits <= maxd + 1)%Z      (* [comment removed for export] *)
    /\ bnorm ws' (Z.to_nat len')
    /\ (bval ws' (Z.to_nat len') < 2 ^ (64 * (digits / 19 + 3)))%Z.

Definition parse_mantissa_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (iptr fptr : word) (ibs fbs : list byte) (dg : word),
    stk USEGS m (bv_unsigned sp - 144) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    pristine m 0x10000 0x22000 ->
    (* [comment removed for export] *)
    u64arr USEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells USEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 0)] ->
    (bv_unsigned a0 mod 8 = 0)%Z ->
    (* [comment removed for export] *)
    rw_cells USEGS m (bv_unsigned a1 + 32)
        [C8 iptr; C8 (Z_to_bv 64 (Z.of_nat (length ibs))); C8 fptr; C8 (Z_to_bv 64 (Z.of_nat (length fbs)))] ->
    bytes_at USEGS m (bv_unsigned iptr) ibs -> (bv_unsigned iptr <> 0)%Z ->
    (bv_unsigned iptr + Z.of_nat (length ibs) < 2^64)%Z -> (Z.of_nat (length ibs) < 2^40)%Z ->
    bytes_at USEGS m (bv_unsigned fptr) fbs ->
    (bv_unsigned fptr + Z.of_nat (length fbs) < 2^64)%Z -> (Z.of_nat (length fbs) < 2^40)%Z ->
    (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z ->
    (* [comment removed for export] *)
    (0 < bv_unsigned a2 <= 769)%Z ->
    (* [comment removed for export] *)
    rw_cells USEGS m (bv_unsigned a3) [C8 dg] ->
    (* [comment removed for export] *)
    (0x22000 <= bv_unsigned sp - 144)%Z ->
    (bv_unsigned sp <= bv_unsigned a1 + 32)%Z ->
    (bv_unsigned a1 + 64 <= bv_unsigned a0)%Z ->
    (bv_unsigned a0 + 498 <= bv_unsigned a3)%Z ->
    (bv_unsigned a3 + 8 <= bv_unsigned iptr \/ 16 <= bv_unsigned iptr /\ bv_unsigned iptr + Z.of_nat (length ibs) <= bv_unsigned sp - 144)%Z ->   (* [comment removed for export] *)
    (bv_unsigned fptr <> 0 -> bv_unsigned a3 + 8 <= bv_unsigned fptr \/ 16 <= bv_unsigned fptr /\ bv_unsigned fptr + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->   (* [comment removed for export] *)
    evt USEGS (parse_mantissa_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a2) ws m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x25f08) fc None m (seg_rom USEGS)).
End U_parse_mantissa_stmt.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_bigadd OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_parse_mantissa.U_small_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_small_add_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_parse_mantissa.U_parse_mantissa_stmt.

Module U_parse_mantissa_1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_small_add_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_bigadd OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_parse_mantissa.U_small_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_small_add_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_parse_mantissa.U_parse_mantissa_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition boxed (P : Prop) : Prop := P.

Section Proof.
  Set Default Proof Using "All".
  Hypothesis small_mul_spec : small_mul_stmt.
  Hypothesis small_add_spec : small_add_stmt.
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
  Hypothesis FBS0 : boxed (bytes_at USEGS m0 (bv_unsigned fptr) fbs).
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
  Notation FRHI m := (rw_cells USEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells USEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
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
      rw_cells USEGS m (SP + -144) lo -> Z.of_nat (cells_size lo) = 40%Z ->
      FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono USEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd + 1)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 3)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26808) fc None m (seg_rom USEGS)).

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
      rw_cells USEGS m (SP + -144) lo -> Z.of_nat (cells_size lo) = 40%Z ->
      FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono USEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 3)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x267fc) fc None m (seg_rom USEGS)).

  Lemma diginc_proof : end_ok -> diginc_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END. unfold diginc_ok. intros until K. intros FRLO LOSZ FRH ST XL Hcur XC DG MU WM LEN DGB V KB. bounds.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply END; try eassumption; try lia.
    all: enough (dg / 19 <= (dg + 1) / 19)%Z by lia; apply Z.div_le_mono; lia.
  Qed.

  Lemma cap_of_K : forall v K, (v < 2 ^ (64 * K))%Z -> (0 <= K <= 62)%Z -> (v < BIG_CAP)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros v K Hv HK. unfold BIG_CAP. eapply Z.lt_le_trans; [exact Hv|]. apply Z.pow_le_mono_r; lia.
  Qed.

  Notation FRLOU j0 w16 m := (rw_cells USEGS m (SP + -144) [CB 8 j0; C8 numv; C8 w16; C8 (Z_to_bv 64 88584); C8 resv]).

  (* [comment removed for export] *)
  Definition ru_ok : Prop :=
    forall (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] ->
      munch W m0 m -> wmono USEGS m0 m ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x267e0) fc None m (seg_rom USEGS)).

  Lemma ru_proof : diginc_ok -> ru_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros DIG; unfold ru_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG MU WM LEN DGB V KB; bounds.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    unfold boxed in V. destruct V as [BN BV].
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur len).
    { exact XL. } { exact Hcur. } { exact XC. } { lia. }
    { rewrite unsigned_lit by lia. apply (cap_mul _ _ K); try lia. pose proof (bval_nonneg cur (Z.to_nat len)). lia. }
    lazymatch goal with
    | XL' : u64arr USEGS ?m' A ?cur', XC' : rw_cells USEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len <= ?len' <= len + 1 /\ _)%Z, HV : bval _ _ = (bval cur (Z.to_nat len) * _)%Z, HN : (_ -> bnorm cur _ -> bnorm _ _) |- _ =>
      rename XL' into XL1; rename XC' into XC1; rename HB into HB1; rename HV into HV1; rename HN into HN1;
      set (cur1 := cur') in *; set (len1 := len') in *
    end.
    rewrite unsigned_lit in HV1, HN1 by lia.
    pose proof (u64arr_bound _ _ _ _ XL1) as BdX1. lazymatch goal with H : length cur1 = 62%nat |- _ => rename H into Hcur1 end. rewrite Hcur1 in BdX1.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call (small_add_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur1 len1).
    { exact XL1. } { exact Hcur1. } { exact XC1. } { lia. }
    { rewrite unsigned_lit by lia. rewrite HV1. pose proof (bval_nonneg cur (Z.to_nat len)).
      eapply cap_of_K with (K := (K + 1)%Z); [| lia]. apply addnative_bound; lia. }
    lazymatch goal with
    | XL' : u64arr USEGS ?m' A ?cur', XC' : rw_cells USEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len1 <= ?len' <= len1 + 1 /\ _)%Z, HV : bval _ _ = (bval cur1 (Z.to_nat len1) + _)%Z, HN : (bnorm cur1 _ -> bnorm _ _) |- _ =>
      rename XL' into XL2; rename XC' into XC2; rename HB into HB2; rename HV into HV2; rename HN into HN2;
      set (cur2 := cur') in *; set (len2 := len') in *
    end.
    rewrite unsigned_lit in HV2 by lia.
    eapply (DIG [CB 8 j0; C8 numv; C8 w16; C8 (Z_to_bv 64 88584); C8 resv] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur2 len2 dg (K + 1)%Z);
      try eassumption; try reflexivity; try lia.
    unfold boxed. split. { apply HN2. apply HN1; [lia| exact BN]. }
    rewrite HV2, HV1. pose proof (bval_nonneg cur (Z.to_nat len)). apply addnative_bound; lia.
  Qed.
  Definition ftb1_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 (Z_to_bv 64 48) (Z_to_bv 64 (-1)) x12 x13 x14 x15 x16 x17 x18 x19 p x21 (Z_to_bv 64 (FP + flen)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x266b4) fc None m (seg_rom USEGS)).

  Definition ftb8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x9 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 (Z_to_bv 64 (flen - Z.of_nat off)) (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) x14 x15 x16 x17 x18 x19 p x21 (Z_to_bv 64 (FP + flen)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2663c) fc None m (seg_rom USEGS)).

  Definition ftb_ok : Prop :=
    forall (off : nat) (p : word) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 p x21 (Z_to_bv 64 (FP + flen)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26620) fc None m (seg_rom USEGS)).

  Definition ftaend_ok : Prop :=
    forall (fw : word) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 fw x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x267dc) fc None m (seg_rom USEGS)).

  Definition fta1_ok (k : nat) : Prop :=
    forall (off : nat) (p fw : word) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x9 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 fw p (Z_to_bv 64 (FP + flen)) (Z_to_bv 64 48) (Z_to_bv 64 (-1)) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x267c8) fc None m (seg_rom USEGS)).

  Definition fta8_ok (k : nat) : Prop :=
    forall (off : nat) (p fw remw : word) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> remw = Z_to_bv 64 (flen - Z.of_nat off) ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 fw p fptr (Z_to_bv 64 flen) (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) remw x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2674c) fc None m (seg_rom USEGS)).

  Definition fta_ok : Prop :=
    forall (fw : word) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 fw x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26710) fc None m (seg_rom USEGS)).

  Definition it1_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x9 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 (Z_to_bv 64 48) (Z_to_bv 64 (-1)) x13 x14 x15 x16 x17 x18 x19 x20 x21 p (Z_to_bv 64 (IP + ilen)) x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26534) fc None m (seg_rom USEGS)).

  Definition it8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x9 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (length ibs - off <= k)%nat -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 (Z_to_bv 64 (ilen - Z.of_nat off)) (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) x14 x15 x16 x17 x18 x19 x20 x21 p (Z_to_bv 64 (IP + ilen)) x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x264bc) fc None m (seg_rom USEGS)).

  Definition it_ok : Prop :=
    forall (off : nat) (p : word) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg K : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K <= dg / 19 + 2)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 p (Z_to_bv 64 (IP + ilen)) x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x264a0) fc None m (seg_rom USEGS)).

  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr USEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).
  Ltac ENDAP := lazymatch goal with FRLO : rw_cells USEGS ?m (SP + -144) ?lo |- _ =>
    eapply (_ : end_ok) with (lo := lo) end.

  Lemma ftb1_proof : end_ok -> ru_ok -> forall k, ftb1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END RU. induction k as [|k IH]; unfold ftb1_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB FBS FNZ Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_not_taken.
    pose proof (ro_block USEGS m FP fbs off 1 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc.
    { clear Hc. eapply RU; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { clear He. eapply (END [CB 8 j0; C8 numv; C8 w16; C8 (Z_to_bv 64 88584); C8 resv]); try eassumption; try lia. reflexivity. }
    step. (* [comment removed for export] *)
    eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1))); try eassumption; try lia.
    all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma ftb8_proof : end_ok -> ru_ok -> (forall k, ftb1_ok k) -> forall k, ftb8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END RU T1. induction k as [|k IH]; unfold ftb8_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB FBS FNZ Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block USEGS m FP fbs off 8 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    do 22 step.
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc.
    { clear Hc. eapply RU; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (flen - Z.of_nat off + -8)) with (Z_to_bv 64 (flen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { clear He. eapply (END [CB 8 j0; C8 numv; C8 w16; C8 (Z_to_bv 64 88584); C8 resv]); try eassumption; try lia. reflexivity. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length fbs - (off + 8))%nat (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma ftb_proof : end_ok -> (forall k, ftb1_ok k) -> (forall k, ftb8_ok k) -> ftb_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END T1 T8. unfold ftb_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB FBS FNZ Hoff Hp; pre.
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
      { clear He. eapply (END [CB 8 j0; C8 numv; C8 w16; C8 (Z_to_bv 64 88584); C8 resv]); try eassumption; try lia. reflexivity. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length fbs - off)%nat off p); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T8 (length fbs - off)%nat off p); try eassumption; try lia.
  Qed.

  Lemma fbs_now : forall m, munch W m0 m -> (FP <> 0)%Z -> bytes_at USEGS m FP fbs.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m MU FNZ. bounds. unfold boxed in FBS0, LAY5. specialize (LAY5 FNZ).
    pose proof (bytes_at_bound _ _ _ _ FBS0) as BF.
    eapply (bytes_at_transport USEGS _ m0 m); [exact FBS0 | exact MU |].
    cbn [disjoint_from]. lia.
  Qed.

  Lemma ftaend_proof : end_ok -> ru_ok -> ftaend_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END RU. unfold ftaend_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB; pre.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    - eapply (END [CB 8 j0; C8 numv; C8 w16; C8 (Z_to_bv 64 88584); C8 resv]); try eassumption; try lia. reflexivity.
    - eapply RU; try eassumption; lia.
  Qed.

  Lemma fta1_proof : ftaend_ok -> ru_ok -> forall k, fta1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FE RU. induction k as [|k IH]; unfold fta1_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB FBS FNZ Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block USEGS m FP fbs off 1 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc.
    { clear Hc. eapply RU; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) fw); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - eapply FE; try eassumption; lia.
  Qed.

  Lemma fta8_proof : ftaend_ok -> ru_ok -> (forall k, fta1_ok k) -> forall k, fta8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FE RU T1. induction k as [|k IH]; unfold fta8_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB FBS FNZ Hk Hoff Hp Hrem; subst remw; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block USEGS m FP fbs off 8 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    do 22 step.
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc.
    { clear Hc. eapply RU; try eassumption; lia. }
    clear Hc.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) fw); try eassumption; try lia.
      all: try (f_equal; lia). all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { eapply FE; try eassumption; lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length fbs - (off + 8))%nat (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) fw); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma fta_proof : end_ok -> ftaend_ok -> (forall k, fta1_ok k) -> (forall k, fta8_ok k) -> fta_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FE T1 T8. unfold fta_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB; pre.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz; cond_cleanup Hz.
    { eapply FE; try eassumption; lia. }
    pose proof (fbs_now m MU Hz) as FBS. pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { eapply FE; try eassumption; lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length fbs) 0%nat fptr fw); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T8 (length fbs) 0%nat fptr fw); try eassumption; try lia. f_equal; lia.
  Qed.

  Lemma it1_proof : fta_ok -> forall k, it1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros TB. induction k as [|k IH]; unfold it1_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_not_taken.
    pose proof (ro_block USEGS m IP ibs off 1 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    - eapply TB; try eassumption; lia.
    - step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb; cond_cleanup Hb.
      + eapply TB; try eassumption; lia.
      + step. (* [comment removed for export] *)
        eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1))); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma it8_proof : fta_ok -> (forall k, it1_ok k) -> forall k, it8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros TB T1. induction k as [|k IH]; unfold it8_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block USEGS m IP ibs off 8 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    do 22 step.
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { step. (* [comment removed for export] *) eapply TB; try eassumption; lia. }
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (ilen - Z.of_nat off + -8)) with (Z_to_bv 64 (ilen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      { step. (* [comment removed for export] *) step. (* [comment removed for export] *) eapply TB; try eassumption; try lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length ibs - (off + 8))%nat (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma it_proof : fta_ok -> (forall k, it1_ok k) -> (forall k, it8_ok k) -> it_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros TB T1 T8. unfold it_ok; intros until K; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V KB Hoff Hp; pre.
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
      { step. (* [comment removed for export] *) step. (* [comment removed for export] *) eapply TB; try eassumption; try lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T1 (length ibs - off)%nat off p); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (T8 (length ibs - off)%nat off p); try eassumption; try lia.
  Qed.
  Definition itrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (cnt K : Z) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (19 * (K + 1) <= dg + 36)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 x17 x18 x19 vw x21 p (Z_to_bv 64 (IP + ilen)) x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26468) fc None m (seg_rom USEGS)).

  Definition ftrunc_ok : Prop :=
    forall (off : nat) (p vw : word) (cnt K : Z) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (19 * (K + 1) <= dg + 36)%Z ->
      bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 x17 x18 vw p x21 (Z_to_bv 64 (FP + flen)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x265e8) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition TBL10 : list Z := Eval vm_compute in (map (fun k => 10 ^ Z.of_nat k)%Z (seq 0 20)).
  Lemma TBL10_ok : table_b USEGS 88584 8 (fun v => le8 (Z_to_bv 64 v)) TBL10 = true.
  Proof. LiaFast.lf_pins LiaFast.lf_all. vm_compute. reflexivity. Qed.
  Lemma TBL10_nth : forall c, (0 <= c <= 19)%Z -> (1 <= nth (Z.to_nat c) TBL10 0 < 2^64)%Z.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros c Hc.
    assert (H : forall n, (n < 20)%nat -> (1 <= nth n TBL10 0 < 2^64)%Z).
    { intros n Hn. do 20 (destruct n as [|n]; [cbn; lia|]). lia. }
    apply H. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac muladd_calls XL Hcur XC V vw K cnt :=
    let BN := fresh "BN" in let BV := fresh "BV" in
    pose proof (table_read USEGS _ _ _ _ _ _ _ TBL10_ok ltac:(eassumption) ltac:(lia) ltac:(cbn; lia) cnt ltac:(cbn; lia)) as RD;
    step; (* [comment removed for export] *)
    clear RD;
    pose proof (TBL10_nth cnt ltac:(lia)) as Hy; set (y := nth (Z.to_nat cnt) TBL10 0%Z) in *;
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    unfold boxed in V; destruct V as [BN BV];
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    [ exact XL | exact Hcur | exact XC | lia
    | rewrite unsigned_lit by lia; apply (cap_mul _ _ K); try lia; pose proof (bval_nonneg _ _ : (0 <= bval _ _)%Z); lia
    | ].

  Lemma itrunc_proof : it_ok -> itrunc_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IT. unfold itrunc_ok; intros until dg; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V HK Hcnt HKd Hoff Hp; pre.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit cnt) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    replace (Z_to_bv 64 (88584 + cnt * 2 ^ 3)) with (Z_to_bv 64 (88584 + 8 * cnt)) by (f_equal; lia).
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL10_ok PR ltac:(lia) ltac:(cbn; lia) cnt ltac:(cbn; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    pose proof (TBL10_nth cnt ltac:(lia)) as Hy. set (y := nth (Z.to_nat cnt) TBL10 0%Z) in *.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    unfold boxed in V. destruct V as [BN BV].
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur len).
    { exact XL. } { exact Hcur. } { exact XC. } { lia. }
    { rewrite unsigned_lit by lia. apply (cap_mul _ _ K); try lia. pose proof (bval_nonneg cur (Z.to_nat len)). lia. }
    lazymatch goal with
    | XL' : u64arr USEGS ?m' A ?cur', XC' : rw_cells USEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len <= ?len' <= len + 1 /\ _)%Z, HV : bval _ _ = (bval cur (Z.to_nat len) * _)%Z, HN : (_ -> bnorm cur _ -> bnorm _ _) |- _ =>
      rename XL' into XL1; rename XC' into XC1; rename HB into HB1; rename HV into HV1; rename HN into HN1;
      set (cur1 := cur') in *; set (len1 := len') in *
    end.
    rewrite unsigned_lit in HV1, HN1 by lia.
    pose proof (u64arr_bound _ _ _ _ XL1) as BdX1. lazymatch goal with H : length cur1 = 62%nat |- _ => rename H into Hcur1 end. rewrite Hcur1 in BdX1.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call (small_add_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur1 len1).
    { exact XL1. } { exact Hcur1. } { exact XC1. } { lia. }
    { rewrite HV1. pose proof (bval_nonneg cur (Z.to_nat len)).
      eapply cap_of_K with (K := (K + 1)%Z); [| lia]. apply addnative_bound; lia. }
    lazymatch goal with
    | XL' : u64arr USEGS ?m' A ?cur', XC' : rw_cells USEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len1 <= ?len' <= len1 + 1 /\ _)%Z, HV : bval _ _ = (bval cur1 (Z.to_nat len1) + _)%Z, HN : (bnorm cur1 _ -> bnorm _ _) |- _ =>
      rename XL' into XL2; rename XC' into XC2; rename HB into HB2; rename HV into HV2; rename HN into HN2;
      set (cur2 := cur') in *; set (len2 := len') in *
    end.
    eapply (IT off p j0 w16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur2 len2 dg (K + 1)%Z); try eassumption; try lia.
    { unfold boxed. split. { apply HN2. apply HN1; [lia| exact BN]. }
      rewrite HV2, HV1. pose proof (bval_nonneg cur (Z.to_nat len)). apply addnative_bound; lia. }
    all: enough ((dg + 36) / 19 <= dg / 19 + 2)%Z; [ assert (K + 1 <= (dg + 36) / 19)%Z by (apply Z.div_le_lower_bound; lia); lia | Z.div_mod_to_equations; lia ].
  Qed.

  Lemma ftrunc_proof : ftb_ok -> ftrunc_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IT. unfold ftrunc_ok; intros until dg; intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V HK Hcnt HKd FBS FNZ Hoff Hp; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit cnt) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    replace (Z_to_bv 64 (88584 + cnt * 2 ^ 3)) with (Z_to_bv 64 (88584 + 8 * cnt)) by (f_equal; lia).
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL10_ok PR ltac:(lia) ltac:(cbn; lia) cnt ltac:(cbn; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    pose proof (TBL10_nth cnt ltac:(lia)) as Hy. set (y := nth (Z.to_nat cnt) TBL10 0%Z) in *.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    unfold boxed in V. destruct V as [BN BV].
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur len).
    { exact XL. } { exact Hcur. } { exact XC. } { lia. }
    { rewrite unsigned_lit by lia. apply (cap_mul _ _ K); try lia. pose proof (bval_nonneg cur (Z.to_nat len)). lia. }
    lazymatch goal with
    | XL' : u64arr USEGS ?m' A ?cur', XC' : rw_cells USEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len <= ?len' <= len + 1 /\ _)%Z, HV : bval _ _ = (bval cur (Z.to_nat len) * _)%Z, HN : (_ -> bnorm cur _ -> bnorm _ _) |- _ =>
      rename XL' into XL1; rename XC' into XC1; rename HB into HB1; rename HV into HV1; rename HN into HN1;
      set (cur1 := cur') in *; set (len1 := len') in *
    end.
    rewrite unsigned_lit in HV1, HN1 by lia.
    pose proof (u64arr_bound _ _ _ _ XL1) as BdX1. lazymatch goal with H : length cur1 = 62%nat |- _ => rename H into Hcur1 end. rewrite Hcur1 in BdX1.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call (small_add_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur1 len1).
    { exact XL1. } { exact Hcur1. } { exact XC1. } { lia. }
    { rewrite HV1. pose proof (bval_nonneg cur (Z.to_nat len)).
      eapply cap_of_K with (K := (K + 1)%Z); [| lia]. apply addnative_bound; lia. }
    lazymatch goal with
    | XL' : u64arr USEGS ?m' A ?cur', XC' : rw_cells USEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len1 <= ?len' <= len1 + 1 /\ _)%Z, HV : bval _ _ = (bval cur1 (Z.to_nat len1) + _)%Z, HN : (bnorm cur1 _ -> bnorm _ _) |- _ =>
      rename XL' into XL2; rename XC' into XC2; rename HB into HB2; rename HV into HV2; rename HN into HN2;
      set (cur2 := cur') in *; set (len2 := len') in *
    end.
    eapply (IT off p j0 w16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur2 len2 dg (K + 1)%Z); try eassumption; try lia.
    { unfold boxed. split. { apply HN2. apply HN1; [lia| exact BN]. }
      rewrite HV2, HV1. pose proof (bval_nonneg cur (Z.to_nat len)). apply addnative_bound; lia. }
    all: try (apply fbs_now; [assumption| exact FNZ]).
    all: enough ((dg + 36) / 19 <= dg / 19 + 2)%Z; [ assert (K + 1 <= (dg + 36) / 19)%Z by (apply Z.div_le_lower_bound; lia); lia | Z.div_mod_to_equations; lia ].
  Qed.
  Definition fback_ok (kk : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs -> bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w16 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 37)%Z -> ((off < length fbs)%nat -> 19 * K <= dg + 18)%Z -> (dg < maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off <= Z.of_nat kk)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 42949672960001) x10 x11 x12 x13 x14 x15 x16 x17 mdw x19 p (Z_to_bv 64 1095216660735) (Z_to_bv 64 (FP + flen)) (Z_to_bv 64 8) (Z_to_bv 64 (-1)) (Z_to_bv 64 10) (Z_to_bv 64 17) (Z_to_bv 64 4294967296000100) x28 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 100000000) x31)
            F (Z_to_bv 64 0x26460) fc None m (seg_rom USEGS)).

  Definition fmul_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x23 x24 x26 x28 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs -> bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w16 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (cnt = 19 \/ off = length fbs \/ dg = maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 42949672960001) (Z_to_bv 64 dg) (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 x17 mdw vw p (Z_to_bv 64 1095216660735) (Z_to_bv 64 (FP + flen)) x23 x24 (Z_to_bv 64 10) x26 (Z_to_bv 64 4294967296000100) x28 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 100000000) x31)
            F (Z_to_bv 64 0x26400) fc None m (seg_rom USEGS)).

  Definition f1_ok (kk : nat) (k : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x11 x14 x15 x16 x17 x23 x28 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs -> bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w16 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 18)%Z -> (Z.to_nat (19 - cnt) <= k)%nat -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (dg < maxd)%Z -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 42949672960001) (Z_to_bv 64 dg) x11 p (Z_to_bv 64 cnt) x14 x15 x16 x17 mdw vw p (Z_to_bv 64 1095216660735) (Z_to_bv 64 (FP + flen)) x23 (Z_to_bv 64 (-1)) (Z_to_bv 64 10) (Z_to_bv 64 17) (Z_to_bv 64 4294967296000100) x28 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 100000000) x31)
            F (Z_to_bv 64 0x263c4) fc None m (seg_rom USEGS)).

  Definition f1entry_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x23 x28 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs -> bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w16 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 16)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt + 18)%Z ->
      (cnt = 0 -> (off < length fbs)%nat /\ dg < maxd)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 42949672960001) (Z_to_bv 64 dg) (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 x17 mdw vw p (Z_to_bv 64 1095216660735) (Z_to_bv 64 (FP + flen)) x23 (Z_to_bv 64 (-1)) (Z_to_bv 64 10) (Z_to_bv 64 17) (Z_to_bv 64 4294967296000100) x28 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 100000000) x31)
            F (Z_to_bv 64 0x263b4) fc None m (seg_rom USEGS)).

  Definition f8body_ok (kk : nat) (zf : Z) : Prop :=
    forall (off : nat) (p vw : word) (cnt0 : Z) (K : Z) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x16 x17 x28 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs -> bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w16 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0 + 18)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> (Z.of_nat (length fbs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 42949672960001) (Z_to_bv 64 dg) (Z_to_bv 64 cnt0) (Z_to_bv 64 (flen - Z.of_nat off - 8)) (Z_to_bv 64 (maxd - dg)) p (Z_to_bv 64 zf) x16 x17 mdw vw p (Z_to_bv 64 1095216660735) (Z_to_bv 64 (FP + flen)) (Z_to_bv 64 8) (Z_to_bv 64 (-1)) (Z_to_bv 64 10) (Z_to_bv 64 17) (Z_to_bv 64 4294967296000100) x28 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 100000000) x31)
            F (Z_to_bv 64 0x262e4) fc None m (seg_rom USEGS)).

  Definition fout_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs -> bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w16 = (FP + flen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z -> (dg < maxd)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 42949672960001) x10 x11 x12 x13 x14 x15 x16 x17 mdw x19 p (Z_to_bv 64 1095216660735) (Z_to_bv 64 (FP + flen)) (Z_to_bv 64 8) (Z_to_bv 64 (-1)) (Z_to_bv 64 10) (Z_to_bv 64 17) (Z_to_bv 64 4294967296000100) x28 (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 100000000) x31)
            F (Z_to_bv 64 0x262b4) fc None m (seg_rom USEGS)).

  Ltac introsF := intros FRLO FRH ST XL Hcur XC DG NUM IBS FBS FNZ FPD MU WM PR LEN DGB Hw16.

  Lemma fback_proof : forall kk, end_ok -> fout_ok kk -> fback_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk END FOUT. unfold fback_ok; intros until dg; introsF; intros V HK HK1 HK2 DGM Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - eapply (FOUT off p K); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      eapply (END [CB 8 j0; C8 numv; C8 w16; C8 (Z_to_bv 64 88584); C8 resv]); try eassumption; try lia.
      { reflexivity. }
      all: enough (K <= (dg + 37) / 19 /\ (dg + 37) / 19 <= dg / 19 + 3)%Z by lia.
      all: split; [apply Z.div_le_lower_bound; lia|].
      all: Z.div_mod_to_equations; lia.
  Qed.

  Lemma fmul_proof : forall kk, ftrunc_ok -> fback_ok kk -> fmul_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FT FB. unfold fmul_ok; intros until dg; introsF; intros V HK Hcnt Hcd HKd EXIT Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    step. (* [comment removed for export] *)
    if_cases Ht; cond_cleanup Ht.
    { eapply (FT off p vw cnt K j0 w16); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit cnt) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    replace (Z_to_bv 64 (88584 + cnt * 2 ^ 3)) with (Z_to_bv 64 (88584 + 8 * cnt)) by (f_equal; lia).
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL10_ok PR ltac:(lia) ltac:(cbn; lia) cnt ltac:(cbn; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    pose proof (TBL10_nth cnt ltac:(lia)) as Hy. set (y := nth (Z.to_nat cnt) TBL10 0%Z) in *.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    unfold boxed in V. destruct V as [BN BV].
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur len).
    { exact XL. } { exact Hcur. } { exact XC. } { lia. }
    { rewrite unsigned_lit by lia. apply (cap_mul _ _ K); try lia. pose proof (bval_nonneg cur (Z.to_nat len)). lia. }
    lazymatch goal with
    | XL' : u64arr USEGS ?m' A ?cur', XC' : rw_cells USEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len <= ?len' <= len + 1 /\ _)%Z, HV : bval _ _ = (bval cur (Z.to_nat len) * _)%Z, HN : (_ -> bnorm cur _ -> bnorm _ _) |- _ =>
      rename XL' into XL1; rename XC' into XC1; rename HB into HB1; rename HV into HV1; rename HN into HN1;
      set (cur1 := cur') in *; set (len1 := len') in *
    end.
    rewrite unsigned_lit in HV1, HN1 by lia.
    pose proof (u64arr_bound _ _ _ _ XL1) as BdX1. lazymatch goal with H : length cur1 = 62%nat |- _ => rename H into Hcur1 end. rewrite Hcur1 in BdX1.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call (small_add_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur1 len1).
    { exact XL1. } { exact Hcur1. } { exact XC1. } { lia. }
    { rewrite HV1. pose proof (bval_nonneg cur (Z.to_nat len)).
      eapply cap_of_K with (K := (K + 1)%Z); [| lia]. apply addnative_bound; lia. }
    lazymatch goal with
    | XL' : u64arr USEGS ?m' A ?cur', XC' : rw_cells USEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len1 <= ?len' <= len1 + 1 /\ _)%Z, HV : bval _ _ = (bval cur1 (Z.to_nat len1) + _)%Z, HN : (bnorm cur1 _ -> bnorm _ _) |- _ =>
      rename XL' into XL2; rename XC' into XC2; rename HB into HB2; rename HV into HV2; rename HN into HN2;
      set (cur2 := cur') in *; set (len2 := len') in *
    end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (FB off p (K + 1)%Z j0 w16); try eassumption; try lia.
    all: try (apply fbs_now; [assumption| exact FNZ]).
    unfold boxed. split. { apply HN2. apply HN1; [lia| exact BN]. }
    rewrite HV2, HV1. pose proof (bval_nonneg cur (Z.to_nat len)). apply addnative_bound; lia.
  Qed.

  Lemma f1_proof : forall kk, fmul_ok kk -> forall k, f1_ok kk k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FM. induction k as [|k IH]; unfold f1_ok; intros until dg; introsF; intros V HK Hcnt Hk Hcd HKd DGM Hoff Hp Hkk; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    if_not_taken.
    pose proof (ro_block USEGS m FP fbs off 1 FBS ltac:(lia)) as BLK.
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
    if_cases H19; cond_cleanup H19.
    { eapply (FM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K j0 w16); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia. }
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply (FM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K j0 w16); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hm; cond_cleanup Hm.
    - eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K j0 w16); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
    - eapply (FM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K j0 w16); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
  Qed.

  Lemma f1entry_proof : forall kk, fmul_ok kk -> (forall k, f1_ok kk k) -> f1entry_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk FM F1. unfold f1entry_ok; intros until dg; introsF; intros V HK Hcnt Hcd HKd H0 Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply (FM off p vw cnt K j0 w16); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    if_cases Hg; cond_cleanup Hg.
    { eapply (FM off p vw cnt K j0 w16); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (F1 (Z.to_nat (19 - cnt)) off p vw cnt K j0 w16); try eassumption; try lia.
  Qed.

  Ltac f8_body_steps p FBS off :=
    pose proof (ro_block USEGS _ FP fbs off 8 FBS ltac:(lia)) as BLK;
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia;
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    if_not_taken;
    do 45 step;
    clear BLK.

End Proof.
End U_parse_mantissa_1.


Module U_parse_mantissa_2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_small_add_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_bigadd OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_parse_mantissa.U_small_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_small_add_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_parse_mantissa.U_parse_mantissa_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_parse_mantissa.U_parse_mantissa_1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section Proof.
  Set Default Proof Using "All".
  Hypothesis small_mul_spec : small_mul_stmt.
  Hypothesis small_add_spec : small_add_stmt.
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
  Hypothesis FBS0 : boxed (bytes_at USEGS m0 (bv_unsigned fptr) fbs).
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
  Notation FRHI m := (rw_cells USEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells USEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 resv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 dv) as RDv; unfold bv_modulus in RDv;
    pose proof (bv_unsigned_in_range 64 numv) as RN; unfold bv_modulus in RN;
    pose proof (bv_unsigned_in_range 64 iptr) as RI; unfold bv_modulus in RI;
    pose proof (bv_unsigned_in_range 64 fptr) as RF; unfold bv_modulus in RF;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp.

  #[local] Definition end_ok := Eval cbv beta delta [U_parse_mantissa_1.end_ok] in (@U_parse_mantissa_1.end_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv dv F fc m0 ws maxd).
  #[local] Definition end_proof := (@U_parse_mantissa_1.end_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition diginc_ok := Eval cbv beta delta [U_parse_mantissa_1.diginc_ok] in (@U_parse_mantissa_1.diginc_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv dv F fc m0 ws maxd).
  #[local] Definition diginc_proof := (@U_parse_mantissa_1.diginc_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition cap_of_K := (@U_parse_mantissa_1.cap_of_K small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  Notation FRLOU j0 w16 m := (rw_cells USEGS m (SP + -144) [CB 8 j0; C8 numv; C8 w16; C8 (Z_to_bv 64 88584); C8 resv]).

  #[local] Definition ru_ok := Eval cbv beta delta [U_parse_mantissa_1.ru_ok] in (@U_parse_mantissa_1.ru_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws maxd).
  #[local] Definition ru_proof := (@U_parse_mantissa_1.ru_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftb1_ok := Eval cbv beta delta [U_parse_mantissa_1.ftb1_ok] in (@U_parse_mantissa_1.ftb1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition ftb8_ok := Eval cbv beta delta [U_parse_mantissa_1.ftb8_ok] in (@U_parse_mantissa_1.ftb8_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition ftb_ok := Eval cbv beta delta [U_parse_mantissa_1.ftb_ok] in (@U_parse_mantissa_1.ftb_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition ftaend_ok := Eval cbv beta delta [U_parse_mantissa_1.ftaend_ok] in (@U_parse_mantissa_1.ftaend_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition fta1_ok := Eval cbv beta delta [U_parse_mantissa_1.fta1_ok] in (@U_parse_mantissa_1.fta1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fta8_ok := Eval cbv beta delta [U_parse_mantissa_1.fta8_ok] in (@U_parse_mantissa_1.fta8_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fta_ok := Eval cbv beta delta [U_parse_mantissa_1.fta_ok] in (@U_parse_mantissa_1.fta_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition it1_ok := Eval cbv beta delta [U_parse_mantissa_1.it1_ok] in (@U_parse_mantissa_1.it1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition it8_ok := Eval cbv beta delta [U_parse_mantissa_1.it8_ok] in (@U_parse_mantissa_1.it8_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition it_ok := Eval cbv beta delta [U_parse_mantissa_1.it_ok] in (@U_parse_mantissa_1.it_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr USEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).
  Ltac ENDAP := lazymatch goal with FRLO : rw_cells USEGS ?m (SP + -144) ?lo |- _ =>
    eapply (_ : end_ok) with (lo := lo) end.

  #[local] Definition ftb1_proof := (@U_parse_mantissa_1.ftb1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftb8_proof := (@U_parse_mantissa_1.ftb8_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftb_proof := (@U_parse_mantissa_1.ftb_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fbs_now := (@U_parse_mantissa_1.fbs_now small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftaend_proof := (@U_parse_mantissa_1.ftaend_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fta1_proof := (@U_parse_mantissa_1.fta1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fta8_proof := (@U_parse_mantissa_1.fta8_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fta_proof := (@U_parse_mantissa_1.fta_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition it1_proof := (@U_parse_mantissa_1.it1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition it8_proof := (@U_parse_mantissa_1.it8_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition it_proof := (@U_parse_mantissa_1.it_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition itrunc_ok := Eval cbv beta delta [U_parse_mantissa_1.itrunc_ok] in (@U_parse_mantissa_1.itrunc_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition ftrunc_ok := Eval cbv beta delta [U_parse_mantissa_1.ftrunc_ok] in (@U_parse_mantissa_1.ftrunc_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  Notation TBL10 := U_parse_mantissa_1.TBL10.
  #[local] Definition TBL10_ok := (@U_parse_mantissa_1.TBL10_ok small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition TBL10_nth := (@U_parse_mantissa_1.TBL10_nth small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  Ltac muladd_calls XL Hcur XC V vw K cnt :=
    let BN := fresh "BN" in let BV := fresh "BV" in
    pose proof (table_read USEGS _ _ _ _ _ _ _ TBL10_ok ltac:(eassumption) ltac:(lia) ltac:(cbn; lia) cnt ltac:(cbn; lia)) as RD;
    step; (* [comment removed for export] *)
    clear RD;
    pose proof (TBL10_nth cnt ltac:(lia)) as Hy; set (y := nth (Z.to_nat cnt) TBL10 0%Z) in *;
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    unfold boxed in V; destruct V as [BN BV];
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    [ exact XL | exact Hcur | exact XC | lia
    | rewrite unsigned_lit by lia; apply (cap_mul _ _ K); try lia; pose proof (bval_nonneg _ _ : (0 <= bval _ _)%Z); lia
    | ].

  #[local] Definition itrunc_proof := (@U_parse_mantissa_1.itrunc_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftrunc_proof := (@U_parse_mantissa_1.ftrunc_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fback_ok := Eval cbv beta delta [U_parse_mantissa_1.fback_ok] in (@U_parse_mantissa_1.fback_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fmul_ok := Eval cbv beta delta [U_parse_mantissa_1.fmul_ok] in (@U_parse_mantissa_1.fmul_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition f1_ok := Eval cbv beta delta [U_parse_mantissa_1.f1_ok] in (@U_parse_mantissa_1.f1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition f1entry_ok := Eval cbv beta delta [U_parse_mantissa_1.f1entry_ok] in (@U_parse_mantissa_1.f1entry_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition f8body_ok := Eval cbv beta delta [U_parse_mantissa_1.f8body_ok] in (@U_parse_mantissa_1.f8body_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fout_ok := Eval cbv beta delta [U_parse_mantissa_1.fout_ok] in (@U_parse_mantissa_1.fout_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  Ltac introsF := intros FRLO FRH ST XL Hcur XC DG NUM IBS FBS FNZ FPD MU WM PR LEN DGB Hw16.

  #[local] Definition fback_proof := (@U_parse_mantissa_1.fback_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fmul_proof := (@U_parse_mantissa_1.fmul_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition f1_proof := (@U_parse_mantissa_1.f1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition f1entry_proof := (@U_parse_mantissa_1.f1entry_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  Ltac f8_body_steps p FBS off :=
    pose proof (ro_block USEGS _ FP fbs off 8 FBS ltac:(lia)) as BLK;
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia;
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    if_not_taken;
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
    eapply (FE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K j0 w16); try eassumption; try lia.
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
      + eapply (FE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ 8%Z K j0 w16); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; lia.
      + replace (Z_to_bv 64 (flen - Z.of_nat off - 8 + -8)) with (Z_to_bv 64 (flen - Z.of_nat (off + 8) - 8)) by (f_equal; lia).
        replace (Z_to_bv 64 (maxd - dg + -8)) with (Z_to_bv 64 (maxd - (dg + 8))) by (f_equal; lia).
        eapply (F80 (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ 8%Z K j0 w16); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; lia.
    - pose proof (f8flag1' (flen - Z.of_nat off - 8) ltac:(lia) Hc) as H16. clear Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (FE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K j0 w16); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma fout_proof : end_ok -> ftrunc_ok -> forall k, fout_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FT. induction k as [|k IH]; unfold fout_ok; intros until dg; introsF; intros V HK HKd DGM Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (fback_proof k END IH) as FB.
    pose proof (fmul_proof k FT FB) as FM.
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
      eapply (FE off p (Z_to_bv 64 0) 0%Z K j0 w16); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite Hw16. replace (Z_to_bv 64 (FP + flen - 8 - bv_unsigned p)) with (Z_to_bv 64 (flen - Z.of_nat off - 8)) by (f_equal; lia).
      step. (* [comment removed for export] *)
      rewrite <- Hmaxd.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit dg) in * by lia.
      if_cases Hc; cond_cleanup Hc.
      + eapply (FE off p (Z_to_bv 64 0) 0%Z K j0 w16); try eassumption; try lia.
      + eapply (F81 off p (Z_to_bv 64 0) 0%Z K j0 w16); try eassumption; try lia.
  Qed.
  Notation FRLOJ j0 j2 m := (rw_cells USEGS m (SP + -144) [CB 8 j0; C8 numv; CB 8 j2; C8 (Z_to_bv 64 88584); C8 resv]).

  Definition fconst_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j0 j2 : list byte) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j0 j2 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      (off <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17 mdw x19 p x21 (Z_to_bv 64 (FP + flen)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26264) fc None m (seg_rom USEGS)).

  Definition fz1_ok (k : nat) : Prop :=
    forall (off : nat) (p fendw : word) (K : Z) (j0 j2 : list byte) (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j0 j2 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      (length fbs - off <= k)%nat -> (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z -> bv_unsigned fendw = (FP + flen)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 fendw (Z_to_bv 64 48) (Z_to_bv 64 (-1)) x13 x14 x15 x16 x17 mdw x19 p x21 (Z_to_bv 64 (FP + flen)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x266e8) fc None m (seg_rom USEGS)).

  Definition fzmid_ok : Prop :=
    forall (off : nat) (p : word) (K : Z) (j0 j2 : list byte) (x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j0 j2 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      (off < length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 p x12 x13 x14 x15 x16 x17 mdw x19 p x21 (Z_to_bv 64 (FP + flen)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x266d8) fc None m (seg_rom USEGS)).

  Definition fz8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (j0 j2 : list byte) (x1 x5 x6 x7 x9 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j0 j2 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      (length fbs - off <= k)%nat -> (off + 8 <= length fbs)%nat -> bv_unsigned p = (FP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 (Z_to_bv 64 (flen - Z.of_nat off)) p (Z_to_bv 64 8) (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 7) x15 x16 x17 mdw x19 p x21 (Z_to_bv 64 (FP + flen)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26570) fc None m (seg_rom USEGS)).

  Definition fz_ok : Prop :=
    forall (u : unit) (K : Z) (j0 j2 : list byte) (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j0 j2 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      bytes_at USEGS m FP fbs -> (FP <> 0)%Z -> (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 (Z_to_bv 64 flen) x11 x12 x13 x14 x15 x16 x17 mdw x19 fptr x21 (Z_to_bv 64 (FP + flen)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26558) fc None m (seg_rom USEGS)).

  Definition fset_ok : Prop :=
    forall (u : unit) (K : Z) (j0 j2 : list byte) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOJ j0 j2 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg < maxd)%Z -> VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17 mdw x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26240) fc None m (seg_rom USEGS)).

  Ltac introsE := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V HK HKd.

  Lemma fconst_proof : end_ok -> (forall k, fout_ok k) -> fconst_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FOUT. unfold fconst_ok; intros until dg; introsE; intros FBS FNZ FPD Hoff Hp; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply (END [CB 8 j0; C8 numv; CB 8 j2; C8 (Z_to_bv 64 88584); C8 resv]); try eassumption; try lia. all: try reflexivity. all: lazymatch goal with |- (?K0 <= ?d / 19 + 3)%Z => enough (K0 <= (d + 18) / 19 /\ (d + 18) / 19 <= d / 19 + 3)%Z by lia; split; [apply Z.div_le_lower_bound; lia|]; Z.div_mod_to_equations; lia end. }
    do 19 step.
    eapply (FOUT (length fbs - off)%nat off p K j0 (Z_to_bv 64 (FP + flen + -8))); try eassumption; try lia.
    rewrite unsigned_lit by lia. lia.
  Qed.

  Lemma fz1_proof : fconst_ok -> forall k, fz1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FC. induction k as [|k IH]; unfold fz1_ok; intros until dg; introsE; intros FBS FNZ FPD Hk Hoff Hp Hfe; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (bv_unsigned_in_range 64 fendw) as Rf; unfold bv_modulus in Rf.
    pose proof (ro_block USEGS m FP fbs off 1 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { eapply (FC off p K j0 j2); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) fendw K j0 j2); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (FC (length fbs) fendw K j0 j2); try eassumption; try lia.
  Qed.

  Lemma fzmid_proof : (forall k, fz1_ok k) -> fzmid_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FZ1. unfold fzmid_ok; intros until dg; introsE; intros FBS FNZ FPD Hoff Hp; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (FZ1 (length fbs - off)%nat off p _ K j0 j2); try eassumption; try lia.
    rewrite (unsigned_lit (FP + flen)) by lia. rewrite !unsigned_lit by lia. lia.
  Qed.

  Lemma fz8_proof : end_ok -> fzmid_ok -> forall k, fz8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FM. induction k as [|k IH]; unfold fz8_ok; intros until dg; introsE; intros FBS FNZ FPD Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block USEGS m FP fbs off 8 FBS ltac:(lia)) as BLK.
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    do 22 step.
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      - eapply (FM off p K j0 j2); try eassumption; try lia.
      - step. (* [comment removed for export] *) eapply (END [CB 8 j0; C8 numv; CB 8 j2; C8 (Z_to_bv 64 88584); C8 resv]); try eassumption; try lia. all: try reflexivity. all: lazymatch goal with |- (?K0 <= ?d / 19 + 3)%Z => enough (K0 <= (d + 18) / 19 /\ (d + 18) / 19 <= d / 19 + 3)%Z by lia; split; [apply Z.div_le_lower_bound; lia|]; Z.div_mod_to_equations; lia end. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (flen - Z.of_nat off + -8)) with (Z_to_bv 64 (flen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) K j0 j2); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      + eapply (FM (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) K j0 j2); try eassumption; try lia.
        rewrite unsigned_lit by lia; lia.
      + step. (* [comment removed for export] *) eapply (END [CB 8 j0; C8 numv; CB 8 j2; C8 (Z_to_bv 64 88584); C8 resv]); try eassumption; try lia. all: try reflexivity. all: lazymatch goal with |- (?K0 <= ?d / 19 + 3)%Z => enough (K0 <= (d + 18) / 19 /\ (d + 18) / 19 <= d / 19 + 3)%Z by lia; split; [apply Z.div_le_lower_bound; lia|]; Z.div_mod_to_equations; lia end.
  Qed.

  Lemma fz_proof : end_ok -> fzmid_ok -> (forall k, fz8_ok k) -> fz_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FM FZ8. unfold fz_ok; intros until dg; introsE; intros FBS FNZ FPD; pre.
    pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He; cond_cleanup He.
      + eapply (END [CB 8 j0; C8 numv; CB 8 j2; C8 (Z_to_bv 64 88584); C8 resv]); try eassumption; try lia. all: try reflexivity. all: lazymatch goal with |- (?K0 <= ?d / 19 + 3)%Z => enough (K0 <= (d + 18) / 19 /\ (d + 18) / 19 <= d / 19 + 3)%Z by lia; split; [apply Z.div_le_lower_bound; lia|]; Z.div_mod_to_equations; lia end.
      + eapply (FM 0%nat fptr K j0 j2); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 flen) with (Z_to_bv 64 (flen - Z.of_nat 0)) by (f_equal; lia).
      eapply (FZ8 (length fbs) 0%nat fptr K j0 j2); try eassumption; try lia.
  Qed.

  Lemma fset_proof : end_ok -> fz_ok -> fconst_ok -> fset_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros END FZ FC. unfold fset_ok; intros until dg; introsE; pre.
    pose proof (bv_unsigned_in_range 64 fptr) as Rfp; unfold bv_modulus in Rfp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz; cond_cleanup Hz.
    { eapply (END [CB 8 j0; C8 numv; CB 8 j2; C8 (Z_to_bv 64 88584); C8 resv]); try eassumption; try lia. all: try reflexivity. all: lazymatch goal with |- (?K0 <= ?d / 19 + 3)%Z => enough (K0 <= (d + 18) / 19 /\ (d + 18) / 19 <= d / 19 + 3)%Z by lia; split; [apply Z.div_le_lower_bound; lia|]; Z.div_mod_to_equations; lia end. }
    pose proof (fbs_now m MU Hz) as FBS. pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    assert (FPD : (D + 8 <= FP \/ 16 <= FP /\ FP + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z) by (unfold boxed in LAY5; apply LAY5; exact Hz).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd; cond_cleanup Hd.
    - eapply (FZ tt K j0 j2); try eassumption; try lia.
    - eapply (FC 0%nat fptr K j0 j2); try eassumption; try lia.
  Qed.
  Definition iback_ok (kk : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x30 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w16 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg + 18)%Z -> ((off < length ibs)%nat -> 19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off <= Z.of_nat kk)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 42949672960001) x10 x11 x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 8) x20 (Z_to_bv 64 1095216660735) p (Z_to_bv 64 (IP + ilen)) (Z_to_bv 64 (-1)) (Z_to_bv 64 17) (Z_to_bv 64 10) (Z_to_bv 64 100000000) x28 (Z_to_bv 64 14974415777481871312) x30 (Z_to_bv 64 4294967296000100))
            F (Z_to_bv 64 0x2623c) fc None m (seg_rom USEGS)).

  Definition imul_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x24 x25 x28 x30 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w16 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (1 <= cnt <= 19)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 19 \/ off = length ibs \/ dg = maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 42949672960001) (Z_to_bv 64 dg) (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 x17 mdw x19 vw (Z_to_bv 64 1095216660735) p (Z_to_bv 64 (IP + ilen)) x24 x25 (Z_to_bv 64 10) (Z_to_bv 64 100000000) x28 (Z_to_bv 64 14974415777481871312) x30 (Z_to_bv 64 4294967296000100))
            F (Z_to_bv 64 0x261dc) fc None m (seg_rom USEGS)).

  Definition i1_ok (kk : nat) (k : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x11 x14 x15 x16 x17 x19 x28 x30 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w16 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 18)%Z -> (Z.to_nat (19 - cnt) <= k)%nat -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (dg < maxd)%Z -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 42949672960001) (Z_to_bv 64 dg) x11 p (Z_to_bv 64 cnt) x14 x15 x16 x17 mdw x19 vw (Z_to_bv 64 1095216660735) p (Z_to_bv 64 (IP + ilen)) (Z_to_bv 64 (-1)) (Z_to_bv 64 17) (Z_to_bv 64 10) (Z_to_bv 64 100000000) x28 (Z_to_bv 64 14974415777481871312) x30 (Z_to_bv 64 4294967296000100))
            F (Z_to_bv 64 0x261a0) fc None m (seg_rom USEGS)).

  Definition i1entry_ok (kk : nat) : Prop :=
    forall (off : nat) (p vw : word) (cnt : Z) (K : Z) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x30 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w16 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (0 <= cnt <= 16)%Z -> (cnt <= dg)%Z -> (19 * K <= dg - cnt)%Z ->
      (cnt = 0 -> (off < length ibs)%nat /\ dg < maxd)%Z ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt <= Z.of_nat kk + 1)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 42949672960001) (Z_to_bv 64 dg) (Z_to_bv 64 cnt) x12 x13 x14 x15 x16 x17 mdw x19 vw (Z_to_bv 64 1095216660735) p (Z_to_bv 64 (IP + ilen)) (Z_to_bv 64 (-1)) (Z_to_bv 64 17) (Z_to_bv 64 10) (Z_to_bv 64 100000000) x28 (Z_to_bv 64 14974415777481871312) x30 (Z_to_bv 64 4294967296000100))
            F (Z_to_bv 64 0x26190) fc None m (seg_rom USEGS)).

  Definition i8body_ok (kk : nat) (zf : Z) : Prop :=
    forall (off : nat) (p vw : word) (cnt0 : Z) (K : Z) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x16 x17 x28 x30 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w16 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (zf = 0 /\ cnt0 = 8 \/ zf = 1 /\ cnt0 = 0)%Z -> (cnt0 <= dg)%Z -> (19 * K <= dg - cnt0)%Z ->
      (dg + 8 <= maxd)%Z -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> (Z.of_nat (length ibs) - Z.of_nat off + cnt0 <= Z.of_nat kk + 1)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 42949672960001) (Z_to_bv 64 dg) (Z_to_bv 64 cnt0) (Z_to_bv 64 (ilen - Z.of_nat off - 8)) (Z_to_bv 64 (maxd - dg)) p (Z_to_bv 64 zf) x16 x17 mdw (Z_to_bv 64 8) vw (Z_to_bv 64 1095216660735) p (Z_to_bv 64 (IP + ilen)) (Z_to_bv 64 (-1)) (Z_to_bv 64 17) (Z_to_bv 64 10) (Z_to_bv 64 100000000) x28 (Z_to_bv 64 14974415777481871312) x30 (Z_to_bv 64 4294967296000100))
            F (Z_to_bv 64 0x260c0) fc None m (seg_rom USEGS)).

  Definition iout_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (K : Z) (j0 : list byte) (w16 : word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x30 : word)
           (m : word -> option byte) (cur : list word) (len dg : Z),
      FRLOU j0 w16 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A cur -> length cur = 62%nat -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 dg)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (0 <= len <= 62)%Z -> (0 <= dg <= maxd)%Z -> bv_unsigned w16 = (IP + ilen - 8)%Z ->
      VAL cur len K -> (0 <= K)%Z -> (19 * K <= dg)%Z -> (dg < maxd)%Z ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv (Z_to_bv 64 42949672960001) x10 x11 x12 x13 x14 x15 x16 x17 mdw (Z_to_bv 64 8) x20 (Z_to_bv 64 1095216660735) p (Z_to_bv 64 (IP + ilen)) (Z_to_bv 64 (-1)) (Z_to_bv 64 17) (Z_to_bv 64 10) (Z_to_bv 64 100000000) x28 (Z_to_bv 64 14974415777481871312) x30 (Z_to_bv 64 4294967296000100))
            F (Z_to_bv 64 0x26090) fc None m (seg_rom USEGS)).

  Ltac introsI := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB Hw16.

  Lemma frloU_to_J : forall m j0 b, FRLOU j0 b m -> FRLOJ j0 (le8 b) m.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros m j0 b [[W B] R]. split; [split|].
    - cbn in W |- *. destruct W as (W1 & W2 & W3 & W4 & W5 & W6). repeat split; try assumption; try apply length_le8.
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
    - eapply (IOUT off p K j0 w16); try eassumption; try lia.
    - eapply (FS tt K j0 (le8 w16)); try eassumption; try lia.
      apply frloU_to_J. exact FRLO.
  Qed.

  Lemma imul_proof : forall kk, itrunc_ok -> iback_ok kk -> imul_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IT IB. unfold imul_ok; intros until dg; introsI; intros V HK Hcnt Hcd HKd EXIT Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (bv_unsigned_in_range 64 vw) as Rv; unfold bv_modulus in Rv.
    step. (* [comment removed for export] *)
    if_cases Ht; cond_cleanup Ht.
    { eapply (IT off p vw cnt K j0 w16); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit cnt) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    replace (Z_to_bv 64 (88584 + cnt * 2 ^ 3)) with (Z_to_bv 64 (88584 + 8 * cnt)) by (f_equal; lia).
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL10_ok PR ltac:(lia) ltac:(cbn; lia) cnt ltac:(cbn; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    pose proof (TBL10_nth cnt ltac:(lia)) as Hy. set (y := nth (Z.to_nat cnt) TBL10 0%Z) in *.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    unfold boxed in V. destruct V as [BN BV].
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur len).
    { exact XL. } { exact Hcur. } { exact XC. } { lia. }
    { rewrite unsigned_lit by lia. apply (cap_mul _ _ K); try lia. pose proof (bval_nonneg cur (Z.to_nat len)). lia. }
    lazymatch goal with
    | XL' : u64arr USEGS ?m' A ?cur', XC' : rw_cells USEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len <= ?len' <= len + 1 /\ _)%Z, HV : bval _ _ = (bval cur (Z.to_nat len) * _)%Z, HN : (_ -> bnorm cur _ -> bnorm _ _) |- _ =>
      rename XL' into XL1; rename XC' into XC1; rename HB into HB1; rename HV into HV1; rename HN into HN1;
      set (cur1 := cur') in *; set (len1 := len') in *
    end.
    rewrite unsigned_lit in HV1, HN1 by lia.
    pose proof (u64arr_bound _ _ _ _ XL1) as BdX1. lazymatch goal with H : length cur1 = 62%nat |- _ => rename H into Hcur1 end. rewrite Hcur1 in BdX1.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call (small_add_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cur1 len1).
    { exact XL1. } { exact Hcur1. } { exact XC1. } { lia. }
    { rewrite HV1. pose proof (bval_nonneg cur (Z.to_nat len)).
      eapply cap_of_K with (K := (K + 1)%Z); [| lia]. apply addnative_bound; lia. }
    lazymatch goal with
    | XL' : u64arr USEGS ?m' A ?cur', XC' : rw_cells USEGS _ (A + 496) [C2 (Z_to_bv 64 ?len')],
      HB : (len1 <= ?len' <= len1 + 1 /\ _)%Z, HV : bval _ _ = (bval cur1 (Z.to_nat len1) + _)%Z, HN : (bnorm cur1 _ -> bnorm _ _) |- _ =>
      rename XL' into XL2; rename XC' into XC2; rename HB into HB2; rename HV into HV2; rename HN into HN2;
      set (cur2 := cur') in *; set (len2 := len') in *
    end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (IB off p (K + 1)%Z j0 w16); try eassumption; try lia.
    unfold boxed. split. { apply HN2. apply HN1; [lia| exact BN]. }
    rewrite HV2, HV1. pose proof (bval_nonneg cur (Z.to_nat len)). apply addnative_bound; lia.
  Qed.

  Lemma i1_proof : forall kk, imul_ok kk -> forall k, i1_ok kk k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IM. induction k as [|k IH]; unfold i1_ok; intros until dg; introsI; intros V HK Hcnt Hk Hcd HKd DGM Hoff Hp Hkk; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    if_not_taken.
    pose proof (ro_block USEGS m IP ibs off 1 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
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
    if_cases H19; cond_cleanup H19.
    { eapply (IM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K j0 w16); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia. }
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply (IM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K j0 w16); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hm; cond_cleanup Hm.
    - eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K j0 w16); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
    - eapply (IM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K j0 w16); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
  Qed.

  Lemma i1entry_proof : forall kk, imul_ok kk -> (forall k, i1_ok kk k) -> i1entry_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IM I1. unfold i1entry_ok; intros until dg; introsI; intros V HK Hcnt Hcd HKd H0 Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply (IM off p vw cnt K j0 w16); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    if_cases Hg; cond_cleanup Hg.
    { eapply (IM off p vw cnt K j0 w16); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (I1 (Z.to_nat (19 - cnt)) off p vw cnt K j0 w16); try eassumption; try lia.
  Qed.

  Ltac i8_body_steps p IBS off :=
    pose proof (ro_block USEGS _ IP ibs off 8 IBS ltac:(lia)) as BLK;
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia;
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    if_not_taken;
    do 45 step;
    clear BLK.

End Proof.
End U_parse_mantissa_2.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_parse_mantissa.U_parse_mantissa_1 OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_parse_mantissa.U_parse_mantissa_2.
Import ListNotations.

Module U_small_mul.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Wbig_tac.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_parse_mantissa.U_small_mul_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Loop.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
  Variables (vec yw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (len : Z).
  Hypothesis Hlen : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis CAP : (bval ws (Z.to_nat len) * bv_unsigned yw < BIG_CAP)%Z.

  Notation A := (bv_unsigned vec).
  Notation y := (bv_unsigned yw).
  Notation POST := (small_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A y ws len m0).

  Definition loop_ok (k : nat) : Prop :=
    forall (i : nat) (p t0 t1 t2 : word) (c : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      u64arr USEGS m A cur -> length cur = 62%nat ->
      rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      smul_inv ws cur y i c ->
      munch (small_mul_W A) m0 m -> wmono USEGS m0 m ->
      evt USEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) yw vec (Z_to_bv 64 len) (Z_to_bv 64 c) (Z_to_bv 64 63) p (Z_to_bv 64 (63 - Z.of_nat i))
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x26cb4) fc None m (seg_rom USEGS)).

  #[using="Hlen LEN CAP"] Lemma loop_body : forall k, loop_ok k -> loop_ok (S k).
  Proof. LiaFast.lf_pins (fun (Hlen LEN CAP : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold loop_ok. intros i p t0 t1 t2 c cur m Hk Hi Hp CUR Hcur LC INV MU WM.
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    cbv delta [small_mul_W] in MU.
    pose proof (bv_unsigned_in_range 64 yw) as Ry. unfold bv_modulus in Ry.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    destruct INV as (Hv & Hag & Hc & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hn. }
    pose proof (u64arr_read USEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_store_ok USEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write USEGS m A cur (Z.of_nat i) (Z_to_bv 64 (bv_unsigned w * y + c)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    rewrite (smul_carry_word (bv_unsigned w) y c) by lia.
    assert (INV' : smul_inv ws (upd cur i (Z_to_bv 64 (bv_unsigned w * y + c))) y (S i) (mul_cout (limbZ ws i) y c)).
    { replace (bv_unsigned w * y)%Z with (limbZ ws i * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply smul_inv_step; [split; [exact Hv| split; [exact Hag| split; [exact Hc| exact Hlc]]] | lia | rewrite Hlen; lia |].
      unfold limbZ. rewrite <- Hw. apply smul_lo_word; lia. }
    replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
    step. (* [comment removed for export] *)
    if_cases Hb.
    - (* [comment removed for export] *)
      cond_cleanup Hb.
      replace (63 - Z.of_nat i + -1)%Z with (63 - Z.of_nat (S i))%Z by lia.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite upd_length. exact Hcur.
    - (* [comment removed for export] *)
      cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      pose proof (proj1 (proj2 (proj2 INV'))) as Hc'. cbn beta in Hc'.
      remember (mul_cout (limbZ ws i) y c) as c' eqn:Ec'.
      step. (* [comment removed for export] *)
      if_cases Hz.
      + (* [comment removed for export] *)
        cond_cleanup Hz.
        step. (* [comment removed for export] *)
        unfold small_mul_post. finish.
        { exact CUR'. } { rewrite upd_length. exact Hcur. } { exact LC. } all: try lia.
        * rewrite <- Hil. rewrite (Z.mul_comm (bval ws _) y). apply (smul_inv_finish_nocarry ws _ y (S i)). rewrite <- Hz. exact INV'.
        * intros Hy BN. rewrite <- Hil in BN |- *. right. cbn [Nat.sub]. rewrite Nat.sub_0_r.
          unfold limbZ. rewrite nth_upd_same by (rewrite Hcur; lia).
          rewrite (smul_lo_word (bv_unsigned w) y c) by lia.
          unfold limbZ in Ec'. rewrite <- Hw in Ec'.
          apply smul_top_nonzero; try lia.
          destruct BN as [BN|BN]; [lia|]. cbn [Nat.sub] in BN. rewrite Nat.sub_0_r in BN. unfold limbZ in BN. rewrite <- Hw in BN. lia.
      + (* [comment removed for export] *)
        cond_cleanup Hz.
        pose proof (smul_carry_room ws _ y _ _ INV' ltac:(lia) ltac:(rewrite Hil; lia)) as ROOM.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_not_taken.
        step. (* [comment removed for export] *)
        rewrite (unsigned_lit len) by lia. rewrite Z.shiftl_mul_pow2 by lia. replace (len * 2 ^ 3)%Z with (8 * len)%Z by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_not_taken.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose proof (u64arr_store_ok USEGS m1 A _ len (Z_to_bv 64 (A + 8 * len)) CUR' ltac:(rewrite upd_length; lia) eq_refl) as SOK2.
        step. (* [comment removed for export] *)
        pose proof (u64arr_write USEGS m1 A _ len (Z_to_bv 64 c') CUR' ltac:(rewrite upd_length; lia)) as CUR''.
        store_done.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        unfold small_mul_post. finish.
        { exact CUR''. } { rewrite !upd_length. exact Hcur. } { exact LC. } all: try lia.
        * replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia. replace (Z.to_nat len) with (S i) by lia.
          rewrite (Z.mul_comm (bval ws _) y). subst c'. apply (smul_inv_finish_carry ws _ y (S i)); [exact INV'| rewrite Hlen; lia].
        * intros Hy BN. replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia.
          apply bnorm_push; [rewrite upd_length, Hcur; lia|]. rewrite unsigned_lit by lia. lia.
  Qed.
End Loop.

Section Loop2.
  Context (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (vec yw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
          (ws : list word) (len : Z)
          (Hlen : length ws = 62%nat) (LEN : (0 < len <= 62)%Z)
          (CAP : (bval ws (Z.to_nat len) * bv_unsigned yw < BIG_CAP)%Z).
  #[using="Hlen LEN CAP"] Lemma sm_loop : forall k, loop_ok ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 vec yw F fc m0 ws len k.
  Proof. LiaFast.lf_pins (fun (Hlen LEN CAP : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH].
    - unfold loop_ok. intros. exfalso. lia.
    - apply loop_body; assumption.
  Qed.
End Loop2.

Lemma small_mul_spec : small_mul_stmt.
Proof.
  unfold small_mul_stmt. intros until len. intros LIMBS Hlen LC LEN CAP.
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bd. rewrite Hlen in Bd.
  pose proof (munch_refl (small_mul_W (bv_unsigned a0)) m) as MU.
  pose proof (wmono_refl USEGS m) as WM.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite zx16_lit by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hz.
  - (* [comment removed for export] *)
    cond_cleanup Hz.
    step. (* [comment removed for export] *)
    unfold small_mul_post. finish.
    { exact LIMBS. } { exact Hlen. } { exact LC. } all: try lia.
    + subst len. change (Z.to_nat 0) with 0%nat. rewrite bval_0. lia.
    + intros _ BN. exact BN.
  - cond_cleanup Hz.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    change (Z_to_bv 64 63) with (Z_to_bv 64 (63 - Z.of_nat 0)) at 2.
    eapply (sm_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a1 F fc m ws len
              Hlen ltac:(lia) CAP (Z.to_nat len) 0%nat a0); try eassumption; try lia.
    apply smul_inv_init.
Qed.
End U_small_mul.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section Proof.
  Set Default Proof Using "All".
  Hypothesis small_mul_spec : small_mul_stmt.
  Hypothesis small_add_spec : small_add_stmt.
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
  Hypothesis FBS0 : boxed (bytes_at USEGS m0 (bv_unsigned fptr) fbs).
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
  Notation FRHI m := (rw_cells USEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells USEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 resv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 dv) as RDv; unfold bv_modulus in RDv;
    pose proof (bv_unsigned_in_range 64 numv) as RN; unfold bv_modulus in RN;
    pose proof (bv_unsigned_in_range 64 iptr) as RI; unfold bv_modulus in RI;
    pose proof (bv_unsigned_in_range 64 fptr) as RF; unfold bv_modulus in RF;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp.

  #[local] Definition end_ok := Eval cbv beta delta [U_parse_mantissa_1.end_ok] in (@U_parse_mantissa_1.end_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv dv F fc m0 ws maxd).
  #[local] Definition end_proof := (@U_parse_mantissa_1.end_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition diginc_ok := Eval cbv beta delta [U_parse_mantissa_1.diginc_ok] in (@U_parse_mantissa_1.diginc_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv dv F fc m0 ws maxd).
  #[local] Definition diginc_proof := (@U_parse_mantissa_1.diginc_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition cap_of_K := (@U_parse_mantissa_1.cap_of_K small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  Notation FRLOU j0 w16 m := (rw_cells USEGS m (SP + -144) [CB 8 j0; C8 numv; C8 w16; C8 (Z_to_bv 64 88584); C8 resv]).

  #[local] Definition ru_ok := Eval cbv beta delta [U_parse_mantissa_1.ru_ok] in (@U_parse_mantissa_1.ru_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws maxd).
  #[local] Definition ru_proof := (@U_parse_mantissa_1.ru_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftb1_ok := Eval cbv beta delta [U_parse_mantissa_1.ftb1_ok] in (@U_parse_mantissa_1.ftb1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition ftb8_ok := Eval cbv beta delta [U_parse_mantissa_1.ftb8_ok] in (@U_parse_mantissa_1.ftb8_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition ftb_ok := Eval cbv beta delta [U_parse_mantissa_1.ftb_ok] in (@U_parse_mantissa_1.ftb_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition ftaend_ok := Eval cbv beta delta [U_parse_mantissa_1.ftaend_ok] in (@U_parse_mantissa_1.ftaend_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition fta1_ok := Eval cbv beta delta [U_parse_mantissa_1.fta1_ok] in (@U_parse_mantissa_1.fta1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fta8_ok := Eval cbv beta delta [U_parse_mantissa_1.fta8_ok] in (@U_parse_mantissa_1.fta8_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fta_ok := Eval cbv beta delta [U_parse_mantissa_1.fta_ok] in (@U_parse_mantissa_1.fta_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition it1_ok := Eval cbv beta delta [U_parse_mantissa_1.it1_ok] in (@U_parse_mantissa_1.it1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition it8_ok := Eval cbv beta delta [U_parse_mantissa_1.it8_ok] in (@U_parse_mantissa_1.it8_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition it_ok := Eval cbv beta delta [U_parse_mantissa_1.it_ok] in (@U_parse_mantissa_1.it_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr USEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).
  Ltac ENDAP := lazymatch goal with FRLO : rw_cells USEGS ?m (SP + -144) ?lo |- _ =>
    eapply (_ : end_ok) with (lo := lo) end.

  #[local] Definition ftb1_proof := (@U_parse_mantissa_1.ftb1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftb8_proof := (@U_parse_mantissa_1.ftb8_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftb_proof := (@U_parse_mantissa_1.ftb_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fbs_now := (@U_parse_mantissa_1.fbs_now small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftaend_proof := (@U_parse_mantissa_1.ftaend_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fta1_proof := (@U_parse_mantissa_1.fta1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fta8_proof := (@U_parse_mantissa_1.fta8_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fta_proof := (@U_parse_mantissa_1.fta_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition it1_proof := (@U_parse_mantissa_1.it1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition it8_proof := (@U_parse_mantissa_1.it8_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition it_proof := (@U_parse_mantissa_1.it_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition itrunc_ok := Eval cbv beta delta [U_parse_mantissa_1.itrunc_ok] in (@U_parse_mantissa_1.itrunc_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition ftrunc_ok := Eval cbv beta delta [U_parse_mantissa_1.ftrunc_ok] in (@U_parse_mantissa_1.ftrunc_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  Notation TBL10 := U_parse_mantissa_1.TBL10.
  #[local] Definition TBL10_ok := (@U_parse_mantissa_1.TBL10_ok small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition TBL10_nth := (@U_parse_mantissa_1.TBL10_nth small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  Ltac muladd_calls XL Hcur XC V vw K cnt :=
    let BN := fresh "BN" in let BV := fresh "BV" in
    pose proof (table_read USEGS _ _ _ _ _ _ _ TBL10_ok ltac:(eassumption) ltac:(lia) ltac:(cbn; lia) cnt ltac:(cbn; lia)) as RD;
    step; (* [comment removed for export] *)
    clear RD;
    pose proof (TBL10_nth cnt ltac:(lia)) as Hy; set (y := nth (Z.to_nat cnt) TBL10 0%Z) in *;
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    unfold boxed in V; destruct V as [BN BV];
    call (small_mul_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    [ exact XL | exact Hcur | exact XC | lia
    | rewrite unsigned_lit by lia; apply (cap_mul _ _ K); try lia; pose proof (bval_nonneg _ _ : (0 <= bval _ _)%Z); lia
    | ].

  #[local] Definition itrunc_proof := (@U_parse_mantissa_1.itrunc_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftrunc_proof := (@U_parse_mantissa_1.ftrunc_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fback_ok := Eval cbv beta delta [U_parse_mantissa_1.fback_ok] in (@U_parse_mantissa_1.fback_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fmul_ok := Eval cbv beta delta [U_parse_mantissa_1.fmul_ok] in (@U_parse_mantissa_1.fmul_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition f1_ok := Eval cbv beta delta [U_parse_mantissa_1.f1_ok] in (@U_parse_mantissa_1.f1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition f1entry_ok := Eval cbv beta delta [U_parse_mantissa_1.f1entry_ok] in (@U_parse_mantissa_1.f1entry_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition f8body_ok := Eval cbv beta delta [U_parse_mantissa_1.f8body_ok] in (@U_parse_mantissa_1.f8body_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fout_ok := Eval cbv beta delta [U_parse_mantissa_1.fout_ok] in (@U_parse_mantissa_1.fout_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  Ltac introsF := intros FRLO FRH ST XL Hcur XC DG NUM IBS FBS FNZ FPD MU WM PR LEN DGB Hw16.

  #[local] Definition fback_proof := (@U_parse_mantissa_1.fback_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fmul_proof := (@U_parse_mantissa_1.fmul_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition f1_proof := (@U_parse_mantissa_1.f1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition f1entry_proof := (@U_parse_mantissa_1.f1entry_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  Ltac f8_body_steps p FBS off :=
    pose proof (ro_block USEGS _ FP fbs off 8 FBS ltac:(lia)) as BLK;
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia;
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    if_not_taken;
    do 45 step;
    clear BLK.

  #[local] Definition f8body0_proof := (@U_parse_mantissa_2.f8body0_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition f8body1_proof := (@U_parse_mantissa_2.f8body1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fout_proof := (@U_parse_mantissa_2.fout_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  Notation FRLOJ j0 j2 m := (rw_cells USEGS m (SP + -144) [CB 8 j0; C8 numv; CB 8 j2; C8 (Z_to_bv 64 88584); C8 resv]).

  #[local] Definition fconst_ok := Eval cbv beta delta [U_parse_mantissa_2.fconst_ok] in (@U_parse_mantissa_2.fconst_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fz1_ok := Eval cbv beta delta [U_parse_mantissa_2.fz1_ok] in (@U_parse_mantissa_2.fz1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fzmid_ok := Eval cbv beta delta [U_parse_mantissa_2.fzmid_ok] in (@U_parse_mantissa_2.fzmid_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fz8_ok := Eval cbv beta delta [U_parse_mantissa_2.fz8_ok] in (@U_parse_mantissa_2.fz8_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fz_ok := Eval cbv beta delta [U_parse_mantissa_2.fz_ok] in (@U_parse_mantissa_2.fz_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fset_ok := Eval cbv beta delta [U_parse_mantissa_2.fset_ok] in (@U_parse_mantissa_2.fset_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  Ltac introsE := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V HK HKd.

  #[local] Definition fconst_proof := (@U_parse_mantissa_2.fconst_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fz1_proof := (@U_parse_mantissa_2.fz1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fzmid_proof := (@U_parse_mantissa_2.fzmid_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fz8_proof := (@U_parse_mantissa_2.fz8_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fz_proof := (@U_parse_mantissa_2.fz_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fset_proof := (@U_parse_mantissa_2.fset_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition iback_ok := Eval cbv beta delta [U_parse_mantissa_2.iback_ok] in (@U_parse_mantissa_2.iback_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition imul_ok := Eval cbv beta delta [U_parse_mantissa_2.imul_ok] in (@U_parse_mantissa_2.imul_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition i1_ok := Eval cbv beta delta [U_parse_mantissa_2.i1_ok] in (@U_parse_mantissa_2.i1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition i1entry_ok := Eval cbv beta delta [U_parse_mantissa_2.i1entry_ok] in (@U_parse_mantissa_2.i1entry_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition i8body_ok := Eval cbv beta delta [U_parse_mantissa_2.i8body_ok] in (@U_parse_mantissa_2.i8body_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition iout_ok := Eval cbv beta delta [U_parse_mantissa_2.iout_ok] in (@U_parse_mantissa_2.iout_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  Ltac introsI := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB Hw16.

  #[local] Definition frloU_to_J := (@U_parse_mantissa_2.frloU_to_J small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition iback_proof := (@U_parse_mantissa_2.iback_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition imul_proof := (@U_parse_mantissa_2.imul_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition i1_proof := (@U_parse_mantissa_2.i1_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition i1entry_proof := (@U_parse_mantissa_2.i1entry_proof small_mul_spec small_add_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  Ltac i8_body_steps p IBS off :=
    pose proof (ro_block USEGS _ IP ibs off 8 IBS ltac:(lia)) as BLK;
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia;
    step; (* [comment removed for export] *)
    step; (* [comment removed for export] *)
    if_not_taken;
    do 45 step;
    clear BLK.

  Lemma i8body0_proof : forall kk, i1entry_ok kk -> i8body_ok kk 0.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IE. unfold i8body_ok; intros until dg; introsI; intros V HK Hz Hcd HKd DGM Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    i8_body_steps p IBS off.
    step. (* [comment removed for export] *)
    if_cases Hc. { exfalso. exact (f8flag0 _ Hc). } clear Hc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (IE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K j0 w16); try eassumption; try lia.
    all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma i8body1_proof : forall kk, i1entry_ok kk -> i8body_ok kk 0 -> i8body_ok kk 1.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IE I80. unfold i8body_ok; intros until dg; introsI; intros V HK Hz Hcd HKd DGM Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    i8_body_steps p IBS off.
    step. (* [comment removed for export] *)
    if_cases Hc.
    - pose proof (f8flag1 (ilen - Z.of_nat off - 8) ltac:(lia) Hc) as H16. clear Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb; cond_cleanup Hb.
      + eapply (IE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ 8%Z K j0 w16); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; lia.
      + replace (Z_to_bv 64 (ilen - Z.of_nat off - 8 + -8)) with (Z_to_bv 64 (ilen - Z.of_nat (off + 8) - 8)) by (f_equal; lia).
        replace (Z_to_bv 64 (maxd - dg + -8)) with (Z_to_bv 64 (maxd - (dg + 8))) by (f_equal; lia).
        eapply (I80 (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ 8%Z K j0 w16); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; lia.
    - pose proof (f8flag1' (ilen - Z.of_nat off - 8) ltac:(lia) Hc) as H16. clear Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (IE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K j0 w16); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma iout_proof : fset_ok -> itrunc_ok -> forall k, iout_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FS IT. induction k as [|k IH]; unfold iout_ok; intros until dg; introsI; intros V HK HKd DGM Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (iback_proof k FS IH) as IB.
    pose proof (imul_proof k IT IB) as IM.
    pose proof (i1_proof k IM) as I1.
    pose proof (i1entry_proof k IM I1) as IE.
    pose proof (i8body0_proof k IE) as I80.
    pose proof (i8body1_proof k IE I80) as I81.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (IP + ilen)) by lia.
    replace (Z_to_bv 64 (IP + ilen - bv_unsigned p)) with (Z_to_bv 64 (ilen - Z.of_nat off)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (IE off p (Z_to_bv 64 0) 0%Z K j0 w16); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite Hw16. replace (Z_to_bv 64 (IP + ilen - 8 - bv_unsigned p)) with (Z_to_bv 64 (ilen - Z.of_nat off - 8)) by (f_equal; lia).
      step. (* [comment removed for export] *)
      rewrite <- Hmaxd.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit dg) in * by lia.
      if_cases Hc; cond_cleanup Hc.
      + eapply (IE off p (Z_to_bv 64 0) 0%Z K j0 w16); try eassumption; try lia.
      + eapply (I81 off p (Z_to_bv 64 0) 0%Z K j0 w16); try eassumption; try lia.
  Qed.
  Notation FRLO0 j0 j1 m := (rw_cells USEGS m (SP + -144) [CB 8 j0; C8 numv; CB 16 j1; C8 resv]).

  Definition iconst_ok : Prop :=
    forall (off : nat) (p : word) (j0 j2 : list byte) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
      FRLOJ j0 j2 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A ws -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17 mdw x19 x20 x21 p (Z_to_bv 64 (IP + ilen)) x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26040) fc None m (seg_rom USEGS)).

  Definition iz1_ok (k : nat) : Prop :=
    forall (off : nat) (p pendw : word) (j0 j2 : list byte) (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
      FRLOJ j0 j2 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A ws -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> bv_unsigned pendw = (IP + ilen)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 pendw (Z_to_bv 64 48) (Z_to_bv 64 (-1)) x13 x14 x15 x16 x17 mdw x19 x20 x21 p (Z_to_bv 64 (IP + ilen)) x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26024) fc None m (seg_rom USEGS)).

  Definition izmid_ok : Prop :=
    forall (off : nat) (p : word) (j0 j2 : list byte) (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
      FRLOJ j0 j2 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A ws -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 p x11 x12 x13 x14 x15 x16 x17 mdw x19 x20 x21 p (Z_to_bv 64 (IP + ilen)) x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26010) fc None m (seg_rom USEGS)).

  Definition izpre_ok : Prop :=
    forall (off : nat) (p : word) (j0 j1 : list byte) (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
      FRLO0 j0 j1 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A ws -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 p x11 x12 x13 x14 x15 x16 x17 mdw x19 x20 x21 p (Z_to_bv 64 (IP + ilen)) x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26004) fc None m (seg_rom USEGS)).

  Definition iz8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (j0 j1 : list byte) (x1 x5 x6 x7 x9 x15 x16 x17 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
      FRLO0 j0 j1 m -> FRHI m -> stk USEGS m (SP + -144) (SP + -144) ->
      u64arr USEGS m A ws -> rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells USEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at USEGS m IP ibs ->
      munch W m0 m -> wmono USEGS m0 m -> pristine m 0x10000 0x22000 ->
      (length ibs - off <= k)%nat -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 p (Z_to_bv 64 (ilen - Z.of_nat off)) (Z_to_bv 64 8) (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 7) x15 x16 x17 mdw x19 x20 x21 p (Z_to_bv 64 (IP + ilen)) x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25f8c) fc None m (seg_rom USEGS)).

  Ltac introsZ := intros FRLO FRH ST XL XC DG NUM IBS MU WM PR.

  Lemma val0 : VAL ws 0 0.
  Proof. LiaFast.lf_pins LiaFast.lf_all. unfold boxed. split. { apply bnorm_0. } change (Z.to_nat 0) with 0%nat. rewrite bval_0. cbn. lia. Qed.

  Lemma iconst_proof : fset_ok -> (forall k, iout_ok k) -> iconst_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FS IOUT. unfold iconst_ok; intros until m; introsZ; intros Hoff Hp; pre.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX'. rewrite Hws in BdX'.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply (FS tt 0%Z j0 j2); try eassumption; try lia. apply val0. }
    do 19 step.
    eapply (IOUT (length ibs - off)%nat off p 0%Z j0 (Z_to_bv 64 (IP + ilen + -8))); try eassumption; try lia.
    { rewrite unsigned_lit by lia. lia. }
    apply val0.
  Qed.

  Lemma iz1_proof : iconst_ok -> forall k, iz1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IC. induction k as [|k IH]; unfold iz1_ok; intros until m; introsZ; intros Hk Hoff Hp Hpe; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (bv_unsigned_in_range 64 pendw) as Rpe; unfold bv_modulus in Rpe.
    step. (* [comment removed for export] *)
    if_not_taken.
    pose proof (ro_block USEGS m IP ibs off 1 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { eapply (IC off p j0 j2); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) pendw j0 j2); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      eapply (IC (length ibs) pendw j0 j2); try eassumption; try lia.
  Qed.

  Lemma izmid_proof : fset_ok -> (forall k, iz1_ok k) -> izmid_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FS IZ1. unfold izmid_ok; intros until m; introsZ; intros Hoff Hp; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply (FS tt 0%Z j0 j2); try eassumption; try lia. apply val0. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (IZ1 (length ibs - off)%nat off p _ j0 j2); try eassumption; try lia.
    rewrite (unsigned_lit (IP + ilen)) by lia. rewrite !unsigned_lit by lia. lia.
  Qed.

  Lemma izpre_proof : izmid_ok -> izpre_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IM. unfold izpre_ok; intros until m; introsZ; intros Hoff Hp; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (IM off p); try eassumption; try lia.
  Qed.

  Lemma iz8_proof : izpre_ok -> forall k, iz8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IP8. induction k as [|k IH]; unfold iz8_ok; intros until m; introsZ; intros Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block USEGS m IP ibs off 8 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    do 22 step.
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { eapply (IP8 off p j0 j1); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (ilen - Z.of_nat off + -8)) with (Z_to_bv 64 (ilen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) j0 j1); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      eapply (IP8 (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) j0 j1); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma body_ok : izpre_ok -> (forall k, iz8_ok k) ->
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 dg0 : word),
      stk USEGS m0 (SP - 144) SP ->
      u64arr USEGS m0 A ws -> rw_cells USEGS m0 (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells USEGS m0 (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)] ->
      bytes_at USEGS m0 IP ibs -> rw_cells USEGS m0 D [C8 dg0] -> pristine m0 0x10000 0x22000 ->
      evt USEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0i s1i resv numv mdw dv a4 a5 a6 a7 s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i t3 t4 t5 t6)
            F (Z_to_bv 64 0x25f08) fc None m0 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IZP IZ8. intros until dg0. intros ST XL XC NUM IBS DG PR. bounds.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hws in BdX.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl USEGS m0) as WM.
    carve_frame 144%nat ST.
    do 14 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with FR : rw_cells USEGS ?m1 (SP + -144) ?cs |- _ =>
      chunk_split FR 4%nat FRLO FRH end.
    change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)) in DG |- *.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    setcmp. decide_ltb.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_false.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H8; cond_cleanup H8; rewrite ?signed_lit in H8 by lia.
    - step. (* [comment removed for export] *)
      eapply (IZP 0%nat iptr); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 ilen) with (Z_to_bv 64 (ilen - Z.of_nat 0)) by (f_equal; lia).
      eapply (IZ8 (length ibs) 0%nat iptr); try eassumption; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma main_ok :
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 dg0 : word),
      stk USEGS m0 (SP - 144) SP ->
      u64arr USEGS m0 A ws -> rw_cells USEGS m0 (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells USEGS m0 (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)] ->
      bytes_at USEGS m0 IP ibs -> rw_cells USEGS m0 D [C8 dg0] -> pristine m0 0x10000 0x22000 ->
      evt USEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0i s1i resv numv mdw dv a4 a5 a6 a7 s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i t3 t4 t5 t6)
            F (Z_to_bv 64 0x25f08) fc None m0 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    pose proof end_proof as END.
    pose proof (diginc_proof END) as DIG.
    pose proof (ru_proof DIG) as RU.
    pose proof (ftb1_proof END RU) as FTB1.
    pose proof (ftb8_proof END RU FTB1) as FTB8.
    pose proof (ftb_proof END FTB1 FTB8) as FTB.
    pose proof (ftaend_proof END RU) as FE.
    pose proof (fta1_proof FE RU) as FTA1.
    pose proof (fta8_proof FE RU FTA1) as FTA8.
    pose proof (fta_proof END FE FTA1 FTA8) as FTA.
    pose proof (it1_proof FTA) as IT1.
    pose proof (it8_proof FTA IT1) as IT8.
    pose proof (it_proof FTA IT1 IT8) as IT.
    pose proof (itrunc_proof IT) as ITRUNC.
    pose proof (ftrunc_proof FTB) as FTRUNC.
    pose proof (fout_proof END FTRUNC) as FOUT.
    pose proof (fconst_proof END FOUT) as FCONST.
    pose proof (fz1_proof FCONST) as FZ1.
    pose proof (fzmid_proof FZ1) as FZMID.
    pose proof (fz8_proof END FZMID) as FZ8.
    pose proof (fz_proof END FZMID FZ8) as FZ.
    pose proof (fset_proof END FZ FCONST) as FSET.
    pose proof (iout_proof FSET ITRUNC) as IOUT.
    pose proof (iconst_proof FSET IOUT) as ICONST.
    pose proof (iz1_proof ICONST) as IZ1.
    pose proof (izmid_proof FSET IZ1) as IZMID.
    pose proof (izpre_proof IZMID) as IZPRE.
    pose proof (iz8_proof IZPRE) as IZ8.
    exact (body_ok IZPRE IZ8).
  Qed.
End Proof.

Section Top.
  Hypothesis small_mul_spec : small_mul_stmt.
  Hypothesis small_add_spec : small_add_stmt.

  Lemma parse_mantissa_spec : parse_mantissa_stmt.
  Proof.
    unfold parse_mantissa_stmt. intros until dg.
    intros ST ALIGN PR XL Hxl XC XAL NUM IBS INZ IEND ILEN FBS FEND FLEN FNULL MAXD DG LAY0 LAY1 LAY2 LAY3 LAY4 LAY5.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI. pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    eapply (main_ok small_mul_spec small_add_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 F fc m ws iptr fptr ibs fbs
              (Z.of_nat (length ibs)) (Z.of_nat (length fbs)) (bv_unsigned a2)
              eq_refl eq_refl eq_refl Hxl MAXD XAL ALIGN INZ IEND ltac:(lia) FEND ltac:(lia) FNULL FBS LAY0 LAY1 LAY2 LAY3 LAY4 LAY5);
      eassumption.
  Qed.
End Top.
