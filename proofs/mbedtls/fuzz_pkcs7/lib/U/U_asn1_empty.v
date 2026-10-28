(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_get_int.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Definition asn1_empty_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP p lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-96)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ rw_cells segs m' PP [C8 (Z_to_bv 64 p)]
    /\ stk segs m' lo (bv_unsigned sp)
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition asn1_empty_stmt (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (PP p lo : Z),
  rw_cells segs m PP [C8 (Z_to_bv 64 p)] -> 0 <= p < 2^64 -> mem_inv segs m -> bv_unsigned ra mod 2 = 0 ->
  0 < PP -> PP mod 8 = 0 ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 p ->
  evt segs (asn1_empty_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP p lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs))
(* [comment removed for export] *).


Lemma U_asn1_get_int_empty : asn1_empty_stmt usegs U_ASN1_GET_INT.
Proof.
  unfold asn1_empty_stmt, U_ASN1_GET_INT. intros until lo. intros HPP PB MI RA NZ AL ST SLO SPA DS -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
  carve_frame 32%nat ST.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 7 zstep.
  zstep; if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|].
  zstep. zstep; if_cases K2; zify_cond K2.
  { exfalso. rewrite ?unsigned_lit in K2 by lia. change 7 with (Z.ones 3) in K2. rewrite Z.land_ones in K2 by lia.
    change (2 ^ 3) with 8 in K2. lia. }
  zstep. zstep. zstep. rewrite ?Z.sub_diag. if_true.
  do 5 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep. fin.
Qed.
