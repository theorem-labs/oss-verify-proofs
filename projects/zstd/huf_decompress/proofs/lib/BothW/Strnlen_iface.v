(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (strnlen_rl_res, strnlen_rl_cstr)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells Stdio_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Strnlen_iface () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib6Common6StrFun9find_byteC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3minK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib6Common6StrFun>find_byte_SomeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3minC46Stdlib5Lists4List=length_firstnC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc59OSSVerify5KrLib5BothW=Strnlen_iface:strnlen_rlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun;strnlen_resC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitions7Z_to_bvC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib6Common6StrFun>find_byte_cstrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib6Common6StrFunDfind_byte_cstr_shortC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition strnlen_i_entry : Z := 0x41dec.
Definition STRNLEN_I_DEPTH : Z := 4400.

(* [comment removed for export] *)
Definition strnlen_rl (n : Z) (buf : list byte) : Z :=
  match find_byte 0 (firstn (Z.to_nat n) buf) with Some j => Z.of_nat j + 1 | None => n end.

Lemma strnlen_rl_res : forall n buf, 0 <= n -> strnlen_rl n buf = Z.min (strnlen_res n buf + 1) n.
Proof.
  intros n buf Hn. unfold strnlen_rl, strnlen_res.
  destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [j|] eqn:E; [|lia].
  pose proof (find_byte_Some _ _ _ E) as [Hj _]. rewrite length_firstn in Hj. lia.
Qed.

(* [comment removed for export] *)
Lemma strnlen_rl_cstr : forall n (str slack : list byte), ~ In (Z_to_bv 8 0) str -> 0 <= n ->
  strnlen_rl n (str ++ Z_to_bv 8 0 :: slack) = Z.min (Z.of_nat (length str) + 1) n.
Proof.
  intros n str slack NONUL Hn. unfold strnlen_rl. destruct (Z.lt_ge_cases (Z.of_nat (length str)) n).
  - rewrite (find_byte_cstr 0 n str slack NONUL) by lia. lia.
  - rewrite (find_byte_cstr_short 0 n str slack NONUL) by lia. lia.
Qed.

Definition strnlen_a_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strnlen_res n buf)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - STRNLEN_I_DEPTH, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ bytes_at bsegs m' P buf.

Definition strnlen_a_stmt : Prop :=
  forall (RNG : footprint) (r : region)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P n : Z) (buf : list byte) (lo : Z),
    a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 n -> 0 < P -> 0 <= n < 2^64 ->
    bytes_at bsegs m P buf -> memchr_ok P 0 n buf ->
    mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - STRNLEN_I_DEPTH -> KHIGH <= lo ->
    (P + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= P) ->
    (* [comment removed for export] *)
    ashenv m -> rclean m r -> inreg r P (strnlen_rl n buf) -> strnlen_rl n buf <= 2^40 ->
    (* [comment removed for export] *)
    rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG P (Z.of_nat (length buf)) -> rrng RNG r ->
    evtF bsegs RNG (strnlen_a_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P n buf lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 strnlen_i_entry) fc None m (seg_rom bsegs)).
End CANSEC1.
