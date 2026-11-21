(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed Hva, Hve, Z_to_bv_u_eq and 74 more; added Hlau, Hvl, brk and 7 more; removed av, ev, hw and 2 more. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require NArith ZArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module ArgvEnv.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_ArgvEnv () := "C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilC59OSSVerify5KrLib7Mh_00387CatExec>valid_argv_lenC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib7Mh_00417ArgvEnv5argcNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac9bsb_boundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesK47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3addc59OSSVerify5KrLib7Mh_00417ArgvEnv9sp_hi_numC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C49OSSVerify5KrLib8PropExec8v_slli_3C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;v_add_smallC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedc59OSSVerify5KrLib7Mh_00417ArgvEnv7u_argcNC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00417ArgvEnv9sp_lo_numC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00c59OSSVerify5KrLib7Mh_00417ArgvEnv8envp_ptrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecDrdn_wrap_stack_aboveC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memI47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib7Mh_00417ArgvEnv4wmemC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8word_le8K47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib8PropExec9read_argcC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib7Mh_00417ArgvEnv>rdn_wmem_stackC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2c59OSSVerify5KrLib7Mh_00417ArgvEnv6bsb_nwC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib7Mh_00387SeqExec?argv_ptr_boundsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib7Mh_00387SeqExecAargv_layout_slackC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC47Corelib4Init3Nat3addC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib7Mh_00387CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec?read_argv_ptr_kC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib7Mh_00387StepTac<word_add_natC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_add".

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section Scaffold.

  (** The loaded segments (source_segs / target_segs at each call site)
      and the launch: the process input, the entry's mmap base, stack
      pointer, program break and draw.  The argv/envp lists, the
      credentials and AT_HWCAP are fields of [inp], and the stack VMA's
      end is [ed_top] of the draw, so one [ProcInput] and one
      [EntryDraw] fix the whole initial stack image. *)
  Variable segs : list Segment.
  Variable v : VaSize.
  Variable inp : ProcInput.
  Variable mbase : word.

  (** The image's program-header record ([MemImageType.PhdrInfo]) and
      its entry point: the auxv carries both. *)
  Variable ph : PhdrInfo.
  Variable entry : word.

  Variable sp brk : word.
  Variable draw : EntryDraw.

  (** The ambient hypotheses every binary shares. *)
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp brk mbase draw) inp.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma sp_lo_num : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. exact Hsp_lo. Qed.

  Lemma sp_hi_num : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. exact Hsp_hi. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition argcN : word := len_word (in_argv inp).

  Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length (in_argv inp)).
  Proof.
    pose proof (valid_argv_len (in_argv inp) Hva).
    unfold argcN, len_word. apply u_Z2bv; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma bsb_nw :
    (bv_unsigned sp
     + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw)) < 2^64)%Z.
  Proof.
    pose proof (bsb_bound v inp mbase ph entry sp brk draw Hvl Hlau).
    pose proof sp_hi_num. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition envp_ptr : word :=
    Z_to_bv 64 (bv_unsigned sp + 8 + 8 * Z.of_nat (length (in_argv inp)) + 8).

  Lemma envp_ptr_eq :
    v_addi (v_add (Z_to_bv 64 (bv_unsigned sp + 8)) (v_slli argcN 3)) 8 = envp_ptr.
  Proof.
    pose proof sp_hi_num. pose proof sp_lo_num.
    pose proof (valid_argv_len (in_argv inp) Hva) as Hlen.
    apply bv_eq. unfold envp_ptr, v_addi.
    rewrite !Z_to_bv_unsigned.
    rewrite v_add_small
      by (rewrite u_Z2bv by lia; rewrite v_slli_3 by (rewrite u_argcN; lia);
          rewrite u_argcN; lia).
    rewrite u_Z2bv by lia.
    rewrite v_slli_3 by (rewrite u_argcN; lia).
    rewrite u_argcN.
    f_equal; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition wmem : word -> option byte := wrap_mem inp mbase ph entry sp draw.

  (* [comment removed for export] *)
  Lemma rdn_wmem_stack : forall (a : word) n,
    (bv_unsigned sp <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs wmem a n
    = rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw)) a n.
  Proof. intros a n Ha Hn. unfold wmem. apply rdn_wrap_stack_above; assumption. Qed.

  (* [comment removed for export] *)
  Lemma read_argc_w :
    rdn segs wmem sp 8%nat = Some (word_le8 argcN).
  Proof.
    pose proof sp_hi_num.
    rewrite rdn_wmem_stack by lia.
    apply read_argc. exact bsb_nw.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma argv_ptr_bounds_at : forall k, (k < length (in_argv inp))%nat ->
    (bv_unsigned sp
     <= bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                       (in_execfn inp) k))%Z /\
    (bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                    (in_execfn inp) k)
       + Z.of_nat (length (nth k (in_argv inp) [])) + 1 < 2^64)%Z.
  Proof.
    intros k Hk. exact (argv_ptr_bounds v inp mbase sp brk draw k Hlau Hk).
  Qed.

  (* [comment removed for export] *)
  Lemma read_argv_ptr_w : forall k, (k < length (in_argv inp))%nat ->
    rdn segs wmem (sp + nat_to_word (8 + 8 * k)) 8%nat
    = Some (word_le8 (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                        (in_execfn inp) k)).
  Proof.
    intros k Hk. pose proof sp_lo_num. pose proof sp_hi_num.
    pose proof (valid_argv_len (in_argv inp) Hva) as Hal.
    rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
    apply read_argv_ptr_k; [ exact Hk | exact bsb_nw ].
  Qed.

End Scaffold.

End ArgvEnv.
From Stdlib Require ZArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.
Module StartupAux.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_StartupAux () := "C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC4ELinuxProcessSemantics5Riscv3Sem7reg_getI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics5Riscv7Prelude6bv_keyK4ELinuxProcessSemantics5Riscv7Prelude4tree01C4ELinuxProcessSemantics5Riscv7Prelude4tgetC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00I47Corelib7Numbers7BinNums8positive00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv3Sem2w0I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z:ones_equivK47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z=ones_mod_pow2C56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith8Zbitwise1Z?sub_land_same_lC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z:ldiff_landC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6shiftlK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z<ldiff_ones_rC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z:land_assocK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C45stdpp9bitvector;definitions7bv_wrapC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC56Stdlib6ZArith6BinInt1Z<eq_decidableI47Corelib4Init5Logic2or00K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula06c59OSSVerify5KrLib7Mh_0041:StartupAux?land_align_maskC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC49OSSVerify5KrLib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib7Mh_0041:StartupAux=land_low_zeroC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z=testbit_neg_rC56Stdlib6ZArith6BinInt1Z=mul_pow2_bitsC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z=pow2_bits_eqbC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib7Mh_0041:StartupAux?land_4_aligned8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9pow_add_rK47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions?bv_half_modulusC46Stdlib6ZArith4ZdivBZminus_mod_idemp_rc59OSSVerify5KrLib7Mh_0041:StartupAux=mod4_mod_pow2C1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_subwC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_lec59OSSVerify5KrLib7Mh_0041:StartupAuxDfirstn_Z_to_le_bytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib7Mh_0041:StartupAuxGfirstn_word_to_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC49OSSVerify5KrLib8PropExec:bytes_le_NC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C45stdpp9bitvector;definitions>bv_swrap_smallC49OSSVerify5KrLib8PropExec4v_lwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega5Tauto8GFormula01C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05C46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool=andb_true_iffC47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool<orb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indC45stdpp9bitvector;definitionsDbv_unsigned_in_rangec59OSSVerify5KrLib7Mh_0041:StartupAux<Z_to_bv_u_eqC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma getr_empty : forall r : reg, getr bvmap_empty r = Z_to_bv 64 0.
Proof.
  intro r. unfold getr. destruct (bv_eqb r 0); [reflexivity|].
  unfold reg_get, bvmap_get, bvmap_empty.
  destruct (bv_key r); cbn [tget]; apply bv_eq; reflexivity.
Qed.
End FPX_1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Open Scope Z_scope.
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Lemma land_align_mask : forall a k, 0 <= a < 2^64 -> 0 <= k <= 64 -> a mod 2^k = 0 ->
  Z.land a (2^64 - 2^k) = a.
Proof.
  intros a k Ha Hk Hmod.
  replace (2^64 - 2^k) with (Z.ldiff (Z.ones 64) (Z.ones k)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod a (2^k) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma v_andi_m16_aligned : forall x : word,
  bv_unsigned x mod 16 = 0 -> v_andi x (-16) = x.
Proof.
  intros x Hm. unfold v_andi. apply bv_eq. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (-16)) with (2^64 - 2^4).
  pose proof (u64_range x).
  rewrite land_align_mask by (first [lia | exact Hm]).
  apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

(* [comment removed for export] *)
Lemma v_andi_m8_aligned : forall x : word,
  bv_unsigned x mod 8 = 0 -> v_andi x (-8) = x.
Proof.
  intros x Hm. unfold v_andi. apply bv_eq. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (-8)) with (2^64 - 2^3).
  pose proof (u64_range x).
  rewrite land_align_mask by (first [lia | exact Hm]).
  apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

(* [comment removed for export] *)
Lemma land_low_zero : forall a k, 0 <= a -> 0 <= k -> a mod 2^k = 0 -> Z.land a (Z.ones k) = 0.
Proof. intros a k Ha Hk Hm. rewrite Z.land_ones by lia. exact Hm. Qed.

Lemma v_andi_3_aligned : forall x : word,
  bv_unsigned x mod 4 = 0 -> v_andi x 3 = Z_to_bv 64 0.
Proof.
  intros x Hm. unfold v_andi. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). apply land_low_zero; [apply u64_range | lia | exact Hm].
Qed.

Lemma land_4_aligned8 : forall a, 0 <= a -> a mod 8 = 0 -> Z.land a 4 = 0.
Proof.
  intros a Ha Hm.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  change 4 with (2^2). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 2 i); [|apply andb_false_r].
  subst i.
  replace a with ((a / 8) * 2^3) by lia.
  rewrite Z.mul_pow2_bits by lia. change (2 - 3) with (-1).
  rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.

Lemma v_andi_4_aligned8 : forall x : word,
  bv_unsigned x mod 8 = 0 -> v_andi x 4 = Z_to_bv 64 0.
Proof.
  intros x Hm. unfold v_andi. f_equal.
  change (bv_wrap 64 4) with 4. apply land_4_aligned8; [apply u64_range | exact Hm].
Qed.

Lemma v_andi_1_of01 : forall z, (z = 0 \/ z = 1) ->
  v_andi (Z_to_bv 64 z) 1 = Z_to_bv 64 z.
Proof.
  intros z [-> | ->]; apply bv_eq; reflexivity.
Qed.

Lemma mod4_mod_pow2 : forall t k, 2 <= k -> (t mod 2^k) mod 4 = t mod 4.
Proof.
  intros t k Hk. apply Z.mod_mod_divide.
  exists (2^(k-2)). change 4 with (2^2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma negw_and3_aligned : forall x : word,
  bv_unsigned x mod 4 = 0 -> v_andi (v_subw (Z_to_bv 64 0) x) 3 = Z_to_bv 64 0.
Proof.
  intros x Hm. unfold v_andi, v_subw. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
  rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  unfold bv_swrap. rewrite bv_wrap64_mod.
  change (bv_half_modulus 32) with (2^31).
  unfold bv_wrap. change (bv_modulus 32) with (2^32). change (2^2) with 4.
  rewrite mod4_mod_pow2 by lia.
  rewrite <- Zminus_mod_idemp_l.
  rewrite mod4_mod_pow2 by lia.
  replace ((0 - bv_unsigned x + 2^31) mod 4) with 0.
  2:{ replace (0 - bv_unsigned x + 2^31) with (2^31 - bv_unsigned x) by lia.
      rewrite <- Zminus_mod_idemp_r, Hm. reflexivity. }
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma firstn_Z_to_le_bytes : forall k n z, (k <= n)%nat ->
  firstn k (Z_to_le_bytes n z) = Z_to_le_bytes k z.
Proof.
  induction k as [|k IH]; intros n z Hk; [reflexivity|].
  destruct n as [|n]; [lia|]. cbn [Z_to_le_bytes firstn]. rewrite IH by lia. reflexivity.
Qed.

Lemma firstn_word_to_le_bytes : forall k n (v : word), (k <= n)%nat ->
  firstn k (word_to_le_bytes n v) = word_to_le_bytes k v.
Proof. intros. unfold word_to_le_bytes. apply firstn_Z_to_le_bytes. assumption. Qed.

(* [comment removed for export] *)
Lemma rdn_low_bytes : forall segs m (a v : word) k, (k <= 8)%nat ->
  rdn segs m a 8 = Some (word_to_le_bytes 8 v) ->
  rdn segs m a k = Some (word_to_le_bytes k v).
Proof.
  intros segs m a v k Hk H.
  rewrite (rdn_firstn segs m 8 a _ k H Hk). f_equal. apply firstn_word_to_le_bytes. exact Hk.
Qed.

Lemma bytes_le_to_Z_4_small : forall v : word, bv_unsigned v < 2^32 ->
  bytes_le_to_Z (word_to_le_bytes 4 v) = bv_unsigned v.
Proof.
  intros v Hv. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4)) with (2^32).
  apply Z.mod_small. pose proof (u64_range v). lia.
Qed.

Lemma v_lw_small : forall v : word, bv_unsigned v < 2^31 -> v_lw v = v.
Proof.
  intros v Hv. unfold v_lw. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (u64_range v).
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia).
  apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

(* [comment removed for export] *)
Lemma v_add_lit_r : forall (x : word) (k : Z), 0 <= k < 2^64 ->
  v_add x (Z_to_bv 64 k) = Z_to_bv 64 (bv_unsigned x + k).
Proof. intros x k Hk. unfold v_add. rewrite (u_Z2bv k) by lia. reflexivity. Qed.

Lemma v_add_lit_l : forall (x : word) (k : Z), 0 <= k < 2^64 ->
  v_add (Z_to_bv 64 k) x = Z_to_bv 64 (bv_unsigned x + k).
Proof. intros x k Hk. unfold v_add. rewrite (u_Z2bv k) by lia. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma v_slli_lit : forall z sh, 0 <= z -> 0 <= sh -> z * 2^sh < 2^64 ->
  v_slli (Z_to_bv 64 z) sh = Z_to_bv 64 (z * 2^sh).
Proof.
  intros z sh Hz Hsh Hb. unfold v_slli. f_equal.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite u_Z2bv by nia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sub_bv : forall (l1 l2 : list reg) (r : reg),
  forallb (fun x => existsb (fun y => bv_eqb x y) l2) l1 = true -> In r l1 -> In r l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 r H Hin; [contradiction|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hx Hl1].
  destruct Hin as [<-|Hin]; [|apply IH; assumption].
  clear IH Hl1. induction l2 as [|y l2 IH2]; [discriminate|].
  cbn [existsb] in Hx. apply orb_true_iff in Hx as [Hxy|Hx].
  - left. symmetry. apply bv_eq. unfold bv_eqb in Hxy. apply Z.eqb_eq in Hxy. exact Hxy.
  - right. apply IH2. exact Hx.
Qed.

Lemma Z_to_bv_u_eq : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma Z_to_bv_u_eq_sym : forall (a : word) (z : Z), z = bv_unsigned a -> a = Z_to_bv 64 z.
Proof. intros a z H. symmetry. apply Z_to_bv_u_eq. exact H. Qed.

End FPX_2.

End StartupAux.
From Stdlib Require FunctionalExtensionality. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
Module ZStores.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

Fixpoint zstores (m : word -> option byte) (d : word) (ws : list (Z * nat)) : word -> option byte :=
  match ws with
  | [] => m
  | (o, n) :: ws' => zstores (wbytes m (Z_to_bv 64 (bv_unsigned d + o)) (zeros n)) d ws'
  end.

Definition covers_off (i : Z) (on : Z * nat) : bool :=
  (fst on <=? i) && (i <? fst on + Z.of_nat (snd on)).

Definition ws_inb (ws : list (Z * nat)) (N : Z) : bool :=
  forallb (fun on => (0 <=? fst on) && (fst on + Z.of_nat (snd on) <=? N)) ws.

Fixpoint iota_Z (i : Z) (k : nat) : list Z :=
  match k with O => [] | S k' => i :: iota_Z (i + 1) k' end.

Definition ws_cover (ws : list (Z * nat)) (N : nat) : bool :=
  forallb (fun i => existsb (covers_off i) ws) (iota_Z 0 N).

Lemma forallb_In : forall {A} (f : A -> bool) l x, forallb f l = true -> In x l -> f x = true.
Proof.
  induction l as [|y l IH]; intros x H Hin; [contradiction|].
  cbn in H. apply andb_true_iff in H as [Hy Hl].
  destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.

Lemma iota_Z_In : forall k i z, i <= z < i + Z.of_nat k -> In z (iota_Z i k).
Proof.
  induction k as [|k IH]; intros i z Hz; [lia|].
  cbn. destruct (Z.eq_dec i z); [left; assumption | right]. apply IH. lia.
Qed.

Lemma existsb_false_forall : forall {A} (f : A -> bool) l,
  existsb f l = false -> forall x, In x l -> f x = false.
Proof.
  induction l as [|y l IH]; intros H x Hin; [contradiction|].
  cbn in H. apply orb_false_iff in H as [Hy Hl].
  destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.

Lemma existsb_true_exists : forall {A} (f : A -> bool) l,
  existsb f l = true -> exists x, In x l /\ f x = true.
Proof.
  induction l as [|y l IH]; intros H; [discriminate|].
  cbn in H. apply orb_true_iff in H as [Hy|Hl].
  - exists y. split; [left; reflexivity | exact Hy].
  - destruct (IH Hl) as [x [Hin Hx]]. exists x. split; [right; exact Hin | exact Hx].
Qed.

Lemma length_zeros : forall n, length (zeros n) = n.
Proof. intro n. apply repeat_length. Qed.

Lemma nth_zeros : forall n k, nth k (zeros n) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof. intros n k. unfold zeros. apply nth_repeat. Qed.

Lemma rdn_wbytes_zeros_in : forall segs m (d a : word) (N n : nat),
  bv_unsigned d + Z.of_nat N < 2^64 ->
  bv_unsigned d <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned d + Z.of_nat N ->
  rdn segs (wbytes m d (zeros N)) a n = Some (zeros n).
Proof.
  intros segs m d a N n Hnw Hlo Hhi. unfold zeros at 2. apply rdn_const; [lia|].
  intros x Hx. rewrite wbytes_inside by (rewrite length_zeros; lia).
  f_equal. apply nth_zeros.
Qed.

Lemma bytes_le_to_Z_zeros : forall n, bytes_le_to_Z (zeros n) = 0.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [zeros repeat bytes_le_to_Z].
  fold (zeros n). rewrite IH. reflexivity.
Qed.

Section Cover.
  Variable d : word.
  Variable N : Z.
  Hypothesis Hnw : bv_unsigned d + N < 2^64.

  Lemma zstores_miss : forall ws m (x : word),
    ws_inb ws N = true ->
    (forall on, In on ws -> covers_off (bv_unsigned x - bv_unsigned d) on = false) ->
    zstores m d ws x = m x.
  Proof.
    induction ws as [|[o n] ws IH]; intros m x Hinb Hno; [reflexivity|].
    cbn [zstores]. cbn [ws_inb forallb fst snd] in Hinb.
    apply andb_true_iff in Hinb as [Hon Hinb]. apply andb_true_iff in Hon as [Ho Hn].
    apply Z.leb_le in Ho. apply Z.leb_le in Hn.
    rewrite IH; [| exact Hinb | intros on Hin; apply Hno; right; exact Hin].
    pose proof (Hno (o, n) (or_introl eq_refl)) as Hc. cbn [covers_off fst snd] in Hc.
    pose proof (u64_range x). pose proof (u64_range d).
    apply wbytes_outside.
    - rewrite length_zeros. rewrite u_Z2bv by lia. lia.
    - rewrite length_zeros. rewrite u_Z2bv by lia.
      apply andb_false_iff in Hc as [Hc|Hc]; [apply Z.leb_gt in Hc | apply Z.ltb_ge in Hc];
        cbn [fst snd] in Hc; lia.
  Qed.

  Lemma zstores_hit : forall ws m (x : word),
    ws_inb ws N = true ->
    (exists on, In on ws /\ covers_off (bv_unsigned x - bv_unsigned d) on = true) ->
    zstores m d ws x = Some (Z_to_bv 8 0).
  Proof.
    induction ws as [|[o n] ws IH]; intros m x Hinb Hex.
    { destruct Hex as [on [[] _]]. }
    cbn [zstores]. cbn [ws_inb forallb fst snd] in Hinb.
    apply andb_true_iff in Hinb as [Hon Hinb]. apply andb_true_iff in Hon as [Ho Hn].
    apply Z.leb_le in Ho. apply Z.leb_le in Hn.
    destruct (existsb (covers_off (bv_unsigned x - bv_unsigned d)) ws) eqn:E.
    - apply IH; [exact Hinb|]. apply existsb_true_exists. exact E.
    - rewrite zstores_miss; [| exact Hinb | apply existsb_false_forall; exact E].
      destruct Hex as [on [[<-|Hin] Hc]].
      2:{ rewrite (existsb_false_forall _ _ E on Hin) in Hc. discriminate. }
      cbn [covers_off fst snd] in Hc. apply andb_true_iff in Hc as [Hc1 Hc2].
      apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2. cbn [fst snd] in Hc1, Hc2.
      pose proof (u64_range x). pose proof (u64_range d).
      rewrite wbytes_inside by (rewrite length_zeros, u_Z2bv by lia; lia).
      f_equal. apply nth_zeros.
  Qed.

  Lemma zstores_cover : forall ws m (n : nat),
    Z.of_nat n = N ->
    ws_inb ws N = true ->
    ws_cover ws n = true ->
    zstores m d ws = wbytes m d (zeros n).
  Proof.
    intros ws m n HnN Hinb Hcov. apply functional_extensionality. intro x.
    pose proof (u64_range x). pose proof (u64_range d).
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d)) as [Hlt|Hge].
    { rewrite wbytes_outside by (rewrite length_zeros; lia).
      apply zstores_miss; [exact Hinb|]. intros [o k] Hin.
      pose proof (forallb_In _ _ _ Hinb Hin) as Hb. cbn [fst snd] in Hb.
      apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1.
      cbn [covers_off fst snd]. apply andb_false_iff. left. apply Z.leb_gt. cbn [fst snd]. lia. }
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d + N)) as [Hin|Hout].
    - rewrite wbytes_inside by (rewrite length_zeros; lia). rewrite nth_zeros.
      apply zstores_hit; [exact Hinb|].
      pose proof (forallb_In _ _ _ Hcov (iota_Z_In n 0 (bv_unsigned x - bv_unsigned d) ltac:(lia))) as He.
      apply existsb_true_exists in He. exact He.
    - rewrite wbytes_outside by (rewrite length_zeros; lia).
      apply zstores_miss; [exact Hinb|]. intros [o k] Hin'.
      pose proof (forallb_In _ _ _ Hinb Hin') as Hb. cbn [fst snd] in Hb.
      apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb2.
      cbn [covers_off fst snd]. apply andb_false_iff. right. apply Z.ltb_ge. cbn [fst snd]. lia.
  Qed.
End Cover.

End FPX_1.

End ZStores.
Module StartupTac.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Export OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.StartupAux OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ZStores.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_StartupTac () := "C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00417ZStores:forallb_InC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00417ZStoresDexistsb_false_forallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00417ZStoresCexistsb_true_existsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0041:StartupTac3bwdC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac pin :=
  repeat match goal with
         | H : getr ?rs ?r = _ |- context [getr ?rs ?r] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with
             | context [Z_to_bv 64 _] => fail
             | _ => rewrite (u_Z2bv z) by lia
             end
         end.

(* [comment removed for export] *)
Ltac zlit :=
  repeat match goal with
         | |- context [Z_to_bv 64 ?z] =>
             lazymatch z with
             | Z0 => fail | Zpos _ => fail | Zneg _ => fail
             | _ => check_closed_term z; let z' := eval vm_compute in z in change z with z'
             end
         end.

(* [comment removed for export] *)
Ltac region_side :=
  unfold win_lo, wok_lo; rewrite ?stack_max_size_val;
  unfold stack_window_reach;
  rewrite ?length_N_to_le_bytes, ?length_zeros, ?repeat_length;
  cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; imm_norm; unorm; lia.

(* [comment removed for export] *)
Ltac addr_norm :=
  gres; pin; imm_norm; rewrite ?v_addi_0; unfold v_addi, v_add; unorm; zlit.

(* [comment removed for export] *)
Ltac vclose_fin :=
  first [ reflexivity | f_equal; lia | apply at_self | symmetry; apply at_self
        | apply Z_to_bv_u_eq; lia | apply Z_to_bv_u_eq_sym; lia | bveq ].
Ltac vclose :=
  gres; pin; imm_norm;
  first [ reflexivity
        | unfold v_addi, v_add; unorm; zlit; vclose_fin
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; first [ reflexivity | vclose_fin ]
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; unfold v_addi, v_add; unorm; zlit; vclose_fin ].

(* [comment removed for export] *)
Ltac sn F D := stepn F D; pin.
Ltac sv F D v := stepiv F D v vclose.

(* [comment removed for export] *)
Ltac blit :=
  repeat match goal with
         | |- context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] =>
             lazymatch z with
             | Z0 => change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 0)
             | Zpos _ => let z' := eval vm_compute in (z mod 256)%Z in
                         change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 z')
             end
         end.

(* [comment removed for export] *)
Ltac push_store :=
  blit;
  first [ rewrite wbytes_cmem_win by region_side
        | rewrite wbytes_cmem_data by region_side
        | idtac ].

(* [comment removed for export] *)
Ltac stw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply step_sh_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | reflexivity | oktac ]
    end
  | step_simpl; push_store ].

(* [comment removed for export] *)
Ltac ok_sub Hok :=
  store_ok_peel; eapply store_ok_sub; [ | exact Hok | | ];
  rewrite ?length_N_to_le_bytes, ?length_zeros; unorm; lia.

(* [comment removed for export] *)
Ltac ok_win HJ :=
  apply store_ok_cmem_win; [ repeat apply wfJ_wbytes; exact HJ | region_side | region_side ].

(* [comment removed for export] *)
Ltac ok_data :=
  apply store_ok_cmem_data;
  lazymatch goal with |- ?g => check_closed_term g; vm_compute; reflexivity end.

(* [comment removed for export] *)
Ltac ld_step F D bsv vv rdtac valtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 true _ _ _, _) => eapply step_lh with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 false _ _ _, _) => eapply step_lhu with (bs := bsv) (v := vv)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac | valtac ]
  | step_simpl ]; vnorm; pin.

(* [comment removed for export] *)
Ltac lb_step F D bb rdtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ1 false _ _ _, _) => eapply step_lbu with (b := bb)
    | decode_any _ = Some (Load SZ1 true _ _ _, _) => eapply step_lb with (b := bb)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac ]
  | step_simpl ]; vnorm; pin.

(* [comment removed for export] *)
Ltac peel := repeat (rewrite rdn_wbytes_out by region_side).

(* [comment removed for export] *)
Ltac rd_img L := addr_norm; rewrite rdn_cmem_data by region_side; peel; exact L.

(* [comment removed for export] *)
Ltac rd_hit8 :=
  addr_norm; peel;
  lazymatch goal with |- rdn _ (wbytes _ ?a' _) ?a _ = _ =>
    first [ constr_eq a a' | replace a with a' by (first [f_equal; lia | bveq]) ] end;
  apply rdn_wbytes_hit8; unorm; lia.

(* [comment removed for export] *)
Ltac in_list := cbn [In]; repeat first [ left; reflexivity | right ].
Ltac solve_regs_agree :=
  repeat (apply regs_agree_upd; [ in_list | ]); apply regs_agree_refl.

(* [comment removed for export] *)
Ltac incl_list :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [in_list|]); destruct Hr.
Ltac regs_agree_weaken Hag :=
  eapply regs_agree_mono; [| exact Hag]; incl_list.

Ltac notin_list :=
  cbn [In]; intros HH; repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH.

(* [comment removed for export] *)
Ltac carry Hag H r T :=
  pose proof (Hag r ltac:(notin_list)) as T;
  repeat first [ rewrite getr_same in T by reg_neq_tac | rewrite getr_other in T by reg_neq_tac ];
  rewrite ?H in T.

(* [comment removed for export] *)
Ltac ra_chain :=
  first [ apply regs_agree_refl
        | apply regs_agree_upd; [ in_list | ]; ra_chain
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | regs_agree_weaken Hag ]; ra_chain
          end ].
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bwd (segs : list Segment) (G : machine_state -> Prop) : Prop :=
  forall st st', msteps segs st st' -> G st' -> G st.

Lemma bwd_msteps : forall segs tgt, bwd segs (fun st => msteps segs st tgt).
Proof. intros segs tgt st st' H1 H2. eapply msteps_trans; eassumption. Qed.
End FPX_1.


(* [comment removed for export] *)
Ltac gsteps HG := eapply HG.

End StartupTac.
Module RefLayout.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ArgvEnv.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_RefLayout () := "C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00417ZStores:forallb_InC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00417ZStoresDexistsb_false_forallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00417ZStoresCexistsb_true_existsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C47Corelib4Init5Logic7f_equalC47Corelib5Lists7ListDef6firstnC45stdpp9bitvector;definitions6bv_addC49OSSVerify5KrLib8PropExec:word_add_0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecEnat_to_word_add_mergeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes7nat_indC47Corelib5Lists7ListDef5skipnC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappK47Corelib4Init9Datatypes3nat01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith4Znat5Nat2Z8inj_succI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01C49OSSVerify5KrLib8PropExec9word1_natC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C46Stdlib5Lists4List9app_nil_rC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:firstn_allC47Corelib4Init3Nat3subC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List:firstn_appc59OSSVerify5KrLib7Mh_00419RefLayout@firstn_app_exactC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9skipn_allC46Stdlib5Lists4List9skipn_appc59OSSVerify5KrLib7Mh_00419RefLayout?skipn_app_exactC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC56Stdlib5Arith8PeanoNat3Nat7sub_0_rc59OSSVerify5KrLib7Mh_00419RefLayout=skipn_repeat'C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03c59OSSVerify5KrLib7Mh_00419RefLayout>firstn_repeat'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib5Lists4List9app_assocc59OSSVerify5KrLib7Mh_00419RefLayoutCrepeat_firstn_skipnC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout:build_auxvC47Corelib4Init9Datatypes3sndC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8word_le8K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<auxv_entriesc59OSSVerify5KrLib7Mh_00419RefLayout@build_auxv_wordsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout:auxv_bytesc59OSSVerify5KrLib7Mh_00419RefLayout:auxv_wordsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00c59OSSVerify5KrLib7Mh_00417ArgvEnv6bsb_nwC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesI47Corelib5Lists7ListDef6Forall00C45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC46Stdlib9micromega;ZifyClasses9and_morphC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathK47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathC47Corelib4Init3Nat3mulC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout=at_random_ptrC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<string_addrsC49OSSVerify5KrLib8PropExecCtotal_arg_bytes_natC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?flatten_stringsC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6to_natC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?at_random_bytesI47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C49OSSVerify5KrLib8PropExecAstring_addrs_pairC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec?cat_string_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec<cat_env_baseC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9auxv_sizeC46Stdlib5Lists4List:length_appC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C49OSSVerify5KrLib8PropExecGlength_string_addrs_fstC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecClength_flat_map_le8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec@length_n_to_le_8C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC49OSSVerify5KrLib8PropExecDread_at_offset_imageC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memc59OSSVerify5KrLib7Mh_00419RefLayout:bsb_decompC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout:lay_bsb_nwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout=len_argc_argvC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List@firstn_length_leC47Corelib4Init5Peano2ltc59OSSVerify5KrLib7Mh_00419RefLayout8envp_offC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout<cat_envp_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecCflat_map_le8_decompC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3powC47Corelib5Lists7ListDef3nthC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib7Mh_00419RefLayout=len_envp_ptrsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout8auxv_offC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAlength_auxv_bytesc59OSSVerify5KrLib7Mh_00419RefLayoutAlength_auxv_wordsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout@auxv_bytes_wordsC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpK46Stdlib9micromega:ZMicromega;ZArithProof03c59OSSVerify5KrLib7Mh_00419RefLayout9rdn_skipnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout=read_auxv_allC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC56Stdlib6ZArith4Znat5Z2Nat2idK47Corelib4Init5Logic3and01C49OSSVerify5KrLib8PropExecFlength_flatten_stringsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC46Stdlib5Lists4List<firstn_skipnC4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutFlength_at_random_bytesC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses:impl_morphC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib5Lists4List<length_skipnc59OSSVerify5KrLib7Mh_00419RefLayout@bsb_random_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac9bsb_boundC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega8ZifyInst7Inj_Z_ZC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib7Mh_00387CatExec?cat_struct_sizeC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat9add_assocC59OSSVerify5KrLib7Mh_00387CatExec@nth_string_addrsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecAtotal_arg_bytes_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecItotal_arg_bytes_firstn_leC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflc59OSSVerify5KrLib7Mh_00419RefLayoutEtotal_firstn_ev_boundC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac<word_add_natC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout?cat_envp_ptr_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout?struct_av_boundC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphc59OSSVerify5KrLib7Mh_00419RefLayout>u_cat_envp_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecCcat_argv_ptr_offsetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecBvalid_argv_str_lenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7ph_addrC56Stdlib6ZArith6BinInt1Z4of_NC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_entC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_numC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout7AT_PHDRC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout8AT_PHENTC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout8AT_PHNUMC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout8AT_HWCAPC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9AT_PAGESZC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout6AT_UIDC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout7AT_EUIDC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9AT_SECUREC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9AT_RANDOMC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout7AT_NULLC56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7add_modc59OSSVerify5KrLib7Mh_00419RefLayout=at_random_offC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout;lay_bsb_lenC1?~~~~~~~~~~~~~~~".

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_skipn : forall segs mem n (a : word) bs off k,
  rdn segs mem a n = Some bs -> (off + k <= n)%nat ->
  rdn segs mem (a + nat_to_word off) k = Some (firstn k (skipn off bs)).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs off k H Hk.
  - assert (off = 0%nat) by lia. assert (k = 0%nat) by lia. subst.
    rewrite word_add_0. cbn in H |- *. injection H as <-. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct off as [|off].
    + rewrite word_add_0. cbn [skipn].
      eapply rdn_firstn; [|exact Hk].
      cbn [rdn]. rewrite Eb, Er. reflexivity.
    + cbn [skipn].
      replace (a + nat_to_word (S off)) with (a + 1 + nat_to_word off)
        by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
      apply (IH (a+1) rest off k Er). lia.
Qed.

Lemma firstn_app_exact : forall {A} (l1 l2 : list A) n,
  length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof.
  intros A l1 l2 n H. subst n. rewrite firstn_app, firstn_all, Nat.sub_diag.
  cbn. apply app_nil_r.
Qed.

Lemma skipn_app_exact : forall {A} (l1 l2 : list A) n,
  length l1 = n -> skipn n (l1 ++ l2) = l2.
Proof.
  intros A l1 l2 n H. subst n. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma skipn_repeat' : forall {A} (x : A) off n,
  skipn off (repeat x n) = repeat x (n - off).
Proof.
  intros A x off. induction off as [|off IH]; intros n.
  - cbn. rewrite Nat.sub_0_r. reflexivity.
  - destruct n as [|n]; [reflexivity|]. cbn [repeat skipn]. rewrite IH. f_equal.
Qed.

Lemma firstn_repeat' : forall {A} (x : A) k n, (k <= n)%nat ->
  firstn k (repeat x n) = repeat x k.
Proof.
  intros A x k. induction k as [|k IH]; intros n H; [reflexivity|].
  destruct n as [|n]; [lia|]. cbn [repeat firstn]. rewrite IH by lia. reflexivity.
Qed.

Lemma repeat_firstn_skipn : forall {A} (x : A) n off k,
  (off + k <= n)%nat -> firstn k (skipn off (repeat x n)) = repeat x k.
Proof.
  intros A x n off k H.
  rewrite skipn_repeat', firstn_repeat' by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cat_envp_ptr (top : word) (av ev : list (list byte))
    (execfn : list byte) (k : nat) : word :=
  nth k (fst (string_addrs (cat_env_base top av ev execfn) ev)) (Z_to_bv 64 0).

(* [comment removed for export] *)
Definition envp_off (av : list (list byte)) : nat := (8 + 8 * (length av + 1))%nat.
Definition auxv_off (av ev : list (list byte)) : nat :=
  (8 + 8 * (length av + 1) + 8 * (length ev + 1))%nat.

(* [comment removed for export] *)
Definition auxv_words (la : LaunchAuxv) (ph : PhdrInfo)
    (entry uid gid hwcap at_random at_execfn : word) : list word :=
  flat_map (fun e => [fst e; snd e])
    (auxv_entries la ph entry uid gid hwcap at_random at_execfn).

Lemma build_auxv_words : forall entries,
  build_auxv entries = flat_map word_le8 (flat_map (fun e => [fst e; snd e]) entries).
Proof.
  induction entries as [|[t v] es IH]; [reflexivity|].
  cbn [build_auxv flat_map fst snd app].
  change (build_auxv es) with
    (flat_map (fun e : bv 64 * bv 64 => word_le8 (fst e) ++ word_le8 (snd e)) es) in IH.
  rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma auxv_bytes_words : forall la ph entry uid gid hwcap ar ae,
  auxv_bytes la ph entry uid gid hwcap ar ae
  = flat_map word_le8 (auxv_words la ph entry uid gid hwcap ar ae).
Proof. intros. unfold auxv_bytes, auxv_words. apply build_auxv_words. Qed.

Lemma length_auxv_words : forall la ph entry uid gid hwcap ar ae,
  length (auxv_words la ph entry uid gid hwcap ar ae)
  = (2 * auxv_count (la_rseq la))%nat.
Proof.
  intros [ehdr c msz [|]] ph entry uid gid hwcap ar ae; reflexivity.
Qed.

Section Layout.

  Variable segs : list Segment.
  Variable v : VaSize.
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable ph : PhdrInfo.
  Variable entry : word.
  Variable sp brk : word.
  (* the entry draw: ed_random = the AT_RANDOM bytes, ed_top = the stack VMA's end *)
  Variable rdraw : EntryDraw.

  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp brk mbase rdraw) inp.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

  (* the mapped image: Linux's whole block, from sp to the stack VMA's end *)
  Let bsb := entry_stack_image inp mbase ph entry sp rdraw.
  Let stk := stack_to_mem sp (entry_stack_image inp mbase ph entry sp rdraw).

  Lemma lay_bsb_nw : (bv_unsigned sp + Z.of_nat (length bsb) < 2^64)%Z.
  Proof.
    unfold bsb.
    exact (bsb_nw v inp mbase ph entry sp brk rdraw Hvl Hlau Hsp_hi).
  Qed.

  Lemma lay_len_av : (1 <= length (in_argv inp) <= 1024)%nat.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma lay_len_ev : (length (in_envp inp) <= 256)%nat.
  Proof. destruct Hve as [H1 _]. lia. Qed.

  (* [comment removed for export] *)
  Lemma bsb_decomp : exists head_tail,
    bsb = (word_le8 (len_word (in_argv inp))
           ++ flat_map word_le8
                (fst (string_addrs
                        (cat_string_base (ed_top rdraw) (in_argv inp) (in_envp inp)
                           (in_execfn inp)) (in_argv inp))))
          ++ word_le8 (Z_to_bv 64 0)
          ++ flat_map word_le8
               (fst (string_addrs
                       (cat_env_base (ed_top rdraw) (in_argv inp) (in_envp inp)
                          (in_execfn inp)) (in_envp inp)))
          ++ word_le8 (Z_to_bv 64 0)
          ++ auxv_bytes (launch_auxv inp sp mbase) ph entry
               (in_uid inp) (in_gid inp) (in_hwcap inp)
               (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
               (at_execfn_ptr (ed_top rdraw) (in_execfn inp))
          ++ head_tail.
  Proof.
    unfold bsb, entry_stack_image, build_stack_bytes, cat_env_base, cat_string_base.
    cbv zeta.
    rewrite (string_addrs_pair (in_argv inp)). cbv beta iota.
    rewrite (string_addrs_pair (in_envp inp)). cbv beta iota.
    eexists. rewrite <- !app_assoc. reflexivity.
  Qed.

  Lemma len_argc_argv :
    length (word_le8 (len_word (in_argv inp))
            ++ flat_map word_le8
                 (fst (string_addrs
                         (cat_string_base (ed_top rdraw) (in_argv inp) (in_envp inp)
                            (in_execfn inp)) (in_argv inp))))
    = (8 + 8 * length (in_argv inp))%nat.
  Proof.
    rewrite length_app, length_n_to_le_8, length_flat_map_le8,
      length_string_addrs_fst. lia.
  Qed.

  Lemma len_envp_ptrs :
    length (flat_map word_le8
              (fst (string_addrs
                      (cat_env_base (ed_top rdraw) (in_argv inp) (in_envp inp)
                         (in_execfn inp)) (in_envp inp))))
    = (8 * length (in_envp inp))%nat.
  Proof. rewrite length_flat_map_le8, length_string_addrs_fst. lia. Qed.

  (* [comment removed for export] *)
  Lemma read_argv_null :
    rdn segs stk (sp + nat_to_word (8 + 8 * length (in_argv inp))) 8%nat
    = Some (word_le8 (Z_to_bv 64 0)).
  Proof.
    destruct bsb_decomp as [tl E].
    pose proof (read_at_offset_image segs inp mbase ph entry sp rdraw
                  _ (word_le8 (Z_to_bv 64 0)) _ 8%nat E
                  (length_n_to_le_8 _) lay_bsb_nw) as H.
    rewrite len_argc_argv in H. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma read_envp_ptr_k : forall k, (k < length (in_envp inp))%nat ->
    rdn segs stk (sp + nat_to_word (envp_off (in_argv inp) + 8 * k)) 8%nat
    = Some (word_le8 (cat_envp_ptr (ed_top rdraw) (in_argv inp) (in_envp inp)
                        (in_execfn inp) k)).
  Proof.
    intros k Hk.
    destruct bsb_decomp as [tl E].
    assert (Hk' : (k < length (fst (string_addrs
                     (cat_env_base (ed_top rdraw) (in_argv inp) (in_envp inp)
                        (in_execfn inp)) (in_envp inp))))%nat)
      by (rewrite length_string_addrs_fst; exact Hk).
    rewrite (flat_map_le8_decomp _ k Hk') in E.
    rewrite <- !app_assoc in E.
    match type of E with
    | bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?p4 ++ ?mid ++ ?rest =>
        pose proof (read_at_offset_image segs inp mbase ph entry sp rdraw
                      (p1 ++ p2 ++ p3 ++ p4) mid rest 8%nat) as H
    end.
    rewrite <- !app_assoc in H.
    specialize (H E (length_n_to_le_8 _) lay_bsb_nw).
    rewrite !length_app in H.
    rewrite !length_flat_map_le8 in H.
    rewrite length_string_addrs_fst in H.
    rewrite firstn_length_le in H by (rewrite length_string_addrs_fst; lia).
    rewrite !length_n_to_le_8 in H.
    unfold envp_off, cat_envp_ptr.
    replace (8 + 8 * (length (in_argv inp) + 1) + 8 * k)%nat
      with (8 + (8 * length (in_argv inp) + (8 + 8 * k)))%nat by lia.
    exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma read_envp_null :
    rdn segs stk
      (sp + nat_to_word (envp_off (in_argv inp) + 8 * length (in_envp inp))) 8%nat
    = Some (word_le8 (Z_to_bv 64 0)).
  Proof.
    destruct bsb_decomp as [tl E].
    match type of E with
    | bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?mid ++ ?rest =>
        pose proof (read_at_offset_image segs inp mbase ph entry sp rdraw
                      (p1 ++ p2 ++ p3) mid rest 8%nat) as H
    end.
    rewrite <- !app_assoc in H.
    specialize (H E (length_n_to_le_8 _) lay_bsb_nw).
    rewrite !length_app in H. rewrite len_envp_ptrs in H.
    rewrite !length_n_to_le_8 in H.
    rewrite length_flat_map_le8, length_string_addrs_fst in H.
    unfold envp_off.
    match type of H with
    | rdn _ _ (sp + nat_to_word ?n) 8 = _ =>
        replace (8 + 8 * (length (in_argv inp) + 1)
                 + 8 * length (in_envp inp))%nat with n by lia
    end.
    exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma read_auxv_all :
    rdn segs stk (sp + nat_to_word (auxv_off (in_argv inp) (in_envp inp)))
        (auxv_size (kb_rseq (in_kernel inp)))
    = Some (auxv_bytes (launch_auxv inp sp mbase) ph entry
              (in_uid inp) (in_gid inp) (in_hwcap inp)
              (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
              (at_execfn_ptr (ed_top rdraw) (in_execfn inp))).
  Proof.
    destruct bsb_decomp as [tl E].
    match type of E with
    | bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?p4 ++ ?mid ++ ?rest =>
        pose proof (read_at_offset_image segs inp mbase ph entry sp rdraw
                      (p1 ++ p2 ++ p3 ++ p4) mid rest
                      (auxv_size (kb_rseq (in_kernel inp)))) as H
    end.
    rewrite <- !app_assoc in H.
    specialize (H E (length_auxv_bytes _ _ _ _ _ _ _ _) lay_bsb_nw).
    rewrite !length_app in H. rewrite len_envp_ptrs in H.
    rewrite !length_n_to_le_8 in H.
    rewrite length_flat_map_le8, length_string_addrs_fst in H.
    unfold auxv_off.
    match type of H with
    | rdn _ _ (sp + nat_to_word ?n) _ = _ =>
        replace (8 + 8 * (length (in_argv inp) + 1)
                 + 8 * (length (in_envp inp) + 1))%nat with n by lia
    end.
    exact H.
  Qed.

  Lemma lay_rseq : la_rseq (launch_auxv inp sp mbase) = kb_rseq (in_kernel inp).
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma read_auxv_word : forall j,
    (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
    rdn segs stk
      (sp + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j)) 8%nat
    = Some (word_le8
              (nth j (auxv_words (launch_auxv inp sp mbase) ph entry
                        (in_uid inp) (in_gid inp) (in_hwcap inp)
                        (at_random_ptr sp (kb_rseq (in_kernel inp))
                           (in_argv inp) (in_envp inp))
                        (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                   (Z_to_bv 64 0))).
  Proof.
    intros j Hj.
    rewrite <- nat_to_word_add_merge.
    rewrite (rdn_skipn segs stk (auxv_size (kb_rseq (in_kernel inp)))
               _ _ (8 * j) 8 read_auxv_all)
      by (unfold auxv_size, auxv_count in *;
          destruct (kb_rseq (in_kernel inp)); lia).
    f_equal. rewrite auxv_bytes_words.
    rewrite (flat_map_le8_decomp _ j)
      by (rewrite length_auxv_words, lay_rseq; exact Hj).
    rewrite skipn_app_exact
      by (rewrite length_flat_map_le8, firstn_length_le
            by (rewrite length_auxv_words, lay_rseq; lia); lia).
    apply firstn_app_exact. apply length_n_to_le_8.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bsb_random_split : exists pre post,
    bsb = pre ++ at_random_bytes (ed_random rdraw) ++ post
    /\ length pre = (block_head_size (kb_rseq (in_kernel inp))
                       (in_argv inp) (in_envp inp) - 16)%nat.
  Proof.
    unfold bsb, entry_stack_image.
    eexists. eexists. split; [apply build_stack_bytes_split_random|].
    unfold block_below_random. cbv zeta.
    rewrite (string_addrs_pair (in_argv inp)). cbv beta iota.
    rewrite (string_addrs_pair (in_envp inp)). cbv beta iota.
    rewrite !length_app, !repeat_length, !length_flat_map_le8,
      !length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes.
    cbn [launch_auxv la_rseq].
    unfold block_head_size, block_items. lia.
  Qed.

  Lemma at_random_off : exists off : nat,
    at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)
    = sp + nat_to_word off
    /\ off = (block_head_size (kb_rseq (in_kernel inp))
                (in_argv inp) (in_envp inp) - 16)%nat
    /\ (Z.of_nat off mod 8 = 0)%Z
    /\ forall j n, (j + n <= 16)%nat ->
         rdn segs stk
           (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)
            + nat_to_word j) n
         = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))).
  Proof.
    destruct bsb_random_split as [pre [post [E Hlen]]].
    unfold bsb in E.
    exists (block_head_size (kb_rseq (in_kernel inp))
              (in_argv inp) (in_envp inp) - 16)%nat.
    split; [reflexivity|]. split; [reflexivity|]. split.
    { unfold block_head_size, block_items, auxv_size, auxv_count.
      pose proof (Nat.mod_upper_bound
                    (length (in_argv inp) + length (in_envp inp) + 3) 2 ltac:(lia)).
      destruct (kb_rseq (in_kernel inp));
        [ replace (8 * (length (in_argv inp) + length (in_envp inp) + 3)
                   + 16 * 29
                   + 8 * ((length (in_argv inp) + length (in_envp inp) + 3) mod 2)
                   + 16 - 16)%nat
            with (8 * ((length (in_argv inp) + length (in_envp inp) + 3)
                       + 58
                       + ((length (in_argv inp) + length (in_envp inp) + 3) mod 2)))%nat
            by lia
        | replace (8 * (length (in_argv inp) + length (in_envp inp) + 3)
                   + 16 * 27
                   + 8 * ((length (in_argv inp) + length (in_envp inp) + 3) mod 2)
                   + 16 - 16)%nat
            with (8 * ((length (in_argv inp) + length (in_envp inp) + 3)
                       + 54
                       + ((length (in_argv inp) + length (in_envp inp) + 3) mod 2)))%nat
            by lia ];
        rewrite Nat2Z.inj_mul; change (Z.of_nat 8) with 8%Z;
        rewrite Z.mul_comm, Z_mod_mult; reflexivity. }
    intros j n Hjn.
    unfold at_random_ptr. rewrite <- Hlen, nat_to_word_add_merge.
    rewrite <- (firstn_skipn j (at_random_bytes (ed_random rdraw))) in E.
    rewrite <- (firstn_skipn n (skipn j (at_random_bytes (ed_random rdraw)))) in E.
    pose proof (read_at_offset_image segs inp mbase ph entry sp rdraw
                  (pre ++ firstn j (at_random_bytes (ed_random rdraw)))
                  (firstn n (skipn j (at_random_bytes (ed_random rdraw))))
                  (skipn n (skipn j (at_random_bytes (ed_random rdraw))) ++ post)
                  n) as H.
    assert (Hl : length (pre ++ firstn j (at_random_bytes (ed_random rdraw)))
                 = (length pre + j)%nat).
    { rewrite length_app, firstn_length_le; [reflexivity|].
      rewrite length_at_random_bytes. lia. }
    rewrite Hl in H.
    apply H;
      [ rewrite E; rewrite <- !app_assoc; reflexivity
      | rewrite firstn_length_le; [reflexivity|];
        rewrite length_skipn, length_at_random_bytes; lia
      | exact lay_bsb_nw ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma lay_bsb_len : (Z.of_nat (length bsb) <= 2101782)%Z.
  Proof.
    unfold bsb. exact (bsb_bound v inp mbase ph entry sp brk rdraw Hvl Hlau).
  Qed.

  Lemma lay_head_bound :
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)
     <= length bsb)%nat.
  Proof.
    unfold bsb, entry_stack_image. rewrite length_build_stack_bytes.
    cbn [launch_auxv la_rseq]. lia.
  Qed.

  Lemma auxv_off_bound :
    (auxv_off (in_argv inp) (in_envp inp)
     + auxv_size (kb_rseq (in_kernel inp)) + 16 <= length bsb)%nat.
  Proof.
    pose proof lay_head_bound.
    unfold auxv_off, block_head_size, block_items in *. lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma cat_envp_ptr_eq : forall k, (k < length (in_envp inp))%nat ->
    cat_envp_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k
    = sp + nat_to_word (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top rdraw)
                          (in_argv inp) (in_envp inp) (in_execfn inp)
                        + total_arg_bytes_nat (in_argv inp)
                        + total_arg_bytes_nat (firstn k (in_envp inp))).
  Proof.
    intros k Hk. unfold cat_envp_ptr. rewrite nth_string_addrs by exact Hk.
    unfold cat_env_base.
    rewrite (cat_string_base_offset v inp mbase sp brk rdraw Hlau).
    rewrite !nat_to_word_add_merge. f_equal. f_equal. lia.
  Qed.

  Lemma total_firstn_ev_bound : forall k,
    (Z.of_nat (total_arg_bytes_nat (firstn k (in_envp inp))) <= 131072)%Z.
  Proof.
    intros k. destruct Hve as [_ [Htot _]]. rewrite total_arg_bytes_Z in Htot.
    pose proof (total_arg_bytes_firstn_le k (in_envp inp)). lia.
  Qed.

  Lemma struct_av_bound :
    (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top rdraw)
       (in_argv inp) (in_envp inp) (in_execfn inp)
     + total_arg_bytes_nat (in_argv inp)
     + total_arg_bytes_nat (in_envp inp)
     <= length bsb)%nat.
  Proof.
    unfold bsb, entry_stack_image. rewrite length_build_stack_bytes.
    unfold cat_string_off, launch_string_bytes.
    cbn [launch_auxv la_rseq]. rewrite !length_flatten_strings. lia.
  Qed.

  Lemma u_cat_envp_ptr : forall k, (k < length (in_envp inp))%nat ->
    bv_unsigned (cat_envp_ptr (ed_top rdraw) (in_argv inp) (in_envp inp)
                   (in_execfn inp) k)
    = (bv_unsigned sp
       + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top rdraw)
                     (in_argv inp) (in_envp inp) (in_execfn inp)
                   + total_arg_bytes_nat (in_argv inp)
                   + total_arg_bytes_nat (firstn k (in_envp inp))))%Z.
  Proof.
    intros k Hk. rewrite cat_envp_ptr_eq by exact Hk. rewrite word_add_nat.
    pose proof struct_av_bound. pose proof lay_bsb_nw.
    pose proof (total_arg_bytes_firstn_le k (in_envp inp)).
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    apply u_Z2bv; lia.
  Qed.

  Lemma cat_envp_ptr_nz : forall k, (k < length (in_envp inp))%nat ->
    bv_unsigned (cat_envp_ptr (ed_top rdraw) (in_argv inp) (in_envp inp)
                   (in_execfn inp) k) <> 0%Z.
  Proof.
    intros k Hk. rewrite u_cat_envp_ptr by exact Hk.
    unfold sp_window_lo in Hsp_lo. lia.
  Qed.

  Lemma u_cat_argv_ptr : forall k, (k < length (in_argv inp))%nat ->
    bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp)
                   (in_execfn inp) k)
    = (bv_unsigned sp
       + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top rdraw)
                     (in_argv inp) (in_envp inp) (in_execfn inp)
                   + total_arg_bytes_nat (firstn k (in_argv inp))))%Z.
  Proof.
    intros k Hk.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp)
               (in_execfn inp) k Hk),
            (cat_string_base_offset v inp mbase sp brk rdraw Hlau).
    rewrite nat_to_word_add_merge, word_add_nat.
    pose proof struct_av_bound. pose proof lay_bsb_nw.
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)).
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    apply u_Z2bv; lia.
  Qed.

  Lemma argv_str_len : forall k, (k < length (in_argv inp))%nat ->
    (Z.of_nat (length (nth k (in_argv inp) [])) <= 131071)%Z.
  Proof. intros k Hk. exact (valid_argv_str_len (in_argv inp) k Hva Hk). Qed.

  (* [comment removed for export] *)
  Lemma auxv_words_eq : forall ar ae,
    auxv_words (launch_auxv inp sp mbase) ph entry
      (in_uid inp) (in_gid inp) (in_hwcap inp) ar ae
    = flat_map (fun e => [fst e; snd e])
        (auxv_entries (launch_auxv inp sp mbase) ph entry
           (in_uid inp) (in_gid inp) (in_hwcap inp) ar ae).
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma rnd_facts : forall (Hal : (bv_unsigned sp mod 16 = 0)%Z),
    (bv_unsigned sp
     <= bv_unsigned (at_random_ptr sp (kb_rseq (in_kernel inp))
                       (in_argv inp) (in_envp inp)))%Z
    /\ (bv_unsigned (at_random_ptr sp (kb_rseq (in_kernel inp))
                       (in_argv inp) (in_envp inp)) + 16
        <= bv_unsigned sp + Z.of_nat (length bsb))%Z
    /\ (bv_unsigned sp + Z.of_nat (length bsb) < 2^64)%Z
    /\ (bv_unsigned (at_random_ptr sp (kb_rseq (in_kernel inp))
                       (in_argv inp) (in_envp inp)) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn segs stk
            (Z_to_bv 64 (bv_unsigned (at_random_ptr sp (kb_rseq (in_kernel inp))
                                        (in_argv inp) (in_envp inp))
                         + Z.of_nat j)) n
          = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw))))).
  Proof.
    intros Hal.
    destruct at_random_off as [off [Hp [Hoff [Hmod Hrd]]]].
    pose proof lay_bsb_nw as Hnw. pose proof lay_bsb_len as Hbl.
    pose proof lay_head_bound as Hhead.
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    assert (Hoff16 : (off + 16
                      <= block_head_size (kb_rseq (in_kernel inp))
                           (in_argv inp) (in_envp inp))%nat).
    { rewrite Hoff. unfold block_head_size. lia. }
    assert (Hu : bv_unsigned (at_random_ptr sp (kb_rseq (in_kernel inp))
                                (in_argv inp) (in_envp inp))
                 = (bv_unsigned sp + Z.of_nat off)%Z).
    { rewrite Hp, word_add_nat. apply u_Z2bv; lia. }
    rewrite Hu. split; [lia|]. split; [lia|]. split; [lia|]. split.
    - rewrite Z.add_mod by lia.
      replace (bv_unsigned sp mod 8)%Z with 0%Z.
      2:{ symmetry.
          rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity).
          rewrite Hal. reflexivity. }
      rewrite Hmod. reflexivity.
    - intros j n Hjn. rewrite <- Hu. rewrite <- word_add_nat. apply Hrd. exact Hjn.
  Qed.

End Layout.

End RefLayout.
From Stdlib Require ZArith NArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
Module FrmFastScan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module FRMF.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma expand_c_safe (c : cinstr) : FrmKeep.FRM.instr_frm_safe (expand_c c) = true.
Proof. destruct c; reflexivity. Qed.

(* [comment removed for export] *)
Ltac dcrush1 :=
  match goal with
  | H : ?o <> ?o |- _ => exfalso; exact (H eq_refl)
  | |- ?l = ?l => reflexivity
  | |- context [match ?x with _ => _ end] =>
      lazymatch x with context [match _ with _ => _ end] => fail | _ => idtac end;
      first [ is_var x; destruct x | destruct x ]; cbv beta iota
  end.
Ltac dcrush := repeat dcrush1.

(* [comment removed for export] *)
Lemma decode_safe (w : bv 32) :
  bv_unsigned (bits 0 7 w) <> 115 ->
  match decode w with Some i => FrmKeep.FRM.instr_frm_safe i | None => true end = true.
Proof.
  intros NE. cbv beta zeta delta [decode].
  remember (bv_unsigned (bits 0 7 w)) as o eqn:Ho. clear Ho.
  dcrush; reflexivity.
Qed.

Lemma low7_bits (w : bv 32) : bv_unsigned (bits 0 7 w) = bv_unsigned w mod 128.
Proof. unfold bits. rewrite bv_extract_unsigned, Z.shiftr_0_r. reflexivity. Qed.

Theorem safe_unless_system (w : bv 32) : bv_unsigned w mod 128 <> 115 -> FrmKeep.FRM.word_frm_safe w = true.
Proof.
  intros NE. unfold FrmKeep.FRM.word_frm_safe, decode_any.
  destruct (decide _) as [E3|N3].
  - pose proof (decode_safe w ltac:(rewrite low7_bits; exact NE)) as D.
    destruct (decode w) as [i|]; [exact D| reflexivity].
  - destruct (decode16 _) as [c|]; [apply expand_c_safe| reflexivity].
Qed.
Corollary safe_unless_systemC (w : bv 32) : bv_unsigned w mod 128 <> 115 -> FrmKeepC.FRMC.word_frm_safe w = true.
Proof. intros NE. apply FrmKeepC.FRMC.safe_of_coarse, safe_unless_system, NE. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma low7_concat (X : bv 16) (b1 b0 : bv 8) :
  bv_unsigned (bv_concat 32 X (bv_concat 16 b1 b0)) mod 128 = bv_unsigned b0 mod 128.
Proof.
  rewrite !bv_concat_unsigned'. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 16) with (2 ^ 16).
  change 128 with (2 ^ 7).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_le_dec n 7) as [LT|GE].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (n - Z.of_N 16)) by (cbn; lia). cbn [orb].
    rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (n - Z.of_N 8)) by (cbn; lia). reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma low7_le4 b3 b2 b1 b0 : bv_unsigned (le4 b3 b2 b1 b0) mod 128 = bv_unsigned b0 mod 128.
Proof. unfold le4, le2. apply low7_concat. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Fast.
Variable wsafe : bv 32 -> bool.
Hypothesis wsafe_sys : forall w, bv_unsigned w mod 128 <> 115 -> wsafe w = true.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition okP (a : Z) : bool :=
  (match fetch_word segs (Z_to_bv 64 a) with Some w => wsafe w | None => true end)
  && (match fetch_tail segs (Z_to_bv 64 a) with Some w => wsafe w | None => true end).
(* [comment removed for export] *)
Definition fposB (base : Z) (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with
  | Some b => if bv_unsigned b mod 128 =? 115 then okP (base + Z.of_N off) else true
  | None => true
  end.
(* [comment removed for export] *)
Definition fpos (base : Z) (s : PrimString.string) (off : N) : bool :=
  match hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off)))) with
  | 7%N | 15%N => fposB base s off
  | _ => true
  end.
Fixpoint fscan1 (base : Z) (s : PrimString.string) (f : nat) (off : N) : bool :=
  match f with O => true | S f' => fpos base s off && fscan1 base s f' (off + 2)%N end.
Fixpoint fscan2 (base : Z) (s : PrimString.string) (g f : nat) (off : N) : bool :=
  match g with O => true | S g' => fscan1 base s f off && fscan2 base s g' f (off + 2 * N.of_nat f)%N end.
(* [comment removed for export] *)
Definition fseg (g f : nat) (seg : Segment) : bool :=
  if seg_executable seg then
    match seg_bytes seg with
    | [chunk] => if (Z.of_N (seg_size seg) <=? 2 * Z.of_nat f * Z.of_nat g) && (Z.of_N (seg_base seg) mod 2 =? 0)
                 then fscan2 (Z.of_N (seg_base seg)) chunk g f 0 else false
    | _ => false
    end
  else true.

Lemma fscan1_sound base s : forall f o0, fscan1 base s f o0 = true ->
  forall o, (o0 <= o < o0 + 2 * N.of_nat f)%N -> (exists k, o = o0 + 2 * k)%N -> fpos base s o = true.
Proof.
  induction f as [|f IH]; intros o0 H o Ho [k Hk]; [cbn [N.of_nat] in Ho; lia|].
  cbn [fscan1] in H. apply andb_true_iff in H as [H0 H1].
  destruct (N.eq_dec o o0) as [->|NE]; [exact H0|].
  apply (IH (o0 + 2)%N H1); [lia|]. exists (k - 1)%N. lia.
Qed.
Lemma fscan2_sound base s : forall g f o0, fscan2 base s g f o0 = true ->
  forall o, (o0 <= o < o0 + 2 * N.of_nat f * N.of_nat g)%N -> (exists k, o = o0 + 2 * k)%N -> fpos base s o = true.
Proof.
  induction g as [|g IH]; intros f o0 H o Ho [k Hk]; [cbn [N.of_nat] in Ho; lia|].
  cbn [fscan2] in H. apply andb_true_iff in H as [H0 H1].
  destruct (N.ltb_spec o (o0 + 2 * N.of_nat f)) as [LT|GE].
  - apply (fscan1_sound base s f o0 H0 o ltac:(lia)). exists k; exact Hk.
  - apply (IH f (o0 + 2 * N.of_nat f)%N H1); [lia|]. exists (k - N.of_nat f)%N. lia.
Qed.

(* [comment removed for export] *)
Lemma hex_byte_sys_hi s off b : hex_byte_at s off = Some b -> bv_unsigned b mod 128 = 115 ->
  hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off)))) = 7%N \/ hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off)))) = 15%N.
Proof.
  unfold hex_byte_at. cbv zeta.
  set (h := hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off))))).
  set (l := hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off + 1))))).
  destruct (_ || _)%bool; [|discriminate].
  destruct (N.ltb_spec h 16) as [Hh|]; cbn [andb]; [|discriminate].
  destruct (N.ltb_spec l 16) as [Hl|]; [|discriminate].
  intros E. injection E as <-. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite (Z.mod_small _ 256) by lia. intros M.
  pose proof (Z_div_mod_eq_full (Z.of_N (h * 16 + l)) 128) as D. rewrite M in D.
  assert (Q : Z.of_N (h * 16 + l) / 128 = 0 \/ Z.of_N (h * 16 + l) / 128 = 1).
  { assert (0 <= Z.of_N (h * 16 + l) / 128 < 2); [|lia]. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma code_read_first a n b0 rest : code_read segs a n = Some (b0 :: rest) ->
  exists seg, In seg segs /\ seg_executable seg = true
    /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + Z.of_N n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg)
    /\ segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) = Some b0.
Proof.
  unfold code_read. destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:E; [|discriminate].
  destruct (seg_executable seg) eqn:X; cbn [andb]; [|discriminate].
  destruct (negb (seg_writable seg)); [|discriminate].
  intros R. exists seg. split; [exact (FrmKeep.FRM.find_segment_In _ _ _ _ E)|]. split; [exact X|].
  destruct (FrmKeep.FRM.find_segment_range _ _ _ _ E) as [R1 R2]. split; [exact R1|]. split; [exact R2|].
  destruct (N.to_nat n) as [|n']; cbn [segment_read_bytes] in R; [discriminate|].
  destruct (segment_byte_at (seg_bytes seg) _) as [b|]; [|discriminate].
  destruct (segment_read_bytes _ _ n') as [r|]; [|discriminate]. injection R as -> _. reflexivity.
Qed.

(* [comment removed for export] *)
Definition fetched_at (a : word) (w : bv 32) : Prop :=
  bv_unsigned a mod 2 = 0 /\ exists seg b0, In seg segs /\ seg_executable seg = true
    /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + 2 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg)
    /\ segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) = Some b0
    /\ bv_unsigned w mod 128 = bv_unsigned b0 mod 128.
Lemma fetch_word_at a w : fetch_word segs a = Some w -> fetched_at a w.
Proof.
  unfold fetch_word. destruct (Z.eqb_spec (bv_unsigned a mod 2) 0) as [E|NE]; cbn [negb]; [|discriminate].
  destruct (code_read segs a 4) as [[|b0 [|b1 [|b2 [|b3 [|? ?]]]]]|] eqn:C; try discriminate. intros H. injection H as <-.
  split; [exact E|]. destruct (code_read_first a 4 b0 _ C) as (seg & IN & X & R1 & R2 & SB).
  exists seg, b0. split; [exact IN|]. split; [exact X|]. split; [exact R1|]. split; [change (Z.of_N 4) with 4 in R2; lia|]. split; [exact SB|]. apply low7_le4.
Qed.
Lemma fetch_tail_at a w : fetch_tail segs a = Some w -> fetched_at a w.
Proof.
  unfold fetch_tail. destruct (Z.eqb_spec (bv_unsigned a mod 2) 0) as [E|NE]; cbn [negb]; [|discriminate].
  unfold fetch_half at 1.
  destruct (code_read segs a 2) as [[|b0 [|b1 [|? ?]]]|] eqn:C; try discriminate. intros H.
  split; [exact E|]. destruct (code_read_first a 2 b0 _ C) as (seg & IN & X & R1 & R2 & SB).
  exists seg, b0. split; [exact IN|]. split; [exact X|]. split; [exact R1|]. split; [exact R2|]. split; [exact SB|].
  destruct (_ =? 3); [destruct (fetch_half segs (a + 2)) as [h1|]; [|discriminate]|]; injection H as <-; unfold le2; apply low7_concat.
Qed.

(* [comment removed for export] *)
Theorem fetch_safe_of_fscan (g f : nat) :
  forallb (fseg g f) segs = true ->
  forall a w, fetch_word segs a = Some w \/ fetch_tail segs a = Some w -> wsafe w = true.
Proof.
  intros SC a w H.
  destruct (Z.eq_dec (bv_unsigned w mod 128) 115) as [SYS|NSYS]; [|exact (wsafe_sys w NSYS)].
  assert (FA : fetched_at a w) by (destruct H as [H|H]; [exact (fetch_word_at a w H)| exact (fetch_tail_at a w H)]).
  destruct FA as (EA & seg & b0 & IN & X & R1 & R2 & SB & LB).
  pose proof (proj1 (forallb_forall _ _) SC seg IN) as FS. unfold fseg in FS. rewrite X in FS.
  destruct (seg_bytes seg) as [|chunk [|? ?]]; try discriminate.
  destruct (_ && _) eqn:FS0 in FS; [|discriminate]. rename FS into F2. apply andb_true_iff in FS0 as [COV EB].
  apply Z.leb_le in COV. apply Z.eqb_eq in EB.
  set (base := Z.of_N (seg_base seg)) in *. set (off := Z.to_N (bv_unsigned a - base)) in *.
  assert (HB : hex_byte_at chunk off = Some b0).
  { cbn [segment_byte_at] in SB. destruct (_ <? _)%N; [exact SB| discriminate]. }
  assert (EO : Z.of_N off = bv_unsigned a - base) by (unfold off; lia).
  assert (FP : fpos base chunk off = true).
  { apply (fscan2_sound base chunk g f 0%N F2); [lia|].
    exists (Z.to_N ((bv_unsigned a - base) / 2)).
    assert (M : (bv_unsigned a - base) mod 2 = 0) by (rewrite Zminus_mod, EA, EB; reflexivity).
    pose proof (Z_div_mod_eq_full (bv_unsigned a - base) 2) as D. lia. }
  assert (FPB : fposB base chunk off = true).
  { unfold fpos in FP. destruct (hex_byte_sys_hi chunk off b0 HB ltac:(rewrite <- LB; exact SYS)) as [HN|HN]; rewrite HN in FP; exact FP. }
  unfold fposB in FPB. rewrite HB in FPB. rewrite <- LB, SYS in FPB. cbn [Z.eqb Pos.eqb] in FPB. rename FPB into FP'.
  clear FP. rename FP' into FP.
  replace (base + Z.of_N off) with (bv_unsigned a) in FP by lia.
  unfold okP in FP. rewrite Z_to_bv_bv_unsigned in FP. apply andb_true_iff in FP as [O1 O2].
  destruct H as [H|H]; [rewrite H in O1; exact O1| rewrite H in O2; exact O2].
Qed.
End Fast.

(* [comment removed for export] *)
Definition fetch_safe_of_fscan_FRM (segs : list Segment) (g f : nat) :=
  fetch_safe_of_fscan FrmKeep.FRM.word_frm_safe safe_unless_system segs g f.
Definition fetch_safe_of_fscan_FRMC (segs : list Segment) (g f : nat) :=
  fetch_safe_of_fscan FrmKeepC.FRMC.word_frm_safe safe_unless_systemC segs g f.
End FRMF.

End FrmFastScan.
Module FrmKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FPSteps.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module FRMK.

Definition frm_ok (fx : FPState) : Prop := frm_zero (@fp_csr fx).

Lemma frm_ok_fx0 : frm_ok fx0.
Proof. exact fp_frm_zero_fx0. Qed.

Lemma frm_ok_unfold fx : frm_ok fx = frm_zero (@fp_csr fx).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma frm_ok_mkFP_same fr (fx : FPState) : frm_ok fx -> frm_ok (mkFP fr (@fp_csr fx)).
Proof. intros H. exact H. Qed.
Lemma frm_ok_mkFP fr cs : frm_zero cs -> frm_ok (mkFP fr cs).
Proof. intros H. exact H. Qed.

(* [comment removed for export] *)
Lemma frm_ok_of_eq (fx fx' : FPState) :
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 -> frm_ok fx -> frm_ok fx'.
Proof. intros E H. unfold frm_ok, frm_zero in *. rewrite E. exact H. Qed.

(* [comment removed for export] *)
Definition msteps_keep_ty (segs : list Segment) : Prop :=
  forall (fx fx' : FPState) R R' pc pc' M M',
    msteps segs (@mkst fx R pc M (seg_rom segs)) (@mkst fx' R' pc' M' (seg_rom segs)) -> frm_zero (@fp_csr fx) -> frm_zero (@fp_csr fx').

(* [comment removed for export] *)
Ltac frm_solve_with L :=
  lazymatch goal with
  | |- frm_ok ?fx => change (frm_zero (@fp_csr fx)); frm_solve_with L
  | |- frm_zero (@fp_csr ?fx) =>
      first [ assumption
            | exact fp_frm_zero_fx0
            | lazymatch fx with
              | mkFP _ (@fp_csr ?f1) => change (frm_zero (@fp_csr f1)); frm_solve_with L
              | mkFP _ ?cs => cbn [fp_csr]; frm_solve_with L
              end
            | match goal with
              | MS : msteps _ (@mkst ?f0 _ _ _ _) (@mkst fx _ _ _ _) |- _ =>
                  lazymatch f0 with fx => fail | _ => idtac end;
                  apply (L _ _ _ _ _ _ _ _ MS); frm_solve_with L
              | E : Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = Z.land (Z.shiftr (bv_unsigned (@fp_csr ?f0)) 5) 7 |- _ =>
                  lazymatch f0 with fx => fail | _ => idtac end;
                  apply (frm_ok_of_eq f0 fx E); change (frm_zero (@fp_csr f0)); frm_solve_with L
              | E : _ /\ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = Z.land (Z.shiftr (bv_unsigned (@fp_csr ?f0)) 5) 7 |- _ =>
                  lazymatch f0 with fx => fail | _ => idtac end;
                  apply (frm_ok_of_eq f0 fx (proj2 E)); change (frm_zero (@fp_csr f0)); frm_solve_with L
              | H : frm_ok fx |- _ => exact H
              end
            | fail 1 "frm_solve: no frm fact for" fx ]
  | |- frm_zero ?cs => first [ assumption | fail 1 "frm_solve: no frm fact for csr" cs ]
  | |- _ => fail "frm_solve: goal is not an frm obligation"
  end.

End FRMK.

End FrmKit.
