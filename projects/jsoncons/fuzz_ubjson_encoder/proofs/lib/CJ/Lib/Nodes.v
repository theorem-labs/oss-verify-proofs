(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Export RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Nodes () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4aregC13~~~K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<ms_read_byteC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@ms_writable_byteC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memK47Corelib4Init9Datatypes6option01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3mrdC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Peano2ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C46Stdlib5Lists4List9nth_errorI47Corelib4Init5Logic3and00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes8bytes_inC13~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes@ms_read_byte_mrdC13~~~K47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib4Init3Nat3addC47Corelib4Init5Logic3iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List>nth_error_app1C46Stdlib9micromega;ZifyClasses5mkrelC47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C35stdpp7tactics<f_equal_helpI47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_app2C56Stdlib5Arith8PeanoNat3Nat9ltb_spec0C56Stdlib5Arith8PeanoNat3Nat3ltbI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic3notC46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib5Lists4List:length_appC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula07C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes<bytes_in_appC13~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics?LinuxProcessSem5State>read_bytes_auxc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes=bytes_in_consC13~~~C45stdpp9bitvector;definitions6bv_addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7wa_succC13~~~C47Corelib4Init9Datatypes8list_indc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5NodesGread_bytes_aux_bytes_inC13~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeGreadable_bytes_aux_fullC56Stdlib6ZArith6BinInt1Z6to_natC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5NodesBword_to_nat_of_natC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>read_bytes_mapC4ELinuxProcessSemantics?LinuxProcessSem5StateAread_bytes_map_eqc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5NodesGread_bytes_map_bytes_inC13~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeCreadable_bytes_fullC46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem5State=read_cstr_auxK4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqK47Corelib4Init5Logic2or01C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or02I4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result02K4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result03C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes4prod00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes;iovec_bytesC13~~~C47Corelib4Init3Nat3mulC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~C47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le8C13~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3MemDle_bytes_to_word_le8C13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8read_u64C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MStateCZ_to_bv_bv_unsignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lit_add_litC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?read_iovecs_auxC46Stdlib5Lists4List9app_assocc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5NodesAread_u64_bytes_inC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes6wa_addC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes6iov_okC13~~~I46Stdlib5Lists4List7Forall200C4ELinuxProcessSemantics?LinuxProcessSem5State=gather_iovecsc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes>wa_unsigned_idC13~~~C46Stdlib5Lists4List;Forall2_indC46Stdlib5Lists4List6concatC4ELinuxProcessSemantics?LinuxProcessSem5State:iovs_totalC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4minvC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry03K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C47Corelib4Init5Logic5proj2I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Fork@PID_MAX_ENVELOPEC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem5State@m_tid_init_modelC4ELinuxProcessSemantics?LinuxProcessSem5State?m_fs_init_modelC4ELinuxProcessSemantics?LinuxProcessSem5State@m_fds_init_modelI4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00K47Corelib4Init9Datatypes:comparison02".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sysno_si : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h02msh14segsh22x8p;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000eR1p4p710p8P0P1p4p7210p8P0p1001Bp4p710p8p1001_p4p710p1002<p4p710R0p8p1002Zp4p710P0p8g0035j14Tg003Uj10Tg004:j12Tg004Xj11Tg005;j23Tg005U#4g006Tg007[#0#0#0#0#0#0#2#1R0f0,30W2W0W1o"). Qed.
(* [comment removed for export] *)
Definition areg (ms : machine_state) (r : bv 5) : word := reg_get (ms_regs ms) r.
Lemma in_a0_si : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = areg ms 10.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h02msh14segsh22x8p;1p;3p;2g0035j18Tg003Uj10Tg004:j11Tg004Xj12Tg008@j17Tg008ej16Tg009Cj34Tg009fj23Tg005;j25Tg005U#8g006Tg007[#0R0#0#0#0#0#0#1#2R1f1%70R0#1%00#6g00;234'3,51W2W0W1o"). Qed.
Lemma in_a1_si : forall segs ms x8, in_arg (sys_input segs ms x8) 1 = areg ms 11.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h02msh14segsh22x8p;1p;3p;2g0035j18Tg003Uj10Tg004:j11Tg004Xj13Tg008@j12Tg008ej17Tg009Cj36Tg009fj24Tg005;j25Tg005U#8g006Tg007[#0R0#0#0#0#0#0#1#3R1f1%20R0#1%20#7g00;236'4,51W2W0W1o"). Qed.
Lemma in_a2_si : forall segs ms x8, in_arg (sys_input segs ms x8) 2 = areg ms 12.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h02msh14segsh22x8p;1p;3p;2g0035j18Tg003Uj10Tg004:j11Tg004Xj13Tg008@j12Tg008ej17Tg009Cj36Tg009fj24Tg005;j25Tg005U#8g006Tg007[R0#0R1#0#0#0#0#0#1#3R2f1%21#1%20#0#0#7g00;236'4,52W2W0W1o"). Qed.
Lemma in_a3_si : forall segs ms x8, in_arg (sys_input segs ms x8) 3 = areg ms 13.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h02msh14segsh22x8p;1p;3p;2g0035j18Tg003Uj10Tg004:j12Tg004Xj13Tg008@j11Tg008ej17Tg009Cj36Tg009fj24Tg005;j25Tg005U#8g006Tg007[R0#0R1#0#0#0#0#0#2#3R2f1%11#2%10#0#1#7g00;236'4,52W2W0W1o"). Qed.
Lemma in_a4_si : forall segs ms x8, in_arg (sys_input segs ms x8) 4 = areg ms 14.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h02msh14segsh22x8p;1p;3p;2g0035j18Tg003Uj10Tg004:j12Tg004Xj13Tg008@j11Tg008ej17Tg009Cj36Tg009fj24Tg005;j25Tg005U#8g006Tg007[R0#0R1#0#0#0#0#0#2#3R2f1%11#2%10#1#0#7g00;236'4,52W2W0W1o"). Qed.
Lemma in_a5_si : forall segs ms x8, in_arg (sys_input segs ms x8) 5 = areg ms 15.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h02msh14segsh22x8p;1p;3p;2g0035j18Tg003Uj10Tg004:j12Tg004Xj13Tg008@j11Tg008ej17Tg009Cj36Tg009fj24Tg005;j25Tg005U#8g006Tg007[R0#0R1#0#0#0#0#0#2#3R2f1%11#2%10#1#1#7g00;236'4,52W2W0W1o"). Qed.
Lemma in_mem_si : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h02msh14segsh22x8p;1p;2g0035j16Tg003Uj10Tg004:j12Tg004Xj11Tg00;Nj15Tg00<0j14Tg005;j23Tg005U#6g006Tg007[#0#0#0R0#0#0#0#2#1R1%20#1#5\1f1#4'3W2W0W1o"). Qed.
Lemma in_wmem_si : forall segs ms x8, in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h02msh14segsh22x8p;1p;2g0035j16Tg003Uj10Tg004:j12Tg004Xj11Tg00;Nj15Tg00=4j24Tg005;j23Tg005U#6g006Tg007[#0#0#0R0#0#0#0#2#1R1%20#1#5\1f2f1'4'3W2W0W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bytes_in (mp : word -> option byte) (a : Z) (bs : list byte) : Prop :=
  0 <= a /\ a + Z.of_nat (length bs) <= 2^64 /\
  forall i, (i < length bs)%nat -> mp (wa (a + Z.of_nat i)) = nth_error bs i.

Lemma ms_read_byte_mrd : forall segs ms a,
  ms_rom ms = seg_rom segs -> ms_read_byte ms a = mrd segs (ms_mem ms) a.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "p'0h01Hh11ah22msh31oh44segsi001bi011xp;1p;3p;2p;6p100><p4p70R0p100>lp4p710p8P0g002<R0p4p710R1p8p100?Hp4p70R2p100@6p4p7210p8P2P1p8g0035j1?Tg003Uj10Tg004:j12Tg004Xj16Tg00;NR1j1>Tg00@Rj17Tg00APj14j25Tg00B[j31Tg00C5j23j1<Tg00D3j29Tg005;j28TP0j6:Tg00<0j2=Tg00DUj3;Tg005U#?g006Tg007[#0#0#0R0#0#0#0#2#6R2%20#6R0#>R3\2R2f1R4#7f2R5#431P2f3R6#4P1P0P31365R7f0R8,90R9P8P5O1n10110100021010000P1P0P3P7P9f4/55n10110100021010000513X32P1P0P31354P91564n10110100021010000,83%75P8E:1=54%<5=;64513eW0W1W2W4o"). Qed.

Lemma bytes_at_in : forall segs ms a bs,
  ms_rom ms = seg_rom segs -> bytes_at segs (ms_mem ms) a bs -> bytes_in (ms_read_byte ms) a bs.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h01ih16__sat1h24__x1h32Hah42H0h57__arithh64__ffh76__sat0h88__varmaph95__with:4__x2h;4cstrh<1Hh=2Hih>2Hlh?4Hromh@1ahA2bshB2mshC1ohD4segsp;1p;3p;4p;2p;6p;7p;8g0035j1=Tg003Uj16Tg004:j1FTg004Xj1DTg00;Nj1eTg00@Rj1YTg00APj1VTg00B[j33Tg00C5j18Tg00E^j4RTg00Flj21Tg00GLj15Tg00Glj20Tg008ej1JTg00HIj2]Tg00Hfj24Tg00IBj2:Tg00IZj1;Tg00DUj39Tg00Jbj37Tg00K@R0j2<Tg00<0j1Ej2UTg00K[j3CTg00Lkj1TTg00MPj2STg00N8j2HTg00NTj3QTg00O8j2PTg005;j2>Tg00OYj1OTg00P9j2@Tg00PWj1NTg00Q5j1MTg00Q`j2?Tg00RCj2ATg00Rfj4GTg00SQj1LTg00T3j2dTg00TUj2cTg00UAj3bTg00U`j4aTg00VRj1_Tg00W0j4\Tg00WNj3ZTg00X1j3[Tg00XTj4XTg002<j6^Tg00Ylj4ITg00ZGj7WTg00Zkj8`Tg00[OR1f0R2'4p=2f1R3g00[mR4g00\LR5P5g00\lR6P2g00]LFWp=Bf3R7P4P5P5P6f2R4P3P2G`p=Kg005U#=g006Tg00]lR8g007[R9#6R:#6#6R;#F#DR<#=%6;#6#6R;#FR=#D%e<R>[%Y4%V733f4R?%87P4P3CRP0%2711<4#5,07%J:R@%J;R;']RA'4g00^JRB11<7,:2f7RCf6RD#8f5RE%53RF'0#;39A7<?353>[]0'<%EE?C?7P2%2E11<E#5,0D/4A11<DRE,:2f:R?f9R7#8f8RG/0F#;39A7<C353>[^0B'<P0%5E,0C/4A11<C,:2f;RE%8?107F#;39A7<G353>[^0B%E7?CGCP211<G#5,07/4A11<?R7,:2f>RGf=RC#8f<R0/0F#;39A7<E353>[^0B%2E%57RH,0E/4ARI11<E,:2RJ10CF#;RF,UGRKA7<0353>[^0BR0'<%T7R7%2HRH1S@;RL1H1@RM%2;1H1A[RN[RO%2@RPg00^iRQAQ@;3UW3R;%2A\Q^3PRPP3g00_E1P1@'>PMeO1RMPNg00_kRQ#ORR%=QRQ1@83%N8RS%M8RTP81?81g00`WRU1A89R9CG,BTRV%L5R5PVCK1dT6R6P2P4g00a>RVg00a^RW'>1c24=3VWdAb813CaR1b6b8b9X28%22%23[^28P2f@RWP?O2b5b1b7b1b;PIP0P7PHPLPOP;PPPMPNPRPQP81@84P3%_8C\PSPTP81A8:9Z89PU1?8@=[8=CG,BTRTP5PTCKP6P1b6b8b9X28X:81023/4A1034/4A[^28^:8P2f?R8,1<#5PWPDO3b5b1b7b1b;P>%8G=98FA7<C493>2XC>P4P3P2O2PKP8PGPFPECXE^X=JX0BCICIW<W>P3P2O2n2001000000121000000W4W3P3P2O2n2001000000121000000W4W?WAW@WBWDo"). Qed.

Lemma bytes_in_app : forall mp a bs1 bs2,
  bytes_in mp a (bs1 ++ bs2) <-> bytes_in mp a bs1 /\ bytes_in mp (a + Z.of_nat (length bs1)) bs2.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "p'0h01ih16__sat4h24__x1h34__x2h44__x3h57__arithh64cstrh75cstr0h84__ffh98__varmaph:5__with;6__sat3h<3Hi0h=3Hl0h>5cstr1h?1Hh@4__p1hA6__sat5hB1xhC2HahD4__x4hE1ni001nhF2H0hG2H3hH2HihI2n0hJ1ohK1yhL2z3hM4__p2hN1mhO2H1hP2H2hQ3Ha2hR2HlhS3Hl1hT3Hl2hU1ahV1bi011bhW3bs1hX3bs2hY1li021lhZ2l0h[2mph\1ri031rh]1zp%0p%1p&0p;1p;2p;3p;4p;5p;6p;<p;8p;Bp;7g003Uj1^Tg004:k109Tg004Xk103Tg00;Nk10BTg0035k10:Tg00Flj23Tg00b>j28Tg00GLR0j11Tg008ek104Tg00HIk20ATg00IBR1j22Tg00GlR2j20Tg00HfR3j27Tg00Jbj3?k20ITg00B[j39j1~Tg00K@R4j2<Tg00bUk201Tg00IZS00j1YTg00bnj1|Tg00cLk40FTg00coj4ITg00Lkj1@Tg00MPk20<Tg00NTk30^Tg00O8k20ZTg005;j2TTg00OYk10WTg00P9j2jTg00PWk10VTg00Q5k10STg00Q`k208Tg00RCj2bTg00SQk10QTg00T3k20PTg00TUk20OTg00UAk30NTg00U`k40MTg00dVj1sTg00e5j2hTg00e^j2`Tg008@k106Tg00X1k30LTg00N8R5j2;Tg00VRk10JTg00fJj4FTg00g5k500Tg002<j6QTg00Ylj4LTg00gXl<ZTg00h=j3dTg00hZj2}Tg00i1j2CTg00iNk20HTg00j1k30GTg00jNj2zTg00k0j2cTg00kJk10ETg00khk20DTg00lIk30CTg00m2j3mTg00mUj8pTg00n2R6j2wTg00nLj5yTg00>lj6vTg00nok20@Tg00oUj2{Tg0105S01k20?Tg010Xj1tTg0111k30KTg011Zk30>Tg00K[j3rTg0129lBlTg012_m<0=Tg00Rfj4aTg00ZGj7kTg00Zkk807Tg013Dk30RTg013mk30;Tg00W0k40TTg00WNk30UTg014Mk20]Tg014jk60\Tg015Nk70[Tg0162k70YTg016Vk60XTg00[OR7f0R8'7p=4f2R9f1R:'0/78p=>10:8#Yp=5f6R;f5R<f4R=f3R>?d9:;?839p=G1<:8,<9p=D%18,0:p=A179:/<8p=:177:/<8p=[A?9:899=>p=B109:/08p=fg00]lR?/T8p=6g00^JR@P@P@P?P?P?g017:P0P0P0P2g017ZP<P=P>P9P:P8MBlp=JP@P?P?P?P0P0P<P=P>P9P:P8N<0=p=WP?P?P?P?P?P?P2P8P:P9P2P>P=P<P;f7R2f8RAf9RBMBlp=\A9?:8p==P?P?P3P2P3P;P<P=P>P9P:P8M<Zp=e1;78p=]P9g00[mRCg00\LRDPDg00\lREP?P:g00`WRFP8Cag00]LRGFkp=SP>PCPDPDPEP9P:P8L07p=EB0R?:8p=Rg00_kRH@0;:8p=OP?P9P:P8H0Tp=HB0U?:8p=KP?P:PFP8Cap=gP=PCPDPDPEP>P9P:PCPDPDPEP8PGFkL07p=MAd>9:=?=8p>02P@P?P1P0P5g018=P<P=P>P9P:P8M<Zp=NP?P:g018_P8Cap=PP:PCPDPDPEP8PGFkp=_P9PCPDPDPEP?P:g019FR5P8CaPGFkp=X20]78p=UP@P@P@P?P?P?g019mP0P0P0P;g01:MP<P=P>P9P:P8MBlp>05A9?87p=iP:PCPDPDPEP8J0\p=oP9PCPDPDPEP:P8K0[p=VP9PCPDPDPEP:P8K0Yp=nP?P:P5P8Cap=xP@P?P6P0P3g01;4P<P=P>P9P:P8M<Zp=uP:PCPDPDPEP8J0Xp=qg007[RC#^R3#^S02#^R6#^#^#^R5$09RG$03S03&096$03R6$0BR1[S04&0:6S05Q05P@136:RF1368RI'8RJ%4>RK%18RL&043RM&045R5+0ARN5>>128:P1P;%1:RO,5<O1RPP6P6P=P>P:FGRQ[^0@3D1369RR#1RS,0>RT/7N136>RU,28RVA?6=:RW991P[^0@5DKS06%1FRP,0T128RRXP;136=RY,A<S07/5OO1A?6>:RZ591[^0@7:N,[TS08'<RT+01XE@%49R[%1J=>9N18RFRJ,28P1P<15=OO1R\P6P6P>P9P:FG[^0@3DS09PT[109PRP/7NA91\Z\X^0@5D[%4P1API128FP1P<1A=URF/5OO1P6P9P:DB[^0@7:N3DS0:1A>J18URS0;,28PQ[^0@7:NRQ,<K[Q09P4PKPQ%4=S0<17FN128YP1P215;OO1S0=P6P<P:DB[^0@3D%4F10FSP2136<RF#1S0>,0;S0?/5OO1=91W\V^0@7:N3DP8%4<S0@18FY,A;136;RV/8FRW,28P1PB15AOO1S0AP6P6P2P;P:FG[^0@7:NP4%1W=>2N1362RW/8VS0B,28P1f:RS15BOO1P6P6PAP2P:FG[^0@%4AS0C1AAWRQ/7N136AS0D,28P1f;RK15SOO1S0EP6PBP:DB[^0@3D%4Q%1VS0F,0Q128WP1PK136BS0G#1RQ,0SS0H/5OO1P6PAP:DB[^0@7:N3DP8Q0D/8WS0I#1=>BN136SRWQ0G'8RR,28P1f=RJf<RI/5OO1S0JP6P6PKPSP:FG[^0@%4KRX%1WR\,0KRZ/7NRT136KR],28S0Kf>R^15JOO1R_A?6I:R`591[^0@Ra'<Rb'<%4ZS0LA>ZQNS0M128WS0NP^136IRZ#1Rc=fJORd#YO1A?6K:S0O591[^0@S0P'<S0Q'<S0RPXPb%1RRb,0KRX/7N10\QRe=>KNRfP8XB?Rg17:8#|XK?XB?S0SPXPgPeO1RX,0KPgPgPgP?P?g01;V10:8H0F#6XN?XE?S0TPKPK%6KPbPXPgPg%6LXB@S0UPRPePWP\%6\Q0GPQ%6QEJEWM:\PNPN%6NS0V1=NNeS0WGeP:CIS0XPf%@WS0Y%4\S0Z%@ZR\%4cRQ20<M5Re%]MRR%45%]N[RX[Rb%4MRhg00^iRiB0^M5:UWCR5%4N\i^ChRhP:g00_E20Z7M'TPReO1RRPX&0WHRi&0:HRH1j?:&0V?Rj&0S?Rk208?7Rl1b?CRm5SkS0[&0QDRDQ0[CE20PkEREP8P9g00a>S0\g00a^Rn'TQ0\20O89;9ndB0N?7:H0MRnb8b9b:X2?S0]%48%4:Ro[^2?S0^P8fBRpPIO2b5b1b;b1b7b6b=PTPaQ0XPfQ0YQ0ZP\PQPePbP5PhPRPXg01<:Ra#sRT#sS0_,h?S0`1h?T1h?aS0a'R'RS0bg01<YRa'`S0c/OiS0dPH1j?9S0e1j?>RT7H:S0fPjPk&06C,b?Rq9SklS0gPDPk1b?3Rr/KqS0h,KmS0i208?M>0L?GRG5SkS0jPDPk1KmrRM/gGDMCEPEPnb8b9b:X2?X3?X4?109>Rs=>:NS0k17sN[\[^2?^3?^4?P8f@Rt,36S0l#1RufAS0m,36S0n#1RvPpP<P;O5b5b1b;b1b7b6b=Q0KP1P6P6PIPKP:I02RwP1P8P6PJP9DBXJ1RxP1P`Px1T1`PwP6PIPKP:12:ZRw1;OcR`P:PO%6ORxPZPc%6cRyENRzPwP`PzP8CIS0oP`136JRz/8ZS0p#1Rw,0^R{/7N%1zR|/0cS0q=>^NR}PgQ0SP{PgQ0qO1R{,0^PgPgPgQ0TP^P^%6^PwP{PgPgQ0UQ0pQ0qPzP|%6|S0rPZPcPyEJS0sEWM:\PNPNQ0WGeP=CIS0tP}%@zS0u%4|S0v%@=S0w%1=#4S0xQ0l#@S0y%4uS0zPePbP5PhPRPXPiPHQ0e&0J?R{7H:S0{PjPk1Pmr,_kS0|PDQ0|CEPEPnb8b9b:X2?X3?S0}1;8:1;:9S0~[^2?^3?S10P8fES11,36Rw#1R~%1SS12PAO3b5b1b;b1b>b7b6b=b<CFI00EQP_P9P:18Z]S13,2:%1]R_,0cS14,;OP:POPxQ13Q14PZPcPyP]P_%6_S14EJENQ0oP`Q0tP}Q0uQ0vQ0wQ0xQ0yQ0zPePbP5PhPRPXQ0dPHQ0fPjPkQ0gPDPkQ0|PDPkQ0h,PmDMCEPEPnb8b9b:X2?X3?X4?Q0~10>=,;9[\[^2?^3?^4?P8fDR`,36S0h#1S0gP~Q12P;PAO5b5b1b;b1b>b7b6b=b<CFO2EQWHX0@CLCLQ0LQ0QQ0XPfQ0YQ0ZP\PQPePbP5PhPRPXQ0dPHQ0{PjPkASklrS0dPDPkQ0[PDPk1glMDMCEPEPnb8b9b:X2?X3?%4s\o\o^2?^3?P8PvPpP=PIO4b5b1b;b1b7b6b=Q0MQ0PQ0XPfQ0YQ0ZP\PQPePbP5PhPRPXPiPHQ0fPjPkQ0jPD1KMqRQ=SkGS0ZCEPEPnb8b9b:X2?X3?X4?10:9RG,08R\/7NA>G>N[^2?^3?^4?P8PuPvPpP;O4b5b1b;b1b7b6b=Q0N18Z:S0Y#1S0X,0JS0P/=dS0M10cORf,0JS0[/=dP?P?%~?S0QPgQ0Q1=:8#|XK?XB?S0LQ0PQ0[PgPgPgQ0TPJPJ%6JQ0XPfPgPgQ0UQ0YPfPZPcPyP:POPxEJEWM:\PdPd%6dM<Z12:]1;O_RdP:POPxP]P_Q14ENP8CIPdQ0tP}Q0uQ0vQ0wQ0xQ0yQ0zPePbP5PhPRPXPiPHQ0fPjQ0i=XkQPEPnb8b9b:X2?X3?X4?Af8:9S0i,=\^2?^3?^4?P8Q12P~fFR\O3b5b1b;b1b>b7b6b=b<CFQ0MP?18z9RQ,A^S0MPt%Y8O1A?6J>R}591X]?P1Ad6JIS0z=?6QS0yA918}XJ1R}P11}QzRd9?6IP}P@P120I6IR}P}PdP9P1\@/T}A9@d9%19R},0|Rx/C|#URf/=}P@P?%~@P0Q0Q1=OLA9@:820H:840GXK@XB@PdPf1C:8#UXN?XE?S0xPQPxPzP|Q0rP9P}%6}RfEJS0wPzP|Q0rK05P9P}PfM<Z129Z1;}cS0vP9P}PfPZPcPyENP:CIS0uQ0vf?Ry136^RZ/8zS0t#1Rf'0Rd/7N%1ZRL/0|R0=>yNS14PgQ0SPdPgP0O1Rd,0yPgPgPgQ0TPyPy%6yPfPdPgPgQ0UQ0tP0PZPL%6LPzP|Q0rEJEWM:\PNPNQ0WGeP<CIS0WQ14%@ZS0t%4LS0Y%@<S0X%1<R0#4S0[Q0n#@S0P%4vS0K136pS0o#1S15/A2Q15'CRd,z7%]d%UdRf/=d'<%if9:d7'cfCS16,36S17#1Rd%1AS18'0/Cd#UP?PePbP5PhPRPXp-0RfQ0cQ0_#s,h?S0_&0EC-0D?Q0`60C?Q0a'RRC'R/`aS191`Ca/OiS1:'O'OPHQ0eAHT>{7H:PjPk1ok<&063,b?R3/Kr=m?3RC9Xkm5VkASkClAXkmlS0e5Vk5nkPDPkQ0dPDPk1xmrDMCEPEPnb8b9b:X2?X3?X4?W@109:/C9RC,=8,<>%i8S1;9:C7'c1=9>\[[^2?^3?^4?^@fP8fHS1<,36R[#1RC%1JS1='0/CC#]PCQ1=P=P<P2O6b5bAb1bAbLbGb>b7b6b=b<CFGpQ0yP6PJPIPQ1wzQ17|xPzP|Q0rPQPxQ0wEuQ0uQ0vQ0WQ14Q0tQ0YQ0XQ0[Q0PQ0KPePbP5PhPRPXPiPHQ0{PjPkQ0dPDPk1gmMDMPEPnb8b9b:X2?X3?17:G\o^2?^3?P8%1KRo136\RJ#1RCP<O3b5b1b;b1b>b7b6b=b<CFDyEQPyQ0M#YO1P>PQQ0p,2QQ0q,;xPQPxQ0wQ0pQ0qQ0sENQ0uQ0vQ0WQ14Q0tQ0YQ0XQ0[Q0PQ0KPePbP5PhPRPXPiPHQ0fPjPk1Prq,_kRxPDPk1KmqRQ,PMDMPEPnb8b9b:X2?X3?X4?Q0~10:>,;G[^2?^3?^4?P8P~PoPCPAO4b5b1b;b1b>b7b6b=b<CFO2EQ10^|RG/0}P8EvbFWHX0@CLCLCLW?WRP:P8O2n2001000000121000000WFWCP:P8O2n2001000000121000000WFQ0:P4Q06Q08Q0<Q0;#1=>=N18YU,28P1Q0=P6P6P<P=P:FG[^0@3DP8Q0@Q07/7N128FP1PA152OO1P6P;P:DB[^0@3DP4%4;Q0?128VRVQ0AA?62:RF591[^0@7:NQ0F,02RYQ0>,0YPSQ0D,ABRY/5OO1=91F\V^0@7:N'[Q0CQ0B#1=>ANQ0I,28P1Q0EP6P6PBPAP:FG[^0@3D[P8Q0CQ0G,28P1PI15KOO1P6PSP:DB[^0@9:YNP4Q0H/7NQ0NQ0JQ0O591[^0@Q0R18]W,AIQ13,28P1Py15^OO1P6Q0zP:DB[^0@7:N,[I[P8A>I_N128zRzPt15yOO1A?6^:R_591[^0@10GcQ0m136yRc,At/5OO1=91_\z^0@7:N,[GP410yLRL#410L|128ZP1PpQ0m/0uRL/5OO1P6PyP:DB[^0@7:N18cZ,AtQ0l/8c,28P1Q1615pOO1P6P6Q0mPtP:FG[^0@7:N,[tP8%4LAfpvuQ0n,28P1Q1110`d/5OO1P6PpP:DB[^0@7:NP4Q16Q15'0?>vNQ0o,28P1P\Q11Q0g'0Rv/5OO1P6Q16P:DB[^0@Q17Q0o'8,A`Q0hQ17'8,28P1fGR415\OO1P6P6Q11P`P:FG[^0@7:N,[`P8A>vdN128wP1fIRvQ1<1364Rd#1Rp'0/5OO1P6P\P:DB[^0@%4418JwR\#1Ru,04RL/7NRc18dJ,28RZP1fJR|15vOO1P6P6Q1<P4P:FG[^0@RO'<%@wRG%4~Rz%@dRd%4pRpPePbP5PhPRPXQ0]Q0^P8fMR_P`O2b5b1b;b1b7b6PcPOPc10C~Rc,04RO/7NPgQ0SPLPOPgPgPgQ0TP4P4%64PuPcPgPgQ0UP\PcPJPC%6CPwP~%6~EJEWM:\PNPNQ0VGePGPzPdPpPePbP5PhPRPXPiPHQ0fPjPkQ0ZPDQ0jCEPEPnb8b9b:X2?X3?X4?Q0i/7NQ0k[^2?^3?^4?P8fKRN,36Rp#1RdfLRz,36RG#1R~P_P2O4b5b1b;b1b7b6CF20@:[12:[1{:[+0?136v,{9Q0\Q01136|,2>fNR|10_0Rv#YR[O1P6P6PzPNP<I02Rw591P:12=pRCP1A?6z<fO%1;RJ,5|O1=918XJ1RcPyP<12<GRy1;0~R\P<P0%60RuPGP~%6~R4ENROPyP\POP8CIP\136_RL/8GR`,2;%1LRI/0~R],;JRWP;PJ%6JP`P]PLPI%6IPGP~P4EJENP<CIR]PW%@LRL%4IRI%@AR`Q18#4RJfP,36RY#@RK%1Y#4RYPePbP5PhPRPXQ0}Q10P8fU,36#1S10%1^R^PAO3b5b1b;b1b>b7b6b<bZCFRVO2PwP6PzPNP<PVI00EQWYP8O1%tCP11}<GRC9?6NRVPcP1P|10_~R_%1CRF'0RU#YR}O1PcQ03P1P|P|P[P}Q04/T|P?Q03Q00Q00PvPUQ03\?Q00'T1=vU1C0~#UR|,0_R},=vP?P?Q0QPgQ0QQ0LPvPv%6vPUP}PgPgPgQ0TP_P_%6_PFP|PgPgQ0UPCP|Q0xP<P0PuPGP~P4K05RgEWM:\M<Z%ty%t\RFB0Ky\OP8CIROPFP]PWPLPIP`PJPKPYQ12fQ,36#1'CR\,z7Ry%]\%U\R_/=\'<%i_9:\7'cR\fR,36#1,Co#URoP?PePbP5PhPRPXQ19Q0cQ1:'O'OPH1j?=R_?H9{?H:TPjPk1ok;R}Q02,b?RUAm?rqRq5Xk5VkASkqlAXkUl5Vk5nkPDPk1qkxPDPk1KQU,xMDMCEPEPnb8b9b:X2?X3?X4?XD?X@f1C:9RM,=>,<=%i>9:M7'c1;9>g01=ERM[Af9=<,=s[[^2?^3?^4?^D?^@fP8%1tRtfW,36#1Rs'CRQ#]RxP=PsPtfXP<PSO7b5bAb1bAbLbGb>b7b6b<bICFGpGpPVP;PC12Cp1;|dPCP|PgPpPd%6dENPOPFP]PWPLPIP`PJPKPYPyP\PoP?PePbP5PhPRPXQ0_Q0b'R/`aQ0_Q0`Q0a'R'R/`a/Oi'OPHAHT9{AH_={7H:PjPkAm?3U9Xkm9Vk}1ok2Q0e5Vk5nkPDPk1KUr,P3,_kPDPk1P3U,_k,qkPDQ0|CECECEPEPnb8b9b:X2?X3?X4?XD?X@fXMf1C>9,=8,<=Q1;,<<'c10>9,;=1;<=PM[1;>=[[[^2?^3?^4?^D?^@f^MfP817Q7PxPtPsfV,36#1P=P<PBPSO9b5bAb1bAbLbGb>b7b6b<bICFO2EvPwP6PzPNP<1wG<17~0PGP~P4P<P0PuEuPOPFP]PWPLPIP`PJPKPYPePbP5PhPRPXPiPHQ0{PjPk1Prm,_k,qkPDPk1gmrDMPEPnb8b9b:X2?X3?1;:8PM[17:9[^2?^3?P8P^Q10PAO3b5b1b;b1b>b7b6b<bICFDyEQWEP8O1n10210110300021110211100bVb\XHZX0@CLCLWPWTP:P8O2n2001000000121000000W?WQP:P8O2n2001000000121000000W?WOWSP:P8O2n2001000010121000000W?WCP:P8O2n2001000010121000000W?P:P8O2n2001000000121000000W?CLAd6:8R@,36B0>6:8EQAr>9@Ar>9:Ar>P8'<+01eWXWWXU?W[o"). Qed.

Lemma bytes_in_cons : forall mp a b bs,
  bytes_in mp a (b :: bs) -> mp (wa a) = Some b /\ bytes_in mp (a + 1) bs.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h02H1h11ih21Hh31ah42mph53bs1h63bs2h72H0h82H2h92_Hh:3_H0h;7__arithh<4__ffh=8__varmaph>5__with?1bh@2bshA1zp;1p;3p;2p;4p;7p;6p;<g003Uj19Tg004:j1FTg004Xj1DTg00;Nj1KTg0035j1GTg013mj30Tg00K[j33Tg00h=j3ETg00K@R0j26Tg01=bj4ITg00OYj1BTg00IZj12Tg00D3j2>Tg00B[j31Tg008ej1ATg00Hfj2<Tg00Flj25Tg00HIj2WTg00IBR1j2;Tg00GLR2j1@Tg00Glj27Tg00Jbj38Tg00dVj1VTg00N8R3j2UTg005;j2?Tg00VRj1QTg00PWj1LTg00Q5j1JTg00Q`j2CTg00Rfj4MTg00ZGj7NTg00T3j2OTg00TUj2PTg00UAj3HTg00U`j4STg00fJj4TTg01?6j1[Tg00>lj6ZTg00Ylj4YTg00gXl<XTf1R4f0R5'5#@p=:f3R6f2R7/74;35p=4%@5,74p==g00^JR8g00]lR9P1P2P3g018=g01<:R3g00[OR2P6P7P4P5M<Xp=Rg007[R1#9R:#9#9R;#9#9#9R<#F#D%F;#DR;#KR=[R>%G;R?A0;459367P0AE;459367f4R@?367P@P61:;7P4C4'6[RAA3674P6P71:;4P5C4'6AE;7493@6RB[f5RC?3@6PCP@1:;6P7C4'6\BP6P7P4P5CIP4n2001000000120000000X6?X5?X39X4>PA^6?^5?^39^4>P5PCP@%B;R>90;6R?P7P4O5A3C@?PCP@1:;?P7C4'6P0f6R?A0;@>RA73CP?PC1:;AP6C4f7R6%2?O11>;C51=P6P?%A1R1P@C4'6P5f8R@A0;?>736f9RCP@A0;6>,:;P?C4f:R?%2CO11>;@51=P?PCP1P6C4P01<2CA0;@>,5;,=C%A:%A<'WR<'<A0;C>,5;,;5f<R:f;R@%@4R6'7#2O1A0;?>=8;451=[^18'6P@%2?O11>;C51=P41<2@A0;@>,5;,=:/<<A0;:>,5;R:,;5f?R@f>RC/76#2O1f=R?=0;>RA=8;451=[^18'6P01=?:/<<15;A,;5f@RA17@6#2O1A0;C>R:=8;451=[^18P@%2CO11>;?51=P515;:,=@/<<A0;A>RA,5;R<,;5fCR@fBR:/76#2O1fAR6=0;>R?=8;451=[^18P5P3%V3R8,;31U21RC1?92P8P11?91CRg00_kR8#B%G8%Q9%L9%J9R8g00[mg00\LR0P0g00\lR0P91C92g018_1C91CMg00]LFN1O80P5P7g00a>R0g00a^R8'?1P57=108dAH924CSb<b=b>PCP5b;CT1;3<eO2P:1=63#2O1A8;A351=P917:2fD%25O1A0;:>=8;351=XA9P5P:%[:EZP@%2:O1A8;?351=P5b0b0W0W:P4P5O2n2001000000121000000W2W9P4P5O2n2001000000121000000P5CYW8W0P4P5O2n2001000000121000000b2b7W2W@X?;X39W4o"). Qed.

Lemma read_bytes_aux_bytes_in : forall bs mp a,
  bytes_in mp a bs -> read_bytes_aux mp (wa a) (length bs) = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "p'0h01Hh11ah22bsh32mph41bi001bh51oh62Hbh72IHi011ri021xp;1p;3p;2p;5p;6g003Uj16Tg004:j1=Tg004Xj1<Tg0035j1@Tg00;NR0j1>Tg00K[j33Tg00IZj12Tg00Flj24Tg01?Wj35Tg00D3j20Tg00B[j31Tg00OYj1?Tg005;j2:Tg013mj37Tg01@Tj5GTg008ej1FTg00Glj28Tg00K@R1j2ETg009Cj3DTg01Aij3;Tg00SQj1CTg002<j69Tg01BNj1BTg01C[j5ATg007[R2#6#6#6R3#=#<R4#@R5P4%63#6#6#=R3#<R6%>4R7[R8g00]lR9f1R:f0R;f2R<33%>5R=%2:R>f3R?,4455<105?31[]1]3R@X25%?4RA93:;105A,:=W0X19X38f4RA=74?93:;P<P:f5RBPAP;DGP<P>O1104B517%F2R2,8:=3<A'EP1P?%2<O1f6R1,0451718<2=3?B%2?f7R?=741R<,4455A105<51=P;PB%2AO1f8RA,0451718B2=31AP7f:RB,04P0P4P=P;P0P5P=f9R<%2Ag00;29D32R>5;3f;RC,4435A74:;,05%C5RDn10110200021010100PDn10110200021010000A74CB,05RC51=X57P61812R2#2R7P0P5P=144B95A;f<=74;,05REPDn10110200021010100=1=CX46P=105<P0P5P=P;PEPDn10110200021010100=1=CX5=A74B<RB,05RC,:=144<95?7PAP?P2P;O3E9%21R2=;3>%B1E9P?P2O1P:E9144B95?2=1=CeW0W6P:P;O2n2001000000121000000b0W0X19X38X7@X25X44P;DAW2o"). Qed.

Lemma readable_bytes_aux_bytes_in : forall bs mp a,
  bytes_in mp a bs -> readable_bytes_aux mp (wa a) (length bs) = bs.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h01ah12bsh22mpp;1p;3p;2p;4p;5g003Uj10Tg004:j12Tg004Xj11Tg0035j13Tg00;Nj19Tg00K[j38Tg00Flj27Tg00IZj14Tg01D=j45Tg01E\j56Tg007[#0#0#0R0#2#1R1#3%00#0#0#2#1%91[g00]lf1R0f0R2f2R338P3f3R4,71%40P4P4P3P0P2C5D6UW0W2W1o"). Qed.

Lemma word_to_nat_of_nat : forall n, Z.of_nat n < 2^64 -> word_to_nat (Z_to_bv 64 (Z.of_nat n)) = n.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h04__x1h16__sat1h21xh32Hah47__arithh54__ffh64__p1h76__sat2h88__varmaph95__with:4__x2h;4cstrh<2H0h=6__sat0h>1nh?1yh@1zhA2z0p;1p;2p;3p;<p;4p;6p;7p;8g00GLR0j12Tg003Uj13Tg008ej1FTg00HIj2MTg00N8j21Tg01FoR1j1GTg00B[j30j1ETg014Mj28Tg00iNj2VTg00j1j3LTg005;j2<Tg00gXl<oTg00Lkj1nTg00jNj2dTg00K@j26Tg00Hfj2?Tg00k0j2HTg00MPj2ZTg00NTj3YTg00O8j2XTg00dVj1>Tg00e5j2;Tg013Dj3:Tg00e^j2ATg00kJj1WTg00khj2UTg00lIj3TTg00OYj1STg013mj3=Tg0035j1NTg00P9j2CTg00VRj1KTg00W0j4OTg00PWj1PTg00Q5j1QTg014jj6RTg00RCj2DTg00Rfj47Tg00Q`j2ITg0162j7mTg00SQj1lTg00T3j2kTg00TUj2cTg00UAj3bTg00U`j4_Tg00fJj4^Tg004:j1`Tg01GOj2aTg01H5j2]Tg00X1j3eTg01H_j2fTg002<j6\Tg01J4j1[Tg012_l<gTg00ZGj7hTg015Nj7iTg00Zkj8jTg00]lR2g00^JR3P2P2P1f4R1P0f3R4g01Jof2R5f1R6f0R7M<gp=Jg00[OR8/?7p=4P6g00[mR9g00\LR:P:g00\lR;P7g00]LFhp=5P5P9P:P:P;P6P7Fip=BP2P6g00`WP7C7p=@P4P9P:P:P;P5P6P7Gjp=9%27R<g007[R=#3R>#FR?%3>#3#3#3#3R@#FRA'MRB'1P2%26RC%G7=035X@2%GCRD=036188CRE=02CP3P2%E3P0%E2A02C<A03671V673LX?3X23PDPEP7X221887X22PCPC1<2CREDJP6PCPEM<o%n6RE%4CRD%25R<,d8118<188<R0=02<'61?<8A0208'6'H%24,88P21Z?AR0118?R<%4A118B[RF[RG%4?RHg00^iRIAY?A6UW3RA%4B\I^3HRHP6g00_E1X8?'<P<eO1R<PFp-0RIg00_kRJg01<:RK#>RL#>RM,;2RN1;2L1;2KRK5:25:2g01<YRL'A%>M,;2%W=,U2=T2N=:2KRK5:2/AL1AKL%SJRK5=J5=J3=%NJRJP21C25P6%K2CO%P2RL%Q2RNPNP9P:P:P;PNP9P:P:P;P1ERP21D2=R=g019FR91D2>R>C7,5NRM5BN1I28RO,@>,5NP2P=P9POC7,5N5BNFm%l:R:PN1@O>,5NP:PMC9C91kN;R;P7P5g00a>RMg00a^R>'<1c75=0M>dAb286C_R>b5b8b9X02X:2W6A0276,651?68A0278'6'H%45RMA0254[[^02^:2^6IP7f8#2RI,18PIP1f5RIf6R8O5b4b7b1b7bAb<b;C^%`@R@1a@CR4']PEPDP0PGPAPHP<PFPKPJ1C26PLPN1@O=,5NROP:PNP2P=g018_1I2?=e2@C7,5NR@P:ABNO@C9C9P;P>b5b8b9X02%47116B115B,6M[[^02P7%28P1PIO3b4b1b=b1b;,fCE\%[4=036eUX>3o"). Qed.

Lemma read_bytes_map_bytes_in : forall bs mp a,
  bytes_in mp a bs -> Z.of_nat (length bs) < 2^64 ->
  read_bytes_map mp (wa a) (Z_to_bv 64 (Z.of_nat (length bs))) = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h01Hh12Hlh21ah32bsh42mph51nh61op;1p;3p;2p;4p;6g003Uj10Tg004:j14Tg004Xj16Tg0035j1=Tg00;Nj1:Tg00K[j3CTg00Flj23Tg00GLj12Tg008ej15Tg00HIj2>Tg00N8j2<Tg00IZj18Tg01GOj2;Tg01J4j1ETg01?Wj39Tg00D3j2DTg00B[j37Tg01D=j4BTg01K\j2@Tg002<j61Tg01M6j3?Tg01N3j3ATg007[#0R0#0#0R1#4#6R2#=R3%01#0#0R1#4R4#6%:2[g00]lf1R5f0R6f2R73Cf3R8,32#2%50%51'>'<%:3R1%87R0f4R9,32R2#2,;4R4#ER:598f5,D3R39716X61g00^JR;P2%88=996=713X5;P9P8P7P5CBP:1@26E1A?804AA804E1W1W0W2W4W3o"). Qed.

Lemma readable_bytes_bytes_in : forall bs mp a,
  bytes_in mp a bs -> Z.of_nat (length bs) < 2^64 ->
  readable_bytes mp (wa a) (Z_to_bv 64 (Z.of_nat (length bs))) = bs.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h01ah12bsh22mpp;1p;3p;2p;5g003Uj10Tg004:j15Tg004Xj14Tg0035j16Tg00;Nj1>Tg00K[j3;Tg00Flj23Tg00GLj12Tg008ej11Tg00HIj27Tg00N8j28Tg00IZj19Tg01GOj2:Tg01O3j5=Tg01PRj5<Tg007[#0R0#0#0R1#5#4R2#6%01#0#0R1#5R3#4%>2[g00]lf1R4f0R5f2R63;f3R7,32#2%10%11'7'8P7%96f4R1,32#2,:3P1P1P7P6P4P5D=D<UUW0W2W1o"). Qed.

(* [comment removed for export] *)
Lemma read_cstr_aux_bytes_in : forall str fuel mp a,
  (length str < fuel)%nat -> ~ In (Z_to_bv 8 0) str ->
  bytes_in mp a (str ++ [Z_to_bv 8 0]) ->
  read_cstr_aux mp (wa a) fuel = CstrOk str.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "p'0h02Hfh11Eh21Hh31ah41bi001bh54fuelh64__p1h74__x1h83Hf0h97__arithh:4__ffh;8__varmaph<5__with=2mph>3strh?2Hbh@3HnzhA4__x2hB4cstrhC1ohD2H0hE3HinhF3HnehG2IHhH2_HhI2b0hJ1chK5cstr0hL1xi011xi021ni031rp;1p;2p;3p;4p;5p;6p;<p;7p;8g003Uj1ATg004:j1\Tg004Xj1ZTg0035j1PTg00;NR0j1vTg00Flj24Tg00IBR1j23Tg01GOj2fTg01Qaj3@Tg010Xj1FTg00OYj1QTg013mj31Tg00h=j3?Tg00K[j3:Tg00IZj16Tg01R8j38Tg01S4j15Tg00N8R2j2<Tg005;j2;Tg00coj4JTg00VRj1eTg00PWj1cTg00Q5j1bTg00Q`j2STg00SQj1aTg00T3j2`Tg00TUj2_Tg00UAj3^Tg00U`j4]Tg00dVR3j1>Tg01@Tj5OTg00D3j2DTg00B[j30Tg008ej1uTg00Glj29Tg00K@R4j2[Tg01T0j3=Tg009Cj3tTg01Aij3YTg002<j6BTg00GLR5j17Tg00Lkj1LTg00Hfj2HTg00P9j2XTg00RCj2WTg00Rfj4TTg00WNj3VTg01T]j3oTg01URj3mTg01Ulj2lTg00W0j4iTg00fJj4jTg01VKj3kTg01BNj1gTg01C[j5nTg00gXl<KTg00ZGj7dTg014jj6qTg00Zkj8rTg012_l<sTg01VeR6f1R7f0R830p=2g00^JR9g00]lR:P1P5P2g018=R;g01<:R<g00[OR=P7P<P=P8M<Kp=hP:P7g018_P8CTp=GP7g00[mR>g00\LR?P?g00\lR@P8g00]LFdp=CP7P>P?P?P@P8Eqp=Rf3RAP>P?P?P@f2R>P7P8Grp=Ig00a>RBg00a^RC708p=EP9P9P:P:P3P5P5PAg01WaP>P7P8M<sp=MP9P:P1P5P2P;PAP>P7P<P=P8M<Kp=pg01XER390B8p=NP9P:P1P5P2P;f5R;f4R2PAP>P7P8M<Kp=Ug007[R5#AR1#A#ARD#\RE#ZRF#PRGPF%AD#A#A#\RD#ZRH%vFRI[RJ14FA/3>1fE=RK=@F2#F%QFRL91FKRM9?F;9:A>%6A=82;f6RN#5'2[[[^3:]=^59ROX>G14FLRP/3>A@FKL#FA?FLM9:A>P913P8%6;=8N7RQ%5LRR'2]0P;13P<13<<1<==RS1;:=RT/hTP8CJPSp-0RUg00_kRV#QRW%PVRV%e:RX%c:RY%b:RZ1S:=R[/G[,CZ%a?R?1RZ>CI1`Z@R@P8P>1;BC1_8>#EdA^:=7C]R\b:b;b<W6P7\S^6UP8f7RS%6NR];8</2RP7O2b9b8W0%>8R^,3PPSPNPKPLPADOPSP]O1R]1DFKRP50I%u5R_,9NR`=:SL'[P4f8Ra%6SRbO1Rc=0IP19S_Rd=:aLf9Re%6a%>A38Rf/2RP8f:Rg%6eO1Rh=0IPf;Ri19g_Rj;:LPIPPP0PFP6P8PBP6A=E8KPRP6P6f>R0f=RP#6g00;29tD_RL5YD;8aRkA1F78#5g01XeRlg01YaRmn011010003101030000n0100000020000Pmn10110100021010000Rn/2RXCI1;6Rf<Ro%6iRpO1RqP7EB%>N98opRp/2ReWHW?P7P8O2n2001000000121000000b2W0X59P8O1n0110200020011102P>O1W2W@W0X3:X=JX59A1F;2,4F/3>A1FN;9@FK#FA1FSN=?FM9:A>P9A1Fea,4F/38A1FgeR2#5,2Q]0P;A1FaS,4F/3<14FaR;#>RQ/3<%7;Rr/9_/<=RsPQ198_RQXL:RtPrO1PtP;Pr1;:rCMPTCpP8CJPs14FeRe#L%7e,H=PWPV1X:7PYPZP:P[g00`W1W:5R5CT,CZP?PZ1S:_Re9V:5Rs/G[,CZP?1RZACICIP@P\b:b;b<X7:X6U1H=8197_R[/<=PA[[^7:^6UP8A8ab<A1Foi#5'214Fi#7P7P>O4b9bBb8W014F2/3^PSPNPiA?FgMRgPADO1DFi90I]A:S`g'[P41DFo90IcA?FiM9:adA1FPo#5,2fP81DF090IhA?F0M9:ijPIf@Rj,DFfARM=1Fj#5Rh,2nXCIA=EjKRIPB1;B8A=EMKRn=0B8PBfCRf==EK=0B8%N7]1P7fBRd==EKRc#EP4A=E78#EA0F>7[R4A0F78A=E>7#ERg[A0FA>\gAoE78P7n2001000000120000000X4FX3FP4^4F^3FP8fDR4PKP7O3A0F4KA0BC3P0fE=0FKA@FK4;m8O1'lb1bDW1%Nc1;B3W1n0110000020100P8O1b1bI%NIPBP3PBP6P8PRP6P6PkA1Ff8#5RfPlPmn011010003101030000n0100000020000A1FdM#5Rk'2X4BPH19o_RB#6RRP6P6A808aPfPlPmn011010003101030000/2kX4HP6%5jP6P6P8PfPlPmn011010003101030000/2kXJ61;6hA8PRSf?RRPSPPPB14FjRB/3S%7BRP%7SRh'<PBPP1;:PR6PSPh1;:hRkEU%>BRm%>SRl'319P_19h_'<R_PmPtPPO1PtPBPPP6CMPlPtPhO1PtPSPhPkCMEUPNCJP_%La%7a,H=14FdRa#L%7a,H=PWPVP:1X:>P7PXCiPYPZ1W:1R1=V:e,Gs,CZP?1G51,CZCIP@P\b:b;b<X7:XA:1<Q[1<7>[^7:^A:P8%7i14F4#7PAO3b9bKbBb8CjA@FKjRAPiA0FdKA@FKM;k8O1WE%FAeP7O6EB%6o=YDL%goEBPnP8EBbFPqP7EBA1FjR#5,2peW2W?P7P8O2n2001000000121000000b2W0X59P8O1n0110200020111102P>O1W2W@W0X3:X=JX59XGOX>GX4FP8DnW>o"). Qed.

Lemma read_cstr_aux_toolong_bytes_in : forall fuel str mp a,
  (fuel <= length str)%nat -> ~ In (Z_to_bv 8 0) str ->
  bytes_in mp a str ->
  read_cstr_aux mp (wa a) fuel = CstrTooLong.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "p'0h01Hh11Eh22Hfh33Hnzh41ah51bi001bh64__x1h73strh84fuelh92mph:3Hf0h;7__arithh<4__ffh=4__p1h>8__varmaph?5__with@4__x2hA4cstrhB2H0hC2HbhD3HinhE3HnehF2IHhG2b0hH1chI5cstr0hJ1ohK1xi011xi021li031rp;1p;2p;3p;4p;6p;5p;<p;7p;8g003Uj1>Tg004:j1VTg004Xj1QTg0035R0j1LTg00;NR1j1rTg00Flj2=Tg00n2R2j25Tg01GOj2_Tg01Qaj3<Tg010Xj1?Tg00K[j3:Tg00IZj11Tg01R8j39Tg005;j28Tg00dVR3j13Tg00OYj1STg00GLR4j17Tg008ej1gTg00Glj24Tg00HfR5j22Tg00coj4PTg00Lkj1GTg00P9j2OTg00PWj1]Tg00Q5j1\Tg00Q`j2NTg00RCj2MTg00SQj1[Tg00WNj3KTg014jj6ZTg00T3j2YTg00TUj2XTg00UAj3WTg00U`j4qTg013mj3ETg01@Tj5pTg00D3j2DTg00B[j30Tg00K@R6j2oTg01T0j3;Tg01S4j1ITg009Cj3lTg01Aij3TTg01T]j3jTg01URj3iTg01Ulj2hTg00VRj1fTg00W0j4eTg00fJj4dTg01VKj3cTg002<j6CTg01BNj1bTg01Z]j4aTg012_l<kTg00gXl<UTg00Rfj4`Tg00ZGj7mTg00Zkj8nTg01VeR7f0R8g01XeR930p=6g00^JR:P:g00]lR;P;P3P4P4f3R3g01Waf2R<f1R=P8M<kp=JP:P;P2P4P5g01;4R>P3P<P=g01<:R?g00[OR@P8M<Up=^P;P=g00`WP8C`p=AP=g00[mRAg00\LRBPBg00\lRCP8g00]LFmp=BP3PAPBPBPCP<P=P8Gnp=Fg00a>RDg00a^RE708p=@g01XERF90D8p=HP:P;P2P4P5P>f5R>f4R5P3P<P=P8M<Up=Rg007[R4#>R2#>#>RG#VRH#QRI#LRJ%>G#>#>#VRG#QRK%rIRL[RM1=I<RN,531_H@RO=<I3#?RPA:3<5RQ%13f6RR595#6[[[^4;]9]7RSX8:15?N1879RTX0QX3PW2X4;X9MX7J%35/5NP0PIf8R0#31=I8'5A<IO=#?f7RN?:R<%1Nf;RU#3RV590#6]0]3]2P>%3N%SIRW,=I'5A<IOW#?A:R>Wf:RR#3RX/5?%7RR?%g4RY'4/2@RZPX148YRXXK;R[P?O1P[PRP?18;?CJ18;@C^P<CPPZ%GU%7U,2@p-0RZg00_kR?#SR\%L?R?1O;=%];R]%\;R^1N;@R_1M;4R4'A,B^%[BR`P^1N;YRa9K;4Rb/A_,B^P`P^PAPBPBPCP3EZCFCF1Y^CRCP8P<18DE1X8<#@dAW;@=CqRBb<b>b?X6;W=12@814=YRA/2@P3[[^6;^=ZP8f9RZ#1f=R_#359R#6%7_P=P<O4b;bAb:W0W3W2AEI=8Rc,=I,5VAEI<=9<IO#?AEI3<9:RZPUPRP5P3P8DpPU%1RO11DI550L14RY=:U3'oP6f<RV%1UO11DI>50L14UY=:V5%1Vf@R5#359_#6P8f>R>%1_O11DIN50Lf?Rd14>Y;:NPL1DIZP1PIP7P8PDP7A;H8O%IWRWP7P7fBR1fARN#1g00;29lGYRe5TGfERf39Rg%IcP9g01YaRcn011010003101030000n0100000020000Pcn10110100021010000#6XJLA;HZORLPD18D8A;HRORh=0D8PDA;HVO=0D8%H=]1P=A;HUORi#@P6A;H=8#@A0I<=[R6A0I=8A;H<=#@Rj[A0I3<\jAjH=8P=n2001000000120000000X5IX4IP6^5I^4IP8P_POP=O3A0I_OA0DEFPUA0I>OA<IO_;i8O1'hb1bBW1%Hi18DFW1n0110000020100P8O1b1bG%HLPDPFPDP7P8PWP7P7PgAEIV8#IRVP9Pcn011010003101030000n0100000020000#6X5DPK145YRD#1RgP7P7A918fPVP9Pcn011010003101030000#6X5KP7P9P7P7P8PVP9Pcn011010003101030000#6XH7PTfDRT99NgfCRgPZPNPD1=IZRD,5T%7TRN%7DR7'2PTPN18;NRcPDP718;7R9ER%3TRV%3DRK'514NY147Y'2RYPVP[PNO1P[PTPNPcCJPKP[P7O1P[PDP7P9CJERP0CPPY%Gf%7f,2@1=IURf#G%7f,2@P\P?P;1O;<P=%f;CeP]P^1M;2R2=K;a,Ab,B^P`1A42,B^CFPCPBb<b>b?X6;X@;12XA12=<[^6;^@;P81=I_#7fH#7P3O3b;bIbAb:CdA<IOZRZP0A0IUOA<IOR;c8O1WD%?ZeP=O6EC%15=TGe%b5ECPhP8ECbEP5%1dRdO1P=EC%3g995d#6eW0WCP=P8O2n2001000000121000000b0W0W3W2X7JX5IP=P8O2n10110200020121100102P<P=P8O3X0QX3PW2X4;X9MX7JXFSX8:P8CaX8:o"). Qed.

(* [comment removed for export] *)
Definition iovec_bytes (iovs : list (word * word)) : list byte :=
  flat_map (fun p => le8 (fst p) ++ le8 (snd p)) iovs.

Lemma length_iovec_bytes : forall iovs, length (iovec_bytes iovs) = (16 * length iovs)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "p'0h01nh14iovsh24__x1h31lh41xh52IHh63IH0h77__arithh84__ffh98__varmaph:5__with;1ah<1bi001bh=4cstrh>5cstr0h?1pi011ph@1yp;1p;2p;3p;4p;7p;6p;5p;Bp;<g003Uj17Tg004:j1QTg004Xj1ITg01[>R0j2YTg0035j1STg01[^j1BTg00Flj20Tg01]1j25Tg00OYj1FTg005;j28Tg013mj3>Tg01]Hj1<Tg00h=j3?Tg000ej3cTg01^Qj3_Tg001Bj4LTg00b>j22Tg01^nj4JTg00dVR1j1@Tg008ej1=Tg00GlR2j29Tg00GLR3j14Tg01_NR4j2;Tg00B[j36j1HTg00iNj2[Tg00j1j3ZTg00coj4WTg00Lkj1DTg00Hfj2OTg00P9j2VTg00PWj1UTg00Q5j1TTg00Q`j2ATg00WNj3CTg00RCj2hTg01_kj3RTg00Rfj4gTg00ZGj7fTg00T3j2eTg00TUj2bTg00UAj3aTg00U`j4`Tg00fJj4^Tg002<j6:Tg01`Nj1MTg011Zj3NTg01C[j5]Tg0129lBPTg012_l<\Tg00gXl<dTf0R5#@#@p=3g00^JR6f1R7;65p=1P6P6P6g00]lR8P8P8g017:P3P3P3P2g017Zf5R2f4R9f3R:f2R;P7P5MBPp=GP6P6P6P8P8P8g01a^P3P3P3P4g01b>P2P9P:P;P7P5MBPp=KP6P6P8P8P1P3P3P:g01WaP;P7P5M<\p=XP6P8P5P3P7P;P:P9P2f6f7f8M<dp=Eg007[R3#7#7#7R1#7R4#7#7#Q#IR</Y<R=#SR>P=%Q1#IR?%B5'0g01<:#3#3#3#3R@#3#3#3#3RA10=5'5'1RBX1>%F=,0=,5A,86P0P<P<A>=;7R0#B,0?10=0,5A'1\B^3>P5P6%<:R0%<;RC5??RD,0?REP=P?Ac<<5#<A_<<5#<5??X?=RFP7CLRG,0?RH'2P<P<P9P:CJ=>=;,0=,5AR9,15X06P610?0RI10?CRJ'2P=P?PFP;CL,0?RF,25/19X06P6P@125I/2F/19X06P6P@12@5/2F/19X06P610=7RK,5ARL12@@RM/25/19X0612MLR9%@KRN,5ARO'1%=1R1/91RP%=4R4%4KRQ';RR'9RS%=3RT,9QRU,;4RV568%H6RW%H8RX%47%4556811751[753ZX@6X46R6P9PSPMPPP@P11881RMP@P1PMEGPLPRPAP41884RMPKPQ188QR@EKRSEGPOPVPAP4PMPNPU195TRUX48PKPQP@CXEKM9E11HL%4HR@=68RRQPWPXP6PHP@188@PLPRPSM9EP5CWPQ%DFg00[ORQ%4F'O10=:RF#D%4F,OQg00_kRF#F%SF1V87%U8%T8RFg00[mg00\LRSPSg00\lRSP81A81R1=C811A84R11h83R35R85C8g019F1A8T9C839R81Cgg00]LFf1eFSP5P;g00a>RSg00a^RF'81b5;=6SFdAa8Q7C`b8b9b:X281;45,9P1;4U568^28P510=2#4O1b7b>b=b6C^P<P<P:P;CJ=>=7R2,0=,5ARA,19ePHP5E:PJ%M;E:PI%M:E:PEAN?0CE:A??DG,0?AN?DGE:%B2,0?/1AeX5BX1>X3<X<<P7P5O2n2001101010121100100X;=P5D]W1o"). Qed.

Lemma read_u64_bytes_in : forall mp a v,
  bytes_in mp a (le8 v) -> read_u64 mp (wa a) = Some v.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "p'0h01xi001xh12Hah21Rh36__sat1h41nh51Hh67__arithh74__ffh86__sat0h98__varmaph:5__with;1ah<1bh=2mph>1oh?1vh@1yi012bsp;1p;3p;2p;<p;4p;7p;6p;5g003Uj14Tg004:j1ETg004Xj1BTg00;NR0j1:Tg01]Hj16Tg00K[j3WTg00dVj10Tg00GLR1j1=Tg008ej19Tg00HIj2LTg00N8R2j23Tg00bnj1GTg005;j25Tg00gXl<]Tg00MPj2XTg00Hfj2<Tg00NTj3VTg00O8j2UTg00OYj1TTg0035j1CTg00VRj1STg00PWj1RTg00Q5j1QTg00Q`j2?Tg00X1j3PTg00Rfj4OTg00ZGj7NTg00T3j2KTg00TUj2JTg00B[j32Tg00UAj3ITg00U`j4HTg00fJj4MTg00Flj2@Tg01`Nj1ATg002<j6>Tg01O3j5FTg00IZj1;Tg01GOj27Tg01M6j38Tg00D3j21Tg00>lj6^Tg01baj1DTg00SQj1\Tg01caj1[Tg01e;j2YTg012_l<ZTg00^JR3g00]lR4P4P4P1P1f5R1f4R5f3R6f2R7f1R8f0R9M<Zp=_g007[#4R:#4#4R;#4#4#4R<#ER=#BR>%E;#BR?#:[%699W78%68R@P6P7P9P3g01<:#0#0#0#0#0#0#0#0RA%=9RB%9:R:%9<R<'LRC'3X43%=ARD/3CRE%9;R;/3CRFP4P4P2P9X04RGP21389#GX@4X04PDP;PGPG154BX03PAP;154;E_PCPC154CM<]1X:<g00[ORG/3:R21<G<13GC[RH[1<G:RIg00^iRJAV:<8UW11<GC\J^1IP8g00_E1UG:'5P2eO1PHg00_kRH#T%CH%S4%R4%Q4RHg00[mg00\LR2P2g00\lR2P41?4;g018_1?4:=P4=COg00]LFN1KH2P9P7g00a>R2g00a^RH'51J97=22HdAI4G8CHb7b9b:PFP9b6b3b8b3CMPEe1@?@RE%A8E>DF%C?RF#:RG%;7RH%=E,7=58611F@32P3%67R@,@?%;5R?17=B581%66RB,1FRE52GX43P9PA%A7E^%;617=D58511F@52GPGPE%:>REP0PFPEP9%D9,1>%\>n1011000002101010011>5R532X>GP>P611>9=2E5X<>11>6,5E%DB%[6E>17=;981?P9E>b2b21Y6H11>852EeW5X?>X;4W=o"). Qed.

Lemma wa_add : forall a (k : word), (wa a + k)%bv = wa (a + bv_unsigned k).
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h01ah11kh25lemmah31yp;1p;2p;3p;4p;6p;;p;9g003Uj10Tg004:j1GTg004Xj1=Tg01H5j27Tg01GOj24Tg00B[j35j1>Tg01f2j1<Tg00IZj11Tg01Aij32j1;Tg01fbj43Tg01gIj1:Tg01h8j49Tg01hoj3FTg01iej4ETg01jRj26Tg01k>j1ATg01kmj6@Tg01lXl;?Tg00Glj28Tg01mSl9BTg01nMj1CTg01oij2DTg00]lg007[#0#0#0#0#0#0#GR0#=R1f0R2,70R3,40R4=512P1%>1R5%<1f2R6#1R7f1R85201708R9,40R:9207P1P1^31R;P5P1P1P5P5C3R<%;0R=P;\1R>P1P;P5P<C3R?P1P;P<P1P1P5%:1C9C99F>?P=CEP71617P8P:P1P5%A1P:P8P2E@M;?1869#1R9P91619M9BW2%C21D83%18=2041883#1551eO2W1W0o"). Qed.

Lemma read_iovecs_aux_bytes_in : forall iovs mp a,
  bytes_in mp a (iovec_bytes iovs) -> read_iovecs_aux mp (wa a) (length iovs) = Some iovs.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "p'0h01Hh11ah22mph32H3h44__x1h51nh62H2h71bi001bh84iovsh91lh:1oh;1xi011xh<2H0h=7__arithh>4__ffh?8__varmaph@5__withA3bs1hB3bs2hC1zhD2H1hE2IHhF1mhG1pi021phH1yi034basei043leni051rp;1p;2p;3p;4p;6p;<p;5p;Bp;7g003Uj1ATg004:j1\Tg004Xj1QTg01[>R0j2`Tg0035j1NTg00;NR1j1KTg01[^j1GTg00K[j31Tg00IZj17Tg00Flj24Tg021=j3:Tg00D3j28Tg00B[j35j1tTg00OYj1]Tg005;j2HTg013mj3ITg01]Hj12Tg00h=j39Tg000ej3jTg01^Qj3fTg001Bj46Tg022;j4dTg002<j6=Tg00K@R2j2DTg01=bj4aTg00GlR3j20Tg00GLR4j1BTg00dVj1<Tg01`Nj1RTg00>lj6JTg008ej1OTg009Cj3PTg01Aij3ETg01e;j2CTg00SQj1_Tg01H5j2^Tg00bnj1sTg00cLj4rTg00gXl<[Tg00P9j2pTg00PWj1oTg00Q5j1nTg00RCj2lTg00Q`j2XTg00WNj3MTg00Rfj4WTg00T3j2kTg00TUj2iTg00UAj3hTg00U`j4gTg00fJj4YTg022Yj4UTg0242j2TTg01C[j5eTg01^nj4ZTg012_l<mTg0129lBcTg00ZGj7bTf5R5f4R6f3R7f2R8f1R9CZf0R:3Ip=F149:#Bp=;1089=17:p=3%B:,09p=Sf6R;P6P7P8P9CZ=I5:'8p=>g00]lR<?59:p=?1H<:p=@g00^JR=P<P<P<P4P4P5P6P7P8P9P:M<mp=qP<P<P<P<P<P<P3P:P9P8P3P7P6P5P;f7R3f8R4f9R>MBcp=LP9g00[mg00\LR?P?g00\lR?P:g00]LFbp=Vg007[R@#A#A#ARA#ARB#A#A#\RC#QRD/`DRE#NRFPE%\A#QRG#K\DRH%G8919:%KFRI%79RJ14E75:818F735[^1<]2RKX8F%]ERL#G919:18FL,HIW0X1<X2HP0PDPDAIE67#G919:AIE56R0,4E9:8J18F055I[^1<^2H\K^9FP:PEPDPDP5P6P7EF#G919:%NGR0%2;RJ%25RL59GPEPGAjDD:#2AfDD:#259GXGERMP6C6RN59GA178:X90P:A9GLN99GJROPGPJPLPNCdE=A189OP2A9G9:9178A1678P6P71;G8P9C3'D[ROA1789P7P81;G9P:C3'DA9G899167RN[A1567P5P61;G7P8C3'D\NP7P8P9P:CaP9n2001000000120000000XB0XA0X1<X2HRNPO^B0^A0^1<^2HR0P:P6P7%24RO%23PEPGPMP;C659GRLP9O5A167OP6P71;GOPLC3'DP2%2>RL9156P5P61;GLPEPGPMP3C699GOC3%75PEPDPDf:R5P>P4EFRO,4E5:;18FO55IP:f;RO#2RL913;P4P3f<R3#2,;GPEPGPMP5C699GLC3PNP0P:P5f>R0#2RN,;GRL,0>R>f=R4#2R;PEPGPMP3C6R6P9O5A15>;P5P>1;G;P6C3'DP2f?R2#2,4G,S5R6=1ONPOP6PLPEPGPMP4C6C3%7OPEPDPDf@ROP2P0EFRL,4E5:318FL55IP:P4P3fAR3#2,;GRL%2OC3P0fBR6#2RN,4G,S4PLPEPGPMPOC6C3P=fCRL#2R4,4GR;POP2%B:R>P4C3X5=P9g01<:#<#<#<#<#<#<#<#<R4%RLEJP2P0%B4R0PNC3P=fDRN#2,4GRJP310O>%BJPEPGPMPLC6RPC3X5=P9P4%RNRQEJPO1020%B;PEPGPMP6C6C3P=PJP61030RJP>PEPGPMPNC6C3X5=P:P4PQEJP310O0P0PPC3%KDRPfFRO,8DP1PDPIP:P1PDPI%7LRQ%OARAg00;2R;5PCR25EC,CNP1PFPIfERR%7N%OBRB=PC;R;5ECfGRS,4E3:PFPEPDPDP8P9P:F>%_FRTn10110100021010500PTn10110100021110400PTn10110100021110300PFPEPDPDPSPOPRF>RU55IX:PPD1^C2RV,03#7P1PDPI1CL:P1PFPIAECQ;14EORQ5:NPFPEPDPDfIRWP9P:F>RXPTn10110100021010500PTn10110100021110400=5IUX7DPD1^C;,03#7P1PDPI106V#7,CLP1PFPIA:N9QPXPTn10110100021010500PTn10110100021010400=5IUX7D103ARU/?JRX1?UUP<P<%t<RQP:X;<RVPQ1?9:#sXH<X;<RYPUPU%@UPJPUPVPVPVP<P<g01;V109:Cr#@XF<X5<RUP3P3%@3P0PAPVPV%@>X;=P4PA%@AEqR4M:LM<[g00_kR=#]R>%N=R=1p<9RJ%o<RZ%n<R[P<1l<@R@1X<AR\5M<R]g019FR^P]CW'V1k[?R?P:P8g00a>R_g00a^R`'H1i:8=5_`dg00[O=h<9CgR`b>b?b@X4<10:AR_/?_^4<P:P6O1b=CYPXP<1060%2S91N:XC<P7106ARXP:E=%2O91LXPP18DSP1PDPIP:P1PFPI10RBRX#7fHR8,4E5:ORaPFPEPDPDfKRbP9P:F>PTn10110100021010500PTn10110100021010400PFPEPDPDPWP8PSF>55IX:P10LBRP10L0Rc/00Rd'?Re10LARf/0ARg,?PP<P<PQPVPQPYPPPP%@PPdPgPVPVPVPUPcPfPVPVPVPUPLPL%@LP0PAP4M:LP0PAP4M:LM<[P>P=PJPZP<1X<B9M<@P^AM<]\CW,V[P?P`b>b?b@X4<10:B10_A'?^4<P:PNO1b=CYPeP<10N0/00PEPGPMP8C691O:XC<P710NBRBP:E=PEPGPMPSC691RBPI18F8P1PFPIP:PFPEPDPDfLPbP:F>PTn10110100021010500PFPEPDPDPbfJRbPWF>55IX:IPFPEPDPDPbPWP8F>,HIPaPSPOPXP:O3E=b3b0%7f,CNPNPfPSP:CUE=b6b0%73RS=EC;1T3;E=AECS21T32E=1C6SP6P3POP5CUE=PEPDPDPOPRPNEFRN,4E9:6S18FN55Ieb3b3b6W3W6P9P:O2n2001000000121000000b0b<W0WDP9P:O2n2001000000121000000b0b<b0W0X1<X2HXEKX8FX9DX7DP9P:O2n2001102010121100100X1EP:DeW8o"). Qed.

(* [comment removed for export] *)
Definition iov_ok (mp : word -> option byte) (iov : word * word) (bs : list byte) : Prop :=
  snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ Z.of_nat (length bs) < 2^64 /\ bytes_in mp (bv_unsigned (fst iov)) bs.

Lemma wa_unsigned_id : forall w : word, wa (bv_unsigned w) = w.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h01wp;1p;2p;3g003Uj10Tg004:j16Tg004Xj12Tg01nMj11Tg01H5j25Tg00IZj14Tg00B[j33Tg007[#0#0#0#0#0#0#6R0#2R1f0R2#11502#4=312eW0o"). Qed.

Lemma gather_iovecs_ok : forall mp iovs bufs,
  Forall2 (iov_ok mp) iovs bufs -> gather_iovecs mp iovs = Some (concat bufs).
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "p'0h01Hh14bufsh24iovsh31lh41bi001bh51oh62Hbh72Hlh84Hlenh92IHh:2_Hh;2bsi012bsh<2l'h=2mph>1xi021xh?1yi031pi044restp;1p;2p;5p;3p;4p;6p;9g003Uj17Tg004:j1MTg004Xj1FTg00;NR0j1ETg01[>R1j2WTg0035j1CTg025@j16j3GTg026Nj58Tg00OYj1UTg005;j2DTg013mj30Tg01^nj45Tg01^Qj3LTg00Flj24Tg00GLj13Tg01GOj2?Tg00B[j32Tg008ej1ITg00HIj2VTg00N8j2>Tg000ej3=Tg01H5j29Tg00K[j3<Tg00K@R2j2HTg01M6j3BTg026lj2@Tg00h=j3JTg00D3j2:Tg00SQj1STg00IZj1RTg002<j6ATg01O3j5OTg027hj1PTg00>lj6QTg029>l9TTg029^j2KTf5R3f4R4f3R5'@f2R6f1R7f0R8'K':32p=11K78,:6p=;1@67=258p=Ng007[#7R9#7#7R:#7#7#7R;#MR<#FR=%M:#FR:#E[1W==R>#CR?%C:R@#CRAP>P@%66P7P8D8P>P@%65%E@RBP3P7P@P:P8E1X1AX2?%U@9;@:,DBP1P=P=f8R1?G56P>P@f9RC#6P6P7D8PBf:RDP5P@P:P6E1PBf;REf6RF=0>4P@P:A0@35E1[[[^<A^3?^?@P8P=P=P4P5C5=GE6P2P=P=P3P4C5RG9L==14:5#3RH,?<52=%I9%I;'VR;,>Hf<RHA===G,9<;<5'HP>P@f=RG#6P5P6D8PBf>R9P4P@P:P5E1PBf?RIP=P=P1f7RJC5RK=0>3P@P:A0@F4E1[[P8P=P=PJPFC59L==14:3#3,?<52=14:F#3/>;A===K,9<=<IF'HP214:J#3/>;f@R2P=P=PCP1C59===,9<;<JP>P@fA#6PJPFD8PBfBP1P@P:PJE1PBfCRFP=P=PHPEC5RK=0>CP@P:A0@D1E1[[P814:C#3/>;A===K,9<=<FDP>P@fD#6PDPCD8PBfEPEP@P:PDE1P=14:G#3,?<RDP0P@PBfGRC?B28P0P@PBfH/@9AJ:78,:@%S@R2n10110200021010400RFP2n10110200021010100A0@9H9;@:RK52BX3=P=19<IR;#RR1P0P@PB14:9#3,?<9BC8PFP2n10110200021010100=2BKX4=PB1:@GP0P@PBP8PFP2n10110200021010100=2BKX5BPBA;@:EP0P@PBP8AJ:I8,:@P2n10110200021010400=2BKX5BA0@GE9;@:R:,DBfFRE/@HP8EAABE1DPGPEP;P6P5DOEAPI%PIEQP9PJEAPBPEP=P=PIP9C5=0>HP:CNeW9W:W6W8P7P8O2n2001000000121000000W0W7P7P8O2n2001000000121000000W0X1AX2?X;@X3=X4=P7P8O2n2001103000121100100X>>P6P7P8M9TW0W1W2W=o"). Qed.

Lemma iovs_total_ok : forall mp iovs bufs,
  Forall2 (iov_ok mp) iovs bufs -> iovs_total iovs = Z.of_nat (length (concat bufs)).
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "p'0h06__sat2h14__x1h21xh31Hh44bufsh54iovsh61lh72Hah87__arithh94__ffh:6__sat1h;8__varmaph<5__with=4__x2h>4cstrh?5cstr0h@1yhA1zhB2HbhC2HlhD4HlenhE2IHhF2_HhG1bi001bhH2bshI2l'hJ2mphK1ni011pp;1p;2p;5p;3p;4p;<p;7p;6p;9p;Bp;8g003Uj1>Tg004:j1WTg004Xj1KTg00;Nj1^Tg01[>R0j2xTg0035j1CTg025@j1=j3JTg026Nj5?Tg00OYj1MTg005;j26Tg013mj33Tg01^nj47Tg01^Qj3TTg01GOj2DTg00B[j3;j1\Tg008ej1RTg00HIj2dTg00N8j24Tg000ej3@Tg01H5j28Tg00K[j3ATg00K@R1j2GTg00Flj21Tg00GLR2j10Tg02:9j1FTg00GlR3j2:Tg029^j2BTg00h=j3LTg00b>j2OTg00bnj1[Tg00gXl<XTg00Lkj1VTg00MPj2wTg00NTj3vTg00O8j2uTg00P9j2UTg00VRj1rTg00W0j4qTg00PWj1pTg00Q5j1nTg00RCj2STg00WNj3mTg00Rfj4ITg00T3j2lTg00TUj2kTg00UAj3jTg00U`j4gTg00fJj4fTg00Q`j2PTg00SQj1eTg00X1j3hTg015Nj7iTg01H_j2cTg002<j6ETg011Zj3oTg029>l9bTg0129lBaTg012_l<`Tg00Hfj2_Tg00ZGj7sTg00Zkj8tTg00]lR4f3R5#Ff2R6f1R7f0R8'B'1#03;p=21B78,16#0p=N1178#0p=<%089;47p=]A;478p=5g00^JR9P9P9P4P4P4g017:P2P2P2P3g017Zf5R3f4R:P5P6P7P8MBap=ZP9P4P4P4P2P2P3P:P5P6P7P8M<`p=Yg00[OR2/_8p=9P7g00[mR;g00\LR<P<g00\lR=P8g00]LFsp=HP5P;P<P<P=P6P7P8Gtp=Qg007[R>#>R?#>#>R@#>#>#>RA#WRB#KRC%W@#KR@#^[1xCCRD#CRE%C@RF#CRGPDPF%=6P7P8D?PDPF%=5P7P@P@P8C2X4GX5E%MF9N@@,64P0PCPCf8R0?J56PDPFf9RH#=P6P7D?P5P@P@P6C2f6RI=3D:P@P@A3F35C2[[[^IG^6E^@FP8f;RJPCPCP:P5C7;J6P1PCPCP3P:C7RK9TCC1<@5RL,DB5;C%R?RM%RARA'dRN,4Lf<RLA@CCK,8B;A5'GPDPFf=RK#=P5P6D?P:P@P@P5C2PCPCP0f7R5C7RO=3D3P@P@A3FI:C2[[P8PCPCP5PIC79TCC1<@3,DB5;C1<@I/4Nf?R3A@CCO,8B;AI'GP11<@5/4Nf@PCPCPHP0C79@CC,8B;A5PDPFfAR1#=P5PID?P0P@P@P5C2PCPCPLPJC7RI=3DHP@P@f:RO=3F0C2[[P81<@H/4NfCR0A@CCI,8B;AOPDPFfD#=POPHD?PJP@P@POC2PC11@KRO#0RI,DBRP18B8%FKRQ':f>RR1B@LRS5L@,1@']X6CP91B@JRT,1@RU,OORV11@RRW#0RX,DB,8BRY/:Q%08RQ'5XK9P4%0URZ1:Y811@SRS,OW#0RY'5XA4P4PI%0S,:8/5YXA41:IZRY%0VRS'515YYP4P4%\4R[P8X24R\P[1578#[X@4X24PYPY164YPSPYP\P\164QX29PVPYPOPI164IPUPZ164ZEZEYM<X%VURU%9ZRZ%VWRW%9XRX1wMARO142MRY%9A142N[RV[R9%9MRQg00^iR\AvMA7UW7RA%9N\\^7QRQP7g00_E1u2M'6PYeO1RYPVg00_kR\#MRS%C\R\P41U46P7%r4Cq%p4R[%n4R]P41S4>R>1S4?5m4R?g019FP?CI'H1l]=R?P8P6g00a>R^g00a^R_'61k86=;^_dAj427CgR_b9b;b<X14X=41:87R^/5^^14^=4P8AN@@11<@0R0O2b8b0b:b0b?b>Cf18BPPUPZPWPXPOP9PAPQPYPVPSP\1U47P[P]P41P42g00`WP>CI,H]R2%e<R[P]P4P>g018_1P4M=h4BCI,H]RBP[P]P;P<P<P=P2PBFiCQCQP?P_b9b;b<X14%98147N%96146N'G[[^14P8P0P:PHO3b8b0b:b0b?b>,cIEE%FLP8EEAL@KT,1@Ao@KTEEPRP5EEPCPCP3PRC7=3DLP@P@A3FKJC2eWEWFWBWDP7P8O2n2001000000121000000W3WCP7P8O2n2001000000121000000W3X4GX5EXHFX6CXGCP7P8O2n2001101000121100100X2DP6P7P8M9bW3W4W5WJo"). Qed.

(* [comment removed for export] *)
Lemma read_bytes_aux_wr_at : forall segs m a n k,
  wr_at segs m a n -> Z.of_nat k <= n ->
  read_bytes_aux (wview segs m) (wa a) k <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "p'0h06__sat1h14__x1h24__x2h31ih42Hah53Hk0h67__arithh74__ffh86__sat0h98__varmaph:5__with;4cstrh<1Eh=1Hh>2H0h?2Hkh@2HnhA3IH'hB1ahC1nhD1xi001xhE1khF2H1hG1bi011bhH1oi021ohI1zhJ2HihK2IHhL1WhM1ehN1li031lhO1mhP4segshQ1yi041rp%0p&0p;1p;4p;2p;3p;6p;:p;<p;7p;8g0035j1ZTg003Uj1CTg004:j1\Tg004Xj1]Tg00;NR0j1eTg02;2j4zTg00GLR1j11Tg00HfR2j23Tg008ej1PTg00HIj2iTg00Glj20Tg00IZj12Tg00SQj1XTg00K@R3j2UTg02<=j2@j3OTg01?Wj38Tg00OYj1_Tg00D3j2=Tg00B[j3?Tg00>lj6NTg01Ulj2[Tg010Xj1JTg00dVR4j1;Tg005;j2DTg009Cj3hTg01Aij3gTg013mj3ATg00i1j2GTg00bnj1fTg00coj4MTg00Lkj1LTg00MPk200Tg00N8j2YTg00NTj3~Tg00O8j2}Tg00P9j2dTg00PWj1|Tg00Q5j1{Tg00Q`j2WTg00RCj2VTg00T3j2yTg00TUj2xTg00UAj3wTg00U`j4uTg00VRj1tTg00W0j4aTg00X1j3sTg00m2j3rTg00Rfj4QTg01BNj1qTg002<j6^Tg00e5j2RTg013Dj3`Tg00e^j2pTg008@j1oTg01?6j1nTg01Z]l:mTg012_l<bTg00gXl<vTg00ZGj7cTg00WNj3lTg00Zkj8kTg015Nj7jTg00[OR5f0R6'3p=4f2R7f1R8'0/36p=51Y86,U7p=9f4R9f3R:?O78;?6#Jp=>A?786#Jp=6AO:78=?96p=Eg00]lR;/D6p=:g00^JR<P<P;P;P4P1P1P:g01WaP7P8P6M<bp=FP<P;P;P;P1P1f5R1P9P:P7P8P6M<bp=KP;P;P2f7R4P2f6R2P1P9P:P7P8P6M<vp=IP7g00[mR=g00\LR>P>g00\lR?P;P8g00`WP6CQg00]LR@Fcp=7Al;86p=<P:P=P>P>P?P7P8P6Gkp=BP8P=P>P>P?P6P@Fcp=HP;P8g018_P6CQp=SP7P=P>P>P?P8P6Fjp=Tg005U#Zg007[R=#CR@#C#CRA#C#C#CRB#\RC#]RD%\A#]RA#eRE[P9P:P7P8Cz%18/37P3%49%P@RF%PBRB'iRG959:%46RH?969PEf8RIP41028#2%XARJD>[^3;'U%ZARK#eRL1@42%21RM;8:%XKRN36P8%42A542GA9H64PEf;ROf:RPf9RQ/08#2PJD>[^3;'UP3A5I4GA9H6IPEf<R3PO10P8#2PJD>[^3;1@OP%2QRR;84=6LNP6A5PQGA9H6OPEf?RSf>RTf=RU/08#2PJD>[^3;%48RVA578GRWA9H6:RXPEfERYfDRZ1018#2R[PJD>[^3;%11/3:1@YZ?8M2=6LN]?]=]@]4^C;^B;R\XE<PEPZfCR]P[PJD>\X^3;g01<:R^#1/3:%_A,=KR_=?LNR`PLP_P0PKp-0P6g00^iR_g01=ERan10110200021000000XMLS00g00;2RbPNP6ENPa1[a6S01bFW>%J`e1@Z]?8M^=6LNeW?W=X@WX4VXC;XB;PEfFR]PYP[PJD>\X^3;%;2#1/3:AO]YMPE1DE6PEfGS02P]%22P6DEP0PAPEfIRXfHS03%2IP6DEP0PAPLP8P0PKPLfKR[fJRZ'@R`%2P%P=Rc=hCb5gCS04;83AAA86,=KPNn10110000021010400PNn10110000021010100=6LN]<P8PEPZPXPR1=A6DEPD10PcRR#2RdP0PKPLfL/@[R[?86UAAA:6,=KPNn10110000021010400=6LNXGDPOPR1GQc%;3RR#1RD/3Q%13Re?5cQRfP6XD;Rg1386#fXQ;XD;RhPDPg106cRDXD;RiPeO1RjO1PgPg%16#:XD<RkPRPjPiP3Pe%:eCFEKPQPQ%:QGIP1CMRePf%LURj%1U#4RR200FBRl1Y5FRm%4B1Y5G[Rn[Ro%4FRpA~FB8V_W4RB%4G\_^4pRpP8g00_E1}5F'DPmeO1RmPng00_kR_#_Rq%Z_Rr1d;8%|;Rs%{;Rt1W;5Ru1V;=Rv57tRw%X>R>1W;cRx,<vRy97tuCB1yt?R?P6P7g00a>Rzg00a^R{'D1x67=?z{dAw;58CuR{b7b9b:X1;108cRz#4\H^1;P6f@R|PTO2b6b0b8b0b;b5PePfPjPRPlPoPBPpPmPnPqPrP;1d;7S05P8%t;S06CaR}PsPt1V;@R@,<v1W;F=s;CRC57tP>Ar;@xRF,<y=7tCCBP?P{b7b9b:X1;X2;A568G1G7cRC=5zG[^1;^2;P6PSP|PUO3b6b0b8b0b;b51GPc99H6%;TRz#1RG/3O%1TR~?5cOS07PgPhPGPgPiP~O1RGO1PgPgPkPzPGPiPTP~%:~CFEKPOPO%:OGIP4CMQ07%LS%1SR~#4PlPoPBPpPmPnPqPrP}PsP;1<x@,<vg019F1<y@CQ,HtP?P{b7b9b:X1;X2;10c8RT,0610D85?;^1;^2;P6P4fBRGO2b6b0b8b0b;b5103T103c/085?;P;10c7Rz,0UPEfOfN%26S07PJD>XI;PQPz%;SRz#1RQ/33A5~c3S08PgPhPQPgPiP~O1RQO1PgPgPkPzPQPiPSP~%:~CFEKP3P3%:3GIPICMQ08%L|%1|R|#4PlPoPBPpPmPnPqPrP}PsPt1SvF,Ht9TtwP>1<xvRw97tu1Sw@,Ht5TtCBP?P{b7b9b:X1;X2;1G8c99H6%4T?9T7[^1;^2;P6PGPIP4O3b6b0b8b0b;b5O210Uc/07P6ENb>WJX3;PePfPjPRPlPoPBPpPmPnPqPrP}PsPtA7ty@P>A7tvFCBP?P{b7b9b:X1;X2;13D8138C[^1;^2;P6PS%1GP1O3b6b0b8b0b;b5O6A8`d3=6LN10Oc#2=8[UPLP0PKA6L6NP0PKPLP8AAA26,=KPNn10110000021010400=6LN]AP61=K6=6LNAAA28,=K=?LNR2PLAAA47,=KQ00PbPNP6ENPaQ01bFW>%J2eWAXNKP6O1A6LNNRKP61DLNO1,[KWAn10110200021010300P8O1bHbAQ04%qPE^W<XGAP6O1PEQ03Q02%24PJDEP9P5%;PRA#1R2/34%1PRa?5c4RbPgPhP2PgPiPaO1R2O1PgPgPkPAP2PiPPPa%:aCFEKP4P4%:4GIP:CMPb%LO%1O#4PlPoPBPpPmPn%;^Rn#;,R;1R;n1R;^5`;5`;g01<Y'p=A_qPrP;Q06P8Q05CaPsPt%o=,V;R=97tuP>Pt1<=x=7tvP>A7tuu1Suv,Ht5TtCBCBP?P{b7b9b:X1;X2;A57c81355?957[\V^1;^2;P6P|PUP9P1O4b6b0b8b0b;b5P;PIPEPZPXQ07PJDEXI;P610I5%nIE^O3,[KW<n10110200021110101P6O1b<bH1@]Y%;478M=6LNeW?W=X@WX4VXC;XB;XK\XE<PPP3POP1P8P6PIM:mW=W@P8P6O2n2001000000121000000W>W4P8P6O2n2001000000121000000W?WLXE<XC;XB;WOWPo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive node : Type :=
| NWrite (fd : Z) (bs : list byte)                 (* [comment removed for export] *)
| NWritev (fd : Z) (bufs : list (list byte))       (* [comment removed for export] *)
| NOpen (path : list byte)                         (* [comment removed for export] *)
| NRead (fd : Z) (buf : Z) (count : Z)             (* [comment removed for export] *)
| NClose (fd : Z)                                  (* [comment removed for export] *)
| NIoctl (fd : Z) (req : Z)                        (* [comment removed for export] *)
| NSetTid                                          (* [comment removed for export] *)
| NExit (code : Z)                                 (* [comment removed for export] *)
| NBrk (req : Z)                                   (* [comment removed for export] *)
| NMmap (addr len prot flags : Z)                  (* [comment removed for export] *)
| NMunmap (addr len : Z)                           (* [comment removed for export] *)
| NMprotect (addr len prot : Z).                   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pure_input (no : Z) (args : list word) : SyscallInput :=
  mkInput (Z_to_bv 64 no) args (fun _ => None) (fun _ => None).

Definition node_input (n : node) : option SyscallInput :=
  match n with
  | NBrk req => Some (pure_input 214 [Z_to_bv 64 req])
  | NMmap addr len prot flags =>
      Some (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0])
  | NMunmap addr len => Some (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len])
  | NMprotect addr len prot => Some (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot])
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AtNode.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

Definition at_node (n : node) (ms : machine_state) : Prop :=
  match n with
  | NWrite fd bs =>
      ms_svc_pending ms = Some (Z_to_bv 64 64) /\
      (fd = 1 \/ fd = 2) /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 12 = Z_to_bv 64 (Z.of_nat (length bs)) /\
      Z.of_nat (length bs) < 2^64 /\
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) bs
  | NWritev fd bufs =>
      ms_svc_pending ms = Some (Z_to_bv 64 66) /\
      (fd = 1 \/ fd = 2) /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\
      (length bufs <= 1024)%nat /\
      Z.of_nat (length (concat bufs)) < 2^63 /\
      ms_rom ms = seg_rom segs /\
      exists iovs : list (word * word),
        bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
        Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                               bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs
  | NOpen path =>
      ms_svc_pending ms = Some (Z_to_bv 64 56) /\
      areg ms 10 = Z_to_bv 64 (-100) /\
      Z.ldiff (bv_unsigned (areg ms 12)) (O_CLOEXEC + O_LARGEFILE) = 0 /\
      ~ In (Z_to_bv 8 0) path /\
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0])
  | NRead fd buf count =>
      ms_svc_pending ms = Some (Z_to_bv 64 63) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 11 = Z_to_bv 64 buf /\
      areg ms 12 = Z_to_bv 64 count /\
      0 <= count /\
      wr_at segs (ms_mem ms) buf count
  | NClose fd =>
      ms_svc_pending ms = Some (Z_to_bv 64 57) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd
  | NIoctl fd req =>
      ms_svc_pending ms = Some (Z_to_bv 64 29) /\
      0 <= fd <= 2 /\ req = 21523 /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 11 = Z_to_bv 64 req
  | NSetTid =>
      ms_svc_pending ms = Some (Z_to_bv 64 96)
  | NExit code =>
      (ms_svc_pending ms = Some (Z_to_bv 64 93) \/ ms_svc_pending ms = Some (Z_to_bv 64 94)) /\
      areg ms 10 = Z_to_bv 64 code
  | NBrk req =>
      ms_svc_pending ms = Some (Z_to_bv 64 214) /\
      areg ms 10 = Z_to_bv 64 req
  | NMmap addr len prot flags =>
      ms_svc_pending ms = Some (Z_to_bv 64 222) /\
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\
      areg ms 12 = Z_to_bv 64 prot /\ areg ms 13 = Z_to_bv 64 flags /\
      areg ms 14 = Z_to_bv 64 (-1) /\ areg ms 15 = Z_to_bv 64 0
  | NMunmap addr len =>
      ms_svc_pending ms = Some (Z_to_bv 64 215) /\
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
  | NMprotect addr len prot =>
      ms_svc_pending ms = Some (Z_to_bv 64 226) /\
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\ areg ms 12 = Z_to_bv 64 prot
  end.

End AtNode.

(* [comment removed for export] *)
Ltac at_node_red :=
  cbn [at_node]; unfold areg; cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS];
  repeat match goal with
  | |- context [reg_get ?R ?r] =>
      let p := eval vm_compute in (bv_key r) in
      let R' := eval hnf in R in
      change (reg_get R r) with (match tget p R' with Some v => v | None => w0 end);
      cbv beta iota delta [tget]
  end.

Ltac split_spine :=
  lazymatch goal with
  | |- _ /\ _ => split; [|split_spine]
  | |- _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition eff0 (r : word) : resp := mkEffect r [] [].
Definition efferr (e : Z) : resp := eff0 (errno_ret e).

(* [comment removed for export] *)
Definition open_result (mo : Model) (ent : FdEntry) (eff : resp) (mo' : Model) : Prop :=
  (exists e, In e openat_errnos /\ eff = efferr e /\ mo' = mo)
  \/ (let fd := alloc_fd (m_fds mo) in
      fd_lookup (m_fds mo) fd = None /\ eff = eff0 fd /\
      mo' = with_fds (fd_insert (m_fds mo) fd ent) mo).

Definition nstep (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  match n with
  | NWrite fd bs =>
      eff = eff0 (Z_to_bv 64 (Z.of_nat (length bs))) /\ mo' = mo /\
      evs = map (WriteEv (Z_to_bv 64 fd)) bs
  | NWritev fd bufs =>
      eff = eff0 (Z_to_bv 64 (Z.of_nat (length (concat bufs)))) /\ mo' = mo /\
      evs = map (WriteEv (Z_to_bv 64 fd)) (concat bufs)
  | NOpen path =>
      evs = [] /\
      if (path_max <=? length path)%nat then eff = efferr ENAMETOOLONG /\ mo' = mo
      else match path with
           | [] => eff = efferr ENOENT /\ mo' = mo
           | _ => if path_eqb path dot_path then open_result mo FdDir eff mo'
                  else match fs_lookup (m_fs mo) path with
                       | None => eff = efferr ENOENT /\ mo' = mo
                       | Some _ => open_result mo (FdFile path (Z_to_bv 64 0)) eff mo'
                       end
           end
  | NRead fd buf count =>
      evs = [] /\
      match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
      | None => eff = efferr EBADF /\ mo' = mo
      | Some FdDir => eff = efferr EISDIR /\ mo' = mo
      | Some (FdFile p off) =>
          match fs_lookup (m_fs mo) p with
          | None => False
          | Some data =>
              let bs := file_read data off (Z_to_bv 64 count) in
              eff = mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) [] /\
              mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo
          end
      | Some _ => False
      end
  | NClose fd =>
      evs = [] /\ 3 <= fd < 2^32 /\   (* [comment removed for export] *)
      match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
      | None => eff = efferr EBADF /\ mo' = mo
      | Some _ => eff = eff0 (Z_to_bv 64 0) /\ mo' = with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo
      end
  | NIoctl fd req => evs = [] /\ eff = efferr ENOTTY /\ mo' = mo
  | NSetTid =>
      evs = [] /\ exists t, eff = eff0 t /\
      match m_tid mo with
      | Some t0 => t = t0 /\ mo' = mo
      | None => 0 < bv_unsigned t < PID_MAX_ENVELOPE /\ mo' = with_tid t mo
      end
  | NExit _ => False
  | NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ =>
      evs = [] /\
      match node_input n with
      | Some i => syscall_spec i mo (Ok eff mo' evs)
      | None => False
      end
  end.

Definition nexit (n : node) (mo : Model) (code : word) (mo' : Model) : Prop :=
  match n with
  | NExit c => code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) /\ mo' = with_halted code mo
  | _ => False
  end.

(* [comment removed for export] *)
Definition minv (mo : Model) : Prop :=
  fd_lookup (m_fds mo) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
  fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
  fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) /\
  (forall k c, fd_lookup (m_fds mo) k = Some (FdChannel c) -> bv_unsigned k < 3) /\
  (forall k p off, fd_lookup (m_fds mo) k = Some (FdFile p off) -> fs_lookup (m_fs mo) p <> None) /\
  (forall k p off, fd_lookup (m_fds mo) k <> Some (FdFileW p off)) /\
  (forall t, m_tid mo = Some t -> 0 < bv_unsigned t < PID_MAX_ENVELOPE) /\
  m_vm_lazy mo = [].   (* [comment removed for export] *)

Lemma minv_nolazy : forall mo, minv mo -> m_vm_lazy mo = [].
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "h01kh13offh21ph31Hh41ch52moh61tp;1p;2p;3g02=:j1LTg003Uj14Tg004:j1>Tg004Xj1=Tg00;Nj1;Tg02>Fj1ITg00D3j2@Tg00B[j30Tg01H5j2?Tg00N8j28Tg00K@j22Tg01[>j2BTg0035j1<Tg02?:j1KTg00OYj1JTg02@2j1:Tg02@fj25Tg02A^j2HTg010Xj1ATg02BVj2GTg02CNj1FTg02DAj2ETg00SQj1DTg02E6j16Tg008@j1CTg008ej17Tg01GOj29Tg02Enj31Tg02FIR0f0R1'@p=3g02GA%L1g007[R2#4R3#4#4R4#4#4#4#>R5#=R6%;6f2R7#I1@6130g00[OR8f1R9,?5R:'8g02H7,8:'2[]6R:1B66R;#<%K9%J;30R;g00><R<%;0R0f4#:/57R=1H91#330#A^16]2^06R>12:;R;1G91#3900=%>4#=#<R4#;f5#F/E7%D430#A[^16^2<^06R<12>;R;f3#:/59%61#35001?57%C2#7'8[^46^06R612<;R;%:9R9%73,95R3'5%63#3500R3126;R;%72,95R2,59%62#3500R2123;R;1958R8,59%68#3500122;;11313131313131W3W5o"). Qed.

Lemma minv_init : forall reserved brk mbase sp lim inp, minv (init_model reserved brk mbase sp lim inp).
Proof.
ltac2:(KReplay.run1 (kr_t_Nodes ()) [] "p'0h01Hh12H0h21kh31bi001bh42E0h53offh61pi011ph72E1h82E2h92H1h:1th;1ch<1eh=1ah>3brkh?1fi021fh@3inphA1lhB3limhC5mbasehD1oi031ohE8reservedhF2spi044chani052idi066offseti072rdi082ski092wri0:6writerp;1p;2p;4p;3p;6p;7p;8g003Uj1?Tg004:j1[Tg004Xj1YTg01[>j2UTg0035j1STg01GOj2RTg02E6j16Tg01^nj4NTg008ej1LTg00OYj1WTg013mj3KTg00;NR0j1JTg01H5j28Tg008@j1cTg00N8j23Tg02@fj2OTg00B[j30Tg02I@j6ITg02CNj1ZTg02DAj2GTg00SQj1MTg02A^j2>Tg02>Fj1XTg00D3j2FTg00K@R1j24Tg02?:j1VTg02J9j1CTg010Xj1DTg005;j2@Tg01T0j31Tg01T]j3\Tg00>lj6Tj7ej8dTg01Ulj2HTg00Ylj4;Tg02Jmj6bTg002<j6PTg02Klj6_Tg02@2j1^Tg02Ljj6`Tg02=:j1]Tg02BVj2aTg02FIR2f0R3'Fp=2f3R4f2R5f1R6'O;03p=91a63,F2p=<A0563#Dp=:1463,45p=7%C6/G3p=Eg00a>R7?063p=Ag00a^9073p=Bg01XE9073p==f4R8P4P5g00;2P6P3ETp=51G56=043p=Qg007[R9#?R:#?#?R;#?#?#?#[R<#YR=/U=R>#SR?g00]lg02Mi1U=2R@#SRAP=P2g00[ORB,R<RC%6CRDCNP=P2%L9,R<RE%6ERFCNP=P2%L:,R<R:%6:RGCN%W@5K@5K@5K@R@%J2RHP3PC%2DRDC9PHP3PE%2FRFC9PHP3P:%2GRGC9PHP5P6%63#2RIC918<5RJ%c9#LR9'3RK[^;=^2=g00><RL1O45RM1<63RN50H%[;#Y#SR;#JROf:RPf9RQf8RRf7RSf6RTf5RUEI#Z/G5%M;R;3:[^5=]6^2=1>63#2RV9:HM^5=^6L^2=%J=RMPSPTPUP8P4P5EI#X1F=3RW3018<6RX,3BRYg02H7RZ,3XR['4R\[^:=PTPUP8P4P5P6EI#V%W>R>50?R]'4R^373737XAAg00?HRA%C3PHP@PCPDC9R_PHP@PEPFC9R`PHP@P:PGC9RaPHP@P6PIC9RIPK[^;=^2=Rb1O@5R@=0HNRN1G85=:O;[^5=^6L^2=A0H@VR@#DRV^5=^6L^2=Rc;7^3737X?APM%M=RA1EU5=:O;\N^5=^6L^2=A0M6WP\[^:=/4]77c97ab97_`XDMP_1E85=:O;\N^5=^6L^2=R_A0MAWRWP\[^:=R\PUP8P4P5P6P3EIR]#V=0?>R^'4Rd,4cRe'4Rf,4bRg,4aRh,4`1@HDP`Ph1@HFPaPg1@HGPbPfA1<C5P71@73RfA1<C4Rb/A3P7A1<CU/A3P7PHP6PDP7PHA1<ETRgPFP7PHA1<:TPG%M2Ran0100000020000Rhn0100000020000n0100000020000%6U#250H18<S/39]0]4P6A1<C8R`#B%68#2Ri90HDP1A1<63#BA0=56[R1A0=63A1<56#BRj[A0=45\jA\<63P6n2001000000120000000X3=X==RjP1^3=^==R1P3PCPSP5O3A0=CSP=PC18<3/39X2=g00_Eg02Nc'@Rk18<C/39dPRP3ETb4b1W0W4%=`P7PHA1<EUR`PFP7PHA1<:UPGPan0100000020000n0100000020000Rl=0HiPgP7PfA1<ES/A3P7A1<EQ/A3P7PHP6PFP7PHA1<:PRgPGPan0100000020000n0100000020000%6Q#250Hf;Ri,8</39]0]7P6A1<ERRm#B%6R#2Rn90HFPjP1P3PEPiP5O3A0=EiP=PEA1<C3#=Ro13X9]4X2=A1<CE#=Pk18<E/39dW4f<RXP3PSFeb7b1W0W7%=mP7PHA1<:QPGPan0100000020000=0HnPgP7PfA1<:i/A3P7f=Rf91<:/A3P7PHP6PGPan0100000020000%6f#2Rf50Hf?Rg,8</39Rn]0]8P6A1<:XRm#B%6X#2RX90HGPjP1P3P:PgP5O3A0=:gP=P:A1<E6#=PK]7^4oX2=A1<C:#=A1<E:#=Pk18<:/39dW7W4f@P3PiPSGdb8b1W0W8%=mA0HaXPHPaP0P2p-0RXP3g01=ERmg00^iR9n10110300021000000X<HRkPfP3D5Pm1Hn3b1W0W8n0110000020100P3P5O2b8b3W0W7n0110000020101P3P5O2b7b3W0W4n0110000020101P3P5O2b4b3X0IX;=X2=P_PePbP7P7P7PHP3PDPln0100000020000Rl1<8450H1ESU=:O;]0P31<45Re90HDPO%CTP8P;CQR_PHPDP0P2PXP3P2PXP3P9PmPmPmPmPmPmPmPmPmn01102000:101042010110620101106201011062010110600101082010510:2010710900Pmn10110300021010200X<HR21<U8RIP6D5Pm1Hm3Rnb9W1%D_eW0P7PHA1<E8PFP7PHA1<:8PGPan0100000020000n0100000020000RE=0HeP`P7P7P7PHP3PFP7PHA1<:SR:PGPan0100000020000n0100000020000R<1<TU50H1EQS=:O;]0P3A0HFIPO%CRPTP;CQRePHPFP21<STR_P6D5PmPnb9W1%DeeW0A0HhIP:P7P7P7PHP3PGPan0100000020000RI1<RS50H1EiQ=:O;]0P3A0HG_PO%CPPRP;CQR;PHPGP21<QRRQP6D5PmPnb9W1%D;RPeW0A0Ha_PHPaPkPQP6D5PmPnb9X1;PPeW0n0110000020000P6O1b3W0n0110000020001P6O1b3W0n0110000020001P6O1b3X0NX5=X6LX2=PcPdPbP7P71>84#2Rb90HlPm]0P31>45#2Rl90HDPHPDP2PbP3D5PmPnb1W0A0HElP`P7P71>TU#2R`90H<Pm]0P31>U8#2R<90HFPHPFP2P`P3D5PmPnb1W0A0Hh<P:P7P71>RS#2RR90HIPm]0P31>ST#2RT90HGPHPGP2PRP3D5PmPnb1W0A0HaTPHPaPkPRP3D5PmPnb1W0n0110000020000P6O1b3W0n0110000020001P6O1b3W0n0110000020001P6O1b3X0@PVeX5=X6LX2=P\P^PYP[PMPAP0P=PXP3PmP9n10110300021000000X<M1F=6P3D5RMPm13BJ/H3b1PMPm13JZ/H3b1C;VWX:=1@?>C;C;C;C;C;C;C;%X]PUP8P4P5P6P3EbEP%Z]PUP8P4P5P6P3E_EP%^]PUP8P4P5P6P3E`EP%]]eW@WBXF=XC=X>=WEo"). Qed.

(* [comment removed for export] *)
Definition munmap_safe_b (addr len : word) (h : VmMaps) : bool :=
  if negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len then true
  else
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ) then false
    else
      let n := Z_to_bv 64 nZ in
      map_has (vm_maps h) addr n || region_free (vm_reserved h ++ vm_maps h) addr n.

Definition mprotect_safe_b (addr len prot : word) (h : VmMaps) : bool :=
  if mprotect_grows_conflict_b prot then true
  else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
  else if w_is0 len then true
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len)) then true
  else if mprotect_modeled_b prot then
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    (map_contains (vm_noaccess h) addr n && map_contains (vm_maps h) addr n)
    || (map_contains (vm_maps h) addr n && region_free (vm_noaccess h) addr n)
  else false.

(* [comment removed for export] *)
Section CEIL_NODES.
Context {RUNp : RunP}.

Definition mmap_safe_b (addr len prot flags fd off : word) (h : VmMaps) : bool :=
  mmap_modeled_b prot flags off            (* [comment removed for export] *)
  || mmap_noaccess_b prot flags off
  || (if w_is0 len then mmap_plain_anon_b flags
      else if mmap_fixed_noaccess_b prot flags off then
        let nZ := page_round_up_Z (bv_unsigned len) in
        if (two_pow_64 <=? bv_unsigned addr + nZ) then true
        else if negb (bv_unsigned addr + nZ <=? alloc_ceiling) then false
        else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
        else region_free (vm_reserved h) addr (Z_to_bv 64 nZ) && map_contains (vm_maps h) addr (Z_to_bv 64 nZ)
      else false).

Definition nsafe (n : node) (mo : Model) : Prop :=
  match n with
  | NMmap addr len prot flags =>
      mmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                  (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (m_vmmaps mo) = true
  | NMunmap addr len => munmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (m_vmmaps mo) = true
  | NMprotect addr len prot =>
      mprotect_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (m_vmmaps mo) = true
  | _ => True
  end.

End CEIL_NODES.

(* [comment removed for export] *)
Definition vm_only (m m' : Model) : Prop :=
  m_fds m' = m_fds m /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\
  m_tid m' = m_tid m /\ m_stdin m' = m_stdin m.
