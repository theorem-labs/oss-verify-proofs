(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac ITree Nodes.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Export Decode.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_SysStep () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem7reg_getC69OSSVerify5KrLib2K53Lib6MState5MSsvcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics5Riscv3Sem5is_x0C69OSSVerify5KrLib2K53Lib6MState>step_ecall_genC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv3Sem2w0I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesI47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK47Corelib4Init9Datatypes4list01C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@delivered_writesK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool;orb_false_rC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib7SysStep8in_rangeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K53Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3subC47Corelib5Lists7ListDef5skipnC69OSSVerify5KrLib2K53Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_nil_rC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List<length_skipnC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega7EnvRing5PExpr03C69OSSVerify5KrLib2K53Lib3MemEbytes_at_write_insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem9upd_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC69OSSVerify5KrLib2K53Lib3Mem;wr_at_writeC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula03I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC47Corelib4Init5Logic8iff_reflC69OSSVerify5KrLib2K53Lib3Mem>wr_at_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib7SysStepDrw_cells_CB_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9leb_spec0I47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z9ltb_spec0C47Corelib4Init5Logic3notc69OSSVerify5KrLib2K53Lib7SysStep@apply_zeros_specC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC47Corelib4Init5Logic9False_indC47Corelib4Init5Peano2ltC69OSSVerify5KrLib2K53Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib7SysStep=zeros_outsideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltc69OSSVerify5KrLib2K53Lib7SysStep@wview_zeros_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib7SysStepDbytes_at_zeros_otherC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib7SysStep;wr_at_zerosC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame6insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC69OSSVerify5KrLib2K53Lib5FrameBinside_not_outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7ro_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3MemAmem_inv_seg_belowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem:mem_inv_roC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem@mem_inv_ov_belowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem=mem_inv_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem4UTOPC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC46Stdlib9micromega;ZifyClasses3injC46Stdlib5Lists4List@nth_error_repeatC47Corelib4Init5Logic6eq_symc69OSSVerify5KrLib2K53Lib7SysStep<zeros_insideC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat7add_0_rc69OSSVerify5KrLib2K53Lib7SysStepBbytes_at_zeros_newC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib7SysStep?wr_at_zeros_newC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib7SysStepAapply_unmaps_specC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib7SysStep>unmaps_outsideC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib7SysStepEbytes_at_unmaps_otherC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib7SysStepBwr_at_unmaps_otherC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem;wr_at_belowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem>bytes_at_belowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem;wview_belowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6Decode8errno_ofC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7mod_addC45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC69OSSVerify5KrLib2K53Lib7RelSpecBerrno_ret_unsignedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00C35stdpp7tactics<f_equal_helpc69OSSVerify5KrLib2K53Lib7SysStep<swrap32_highC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MStateAunsigned_lit_wrapC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib7SysStep=swrap32_smallC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree4implC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree8impl_evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma evt_ecall : forall segs (Q : machine_state -> Prop) R F pc fc rv m ro w,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true ->
  Q (MSsvc R F (Z_to_bv 64 pc) (reg_get R 17) fc rv m ro) ->
  evt segs Q (MS R F (Z_to_bv 64 pc) fc rv m ro).
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01mh11Fh22HQh32Heh42Hfh51Qh61Rh72fch82pch92roh:2rvh;4segsh<1wp;1p;2p;3p;8p;7p;;p;6p;4p10000p4p710R0p1000Mp4p710p8P0g000iR0p4p710R1p8g001GR2p4p7210P1p8g0023j1MTg002Sj10Tg0038j19Tg003]j15Tg004;j18TP2j2KTg004^j17Tg005@j24Tg005fj2?Tg006hj2>Tg007Jj31Tg007dj1=Tg008dj1<Tg009Bj2LTg009ej3;Tg00:Hj23Tg00;2j82Tg00;jj7JTg00<_j1DTg00=ej1CTg00>Gj1BTg00?Oj2ATg00@Kj26Tg00ASj2:Tg00Amj1@Tg00BUl;ETP0j6FTg00CVj4GTg00D1j4HTg00Djj6ITg00Ec#Mg00FbR0p-0[g00Gi#0R2#9#5R1%02#0R2#0#0R3#0#5R4#8R5'KR6g00HN%53#8R3%75R7%52#8#7\5R8%73f9R9f5R:,44'?f0R;,>331g00HlR<f1R=#=g00IL31f:R>P9f8R?f7R@,44%92#<R2g00IlRA1L12d5;1RB,39f6RCP:f4RDf3REG2O1f<RFf;RGP>P9144?RHP@PCP:PDFJRIP>P9PH13>BP@PCP:PDG2RB%DI%C5RJ517%B0RK1AFIRIP>P9PHA;12ARA,3>R2P@PCP:PDG2,60R1311:7JPKP>P9PHP<P5%@Ag00JHP2n0100000020000P@PCP:PDG2,60PGP>144913GAP?P@PCP:G2,6091K;X0K1:K1PIPFP>P9PHP@PCP:PDPEf2P=M;EEFCGPFPGPBP;CHEIW2W3W4X<3X98W0W:W7W8X16W6W5W;o"). Qed.

(* [comment removed for export] *)
Ltac step_ecall :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w =>
          apply (evt_ecall segs Q R F pc fc rv m ro w);
          [ vm_compute; reflexivity | vm_compute; reflexivity | simp_regs ]
      | None => fail "no instruction at" pc
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nret_MSsvc : forall R F pc x8 fc rv m ro r ws zs us ci,
  nret (MSsvc R F pc x8 fc rv m ro) (mkEffectU r ws zs us [] ci)
  = MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4) fc rv (apply_writes (apply_zeros (apply_unmaps m us) zs) ws) ro.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01Fh11Rh22cih32fch41mh52pch61rh72roh82rvh92ush:2wsh;2x8h<2zsp;1p;2p;3p;5p;7g002Sj10Tg0038j1ATg003]j11Tg004;j14Tg001Gj2@Tg004^j16Tg0023j12Tg00Jmj23Tg008dj15Tg009ej38Tg00KMj57Tg005@j29Tg00L=j3:Tg00Lbj2?Tg00M[j2>Tg00NSj2<Tg00;jj7;Tg00ASj2=Tg00Gi#0R0#AR1#1R2%00R0#0R3#0#0R4#0#1R5#4R6'@R7%14#4%66%13#4R3#6\6R4%23,36#21366#2R3g00OL,36#2g00FbP2P6%01#5g00Il582f4f<D7f;f:%50,955:5f8f7f6f1'?f2'>f3'<f5F;'=W2X93W<W:X66X74W4W8W3X;6X56X07W1o"). Qed.

Lemma mkR_set_a0 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v,
  bvmap_set 10 v (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
  = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01vh12x1h23x10h33x11h43x12h53x13h63x14h73x15h83x16h93x17h:3x18h;3x19h<2x2h=3x20h>3x21h?3x22h@3x23hA3x24hB3x25hC3x26hD3x27hE3x28hF3x29hG2x3hH3x30hI3x31hJ2x4hK2x5hL2x6hM2x7hN2x8hO2x9p;1p;2p;Og002Sj10Tg003]j11Tg004;j13Tg0038j12Tg001Gj26Tg00OklO5Tg00ASj24Tg00Gi#0R0#0#0#0#0#0#1#3R1%20#1/61fOfNfMfLfKfJfIfHfGf0fEfDfCfBfAf@f?f>f=f<f;f:f9f8f7f6f5f4f3f2f1MO5'4X01XI1XH1XF1XE1XD1XC1XB1XA1X@1X?1X>1X=1X;1X:1X91X81X71X61X51X41X31X21XO1XN1XM1XL1XK1XJ1XG1X<1W1o"). Qed.

(* [comment removed for export] *)
Lemma apply_mem_none : forall m, apply_writes (apply_zeros (apply_unmaps m []) []) [] = m.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01mp;1p;2g002Sj10Tg003]j12Tg004;j11Tg004^j13Tg00ASj24Tg00Gi#0#0#0R0#0#0#0#2#1%20#1#3[R0f0,40W0o"). Qed.

Lemma apply_mem_write : forall m a bs, apply_writes (apply_zeros (apply_unmaps m []) []) [(a, bs)] = write_to_mem m a bs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01ah12bsh21mp;1p;3p;2g002Sj10Tg003]j12Tg004;j11Tg004^j13Tg0023j16Tg00P`j35Tg00ASj24Tg00Gi#0#0#0R0#0#0#0#2#1R1%20#1R0#3[R2%60f2f1f035,42W1X01W2o"). Qed.

Lemma apply_mem_delivered : forall m a bs,
  apply_writes (apply_zeros (apply_unmaps m []) []) (delivered_writes a bs) = write_to_mem m a bs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "p'0h01ah11bi001bh22bsh33bs0h41mi011lp;1p;2p;3g002Sj10Tg003]j14Tg004;j12Tg004^j16Tg0023R0j1>Tg00Jmj2<Tg00Qdj13Tg00Lbj2;Tg00M[j2:Tg00RDj28Tg00NSj27Tg00P`j31Tg007Jj39Tg00ASj25Tg00SIj3=Tg00Gi#0#0#0R1#0#0#0#4#2R2%41#2R1#6[R3%>1R4P0P1f3R01<22#3R5';/:5f2R5f0R6'8'7A1056593P6f1R0%31515,53f6f5A=10631,53X24X11P0P6O2n10110100020020100101W3X02W4o"). Qed.

(* [comment removed for export] *)
Definition in_range (a n : Z) (x : word) : bool :=
  (a <=? bv_unsigned x)%Z && (bv_unsigned x <? a + n)%Z.

Lemma apply_zeros_spec : forall m a n x, (0 <= a < 2^64)%Z -> (0 <= n < 2^64)%Z -> (a + n <= 2^64)%Z ->
  apply_zeros m [(wa a, Z_to_bv 64 n)] x = if in_range a n x then Some (Z_to_bv 8 0) else m x.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h06__sat1h12Hah27__arithh36__sat0h44__x1h51zh63Hanh72Hnh84__ffh98__varmaph:5__with;1ah<1bh=1mh>1nh?1xp;1p;2p;3p;6p;4p;7p;8g002Sj12Tg003]j1ETg004;j1CTg004^j1ITg008dj1DTg00Sij2VTg00TFj27Tg00Tbj2:Tg00U=j21Tg00UZj2?Tg00V6j25Tg00V`j29Tg005@j2=Tg00W=j26Tg00WZj24Tg00X8j28Tg006hj2WTg007Jj30Tg00ASj2;Tg00XUj1UTg000ij6<Tg00Y4j2PTg00Y\j3OTg00Z@j2NTg00Qdj1ATg0023j1MTg00Zaj2LTg00[?j1KTg00[]j1JTg00\Hj2@Tg00\kj2HTg00]Nj4BTg00^9j3GTg00^\j7QTg00=ej1RTg00_@j8FTg00_dj2STg00`Fj2TTg00a2j3bTg00aQj4aTg00bCj2`Tg00cBj1_Tg00d4j2^Tg00doj3]Tg00Jmj2ZTg00ekj4[Tg00SIj3\Tg00M[j3YTg00fKj7XTg00foR0f0R1'?p=3f1R2g00gMR3g00glR4P4g00hLR5P1g00hlFXp=>g00GiR6#2R7#2#2R8#2#2#2R9#ER:#CR;%E8R8#CR<#IR=[g00HNR>f2R?#3%D7R7%D9R9'VR@,7?':RAf4RBf3RC'1/?@P>f5RDg00HlREP=15:BRF,911=:D,5:,11,6F'4g00iLRG'81=80,W<R<f7PBO1R8n0100000020000PEP=f6RH/9FRI11HD,6F'4P<P8n0100000020000RJ50=X5>P>PBPEP=11H1,6F,4I/8GP<P8n0100000020000=0=JX5>PE15:CRI,9D11DB,6I'4RFPEP=P1P<P8n0100000020000=0=JX<EPEP=PFP<PHPCO1RJn0100000020000,;=18FG%UFE<1=:BRF,5:R81P79RK1707RL%39170@[RM[RN%37ROg00ilRPAO792UW1R9%3@\P^1OROP2g00jH1N07';PLeO1RLPMg00jnRP#A%MP1L>2%K>%J>RPP3P4P4P5PPP3P4P4P5P>1@>0g00kZ1H>6R6CB,>PP>P6g00lA1@>7=G>:CB,>PFQR7%R4P7GF1SP5P1P?g00ILRP,;E1T1?=0EPdAb>02Cab8b9b:X4>R0%31171@':%32172@':[^4>R@P1f8PDO2b2b0b3b0,`BE<%_DR2,5:R:PKPNP9POPLPMP0P@P1f9PHO2b2b0b3b0,^DE<PEP=19:I11:8,6I'4/8GP<PJn0100000020000PEP=A]DBCP<PJn0100000020000RJ50=e1Z;;R<P;P;P2PFC[%A<3\=YHC=0=JeW6X7AW1X?;X>>W;W=o"). Qed.

Lemma apply_unmaps_spec : forall m a n x, (0 <= a < 2^64)%Z -> (0 <= n < 2^64)%Z -> (a + n <= 2^64)%Z ->
  apply_unmaps m [(wa a, Z_to_bv 64 n)] x = if in_range a n x then None else m x.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h06__sat1h12Hah27__arithh36__sat0h44__x1h51zh63Hanh72Hnh84__ffh98__varmaph:5__with;1ah<1bh=1mh>1nh?1xp;1p;2p;3p;6p;4p;7p;8g002Sj10Tg003]j1ETg004;j1BTg004^j1JTg008dj1DTg00Sij2WTg00TFj24Tg00Tbj2:Tg00U=j22Tg00UZj2=Tg00V6j26Tg00V`j29Tg005@j2FTg00W=j25Tg00WZj27Tg00X8j28Tg00=ej1CTg007Jj33Tg00ASj2;Tg00XUj1VTg000ij6<Tg00Y4j2STg00Y\j3RTg00Z@j2QTg00Qdj1@Tg0023j1NTg00Zaj2MTg00[?j1LTg00[]j1KTg00\Hj2?Tg00\kj2ITg00]Nj4>Tg00^9j3HTg00^\j7OTg00_@j8PTg00_dj2GTg00`Fj2TTg00a2j3UTg00aQj4aTg00bCj2`Tg00cBj1_Tg00d4j2^Tg00doj3]Tg00Jmj2\Tg00ekj4YTg00SIj3ZTg00Lbj3[Tg00fKj7XTg00foR0f0R1'=p=1f1R2g00gMR3g00glR4P4g00hLR5P1g00hlFXp=Ag00GiR6#0R7#0#0R8#0#0#0R9#ER:#BR;%E8#BR8#JR<[g00HNR=f2R>#1%D7R7%D9R9'WR?,4>':R@f4RAf3RB'2/=?P=f5RCg00HlRDP<16:ARE,911F:C,6:,21,5E'7g00iLRF'8%C8R8f7PAO1RGn0100000020000PDP<f6RH/9ERI12HC,5E'7P8PGn0100000020000RJ53<X5=P=PAPDP<12H1,5E,7I/8FP8PGn0100000020000=3<JX5=PD16:BRI,9C12CA,5I'7REPDP<P1P8PGn0100000020000=3<JX<DPDP<PEP8PHPBO1RJn0100000020000,;<18EF%VEE<1F:ARE,6:RG1S79RK1407RL%19140?[RM[RN%17ROg00ilRPAR792UW1R9%1?\P^1OROP2g00jH1Q07';PLeO1RLPMg00jnRP#@%NP1M=2%L=%K=RPP3P4P4P5PPP3P4P4P5P=1?=0g00kZ1I=6R6C>,APP=P6g00lA1?=7=H=:C>,APFOR7%C4P7GP1GP5P1P>g00ILRP,;D1T1>=3DPdAU=02Cab8b9b:X4=R0%11141?':%12142?':[^4=R?P1f8PCO2b2b0b3b0,`AE<%_CR2,6:R:PKPNP9POPLPMP0P?P1f9PHO2b2b0b3b0,^CE<PDP<19:I12:G,5I'7/8FP8PJn0100000020000PDP<A]CABP8PJn0100000020000RJ53<e1\;;R8P;P;P2PECY%@83Z=[HB=3<JeW6X7@W1X?;X>=W;W=o"). Qed.

Section MemEffects.
Variable segs : list Segment.

(* [comment removed for export] *)

Lemma rw_cells_CB_prefix_write : forall m A n junk bs,
  rw_cells segs m A [CB n junk] -> (length bs <= n)%nat ->
  rw_cells segs (write_to_mem m (wa A) bs) A [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)].
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"] "h04__x1h14__x2h24__x3h33Hj0h45Hlen0h57__arithh64__ffh74__p1h88__varmaph95__with:4__x4h;4cstrh<5cstr0h=5cstr1h>1nh?1Hh@2H2hA1xhB2z2hC2HbhD1WhE4__p2hF4__x5hG1lhH1mhI1AhJ2H3hK2HjhL4HlenhM2HwhN3HwfhO2_HhP2bshQ4junkhR1yhS1zhT2z3p%0p&0p;1p;4p;2p;3p;6p;9p;7p;Bp;<p;8g002Sj1ITg003]j1|Tg004;j1vTg004^k104Tg0023j1}Tg00Qdj1jTg00lhj4TTg00maj4^Tg00n[j1STg00oWR0j10Tg0107j4OTg010lj21Tg011LR1j2RTg00cBj1<Tg00P`j3?Tg011fj2HTg012=j3XTg012[j1dTg013Uj1cTg014Rj4;Tg015Jj3`Tg015gj2wTg000Mj6_Tg00TbR2j23Tg00ASj2@Tg016Ej26Tg007Jj1uj3UTg016bk203Tg017Ek302Tg00UZR3j24Tg017bj4nTg018Ij1\Tg018nj2[Tg00TFj2KTg019Pj2ETg019jj1QTg01:Ij2FTg01;2k10JTg01;Pk20ITg01<1j3mTg00Zaj2YTg01<Zk10ETg01=8j4NTg00[?k10DTg00[]k10CTg00\Hk20ATg0038j1xTg00\kj2MTg01=Vj3aTg00=ek10@Tg00_dk20?Tg00`Fk20>Tg00a2k30=Tg00aQk40<Tg01>9j4iTg01>dk30:Tg000ij6tTg00CVj4ZTg01?ER4k109Tg01?ej2CTg01@<j2sTg00U=R5j2LTg01@Yj3VTg01A<m907Tg01BAj3eTg01C:k106Tg01C[k705Tg01DVk20;Tg00SIj3PTg01ENlBfTg01F4l<qTg01FYj3lTg01GBj2bTg00]Nj4gTg00fKj7yTg00^\k701Tg01Gnk70BTg00_@k800Tg01HRl<~Tg01I7k60FTg01I[R6f2R7f1R8+0;f0R93Pp=2g00OLR:?U89p=9g00foR;/s9p=Ag00HNR<?U89p=5P:P:P:P<P<P<g01JSP0P0P0f6R=g01K3f5R>f4R?f3R@P7P8P9MBfp=zP:P<P9P0P8P7P@P?P>P=f7RAf8RBM<qp=hP:P<P1P0P3g01KZP>P?P@P7P8P9M<qp=oAU<9;p=JAl<89p=:Al<89g01L<R3'bp>0Hg00jnR1Al<78/b3;P9p=>AP1899P17p>0G1b83=P19p={P<P8g00lAP9Cgp=kP8g00gMR3g00glRCPCg00hLRDP9g00hlREFyp=8P7P3PCPCPDP<P8g01LhP9CgPEFyp=7P7P3PCPCPDP8P9K01p=BP<P8g00kZP9Cgp=DP7P3PCPCPDP8P9K0Bp=WP@P3PCPCPDP7P8P9L00p==P<P:P<P<P4P7P0P8g01MOP;P;P9M<~p>08P:P:P:P<P<P<g01N<R4P0P0P0P5g01N\REP>P?P@P7P8P9MBfp=rP8P3PCPCPDP9J0Fp=]1L9;p=GP:P:P:P<P<P<P4P0P0P0P5PEP@P7P8g01O?REP;P9MBfp=pg00GiR5#IR0#IR4#IR3#I#I#I#|#v%|3#vR3$04[%}3RFp,4segsRGP?P@%j6R69278CTP2PGP>P?A2@76RHC^PGP>P?%SH#0CO1137/R?PG%<==?A@P=113@RH1H>HAX3H?;2672@CT[P9PGPAP=A2>?6C^P2A2=>6RH#dPGPBPA%cHC;PGf9RHPBA2A=6#S#0CO113=/RBPGf;RIf:RJ#<;?APJ113ARK1HHKAX3KB;2672ACT[[P9A2BA6#dPGPIPJA2HB6#cC;PGf<RKPIA2JH6#S#0CO113H/RIP2113IR2/9Kg00ilRHPGf?RJf>RL#<;?IPLf=RM/H2AX32K;26922ICTP@113M/9LPF%j3RL9`3JPGfCRMfBR2P9C;XGFP=PJ1w3JE_PGP2fARIPJC;PG%<2=?MJRKP2113JRN1HINROf@RP9X3NRQ;2672JR6C^PGPKP2%S6#0COS00%d6RRPGPKP2%c6C;S0119NN113QR6/9ORK/3H1@:NPKPHP:113PRK/HNRS1H2KRT,99X>:19SO%0KRU%0NRV'6#ARW%0IRX/6V#ARY'5%u:RZ%u<R[%08%09S02'5198920389402XR:XA:R\PSPW1689#AXH<X><RWPKPU1@<US03PNPV1@<VRSFzPOPYPWPIPX1@<XRWPNPVPSFzS04M9h1RNI14VXR]PNPVPSPIPXPWEoP>CnR^P]113IR_/92%0_R`%02Ra'5RbPZP[P\P_P`1@<`P2Pa1@<aM9hP@CnRaPb%\_R_14;`R`fDRc#\Rd%0c,4;Re113cRf#\Rg%0fRf,4;RhfFRi#0/6fRf,[;S051K;f%AfRj/5f'314f;%Jj'3'ES06fGRj#0fERf,13#0'6#AS07P<113j#0Rj113i#0'6Ri,[;1K;i%AiRk/5i'314i;%Jk'3'EfH,13#0S08/6j#AP<%QERk#QRi#QRl#QRm,F<Rn&0J5-0I<Ro1F<iRi5m<Rp1F<ERq':RrAm<onRs1:iq':Rt%Qm,F<Rm1F<lRl1F<kRk9m<oRo':+0HRu1:kqRv,:pRp1:oq,:i1:lk%j1Rk5>m9>mt5>s5>n80Gu'{3>%}1R1P<P<1Y<?P7&0E<RuCNRnP8P<1Y<>P@PuCNCN&0D<Rs&0C<Rm20A<;Rt%x0,M<Ro%x5,M<Rq5a<Rw'k,8m1M<5R5=7mw5Bm1Dwt,8mA7m5tRw5Bm5Wm&0@CRCPm1M<4R4=a<qRx,kt,8m1M<0R0=7mx5Bm1Dxt,8mA7m0t5Bm5WmPCPmA7mo4PCA7m50C=C=C=20?mDRDP9P7g00HlRog00ILRx'@20>97=UoxdB0=<;8H0<Rxb6b8b9X0<X1<X2<X:<XF<16?7Ro,K;159o'314o;%J9Ro'3'E16?@Ry,K;157y'314y;%J7Ry'3'E15=>15@?Rz[[[^0<^1<^2<^:<^F<P9fJ,13#0fK#0fIR{,13#0P@P8P7P?PBO8b5bTbJbBb@b=b<b;b3b4CiP6B0:3NPEtg00IlCZCZPRePFPQPG%<MS09=?cPRRPMA`3P9C;XGFPGPMP2PPP;PJP9P^P]PaPbP_P`PdPePgPhPkP1PuPs1Dtt,8mPDPxb6b8b914;;RuP9b5b=b<b;b3b4&09;R6/CNRB/RKR|1s;;R}/LVR~/4UPBP~P6P}P9XA<%A9XA<1@<;R~408PNPVPSErPKPUQ03EoP^P]PaPbP_P`PdPePgPh1[;;1K;;RU%J}RB'313uB'EP}P<p-0R}A>lpkP1P<PnP81Y<@RnCNPsPm1ktt,8m1]m=5Bm1]mA=Bmw5WmPCPmA7mq4PCPm1D04,8mPCAV<50/Dq,8mC=C=C=PDPxb6b8b9X0<X1<X2<X:<X7}WE13U?13>o'E14@>1L@?/4>[\z[^0<^1<^2<^:<^7}^E}P9Pu%J8%0{R{Q08PjP8P7P=PAO9b5bBb@b=b<b;b3b4CiP|eN907PG%G2#<=?MJP2AeP6JC;P<%GMPG%<9=?fIPcAe26IC;XS<P9PM&06ME_PGPRPMAeI6PC;P9bDbDA`3QL1w3QEtQ01eCZ1CIERQ1COER3,CNRL'9R6%GXRR%GYRJ,LVR|'5PZP[P\PQPRPIPXPWP~CpPLP|PNPVPSP3PJPOPYQ04P~CpErM9hP^P]PaPbP_P`PdPePgPhQ05Q06Q07P<1{rk9>iv9>lrP1P<1Y<7P8PnCNPsPm1]m>Aa<50R>97mq5Bm1D>t,8mA7mqt5Bm5WmPCPm1D05,8mPCAV<5tAV<qt9V<057mC=C=PDPxb6b8b9X0<X1<X2<X7}1698Rx,57,3@14x;/3y'E1478%G7%G?,L@'5[[^0<^1<^2<^7}P916{j,K;P8PjP{P7PAO6b5bBb@b=b<b;b3b4CiP6P:1C2ER2PG%<c=?fIPcQ02COX>:PGPcPM%02Q09PPPAK051CTE,CKP9E_b?Q00eCZbCXOHWKP8P9O2n2001000000121000000WLWMWCWNP8P9O2n2001000000121000000W?P8P9O2n2001000000121000000W?XPFWQX>:XI<WHo"). Qed.

Lemma rw_cells_CB_store_ok : forall m A n junk k,
  rw_cells segs m A [CB n junk] -> (k <= n)%nat -> store_ok segs m (wa A) k = true.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"] "h01xh11Ah23Hk0h37__arithh44__ffh58__varmaph65__with74__x1h84__x2h94cstrh:5cstr0h;1Hh<2Hkh=2Hwh>2_Hh?4junkh@1khA1mhB1nhC1yp;1p;2p;3p;4p;<p;8p;9p;6p;7p;Bg002Sj13Tg003]j1CTg004;j1?Tg004^j1KTg0023j1GTg01DVj25Tg00Qdj1ATg00SIj36Tg00lhj4UTg00maj4=Tg00n[j1;Tg00oWR0j11Tg0107j4>Tg011LR1j2:Tg00cBj1ETg01O^j4DTg00U=R2j24Tg01?ej2YTg00UZR3j20Tg00ASj22Tg017bj4WTg018Ij1@Tg01<Zj1VTg00[?j1TTg00[]j1RTg00\Hj2QTg00_dj2LTg00`Fj2JTg00a2j3MTg00aQj4NTg01P^j1ITg01F4l<<Tg00Zaj2HTg01=8j4STg00\kj2FTg00=ej1dTg01@Yj3BTg00_@j8cTg01>9j4bTg01Q<l9aTg01C:j1`Tg000Mj6_Tg007Jj3]Tg00]Nj4\Tg00fKj7[Tg01ENlB^Tg01HRl<ZTg00HlR4f0R5g00ILR63]p=8g00OLR7g00HNR8P1P0P3g01KZf5R1f4R9f3R:f2R;f1R<P5M<<p=XP8P<g00kZP5C\p=7P<g00gMR=g00glR>P>g00hLR?P5g00hlF[p=9P7P7P7P8P8P8g01N<P0P0P0P2g01N\P:P;P<g01O?R2g00foR@P5MB^p=OP7P8P8P8P0P0P1P9P:P;P<P5M<Zp=Pg00GiR0#3RA#3#3RB#3#3#3#C#?%CB#?RB#K[%GBp,4segsRBP9P:g01I[RC15;<%ACRD36CUg00TbPBP1P915:;=6CDREC=PBP1P9%;E#1C>1:;9PBf7REf6RF#EP:CD#8[P5PBPEPF1519=6CDC=PBf8R9PE15F1=6CD#;#1C>1:1EP8f9R1/4@PBf;%E5PECD#8X18PBf:RBP11Y92R2#1RDP@PFP<1:F9%1FRC%19RG'0RHPFPC128CP9PG128GRFEXP5CWRIPH%@ERJ%1E,0@RE%@BRK%1BRB,0@RLg00jnRM#ARN%GMRM%V8RO%T8RP%R8RQ1Q8@RR/7R'91LQ?RSP5P;12461J5;#8dAM8@<CNR6b4b5b610@@P5b3b:b9b214@CRC/0D14G@R4,0CP8P8P3P5X08RTP310<5#IXC8X08PCPC128CPDP4PTPT%15,28X07P2P4P9PGPF128@COEPM<<PIPHPJPEPKPLPNPMP81H8;P<POCSPPPQP=P>P>P?1F80R01F8ARA'7,9Q%d>AB8R0AB8AR'7,9QGcPSP6b4b5b6X78X88105<14@<14;@'0[^78^88P5f<#1PBP:O3b3b:b9b2CbM9aP1%`1E_W<W=W>P<P5O2n2001000000121000000W;X@7W?XB7X18WAo"). Qed.

Lemma mem_inv_syswrite : forall m A n junk bs,
  mem_inv segs m -> rw_cells segs m A [CB n junk] -> (length bs <= n)%nat ->
  mem_inv segs (write_to_mem m (wa A) bs).
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"] "h01Ah12bsh24junkh31mh41np;1p;2p;3p;4p;7p;6g002Sj10Tg003]j13Tg004;j12Tg004^j14Tg0023j1>Tg01R:j2;Tg01DVj2:Tg00Qdj15Tg00SIj36Tg00lhj47Tg010lj21Tg011Lj28Tg00cBj19Tg01S1j7=Tg01T9j6<Tg00Gi#0#0#0R0#0#0#0#3#2%30#2R0#4[g00HNg00OL%>0R1p,4segsR2f4R3';P2f5R4P3g01I[R5f3R6f2R7':%5536C71107/83P2f7R2f6R5#9P6P7P2P5P4P31106f1f0F=E<UUUX11W2W4W0W3o"). Qed.

(* [comment removed for export] *)

Section Zeros.
Variables (m : word -> option byte) (a n : Z).
Hypothesis Ha : (0 <= a < 2^64)%Z.
Hypothesis Hn : (0 <= n < 2^64)%Z.
Hypothesis Han : (a + n <= 2^64)%Z.
Let m' := apply_zeros m [(wa a, Z_to_bv 64 n)].

Lemma zeros_outside : forall x, (bv_unsigned x < a \/ a + n <= bv_unsigned x)%Z -> m' x = m x.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h01bi001bh11ri011rh22Hah34__p1h46__sat2h54__x1h64__x2h74__x3h82a0h91li021lh:2n0h;1Hh<2H0h=2H1h>2H2h?2Hxh@7__arithhA4__ffhB6__sat1hC8__varmaphD5__withE2l0hF2n1hG1ohH1xi031np;1p;2p;3p;4p;7p;6p;8g002Sj15Tg003]j1GTg004;j1DTg00V6j23Tg00TFj22Tg00U=j2;Tg00UZj21Tg019Pj2@Tg004^j1QTg00doj3NTg005@j2<Tg006hj2ITg007Jj30Tg01U6j2fTg00V`j2ETg01UYR0j2CTg00W=j2FTg00WZj24Tg01V<j2XTg008dj1ATg00Y4j2WTg00Sij2VTg00Y\j3STg00TbR1j2?Tg00Z@j2RTg00ASj28Tg00Qdj1>Tg0023j1PTg00Zaj2=Tg01=8j4MTg00[?j1LTg00[]j1KTg0038j1JTg00\kj29Tg01@Yj3OTg00]Nj46Tg00=ej1HTg01Gnj7TTg01I7j6UTg00_dj2eTg00`Fj2dTg00a2j3cTg00aQj4bTg01V_j1BTg00Jmj2^Tg00cBj1]Tg00ekj4\Tg00SIj3[Tg00M[j3ZTg01W8j7_Tg000ij6YTg00fKj7`Tg00_@j8aTf1R2g00gMR3g00glR4P4g00hLR5f0R6g00hlF`p=7f3R7P3P4P4P5f2R8P2P6Gap=:g00GiR9#5R:#5#5R;#5#5#5R<#GR=#DR>13=6R?p,1aR@'2p,1nRA,;@RB/1?'@%G;R;#DR?#QRCg00HlRDPCAN@A2g00foRE,<;,I?R?p,1mR;P2O1RFn0100000020000RGP;P8O190C6XGC13=2RH,f@11@H1E@H'C13=8,E@PDP013=7,1@PDPCf5RH,3=RI/FBRJ,42P?P;PHO1RKn0100000020000=0CKP2f4RK,3=,1@RL1XIBRM12IB/CJRJf6RI,3=/FBRNPDP0f7,3=/2BROPDPCg00ILRP/42P?P;f9O1RQn0100000020000=0CQP2f8,3=/2BRB%A:RR%A<R<'W12ERRS11E<1VR<RT,2E[RU[11ERRVg00ilRWASR<2UW211ET\W^2Vp,2HaRV11E@RW12@TR<'?P1PWP<P;f=O190C?P6p,2HnRX11EARY12ATRT'?P1PYPTP;fBR1O190C?P6f;g00jH1RER'8PSeO1PUp-0RUg00HNRSg00jnRR#>%PRPS1=S8P21=S7CM%LS%KSRRPS%J9,9SRZg00lAR[19S9R919S:5OSR:C6,7R%H4R\PRPSP9g00kZR]PZC6,7RP\PRPRP3P4P4P5PSPZP[P9C6,7RPSP:P]PZC6,7RFTP\PRP3P4P4P5PHEUC:C:C:1eR5P6P818DP1d68=0DPdAcSE2CbbAbCbDX5SX6SW7W31;62,28112712K81;87/1K'@PI[[[^5S^6S^7S^3UP6P;fGRUO190C?13=UPAP@f>P1fFO7b@b4X>TX=YP2P6O2n2001000000121000000b8X<<X;WP2P6O2n2001000000121000000b8bBb4PDPC14PPP?PQn0100000020000=0CQeWEP6O1%BBRW18CQR<PDPCg00iLRY,4PP?PQn0100000020000=0CQeW:P6O1n10210010100021110210103b0b1W9P6O1%BLPMPJPNPDP0POPDPC14Y2P?PQn0100000020000=0CQP2P<PDPC14YPP?PQn0100000020000=0CQeX9BP6O1P<PDPC14YYP?PQn0100000020000=0CQeXFWP6O1n10210010100021010210103b0b1W:P6O1n10210010100021110211103b0b1A0CGFe1^>>RGP>P>%]@1<=AC\%>G3[=Z;2P;P@PAP2PVPXp,3HanF_EYp,2m'P2O1=0CFeW?WHo"). Qed.

Lemma zeros_inside : forall x, (a <= bv_unsigned x < a + n)%Z -> m' x = Some (Z_to_bv 8 0).
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h02a0h16__sat2h24__p1h34__p2h44__x1h54__x2h61Hh72H0h82H1h92H2h:1bi001bh;1ri011rh<2Hah=7__arithh>4__ffh?6__sat1h@6__sat3hA8__varmaphB5__withC4__x3hD1li021lhE2n0hF2HxhG2l0hH2n1hI1ohJ1xi031np;1p;2p;3p;4p;7p;6p;8g002Sj15Tg003]j1JTg004;j1ATg00V6j23Tg00UZj21Tg00U=j2;Tg00TFj22Tg00TbR0j26Tg004^j1TTg00doj3QTg005@j2>Tg006hj2LTg007Jj30Tg01U6j2jTg00V`j2HTg01UYR1j2ETg00W=j2DTg00WZj24Tg01V<j2YTg00ASj2:Tg01V_j1CTg008dj1BTg00Y4j2WTg00Sij2VTg00Y\j3UTg00Z@j2STg00Qdj1@Tg0023j1RTg00Zaj2?Tg01=8j4<Tg00[?j1PTg00[]j1NTg0038j1MTg00\kj28Tg01@Yj3OTg00]Nj4=Tg00=ej1KTg00_dj2iTg00`Fj2hTg00a2j3gTg00aQj4fTg01<Zj1`Tg00Jmj2_Tg00cBj1]Tg00ekj4\Tg00SIj3[Tg00M[j3^Tg01W8j7ZTg000ij6aTg00fKj7bTg01X<j6cTg01I7j6dTg00^\j7eTg00_@j8XTf1R2g00gMR3g00glR4P4g00hLR5f0R6g00hlFbp=FP2P3P4P4P5P6Ecp=GP2P3P4P4P5P6Edp=9f2R7P3P4P4P5P2P6Fep=If3R8P3P4P4P5P7P2P6GXp=7g00GiR3#5R9#5#5R:#5#5#5R;#JR<#AR=p,1aR>13<6R?'1p,1nR@,;>RA,2?'6%J:R:#AR?#TRBg00HlRCPBAQ>@2g00foRD,>:,L?R?p,1mR:P2O1n0100000020000REA0B6?XIB13<2RF,j>11>F1H>F'E13<7,H>PCP113<8,1>PCPBf5RF,3<RG/DARH,42P?P:PFO1n0100000020000=0B?P2f4RI,3<,1>RJ1YGARK12GA/EHRHf6RG,3</DARLPCP1f7,3</2ARMPCPBg00ILRN/42P?P:f9O1ROn0100000020000=0B?P2f8,3</2ARP1:B?PCPB14NNP?POn0100000020000=0B?eWGP6O1%CPRQ%B9RR%B;R;'WRS12DRRT11D;1VR;RU,2D[RV[RW11DRRXg00ilRYAUR;2UW<R;11DU\Y^<XRXp,2HaRY11D>RZ12>UR['6R\P0PZP[P:f=O1=0B?R]P6p,2HnR^11D@R_12@URU'6R`P0P_PUP:fBRaO1=0B?RbP6f;g00jH1SDR':PTeO1RTPVp-0RRg00HNRcg00jnRd#@Re%RdRdPc1?c7RfP21?c8C<%PcRg%NcRhPc%M3,8cRig00lA18c3R318c95OcC=,FhR9,Gh%K4R4Ph19hFRj=Ih9P419hGC7C71ih5R5P6P71:CN1h67=0CNdAgcD2CfRDb>bAbBX4cX5cWCX2RW31;62,27g01X`R9[1;27,28,6IPG[[^4c^5c^Cc^2R^3RP6P:fGRGO1=0B?Rk13<GRG,1>PGP@P>f>fFRlO7b=b1X9UX8_P2P6O2n2001000000121000000b0X7[X6ZP2P6O2n2001000000121000000b0b?b1PCPBg00iLRm,4NP?POn0100000020000=0B?eWEP6O1n10210010100021010211103b:b;WDP6O1%CJPKPHPLPCP1PMPCPB14m2P?POn0100000020000=0B?P2PSPWP;PXPYP\P0PZP[P]P6P^P`P0P_PUPbP6PTPVPePdPc%`cP2PfC<PgPhPcP3g00kZPiC=,FhRi,GhP4Ph19hI9IhiP4PjC7C7P5PDb>bAbBX4cX5cX2RX3R1162P9[1127/68PF[[^4c^5c^2R^3RP6Pk12GAPGP>PaPlO6b=Rlb1X9UX8_P2P6O2n2001000000121000000b0X7[X6ZP2P6O2n2001000000121000000b0b?b1PCPB14mNP?POn0100000020000=0B?eXDPP6O1PSPWP;PXPYP\P0PZP[P]P6P^P`P0P_PUPbP6PTPVPlb@X9UX8_P2P6O2n2001000000121000000b0X7[X6ZP2P6O2n2001000000121000000b0b1b@PCPB14mmP?POn0100000020000=0B?eXHQP6O1n10210010100021110211103b:b;WEP6O1n10210010100021110211103b:b;A0BE?e1_==REP=P=%]>1><@C\%@E3[=^:2P:P>P@P2PYP^p,3HanFZEap,2m'P2O1=0B?eWFWJo"). Qed.

Lemma wview_zeros_mono : forall x, wview segs m x <> None -> wview segs m' x <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h01Hh12H0h22Hxh31bi001bh41eh51oi011oh61xi021xi033segp;1p;3p;2p;6p;4p;7g002Sj10Tg003]j1;Tg004;j19Tg004^R0j1>Tg01Y=j3<Tg00=ej1LTg007Jj32Tg01V_j11Tg00doj3@Tg005@j2:Tg006hj28Tg00V6j23Tg008dj1=Tg01Z:j37Tg01[>j1NTg01\@j1MTg01]?j1KTg01^=j1HTg016Ej24Tg01^[j15Tg01_9j26Tg000Mj6CTg01`@j2BTg00Jmj2ATg00cBj1DTg00ekj4ETg00Qdj1FTg00SIj3GTg00M[j3?Tg01W8j7ITg000ij6JTg00GiR1#0#0#0R2#0#0#0#;R3#9R4%;2R2#9R5#>R6p,4segsR7p,1mR8f0R93<%L5R:32#1P6g00HlR;P6p,1aR<p,1nR=f1R>3@R?g00fo,:2,85R2P8P>O1n0100000020000P0P5P6P91859R@P0g00EcRAP6f2,33RB%=1R1577P;P6%N9RC%M9RDf3RE,33RF%K9#HRG'4#5'6P:n0100000020000P:n10110200021010300n10110200021010000=26:#1X56P?P;P;P0P5P6P;P6P9P2P8PEO1n0100000020000P@P0PAP6A77F1P;P6PCf4,33/4G#5,6DP:n0100000020000P:n10110200021010300n10110200021010000=26:#1P9A262:RFP6P2P0P5p-0P9g00ilg01X`R2n10110100021000000X46g00IlP:P9ECP21B29b1W0%1FeP>n0110000020000b31A44RFP4P4%D<1:3=CE%FF3G=?8>P8P<P=P>p,2Hap,2Hnp,3HanFIEJP0P5P6p,2m'R5P>O1P@P0PAP6133>=771P;P6PC14BG#5,6DP:n0100000020000P:n10110200021010300n10110200021010000=26:#1eA<75>=26:#1eW2W6o"). Qed.

Lemma bytes_at_zeros_other : forall A bs,
  bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> bytes_at segs m' A bs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h06__sat3h14__x1h22a0h32H2h44__x2h51ih61Hh72H3h82H4h97__arithh:4__ffh;6__sat2h<8__varmaph=5__with>4__x3h?4cstrh@2HahA3Hi0hB4__x4hC4__x5hD5cstr0hE1AhF2H0hG2H1hH2H5hI2HdhJ2HihK2bshL1ohM1zi001bi011xp;1p;4p;2p;3p;7p;6p;8p;<g002Sj1>Tg003]j1ZTg004;j1jTg0023j1RTg014Rj4OTg010lj21Tg008dj1XTg00Sij2eTg01`_R0j2=Tg004^R1j1`Tg00oWR2j14Tg00U=j23Tg00cBj1@Tg01a7j3ETg01ajj3<Tg007Jj3;Tg00TbR3j28Tg018Ij1MTg00Y4j2iTg00TFR4j22Tg00Y\j3fTg00Z@j2dTg00ASj2FTg00Qdj1cTg00Zaj2BTg00[?j1bTg00[]j1aTg00\Hj2STg00\kj2ATg00=ej1_Tg00_dj2^Tg00`Fj2]Tg00a2j3\Tg00aQj4[Tg01<Zj1xTg01@Yj3NTg00^9j3wTg006hj2vTg01bHj2uTg017bj4qTg019jj1ITg01:Ij2CTg01GBj2HTg00SIj3GTg0038j1WTg00V6j2oTg00^\j7nTg00d4j2mTg000ij6UTg01cGj2lTg00CVj4TTg00UZj2JTg019Pj2kTg00]Nj4YTg00fKj7PTg00_@j8hTg01=8j4pTg01F4l<gTg01FYj3sTg01Gnj7tTg00foR5f0R6'Jp=0f2R7f1R8#4'3/J6p=61J86,k7p=91378/J6p=DP7g00gMR9g00glR:P:g00hLR;g00HNR<P8g00kZP6CYg00hlR=FPp=7f3R>P9P:P:P;P7P8P6Ghp=5P<P7P8P6Cpp=?g00OLR?P<P0P2P4g01dHf5R4f4R2P>P7P8P6M<gp=r%46,38p=QAs<86p=:P<P8g00lAP6CYp=KP8P9P:P:P;P6P=FPp=LP7P9P:P:P;P8P6Ftp=Vg00GiR=#>R0#>R@#>RA#Z#jRB#Rp,4segsRCp,1mRDP8P6COP3%0711B8%X0RE%>A#>#>RA#XRF'eRG56711B7RH,=6%`BRI%48RJ,32#@9ECDA<B>83;[^5?'8p,1aRK96>Hp,1nRH,3KRL;9>PCp,2m'RMP2P>CO[P6%0211B2=64G11B4RN,=6f7RO/3J#@9ECDf6RP=<B85;I[^5?'8P3A6PNG11BPRN,=6f8RQ/3J#@9ECDA<BO85;I[^5?A6ONK?9LOPCPMPQPOCO[P611BO=6QGf9,1BRO,=6f;RN/3J#@9ECDf:RR=<B85;I[^5?A6ROK?9LR%0N11BRRR#4RO=DNGRS11BN,=6RTf=RU/3JRV#@RW9ECMf<RX=<B85;IRY[^5?RZ'8%MRRR%0ORO1iEFR[125ER\%0F125G[R][R^%0ER_g00ilR`AfEF8UW@RF%0G\`^@_R_p,2HaR`%0KRa12KGRb'8RcP3PaPbf@Rd#0P6p,2HnRe%0HRf12HGRg'8RhP3PfPgfERi#0P6PNg00jH1d5E'FP\eO1R\P]g00jnRN#cRj%RNRk1B<8%b<Rl%a<Rm1S<5Rn1A<=Ro57mRp%_:RqPpC51^m;RrP6P7g00HlRsg00ILRt'F1]67=;stdA\<58C[R5b:b<b=X1<%06%08Rt[^1<P6fJRsPiO2b9b0X8gX7fP8P6O2n2001000000120000000b2X3bX6aP8P6O2n2001000000121000000b2b;b0b?PSPZPRPOP[P^PFP_P`PcP3PaPbf?RO,1B=6dGP6PePhP3PfPgfDRR,1B=6iGP6P\P]PjPk1B<7RZ%x<RS7?8PlPm1A<0Ru9N<oRv1S<E%ZARA5w<RE57mRwPqPwC5PrP5b:b<b=X1<X4<AD68GAD87G[^1<^4<P6fIRw,1B#4PsfAO3b9b0X8gX7fP8P6O2n2001000000121000000b2X3bX6aP8P6O2n2001000000121000000b2b;b0b?PIPDPWO1P1PBPIP61vB6f>R1%47RD'3#@,uCn10110100021010000A<BU75;IXLIP>P8P6O2PMPWO1P<PV126K?9L6XM<11BXRX,=8%4XRM,2JRIP8PJ1F<JPXPM1F<MErP6CqRMPI%M7RX%0DRD11B1R1#MRJ%41#0R1P[P^PFP_P`PcP3PaPb1QRQRR/2K?9LRP6PePhP3PfPg1QwURU/2K?9LUP6P\P]g01O?RL#IRQ#IRC#IRs#I,C<Rx1C<CRC1C<LRL':Ry':g01L<Rz'H1C<sRs1C<QRQ,:C':/Hz=GNj5GNPk1B<2??7S1B<4??>S7?8PlPmA7mnuRCPqPm%W0,A<R0,Ku,LmRuPqPmAN<o0R0%W=,A<R=57m1A<@9N<=R@=7mo5VmPq1Kv=,LmA7m@v5VmC5C5C5PrP5b:b<b=X1<X4<X><XB<XC<1274AD7P21324R@;9713>2R=/24134P;9=[[\t^1<^4<^><^B<^C<P6fM,1B#4RBPHPKfB#4RKfNRHPOPdfCO8b9b0XHgX8fP8P6O2n2001000000121000000b2X7bX3aP8P6O2n2001000000121000000b2b;b0bDb?bA1oAWPMPIPXPDPJP1P[P^PFP_P`PcP3PaPb%0R12RG'8P6PePhP3PfPg%0U12UG'8P6P\P]1:QL,:x/Hz1:sy/Hz=GNj5GNPk1B<>??>S9?Z8PlPmPCPqPmPuPqPmA7m0EPqPmPpPqPmP9P:P:P;A7mnv1KvE,LmFnC5C5C5C5PrP5b:b<b=X1<X4<X><127>AD72G%0>%0@12@G'8[[[\t^1<^4<^><P6PBPKPHPOPdPiPwO7b9b0X8gX7fP8P6O2n2001000000121000000b2X3bX6aP8P6O2n2001000000121000000b2b;b0bDb?bA,mVEU,lWEUPYeXJTX5?CTCTWIW6WGP8P6O2n2001000000121000000W3WFP8P6O2n2001000000121000000W3WKXE<o"). Qed.

Lemma wr_at_zeros : forall A k, wr_at segs m A k -> wr_at segs m' A k.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "h01ih12H2h26__sat3h34__x1h42a0h51Hh62H3h72H4h82Hah97__arithh:4__ffh;6__sat2h<8__varmaph=5__with>4__x2h?1Ah@2H0hA2H1hB2HihC1kp;4p;1p;2p;3p;7p;8g0107j4:Tg002Sj14Tg008dj1@Tg00Sij2[Tg00TFj23Tg00TbR0j21Tg003]j1?Tg004;j1KTg004^j1JTg00U=j26Tg00cBj18Tg01Y=j37Tg00=ej1DTg007Jj35Tg01V_j19Tg00Y4j2XTg00Y\j3WTg00Z@j2VTg00ASj2BTg00Qdj1UTg0023j1PTg00Zaj2ATg00[?j1OTg00[]j1LTg00\Hj2<Tg00\kj2=Tg00]Nj4>Tg00_dj2ITg00`Fj2MTg00a2j3NTg00aQj4HTg01<Zj1QTg01=8j4RTg01@Yj3GTg00^9j3STg01djj2TTg00CVj4FTg00UZj2ETg00fKj7ZTg00_@j8YTg00foR1f0R2'Ep=0f2R3f1R4'6/E2p=2P4g00gMR5g00glR6P6g00hLR7P2g00hlFZp=Cf3R8P5P6P6P7P3P4P2GYp=;g00HNR5p,4segsR9p,1mR:P4P2C:P0%03g00GiR;#4R<#@R=%4<#4R>#4#4#4R?#@R@'[RA9234%02RB1323'1%?>#KR>#JRCf4RD/64#8979:%D>R>35#9[^05'1P9p,2m'REP8P3C:P2%0Df5R8?2DA1328,1Bf7RD/64#8979:=5C>#9[^05'1P0f6RF?28A132F,1Bf8R8/64#8979:=5C>#9[^05P9PEPDPFC:P2A28DAf9R8,32,1Bf;RD/64#8979:=5C>#9[^05f:R:#0A2:8AR8132:,1BR:f</64#8RF979E=5C>#9[^05R>'11X=@RC131=RE%0@131A[R9[RG%0=RHg00ilRIAW=@4UW8R@%0A\I^8HRHp,2HaRIp,1aRJ#0RK13JARJ'1RLP0PKPJf>RM#0P2p,2HnRNp,1nRO#0RP13OARO'1RQP0PPPOfCRR#0P2PDg00jH1V1='BPEeO1REP9g00jnRD#URS%PDRD1A54%O5RT%L5RUP51<51g00kZRV1=5;R;C>,CURW%D6R6PWC;1IU7R7P2P3g00HlRWg00ILRX'B1M23=5WXdAN514CHR1b:b<b=X35%04\B^35P2fHRBPRO2b9b2X7OX6PP4P2O2n2001000000120000000b4X1JX5KP4P2O2n2001000000121000000b4b;b2P8P>PCPGP@PHPIPLP0PKPJf==2MAP2PNPQP0PPPOfB=2RAP2PEP9PSPDP51A53P4%Q5CRPTPUP51=5<9G5;PV1<5=%??5S5C>,CURUP6PUC;P7P1b:b<b=X35X>5A224AA243A[^35^>5P2fGPBf?O3b9b2X7OX6PP4P2O2n2001000000121000000b4X1JX5KP4P2O2n2001000000121000000b4b;b2P3P4P2O2,TFXB:X05CFCFW5WAP4P2O2n2001000000121000000W1W@P4P2O2n2001000000121000000W1XC5W?o"). Qed.

Lemma rw_cells_zeros_other : forall A cs,
  rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> rw_cells segs m' A cs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "h01Hh11Ah22Hbh32Hdh42Hwh53Hwfh62csh71np;1p;4p;2p;6p;3g0023j1DTg00lhj4;Tg00maj48Tg00n[j12Tg00oWj11Tg0107j45Tg00U=j23Tg00UZj20Tg019Pj24Tg012[j17Tg013Uj16Tg014Rj49Tg002Sj1:Tg003]j1CTg004;j1BTg010lj2ATg01enj2@Tg000ij6?Tg01g2j4>Tg00CVj4<Tg01h:j3=Tg00HNg01I[#Dp,4segsR0p,1mR1f1R2f0R3C;g00TbR4P0P1f2R5P2C8P0P1P5%22#1C5f3R6%25#1'3p,1aR7'0p,1n,37R8/06'4P0p,2m'R9f4R:P6C;[P3P0P1P:P6C8P4%7:P0P1f5R4%6:C9P0P1f6R:%24#1C5f7R4%2:#1'3/071084'4P0P9f8R;P4C;[[P3%7:P0P1P;%64C9P0P1f9R1%2;#1C5f:R;%21#1'3/07108;'4P0P9f;R1P;C8P0P9P1%2;R4#1R:C5%7;P0P9P1%6;R9C9P6P1P9P5g00OLR5P4f<R4%13'3/071084'4X75P3g00Gi#:#:#:#C#B/A91@;6E?C>C<A=1:2C<W3W4W2W5P2P3O2n2001000000120000000W0P2P3O2n2001000000120000000W0W6W1o"). Qed.

Lemma ro_cells_zeros_other : forall A cs,
  ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> ro_cells segs m' A cs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "h01Ah11Hh22Hbh32Hdh43Hwfh52csh61np;1p;4p;2p;6g0023j1ATg01i9j49Tg012[j13Tg013Uj17Tg014Rj48Tg00n[j15Tg00oWj14Tg00U=j21Tg00UZj20Tg019Pj26Tg002Sj12Tg003]j1;Tg004;j1:Tg010lj2@Tg01enj2?Tg000ij6>Tg01g2j4<Tg00CVj4=Tg00HNg01I[#Ap,4segsR0p,1mR1f1R2f0R3C9g00Tb%32P0P1f2R4%72C8f3R5%54#4'1p,1aR6'0p,1n,16R7/05'6P0p,2m'R8f4R9P5C9[P3%35P0P1f5R1%79C8f6R9%51#4'1/061079'6%39P0P8f7R8%79R0C8P4P8P0P2g00OLR8%59f8R1%43'1/061071'6X68P3g00Gi#2#2#2#;#:/@01?94E>C<C=W3W2W4P2P3O2n2001000000120000000W1W5W0o"). Qed.

Lemma stk_zeros : forall lo hi, stk segs m lo hi -> stk segs m' lo hi.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h01bi001bh12H2h21ah32a0h46__sat3h54__x1h61Hh72H3h82H4h92Hah:7__arithh;4__ffh<6__sat2h=8__varmaph>5__with?2H0h@2H1hA2HbhB2HwhC2HxhD2b0hE2hihF2lohG1ohH1xi011xp;4p;1p;2p;3p;7p;6p;8g01j2j4<Tg002Sj1:Tg008dj1ATg00Sij2dTg00UZj21Tg00TFj27Tg00TbR0j22Tg003]j1DTg004;j1?Tg004^R1j1NTg00cBj13Tg01Y=j39Tg00=ej1JTg007Jj30Tg01V_j18Tg006hj2HTg01jgR2j25Tg00Y4j2ZTg00Y\j3YTg00Z@j2XTg00ASj2;Tg00Qdj1FTg0023j1WTg00Zaj2VTg00[?j1UTg00[]j1TTg00\Hj2CTg00\kj2OTg00]Nj4@Tg00_dj2MTg00`Fj2LTg00a2j3PTg00aQj4QTg00^9j3KTg01djj2RTg00doj3STg005@j2ITg01bHj2=Tg01kAj4GTg00Jmj2cTg00ekj4bTg00SIj3aTg00M[j3`Tg01W8j7_Tg000ij6^Tg00CVj4>Tg01a7j3]Tg00fKj7\Tg00_@j8[Tg00foR3f0R4'1p=4f4R5f3R6f2R7f1R83];04p=6P8g00gMR9g00glR:P:g00hLR;P4g00hlF\p=BP6P9P:P:P;P7P8P4G[p=Eg00HNR9p,4segsR<p,1mR=P8P4C<P0%47g00GiR>#:R?#AR@%:?#:R?#:#:#:RA#ARB'dRC,18RD11641747'2%D?R?#?RE#NRF%38RG99<=%JERH30#8PFP<P=%37RI1HE4RJD6X0E,5E'2RK[^29'2P<p,2m'RLP6P7C<P4%45115Cf6RM/14f5RN,74'2PK[^29'2P011NCf7RO/14174M'2PK[^29P<PLPOPMC<P411OCf:RP/14f9RQ,74'2PK[^29%4P11QCRRf;RS/14174P'2RTA9<LG=0FH#8PFP<PLPIPJD6X0E,5E'2[^29RG'21Z@BRU173@RV%4B173C[RW[RX%4@RYg00ilRZAY@B8UW9RB%4C\Z^9YRYp,2HaRZp,1aR[#4R\17[CR]'2R^P0P\P]f>#4P4p,2HnR_p,1nR`#4Ra17`CRb'2RcP0PaPbfCRd#4P4PSg00jH1X3@';PVeO1RVPWg00jnRe#FRf%WeRe1V98Rg%U9Rh%T9RiP91C93g00kZRj1O9>R>C@,BiRk%J:R:PkCE1Mi;R;P4P7g00HlRkg00ILRl';1L47=0kldAP938CQRlb;b=b>X59%44%48[^59P4fHPdO2b:b4X8bX7aP8P4O2n2001000000120000000b3X1]X6\P8P4O2n2001000000121000000b3b<b4PRPGPUPXPBPYPZP^P0P\P]f=R^/1CP4P_PcP0PaPbfB/1CP4PVPWPfPePgPhPiP9P>Pj1C9@%DARA5K9C@,BiRiP:PiCEP;Plb;b=b>X59114CPD[^59P4fGf?O2b:b4X8bX7aP8P4O2n2001000000121000000b3X1]X6\P8P4O2n2001000000121000000b3b<b4P7P8P4O2PKP0A9<=I=0FH#8PFP<P=%36R6PJD6X0E,5EA9<L6=0FH#8PFP<PL%35R5PJD6X0E,5E'2P4A9<=5=0FH#8PFP<P=%3MPJD6X0E,5EP2PEPFP<P=%3OROPJD6X0EA9<LO=0FH#8PFP<PLf8#3PJD6X0E,5E'2P4PFP<P=%3QPJD6%3PRP99<L=0FH#8PFP<PL%3SRSPJD6X0E,5ERH1RPNPFPkPFAS[`PRN1I?3R?,HER3P=PPO1n0100000020000P1PEPFP8PJf<#3RQ,=<ROn10110100021010000=0FJX0E,5EXGFPNPkPkP1PEPFPkPFP8P3P=%3^R^O1n0100000020000PJ1=<^n10110100021010000=0FJX0E,5EP4PEA0F3JX0EP?1;F3CGPEP1PEPFP=PQO1PJPOn10110100021010000=0FJX0EP7P8CGn0110000020000bD%?AR7/c7ROP7P7%3[1IA`Cb%FO3a=`=PP=P[P`PPPZP_p,3HanF_E^P1PEPFPLPSO1PJ1=<Sn10110100021010000=0FJX0E,5EePHeC>WAX0EP8P4O2n2001000000121101000W1WBP8P4O2n2001000000121000000b3XCTXH9C>C>W6W@P8P4O2n2001000000121000000W1W?P8P4O2n2001000000121000000W1XE9WFo"). Qed.

Lemma munch_zeros : forall W m0, munch W m0 m -> inside W a n -> munch W m0 m'.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h04__x1h14__x2h22a0h36__sat2h44__p1h54__x3h61Hh72H1h82H2h92H3h:7__arithh;4__ffh<8__varmaph=5__with>2Hah?6__sat1h@6__sat3hA1bi001bhB1li011lhC1ri021rhD2H0hE2H4hF3HinhG2HxhH1WhI2m0hJ2n0hK2n1hL1ohM1xi031np;1p;3p;2p;4p;7p;6p;8g0023j1NTg002Sj16Tg003]j1BTg004;j1>Tg004^j1mTg01k[j3GTg01lRj3]Tg00V6j21Tg01mJj2WTg01nCj2TTg01o6j1OTg00TFj20Tg00TbR0j24Tg007Jj3KTg01V<j2dTg00W=j2MTg01UYR1j2DTg00U=j28Tg00UZj22Tg019Pj23Tg008dj1CTg00Y4j2ZTg00Sij2YTg00Y\j3XTg00Z@j2VTg00ASj2@Tg00Qdj1UTg00Zaj2?Tg01<Zj1STg01=8j4JTg00[?j1QTg00[]j1PTg00\kj2:Tg00=ej1RTg00_dj2lTg00`Fj2kTg00a2j3jTg00aQj4iTg01V_j1LTg01U6j2hTg00V`j2HTg0038j1cTg01@Yj3FTg00^\j7`Tg01o_j7_Tg01`@j2aTg01cGj2bTg000ij6^Tg00]Nj4ATg00fKj7eTg01I7j6\Tg01Gnj7fTg00_@j8gTg01X<j6[Tg00foR2f0R3'2p=7g00HNR4f1R5g00lAP3CAp=;P5g00gMR6g00glR7P7g00hLR8P3g00hlFep=5P5P6P7P7P8P3E\p==f2R9P6P7P7P8P5P3Ffp=If3R:P6P7P7P8P9P5P3Ggp=9P4P5g00kZP3CAp=<P5P6P7P7P8P3E[p=Eg020c#Ng00GiR;#6R<#6#6R=#6#6#6R>#BR?#>R@%B=#>#mR=[p,1mRA9G53p,1aRBp,1nRC5]9f4RD11?3'W1T?511?5RE#7%O?,0E'4P=PAP9O1f6RAP:O19K=3XL=PDP9P5O2p,2m'R=P9O111?9RE/dB10EB1MEB'D11?:/MBg00HlREP111?D/0B11?ARA/0B18BCRF/2ARG'3P5f5RH,1?/0BRI%C<RJ%C>R>'ZRK102JRL%7>1YJ>RM,02[RN[RO%7JRPg00ilRQAXJ>5UW>R>%7M\Q^>PRPp,2HaRQ%7BRR10BMRS'4RTP0PRPSf:,1?RU/0B12FU'3RVP3p,2HnRW%7CRX10CMRM'4RYP0PXPMf?,1?RZ/0B12FZ'3P3f;RZg00jH1V2J'@PLeO1RLPNp-0RJg00jnR[#UR\%N[R[P41?49R]P5%S4CJ%Q4R^%P4R_1:4;R`1:4<R<';,5_Ra%R7Rb1=_D9I_aC91l_8RaP3P9g00ILRc,@E1k39=KEcdAj425CiR2b;b<b=X04X14W410351059/3:[^04^14^4JP3fD,1?Rc,2FPBPcf>RcO4b:b3X9MX8XP5P3O2n2001000000121000000b2X7SX6RP5P3O2n2001000000121000000b2b?b3WBP3O1%LI1hFA1HFA,DGf7,1?,HFPEP1f8,1?,2FPVP5f9R1,1?,2FREPKPOP>PPPQPTP0PRPS11?cRG/0B12FG'3P3PWPYP0PXPMfC,1?RA/0B12FA'3P3PLPNP\P[P4P]P51?4:CJR]P^P_%c;,:4R;9F4</<`,5_RIPb1=_H=I_IC9PaP2b;b<b=X04X14X54X4J1859/23189:/25,3D[^04^14^54^4JP3fH,1?R?/0BPCPBP?PcO5b:b3X9MX8XP5P3O2n2001000000121000000b2X7SX6RP5P3O2n2001000000121000000b2b?b3WBP3O1%LEPcPBPCPUPZPKPOP>PPPQPTP0PRPS12BG10GF'4P3PWPYP0PXPM12BA10AF'4P3PLPNP\P[P]P^P_AF4`;R;/<<,5_,E_PbP_1;<`,5_,E_PbP_P6P7P7P81<`<,5_1;<;,5_F`C9C9PaP2b;b<b=X04X14X541839/25g01X`R2[1095P2[129:189D,0:'4[[^04^14^54P3PCP?PBPcfBO5b:b@XEMX9XP5P3O2n2001000000121000000b2X8SX7RP5P3O2n2001000000121000000b2b3b@P1F_,aVWKP3O1n10210010200021110111103bAbCWJP3O1n10210010200021110111103bAbC,b9E^bDWGXM@AG:9=eWFW6WIWHo"). Qed.

Lemma wmono_zeros : forall m0, wmono segs m0 m -> wmono segs m0 m'.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "h01Hh12Hxh22m0h31xp;1p;3p;2g002Sj10Tg003]j11Tg004;j12Tg004^j14Tg021Xj33Tg01Y=j39Tg00=ej18Tg007Jj35Tg01V_j16Tg01djj27Tg00Gi#0#0#0R0#0#0#0#1#2R1%10#2R0#4R2[p,4segsR3f0R4p,1m33f2R5=934%80552#6f1R2P5P2P4O2'7W1X31p,2m'9332eW0W2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mem_inv_zeros : mem_inv segs m -> (forall x : word, (a <= bv_unsigned x < a + n)%Z -> ro_addr segs x = false) ->
  (a + n <= UTOP)%Z -> mem_inv segs m'.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h02Hxh16__sat2h24__x1h34__x2h44__x3h52a0h62b0h71ri001rh81xh91Hh:2H0h;2H1h<2H2h=2Hah>7__arithh?4__ffh@6__sat1hA8__varmaphB5__withC4__x4hD1li011lhE2n0hF4HinvhG3HrohH4HtophI1bi021bhJ2l0hK2n1hL1oi031np;2p;1p;4p;3p;7p;6p;8g01R:j2rTg002Sj16Tg003]j1HTg004;j1ETg00V6j22Tg00UZj21Tg00U=j28Tg00TFj20Tg00TbR0j25Tg022Oj2ATg023Fj4VTg004^j1STg006hj27Tg007Jj33Tg00Jmj2jTg00cBj1hTg005@j2KTg00ekj4bTg00Qdj1MTg00SIj3PTg00M[j3^Tg00doj3]Tg01W8j7\Tg000Mj6[Tg01U6j2ZTg00V`j2GTg01UYR1j2ITg00W=j2=Tg00WZj24Tg01V<j2YTg008dj1FTg00Y4j2XTg00Sij2WTg00Y\j3UTg00Z@j2TTg00ASj2DTg0023j1RTg00Zaj2<Tg01=8j4CTg00[?j1qTg00[]j1pTg00\kj2;Tg0038j1oTg01@Yj3QTg00=ej1iTg00]Nj4?Tg00^\j7gTg00_dj2fTg00`Fj2eTg00a2j3dTg00aQj4cTg019jj1JTg01:Ij2@Tg01FYj3LTg01GBj2aTg01<Zj1`Tg00CVj4OTg01V_j1NTg024Gj6_Tg025Aj6kTg026Aj4lTg00fKj7mTg00_@j8nTg00HlR2f0R3g00iLR433p=Bg00HNR5f1R6g00lAP3C?p=>P6g00gMR7g00glR8P8g00hLR9P3g00hlFmp=9f3R:P7P8P8P9f2R;P6P3Gnp=:p,4segsR<p,1mR='rg00GiR>#6R?#6R@#6RA#6#6#6RB#HRC#ERDp,1aRE12C3RF'1p,1nRG,8ERH,0F'51A<6#B[]8g027>RF,1HP<p,2m'RIP<P=P3P:CVX8D%HARA#ERJ%SJRKPIP6O117J333PK1jDDRIPDPD%hE1KCGCb%MI3P=^=;17J;93K3XLKP3P2PKA]EG;g00foRI,KA,7JRAP=P;O1n0100000020000RLP=PEPGP;p,2HaRMp,2HnRNp,3HanF\E[17J693KL12C:RL,ZE11EL1GEL'If4RL,2C,GEP2P1f5,2C,1EP2PKf7RO,2C/=HRP,46PAP=POO1ROn0100000020000f6RQ,7JRR53Kf8RS,A<#B12CSRS/0F'5]0P612CQ,1ERQP2PKg00ILRT/4PPAPOn0100000020000=3KR1YSHRU10SH1=SH'IRSf9,2C/=HRVP2P1f:,2C/0HRWP2PK14T6PAP=f<RXO1RYn0100000020000f;RZ,7JRJ53Kf=R[,A<#BR\12C[/0FR]'5R^]0P612CZ/0HR_P2PK14TTPAPYn0100000020000=3KJP\P]f?R`P[%F?Ra%FBRB'XRb10IaRc11IB1WaBRd,0I[Re[Rf11IaRgg00ilRhAUaB6UW=RB11Id\h^=gRgPM11IERh10EdRi'5RjP0PhPifA,2CRk,1E10kH'5P3PN11IGRl10GdRd'5RmP0PlPdfF,2CRn,1E10nH'5P3PZg00jH1TIa'DPceO1RcPeg00jnRa#MRZ%RaRHP51<5;P61<5:RoCC%q5Rp%p5Rq1;5?R?1;5>Rr%o>,;5R>5Q5'>,9qRs%i8RtPqP5Prg00kZRuP?C?,9qRvPtPqP7P8P8P9PvPsFgC:C:1fq9R9P3P;1D2T1e3;=32TdAd5I6CcRIb?bAbBX25X35X45183;,06116;11;:18;L,0:'5[[^25^35^45P3PGfK,2CRCPEP`fDO5b>b1X<dX;lP6P3O2n2001000000121000000b5X:iX9hP6P3O2n2001000000121000000b5b@b1O2PbPfPBPgPMPjP0PhPi10kFP3PNPmP0PlPd10nFP3PcPeg01O?Re#JRc#J,@51@5c1@5e5L55L5g01L<'a=PaZPHP5P51<5LP;%`5CCP6PoCCPpPq1;5@9Q5>R>,>r,9qPtPqP5P>PuP?C?,9qPt1>r?,9qC:C:P9PIb?bAbBX25X35X45XC518;:,0318:L/1;10;:[[^25^35^45^C5P3PGPEPFPCP`fLO6b>b1X<dX;lP6P3O2n2001000000121000000b5X:iX9hP6P3O2n2001000000121000000b5b@b1COW0WJP3O1%N_RhP2PK14T4PAPYn0100000020000=3KJP\P]P<P=P[PXf@R]P3E_P<P=P[PXP]P3EkCOR]W0WEP3O1n10210210000021110110103P;O1b6b7W0WDP3O1%NQP2PK144PPAPOn0100000020000=3KRPUPSPVP2P1PWP2PK1446PAPYn0100000020000=3KJP^]0P6P2PK144TPAPYn0100000020000=3KJP]W0XD_P3O1P2PK1444PAPYn0100000020000=3KJP]W0XKhP3O1n10210210000021010110103P;O1b6b7W0WEP3O1n10210210000021110111103P;O1b6b7b0W0WIX8DClWHWGWFo"). Qed.

(* [comment removed for export] *)
Lemma bytes_at_zeros_new : bytes_at segs m' a (repeat (Z_to_bv 8 0) (Z.to_nat n)).
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h04__x1h12a0h24__p1h34__p2h46__sat2h54__x2h64__x3h76__sat1h81Hh92H0h:2H1h;2H2h<7__arithh=4__ffh>8__varmaph?5__with@4__x4hA1ihB1xi001xhC2H3hD2z0hE2HahF3Hi0hG4cstrhH1nhI2HihJ6__sat0hK1mhL1ohM1yhN1zi011bp%0p&0p;1p;2p;3p;4p;<p;5p;6p;7p;8p;Bg002Sj1=Tg003]j1TTg004;j1bTg005@k20<Tg01?ER0j1~Tg0282j3yTg010lj2oTg00oWR1j19Tg00U=R2j21Tg008dj1PTg00Sij2aTg00UZR3j22Tg01`_R4j2GTg004^R5k109Tg00cBj1XTg01a7j3}Tg01ajj3VTg007Jj37Tg00TbR6j20Tg00Y4j2uTg00TFR7j23Tg00Y\j3nTg00Z@j2lTg00ASj2JTg00Qdj1jTg0023j1hTg00Zaj2DTg00[?j1fTg00[]j1dTg00\Hj2ZTg00\kj2ATg00=ej1`Tg00_dj2_Tg00`Fj2^Tg00a2j3]Tg00aQj4\Tg01@<j2[Tg01P^k10;Tg028Qk40:Tg01F4l<OTg018nk200Tg019Pj2FTg019jj1;Tg01:Ij2QTg01=8j4MTg00^9j3{Tg0038j1xTg01@Yj3STg01>9j4pTg006hj2RTg01bHj2mTg0294j5qTg029Yj4rTg017bj4tTg018Ij1kTg01<Zj1vTg00V6j2wTg00d4j2iTg000ij6ITg02:5j2zTg00CVj4WTg02;5j3|Tg00]Nj4NTg00fKj7gTg00_@j8KTg01HRl<YTg01ENlBeTg01FYk302Tg01GBk203Tg00SIk304Tg01I7k605Tg00^\k706Tg01Gnj7cTg00foR8f0R9'2p=6g00HNR:f1R;g00kZP9CNp=:P;g00gMR<g00glR=P=g00hLR>P9g00hlFgp=4f3R?P<P=P=P>f2R@P;P9GKp=H1J:9p=>P:g00OLRAP:P:P0f4R0P1P?g01MOP@P;P9M<Yp>08PAP:P:P:P1P1f5RBP0P?P@P;P9M<Yp>07P:P:P:P:P:P:P2P9P;P@P2P?P0PBf6R2f7RCf8S00f9RDMBep>01A7:98p=E1Q:9p=<B02:;9p=5g00jnREg01L<-03;<049p=8P:P;g00lAP9CNp=BP;P<P=P=P>P9J05p=LP:P;g01LhP9CNp=CP@P<P=P=P>P;P9K06p=?P@P<P=P=P>P;P9Fcp=UP2P<P=P=P>PBP0P?P<P=P=P>P@P;P9GKGKp=@PAP:P4P1P7g01dHPBP0P?P@P;P9M<Op=sp,1aR7#6R1g00GiR4#=R<#=RF#=RG#TRH#bRI20<H8RHp,1nRJ#~RK5yIRL'oRM#9,17%P<RN%=G#=#=RG#PRO'aRP'21G9M&09IRQp,4segsRRp,2m'S01%9;RS,17RT#XRU3}AVIL;S0237RV[^AA'01uNORW138NRX%6O138P[RY[RZ%6NR[g00ilR\AnNO;UWERO%6P\\^E[R[p,2HaR\137PR],01R^P6P1P]P1P9p,2HnR_%6JR`13JPRa'0RbP6P`PaP1P9f;g00jH1l8N'JPXeO1RXPY%jERc%hERE1D:;%f:Rd%d:Re1Z:8Rf1A:4Rg':,4eRh%`=R=PhCH1_e>R>P9P@g00HlRig00ILRj'J1^9@=7ijdA]:8;C\Rjb=b>b?X0:%69%6;Ri[^0:P9P7Q00O2b<b7X;aX:`P;P9O2n2001000000120000000b1X9]X81P;P9O2n2001000000121000000b1bJb7PAPK%99Rk,17/2P1G9;PV[^AA'0XHA%9KRl,17Rm/2PRn1G9KRoPV[^AAPn1[8JRn,17Rp/2PP:P:P3P9XB:RqP312;9$0;XM:XB:PmPpPqPqPqP:P:g02;W11;9H0:#>XK:XH:P7P7%>7PlPnPqPq%>kXBAPKPnPq1[89XB:S03PJPJ%>JI08S04J07N:01PPPP%>PM<O2008JRq138JRkA7:nJ'012J8R8%En'0'FRlPnP:PWPZPOP[P\P^P6P1P]1170/2PP9P_PbP6P`Pa117D/2PP9PXPYp-0Rpg01O?Rm#;R3#;Rr#<Rs%<3R31Q:mRm'5Rt'5Ru%;rRr#<Rv15smRw'5/8c'8PEP:1D:@P;1D:?S05CMPdPe1Z:N%TGRG5{:RN,Bg,4eS06P=Pe1LeB1A:<R<%x4,A:R4'C,4e5?e1Le2Rx1C<f,4e5?e5UeP=PeAS:g4Ry/:N,4eS07P=AS:g<Rz/:N,4eCHF@P>Pjb=b>b?X0:X5:X6:X2pW3139PR{A7:@?,00%E@,0B'F11@0/2P11?0R|/2P[[[^0:^5:^6:^2p^3pP9P8PkPJf>R}P7PCf?R~p,3HanS08O8b<b4XCaX;`P;P9O2n2001000000121000000b1X:]X81P;P9O2n2001000000121000000b1b7b4bDb9CpPQ1RIHS09P5PIPQP91RI9%9@R5,17#X,mRn10110000021010100AVIL@57QXLQPQQ02Q09PIPHPKP;P9DqCrQ01PUO1P:PT1279117JRQ,39'0XN:1G;K13SnRLP;PS%>SPKQ03PJO1Q04EsP9CtS04PL%k@RS%65R5PqPlPnP:PWPZPOP[P\P^P6P1P]%9D,17RD,2713DQ'0P9P_PbP6P`Pa%9},17RR,2713RQ'0P9PXPY15s3,5v15vt/8c'8PEP:P:1D:0P@%v:CMP;Q05CMRtPdPe1A:FRF/C4,4e9?ex1LeC1CFf,4e5?e5UeRxP=Pe1:f<,4eR4P=Pe1B<F,4eRFP=1:gz,4e1Bzy,4e5?eCHF@P>Pjb=b>b?X0:X5:X6:X@:X2pX3pA7:?@,00%E?,0B'F%6@13?B12?|11?B,3|'0[[[^0:^5:^6:^@:^2p^3pP9P8PkP}PJfC#9R|P7P~f@R?fAR@O9b<b4XCaX;`P;P9O2n2001000000121000000b1X:]X81P;P9O2n2001000000121000000b1b7b4bDb9bGbF1wGUQ04PLPSP5PqPlPnP:PWPZPOP[P\P^P6P1P]%6D13DP'0P9P_PbP6P`Pa%6R13RP'0P9PXPY%;rRr#;RY#;#<%<rRr/5w'515vs,5r%<Y15vm'515ru/8c'8'8'8PEPtPdPeQ06P=PePhP=PePxP=PeP4P=PePFP=PeQ07P=1:fz,4e1BzN,4e5?eF@F@F@P>Pjb=b>b?X0:X5:X6:X@:X2pX3pA7:B0,02%EB,0C'F%6013BC11BC/2P112CR2#6132P'0[[[[\i\{^0:^5:^6:^@:^2p^3pP9P8PkP}PJP|P7PCQ00P~P?P@Q08O<b<b4XCaX;`P;P9O2n2001000000121000000b1X:]X81P;P9O2n2001000000121000000b1b7b4bDb9bGbF,iTEI,zUEIPVeXIoXAACWPMA|IHKEICWo"). Qed.

Lemma wr_at_zeros_new : wr_at segs m' a n.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h06__sat1h14__x1h22a0h34__x2h41Hh52H0h62H1h72H2h87__arithh94__ffh:6__sat0h;8__varmaph<5__with=4__x3h>2Hah?1ih@2HihA1ehB1oi001ohC1zi011bi023segi031xp;2p;1p;3p;4p;6p;7p;8g00U=j20Tg002Sj16Tg008dj1CTg00Sij2sTg00UZj24Tg003]j1LTg004;j1\Tg004^R0j1ZTg00cBj1>Tg01Y=j3VTg00=ej1HTg007Jj3=Tg01V_j1DTg00TbR1j2:Tg00Y4j2iTg00TFj28Tg00Y\j3dTg00Z@j2cTg00ASj2JTg00Qdj1`Tg0023j1_Tg00Zaj2@Tg00[?j1]Tg00[]j1[Tg00\Hj2ITg00\kj2?Tg00_dj2YTg00`Fj2XTg00a2j3WTg00aQj4UTg01<Zj1TTg01=8j4FTg01@Yj3GTg00^9j3RTg005@j2STg006hj2QTg00V6j2ETg01Z:j3rTg01[>j1qTg01\@j1pTg01]?j1oTg01^=j1lTg016Ej2kTg01^[j1jTg01_9j2hTg000Mj6gTg01`@j2fTg0038j1eTg019jj1<Tg01:Ij29Tg01FYj3;Tg01GBj2MTg00SIj3NTg00d4j2bTg000ij6KTg02:5j2aTg00CVj4OTg00]Nj4PTg00fKj7mTg00_@j8nTg00^\j7^Tg00foR2f0R3'4p=1f2R4f1R5/83':p=2g00HNR6P5g00kZP3CPp=5P5g00gMR7g00glR8P8g00hLR9P3g00hlFmp=3f3R:P7P8P8P9P4P5P3Gnp=7P6P5g00lAP3CPp=BP4P7P8P8P9P5P3F^p=Ap,1aR7#1R;p,1nR<,07R=g00GiR>#6R?#CR@%6?#6RA#6#6#6RB#CRC'sRD'4RE%13RF?23<RG%LARA#\RH#ZRIp,4segsRJp,2m'RK1075RL#>RM3V%HHRN3=#DRO[^?6RP':1i@CRQ182@RR%1C182D[RS[RT%1@RUg00ilRVAd@C5UW>RC%1D\V^>URUp,2HaRW187DRX,:;RYP1P;PXP;P3p,2HnRZ%1<R[18<DR\':R]P1P[P\P;P3f;g00jH1c2@'JPReO1RRPSg00jnR^#`R_%_^R`1@65%]6Ra%[6Rb1I62Rc1?6>Rd'5,3bRe%H8R8PeC71Yb9R9P3P4g00HlRfg00ILRg'J1X34==fgdAW625CURgb9b;b<X16%15Rh\F^16P3P7f8RiO2b8b0X7\X6[P5P3O2n2001000000120000000b2X5XX4;P5P3O2n2001000000121000000b2b:b0PEPPPQPTPCPUPWPYP1P;PXPEP3PZP]P1P[P\PEP3PRPSP_P`P61@64REP5%T6CFPaPb1?6?R?9G6dRP1I6@%LBRB5R6R@'5,3bRjP8PjC7P9Pgb9b;b<X16X361035/4D1054Rj/4D[^16^36P3P<P7p,3HanRkO3b8b0X7\X6[P5P3O2n2001000000121000000b2X5XX4;P5P3O2n2001000000121000000b2b:b0PI1SA2,QHRAP0PHPIP31QH3P0g00EcPI1074#>,EB%C>5rJPfPI%q3%p3107:#>,EB%o3#l'k#j'hPNn0100000020000PNn10110300021010200n10110300021010100==IN#DXBIA=IANRfPIPAP0PHp-0P3PVg01X`RVn10110000021000000XAIg00IlPNP3EgPV1fV3b5W4%DfePKPMO1P6PL1473?23=XC6PQPTPCPUPWPYP1P;PXf5,07RK,47?2K=P3PZP]P1P[P\f:,07Rf,47?2f=P3PRPSP_P`P6PEP51@6:CFREPaPb15c?,3b%e>,?6R>,B?,3b5AbR?P815dP,3bAG6d>R>,BP,3b5AbC7P9Pgb9b;b<X16X36X=6A2h54145j105:72j[^16^36^=6P3P<f?RjP7f>RhO4b8b0X7\X6[P5P3O2n2001000000121000000b2X5XX4;P5P3O2n2001000000121000000b2b:b01EBMPQPTPCPUPWPYP1P;PX%1K?2KDP3PZP]P1P[P\%1f?2fDP3PRPSg01O?RS#<RR#<Rf,96196R196SRS5;65;6g01L<RR'M%<fRf#<,96196f=;6S5;6/MR=N^_5N^P`PEPaPbPeP8PbP?P8Pb15>@,3bP815cP,3b1BP@,3b5AbC7C7C7P9Pgb9b;b<X16X36X=6%14?24:f4Rg,04/4D10:gRg#1?2gD[[\F^16^36^=6P3P<PjP7PiPhPkO6b8b0X7\X6[P5P3O2n2001000000121000000b2X5XX4;P5P3O2n2001000000121000000b2b:b0,bLEK,aMEKPOeX@GX?6COCOo"). Qed.

Lemma rw_cells_zeros_new : rw_cells segs m' a [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "h02Hah16__sat1h24__x1h32a0h41Hh52H0h62H1h72H2h87__arithh94__ffh:6__sat0h;8__varmaph<5__with=1lh>1nh?1zp;1p;2p;3p;4p;6p;7p;8g01?Ej1aTg002Sj11Tg003]j1ETg004;j1ATg005@j2`Tg0282j3OTg01DVj2HTg00Qdj14Tg00SIj3CTg00maj4BTg00n[j1@Tg00oWj17Tg0107j45Tg012[j1_Tg013Uj1UTg014Rj4=Tg010lj2NTg007Jj39Tg02;5j3LTg00CVj43Tg0023j1;Tg015Jj3GTg015gj2DTg000ij66Tg008dj1:Tg00Y4j2FTg00TFj22Tg00Sij2ITg00Y\j3JTg00TbR0j28Tg00Z@j2KTg00ASj2<Tg00Zaj2MTg00[?j1?Tg00[]j1PTg00\Hj2QTg00\kj2>Tg00]Nj4RTg00fKj7STg00=ej1^Tg00_@j8]Tg00_dj2YTg00`Fj2VTg00a2j3WTg00aQj4XTg02<;j2TTg01N<j2ZTg02<Yj1[Tg00UZj2\Tg00foR1f0R2'\p=0p,4segsR3p,2m'R4p,1aR5g01I[R6p,1nR7#aR8g00GiR9#1R:#1#1R;#ER<#AR=1`<1R<;O8R>'H%463CR6CBP3P4P5%@6#7C5R?%_6R@P3P4P5%U6C=R6g00OLRA1N=>;98g00ilRBAL=<8g00IlC3P@e%;=R@P>P3P4P5P2C=X=@g02==%4=9G=>1D=>E6P6eC3PAP8P3P4P5%72C5X>Ag00HNRAP7P3P4P5P2C5X?Ag02>C%78%::R:%1;#1#1#:R;'F121:R4%0;1I:;R3,21[R6[%0:R>f1R=9J:;VBW0%03\B^0>p,2Ha%05R>1253R5'8P0P>P5%07RBP2p,2Hn1273R3,8BP0PBP3PBP2f;g00jH1K1:'<P4eO1P6g00jnR6#4%;61MA=%?A%PAR6g00gMR4g00glR:P:g00hLR0P6P4P:P:P0PA1QA1g00kZ1>A9CRg00hlFSR9%^:P9G]1Y60P2f2R0g00HlR6g00ILR9'<1V20=969dAWA1=CXb9b;b<X2A%02%0=[^2AP2P7f3O2b8b1X73X6BP=P2O2n2001000000120000000b3X55X4>P=P2O2n2001000000121000000b3b:b1,T7E6g01O?,Z8%[8E6P?eC3o"). Qed.

End Zeros.

(* [comment removed for export] *)

Section Unmaps.
Variables (m : word -> option byte) (a n : Z).
Hypothesis Ha : (0 <= a < 2^64)%Z.
Hypothesis Hn : (0 <= n < 2^64)%Z.
Hypothesis Han : (a + n <= 2^64)%Z.
Let m' := apply_unmaps m [(wa a, Z_to_bv 64 n)].

Lemma unmaps_outside : forall x, (bv_unsigned x < a \/ a + n <= bv_unsigned x)%Z -> m' x = m x.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "p'0h01bi001bh11ri011rh22Hah34__p1h46__sat2h54__x1h64__x2h74__x3h82a0h91li021lh:2n0h;1Hh<2H0h=2H1h>2H2h?2Hxh@7__arithhA4__ffhB6__sat1hC8__varmaphD5__withE2l0hF2n1hG1ohH1xi031np;1p;2p;3p;4p;7p;6p;8g002Sj15Tg003]j1FTg004;j1@Tg00V6j22Tg00TFj23Tg00U=j29Tg00UZj21Tg019Pj2CTg004^j1QTg00doj3OTg00=ej1=Tg007Jj30Tg01U6j2HTg00V`j2GTg01UYR0j2BTg00W=j2DTg00WZj24Tg01V<j2XTg008dj1ATg00Y4j2WTg00Sij2VTg00Y\j3UTg00TbR1j2?Tg00Z@j2RTg00ASj2;Tg00Qdj1>Tg0023j1PTg00Zaj2<Tg01=8j4NTg00[?j1MTg00[]j1LTg0038j1KTg00\kj2:Tg01@Yj3JTg00]Nj46Tg01Gnj7ITg01I7j6STg00_dj2TTg00`Fj2eTg00a2j3dTg00aQj4cTg01V_j1ETg00Jmj2bTg00cBj1aTg005@j2]Tg00ekj4\Tg00SIj3[Tg00Lbj3ZTg02?Fj7YTg000ij6^Tg00fKj7_Tg00_@j8`Tf1R2g00gMR3g00glR4P4g00hLR5f0R6g00hlF_p=7f3R7P3P4P4P5f2R8P2P6G`p=8g00GiR9#5R:#5#5R;#5#5#5R<#FR=#@R>12=6R?p,1aR@'3p,1nRA,9@RB/1?'C%F;#@R;#QR?g00HlRCP?AO@A2%=;R;p,1mRDP2O1REn0100000020000RFPDP8O190?6XG?12=2RG,H@11@G1G@G'B12=8,G@PCP012=7,1@PCP?f5RG,2=RH/DBRI,42P;PDPGO1RJn0100000020000=0?JP2f4RJ,2=,1@RK1XHBRL13HB/BIRIf6RH,2=/DBRMPCP0f7,2=/3BRNPCP?g00ILRO/42P;PDf9O1RPn0100000020000=0?PP2f8,2=/3BRB%A:RQ%A<R<'Wg00foRR/3QRS11R<1VQ<RT,3R[RU[11RQRVg00ilRWAUQ<2UW211RT\W^2Vp,2HaRV11R@RW13@TR<'?P1PWP<PDf=O190?;P6p,2HnRX11RARY13ATRT'?P1PYPTPDfBR1O190?;P6f;g00jH1RRQ';PSeO1PUp-0RUg00HNRSg00jnRQ#>%PQPS1<S8P21<S7CN%MS%LSRQPS%K9,:SRZg00lAR[1:S9R91:S:5JSR:C6,7Q%=4R\PQPSP9g00kZR]PZC6,7QP\PQPQP3P4P4P5PSPZP[P9C6,7QPSP:P]PZC6,7QFIP\PQP3P4P4P5PGESC8C8C81TQ5P6P81;CO1e68=0COdAdSR2CcbAbCbDX5SX6SW7W31962,38112713J81987/1J'CPH[[[^5S^6S^7S^3UP6PDfGRUO190?;12=UPAP@f>P1fFO7b@b4X>TX=YP2P6O2n2001000000121000000b8X<<X;WP2P6O2n2001000000121000000b8bBb4PCP?14OOP;PPn0100000020000=0?PeWEP6O1%EBRW1;?PR<PCP?g00iLRY,4OP;PPn0100000020000=0?PeW:P6O1n10210010100021110210103b0b1W9P6O1%EKPLPIPMPCP0PNPCP?14Y2P;PPn0100000020000=0?PP2P<PCP?14YOP;PPn0100000020000=0?PeX9BP6O1P<PCP?14YYP;PPn0100000020000=0?PeXFWP6O1n10210010100021010210103b0b1W:P6O1n10210010100021110211103b0b1A0?FEe1b>>RFP>P>%a@1]=AC\%>F3[=ZD2PDP@PAP2PVPXp,3HanFYE^p,2m'P2O1=0?EeW?WHo"). Qed.

Lemma bytes_at_unmaps_other : forall A bs,
  bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> bytes_at segs m' A bs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "p'0h06__sat3h14__x1h22a0h32H2h44__x2h51ih61Hh72H3h82H4h97__arithh:4__ffh;6__sat2h<8__varmaph=5__with>4__x3h?4cstrh@2HahA3Hi0hB4__x4hC4__x5hD5cstr0hE1AhF2H0hG2H1hH2H5hI2HdhJ2HihK2bshL1ohM1zi001bi011xp;1p;4p;2p;3p;7p;6p;8p;<g002Sj1>Tg003]j1ZTg004;j1jTg0023j1RTg014Rj4OTg010lj21Tg008dj1XTg00Sij2eTg01`_R0j2=Tg004^R1j1`Tg00oWR2j14Tg00U=j23Tg00cBj1@Tg01a7j3ETg01ajj3<Tg007Jj3;Tg00TbR3j28Tg018Ij1MTg00Y4j2iTg00TFR4j22Tg00Y\j3fTg00Z@j2dTg00ASj2FTg00Qdj1cTg00Zaj2BTg00[?j1bTg00[]j1aTg00\Hj2STg00\kj2ATg00=ej1_Tg00_dj2^Tg00`Fj2]Tg00a2j3\Tg00aQj4[Tg01<Zj1xTg01@Yj3NTg00^9j3wTg006hj2vTg01bHj2uTg017bj4qTg019jj1ITg01:Ij2CTg01GBj2HTg00SIj3GTg0038j1WTg00V6j2oTg00^\j7nTg00d4j2mTg000ij6UTg02@Kj2lTg00CVj4TTg00UZj2JTg019Pj2kTg00]Nj4YTg00fKj7PTg00_@j8hTg01=8j4pTg01F4l<gTg01FYj3sTg01Gnj7tTg00foR5f0R6'Jp=0f2R7f1R8#4'3/J6p=61J86,k7p=91378/J6p=DP7g00gMR9g00glR:P:g00hLR;g00HNR<P8g00kZP6CYg00hlR=FPp=7f3R>P9P:P:P;P7P8P6Ghp=5P<P7P8P6Cpp=?g00OLR?P<P0P2P4g01dHf5R4f4R2P>P7P8P6M<gp=r%46,38p=QAs<86p=:P<P8g00lAP6CYp=KP8P9P:P:P;P6P=FPp=LP7P9P:P:P;P8P6Ftp=Vg00GiR=#>R0#>R@#>RA#Z#jRB#Rp,4segsRCp,1mRDP8P6COP3%0711B8%X0RE%>A#>#>RA#XRF'eRG56711B7RH,=6%`BRI%48RJ,32#@9ECDA<B>83;[^5?'8p,1aRK96>Hp,1nRH,3KRL;9>PCp,2m'RMP2P>CO[P6%0211B2=64G11B4RN,=6f7RO/3J#@9ECDf6RP=<B85;I[^5?'8P3A6PNG11BPRN,=6f8RQ/3J#@9ECDA<BO85;I[^5?A6ONK?9LOPCPMPQPOCO[P611BO=6QGf9,1BRO,=6f;RN/3J#@9ECDf:RR=<B85;I[^5?A6ROK?9LR%0N11BRRR#4RO=DNGRS11BN,=6RTf=RU/3JRV#@RW9ECMf<RX=<B85;IRY[^5?RZ'8%MRRR%0ORO1iEFR[125ER\%0F125G[R][R^%0ER_g00ilR`AfEF8UW@RF%0G\`^@_R_p,2HaR`%0KRa12KGRb'8RcP3PaPbf@Rd#0P6p,2HnRe%0HRf12HGRg'8RhP3PfPgfERi#0P6PNg00jH1d5E'FP\eO1R\P]g00jnRN#cRj%RNRk1B<8%b<Rl%a<Rm1S<5Rn1A<=Ro57mRp%_:RqPpC51^m;RrP6P7g00HlRsg00ILRt'F1]67=;stdA\<58C[R5b:b<b=X1<%06%08Rt[^1<P6fJRsPiO2b9b0X8gX7fP8P6O2n2001000000120000000b2X3bX6aP8P6O2n2001000000121000000b2b;b0b?PSPZPRPOP[P^PFP_P`PcP3PaPbf?RO,1B=6dGP6PePhP3PfPgfDRR,1B=6iGP6P\P]PjPk1B<7RZ%x<RS7?8PlPm1A<0Ru9N<oRv1S<E%ZARA5w<RE57mRwPqPwC5PrP5b:b<b=X1<X4<AD68GAD87G[^1<^4<P6fIRw,1B#4PsfAO3b9b0X8gX7fP8P6O2n2001000000121000000b2X3bX6aP8P6O2n2001000000121000000b2b;b0b?PIPDPWO1P1PBPIP61vB6f>R1%47RD'3#@,uCn10110100021010000A<BU75;IXLIP>P8P6O2PMPWO1P<PV126K?9L6XM<11BXRX,=8%4XRM,2JRIP8PJ1F<JPXPM1F<MErP6CqRMPI%M7RX%0DRD11B1R1#MRJ%41#0R1P[P^PFP_P`PcP3PaPb1QRQRR/2K?9LRP6PePhP3PfPg1QwURU/2K?9LUP6P\P]g01O?RL#IRQ#IRC#IRs#I,C<Rx1C<CRC1C<LRL':Ry':g01L<Rz'H1C<sRs1C<QRQ,:C':/Hz=GNj5GNPk1B<2??7S1B<4??>S7?8PlPmA7mnuRCPqPm%W0,A<R0,Ku,LmRuPqPmAN<o0R0%W=,A<R=57m1A<@9N<=R@=7mo5VmPq1Kv=,LmA7m@v5VmC5C5C5PrP5b:b<b=X1<X4<X><XB<XC<1274AD7P21324R@;9713>2R=/24134P;9=[[\t^1<^4<^><^B<^C<P6fM,1B#4RBPHPKfB#4RKfNRHPOPdfCO8b9b0XHgX8fP8P6O2n2001000000121000000b2X7bX3aP8P6O2n2001000000121000000b2b;b0bDb?bA1oAWPMPIPXPDPJP1P[P^PFP_P`PcP3PaPb%0R12RG'8P6PePhP3PfPg%0U12UG'8P6P\P]1:QL,:x/Hz1:sy/Hz=GNj5GNPk1B<>??>S9?Z8PlPmPCPqPmPuPqPmA7m0EPqPmPpPqPmP9P:P:P;A7mnv1KvE,LmFnC5C5C5C5PrP5b:b<b=X1<X4<X><127>AD72G%0>%0@12@G'8[[[\t^1<^4<^><P6PBPKPHPOPdPiPwO7b9b0X8gX7fP8P6O2n2001000000121000000b2X3bX6aP8P6O2n2001000000121000000b2b;b0bDb?bA,mVEU,lWEUPYeXJTX5?CTCTWIW6WGP8P6O2n2001000000121000000W3WFP8P6O2n2001000000121000000W3WKXE<o"). Qed.

Lemma wr_at_unmaps_other : forall A k,
  wr_at segs m A k -> (A + k <= a \/ a + n <= A)%Z -> wr_at segs m' A k.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "p'0h06__sat3h14__x1h22a0h32H2h44__x2h51ih61Hh72H3h82H4h97__arithh:4__ffh;6__sat2h<8__varmaph=5__with>4__x3h?2Hah@4__x4hA4__x5hB1AhC2H0hD2H1hE2H5hF2HdhG2HihH1khI1ohJ1zi001bi013segi021xp;4p;1p;2p;3p;6p;7p;8g0107j4LTg002Sj1>Tg008dj1HTg00Sij2xTg003]j1UTg004;j1aTg004^R0j1^Tg00U=j22Tg00cBj1:Tg01Y=j3BTg00=ej1WTg007Jj38Tg01V_j1;Tg00TbR1j2<Tg00Y4j2iTg00TFj24Tg00Y\j3gTg00Z@j2fTg00ASj2MTg00Qdj1cTg0023j1bTg00Zaj2@Tg00[?j1`Tg00[]j1_Tg00\Hj2NTg00\kj2?Tg00_dj2]Tg00`Fj2\Tg00a2j3[Tg00aQj4ZTg01<Zj1YTg01@Yj3FTg00^9j3XTg006hj2wTg00V6j2GTg01Z:j3vTg01[>j1uTg01\@j1tTg01]?j1pTg01^=j1oTg016Ej2nTg01^[j1mTg01_9j2jTg019jj1ETg01:Ij2ATg01GBj2DTg00SIj3CTg0038j1STg00d4j2hTg000ij6VTg02@Kj2kTg00CVj4OTg00UZj2ITg019Pj2lTg00]Nj4TTg00fKj7PTg00_@j8eTg01=8j4dTg01FYj3qTg00^\j7rTg01Gnj7sTg00foR2f0R3'Ip=0f2R4f1R5'2/I3p=11453,<4p=31I53,l4p=6P4g00gMR6g00glR7P7g00hLR8g00HNR9P5g00kZP3CTg00hlR:FPp=5f3R;P6P7P7P8P4P5P3Gep=9P9P4P5P3Cdp==Aq953p=7P9P5g00lAP3CTp=KP5P6P7P7P8P3P:FPp=JP4P6P7P7P8P5P3Frp=QP4P6P7P7P8P5P3Fsp=Rp,4segsR6p,1mR:P5P3CLP1%04R<g00GiR=#>R>#HR?%>>R@#>RA#>#>#>RB#HRC'xRD9145%03RE?334%UA#aRA#^RFf4RG/25#:9B6:%WARH38#;[^59'<p,1aRI91;4p,1nRJ,2IRK;6;P6p,2m'RLPGP;CL[P3%0Gf5RM?1GDA3E3Mf7RN/25#:9B6:=8FH#;[^59'<P1f6RO?1MDA3E3Of8RP/25#:9B6:=8FH#;[^59A1NOI?6KNP6PLPPPNCL[P3A1PNDf9RP93E3f;RN/25#:9B6:=8FH#;[^59f:RO?1PI?6KO%0NA1NODRPA3E3NRQf=/25RR#:RS9B6L=8FH#;RT[^59RU'<1i?CRV142?RW%0C142D[RX[RY%0?RZg00ilR[Ag?C5UW?RC%0D\[^?ZRZp,2HaR[%0IR\14IDR]'<R^P1P\P]f?R_#0P3p,2HnR`%0JRa14JDRb'<RcP1PaPbfDRd#0P3PNg00jH1f2?'MPWeO1RWPXg00jnRN#cRe%bNRf1@95%`9Rg%_9Rh1N92Ri1?9=Rj55hRk%W7R7PkC91]h8R8P3P4g00HlRlg00ILRm'M1\34=8lmdA[925CZR2b:b<b=X19%05Rm\E^19P3fIREPdO2b9b0X8bX7aP5P3O2n2001000000120000000b2X3]X6\P5P3O2n2001000000121000000b2b;b0PPPUPVPYPCPZP[P^P1P\P]f>RU=1_DP3P`PcP1PaPbfC=1dDP3PWPXPePf1@94Rd%Y9RP7=5PgPh1?9>Rn9F9jRo1N9?%UBRB5X9R?55hRpP7PpC9P8P2b:b<b=X19X49A135DA154D[^19^49P3fHPEf@REO3b9b0X8bX7aP5P3O2n2001000000121000000b2X3]X6\P5P3O2n2001000000121000000b2b;b0PFP:PSO1P0PAPFP31wA3P0g00EcPF12U4#:,GB%H=5v6PlPF%u3%t312_;#:,GB%p3#o'n#m'jPHn0100000020000PHn10110200021010100n10110200021010000=8FH#;XIFP;P5P3O2PLPSO1P9PR143I?6K3XJ9PVPYPCPZP[P^P1P\P]fA/2MRL/4I?6KLP3P`PcP1PaPbfFRF/2ORO/4I?6KOP3PWPXg01O?RK#ERH#ERl#ER6,A9R01A9lRl1A9HRH'7'7g01L<RA'D%E6,A9R61A9KRK,7lRl'7/DA=CNe5CNPf1@9G?=4P1@9M?=;P7=5PgPhA5hin%S>,?9R>,Kn,Jh5QhRnP7PhAF9j>R>%S=,?9R=55h1?9@9F9=R@=5hj5RhP71Ko=,JhA5h@o5RhC9C9P8P2b:b<b=X19X49X>9X@9XA9A3m5GA15M;12;GR@;65124;R=/4G12GM;6=[[^19^49^>9^@9^A9P3fJR=PJPIP_fKRIPUPEO7b9b0XEbX8aP5P3O2n2001000000121000000b2X7]X3\P5P3O2n2001000000121000000b2b;b01GBSPVPYPCPZP[P^P1P\P]%0L?3LDP3P`PcP1PaPb%0O?3ODP3PWPX170l/DA17HK,76/DA=CNe5CNPf1@9;?=;P9=d5PgPhPnP7PhA5h>?P7PhPkP7A5hio1Ko?,Jh5QhC9C9C9P8P2b:b<b=X19X49X>9A3m54A15;D%0@?3@D\<[[^19^49^>9P3P=P_PIPUfBPFO6b9b0X8bX7aP5P3O2n2001000000121000000b2X3]X6\P5P3O2n2001000000121000000b2b;b0,hREV,kSEVPTeXGQX59COCOWFW6WDP5P3O2n2001000000121000000W3WCP5P3O2n2001000000121000000W3XH9XB9o"). Qed.

Lemma rw_cells_unmaps_other : forall A cs,
  rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> rw_cells segs m' A cs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "h01Hh11Ah22Hbh32Hdh42Hwh53Hwfh62csh71np;1p;4p;2p;6g0023j1DTg00lhj4;Tg00maj48Tg00n[j12Tg00oWj11Tg0107j45Tg00U=j23Tg00UZj20Tg019Pj24Tg012[j17Tg013Uj16Tg014Rj49Tg002Sj1:Tg003]j1CTg004;j1BTg010lj2ATg01enj2@Tg000ij6?Tg02AMj4>Tg00CVj4<Tg02BVj4=Tg00HNg01I[#Dp,4segsR0p,1mR1f1R2f0R3C;g00TbR4P0P1f2R5P2C8P0P1P5%22#1C5f3R6%25#1'3p,1aR7'0p,1n,37R8/06'4P0p,2m'R9f4R:P6C;[P3P0P1P:P6C8P4%7:P0P1f5R4%6:C9P0P1f6R:%24#1C5f7R4%2:#1'3/071084'4P0P9f8R;P4C;[[P3%7:P0P1P;%64C9P0P1f9R1%2;#1C5f:R;%21#1'3/07108;'4P0P9f;R1P;C8P0P9P1%2;R4#1R:C5%7;P0P9P1%6;R9C9P6P1P9P5g00OLR5P4f<R4%13'3/071084'4X75P3g00Gi#:#:#:#C#B/A91@;6E?C>C<P1P:P2P3C=C<W3W4W2W5P2P3O2n2001000000120000000W0P2P3O2n2001000000120000000W0W6W1o"). Qed.

Lemma ro_cells_unmaps_other : forall A cs,
  ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> ro_cells segs m' A cs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "h01Ah11Hh22Hbh32Hdh43Hwfh52csh61np;1p;4p;2p;6g0023j1ATg01i9j49Tg012[j13Tg013Uj17Tg014Rj48Tg00n[j15Tg00oWj14Tg00U=j21Tg00UZj20Tg019Pj26Tg002Sj12Tg003]j1;Tg004;j1:Tg010lj2@Tg01enj2?Tg000ij6>Tg02AMj4<Tg00CVj4=Tg00HNg01I[#Ap,4segsR0p,1mR1f1R2f0R3C9g00Tb%32P0P1f2R4%72C8f3R5%54#4'1p,1aR6'0p,1n,16R7/05'6P0p,2m'R8f4R9P5C9[P3%35P0P1f5R1%79C8f6R9%51#4'1/061079'6%39P0P8f7R8%79R0C8P4P8P0P2g00OLR8%59f8R1%43'1/061071'6X68P3g00Gi#2#2#2#;#:/@01?94E>C<C=W3W2W4P2P3O2n2001000000120000000W1W5W0o"). Qed.

Lemma stk_unmaps_other : forall lo hi, stk segs m lo hi -> (hi <= a \/ a + n <= lo)%Z -> stk segs m' lo hi.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "p'0h02a0h11bi001bh26__sat3h34__x1h42H2h51ah61Hh72H3h82H4h97__arithh:4__ffh;6__sat2h<8__varmaph=5__with>4__x2h?4__x3h@2HahA4__x4hB4__x5hC1ohD1EhE2H0hF2H1hG2H5hH2HbhI2HdhJ2HwhK2HxhL2hihM2lohN1xi011xhO1zi023segp;4p;1p;2p;3p;6p;7p;8g01j2j4OTg002Sj1>Tg008dj1GTg00Sij2}Tg00UZj20Tg00TFj24Tg00TbR0j23Tg003]j1QTg004;j1aTg004^R1j1^Tg00cBj12Tg01Y=j3=Tg00=ej1XTg006hj2NTg01jgR2j2:Tg00U=j2JTg00Y4j2jTg00Y\j3iTg00Z@j2fTg00ASj2STg00Qdj1dTg0023j1bTg00Zaj2BTg00[?j1`Tg00[]j1_Tg00\Hj2PTg00\kj2ATg00_dj2]Tg00`Fj2\Tg007Jj3@Tg00a2j3[Tg00aQj4ZTg00^9j3YTg019jj1FTg01:Ij2CTg01GBj2ETg00SIj3DTg01<Zj1|Tg0038j1WTg01@Yj3{Tg00V6j2ITg00d4j2zTg000ij6LTg02@Kj2xTg01Z:j3wTg01[>j1tTg01\@j1sTg01]?j1rTg01^=j1pTg016Ej2oTg01^[j1nTg01_9j2kTg01bHj2lTg01kAj4mTg00CVj4MTg01V_j1hTg01a7j3gTg019Pj2qTg00]Nj4UTg00fKj7RTg00_@j8eTg01FYj3uTg01=8j4vTg00^\j7cTg01Gnj7yTg00foR3f0R4'0p=1f2R5f1R6;@4#hp=7f4R7f3R8?g56;@4p=51064,q5p=81464,35p=6P5g00gMR9g00glR:P:g00hLR;g00HNR<P6g00kZP4CUg00hlR=FRp=9P8P9P:P:P;P5P6P4Gep=<Au<64p=;P<P5P6P4Cvp=?P<P6g00lAP4CUp=KP6P9P:P:P;P4P=FRp=HP5P9P:P:P;P6P4Fcp=VP5P9P:P:P;P6P4Fyp=Tp,4segsR9p,1mR=P6P4COP0%15g00GiR>#>R?#GR@%>?RA#>RB#>#>#>RC#GRD'}RE,06RF1084RG1445RH'3%QB#aRB#^RI%26RJ9=9=%XBRK37PIP9P=%25RL1NB4RMD5X1B,:B'3RN[^5<'3p,1aRO,05p,1nRP,JORQ;88P9p,2m'RRP7P8CO[P4%17107Ef6RS/04f5RT764PN[^5<'3P010TEf7RU/04?64SPN[^5<10SO?8QUP9PRf8RVPUCO[P410UEf:RW/04f9RX764PN[^5<10XO?8QWf;RY#110WERZf<R[/04?64YR\A=9RJ=7IKPIP9PRPLPMD5X1B,:B'3[^5<RJ'31j@DR]143@R^%1D143E[R_[R`%1@Rag00ilRbAi@D6UW@RD%1E\b^@aRap,2HaRb%1ORc14OERd'3ReP0PcPdf?#1P4p,2HnRf%1PRg14PERh'3RiP0PgPhfDRj#1P4PYg00jH1f3@'SP^eO1R^P_g00jnRk#dRl%bkRm1B<6Rn%`<Ro%_<Rp1P<3Rq1A<>Rr59pRs%X:R:PsC<1]p;R;P4P5g00HlRtg00ILRu'S1\45=@tudA[<36CZR3b:b<b=X3<%14%16[^3<P4fIRuPjO2b9b2X8hX7gP6P4O2n2001000000120000000b0X4dX6cP6P4O2n2001000000121000000b0b;b2PZPJP]P`PDPaPbPeP0PcPdf>RJ/0EP4PfPiP0PgPhfCRZ/0EP4P^P_PlPmPnPoPp1P<@%QCRC5Y<R@99prRnP:PnC<P;P3b:b<b=X3<104EPF[^3<P4fHRFf@O2b9b2X8hX7gP6P4O2n2001000000121000000b0X4dX6cP6P4O2n2001000000121000000b0b;b2P8P6P4O2PNP0A=9=L=7IKPIP9P=%28RLPMD5X1B,:BA=9RL=7IKPIP9PR%27RLPMD5X1B,:B'3P4A=9=L=7IKPIP9P=%2SPMD5X1B,:BP2PBPIP9P=%2URUPMD5X1BA=9RU=7IKPIP9PR%2VPMD5X1B,:B'3P4PIP9P=%2XPMD5%2WRXP<PW144O?8Q4XO<P]P`PDPaPbPeP0PcPd14JO?8QJP4PfPiP0PgPh14ZO?8QZP4P^P_g01O?RQ#FRV#FRU#FR2,C<RL1C<URU1C<VRV';';g01L<RN'E%F2,C<R21C<QRQ,;URU';/EN=Dkl5DkPm1B<7%|<Rn7?51B<T??8n7?6PoPp1A<ARA=9pr%W?,A<Rj,Kr,Hp5VpRvP:Pp1A<?R?99pj%W>,A<9{<?Rw=9pA5TpP:1Kr?,HpA9pwr5TpC<C<P;P3b:b<b=X3<X><X?<XA<XB<A6G4710T51J58;8714581J87;85[[^3<^><^?<^A<^B<P4fSR7fTRTPPPOPFfGROPuO7b9b2XGhX8gP6P4O2n2001000000121000000b0X7dX4cP6P4O2n2001000000121000000b0b;b21ICXP]P`PDPaPbPeP0PcPd%1J?6JEP4PfPiP0PgPh%1Z?6ZEP4P^P_1;LU/EN1;VQ,;2/EN=Dkl5DkPm1B<5??8n1B<8??8n7?6PoPpPvP:PpA9pj@P:PpA9pqAP:1Kr@,Hp9VpsC<C<C<P;P3b:b<b=X3<X><X?<1064/3H108E%18RHA6H8E[[[^3<^><^?<P4P7PTPFPOfKfOO6b9b2X8hX7gP6P4O2n2001000000121000000b0X4dX6cP6P4O2n2001000000121000000b0b;b2,zWEL'xPRPXO1P=PXO15@I%2YRY9=9R=7IKRXPIP9PR%2[R[PMD5X1BRW,:BPIP=PYO1R=P1PBPIP4PMP1g00EcPI1IC[%G>5w9PtPI%t4%s4f=#2,IC%r4#p'o#n'kPKn0100000020000PKn10110100021010200n10110100021010000=7IKXCIPSPRPYO1RSP4ELPXePBPWP5PIP=P1PBPIP4PM1l9[n101101000210100001NB85@IXCIP6PSP4ELPIP9PRPY1NB5D5eCmCMbDWHX1BP6P4O2n2001000000121101000W4WJP6P4O2n2001000000121000000b0XK\XN<CMCMWIW6WFP6P4O2n2001000000121000000W4WEP6P4O2n2001000000121000000W4XL<XM<o"). Qed.

Lemma munch_unmaps : forall W m0, munch W m0 m -> inside W a n -> munch W m0 m'.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "p'0h04__x1h14__x2h22a0h36__sat2h44__p1h54__x3h61Hh72H1h82H2h92H3h:7__arithh;4__ffh<8__varmaph=5__with>2Hah?6__sat1h@6__sat3hA1bi001bhB1li011lhC1ri021rhD2H0hE2H4hF3HinhG2HxhH1WhI2m0hJ2n0hK2n1hL1ohM1xi031np;1p;3p;2p;4p;7p;6p;8g0023j1NTg002Sj16Tg003]j1BTg004;j1>Tg004^j1mTg01k[j3GTg01lRj3]Tg00V6j21Tg01mJj2WTg01nCj2TTg01o6j1OTg00TFj20Tg00TbR0j24Tg007Jj3KTg01V<j2dTg00W=j2MTg01UYR1j2DTg00U=j28Tg00UZj22Tg019Pj23Tg008dj1CTg00Y4j2ZTg00Sij2YTg00Y\j3XTg00Z@j2VTg00ASj2@Tg00Qdj1UTg00Zaj2?Tg01<Zj1STg01=8j4JTg00[?j1QTg00[]j1PTg00\kj2:Tg00=ej1RTg00_dj2lTg00`Fj2kTg00a2j3jTg00aQj4iTg01V_j1LTg01U6j2hTg00V`j2HTg0038j1cTg01@Yj3FTg00^\j7`Tg01o_j7_Tg01`@j2aTg02@Kj2bTg000ij6^Tg00]Nj4ATg00fKj7eTg01I7j6\Tg01Gnj7fTg00_@j8gTg01X<j6[Tg00foR2f0R3'2p=7g00HNR4f1R5g00lAP3CAp=;P5g00gMR6g00glR7P7g00hLR8P3g00hlFep=5P5P6P7P7P8P3E\p==f2R9P6P7P7P8P5P3Ffp=If3R:P6P7P7P8P9P5P3Ggp=9P4P5g00kZP3CAp=<P5P6P7P7P8P3E[p=Eg020c#Ng00GiR;#6R<#6#6R=#6#6#6R>#BR?#>R@%B=#>#mR=[p,1mRA9G53p,1aRBp,1nRC5]9f4RD11?3'W1T?511?5RE#7%O?,0E'4P=PAP9O1f6RAP:O19K=3XL=PDP9P5O2p,2m'R=P9O111?9RE/dB10EB1MEB'D11?:/MBg00HlREP111?D/0B11?ARA/0B18BCRF/2ARG'3P5f5RH,1?/0BRI%C<RJ%C>R>'ZRK102JRL%7>1YJ>RM,02[RN[RO%7JRPg00ilRQAXJ>5UW>R>%7M\Q^>PRPp,2HaRQ%7BRR10BMRS'4RTP0PRPSf:,1?RU/0B12FU'3RVP3p,2HnRW%7CRX10CMRM'4RYP0PXPMf?,1?RZ/0B12FZ'3P3f;RZg00jH1V2J'@PLeO1RLPNp-0RJg00jnR[#UR\%N[R[P41?49R]P5%S4CJ%Q4R^%P4R_1:4;R`1:4<R<';,5_Ra%R7Rb1=_D9I_aC91l_8RaP3P9g00ILRc,@E1k39=KEcdAj425CiR2b;b<b=X04X14W410351059/3:[^04^14^4JP3fD,1?Rc,2FPBPcf>RcO4b:b3X9MX8XP5P3O2n2001000000121000000b2X7SX6RP5P3O2n2001000000121000000b2b?b3WBP3O1%LI1hFA1HFA,DGf7,1?,HFPEP1f8,1?,2FPVP5f9R1,1?,2FREPKPOP>PPPQPTP0PRPS11?cRG/0B12FG'3P3PWPYP0PXPMfC,1?RA/0B12FA'3P3PLPNP\P[P4P]P51?4:CJR]P^P_%c;,:4R;9F4</<`,5_RIPb1=_H=I_IC9PaP2b;b<b=X04X14X54X4J1859/23189:/25,3D[^04^14^54^4JP3fH,1?R?/0BPCPBP?PcO5b:b3X9MX8XP5P3O2n2001000000121000000b2X7SX6RP5P3O2n2001000000121000000b2b?b3WBP3O1%LEPcPBPCPUPZPKPOP>PPPQPTP0PRPS12BG10GF'4P3PWPYP0PXPM12BA10AF'4P3PLPNP\P[P]P^P_AF4`;R;/<<,5_,E_PbP_1;<`,5_,E_PbP_P6P7P7P81<`<,5_1;<;,5_F`C9C9PaP2b;b<b=X04X14X541839/25g01X`R2[1095P2[129:189D,0:'4[[^04^14^54P3PCP?PBPcfBO5b:b@XEMX9XP5P3O2n2001000000121000000b2X8SX7RP5P3O2n2001000000121000000b2b3b@P1F_,aVWKP3O1n10210010200021110111103bAbCWJP3O1n10210010200021110111103bAbC,b9E^bDWGXM@AG:9=eWFW6WIWHo"). Qed.

Lemma mem_inv_unmaps : mem_inv segs m -> mem_inv segs m'.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "p'0h02Hxh11xh21Hh34Hinvh41bi001bh52b0h61eh71oi011op;2p;1p;4p;3p;7p;6g01R:j2KTg002Sj11Tg003]j19Tg004;j13Tg023Fj4JTg004^R0j1CTg006hj22Tg007Jj30Tg00Jmj2>Tg00cBj1=Tg005@j2<Tg00ekj4;Tg00Qdj1:Tg00SIj3ITg00Lbj3HTg00doj38Tg00=ej1BTg02?Fj7ATg000Mj66Tg022Oj25Tg00V6j24Tg00TFj27Tg00Tbj2@Tg01`@j2?Tg024Gj6DTg025Aj6ETg00CVj4FTg026Aj4GTp,4segsR1p,1mR2'KP1p,2m'R3g00Gi#1#1#1R4#1#1#1#9R5#3R6P1P2f0R7f1R8CJW1%94#3R4%C4R9P3P8O1124730P91>66R3P6P6p,1aR:#=p,1nR;,<5C;%:33If2R35H212439097X79P7g00HlR<P9A8:;3%B4R=P2P3O1n0100000020000R>P2P:P;P3p,2Hap,2Hnp,3HanFAE61248909>f3R>98:;P<P<P<P9P7P=P2f5R;O1n0100000020000f4R:,24R3509f6R?,51g00iLR@50<145?g027>RA'7'@RB]0P7124>R>909=P9P=P0P4p-0P7g01X`R4g00iln10110100021000000X69g00IlP3P7E6P41?B7b2W0P2P:O1=09>151;=0<@145;/7AP1P2P;P:P?P7EDP1P2P;P:P?P7EECFW0n0110000020000P8O1b5b0W0W4X16CGW3o"). Qed.

(* [comment removed for export] *)
End Unmaps.

End MemEffects.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_cells_wr_at : forall segs m A cs n,
  rw_cells segs m A cs -> (n <= Z.of_nat (cells_size cs))%Z -> wr_at segs m A n.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h06__sat3h14__x1h21ih34__x2h44__x3h52H2h67__arithh74__ffh86__sat2h98__varmaph:5__with;4cstrh<2Hah=1Ah>1Hh?2H0h@2H1hA2HihB2HnhC2_HhD2cshE1mhF1nhG4segsp;1p;4p;2p;3p;7p;8g0023j1FTg002Sj18Tg003]j1MTg004;j1ITg004^j1hTg00lhj4aTg00maj4NTg0107j4:Tg00UZj20Tg00U=j22Tg008dj1GTg00Sij2gTg00TFj25Tg00TbR0j24Tg00cBj1=Tg01Y=j3;Tg00=ej1KTg007Jj37Tg01V_j1<Tg00n[j1DTg018Ij1LTg00oWj1BTg00Y4j2\Tg00Y\j3[Tg00Z@j2ZTg00ASj2JTg00Qdj1YTg00Zaj2@Tg00[?j1XTg00[]j1WTg00\Hj2HTg00\kj2?Tg00_dj2VTg00`Fj2UTg00a2j3TTg00aQj4fTg019jj1STg01:Ij2ATg01FYj3QTg01GBj2eTg00SIj3dTg01=8j4CTg0038j1bTg01@Yj3PTg00^9j3`Tg01<Zj1_Tg00]Nj4ETg00CVj4OTg00fKj7^Tg00_@j8]Tg00^\j7cTf0R1#D#Bp=1g00foR2/01p=3g00HNR3f1R4g00kZP1CEp=9P4g00gMR5g00glR6P6g00hLR7P1g00hlF^p=6f3R8P5P6P6P7f2R9P4P1G]p=>P9P5P6P6P7P4P1Fcp=Rg00Ec#Fg00GiR5#8R:#8R;#8R<#8#8#8R=#MR>#I%M<#IR<#hR?[g01I[#Ff4R@P8P9P4CaP0f5RAP@P8P9CNPAP@P8%19C:%18,09f7RBf6RCPAP8C:[P1PBPCPAP@CNf8PBPC%1AC:P0%3B%1C,2B%G:R@%G=R='gRD'0%31RE%1BRF,51'4f;RGf:RHf9RI/24#=3;%K<R<57?#<[^23'410CFPGPHPIPBC:[P1%3I%1I,2H/0D%1HRI,51,4Ef>RFf=RJf<RK/24#=3;=7?<#<[^23'4P012GI/0D%1GRI,51,4Ef?R012J4#=7;F=7?<#<[^2310HIP0PFPJPGC:[P1%1K,2J/0D%1FRK,51,4EfBRIfARHf@RL/24#=3;=7?<#<[^2310JK%3L12LF/0DRL1510,4ERFfDRKfCRJ12I4#=3;=7?<#<[^23R<'4%D0R0#LR?%B0#3R01\@=RI152@RM%3=152D[RN[RO%3@RPg00ilRQA[@=4UW<R=%3D\Q^<PRPP4g00jH1Z2@'JPMeO1RMPNg00jnRQ#YRR%FQRS1@34%X3RT%W3RU1H321?35RV'9,6URW%K6R6PWC>1VU7R7P1P9g00HlRXg00ILRY'J1U19=7XYdAT324CfR2b7b9b:X13%34\E^13P1fERYPGO2b6b0b8b0b;PLP<P?P0PIPOP=PPPMPNg01O?R0#SR?#S,A31A3?1A305Q35Q3g01L<'e=dQRRRPSP31@39P41@38RQCCPTPU1?3:R:%b5,?3R5'9,6UP6PUAP3V51H3@=`3>R>'9,6UP6AP3V:/9>,6UC>C>P7P2b7b9b:X13X33X4310491248/0D1298/0D[[^13^33^43P1%1KPJPYPAPBO5b6b0b8b0b;P8P4%DHRH#L%BH#3PIPOP=PPPMPNPRPSP3P3PQP9%_3RQCCP4PQCCPTPUP3PVg00lART1?3;R;CE,6U9RUWP6PU19;:,6UP6P3PVPTP:CE,6U9RUWC>C>P7P2b7b9b:X13X33X431519,4E1089%391598'4[[^13^33^43P1PYfF#1PCPAPBO5b6b0b8b0b;O2XAFX23COCOWBW>W@P4P1O2n2001000000121000000W5W?P4P1O2n2001000000121000000W5WCP4P1O2n2001000000121000000W5XF3WDX=3WEWGo"). Qed.

(* [comment removed for export] *)
Lemma rw_cells_below : forall segs m A cs,
  mem_inv segs m -> rw_cells segs m A cs -> (0 < cells_size cs)%nat -> (A + Z.of_nat (cells_size cs) <= UTOP)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h04__x1h11Ah21Hh32Hnh43Hn0h52MIh61Wh72_Hh87__arithh94__ffh:8__varmaph;5__with<2csh=4cstrh>1mh?4segsp;1p;2p;4p;7p;8p;3p;<g0023j13Tg002Sj12Tg003]j18Tg004;j19Tg004^j1STg01R:j2RTg00lhj4LTg00maj4:Tg00n[j10Tg00oWR0j11Tg0107j47Tg01`_R1j25Tg00U=j2<Tg00UZj2;Tg00TFR2j26Tg00ASj24Tg017bj4PTg018Ij1NTg00Qdj1KTg00Zaj2HTg00[?j1ETg00[]j1CTg00\Hj2BTg00\kj2DTg00]Nj4ATg00fKj7FTg00=ej1GTg00_@j8@Tg00_dj2ITg00`Fj2JTg007Jj3?Tg00a2j3>Tg00aQj4MTg02C\j7=Tg01F4l<OTg00OLg00HNR3P1P0P2g01dHg01O?R2g00foR0f3R1f2R4f1R5f0R6M<Op=Qg00Ec#3g00GiR7#2#2#2R8#2#2#2#8#9%88#9#S[g01I[#31R14f4R8P1P4P5CLg00Tbf5R9P8P1P4C:P9P8P1%04#1C7%01,52%08#1,<9g027>';[P6f7R1f6R:P9P8C:f8R8P1P:%09#1C7%0:,52f:R9f9P8%01R1#1R;P:P51521160;R21430P1P;143;CQP6CPP2%08R8#N%18,;0g00jnR8#K%381H35%E3%C3R8g00gMR2g00glR;P;g00hLR1P8P2P;P;P1P31B30g00lA1D37CAg00hlFFR7%G;P7G@1I81P6P4g00HlR1g00ILR8'41J64=?18dA>305CMb9b:b;X0316061605[^03P6%09#1P4O2b8b=b4F=W3W6W7P5P6O2n2001000000120000000W2W5W<X13W>W?o"). Qed.

Lemma u8arr_below : forall segs m A bs,
  mem_inv segs m -> u8arr segs m A bs -> bs <> [] -> (A + Z.of_nat (length bs) <= UTOP)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01Ah11Bh21Hh33Hneh42MIh52_Hh62bsh71mh84segsp;1p;2p;4p;3p;7g0023j16Tg002Sj10Tg003]j14Tg004;j17Tg004^j1@Tg01R:j2<Tg02DWj4;Tg014Rj45Tg010lj21Tg00oWj12Tg0107j43Tg00Qdj1:Tg007Jj38Tg01V_j19Tg00U=j2?Tg00UZj2>Tg02ELj7=Tg00Ec#6g00Gi#0#0#0R0#0#0#0#4#7%40#7R0#@[g00HN%60R1f3R2f2R3'<f4R4P2P3f1R5C;g00Tbf5R6P4P2P3C5P6P4P21103#2C3%:0R79812#91104#2,?6g027>'>[f0R2f7R8f6R9P6P4C5f8R4P8P91106#2C3A8197#9f:f9P4P8P9P3P2F=W3W5W1P5P2O2n2001000000120000000W2W4W6W0W7W8o"). Qed.

Lemma stk_below : forall segs m lo hi,
  mem_inv segs m -> stk segs m lo hi -> (lo < hi)%Z -> (hi <= UTOP)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01bh16__sat3h24__x1h34__x2h41ah57__arithh64__ffh76__sat2h88__varmaph95__with:1Bh;2H2h<2Hah=1Hh>2H0h?2H1h@3HlthA2MIhB1WhC2_HhD2hihE2lohF1mhG4segshH1zp;1p;2p;4p;3p;5p;6p;7p;8g0023j1NTg002Sj1<Tg003]j1ITg004;j1GTg004^j1iTg01R:j2^Tg01j2j4ZTg008dj1ATg00Sij2STg00UZj21Tg00TFj20Tg00TbR0j23Tg00cBj16Tg01Y=j37Tg00=ej1LTg007Jj32Tg01V_j19Tg01a7j3:Tg006hj2YTg01jgj28Tg016Ej25Tg00Y4j2XTg00Y\j3WTg00Z@j2VTg00ASj2HTg00Qdj1UTg00Zaj2TTg01<Zj1RTg01=8j4QTg00[?j1PTg00[]j1OTg00\kj2FTg00\Hj2@Tg01=Vj3ETg00_dj2hTg00`Fj2gTg00a2j3fTg00aQj4cTg02FJj5bTg00V6j2JTg019jj1BTg01:Ij2CTg01FYj3KTg01GBj2]Tg00SIj3_Tg00^9j3`Tg00d4j2\Tg000Mj6aTg00]Nj4MTg00fKj7[Tg00^\j7dTg00_@j8eTg00foR1f0R2'1p=;g00HNR3f1R4g00lAP2CMp==P4g00gMR5g00glR6P6g00hLR7P2g00hlF[p=4P3P4g00kZP2CMp=?f2R8P5P6P6P7P4P2Fdp=Df3R9P5P6P6P7P8P4P2Gep=>g00Ec#Ng00GiR5#<R:#<#<R;#<#<#<R<#IR=#G%I;#GR;#iR>[1^98f4R?P9P8P4CZP0%;9R@%A:RA%A<R<'SRB,1811?21029'3f7RCf6RD%64RE37%L;RF52>#9f8RG%68RH7:C1Y;2RI52>X0;,8;'3[^43'310?9g027>RJ,1?[P2f5RK#;11KB11C2102D'3f:RKf9;7E=2>F#9f;RL?:KH=2>IX0;,8;'3[^43'3P011DB11G2102C'3A7LKE=2>F#9f<RD?:LH=2>IX0;,8;'3[^4310GC11GJ[P211GB11L2102K'3f>RGf=RC;7E=2>F#9f?RE?:GH=2>IX0;,8;'3[^4310LKP4%A5RH,5LRL1XA<RM101ARN%;<101B[RO[RP%;ARQg00ilRRAWA<4UW<R<%;B\R^<QRQP4g00jH1V1A'HPNeO1RNPOg00jnRR#URS%NRRTP31T38P4%R3CQRU%P3RV%O3RW1F35R51F3:R:'=,4W%L6R61@3HRX9E3:RY,?5,4W1=Y:,4W5DWC>1hW7R7P2P8g00HlRYg00ILRZ'H1g28=2YZdAf314CcRZb6b8b9X23X331024158HRY,1410Y8'3[^23^33P2PEf@RYP?O3b5b1b7b1O2%6L97GC=2>F#915DH#6RL9:EG=2>IX0;,8;'3P0A7EGL=2>F#915CH#69:YE=2>IX0;,8;11CJP2fARC15GH#677Y=2>F#9fCRFfBRG15YH#6RL3:=2>IX0;,8;PFPGPLPEP4Db1J=L/0JP315CHRC#6,J=102JXH3P2PCPMPPP<PQPNPOg01O?RL#BRE#B#B,C31C3E1C3L5K35K3g01L<']=_RSPTPUPVPW1=:5,4WP6PW1@3A=`3=R=,?5,4WP6PW1@31R1/?:,4WP6AE35XRX,?1,4W1=X=,4W5DWC>C>C>P7PZb6b8b9X23X331042114B159HR9#;109B'3\@[[^23^33P2fFR@fEPKPDPYO5b5b1b7b1,\CEa10CJPMPPP<PQPNPOPSPTPUPVPW1=X:,4WP61?5:,4WC>P7PZb6b8b9X23X33152H/041148[^23^33P2PJP@P?O3b5b1b7b1b:b:WCWBP4P2O2n2001000000121000000b4W@W=W?P4P2O2n2001000000121000000W;W>P4P2O2n2001000000121000000W;WAXD3XE3WFWGo"). Qed.

Lemma rw_cells_bytes_at : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h02H0h11Ah21Hh32_Hh43_H0h52csh61mh74segsp;1p;4g0023j1:Tg002Sj10Tg003]j17Tg004;j16Tg004^j1<Tg00lhj4;Tg00maj48Tg00n[j14Tg00oWj13Tg0107j45Tg013Uj11Tg014Rj42Tg012[j19Tg00Ec#:g00Gi#0#0#0R0#0#0#0#7#6%70#6#<[g00HNg01I[#:f3R0f2R1f1R2f0R3C;g00TbR4f4R5P0P1P2C8P5P0P1%42#3C5f5R6P5P0%11C2P3f6R1P6P5P0C8P4%95f7R4P1P6%15C2f8R5P4P1%46#3C5f9R6P5P4%11C2[P3%91f:R1P6P5%14C2f;P1P6%45#3C5P2W4W2W3P2P3O2n2001000000120000000W0P2P3O2n2001000000120000000W0W5W1W6W7o"). Qed.

Lemma ro_cells_bytes_at : forall segs m A cs, ro_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01Ah11Hh22H0h32_Hh42csh51mh64segsp;1p;4g0023j16Tg002Sj10Tg003]j14Tg004;j13Tg004^j18Tg01i9j47Tg012[j15Tg013Uj11Tg014Rj42Tg00Ec#6g00Gi#0#0#0R0#0#0#0#4#3%40#3#8[g00HNg01I[#6f3R0f2R1f1R2f0R3C7g00Tb%52f4R4P0P1%12C2f5R5P4P0%11C2P3%50f7f6P5%14C2P3W1W3P2P3O2n2001000000120000000W2W4W0W5W6o"). Qed.

(* [comment removed for export] *)
Ltac at_node_solve :=
  at_node_red; split_spine;
  first [ reflexivity | lia | assumption
        | symmetry; apply Z_to_bv_bv_unsigned
        | lazymatch goal with
          | |- wr_at ?segs ?m ?A ?n =>
              match goal with H : rw_cells segs m A ?cs |- _ =>
                apply (rw_cells_wr_at segs m A cs n H); cbn [cells_size csize]; lia end
          | |- bytes_at ?segs ?m ?A ?bs =>
              match goal with
              | H : rw_cells segs m A ?cs |- _ =>
                apply (bytes_at_ext segs m A _ bs (rw_cells_bytes_at segs m A cs H));
                cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
              | H : ro_cells segs m A ?cs |- _ =>
                apply (bytes_at_ext segs m A _ bs (ro_cells_bytes_at segs m A cs H));
                cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
              end
          end
        | idtac ].

(* [comment removed for export] *)
Ltac sys_mem_write :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (Z_to_bv 64 ?B) ?bs) ?ro) =>
    change (write_to_mem m (Z_to_bv 64 B) bs) with (write_to_mem m (wa B) bs);
    lazymatch goal with
    | H : rw_cells segs m B [CB ?n ?junk] |- _ =>
        let HB := fresh "HB" in
        pose proof (rw_cells_bound segs m B _ H) as HB; cbn [cells_size csize Nat.add] in HB;
        (try lazymatch goal with
         | HI : mem_inv segs m |- _ =>
             let HI' := fresh "MI" in
             pose proof (mem_inv_syswrite segs m B n junk bs HI H ltac:(lia)) as HI'; clear HI; rename HI' into HI
         end);
        let H' := fresh "DST" in
        pose proof (rw_cells_CB_prefix_write segs m B n junk bs H ltac:(lia)) as H';
        clear H;
        transport_chunks segs m B bs;
        footprint_after_store segs m B bs;
        let m' := fresh "m" in
        gen_mem (write_to_mem m (wa B) bs) m';
        clear HB; try clear m; rename H' into H
    | _ => fail "sys_mem_write: no hypothesis rw_cells" segs m B "[CB _ _]"
    end
  end.

(* [comment removed for export] *)
Lemma apply_mem_zeros : forall m z, apply_writes (apply_zeros (apply_unmaps m []) [z]) [] = apply_zeros m [z].
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01mh11zp;1p;2p;3g002Sj10Tg003]j12Tg004;j11Tg004^j13Tg00Jmj28Tg00Qdj17Tg00SIj36Tg00M[j24Tg00ASj25Tg00Gi#0#0#0R0#0#0#0#2#1R1%20#1#3[R01811R1f1f0%71561'4,50W1W0o"). Qed.
Lemma apply_mem_unmaps : forall m u, apply_writes (apply_zeros (apply_unmaps m [u]) []) [] = apply_unmaps m [u].
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01mh11up;1p;2p;3g002Sj10Tg003]j12Tg004;j11Tg004^j13Tg00Jmj28Tg00Qdj17Tg00SIj36Tg00Lbj24Tg00ASj25Tg00Gi#0#0#0R0#0#0#0#2#1R1%20#1#3[R01811R1f1f0%71561'4,50W1W0o"). Qed.

(* [comment removed for export] *)
Ltac transport_zeros segs m a n Ha Hn Han :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_zeros_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_zeros segs m a n Ha Hn Han A2 n2) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ => apply (stk_zeros segs m a n Ha Hn Han lo hi) in H
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_zeros m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
            | fail 100 "zero-filled range not inside the declared footprint" ]
  | H : wmono segs ?m0 m |- _ => apply (wmono_zeros segs m a n Ha Hn Han m0) in H
  | H : mem_inv segs m |- _ =>
      let H' := fresh "MI" in
      assert (H' : mem_inv segs (apply_zeros m [(wa a, Z_to_bv 64 n)]))
        by (apply (mem_inv_zeros segs m a n Ha Hn Han H); first [assumption | unfold UTOP; lia | intros; shelve]);
      clear H
  end.

Ltac sys_mem_zeros :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_zeros ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
    let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
    change (apply_zeros m [(A, Z_to_bv 64 n)]) with (apply_zeros m [(wa a, Z_to_bv 64 n)]);
    let Ha := fresh "Hza" in let Hn := fresh "Hzn" in let Han := fresh "Hzan" in
    assert (Ha : (0 <= a < 2^64)%Z) by lia;
    assert (Hn : (0 <= n < 2^64)%Z) by lia;
    assert (Han : (a + n <= 2^64)%Z) by lia;
    transport_zeros segs m a n Ha Hn Han;
    let Z' := fresh "ZNEW" in
    pose proof (rw_cells_zeros_new segs m a n Ha Hn Han) as Z';
    let m' := fresh "m" in
    remember (apply_zeros m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm;
    clear Heqm Ha Hn Han; try clear m
  end.

Ltac transport_unmaps segs m a n Ha Hn Han :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_unmaps_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ =>
      first [ apply (wr_at_unmaps_other segs m a n Ha Hn Han A2 n2) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ =>
      first [ apply (stk_unmaps_other segs m a n Ha Hn Han lo hi) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_unmaps m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
            | fail 100 "unmapped range not inside the declared footprint" ]
  | H : wmono segs ?m0 m |- _ => idtac "note: dropping wmono (not preserved by an unmap):" H; clear H
  | H : mem_inv segs m |- _ => apply (mem_inv_unmaps segs m a n Ha Hn Han) in H
  end.

Ltac sys_mem_unmaps :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_unmaps ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
    let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
    change (apply_unmaps m [(A, Z_to_bv 64 n)]) with (apply_unmaps m [(wa a, Z_to_bv 64 n)]);
    let Ha := fresh "Hua" in let Hn := fresh "Hun" in let Han := fresh "Huan" in
    assert (Ha : (0 <= a < 2^64)%Z) by lia;
    assert (Hn : (0 <= n < 2^64)%Z) by lia;
    assert (Han : (a + n <= 2^64)%Z) by lia;
    transport_unmaps segs m a n Ha Hn Han;
    let m' := fresh "m" in
    remember (apply_unmaps m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm;
    clear Heqm Ha Hn Han; try clear m
  end.

(* [comment removed for export] *)
Ltac sys_nret :=
  rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   | _ => idtac
   end);
  first [ rewrite apply_mem_none
        | rewrite apply_mem_delivered; sys_mem_write
        | rewrite apply_mem_write; sys_mem_write
        | rewrite apply_mem_zeros; sys_mem_zeros
        | rewrite apply_mem_unmaps; sys_mem_unmaps
        | idtac ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Notation errno_addr tp := (bv_unsigned tp + (-164))%Z (only parsing).

(* [comment removed for export] *)
Definition sysret_val (r : word) : word :=
  match errno_of r with Some _ => Z_to_bv 64 (-1) | None => r end.
Definition sysret_errno (r errv : word) : word :=
  match errno_of r with Some e => Z_to_bv 64 e | None => errv end.

Lemma errno_of_big : forall r, (2^64 - 4096 < bv_unsigned r)%Z -> errno_of r = Some (2^64 - bv_unsigned r)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "p'0h02Hah14__p1h26__sat1h34__x1h41Hh57__arithh64__ffh76__sat0h88__varmaph95__with:1bi001bh;1li011lh<1ni021nh=1ri031rh>2r0p;1p;2p;3p;4p;6p;7p;8g002Sj18Tg003]j1OTg004;j1FTg008dj15Tg00Sij2UTg016Ej24Tg00V6j21Tg00TFj26Tg0038j19Tg01U6j2DTg00UZj20Tg00V`j2BTg01UYR0j2YTg004^j1VTg006hj2;Tg00=ej1@Tg007Jj37Tg00ASj2<Tg01V_j1STg00Y4j2RTg00Y\j3NTg00Z@j2MTg00Qdj1LTg0023j1JTg00Zaj2ITg00[?j1HTg00[]j1GTg00\Hj2:Tg00^9j3KTg01=Vj3>Tg00\kj2ETg00]Nj4ATg01X<j6PTg01I7j6QTg00_dj2CTg00`Fj2TTg00a2j3\Tg00aQj4[Tg02GEj1ZTg00fKj7XTg00_@j8WTf0R1#8#8p=3%91#9p=2f1R2g00gMR3g00glR4P4g00hLR5P1g00hlFXp==f3R6P3P4P4P5f2R7P2P1GWp=?g00GiR8#8R9#8#3#3R:#OR;#F%59R9%5:R<'UR=%3:#3#3#5R:'4R>11;1'6%98#2#2#2#2#2#5R?,4=R@11;2RA'D10@A1B@A'Y11;7,B@g00HlRBP011;6,0@g00HNR0#VRCPBPCP2f5,1;,4=,;0RD%@0REn0100000020000;7DP2f4RF,1;,0@RG1<CDW;P1O1%SG1R9<g00foRG/69RD10G<16G=[RH[10G9RIg00ilRJAN9<2UW010G=\J^0IP2g00jH1MG9'<PDeO1PHp-0RHg00jnRD#L%JD1I02%H0%G0RDPDP3P4P4P5P01:09=K0;R91:0?5>0g00kZ1E08R8CA,=DEP%@4R?PDP01:0:9>09g00lAP8CA,=DP?PDP3P4P4P5P6EQC?C?1CD5P1P7g00ILRD,<B1T17=7BDdA\0G2C[b6b8b9X30W110@1g01X`[16>2P6[[^30^1HP1f9,1;R;,4=,;097CEP;PFf8O4b5b2b7b2W<P1O1n10210010300021010111102b:b>%Z214=A,;057CeW4W=o"). Qed.

(* [comment removed for export] *)
Lemma negw_errno : forall u, (2^64 - 4096 < u < 2^64)%Z -> bv_swrap 32 (0 - u) = (2^64 - u)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h06__sat1h16__sat3h22Hah34__x1h47__arithh54__ffh66__sat0h76__sat2h86__sat5h98__varmaph:5__with;6__sat4h<1zh=1Hh>2Huh?1up;1p;2p;3p;4p;8p;6p;7g002Sj1:Tg008dj17Tg00Sij2;Tg016Ej20Tg00TFj23Tg00Tbj2HTg00Y4j2?Tg00Y\j3=Tg0038j18Tg00Z@j2KTg00ASj2GTg00Qdj1dTg0023j1aTg00Zaj2XTg00[?j1WTg00[]j1UTg00\Hj2DTg003]j1CTg00^9j3BTg00\kj2TTg01=Vj39Tg01@Yj3@Tg02H@j2STg02Hcj3RTg00_dj2QTg00`Fj2PTg007Jj3<Tg00a2j3MTg00aQj4LTg00U=j21Tg02IFj1NTg02Icj2OTg02J@j2ETg00=ej1cTg00]Nj4FTg00_@j8bTg02J`j3`Tg000ij6JTg01<Zj1\Tg01X<j6YTg02KCj4ZTg000Mj6[Tg02Kdj2VTg00UZj2]Tg00fKj7^Tg00^\j7_Tf0R0#:#:p=6g00foR1/]0p=2g00HNR2f1R3g01LhP0CFp=>P3g00gMR4g00glR5P5g00hLR6P0g00hlF^p=4A<230p=5P2P3g00lAP0CFp=Af2R7P4P5P5P6P3P0F_p=Ig00GiR8#:R9#7R:%69#6R9#:R;#7R<';R=%6;#6#6#7R>'0/30130='HR?%79R@,?:RA131:RB%2@1;:@RC,31[RD[RE%2:RFg00ilRGA=:@3UW2R@%2C\G^2FRH1?:<RI%2<131=[RJ\BRKA=:<3VGX2FR<%2=\G^2FRL%88#8#8#8RM#7RN,?:RO%2N1;:NRP,31[RQ\BRRA=:N3VGX2FRN%2P\G^2FRFP3g00jH1K1:'GPBeRBO1RGPQf4PBO1RSPJf7PBO1RBPDg00jnRT#dRU%aTRT1X23RV%W2RW%U2RX1D2:R:%C;5B2R;1T28R8592RY%CM9B2:RM5@2RZ%C9R99B2:R:,S2=R2:5@21D21R[=928=@2M'>'41QX6R\P0P7g00HlR]g00ILR^'G1P07=<]^dAM213CLR^b5b9b:X3210=0R]/1PR_%NCR`/OCRa'11010/1P'5^32P0f;RbO1b4b8b1b0b6b0b7b1b;b810=3Rc/1PRd/1a1013R3/1P'5P210=7/1PRe/1aRa1E0C/0Pf3,0=R='5X<2P21EeCRf100P/5=X<2R=P2PeP=PIPKP<PLPOPRPNPFPGPQPSPJPUPTPVPWA92ZM/>Y,4XP\P^b5b9b:X3210_P/5]^32P0f9O1b4b1b0b6b0b7b1PfPAPEP@PHPIPKP<PLPOPRPNPFPGPQPSPJPBPDPUPTPVPWPXP4P5P5P61D2>992;/A8,4X1A8;,4X5IX%c5P2P[g00kZPZCF,4X1AZ:,4X5IXGbP\P^b5b9b:X32%2d13dC'H\?^32P0f<PbO2b4b8b1b0b6b0b7b1b;b89`eCEJ1EaCPeP`PCPAPEP@PHPIPKP<PLPGPJPSPDPUPT%\2PWPXP4P5P5P61>:[,4XEYP\P^b5b9b:A<2C1g01X`[P0b4b1b0b6b0b7b1CZEJ1017/1PP0E[b=1V93/5ceW>X?2o"). Qed.

(* [comment removed for export] *)
Lemma swrap32_small : forall z, (-2^31 <= z < 2^31)%Z -> bv_swrap 32 z = z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h02Hah16__sat1h24__x1h37__arithh44__ffh56__sat0h66__sat3h78__varmaph85__with91zh:2Hzh;6__sat2p;1p;2p;3p;4p;8p;6p;7g002Sj14Tg008dj17Tg0038j16Tg00Sij2=Tg02IFj1ZTg00UZj2@Tg00TFj22Tg00Tbj2<Tg00U=j2:Tg016Ej2ATg007Jj35Tg00Y4j2?Tg00Y\j3CTg00Z@j2VTg00ASj2BTg00Qdj1UTg0023j1TTg00Zaj2QTg00[?j1OTg00[]j1NTg00\kj2LTg00\Hj2;Tg003]j19Tg00^9j38Tg01@Yj3JTg01=Vj3ITg00]Nj43Tg00_dj2HTg00`Fj2KTg00a2j3GTg00aQj4FTg02J@j2MTg02H@j2ETg00=ej1PTg00_@j8DTg02J`j3RTg000ij6STg02Kdj2YTg00fKj7XTg00^\j7WTg00foR0f0R1'@p=0f1R2g00gMR3g00glR4P4g00hLR5P1g00hlFXp=1f2R6P3P4P4P5P2P1FWp=>g00HNR7g00GiR8#4R9#7R:%68#6#6#6R;#7R<'=R=#Z/@1121='<R>P71:2=R?1A1==576X971?:<R@120:RA%0<120=[RB[RC%0:RDg00ilREAC:<2UW0R<%0=\E^0DRFP2g00jH1V0:'BPAeRGO1RHPBg00jnRI#URJ%TIRI1Q72RK%O7RL%N7RMP71L78R81;7:RN%9;587R;5J7RO=I7;g01LhP8C3'11HM5RPP1P6g00HlRQg00ILRR'B1K16=5QRdAG702CFRRb4b7b8X271:1=/A==571^27P1f5O1b3b1b5b1%49#4#4#4R9#7R=,=:RQ,M?1?:=%0=120Q[R6\AAC:=2VEX0D%0Q\E^0DP@PCP<PFPHPBf4PGO1P6PJPIPKPLPMP3P4P4P5P71E7;g00kZR5P8C3,1MP7P8g00lAR8P;C3,1M5>M%P4P71;70P5POC3,1MP7POP8%99R9987NC3,1M5>MGDPPPRb4b7b8X27%0?12?Q'<\>^27P1f8f7O2b3b6b1b5b1b;b69R?QES1Y92=572eW:W9o"). Qed.

Lemma swrap32_high : forall u, (2^64 - 2^31 <= u < 2^64)%Z -> bv_swrap 32 u = (u - 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h06__sat1h16__sat3h22Hah36__sat5h44__x1h57__arithh64__ffh76__sat0h86__sat2h98__varmaph:5__with;6__sat4h<1zh=1Hh>2Huh?1up;1p;2p;3p;4p;8p;6p;7g002Sj14Tg008dj19Tg00Sij2@Tg0038j18Tg016Ej21Tg00UZj2HTg00TFj26Tg00Tbj2DTg00Y4j2:Tg00Y\j3BTg00Z@j2KTg00ASj2GTg00Qdj1`Tg0023j1]Tg00Zaj2VTg00[?j1UTg00[]j1TTg00\kj2RTg00\Hj2ETg003]j1?Tg00^9j3=Tg01=Vj3>Tg01@Yj3ATg02Hcj3QTg00_dj2PTg00`Fj2OTg007Jj3;Tg00a2j3NTg00aQj4MTg00U=j20Tg02Icj2LTg02J@j2CTg00]Nj47Tg00=ej1JTg00_@j8STg02J`j3_Tg000ij6ITg01<Zj1^Tg01X<j6\Tg02KCj4WTg000Mj6XTg02Kdj2YTg00fKj7ZTg00^\j7[Tg00foR0f0R1'Hp=2g00HNR2f1R3g01LhP1C7p=<P3g00gMR4g00glR5P5g00hLR6P1g00hlFZp=3A;231p=5f2R7P4P5P5P6P3P1F[p=Fg00GiR8#4R9#9R:%49#4#4#4R9#4R;#9R<'@R=%88#8#8#8R>#9R?,@:R@'1/H1161='DRA%99RB,::RC160:RD%2B1@:BRE,60[RF[RG%2:RHg00ilRIAB:B3UW2RB%2E\I^2HRJ1::<RK%2<160=[RL\DRMAB:<3VIX2HR<%2=\I^2HRN1::?RO%2?160@[RP\DRQAB:?3VIX2HR?%2@\I^2HRHP3g00jH1K0:'GPDeRDO1RIPPf4PDO1RRPLf7PDO1RDPFg00jnRS#`RT%]SRS1V23RU%U2RV%T2RW1R28R81E2:R:%?;5=2R;5>2RX%?>9=2:R>5A2RY%?9R99=2:R:=Q2:5A2AA28>'<'31PW6RZP1P7g00HlR[g00ILR\'G1O17=;[\dAN203CMR\b6b9b:X42111=R[/0@R]1LEER^'0101@'5^42P1f;R_O1b5b3b1b0b7b0b8b1b;b3113=R`/0@Ra/0^103@'5P2117=/0@Rb/0^R^1C1E/1@f3/1=R='5X<2P21CbERc111@/5=X<2R=P2PbP=PKPMP<PNPOPQP?PHPIPPPRPLPTPSPUPVA>2Y>/<X,3WPZP\b6b9b:X4211]@/5[^42P1f9O1b5b1b0b7b0b8b1PcPCPGPBPJPKPMP<PNPOPQP?PHPIPPPRPLPDPFPTPSPUPVPWP4P5P5P6P2A>2;>g00kZR>P8C7,3WP2P8g00lAR8P;C7,3W5FW%J5P21E20R;P>PYC7,3WP2PYP8P:C7,3W5FWGSPZP\b6b9b:X42%2a16aE'D\A^42P1f<P_O2b5b3b1b0b7b0b8b1b;b39_bEEI1C^EPbPEPEPCPGPBPJPKPMP<PNPOPQP?PHPIPPPRPLPDPFPTPS%^2PVPWP4P5P5P61<:;,3WE\PZP\b6b9b:A;2E0g01X`[P1b5b3b1b0b7b0b8b1b;b3CWEI107@P1EXb=1Y93/5`eW>X?2o"). Qed.

Lemma unsigned_errno_ret : forall e, (1 <= e <= 4095)%Z -> bv_unsigned (errno_ret e) = (2^64 - e)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h04__p1h14__x1h27__arithh34__ffh48__varmaph55__with61eh71zp;1p;2p;3p;4p;6p;7p;8g008dj13Tg00UZj20Tg0038j14Tg00Tbj26Tg016Ej25Tg002Sj11Tg00Sij2ETg007Jj3<Tg00ASj2=Tg003]j1ATg02LKj1?Tg00V6j2>Tg00Qdj1RTg0023j1QTg00Zaj2PTg00[?j1LTg00[]j1KTg00\Hj27Tg00\kj2GTg00]Nj4;Tg01I7j6DTg00=ej1FTg00_dj2CTg00`Fj2HTg00a2j3BTg00aQj4ITg02MCj3JTg000ij6@Tg00fKj7MTg00^\j7NTg00_@j8OTf0R0#4#4p=2f1R1g00gMR2g00glR3P3g00hLR4P0g00hlFMp=:f2R5P2P3P3P4P1P0FNp=8f3R6P2P3P3P4P5P1P0GOp=9g00HNR7g00GiR8#3R9/00R:%48#2#2#2#2#2#3R;,00R<'6P7g02NI/51%18R=#3%1=#1#1#1#1R=#3'ER>/559<70X7715>1,=7%A=%?1'>p-0R=g00jnR>#RR?%Q>R>1P71R@%L7RA%K7RBP71779g00kZRC1G78R8C;,:BRDPBP2P3P3P4P6EDR658B%F3R3PDC91CB4R4P0P5g00HlRDg00ILR2'=1H05=<D2dg00fo=B71CIR2b3b4b5X17W016:11091[^17^0=P0105;P5P1O3b2P?P>P@PAPBP7P8PC177;C;,:BRC98B6P3PCC9P4P2b3b4b5X17X0=161<101;[^17^0=P01095P5P1O3b25J1E@UW6o"). Qed.

Lemma Z_to_bv_minus_mod : forall z, Z_to_bv 64 (z - 2^64) = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h06__sat1h11zh21Hh32Hah47__arithh54__ffh66__sat0h78__varmaph85__with94__x1h:2b1h;2b2h<1np;1p;3p;2p;4p;6p;7g004;j14Tg007Jj33Tg00V6j21Tg02OBj3]Tg002Sj12Tg003]j1UTg008dj1=Tg00Sij2KTg016Ej27Tg005@j29Tg02Ofj28Tg00Y4j2CTg00TFj2BTg00UZj2:Tg00Y\j3XTg00Z@j2WTg00ASj2?Tg00Qdj1VTg0023j1TTg00Zaj2RTg00[?j1QTg00[]j1NTg00\kj2MTg01;2j1LTg00\Hj26Tg00^9j3JTg02Hcj3HTg01@Yj3GTg01=Vj3ITg00]Nj4<Tg00_dj2FTg00`Fj2ETg00a2j3DTg00aQj4OTg02Icj2PTg00U=j25Tg02J@j2>Tg01<Zj1STg01X<j6\Tg02KCj4[Tg000Mj6ZTg02PLj2ATg000ij6@Tg00fKj7YTg00HNR0f1R1f0R233p=0P1g00gMR3g00glR4P4g00hLR5P2g00hlFYp=;g02Q;R6%42R7%41R8g00Tbf2R9#4?312f3R:/1911:1'0R;[11911192'0%4:?391[R<f4#4?3:9\;A]912P2n2001000000120000000W;W:W<P<^;8^:7^<6P2g00GiR6#2R7#2#2#2#2#2R8#UR<%=7R7%=8R8'KR;,71R=,9<R>19<1R?P018<=R@19<9,1<,02X10P018<1RA179;RB,8</02X101C78RCg00foRD/B7RE1:D81BD;[RF[RG1:D7RHg00ilRIAX781UW3R81:D;\I^3HRHP1g00jH1WD7'?PEeO1REPFg00jnRI#VRJ%TIRI1R01%Q0RK%N0RLP01M06RM%L6R6,601607=J0<R75H05G0g01LhRNAI0M7C<';1FL5RMP2P9g00HlROg00ILRP'?1E29=3OPdAD0D1CORPb5b7b8X901P6;RO,52172;'0^90P2f5O1b4b0b6b0151O/0=P0159O1>2;1>:;'0X10P9P6P;PCPGP8PHPEPFPJPI%S0PKPLP3P4P4P5P0P7PN160DC<,;LE\PMPPb5b7b8A30;Dg01X`[P2b4b0b6b0C[PBP2EZb210@Ae11<?1A<1E@11<>1A<=E@O4b2X10o"). Qed.

Lemma errno_ret_fold : forall e, Z_to_bv 64 (- e) = errno_ret e.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01ep;1p;2g002Sj10Tg003]j14Tg004;j12Tg02LKj11Tg00ASj23Tg00HNg00Gi#0#0#0#0#0#0#4#2f0#1'3W0o"). Qed.

Lemma sextw_errno : forall e, (1 <= e <= 2^31)%Z ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (errno_ret e) + 0)) = errno_ret e.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h06__sat1h16__sat3h24__x1h31zh47__arithh54__ffh66__sat0h76__sat2h88__varmaph95__with:2Hah;1Hh<2Heh=1ep;1p;2p;3p;4p;6p;8p;7g008dj1ATg00UZj2<Tg002Sj15Tg0038j1;Tg00Sij2OTg00Tbj2GTg02IFj1>Tg02J@j28Tg003]j1ETg004;j1XTg00U=j27Tg02Kdj2:Tg005@j23j1eTg007Jj30Tg00Y4j2NTg00TFj2@Tg00Y\j3JTg00Z@j2aTg00ASj2=Tg00Qdj1^Tg0023j1]Tg00Zaj2\Tg00[?j1[Tg00[]j1ZTg00\Hj2?Tg00^9j3ITg00\kj2YTg01=Vj3DTg01;2j1WTg02Hcj3VTg01@Yj3UTg02H@j2TTg00_dj2RTg00`Fj2QTg00a2j3PTg00aQj4STg016Ej22Tg02Icj2nTg00=ej1mTg00]Nj4FTg02J`j3lTg000ij69Tg01<Zj1hTg01X<j6gTg02KCj4fTg000Mj6KTg02QYj8dTg02R6j2bTg01C:j1cTg00V6j2LTg02S6j1`Tg02LKj1_Tg00fKj7iTg00^\j7jTg00_@j8kTg00foR0f0R1'<p=4g00HNR2f1R3g01LhP1CFp=CP3g00gMR4g00glR5P5g00hLR6P1g00hlFip=1A0231p=6P2P3g00kZP1CFp=Bf2R7P4P5P5P6P3P1Fjp=Hf3R8P4P5P5P6P7P3P1Gkp=Mg00GiR9#AR:/<1%59R;#AR<%;9#;#;#;R=#AR>'OR?,<1'GR@P2%>3RA%5;#5#5#5R;#5RB#ARC,O<RD'8RE%EBRB#XRF%E;R;1710':,3BRG%>7RH,3B30X321N<CRI1@0<RJ%4C1@0D[RK[RL%4<RMg00ilRNAJ<C3UW:RC%4D\N^:MRO1N<>RP%4>1@0?[RQ\JRRAJ<>3VNX:MR>%4?\N^:MRMP3g00jH1a0<'=PJeRJO1RNPQf4PJO1RJPKg00jnRS#^RT%]SRS1\23RU%[2RV%Z2RW1?2<R<=I2BRX1Y29RY5D2RZ%W9R9,?2=V2X5U21T2YR['C'11RW6R\P1P7g00HlR]g00ILR^'=1Q17=0]^dAP203CSR^b5b8b9X2212D1R]1n9DR_'7%>1R`'6^22P1f8RaO1b4b1b0b6b0b7b112D3Rb/7_/6AP212D7R7/7_R_12D8Rc181D'6X32P2187DRd16c1X32RcP2P7Pc1=27PdPIPLPCPOPPPRP>PMPNPQPJPKPTPSPUPVPW1?2:/BY,1W%E=9I2<R<,BY,1W5HWRY%m5R=1?20R:/BZ,1WP2PZg00lAPXCF,1WRd5HWCMP\P^b5b8b9X22%4b1@bDRc'G\@^22P1f9RePaO2Rab4b1b0b6b0b7b19l7DE918_DP7P9PDPIPLPCPOPPPRP>PMPNPQPJPKPTPS%h2PVPWP4P5P5P61CX:,1WEgP\P^b5b8b9A02D0g01X`[P1b4b1b0b6b0b7b1CfE9PHP1EKb;16bEP2P7%>8,3BR890FGX32P2P71:;1,3B=0F8X32P2127DRG13B1=0F8X32P2PF%eBR8P8PGPHPF\2/=8PIPLPCPOPPPRP>PMPNPQPJPKPTPSPUPVAD2ZX/C[,1WP\P^b5b8b9X2212]D/6`^22P1PeO1b4b1b0b6b0b7b1Gd1:;7PIPLPCPOPPPRP>PMPNPQPJPKPTPSPUPVPWPYP=AD2X</BZ,1W=HWdCMP\P^b5b8b9X2212D?/<b/Gc\@^22Pab4b1b0b6b0b7b1,b7E91770%c7E918HDP1EKb;13BA,LB%`AE9%_3R3,LB/70,:;,3B=0F3eW<X=2o"). Qed.

Lemma sextw_small : forall z, (0 <= z < 2^31)%Z ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 0)) = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h02Hah16__sat1h24__x1h31zh47__arithh54__ffh66__sat0h76__sat3h88__varmaph95__with:2Hzh;6__sat2p;1p;2p;3p;4p;6p;7p;8g002Sj12Tg008dj1=Tg0038j15Tg00Sij2FTg00TFj21Tg00Tbj2:Tg003]j1<Tg004;j1MTg00U=j2?Tg02Kdj29Tg005@j23Tg007Jj37Tg00ASj2>Tg00Y4j2ETg00Y\j3DTg00Z@j2WTg00Qdj1VTg0023j1UTg00Zaj2STg00[?j1RTg00[]j1QTg00\Hj2BTg00\kj2NTg00]Nj46Tg00^9j3@Tg00=ej1LTg02H@j2KTg00_dj2JTg00`Fj2ITg00a2j3OTg00aQj4HTg02IFj1PTg00UZj2CTg02T:j2GTg000ij6;Tg01C:j1TTg00V6j2\Tg00bCj2[Tg00fKj7ZTg00^\j7YTg00_@j8XTg00foR0f0R1'Cp=0f1R2g00gMR3g00glR4P4g00hLR5P1g00hlFZp=4f2R6P3P4P4P5P2P1FYp=8f3P3P4P4P5P6P2P1GXp=Ag00HNR3%01g00GiR7#2R8#=R9%57#5#5#5R:#=R;'FR<,11':R=P3P2%28#2#2#2R8#2R>#<R?#MR@%<8R81?10'9,3?13?6RA37X33P3P21981,3?=7@AX33P3P213?1=7@AX3313?2RA,>@19821E9;R81109R@%0;110<[RB[RC%09RDg00ilREAD9;2UW0R;%0<\E^0DRFP2g00jH1W09'>P@eRGO1RHPBg00jnRI#VRJ%UIRI1S32RK%R3RL%Q3RMP31B30g00kZRN1N37R7C6,4MROP3P7g00lARP1B39RQ%<:5@3R:C6,4MRR58MRS%L4R4P31K3:PNP7C6,4M=8MRCA1JM5R5P1P6g00HlRRg00ILRN'>1I16=7RNdAO302CHRNb5b8b9X23%P</C2112<':\=^23P1f5f4R<O2b4b1b6b1,G2E;1?20%T2E;1\?A%=>R>,E9%0>1F9>RA,10[R0\@AD9>2VEX0D%0A\E^0DP8PCP;PFPHPBP<PGO1P0PJPIPKPLPMPSP4P3P7PPA@3Q?C6,4M98MOCAP5PNb5b8b9X23%02112A':\=^23P1f8f7O2b4b7b1b6b1b;b7,[2E;W:W3o"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stk_lo_nonneg : forall segs m lo hi, stk segs m lo hi -> (0 <= lo)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01ah11bh21Hh32H0h42_Hh52hih62loh71mh84segsp;1p;4p;2p;3g0023j1BTg002Sj12Tg003]j16Tg004;j14Tg004^j1ATg01j2j4?Tg00UZj20Tg008dj15Tg00Sij2=Tg00TFj27Tg00TbR0j21Tg00cBj18Tg01Y=j39Tg00=ej1@Tg007Jj33Tg01V_j1<Tg01a7j3:Tg006hj2>Tg01jgj2;Tg00Ec#Bg00Gi#2R1#2#2R2#2#2#2R3#6#4%62#4R2#AR4[g00HNR5f3R6f2R7f1R8f0R9C?P0g00foR0/07%51%53'=R3,0810691797'1f6R1f5R:%88R;39%@2R<534#<f7%87R77:11>29R=534X12,;2'1[^05'11006P9f4R6,0010631019179:'1f9R:f8;9;=34<#<f:?::7=34=X12,;2'1[^05'1P8W4W2P8P9O2n2001000000120000000W3X55W6W7W8o"). Qed.

Ltac name_sp sp k :=
  let sp1 := fresh "sp" in let E := fresh "Esp" in let H := fresh "Hsp" in
  remember (Z_to_bv 64 (bv_unsigned sp + k)) as sp1 eqn:E;
  assert (H : bv_unsigned sp1 = (bv_unsigned sp + k)%Z)
    by (rewrite E; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *;
        try match goal with ST : stk _ _ _ _ |- _ => pose proof (stk_lo_nonneg _ _ _ _ ST) end;
        apply unsigned_lit; lia).

Ltac unname_sp :=
  match goal with
  | H : bv_unsigned ?sp1 = (bv_unsigned ?sp + ?k)%Z, E : ?sp1' = Z_to_bv 64 (bv_unsigned ?sp + ?k) |- _ =>
      constr_eq sp1 sp1'; rewrite ?H in *; clear H; subst sp1
  end.

Tactic Notation "call_sp" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
      name_sp sp k; call SPEC; unname_sp
  | |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      name_sp sp k; call SPEC; unname_sp
  | _ => call SPEC
  end.

(* [comment removed for export] *)
Ltac sys_finish :=
  (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
  | |- _ = _ => cbv delta [mkR]; reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma impl_from_evt : forall {node : Type} segs (atn : node -> machine_state -> Prop) {R} (t : itree node R) Q ms,
  evt segs (fun ms' => impl segs atn t Q ms') ms -> impl segs atn t Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h03ms'h11Hh22H'h31Qh41Rh53atnh62msh74nodeh84segsh91tp;1p;2p;7p;3p;:p200R0g02U;R1p4p710p8p202R2g02V4R3p4p741110p8P2g02VjR4p4p741110p8g0023j14TP1j23TP3j70Tg02Wdj31TP4l:2Tg00Ec#4f1R4g00FbR3p-0[[R1f3R5f0R6'3f5R7f7R8f6R9P7f4R:P5f2R;P6F0X03;16P8P9P7P:P5P;f8R;P8P9P7P:P5P6F0X03P4P6f9P;P8P9P7P:P6F0X03P6O1P6W2X03M:2W1X63X31W9X42W5W8X70o"). Qed.

Ltac iprefix := apply impl_from_evt.
Ltac ihere := apply evt_done.

(* [comment removed for export] *)
Tactic Notation "icall" uconstr(SPEC) :=
  (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
  first [ eapply SPEC
        | eapply impl_epost_mono; [ eapply SPEC | ] ].

(* [comment removed for export] *)
Ltac ipost segs :=
  let a := fresh "ans" in let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros a ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ ?m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (let MIname := fresh "MI" in
       lazymatch goal with H : mem_inv segs _ |- _ => rename H into MIname; try rename MIname into MI end);
  (* [comment removed for export] *)
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
