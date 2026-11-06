(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac ITree Nodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Export Decode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_SysStep () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem7reg_getC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState5MSsvcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics5Riscv3Sem5is_x0C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState>step_ecall_genC13~~~K47Corelib4Init5Logic3and01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_stepC13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv3Sem2w0I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesI47Corelib4Init9Datatypes3nat00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK47Corelib4Init9Datatypes4list01C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@delivered_writesK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool;orb_false_rC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem;wa_unsignedC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep8in_rangeC13~~~K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3subC47Corelib5Lists7ListDef5skipnC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_nil_rC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List<length_skipnC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega7EnvRing5PExpr03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3MemEbytes_at_write_insideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem9upd_bytesC13~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem;wr_at_writeC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula03I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC47Corelib4Init5Logic8iff_reflC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem>wr_at_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStepDrw_cells_CB_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem=mem_inv_storeC13~~~C56Stdlib6ZArith6BinInt1Z9leb_spec0I47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z9ltb_spec0C47Corelib4Init5Logic3notc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep@apply_zeros_specC13~~~K46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC47Corelib4Init5Logic9False_indC47Corelib4Init5Peano2ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3mrdC13~~~C46Stdlib5Lists4List9nth_errorC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep=zeros_outsideC13~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep@wview_zeros_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5CellsBcells_bytes_lengthC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStepDbytes_at_zeros_otherC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep;wr_at_zerosC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8ro_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6insideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame7outsideC13~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5FrameBinside_not_outsideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3ivlC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7ro_addrC13~~~C47Corelib5Lists7ListDef6repeatC46Stdlib9micromega;ZifyClasses3injC46Stdlib5Lists4List@nth_error_repeatC47Corelib4Init5Logic6eq_symc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep<zeros_insideC13~~~C46Stdlib5Lists4List=repeat_lengthC46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat7add_0_rc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStepBbytes_at_zeros_newC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep?wr_at_zeros_newC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStepAapply_unmaps_specC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep>unmaps_outsideC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStepEbytes_at_unmaps_otherC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStepBwr_at_unmaps_otherC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode8errno_ofC13~~~K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7mod_addC45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBerrno_ret_unsignedC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00C35stdpp7tactics<f_equal_helpc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep<swrap32_highC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MStateAunsigned_lit_wrapC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep=swrap32_smallC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree5itree00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4implC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree8impl_evtC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma evt_ecall : forall segs (Q : machine_state -> Prop) R F pc fc rv m ro w,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true ->
  Q (MSsvc R F (Z_to_bv 64 pc) (reg_get R 17) fc rv m ro) ->
  evt segs Q (MS R F (Z_to_bv 64 pc) fc rv m ro).
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01mh11Fh22HQh32Heh42Hfh51Qh61Rh72fch82pch92roh:2rvh;4segsh<1wp;1p;2p;3p;8p;7p;;p;6p;4p10000p4p710R0p1000Mp4p710p8P0g000iR0p4p710R1p8g001GR2p4p7210P1p8g0023j1LTg002Sj10Tg0038j1:Tg003]j12Tg004;j18TP2j2JTg004^j17Tg005@j23Tg005fj2>Tg006hj2=Tg007Jj31Tg007dj1<Tg008dj1;Tg009Bj3KTg009ej26Tg00:Oj84Tg00;]j7ITg00<hj1DTg00=nj1CTg00>Pj1BTg00?Xj2ATg00@Tj25Tg00A\j29Tg00B6j1@Tg00B^l;?TP0j6ETg00D5j4FTg00DPj4GTg00E_j6HTg00Fn#Lg00GmR0p-0[g00I4#0R2#:#2R1%02#0R2#0#0R3#0#2R4#8R5'JR6g00IY%23#8R3%75R7%22#8#7\5R8%73f9R9f5R:,34'>f0R;,=331g00J7R<f1R=#<g00JW31f:R>P9f8R?f7R@,34%:2#;g00K75K1R1,69f6R2P:f4RAf3RBG4O1f<RCf;RDP>P9134?REP@P2P:PAFIRFP>P9PE16>1RGP@P2P:PAG4RH%DF%C5RI517%B0RJ1ACFRF150HRK31197IPJP>P9PEP<P5%@1g00KSPGn0100000020000P@P2P:PAG4,50PDP>134916D1P?P@P2P:G4,5091J;X0J19JKPFPCP>P9PEP@P2P:PAPBf2P=M;?EECFPCPDPHP;CGEHW2W3W4X<3X98W0W:W7W8X16W6W5W;o"). Qed.

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

Lemma nret_MSsvc : forall R F pc x8 fc rv m ro r ws zs us ci,
  nret (MSsvc R F pc x8 fc rv m ro) (mkEffectU r ws zs us [] ci)
  = MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4) fc rv (apply_writes (apply_zeros (apply_unmaps m us) zs) ws) ro.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01Fh11Rh22cih32fch41mh52pch61rh72roh82rvh92ush:2wsh;2x8h<2zsp;1p;2p;3p;5p;7g002Sj10Tg0038j1ATg003]j11Tg004;j14Tg001Gj2@Tg004^j16Tg0023j12Tg00L8j23Tg008dj15Tg009Bj38Tg00LXj57Tg005@j29Tg00MHj3:Tg00Mmj2?Tg00Nfj2>Tg00O^j2<Tg00;]j7;Tg00A\j2=Tg00I4#0R0#AR1#1R2%00R0#0R3#0#0R4#0#1R5#4R6'@R7%14#4%66%13#4R3#6\6R4%23,36#21366#2R3g00PW,36#2g00GmP2P6%01#5g00K7582f4f<D7f;f:%50,955:5f8f7f6f1'?f2'>f3'<f5F;'=W2X93W<W:X66X74W4W8W3X;6X56X07W1o"). Qed.

Lemma mkR_set_a0 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v,
  bvmap_set 10 v (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
  = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01vh12x1h23x10h33x11h43x12h53x13h63x14h73x15h83x16h93x17h:3x18h;3x19h<2x2h=3x20h>3x21h?3x22h@3x23hA3x24hB3x25hC3x26hD3x27hE3x28hF3x29hG2x3hH3x30hI3x31hJ2x4hK2x5hL2x6hM2x7hN2x8hO2x9p;1p;2p;Og002Sj10Tg003]j11Tg004;j13Tg0038j12Tg001Gj26Tg00Q6lO5Tg00A\j24Tg00I4#0R0#0#0#0#0#0#1#3R1%20#1/61fOfNfMfLfKfJfIfHfGf0fEfDfCfBfAf@f?f>f=f<f;f:f9f8f7f6f5f4f3f2f1MO5'4X01XI1XH1XF1XE1XD1XC1XB1XA1X@1X?1X>1X=1X;1X:1X91X81X71X61X51X41X31X21XO1XN1XM1XL1XK1XJ1XG1X<1W1o"). Qed.

(* [comment removed for export] *)
Lemma apply_mem_none : forall m, apply_writes (apply_zeros (apply_unmaps m []) []) [] = m.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01mp;1p;2g002Sj10Tg003]j12Tg004;j11Tg004^j13Tg00A\j24Tg00I4#0#0#0R0#0#0#0#2#1%20#1#3[R0f0,40W0o"). Qed.

Lemma apply_mem_write : forall m a bs, apply_writes (apply_zeros (apply_unmaps m []) []) [(a, bs)] = write_to_mem m a bs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01ah12bsh21mp;1p;3p;2g002Sj10Tg003]j12Tg004;j11Tg004^j13Tg0023j16Tg00RAj35Tg00A\j24Tg00I4#0#0#0R0#0#0#0#2#1R1%20#1R0#3[R2%60f2f1f035,42W1X01W2o"). Qed.

Lemma apply_mem_delivered : forall m a bs,
  apply_writes (apply_zeros (apply_unmaps m []) []) (delivered_writes a bs) = write_to_mem m a bs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "p'0h01ah11bi001bh22bsh33bs0h41mi011lp;1p;2p;3g002Sj10Tg003]j14Tg004;j12Tg004^j16Tg0023R0j1>Tg00L8j2<Tg00SEj13Tg00Mmj2;Tg00Nfj2:Tg00Sej28Tg00O^j27Tg00RAj31Tg007Jj39Tg00A\j25Tg00Tjj3=Tg00I4#0#0#0R1#0#0#0#4#2R2%41#2R1#6[R3%>1R4P0P1f3R01<22#3R5';/:5f2R5f0R6'8'7A1056593P6f1R0%31515,53f6f5A=10631,53X24X11P0P6O2n10110100020020100101W3X02W4o"). Qed.

(* [comment removed for export] *)
Definition in_range (a n : Z) (x : word) : bool :=
  (a <=? bv_unsigned x)%Z && (bv_unsigned x <? a + n)%Z.

Lemma apply_zeros_spec : forall m a n x, (0 <= a < 2^64)%Z -> (0 <= n < 2^64)%Z -> (a + n <= 2^64)%Z ->
  apply_zeros m [(wa a, Z_to_bv 64 n)] x = if in_range a n x then Some (Z_to_bv 8 0) else m x.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h06__sat1h12Hah27__arithh36__sat0h44__x1h51zh63Hanh72Hnh84__ffh98__varmaph:5__with;1ah<1bh=1mh>1nh?1xp;1p;2p;3p;6p;4p;7p;8g002Sj12Tg003]j1ETg004;j1CTg004^j1ITg008dj1DTg00UJj2VTg00Ugj27Tg00VCj2:Tg00V^j21Tg00W;j2?Tg00WWj25Tg00XAj29Tg005@j2=Tg00X^j26Tg00Y;j24Tg00YYj28Tg006hj2WTg007Jj30Tg00A\j2;Tg00Z6j1UTg000ij6<Tg00ZUj2PTg00[=j3OTg00[aj2NTg00SEj1ATg0023j1MTg00\Bj2LTg00\`j1KTg00]>j1JTg00]ij2@Tg00^Lj2HTg00^oj4BTg00_Zj3GTg00`=j7QTg00=nj1RTg00`aj8FTg00aEj2STg00agj2TTg00bSj3bTg00c2j4aTg00cdj2`Tg00e9j1_Tg00fAj2^Tg00gRj3]Tg00L8j2ZTg00hdj4[Tg00Tjj3\Tg00Nfj3YTg00iDj7XTg00ihR0f0R1'?p=3f1R2g00jFR3g00jeR4P4g00kER5P1g00keFXp=>g00I4R6#2R7#2#2R8#2#2#2R9#ER:#CR;%E8R8#CR<#IR=[g00IYR>f2R?#3%D7R7%D9R9'VR@,7?':RAf4RBf3RC'1/?@P>f5RDg00J7REP=15:BRF,911=:D,5:,11,6F'4g00lERG'81=80,W<R<f7PBO1R8n0100000020000PEP=f6RH/9FRI11HD,6F'4P<P8n0100000020000RJ50=X5>P>PBPEP=11H1,6F,4I/8GP<P8n0100000020000=0=JX5>PE15:CRI,9D11DB,6I'4RFPEP=P1P<P8n0100000020000=0=JX<EPEP=PFP<PHPCO1RJn0100000020000,;=18FG%UFE<1=:BRF,5:R81P79RK1707RL%39170@[RM[RN%37ROg00leRPAO792UW1R9%3@\P^1OROP2g00mA1N07';PLeO1RLPMg00mgRP#A%MP1L>2%K>%J>RPP3P4P4P5PPP3P4P4P5P>1@>0g00nS1H>6R6CB,>PP>P6g00o:1@>7=G>:CB,>PFQR7%R4P7GF1SP5P1P?g00JWRP,;E1T1?=0EPdAb>02Cab8b9b:X4>R0%31171@':%32172@':[^4>R@P1f8PDO2b2b0b3b0,`BE<%_DR2,5:R:PKPNP9POPLPMP0P@P1f9PHO2b2b0b3b0,^DE<PEP=19:I11:8,6I'4/8GP<PJn0100000020000PEP=A]DBCP<PJn0100000020000RJ50=e1Z;;R<P;P;P2PFC[%A<3\=YHC=0=JeW6X7AW1X?;X>>W;W=o"). Qed.

Lemma apply_unmaps_spec : forall m a n x, (0 <= a < 2^64)%Z -> (0 <= n < 2^64)%Z -> (a + n <= 2^64)%Z ->
  apply_unmaps m [(wa a, Z_to_bv 64 n)] x = if in_range a n x then None else m x.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h06__sat1h12Hah27__arithh36__sat0h44__x1h51zh63Hanh72Hnh84__ffh98__varmaph:5__with;1ah<1bh=1mh>1nh?1xp;1p;2p;3p;6p;4p;7p;8g002Sj10Tg003]j1ETg004;j1BTg004^j1JTg008dj1DTg00UJj2WTg00Ugj24Tg00VCj2:Tg00V^j22Tg00W;j2=Tg00WWj26Tg00XAj29Tg005@j2FTg00X^j25Tg00Y;j27Tg00YYj28Tg00=nj1CTg007Jj33Tg00A\j2;Tg00Z6j1VTg000ij6<Tg00ZUj2STg00[=j3RTg00[aj2QTg00SEj1@Tg0023j1NTg00\Bj2MTg00\`j1LTg00]>j1KTg00]ij2?Tg00^Lj2ITg00^oj4>Tg00_Zj3HTg00`=j7OTg00`aj8PTg00aEj2GTg00agj2TTg00bSj3UTg00c2j4aTg00cdj2`Tg00e9j1_Tg00fAj2^Tg00gRj3]Tg00L8j2\Tg00hdj4YTg00Tjj3ZTg00Mmj3[Tg00iDj7XTg00ihR0f0R1'=p=1f1R2g00jFR3g00jeR4P4g00kER5P1g00keFXp=Ag00I4R6#0R7#0#0R8#0#0#0R9#ER:#BR;%E8#BR8#JR<[g00IYR=f2R>#1%D7R7%D9R9'WR?,4>':R@f4RAf3RB'2/=?P=f5RCg00J7RDP<16:ARE,911F:C,6:,21,5E'7g00lERF'8%C8R8f7PAO1RGn0100000020000PDP<f6RH/9ERI12HC,5E'7P8PGn0100000020000RJ53<X5=P=PAPDP<12H1,5E,7I/8FP8PGn0100000020000=3<JX5=PD16:BRI,9C12CA,5I'7REPDP<P1P8PGn0100000020000=3<JX<DPDP<PEP8PHPBO1RJn0100000020000,;<18EF%VEE<1F:ARE,6:RG1S79RK1407RL%19140?[RM[RN%17ROg00leRPAR792UW1R9%1?\P^1OROP2g00mA1Q07';PLeO1RLPMg00mgRP#@%NP1M=2%L=%K=RPP3P4P4P5PPP3P4P4P5P=1?=0g00nS1I=6R6C>,APP=P6g00o:1?=7=H=:C>,APFOR7%C4P7GP1GP5P1P>g00JWRP,;D1T1>=3DPdAU=02Cab8b9b:X4=R0%11141?':%12142?':[^4=R?P1f8PCO2b2b0b3b0,`AE<%_CR2,6:R:PKPNP9POPLPMP0P?P1f9PHO2b2b0b3b0,^CE<PDP<19:I12:G,5I'7/8FP8PJn0100000020000PDP<A]CABP8PJn0100000020000RJ53<e1\;;R8P;P;P2PECY%@83Z=[HB=3<JeW6X7@W1X?;X>=W;W=o"). Qed.

Section MemEffects.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)

Lemma rw_cells_CB_prefix_write : forall m A n junk bs,
  rw_cells segs m A [CB n junk] -> (length bs <= n)%nat ->
  rw_cells segs (write_to_mem m (wa A) bs) A [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)].
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"] "h04__x1h14__x2h24__x3h33Hj0h45Hlen0h57__arithh64__ffh74__p1h88__varmaph95__with:4__x4h;4cstrh<5cstr0h=5cstr1h>1nh?1Hh@2H2hA1xhB2z2hC2HbhD1WhE4__p2hF4__x5hG1lhH1mhI1AhJ2H3hK2HjhL4HlenhM2HwhN3HwfhO2_HhP2bshQ4junkhR1yhS1zhT2z3p%0p&0p;1p;4p;2p;3p;6p;9p;7p;Bp;<p;8g002Sj1ITg003]j1|Tg004;j1vTg004^k104Tg0023j1}Tg00SEj1jTg00oaj4TTg0110j4^Tg012@j1STg013RR0j10Tg0142j4OTg015=j21Tg015]R1j2RTg00e9j1<Tg00RAj3?Tg0167j2HTg016Nj3XTg016lj1dTg018<j1cTg019Oj4;Tg01:]j3`Tg01;:j2wTg000Mj6_Tg00VCR2j23Tg00A\j2@Tg01;Xj26Tg007Jj1uj3UTg01<5k203Tg01<Xk302Tg00W;R3j24Tg01=5j4nTg01=\j1\Tg01>Aj2[Tg00Ugj2KTg01>cj2ETg01?=j1QTg01?\j2FTg01@Ek10JTg01@ck20ITg01ADj3mTg00\Bj2YTg01Amk10ETg01BKj4NTg00\`k10DTg00]>k10CTg00]ik20ATg0038j1xTg00^Lj2MTg01Bij3aTg00=nk10@Tg00aEk20?Tg00agk20>Tg00bSk30=Tg00c2k40<Tg01CLj4iTg01D7k30:Tg000ij6tTg00D5j4ZTg01DXR4k109Tg01E8j2CTg01EOj2sTg00V^R5j2LTg01Elj3VTg01FOm907Tg01Gjj3eTg01I9k106Tg01IZk705Tg01Jkk20;Tg00Tjj3PTg01L9lBfTg01L_l<qTg01MDj3lTg01Mmj2bTg00^oj4gTg00iDj7yTg00`=k701Tg01NYk70BTg00`ak800Tg01O=l<~Tg01Obk60FTg01PFR6f2R7f1R8+0;f0R93Pp=2g00PWR:?U89p=9g00ihR;/s9p=Ag00IYR<?U89p=5P:P:P:P<P<P<g01QTP0P0P0f6R=g01R4f5R>f4R?f3R@P7P8P9MBfp=zP:P<P9P0P8P7P@P?P>P=f7RAf8RBM<qp=hP:P<P1P0P3g01R[P>P?P@P7P8P9M<qp=oAU<9;p=JAl<89p=:Al<89g01S=R3'bp>0Hg00mgR1Al<78/b3;P9p=>AP1899P17p>0G1b83=P19p={P<P8g00o:P9Cgp=kP8g00jFR3g00jeRCPCg00kERDP9g00keREFyp=8P7P3PCPCPDP<P8g01SiP9CgPEFyp=7P7P3PCPCPDP8P9K01p=BP<P8g00nSP9Cgp=DP7P3PCPCPDP8P9K0Bp=WP@P3PCPCPDP7P8P9L00p==P<P:P<P<P4P7P0P8g01TPP;P;P9M<~p>08P:P:P:P<P<P<g01U=R4P0P0P0P5g01U]REP>P?P@P7P8P9MBfp=rP8P3PCPCPDP9J0Fp=]1L9;p=GP:P:P:P<P<P<P4P0P0P0P5PEP@P7P8g01V@REP;P9MBfp=pg00I4R5#IR0#IR4#IR3#I#I#I#|#v%|3#vR3$04[%}3RFp,4segsRGP?P@%j6R69278CTP2PGP>P?A2@76RHC^PGP>P?%SH#0CO1137/R?PG%<==?A@P=113@RH1H>HAX3H?;2672@CT[P9PGPAP=A2>?6C^P2A2=>6RH#dPGPBPA%cHC;PGf9RHPBA2A=6#S#0CO113=/RBPGf;RIf:RJ#<;?APJ113ARK1HHKAX3KB;2672ACT[[P9A2BA6#dPGPIPJA2HB6#cC;PGf<RKPIA2JH6#S#0CO113H/RIP2113IR2/9Kg00leRHPGf?RJf>RL#<;?IPLf=RM/H2AX32K;26922ICTP@113M/9LPF%j3RL9`3JPGfCRMfBR2P9C;XGFP=PJ1w3JE_PGP2fARIPJC;PG%<2=?MJRKP2113JRN1HINROf@RP9X3NRQ;2672JR6C^PGPKP2%S6#0COS00%d6RRPGPKP2%c6C;S0119NN113QR6/9ORK/3H1@:NPKPHP:113PRK/HNRS1H2KRT,99X>:19SO%0KRU%0NRV'6#ARW%0IRX/6V#ARY'5%u:RZ%u<R[%08%09S02'5198920389402XR:XA:R\PSPW1689#AXH<X><RWPKPU1@<US03PNPV1@<VRSFzPOPYPWPIPX1@<XRWPNPVPSFzS04M9h1RNI14VXR]PNPVPSPIPXPWEoP>CnR^P]113IR_/92%0_R`%02Ra'5RbPZP[P\P_P`1@<`P2Pa1@<aM9hP@CnRaPb%\_R_14;`R`fDRc#\Rd%0c,4;Re113cRf#\Rg%0fRf,4;RhfFRi#0/6fRf,[;S051K;f%AfRj/5f'314f;%Jj'3'ES06fGRj#0fERf,13#0'6#AS07P<113j#0Rj113i#0'6Ri,[;1K;i%AiRk/5i'314i;%Jk'3'EfH,13#0S08/6j#AP<%QERk#QRi#QRl#QRm,F<Rn&0J5-0I<Ro1F<iRi5m<Rp1F<ERq':RrAm<onRs1:iq':Rt%Qm,F<Rm1F<lRl1F<kRk9m<oRo':+0HRu1:kqRv,:pRp1:oq,:i1:lk%j1Rk5>m9>mt5>s5>n80Gu'{3>%}1R1P<P<1Y<?P7&0E<RuCNRnP8P<1Y<>P@PuCNCN&0D<Rs&0C<Rm20A<;Rt%x0,M<Ro%x5,M<Rq5a<Rw'k,8m1M<5R5=7mw5Bm1Dwt,8mA7m5tRw5Bm5Wm&0@CRCPm1M<4R4=a<qRx,kt,8m1M<0R0=7mx5Bm1Dxt,8mA7m0t5Bm5WmPCPmA7mo4PCA7m50C=C=C=20?mDRDP9P7g00J7Rog00JWRx'@20>97=UoxdB0=<;8H0<Rxb6b8b9X0<X1<X2<X:<XF<16?7Ro,K;159o'314o;%J9Ro'3'E16?@Ry,K;157y'314y;%J7Ry'3'E15=>15@?Rz[[[^0<^1<^2<^:<^F<P9fJ,13#0fK#0fIR{,13#0P@P8P7P?PBO8b5bTbJbBb@b=b<b;b3b4CiP6B0:3NPEtg00K7CZCZPRePFPQPG%<MS09=?cPRRPMA`3P9C;XGFPGPMP2PPP;PJP9P^P]PaPbP_P`PdPePgPhPkP1PuPs1Dtt,8mPDPxb6b8b914;;RuP9b5b=b<b;b3b4&09;R6/CNRB/RKR|1s;;R}/LVR~/4UPBP~P6P}P9XA<%A9XA<1@<;R~408PNPVPSErPKPUQ03EoP^P]PaPbP_P`PdPePgPh1[;;1K;;RU%J}RB'313uB'EP}P<p-0R}A>lpkP1P<PnP81Y<@RnCNPsPm1ktt,8m1]m=5Bm1]mA=Bmw5WmPCPmA7mq4PCPm1D04,8mPCAV<50/Dq,8mC=C=C=PDPxb6b8b9X0<X1<X2<X:<X7}WE13U?13>o'E14@>1L@?/4>[\z[^0<^1<^2<^:<^7}^E}P9Pu%J8%0{R{Q08PjP8P7P=PAO9b5bBb@b=b<b;b3b4CiP|eN907PG%G2#<=?MJP2AeP6JC;P<%GMPG%<9=?fIPcAe26IC;XS<P9PM&06ME_PGPRPMAeI6PC;P9bDbDA`3QL1w3QEtQ01eCZ1CIERQ1COER3,CNRL'9R6%GXRR%GYRJ,LVR|'5PZP[P\PQPRPIPXPWP~CpPLP|PNPVPSP3PJPOPYQ04P~CpErM9hP^P]PaPbP_P`PdPePgPhQ05Q06Q07P<1{rk9>iv9>lrP1P<1Y<7P8PnCNPsPm1]m>Aa<50R>97mq5Bm1D>t,8mA7mqt5Bm5WmPCPm1D05,8mPCAV<5tAV<qt9V<057mC=C=PDPxb6b8b9X0<X1<X2<X7}1698Rx,57,3@14x;/3y'E1478%G7%G?,L@'5[[^0<^1<^2<^7}P916{j,K;P8PjP{P7PAO6b5bBb@b=b<b;b3b4CiP6P:1C2ER2PG%<c=?fIPcQ02COX>:PGPcPM%02Q09PPPAK051CTE,CKP9E_b?Q00eCZbCXOHWKP8P9O2n2001000000121000000WLWMWCWNP8P9O2n2001000000121000000W?P8P9O2n2001000000121000000W?XPFWQX>:XI<WHo"). Qed.

Lemma rw_cells_CB_store_ok : forall m A n junk k,
  rw_cells segs m A [CB n junk] -> (k <= n)%nat -> store_ok segs m (wa A) k = true.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"] "h01xh11Ah23Hk0h37__arithh44__ffh58__varmaph65__with74__x1h84__x2h94cstrh:5cstr0h;1Hh<2Hkh=2Hwh>2_Hh?4junkh@1khA1mhB1nhC1yp;1p;2p;3p;4p;<p;8p;9p;6p;7p;Bg002Sj13Tg003]j1CTg004;j1?Tg004^j1KTg0023j1GTg01Jkj25Tg00SEj1ATg00Tjj36Tg00oaj4UTg0110j4=Tg012@j1;Tg013RR0j11Tg0142j4>Tg015]R1j2:Tg00e9j1ETg01V_j4DTg00V^R2j24Tg01E8j2YTg00W;R3j20Tg00A\j22Tg01=5j4WTg01=\j1@Tg01Amj1VTg00\`j1TTg00]>j1RTg00]ij2QTg00aEj2LTg00agj2JTg00bSj3MTg00c2j4NTg01W_j1ITg01L_l<<Tg00\Bj2HTg01BKj4STg00^Lj2FTg00=nj1dTg01Elj3BTg00`aj8cTg01CLj4bTg01X=l9aTg01I9j1`Tg000Mj6_Tg007Jj3]Tg00^oj4\Tg00iDj7[Tg01L9lB^Tg01O=l<ZTg00J7R4f0R5g00JWR63]p=8g00PWR7g00IYR8P1P0P3g01R[f5R1f4R9f3R:f2R;f1R<P5M<<p=XP8P<g00nSP5C\p=7P<g00jFR=g00jeR>P>g00kER?P5g00keF[p=9P7P7P7P8P8P8g01U=P0P0P0P2g01U]P:P;P<g01V@R2g00ihR@P5MB^p=OP7P8P8P8P0P0P1P9P:P;P<P5M<Zp=Pg00I4R0#3RA#3#3RB#3#3#3#C#?%CB#?RB#K[%GBp,4segsRBP9P:g01PFRC15;<%ACRD36CUg00VCPBP1P915:;=6CDREC=PBP1P9%;E#1C>1:;9PBf7REf6RF#EP:CD#8[P5PBPEPF1519=6CDC=PBf8R9PE15F1=6CD#;#1C>1:1EP8f9R1/4@PBf;%E5PECD#8X18PBf:RBP11Y92R2#1RDP@PFP<1:F9%1FRC%19RG'0RHPFPC128CP9PG128GRFEXP5CWRIPH%@ERJ%1E,0@RE%@BRK%1BRB,0@RLg00mgRM#ARN%GMRM%V8RO%T8RP%R8RQ1Q8@RR/7R'91LQ?RSP5P;12461J5;#8dAM8@<CNR6b4b5b610@@P5b3b:b9b214@CRC/0D14G@R4,0CP8P8P3P5X08RTP310<5#IXC8X08PCPC128CPDP4PTPT%15,28X07P2P4P9PGPF128@COEPM<<PIPHPJPEPKPLPNPMP81H8;P<POCSPPPQP=P>P>P?1F80R01F8ARA'7,9Q%d>AB8R0AB8AR'7,9QGcPSP6b4b5b6X78X88105<14@<14;@'0[^78^88P5f<#1PBP:O3b3b:b9b2CbM9aP1%`1E_W<W=W>P<P5O2n2001000000121000000W;X@7W?XB7X18WAo"). Qed.

Lemma mem_inv_syswrite : forall m A n junk bs,
  mem_inv segs m -> rw_cells segs m A [CB n junk] -> (length bs <= n)%nat ->
  mem_inv segs (write_to_mem m (wa A) bs).
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"] "h01Ah12bsh24junkh31mh41np;1p;2p;3p;4p;7p;6g002Sj10Tg003]j13Tg004;j12Tg004^j14Tg0023j1>Tg01YQj2;Tg01Jkj2:Tg00SEj15Tg00Tjj36Tg00oaj47Tg015=j21Tg015]j28Tg00e9j19Tg01Z^j7=Tg01\<j6<Tg00I4#0#0#0R0#0#0#0#3#2%30#2R0#4[g00IYg00PW%>0R1p,4segsR2f4R3';P2f5R4P3g01PFR5f3R6f2R7':%5536C71107/83P2f7R2f6R5#9P6P7P2P5P4P31106f1f0F=E<UUUX11W2W4W0W3o"). Qed.

(* [comment removed for export] *)

Section Zeros.
Variables (m : word -> option byte) (a n : Z).
Hypothesis Ha : (0 <= a < 2^64)%Z.
Hypothesis Hn : (0 <= n < 2^64)%Z.
Hypothesis Han : (a + n <= 2^64)%Z.
Let m' := apply_zeros m [(wa a, Z_to_bv 64 n)].

Lemma zeros_outside : forall x, (bv_unsigned x < a \/ a + n <= bv_unsigned x)%Z -> m' x = m x.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h01bi001bh11ri011rh22Hah34__p1h46__sat2h54__x1h64__x2h74__x3h82a0h91li021lh:2n0h;1Hh<2H0h=2H1h>2H2h?2Hxh@7__arithhA4__ffhB6__sat1hC8__varmaphD5__withE2l0hF2n1hG1ohH1xi031np;1p;2p;3p;4p;7p;6p;8g002Sj15Tg003]j1GTg004;j1DTg00WWj23Tg00Ugj22Tg00V^j2;Tg00W;j21Tg01>cj2@Tg004^j1QTg00gRj3NTg005@j2<Tg006hj2ITg007Jj30Tg01]Oj2fTg00XAj2ETg01^2R0j2CTg00X^j2FTg00Y;j24Tg01^Uj2XTg008dj1ATg00ZUj2WTg00UJj2VTg00[=j3STg00VCR1j2?Tg00[aj2RTg00A\j28Tg00SEj1>Tg0023j1PTg00\Bj2=Tg01BKj4MTg00\`j1LTg00]>j1KTg0038j1JTg00^Lj29Tg01Elj3OTg00^oj46Tg00=nj1HTg01NYj7TTg01Obj6UTg00aEj2eTg00agj2dTg00bSj3cTg00c2j4bTg01_8j1BTg00L8j2^Tg00e9j1]Tg00hdj4\Tg00Tjj3[Tg00Nfj3ZTg01_Qj7_Tg000ij6YTg00iDj7`Tg00`aj8aTf1R2g00jFR3g00jeR4P4g00kER5f0R6g00keF`p=7f3R7P3P4P4P5f2R8P2P6Gap=:g00I4R9#5R:#5#5R;#5#5#5R<#GR=#DR>13=6R?p,1aR@'2p,1nRA,;@RB/1?'@%G;R;#DR?#QRCg00J7RDPCAN@A2g00ihRE,<;,I?R?p,1mR;P2O1RFn0100000020000RGP;P8O190C6XGC13=2RH,f@11@H1E@H'C13=8,E@PDP013=7,1@PDPCf5RH,3=RI/FBRJ,42P?P;PHO1RKn0100000020000=0CKP2f4RK,3=,1@RL1XIBRM12IB/CJRJf6RI,3=/FBRNPDP0f7,3=/2BROPDPCg00JWRP/42P?P;f9O1RQn0100000020000=0CQP2f8,3=/2BRB%A:RR%A<R<'W12ERRS11E<1VR<RT,2E[RU[11ERRVg00leRWASR<2UW211ET\W^2Vp,2HaRV11E@RW12@TR<'?P1PWP<P;f=O190C?P6p,2HnRX11EARY12ATRT'?P1PYPTP;fBR1O190C?P6f;g00mA1RER'8PSeO1PUp-0RUg00IYRSg00mgRR#>%PRPS1=S8P21=S7CM%LS%KSRRPS%J9,9SRZg00o:R[19S9R919S:5OSR:C6,7R%H4R\PRPSP9g00nSR]PZC6,7RP\PRPRP3P4P4P5PSPZP[P9C6,7RPSP:P]PZC6,7RFTP\PRP3P4P4P5PHEUC:C:C:1eR5P6P818DP1d68=0DPdAcSE2CbbAbCbDX5SX6SW7W31;62,28112712K81;87/1K'@PI[[[^5S^6S^7S^3UP6P;fGRUO190C?13=UPAP@f>P1fFO7b@b4X>TX=YP2P6O2n2001000000121000000b8X<<X;WP2P6O2n2001000000121000000b8bBb4PDPC14PPP?PQn0100000020000=0CQeWEP6O1%BBRW18CQR<PDPCg00lERY,4PP?PQn0100000020000=0CQeW:P6O1n10210010100021110210103b0b1W9P6O1%BLPMPJPNPDP0POPDPC14Y2P?PQn0100000020000=0CQP2P<PDPC14YPP?PQn0100000020000=0CQeX9BP6O1P<PDPC14YYP?PQn0100000020000=0CQeXFWP6O1n10210010100021010210103b0b1W:P6O1n10210010100021110211103b0b1A0CGFe1^>>RGP>P>%]@1<=AC\%>G3[=Z;2P;P@PAP2PVPXp,3HanF_EYp,2m'P2O1=0CFeW?WHo"). Qed.

Lemma zeros_inside : forall x, (a <= bv_unsigned x < a + n)%Z -> m' x = Some (Z_to_bv 8 0).
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h02a0h16__sat2h24__p1h34__p2h44__x1h54__x2h61Hh72H0h82H1h92H2h:1bi001bh;1ri011rh<2Hah=7__arithh>4__ffh?6__sat1h@6__sat3hA8__varmaphB5__withC4__x3hD1li021lhE2n0hF2HxhG2l0hH2n1hI1ohJ1xi031np;1p;2p;3p;4p;7p;6p;8g002Sj15Tg003]j1JTg004;j1ATg00WWj23Tg00W;j21Tg00V^j2;Tg00Ugj22Tg00VCR0j26Tg004^j1TTg00gRj3QTg005@j2>Tg006hj2LTg007Jj30Tg01]Oj2jTg00XAj2HTg01^2R1j2ETg00X^j2DTg00Y;j24Tg01^Uj2YTg00A\j2:Tg01_8j1CTg008dj1BTg00ZUj2WTg00UJj2VTg00[=j3UTg00[aj2STg00SEj1@Tg0023j1RTg00\Bj2?Tg01BKj4<Tg00\`j1PTg00]>j1NTg0038j1MTg00^Lj28Tg01Elj3OTg00^oj4=Tg00=nj1KTg00aEj2iTg00agj2hTg00bSj3gTg00c2j4fTg01Amj1`Tg00L8j2_Tg00e9j1]Tg00hdj4\Tg00Tjj3[Tg00Nfj3^Tg01_Qj7ZTg000ij6aTg00iDj7bTg01`kj6cTg01Obj6dTg00`=j7eTg00`aj8XTf1R2g00jFR3g00jeR4P4g00kER5f0R6g00keFbp=FP2P3P4P4P5P6Ecp=GP2P3P4P4P5P6Edp=9f2R7P3P4P4P5P2P6Fep=If3R8P3P4P4P5P7P2P6GXp=7g00I4R3#5R9#5#5R:#5#5#5R;#JR<#AR=p,1aR>13<6R?'1p,1nR@,;>RA,2?'6%J:R:#AR?#TRBg00J7RCPBAQ>@2g00ihRD,>:,L?R?p,1mR:P2O1n0100000020000REA0B6?XIB13<2RF,j>11>F1H>F'E13<7,H>PCP113<8,1>PCPBf5RF,3<RG/DARH,42P?P:PFO1n0100000020000=0B?P2f4RI,3<,1>RJ1YGARK12GA/EHRHf6RG,3</DARLPCP1f7,3</2ARMPCPBg00JWRN/42P?P:f9O1ROn0100000020000=0B?P2f8,3</2ARP1:B?PCPB14NNP?POn0100000020000=0B?eWGP6O1%CPRQ%B9RR%B;R;'WRS12DRRT11D;1VR;RU,2D[RV[RW11DRRXg00leRYAUR;2UW<R;11DU\Y^<XRXp,2HaRY11D>RZ12>UR['6R\P0PZP[P:f=O1=0B?R]P6p,2HnR^11D@R_12@URU'6R`P0P_PUP:fBRaO1=0B?RbP6f;g00mA1SDR':PTeO1RTPVp-0RRg00IYRcg00mgRd#@Re%RdRdPc1?c7RfP21?c8C<%PcRg%NcRhPc%M3,8cRig00o:18c3R318c95OcC=,FhR9,Gh%K4R4Ph19hFRj=Ih9P419hGC7C71ih5R5P6P71:CN1h67=0CNdAgcD2CfRDb>bAbBX4cX5cWCX2RW31;62,27g01aOR9[1;27,28,6IPG[[^4c^5c^Cc^2R^3RP6P:fGRGO1=0B?Rk13<GRG,1>PGP@P>f>fFRlO7b=b1X9UX8_P2P6O2n2001000000121000000b0X7[X6ZP2P6O2n2001000000121000000b0b?b1PCPBg00lERm,4NP?POn0100000020000=0B?eWEP6O1n10210010100021010211103b:b;WDP6O1%CJPKPHPLPCP1PMPCPB14m2P?POn0100000020000=0B?P2PSPWP;PXPYP\P0PZP[P]P6P^P`P0P_PUPbP6PTPVPePdPc%`cP2PfC<PgPhPcP3g00nSPiC=,FhRi,GhP4Ph19hI9IhiP4PjC7C7P5PDb>bAbBX4cX5cX2RX3R1162P9[1127/68PF[[^4c^5c^2R^3RP6Pk12GAPGP>PaPlO6b=Rlb1X9UX8_P2P6O2n2001000000121000000b0X7[X6ZP2P6O2n2001000000121000000b0b?b1PCPB14mNP?POn0100000020000=0B?eXDPP6O1PSPWP;PXPYP\P0PZP[P]P6P^P`P0P_PUPbP6PTPVPlb@X9UX8_P2P6O2n2001000000121000000b0X7[X6ZP2P6O2n2001000000121000000b0b1b@PCPB14mmP?POn0100000020000=0B?eXHQP6O1n10210010100021110211103b:b;WEP6O1n10210010100021110211103b:b;A0BE?e1_==REP=P=%]>1><@C\%@E3[=^:2P:P>P@P2PYP^p,3HanFZEap,2m'P2O1=0B?eWFWJo"). Qed.

Lemma wview_zeros_mono : forall x, wview segs m x <> None -> wview segs m' x <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h01Hh12H0h22Hxh31bi001bh41eh51oi011oh61xi021xi033segp;1p;3p;2p;6p;4p;7g002Sj10Tg003]j1;Tg004;j19Tg004^R0j1>Tg01alj3<Tg00=nj1LTg007Jj32Tg01_8j11Tg00gRj3@Tg005@j2:Tg006hj28Tg00WWj23Tg008dj1=Tg01bij37Tg01cmj1NTg01doj1MTg01enj1KTg01flj1HTg01;Xj24Tg01gJj15Tg01ghj26Tg000Mj6CTg01hoj2BTg00L8j2ATg00e9j1DTg00hdj4ETg00SEj1FTg00Tjj3GTg00Nfj3?Tg01_Qj7ITg000ij6JTg00I4R1#0#0#0R2#0#0#0#;R3#9R4%;2R2#9R5#>R6p,4segsR7p,1mR8f0R93<%L5R:32#1P6g00J7R;P6p,1aR<p,1nR=f1R>3@R?g00ih,:2,85R2P8P>O1n0100000020000P0P5P6P91859R@P0g00FnRAP6f2,33RB%=1R1577P;P6%N9RC%M9RDf3RE,33RF%K9#HRG'4#5'6P:n0100000020000P:n10110200021010300n10110200021010000=26:#1X56P?P;P;P0P5P6P;P6P9P2P8PEO1n0100000020000P@P0PAP6A77F1P;P6PCf4,33/4G#5,6DP:n0100000020000P:n10110200021010300n10110200021010000=26:#1P9A262:RFP6P2P0P5p-0P9g00leg01aOR2n10110100021000000X46g00K7P:P9ECP21B29b1W0%1FeP>n0110000020000b31A44RFP4P4%D<1:3=CE%FF3G=?8>P8P<P=P>p,2Hap,2Hnp,3HanFIEJP0P5P6p,2m'R5P>O1P@P0PAP6133>=771P;P6PC14BG#5,6DP:n0100000020000P:n10110200021010300n10110200021010000=26:#1eA<75>=26:#1eW2W6o"). Qed.

Lemma bytes_at_zeros_other : forall A bs,
  bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> bytes_at segs m' A bs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h06__sat3h14__x1h22a0h32H2h44__x2h51ih61Hh72H3h82H4h97__arithh:4__ffh;6__sat2h<8__varmaph=5__with>4__x3h?4cstrh@2HahA3Hi0hB4__x4hC4__x5hD5cstr0hE1AhF2H0hG2H1hH2H5hI2HdhJ2HihK2bshL1ohM1zi001bi011xp;1p;4p;2p;3p;7p;6p;8p;<g002Sj1>Tg003]j1ZTg004;j1jTg0023j1RTg019Oj4OTg015=j21Tg008dj1XTg00UJj2eTg01iNR0j2=Tg004^R1j1`Tg013RR2j14Tg00V^j23Tg00e9j1@Tg01ifj3ETg01joj3<Tg007Jj3;Tg00VCR3j28Tg01=\j1MTg00ZUj2iTg00UgR4j22Tg00[=j3fTg00[aj2dTg00A\j2FTg00SEj1cTg00\Bj2BTg00\`j1bTg00]>j1aTg00]ij2STg00^Lj2ATg00=nj1_Tg00aEj2^Tg00agj2]Tg00bSj3\Tg00c2j4[Tg01Amj1xTg01Elj3NTg00_Zj3wTg006hj2vTg01kMj2uTg01=5j4qTg01?=j1ITg01?\j2CTg01Mmj2HTg00Tjj3GTg0038j1WTg00WWj2oTg00`=j7nTg00fAj2mTg000ij6UTg01lXj2lTg00D5j4TTg00W;j2JTg01>cj2kTg00^oj4YTg00iDj7PTg00`aj8hTg01BKj4pTg01L_l<gTg01MDj3sTg01NYj7tTg00ihR5f0R6'Jp=0f2R7f1R8#4'3/J6p=61J86,k7p=91378/J6p=DP7g00jFR9g00jeR:P:g00kER;g00IYR<P8g00nSP6CYg00keR=FPp=7f3R>P9P:P:P;P7P8P6Ghp=5P<P7P8P6Cpp=?g00PWR?P<P0P2P4g01mof5R4f4R2P>P7P8P6M<gp=r%46,38p=QAs<86p=:P<P8g00o:P6CYp=KP8P9P:P:P;P6P=FPp=LP7P9P:P:P;P8P6Ftp=Vg00I4R=#>R0#>R@#>RA#Z#jRB#Rp,4segsRCp,1mRDP8P6COP3%0711B8%X0RE%>A#>#>RA#XRF'eRG56711B7RH,=6%`BRI%48RJ,32#@9ECDA<B>83;[^5?'8p,1aRK96>Hp,1nRH,3KRL;9>PCp,2m'RMP2P>CO[P6%0211B2=64G11B4RN,=6f7RO/3J#@9ECDf6RP=<B85;I[^5?'8P3A6PNG11BPRN,=6f8RQ/3J#@9ECDA<BO85;I[^5?A6ONK?9LOPCPMPQPOCO[P611BO=6QGf9,1BRO,=6f;RN/3J#@9ECDf:RR=<B85;I[^5?A6ROK?9LR%0N11BRRR#4RO=DNGRS11BN,=6RTf=RU/3JRV#@RW9ECMf<RX=<B85;IRY[^5?RZ'8%MRRR%0ORO1iEFR[125ER\%0F125G[R][R^%0ER_g00leR`AfEF8UW@RF%0G\`^@_R_p,2HaR`%0KRa12KGRb'8RcP3PaPbf@Rd#0P6p,2HnRe%0HRf12HGRg'8RhP3PfPgfERi#0P6PNg00mA1d5E'FP\eO1R\P]g00mgRN#cRj%RNRk1B<8%b<Rl%a<Rm1S<5Rn1A<=Ro57mRp%_:RqPpC51^m;RrP6P7g00J7Rsg00JWRt'F1]67=;stdA\<58C[R5b:b<b=X1<%06%08Rt[^1<P6fJRsPiO2b9b0X8gX7fP8P6O2n2001000000120000000b2X3bX6aP8P6O2n2001000000121000000b2b;b0b?PSPZPRPOP[P^PFP_P`PcP3PaPbf?RO,1B=6dGP6PePhP3PfPgfDRR,1B=6iGP6P\P]PjPk1B<7RZ%x<RS7?8PlPm1A<0Ru9N<oRv1S<E%ZARA5w<RE57mRwPqPwC5PrP5b:b<b=X1<X4<AD68GAD87G[^1<^4<P6fIRw,1B#4PsfAO3b9b0X8gX7fP8P6O2n2001000000121000000b2X3bX6aP8P6O2n2001000000121000000b2b;b0b?PIPDPWO1P1PBPIP61vB6f>R1%47RD'3#@,uCn10110100021010000A<BU75;IXLIP>P8P6O2PMPWO1P<PV126K?9L6XM<11BXRX,=8%4XRM,2JRIP8PJ1F<JPXPM1F<MErP6CqRMPI%M7RX%0DRD11B1R1#MRJ%41#0R1P[P^PFP_P`PcP3PaPb1QRQRR/2K?9LRP6PePhP3PfPg1QwURU/2K?9LUP6P\P]g01V@RL#IRQ#IRC#IRs#I,C<Rx1C<CRC1C<LRL':Ry':g01S=Rz'H1C<sRs1C<QRQ,:C':/Hz=GNj5GNPk1B<2??7S1B<4??>S7?8PlPmA7mnuRCPqPm%W0,A<R0,Ku,LmRuPqPmAN<o0R0%W=,A<R=57m1A<@9N<=R@=7mo5VmPq1Kv=,LmA7m@v5VmC5C5C5PrP5b:b<b=X1<X4<X><XB<XC<1274AD7P21324R@;9713>2R=/24134P;9=[[\t^1<^4<^><^B<^C<P6fM,1B#4RBPHPKfB#4RKfNRHPOPdfCO8b9b0XHgX8fP8P6O2n2001000000121000000b2X7bX3aP8P6O2n2001000000121000000b2b;b0bDb?bA1oAWPMPIPXPDPJP1P[P^PFP_P`PcP3PaPb%0R12RG'8P6PePhP3PfPg%0U12UG'8P6P\P]1:QL,:x/Hz1:sy/Hz=GNj5GNPk1B<>??>S9?Z8PlPmPCPqPmPuPqPmA7m0EPqPmPpPqPmP9P:P:P;A7mnv1KvE,LmFnC5C5C5C5PrP5b:b<b=X1<X4<X><127>AD72G%0>%0@12@G'8[[[\t^1<^4<^><P6PBPKPHPOPdPiPwO7b9b0X8gX7fP8P6O2n2001000000121000000b2X3bX6aP8P6O2n2001000000121000000b2b;b0bDb?bA,mVEU,lWEUPYeXJTX5?CTCTWIW6WGP8P6O2n2001000000121000000W3WFP8P6O2n2001000000121000000W3WKXE<o"). Qed.

Lemma wr_at_zeros : forall A k, wr_at segs m A k -> wr_at segs m' A k.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "h01ih12H2h26__sat3h34__x1h42a0h51Hh62H3h72H4h82Hah97__arithh:4__ffh;6__sat2h<8__varmaph=5__with>4__x2h?1Ah@2H0hA2H1hB2HihC1kp;4p;1p;2p;3p;7p;8g0142j4:Tg002Sj14Tg008dj1@Tg00UJj2[Tg00Ugj23Tg00VCR0j21Tg003]j1?Tg004;j1KTg004^j1JTg00V^j26Tg00e9j18Tg01alj37Tg00=nj1DTg007Jj35Tg01_8j19Tg00ZUj2XTg00[=j3WTg00[aj2VTg00A\j2BTg00SEj1UTg0023j1PTg00\Bj2ATg00\`j1OTg00]>j1LTg00]ij2<Tg00^Lj2=Tg00^oj4>Tg00aEj2ITg00agj2MTg00bSj3NTg00c2j4HTg01Amj1QTg01BKj4RTg01Elj3GTg00_Zj3STg01nQj2TTg00D5j4FTg00W;j2ETg00iDj7ZTg00`aj8YTg00ihR1f0R2'Ep=0f2R3f1R4'6/E2p=2P4g00jFR5g00jeR6P6g00kER7P2g00keFZp=Cf3R8P5P6P6P7P3P4P2GYp=;g00IYR5p,4segsR9p,1mR:P4P2C:P0%03g00I4R;#4R<#@R=%4<#4R>#4#4#4R?#@R@'[RA9234%02RB1323'1%?>#KR>#JRCf4RD/64#8979:%D>R>35#9[^05'1P9p,2m'REP8P3C:P2%0Df5R8?2DA1328,1Bf7RD/64#8979:=5C>#9[^05'1P0f6RF?28A132F,1Bf8R8/64#8979:=5C>#9[^05P9PEPDPFC:P2A28DAf9R8,32,1Bf;RD/64#8979:=5C>#9[^05f:R:#0A2:8AR8132:,1BR:f</64#8RF979E=5C>#9[^05R>'11X=@RC131=RE%0@131A[R9[RG%0=RHg00leRIAW=@4UW8R@%0A\I^8HRHp,2HaRIp,1aRJ#0RK13JARJ'1RLP0PKPJf>RM#0P2p,2HnRNp,1nRO#0RP13OARO'1RQP0PPPOfCRR#0P2PDg00mA1V1='BPEeO1REP9g00mgRD#URS%PDRD1A54%O5RT%L5RUP51<51g00nSRV1=5;R;C>,CURW%D6R6PWC;1IU7R7P2P3g00J7RWg00JWRX'B1M23=5WXdAN514CHR1b:b<b=X35%04\B^35P2fHRBPRO2b9b2X7OX6PP4P2O2n2001000000120000000b4X1JX5KP4P2O2n2001000000121000000b4b;b2P8P>PCPGP@PHPIPLP0PKPJf==2MAP2PNPQP0PPPOfB=2RAP2PEP9PSPDP51A53P4%Q5CRPTPUP51=5<9G5;PV1<5=%??5S5C>,CURUP6PUC;P7P1b:b<b=X35X>5A224AA243A[^35^>5P2fGPBf?O3b9b2X7OX6PP4P2O2n2001000000121000000b4X1JX5KP4P2O2n2001000000121000000b4b;b2P3P4P2O2,TFXB:X05CFCFW5WAP4P2O2n2001000000121000000W1W@P4P2O2n2001000000121000000W1XC5W?o"). Qed.

Lemma rw_cells_zeros_other : forall A cs,
  rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> rw_cells segs m' A cs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "h01Hh11Ah22Hbh32Hdh42Hwh53Hwfh62csh71np;1p;4p;2p;6p;3g0023j1DTg00oaj4;Tg0110j48Tg012@j12Tg013Rj11Tg0142j45Tg00V^j23Tg00W;j20Tg01>cj24Tg016lj17Tg018<j16Tg019Oj49Tg002Sj1:Tg003]j1CTg004;j1BTg015=j2ATg01okj2@Tg000ij6?Tg021Ej4>Tg00D5j4<Tg022cj3=Tg00IYg01PF#Dp,4segsR0p,1mR1f1R2f0R3C;g00VCR4P0P1f2R5P2C8P0P1P5%22#1C5f3R6%25#1'3p,1aR7'0p,1n,37R8/06'4P0p,2m'R9f4R:P6C;[P3P0P1P:P6C8P4%7:P0P1f5R4%6:C9P0P1f6R:%24#1C5f7R4%2:#1'3/071084'4P0P9f8R;P4C;[[P3%7:P0P1P;%64C9P0P1f9R1%2;#1C5f:R;%21#1'3/07108;'4P0P9f;R1P;C8P0P9P1%2;R4#1R:C5%7;P0P9P1%6;R9C9P6P1P9P5g00PWR5P4f<R4%13'3/071084'4X75P3g00I4#:#:#:#C#B/A91@;6E?C>C<A=1:2C<W3W4W2W5P2P3O2n2001000000120000000W0P2P3O2n2001000000120000000W0W6W1o"). Qed.

Lemma ro_cells_zeros_other : forall A cs,
  ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> ro_cells segs m' A cs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "h01Ah11Hh22Hbh32Hdh43Hwfh52csh61np;1p;4p;2p;6g0023j1ATg0248j49Tg016lj13Tg018<j17Tg019Oj48Tg012@j15Tg013Rj14Tg00V^j21Tg00W;j20Tg01>cj26Tg002Sj12Tg003]j1;Tg004;j1:Tg015=j2@Tg01okj2?Tg000ij6>Tg021Ej4<Tg00D5j4=Tg00IYg01PF#Ap,4segsR0p,1mR1f1R2f0R3C9g00VC%32P0P1f2R4%72C8f3R5%54#4'1p,1aR6'0p,1n,16R7/05'6P0p,2m'R8f4R9P5C9[P3%35P0P1f5R1%79C8f6R9%51#4'1/061079'6%39P0P8f7R8%79R0C8P4P8P0P2g00PWR8%59f8R1%43'1/061071'6X68P3g00I4#2#2#2#;#:/@01?94E>C<C=W3W2W4P2P3O2n2001000000120000000W1W5W0o"). Qed.

Lemma stk_zeros : forall lo hi, stk segs m lo hi -> stk segs m' lo hi.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h01bi001bh12H2h21ah32a0h46__sat3h54__x1h61Hh72H3h82H4h92Hah:7__arithh;4__ffh<6__sat2h=8__varmaph>5__with?2H0h@2H1hA2HbhB2HwhC2HxhD2b0hE2hihF2lohG1ohH1xi011xp;4p;1p;2p;3p;7p;6p;8g025Gj4<Tg002Sj1:Tg008dj1ATg00UJj2dTg00W;j21Tg00Ugj27Tg00VCR0j22Tg003]j1DTg004;j1?Tg004^R1j1NTg00e9j13Tg01alj39Tg00=nj1JTg007Jj30Tg01_8j18Tg006hj2HTg026RR2j25Tg00ZUj2ZTg00[=j3YTg00[aj2XTg00A\j2;Tg00SEj1FTg0023j1WTg00\Bj2VTg00\`j1UTg00]>j1TTg00]ij2CTg00^Lj2OTg00^oj4@Tg00aEj2MTg00agj2LTg00bSj3PTg00c2j4QTg00_Zj3KTg01nQj2RTg00gRj3STg005@j2ITg01kMj2=Tg026lj4GTg00L8j2cTg00hdj4bTg00Tjj3aTg00Nfj3`Tg01_Qj7_Tg000ij6^Tg00D5j4>Tg01ifj3]Tg00iDj7\Tg00`aj8[Tg00ihR3f0R4'1p=4f4R5f3R6f2R7f1R83];04p=6P8g00jFR9g00jeR:P:g00kER;P4g00keF\p=BP6P9P:P:P;P7P8P4G[p=Eg00IYR9p,4segsR<p,1mR=P8P4C<P0%47g00I4R>#:R?#AR@%:?#:R?#:#:#:RA#ARB'dRC,18RD11641747'2%D?R?#?RE#NRF%38RG99<=%JERH30#8PFP<P=%37RI1HE4RJD6X0E,5E'2RK[^29'2P<p,2m'RLP6P7C<P4%45115Cf6RM/14f5RN,74'2PK[^29'2P011NCf7RO/14174M'2PK[^29P<PLPOPMC<P411OCf:RP/14f9RQ,74'2PK[^29%4P11QCRRf;RS/14174P'2RTA9<LG=0FH#8PFP<PLPIPJD6X0E,5E'2[^29RG'21Z@BRU173@RV%4B173C[RW[RX%4@RYg00leRZAY@B8UW9RB%4C\Z^9YRYp,2HaRZp,1aR[#4R\17[CR]'2R^P0P\P]f>#4P4p,2HnR_p,1nR`#4Ra17`CRb'2RcP0PaPbfCRd#4P4PSg00mA1X3@';PVeO1RVPWg00mgRe#FRf%WeRe1V98Rg%U9Rh%T9RiP91C93g00nSRj1O9>R>C@,BiRk%J:R:PkCE1Mi;R;P4P7g00J7Rkg00JWRl';1L47=0kldAP938CQRlb;b=b>X59%44%48[^59P4fHPdO2b:b4X8bX7aP8P4O2n2001000000120000000b3X1]X6\P8P4O2n2001000000121000000b3b<b4PRPGPUPXPBPYPZP^P0P\P]f=R^/1CP4P_PcP0PaPbfB/1CP4PVPWPfPePgPhPiP9P>Pj1C9@%DARA5K9C@,BiRiP:PiCEP;Plb;b=b>X59114CPD[^59P4fGf?O2b:b4X8bX7aP8P4O2n2001000000121000000b3X1]X6\P8P4O2n2001000000121000000b3b<b4P7P8P4O2PKP0A9<=I=0FH#8PFP<P=%36R6PJD6X0E,5EA9<L6=0FH#8PFP<PL%35R5PJD6X0E,5E'2P4A9<=5=0FH#8PFP<P=%3MPJD6X0E,5EP2PEPFP<P=%3OROPJD6X0EA9<LO=0FH#8PFP<PLf8#3PJD6X0E,5E'2P4PFP<P=%3QPJD6%3PRP99<L=0FH#8PFP<PL%3SRSPJD6X0E,5ERH1RPNPFPkPFAS[`PRN1I?3R?,HER3P=PPO1n0100000020000P1PEPFP8PJf<#3RQ,=<ROn10110100021010000=0FJX0E,5EXGFPNPkPkP1PEPFPkPFP8P3P=%3^R^O1n0100000020000PJ1=<^n10110100021010000=0FJX0E,5EP4PEA0F3JX0EP?1;F3CGPEP1PEPFP=PQO1PJPOn10110100021010000=0FJX0EP7P8CGn0110000020000bD%?AR7/c7ROP7P7%3[1IA`Cb%FO3a=`=PP=P[P`PPPZP_p,3HanF_E^P1PEPFPLPSO1PJ1=<Sn10110100021010000=0FJX0E,5EePHeC>WAX0EP8P4O2n2001000000121101000W1WBP8P4O2n2001000000121000000b3XCTXH9C>C>W6W@P8P4O2n2001000000121000000W1W?P8P4O2n2001000000121000000W1XE9WFo"). Qed.

Lemma munch_zeros : forall W m0, munch W m0 m -> inside W a n -> munch W m0 m'.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h04__x1h14__x2h22a0h36__sat2h44__p1h54__x3h61Hh72H1h82H2h92H3h:7__arithh;4__ffh<8__varmaph=5__with>2Hah?6__sat1h@6__sat3hA1bi001bhB1li011lhC1ri021rhD2H0hE2H4hF3HinhG2HxhH1WhI2m0hJ2n0hK2n1hL1ohM1xi031np;1p;3p;2p;4p;7p;6p;8g0023j1NTg002Sj16Tg003]j1BTg004;j1>Tg004^j1mTg027Fj3GTg028Sj3]Tg00WWj21Tg029aj2WTg02;0j2TTg02;cj1OTg00Ugj20Tg00VCR0j24Tg007Jj3KTg01^Uj2dTg00X^j2MTg01^2R1j2DTg00V^j28Tg00W;j22Tg01>cj23Tg008dj1CTg00ZUj2ZTg00UJj2YTg00[=j3XTg00[aj2VTg00A\j2@Tg00SEj1UTg00\Bj2?Tg01Amj1STg01BKj4JTg00\`j1QTg00]>j1PTg00^Lj2:Tg00=nj1RTg00aEj2lTg00agj2kTg00bSj3jTg00c2j4iTg01_8j1LTg01]Oj2hTg00XAj2HTg0038j1cTg01Elj3FTg00`=j7`Tg02<Lj7_Tg01hoj2aTg01lXj2bTg000ij6^Tg00^oj4ATg00iDj7eTg01Obj6\Tg01NYj7fTg00`aj8gTg01`kj6[Tg00ihR2f0R3'2p=7g00IYR4f1R5g00o:P3CAp=;P5g00jFR6g00jeR7P7g00kER8P3g00keFep=5P5P6P7P7P8P3E\p==f2R9P6P7P7P8P5P3Ffp=If3R:P6P7P7P8P9P5P3Ggp=9P4P5g00nSP3CAp=<P5P6P7P7P8P3E[p=Eg02=f#Ng00I4R;#6R<#6#6R=#6#6#6R>#BR?#>R@%B=#>#mR=[p,1mRA9G53p,1aRBp,1nRC5]9f4RD11?3'W1T?511?5RE#7%O?,0E'4P=PAP9O1f6RAP:O19K=3XL=PDP9P5O2p,2m'R=P9O111?9RE/dB10EB1MEB'D11?:/MBg00J7REP111?D/0B11?ARA/0B18BCRF/2ARG'3P5f5RH,1?/0BRI%C<RJ%C>R>'ZRK102JRL%7>1YJ>RM,02[RN[RO%7JRPg00leRQAXJ>5UW>R>%7M\Q^>PRPp,2HaRQ%7BRR10BMRS'4RTP0PRPSf:,1?RU/0B12FU'3RVP3p,2HnRW%7CRX10CMRM'4RYP0PXPMf?,1?RZ/0B12FZ'3P3f;RZg00mA1V2J'@PLeO1RLPNp-0RJg00mgR[#UR\%N[R[P41?49R]P5%S4CJ%Q4R^%P4R_1:4;R`1:4<R<';,5_Ra%R7Rb1=_D9I_aC91l_8RaP3P9g00JWRc,@E1k39=KEcdAj425CiR2b;b<b=X04X14W410351059/3:[^04^14^4JP3fD,1?Rc,2FPBPcf>RcO4b:b3X9MX8XP5P3O2n2001000000121000000b2X7SX6RP5P3O2n2001000000121000000b2b?b3WBP3O1%LI1hFA1HFA,DGf7,1?,HFPEP1f8,1?,2FPVP5f9R1,1?,2FREPKPOP>PPPQPTP0PRPS11?cRG/0B12FG'3P3PWPYP0PXPMfC,1?RA/0B12FA'3P3PLPNP\P[P4P]P51?4:CJR]P^P_%c;,:4R;9F4</<`,5_RIPb1=_H=I_IC9PaP2b;b<b=X04X14X54X4J1859/23189:/25,3D[^04^14^54^4JP3fH,1?R?/0BPCPBP?PcO5b:b3X9MX8XP5P3O2n2001000000121000000b2X7SX6RP5P3O2n2001000000121000000b2b?b3WBP3O1%LEPcPBPCPUPZPKPOP>PPPQPTP0PRPS12BG10GF'4P3PWPYP0PXPM12BA10AF'4P3PLPNP\P[P]P^P_AF4`;R;/<<,5_,E_PbP_1;<`,5_,E_PbP_P6P7P7P81<`<,5_1;<;,5_F`C9C9PaP2b;b<b=X04X14X541839/25g01aOR2[1095P2[129:189D,0:'4[[^04^14^54P3PCP?PBPcfBO5b:b@XEMX9XP5P3O2n2001000000121000000b2X8SX7RP5P3O2n2001000000121000000b2b3b@P1F_,aVWKP3O1n10210010200021110111103bAbCWJP3O1n10210010200021110111103bAbC,b9E^bDWGXM@AG:9=eWFW6WIWHo"). Qed.

Lemma wmono_zeros : forall m0, wmono segs m0 m -> wmono segs m0 m'.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "h01Hh12Hxh22m0h31xp;1p;3p;2g002Sj10Tg003]j11Tg004;j12Tg004^j14Tg02?1j33Tg01alj39Tg00=nj18Tg007Jj35Tg01_8j16Tg01nQj27Tg00I4#0#0#0R0#0#0#0#1#2R1%10#2R0#4R2[p,4segsR3f0R4p,1m33f2R5=934%80552#6f1R2P5P2P4O2'7W1X31p,2m'9332eW0W2o"). Qed.

(* [comment removed for export] *)
Lemma mem_inv_zeros : mem_inv segs m -> (forall x : word, (a <= bv_unsigned x < a + n)%Z -> ro_addr segs x = false) -> mem_inv segs m'.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h02Hxh12b0h21ri001rh32Hah46__sat2h54__x1h64__x2h74__x3h82a0h91li011lh:2n0h;1xh<1Hh=2H0h>2H1h?2H2h@4HinvhA3HrohB7__arithhC4__ffhD6__sat1hE8__varmaphF5__withG1bi021bhH2l0hI2n1hJ1oi031np;2p;1p;3p;4p;7p;6p;8g01YQj2JTg002Sj15Tg003]j1ATg004;j1CTg00WWj22Tg00W;j21Tg00V^j2:Tg00Ugj23Tg00VCR0j27Tg02@>j29Tg004^j1LTg006hj26Tg007Jj30Tg00L8j2eTg00e9j1cTg005@j2FTg00hdj4[Tg00SEj1ITg00Tjj3YTg00Nfj3XTg00gRj3WTg01_Qj7VTg000Mj6UTg01]Oj2TTg00XAj2?Tg01^2R1j2GTg00X^j2;Tg00Y;j24Tg01^Uj2RTg008dj1>Tg00ZUj2NTg00UJj2MTg00[=j3OTg00[aj2PTg00A\j2=Tg0023j1QTg00\Bj2@Tg01BKj4KTg00\`j1STg00]>j1gTg00^Lj2<Tg0038j1fTg01Elj3dTg00^oj4ETg00=nj1bTg00`=j7`Tg00aEj2]Tg00agj2\Tg00bSj3^Tg00c2j4_Tg01_8j1HTg00iDj7aTg00`aj8ZTg00J7R2f0R3g00lER430p=8f1R5g00jFR6g00jeR7P7g00kER8P3g00keFap=Df3R9P6P7P7P8f2R:P5P3GZp=Bp,4segsR;p,1mR<'Jg00I4R=#5R>#5#5R?#5#5#5R@#ARA#CRBp,1aRC12A3RD'1p,1nRE,:CRF,3D'719;5#8[];%A?R?#CRD%LDRGp,2m'RHP5O116D330PG1eBBRIPBPB%cC1FAEC[%II3Y=X<:16D:90G3XJGP3P2PGAWCE:g00ihRI,F?,6DR?P<P:O1n0100000020000RJP<PCPEP:p,2HaRKp,2HnRLp,3HanFVEU16D590GJ12A9RJ,TC11CJ1?CJ'Gf4RJ,2A,?CP2P1f5,2A,1CP2PGf7RM,2A/;FRN,45P?P<PMO1RMn0100000020000f6RO,6DRP50Gf8RQ,9;#8]0P512AO,1CROP2PGg00JWRR/4NP?PMn0100000020000=0GP12AQRQ/RFRS13QF1;QF'GRQf9,2A/;FRTP2P1f:,2A/3FRUP2PG14R5P?P<f<R<O1RVn0100000020000f;RW,6DRD50Gf=RX,9;#8RY]0P512AW/3FRZP2PG14RRP?PVn0100000020000=0GDf>PX%>>R[%>@R@'N13I[R\11I@1M[@R],3I[R^[11I[R_g00leR`AO[@5UW311I]\`^3_PK11ICRK13C]R_'7P0PKP_fA,2AR`,1C13`F'7P3PL11IERL13E]R]'7P0PLP]fF,2AR0,1C130F'7P3PWg00mA1PI['=P\eO1P^g00IYR^g00mgR\#I%Q\P^1@^:P51@^9CK%S^%g^R\P^1<^>R>g00o:1<^=R[%f=,<^5d^CE,D\R=%b7RWP\P^P[g00nSP>CE,D\R>PWP\P6P7P7P8P>P=F`CBCB1]\8P3P:1=2R1\3:=02RdA^^I5C_bCbEbFX5^X6^W71:3:,35115:11:91::J,39'7[[^5^^6^^7^P3PEfK,2APCf?RCfDO5bBb4X?]X>LP5P3O2n2001000000121000000b8X=_X<KP5P3O2n2001000000121000000b8bDb4O2W0WHP3O1%HZRKP2PG14R4P?PVn0100000020000=0GDPCPXP<P3O3R<W0W:P3O1n10210210000021110110103P:O1b1b2W0W9P3O1%HOP2PG144NP?PMn0100000020000=0GPPSPQPTP2P1PUP2PG1445P?PVn0100000020000=0GDPY]0P5P2PG144RP?PVn0100000020000=0GDP<W0X9ZP3O1P2PG1444P?PVn0100000020000=0GDP<W0XIKP3O1n10210210000021010110103P:O1b1b2W0W:P3O1n10210210000021110111103P:O1b1b2b0W0WGX;B1J;HeWAW@o"). Qed.

(* [comment removed for export] *)
Lemma bytes_at_zeros_new : bytes_at segs m' a (repeat (Z_to_bv 8 0) (Z.to_nat n)).
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h04__x1h12a0h24__p1h34__p2h46__sat2h54__x2h64__x3h76__sat1h81Hh92H0h:2H1h;2H2h<7__arithh=4__ffh>8__varmaph?5__with@4__x4hA1ihB1xi001xhC2H3hD2z0hE2HahF3Hi0hG4cstrhH1nhI2HihJ6__sat0hK1mhL1ohM1yhN1zi011bp%0p&0p;1p;2p;3p;4p;<p;5p;6p;7p;8p;Bg002Sj1=Tg003]j1TTg004;j1bTg005@k20<Tg01DXR0j1~Tg02AKj3yTg015=j2oTg013RR1j19Tg00V^R2j21Tg008dj1PTg00UJj2aTg00W;R3j22Tg01iNR4j2GTg004^R5k109Tg00e9j1XTg01ifj3}Tg01joj3VTg007Jj37Tg00VCR6j20Tg00ZUj2uTg00UgR7j23Tg00[=j3nTg00[aj2lTg00A\j2JTg00SEj1jTg0023j1hTg00\Bj2DTg00\`j1fTg00]>j1dTg00]ij2ZTg00^Lj2ATg00=nj1`Tg00aEj2_Tg00agj2^Tg00bSj3]Tg00c2j4\Tg01EOj2[Tg01W_k10;Tg02Ajk40:Tg01L_l<OTg01>Ak200Tg01>cj2FTg01?=j1;Tg01?\j2QTg01BKj4MTg00_Zj3{Tg0038j1xTg01Elj3STg01CLj4pTg006hj2RTg01kMj2mTg02BMj5qTg02C2j4rTg01=5j4tTg01=\j1kTg01Amj1vTg00WWj2wTg00fAj2iTg000ij6ITg02CNj2zTg00D5j4WTg02Ddj3|Tg00^oj4NTg00iDj7gTg00`aj8KTg01O=l<YTg01L9lBeTg01MDk302Tg01Mmk203Tg00Tjk304Tg01Obk605Tg00`=k706Tg01NYj7cTg00ihR8f0R9'2p=6g00IYR:f1R;g00nSP9CNp=:P;g00jFR<g00jeR=P=g00kER>P9g00keFgp=4f3R?P<P=P=P>f2R@P;P9GKp=H1J:9p=>P:g00PWRAP:P:P0f4R0P1P?g01TPP@P;P9M<Yp>08PAP:P:P:P1P1f5RBP0P?P@P;P9M<Yp>07P:P:P:P:P:P:P2P9P;P@P2P?P0PBf6R2f7RCf8S00f9RDMBep>01A7:98p=E1Q:9p=<B02:;9p=5g00mgREg01S=-03;<049p=8P:P;g00o:P9CNp=BP;P<P=P=P>P9J05p=LP:P;g01SiP9CNp=CP@P<P=P=P>P;P9K06p=?P@P<P=P=P>P;P9Fcp=UP2P<P=P=P>PBP0P?P<P=P=P>P@P;P9GKGKp=@PAP:P4P1P7g01moPBP0P?P@P;P9M<Op=sp,1aR7#6R1g00I4R4#=R<#=RF#=RG#TRH#bRI20<H8RHp,1nRJ#~RK5yIRL'oRM#9,17%P<RN%=G#=#=RG#PRO'aRP'21G9M&09IRQp,4segsRRp,2m'S01%9;RS,17RT#XRU3}AVIL;S0237RV[^AA'01uNORW138NRX%6O138P[RY[RZ%6NR[g00leR\AnNO;UWERO%6P\\^E[R[p,2HaR\137PR],01R^P6P1P]P1P9p,2HnR_%6JR`13JPRa'0RbP6P`PaP1P9f;g00mA1l8N'JPXeO1RXPY%jERc%hERE1D:;%f:Rd%d:Re1Z:8Rf1A:4Rg':,4eRh%`=R=PhCH1_e>R>P9P@g00J7Rig00JWRj'J1^9@=7ijdA]:8;C\Rjb=b>b?X0:%69%6;Ri[^0:P9P7Q00O2b<b7X;aX:`P;P9O2n2001000000120000000b1X9]X81P;P9O2n2001000000121000000b1bJb7PAPK%99Rk,17/2P1G9;PV[^AA'0XHA%9KRl,17Rm/2PRn1G9KRoPV[^AAPn1[8JRn,17Rp/2PP:P:P3P9XB:RqP312;9$0;XM:XB:PmPpPqPqPqP:P:g02EF11;9H0:#>XK:XH:P7P7%>7PlPnPqPq%>kXBAPKPnPq1[89XB:S03PJPJ%>JI08S04J07N:01PPPP%>PM<O2008JRq138JRkA7:nJ'012J8R8%En'0'FRlPnP:PWPZPOP[P\P^P6P1P]1170/2PP9P_PbP6P`Pa117D/2PP9PXPYp-0Rpg01V@Rm#;R3#;Rr#<Rs%<3R31Q:mRm'5Rt'5Ru%;rRr#<Rv15smRw'5/8c'8PEP:1D:@P;1D:?S05CMPdPe1Z:N%TGRG5{:RN,Bg,4eS06P=Pe1LeB1A:<R<%x4,A:R4'C,4e5?e1Le2Rx1C<f,4e5?e5UeP=PeAS:g4Ry/:N,4eS07P=AS:g<Rz/:N,4eCHF@P>Pjb=b>b?X0:X5:X6:X2pW3139PR{A7:@?,00%E@,0B'F11@0/2P11?0R|/2P[[[^0:^5:^6:^2p^3pP9P8PkPJf>R}P7PCf?R~p,3HanS08O8b<b4XCaX;`P;P9O2n2001000000121000000b1X:]X81P;P9O2n2001000000121000000b1b7b4bDb9CpPQ1RIHS09P5PIPQP91RI9%9@R5,17#X,mRn10110000021010100AVIL@57QXLQPQQ02Q09PIPHPKP;P9DqCrQ01PUO1P:PT1279117JRQ,39'0XN:1G;K13SnRLP;PS%>SPKQ03PJO1Q04EsP9CtS04PL%k@RS%65R5PqPlPnP:PWPZPOP[P\P^P6P1P]%9D,17RD,2713DQ'0P9P_PbP6P`Pa%9},17RR,2713RQ'0P9PXPY15s3,5v15vt/8c'8PEP:P:1D:0P@%v:CMP;Q05CMRtPdPe1A:FRF/C4,4e9?ex1LeC1CFf,4e5?e5UeRxP=Pe1:f<,4eR4P=Pe1B<F,4eRFP=1:gz,4e1Bzy,4e5?eCHF@P>Pjb=b>b?X0:X5:X6:X@:X2pX3pA7:?@,00%E?,0B'F%6@13?B12?|11?B,3|'0[[[^0:^5:^6:^@:^2p^3pP9P8PkP}PJfC#9R|P7P~f@R?fAR@O9b<b4XCaX;`P;P9O2n2001000000121000000b1X:]X81P;P9O2n2001000000121000000b1b7b4bDb9bGbF1wGUQ04PLPSP5PqPlPnP:PWPZPOP[P\P^P6P1P]%6D13DP'0P9P_PbP6P`Pa%6R13RP'0P9PXPY%;rRr#;RY#;#<%<rRr/5w'515vs,5r%<Y15vm'515ru/8c'8'8'8PEPtPdPeQ06P=PePhP=PePxP=PeP4P=PePFP=PeQ07P=1:fz,4e1BzN,4e5?eF@F@F@P>Pjb=b>b?X0:X5:X6:X@:X2pX3pA7:B0,02%EB,0C'F%6013BC11BC/2P112CR2#6132P'0[[[[\i\{^0:^5:^6:^@:^2p^3pP9P8PkP}PJP|P7PCQ00P~P?P@Q08O<b<b4XCaX;`P;P9O2n2001000000121000000b1X:]X81P;P9O2n2001000000121000000b1b7b4bDb9bGbF,iTEI,zUEIPVeXIoXAACWPMA|IHKEICWo"). Qed.

Lemma wr_at_zeros_new : wr_at segs m' a n.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "p'0h06__sat1h14__x1h22a0h34__x2h41Hh52H0h62H1h72H2h87__arithh94__ffh:6__sat0h;8__varmaph<5__with=4__x3h>2Hah?1ih@2HihA1ehB1oi001ohC1zi011bi023segi031xp;2p;1p;3p;4p;6p;7p;8g00V^j20Tg002Sj16Tg008dj1CTg00UJj2sTg00W;j24Tg003]j1LTg004;j1\Tg004^R0j1ZTg00e9j1>Tg01alj3VTg00=nj1HTg007Jj3=Tg01_8j1DTg00VCR1j2:Tg00ZUj2iTg00Ugj28Tg00[=j3dTg00[aj2cTg00A\j2JTg00SEj1`Tg0023j1_Tg00\Bj2@Tg00\`j1]Tg00]>j1[Tg00]ij2ITg00^Lj2?Tg00aEj2YTg00agj2XTg00bSj3WTg00c2j4UTg01Amj1TTg01BKj4FTg01Elj3GTg00_Zj3RTg005@j2STg006hj2QTg00WWj2ETg01bij3rTg01cmj1qTg01doj1pTg01enj1oTg01flj1lTg01;Xj2kTg01gJj1jTg01ghj2hTg000Mj6gTg01hoj2fTg0038j1eTg01?=j1<Tg01?\j29Tg01MDj3;Tg01Mmj2MTg00Tjj3NTg00fAj2bTg000ij6KTg02CNj2aTg00D5j4OTg00^oj4PTg00iDj7mTg00`aj8nTg00`=j7^Tg00ihR2f0R3'4p=1f2R4f1R5/83':p=2g00IYR6P5g00nSP3CPp=5P5g00jFR7g00jeR8P8g00kER9P3g00keFmp=3f3R:P7P8P8P9P4P5P3Gnp=7P6P5g00o:P3CPp=BP4P7P8P8P9P5P3F^p=Ap,1aR7#1R;p,1nR<,07R=g00I4R>#6R?#CR@%6?#6RA#6#6#6RB#CRC'sRD'4RE%13RF?23<RG%LARA#\RH#ZRIp,4segsRJp,2m'RK1075RL#>RM3V%HHRN3=#DRO[^?6RP':1i@CRQ182@RR%1C182D[RS[RT%1@RUg00leRVAd@C5UW>RC%1D\V^>URUp,2HaRW187DRX,:;RYP1P;PXP;P3p,2HnRZ%1<R[18<DR\':R]P1P[P\P;P3f;g00mA1c2@'JPReO1RRPSg00mgR^#`R_%_^R`1@65%]6Ra%[6Rb1I62Rc1?6>Rd'5,3bRe%H8R8PeC71Yb9R9P3P4g00J7Rfg00JWRg'J1X34==fgdAW625CURgb9b;b<X16%15Rh\F^16P3P7f8RiO2b8b0X7\X6[P5P3O2n2001000000120000000b2X5XX4;P5P3O2n2001000000121000000b2b:b0PEPPPQPTPCPUPWPYP1P;PXPEP3PZP]P1P[P\PEP3PRPSP_P`P61@64REP5%T6CFPaPb1?6?R?9G6dRP1I6@%LBRB5R6R@'5,3bRjP8PjC7P9Pgb9b;b<X16X361035/4D1054Rj/4D[^16^36P3P<P7p,3HanRkO3b8b0X7\X6[P5P3O2n2001000000121000000b2X5XX4;P5P3O2n2001000000121000000b2b:b0PI1SA2,QHRAP0PHPIP31QH3P0g00FnPI1074#>,EB%C>5rJPfPI%q3%p3107:#>,EB%o3#l'k#j'hPNn0100000020000PNn10110300021010200n10110300021010100==IN#DXBIA=IANRfPIPAP0PHp-0P3PVg01aORVn10110000021000000XAIg00K7PNP3EgPV1fV3b5W4%DfePKPMO1P6PL1473?23=XC6PQPTPCPUPWPYP1P;PXf5,07RK,47?2K=P3PZP]P1P[P\f:,07Rf,47?2f=P3PRPSP_P`P6PEP51@6:CFREPaPb15c?,3b%e>,?6R>,B?,3b5AbR?P815dP,3bAG6d>R>,BP,3b5AbC7P9Pgb9b;b<X16X36X=6A2h54145j105:72j[^16^36^=6P3P<f?RjP7f>RhO4b8b0X7\X6[P5P3O2n2001000000121000000b2X5XX4;P5P3O2n2001000000121000000b2b:b01EBMPQPTPCPUPWPYP1P;PX%1K?2KDP3PZP]P1P[P\%1f?2fDP3PRPSg01V@RS#<RR#<Rf,96196R196SRS5;65;6g01S=RR'M%<fRf#<,96196f=;6S5;6/MR=N^_5N^P`PEPaPbPeP8PbP?P8Pb15>@,3bP815cP,3b1BP@,3b5AbC7C7C7P9Pgb9b;b<X16X36X=6%14?24:f4Rg,04/4D10:gRg#1?2gD[[\F^16^36^=6P3P<PjP7PiPhPkO6b8b0X7\X6[P5P3O2n2001000000121000000b2X5XX4;P5P3O2n2001000000121000000b2b:b0,bLEK,aMEKPOeX@GX?6COCOo"). Qed.

Lemma rw_cells_zeros_new : rw_cells segs m' a [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Zeros"] "h02Hah16__sat1h24__x1h32a0h41Hh52H0h62H1h72H2h87__arithh94__ffh:6__sat0h;8__varmaph<5__with=1lh>1nh?1zp;1p;2p;3p;4p;6p;7p;8g01DXj1aTg002Sj11Tg003]j1ETg004;j1ATg005@j2`Tg02AKj3OTg01Jkj2HTg00SEj14Tg00Tjj3CTg0110j4BTg012@j1@Tg013Rj17Tg0142j45Tg016lj1_Tg018<j1UTg019Oj4=Tg015=j2NTg007Jj39Tg02Ddj3LTg00D5j43Tg0023j1;Tg01:]j3GTg01;:j2DTg000ij66Tg008dj1:Tg00ZUj2FTg00Ugj22Tg00UJj2ITg00[=j3JTg00VCR0j28Tg00[aj2KTg00A\j2<Tg00\Bj2MTg00\`j1?Tg00]>j1PTg00]ij2QTg00^Lj2>Tg00^oj4RTg00iDj7STg00=nj1^Tg00`aj8]Tg00aEj2YTg00agj2VTg00bSj3WTg00c2j4XTg02Ejj2TTg01U=j2ZTg02FHj1[Tg00W;j2\Tg00ihR1f0R2'\p=0p,4segsR3p,2m'R4p,1aR5g01PFR6p,1nR7#aR8g00I4R9#1R:#1#1R;#ER<#AR=1`<1R<;O8R>'H%463CR6CBP3P4P5%@6#7C5R?%_6R@P3P4P5%U6C=R6g00PWRA1N=>;98g00leRBAL=<8g00K7C3P@e%;=R@P>P3P4P5P2C=X=@g02Fl%4=9G=>1D=>E6P6eC3PAP8P3P4P5%72C5X>Ag00IYRAP7P3P4P5P2C5X?Ag02HH%78%::R:%1;#1#1#:R;'F121:R4%0;1I:;R3,21[R6[%0:R>f1R=9J:;VBW0%03\B^0>p,2Ha%05R>1253R5'8P0P>P5%07RBP2p,2Hn1273R3,8BP0PBP3PBP2f;g00mA1K1:'<P4eO1P6g00mgR6#4%;61MA=%?A%PAR6g00jFR4g00jeR:P:g00kER0P6P4P:P:P0PA1QA1g00nS1>A9CRg00keFSR9%^:P9G]1Y60P2f2R0g00J7R6g00JWR9'<1V20=969dAWA1=CXb9b;b<X2A%02%0=[^2AP2P7f3O2b8b1X73X6BP=P2O2n2001000000120000000b3X55X4>P=P2O2n2001000000121000000b3b:b1,T7E6g01V@,Z8%[8E6P?eC3o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "p'0h01bi001bh11ri011rh22Hah34__p1h46__sat2h54__x1h64__x2h74__x3h82a0h91li021lh:2n0h;1Hh<2H0h=2H1h>2H2h?2Hxh@7__arithhA4__ffhB6__sat1hC8__varmaphD5__withE2l0hF2n1hG1ohH1xi031np;1p;2p;3p;4p;7p;6p;8g002Sj15Tg003]j1FTg004;j1@Tg00WWj22Tg00Ugj23Tg00V^j29Tg00W;j21Tg01>cj2CTg004^j1QTg00gRj3OTg00=nj1=Tg007Jj30Tg01]Oj2HTg00XAj2GTg01^2R0j2BTg00X^j2DTg00Y;j24Tg01^Uj2XTg008dj1ATg00ZUj2WTg00UJj2VTg00[=j3UTg00VCR1j2?Tg00[aj2RTg00A\j2;Tg00SEj1>Tg0023j1PTg00\Bj2<Tg01BKj4NTg00\`j1MTg00]>j1LTg0038j1KTg00^Lj2:Tg01Elj3JTg00^oj46Tg01NYj7ITg01Obj6STg00aEj2TTg00agj2eTg00bSj3dTg00c2j4cTg01_8j1ETg00L8j2bTg00e9j1aTg005@j2]Tg00hdj4\Tg00Tjj3[Tg00Mmj3ZTg02Iaj7YTg000ij6^Tg00iDj7_Tg00`aj8`Tf1R2g00jFR3g00jeR4P4g00kER5f0R6g00keF_p=7f3R7P3P4P4P5f2R8P2P6G`p=8g00I4R9#5R:#5#5R;#5#5#5R<#FR=#@R>12=6R?p,1aR@'3p,1nRA,9@RB/1?'C%F;#@R;#QR?g00J7RCP?AO@A2%=;R;p,1mRDP2O1REn0100000020000RFPDP8O190?6XG?12=2RG,H@11@G1G@G'B12=8,G@PCP012=7,1@PCP?f5RG,2=RH/DBRI,42P;PDPGO1RJn0100000020000=0?JP2f4RJ,2=,1@RK1XHBRL13HB/BIRIf6RH,2=/DBRMPCP0f7,2=/3BRNPCP?g00JWRO/42P;PDf9O1RPn0100000020000=0?PP2f8,2=/3BRB%A:RQ%A<R<'Wg00ihRR/3QRS11R<1VQ<RT,3R[RU[11RQRVg00leRWAUQ<2UW211RT\W^2Vp,2HaRV11R@RW13@TR<'?P1PWP<PDf=O190?;P6p,2HnRX11RARY13ATRT'?P1PYPTPDfBR1O190?;P6f;g00mA1RRQ';PSeO1PUp-0RUg00IYRSg00mgRQ#>%PQPS1<S8P21<S7CN%MS%LSRQPS%K9,:SRZg00o:R[1:S9R91:S:5JSR:C6,7Q%=4R\PQPSP9g00nSR]PZC6,7QP\PQPQP3P4P4P5PSPZP[P9C6,7QPSP:P]PZC6,7QFIP\PQP3P4P4P5PGESC8C8C81TQ5P6P81;CO1e68=0COdAdSR2CcbAbCbDX5SX6SW7W31962,38112713J81987/1J'CPH[[[^5S^6S^7S^3UP6PDfGRUO190?;12=UPAP@f>P1fFO7b@b4X>TX=YP2P6O2n2001000000121000000b8X<<X;WP2P6O2n2001000000121000000b8bBb4PCP?14OOP;PPn0100000020000=0?PeWEP6O1%EBRW1;?PR<PCP?g00lERY,4OP;PPn0100000020000=0?PeW:P6O1n10210010100021110210103b0b1W9P6O1%EKPLPIPMPCP0PNPCP?14Y2P;PPn0100000020000=0?PP2P<PCP?14YOP;PPn0100000020000=0?PeX9BP6O1P<PCP?14YYP;PPn0100000020000=0?PeXFWP6O1n10210010100021010210103b0b1W:P6O1n10210010100021110211103b0b1A0?FEe1b>>RFP>P>%a@1]=AC\%>F3[=ZD2PDP@PAP2PVPXp,3HanFYE^p,2m'P2O1=0?EeW?WHo"). Qed.

Lemma bytes_at_unmaps_other : forall A bs,
  bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> bytes_at segs m' A bs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "p'0h06__sat3h14__x1h22a0h32H2h44__x2h51ih61Hh72H3h82H4h97__arithh:4__ffh;6__sat2h<8__varmaph=5__with>4__x3h?4cstrh@2HahA3Hi0hB4__x4hC4__x5hD5cstr0hE1AhF2H0hG2H1hH2H5hI2HdhJ2HihK2bshL1ohM1zi001bi011xp;1p;4p;2p;3p;7p;6p;8p;<g002Sj1>Tg003]j1ZTg004;j1jTg0023j1RTg019Oj4OTg015=j21Tg008dj1XTg00UJj2eTg01iNR0j2=Tg004^R1j1`Tg013RR2j14Tg00V^j23Tg00e9j1@Tg01ifj3ETg01joj3<Tg007Jj3;Tg00VCR3j28Tg01=\j1MTg00ZUj2iTg00UgR4j22Tg00[=j3fTg00[aj2dTg00A\j2FTg00SEj1cTg00\Bj2BTg00\`j1bTg00]>j1aTg00]ij2STg00^Lj2ATg00=nj1_Tg00aEj2^Tg00agj2]Tg00bSj3\Tg00c2j4[Tg01Amj1xTg01Elj3NTg00_Zj3wTg006hj2vTg01kMj2uTg01=5j4qTg01?=j1ITg01?\j2CTg01Mmj2HTg00Tjj3GTg0038j1WTg00WWj2oTg00`=j7nTg00fAj2mTg000ij6UTg02K<j2lTg00D5j4TTg00W;j2JTg01>cj2kTg00^oj4YTg00iDj7PTg00`aj8hTg01BKj4pTg01L_l<gTg01MDj3sTg01NYj7tTg00ihR5f0R6'Jp=0f2R7f1R8#4'3/J6p=61J86,k7p=91378/J6p=DP7g00jFR9g00jeR:P:g00kER;g00IYR<P8g00nSP6CYg00keR=FPp=7f3R>P9P:P:P;P7P8P6Ghp=5P<P7P8P6Cpp=?g00PWR?P<P0P2P4g01mof5R4f4R2P>P7P8P6M<gp=r%46,38p=QAs<86p=:P<P8g00o:P6CYp=KP8P9P:P:P;P6P=FPp=LP7P9P:P:P;P8P6Ftp=Vg00I4R=#>R0#>R@#>RA#Z#jRB#Rp,4segsRCp,1mRDP8P6COP3%0711B8%X0RE%>A#>#>RA#XRF'eRG56711B7RH,=6%`BRI%48RJ,32#@9ECDA<B>83;[^5?'8p,1aRK96>Hp,1nRH,3KRL;9>PCp,2m'RMP2P>CO[P6%0211B2=64G11B4RN,=6f7RO/3J#@9ECDf6RP=<B85;I[^5?'8P3A6PNG11BPRN,=6f8RQ/3J#@9ECDA<BO85;I[^5?A6ONK?9LOPCPMPQPOCO[P611BO=6QGf9,1BRO,=6f;RN/3J#@9ECDf:RR=<B85;I[^5?A6ROK?9LR%0N11BRRR#4RO=DNGRS11BN,=6RTf=RU/3JRV#@RW9ECMf<RX=<B85;IRY[^5?RZ'8%MRRR%0ORO1iEFR[125ER\%0F125G[R][R^%0ER_g00leR`AfEF8UW@RF%0G\`^@_R_p,2HaR`%0KRa12KGRb'8RcP3PaPbf@Rd#0P6p,2HnRe%0HRf12HGRg'8RhP3PfPgfERi#0P6PNg00mA1d5E'FP\eO1R\P]g00mgRN#cRj%RNRk1B<8%b<Rl%a<Rm1S<5Rn1A<=Ro57mRp%_:RqPpC51^m;RrP6P7g00J7Rsg00JWRt'F1]67=;stdA\<58C[R5b:b<b=X1<%06%08Rt[^1<P6fJRsPiO2b9b0X8gX7fP8P6O2n2001000000120000000b2X3bX6aP8P6O2n2001000000121000000b2b;b0b?PSPZPRPOP[P^PFP_P`PcP3PaPbf?RO,1B=6dGP6PePhP3PfPgfDRR,1B=6iGP6P\P]PjPk1B<7RZ%x<RS7?8PlPm1A<0Ru9N<oRv1S<E%ZARA5w<RE57mRwPqPwC5PrP5b:b<b=X1<X4<AD68GAD87G[^1<^4<P6fIRw,1B#4PsfAO3b9b0X8gX7fP8P6O2n2001000000121000000b2X3bX6aP8P6O2n2001000000121000000b2b;b0b?PIPDPWO1P1PBPIP61vB6f>R1%47RD'3#@,uCn10110100021010000A<BU75;IXLIP>P8P6O2PMPWO1P<PV126K?9L6XM<11BXRX,=8%4XRM,2JRIP8PJ1F<JPXPM1F<MErP6CqRMPI%M7RX%0DRD11B1R1#MRJ%41#0R1P[P^PFP_P`PcP3PaPb1QRQRR/2K?9LRP6PePhP3PfPg1QwURU/2K?9LUP6P\P]g01V@RL#IRQ#IRC#IRs#I,C<Rx1C<CRC1C<LRL':Ry':g01S=Rz'H1C<sRs1C<QRQ,:C':/Hz=GNj5GNPk1B<2??7S1B<4??>S7?8PlPmA7mnuRCPqPm%W0,A<R0,Ku,LmRuPqPmAN<o0R0%W=,A<R=57m1A<@9N<=R@=7mo5VmPq1Kv=,LmA7m@v5VmC5C5C5PrP5b:b<b=X1<X4<X><XB<XC<1274AD7P21324R@;9713>2R=/24134P;9=[[\t^1<^4<^><^B<^C<P6fM,1B#4RBPHPKfB#4RKfNRHPOPdfCO8b9b0XHgX8fP8P6O2n2001000000121000000b2X7bX3aP8P6O2n2001000000121000000b2b;b0bDb?bA1oAWPMPIPXPDPJP1P[P^PFP_P`PcP3PaPb%0R12RG'8P6PePhP3PfPg%0U12UG'8P6P\P]1:QL,:x/Hz1:sy/Hz=GNj5GNPk1B<>??>S9?Z8PlPmPCPqPmPuPqPmA7m0EPqPmPpPqPmP9P:P:P;A7mnv1KvE,LmFnC5C5C5C5PrP5b:b<b=X1<X4<X><127>AD72G%0>%0@12@G'8[[[\t^1<^4<^><P6PBPKPHPOPdPiPwO7b9b0X8gX7fP8P6O2n2001000000121000000b2X3bX6aP8P6O2n2001000000121000000b2b;b0bDb?bA,mVEU,lWEUPYeXJTX5?CTCTWIW6WGP8P6O2n2001000000121000000W3WFP8P6O2n2001000000121000000W3WKXE<o"). Qed.

Lemma wr_at_unmaps_other : forall A k,
  wr_at segs m A k -> (A + k <= a \/ a + n <= A)%Z -> wr_at segs m' A k.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "p'0h06__sat3h14__x1h22a0h32H2h44__x2h51ih61Hh72H3h82H4h97__arithh:4__ffh;6__sat2h<8__varmaph=5__with>4__x3h?2Hah@4__x4hA4__x5hB1AhC2H0hD2H1hE2H5hF2HdhG2HihH1khI1ohJ1zi001bi013segi021xp;4p;1p;2p;3p;6p;7p;8g0142j4LTg002Sj1>Tg008dj1HTg00UJj2xTg003]j1UTg004;j1aTg004^R0j1^Tg00V^j22Tg00e9j1:Tg01alj3BTg00=nj1WTg007Jj38Tg01_8j1;Tg00VCR1j2<Tg00ZUj2iTg00Ugj24Tg00[=j3gTg00[aj2fTg00A\j2MTg00SEj1cTg0023j1bTg00\Bj2@Tg00\`j1`Tg00]>j1_Tg00]ij2NTg00^Lj2?Tg00aEj2]Tg00agj2\Tg00bSj3[Tg00c2j4ZTg01Amj1YTg01Elj3FTg00_Zj3XTg006hj2wTg00WWj2GTg01bij3vTg01cmj1uTg01doj1tTg01enj1pTg01flj1oTg01;Xj2nTg01gJj1mTg01ghj2jTg01?=j1ETg01?\j2ATg01Mmj2DTg00Tjj3CTg0038j1STg00fAj2hTg000ij6VTg02K<j2kTg00D5j4OTg00W;j2ITg01>cj2lTg00^oj4TTg00iDj7PTg00`aj8eTg01BKj4dTg01MDj3qTg00`=j7rTg01NYj7sTg00ihR2f0R3'Ip=0f2R4f1R5'2/I3p=11453,<4p=31I53,l4p=6P4g00jFR6g00jeR7P7g00kER8g00IYR9P5g00nSP3CTg00keR:FPp=5f3R;P6P7P7P8P4P5P3Gep=9P9P4P5P3Cdp==Aq953p=7P9P5g00o:P3CTp=KP5P6P7P7P8P3P:FPp=JP4P6P7P7P8P5P3Frp=QP4P6P7P7P8P5P3Fsp=Rp,4segsR6p,1mR:P5P3CLP1%04R<g00I4R=#>R>#HR?%>>R@#>RA#>#>#>RB#HRC'xRD9145%03RE?334%UA#aRA#^RFf4RG/25#:9B6:%WARH38#;[^59'<p,1aRI91;4p,1nRJ,2IRK;6;P6p,2m'RLPGP;CL[P3%0Gf5RM?1GDA3E3Mf7RN/25#:9B6:=8FH#;[^59'<P1f6RO?1MDA3E3Of8RP/25#:9B6:=8FH#;[^59A1NOI?6KNP6PLPPPNCL[P3A1PNDf9RP93E3f;RN/25#:9B6:=8FH#;[^59f:RO?1PI?6KO%0NA1NODRPA3E3NRQf=/25RR#:RS9B6L=8FH#;RT[^59RU'<1i?CRV142?RW%0C142D[RX[RY%0?RZg00leR[Ag?C5UW?RC%0D\[^?ZRZp,2HaR[%0IR\14IDR]'<R^P1P\P]f?R_#0P3p,2HnR`%0JRa14JDRb'<RcP1PaPbfDRd#0P3PNg00mA1f2?'MPWeO1RWPXg00mgRN#cRe%bNRf1@95%`9Rg%_9Rh1N92Ri1?9=Rj55hRk%W7R7PkC91]h8R8P3P4g00J7Rlg00JWRm'M1\34=8lmdA[925CZR2b:b<b=X19%05Rm\E^19P3fIREPdO2b9b0X8bX7aP5P3O2n2001000000120000000b2X3]X6\P5P3O2n2001000000121000000b2b;b0PPPUPVPYPCPZP[P^P1P\P]f>RU=1_DP3P`PcP1PaPbfC=1dDP3PWPXPePf1@94Rd%Y9RP7=5PgPh1?9>Rn9F9jRo1N9?%UBRB5X9R?55hRpP7PpC9P8P2b:b<b=X19X49A135DA154D[^19^49P3fHPEf@REO3b9b0X8bX7aP5P3O2n2001000000121000000b2X3]X6\P5P3O2n2001000000121000000b2b;b0PFP:PSO1P0PAPFP31wA3P0g00FnPF12U4#:,GB%H=5v6PlPF%u3%t312_;#:,GB%p3#o'n#m'jPHn0100000020000PHn10110200021010100n10110200021010000=8FH#;XIFP;P5P3O2PLPSO1P9PR143I?6K3XJ9PVPYPCPZP[P^P1P\P]fA/2MRL/4I?6KLP3P`PcP1PaPbfFRF/2ORO/4I?6KOP3PWPXg01V@RK#ERH#ERl#ER6,A9R01A9lRl1A9HRH'7'7g01S=RA'D%E6,A9R61A9KRK,7lRl'7/DA=CNe5CNPf1@9G?=4P1@9M?=;P7=5PgPhA5hin%S>,?9R>,Kn,Jh5QhRnP7PhAF9j>R>%S=,?9R=55h1?9@9F9=R@=5hj5RhP71Ko=,JhA5h@o5RhC9C9P8P2b:b<b=X19X49X>9X@9XA9A3m5GA15M;12;GR@;65124;R=/4G12GM;6=[[^19^49^>9^@9^A9P3fJR=PJPIP_fKRIPUPEO7b9b0XEbX8aP5P3O2n2001000000121000000b2X7]X3\P5P3O2n2001000000121000000b2b;b01GBSPVPYPCPZP[P^P1P\P]%0L?3LDP3P`PcP1PaPb%0O?3ODP3PWPX170l/DA17HK,76/DA=CNe5CNPf1@9;?=;P9=d5PgPhPnP7PhA5h>?P7PhPkP7A5hio1Ko?,Jh5QhC9C9C9P8P2b:b<b=X19X49X>9A3m54A15;D%0@?3@D\<[[^19^49^>9P3P=P_PIPUfBPFO6b9b0X8bX7aP5P3O2n2001000000121000000b2X3]X6\P5P3O2n2001000000121000000b2b;b0,hREV,kSEVPTeXGQX59COCOWFW6WDP5P3O2n2001000000121000000W3WCP5P3O2n2001000000121000000W3XH9XB9o"). Qed.

Lemma rw_cells_unmaps_other : forall A cs,
  rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> rw_cells segs m' A cs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "h01Hh11Ah22Hbh32Hdh42Hwh53Hwfh62csh71np;1p;4p;2p;6g0023j1DTg00oaj4;Tg0110j48Tg012@j12Tg013Rj11Tg0142j45Tg00V^j23Tg00W;j20Tg01>cj24Tg016lj17Tg018<j16Tg019Oj49Tg002Sj1:Tg003]j1CTg004;j1BTg015=j2ATg01okj2@Tg000ij6?Tg02LTj4>Tg00D5j4<Tg02N3j4=Tg00IYg01PF#Dp,4segsR0p,1mR1f1R2f0R3C;g00VCR4P0P1f2R5P2C8P0P1P5%22#1C5f3R6%25#1'3p,1aR7'0p,1n,37R8/06'4P0p,2m'R9f4R:P6C;[P3P0P1P:P6C8P4%7:P0P1f5R4%6:C9P0P1f6R:%24#1C5f7R4%2:#1'3/071084'4P0P9f8R;P4C;[[P3%7:P0P1P;%64C9P0P1f9R1%2;#1C5f:R;%21#1'3/07108;'4P0P9f;R1P;C8P0P9P1%2;R4#1R:C5%7;P0P9P1%6;R9C9P6P1P9P5g00PWR5P4f<R4%13'3/071084'4X75P3g00I4#:#:#:#C#B/A91@;6E?C>C<P1P:P2P3C=C<W3W4W2W5P2P3O2n2001000000120000000W0P2P3O2n2001000000120000000W0W6W1o"). Qed.

Lemma ro_cells_unmaps_other : forall A cs,
  ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> ro_cells segs m' A cs.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "h01Ah11Hh22Hbh32Hdh43Hwfh52csh61np;1p;4p;2p;6g0023j1ATg0248j49Tg016lj13Tg018<j17Tg019Oj48Tg012@j15Tg013Rj14Tg00V^j21Tg00W;j20Tg01>cj26Tg002Sj12Tg003]j1;Tg004;j1:Tg015=j2@Tg01okj2?Tg000ij6>Tg02LTj4<Tg00D5j4=Tg00IYg01PF#Ap,4segsR0p,1mR1f1R2f0R3C9g00VC%32P0P1f2R4%72C8f3R5%54#4'1p,1aR6'0p,1n,16R7/05'6P0p,2m'R8f4R9P5C9[P3%35P0P1f5R1%79C8f6R9%51#4'1/061079'6%39P0P8f7R8%79R0C8P4P8P0P2g00PWR8%59f8R1%43'1/061071'6X68P3g00I4#2#2#2#;#:/@01?94E>C<C=W3W2W4P2P3O2n2001000000120000000W1W5W0o"). Qed.

Lemma stk_unmaps_other : forall lo hi, stk segs m lo hi -> (hi <= a \/ a + n <= lo)%Z -> stk segs m' lo hi.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "p'0h02a0h11bi001bh26__sat3h34__x1h42H2h51ah61Hh72H3h82H4h97__arithh:4__ffh;6__sat2h<8__varmaph=5__with>4__x2h?4__x3h@2HahA4__x4hB4__x5hC1ohD1EhE2H0hF2H1hG2H5hH2HbhI2HdhJ2HwhK2HxhL2hihM2lohN1xi011xhO1zi023segp;4p;1p;2p;3p;6p;7p;8g025Gj4OTg002Sj1>Tg008dj1GTg00UJj2}Tg00W;j20Tg00Ugj24Tg00VCR0j23Tg003]j1QTg004;j1aTg004^R1j1^Tg00e9j12Tg01alj3=Tg00=nj1XTg006hj2NTg026RR2j2:Tg00V^j2JTg00ZUj2jTg00[=j3iTg00[aj2fTg00A\j2STg00SEj1dTg0023j1bTg00\Bj2BTg00\`j1`Tg00]>j1_Tg00]ij2PTg00^Lj2ATg00aEj2]Tg00agj2\Tg007Jj3@Tg00bSj3[Tg00c2j4ZTg00_Zj3YTg01?=j1FTg01?\j2CTg01Mmj2ETg00Tjj3DTg01Amj1|Tg0038j1WTg01Elj3{Tg00WWj2ITg00fAj2zTg000ij6LTg02K<j2xTg01bij3wTg01cmj1tTg01doj1sTg01enj1rTg01flj1pTg01;Xj2oTg01gJj1nTg01ghj2kTg01kMj2lTg026lj4mTg00D5j4MTg01_8j1hTg01ifj3gTg01>cj2qTg00^oj4UTg00iDj7RTg00`aj8eTg01MDj3uTg01BKj4vTg00`=j7cTg01NYj7yTg00ihR3f0R4'0p=1f2R5f1R6;@4#hp=7f4R7f3R8?g56;@4p=51064,q5p=81464,35p=6P5g00jFR9g00jeR:P:g00kER;g00IYR<P6g00nSP4CUg00keR=FRp=9P8P9P:P:P;P5P6P4Gep=<Au<64p=;P<P5P6P4Cvp=?P<P6g00o:P4CUp=KP6P9P:P:P;P4P=FRp=HP5P9P:P:P;P6P4Fcp=VP5P9P:P:P;P6P4Fyp=Tp,4segsR9p,1mR=P6P4COP0%15g00I4R>#>R?#GR@%>?RA#>RB#>#>#>RC#GRD'}RE,06RF1084RG1445RH'3%QB#aRB#^RI%26RJ9=9=%XBRK37PIP9P=%25RL1NB4RMD5X1B,:B'3RN[^5<'3p,1aRO,05p,1nRP,JORQ;88P9p,2m'RRP7P8CO[P4%17107Ef6RS/04f5RT764PN[^5<'3P010TEf7RU/04?64SPN[^5<10SO?8QUP9PRf8RVPUCO[P410UEf:RW/04f9RX764PN[^5<10XO?8QWf;RY#110WERZf<R[/04?64YR\A=9RJ=7IKPIP9PRPLPMD5X1B,:B'3[^5<RJ'31j@DR]143@R^%1D143E[R_[R`%1@Rag00leRbAi@D6UW@RD%1E\b^@aRap,2HaRb%1ORc14OERd'3ReP0PcPdf?#1P4p,2HnRf%1PRg14PERh'3RiP0PgPhfDRj#1P4PYg00mA1f3@'SP^eO1R^P_g00mgRk#dRl%bkRm1B<6Rn%`<Ro%_<Rp1P<3Rq1A<>Rr59pRs%X:R:PsC<1]p;R;P4P5g00J7Rtg00JWRu'S1\45=@tudA[<36CZR3b:b<b=X3<%14%16[^3<P4fIRuPjO2b9b2X8hX7gP6P4O2n2001000000120000000b0X4dX6cP6P4O2n2001000000121000000b0b;b2PZPJP]P`PDPaPbPeP0PcPdf>RJ/0EP4PfPiP0PgPhfCRZ/0EP4P^P_PlPmPnPoPp1P<@%QCRC5Y<R@99prRnP:PnC<P;P3b:b<b=X3<104EPF[^3<P4fHRFf@O2b9b2X8hX7gP6P4O2n2001000000121000000b0X4dX6cP6P4O2n2001000000121000000b0b;b2P8P6P4O2PNP0A=9=L=7IKPIP9P=%28RLPMD5X1B,:BA=9RL=7IKPIP9PR%27RLPMD5X1B,:B'3P4A=9=L=7IKPIP9P=%2SPMD5X1B,:BP2PBPIP9P=%2URUPMD5X1BA=9RU=7IKPIP9PR%2VPMD5X1B,:B'3P4PIP9P=%2XPMD5%2WRXP<PW144O?8Q4XO<P]P`PDPaPbPeP0PcPd14JO?8QJP4PfPiP0PgPh14ZO?8QZP4P^P_g01V@RQ#FRV#FRU#FR2,C<RL1C<URU1C<VRV';';g01S=RN'E%F2,C<R21C<QRQ,;URU';/EN=Dkl5DkPm1B<7%|<Rn7?51B<T??8n7?6PoPp1A<ARA=9pr%W?,A<Rj,Kr,Hp5VpRvP:Pp1A<?R?99pj%W>,A<9{<?Rw=9pA5TpP:1Kr?,HpA9pwr5TpC<C<P;P3b:b<b=X3<X><X?<XA<XB<A6G4710T51J58;8714581J87;85[[^3<^><^?<^A<^B<P4fSR7fTRTPPPOPFfGROPuO7b9b2XGhX8gP6P4O2n2001000000121000000b0X7dX4cP6P4O2n2001000000121000000b0b;b21ICXP]P`PDPaPbPeP0PcPd%1J?6JEP4PfPiP0PgPh%1Z?6ZEP4P^P_1;LU/EN1;VQ,;2/EN=Dkl5DkPm1B<5??8n1B<8??8n7?6PoPpPvP:PpA9pj@P:PpA9pqAP:1Kr@,Hp9VpsC<C<C<P;P3b:b<b=X3<X><X?<1064/3H108E%18RHA6H8E[[[^3<^><^?<P4P7PTPFPOfKfOO6b9b2X8hX7gP6P4O2n2001000000121000000b0X4dX6cP6P4O2n2001000000121000000b0b;b2,zWEL'xPRPXO1P=PXO15@I%2YRY9=9R=7IKRXPIP9PR%2[R[PMD5X1BRW,:BPIP=PYO1R=P1PBPIP4PMP1g00FnPI1IC[%G>5w9PtPI%t4%s4f=#2,IC%r4#p'o#n'kPKn0100000020000PKn10110100021010200n10110100021010000=7IKXCIPSPRPYO1RSP4ELPXePBPWP5PIP=P1PBPIP4PM1l9[n101101000210100001NB85@IXCIP6PSP4ELPIP9PRPY1NB5D5eCmCMbDWHX1BP6P4O2n2001000000121101000W4WJP6P4O2n2001000000121000000b0XK\XN<CMCMWIW6WFP6P4O2n2001000000121000000W4WEP6P4O2n2001000000121000000W4XL<XM<o"). Qed.

Lemma munch_unmaps : forall W m0, munch W m0 m -> inside W a n -> munch W m0 m'.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "p'0h04__x1h14__x2h22a0h36__sat2h44__p1h54__x3h61Hh72H1h82H2h92H3h:7__arithh;4__ffh<8__varmaph=5__with>2Hah?6__sat1h@6__sat3hA1bi001bhB1li011lhC1ri021rhD2H0hE2H4hF3HinhG2HxhH1WhI2m0hJ2n0hK2n1hL1ohM1xi031np;1p;3p;2p;4p;7p;6p;8g0023j1NTg002Sj16Tg003]j1BTg004;j1>Tg004^j1mTg027Fj3GTg028Sj3]Tg00WWj21Tg029aj2WTg02;0j2TTg02;cj1OTg00Ugj20Tg00VCR0j24Tg007Jj3KTg01^Uj2dTg00X^j2MTg01^2R1j2DTg00V^j28Tg00W;j22Tg01>cj23Tg008dj1CTg00ZUj2ZTg00UJj2YTg00[=j3XTg00[aj2VTg00A\j2@Tg00SEj1UTg00\Bj2?Tg01Amj1STg01BKj4JTg00\`j1QTg00]>j1PTg00^Lj2:Tg00=nj1RTg00aEj2lTg00agj2kTg00bSj3jTg00c2j4iTg01_8j1LTg01]Oj2hTg00XAj2HTg0038j1cTg01Elj3FTg00`=j7`Tg02<Lj7_Tg01hoj2aTg02K<j2bTg000ij6^Tg00^oj4ATg00iDj7eTg01Obj6\Tg01NYj7fTg00`aj8gTg01`kj6[Tg00ihR2f0R3'2p=7g00IYR4f1R5g00o:P3CAp=;P5g00jFR6g00jeR7P7g00kER8P3g00keFep=5P5P6P7P7P8P3E\p==f2R9P6P7P7P8P5P3Ffp=If3R:P6P7P7P8P9P5P3Ggp=9P4P5g00nSP3CAp=<P5P6P7P7P8P3E[p=Eg02=f#Ng00I4R;#6R<#6#6R=#6#6#6R>#BR?#>R@%B=#>#mR=[p,1mRA9G53p,1aRBp,1nRC5]9f4RD11?3'W1T?511?5RE#7%O?,0E'4P=PAP9O1f6RAP:O19K=3XL=PDP9P5O2p,2m'R=P9O111?9RE/dB10EB1MEB'D11?:/MBg00J7REP111?D/0B11?ARA/0B18BCRF/2ARG'3P5f5RH,1?/0BRI%C<RJ%C>R>'ZRK102JRL%7>1YJ>RM,02[RN[RO%7JRPg00leRQAXJ>5UW>R>%7M\Q^>PRPp,2HaRQ%7BRR10BMRS'4RTP0PRPSf:,1?RU/0B12FU'3RVP3p,2HnRW%7CRX10CMRM'4RYP0PXPMf?,1?RZ/0B12FZ'3P3f;RZg00mA1V2J'@PLeO1RLPNp-0RJg00mgR[#UR\%N[R[P41?49R]P5%S4CJ%Q4R^%P4R_1:4;R`1:4<R<';,5_Ra%R7Rb1=_D9I_aC91l_8RaP3P9g00JWRc,@E1k39=KEcdAj425CiR2b;b<b=X04X14W410351059/3:[^04^14^4JP3fD,1?Rc,2FPBPcf>RcO4b:b3X9MX8XP5P3O2n2001000000121000000b2X7SX6RP5P3O2n2001000000121000000b2b?b3WBP3O1%LI1hFA1HFA,DGf7,1?,HFPEP1f8,1?,2FPVP5f9R1,1?,2FREPKPOP>PPPQPTP0PRPS11?cRG/0B12FG'3P3PWPYP0PXPMfC,1?RA/0B12FA'3P3PLPNP\P[P4P]P51?4:CJR]P^P_%c;,:4R;9F4</<`,5_RIPb1=_H=I_IC9PaP2b;b<b=X04X14X54X4J1859/23189:/25,3D[^04^14^54^4JP3fH,1?R?/0BPCPBP?PcO5b:b3X9MX8XP5P3O2n2001000000121000000b2X7SX6RP5P3O2n2001000000121000000b2b?b3WBP3O1%LEPcPBPCPUPZPKPOP>PPPQPTP0PRPS12BG10GF'4P3PWPYP0PXPM12BA10AF'4P3PLPNP\P[P]P^P_AF4`;R;/<<,5_,E_PbP_1;<`,5_,E_PbP_P6P7P7P81<`<,5_1;<;,5_F`C9C9PaP2b;b<b=X04X14X541839/25g01aOR2[1095P2[129:189D,0:'4[[^04^14^54P3PCP?PBPcfBO5b:b@XEMX9XP5P3O2n2001000000121000000b2X8SX7RP5P3O2n2001000000121000000b2b3b@P1F_,aVWKP3O1n10210010200021110111103bAbCWJP3O1n10210010200021110111103bAbC,b9E^bDWGXM@AG:9=eWFW6WIWHo"). Qed.

Lemma mem_inv_unmaps : mem_inv segs m -> mem_inv segs m'.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) ["MemEffects"; "Unmaps"] "p'0h02Hxh11Hh24Hinvh31bi001bh42b0h51eh61oi011oh71xp;2p;1p;3p;4p;7p;6g01YQj26Tg002Sj11Tg003]j13Tg004;j14Tg004^R0j1CTg006hj22Tg007Jj30Tg00L8j2=Tg00e9j1<Tg005@j2;Tg00hdj48Tg00SEj19Tg00Tjj3:Tg00Mmj3BTg00gRj37Tg00=nj1ATg02Iaj7@Tg000Mj65Tg02@>j2?Tg01hoj2>Tp,4segsR1p,1mR2'6g00I4#1#1#1R3#1#1#1#3R4#4R5%33#4R3%C3R6p,2m'R7f1R8O1f0R9,2330P61=55R:P5P5p,1aR5#<p,1nR;,;4C8%9:3:f2R:5B2123:9069X66P9g00J7R4P6A75;:%A3R<P2P:O1n0100000020000R=P2P5P;P:p,2Hap,2Hnp,3HanF@E51238906=f3R=975;P4P4P4P6P9P<P2f5R;O1n0100000020000f4R5,23R:506f6R>,?1g00lE504R4]0P9123=R=906<P6P<P0P3p-0P9g01aOR3g00len10110100021000000X56g00K7P:P9E5P31>49b1W0P2P5O1=06=P>P;P5P9O3W0n0110000020000P8O1b4b0W0W3W71617eW2o"). Qed.

(* [comment removed for export] *)
End Unmaps.

End MemEffects.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_cells_wr_at : forall segs m A cs n,
  rw_cells segs m A cs -> (n <= Z.of_nat (cells_size cs))%Z -> wr_at segs m A n.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h06__sat3h14__x1h21ih34__x2h44__x3h52H2h67__arithh74__ffh86__sat2h98__varmaph:5__with;4cstrh<2Hah=1Ah>1Hh?2H0h@2H1hA2HihB2HnhC2_HhD2cshE1mhF1nhG4segsp;1p;4p;2p;3p;7p;8g0023j1FTg002Sj18Tg003]j1MTg004;j1ITg004^j1hTg00oaj4aTg0110j4NTg0142j4:Tg00W;j20Tg00V^j22Tg008dj1GTg00UJj2gTg00Ugj25Tg00VCR0j24Tg00e9j1=Tg01alj3;Tg00=nj1KTg007Jj37Tg01_8j1<Tg012@j1DTg01=\j1LTg013Rj1BTg00ZUj2\Tg00[=j3[Tg00[aj2ZTg00A\j2JTg00SEj1YTg00\Bj2@Tg00\`j1XTg00]>j1WTg00]ij2HTg00^Lj2?Tg00aEj2VTg00agj2UTg00bSj3TTg00c2j4fTg01?=j1STg01?\j2ATg01MDj3QTg01Mmj2eTg00Tjj3dTg01BKj4CTg0038j1bTg01Elj3PTg00_Zj3`Tg01Amj1_Tg00^oj4ETg00D5j4OTg00iDj7^Tg00`aj8]Tg00`=j7cTf0R1#D#Bp=1g00ihR2/01p=3g00IYR3f1R4g00nSP1CEp=9P4g00jFR5g00jeR6P6g00kER7P1g00keF^p=6f3R8P5P6P6P7f2R9P4P1G]p=>P9P5P6P6P7P4P1Fcp=Rg00Fn#Fg00I4R5#8R:#8R;#8R<#8#8#8R=#MR>#I%M<#IR<#hR?[g01PF#Ff4R@P8P9P4CaP0f5RAP@P8P9CNPAP@P8%19C:%18,09f7RBf6RCPAP8C:[P1PBPCPAP@CNf8PBPC%1AC:P0%3B%1C,2B%G:R@%G=R='gRD'0%31RE%1BRF,51'4f;RGf:RHf9RI/24#=3;%K<R<57?#<[^23'410CFPGPHPIPBC:[P1%3I%1I,2H/0D%1HRI,51,4Ef>RFf=RJf<RK/24#=3;=7?<#<[^23'4P012GI/0D%1GRI,51,4Ef?R012J4#=7;F=7?<#<[^2310HIP0PFPJPGC:[P1%1K,2J/0D%1FRK,51,4EfBRIfARHf@RL/24#=3;=7?<#<[^2310JK%3L12LF/0DRL1510,4ERFfDRKfCRJ12I4#=3;=7?<#<[^23R<'4%D0R0#LR?%B0#3R01\@=RI152@RM%3=152D[RN[RO%3@RPg00leRQA[@=4UW<R=%3D\Q^<PRPP4g00mA1Z2@'JPMeO1RMPNg00mgRQ#YRR%FQRS1@34%X3RT%W3RU1H321?35RV'9,6URW%K6R6PWC>1VU7R7P1P9g00J7RXg00JWRY'J1U19=7XYdAT324CfR2b7b9b:X13%34\E^13P1fERYPGO2b6b0b8b0b;PLP<P?P0PIPOP=PPPMPNg01V@R0#SR?#S,A31A3?1A305Q35Q3g01S='e=dQRRRPSP31@39P41@38RQCCPTPU1?3:R:%b5,?3R5'9,6UP6PUAP3V51H3@=`3>R>'9,6UP6AP3V:/9>,6UC>C>P7P2b7b9b:X13X33X4310491248/0D1298/0D[[^13^33^43P1%1KPJPYPAPBO5b6b0b8b0b;P8P4%DHRH#L%BH#3PIPOP=PPPMPNPRPSP3P3PQP9%_3RQCCP4PQCCPTPUP3PVg00o:RT1?3;R;CE,6U9RUWP6PU19;:,6UP6P3PVPTP:CE,6U9RUWC>C>P7P2b7b9b:X13X33X431519,4E1089%391598'4[[^13^33^43P1PYfF#1PCPAPBO5b6b0b8b0b;O2XAFX23COCOWBW>W@P4P1O2n2001000000121000000W5W?P4P1O2n2001000000121000000W5WCP4P1O2n2001000000121000000W5XF3WDX=3WEWGo"). Qed.

Lemma rw_cells_bytes_at : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h02H0h11Ah21Hh32_Hh43_H0h52csh61mh74segsp;1p;4g0023j1:Tg002Sj10Tg003]j17Tg004;j16Tg004^j1<Tg00oaj4;Tg0110j48Tg012@j14Tg013Rj13Tg0142j45Tg018<j11Tg019Oj42Tg016lj19Tg00Fn#:g00I4#0#0#0R0#0#0#0#7#6%70#6#<[g00IYg01PF#:f3R0f2R1f1R2f0R3C;g00VCR4f4R5P0P1P2C8P5P0P1%42#3C5f5R6P5P0%11C2P3f6R1P6P5P0C8P4%95f7R4P1P6%15C2f8R5P4P1%46#3C5f9R6P5P4%11C2[P3%91f:R1P6P5%14C2f;P1P6%45#3C5P2W4W2W3P2P3O2n2001000000120000000W0P2P3O2n2001000000120000000W0W5W1W6W7o"). Qed.

Lemma ro_cells_bytes_at : forall segs m A cs, ro_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01Ah11Hh22H0h32_Hh42csh51mh64segsp;1p;4g0023j16Tg002Sj10Tg003]j14Tg004;j13Tg004^j18Tg0248j47Tg016lj15Tg018<j11Tg019Oj42Tg00Fn#6g00I4#0#0#0R0#0#0#0#4#3%40#3#8[g00IYg01PF#6f3R0f2R1f1R2f0R3C7g00VC%52f4R4P0P1%12C2f5R5P4P0%11C2P3%50f7f6P5%14C2P3W1W3P2P3O2n2001000000120000000W2W4W0W5W6o"). Qed.

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
        remember (write_to_mem m (wa B) bs) as m' eqn:Heqm;
        clear Heqm; clear HB; try clear m; rename H' into H
    | _ => fail "sys_mem_write: no hypothesis rw_cells" segs m B "[CB _ _]"
    end
  end.

(* [comment removed for export] *)
Lemma apply_mem_zeros : forall m z, apply_writes (apply_zeros (apply_unmaps m []) [z]) [] = apply_zeros m [z].
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01mh11zp;1p;2p;3g002Sj10Tg003]j12Tg004;j11Tg004^j13Tg00L8j28Tg00SEj17Tg00Tjj36Tg00Nfj24Tg00A\j25Tg00I4#0#0#0R0#0#0#0#2#1R1%20#1#3[R01811R1f1f0%71561'4,50W1W0o"). Qed.
Lemma apply_mem_unmaps : forall m u, apply_writes (apply_zeros (apply_unmaps m [u]) []) [] = apply_unmaps m [u].
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01mh11up;1p;2p;3g002Sj10Tg003]j12Tg004;j11Tg004^j13Tg00L8j28Tg00SEj17Tg00Tjj36Tg00Mmj24Tg00A\j25Tg00I4#0#0#0R0#0#0#0#2#1R1%20#1#3[R01811R1f1f0%71561'4,50W1W0o"). Qed.

Ltac transport_zeros segs m a n Ha Hn Han :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_zeros_other segs m a n Ha Hn Han A2 bs2 H) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_zeros segs m a n Ha Hn Han A2 n2) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_zeros_other segs m a n Ha Hn Han A2 cs2 H) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_zeros_other segs m a n Ha Hn Han A2 cs2 H) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ => apply (stk_zeros segs m a n Ha Hn Han lo hi) in H
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_zeros segs m a n Ha Hn Han W m0 H) in H; [|cbn [inside]; slia]
            | fail 100 "zero-filled range not inside the declared footprint" ]
  | H : wmono segs ?m0 m |- _ => apply (wmono_zeros segs m a n Ha Hn Han m0) in H
  | H : mem_inv segs m |- _ =>
      let H' := fresh "MI" in
      assert (H' : mem_inv segs (apply_zeros m [(wa a, Z_to_bv 64 n)]))
        by (apply (mem_inv_zeros segs m a n Ha Hn Han H); first [assumption | intros; shelve]);
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
      first [ apply (bytes_at_unmaps_other segs m a n Ha Hn Han A2 bs2 H) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ =>
      first [ apply (wr_at_unmaps_other segs m a n Ha Hn Han A2 n2 H) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_unmaps_other segs m a n Ha Hn Han A2 cs2 H) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_unmaps_other segs m a n Ha Hn Han A2 cs2 H) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ =>
      first [ apply (stk_unmaps_other segs m a n Ha Hn Han lo hi H) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_unmaps m a n Ha Hn Han W m0 H) in H; [|cbn [inside]; slia]
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
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "p'0h02Hah14__p1h26__sat1h34__x1h41Hh57__arithh64__ffh76__sat0h88__varmaph95__with:1bi001bh;1li011lh<1ni021nh=1ri031rh>2r0p;1p;2p;3p;4p;6p;7p;8g002Sj18Tg003]j1OTg004;j1FTg008dj15Tg00UJj2UTg01;Xj24Tg00WWj21Tg00Ugj26Tg0038j19Tg01]Oj2DTg00W;j20Tg00XAj2BTg01^2R0j2YTg004^j1VTg006hj2;Tg00=nj1@Tg007Jj37Tg00A\j2<Tg01_8j1STg00ZUj2RTg00[=j3NTg00[aj2MTg00SEj1LTg0023j1JTg00\Bj2ITg00\`j1HTg00]>j1GTg00]ij2:Tg00_Zj3KTg01Bij3>Tg00^Lj2ETg00^oj4ATg01`kj6PTg01Obj6QTg00aEj2CTg00agj2TTg00bSj3\Tg00c2j4[Tg02OOj1ZTg00iDj7XTg00`aj8WTf0R1#8#8p=3%91#9p=2f1R2g00jFR3g00jeR4P4g00kER5P1g00keFXp==f3R6P3P4P4P5f2R7P2P1GWp=?g00I4R8#8R9#8#3#3R:#OR;#F%59R9%5:R<'UR=%3:#3#3#5R:'4R>11;1'6%98#2#2#2#2#2#5R?,4=R@11;2RA'D10@A1B@A'Y11;7,B@g00J7RBP011;6,0@g00IYR0#VRCPBPCP2f5,1;,4=,;0RD%@0REn0100000020000;7DP2f4RF,1;,0@RG1<CDW;P1O1%SG1R9<g00ihRG/69RD10G<16G=[RH[10G9RIg00leRJAN9<2UW010G=\J^0IP2g00mA1MG9'<PDeO1PHp-0RHg00mgRD#L%JD1I02%H0%G0RDPDP3P4P4P5P01:09=K0;R91:0?5>0g00nS1E08R8CA,=DEP%@4R?PDP01:0:9>09g00o:P8CA,=DP?PDP3P4P4P5P6EQC?C?1CD5P1P7g00JWRD,<B1T17=7BDdA\0G2C[b6b8b9X30W110@1g01aO[16>2P6[[^30^1HP1f9,1;R;,4=,;097CEP;PFf8O4b5b2b7b2W<P1O1n10210010300021010111102b:b>%Z214=A,;057CeW4W=o"). Qed.

(* [comment removed for export] *)
Lemma negw_errno : forall u, (2^64 - 4096 < u < 2^64)%Z -> bv_swrap 32 (0 - u) = (2^64 - u)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h06__sat1h16__sat3h22Hah34__x1h47__arithh54__ffh66__sat0h76__sat2h86__sat5h98__varmaph:5__with;6__sat4h<1zh=1Hh>2Huh?1up;1p;2p;3p;4p;8p;6p;7g002Sj1:Tg008dj17Tg00UJj2;Tg01;Xj20Tg00Ugj23Tg00VCj2HTg00ZUj2?Tg00[=j3=Tg0038j18Tg00[aj2KTg00A\j2GTg00SEj1dTg0023j1aTg00\Bj2XTg00\`j1WTg00]>j1UTg00]ij2DTg003]j1CTg00_Zj3BTg00^Lj2TTg01Bij39Tg01Elj3@Tg02P`j2STg02QCj3RTg00aEj2QTg00agj2PTg007Jj3<Tg00bSj3MTg00c2j4LTg00V^j21Tg02Qfj1NTg02RCj2OTg02R`j2ETg00=nj1cTg00^oj4FTg00`aj8bTg02S@j3`Tg000ij6JTg01Amj1\Tg01`kj6YTg02Scj4ZTg000Mj6[Tg02TDj2VTg00W;j2]Tg00iDj7^Tg00`=j7_Tf0R0#:#:p=6g00ihR1/]0p=2g00IYR2f1R3g01SiP0CFp=>P3g00jFR4g00jeR5P5g00kER6P0g00keF^p=4A<230p=5P2P3g00o:P0CFp=Af2R7P4P5P5P6P3P0F_p=Ig00I4R8#:R9#7R:%69#6R9#:R;#7R<';R=%6;#6#6#7R>'0/30130='HR?%79R@,?:RA131:RB%2@1;:@RC,31[RD[RE%2:RFg00leRGA=:@3UW2R@%2C\G^2FRH1?:<RI%2<131=[RJ\BRKA=:<3VGX2FR<%2=\G^2FRL%88#8#8#8RM#7RN,?:RO%2N1;:NRP,31[RQ\BRRA=:N3VGX2FRN%2P\G^2FRFP3g00mA1K1:'GPBeRBO1RGPQf4PBO1RSPJf7PBO1RBPDg00mgRT#dRU%aTRT1X23RV%W2RW%U2RX1D2:R:%C;5B2R;1T28R8592RY%CM9B2:RM5@2RZ%C9R99B2:R:,S2=R2:5@21D21R[=928=@2M'>'41QX6R\P0P7g00J7R]g00JWR^'G1P07=<]^dAM213CLR^b5b9b:X3210=0R]/1PR_%NCR`/OCRa'11010/1P'5^32P0f;RbO1b4b8b1b0b6b0b7b1b;b810=3Rc/1PRd/1a1013R3/1P'5P210=7/1PRe/1aRa1E0C/0Pf3,0=R='5X<2P21EeCRf100P/5=X<2R=P2PeP=PIPKP<PLPOPRPNPFPGPQPSPJPUPTPVPWA92ZM/>Y,4XP\P^b5b9b:X3210_P/5]^32P0f9O1b4b1b0b6b0b7b1PfPAPEP@PHPIPKP<PLPOPRPNPFPGPQPSPJPBPDPUPTPVPWPXP4P5P5P61D2>992;/A8,4X1A8;,4X5IX%c5P2P[g00nSPZCF,4X1AZ:,4X5IXGbP\P^b5b9b:X32%2d13dC'H\?^32P0f<PbO2b4b8b1b0b6b0b7b1b;b89`eCEJ1EaCPeP`PCPAPEP@PHPIPKP<PLPGPJPSPDPUPT%\2PWPXP4P5P5P61>:[,4XEYP\P^b5b9b:A<2C1g01aO[P0b4b1b0b6b0b7b1CZEJ1017/1PP0E[b=1V93/5ceW>X?2o"). Qed.

(* [comment removed for export] *)
Lemma swrap32_small : forall z, (-2^31 <= z < 2^31)%Z -> bv_swrap 32 z = z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h02Hah16__sat1h24__x1h37__arithh44__ffh56__sat0h66__sat3h78__varmaph85__with91zh:2Hzh;6__sat2p;1p;2p;3p;4p;8p;6p;7g002Sj14Tg008dj17Tg0038j16Tg00UJj2=Tg02Qfj1ZTg00W;j2@Tg00Ugj22Tg00VCj2<Tg00V^j2:Tg01;Xj2ATg007Jj35Tg00ZUj2?Tg00[=j3CTg00[aj2VTg00A\j2BTg00SEj1UTg0023j1TTg00\Bj2QTg00\`j1OTg00]>j1NTg00^Lj2LTg00]ij2;Tg003]j19Tg00_Zj38Tg01Elj3JTg01Bij3ITg00^oj43Tg00aEj2HTg00agj2KTg00bSj3GTg00c2j4FTg02R`j2MTg02P`j2ETg00=nj1PTg00`aj8DTg02S@j3RTg000ij6STg02TDj2YTg00iDj7XTg00`=j7WTg00ihR0f0R1'@p=0f1R2g00jFR3g00jeR4P4g00kER5P1g00keFXp=1f2R6P3P4P4P5P2P1FWp=>g00IYR7g00I4R8#4R9#7R:%68#6#6#6R;#7R<'=R=#Z/@1121='<R>P71:2=R?1A1==576X971?:<R@120:RA%0<120=[RB[RC%0:RDg00leREAC:<2UW0R<%0=\E^0DRFP2g00mA1V0:'BPAeRGO1RHPBg00mgRI#URJ%TIRI1Q72RK%O7RL%N7RMP71L78R81;7:RN%9;587R;5J7RO=I7;g01SiP8C3'11HM5RPP1P6g00J7RQg00JWRR'B1K16=5QRdAG702CFRRb4b7b8X271:1=/A==571^27P1f5O1b3b1b5b1%49#4#4#4R9#7R=,=:RQ,M?1?:=%0=120Q[R6\AAC:=2VEX0D%0Q\E^0DP@PCP<PFPHPBf4PGO1P6PJPIPKPLPMP3P4P4P5P71E7;g00nSR5P8C3,1MP7P8g00o:R8P;C3,1M5>M%P4P71;70P5POC3,1MP7POP8%99R9987NC3,1M5>MGDPPPRb4b7b8X27%0?12?Q'<\>^27P1f8f7O2b3b6b1b5b1b;b69R?QES1Y92=572eW:W9o"). Qed.

Lemma swrap32_high : forall u, (2^64 - 2^31 <= u < 2^64)%Z -> bv_swrap 32 u = (u - 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h06__sat1h16__sat3h22Hah36__sat5h44__x1h57__arithh64__ffh76__sat0h86__sat2h98__varmaph:5__with;6__sat4h<1zh=1Hh>2Huh?1up;1p;2p;3p;4p;8p;6p;7g002Sj14Tg008dj19Tg00UJj2@Tg0038j18Tg01;Xj21Tg00W;j2HTg00Ugj26Tg00VCj2DTg00ZUj2:Tg00[=j3BTg00[aj2KTg00A\j2GTg00SEj1`Tg0023j1]Tg00\Bj2VTg00\`j1UTg00]>j1TTg00^Lj2RTg00]ij2ETg003]j1?Tg00_Zj3=Tg01Bij3>Tg01Elj3ATg02QCj3QTg00aEj2PTg00agj2OTg007Jj3;Tg00bSj3NTg00c2j4MTg00V^j20Tg02RCj2LTg02R`j2CTg00^oj47Tg00=nj1JTg00`aj8STg02S@j3_Tg000ij6ITg01Amj1^Tg01`kj6\Tg02Scj4WTg000Mj6XTg02TDj2YTg00iDj7ZTg00`=j7[Tg00ihR0f0R1'Hp=2g00IYR2f1R3g01SiP1C7p=<P3g00jFR4g00jeR5P5g00kER6P1g00keFZp=3A;231p=5f2R7P4P5P5P6P3P1F[p=Fg00I4R8#4R9#9R:%49#4#4#4R9#4R;#9R<'@R=%88#8#8#8R>#9R?,@:R@'1/H1161='DRA%99RB,::RC160:RD%2B1@:BRE,60[RF[RG%2:RHg00leRIAB:B3UW2RB%2E\I^2HRJ1::<RK%2<160=[RL\DRMAB:<3VIX2HR<%2=\I^2HRN1::?RO%2?160@[RP\DRQAB:?3VIX2HR?%2@\I^2HRHP3g00mA1K0:'GPDeRDO1RIPPf4PDO1RRPLf7PDO1RDPFg00mgRS#`RT%]SRS1V23RU%U2RV%T2RW1R28R81E2:R:%?;5=2R;5>2RX%?>9=2:R>5A2RY%?9R99=2:R:=Q2:5A2AA28>'<'31PW6RZP1P7g00J7R[g00JWR\'G1O17=;[\dAN203CMR\b6b9b:X42111=R[/0@R]1LEER^'0101@'5^42P1f;R_O1b5b3b1b0b7b0b8b1b;b3113=R`/0@Ra/0^103@'5P2117=/0@Rb/0^R^1C1E/1@f3/1=R='5X<2P21CbERc111@/5=X<2R=P2PbP=PKPMP<PNPOPQP?PHPIPPPRPLPTPSPUPVA>2Y>/<X,3WPZP\b6b9b:X4211]@/5[^42P1f9O1b5b1b0b7b0b8b1PcPCPGPBPJPKPMP<PNPOPQP?PHPIPPPRPLPDPFPTPSPUPVPWP4P5P5P6P2A>2;>g00nSR>P8C7,3WP2P8g00o:R8P;C7,3W5FW%J5P21E20R;P>PYC7,3WP2PYP8P:C7,3W5FWGSPZP\b6b9b:X42%2a16aE'D\A^42P1f<P_O2b5b3b1b0b7b0b8b1b;b39_bEEI1C^EPbPEPEPCPGPBPJPKPMP<PNPOPQP?PHPIPPPRPLPDPFPTPS%^2PVPWP4P5P5P61<:;,3WE\PZP\b6b9b:A;2E0g01aO[P1b5b3b1b0b7b0b8b1b;b3CWEI107@P1EXb=1Y93/5`eW>X?2o"). Qed.

Lemma unsigned_errno_ret : forall e, (1 <= e <= 4095)%Z -> bv_unsigned (errno_ret e) = (2^64 - e)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h04__p1h14__x1h27__arithh34__ffh48__varmaph55__with61eh71zp;1p;2p;3p;4p;6p;7p;8g008dj13Tg00W;j20Tg0038j14Tg00VCj26Tg01;Xj25Tg002Sj11Tg00UJj2ETg007Jj3<Tg00A\j2=Tg003]j1ATg02Tkj1?Tg00WWj2>Tg00SEj1RTg0023j1QTg00\Bj2PTg00\`j1LTg00]>j1KTg00]ij27Tg00^Lj2GTg00^oj4;Tg01Obj6DTg00=nj1FTg00aEj2CTg00agj2HTg00bSj3BTg00c2j4ITg02Ucj3JTg000ij6@Tg00iDj7MTg00`=j7NTg00`aj8OTf0R0#4#4p=2f1R1g00jFR2g00jeR3P3g00kER4P0g00keFMp=:f2R5P2P3P3P4P1P0FNp=8f3R6P2P3P3P4P5P1P0GOp=9g00IYR7g00I4R8#3R9/00R:%48#2#2#2#2#2#3R;,00R<'6P7g02W1/51%18R=#3%1=#1#1#1#1R=#3'ER>/559<70X7715>1,=7%A=%?1'>p-0R=g00mgR>#RR?%Q>R>1P71R@%L7RA%K7RBP71779g00nSRC1G78R8C;,:BRDPBP2P3P3P4P6EDR658B%F3R3PDC91CB4R4P0P5g00J7RDg00JWR2'=1H05=<D2dg00ih=B71CIR2b3b4b5X17W016:11091[^17^0=P0105;P5P1O3b2P?P>P@PAPBP7P8PC177;C;,:BRC98B6P3PCC9P4P2b3b4b5X17X0=161<101;[^17^0=P01095P5P1O3b25J1E@UW6o"). Qed.

Lemma Z_to_bv_minus_mod : forall z, Z_to_bv 64 (z - 2^64) = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h06__sat1h11zh21Hh32Hah47__arithh54__ffh66__sat0h78__varmaph85__with94__x1h:2b1h;2b2h<1np;1p;3p;2p;4p;6p;7g004;j14Tg007Jj33Tg00WWj21Tg02Wjj3]Tg002Sj12Tg003]j1UTg008dj1=Tg00UJj2KTg01;Xj27Tg005@j29Tg02XNj28Tg00ZUj2CTg00Ugj2BTg00W;j2:Tg00[=j3XTg00[aj2WTg00A\j2?Tg00SEj1VTg0023j1TTg00\Bj2RTg00\`j1QTg00]>j1NTg00^Lj2MTg01@Ej1LTg00]ij26Tg00_Zj3JTg02QCj3HTg01Elj3GTg01Bij3ITg00^oj4<Tg00aEj2FTg00agj2ETg00bSj3DTg00c2j4OTg02RCj2PTg00V^j25Tg02R`j2>Tg01Amj1STg01`kj6\Tg02Scj4[Tg000Mj6ZTg02Y4j2ATg000ij6@Tg00iDj7YTg00IYR0f1R1f0R233p=0P1g00jFR3g00jeR4P4g00kER5P2g00keFYp=;g02YcR6%42R7%41R8g00VCf2R9#4?312f3R:/1911:1'0R;[11911192'0%4:?391[R<f4#4?3:9\;A]912P2n2001000000120000000W;W:W<P<^;8^:7^<6P2g00I4R6#2R7#2#2#2#2#2R8#UR<%=7R7%=8R8'KR;,71R=,9<R>19<1R?P018<=R@19<9,1<,02X10P018<1RA179;RB,8</02X101C78RCg00ihRD/B7RE1:D81BD;[RF[RG1:D7RHg00leRIAX781UW3R81:D;\I^3HRHP1g00mA1WD7'?PEeO1REPFg00mgRI#VRJ%TIRI1R01%Q0RK%N0RLP01M06RM%L6R6,601607=J0<R75H05G0g01SiRNAI0M7C<';1FL5RMP2P9g00J7ROg00JWRP'?1E29=3OPdAD0D1CORPb5b7b8X901P6;RO,52172;'0^90P2f5O1b4b0b6b0151O/0=P0159O1>2;1>:;'0X10P9P6P;PCPGP8PHPEPFPJPI%S0PKPLP3P4P4P5P0P7PN160DC<,;LE\PMPPb5b7b8A30;Dg01aO[P2b4b0b6b0C[PBP2EZb210@Ae11<?1A<1E@11<>1A<=E@O4b2X10o"). Qed.

Lemma errno_ret_fold : forall e, Z_to_bv 64 (- e) = errno_ret e.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01ep;1p;2g002Sj10Tg003]j14Tg004;j12Tg02Tkj11Tg00A\j23Tg00IYg00I4#0#0#0#0#0#0#4#2f0#1'3W0o"). Qed.

Lemma sextw_errno : forall e, (1 <= e <= 2^31)%Z ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (errno_ret e) + 0)) = errno_ret e.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h06__sat1h16__sat3h24__x1h31zh47__arithh54__ffh66__sat0h76__sat2h88__varmaph95__with:2Hah;1Hh<2Heh=1ep;1p;2p;3p;4p;6p;8p;7g008dj1ATg00W;j2<Tg002Sj15Tg0038j1;Tg00UJj2OTg00VCj2GTg02Qfj1>Tg02R`j28Tg003]j1ETg004;j1XTg00V^j27Tg02TDj2:Tg005@j23j1eTg007Jj30Tg00ZUj2NTg00Ugj2@Tg00[=j3JTg00[aj2aTg00A\j2=Tg00SEj1^Tg0023j1]Tg00\Bj2\Tg00\`j1[Tg00]>j1ZTg00]ij2?Tg00_Zj3ITg00^Lj2YTg01Bij3DTg01@Ej1WTg02QCj3VTg01Elj3UTg02P`j2TTg00aEj2RTg00agj2QTg00bSj3PTg00c2j4STg01;Xj22Tg02RCj2nTg00=nj1mTg00^oj4FTg02S@j3lTg000ij69Tg01Amj1hTg01`kj6gTg02Scj4fTg000Mj6KTg02ZAj8dTg02Z^j2bTg01I9j1cTg00WWj2LTg02\4j1`Tg02Tkj1_Tg00iDj7iTg00`=j7jTg00`aj8kTg00ihR0f0R1'<p=4g00IYR2f1R3g01SiP1CFp=CP3g00jFR4g00jeR5P5g00kER6P1g00keFip=1A0231p=6P2P3g00nSP1CFp=Bf2R7P4P5P5P6P3P1Fjp=Hf3R8P4P5P5P6P7P3P1Gkp=Mg00I4R9#AR:/<1%59R;#AR<%;9#;#;#;R=#AR>'OR?,<1'GR@P2%>3RA%5;#5#5#5R;#5RB#ARC,O<RD'8RE%EBRB#XRF%E;R;1710':,3BRG%>7RH,3B30X321N<CRI1@0<RJ%4C1@0D[RK[RL%4<RMg00leRNAJ<C3UW:RC%4D\N^:MRO1N<>RP%4>1@0?[RQ\JRRAJ<>3VNX:MR>%4?\N^:MRMP3g00mA1a0<'=PJeRJO1RNPQf4PJO1RJPKg00mgRS#^RT%]SRS1\23RU%[2RV%Z2RW1?2<R<=I2BRX1Y29RY5D2RZ%W9R9,?2=V2X5U21T2YR['C'11RW6R\P1P7g00J7R]g00JWR^'=1Q17=0]^dAP203CSR^b5b8b9X2212D1R]1n9DR_'7%>1R`'6^22P1f8RaO1b4b1b0b6b0b7b112D3Rb/7_/6AP212D7R7/7_R_12D8Rc181D'6X32P2187DRd16c1X32RcP2P7Pc1=27PdPIPLPCPOPPPRP>PMPNPQPJPKPTPSPUPVPW1?2:/BY,1W%E=9I2<R<,BY,1W5HWRY%m5R=1?20R:/BZ,1WP2PZg00o:PXCF,1WRd5HWCMP\P^b5b8b9X22%4b1@bDRc'G\@^22P1f9RePaO2Rab4b1b0b6b0b7b19l7DE918_DP7P9PDPIPLPCPOPPPRP>PMPNPQPJPKPTPS%h2PVPWP4P5P5P61CX:,1WEgP\P^b5b8b9A02D0g01aO[P1b4b1b0b6b0b7b1CfE9PHP1EKb;16bEP2P7%>8,3BR890FGX32P2P71:;1,3B=0F8X32P2127DRG13B1=0F8X32P2PF%eBR8P8PGPHPF\2/=8PIPLPCPOPPPRP>PMPNPQPJPKPTPSPUPVAD2ZX/C[,1WP\P^b5b8b9X2212]D/6`^22P1PeO1b4b1b0b6b0b7b1Gd1:;7PIPLPCPOPPPRP>PMPNPQPJPKPTPSPUPVPWPYP=AD2X</BZ,1W=HWdCMP\P^b5b8b9X2212D?/<b/Gc\@^22Pab4b1b0b6b0b7b1,b7E91770%c7E918HDP1EKb;13BA,LB%`AE9%_3R3,LB/70,:;,3B=0F3eW<X=2o"). Qed.

Lemma sextw_small : forall z, (0 <= z < 2^31)%Z ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 0)) = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h02Hah16__sat1h24__x1h31zh47__arithh54__ffh66__sat0h76__sat3h88__varmaph95__with:2Hzh;6__sat2p;1p;2p;3p;4p;6p;7p;8g002Sj12Tg008dj1=Tg0038j15Tg00UJj2FTg00Ugj21Tg00VCj2:Tg003]j1<Tg004;j1MTg00V^j2?Tg02TDj29Tg005@j23Tg007Jj37Tg00A\j2>Tg00ZUj2ETg00[=j3DTg00[aj2WTg00SEj1VTg0023j1UTg00\Bj2STg00\`j1RTg00]>j1QTg00]ij2BTg00^Lj2NTg00^oj46Tg00_Zj3@Tg00=nj1LTg02P`j2KTg00aEj2JTg00agj2ITg00bSj3OTg00c2j4HTg02Qfj1PTg00W;j2CTg02]Nj2GTg000ij6;Tg01I9j1TTg00WWj2\Tg00cdj2[Tg00iDj7ZTg00`=j7YTg00`aj8XTg00ihR0f0R1'Cp=0f1R2g00jFR3g00jeR4P4g00kER5P1g00keFZp=4f2R6P3P4P4P5P2P1FYp=8f3P3P4P4P5P6P2P1GXp=Ag00IYR3%01g00I4R7#2R8#=R9%57#5#5#5R:#=R;'FR<,11':R=P3P2%28#2#2#2R8#2R>#<R?#MR@%<8R81?10'9,3?13?6RA37X33P3P21981,3?=7@AX33P3P213?1=7@AX3313?2RA,>@19821E9;R81109R@%0;110<[RB[RC%09RDg00leREAD9;2UW0R;%0<\E^0DRFP2g00mA1W09'>P@eRGO1RHPBg00mgRI#VRJ%UIRI1S32RK%R3RL%Q3RMP31B30g00nSRN1N37R7C6,4MROP3P7g00o:RP1B39RQ%<:5@3R:C6,4MRR58MRS%L4R4P31K3:PNP7C6,4M=8MRCA1JM5R5P1P6g00J7RRg00JWRN'>1I16=7RNdAO302CHRNb5b8b9X23%P</C2112<':\=^23P1f5f4R<O2b4b1b6b1,G2E;1?20%T2E;1\?A%=>R>,E9%0>1F9>RA,10[R0\@AD9>2VEX0D%0A\E^0DP8PCP;PFPHPBP<PGO1P0PJPIPKPLPMPSP4P3P7PPA@3Q?C6,4M98MOCAP5PNb5b8b9X23%02112A':\=^23P1f8f7O2b4b7b1b6b1b;b7,[2E;W:W3o"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stk_lo_nonneg : forall segs m lo hi, stk segs m lo hi -> (0 <= lo)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStep ()) [] "h01ah11bh21Hh32H0h42_Hh52hih62loh71mh84segsp;1p;4p;2p;3g0023j1BTg002Sj12Tg003]j16Tg004;j14Tg004^j1ATg025Gj4?Tg00W;j20Tg008dj15Tg00UJj2=Tg00Ugj27Tg00VCR0j21Tg00e9j18Tg01alj39Tg00=nj1@Tg007Jj33Tg01_8j1<Tg01ifj3:Tg006hj2>Tg026Rj2;Tg00Fn#Bg00I4#2R1#2#2R2#2#2#2R3#6#4%62#4R2#AR4[g00IYR5f3R6f2R7f1R8f0R9C?P0g00ihR0/07%51%53'=R3,0810691797'1f6R1f5R:%88R;39%@2R<534#<f7%87R77:11>29R=534X12,;2'1[^05'11006P9f4R6,0010631019179:'1f9R:f8;9;=34<#<f:?::7=34=X12,;2'1[^05'1P8W4W2P8P9O2n2001000000120000000W3X55W6W7W8o"). Qed.

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
ltac2:(KReplay.run1_chk (kr_t_SysStep ()) [] "h03ms'h11Hh22H'h31Qh41Rh53atnh62msh74nodeh84segsh91tp;1p;2p;7p;3p;:p200R0g02^eR1p4p710p8p202R2g02`4R3p4p741110p8P2g02a@R4p4p741110p8g0023j14TP1j23TP3j70Tg02bPj31TP4l:2Tg00Fn#4f1R4g00GmR3p-0[[R1f3R5f0R6'3f5R7f7R8f6R9P7f4R:P5f2R;P6F0X03;16P8P9P7P:P5P;f8R;P8P9P7P:P5P6F0X03P4P6f9P;P8P9P7P:P6F0X03P6O1P6W2X03M:2W1X63X31W9X42W5W8X70o"). Qed.

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
