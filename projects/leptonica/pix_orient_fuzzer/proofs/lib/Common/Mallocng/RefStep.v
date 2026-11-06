(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From Ltac2 Require Ltac2.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocTree MallocOps MallocShape RefLrSc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RefStep () := "C47Corelib7Classes?RelationClasses9ReflexiveC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr06K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4prod01C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC59OSSVerify5KrLib6Common8PropExec8step_lbuC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC59OSSVerify5KrLib6Common8PropExec7step_ldC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib6Common8PropExec4v_lwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7step_lwC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03C59OSSVerify5KrLib6Common8PropExec8step_lwuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec8step_lhuC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib6Common7MmapSim:step_sb_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common9PureModel7md_pure00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC59OSSVerify5KrLib6Common8ShapeAlg7rz_stepC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng7RefStep9rz_step_pC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indc69OSSVerify5KrLib6Common8Mallocng7RefStep4minvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree5ms_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree5ms_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powc69OSSVerify5KrLib6Common8Mallocng7RefStep4wtopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib6Common8Mallocng:MallocTree5ms_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topI47Corelib4Init5Logic3and00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I69OSSVerify5KrLib6Common8Mallocng:MallocTree6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init5Logic3and01C4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEC59OSSVerify5KrLib6Common8AsanCeil=alloc_ceilingC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng7RefStep9minv_ceilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8AsanCeilAalloc_ceiling_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Common8VmLedger>md_pure_vmmapsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng7RefStep4wregC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib6Common8PropExec:getr_otherC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib6Common:AllocIface<callee_savedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng7RefStep6cs_numC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List7forallbC46Stdlib4Bool4BoolBnot_true_iff_falseC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC46Stdlib4Bool4Bool=negb_true_iffC46Stdlib4Bool4Bool=orb_false_iffC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_gtC47Corelib4Init9Datatypes3orbK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib6Common8Mallocng:MallocTree6acc_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<orb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib6Common7CatExec<wbytes_aboveC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC59OSSVerify5KrLib6Common7CatExec<wbytes_belowC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib6Common7StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib6Common7MmapSim6unfillC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7MmapSim5zfillC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8AllocSim4zmemC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng7RefStep9zfill_outC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC59OSSVerify5KrLib6Common8AllocSim?apply_zeros_oneC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng7RefStep8zfill_nnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib6Common5Hoare7at_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7add_modc69OSSVerify5KrLib6Common8Mallocng7RefStep8u_v_addiC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib6Common8PropExec8v_addi_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng7RefStep<v_addi_addi'C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=andb_true_iffc69OSSVerify5KrLib6Common8Mallocng7RefStepCcallee_saved_cs_numC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec8u5_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z9mod_smallc69OSSVerify5KrLib6Common8Mallocng7RefStep<getr_other_wC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_eq_decC35stdpp4base:decide_relC35stdpp4base6decideI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00c69OSSVerify5KrLib6Common8Mallocng7RefStep7wreg_csC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng7RefStep:noncs_numsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng7RefStepCcallee_saved_of_numC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitionsAbv_swrap_in_rangeC45stdpp9bitvector;definitions?bv_half_modulusC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z7add_0_rC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib6Common8PropExec7v_addiwC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib6Common8PropExec6v_andiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4c_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z;land_nonnegC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_ones".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section StepForms.
Context {fx : FPState}.

Lemma step_lbu_at : forall segs regs pc mem rom w rd rs (imm : bv 12) (a : word) (b : byte),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 1%nat = Some [b] ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) ["StepForms"] "h01bh12Hah22Hdh32Heh42Hfh52Hrh63Hrdh71ah83immh91mh:3memh;2pch<2rdh=4regsh>3romh?2rsh@4segshA1wp;1p;2p;3p;5p;4p;6p;?p-1p10000p4p710p9g000\R0p4p7210g001HR1p4p710p8g001fj1DTg002Fj11Tg002kj1?Tg003Pj13Tg003nj12TP0j2NTg004Qj18Tg0053j2LTg0065j25Tg006Wj30Tg0071j1HTg0081j2FTg008Qj1ETg009Bj5STg009nj1RTg00:Lj4QTg00:lj2MTg00;Oj3CTg00<2j3BTg00<_j2@Tg00=Xj2ATg00>@j26Tg00?;j1KTg00?Zj4>Tg00@Rj1JTg00A2j3=Tg00ARj1ITg00BZj2;Tg00CDj2<Tg00Cjj3:Tg00Dej54Tg00E^j27Tg00Ffj2GTP1j69Tg00G@j2OTg00H<l?PTg00I9#Dg00J8R1#1R0#?#3R2%10R0#1R3#1#1R4#1#3R5#2R6'NR7%33R3#2R8#8\6R9%34#2R4%22R:%?1#1#1#3R1#2%84f:R;f8R<'Lf5R=,5430g00J]R4f6R>#Hg00K=R?30g00K]R@g00LIRA'FRB#8f7RC#EP@PAg00LgP?P>P=f4RADS%R0R0CQ,5B30g00MSRBg00N1R@1M2Bd5C29B2C=04?f=RD/@C1A1>'6=06=%D8RE#8RFf?RGf<RHP>g00NM#KRIC>%J8RJ9=8=,5E30g00NlRK#IRLp,2fxRMP4P7AC2B@9B2;R2PG1;3>,<59:G;R@n0100000020000f>RB/60RNPDPHD4,7Kf0ROPMf@RPf;RQ1;3C,<53:R516G0R0PBPDD4,7KR350LX9LP4P?PMP4P7POPPP5n0100000020000P0PBPDD4,7K=0L3X04PMP@PNPDPHD4,7K,GLP2f2E9PMPGPBPDPHD4,OPPMPPPGPBPDPHPQP;f9R;P<P>P=PAf3P6PCfAPBPOPIC>A=8CJ,5E50FX06PO1@G;1A1<'6f1E9M?PE9W5W1W6W2W3W4X08X76W8X?:W<WAX>9W:X;6W=W@o"). Qed.

Lemma step_ld_at : forall segs regs pc mem rom w rd rs (imm : bv 12) (a : word) bs (v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) ["StepForms"] "h01bh12Hah22Hdh32Heh42Hfh52Hrh63Hrdh72Hvh81ah92bsh:3immh;1mh<3memh=2pch>2rdh?4regsh@3romhA2rshB4segshC1vhD1wp;1p;2p;3p;5p;4p;6p;Ag001fj1BTg002Fj11Tg002kj1=Tg003Pj13Tg003nj14Tg000\j2MTg004Qj18Tg0053j2KTg0065j27Tg006Wj30Tg0071j1FTg0081j2DTg008Qj1CTg009Bj5QTg009nj1PTg00:Lj4OTg00:lj2LTg00;Oj3ATg00<2j3@Tg00<_j2?Tg00=Xj2;Tg00>@j26Tg00?;j12Tg00?Zj4>Tg00P3j1JTg00BZj2ITg00ARj1HTg00Cjj3<Tg00Dej55Tg00E^j29Tg00Ffj2GTg001Hj6:Tg00G@j2ETg00Q0lANTg00I9#Bg00J8R0#1R1#=#3R2%11R1#1R3#1#1R4#1#3R5#4R6'MR7%33#4R3#8\6R8%34#4R4%42R9%=0#1#1#3R0#4%B3R3%84f;R:f9R;'Kf6R<,7430g00J]R4f7R=#Fg00K=R>30g00K]R?g00LIR@'DRA#8f8RB#CP?P@g00Qlg00RXP=P<f5R?DQ%P1R1CO,7A30g00MSRAg00N1RC1L2Ad5A29@2B=04>f>RD/?B1;0='6=06<%83REf@RFf=RGP=g00NM#2#2#2#2#2#2#2#2RHC>173<30%J=1I5<50@g00NlR@#HR5p,2fxRIP4P7f<RJAA2AC5@2R2fARCA<CJ=RAn010000002000016F1RKf?RLPDD5,9@f0RMPIfBRN?<GBRO16C1R1PFPLD5,9@RP505X;5P4P>PIP4P7PMPNPOn0100000020000P1PFPLD5,9@=05PX04PIPAPKPLPDD5,9@,G5P2f3E:PIPCPFPLPDD5,ENPIPNPCPFPLPDPGPJP:f:RJPBP=P<P?f4P6P;fCPFPMPHC>173;50EX06f11?C:1;0J'6f2E:PMMANE:W7W5W1W6W2W3W4XC6W9X86W:XA9W>WDX@8W<X=6W?WBo"). Qed.

Lemma step_lw_at : forall segs regs pc mem rom w rd rs (imm : bv 12) (a : word) bs (v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (v_lw v)) (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) ["StepForms"] "h01bh12Hah22Hdh32Heh42Hfh52Hrh63Hrdh72Hvh81ah92bsh:3immh;1mh<3memh=2pch>2rdh?4regsh@3romhA2rshB4segshC1vhD1wp;1p;2p;3p;5p;4p;6p;Ag001fj1CTg002Fj11Tg002kj1=Tg003Pj12Tg003nj14Tg000\j2MTg004Qj18Tg0053j2KTg0065j25Tg006Wj30Tg0071j1GTg0081j2ETg008Qj1DTg009Bj5RTg009nj1QTg00:Lj4PTg00:lj2LTg00;Oj3BTg00<2j3ATg00<_j2?Tg00=Xj2@Tg00>@j27Tg00?;j16Tg00?Zj4>Tg00P3j1JTg00BZj2ITg00ARj1HTg00S8j1<Tg00Cjj3;Tg00Dej53Tg00E^j29Tg00Ffj2FTg001Hj6:Tg00G@j2NTg00T1lAOTg00I9#Cg00J8R0#1R1#=#2R2%11R1#1R3#1#1R4#1#2R5#4R6'MR7%23#4R3#8\6R8%24#4R4%42R9%=0#1#1#2R0#4%C3R3%84f;R:f9R;'Kf6R<,5430g00J]R4f7R=#Gg00K=R>30g00K]R?g00LIR@'ERA#8f8RB#DP?P@g00Tmg00RXP=P<f5R?DR%Q1R1CP,5A30g00MSRAg00N1RC1L2Ad5B29A2B=04>f>RD/?B1@0='7=06<%83REf@RFf=RGP=g00NM#6#6#6#6RHC>153<30%J=1I5<50@g00NlR@#HR5p,2fxRIP4P7f<RJAB2AC5A2R2fARC%<=9;CJRAn010000002000017F1RKf?RLPDD3,9@f0RMPIfBRN%<B7;GRO17C1R1PFPLD3,9@RP505X;5P4P>PIP4P7PMPNPOn0100000020000P1PFPLD3,9@=05PX04PIPAPKPLPDD3,9@,F5P2f3E:PIPCPFPLPDD3,NNPIPNPCPFPLPDPGPJP:f:RJPBP=P<P?f4P6P;fCPFPMPHC>153;50EX06f11?C:1@0J'7f2E:PMMAOE:W7W5W1W6W2W3W4XC6W9X86W:XA9W>WDX@8W<X=6W?WBo"). Qed.

Lemma step_lwu_at : forall segs regs pc mem rom w rd rs (imm : bv 12) (a : word) bs (v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) ["StepForms"] "h01bh12Hah22Hdh32Heh42Hfh52Hrh63Hrdh72Hvh81ah92bsh:3immh;1mh<3memh=2pch>2rdh?4regsh@3romhA2rshB4segshC1vhD1wp;1p;2p;3p;5p;4p;6p;Ag001fj1BTg002Fj11Tg002kj1=Tg003Pj12Tg003nj13Tg000\j2MTg004Qj17Tg0053j2KTg0065j26Tg006Wj30Tg0071j1FTg0081j2DTg008Qj1CTg009Bj5QTg009nj1PTg00:Lj4OTg00:lj2LTg00;Oj3ATg00<2j3@Tg00<_j2?Tg00=Xj2;Tg00>@j28Tg00?;j15Tg00?Zj4>Tg00P3j1JTg00BZj2ITg00ARj1HTg00Cjj3<Tg00Dej54Tg00E^j29Tg00Ffj2GTg001Hj6:Tg00G@j2ETg00UYlANTg00I9#Bg00J8R0#1R1#=#2R2%11R1#1R3#1#1R4#1#2R5#3R6'MR7%23#3R3#7\6R8%24#3R4%32R9%=0#1#1#2R0#3%B3R3%74f;R:f9R;'Kf6R<,6430g00J]R4f7R=#Fg00K=R>30g00K]R?g00LIR@'DRA#7f8RB#CP?P@g00TmP>P=P<f5R?DQ%P1R1CO,6A30g00MSRAg00N1RC1L2Ad5A29@2B=04>f>RD/?B1;0='8=06<%73REf@RFf=RGP=g00NM#5#5#5#5RHC>163<30%J=1I5<50@g00NlR@#HR5p,2fxRIP4P7f<RJAA2AC5@2R2fARCA<CJ=RAn010000002000018F1RKf?RLPDD4,9@f0RMPIfBRN?<GBRO18C1R1PFPLD4,9@RP505X;5P4P>PIP4P7PMPNPOn0100000020000P1PFPLD4,9@=05PX04PIPAPKPLPDD4,9@,G5P2f3E:PIPCPFPLPDD4,ENPIPNPCPFPLPDPGPJP:f:RJPBP=P<P?f4P6P;fCPFPMPHC>163;50EX06f11?C:1;0J'8f2E:PMMANE:W7W5W1W6W2W3W4XC6W9X86W:XA9W>WDX@8W<X=6W?WBo"). Qed.

Lemma step_lhu_at : forall segs regs pc mem rom w rd rs (imm : bv 12) (a : word) bs (v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 2%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) ["StepForms"] "h01bh12Hah22Hdh32Heh42Hfh52Hrh63Hrdh72Hvh81ah92bsh:3immh;1mh<3memh=2pch>2rdh?4regsh@3romhA2rshB4segshC1vhD1wp;1p;2p;3p;5p;4p;6p;Ag001fj1BTg002Fj11Tg002kj1;Tg003Pj12Tg003nj13Tg000\j2MTg004Qj17Tg0053j2KTg0065j26Tg006Wj30Tg0071j1FTg0081j2DTg008Qj1CTg009Bj5QTg009nj1PTg00:Lj4OTg00:lj2LTg00;Oj3ATg00<2j3@Tg00<_j2?Tg00=Xj2:Tg00>@j25Tg00?;j1>Tg00?Zj4=Tg00P3j1JTg00BZj2ITg00ARj1HTg00Cjj3<Tg00Dej54Tg00E^j28Tg00Ffj2GTg001Hj69Tg00G@j2ETg00VVlANTg00I9#Bg00J8R0#1R1#;#2R2%11R1#1R3#1#1R4#1#2R5#3R6'MR7%23#3R3#7\6R8%24#3R4%32R9%;0#1#1#2R0#3%B3R3%74f;R:f9R;'Kf6R<,6430g00J]R4f7R=#Fg00K=R>30g00K]R?g00LIR@'DRA#7f8RB#CP?P@g00WSP>P=P<f5R?DQ%P1R1CO,6A30g00MSRAg00N1RC1L2Ad5A29@2B=04>f>RD/?B1:0='5=06<%73REf@RFf=RGP=g00NM#>#>RHC=163<30%J=1I5<50@g00NlR@#HR5p,2fxRIP4P7f<RJAA2AC5@2R2fARCA<CJ=RAn010000002000015F1RKf?RLPDD4,8@f0RMPIfBRN?<GBRO15C1R1PFPLD4,8@RP505X;5P4P>PIP4P7PMPNPOn0100000020000P1PFPLD4,8@=05PX04PIPAPKPLPDD4,8@,G5P2f3E9PIPCPFPLPDD4,ENPIPNPCPFPLPDPGPJP:f:RJPBP=P<P?f4P6P;fCPFPMPHC=163;50EX06f11?C:1:0J'5f2E9PMMANE9W7W5W1W6W2W3W4XC6W9X86W:XA9W>WDX@8W<X=6W?WBo"). Qed.

(* [comment removed for export] *)
Lemma step_sb_w : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 1 v)) rom).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) ["StepForms"] "h02Hah12Hdh22Heh32Hfh43Hokh52Hvh61ah73immh81mh93memh:2pch;4regsh<3romh=3rs1h>3rs2h?4segsh@1vhA1wp;1p;2p;3p;4p;5p;Dp;6g001fj1QTg002Fj10Tg002kj1<Tg003Pj12Tg003nj13Tg000\j2KTg004Qj17Tg0053j2DTg0065j2:Tg006Wj31Tg0071j1ATg0081j2?Tg008Qj1>Tg00X?j4PTg009nj1OTg00:Lj4NTg00<_j2;Tg00=Xj2JTg00>@j25Tg00?;j1ITg00Xkj4HTg00ARj1GTg00BZj2CTg00CDj2ETg00@Rj1FTg00A2j3BTg00Ykj36Tg00Dej54Tg00E^j28Tg00Zej29Tg00Ffj2=Tg00G@j2@Tg00[mlDLTg001Hj6MTg00I9#Qg00J8R0#0R1#<#2R2%01R1#0R3#0#0R4#0#2R5#3R6'K%23R3#3R7#7\6R8%24#3R4%32R2%<0#0#0#2R0#3%74f:R9f8R:'Df5R;,:431g00J]R4f6R<#Ag00K=31g00K]R=g00LIR>'?R?#7f7R@#>P=P>g00LgP<P;f4R>CP%O1R1CN,:?31f<R?/;@1J0;'5=16>f=R0/;@=16>f?R=P?P<g00NM#IRACHg00RX514g00NlR4#GRBp,2fxRCP=f>RD/51RE1C5<,E3R3%F75B7960@P?D4,84f0R5PCf@RF15=119A@96D:P0D4,8451BX8BPCP=PE19A<960@P?D4,84,=BPCP=PDP0P?D4,@FPCPFP=PDP0P?f;P9f9P:P@P<P3P;P>f3f2f11=73P5MDLEMW4W5W0W1W2W3X@6X66W7X>2W=WAX<8W9X:6W;W?o"). Qed.

(* [comment removed for export] *)
Lemma rz_step_p : forall segs ms md ms' T,
  md_pure md -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  realizes segs (mkCfg ms' md) T -> realizes segs (mkCfg ms md) T.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) ["StepForms"] "p'0h01Hh12H0h22Hhh32Hlh42Hmh52Hsh64Hsvch71Th82mdh92msh:3ms'h;4segsi009mp_haltedi017mp_lazyi026mp_matp;1p;3p;2p;:g001fj12Tg00\kR0j1CTg002Fj11Tg003Pj19Tg003nj1BTg004Qj1>Tg00]jj18Tg00_0j1;Tg006Wj30Tg00ARj1:Tg00G@j25Tg00E^j26Tg00_Rj23Tg00`Gj34Tg00aFj1ATg0081j2@Tg00b=j1=Tg00@Rj17Tg00c5j1?Tg00d5l:<Tg00I9#2g00NlR1g00e1g00egf2R2#CP0f3g00J8#1#1#1#1#1#1#9#BR0#>R3f5R4#8%;0R530%:1R6f7R7f6R8'5f4R9,6130f8R:1348;49f9R;13:7;44[[[f0R<%A8=0351@00R8#2%=7%7830%20%?:%7030f:R0#8=035f<R5f;R3'5161;506f=R61303;4;f>P6P5P3P0P4P9P2f1R9P<M:<W0W5W6W4W3W2P2P9P<O3n101000000130100101102W1W7X:1W8W9W;o"). Qed.

(* [comment removed for export] *)
Lemma rz_regupd_eq : forall segs (R : bvmap 5 word) (rd : reg) (v v' : word) pc M rom md T,
  v = v' ->
  realizes segs (mkCfg (mkst (regupd R rd v') pc M rom) md) T ->
  realizes segs (mkCfg (mkst (regupd R rd v) pc M rom) md) T.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) ["StepForms"] "h01vh11Hh22H0h31Mh41Rh51Th62mdh72pch82rdh93romh:4segsh;2v'p;1p;2p;3p;5p;6g001fj1<Tg002Fj10Tg002kj19Tg003Pj13Tg003nj16Tg000\j2;Tg004Qj1:Tg006Wj38Tg00Cjj31Tg00Dej54Tg00_Rj22Tg00`Gj35Tg001Hj67Tg00I9#<g00J8#0R0#9#3R1%00#0R0#0#0#0#3#6R2';%61%30#6#:\2R0g00e1g00egf6R1f5R3582P2P1f;R4p,2fxR5f:R6f9R7f7R831P1P3f4R9D4f3R:'2f2R;35f<P5f1R<9146P8P1P3D4/29;5:[X02P5f8=171P3P9P:D4/2;=56<f0R<W1P8P<E7W2W5W6X90W3X72X;2X02W8W4W:o"). Qed.

(* [comment removed for export] *)
Lemma rz_step_reg : forall segs (R : bvmap 5 word) pc M rom md T (rd : reg) (e v : word) (pc2 pc' : word),
  md_pure md ->
  RiscvSemantics.step segs (mkst R pc M rom) =
    MachineOk (mkst (if bv_eqb rd 0 then R else regupd R rd e) pc2 M rom) ->
  bv_eqb rd 0 = false -> e = v -> pc2 = pc' ->
  realizes segs (mkCfg (mkst (regupd R rd v) pc' M rom) md) T ->
  realizes segs (mkCfg (mkst R pc M rom) md) T.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) ["StepForms"] "h02H0h13pc'h21vh31Hh42Hph53Hrdh62Hsh71Mh81Rh91Th:1bh;1eh<2mdh=2pch>3pc2h?2rdh@3romhA4segsp;1p;2p;5p;3p;6p;9g001fj1GTg002Fj11Tg002kj1@Tg003Pj17Tg003nj18Tg000\j2ETg004Qj1:Tg00\kj1?Tg00ARj1>Tg00Dej50Tg00G@j2=Tg00:lj2<Tg00;Oj39Tg00<2j35Tg00Cjj34Tg00E^j2FTg006Wj36Tg00_Rj23Tg00`Gj32Tg00_0j1DTg00Ffj2CTg001Hj6ATg00f`l9BTg00gfj6;Tg00I9#Gg00J8#1R0#@#7R1%10#1R0#1#1#1#7#8R2'ER3%70#8#:\2R0g00e1g00eg%81f6R4#?g00NlR5#>f<R6p,2fxR7f;R8f:R9f9R:f8R;D0'=P7g00J]R<P3f5R=g00MSR>g00N1R?1<1>d591R@551P8f4RA948=n0100000020000f2P:P;D0,F536A514@g00K=R556<A624=RBP2f7RCfARDP7f@REf1749P4f>RFf=RGD0/36;28fBRHP7PDPEf?RIPFD0/3G;26RJ[\BX22A62=AP2P4P7A4E9:RBf0RKPFPGD0/36=2D8PJ[X12P7A4I:;P4PGP6D0/38=2E9PDP7PEPIPFPGD0P6P7P<P3A519@PEPBn0100000020000PCPFPGD0P8P=%:2%D2'CPAP<P5P7P<P3PKPDA4D89n0100000020000P;PIPFD0/3G=2H6X:<PKA91>?9519f3EAM9BW3P=PKE;W0P4PKE;W0W5W6W4X12X>2X22X;2W?W9W<X@0W7X=2W8WAo"). Qed.

(* [comment removed for export] *)
Lemma rz_step_pc : forall segs (R : bvmap 5 word) pc M rom md T (pc2 pc' : word),
  md_pure md ->
  RiscvSemantics.step segs (mkst R pc M rom) = MachineOk (mkst R pc2 M rom) ->
  pc2 = pc' ->
  realizes segs (mkCfg (mkst R pc' M rom) md) T ->
  realizes segs (mkCfg (mkst R pc M rom) md) T.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) ["StepForms"] "h03pc'h11Hh22H0h32Hph42Hsh51Mh61Rh71Th82mdh92pch:3pc2h;3romh<4segsp;1p;2p;5p;3p;9p;6g001fj1BTg002Fj11Tg002kj1<Tg003Pj12Tg003nj17Tg000\j2@Tg004Qj16Tg00\kj1;Tg00ARj1:Tg00Dej50Tg00G@j28Tg00E^j29Tg006Wj35Tg00_Rj24Tg00`Gj33Tg00_0j1ATg00Ffj2?Tg00f`l9=Tg00gfj6>Tg00I9#Bg00J8#1R0#<#2%10#1R0#1#1#1#2#7R1'@%20#7#6\1R0g00e1g00egf3R2#;g00NlR3#:f9R4p,2fxR5f8R6f7R7f6R8f5R9D0'8P5P6f2R:P8P9D0,9335A512:P1f4R3f<R;P5f;R<f0R=P4P6D0/47;38f=P5P;P<f:R>P4D0/46;37[X01P5P>P3P6P7D0/48=3<9P;P5P<P>P4P6D0P7P5P<P9P4P6D0P8P2%61%A1'?P:P=M9=W1P2P=E>W2W4W3X01X:1W7W8X;0W5X91W6W<o"). Qed.

(* [comment removed for export] *)
Lemma rz_at_pc : forall segs (R : bvmap 5 word) (pc' : word) M rom md T (pc : word),
  realizes segs (mkCfg (mkst R pc' M rom) md) T -> pc' = pc ->
  realizes segs (mkCfg (mkst R pc M rom) md) T.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) ["StepForms"] "h02pch11Hh22H0h31Mh41Rh51Th62mdh73pc'h83romh94segsp;1p;2p;5p;3p;6g001fj1;Tg002Fj10Tg002kj17Tg003Pj11Tg003nj15Tg000\j2:Tg004Qj19Tg00Dej53Tg00_Rj22Tg00`Gj34Tg006Wj36Tg00gfj68Tg00I9#;g00J8#0R0#7#1%00#0R0#0#0#0#1#5R1':%10#5#9\1R0g00e1g00egf7R2p,2fxR3f6R4f5R5f4R6f3D3f2R7'2f1R834A6148P1P2f:P3f9f0R3P2P4D3/25;46X01P8P7P3E8W2W1X01W5W6X80W3X71W4W9o"). Qed.

(* [comment removed for export] *)
Lemma rz_step_mem : forall segs (R : bvmap 5 word) pc M M' rom md T (pc2 pc' : word),
  md_pure md ->
  RiscvSemantics.step segs (mkst R pc M rom) = MachineOk (mkst R pc2 M' rom) ->
  pc2 = pc' ->
  realizes segs (mkCfg (mkst R pc' M' rom) md) T ->
  realizes segs (mkCfg (mkst R pc M rom) md) T.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) ["StepForms"] "h03pc'h11Hh22H0h32Hph42Hsh51Mh62M'h71Rh81Th92mdh:2pch;3pc2h<3romh=4segsp;1p;2p;5p;3p;9p;6g001fj1BTg002Fj11Tg002kj1<Tg003Pj12Tg003nj17Tg000\j2@Tg004Qj16Tg00\kj1;Tg00ARj1:Tg00Dej50Tg00G@j28Tg00E^j29Tg006Wj35Tg00_Rj24Tg00`Gj33Tg00_0j1ATg00Ffj2?Tg00f`l9=Tg00gfj6>Tg00I9#Bg00J8#1R0#<#2%10#1R0#1#1#1#2#7R1'@%20#7#6\1R0g00e1g00egf3R2#;g00NlR3#:f:R4p,2fxR5f9R6f8R7f7R8f5R9D0'8P5P6f2R:f6R;P9D0,9335A512:P1f4R3f=R<P5f<R=f0R>P6P7D0/48;3;f>P5P<P=f;R?P6D0/47;38[X01P5P?P3P7P8D0/4;=3=9P<P5P=P?P4P7D0P8P5P=P9P6P7D0P;P2%61%A1'?P:P>M9=W1P2P>E>W2W4W3X01X;1W8W9X<0X60W5X:1W7W=o"). Qed.

End StepForms.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wtop (s : mstate) : Prop :=
  alloc_ceiling <= alloc_top (ms_vm s) /\ alloc_top (ms_vm s) <= TASK_SIZE /\ alloc_top (ms_vm s) <= ms_lo s.

Definition minv (s0 : mstate) (s : mstate) : Prop :=
  ms_lo s = ms_lo s0 /\ ms_hi s = ms_hi s0 /\ alloc_top (ms_vm s) = alloc_top (ms_vm s0) /\
  0 <= ms_lo s0 /\ ms_lo s0 <= ms_hi s0 /\ ms_hi s0 <= 2^64 /\ wtop s0.

Lemma minv_lo64 : forall s0 s, minv s0 s -> ms_lo s <= 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01Hh12Hah24__x1h34__x2h41Ah51Bh61Ch71Dh81Eh91Fh:1Th;7__arithh<4__ffh=6__sat1h>6__sat2h?8__varmaph@5__withA1shB2s0hC1zp;2p;1p;3p;4p;6p;7p;8g00hBj2aTg00iCj11Tg00jHj12Tg00kMj20Tg002Fj18Tg009nj1ATg00kij2MTg00lFj1>Tg00mGj2^Tg00moj2ETg00nKj3XTg00?;j1CTg00noj2=Tg00oXj3BTg010Aj2VTg00@Rj1UTg00A2j3RTg001fj1QTg010mj2PTg011Kj1OTg011ij4@Tg012Gj1NTg012ej1LTg013Pj2?Tg0143j2KTg003Pj1JTg014Vj3ITg00_0j1HTg0159j2GTg00Ffj2STg015[j2TTg006Wj3FTg016Gj3`Tg016fj4_Tg001Hj6]Tg017Xj1\Tg018]j1ZTg019UR0j2:Tg01:0j4YTg01:[j7[Tg01;?j8WTg00LIR1f1R2f0R33Fp=3%\3#Zp=5g00MSR4/03p=4f2R5/02%>3':p=61:23,:5p=71052/:3p=9P1P2g01;cP3CYp=;P2g01<JR6g01<iR7P7g01=IR8P3g01=iF[p=<f3R9P6P7P7P8P5P2P3GWp=Dg01>IR61a23P0%12%15R:'3%22%25R;'3%52%55'3%4:10:;g00J8R<#8R=#AR>%8=R=#8#8#8#8R?#AR@'MRA=6;5373710:AP3%19f4R9#1'3%29f5R:#2R;'3%59%5:RB'3%1:RC#410C;A6;A:3737P0f6R:#2RC,3;%5:,3B%1:RB#4A6CA:99BC3710BAP3f7#2f8RB#2'3%5Bf9RC#5R:'3%1CR;#4%2CRDA6DAC59;37P0f:R;#5,3:%1;R:#4%2;RD,0:A6DA;3710:AP3f;#5f<#5'3f=R:#1RD#4%2:R;,0DA6;A:37P0f>R;#1R:#4%2;RDA6DA;59:10:AP3f@#1#4fAR:#1%2:RDA6DA:39P0fBRD#1R:%2DR;'0A6;AD10:AP3fDR:#1%2:'0fER:#2?6A:P0fFR0#2/0A%>0%10/0AP3fH#2/0AfIR0#>P1fJ#1103AXC11^>@1E4>%4@1E4A[[%4>R;g01?QRDAX>@2UW1%4A\D^1;g01?mR;g00NMRD#CR@#C,=11=1@1=1D5B15B1g01@Y'V%U;3R%Q;P1P11P15P5%O1R;C@P2P;C@%N1%L1R;1?1=R=1K1>%J?5I1R?';,<;%H7R7P;1?1<R</;=,<;P71;<?,<;CDCD1G;8P3P5g00J]R;g00RXR8'S1T35=F;8dA`142C_b<b?b@X21X31102A1025105A[[^21^31P3fMR1#2%11P9PBO4b;b=b>%10P:E]W9W8P2P3O2n2001000000121000000W0W7P2P3O2n2001000000121000000W0W6P2P3O2n2001000000121000000W0W:P2P3O2n2001000000121000000W0W5P2P3O2n2001000000121000000W0W4P2P3O2n2001000000121000000W0XA6WBo"). Qed.
Lemma minv_lo : forall s0 s, minv s0 s -> ms_lo s = ms_lo s0.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01Hh11Ah21Bh31Ch41sh52s0p;2p;1p;3g00hBj2>Tg00iCj12Tg00jHj13Tg017Xj15Tg018]j14Tg002Fj16Tg009nj1;Tg00kij2<Tg00lFj17Tg00kMj29Tg006Wj3=Tg019UR0j2:Tg00LIf1R1f0R23=p=0f2R3/91/:2p=11:12,:3p=8g01>IR41>12P0%21%23R5'0%31%33R6'0%51#4%53#4'0g00MSR7g00J8#6R8#;%68#6#6#6#6#;'<R8%73516915671538f3#2R6,05P2f4R5#2,06%35f5R6#3R3'0%55#4%56#4R5'0%26R9%769138919351738P0f6R0#3R9,03%50#4,05%20R5,97%709198915938f7R9#2,05P2%39f8R9#3'0%59#4f9R9#5#4'0%29R5,97%39R7%79917851538P6W3W2P1P2O2n2001000000120000000W0W1P1P2O2n2001000000120000000W0X44W5o"). Qed.
Lemma minv_hi : forall s0 s, minv s0 s -> ms_hi s = ms_hi s0.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01Hh11Ah21Bh31Ch41sh52s0p;2p;1p;3g00hBj2>Tg00iCj13Tg00jHj12Tg017Xj15Tg018]j14Tg002Fj16Tg009nj1;Tg00kij2<Tg00lFj17Tg00kMj29Tg006Wj3=Tg019UR0j2:Tg00LIf1R1f0R23=p=0f2R3/91/:2p=11:12,:3p=8g01>IR41>12P0%31%33R5'0%21%23R6'0%51#4%53#4'0g00MSR7g00J8#6R8#;%68#6#6#6#6#;'<R8%73516915671538f3R5#2,06P2%35f4R5#3'0%25f5R6#2R3'0%55#4%56#4R5'0%36R9%769138919351738P0f6R0#2R9,03%50#4,05%30R5,97%709198915938f7#2R5,09P2f8R9#2,05%59#4f9R9#5#4'0%39R5,97%29R7%79917851538P1W3W2P1P2O2n2001000000120000000W0W1P1P2O2n2001000000120000000W0X44W5o"). Qed.
Lemma minv_top : forall s0 s, minv s0 s -> alloc_top (ms_vm s) = alloc_top (ms_vm s0).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01Hh11Ah21Bh31Ch41Th51sh62s0p;2p;1p;3g00hBj2@Tg00iCj13Tg00jHj12Tg00kMj28Tg002Fj17Tg009nj1;Tg00kij2<Tg00lFj16Tg006Wj3?Tg017Xj1>Tg018]j1=Tg019UR0j2:Tg00LIf1R1f0R23?p=0%>2#=p=1g00MS/82p=9f2R3/81/:2p=51:12,:3p=4g01>IR41@12P0%31%33R5'0%21%23R6'0%11%13R7'0%951856g00J8#7R5#;%75#7#7#7#7#;'<R5%635563434f3R6#1,07P2%36f4R6#3'0%26f5R7#2R3'0%16%17R6'0%37R8#91883%6795353434P0f6R7#2R8,03%17R3,06%37R6#9%679585956834f7R6#1,03P2%26f8R6#2'0%16f9R6#1R3'0%36R8#9%26R7%66957555834P0f:R0#1R8,03%30R3#9%20R7,83%60957534f;#1R7,08P2f<#1,07f=R7#3R8#9%27R0,88%67950534P1W3W4P1P2O2n2001000000120000000W0W2P1P2O2n2001000000120000000W0W1P1P2O2n2001000000121000000W0X54W6o"). Qed.
(* [comment removed for export] *)
Lemma minv_ceil : forall s0 s, minv s0 s -> wtop s.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01Hh11zh21Ah31Bh41Ch51Dh61Eh72F1h82F2h92F3h:1Th;1sh<2s0p;2p;1p;4p;6p;3g00hBj2CTg00iCj11Tg00jHj13Tg00kMj20Tg002Fj1:Tg009nj1<Tg00kij2?Tg00lFj15Tg019UR0j29Tg01AEj4>Tg001Hj6=Tg006Wj3BTg017Xj1ATg018]j1@Tg00LIR1f1R2f0R33Bp=6%A3#@p=2g00MS/03p=8f2R4/02/93p=41923,94p=7g01A`,03p=;g01>IR51C23P0%12%14R6'6%32%34R7'6%22%24'6%861067g00J8#:R6#<%:6#:#:#:#:#<'?R6%54R45473737P4P3f3#1f4R4#1'6%34f5R7#3R8'6%24%27R4'6%17R9#81098%5794863737P0f6R9#3R:,68%29,64%19R4#8%59R994:6944:37P9P3f7#3f8R9#3'6%29f9R9#2R4'6%19R:#8%39R8%59948654:37P0f:R:#2,64%1:R4#8%3:R8,04%5:R:948637P:P3f;#2f<#2'6f=R:#1R8#8%3:R4,08%5:944637P0f>R4#1R:#8%34R8%54R4948654:P4P3f@#1#8fAR4#1%34R:%5494:634P0fBR:#1%3:R4'0%5:R:9446P:P3fDR:#1%3:'0fER:#3%5:746P0fFR4#3/06%54R4P4P3fH#3/06fI#5P0g01BXR6fJR4#2R8'0%;8%14,08'9%54P3fL#2,06fMR4#2R8#;%14,08'9P0fNR0#2R8#;%10,08%50P3fP#2#;fQR0#2R8%10R9'0P1fRR;#1R<%2;R;,06R=%;;R>10;337X11P1P;%;3fS#1,03'99463X11P=10;<R;,9>P7P>P;P2P3C>C>P8P:E=P9P4E=%50eW9W8P2P3O2n2001000000120000000W0W7P2P3O2n2001000000120000000W0W6P2P3O2n2001000000120000000W0W5P2P3O2n2001000000121000000W0W4P2P3O2n2001000000121000000W0W:P2P3O2n2001000000121000000W0W3P2P3O2n2001000000121000000W0W2P2P3O2n2001000000121000000W0X;5W<o"). Qed.
Lemma minv_ceil_num : forall s0 s, minv s0 s ->
  140735332483072 <= alloc_top (ms_vm s) /\ alloc_top (ms_vm s) <= 140737488355328 /\ alloc_top (ms_vm s) <= ms_lo s.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01Hh12HIh21sh32s0h41zp;2p;3p;1p;6g00hBj2@Tg01CZj3?Tg00lFj1<Tg017Xj16Tg018]j1;Tg00kMj23Tg002Fj10Tg009nj17Tg00iCj18Tg019Uj25Tg00gfj6=Tg002kj12Tf0R0#0#0p=:%00#0#0#0p=9%00#0#0#0#0#0#0#0p=1%20#2p=>%20#2#2#2p=4g01>IR1f1R2/@0f2R3??20%<2g00LIR2g01BXf3R4#6#;R5,30g00J8R6#0#:#9#1#1#1#1#1#7R7,35%84,35'5'5X42P0%>6#4#4#4#0#4#4#0#:#9#1#1#7R6g01D`E=%63#;R2,361327%83,32'5'5P0b0b0W1X21W3o"). Qed.
Lemma wtop_task : forall s, wtop s -> alloc_top (ms_vm s) <= TASK_SIZE.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01Hh11Ah21Bh31Ch41sp;1p;2g00lFj17Tg00kMj21Tg00iCj13Tg019UR0j24Tg017Xj16Tg018]j15Tf0R1#6#5p=0g01A`,11p=2g01>I%71P0g01BXR2f1R3#0R4'1%24%33,14'4f2#0#2P1f3#0,12f4R2#0R4#2%32,14'4P0f5R0#0R4#2%30,14f6#0#2P1f7#0#2f8R4#0%34'1P3W3W2P3P1O2n2001000000120000000W0W1P3P1O2n2001000000120000000W0W4o"). Qed.
Lemma minv_same : forall s0 s s', minv s0 s -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
  alloc_top (ms_vm s') = alloc_top (ms_vm s) -> minv s0 s'.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01Hh17__arithh26__sat4h36__sat5h44__x1h51zh64__ffh78__varmaph85__with92Hah:4__x2h;1Ah<1Bh=1Ch>1Dh?1Eh@2F1hA2F2hB2F3hC2H1hD2H2hE2H3hF1ThG1shH2s'hI2s0p;2p;1p;3p;4p;7p;8p;6g00hBj29Tg00iCj11Tg00jHj12Tg00kMj20Tg002Fj1>Tg009nj1ITg00kij2UTg00lFj1GTg019UR0j26Tg00Ffj2BTg00mGj2[Tg00moj2LTg00nKj3ZTg00@Rj1YTg001fj1XTg010mj2JTg012Gj1WTg012ej1VTg0143j2HTg013Pj2KTg00_0j1RTg0159j2QTg015[j2PTg006Wj3ATg016Gj3OTg016fj4STg011Kj1TTg011ij4bTg003Pj1aTg014Vj3`Tg01AEj4=Tg017Xj1NTg018]j1MTg01:0j4_Tg01:[j7^Tg01;?j8]Tg001Hj6\Tg00LIR1f1R2f0R33Ap=4%N3#Mp=3g00MSR4/03p=5f2R5/02%G3'6p=81623,65p=7AA152/63p=;%239A12p=<%N2#M=A13p=:1052/63p=Cg01A`R6,03p=?P1P2g01;cP3C_p=FP2g01<JR7g01<iR8P8g01=IR9P3g01=iF^p=Ef3R:P7P8P8P9P5P2P3G]p=DP1f4R7P:P5P2P3E\p=@g01>IR;1952P0%15%1:R<'4R=%25%2:R>%35%3:%5<10<>g00J8R<#>R?#IR@%>?#>#>#>#>RA#IRB'URC=8>:373;3;1<>7f5R>#3R:,:7f7RD/9>[[\=P3%17%1>'4%2>f6R>#2R7%3>R=%1>RE#510E7A87C>375;:3;P0%2DR:,47%3D%1DR7#5107:A8:CD375;=14E7f8R7#2RE,4:f9R:#3R=,:7f;R7/9:[[[P31<E:f:R:#3RE%1:RF#5%2:RG,0FA8GC:375;=P0%37,4E%17RE#5%27R=,0EA8=C73714FEf<RE,<=f=R=#3,:EREf?RF/9=[[[P3f>R=#1RG#5%2=R:,0GA8:C=37P0%1FR:#5%2FR=A8=CF5C:14G:f@R:,<=fAR=#3,::fCR:/9=[[[P3%1=#5fBR=#1RG%2=RHA8HC=3CP0%1:RH%2:R='0A8=C:14GHfDRH,<=fER=#3,:HfGRH/9=[[[P3%1=%2='0fFR=#2?8C=P0%2HRG/0C%GH%1=%1H'4fHR=,<GfIRG#3,:=fKRI/9G[[[P3%2G/0CfJRG#GP0g01BXRJ%3IRK'0%?K%1IRL,0K'6%1G/4L%2IfLRI'<fMRL#3RG,:IfORK/9L[[[P310JGfNRG#3RL#?%1GRG,0L'6P0%3KR0#?%1KRL,0014GL%2KfPRK'<fQRL#3RG,:KfSR0/9L[[[P3%?GfRRG#3%1GRM'0%1L/4M%2G/<0fTRG#3RM,:0fUR0#1RLfWRN#1RO,43RP%20RQ%2NRR'4%30R0%3NRN%5O10OR%?N10NO'69CJN9CRC37RS3;RT37X51PQfVRU#1RV/4ORW143RRX;7TX51P0%2URT/4RRYA;3NSRZ57WX51PV%3URW?;NSRS97PYX51PT14OORO?7XSX51PW14RR=7OZX5114VV14TTRO14WWRZ%5VRR10VTRS10TCRX10JWRY%?WRP10WVRN'6R['6R\'6R]'6R^'6R_'6R`'61B1VPOP`1B1TPZP_1B1WPRP^1[@BR^1L4@%5B1L4C[[RR%5@RWg01?QR_AZ@B2UW9RB%5C\_^9WRWg01?mR_#YRZ%X_R_1J12RT%W1R`%V1RO1H141K1<R<'F,EORV%R8R8PVCD1QO9R9P3P5g00J]RVg00RXRa'B1P35=AVadAO142CSR4b6b7b8X41%53%52[^41P3fYRa#1RVPHO2b1b2b3PSP]P^PRPBPWPZP_P11J15P2%T1CbP`PO1K1?,F<,EOR?P8P?CDP9P4b6b7b8X41X:1R?10321025[^41^:1R]P3%2aRSPVP:O3b1b2b3PXP\P^PRPBPWPZP_PTP`PO1H1@%aA5`1,F<,EOROP8POCDP9P4b6b7b8X41103C102C[^41P3PSPFO2b1b2b3PYP[P^PRPBPWP?P]P3%3aRaPJP7O3b1b2b3PPPNP^PRPBPWP?P]P3P6PaPDO3b1b2b3P^PRPBPWP?P]P3PVPaP>O3b1b2b3C=C=C=C=C=C=C=C=P0P=D@PQPID@PLPKD@PMP3D@%2GP2D@%1GP5D@19UGeWEWDWCWBWAP2P3O2n2001000000121000000W0W@P2P3O2n2001000000121000000W0W?P2P3O2n2001000000121000000W0W>P2P3O2n2001000000121000000W0W=P2P3O2n2001000000121000000W0XFEP2P3O2n2001000000121000000W0W<P2P3O2n2001000000121000000W0W;P2P3O2n2001000000121000000W0XH;XG;WIo"). Qed.
Lemma minv_init : forall s0 (sp : word) D,
  0 <= ms_lo s0 -> ms_lo s0 <= bv_unsigned sp - D -> 0 <= D -> bv_unsigned sp <= ms_hi s0 -> ms_hi s0 <= 2^64 ->
  wtop s0 -> minv s0 s0.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h04__x1h17__arithh26__sat6h36__sat7h44__ffh58__varmaph65__with74__x2h81Hh92Hah:4__x3h;4__x4h<1Dh=2F1h>2F2h?2F3h@2H1hA2H2hB2H3hC2H4hD2H5hE2s0hF2spp;1p;2p;3p;4p;7p;8g002Fj19Tg003Pj1bTg003nj1STg00iCj14Tg00BZj2BTg01Efj2GTg00kMj20Tg00jHj1;Tg009nj1ETg00kij2LTg00lFj1JTg019UR0j21Tg00hBj2CTg006Wj3>Tg00Ffj2=Tg00mGj2XTg00moj2HTg00nKj3WTg00@Rj1VTg001fj1UTg010mj2<Tg012Gj1RTg012ej1QTg0143j2FTg013Pj2:Tg00_0j1PTg0159j2KTg015[j2MTg016Gj3NTg016fj4OTg00?;j1@Tg00noj2?Tg00oXj3ATg010Aj2ITg00A2j3TTg011Kj1aTg011ij4DTg002kj1`Tg01FCj3_Tg014Vj3^Tg01AEj45Tg017Xj1]Tg018]j1\Tg01:0j4[Tg01:[j7ZTg01;?j8YTg00MSR1f0R2'0p=2%]2#\p=3g00LIR3f1R4g01;cP2C[p=7P4g01<JR5g01<iR6P6g01=IR7P2g01=iFZp=6f3R8P5P6P6P7f2R5P4P2GYp=8g01>Ig00J8R9#9R:#9R;#9#9#9#9R<#bR=#S%45#2%481B=5/G4'0%25f4R>,B=f5R?#;'0f6#;%E:R@%E<R<'LRA'0f7#JP0g01BXRBf8RC#3RD'0g01A`RE,0D%4C,0D'1f9RD/CDP2f:#3,0Bf;RD#3RF/0E%4D,0F'1P0f<R0#3RF/0E%40,0Ff=RF/CFP2f>RD#3/0Ef?RG#3%4G'0f@RH#4RI=>3I%;HRJ=>3JRK%3HRL=>3LRM%2IRN10IJRO10JARP10BLRQ10LERR10LIRS'1RT'1RU'1RV'1RW'1RX'1RY'11=3IPKPY1=3JPMPX1=3LPNPW1X@<RW1H1@%2<1H1A[[RN%2@RLg01?QRXAW@<4UW9R<%2A\X^9LRLg01?mRX#VRM%UXRJ1<34RY%R3RK%Q3RI1F31RZ1:39R['7,6IR\%P6R6P\C81KI7R7P2P5g00J]R\g00RXR]'=1M25=>\]dAN314COR1b4b5b6X03%22%24[^03P2fCR]#4R\PHO2b1b2b3POPVPWPNP<PLg00NMRV#@RO#@R^#@,?31?3^1?3O1?3V5A35A35A3g01@Y'I=TXMPJP3P31<3>P5%a3RXCDP41<38CDPKPI%`9,:3R91:3:R:'7,6IP6PI1:3;R;,7Z,6IP6PIA_39;,7[,6IP617[:,6IR:C8C8C8P7P1b4b5b6X03X73X:3X;31054%2>1G>?,05108>[[[^03^73^:3^;3P2fAfB,B=%;]R?P\PFPDPGO7b1b2b3PPPUPWPNP<PLPMPJPYPKPI1F3@=^3=,7[,6IR[P6P[C8P7P1b4b5b6X03102A104A[^03P2P?P0O2b1b2b3PQPTPWPNP<PLPMPJP31<35P4PXCDPKPIP:P6P:C8P7P1b4b5b6X03X73R110241045[^03^73R5P2%3]R]PBPCO3b1b2b3PRPSPWPNP<PLP1P5P2PEP]P>O3b1b2b3PWPNP<PLP1P5P2P\P]P8O3b1b2b3C5C5C5C5C5C5C5C51CHHeW?W>P4P2O2n2001000000121000000W8W=P4P2O2n2001000000121000000W8WDWCWBWAW@X<3WFWEo"). Qed.

(* [comment removed for export] *)
Lemma alloc_top_vm_mmap : forall a n h, alloc_top (vm_mmap a n h) = alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01ah11hh21np;1p;2g002Fj10Tg003Pj14Tg003nj12Tg018]j11Tg00Ffj23Tg00J8#0#0#0#0#0#0#4#2R0g01Ffg00LIf0#1'3W1X20W0o"). Qed.
Lemma alloc_top_vm_noacc : forall a n h, alloc_top (vm_noacc a n h) = alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01ah11hh21np;1p;2g002Fj10Tg003Pj14Tg003nj12Tg018]j11Tg00Ffj23Tg00J8#0#0#0#0#0#0#4#2R0g01Ffg00LIf0#1'3W1X20W0o"). Qed.
Lemma alloc_top_vm_munmap : forall a n h, alloc_top (vm_munmap a n h) = alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01ah11hh21np;1p;2g002Fj10Tg003Pj14Tg003nj12Tg018]j11Tg00Ffj23Tg00J8#0#0#0#0#0#0#4#2R0g01Ffg00LIf0#1'3W1X20W0o"). Qed.
Lemma alloc_top_vm_fixed_ok : forall a n h, alloc_top (vm_fixed_ok a n h) = alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01ah11hh21np;1p;2g002Fj10Tg003Pj14Tg003nj12Tg018]j11Tg00Ffj23Tg00J8#0#0#0#0#0#0#4#2R0g01Ffg00LIf0#1'3W1X20W0o"). Qed.
Lemma alloc_top_vm_fixed_destroy : forall a n h, alloc_top (vm_fixed_destroy a n h) = alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01ah11hh21np;1p;2g002Fj10Tg003Pj14Tg003nj12Tg018]j11Tg00Ffj23Tg00J8#0#0#0#0#0#0#4#2R0g01Ffg00LIf0#1'3W1X20W0o"). Qed.
Lemma alloc_top_vm_unprotect : forall a n h, alloc_top (vm_unprotect a n h) = alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01ah11hh21np;1p;2g002Fj10Tg003Pj14Tg003nj12Tg018]j11Tg00Ffj23Tg00J8#0#0#0#0#0#0#4#2R0g01Ffg00LIf0#1'3W1X20W0o"). Qed.
Lemma alloc_top_vm_brk_grow : forall r h, alloc_top (vm_brk_grow r h) = alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01hh11rp;1p;2g002Fj10Tg003Pj14Tg003nj12Tg018]j11Tg00Ffj23Tg00J8#0#0#0#0#0#0#4#2g01Ffg00LIf0#1'3W0W1o"). Qed.

(* [comment removed for export] *)
Definition mwin (s0 : mstate) (mm0 : word -> option byte) (sp : word) (D : Z)
                (mm : word -> option byte) : Prop :=
  (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 ->
     ~ (bv_unsigned sp - D <= bv_unsigned a < bv_unsigned sp) -> mm a = mm0 a)
  /\ (forall a : word, bv_unsigned sp - D <= bv_unsigned a < bv_unsigned sp -> mm a <> None).

Lemma mwin_init : forall s0 mm0 sp D,
  (forall a : word, bv_unsigned sp - D <= bv_unsigned a < bv_unsigned sp -> mm0 a <> None) ->
  mwin s0 mm0 sp D mm0.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01ah11Dh23mm0h32s0h42sph51xp;1p;2p;3p;4g002Fj10Tg003Pj19Tg003nj18Tg004Qj1;Tg00BZj21Tg01Efj27Tg00kMj22Tg00moj23Tg019Uj24Tg00_0j1<Tg006Wj35Tg01G]j16Tg00iCj1:Tg00jHj1?Tg00Ffj2>Tg01AEj4=Tg01>Ig00J8#0#0#0R0#0#0#0#9R1#8R2%90#8R0#;R3]5g00LIf2R4,11R5f1R6'7f0R7,11R8'21385'4f4R5P6O1%<0R0553#6[^02f5R9#:/28%?9,38'4R:1115R5f3R;'71116R<'213<5'4#6R<f6P4O1R5=535[[^02111;R;/74/28138;'4P9P6O1=530#6[^021>35V<V:X02P7C=UW1X42W2W3o"). Qed.

(* [comment removed for export] *)
Lemma pure_wv : forall md h, md_pure md -> md_pure (with_vmmaps h md).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01Hh11hh22mdp;1p;3g00\kj11Tg01H6j30Tg00e1g01Fff1R0#1f2f0500W0W1W2o"). Qed.

(* [comment removed for export] *)
Definition wreg (l : list Z) (r : reg) : bool := existsb (Z.eqb (bv_unsigned r)) l.

Lemma getr_other_w : forall l R (rd : reg) v (r : reg),
  wreg l rd = true -> wreg l r = false -> getr (regupd R rd v) r = getr R r.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "p'0h02Hrh11Hh21rh32Hdh41Rh51bi001bh61eh71lh82rdh91vp;1p;2p;3p;6p;7p;5g001fj1=Tg002Fj10Tg002kj18Tg003Pj15Tg003nj16Tg000\j2;Tg01I9j21Tg006Wj33Tg00gfj64Tg01J:j27Tg001Hj79Tg01G]j1:Tg01JYj5<Tg00J]R0f0R1g00K=R233p=2g00LI#=g00J8#0R3#8#5R4%03#0#0#0#0#5#6R3';%64R4f4R5f2R6'1g00RXR7530f5R8f1R9'1#2P8P5f3R:P6A3465R6P4P8f8R5/11#2g01KXR;]0X24f7/18#2P0f6,15%21X50P1P7P:E4A3072P0P7P0p-0P1g01?QP;n0110000020000X60g00N1P2P1E4P;17;1b1b0W0P:P1P9F9W1%:6eD<W0W3X24X93W8W4W7o"). Qed.

(* [comment removed for export] *)
Definition cs_num (z : Z) : bool :=
  ((z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)))%Z.

Lemma wreg_cs : forall wl (x : reg), callee_saved x ->
  forallb (fun z => negb (cs_num z)) wl = true -> wreg wl x = false.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "p'0h03Hwlh11Hh21xi001xh33Hinh44__p1h54__p2h64__x1h71bi011bh82b1h92b2h:1zh;1Ah<3Hexh=2Hzh>7__arithh?4__ffh@8__varmaphA5__withB1fhC1lhD1mhE1nhF1yhG2HrhH2HxhI2_HhJ1ehK5lemmahL2wlp;1p;3p;2p;6p;8p;4p;7g001fj1NTg002Fj1ETg002kj1BTg003Pj1\Tg003nj1zTg01L5j1rTg01M8j1QTg01N;j1FTg01NYj3PTg01G]j1OTg01O5j1YTg00BZj20Tg01O[j1Vj22Tg01P8R0j3RTg01PTj3KTg019UR1j26Tg01PkR2j2HTg01QEj3gTg006Wj33Tg01Qhj2aTg01RHj2`Tg01Raj3_Tg01SRj3^Tg01T5j1]Tg009nj1?Tg00;Oj3CTg00gfj6[j7cTg01J:j2ZTg001Hj8DTg00kMj27Tg01TVj2yTg01U7j2MTg01UUR3j2@Tg01Uoj2xTg01VQj28Tg00moj2=Tg01Vnj2wTg00@Rj1qTg010mj2pTg012Gj1oTg012ej1lTg013Pj2kTg0143j2UTg01:0j4ITg00_0j1hTg0159j2fTg00Ffj2iTg015[j2jTg016Gj3eTg016fj4mTg01I9j2bTg01WNj2>Tg01:[j7sTg01Wkj6tTg01XOj7uTg01;?j8vTg00J]R4f0R5g00RXR633p=1g00K=R79345p=4g00LIR8f1R9;K5p=5f3R:f2R;'71795'6p=Af6R<f5R=f4R>33A3:;9/@5'@p=:12:;,>>1295'>p=;18:;1895'Mp=912>:,>=12;9'>/>5=347p=<A3=>:17;9/65'@p=J1>95=347p=X12;9/>5p=WP9g01<JR?g01<iR@P@g01=IRAP5g01=iFsp=GP9P?P@P@PAP5Etp=SP;P?P@P@PAP9P5Fup=TP:P?P@P@PAP;P9P5Gvp=L17;9/65p=n1795,6;p=d%N8g00J8R?#ERB#B#\RC#zRD%r5%Q5#FX:8RE=P8;#1P1%15#O%49RF[RG%45RH%19#ORI[%4;RJ\I%Y5P9n2001000000120000000X74PG^74P510C:#V=R8>RG%1GRGP0p4p710R0P4\5RI%N9RKP1AR;95#1AK>5;P:P5O1#1'6X2:,H:[RLAK:59P;P5O1#1'6X2;,H;AR:;9#1RM[AK=5:P>P5O1#1'6X2>,H>\MAg;95P9n2001000000120000000WCWBW;PL^CK^BI^;0P5P810C=#VP<P9O4f7R=,5510C</25#1'6X28,H8P2P8f8R2,5510C=/25#1'6X28g01KXR0P5f:RI,55f9,0C/25#1'6P1f;RK,5910CI/29#1P0P5f=RL,5:10CL/2>#1P11295#1A38;9[RMA389512;9#1RN[A38:;\N1a95P9n2001000000120000000XD8XE8PM^D8^E8P5f?RM,0CRNP<P9O3A38N<P8f@,0CRNfBRO,55P0]3X:8fA,5NAP8EO#1fCRN,55PEP9O1#1RP[^28RQ'`AP8EN#1fDRN,55PP[^28;_5WKA^8EOPMO2PQP510COROP9O2%QO#F#1P1%F5#1PF[RO%F9#1RQ\HPJ\Q%]5P9n2001000000120000000X74PO^74P510CN#QROP9O2%4OP3fERO%?BRQg00N1RM5CCRE53DPDPO%B?RP#?RR=CCMRSPDPO%EBRB#?RT=CCMRUPDPO%EB#?RV=CCMRWPDPO%BBRB#?RX=CCMRY%EB#?RB10COROPO%EP#B#B#?RPCAF:F:P0PNfFRN=3DEPDPE10C5RO/2QPOPRPOPTD;POPVPOPXPBPOPOPPC9E<RO10C9RZfJR['5P0]3]0X2D10CERE/2QPEPRPEPTD;PEPVPEPXPBPEPEPPC9E<fIR\,5EP4P6P4p-0REP5g01?QP0n0110100020000XJ4PMP7P9E[P01Z05b1R7W3W0fGRMP5P;P<GDW1P5O1PDPNPSPDPNPUPDPNPWPDPNPYPB10CNRNPNPPCAF:F:P3A3DMSPDPMPUPDPMPWPDPMPYPB10CMRM17MPEJF:P0P5fHRM=3DSPDPSfLRN,5ZP0]3^0OX2D10CSRS/2QPSPRPSPTD;PSPVPSPXPBPSPSPPC9E<fKR],5SP7W3W0P\P5P>P2GDW1P5O1PDPMPUPDPMPWPDPMPYPB10CMRM17MPEJF:P3A3D\UPDP\PWPDP\PYPB10C\R\P\PPCAF:P0P5A3D[UPDPUfNR\,5ZP0]3^0OX2D10CURU/2QPUPRPUPTD;PUPVPUPXPBPUPUPPC9E<fMRM,5UP7W3W0P]P5P<PIGDW1P5O1PDP[PWPDP[PYPB10C[R[P[PPCAF:P3A3D]WPDP]PYPB10C]R]17]PEJP0P5A3DNWPDPWfPR],5ZP0]3^0OX2D10CWRW/2QPWPRPWPTD;PWPVPWPXPBPWPWPPC9E<fOR[,5WP7W3W0PMP5P2f<GDW1P5O1PDPNPYPB10CNRN17NPEJP3A3DMYPB10CMRMPMPPCAP0P5A3D\YPDPYfR,5ZP0]3^0OX2D10CYRY/2QPYPRPYPTD;PYPVPYPXPBPYPYPPC9E<fQRD,5YP7W3W0P[P5PIf>GDW1P5O1PB10C\R\P\PPCAP11X9516JF[R\16FH1X;9RI[%4:R[/6J\I1y95P9n2001000000120000000X94X84P\^94^84P510C]R]/2QP]PRP]PTD;P]PVP]PXD;R\PBP]P]PPC9R]PKO3%4\%4]'6P110CDRD12DR7WQPDPTPDPV12DXE<PBPDPDPPC9#4P0P5fS,0CRD12DR7WQPDPTPDPV12DXE<PBfT,0CRDPDPPC9#4P11M95#41@JF[RD1@FH1M;9#4RH[1@[J\H1x95P9n2001000000120000000X94X84PD^94^84P5fV,0CRD,8BRH18DPRDP9O3%4H%4D'@P3fW,0CR3,8B#4183P#4P0P5fX,0CR3,8B#4P11895#41=9;[R11=5918;9#4RD[1=;:\D1w95P9n2001000000120000000XF8X28RDP1^F8^28R1P5PBfZ,0CRHP9O31=HBg01?mR[#qRJ%N[R[1p89RF%o8RX%l8RVP81k8?R?g01Y3RT1U8BRQCI,GV%h@R@PVP8PQg01;cRQP?CI,GV1SV:RR5TVP@1SV>R]CLCL1fVARAP5P;1i461j5;#1dg00MS=e89CmR6b?b@bAX68X4EX5E1=5BAnB9;P>[[^68^4E^5EP5P0f\,0CRC/7PPCP9PLO5b>b0b1W0P5O1183P#4PDP1P5PHPPP9O31=PHPJP[PFPXPVP81U8PRXPTP?CI,GVP@PVP8P?PQPXCI,GV9TVRP@P]CLCLPAP6b?b@bAX68X4EX5E1=P5Ad;9PP>[[^68^4E^5EP5P017BCPCP9PLO5b>b0b1W0P5O1n200100000021100011000b0b1W0WIP9P5O2n2001000000121000000b0b1WGP5O1n200100000021100011000W1P5O1n200100000021100011000W1P5O1n200100000021100011000W1P5O1n200100000021100011000W1P5O1n200100000021100011000b0b1b0b0W3P=P5P:Fcb=b1W=W3P9P5O2n2001000000121000000W1X:8P9P5O2n2001000000121100000b<b1W<%OGeO2b11b:;#4eW0WHW2WLo"). Qed.

Lemma wreg_sub : forall (wl wl' : list Z) (r : reg),
  forallb (fun z => existsb (Z.eqb z) wl) wl' = true -> wreg wl r = false -> wreg wl' r = false.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "p'0h01xi001xh11zh21Eh31Hh43Hinh54Hsubh61Ah72Hrh82Hzh91bi011bh:1fh;1lh<1mh=1nh>1eh?5lemmah@1rhA2wlhB3wl'p;1p;3p;2p;6p;7g001fj1ATg002Fj1KTg002kj1GTg003Pj1BTg003nj1JTg01O[j15j26Tg01NYj3;Tg01I9j2>Tg00BZj21Tg00Ffj2=Tg006Wj34Tg01P8R0j3<Tg01PTj3:Tg019UR1j27Tg01PkR2j29Tg01QEj3ITg01Qhj2HTg01RHj2FTg01Raj3ETg01SRj3DTg00gfj6@j7CTg01J:j2?Tg00LIR3f1R4f0R53<p=2g00J]R6g00RXR7745p=0g00K=R89465p=8A:345p=3%A3R9g00J8#K#G#BR:#J%55R;f3R<'2X13=;34#01><4#8f2R=,1:#5/2<P61=6511:<#5f4R>'2=465P6f5R?,1:#5f6R@'2=465%84]2P411:>#5/2?RA#0A4678RBP0p4p710R0P6\5RC%A4RDP1A<=45#0A:>5=P<P5O1#0'7X0<,9<[REA:<54P=P5O1#0'7X0=,9=A<<=4#0RF[A:?5<P>P5O1#0'7X0>,9>\FAI=45P4n2001000000120000000W;W:W6PE^;D^:C^60P5P311:@#5f7R0P4O4f8RC,3511:0/65#0'7X03,93P2P3f9,3511:C/65#0'7X03g01KXRCP5f;R2,35f:,1:/65#0'7P1f<,3411:2/64#0PCP5f>R2,3<11:2/6>#0P11645#0A43=4[R1A434516=4#0R>[A43<=\>1H45P4n2001000000120000000X<3X=3P1^<3^=3P5f@,1:R1P@P4O3A431@P3fAR1,1:R@fCR>,35PC]4X13fBR2,3@fER@,2;X13RD=;3>#0fDRE,35fG,2;X13P4O1#0[^03RF'FfFR?,2;X13=;3E#0135@fH,2;X13P4O1#0[^03;E5W?AD3D>P1O2PFP511:>R>P4O2%5>/2@#0P611:E#5/2?%85X96P2P7P5E@PBP6P7P6p-0P5g01?QPCn0110100020000X>6g00N1P8P5E@PC1?C5b3b7b5b5W4P0P5P<FCb8b3W8W4P4P5O2n2001000000121000000W3X13P4P5O2n2001000000121100000b2b3'?W2%8A1=68W2n0110100020100P5O1b2b91><=#8eW7W5W@XB9WAo"). Qed.

(* [comment removed for export] *)
Ltac keep_facts Hkeep :=
  let one z :=
    let r := constr:(@BV 5 z I) in
    try (let H := fresh "Hk" in
         assert (H := Hkeep r ltac:(reflexivity))) in
  one 1%Z; one 2%Z; one 3%Z; one 4%Z; one 5%Z; one 6%Z; one 7%Z; one 8%Z; one 9%Z; one 10%Z;
  one 11%Z; one 12%Z; one 13%Z; one 14%Z; one 15%Z; one 16%Z; one 17%Z; one 18%Z; one 19%Z; one 20%Z;
  one 21%Z; one 22%Z; one 23%Z; one 24%Z; one 25%Z; one 26%Z; one 27%Z; one 28%Z; one 29%Z; one 30%Z; one 31%Z.

(* [comment removed for export] *)
Ltac keep_tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr;
  lazymatch type of Hr with wreg ?wl _ = false =>
    repeat first
      [ (* [comment removed for export] *)
        lazymatch goal with
        | |- getr (regupd ?R0 ?r0 ?v0) r = _ =>
            let R := constr:(regupd R0 r0 v0) in
            let bl := gf_reify R in
            lazymatch bl with
            | (?base, ?l) => rewrite (getr_upds_test (wreg wl) base l r eq_refl Hr : getr R r = getr base r)
            end
        end
      | rewrite (getr_other_w wl _ _ _ r); [ | reflexivity | exact Hr ]
      | match goal with
        | Hk : forall r' : reg, wreg ?wl' r' = false -> getr ?R1 r' = getr _ r' |- getr ?R1 r = _ =>
            rewrite (Hk r (wreg_sub wl wl' r eq_refl Hr))
        end ]
  end;
  reflexivity.

(* [comment removed for export] *)
Ltac cur_pc k :=
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ => let u := eval vm_compute in (bv_unsigned pc) in k u
  end.

(* [comment removed for export] *)
Lemma at_v_addi : forall (b : word) (d : Z), at_ b d = v_addi b d.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01bh11dp;1p;2g002Fj10Tg003Pj14Tg003nj12Tg00>@j21Tg00Ffj23Tg00J8#0#0#0#0#0#0#4#2R0g00LIf1f0'1,30W1W0o"). Qed.

(* [comment removed for export] *)
Lemma negb_true_eq : forall b, negb b = true -> b = false.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "p'0h01Hh12H0h21bi001bh31ep;1p;3p;6p;2g01N;j11Tg006Wj30Tg00gfj63Tg01J:j25Tg00Ffj24Tg00J]R0f0R1g00RXR230p=2P0%11#2f1g00K=R3500[P1%12R4#2P0P4P0p-0P1g01KXR4g01?Qn0110000020000X30g00N1P2P1E3P4A0023/51b1W0%13#21403Un0110000020000X20o"). Qed.
Lemma negb_false_eq : forall b, negb b = false -> b = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "p'0h01Hh12H0h21bi001bh31ep;1p;3p;2p;6g01N;j11Tg006Wj30Tg00Ffj23Tg00gfj65Tg01J:j24Tg00J]R0f0R1g00K=R230p=2P0%11#2f1g00RXR3500[P1%13#21303U%12R4#2P0P4P0p-0P1g01?Qg01KXR4n0110000020000X30g00N1P2P1E5P4A0023/41b1W0n0110000020000X20o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lit_bv t :=
  let T := type of t in
  lazymatch eval cbv in T with
  | bv ?n => let u := eval vm_compute in (bv_unsigned t) in
             constr:(@BV n u ltac:(vm_compute; exact I))
  end.

(* [comment removed for export] *)
Ltac lit_instr i :=
  lazymatch i with
  | OpImm ?op ?rd ?rs ?imm => let rd := lit_bv rd in let rs := lit_bv rs in let imm := lit_bv imm in constr:(OpImm op rd rs imm)
  | ShiftImm ?op ?rd ?rs ?sh => let rd := lit_bv rd in let rs := lit_bv rs in let sh := lit_bv sh in constr:(ShiftImm op rd rs sh)
  | Op ?op ?rd ?a ?b => let rd := lit_bv rd in let a := lit_bv a in let b := lit_bv b in constr:(Op op rd a b)
  | OpImm32 ?rd ?rs ?imm => let rd := lit_bv rd in let rs := lit_bv rs in let imm := lit_bv imm in constr:(OpImm32 rd rs imm)
  | ShiftImm32 ?op ?rd ?rs ?sh => let rd := lit_bv rd in let rs := lit_bv rs in let sh := lit_bv sh in constr:(ShiftImm32 op rd rs sh)
  | Op32 ?op ?rd ?a ?b => let rd := lit_bv rd in let a := lit_bv a in let b := lit_bv b in constr:(Op32 op rd a b)
  | Mul ?op ?rd ?a ?b => let rd := lit_bv rd in let a := lit_bv a in let b := lit_bv b in constr:(Mul op rd a b)
  | Mul32 ?op ?rd ?a ?b => let rd := lit_bv rd in let a := lit_bv a in let b := lit_bv b in constr:(Mul32 op rd a b)
  | Lui ?rd ?imm => let rd := lit_bv rd in let imm := lit_bv imm in constr:(Lui rd imm)
  | Auipc ?rd ?imm => let rd := lit_bv rd in let imm := lit_bv imm in constr:(Auipc rd imm)
  | Jal ?rd ?imm => let rd := lit_bv rd in let imm := lit_bv imm in constr:(Jal rd imm)
  | Jalr ?rd ?rs ?imm => let rd := lit_bv rd in let rs := lit_bv rs in let imm := lit_bv imm in constr:(Jalr rd rs imm)
  | Branch ?c ?a ?b ?imm => let a := lit_bv a in let b := lit_bv b in let imm := lit_bv imm in constr:(Branch c a b imm)
  | Load ?sz ?sg ?rd ?rs ?imm => let rd := lit_bv rd in let rs := lit_bv rs in let imm := lit_bv imm in constr:(Load sz sg rd rs imm)
  | Store ?sz ?a ?b ?imm => let a := lit_bv a in let b := lit_bv b in let imm := lit_bv imm in constr:(Store sz a b imm)
  | Lr ?wd ?aq ?rl ?rd ?rs => let rd := lit_bv rd in let rs := lit_bv rs in constr:(Lr wd aq rl rd rs)
  | Sc ?wd ?aq ?rl ?rd ?a ?b => let rd := lit_bv rd in let a := lit_bv a in let b := lit_bv b in constr:(Sc wd aq rl rd a b)
  | ?x => x
  end.

(* [comment removed for export] *)
Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Ltac solveF :=
  lazymatch goal with
  | |- fetch_word ?segs ?pc = Some ?w =>
      let f := eval vm_compute in (fetch_word segs pc) in
      lazymatch f with Some ?w0 => let wl := lit_bv w0 in unify w wl; vm_refl end
  end.
Ltac solveD :=
  lazymatch goal with
  | |- decode_any ?w = ?rhs =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with Some (?i, ?sz) => let il := lit_instr i in unify rhs (Some (il, sz)); vm_refl end
  end.

(* [comment removed for export] *)
Ltac gres :=
  gres_loop;          (* [comment removed for export] *)
  rewrite ?getr_zero.

(* [comment removed for export] *)
Ltac eregs :=
  repeat match goal with
  | H : getr ?R ?r = _ |- context [getr ?R ?r] => rewrite !H
  end.

(* [comment removed for export] *)
Ltac regnorm := gres; repeat (progress (eregs; gres)).

(* [comment removed for export] *)
Ltac munf :=
  cbv beta match zeta delta [MallocOps.is0 MallocOps.w0 MallocOps.wlit MallocOps.wm1 PAGEMASK
    DEBRUIJN_MULT MMAP_THRESHOLD_W MAP_FAILED
    m_unlock m_canary_load m_canary_check m_free_meta m_seq_next FREE_FUEL
    m_ctz32 m_size_to_class_big set_errno] in *.

(* [comment removed for export] *)
Ltac zlit t :=
  let u := eval vm_compute in (bv_unsigned t) in constr:(Z_to_bv 64 u).

Ltac klit_g t :=
  lazymatch t with
  | Z_to_bv 64 (bv_unsigned _) => fail
  | Z_to_bv 64 (bytes_le_to_Z _) => fail
  | _ => idtac
  end;
  check_closed_term t;
  let l := zlit t in
  tryif constr_eq t l then fail else
  replace t with l by (apply bv_eq; vm_compute; reflexivity).

Ltac klits_with tac :=
  repeat match goal with
  | |- context [Z_to_bv 64 ?z] => tac (Z_to_bv 64 z)
  | |- context [@BV 64 ?u ?p] => lazymatch goal with |- context [mkst _ (@BV 64 u p) _ _] => fail | _ => tac (@BV 64 u p) end
  | |- context [v_lui ?k] => tac (v_lui k)
  | |- context [v_auipc ?a ?k] => tac (v_auipc a k)
  | |- context [v_addi (Z_to_bv 64 ?a) ?k] => tac (v_addi (Z_to_bv 64 a) k)
  | |- context [v_addiw (Z_to_bv 64 ?a) ?k] => tac (v_addiw (Z_to_bv 64 a) k)
  | |- context [at_ (Z_to_bv 64 ?a) ?k] => tac (at_ (Z_to_bv 64 a) k)
  | |- context [v_andi (Z_to_bv 64 ?a) ?k] => tac (v_andi (Z_to_bv 64 a) k)
  | |- context [v_ori (Z_to_bv 64 ?a) ?k] => tac (v_ori (Z_to_bv 64 a) k)
  | |- context [v_xori (Z_to_bv 64 ?a) ?k] => tac (v_xori (Z_to_bv 64 a) k)
  | |- context [v_slli (Z_to_bv 64 ?a) ?k] => tac (v_slli (Z_to_bv 64 a) k)
  | |- context [v_srli (Z_to_bv 64 ?a) ?k] => tac (v_srli (Z_to_bv 64 a) k)
  | |- context [v_srai (Z_to_bv 64 ?a) ?k] => tac (v_srai (Z_to_bv 64 a) k)
  | |- context [v_slliw (Z_to_bv 64 ?a) ?k] => tac (v_slliw (Z_to_bv 64 a) k)
  | |- context [v_add (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => tac (v_add (Z_to_bv 64 a) (Z_to_bv 64 b))
  | |- context [v_sub (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => tac (v_sub (Z_to_bv 64 a) (Z_to_bv 64 b))
  | |- context [v_and (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => tac (v_and (Z_to_bv 64 a) (Z_to_bv 64 b))
  | |- context [v_or (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => tac (v_or (Z_to_bv 64 a) (Z_to_bv 64 b))
  | |- context [v_addw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => tac (v_addw (Z_to_bv 64 a) (Z_to_bv 64 b))
  | |- context [v_subw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => tac (v_subw (Z_to_bv 64 a) (Z_to_bv 64 b))
  end.

(* [comment removed for export] *)
Ltac klitsg := klits_with klit_g.

(* [comment removed for export] *)
Ltac addr_tac :=
  regnorm; imm_norm; rewrite ?v_addi_0;
  first [ reflexivity | bveq | f_equal; first [reflexivity | bveq]
        | match goal with |- ?g => fail 100 "addr_tac cannot prove" g end ].

(* [comment removed for export] *)
Ltac rz_norm :=
  try lazymatch goal with
  | |- realizes _ (mkCfg ?st _) _ => norm_pc_state st
  end.
Ltac mpost HS := rz_norm.

(* [comment removed for export] *)
Ltac mpure Hp := first [ exact Hp | apply pure_wv; exact Hp ].

(* [comment removed for export] *)
Ltac cur_instr tac :=
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst _ ?pc _ _) _) _ =>
      let f := eval vm_compute in (fetch_word segs pc) in
      lazymatch f with
      | Some ?w =>
          let d := eval vm_compute in (decode_any w) in
          lazymatch d with
          | Some (?i, _) => tac w i
          | _ => fail "cur_instr: no decode at" pc
          end
      | _ => fail "cur_instr: no fetch at" pc
      end
  end.

(* [comment removed for export] *)
Ltac pc_tac :=
  lazymatch goal with
  | |- ?l = ?x => let lit := word_lit l in unify x lit; apply bv_eq; vm_compute; reflexivity
  end.

(* [comment removed for export] *)
Ltac val_tac := regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity.

Ltac rz_plain Hp HS L :=
  first
    [ eapply rz_step_reg;
      [ mpure Hp | eapply L; [solveF | reflexivity | solveD] | reflexivity | val_tac | pc_tac | ]
    | eapply rz_step_pc;
      [ mpure Hp | eapply L; [solveF | reflexivity | solveD] | pc_tac | ] ].

(* [comment removed for export] *)
Ltac mach Hp HS :=
  cur_instr ltac:(fun w i =>
    lazymatch i with
    | OpImm ALU_ADD _ _ _   => rz_plain Hp HS step_addi
    | OpImm ALU_AND _ _ _   => rz_plain Hp HS step_andi
    | OpImm ALU_OR _ _ _    => rz_plain Hp HS step_ori
    | OpImm ALU_XOR _ _ _   => rz_plain Hp HS step_xori
    | OpImm ALU_SLT _ _ _   => rz_plain Hp HS step_slti
    | OpImm ALU_SLTU _ _ _  => rz_plain Hp HS step_sltiu
    | ShiftImm ALU_SLL _ _ _ => rz_plain Hp HS step_slli
    | ShiftImm ALU_SRL _ _ _ => rz_plain Hp HS PropExec.step_srli
    | ShiftImm ALU_SRA _ _ _ => rz_plain Hp HS step_srai
    | Op ALU_ADD _ _ _  => rz_plain Hp HS step_add
    | Op ALU_SUB _ _ _  => rz_plain Hp HS step_sub
    | Op ALU_AND _ _ _  => rz_plain Hp HS step_and
    | Op ALU_OR _ _ _   => rz_plain Hp HS step_or
    | Op ALU_XOR _ _ _  => rz_plain Hp HS step_xor
    | Op ALU_SLL _ _ _  => rz_plain Hp HS step_sll
    | Op ALU_SRL _ _ _  => rz_plain Hp HS step_srl
    | Op ALU_SRA _ _ _  => rz_plain Hp HS step_sra
    | Op ALU_SLT _ _ _  => rz_plain Hp HS step_slt
    | Op ALU_SLTU _ _ _ => rz_plain Hp HS step_sltu
    | OpImm32 _ _ _     => rz_plain Hp HS step_addiw
    | Op32 ALU_ADD _ _ _ => rz_plain Hp HS step_addw
    | Op32 ALU_SUB _ _ _ => rz_plain Hp HS step_subw
    | Op32 ALU_SLL _ _ _ => rz_plain Hp HS step_sllw
    | Op32 ALU_SRL _ _ _ => rz_plain Hp HS step_srlw
    | Op32 ALU_SRA _ _ _ => rz_plain Hp HS step_sraw
    | ShiftImm32 ALU_SLL _ _ _ => rz_plain Hp HS step_slliw
    | ShiftImm32 ALU_SRL _ _ _ => rz_plain Hp HS step_srliw
    | ShiftImm32 ALU_SRA _ _ _ => rz_plain Hp HS step_sraiw
    | Mul M_MUL _ _ _   => rz_plain Hp HS step_mul
    | Mul M_MULHU _ _ _ => rz_plain Hp HS step_mulhu
    | Lui _ _           => rz_plain Hp HS step_lui
    | Auipc _ _         => rz_plain Hp HS step_auipc
    | Jal _ _           => rz_plain Hp HS step_jal_x0
    | _ => fail "mach: not a plain instruction:" i
    end).

(* [comment removed for export] *)
Ltac mach_jal Hp HS := rz_plain Hp HS step_jal_link.
Ltac mach_jr Hp HS :=
  eapply rz_step_pc;
  [ mpure Hp
  | eapply step_jalr_x0; [ solveF | reflexivity | solveD | regnorm; imm_norm; klitsg; reflexivity ]
  | lazymatch goal with
    | |- v_jalr (Z_to_bv 64 _) _ = _ => pc_tac
    | |- v_jalr (@BV _ _ _) _ = _ => pc_tac
    | |- ?g => fail "mach_jr: target not literal:" g
    end
  | ].

(* [comment removed for export] *)
Ltac snorm_in H := rewrite ?upd_mem, ?upd_vm, ?upd_upd in H.

(* [comment removed for export] *)
Ltac mnorm HS :=
  repeat first
    [ progress (cbv beta match zeta delta [negb andb orb fst snd] in HS;
                cbv beta match zeta delta [negb andb orb fst snd])
    | progress (rewrite mbind_assoc in HS; rewrite mbind_assoc)
    | progress (rewrite mret_bind in HS; rewrite mret_bind)
    | progress (rewrite mbind_assoc_k in HS; rewrite mbind_assoc_k)
    | progress (rewrite mret_bind_k in HS; rewrite mret_bind_k)
    | progress (snorm_in HS; rewrite ?upd_mem, ?upd_vm, ?upd_upd) ];
  try match goal with Hag : magree _ _ |- _ => snorm_in Hag end;
  try match goal with HI : minv _ _ |- _ => snorm_in HI end.

(* [comment removed for export] *)
Ltac tnorm_eq :=
  repeat first
    [ progress (cbv beta match zeta delta [negb andb orb fst snd])
    | progress (rewrite mbind_assoc)
    | progress (rewrite mret_bind)
    | progress (rewrite mbind_assoc_k)
    | progress (rewrite mret_bind_k)
    | progress (rewrite ?upd_mem, ?upd_vm, ?upd_upd) ];
  reflexivity.

(* [comment removed for export] *)
Ltac exact_HS HS := first [ exact HS | eapply tsafe_teq; [ exact HS | tnorm_eq ] ].

(* [comment removed for export] *)
Ltac mach_ld Hp HS Hag HI :=
  let bs := fresh "bs" in let Hok := fresh "Hok" in let Hrd := fresh "Hrd" in
  let Hv := fresh "Hv" in let EQ := fresh "EQ" in
  cur_instr ltac:(fun w i =>
    lazymatch i with
    | Load SZ8 true _ _ _ =>
        destruct (tsafe_ld_inv _ _ _ _ HS) as (bs & Hok & Hrd & Hv & EQ);
        rewrite EQ in HS; rewrite EQ; clear EQ;
        eapply rz_step_p; [ mpure Hp | reflexivity
          | lazymatch type of Hok with acc_ok _ ?ma _ = true => eapply step_ld_at with (a := ma) end;
            [solveF | reflexivity | solveD | reflexivity
            | addr_tac
            | exact (magree_rd _ _ _ 8%nat _ Hag (minv_lo64 _ _ HI) Hok Hrd) | exact Hv ]
          | mpost HS ]
    | Load SZ4 true _ _ _ =>
        destruct (tsafe_lw_inv _ _ _ _ HS) as (bs & Hok & Hrd & Hv & EQ);
        rewrite EQ in HS; rewrite EQ; clear EQ;
        eapply rz_step_p; [ mpure Hp | reflexivity
          | lazymatch type of Hok with acc_ok _ ?ma _ = true => eapply step_lw_at with (a := ma) end;
            [solveF | reflexivity | solveD | reflexivity
            | addr_tac
            | exact (magree_rd _ _ _ 4%nat _ Hag (minv_lo64 _ _ HI) Hok Hrd) | exact Hv ]
          | mpost HS ]
    | Load SZ4 false _ _ _ =>
        destruct (tsafe_lwu_inv _ _ _ _ HS) as (bs & Hok & Hrd & Hv & EQ);
        rewrite EQ in HS; rewrite EQ; clear EQ;
        eapply rz_step_p; [ mpure Hp | reflexivity
          | lazymatch type of Hok with acc_ok _ ?ma _ = true => eapply step_lwu_at with (a := ma) end;
            [solveF | reflexivity | solveD | reflexivity
            | addr_tac
            | exact (magree_rd _ _ _ 4%nat _ Hag (minv_lo64 _ _ HI) Hok Hrd) | exact Hv ]
          | mpost HS ]
    | Load SZ2 false _ _ _ =>
        destruct (tsafe_lhu_inv _ _ _ _ HS) as (bs & Hok & Hrd & Hv & EQ);
        rewrite EQ in HS; rewrite EQ; clear EQ;
        eapply rz_step_p; [ mpure Hp | reflexivity
          | lazymatch type of Hok with acc_ok _ ?ma _ = true => eapply step_lhu_at with (a := ma) end;
            [solveF | reflexivity | solveD | reflexivity
            | addr_tac
            | exact (magree_rd _ _ _ 2%nat _ Hag (minv_lo64 _ _ HI) Hok Hrd) | exact Hv ]
          | mpost HS ]
    | Load SZ1 false _ _ _ =>
        destruct (tsafe_lbu_inv _ _ _ _ HS) as (bs & Hok & Hrd & EQ);
        rewrite EQ in HS; rewrite EQ; clear EQ;
        eapply rz_step_p; [ mpure Hp | reflexivity
          | lazymatch type of Hok with acc_ok _ ?ma _ = true => eapply step_lbu_at with (a := ma) end;
            [solveF | reflexivity | solveD | reflexivity
            | addr_tac
            | exact (magree_rd _ _ _ 1%nat _ Hag (minv_lo64 _ _ HI) Hok Hrd) ]
          | mpost HS ]
    | _ => fail "mach_ld: not a modeled load:" i
    end);
  mnorm HS.

(* [comment removed for export] *)
Ltac mach_st Hp HS Hag HI :=
  let Hok := fresh "Hok" in let Hso := fresh "Hso" in let EQ := fresh "EQ" in
  let go L n :=
    unfold m_sb, m_sh, m_sw, m_sd in HS |- *;
    let body ma mv :=
      rewrite EQ in HS; rewrite EQ; clear EQ;
      eapply rz_step_p; [ mpure Hp | reflexivity
        | eapply L with (a := ma) (v := mv);
          [solveF | reflexivity | solveD
          | addr_tac
          | addr_tac
          | exact (magree_sok _ _ _ n Hag (minv_lo64 _ _ HI) Hok Hso) ]
        | mpost HS ];
      lazymatch type of Hag with magree ?s0 _ =>
        apply (magree_wbytes s0 _ ma (word_to_le_bytes n mv) (ms_vm s0)) in Hag end in
    lazymatch type of HS with
    | tsafe (MallocTree.mbind (m_st _ ?ma ?mv) _ _) _ =>
        destruct (tsafe_st_inv _ _ _ _ _ _ HS) as (Hok & Hso & EQ); body ma mv
    | tsafe (m_st _ ?ma ?mv _) _ =>
        destruct (tsafe_st_inv0 _ _ _ _ _ HS) as (Hok & Hso & EQ); body ma mv
    end
  in
  cur_instr ltac:(fun w i =>
    lazymatch i with
    | Store SZ8 _ _ _ => go step_sd_at 8%nat
    | Store SZ4 _ _ _ => go step_sw_at 4%nat
    | Store SZ2 _ _ _ => go step_sh_at 2%nat
    | Store SZ1 _ _ _ => go step_sb_w 1%nat
    | _ => fail "mach_st: not a store:" i
    end);
  mnorm HS.

(* [comment removed for export] *)
Ltac mach_br_dir Hp HS dir ctac :=
  cur_instr ltac:(fun w i =>
    let go Ltk Lft :=
      lazymatch dir with
      | true => eapply rz_step_pc; [ mpure Hp
                 | eapply Ltk; [solveF | reflexivity | solveD | regnorm; imm_norm; ctac] | pc_tac | ]
      | false => eapply rz_step_pc; [ mpure Hp
                 | eapply Lft; [solveF | reflexivity | solveD | regnorm; imm_norm; ctac] | pc_tac | ]
      end in
    lazymatch i with
    | Branch BC_EQ _ _ _  => go step_beq_tk step_beq_ft
    | Branch BC_NE _ _ _  => go step_bne_tk step_bne_ft
    | Branch BC_LT _ _ _  => go step_blt_tk step_blt_ft
    | Branch BC_GE _ _ _  => go step_bge_tk step_bge_ft
    | Branch BC_LTU _ _ _ => go step_bltu_tk step_bltu_ft
    | Branch BC_GEU _ _ _ => go step_bgeu_tk step_bgeu_ft
    | _ => fail "mach_br: not a branch:" i
    end).

(* [comment removed for export] *)
Ltac by_bool Hb :=
  first [ exact Hb
        | exact (negb_true_eq _ Hb)
        | exact (negb_false_eq _ Hb)
        | rewrite <- Hb; reflexivity
        | rewrite <- (negb_true_eq _ Hb); reflexivity
        | rewrite <- (negb_false_eq _ Hb); reflexivity
        | lazymatch goal with |- ?g => let t := type of Hb in fail 1 "by_bool: goal" g "fact" t end ].

(* [comment removed for export] *)
Ltac mach_assert Hp HS :=
  let Hb := fresh "Hb" in let EQ := fresh "EQ" in
  destruct (tsafe_assert_inv _ _ _ _ HS) as [Hb EQ];
  rewrite EQ in HS; rewrite EQ; clear EQ; mnorm HS;
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst _ ?pc _ _) _) _ =>
      let f := eval vm_compute in (match fetch_word segs (v_addi pc 4) with Some w => bv_unsigned w | None => 0%Z end) in
      lazymatch f with
      | 35%Z => first [ mach_br_dir Hp HS true ltac:(by_bool Hb) | mach_br_dir Hp HS false ltac:(by_bool Hb) ]
      | _ => first [ mach_br_dir Hp HS false ltac:(by_bool Hb) | mach_br_dir Hp HS true ltac:(by_bool Hb) ]
      end
  end;
  clear Hb.

(* [comment removed for export] *)
Ltac mach_if Hp HS Hc :=
  first [ mach_br_dir Hp HS true ltac:(by_bool Hc)
        | mach_br_dir Hp HS false ltac:(by_bool Hc) ].

(* [comment removed for export] *)
Ltac mach_case Hp HS :=
  let Hc := fresh "Hc" in
  lazymatch goal with
  | |- realizes _ _ (tshape (MallocTree.mbind (if ?c then _ else _) _ _) _) =>
      destruct c eqn:Hc; rewrite ?Hc in HS; mnorm HS; mach_if Hp HS Hc
  | |- realizes _ _ (tshape ((if ?c then _ else _) _) _) =>
      destruct c eqn:Hc; rewrite ?Hc in HS; mnorm HS; mach_if Hp HS Hc
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wbytes_win_out : forall s (a : word) (n : nat) bs m (x : word),
  acc_ok s a (Z.of_nat n) = true -> length bs = n ->
  ms_lo s <= bv_unsigned x < ms_hi s ->
  wbytes m a bs x = m x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h04__x1h14__x2h21mh32H1h41nh51Hh62H0h72H3h82Hkh94__p1h:4__x3h;2H2h<5Hlen0h=7__arithh>4__ffh?8__varmaph@5__withA4cstrhB5cstr0hC2H4hD2HahE3HokhF6__sat3hG6__sat4hH4__x4hI2b1hJ2b2hK1xhL4HlenhM2HxhN6__sat1hO6__sat2hP1ahQ2bshR1shS1yp;1p;3p;2p;4p;6p;5p;<p;7p;8g002Fj1?Tg003Pj1ZTg003nj1XTg001fj1NTg004Qj1zTg01YZR0j15Tg01Z:j3jTg01[@j2ATg006Wj36j1OTg00iCj1;Tg00BZj20Tg00kMj21Tg00jHj18Tg00moj22Tg019UR1j2>Tg01[`j1WTg009nj1STg00kij2iTg01WNj2VTg01UUR2j2GTg01\^j2dTg01VQj27Tg01U7j2HTg00Ykj4PTg01]>j2_Tg01]^j2<Tg01^;j2^Tg01^^j3]Tg00Ffj2@Tg01_;j4QTg01_bj1FTg00mGj2\Tg00nKj3[Tg00?;j1LTg00noj2KTg00oXj3YTg010Aj2yTg00@Rj1xTg00A2j3wTg010mj2ITg011Kj1uTg011ij4DTg012Gj1tTg012ej1qTg013Pj2ETg002kj1pTg00_0j1oTg01`Gj3nTg0159j2hTg015[j2gTg016Gj3fTg016fj4kTg001Hj6RTg01`jj5eTg01ajj3lTg0143j2mTg014Vj3cTg01:0j4JTg01bMj6bTg01cMl<aTg01:[j7rTg01Wkj6sTg01XOj7`Tg01;?j8vTg00J]R3f0R4g00RXR536p=4g00MSR6/14p=3f1R7%54'<p=91774=635p=:g01d2R8g00LIR9P4P0P7f2R0f3R:f4R;f5R<f6R=f7R>f8R?M<ap=MP9P7g01;cP4CJp=BP7g01<JR@g01<iRAPAg01=IRBP4g01=iFrp==P7P@PAPAPBP4Esp=UP0P@PAPAPBP7P4F`p=TP:P@PAPAPBP0P7P4Gvp=Cg01>Ig00J8R@#?RC#?RD#?RE#?#?#?RF#ZRG#XRH%ZE#XRE#N%zERI\H%5:9j<;#41AE:=68;%;>10G0RJ'1%8>,2J'>%W>10G>R>#3%SCRJ%SFRF'iRK,2>'>%W;10G;R>#312>K'>P11V74#4%40R>%47RL'G[RM%44,GL1V07#4RL[%4:/G>\L1d74P7n2001000000120000000XJ3XI3PM^J3^I3P4f:RM,0GRLf9R>'9RNf;RO#;'7RP%8O/7L17NK'HRNP<O3%4P%4N'GP210GOR2/9MRNf<RP#;':%8P/7217NK'H#4P>PPPMP?CPP>P?O156IP410GPR?/9ORMf=RN#;':P11:741107[R211741:07RL[11:0RQ\L1_74P7n2001000000120000000X29X49RLP2^29^49R2P4f>RR,0GRS/9NRTf?RU#;RVP7O311TVPNPPPUPOP8PRf@RV,0GRW%54RX'</1?X481AENRY=68R%5YRZ%5RR[569R\%O8R]%O9R^%57=69XA68741^743]XS8XK8R_PYPZ1@9ZPRP[1@9[M9MP>CQP\1AERR\#F%5\#3%FV%5VR\#31\JFR[126J%3F126K[[RZ%3JR`g01?QRaA[JF7UWDRF%3K\a^D`R`P1%3W12WKfERa,0GRbfDRc'9RdfARe,0GRf'1POfBRg,0G#3fCRh,0GRi/2KP1fHRj,0GRk#312kKfIRl,0GRm/9j/1bPVfJ,0GRb#3fKRn,0G/2KPlPjO1PIp-0Rjg01?mRlg00NMRo#LRp#L,K91K9p1K9o5Y95Y9g01@Y'y%xlRo3wRp%NlRlP9P91I9;P0%u9RqCDP71I9:RrCD%t9Rs%q9Rt1E9DRD%p@,E9Ru'B,=t1Ut=5Tt%oARAPt1E9@R@1E9CRC5n9R=/BD,=tPA1B=u,=tCCCC1htBRBP4P01@351g40#4dAf967CkR6b>b?b@X09X19X:9XH9W91>Q;1<70R5/1;1<0:/1;[[^09^19^:9^H9^9jP4fOR;#8,2b%;;PbfM#5fNR3,0GfGRDPUO7b=b2W;W5P7P4O2n2001000000121000000W3W6P7P4O2n2001000000121000000bNbObBbAb<PYP>ERDeb8b3W8P4O1%8N/7?17MK'H#4%8R10GNRR'7RM19RP/7KRR;l4%4M%4R'>P1%8U/:S1:TKPPPUPNPOCPPPPOO156IP4%8e/:W1<f\/:KPLP2P4%8cRfPiP0O311fiPLP2P4PdPKP:O311dKPcPhfFPgP8Pa10GDRh/<X/1KX481AEcRc=68a%5cRX%5aRd569R2P]P^P_PcPX1@9XPaPd1@9dM9MPVCQRdP21AEaRa#FRE%5a#3Ra%FDRX%5D#3R_P[PZPFP`P1%3hR^12hKRhfL,0GR]/9n/1KPg%3mRm12bKRbP110G;Rn#3RL12nKRnfPRf,0GRi/9;/1KPDfQ,0GR\#3RWfR,0G/2KROPfP;O1R;PIPoPlP91I90RoP7PqCDPsPt1m9J=c9G,B=,=tR=PAP=CCPBP6b>b?b@X09X191<47/1K115K[^09^19P4fT#5fU,0GRGPUO3b=b2WCW5P7P4O2n2001000000121000000W7W6P7P4O2n2001000000121000000bFbGbBbAb<PcPVERPdP2PEPaPXP_P[PZPFP`P1P^Ph12k]PgP1PLPn12]iPDP;PIPpPlP9PoP7PrCDPsPt1Ut<P9P@g01Y3R<PuCJ,=t5TtPAPt1BuC,=tPAP9P@P<PCCJ,=tCCCCPBP6b>b?b@X09X19X:9X9j1240,>:120:\Q[^09^19^:9^9jP4fVRj#;/1\%8jPGP\P3PeO6b=b2XCOX5WP7P4O2n2001000000121000000X7bX6mP7P4O2n2001000000121000000bFbGbBbAb<Ebb;b7b3b7W;W3P7P4O2n2001000000121000000b8W8P4O1n200100000021100011000bEb3b6b5WMWLWEXKHW2WQX48WPWRo"). Qed.

(* [comment removed for export] *)
Lemma wbytes_out : forall bs m (a x : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x) ->
  wbytes m a bs x = m x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01Hh12H0h23Hnwh31ah42bsh51mh61xp;1p;2p;4p;3p;6p;5g002Fj10Tg003Pj19Tg003nj18Tg001fj1;Tg004Qj1ATg00BZj25Tg01[@j23Tg01YZj12Tg01]^j21Tg009nj17Tg00kij2:Tg00kMj24Tg00moj26Tg01UUR0j2@Tg00Ykj4?Tg006Wj3>Tg01bMj6<Tg01`jj5=Tg00J8#0R1#0#0R2#9#8R3#;%02#0#0R2#9R4#8R5%A3R6[f1,54R7f3R8,33#2'1%71%72':'4f2,54R2,67f4R1,33#2,12/47'@P01548R0,62f5R7,33#2,10/42P7P1f6R2P8C?P7P8O15>6f0R61541R4,60f7R9P2P7P1P8P6E<W0P6O11332#2,14/40P9P2P7P1P6D=W0P6O1n200100000021000010000W1W2X65X35W5W4o"). Qed.

Lemma wbytes_nn : forall bs m (a x : word), m x <> None -> wbytes m a bs x <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01xh11Hh21ah32bsh41mp;1p;3p;5g002Fj10Tg003Pj12Tg003nj11Tg001fj13Tg004Qj18Tg00_0j17Tg006Wj36Tg01G]j14Tg01dQj55Tg00J8#0#0#0R0#2#1R1#3%00#0#0#2#1R0%81R2]0f2R3f0R4O1%71562#4f4f3P3f1P4D5W1X00X20W4W3o"). Qed.

Lemma unfill_out : forall (a n : word) m (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x) ->
  unfill a n m x = m x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "p'0h02E2h12E1h21mh31nh41bi001bh52H0h64__p1h74__x1h84__x2h94__x3h:1Hh;7__arithh<4__ffh=8__varmaph>5__with?1ah@1xp;1p;2p;3p;4p;7p;6p;8g002Fj19Tg003Pj1BTg003nj1@Tg004Qj1GTg00BZj21Tg00moj23Tg01]^j22Tg00kMj27Tg01UUj2?Tg01VQj26Tg00Ffj2=Tg006Wj30Tg01eQj28Tg01U7j25Tg00_0j1CTg01]>j2VTg01enj2UTg00@Rj1TTg001fj1RTg010mj2ATg011ij4QTg012Gj1MTg012ej1LTg013Pj2<Tg002kj1JTg01`Gj3ITg01:0j4:Tg01fNj7HTg01Wkj6KTg0159j2FTg015[j2NTg016Gj3ETg016fj4OTg01g2j4PTg01:[j7DTg01;?j8STg00J]R0f0R1g00RXR230p=4f1R3g01<JR4g01<iR5P5g01=IR6P1g01=iFDp=;f3R7P4P5P5P6f2R8P3P1GSp=>g00J8R9#9R:#9#9R;#9#9#9#BR<#@R=%B;#@R;#GR>\=11<1R?11<7R@'311<8RA,2@/7?'?f4R?,1<RB11<3'6P01=01RCf5RD,1<RE/6A=001P0f7RA,1<RF/6B=001P0P>f8RG,1<RH/2F,8ERE,53%C;R;f6RIPDO1RJn0100000020000=0>J]1P311<IRJ/6@R@#412FJ,8BRBP0PCA00E1REP0f:,1<RKf9RL,1<RM'2,8F=001RFP0P>1523P;PLPGO1RLn0100000020000=0>L]0P312MH,8JRJ#4RMg00LIRNg019URO1631#41783RP[RQ17311683#4RR[1778\R1V31P3n2001000000120000000X2NW3PQ^2N^3NP1f;RQ,1<RRPHP?O317RHPO1831#41383[RO13311883#4RR[1378\R1U31P3n2001000000120000000X2NX3NPO^2N^3NP1PKf=RO,1<f<RR,1<RH'2RSP7O313KSp-0RSg01?mRK#T%RKPN1AN8P31AN7CQ%MN%LNRKPN1<N9RTg01Y3RU1<N:R:%J9,<N5INR9C:,;K%C5RVPKPNP:g01;cRWPTC:,;KPVPKPKP4P5P5P6PNPTPUP:C:,;KPNP9PWPTC:,;KFHPVPKP4P5P5P6PDEKC>C>C>1FK6P1P81=021N18#4dg00MS=EN3COb<b=b>X7NX8NX9NW61238,311387127?/78'?PI[\P[^7N^8N^9N^6SP1POPRO190>;f>,1<f?,1<PHP3P7PQO7b;b0b5b1b5P0P>1522P;PGPAO1RAn0100000020000=0>AeW0g00K=RG900JRJ1=>ARQP0P>152GP;PAn0100000020000=0>AeW0n0110000020100P1O1b0b4W1A00@GPBP0PCPEP0P0P>15G3P;PLn0100000020000=0>L^0FP3PQP0P>15G2P;PAn0100000020000=0>AeX0MPQP0P>15GGP;PAn0100000020000=0>AeX0Jn0110000020000P1O1b0b4W1n0110000020101P1O1b1b4P?P7P8P3CPP8P3O150>eW:X@=W2X3=W?o"). Qed.

(* [comment removed for export] *)
Lemma zfill_out : forall (a n : word) m (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x) ->
  zfill a n m x = m x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "p'0h01Eh11mh21nh32E1h42E2h52H0h64__p1h74__x1h84__x2h94__x3h:1Hh;7__arithh<4__ffh=8__varmaph>5__with?1ah@1bi001bhA1xp;1p;2p;3p;4p;7p;6p;8g002Fj18Tg003Pj1BTg003nj1@Tg004Qj1FTg00BZj20Tg00moj26Tg01]^j22Tg00kMj27Tg01UUj2?Tg01VQj23Tg01eQj25Tg01U7j2:Tg00Ffj2>Tg006Wj34Tg00CDj2WTg0065j2VTg01ajj3UTg019UR0j2TTg01]>j2PTg01enj2OTg00@Rj1NTg001fj1LTg010mj2ATg011ij4KTg012Gj1ITg012ej1HTg013Pj2<Tg002kj1GTg01`Gj3JTg01:0j4;Tg00_0j1ETg01fNj7MTg01Wkj6DTg0159j2QTg015[j2CTg016Gj3RTg016fj4STg01glj4ZTg01:[j7YTg01;?j8XTg00J]R1f0R2g00RXR334p=1f1R4g01<JR5g01<iR6P6g01=IR7P2g01=iFYp=9f3R8P5P6P6P7f2R9P4P2GXp==g00J8R:#8R;#8#8R<#8#8#8#BR=#@R>%B<R<#@R?#FR@\>10=2RA10=8RB'610=9RC,2B/7A'?f4RA,0=RD10=4RE'312DB,5E':P11>12f5RE,0=RF/3C12FD,5C':=412P1f7RC,0=RG/3DRHf6RI,0=RJ,2G,5DRD':=412P1P@P4g00MSRK,W<,V?R?PIPEO1R<n0100000020000=4@<]0P413JB12JF,5B':RB#1AUHD2%1H%1D'TP0f8,0=RD/3F#112DG,5F#1PCPIO194@?P2f:,0=RC/3G#1f;,0=/2C,5D#1g00LIRDP01342#11794RG[RF17421394#1RH[1789\H1P42P4n2001000000120000000X1DW2PF^1D^2DP2f=RF,0=RHPCP9O317HCP01542#11694[R016421594#1RH[1689\H1O42P4n2001000000120000000X1DX2DP0^1D^2DP2f<,0=R0f?RH,0=f>RC,0=RJ'2R<P8O3160<p-0R<g01?mR0#N%L0PD1AD9P41AD8CK%ID%HDR0PD1<D:RLg01Y3RM1<D;R;%G:,<D5JDR:C;,90%E6RNP0PDP;g01;cROPLC;,90PNP0P0P5P6P6P7PDPLPMP;C;,90PDP:POPLC;,90FMPNP0P5P6P6P7PEEDC=C=C=1Q07P2P91>131C29#1dARDK4CSb<b=b>X7DX8DX9DW61249,621698128A/79'?PI[\G[^7D^8D^9D^6<P2PHPCO194@?f@,0=fA,0=PJP4P8PFO7b;b4b5b3b5W4W3P4P2O2n2001000000121000000b0W0g00K=941BPEPAO1,>@W0n0110000020100P2O1b0b@PAP8P9P4CZP9P4O154@eW:XA>W1X2>W?o"). Qed.

Lemma zfill_nn : forall (a n : word) m (x : word), m x <> None -> zfill a n m x <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "p'0h01xh11Hh22H0h32H1h41ah51bi001bh61eh71mh81ni011op;1p;3p;2p;6p;4g002Fj10Tg003Pj15Tg003nj14Tg004QR0j16Tg00_0j1@Tg006Wj32Tg01G]j11Tg00BZj23Tg01VQj2;Tg01]^j2:Tg01eQj27Tg01U7j28Tg00CDj29Tg0065j2?Tg00gfj6>Tg01J:j2=Tg01glj4<Tg00J8#0#0#0R1#0#0#0#5R2#4R3%51R1#4R4#6R5^03f1R6f0R7O1%@4R8525#1f4R9,32R:1326R;';f3R<,32,::,7;'8g00J]R;P;P;P5P7g00MS,91,?4R1P9P<O1n0100000020000=258#1P7A2518R;P5P1P0P4p-0P7g01?Qg01KXR4n10110100021000000X65g00N1P8P7E>P41=47b3W2%1;eP6n0110000020000b5P9P<f2P6C<=258#1eW1X03W7X83W4o"). Qed.

Lemma apply_zeros1_out : forall (a n : word) m (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x) ->
  apply_zeros m [(a, n)] x = m x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01Hh11ah21mh31nh41oh51xp;1p;2p;3p;5p;4p;6g002Fj10Tg003Pj13Tg003nj12Tg004Qj14Tg00BZj21Tg00moj2<Tg01]^j2;Tg00kMj25Tg01UUj26Tg01hej37Tg006Wj38Tg01i^j59Tg0081j2:Tg00:Lj4BTg00@Rj1ATg00A2j3@Tg01jdj2=Tg01k\j3>Tg001Hj6?Tg00J8#0#0#0R0#0#0#0#3R1#2R2%30#2#4R0\2R3f0R4,11R5f3R6,11R7'<f2R8,11,;7/55'6P3f4R5=786P4P8O1P6P8O1580X43P5P6P8f1P4D91:22R4P2P2P5P6CB%A43@,=8A>856E?W0X52W2X32W1o"). Qed.

Lemma apply_zeros1_nn : forall (a n : word) m (x : word), m x <> None -> apply_zeros m [(a, n)] x <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01xh11Hh21ah31mh41nh51op;1p;3p;5p;2p;4p;6g002Fj10Tg003Pj14Tg003nj12Tg004Qj15Tg00_0j1?Tg006Wj33Tg01G]j11Tg01hej3;Tg01l`j5:Tg0081j26Tg00:Lj47Tg00@Rj18Tg00A2j39Tg01jdj2>Tg01k\j3=Tg001Hj6<Tg00J8#0#0#0R0#0#0#0#4#2R1%40#2R0#5R2^01f1R3f0R4O1%?0R0532#1P2\1R5f2R6f4R7f3R83;P4P6O1=320#1X55P7P8P6P3P4D:1611R4P1P1P7P8C7%8439,>6A=678E<W1X01W3X41W2o"). Qed.

Lemma apply_zeros0 : forall m, apply_zeros m [] = m.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01mp;1p;2g002Fj10Tg003Pj12Tg003nj11Tg004Qj13Tg00Ffj24Tg00J8#0#0#0R0#0#0#0#2#1%20#1#3[R0f0,40W0o"). Qed.

Lemma length_w2l : forall n (v : word), length (word_to_le_bytes n v) = n.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01nh11vp;1p;2g002Fj10Tg003Pj13Tg003nj12Tg01mej21Tg01d2g00J8#0#0#0#0#0#0#3#2f1f0'1W1W0o"). Qed.

(* [comment removed for export] *)
Lemma u_v_addi : forall (x : word) (k : Z), 0 <= bv_unsigned x + k < 2^64 ->
  bv_unsigned (v_addi x k) = bv_unsigned x + k.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01Hh12Hah24__x1h34__x2h42H0h57__arithh64__ffh76__sat0h86__sat1h98__varmaph:5__with;1kh<1xh=1zp;1p;2p;3p;4p;7p;6p;8g002Fj14Tg003Pj1ZTg003nj1ETg00BZj20Tg01]^j21Tg009nj1:Tg00kij2DTg00moj23Tg019UR0j25Tg01nmj2@Tg006Wj36Tg00mGj2=Tg00nKj3YTg00@Rj1UTg001fj1TTg010mj2LTg011Kj1KTg011ij4ITg012Gj1HTg012ej1GTg013Pj29Tg01`Gj3CTg0143j2;Tg014Vj3FTg01:0j47Tg00_0j1BTg01XOj7ATg0159j2JTg00Ffj2?Tg015[j2MTg016Gj3NTg016fj4>Tg01oSj3OTg00CDj2PTg020?j2QTg001Hj6RTg00>@j2STg00kMj2XTg01:[j7WTg01;?j8VTg00MSR1f0R2'Xp=2f1R3g01<JR4g01<iR5P5g01=IR6P2g01=iFWp=8f3R7P4P5P5P6f2R8P3P2GVp=<g00J8R9#4R:#4#4#4#4#4R;#ZR<#Eg00LIR=10<3/12R>#2%::R?%:;R;'DR@,3>'5P=10<8/13R>,@<10<7/1896=2X==1=?;131?%2;131@[[%2?RAg01?QRBAY?;3UW1%2@\B^1AP0f4R0,0</17RA#213A@f5RA,0</10R0#2130@'5P8f6R0,0</1A#2f7,0</10/3@g01?mR0#U%T0P=1L=8P3%K=CI%H=%G=R0P=19=919=:5C=R:g01Y31;=?=F=<C7,80R?%B5R9P0P=1;=1g01;cP:C7,80R:P9P0P4P5P5P6P:P?FAC<C<1J06P2P8g00J]R0g00RXR6'?1M28=606dAN=13C>b6b9b:X2=X3=1123/3@1138#21187R7#2137@'5[[^2=^3=P2f8f9,0<P3P8O4b5W4W0P3P2O2n2001000000121000000b7b89O<>1P<>,0<1Q<>ER1S83,0<=6=>eW0W;W<o"). Qed.

Lemma v_addi_addi' : forall (x : word) (a b : Z), v_addi (v_addi x a) b = v_addi x (a + b).
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01ah11bh21xp;1p;3g002Fj10Tg003Pj13Tg003nj12Tg020nj31Tg00J8#0#0#0#0#0#0#3#2g00LIR0f2f1f031X10W0W2o"). Qed.

(* [comment removed for export] *)
Definition in_frame (sp : word) (F : Z) (x : word) : Prop :=
  bv_unsigned sp - F <= bv_unsigned x < bv_unsigned sp.

Ltac atop_norm_in H :=
  cbn [ms_lo ms_hi ms_mem ms_vm upd] in H;
  rewrite ?alloc_top_vm_mmap, ?alloc_top_vm_noacc, ?alloc_top_vm_munmap, ?alloc_top_vm_fixed_ok,
    ?alloc_top_vm_fixed_destroy, ?alloc_top_vm_unprotect, ?alloc_top_vm_brk_grow in H.
Ltac atop_norm :=
  cbn [ms_lo ms_hi ms_mem ms_vm upd];
  rewrite ?alloc_top_vm_mmap, ?alloc_top_vm_noacc, ?alloc_top_vm_munmap, ?alloc_top_vm_fixed_ok,
    ?alloc_top_vm_fixed_destroy, ?alloc_top_vm_unprotect, ?alloc_top_vm_brk_grow.

Ltac note_win HI :=
  let H1 := fresh "Hwlo" in let H2 := fresh "Hwhi" in let H3 := fresh "Hwtop" in
  pose proof (minv_lo _ _ HI) as H1; pose proof (minv_hi _ _ HI) as H2;
  pose proof (minv_ceil_num _ _ HI) as H3;
  cbn [ms_lo ms_hi ms_mem ms_vm upd] in H1, H2; atop_norm_in H3.

(* [comment removed for export] *)
Ltac arith_only :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | (_ <= _)%Z => fail | (_ < _)%Z => fail | (_ >= _)%Z => fail | (_ > _)%Z => fail
      | (_ <= _ < _)%Z => fail | (_ <= _ <= _)%Z => fail | (_ < _ <= _)%Z => fail | (_ < _ < _)%Z => fail
      | @eq Z _ _ => fail | ~ _ => fail | _ /\ _ => fail | _ \/ _ => fail
      | _ => clear H
      end
  end.
(* [comment removed for export] *)
Module RefLiaL2.
  Import Ltac2.
  Ltac2 arith_ty (ty : constr) : bool :=
    lazy_match! ty with
    | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
    | @eq Z _ _ => true | ~ _ => true | _ /\ _ => true | _ \/ _ => true
    | _ => false
    end.
  Ltac2 keep_arith1 () :=
    let hs := Control.hyps () in
    let ids := List.map (fun (h : ident * constr option * constr) => let (id, _, _) := h in id)
                 (List.filter (fun (h : ident * constr option * constr) => let (_, _, ty) := h in arith_ty ty) hs) in
    Std.keep ids.
  Ltac2 keep_arith () := Control.enter keep_arith1.
End RefLiaL2.
Ltac arith_only_fast := ltac2:(RefLiaL2.keep_arith ()).
(* [comment removed for export] *)
Ltac lia_nodiv :=
  intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook;
  xlia zchecker.
Ltac alia := first [ arith_only_fast | arith_only ]; first [ lia_nodiv | lia ].

(* [comment removed for export] *)
Ltac uaddr :=
  cbn [ms_lo ms_hi ms_mem ms_vm upd];
  rewrite ?v_addi_addi'; rewrite ?u_v_addi by alia.
(* [comment removed for export] *)
Ltac uaddrH H :=
  cbn [ms_lo ms_hi ms_mem ms_vm upd] in H;
  rewrite ?v_addi_addi' in H; rewrite ?u_v_addi in H by alia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac peel_by L side := etransitivity; [ apply L; side | ].
Ltac peel1 x :=
  first
    [ (* [comment removed for export] *)
      match goal with
      | Hf : forall a : word, in_frame _ _ a -> ?m1 a = ?m0 a |- ?m1 x = _ =>
          peel_by (Hf x) ltac:(unfold in_frame; uaddr; alia)
      end
    | (* [comment removed for export] *)
      match goal with
      | Hok : acc_ok ?s ?a (Z.of_nat ?n) = true |- wbytes ?m ?a ?bs x = _ =>
          peel_by (wbytes_win_out s a n bs m x Hok (length_w2l _ _)) ltac:(uaddr; alia)
      | Hok : acc_ok ?s ?a ?z = true |- wbytes ?m ?a ?bs x = _ =>
          peel_by (wbytes_win_out s a (Z.to_nat z) bs m x Hok (length_w2l _ _)) ltac:(uaddr; alia)
      end
    | (* [comment removed for export] *)
      lazymatch goal with
      | |- wbytes ?m ?a ?bs x = _ =>
          peel_by (wbytes_out bs m a x) ltac:(rewrite ?length_w2l; uaddr; alia)
      end
    | (* [comment removed for export] *)
      lazymatch goal with
      | |- unfill ?a ?n ?m x = _ => peel_by (unfill_out a n m x) ltac:(uaddr; alia)
      end
    | (* [comment removed for export] *)
      lazymatch goal with
      | |- zfill ?a ?n ?m x = _ => peel_by (zfill_out a n m x) ltac:(uaddr; alia)
      | |- apply_zeros ?m [(?a, ?n)] x = _ => peel_by (apply_zeros1_out a n m x) ltac:(uaddr; alia)
      | |- apply_zeros ?m [] x = _ => rewrite (apply_zeros0 m)
      end
    | (* [comment removed for export] *)
      match goal with
      | HWb : mwin _ ?m0 _ _ ?mb |- ?mb x = _ =>
          peel_by (proj1 HWb x) ltac:(uaddr; alia)
      end
    | (* [comment removed for export] *)
      match goal with
      | Hj : forall a : word, _ -> ?m1 a = ?m0 a |- ?m1 x = _ =>
          peel_by (Hj x) ltac:(uaddr; alia)
      end
    | (* [comment removed for export] *)
      match goal with
      | Hp : forall a : word, _ -> _ -> ?m1 a = ?m0 a |- ?m1 x = _ =>
          peel_by (Hp x) ltac:(uaddr; alia)
      end ].

(* [comment removed for export] *)
Ltac peel_at x :=
  lazymatch goal with
  | |- ?l = ?r => tryif constr_eq l r then reflexivity else peel1 x
  end.
Ltac peel x := repeat (progress (peel_at x)).

(* [comment removed for export] *)
Lemma nn_rew : forall (u v : option byte), u = v -> v <> None -> u <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01uh11Hh22H0h31vp;1p;3p;6g002Fj10Tg003Pj17Tg003nj14Tg004Qj13Tg006Wj31Tg00_0j16Tg01G]j12Tg001Hj65Tg00J8#0#0#0#7#4R0#3R1f1R2f0R3511P1P2f2R4%60R0511#2A1120#2R0[X01P3X10P4P3E5W2X31W0o"). Qed.
Ltac nn_by L side := eapply nn_rew; [ apply L; side | ].
Ltac nn_at x :=
  repeat first
    [ lazymatch goal with
      | |- wbytes _ _ _ x <> None => apply wbytes_nn
      | |- unfill ?a ?n ?m x <> None => nn_by (unfill_out a n m x) ltac:(uaddr; alia)
      | |- zfill ?a ?n ?m x <> None => apply zfill_nn
      | |- apply_zeros ?m [(?a, ?n)] x <> None => apply apply_zeros1_nn
      | |- apply_zeros ?m [] x <> None => rewrite (apply_zeros0 m)
      end
    | match goal with
      | Hn : forall a : word, in_frame _ _ a -> ?m1 a <> None |- ?m1 x <> None =>
          apply Hn; unfold in_frame; uaddr; alia
      end
    | match goal with
      | HWb : mwin _ _ _ _ ?mb |- ?mb x <> None =>
          first [ apply (proj2 HWb); uaddr; alia
                | nn_by (proj1 HWb x) ltac:(uaddr; alia) ]
      | Hn : forall a : word, (?lo <= bv_unsigned a < ?hi)%Z -> ?m1 a <> None |- ?m1 x <> None =>
          first [ apply Hn; uaddr; alia
                | match goal with
                  | Hp : forall a : word, _ -> _ -> m1 a = ?m0 a |- _ =>
                      first [ nn_by (Hp x) ltac:(uaddr; alia)
                            | destruct (Z_lt_le_dec (bv_unsigned x) lo);
                              [ nn_by (Hp x) ltac:(uaddr; alia)
                              | destruct (Z_lt_le_dec (bv_unsigned x) hi);
                                [ apply Hn; uaddr; alia
                                | nn_by (Hp x) ltac:(uaddr; alia) ] ] ]
                  end ]
      | Hj : forall a : word, _ -> ?m1 a = ?m0 a |- ?m1 x <> None =>
          nn_by (Hj x) ltac:(uaddr; alia)
      | Hp : forall a : word, _ -> _ -> ?m1 a = ?m0 a |- ?m1 x <> None =>
          nn_by (Hp x) ltac:(uaddr; alia)
      end ].

(* [comment removed for export] *)
Definition frame_base (F : Z) (m : word -> option byte) : Prop := True.

Ltac mark_frame F :=
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst _ _ ?m _) _) _ => pose proof (I : frame_base F m)
  end.

Ltac frame_facts HW mnew :=
  try (lazymatch goal with
       | HPm : frame_base ?F ?mmP |- _ =>
           lazymatch type of HW with
           | mwin _ _ ?sp0 ?D0 _ =>
               let H1 := fresh "Hfr" in let H2 := fresh "Hnnf" in
               let x := fresh "x" in let Hx := fresh "Hx" in
               try (assert (H2 : forall x : word, in_frame sp0 D0 x -> mnew x <> None)
                      by (intros x Hx; unfold in_frame in Hx; nn_at x));
               try (assert (H1 : forall x : word, in_frame sp0 F x -> mnew x = mmP x)
                      by (intros x Hx; unfold in_frame in Hx; peel x))
           end
       end).

(* [comment removed for export] *)
Ltac win_same :=
  lazymatch goal with
  | |- forall a : word, _ -> ?m1 a = ?m0 a =>
      let x := fresh "x" in let Hw := fresh "Hw" in
      intros x Hw; uaddrH Hw; peel x; try reflexivity
  end.

(* [comment removed for export] *)
Ltac win_pres :=
  lazymatch goal with
  | |- forall a : word, _ -> _ -> ?m1 a = ?m0 a =>
      let x := fresh "x" in let Hw := fresh "Hw" in let Hf := fresh "Hf" in
      intros x Hw Hf; uaddrH Hw; uaddrH Hf; peel x; try reflexivity
  end.

(* [comment removed for export] *)
Ltac win_nn :=
  lazymatch goal with
  | |- forall a : word, _ -> ?m1 a <> None =>
      let x := fresh "x" in let Hf := fresh "Hf" in
      intros x Hf; uaddrH Hf; nn_at x
  end.

(* [comment removed for export] *)
Ltac frame_ok :=
  lazymatch goal with
  | |- store_ok _ ?m ?a ?n = true =>
      apply store_ok_of_all; [ uaddr; alia |];
      let x := fresh "x" in let Hx := fresh "Hx" in
      intros x Hx; uaddrH Hx;
      let Hs := fresh in
      assert (Hs : m x <> None) by nn_at x;
      unfold wview; destruct (m x); [discriminate | exfalso; apply Hs; reflexivity]
  end.

(* [comment removed for export] *)
Ltac base_mem m :=
  lazymatch m with
  | wbytes ?m0 _ _ => base_mem m0
  | unfill _ _ ?m0 => base_mem m0
  | zfill _ _ ?m0 => base_mem m0
  | apply_zeros ?m0 _ => base_mem m0
  | ?v => v
  end.

Ltac find_store m a k :=
  match m with
  | context [wbytes ?m0 a ?bs] => k constr:(wbytes m0 a bs)
  | _ =>
      let v := base_mem m in
      first
        [ match goal with
          | Hf : forall y : word, in_frame _ _ y -> v y = ?M y |- _ => find_store M a k
          end
        | match goal with
          | Hj : forall y : word, _ -> v y = ?M y |- _ => find_store M a k
          | Hp : forall y : word, _ -> _ -> v y = ?M y |- _ => find_store M a k
          end ]
  end.

Ltac peel_to T x :=
  repeat (lazymatch goal with
          | |- T x = _ => fail
          | |- _ => peel1 x
          end);
  reflexivity.

Ltac frame_rd :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a (word_to_le_bytes 8 _)) ?a 8%nat = Some _ =>
      apply rdn_wbytes_hit8; uaddr; alia
  | |- rdn ?segs ?m ?a ?n = Some _ =>
      first
        [ match goal with H : rdn _ m a n = Some _ |- _ => exact H end
        | find_store m a ltac:(fun T =>
            rewrite (rdn_ext segs n m T);
            [ apply rdn_wbytes_hit8; uaddr; alia
            | rewrite ?length_w2l; uaddr; alia
            | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; uaddrH Hx; peel_to T x ]) ]
  | |- ?g => fail "frame_rd:" g
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zsum_norm :=
  repeat match goal with
  | |- context [v_addi _ ?z] =>
      lazymatch z with
      | (?a + ?b)%Z => check_closed_term z; let z' := eval vm_compute in z in change z with z'
      end
  end.
Ltac spaddr := regnorm; imm_norm; rewrite ?v_addi_addi'; zsum_norm.

Ltac mach_stk_st Hp HS Hag HI :=
  cur_instr ltac:(fun w i =>
    let go L :=
      eapply rz_step_p; [ mpure Hp | reflexivity
        | eapply L; [ solveF | reflexivity | solveD
                    | spaddr; reflexivity
                    | regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity
                    | frame_ok ]
        | mpost HS ];
      (* [comment removed for export] *)
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst _ _ (wbytes ?m ?a ?bs) _) _) _ =>
          apply (magree_wbytes_win _ m a bs) in Hag;
          [ | rewrite length_w2l; uaddr; alia
            | cbn [ms_lo ms_hi upd]; uaddr; alia
            | rewrite length_w2l; cbn [ms_lo ms_hi upd]; uaddr; alia ]
      end in
    lazymatch i with
    | Store SZ8 _ _ _ => go step_sd_at
    | Store SZ4 _ _ _ => go step_sw_at
    | _ => fail "mach_stk_st:" i
    end).

Ltac mach_stk_ld Hp HS Hag HI :=
  cur_instr ltac:(fun w i =>
    lazymatch i with
    | Load SZ8 true _ _ _ =>
        eapply rz_step_p; [ mpure Hp | reflexivity
          | eapply step_ld_at; [ solveF | reflexivity | solveD | reflexivity
                               | spaddr; reflexivity
                               | frame_rd
                               | apply bytes_le_to_Z_8 ]
          | mpost HS ]
    | _ => fail "mach_stk_ld:" i
    end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma callee_saved_of_num : forall r : reg, cs_num (bv_unsigned r) = true -> callee_saved r.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01Hh12H0h21nh32b1h42b2h51mh62H1h72H2h84__x1h97__arithh:4__ffh;8__varmaph<5__with=1rp;1p;2p;3p;4p;7p;8g002Fj1FTg002kj1ATg003Pj1[Tg003nj1>Tg00BZj22Tg01M8j1^Tg01UUR0j23Tg01\^j2XTg009nj1=Tg01O[j24Tg01VQj26Tg01U7j2ITg00;Oj3ETg01Qhj2ZTg006Wj30Tg021gj3YTg022Kj3CTg022ej3BTg00kMj27Tg01ajj3VTg019UR1j2GTg01]>j2UTg00@Rj1RTg001fj1QTg010mj2PTg012Gj1OTg012ej1STg013Pj2TTg0143j2NTg01:0j4MTg00_0j1fTg01XOj7eTg0159j2dTg00Ffj2cTg015[j2bTg016Gj3]Tg016fj4_Tg01L5j1`Tg01WNj2DTg01:[j7\Tg01;?j8aTg00J]R2f0R3g00RXR430p=1f1R5/D3=024p=Jf4R6f3R7f2R8'4'D1453'Dp=<1485/D3p=?1453,D8=024p=;f6R9f5R:;0617781753'G'3p=:A09:6A0785/33'3p=51453=024p=8g00LIR;?053p=917781753'Gp=HAB8539B67p=@1753,G8p=WP5g01<JR<g01<iR=P=g01=IR>P3g01=iF\p=LP7P<P=P=P>P8P5P3Gap=Kg00J8R?#FR@#A#[RA#>RB12A3#^#1P11J53%18RC%15RD'3[RE%13,3D1J85RD[%17/3C\D1X53P5n2001000000120000000X42X32RDPE^42^32REP312A8RC%=@RF'4PC%A?RG#=RHPC%F@R@#=RID<PC%F@#=RJPC%A@R@#=RKD<RL%F@#=R@/6C%FG#A#A#=RG,6C'IRCP5O3%1L%1C'3P012A7RC14CH7?FPCPIPCPJD<?;CK16@C16CG'I#1PBP6g00N1RC9EAFRLPBP6AEAHCRMPBP6AEAICRNPBP6AEAJCROPBP6AEAKCRCP@12A6RPPPPGF:F5F5P314PH9?PFPPPIPPPJD<?;PKPDPEP312A9R9149H7?FP9PIP9PJD<RQ149KRRP5O3%1Q%1R'3P0f7RR,2ARQ/4FPQPHPQPID<?;QJ18QKPBf8RSPLPBPSPMPBPSPNPBPSPOPBPSPCP@12ASRSPSPGF:F5F5P314SFPSPHPSPID<?;SJPDPEP3f:,2ART/4FPTPHPTPID<RU14TJRVP5O3%1U%1V'3P0f;RV,2ARU14UH7?F?;UI18UJPBf<RWPLPBPWPMPBPWPNPBPWPOPBPWPCP@12AWRXPXPGF:F5F5P314XH9?XF?;XIPDPEP3f>RY,2ARZ14ZH7?FR[14ZIR\P5O3%1[%1\'3P0f?R\,2AR[/4F?;[H18[IPBf@R]PLPBP]PMPBP]PNPBP]POPBP]PCP@12A]R^P^PGF:F5F5P314^F?;^HPDPEP3fB,2ARE/4FRD14EHR_P5O3%1D%1_'3P0fCR0,2AR_/8F18_HPBfDRDPLPBPDPMPBPDPNPBPDPOPBPDPCP@12ADR`P`PGF:F5F5P318`FP118531985[Ra19531885Rb[1978\b1Z53P5n2001000000120000000X5;X2;RbPa^5;^2;RaP3fF,2ARcPFP5O319cFfGRF=0BLRdA0BFMRePBPFPNPBPFPOPBPFPCP@12AFRFPFPGF:F5RF'3Rfg023?Rg%>3Rh%>5RiP1%>8?05312781275'9Rj[12851283'9%>7?085[Rk%>6?078\jAY853P3n2001000000120000000W4W3W2RjPk^4i^3h^2gRgP3PAfHRhPLP5O4b13Cb0b1W0P3O118`HPbPaP3PcPHP5O319cHPjPgP3PAPhPMP5O4b19CeF9Bdfb0b1W0P3O1n200100000021100011000b0b1W0P3O118^IPbPaP3PEPIP5O319EIA0B0LA0B0MREA0B0NRIPBP0POPBP0PCP@P_P_PGCHF5R_'3R0'3PEP0PjPgP3PAPDPNP5O4b19CI_D@b0b1W0P3O1n200100000021100011000b0b1W0P3O118XJPbPaP3PZPJP5O319ZJA0B\LA0B\MRJA0B\NRXA0B\OR_PBP\PCP@P[P[PGF:R\'3RI'3RD'3PJPDPjPgP3PAP]POP5O4b19C_\9BXID@b0b1W0P3O1n200100000021100011000b0b1W0P3O118SKPbPaP3PTPKP5O319TKA0BVLA0BVMRTA0BVNRKA0BVORaA0BVCRV17@URb?WUGRI'3RX'3R\'3R_'3PTP_PKP\PaPXPjPgP3PAPWPCP5O4b19CVID@D@b0b1W0P3O1n200100000021100011000b0b1W0P3O116@P16PG'I#112A:R:,6@RP16:GR:;V3%1P%1:'GP116@9#1169G#1PBPRPLPBPRPMPBPRPNPBPRPOPBPRPCP@PQPQPGF:F5F5P316@S#1f9,2A/6G#1P11653#11785[R117531685#1RS[1778\S1U53P5n2001000000120000000X5;X2;RSP1^5;^2;R1P3P@PUP8O3PbPSP1P3f=,2ARAPGP7O317AGA0BYLA0BYMRMA0BYNRNA0BYOROA0BYCRYP@PZPZPGCHRZ'3RC'3RB'3RL'3PMPLPNPBPOPCg01?mRC#R%QC1P;5%O;%S;RCP;1T;?R?g01;cRO1N;GCM,LCRB%f=RNPCP;1N;@POP?CM,LCR?PNPCP<P=P=P>P?PBFeCKCK1dC>P3P81c241b38#1dg00MS=];5C_b:b;b<X8;173G17@5P@P8P8PGCH[[^8;P3P[P5P7O3b99BYZD@D@b7b0b6b0W7W6P5P3O2n2001000000121000000b0W0P3O1n200100000021100011000b0b1%`5eW0W=o"). Qed.

(* [comment removed for export] *)
Ltac cs_facts Hcs :=
  let one z :=
    let r := constr:(@BV 5 z I) in
    try (let H := fresh "Hk" in
         assert (H : getr _ r = getr _ r) by (apply Hcs; apply callee_saved_of_num; reflexivity)) in
  one 2%Z; one 3%Z; one 4%Z; one 8%Z; one 9%Z; one 18%Z; one 19%Z; one 20%Z; one 21%Z;
  one 22%Z; one 23%Z; one 24%Z; one 25%Z; one 26%Z; one 27%Z.

Lemma sp_mod16 : forall (sp : word) (k : Z),
  bv_unsigned sp mod 16 = 0 -> k mod 16 = 0 -> 0 <= bv_unsigned sp + k < 2^64 ->
  bv_unsigned (v_addi sp k) mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01zh12Hah21Hh32H0h42H1h53H10h62H2h72H3h82H4h92H5h:2H6h;2H7h<2H8h=2H9h>2Hkh?2Hrh@2HshA7__arithhB4__ffhC6__sat0hD6__sat1hE6__sat2hF6__sat3hG8__varmaphH5__withI1khJ1qhK2q0hL1rhM2r0hN2spp;1p;2p;6p;3p;4p;7g002Fj16Tg003Pj1ZTg003nj1OTg00BZj21Tg009nj1<Tg023]j20Tg01]^j24Tg00kij2MTg00moj23Tg019UR0j29Tg00Ffj2CTg001Hj6:Tg024=j2ETg00mGj2VTg00nKj3UTg024nj2DTg01G]j1TTg025Oj28Tg025lj2BTg006Wj37Tg026Ij2ATg0270j2@Tg00kMj2;Tg027Wj2?Tg028=j2>Tg00@Rj1NTg001fj1LTg011Kj1KTg012Gj1JTg012ej1ITg0143j2=Tg01:0j4HTg01:[j7GTg028cj6PTg0159j2QTg015[j2FTg016Gj3RTg016fj4STg029Gj4YTg00>@j2XTg029hj3WTg00LIR1f0R2g00MSR337p=51;32p=2g00J8#6R4#6#6#6R5#6#6R6#ZR7#Of1R8,17%<5R5'0#51085#5f3R9,17f2R:'4R;#2%<4R4%<6R6'MR<,3;'9P1f4R;,17R=/49R>1025#5X01P110=5R?1095R@'4/05%52X01P1P310;5,42/05#5X01P1P31432/05#5X011C13P@P8E:P?P:E:10>5P=P9P51E=5%2=%25R=f6R>,17/05#2[[1V461334%26133<[[%24R?g01?QR@AU468UW1%2<\@^1?1E>5%2>f8R>/05R?#2\=[f7/D5%55R=#TR@18>5,B5/4?971>[1A>51335R>f9R?/05R6#21365'9[1@?51353R?f:R6/05R4,351;43'9[1?65f;R6/85#5\=1>65f<R6/05=716\=1865P1f=/05P1f?,17/D5f@,17R61865,B51065'4571\@1A65fA,17R6/05R4#21345'9\>1@65fBR6,17R>/05R4,351;43'9\?1?>5fC,17R>/85#5\=1>>5fD,17R>/05=71>\=18>5P1fER>,17/05P1P0fF,17/4>R>#213><P@P6fHR6,17fG'4#2fI,17/46/3<g01?mR<#N%L<%K1%J1%I1R<g01<JR6g01<iR@P@g01=IR>P<P6P@P@P>P11=15g02:m1=13CHg01=iFGEP1Q<>P2P:g00J]R>g00RXR<'C1F2:=7><dAR138CSbBbGbHg01KX\=P2bAW5W=P8P2O2n2001000000120000000bMbKb<b;b:b9b8bLbJb7b6b4b3b2bCbDbEbFCYE:1X;9,17AW;92E:W?W>W@XI1WNo"). Qed.

(* [comment removed for export] *)
Ltac call_side Hp Hag HI HW HS :=
  lazymatch goal with
  | |- md_pure _ => mpure Hp
  | |- ms_vm _ = m_vmmaps _ => symmetry; apply with_vmmaps_vmmaps
  | |- magree _ _ => exact Hag
  | |- wtop _ => exact (minv_ceil _ _ HI)
  | |- getr _ _ = _ => regnorm; imm_norm; rewrite ?v_addi_addi', ?v_addi_0; first [reflexivity | klitsg; first [reflexivity | bveq]]
  | |- bv_unsigned _ mod 16 = 0 => first [assumption | apply sp_mod16; [assumption | reflexivity | uaddr; alia]]
  | |- ret_ok _ => first [assumption | apply ret_ok_even; vm_compute; reflexivity]
  | |- tsafe _ _ => first [ exact HS | exact (tsafe_bind_inv _ _ _ HS) ]
  | |- forall a : word, _ -> ?m a <> None => win_nn
  | |- context [alloc_ceiling] => rewrite alloc_ceiling_val; uaddr; alia
  | |- _ => uaddr; alia
  end.

(* [comment removed for export] *)
Ltac call_intro Hag HI HW HS :=
  let r := fresh "cr" in let s' := fresh "s" in let mm' := fresh "mm" in let R' := fresh "R" in
  let HP := fresh "HS" in let Hag' := fresh "Hag" in let Hlo' := fresh "Hlo'" in let Hhi' := fresh "Hhi'" in
  let Hr1 := fresh "Hres" in let Hr2 := fresh "Hres" in let Hsp := fresh "Hsp" in
  let Hcs := fresh "Hcs" in let Hpres := fresh "Hpres" in let Hnn := fresh "Hnn" in let HInew := fresh "HI" in
  let Htop' := fresh "Htop'" in let Hwk := fresh "Hwkeep" in
  first
    [ intros r s' mm' R' HP Hag' Hlo' Hhi' Htop' Hr1 Hsp Hcs Hpres Hnn Hwk;
      lazymatch type of Hwk with forall x : reg, wreg _ x = false -> _ => idtac end;
      keep_facts Hwk
    | intros r s' mm' R' HP Hag' Hlo' Hhi' Htop' Hr1 Hsp Hcs Hpres Hnn;
      lazymatch type of Hnn with forall a : word, _ -> _ <> None => idtac end
    | intros r s' mm' R' HP Hag' Hlo' Hhi' Htop' Hr1 Hr2 Hsp Hcs Hpres Hnn;
      lazymatch type of Hnn with forall a : word, _ -> _ <> None => idtac end;
      destruct r as [?r1 ?r2]; cbn [fst snd] in Hr1, Hr2, HP |- * ];
  cbv beta in HP; rewrite with_vmmaps_twice; cbv beta;
  pose proof (minv_same _ _ _ HI Hlo' Hhi' Htop') as HInew;
  cbn [ms_lo ms_hi ms_mem ms_vm upd] in Hsp;
  cbv delta [ALLOC_STACK] in Hpres, Hnn;
  uaddrH Hpres; uaddrH Hnn;
  clear Hlo' Hhi' Htop'; clear HS Hag HI; rename HP into HS; rename Hag' into Hag; rename HInew into HI;
  note_win HI;
  frame_facts HW mm';
  cs_facts Hcs;   (* [comment removed for export] *)
  mnorm HS.

(* [comment removed for export] *)
Ltac mach_call Hp HS Hag HI HW THM :=
  mach_jal Hp HS;
  apply rz_bind_shape;
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R ?pc ?mm ?rom) (with_vmmaps _ ?md)) (tshape (_ ?s) _) =>
      eapply rz_at_pc;
      [ eapply (THM (with_vmmaps (ms_vm s) md) R mm rom s);
        first [ lazymatch goal with |- forall (r : _) (s' : mstate), _ => call_intro Hag HI HW HS end
              | call_side Hp Hag HI HW HS ]
      | bveq ]
  end.

(* [comment removed for export] *)
Lemma v_addi_back : forall (x : word) (a b : Z), a + b = 0 -> v_addi (v_addi x a) b = x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01bh11Hh21ah31xh41zp;1p;2p;3p;6g002Fj10Tg003Pj18Tg003nj15Tg01]^j23Tg006Wj32Tg00>@j21Tg02;Tj17Tg001Hj64Tg02<Qj36Tg00J8#0#0#0#0#0#0#8#5R0g00LIR1f1R2f0R3'3g00MSR4521P0f3R5f2R6/32R7'1f4R89203X00P1P41183=208X41%75P7P3E41156/12A6562E4W1X01W2W3o"). Qed.

Lemma v_addi_k0 : forall (x : word) (k : Z), k = 0 -> v_addi x k = x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01kh11Hh21xp;1p;3p;2p;6g002Fj10Tg003Pj16Tg003nj12Tg006Wj31Tg00>@j25Tg02;Tj14Tg001Hj63Tg00J8#0#0#0#0#0#0#6#2R0g00LIR1f0R2g00MSR3511P1P3f3R3/52=103X01f2#4f1P2E3W1W0W2o"). Qed.

Lemma not_cs_neq : forall (x r : reg), callee_saved x -> ~ callee_saved r -> x <> r.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h02Hxh11xh21Hh32Hrh41rp;1p;3p;7g002Fj17Tg002kj16Tg003Pj13Tg003nj12Tg01L5j10Tg01G]j11Tg006Wj35Tg001Hj74Tg00J8#7#6#3#2R0f1#0R1%11f3R1f2R2550R3P0P1f0R4#0g01KX]0X10%01P2P4O1W0f4P4P2F4W2%13eW3W0X40W1o"). Qed.

(* [comment removed for export] *)
Lemma callee_saved_cs_num : forall r : reg, callee_saved r -> cs_num (bv_unsigned r) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01Hh11Eh24__p1h34__x1h42b1h52b2h67__arithh74__ffh88__varmaph95__with:1mh;1nh<1rh=2Hch>1Rp;1p;3p;2p;6p;4p;7p;8g002Fj1@Tg002kj1ATg003Pj1VTg003nj1LTg01L5j1cTg009nj1:Tg00;Oj3>Tg006Wj34Tg00BZj21Tg01O[j27Tg01VQj20Tg01U7j26Tg00Ffj2XTg001Hj6?Tg00kMj22Tg01UUR0j2=Tg01\^j2UTg019UR1j2<Tg02=Zj2TTg01]>j2RTg00@Rj1QTg001fj1PTg010mj2OTg012Gj1NTg012ej1MTg0143j2ETg013Pj2KTg01:0j4FTg01Wkj6JTg00_0j1ITg0159j2STg015[j2bTg016Gj3aTg016fj4`Tg01AEj4[Tg022ej3YTg01M8j1ZTg01WNj2CTg01:[j7WTg01XOj7^Tg01;?j8_Tf3R2f2R3'2f1R4f0R5'2'<p=;f6R6f5R7f4R834A4234/=5'=p=91723,C81745'Cp=5g00J]R91C45g00RXR:34p=8A47821234/<5'=p=BA495:p=3P4g01<JR;g01<iR<P<g01=IR=P5g01=iFWp=DP3P;P<P<P=P4P5F^p=GP2P;P<P<P=P3P4P5G_p=H1234/<5p=]1245,<3p=\g00J8R>#@R?#A#VR@#LRA%c5P0%:?RBg00N1RC5>@RD94A4PAP4%A>RE#:RF=>@CRGPAP4%@?R?#:RH=>@CRIPAP4%@?#:RJ=>@CRKPAP4%A?R?#:RL=>@CRC%@?#:R?11@4RMPM%@E#A#A#:REC;F9F911@3RN/7BPNPFPNPHD5PNPJPNPLD510?N10NE'6'8P5A4A3DPAPD11@5RD/7BPDPFPDPHD5PDPJPDPLD510?D10DE'6'8X<ARD1X9:R:P2P5E?W1P5O1PAP3PGPAP3PIPAP3PKPAP3PCP?PNPNPEC;F9F9P0A4A2GPAP2PIPAP2PKPAP2PCP?11@2RN12NEEBF911@8RN/7BPNPFPNPHD5PNPJPNPLD510?N10NE'6'8P5A4A8GPAPGPDP:P7P5E?W1P5O1PAP8PIPAP8PKPAP8PCP?PN12NEEBF9P0A4A7IPAP7PKPAP7PCP?11@7R7P7PEC;F911@6R7/7BP7PFP7PHD5P7PJP7PLD510?7107E'6'8P5A4A6IPAPIPDP:f7RIP5E?W1P5O1PAP6PKPAP6PCP?P7P7PEC;F9P0A4AIKPAPIPCP?11@IRI12IEEBf8RI,1@R7/7BP7PFP7PHD5P7PJP7PLD510?7107E'6'8P5A4AIKPAPKPDP:f9RKP5E?W1P5O1PAPIPCP?P7127EEBP0A4AKCP?11@KRKPKPEC;f:RK,1@R0/7BP0PFP0PHD5P0PJP0PLD510?0100E'6'8P5A4AKCPAPCPDP:f;P5E?W1P5O1P?P0P0PEC;P11845%33R0%34RD'=RC[%35RA,=D1834[RK1823\C1U45P5n2001000000120000000X59X49PK^59^49P5f<,1@RK/7BPKPFPKPHD5PKPJPKPLD5RL10?K10KE'6RK%3L%3KP11645#31<0DR0[1<DA1634#3[RA1623#3\01T45P5n2001000000120000000X59X49PA^59^49P5f=,1@R9,0?RA109ER9%3A%39g00LIR9P11045#31234R1[12451034#3[RA1023#3\11R45P5n2001000000120000000X:9W;R1PA^:9^;9RAP5P?f>,1@R0p-0RDg01?mRK#QRL%PKRK1O94RJ%N9RH%M9RFP91E9?g01;cRB1K9>R>CF,DFRCPFP;P<P<P=P2EJR25GF%I<R<PCCH1SF=R=P5P3P:1b53#3dg00MS=a94C`R3b7b8b9X39W2A]?5412?4[^39^2DP5f?,1@R@/2EP@P8O3b6O3b0P1PAP5P0PEPLPKPJPHPFP9P>PB1E9ECF,DFRB9GF2P<PBCHP=P3b7b8b9X39X2DA\45E124E[^39^2DP512?@P@P8O3b6O3b0C[O3b03YO3b0W>P5O1n200100000021000011000W0P5O1n200100000021000011000W0P5O1n200100000021000011000W0P5O1n200100000021000011000W0P5O1n200100000021000011000%ZM#3eW=W<o"). Qed.
Lemma not_callee_saved_of_num : forall r : reg, cs_num (bv_unsigned r) = false -> ~ callee_saved r.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "p'0h01Hh12H0h22Hch31bi001bh41eh51rp;1p;2p;3p;6g002Fj1;Tg002kj1:Tg003Pj17Tg003nj14Tg00BZj23Tg01M8j11Tg006Wj30Tg01L5j16Tg02>;j25Tg00gfj62Tg01J:j28Tg01G]j19Tg00J8#;#:#7R0#4g00J]R1f0R2,30#1g00K=R330f1R4#6R5P1f2R6,30#1A0123X31P4g00RXR41562E2A0143P1P4P1p-0P2g01?Qg01KXR4n0110000020000X41g00N1P3P2E2P41842b1b0W2%95eW0W5o"). Qed.

(* [comment removed for export] *)
Ltac not_cs :=
  first [ apply not_callee_saved_of_num; reflexivity
        | unfold callee_saved; let HH := fresh in intros HH;
          repeat (destruct HH as [HH|HH]; [apply (f_equal bv_unsigned) in HH; cbv in HH; discriminate HH|]);
          revert HH; imm_norm; lia ].

(* [comment removed for export] *)
Ltac cs_chain Hx :=
  repeat match goal with
  | |- ?a = ?a => reflexivity
  | |- getr (regupd ?R ?r ?v) ?x = _ =>
      rewrite (getr_other R r v x (not_cs_neq x r Hx ltac:(not_cs)))
  | Hk : forall r : reg, wreg ?wl r = false -> getr ?R1 r = getr _ r |- getr ?R1 ?x = _ =>
      rewrite (Hk x (wreg_cs wl x Hx eq_refl))
  end;
  reflexivity.

Lemma cs_enum : forall x : reg, callee_saved x ->
  x = 2%bv \/ x = 3%bv \/ x = 4%bv \/ x = 8%bv \/ x = 9%bv \/ x = 18%bv \/ x = 19%bv \/ x = 20%bv \/ x = 21%bv \/ x = 22%bv \/
  x = 23%bv \/ x = 24%bv \/ x = 25%bv \/ x = 26%bv \/ x = 27%bv.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h02H0h11zh21Ch31Hh44__x1h57__arithh64__ffh78__varmaph85__with92b1h:2b2h;1nh<1xh=1Eh>2H1h?2Hxp;1p;3p;2p;6p;4p;7p;8g002Fj1:Tg002kj1=Tg003Pj1gTg003nj1HTg01L5j1uTg009nj17Tg006Wj30Tg00BZj23Tg00Ffj2GTg022Kj3BTg001Hj6DTg00kMj2?Tg01UUR0j22Tg021gj3dTg00CDj2VTg01nmj2UTg02?Kj1cTg00moj2KTg02@Hj1bTg023]j2aTg00@Rj1`Tg001fj1_Tg010mj2^Tg012Gj1]Tg012ej1\Tg013Pj2[Tg00_0j1tTg0143j2NTg01:0j4ITg0159j2sTg015[j2rTg016Gj3qTg016fj4pTg02A1j3oTg020?j2nTg00;Oj3hTg019UR1j2STg022ej3LTg01:[j7JTg01XOj7fTg01;?j8eTg01fNj7TTf1R2f0R3g00N13hp=8f3R4f2R5'?1?23'Sp=@f6R6f5R7f4R830A0452/23'2p=11223,25p=9A0784A0523'2p=>A0452/23p=MA07841252;L3p=;1S23,25p=WAB5239L84p=EAL5239L84p=4g00LIR9?023p=51?52/S3p=R1N93p=QP9P2g01;cP3CIp=PP2g01<JR:g01<iR;P;g01=IR<P3g01=iR=FJp=OP5P:P;P;P<P2P3Ffp=ZP4P:P;P;P<P5P2P3Gep=YP9P8P41G95P2P3EDp=<P9P8P4P5P2P3EDp=mP9P2g02:mR>P3CIp=lP9P2P>1N93CIp=kP5P:P;P;P<P9P2P>P3CIP=FJp=jP8P:P;P;P<P4P:P;P;P<P9P5P>1N92CIP=FJP3FTp=FP6P:P;P;P<P7P:P;P;P<P8P=FJP4P:P;P;P<P5P:P;P;P<P2P=FJP3FTFTp=if7R==096A0978A0945A0923'2'2'2p=CA0984A0952/23'2p=6A0978A0945A0923'2'2p=AA0945A0923'2p=Xg00J8R:#:R>#=R?#gR@#HRA%u3P0%7>,8@RB90A2PAP2%=:RC#7,8@RDPAP2%:>R>#7,8@REPAP2%:>RF#7,8@RGPAP2%=>R>#7,8@RH%:>#7RI13@2RJPJ%:CRC#=RJ#=#7RKC@F1F1A0A5BRLA0A5DRMA0A5ERNA0A5GROA0A5HRP18@IRQ90A5PAP5%=>#7R>,8@RRPAP5%:?RS#:#7RT,8@RUPAP5%=S#7RS,8@RVPAP5%=?R?#:#7RW,8@RXPAP5%=?#7R?,8@RYPAP5%:CRC#:#7RZ,8@R[PAP5%=C#7RC,8@R\PAP5%:J#7RJ,8@R]18@KR^90A5F1F1F1F1393939P3PAPBPAP3PBPAP3PDPAP3PEPAP3PGPAP3PHPAP3PQPAP3PRPAP3PUPAP3PVPAP3PXPAP3PYPAP3P[PAP3P\PAP3P]A0A3^F1F1F1F1F1F1F1X<AR_A0ABBPAPBPDPAPBPEPAPBPGPAPBPHPAPBPQPAPBPRPAPBPUPAPBPVPAPBPXPAPBPYPAPBP[PAPBP\PAPBP]PAPBP^E>F1F1F1F1F1F11GAB3BP4P3EDX3LP3O1PI13@5RLPLPKC@99OP99MNP0A0A4DPAP4PEPAP4PGPAP4PHPI13@4RNPNPKC@CMF1PAP8PBA0A8DRNA0A8ERMA0A8GRPA0A8HROPAP8PQPAP8PRPAP8PUPAP8PVPAP8PXPAP8PYPAP8P[PAP8P\PAP8P]PAP8P^E>F1F1F1F13939CMP3PAPDP_PAPDPBA0ADDRLPAPDPEPAPDPGPAPDPHPAPDPQPAPDPRPAPDPUPAPDPVPAPDPXPAPDPYPAPDP[PAPDP\PAPDP]A0AD^F1F1F1F1F1F1R`1GAD9BL`E;P7P3EDX3NP3O113@8RN,?I1?NK5WO99MPP0A0A7EPAP7PGPAP7PHPI13@7R7P7PKC@F1PAP6PBPAP6PDA0A6ER7A0A6GRPA0A6HRMA0A6QPAP6PRPAP6PUPAP6PVPAP6PXPAP6PYPAP6P[PAP6P\PAP6P]A0A6^F1F1F1F13939F1P3PAPEP_PAPEPBA0AEDROA0AEERNPAPEPGPAPEPHPAPEPQPAPEPRPAPEPUPAPEPVPAPEPXPAPEPYPAPEP[PAPEP\PAPEP]PAPEP^E>F1F1F1F1F1R`'2RLPOPLPNP`1GAEDEE;P=P3EDX37P3O1PI13@6R6P6PKC@99PMP0A0A=GPAP=PHPI13@=RMPMPKC@CMPAf8RMPBPAPMPDPAPMPEA0AMGRPA0AMHR6PAPMPQPAPMPRPAPMPUPAPMPVPAPMPXPAPMPYPAPMP[PAPMP\PAPMP]PAPMP^E>F1F1F1F139CMF1P3PAPGP_PAPGPBA0AGDR7A0AGER`A0AGGRNPAPGPHPAPGPQPAPGPRPAPGPUPAPGPVPAPGPXPAPGPYPAPGP[PAPGP\PAPGP]A0AG^F1F1F1F1F1RL'2RO'2RaP7PaP`PO1GAG9BNLD4E;f9RLP3EDX3PP3O113@MRM,?I1?MK5W6P0A0ALHPI13@LRLPLPKC@PAf:RLPBPAPLPDPAPLPEPAPLPGA0ALHR6A0ALQPAPLPRPAPLPUPAPLPVPAPLPXPAPLPYPAPLP[PAPLP\PAPLP]A0AL^F1F1F1F139F1F1P3PAPHP_PAPHPBA0AHDR_A0AHERMA0AHGRPA0AHHRNPAPHPQPAPHPRPAPHPUPAPHPVPAPHPXPAPHPYPAPHP[PAPHP\PAPHP]PAPHP^E>F1F1F1F1RO'2R`'2Ra'2R7P_P7PMPaPPP`PNPO1GAHDED4E;f;ROP3EDX36P3O1PI13@LRLPLPKC@g023?RL%H3R6%H2RNP1%H5?02313451342'5R`[13521353'5%H4?052[RP%H8?045\`Ad523P3n2001000000120000000W:W9W;R`PP^:N^96^;LRLP3P@f<R613@6RN,V@RP1U@Nf=,3@R4/53X19%c6g00MSR6%:F#:#7RF,KN7RNP4f>R8,3@Ra/53X19P4%b@RM,a4P11?641K4F1KaF9R6aP3f?R1,3@R7,?6f@R_,3@Rb/KFg01?mRc#`Rd%_cRc1^92Re%]9Rf%\9Rg%QIRh1[9:R:'P,Og%QKRi,P:,Og5ZgRj%t;R;1N96/P:,OgP9P:g01Y3%QFCI,Og5ZgCY1sg<R<P3P5g00J]Rkg00RXRl'G1r35=0kldAq962CpRlb6b7b8X49PIP3P3PKC@Rk1K2F9R62[^49P3fBR6,3@RFP=O2b5W>W0P2P3O2n20010000001210000009o4MD<1U@4,54eb013@P1n@NDmO4b013@O,V@90AOPdPcPePfPgPjP;PgPg1l:hPgPg1k:>PgPgP:PTPgPgP:PSPgPgP:PWPgPgP:P?PgPgP:PZPgPgP:PCPgPgP:PJAjg:iDFDFDFDFDFDFDFFiCYP<Plb6b7b8X49P2PIP2P>P2PTP2PSP2PWP2P?P2PZP2PCP2PJP2PKGCD6D6D6\k^49P3P4P5O2b5PNPIPNP>PNPTPNPSPNPWPNP?PNPZPNPCPNPJPNPKGCD6D6D6P0154IP4P>P4PTP4PSP4PWP4P?P4PZP4PCP4PJP4PKEAD6D6D6PAP8PBPAP8PDPAP8PEPAP8PGPAP8PHPAP8PQPAP8PRPAP8PUPAP8PVPAP8PXPAP8PYPAP8P[PAP8P\PAP8P]A0A8^F1F1F1F1F1F1F1P315aIPAP1PBA0A1DR8A0A1ER4A0A1GRNA0A1HR5A0A1QRkPAP1PRPAP1PUPAP1PVPAP1PXPAP1PYPAP1P[PAP1P\PAP1P]A0A1^F1F1F1F1R1'2Rl'2R<'2Ri'2R:P8P:P4PiPNP<P5PlP`PLP3P@P_PQPI13@QRI,53X19PIPbP2D<O4b09Bk1D4D4E;W2P3O1PaP>PaPTPaPSPaPWPaP?PaPZPaPCPaPJPaPKEAD6D6D6P0157>P7PTP7PSP7PWP7P?P7PZP7PCP7PJP7PKGCD6D6PAP_PBPAP_PDPAP_PEPAP_PGPAP_PHPAP_PQPAP_PRPAP_PUPAP_PVPAP_PXPAP_PYPAP_P[PAP_P\PAP_P]A0A_^F1F1F1F1F1F1F1P315b>PAfAR_PBA0A_DR7A0A_ERaA0A_GR1A0A_HRkA0A_QRIA0A_RRlPAP_PUPAP_PVPAP_PXPAP_PYPAP_P[PAP_P\PAP_P]PAP_P^E>F1F1F1R5'2R<'2RN'2Ri'2R4'2R:P7P:PaP4P1PiPkPNPIP<PlP5P`PLP3P@P6PRP>13@RR>,53X19P>PFP2D<O4b0DED4D4E;W2P3O1PbPTPbPSPbPWPbP?PbPZPbPCPbPJPbPKGCD6D6P013@_R_/5TP_PSP_PWP_P?P_PZP_PCP_PJP_PKEAD6D6PAP6PBPAP6PDPAP6PEPAP6PGPAP6PHPAP6PQPAP6PRPAP6PUPAP6PVPAP6PXPAP6PYPAP6P[PAP6P\PAP6P]A0A6^F1F1F1F1F1F1F1P315FTPAfCR6PBA0A6DR_A0A6ERbA0A6GR>A0A6HR5A0A6QRlA0A6RR<A0A6URIPAP6PVPAP6PXPAP6PYPAP6P[PAP6P\PAP6P]A0A6^F1F1F1RN'2Rk'2Ri'2R1'2R4'2Ra'2R:P_P:PbPaP>P4P5P1PlPiP<PkP`PLP3P@fDRkPUPT13@URT,53X19PT13@kRTP2D<O4b09BIND4D4D4E;W2P3O1PFPSPFPWPFP?PFPZPFPCPFPJPFPKEAD6D6P013@6R6/5SP6PWP6P?P6PZP6PCP6PJP6PKGCD6PAPkPBPAPkPDPAPkPEPAPkPGPAPkPHPAPkPQPAPkPRPAPkPUPAPkPVPAPkPXPAPkPYPAPkP[PAPkP\PAPkP]A0Ak^F1F1F1F1F1F1F1P315TSPAfERkPBA0AkDR6A0AkERFA0AkGRNA0AkHRIA0AkQR<A0AkRRiA0AkURlA0AkVR1PAPkPXPAPkPYPAPkP[PAPkP\PAPkP]PAPkP^E>F1F1R5'2R4'2R>'2Ra'2Rb'2R:'2R_'2R7P6P7PFP_PNP:PIPbP<PaPiP>PlP4P1P5P`PLP3P@fFR5PVPS13@VRS,53X19PS13@5RSP2D<O4b0DED4D4D4E;W2P3O1PTPWPTP?PTPZPTPCPTPJPTPKGCD6P013@kRk/5WPkP?PkPZPkPCPkPJPkPKEAD6PAP5PBPAP5PDPAP5PEPAP5PGPAP5PHPAP5PQPAP5PRPAP5PUPAP5PVPAP5PXPAP5PYPAP5P[PAP5P\PAP5P]A0A5^F1F1F1F1F1F1F1P315SWPAfGR5PBA0A5DRkA0A5ERTA0A5GR1A0A5HR4A0A5QRlA0A5RR>A0A5URiA0A5VRaA0A5XR<PAP5PYPAP5P[PAP5P\PAP5P]A0A5^F1F1Rb'2RI'2R:'2RN'2R_'2RF'2R7'2R6'2R8PkP8PTP6P1P7P4PFPlP_P>PNPiP:PaPIP`PLP3P@fHRIPXPW13@XRW,53X19PW13@IRWP2D<O4b09B<bD4D4D4D4E;W2P3O1PSP?PSPZPSPCPSPJPSPKEAD6P013@5R5/5?P5PZP5PCP5PJP5PKGCPAPIPBPAPIPDPAPIPEPAPIPGPAPIPHPAPIPQPAPIPRPAPIPUPAPIPVPAPIPXPAPIPYPAPIP[PAPIP\PAPIP]A0AI^F1F1F1F1F1F1F1P315W?PAfIRIPBA0AIDR5A0AIERSA0AIGRbA0AIHR<A0AIQRaA0AIRR:A0AIURiA0AIVRNA0AIXR>A0AIYR_PAPIP[PAPIP\PAPIP]PAPIP^E>F1Rl'2RF'2R4'2R7'2R1'2R6'2RT'2R8'2Rk'2RgP5PgPSPkPbP8P<PTPaP6P:P1PiP7PNP4P>PFP_PlP`PLP3P@fJRlPYP?13@YR?,53X19P?13@lR?P2D<O4b0DED4D4D4D4E;W2P3O1PWPZPWPCPWPJPWPKGCP013@IRI/5ZPIPCPIPJPIPKEAPAPlPBPAPlPDPAPlPEPAPlPGPAPlPHPAPlPQPAPlPRPAPlPUPAPlPVPAPlPXPAPlPYPAPlP[PAPlP\PAPlP]A0Al^F1F1F1F1F1F1F1P315?ZPAfKRlPBA0AlDRIA0AlERWA0AlGR_A0AlHRFA0AlQR>A0AlRR4A0AlURNA0AlVR7A0AlXRiA0AlYR1A0Al[R:PAPlP\PAPlP]A0Al^F1R6'2Ra'2RT'2R<'2R8'2Rb'2Rk'2RS'2Rg'2R5'2RhPIPhPWP5P_PgPFPSP>PkP4PbPNP8P7P<PiPTP1PaP`PLP3P@fLRaP[PZ13@[RZ,53X19PZ13@aRZP2D<O4b09B:6D4D4D4D4D4E;W2P3O1P?PCP?PJP?PKEAP013@lRl/5CPlPJPlPKCXPAPaPBPAPaPDPAPaPEPAPaPGPAPaPHPAPaPQPAPaPRPAPaPUPAPaPVPAPaPXPAPaPYPAPaP[PAPaP\PAPaP]A0Aa^F1F1F1F1F1F1F1P315ZCPAfMRaPBA0AaDRlA0AaER?A0AaGR6A0AaHR:A0AaQR1A0AaRRTA0AaURiA0AaVR<A0AaXR7A0AaYR8A0Aa[RNA0Aa\RbPAPaP]PAPaP^E>R4'2Rk'2R>'2RS'2RF'2Rg'2R_'2R5'2RW'2Rh'2RI'2R;PlP;P?PIP6PhP:PWP1P5PTP_PiPgP<PFP7PSP8P>PNPkPbP4P`PLP3P@fNR4P\PC13@\RC,53X19PC13@4RCP2D<O4b0DED4D4D4D4D4E;W2P3O1PZPJPZPKCXP013@aRa/5J15aKPAP4PBPAP4PDPAP4PEPAP4PGPAP4PHPAP4PQPAP4PRPAP4PUPAP4PVPAP4PXPAP4PYPAP4P[PAP4P\PAP4P]A0A4^F1F1F1F1F1F1F1P315CJfOR4=0ABRBA0A4DRDA0A4EREA0A4GRGA0A4HRHA0A4QRQA0A4RRRA0A4URUA0A4VRVA0A4XRXA0A4YRYA0A4[R[A0A4\R\A0A4]RaA0A4^R4'2RA'2R0'2RZ'2Rb'2Rk'2RN'2R>'2R8'2RS'2R7'2RF'2R<'2RgPDP<PEPFPGP7PHPSPQP8PRP>PUPNPVPkPXPbPYPZP[P0P\PAPaP4P`PLP3P@fPRiP]PJ13@]R],53X19P]13@iR]P2D<O4b0DED4D4D4D4D4D4W2P3O115CKPBPgPDP<PEPFPGP7PHPSPQP8PRP>PUPNPVPkPXPbPYPZP[P0P\PAPaP4P`PLP3P@PiP^PK13@^R^,53X19P^P]P2D<O4b0D4D4D4D4D4D4D4W2P3O1n200100001021100011000W0P3O1n200100001021100011000W0P3O1n200100001021100011000W0P3O1n200100001021100011000W0P3O1n200100001021100011000W0P3O1n200100001021100011000W0P3O1n200100001021100011000W0P3O1n200100001021100011000W0P3O1n200100001021100011000b2b=W3P3O1n200100001021100011000W0P3O1n200100001021100011000W0P3O1n200100001021100011000W0P3O1n200100001021100011000W0P3O1n200100001021100011000W?W<o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kp_skip_w : forall (wl : list Z) (R R2 : bvmap 5 word) (rd : reg) (v : word),
  wreg wl rd = true ->
  (forall x : reg, wreg wl x = false -> getr R2 x = getr R x) ->
  forall x : reg, wreg wl x = false -> getr (regupd R2 rd v) x = getr R x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01xh13Hrdh22Hxh32IHh41Rh52R2h61bh72rdh81vh92wlp;1p;2p;3p;7p;6g001fj1;Tg002Fj10Tg002kj18Tg003Pj14Tg003nj15Tg000\j2:Tg01I9j23Tg006Wj31Tg00<_j22Tg00Cjj37Tg02ATj76Tg001Hj69Tg00LI#;g00J8#0R0#8#4R1%00#0#0#0#0#4#5R0':R2%51R1g00J]R3f4R4f1R5'3g00RX31f6R6f0R7'3g00K=R8513f5R9/251265R:510[^01f7/37=138P0P:f8R:f2R8'29107X60P8P5P7O2A7694/25P:P6P9P4P5f3P7F6E9W2X01W3W1X80W7X52W4W9o"). Qed.
Lemma kp_restore_w : forall (wl : list Z) (R R2 : bvmap 5 word) (rd : reg) (v : word),
  getr (regupd R2 rd v) rd = getr R rd ->
  (forall x : reg, wreg (bv_unsigned rd :: wl) x = false -> getr R2 x = getr R x) ->
  forall x : reg, wreg wl x = false -> getr (regupd R2 rd v) x = getr R x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "p'0h02Hxh11bi001bh21xh32b1h42b2h51ni011nh61Eh71Hh82Hvh92IHh:2NEh;1Rh<2R2h=1ei021eh>2neh?1ri031rh@2rdhA1si041shB1vhC2wlp;1p;2p;3p;6p;7p;5g001fj1NTg002Fj15Tg002kj1BTg003Pj1;Tg003nj14Tg000\j2JTg00Cjj38Tg00<_j22Tg006Wj30j1MTg00BZj21Tg00A2j3:Tg01I9j26Tg02B]j1LTg02CEj6KTg02C]j2ITg01G]j17Tg02D1R0j2HTg001Hj7Cj6>Tg01O[j2<j1GTg01WNj29Tg02DQj2ATg02E3R1j2DTg021gj3ETg01J:j2@Tg00Ffj2FTg01P8j3=Tg01JYj5?Tg00J]R2f0R3g00K=R430p=3g00LIR5#Ng00J8#5R6#B#;R7%56#5#5#5#5#;#4R6'JR8%47R9f2R:f1R;;83/2;f3R</2;506117<f6R=5:5/63#3f5R>/2;12=;506[^29f7R?/63#3A09;>R@P9P9%M9%L7P;P>EK'I%7@,H@P0A09:=R0%70f8R0?8?=/2<f9R@/2<506P3A09<?RAP9P0f<RB/63#3f;RCf:RD;8@/2;12B;506]0X2916C0#3P?W0f4RBP3P<FCW=P3O1%7AP612@B12C>9063X16P>PBP2P4117>117@'<R>/93#3X12117BRA1170RE'AA05AE1<AE'DP>P2P1117=117D50519;4#3P;117?117C505RDg00RX/94#3PBg023?R=%43R1%4;R>g019U%4:?0;311<:11<;505RF[11:;11:3505%4<?0:;[RG%4B?0<:\FAE:;3P3n2001000000120000000W4W3W5PG^4>^31^5=P3P7P@f=P;O4b7O1'@W6P3O1%7D1F24W:P3O1n10210010300021010210101b1b?%GARA==5CP<E>A:5ECRE9=5A#3e16EB#3eO2A8@0?/2BP@P0P?PBP3D?E>W>P3O1n200110400021010211101bAW0X29W9W8XB6W@X<8W;WCo"). Qed.
(* [comment removed for export] *)
Definition noncs_nums : list Z := [0; 1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%Z.
Lemma cs_to_wreg : forall (R R' : bvmap 5 word),
  (forall x : reg, wreg noncs_nums x = false -> getr R' x = getr R x) ->
  forall x : reg, callee_saved x -> getr R' x = getr R x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01xh11Hh22Hxh31Rh42R'p;1p;2p;3p;4g002Fj10Tg002kj1:Tg003Pj13Tg003nj14Tg000\j29Tg01I9j28Tg006Wj31Tg00<_j22Tg01L5j16Tg00Ffj27Tg02EVj45Tg00J8#0R0#:#3R1%00#0#0#0#0#3#4R0'9R2%41R1g00J]R3g02FZR4f0R5'8g00K=31f2R6f1R7'2f3/27510[]0%65P6P7P4P7P5g00RX,73C5O2W2X01W1X42W3o"). Qed.
(* [comment removed for export] *)
Lemma wreg_noncs_cs : forall (wl : list Z) (x : reg),
  forallb (fun z => cs_num z || existsb (Z.eqb z) wl)%bool
          [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%Z = true ->
  wreg wl x = false -> callee_saved x.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "p'0h01zh11Eh24Hallh31bi001bh41xh51Hh62Hxh74__p1h84__x1h92H0h:3Hinh;2Hrh<7__arithh=4__ffh>8__varmaph?5__with@1ehA5lemmahB2wlp;1p;2p;3p;4p;6p;7p;8g001fj1STg002Fj15Tg002kj1<Tg003Pj1ZTg003nj1nTg01M8j1>Tg01O[j1ETg01WNj2;Tg009nj12Tg00@Rj1JTg00A2j3:Tg01NYj3GTg01I9j2`Tg00BZj26Tg00Ffj2OTg006Wj34Tg01L5j1NTg02Gaj2]Tg02?Kj1\Tg00kMj2ATg00moj2@Tg019UR0j2[Tg01PTj3MTg01RHj2YTg01Raj3XTg01SRj3WTg010mj2VTg012Gj1UTg012ej1TTg013Pj2lTg01:0j4?Tg00_0j1iTg0143j2DTg01Wkj6fTg0159j2dTg015[j2cTg016Gj3bTg016fj4aTg00gfj6FTg01J:j2QTg01P8j3_Tg01UUj2CTg01:[j7BTg01fNj7HTg01;?j8^Tg00LIR1f1R2f0R33_p=9%<3#2p=7%53#2p=8A:123p=mf2R4A:1235:1p=jf4R5f3R6A:1239:145:15:1p==g00J]R7g00RXR8743p=3g00K=R99473p=IA4123p=LA4156A4142/C3'Cp=01C23,C4p=K1D13p=kP2g01<JR:g01<iR;P;g01=IR<P3g01=iR=FBp=RP1P2g02:mR>P3C?p=hP11D12P>P3C?p=gP5P:P;P;P<P6P:P;P;P<P11D14P>P2C?P=FBP3FHp=1f6R>P:P;P;P<f5R?P:P;P;P<P5P=FBP6P:P;P;P<P4P:P;P;P<P2P=FBP3FHFHp=eP6P:P;P;P<P4P2P3G^p=P%S1g00J8R=#5R@#<RA#ZRB#n%>3RC%E3RD/94';X01g00MSRE%2=RF%2@RG%<=RH#2RI%5@R@#2RJ%2ARK%5HRL#2RM%<HRH#2RN%5@RO#2RP%<@R@#2RQ%5ARR#2RS%<ARA#2RT%5LRU#2RV%<LRL#2RW%5HRX#2RY%<HRH#2RZ%5OR[#2R\%7ORO%8@R]%7@R@%8RR^%7RRR%8AR_%7ARA%8UR`%7URU%8LRa%7LRL%8XRb%7XRX%8HRc%7HRH%J1'm3jD=D=D=D=D=D=D=5:1Rd5G1#31`42#I16B4#>P71O7316B6#>=473P716B?Re#>=473%N>]1P216B5#>R>#31]?3W1%I>%N?%\?1AEe%8[R[,@e'[f8Re,9D,;CX01R>=G1d#3AM13dRff:Rg,9D,;CX01P2O1#3[^41Rh'Yf9Ri,9D,;CX01=G1d#3f;Rj,9D,;CX01P2O1#3\f^41;X3WAAW1>dP?O2PhP0f7,6BR0,AE1@0[16BeRh941E1LFhPGPhPIPhPJPhPKPhPMPhPNPhPPPhPQPhPSPhPTPhPVPhPWPhPYPhPZPhP\PhPOPhP]PhP@PhP^PhPRPhP_PhPAPhP`PhPUPhPaPhPLPhPbPhPXPhPcPhPHPhg01KXR?D0D0D0D0D0D0D0D0D0D0D0D0D0D0D03KP216BiR>,AE16BgRf/@[p-0RCg01?mRD#J%SD1V12%U1%T1RDP11l1=R=g01Y3%k[C?,RD%i;RkPDP11D1ERlg01;cP=C?,RDPkPDPD1hl=PDPD1gF=PDPDPGP=PDPDPIP=PDPDPJP=PDPDPKP=PDPDPMP=PDPDPNP=PDPDPPP=PDPDPQP=PDPDPSP=PDPDPTP=PDPDPVP=PDPDPWP=PDPDPYP=PDPDPZP=PDPDP\P=PDPDPOP=PDPDP]P=PDPDP@P=PDPDP^P=PDPDPRP=PDPDP_P=PDPDPAP=PDPDP`P=PDPDPUP=PDPDPaP=PDPDPLP=PDPDPbP=PDPDPXP=PDPDPcP=PDPDPHP=PDP:P;P;P<P6EfD1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1FeCPCP1dD<P3P41O781c34#3dAb1E2Cab=b>b?X81W71@3[1AE2A41E41LF4PGP4PIP4PJP4PKP4PMP4PNP4PPP4PQP4PSP4PTP4PVP4PWP4PYP4PZP4P\P4POP4P]P4P@P4P^P4PRP4P_P4PAP4P`P4PUP4PaP4PLP4PbP4PXP4PcP4PHP4P6D0D0D0D0D0D0D0D0D0D0D0D0D0D0D03K[[^81^7CP3P?f<,6BP2P4O4b<W9W5P2P3O2n2001000010121000000AM10dR0eP0P2PhP3O2%>h%Eh/9i';#3P7%>>%Ef/9jRj,;3#3X37P3P9P5EF%E>/9g,;9#3P7Pj%I3X37PeP8P3EFA4789P7P8P7PCP3g01?QP?n0110000020000X@7g00N1P9P3EFP?1Q?3b5b6b2b2b:b2b;'QW1n0110000020001P3O1b1b3W6W2W4WBo"). Qed.

(* [comment removed for export] *)
Ltac kp_value :=
  regnorm; imm_norm; rewrite ?v_addi_0;
  first [ reflexivity | apply v_addi_back; reflexivity
        | rewrite ?v_addi_addi'; first [reflexivity | apply v_addi_k0; reflexivity | klitsg; first [reflexivity | bveq]] ].

(* [comment removed for export] *)
Ltac kp_base per_reg :=
  first [ lazymatch goal with |- forall x : reg, _ -> getr ?A x = getr ?B x => constr_eq A B end;
          let x := fresh "x" in intros x _; reflexivity
        | assumption
        | keep_tac
        | let x := fresh "x" in let Hx := fresh "Hx" in
          intros x Hx;
          first [ lazymatch type of Hx with wreg ?wl _ = false =>
                  match goal with
                  | Hk : forall r' : reg, wreg ?wl' r' = false -> getr _ r' = getr _ r' |- getr _ x = _ =>
                      exact (Hk x (wreg_sub wl wl' x eq_refl Hx))
                  | Hc : forall r' : reg, callee_saved r' -> getr _ r' = getr _ r' |- getr _ x = _ =>
                      exact (Hc x (wreg_noncs_cs wl x eq_refl Hx))
                  end end
                | per_reg x Hx ] ].

Ltac kp_chain_w per_reg :=
  lazymatch goal with
  | |- forall x : reg, wreg ?wl x = false -> getr (regupd ?R2 ?rd ?v) x = getr ?R x =>
      first [ apply (kp_skip_w wl R R2 rd v); [ reflexivity | kp_chain_w per_reg ]
            | apply (kp_restore_w wl R R2 rd v);
              [ kp_value
              | let u := eval vm_compute in (bv_unsigned rd) in
                change (bv_unsigned rd) with u; kp_chain_w per_reg ] ]
  | |- _ => kp_base per_reg
  end.

(* [comment removed for export] *)
Ltac cs_per_reg x Hx :=
  lazymatch type of Hx with wreg ?wl _ = false =>
    let Hc := fresh "Hcsx" in
    pose proof (wreg_noncs_cs wl x eq_refl Hx) as Hc;
    first
      [ regnorm; cs_chain Hc
      | destruct (cs_enum x Hc) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
        kp_value ]
  end.

Ltac cs_goal :=
  first
    [ apply cs_to_wreg; kp_chain_w cs_per_reg
    | let x := fresh "x" in let Hx := fresh "Hx" in
      intros x Hx;
      first
        [ regnorm; cs_chain Hx
        | destruct (cs_enum x Hx) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
          regnorm; imm_norm;
          first [ reflexivity | apply v_addi_back; reflexivity
                | rewrite ?v_addi_addi'; first [reflexivity | apply v_addi_k0; reflexivity | klitsg; first [reflexivity | bveq]] ] ] ].

(* [comment removed for export] *)
Lemma reg_enum : forall x : reg,
  x = 0%bv \/ x = 1%bv \/ x = 2%bv \/ x = 3%bv \/ x = 4%bv \/ x = 5%bv \/ x = 6%bv \/ x = 7%bv \/
  x = 8%bv \/ x = 9%bv \/ x = 10%bv \/ x = 11%bv \/ x = 12%bv \/ x = 13%bv \/ x = 14%bv \/ x = 15%bv \/
  x = 16%bv \/ x = 17%bv \/ x = 18%bv \/ x = 19%bv \/ x = 20%bv \/ x = 21%bv \/ x = 22%bv \/ x = 23%bv \/
  x = 24%bv \/ x = 25%bv \/ x = 26%bv \/ x = 27%bv \/ x = 28%bv \/ x = 29%bv \/ x = 30%bv \/ x = 31%bv.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h01Ch11Hh21zh34__x1h42H0h57__arithh64__ffh78__varmaph85__with92b1h:2b2h;1nh<1Eh=2Hrh>1xp%0p;1p;3p;2p;4p;7p;6p;8g002Fj1ATg002kj1DTg003Pj1fTg003nj1GTg006Wj31Tg00BZj25Tg021gj3eTg00CDj2TTg01nmj2STg02?Kj1`Tg00moj2ITg019UR0j2RTg02@Hj1sTg023]j2oTg00@Rj1lTg001fj1kTg010mj2iTg012Gj1hTg012ej1gTg013Pj2dTg01:0j4HTg00_0j1cTg0143j2MTg01XOj7bTg0159j2aTg00Ffj2OTg015[j2_Tg016Gj3^Tg016fj4]Tg02A1j3\Tg020?j2[Tg009nj1>Tg01UUR1j22Tg00;Oj3XTg001Hj6PTg022Kj3NTg022ej3ETg00kMj2mTg01:[j7JTg01;?j8pTg01fNj7QTg00LIR2f1R3f0R431p=6g00MSR5/m4p=F%A4#>p=B1M24p=VP3g01<JR6g01<iR7P7g01=IR8P4g01=iR9FJp=Uf3R:P6P7P7P8f2R;P3P4Gpp=LP2f4R<P:1O2;P3P4EPp=8P2P<P:P;P3P4EPp=ZA1245p=K%D4#>p=Cf5R==12<A12:;A1234'2'2p=;A12<:A12;3/24'2p=3P2P3g02:mR>P4CHp=tP2P3P>1M24CHp=rP;P6P7P7P8P2P3P>P4CHP9FJp=qP<P6P7P7P8P:P6P7P7P8P2P;P>1M23CHP9FJP4FQp==f6R>P6P7P7P8P=P6P7P7P8P<P9FJP:P6P7P7P8P;P6P7P7P8P3P9FJP4FQFQp=nf7R9=12>A12=<A12:;A1234'2'2'2p=:1234,2;p=Yg00N1R?9X34p=9A1=<:A1;34'2p=7A1>=<A1:;3/24'2p=01O24p=jA1=<:12;3;E4p=<AN;349E<:p=@AN;349E<:9E>=p=?AE;349E<:p=4A12:;A1234'2p=Wg00J8R@#ARA#DRB#fRC#GRDg023?RE%G4RF%G3RGP0%G;?13415:;15:3'6RH[15;315;4'6%G:?1;3[RI%G<?1:;\HAe;34P4n2001000000120000000W:W9W;RHPI^:G^9F^;EREP4PCP315C3RF,TCRG1SCF15C;RI/64X22%`3RJ%FF%AARK#ARL#ARM#BRN,IF'RROPI15C:R:/64X22PI%sCRP,oIP0%FIRQ1IINRR%F:1I:N'RP415C<RS#FRT15C=RU/INRVg01?mRW#lRX%kWRW1i23RY%h2RZ%g2R[P21d2@R\g01Y3%VNCH,U[R]%c7R^P[P21M25R_g01;cP\CH,U[R`P^P[P6P7P7P8P`P]FbCLCL1a[8R8P4P;g00J]R7g00RXR6'O1_4;=176dA^253C]R6b6b7b8X321I4NR7%F3Ra%F;1I;N'R[[^32P415C9RNP3P;O3Rbb5W4W1P3P4O2n20010000001200000009\IPD81SCI,6Ieb115CG1[CFDZO4b115C4,TC91D4PJPOP0PQPR%K:RRP:%>@RQP:%>ARAP:%D@R@#>R0P:%>KROP:%>BRJP:%A@RF#>RGP:%D@R@#>RPP:%>LRcP:%DKRK#>RdP:%ABRe#>RfP:%DBRB#>RgP:%AFRh#>RiP:%DFRF#>RjP:%A@Rk#>RlP:%D@R@#>RmP:%>MRMP:%CLRLP:%BKRnP:%CKRKP:%BeRoP:%CeReP:%BBRpP:%CBRBP:%BhRqP:%ChRhP:%BFRrP:%CFRFP:%BkRsP:%CkRkP:%B@RtP:%C@R@E;D3D3D3D3D3D3D3D3D3D3D3D3D3D3R:'2P4PXPWPYPZP[P]P^P[P`P^P[P[1t\_P[P[1r\QP[P[P\PAP[P[P\P0P[P[P\POP[P[P\PJP[P[P\PGP[P[P\PPP[P[P\PcP[P[P\PdP[P[P\PfP[P[P\PgP[P[P\PiP[P[P\PjP[P[P\PlP[P[P\PmP[P[P\PMP[P[P\PLP[P[P\PnP[P[P\PKP[P[P\PoP[P[P\PeP[P[P\PpP[P[P\PBP[P[P\PqP[P[P\PhP[P[P\PrP[P[P\PFP[P[P\PsP[P[P\PkP[P[P\Pt%V@9q[\D=D=D=D=D=D=D=D=D=D=D=D=D=D=D=D=D=D=D=D=D=D=D=D=D=D=D=D=D=FnCLCLP8P6b6b7b8X32%K;16;QP;PAP;P0P;POP;PJP;PGP;PPP;PcP;PdP;PfP;PgP;PiP;PjP;PlP;PmP;PMP;PLP;PnP;PKP;PoP;PeP;PpP;PBP;PqP;PhP;PrP;PFP;PsP;PkP;PtP;P@G:D3D3D3D3D3D3D3D3D3D3D3D3D33Y\a\7^32Pbb5X4VX1TP3P4O2n2001000010121000000%KI16IQPIPAPIP0PIPOPIPJPIPGPIPPPIPcPIPdPIPfPIPgPIPiPIPjPIPlPIPmPIPMPIPLPIPnPIPKPIPoPIPePIPpPIPBPIPqPIPhPIPrPIPFPIPsPIPkPIPtPIP@G:D3D3D3D3D3D3D3D3D3D3D3D3D33YP1PRP:PDP<AXC5?R?PDP<19CQR:PDP<19CARRPDP<19C0RIPDP<19CORTPDP<19CJRVPDP<19CGRbPDP<19CPR7PDP<19CcRaPDP<19CdR;PDP<19CfR6PDP<19CgR8PDP<19CiR\PDP<19CjR[PDP<19ClR_PDP<19CmR^PDP<19CMR`PDP<19CLR]PDP<19CnRZPDP<19CKRYPDP<19CoRWPDP<19CeRXPDP<19CpRuPDP<19CBRvPDP<19CqRwPDP<19ChRxPDP<19CrRyPDP<19CFRzPDP<19CsR{PDP<19CkR|PDP<19CtR}PDP<19C@R<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P4%KSA1D=?PDP=P:PDP=PRPDP=PIPDP=PTPDP=PVPDP=PbPDP=P7PDP=PaPDP=P;PDP=P6PDP=P8PDP=P\PDP=P[PDP=P_PDP=P^PDP=P`PDP=P]PDP=PZPDP=PYPDP=PWPDP=PXPDP=PuPDP=PvPDP=PwPDP=PxPDP=PyPDP=PzPDP=P{PDP=P|PDP=P}A1D=<F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0PHPEP4PCP>P?P2P515C?R5,64X22%j515C>R5P3EPO4b13NW0P4O1PSPQPSPAPSP0PSPOPSPJPSPGPSPPPSPcPSPdPSPfPSPgPSPiPSPjPSPlPSPmPSPMPSPLPSPnPSPKPSPoPSPePSPpPSPBPSPqPSPhPSPrPSPFPSPsPSPkPSPtPSP@E;D3D3D3D3D3D3D3D3D3D3D3D3D3D3P116UQPUPAPUP0PUPOPUPJPUPGPUPPPUPcPUPdPUPfPUPgPUPiPUPjPUPlPUPmPUPMPUPLPUPnPUPKPUPoPUPePUPpPUPBPUPqPUPhPUPrPUPFPUPsPUPkPUPtPUP@G:D3D3D3D3D3D3D3D3D3D3D3D3D3PDP>P?PDP>P:PDP>PRPDP>PIPDP>PTPDP>PVPDP>PbPDP>P7PDP>PaPDP>P;PDP>P6PDP>P8PDP>P\PDP>P[PDP>P_PDP>P^PDP>P`PDP>P]PDP>PZPDP>PYPDP>PWPDP>PXPDP>PuPDP>PvPDP>PwPDP>PxPDP>PyPDP>PzPDP>P{PDP>P|PDP>P}PDP>P<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P4165QPDP9P?A1D9:R>PDP9PRPDP9PIPDP9PTPDP9PVPDP9PbPDP9P7PDP9PaPDP9P;PDP9P6PDP9P8PDP9P\PDP9P[PDP9P_PDP9P^PDP9P`PDP9P]PDP9PZPDP9PYPDP9PWPDP9PXPDP9PuPDP9PvPDP9PwPDP9PxPDP9PyPDP9PzPDP9P{PDP9P|PDP9P}PDP9P<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0R9PHPEP4PCf8RUP:PQ15C:RQ,64X22PQ15CURQP3D8O4b19N>9E<W0P4O1P5PAP5P0P5POP5PJP5PGP5PPP5PcP5PdP5PfP5PgP5PiP5PjP5PlP5PmP5PMP5PLP5PnP5PKP5PoP5PeP5PpP5PBP5PqP5PhP5PrP5PFP5PsP5PkP5PtP5P@G:D3D3D3D3D3D3D3D3D3D3D3D3D3P116NAPNP0PNPOPNPJPNPGPNPPPNPcPNPdPNPfPNPgPNPiPNPjPNPlPNPmPNPMPNPLPNPnPNPKPNPoPNPePNPpPNPBPNPqPNPhPNPrPNPFPNPsPNPkPNPtPNP@E;D3D3D3D3D3D3D3D3D3D3D3D3D3PDPUP?PDPUP:PDPUPRPDPUPIPDPUPTPDPUPVPDPUPbPDPUP7PDPUPaPDPUP;PDPUP6PDPUP8PDPUP\PDPUP[PDPUP_PDPUP^PDPUP`PDPUP]PDPUPZPDPUPYPDPUPWPDPUPXPDPUPuPDPUPvPDPUPwPDPUPxPDPUPyPDPUPzPDPUP{PDPUP|PDPUP}PDPUP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416QAPDf9RUP?A1DU:RNA1DURR5PDPUPIPDPUPTPDPUPVPDPUPbPDPUP7PDPUPaPDPUP;PDPUP6PDPUP8PDPUP\PDPUP[PDPUP_PDPUP^PDPUP`PDPUP]PDPUPZPDPUPYPDPUPWPDPUPXPDPUPuPDPUPvPDPUPwPDPUPxPDPUPyPDPUPzPDPUP{PDPUP|PDPUP}A1DU<F0F0F0F0F0F0F0F0F0F0F0F0F0F0R9'2R>PNP>P5P9PHPEP4PCf:R9PRPA15CRRA,64X22PA15C9RAP3D8O4b1D@E<W0P4O1PQP0PQPOPQPJPQPGPQPPPQPcPQPdPQPfPQPgPQPiPQPjPQPlPQPmPQPMPQPLPQPnPQPKPQPoPQPePQPpPQPBPQPqPQPhPQPrPQPFPQPsPQPkPQPtPQP@E;D3D3D3D3D3D3D3D3D3D3D3D3D3P115CURU/60PUPOPUPJPUPGPUPPPUPcPUPdPUPfPUPgPUPiPUPjPUPlPUPmPUPMPUPLPUPnPUPKPUPoPUPePUPpPUPBPUPqPUPhPUPrPUPFPUPsPUPkPUPtPUP@G:D3D3D3D3D3D3D3D3D3D3D3D3PDP9P?PDP9P:PDP9PRPDP9PIPDP9PTPDP9PVPDP9PbPDP9P7PDP9PaPDP9P;PDP9P6PDP9P8PDP9P\PDP9P[PDP9P_PDP9P^PDP9P`PDP9P]PDP9PZPDP9PYPDP9PWPDP9PXPDP9PuPDP9PvPDP9PwPDP9PxPDP9PyPDP9PzPDP9P{PDP9P|PDP9P}PDP9P<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416A0PDf;R9P?A1D9:RUA1D9RRQA1D9IR5PDP9PTPDP9PVPDP9PbPDP9P7PDP9PaPDP9P;PDP9P6PDP9P8PDP9P\PDP9P[PDP9P_PDP9P^PDP9P`PDP9P]PDP9PZPDP9PYPDP9PWPDP9PXPDP9PuPDP9PvPDP9PwPDP9PxPDP9PyPDP9PzPDP9P{PDP9P|PDP9P}PDP9P<E7F0F0F0F0F0F0F0F0F0F0F0F0F0R>'2RN'2RSPUPSPQPNP5P>PHPEP4PCf<R>PIP015CIR0,64X22P015C>R0P3D8O4b1F?E<W0P4O1PAPOPAPJPAPGPAPPPAPcPAPdPAPfPAPgPAPiPAPjPAPlPAPmPAPMPAPLPAPnPAPKPAPoPAPePAPpPAPBPAPqPAPhPAPrPAPFPAPsPAPkPAPtPAP@G:D3D3D3D3D3D3D3D3D3D3D3D3P115C9R9/6OP9PJP9PGP9PPP9PcP9PdP9PfP9PgP9PiP9PjP9PlP9PmP9PMP9PLP9PnP9PKP9PoP9PeP9PpP9PBP9PqP9PhP9PrP9PFP9PsP9PkP9PtP9P@E;D3D3D3D3D3D3D3D3D3D3D3D3PDP>P?PDP>P:PDP>PRPDP>PIPDP>PTPDP>PVPDP>PbPDP>P7PDP>PaPDP>P;PDP>P6PDP>P8PDP>P\PDP>P[PDP>P_PDP>P^PDP>P`PDP>P]PDP>PZPDP>PYPDP>PWPDP>PXPDP>PuPDP>PvPDP>PwPDP>PxPDP>PyPDP>PzPDP>P{PDP>P|PDP>P}PDP>P<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P4160OPDf=R>P?A1D>:R9A1D>RRAA1D>IR5A1D>TRNPDP>PVPDP>PbPDP>P7PDP>PaPDP>P;PDP>P6PDP>P8PDP>P\PDP>P[PDP>P_PDP>P^PDP>P`PDP>P]PDP>PZPDP>PYPDP>PWPDP>PXPDP>PuPDP>PvPDP>PwPDP>PxPDP>PyPDP>PzPDP>P{PDP>P|PDP>P}A1D><F0F0F0F0F0F0F0F0F0F0F0F0F0RQ'2RS'2RU'2R=P9P=PAPUP5PSPNPQPHPEP4PCf>RQPTPO15CTRO,64X22PO15CQROP3D8O4b1D@D4E<W0P4O1P0PJP0PGP0PPP0PcP0PdP0PfP0PgP0PiP0PjP0PlP0PmP0PMP0PLP0PnP0PKP0PoP0PeP0PpP0PBP0PqP0PhP0PrP0PFP0PsP0PkP0PtP0P@E;D3D3D3D3D3D3D3D3D3D3D3D3P115C>R>/6JP>PGP>PPP>PcP>PdP>PfP>PgP>PiP>PjP>PlP>PmP>PMP>PLP>PnP>PKP>PoP>PeP>PpP>PBP>PqP>PhP>PrP>PFP>PsP>PkP>PtP>P@G:D3D3D3D3D3D3D3D3D3D3D3PDPQP?PDPQP:PDPQPRPDPQPIPDPQPTPDPQPVPDPQPbPDPQP7PDPQPaPDPQP;PDPQP6PDPQP8PDPQP\PDPQP[PDPQP_PDPQP^PDPQP`PDPQP]PDPQPZPDPQPYPDPQPWPDPQPXPDPQPuPDPQPvPDPQPwPDPQPxPDPQPyPDPQPzPDPQP{PDPQP|PDPQP}PDPQP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416OJPDf?RQP?A1DQ:R>A1DQRR0A1DQIRNA1DQTRSA1DQVR5PDPQPbPDPQP7PDPQPaPDPQP;PDPQP6PDPQP8PDPQP\PDPQP[PDPQP_PDPQP^PDPQP`PDPQP]PDPQPZPDPQPYPDPQPWPDPQPXPDPQPuPDPQPvPDPQPwPDPQPxPDPQPyPDPQPzPDPQP{PDPQP|PDPQP}PDPQP<E7F0F0F0F0F0F0F0F0F0F0F0F0RU'2RA'2R='2R9'2R~P>P~P0P9PNP=PSPAP5PUPHPEP4PCf@RUPVPJ15CVRJ,64X22PJ15CURJP3D8O4b1F?D4E<W0P4O1POPGPOPPPOPcPOPdPOPfPOPgPOPiPOPjPOPlPOPmPOPMPOPLPOPnPOPKPOPoPOPePOPpPOPBPOPqPOPhPOPrPOPFPOPsPOPkPOPtPOP@G:D3D3D3D3D3D3D3D3D3D3D3P115CQRQ/6GPQPPPQPcPQPdPQPfPQPgPQPiPQPjPQPlPQPmPQPMPQPLPQPnPQPKPQPoPQPePQPpPQPBPQPqPQPhPQPrPQPFPQPsPQPkPQPtPQP@E;D3D3D3D3D3D3D3D3D3D3D3PDPUP?PDPUP:PDPUPRPDPUPIPDPUPTPDPUPVPDPUPbPDPUP7PDPUPaPDPUP;PDPUP6PDPUP8PDPUP\PDPUP[PDPUP_PDPUP^PDPUP`PDPUP]PDPUPZPDPUPYPDPUPWPDPUPXPDPUPuPDPUPvPDPUPwPDPUPxPDPUPyPDPUPzPDPUP{PDPUP|PDPUP}PDPUP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416JGPDfARUP?A1DU:S00A1DURRQA1DUIROA1DUTR5A1DUVRAA1DUbRSPDPUP7PDPUPaPDPUP;PDPUP6PDPUP8PDPUP\PDPUP[PDPUP_PDPUP^PDPUP`PDPUP]PDPUPZPDPUPYPDPUPWPDPUPXPDPUPuPDPUPvPDPUPwPDPUPxPDPUPyPDPUPzPDPUP{PDPUP|PDPUP}A1DU<F0F0F0F0F0F0F0F0F0F0F0F0R='2RN'2R9'2R0'2R~'2R>Q00P>PQP~POP0P5P9PAPNPSP=PHPEP4PCfBR=PbPG15CbRG,64X22PG15C=RGP3D8O4b1D@D4D4E<W0P4O1PJPPPJPcPJPdPJPfPJPgPJPiPJPjPJPlPJPmPJPMPJPLPJPnPJPKPJPoPJPePJPpPJPBPJPqPJPhPJPrPJPFPJPsPJPkPJPtPJP@E;D3D3D3D3D3D3D3D3D3D3D3P115CURU/6PPUPcPUPdPUPfPUPgPUPiPUPjPUPlPUPmPUPMPUPLPUPnPUPKPUPoPUPePUPpPUPBPUPqPUPhPUPrPUPFPUPsPUPkPUPtPUP@G:D3D3D3D3D3D3D3D3D3D3PDP=P?PDP=P:PDP=PRPDP=PIPDP=PTPDP=PVPDP=PbPDP=P7PDP=PaPDP=P;PDP=P6PDP=P8PDP=P\PDP=P[PDP=P_PDP=P^PDP=P`PDP=P]PDP=PZPDP=PYPDP=PWPDP=PXPDP=PuPDP=PvPDP=PwPDP=PxPDP=PyPDP=PzPDP=P{PDP=P|PDP=P}PDP=P<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416GPPDfCR=P?A1D=:S00A1D=RS01A1D=IRUA1D=TRJA1D=VRSA1D=bRNA1D=7RAPDP=PaPDP=P;PDP=P6PDP=P8PDP=P\PDP=P[PDP=P_PDP=P^PDP=P`PDP=P]PDP=PZPDP=PYPDP=PWPDP=PXPDP=PuPDP=PvPDP=PwPDP=PxPDP=PyPDP=PzPDP=P{PDP=P|PDP=P}PDP=P<E7F0F0F0F0F0F0F0F0F0F0F0R9'2R5'2R0'2RO'2R~'2RQ'2R>Q00P>Q01PQPUP~PJPOPSP0PNP5PAP9PHPEP4PCfDR9P7PP15C7RP,64X22PP15C9RPP3D8O4b1F?D4D4E<W0P4O1PGPcPGPdPGPfPGPgPGPiPGPjPGPlPGPmPGPMPGPLPGPnPGPKPGPoPGPePGPpPGPBPGPqPGPhPGPrPGPFPGPsPGPkPGPtPGP@G:D3D3D3D3D3D3D3D3D3D3P115C=R=/6cP=PdP=PfP=PgP=PiP=PjP=PlP=PmP=PMP=PLP=PnP=PKP=PoP=PeP=PpP=PBP=PqP=PhP=PrP=PFP=PsP=PkP=PtP=P@E;D3D3D3D3D3D3D3D3D3D3PDP9P?PDP9P:PDP9PRPDP9PIPDP9PTPDP9PVPDP9PbPDP9P7PDP9PaPDP9P;PDP9P6PDP9P8PDP9P\PDP9P[PDP9P_PDP9P^PDP9P`PDP9P]PDP9PZPDP9PYPDP9PWPDP9PXPDP9PuPDP9PvPDP9PwPDP9PxPDP9PyPDP9PzPDP9P{PDP9P|PDP9P}PDP9P<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416PcPDfER9P?A1D9:S01A1D9RS00A1D9IS02A1D9TR=A1D9VRGA1D9bRAA1D97R5A1D9aRNPDP9P;PDP9P6PDP9P8PDP9P\PDP9P[PDP9P_PDP9P^PDP9P`PDP9P]PDP9PZPDP9PYPDP9PWPDP9PXPDP9PuPDP9PvPDP9PwPDP9PxPDP9PyPDP9PzPDP9P{PDP9P|PDP9P}A1D9<F0F0F0F0F0F0F0F0F0F0F0R0'2RS'2RO'2RJ'2R~'2RU'2RQ'2R>Q01P>Q00PQQ02PUP=P~PGPJPAPOP5PSPNP0PHPEP4PCfFR0PaPc15CaRc,64X22Pc15C0RcP3D8O4b1D@D4D4D4E<W0P4O1PPPdPPPfPPPgPPPiPPPjPPPlPPPmPPPMPPPLPPPnPPPKPPPoPPPePPPpPPPBPPPqPPPhPPPrPPPFPPPsPPPkPPPtPPP@E;D3D3D3D3D3D3D3D3D3D3P115C9R9/6dP9PfP9PgP9PiP9PjP9PlP9PmP9PMP9PLP9PnP9PKP9PoP9PeP9PpP9PBP9PqP9PhP9PrP9PFP9PsP9PkP9PtP9P@G:D3D3D3D3D3D3D3D3D3PDP0P?PDP0P:PDP0PRPDP0PIPDP0PTPDP0PVPDP0PbPDP0P7PDP0PaPDP0P;PDP0P6PDP0P8PDP0P\PDP0P[PDP0P_PDP0P^PDP0P`PDP0P]PDP0PZPDP0PYPDP0PWPDP0PXPDP0PuPDP0PvPDP0PwPDP0PxPDP0PyPDP0PzPDP0P{PDP0P|PDP0P}PDP0P<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416cdPDfGR0P?A1D0:S02A1D0RS00A1D0IS01A1D0TS03A1D0VR9A1D0bRPA1D07RNA1D0aRSA1D0;R5PDP0P6PDP0P8PDP0P\PDP0P[PDP0P_PDP0P^PDP0P`PDP0P]PDP0PZPDP0PYPDP0PWPDP0PXPDP0PuPDP0PvPDP0PwPDP0PxPDP0PyPDP0PzPDP0P{PDP0P|PDP0P}PDP0P<E7F0F0F0F0F0F0F0F0F0F0RO'2RA'2RJ'2RG'2R~'2R='2RU'2RQ'2R>Q02P>Q00PQQ01PUQ03P=P9P~PPPGPNPJPSPAP5POPHPEP4PCfHROP;Pd15C;Rd,64X22Pd15CORdP3D8O4b1F?D4D4D4E<W0P4O1PcPfPcPgPcPiPcPjPcPlPcPmPcPMPcPLPcPnPcPKPcPoPcPePcPpPcPBPcPqPcPhPcPrPcPFPcPsPcPkPcPtPcP@G:D3D3D3D3D3D3D3D3D3P115C0R0/6fP0PgP0PiP0PjP0PlP0PmP0PMP0PLP0PnP0PKP0PoP0PeP0PpP0PBP0PqP0PhP0PrP0PFP0PsP0PkP0PtP0P@E;D3D3D3D3D3D3D3D3D3PDPOP?PDPOP:PDPOPRPDPOPIPDPOPTPDPOPVPDPOPbPDPOP7PDPOPaPDPOP;PDPOP6PDPOP8PDPOP\PDPOP[PDPOP_PDPOP^PDPOP`PDPOP]PDPOPZPDPOPYPDPOPWPDPOPXPDPOPuPDPOPvPDPOPwPDPOPxPDPOPyPDPOPzPDPOP{PDPOP|PDPOP}PDPOP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416dfPDfIROP?A1DO:S03A1DORS01A1DOIS00A1DOTS02A1DOVS04A1DObR0A1DO7RcA1DOaR5A1DO;RAA1DO6RSPDPOP8PDPOP\PDPOP[PDPOP_PDPOP^PDPOP`PDPOP]PDPOPZPDPOPYPDPOPWPDPOPXPDPOPuPDPOPvPDPOPwPDPOPxPDPOPyPDPOPzPDPOP{PDPOP|PDPOP}A1DO<F0F0F0F0F0F0F0F0F0F0RJ'2RN'2RG'2RP'2R~'2R9'2R='2RU'2RQ'2R>Q03P>Q01PQQ00PUQ02P=Q04P9P0P~PcPPP5PGPAPNPSPJPHPEP4PCfJRJP6Pf15C6Rf,64X22Pf15CJRfP3D8O4b1D@D4D4D4D4E<W0P4O1PdPgPdPiPdPjPdPlPdPmPdPMPdPLPdPnPdPKPdPoPdPePdPpPdPBPdPqPdPhPdPrPdPFPdPsPdPkPdPtPdP@E;D3D3D3D3D3D3D3D3D3P115CORO/6gPOPiPOPjPOPlPOPmPOPMPOPLPOPnPOPKPOPoPOPePOPpPOPBPOPqPOPhPOPrPOPFPOPsPOPkPOPtPOP@G:D3D3D3D3D3D3D3D3PDPJP?PDPJP:PDPJPRPDPJPIPDPJPTPDPJPVPDPJPbPDPJP7PDPJPaPDPJP;PDPJP6PDPJP8PDPJP\PDPJP[PDPJP_PDPJP^PDPJP`PDPJP]PDPJPZPDPJPYPDPJPWPDPJPXPDPJPuPDPJPvPDPJPwPDPJPxPDPJPyPDPJPzPDPJP{PDPJP|PDPJP}PDPJP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416fgPDfKRJP?A1DJ:S04A1DJRS02A1DJIS00A1DJTS01A1DJVS03A1DJbS05A1DJ7ROA1DJaRdA1DJ;RSA1DJ6RNA1DJ8RAPDPJP\PDPJP[PDPJP_PDPJP^PDPJP`PDPJP]PDPJPZPDPJPYPDPJPWPDPJPXPDPJPuPDPJPvPDPJPwPDPJPxPDPJPyPDPJPzPDPJP{PDPJP|PDPJP}PDPJP<E7F0F0F0F0F0F0F0F0F0RG'2R5'2RP'2Rc'2R~'2R0'2R9'2R='2RU'2RQ'2R>Q04P>Q02PQQ00PUQ01P=Q03P9Q05P0POP~PdPcPSPPPNP5PAPGPHPEP4PCfLRGP8Pg15C8Rg,64X22Pg15CGRgP3D8O4b1F?D4D4D4D4E<W0P4O1PfPiPfPjPfPlPfPmPfPMPfPLPfPnPfPKPfPoPfPePfPpPfPBPfPqPfPhPfPrPfPFPfPsPfPkPfPtPfP@G:D3D3D3D3D3D3D3D3P115CJRJ/6iPJPjPJPlPJPmPJPMPJPLPJPnPJPKPJPoPJPePJPpPJPBPJPqPJPhPJPrPJPFPJPsPJPkPJPtPJP@E;D3D3D3D3D3D3D3D3PDPGP?PDPGP:PDPGPRPDPGPIPDPGPTPDPGPVPDPGPbPDPGP7PDPGPaPDPGP;PDPGP6PDPGP8PDPGP\PDPGP[PDPGP_PDPGP^PDPGP`PDPGP]PDPGPZPDPGPYPDPGPWPDPGPXPDPGPuPDPGPvPDPGPwPDPGPxPDPGPyPDPGPzPDPGP{PDPGP|PDPGP}PDPGP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416giPDfMRGP?A1DG:S05A1DGRS03A1DGIS01A1DGTS00A1DGVS02A1DGbS04A1DG7S06A1DGaRJA1DG;RfA1DG6RAA1DG8R5A1DG\RNPDPGP[PDPGP_PDPGP^PDPGP`PDPGP]PDPGPZPDPGPYPDPGPWPDPGPXPDPGPuPDPGPvPDPGPwPDPGPxPDPGPyPDPGPzPDPGP{PDPGP|PDPGP}A1DG<F0F0F0F0F0F0F0F0F0RP'2RS'2Rc'2Rd'2R~'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q05P>Q03PQQ01PUQ00P=Q02P9Q04P0Q06POPJP~PfPdPAPcP5PSPNPPPHPEP4PCfNRPP\Pi15C\Ri,64X22Pi15CPRiP3D8O4b1D@D4D4D4D4D4E<W0P4O1PgPjPgPlPgPmPgPMPgPLPgPnPgPKPgPoPgPePgPpPgPBPgPqPgPhPgPrPgPFPgPsPgPkPgPtPgP@E;D3D3D3D3D3D3D3D3P115CGRG/6jPGPlPGPmPGPMPGPLPGPnPGPKPGPoPGPePGPpPGPBPGPqPGPhPGPrPGPFPGPsPGPkPGPtPGP@G:D3D3D3D3D3D3D3PDPPP?PDPPP:PDPPPRPDPPPIPDPPPTPDPPPVPDPPPbPDPPP7PDPPPaPDPPP;PDPPP6PDPPP8PDPPP\PDPPP[PDPPP_PDPPP^PDPPP`PDPPP]PDPPPZPDPPPYPDPPPWPDPPPXPDPPPuPDPPPvPDPPPwPDPPPxPDPPPyPDPPPzPDPPP{PDPPP|PDPPP}PDPPP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416ijPDfORPP?A1DP:S06A1DPRS04A1DPIS02A1DPTS00A1DPVS01A1DPbS03A1DP7S05A1DPaS07A1DP;RGA1DP6RgA1DP8RNA1DP\RSA1DP[R5PDPPP_PDPPP^PDPPP`PDPPP]PDPPPZPDPPPYPDPPPWPDPPPXPDPPPuPDPPPvPDPPPwPDPPPxPDPPPyPDPPPzPDPPP{PDPPP|PDPPP}PDPPP<E7F0F0F0F0F0F0F0F0Rc'2RA'2Rd'2Rf'2R~'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q06P>Q04PQQ02PUQ00P=Q01P9Q03P0Q05POQ07PJPGP~PgPfPNPdPSPAP5PcPHPEP4PCfPRcP[Pj15C[Rj,64X22Pj15CcRjP3D8O4b1F?D4D4D4D4D4E<W0P4O1PiPlPiPmPiPMPiPLPiPnPiPKPiPoPiPePiPpPiPBPiPqPiPhPiPrPiPFPiPsPiPkPiPtPiP@G:D3D3D3D3D3D3D3P115CPRP/6lPPPmPPPMPPPLPPPnPPPKPPPoPPPePPPpPPPBPPPqPPPhPPPrPPPFPPPsPPPkPPPtPPP@E;D3D3D3D3D3D3D3PDPcP?PDPcP:PDPcPRPDPcPIPDPcPTPDPcPVPDPcPbPDPcP7PDPcPaPDPcP;PDPcP6PDPcP8PDPcP\PDPcP[PDPcP_PDPcP^PDPcP`PDPcP]PDPcPZPDPcPYPDPcPWPDPcPXPDPcPuPDPcPvPDPcPwPDPcPxPDPcPyPDPcPzPDPcP{PDPcP|PDPcP}PDPcP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416jlPDfQRcP?A1Dc:S07A1DcRS05A1DcIS03A1DcTS01A1DcVS00A1DcbS02A1Dc7S04A1DcaS06A1Dc;S08A1Dc6RPA1Dc8RiA1Dc\R5A1Dc[RAA1Dc_RSPDPcP^PDPcP`PDPcP]PDPcPZPDPcPYPDPcPWPDPcPXPDPcPuPDPcPvPDPcPwPDPcPxPDPcPyPDPcPzPDPcP{PDPcP|PDPcP}A1Dc<F0F0F0F0F0F0F0F0Rd'2RN'2Rf'2Rg'2R~'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q07P>Q05PQQ03PUQ01P=Q00P9Q02P0Q04POQ06PJQ08PGPPP~PiPgP5PfPAPNPSPdPHPEP4PCfRRdP_Pl15C_Rl,64X22Pl15CdRlP3D8O4b1D@D4D4D4D4D4D4E<W0P4O1PjPmPjPMPjPLPjPnPjPKPjPoPjPePjPpPjPBPjPqPjPhPjPrPjPFPjPsPjPkPjPtPjP@E;D3D3D3D3D3D3D3P115CcRc/6mPcPMPcPLPcPnPcPKPcPoPcPePcPpPcPBPcPqPcPhPcPrPcPFPcPsPcPkPcPtPcP@G:D3D3D3D3D3D3PDPdP?PDPdP:PDPdPRPDPdPIPDPdPTPDPdPVPDPdPbPDPdP7PDPdPaPDPdP;PDPdP6PDPdP8PDPdP\PDPdP[PDPdP_PDPdP^PDPdP`PDPdP]PDPdPZPDPdPYPDPdPWPDPdPXPDPdPuPDPdPvPDPdPwPDPdPxPDPdPyPDPdPzPDPdP{PDPdP|PDPdP}PDPdP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416lmPDfSRdP?A1Dd:S08A1DdRS06A1DdIS04A1DdTS02A1DdVS00A1DdbS01A1Dd7S03A1DdaS05A1Dd;S07A1Dd6S09A1Dd8RcA1Dd\RjA1Dd[RSA1Dd_RNA1Dd^RAPDPdP`PDPdP]PDPdPZPDPdPYPDPdPWPDPdPXPDPdPuPDPdPvPDPdPwPDPdPxPDPdPyPDPdPzPDPdP{PDPdP|PDPdP}PDPdP<E7F0F0F0F0F0F0F0Rf'2R5'2Rg'2Ri'2R~'2RP'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q08P>Q06PQQ04PUQ02P=Q00P9Q01P0Q03POQ05PJQ07PGQ09PPPcP~PjPiPSPgPNP5PAPfPHPEP4PCfTRfP^Pm15C^Rm,64X22Pm15CfRmP3D8O4b1F?D4D4D4D4D4D4E<W0P4O1PlPMPlPLPlPnPlPKPlPoPlPePlPpPlPBPlPqPlPhPlPrPlPFPlPsPlPkPlPtPlP@G:D3D3D3D3D3D3P115CdRd/6MPdPLPdPnPdPKPdPoPdPePdPpPdPBPdPqPdPhPdPrPdPFPdPsPdPkPdPtPdP@E;D3D3D3D3D3D3PDPfP?PDPfP:PDPfPRPDPfPIPDPfPTPDPfPVPDPfPbPDPfP7PDPfPaPDPfP;PDPfP6PDPfP8PDPfP\PDPfP[PDPfP_PDPfP^PDPfP`PDPfP]PDPfPZPDPfPYPDPfPWPDPfPXPDPfPuPDPfPvPDPfPwPDPfPxPDPfPyPDPfPzPDPfP{PDPfP|PDPfP}PDPfP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416mMPDfURfP?A1Df:S09A1DfRS07A1DfIS05A1DfTS03A1DfVS01A1DfbS00A1Df7S02A1DfaS04A1Df;S06A1Df6S08A1Df8S0:A1Df\RdA1Df[RlA1Df_RAA1Df^R5A1Df`RNPDPfP]PDPfPZPDPfPYPDPfPWPDPfPXPDPfPuPDPfPvPDPfPwPDPfPxPDPfPyPDPfPzPDPfP{PDPfP|PDPfP}A1Df<F0F0F0F0F0F0F0Rg'2RS'2Ri'2Rj'2R~'2Rc'2RP'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q09P>Q07PQQ05PUQ03P=Q01P9Q00P0Q02POQ04PJQ06PGQ08PPQ0:PcPdP~PlPjPAPiP5PSPNPgPHPEP4PCfVRgP`PM15C`RM,64X22PM15CgRMP3D8O4b1D@D4D4D4D4D4D4D4E<W0P4O1PmPLPmPnPmPKPmPoPmPePmPpPmPBPmPqPmPhPmPrPmPFPmPsPmPkPmPtPmP@E;D3D3D3D3D3D3P115CfRf/6LPfPnPfPKPfPoPfPePfPpPfPBPfPqPfPhPfPrPfPFPfPsPfPkPfPtPfP@G:D3D3D3D3D3PDPgP?PDPgP:PDPgPRPDPgPIPDPgPTPDPgPVPDPgPbPDPgP7PDPgPaPDPgP;PDPgP6PDPgP8PDPgP\PDPgP[PDPgP_PDPgP^PDPgP`PDPgP]PDPgPZPDPgPYPDPgPWPDPgPXPDPgPuPDPgPvPDPgPwPDPgPxPDPgPyPDPgPzPDPgP{PDPgP|PDPgP}PDPgP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416MLPDfWRgP?A1Dg:S0:A1DgRS08A1DgIS06A1DgTS04A1DgVS02A1DgbS00A1Dg7S01A1DgaS03A1Dg;S05A1Dg6S07A1Dg8S09A1Dg\S0;A1Dg[RfA1Dg_RmA1Dg^RNA1Dg`RSA1Dg]R5PDPgPZPDPgPYPDPgPWPDPgPXPDPgPuPDPgPvPDPgPwPDPgPxPDPgPyPDPgPzPDPgP{PDPgP|PDPgP}PDPgP<E7F0F0F0F0F0F0Ri'2RA'2Rj'2Rl'2R~'2Rd'2Rc'2RP'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q0:P>Q08PQQ06PUQ04P=Q02P9Q00P0Q01POQ03PJQ05PGQ07PPQ09PcQ0;PdPfP~PmPlPNPjPSPAP5PiPHPEP4PCfXRiP]PL15C]RL,64X22PL15CiRLP3D8O4b1F?D4D4D4D4D4D4D4E<W0P4O1PMPnPMPKPMPoPMPePMPpPMPBPMPqPMPhPMPrPMPFPMPsPMPkPMPtPMP@G:D3D3D3D3D3P115CgRg/6nPgPKPgPoPgPePgPpPgPBPgPqPgPhPgPrPgPFPgPsPgPkPgPtPgP@E;D3D3D3D3D3PDPiP?PDPiP:PDPiPRPDPiPIPDPiPTPDPiPVPDPiPbPDPiP7PDPiPaPDPiP;PDPiP6PDPiP8PDPiP\PDPiP[PDPiP_PDPiP^PDPiP`PDPiP]PDPiPZPDPiPYPDPiPWPDPiPXPDPiPuPDPiPvPDPiPwPDPiPxPDPiPyPDPiPzPDPiP{PDPiP|PDPiP}PDPiP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416LnPDfYRiP?A1Di:S0;A1DiRS09A1DiIS07A1DiTS05A1DiVS03A1DibS01A1Di7S00A1DiaS02A1Di;S04A1Di6S06A1Di8S08A1Di\S0:A1Di[S0<A1Di_RgA1Di^RMA1Di`R5A1Di]RAA1DiZRSPDPiPYPDPiPWPDPiPXPDPiPuPDPiPvPDPiPwPDPiPxPDPiPyPDPiPzPDPiP{PDPiP|PDPiP}A1Di<F0F0F0F0F0F0Rj'2RN'2Rl'2Rm'2R~'2Rf'2Rd'2Rc'2RP'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q0;P>Q09PQQ07PUQ05P=Q03P9Q01P0Q00POQ02PJQ04PGQ06PPQ08PcQ0:PdQ0<PfPgP~PMPmP5PlPAPNPSPjPHPEP4PCfZRjPZPn15CZRn,64X22Pn15CjRnP3D8O4b1D@D4D4D4D4D4D4D4D4E<W0P4O1PLPKPLPoPLPePLPpPLPBPLPqPLPhPLPrPLPFPLPsPLPkPLPtPLP@E;D3D3D3D3D3P115CiRi/6KPiPoPiPePiPpPiPBPiPqPiPhPiPrPiPFPiPsPiPkPiPtPiP@G:D3D3D3D3PDPjP?PDPjP:PDPjPRPDPjPIPDPjPTPDPjPVPDPjPbPDPjP7PDPjPaPDPjP;PDPjP6PDPjP8PDPjP\PDPjP[PDPjP_PDPjP^PDPjP`PDPjP]PDPjPZPDPjPYPDPjPWPDPjPXPDPjPuPDPjPvPDPjPwPDPjPxPDPjPyPDPjPzPDPjP{PDPjP|PDPjP}PDPjP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416nKPDf[RjP?A1Dj:S0<A1DjRS0:A1DjIS08A1DjTS06A1DjVS04A1DjbS02A1Dj7S00A1DjaS01A1Dj;S03A1Dj6S05A1Dj8S07A1Dj\S09A1Dj[S0;A1Dj_S0=A1Dj^RiA1Dj`RLA1Dj]RSA1DjZRNA1DjYRAPDPjPWPDPjPXPDPjPuPDPjPvPDPjPwPDPjPxPDPjPyPDPjPzPDPjP{PDPjP|PDPjP}PDPjP<E7F0F0F0F0F0Rl'2R5'2Rm'2RM'2R~'2Rg'2Rf'2Rd'2Rc'2RP'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q0<P>Q0:PQQ08PUQ06P=Q04P9Q02P0Q00POQ01PJQ03PGQ05PPQ07PcQ09PdQ0;PfQ0=PgPiP~PLPMPSPmPNP5PAPlPHPEP4PCf\RlPYPK15CYRK,64X22PK15ClRKP3D8O4b1F?D4D4D4D4D4D4D4D4E<W0P4O1PnPoPnPePnPpPnPBPnPqPnPhPnPrPnPFPnPsPnPkPnPtPnP@G:D3D3D3D3P115CjRj/6oPjPePjPpPjPBPjPqPjPhPjPrPjPFPjPsPjPkPjPtPjP@E;D3D3D3D3PDPlP?PDPlP:PDPlPRPDPlPIPDPlPTPDPlPVPDPlPbPDPlP7PDPlPaPDPlP;PDPlP6PDPlP8PDPlP\PDPlP[PDPlP_PDPlP^PDPlP`PDPlP]PDPlPZPDPlPYPDPlPWPDPlPXPDPlPuPDPlPvPDPlPwPDPlPxPDPlPyPDPlPzPDPlP{PDPlP|PDPlP}PDPlP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416KoPDf]RlP?A1Dl:S0=A1DlRS0;A1DlIS09A1DlTS07A1DlVS05A1DlbS03A1Dl7S01A1DlaS00A1Dl;S02A1Dl6S04A1Dl8S06A1Dl\S08A1Dl[S0:A1Dl_S0<A1Dl^S0>A1Dl`RjA1Dl]RnA1DlZRAA1DlYR5A1DlWRNPDPlPXPDPlPuPDPlPvPDPlPwPDPlPxPDPlPyPDPlPzPDPlP{PDPlP|PDPlP}A1Dl<F0F0F0F0F0Rm'2RS'2RM'2RL'2R~'2Ri'2Rg'2Rf'2Rd'2Rc'2RP'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q0=P>Q0;PQQ09PUQ07P=Q05P9Q03P0Q01POQ00PJQ02PGQ04PPQ06PcQ08PdQ0:PfQ0<PgQ0>PiPjP~PnPLPAPMP5PSPNPmPHPEP4PCf^RmPWPo15CWRo,64X22Po15CmRoP3D8O4b1D@D4D4D4D4D4D4D4D4D4E<W0P4O1PKPePKPpPKPBPKPqPKPhPKPrPKPFPKPsPKPkPKPtPKP@E;D3D3D3D3P115ClRl/6ePlPpPlPBPlPqPlPhPlPrPlPFPlPsPlPkPlPtPlP@G:D3D3D3PDPmP?PDPmP:PDPmPRPDPmPIPDPmPTPDPmPVPDPmPbPDPmP7PDPmPaPDPmP;PDPmP6PDPmP8PDPmP\PDPmP[PDPmP_PDPmP^PDPmP`PDPmP]PDPmPZPDPmPYPDPmPWPDPmPXPDPmPuPDPmPvPDPmPwPDPmPxPDPmPyPDPmPzPDPmP{PDPmP|PDPmP}PDPmP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416oePDf_RmP?A1Dm:S0>A1DmRS0<A1DmIS0:A1DmTS08A1DmVS06A1DmbS04A1Dm7S02A1DmaS00A1Dm;S01A1Dm6S03A1Dm8S05A1Dm\S07A1Dm[S09A1Dm_S0;A1Dm^S0=A1Dm`S0?A1Dm]RlA1DmZRKA1DmYRNA1DmWRSA1DmXR5PDPmPuPDPmPvPDPmPwPDPmPxPDPmPyPDPmPzPDPmP{PDPmP|PDPmP}PDPmP<E7F0F0F0F0RM'2RA'2RL'2Rn'2R~'2Rj'2Ri'2Rg'2Rf'2Rd'2Rc'2RP'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q0>P>Q0<PQQ0:PUQ08P=Q06P9Q04P0Q02POQ00PJQ01PGQ03PPQ05PcQ07PdQ09PfQ0;PgQ0=PiQ0?PjPlP~PKPnPNPLPSPAP5PMPHPEP4PCf`RMPXPe15CXRe,64X22Pe15CMReP3D8O4b1F?D4D4D4D4D4D4D4D4D4E<W0P4O1PoPpPoPBPoPqPoPhPoPrPoPFPoPsPoPkPoPtPoP@G:D3D3D3P115CmRm/6pPmPBPmPqPmPhPmPrPmPFPmPsPmPkPmPtPmP@E;D3D3D3PDPMP?PDPMP:PDPMPRPDPMPIPDPMPTPDPMPVPDPMPbPDPMP7PDPMPaPDPMP;PDPMP6PDPMP8PDPMP\PDPMP[PDPMP_PDPMP^PDPMP`PDPMP]PDPMPZPDPMPYPDPMPWPDPMPXPDPMPuPDPMPvPDPMPwPDPMPxPDPMPyPDPMPzPDPMP{PDPMP|PDPMP}PDPMP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416epPDfaRMP?A1DM:S0?A1DMRS0=A1DMIS0;A1DMTS09A1DMVS07A1DMbS05A1DM7S03A1DMaS01A1DM;S00A1DM6S02A1DM8S04A1DM\S06A1DM[S08A1DM_S0:A1DM^S0<A1DM`S0>A1DM]S0@A1DMZRmA1DMYRoA1DMWR5A1DMXRAA1DMuRSPDPMPvPDPMPwPDPMPxPDPMPyPDPMPzPDPMP{PDPMP|PDPMP}A1DM<F0F0F0F0RL'2RN'2Rn'2RK'2R~'2Rl'2Rj'2Ri'2Rg'2Rf'2Rd'2Rc'2RP'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q0?P>Q0=PQQ0;PUQ09P=Q07P9Q05P0Q03POQ01PJQ00PGQ02PPQ04PcQ06PdQ08PfQ0:PgQ0<PiQ0>PjQ0@PlPmP~PoPKP5PnPAPNPSPLPHPEP4PCfbRLPuPp15CuRp,64X22Pp15CLRpP3D8O4b1D@D4D4D4D4D4D4D4D4D4D4E<W0P4O1PePBPePqPePhPePrPePFPePsPePkPePtPeP@E;D3D3D3P115CMRM/6BPMPqPMPhPMPrPMPFPMPsPMPkPMPtPMP@G:D3D3PDPLP?PDPLP:PDPLPRPDPLPIPDPLPTPDPLPVPDPLPbPDPLP7PDPLPaPDPLP;PDPLP6PDPLP8PDPLP\PDPLP[PDPLP_PDPLP^PDPLP`PDPLP]PDPLPZPDPLPYPDPLPWPDPLPXPDPLPuPDPLPvPDPLPwPDPLPxPDPLPyPDPLPzPDPLP{PDPLP|PDPLP}PDPLP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416pBPDfcRLP?A1DL:S0@A1DLRS0>A1DLIS0<A1DLTS0:A1DLVS08A1DLbS06A1DL7S04A1DLaS02A1DL;S00A1DL6S01A1DL8S03A1DL\S05A1DL[S07A1DL_S09A1DL^S0;A1DL`S0=A1DL]S0?A1DLZS0AA1DLYRMA1DLWReA1DLXRSA1DLuRNA1DLvRAPDPLPwPDPLPxPDPLPyPDPLPzPDPLP{PDPLP|PDPLP}PDPLP<E7F0F0F0Rn'2R5'2RK'2Ro'2R~'2Rm'2Rl'2Rj'2Ri'2Rg'2Rf'2Rd'2Rc'2RP'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q0@P>Q0>PQQ0<PUQ0:P=Q08P9Q06P0Q04POQ02PJQ00PGQ01PPQ03PcQ05PdQ07PfQ09PgQ0;PiQ0=PjQ0?PlQ0APmPMP~PePoPSPKPNP5PAPnPHPEP4PCfdRnPvPB15CvRB,64X22PB15CnRBP3D8O4b1F?D4D4D4D4D4D4D4D4D4D4E<W0P4O1PpPqPpPhPpPrPpPFPpPsPpPkPpPtPpP@G:D3D3P115CLRL/6qPLPhPLPrPLPFPLPsPLPkPLPtPLP@E;D3D3PDPnP?PDPnP:PDPnPRPDPnPIPDPnPTPDPnPVPDPnPbPDPnP7PDPnPaPDPnP;PDPnP6PDPnP8PDPnP\PDPnP[PDPnP_PDPnP^PDPnP`PDPnP]PDPnPZPDPnPYPDPnPWPDPnPXPDPnPuPDPnPvPDPnPwPDPnPxPDPnPyPDPnPzPDPnP{PDPnP|PDPnP}PDPnP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416BqPDfeRnP?A1Dn:S0AA1DnRS0?A1DnIS0=A1DnTS0;A1DnVS09A1DnbS07A1Dn7S05A1DnaS03A1Dn;S01A1Dn6S00A1Dn8S02A1Dn\S04A1Dn[S06A1Dn_S08A1Dn^S0:A1Dn`S0<A1Dn]S0>A1DnZS0@A1DnYS0BA1DnWRLA1DnXRpA1DnuRAA1DnvR5A1DnwRNPDPnPxPDPnPyPDPnPzPDPnP{PDPnP|PDPnP}A1Dn<F0F0F0RK'2RS'2Ro'2Re'2R~'2RM'2Rm'2Rl'2Rj'2Ri'2Rg'2Rf'2Rd'2Rc'2RP'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q0AP>Q0?PQQ0=PUQ0;P=Q09P9Q07P0Q05POQ03PJQ01PGQ00PPQ02PcQ04PdQ06PfQ08PgQ0:PiQ0<PjQ0>PlQ0@PmQ0BPMPLP~PpPePAPoP5PSPNPKPHPEP4PCffRKPwPq15CwRq,64X22Pq15CKRqP3D8O4b1D@D4D4D4D4D4D4D4D4D4D4D4E<W0P4O1PBPhPBPrPBPFPBPsPBPkPBPtPBP@E;D3D3P115CnRn/6hPnPrPnPFPnPsPnPkPnPtPnP@G:D3PDPKP?PDPKP:PDPKPRPDPKPIPDPKPTPDPKPVPDPKPbPDPKP7PDPKPaPDPKP;PDPKP6PDPKP8PDPKP\PDPKP[PDPKP_PDPKP^PDPKP`PDPKP]PDPKPZPDPKPYPDPKPWPDPKPXPDPKPuPDPKPvPDPKPwPDPKPxPDPKPyPDPKPzPDPKP{PDPKP|PDPKP}PDPKP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416qhPDfgRKP?A1DK:S0BA1DKRS0@A1DKIS0>A1DKTS0<A1DKVS0:A1DKbS08A1DK7S06A1DKaS04A1DK;S02A1DK6S00A1DK8S01A1DK\S03A1DK[S05A1DK_S07A1DK^S09A1DK`S0;A1DK]S0=A1DKZS0?A1DKYS0AA1DKWS0CA1DKXRnA1DKuRBA1DKvRNA1DKwRSA1DKxR5PDPKPyPDPKPzPDPKP{PDPKP|PDPKP}PDPKP<E7F0F0Ro'2RA'2Re'2Rp'2R~'2RL'2RM'2Rm'2Rl'2Rj'2Ri'2Rg'2Rf'2Rd'2Rc'2RP'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q0BP>Q0@PQQ0>PUQ0<P=Q0:P9Q08P0Q06POQ04PJQ02PGQ00PPQ01PcQ03PdQ05PfQ07PgQ09PiQ0;PjQ0=PlQ0?PmQ0APMQ0CPLPnP~PBPpPNPePSPAP5PoPHPEP4PCfhRoPxPh15CxRh,64X22Ph15CoRhP3D8O4b1F?D4D4D4D4D4D4D4D4D4D4D4E<W0P4O1PqPrPqPFPqPsPqPkPqPtPqP@G:D3P115CKRK/6rPKPFPKPsPKPkPKPtPKP@E;D3PDPoP?PDPoP:PDPoPRPDPoPIPDPoPTPDPoPVPDPoPbPDPoP7PDPoPaPDPoP;PDPoP6PDPoP8PDPoP\PDPoP[PDPoP_PDPoP^PDPoP`PDPoP]PDPoPZPDPoPYPDPoPWPDPoPXPDPoPuPDPoPvPDPoPwPDPoPxPDPoPyPDPoPzPDPoP{PDPoP|PDPoP}PDPoP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416hrPDfiRoP?A1Do:S0CA1DoRS0AA1DoIS0?A1DoTS0=A1DoVS0;A1DobS09A1Do7S07A1DoaS05A1Do;S03A1Do6S01A1Do8S00A1Do\S02A1Do[S04A1Do_S06A1Do^S08A1Do`S0:A1Do]S0<A1DoZS0>A1DoYS0@A1DoWS0BA1DoXS0DA1DouRKA1DovRqA1DowR5A1DoxRAA1DoyRSPDPoPzPDPoP{PDPoP|PDPoP}A1Do<F0F0Re'2RN'2Rp'2RB'2R~'2Rn'2RL'2RM'2Rm'2Rl'2Rj'2Ri'2Rg'2Rf'2Rd'2Rc'2RP'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q0CP>Q0APQQ0?PUQ0=P=Q0;P9Q09P0Q07POQ05PJQ03PGQ01PPQ00PcQ02PdQ04PfQ06PgQ08PiQ0:PjQ0<PlQ0>PmQ0@PMQ0BPLQ0DPnPKP~PqPBP5PpPAPNPSPePHPEP4PCfjRePyPr15CyRr,64X22Pr15CeRrP3D8O4b1D@D4D4D4D4D4D4D4D4D4D4D4D4E<W0P4O1PhPFPhPsPhPkPhPtPhP@E;D3P115CoRo/6FPoPsPoPkPoPtPoP@G:PDPeP?PDPeP:PDPePRPDPePIPDPePTPDPePVPDPePbPDPeP7PDPePaPDPeP;PDPeP6PDPeP8PDPeP\PDPeP[PDPeP_PDPeP^PDPeP`PDPeP]PDPePZPDPePYPDPePWPDPePXPDPePuPDPePvPDPePwPDPePxPDPePyPDPePzPDPeP{PDPeP|PDPeP}PDPeP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416rFPDfkReP?A1De:S0DA1DeRS0BA1DeIS0@A1DeTS0>A1DeVS0<A1DebS0:A1De7S08A1DeaS06A1De;S04A1De6S02A1De8S00A1De\S01A1De[S03A1De_S05A1De^S07A1De`S09A1De]S0;A1DeZS0=A1DeYS0?A1DeWS0AA1DeXS0CA1DeuS0EA1DevRoA1DewRhA1DexRSA1DeyRNA1DezRAPDPeP{PDPeP|PDPeP}PDPeP<E7F0Rp'2R5'2RB'2Rq'2R~'2RK'2Rn'2RL'2RM'2Rm'2Rl'2Rj'2Ri'2Rg'2Rf'2Rd'2Rc'2RP'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q0DP>Q0BPQQ0@PUQ0>P=Q0<P9Q0:P0Q08POQ06PJQ04PGQ02PPQ00PcQ01PdQ03PfQ05PgQ07PiQ09PjQ0;PlQ0=PmQ0?PMQ0APLQ0CPnQ0EPKPoP~PhPqPSPBPNP5PAPpPHPEP4PCflRpPzPF15CzRF,64X22PF15CpRFP3D8O4b1F?D4D4D4D4D4D4D4D4D4D4D4D4E<W0P4O1PrPsPrPkPrPtPrP@G:P115CeRe/6sPePkPePtPeP@E;PDPpP?PDPpP:PDPpPRPDPpPIPDPpPTPDPpPVPDPpPbPDPpP7PDPpPaPDPpP;PDPpP6PDPpP8PDPpP\PDPpP[PDPpP_PDPpP^PDPpP`PDPpP]PDPpPZPDPpPYPDPpPWPDPpPXPDPpPuPDPpPvPDPpPwPDPpPxPDPpPyPDPpPzPDPpP{PDPpP|PDPpP}PDPpP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416FsPDfmRpP?A1Dp:S0EA1DpRS0CA1DpIS0AA1DpTS0?A1DpVS0=A1DpbS0;A1Dp7S09A1DpaS07A1Dp;S05A1Dp6S03A1Dp8S01A1Dp\S00A1Dp[S02A1Dp_S04A1Dp^S06A1Dp`S08A1Dp]S0:A1DpZS0<A1DpYS0>A1DpWS0@A1DpXS0BA1DpuS0DA1DpvS0FA1DpwReA1DpxRrA1DpyRAA1DpzR5A1Dp{RNPDPpP|PDPpP}A1Dp<F0RB'2RS'2Rq'2Rh'2R~'2Ro'2RK'2Rn'2RL'2RM'2Rm'2Rl'2Rj'2Ri'2Rg'2Rf'2Rd'2Rc'2RP'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q0EP>Q0CPQQ0APUQ0?P=Q0=P9Q0;P0Q09POQ07PJQ05PGQ03PPQ01PcQ00PdQ02PfQ04PgQ06PiQ08PjQ0:PlQ0<PmQ0>PMQ0@PLQ0BPnQ0DPKQ0FPoPeP~PrPhPAPqP5PSPNPBPHPEP4PCfnRBP{Ps15C{Rs,64X22Ps15CBRsP3D8O4b1D@D4D4D4D4D4D4D4D4D4D4D4D4D4E<W0P4O1PFPkPFPtPFP@E;P115CpRp/6kPpPtPpP@CWPDPBP?PDPBP:PDPBPRPDPBPIPDPBPTPDPBPVPDPBPbPDPBP7PDPBPaPDPBP;PDPBP6PDPBP8PDPBP\PDPBP[PDPBP_PDPBP^PDPBP`PDPBP]PDPBPZPDPBPYPDPBPWPDPBPXPDPBPuPDPBPvPDPBPwPDPBPxPDPBPyPDPBPzPDPBP{PDPBP|PDPBP}PDPBP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416skPDfoRBP?A1DB:S0FA1DBRS0DA1DBIS0BA1DBTS0@A1DBVS0>A1DBbS0<A1DB7S0:A1DBaS08A1DB;S06A1DB6S04A1DB8S02A1DB\S00A1DB[S01A1DB_S03A1DB^S05A1DB`S07A1DB]S09A1DBZS0;A1DBYS0=A1DBWS0?A1DBXS0AA1DBuS0CA1DBvS0EA1DBwS0GA1DBxRpA1DByRFA1DBzRNA1DB{RSA1DB|R5PDPBP}PDPBP<E7Rq'2RA'2Rh'2Rr'2R~'2Re'2Ro'2RK'2Rn'2RL'2RM'2Rm'2Rl'2Rj'2Ri'2Rg'2Rf'2Rd'2Rc'2RP'2RG'2RJ'2RO'2R0'2R9'2R='2RU'2RQ'2R>Q0FP>Q0DPQQ0BPUQ0@P=Q0>P9Q0<P0Q0:POQ08PJQ06PGQ04PPQ02PcQ00PdQ01PfQ03PgQ05PiQ07PjQ09PlQ0;PmQ0=PMQ0?PLQ0APnQ0CPKQ0EPoQ0GPePpP~PFPrPNPhPSPAP5PqPHPEP4PCfpRqP|Pk15C|Rk,64X22Pk15CqRkP3D8O4b1F?D4D4D4D4D4D4D4D4D4D4D4D4D4E<W0P4O1PsPtPsP@CWP115CBRB/6t16B@PDPqP?PDPqP:PDPqPRPDPqPIPDPqPTPDPqPVPDPqPbPDPqP7PDPqPaPDPqP;PDPqP6PDPqP8PDPqP\PDPqP[PDPqP_PDPqP^PDPqP`PDPqP]PDPqPZPDPqPYPDPqPWPDPqPXPDPqPuPDPqPvPDPqPwPDPqPxPDPqPyPDPqPzPDPqP{PDPqP|PDPqP}PDPqP<E7F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0P416ktfqRq=1D?R?A1Dq:R:A1DqRRRA1DqIRIA1DqTRTA1DqVRVA1DqbRbA1Dq7R7A1DqaRaA1Dq;R;A1Dq6R6A1Dq8R8A1Dq\R\A1Dq[R[A1Dq_R_A1Dq^R^A1Dq`R`A1Dq]R]A1DqZRZA1DqYRYA1DqWRWA1DqXRXA1DquRuA1DqvRvA1DqwRwA1DqxRxA1DqyRyA1DqzRzA1Dq{R{A1Dq|R|A1Dq}RBA1Dq<Rq'2RD'2R1'2Rs'2R5'2RA'2RS'2Rh'2RN'2Rr'2RF'2R~'2Rp'2Re'2Ro'2RK'2Rn'2RL'2RM'2Rm'2Rl'2Rj'2Ri'2Rg'2Rf'2Rd'2Rc'2RP'2RG'2RJ'2ROP:PJPRPGPIPPPTPcPVPdPbPfP7PgPaPiP;PjP6PlP8PmP\PMP[PLP_PnP^PKP`PoP]PePZPpPYP~PWPFPXPrPuPNPvPhPwPSPxPAPyP5PzPsP{P1P|PDPBPqPHPEP4PCfrR0P}Pt15C}R},64X22P}15C0R}P3D8O4b1F?D4D4D4D4D4D4D4D4D4D4D4D4D4D4W0P4O116k@P?POP:PJPRPGPIPPPTPcPVPdPbPfP7PgPaPiP;PjP6PlP8PmP\PMP[PLP_PnP^PKP`PoP]PePZPpPYP~PWPFPXPrPuPNPvPhPwPSPxPAPyP5PzPsP{P1P|PDPHPEP4PCP0P<P@15C<R<,64X22P<P}P3D8O4b19EBqD4D4D4D4D4D4D4D4D4D4D4D4D4D4D4W0P4O1n200100001021100011000W0P4O1n200100001021100011000W0P4O1n200100001021100011000W0P4O1n200100001021100011000W0P4O1n200100001021100011000W0P4O1n200100001021100011000W0P4O1n200100001021100011000W0P4O1n200100001021100011000W0P4O1n200100001021100011000W0P4O1n200100001021100011000W0P4O1n200100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000W0P4O1n201100001021100011000b0b=b<W>o"). Qed.

Ltac wkeep_per_reg x Hx :=
  destruct (reg_enum x) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
  first [ discriminate Hx | kp_value ].

Ltac wkeep_goal :=
  first
    [ kp_chain_w wkeep_per_reg
    | keep_tac
    | let x := fresh "x" in let Hx := fresh "Hx" in
      intros x Hx;
      destruct (reg_enum x) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
      first [ discriminate Hx
            | regnorm; imm_norm;
              first [ reflexivity | apply v_addi_back; reflexivity
                    | rewrite ?v_addi_addi'; first [reflexivity | apply v_addi_k0; reflexivity | klitsg; first [reflexivity | bveq]] ] ] ].

Ltac tail_intro Hag HI HW HS HK :=
  let r := fresh "cr" in let s' := fresh "s" in let mm' := fresh "mm" in let R' := fresh "R" in
  let HP := fresh "HP" in let Hag' := fresh "Hag" in let Hlo' := fresh "Hlo'" in let Hhi' := fresh "Hhi'" in
  let Hr1 := fresh "Hres" in let Hsp := fresh "Hsp" in let Hcs := fresh "Hcs" in
  let Hpres := fresh "Hpres" in let Hnn := fresh "Hnn" in let Htop' := fresh "Htop'" in
  intros r s' mm' R' HP Hag' Hlo' Hhi' Htop' Hr1 Hsp Hcs Hpres Hnn;
  rewrite ?with_vmmaps_twice;
  uaddrH Hpres; uaddrH Hnn;
  eapply (HK r s' mm' R');
  [ exact HP
  | exact Hag'
  | rewrite Hlo'; cbn [ms_lo ms_hi ms_vm ms_mem upd]; exact (minv_lo _ _ HI)
  | rewrite Hhi'; cbn [ms_lo ms_hi ms_vm ms_mem upd]; exact (minv_hi _ _ HI)
  | rewrite Htop'; atop_norm; exact (minv_top _ _ HI)
  | .. ];
  [ exact Hr1
  | rewrite Hsp; first [reflexivity | apply v_addi_k0; reflexivity | apply v_addi_back; reflexivity
                       | rewrite ?v_addi_addi'; first [reflexivity | apply v_addi_k0; reflexivity]]
  | let x := fresh "x" in let Hx := fresh "Hx" in
    intros x Hx; rewrite (Hcs x Hx); revert x Hx; cs_goal
  | win_pres
  | win_nn ].

Ltac mach_tailcall Hp HS Hag HI HW HK THM :=
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R ?pc ?mm ?rom) (with_vmmaps _ ?md)) (tshape (_ ?s) ?L) =>
      eapply rz_at_pc;
      [ eapply (THM (with_vmmaps (ms_vm s) md) R mm rom s);
        first [ lazymatch goal with |- forall (r : _) (s' : mstate), _ => tail_intro Hag HI HW HS HK end
              | call_side Hp Hag HI HW HS ]
      | bveq ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac mach_ret Hp HS Hag HK HI Hret :=
  lazymatch goal with
  | |- realizes _ (mkCfg _ ?md) (tshape (MallocTree.mret ?r ?s') ?L) =>
      unfold MallocTree.mret in HS; cbn [tsafe] in HS;
      change (tshape (MallocTree.mret r s') L) with (L r s');
      eapply rz_step_p; [ mpure Hp | reflexivity
        | eapply step_jalr_x0; [solveF | reflexivity | solveD | regnorm; reflexivity]
        | imm_norm ];
      lazymatch type of Hret with ret_ok ?ra =>
        first [ change (v_jalr ra 0) with ra | pose proof Hret as Hret_eq; unfold ret_ok in Hret_eq; rewrite Hret_eq; clear Hret_eq ] end;
      cbn [ms_lo ms_hi ms_vm ms_mem upd] in HS, Hag |- *;
      lazymatch type of HS with _ ?rv ?sf => eapply (HK rv sf) end;
      [ exact HS | exact Hag
      | cbn [ms_lo ms_hi ms_vm ms_mem upd]; exact (minv_lo _ _ HI)
      | cbn [ms_lo ms_hi ms_vm ms_mem upd]; exact (minv_hi _ _ HI)
      | atop_norm; exact (minv_top _ _ HI)
      | .. ];
      (* [comment removed for export] *)
      repeat match goal with
      | |- getr _ _ = _ => regnorm; imm_norm; rewrite ?v_addi_0;
                           first [reflexivity | apply v_addi_back; reflexivity
                                 | rewrite ?v_addi_addi'; first [reflexivity | apply v_addi_k0; reflexivity | klitsg; first [reflexivity | bveq]]
                                 | idtac]; fail
      | _ => fail
      end;
      try (regnorm; imm_norm; first [reflexivity | apply v_addi_back; reflexivity
                               | rewrite ?v_addi_addi'; first [reflexivity | apply v_addi_k0; reflexivity]]);
      try (lazymatch goal with |- forall x : reg, callee_saved x -> _ => cs_goal end);
      try win_pres;
      try win_nn;
      try (lazymatch goal with |- forall x : reg, wreg _ x = false -> _ => wkeep_goal end)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac branch_cond k :=
  cur_instr ltac:(fun w i =>
    let il := lit_instr i in
    lazymatch goal with
    | |- realizes _ (mkCfg (mkst ?R _ _ _) _) _ =>
      let mk c a b :=
        let H := fresh "Hcond" in
        eassert (H : c (getr R a) (getr R b) = _) by (regnorm; imm_norm; klitsg; reflexivity);
        lazymatch type of H with _ = ?t => clear H; k t end in
      lazymatch il with
      | Branch BC_EQ ?a ?b _  => mk c_eq a b
      | Branch BC_NE ?a ?b _  => mk c_eq a b
      | Branch BC_LT ?a ?b _  => mk c_lts a b
      | Branch BC_GE ?a ?b _  => mk c_lts a b
      | Branch BC_LTU ?a ?b _ => mk c_ltu a b
      | Branch BC_GEU ?a ?b _ => mk c_ltu a b
      end
    end).

(* [comment removed for export] *)
Ltac model_rewrite_cond HS Hc :=
  try (rewrite Hc in HS); try (rewrite Hc); mnorm HS.

(* [comment removed for export] *)
Ltac model_decide_closed HS :=
  let go c :=
    match c with
    | context [?a] =>
        lazymatch type of a with bool => idtac end;
        lazymatch a with true => fail | false => fail | _ => idtac end;
        check_closed_term a;
        let b := eval vm_compute in a in
        let Hc := fresh "Hcc" in
        assert (Hc : a = b) by (vm_compute; reflexivity);
        rewrite ?Hc in HS; rewrite ?Hc; clear Hc; mnorm HS
    end in
  repeat (lazymatch goal with
          | |- realizes _ _ (tshape (MallocTree.mbind (if ?c then _ else _) _ _) _) => go c
          | |- realizes _ _ (tshape ((if ?c then _ else _) _) _) => go c
          end).

(* [comment removed for export] *)
Ltac mach_branch Hp HS :=
  branch_cond ltac:(fun t =>
    first
      [ (* [comment removed for export] *)
        match goal with Hc : ?t' = _ |- _ => unify t' t; model_rewrite_cond HS Hc; mach_if Hp HS Hc end
      | (* [comment removed for export] *)
        check_closed_term t;
        let b := eval vm_compute in t in
        let Hc := fresh "Hc" in
        assert (Hc : t = b) by (vm_compute; reflexivity);
        model_decide_closed HS;
        mach_if Hp HS Hc; clear Hc
      | (* [comment removed for export] *)
        lazymatch goal with
        | |- realizes _ _ (tshape (MallocTree.mbind (if ?c then _ else _) _ _) _) =>
            match c with
            | context [?a] =>
                lazymatch type of a with bool => idtac end; unify a t;
                let Hc := fresh "Hc" in
                destruct a eqn:Hc; rewrite ?Hc in HS; mnorm HS; mach_if Hp HS Hc
            end
        | |- realizes _ _ (tshape ((if ?c then _ else _) _) _) =>
            match c with
            | context [?a] =>
                lazymatch type of a with bool => idtac end; unify a t;
                let Hc := fresh "Hc" in
                destruct a eqn:Hc; rewrite ?Hc in HS; mnorm HS; mach_if Hp HS Hc
            end
        end
      | let Hc := fresh "Hc" in
        destruct t eqn:Hc; rewrite ?Hc in HS; mnorm HS; mach_if Hp HS Hc ]).

(* [comment removed for export] *)
Ltac mach_passert HS :=
  let Hb := fresh "Hal" in let EQ := fresh "EQ" in
  destruct (tsafe_assert_inv _ _ _ _ HS) as [Hb EQ];
  rewrite EQ in HS; rewrite EQ; clear EQ; mnorm HS.

(* [comment removed for export] *)
Lemma v_addiw0_lw : forall v : word, v_addiw (v_lw v) 0 = v_lw v.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "p'0h04__x1h17__arithh26__sat0h36__sat1h46__sat2h56__sat3h65heq_yh71Hh84__ffh98__varmaph:5__with;1zh<2H0h=2H1h>2H2h?2H3h@2HahA6__sat4hB1qhC1rhD4__p1hE6__sat5hF6__sat6hG1EhH2b1hI2b2hJ1li001lhK1ni011nhL2HrhM1ehN1si021shO1vhP1yp%0p&0p;1p;3p;2p;6p;4p;8p;7g002Fj1BTg003Pj1ZTg003nj1ATg006Wj38Tg00BZj26Tg021gj3xTg02I1j29Tg00CDj2WTg01]^j22Tg01nmj2Ej1kTg00Ffj2KTg00gfj6[Tg01J:k206Tg01G]j1cTg02IXk300Tg02JHj1{Tg02K6j1aTg00kMj2;Tg02KSj2vTg00moj24Tg02D1R0j2sTg009nj1FTg00kij2XTg023]j23Tg01UUR1j2^Tg025lj2?Tg00mGj2VTg00nKj3UTg002kj1LTg00@Rj1jTg001fj1iTg010mj2hTg012Gj1gTg012ej1fTg013Pj2eTg0143j2]Tg014Vj3\Tg02L:j3dTg01`Gj3ITg0159k205Tg015[k204Tg016Gk303Tg016fj4~Tg00_0j1}Tg02L]j2zTg01Wkj6yTg019UR2j2DTg02A1j3STg011Kj1wTg02M@j4_Tg022ej3uTg022Kj3tTg01Efj2CTg024=j2QTg024nj2OTg025Oj2=Tg026Ij2PTg0270j2MTg027Wj2NTg028=j2RTg01FCj3rTg02Maj1qTg02NBj8pTg020?j2bTg00S8j1oTg02N_j2nTg01:0j4YTg01:[j7|Tg01XOj7mTg01;?k801Tg001Hk602Tg028cj6lTg00LIR3f1R4f0R538p=0f2R61445'Dp=7g00MSR7/;5p=112459836p=<P3P4g02:mP5CYp=JP4g01<JR8g01<iR9P9g01=IR:P5g01=iF|p=5P3P4g01Y3P5CYp=HP3P4g01;cP5CYp=TP6P8P9P9P:P4P5Fmp=@f3R;P8P9P9P:P6P4P5L01p=GP3f4R<P;P6P4P5J02p=:P4P8P9P9P:P5Elp=`A8357p=>g00J8R=#BR>#B#B#B#BR?#BR@#ZRA#ARBg023?RC%A5RD%A4REP2%A6?84516;616;4'0R2[16641665'0%A;?864[RF%A<?8;6\2Ax645P5n2001000000120000000WIWHWKPF^IE^HD^KCP5PA%Z?RD16A4RE,9DRF,WAR2,6AS00/27'9RG,WARHP21EAG16A6,9DR2,WA,6A,05X;31EAFRI1257,9D,EA/05X;3P3P3%kARJPJ12I7S01,9DPFP3\3/KJPI19D5/02X;3g02O[RJ98CDRKPCPDPCp-0RLP5g01KXRMg01?QRNn0110100020010000XMCg00N1PJP5E[PM206M5b<W7%cKe:00DE%{DRE#a/;F?7FEP2P31v571457R2%15RE'sP01447%14%F>R>%F@R@'XR0,36RK/06RJA<K60RC'^P5146713;0RO/0;RP12;0RQ,0ORRP3%F=RS/?0RT,2;RU/30RV12<0RW,05X;3RXPUPXf6RX,6A,9DRY,K310;YRYeRZPY1V>@R[147>R\%1@1470R][[R^%1>R_AU>@4VNW@R@%10R`\N^@_Ra%L=#L#L#LRb#FRc,V>Rd%1c1X>cRe,47[\\RfAU>c4VNX@_Rc%1e\N^@_Rgg01?mRh#jRi%ihRh1h34Rj%g3Rk%f3Rl1e3=R=1]3S1]3>Rm=\3ARn5d35I3RoAI3=nRp'J'5205l:RqP5P6g00J]Rrg00RXRs'K20456=8rsdB03374C~Rsb8b9b:X03125T1250Rr'0^03P5f9RtO1b1b2b3b4b5b6PVPZPYP[P^P@PaPdPfPcPgPiPhPjPkPl1]37RV,H=,5l%}9RuPl%Zb9\3mRb,z3/T=,5lRvPlP8P9P9P:P;EyR:5@lPu1TVo,5l1Hon,5l5@lCGCGPqPsb8b9b:X03XDL%aeRo/;4/D6126TRT#1?7T0[\2^03^DLP514tePtPXf:R2O4b1b2b3b4b5b69SU0D:POP;PSP0PZPYP[P^P@PaPdPfPcPgPiPh%w3S02Pk1JnV,5l,`lPqPsb8b9b:%>0RSPM[P5b1b2b3b4b5b6C_E[3uWJP5O1%16RUPZPYP[P^P@PaPdPfPcPgPiPhPjPkPl1TV=,5lRTPuPl1H=b,5lR99@l:Pu1H=n,5l9@lTCGCGPqPsb8b9b:X03XDLA764eA7U60[\E^03^DLP51;otPtPXP2O4b1b2b3b4b5b69S;09tPRWJP5O1n200110200021110011100bN1350RR/0510Rr'^P11340R1/04A<14012Ke%F?R?,X>RK'3/Ce/06P5P;125eR6/3K/Ce/0<X;3S0312;eR;1C5eR1/0<X;3PZPYPdPfPcPgP[P^P@Paf8RR/Q0%1R1320RR#1\`[1Ot0%cSRP1=20,?0=<2R[1P20f;RR/30RX#1S04?7X0\]1MR01407RLf<RE/30RU,401;U7'D[1NE0f=RT/=0Rn#>\S1RT0f>R:/30R8/0:\S1=:0RwP3f?Rx/30RyP3PiPhPjPkAI3=bRz=r3b/J=,5lPqPsb8b9b:X03S051C6e/05^03S06P5fAR=O1b1bCbBb?b>b=b<b7b2b3b4b5bAb613;KPZPY1V>?R{%1?147K[\\R\AU>?4VNX@_R?%1K\N^@_R_PdPfPcPgP[P^P@Pa1Q20S07%12%1URN\`[S081OR0S091=E0,?0=<EU\PS0:1PE0S0;13T0R>#1S0<?7>0\]S0=1MT0S0>14081;87'D\LS0?1N:0S0@1=x0S0A#>\SS0B1Rx0S0Cf@R|/30S0D/0|\SS0E1=|0R}P313=0R~P3PiPhPjPkPlA@lv9Pu1TVz,5lA\3mDRm,Hz,5l5@lCGPqPsb8b9b:X03Ru1;o5?75e124eR4#1?74K[^03R4P5fCRofDR9O2b1bCbBb?b>b=b<b7b2b3b4b5bAbEbFb69S;KD:POP5D:XGJP5O1PQQ03PZPYP{P\P?P_PdPfPcPgP[P^P@PaQ07Q08Q09Q0:Q0;Q0=Q0>Q0?Q0@Q0BQ0CQ0EP}P3P~P3PiPhPjPkAd3mm9I3zAI3pb'J,5lPqPsb8b9b:X031?KKRb,26?<re^03P5PoO1b1bCbBb?b>b=b<b7b2b3b4b5bAbEbFb612;b?<QeP312<eRQ/2bRb135K/Cef5R;'0X;313QKRo101;X;3R;PQP;f7,6A,9DR;,K310<;R;eR<P;PdPfPcPgP[P^P@Pa1Qt0%1tQ04\`[1O201=R0,?0=<RX\P1PR0A7NU0\]1ME0140>1;>7'D\L1NT0%>w\S1R:010yx\SQ0AP3Q0DP3Q05Q06P5fBRwO1b1bCbBb?b>b=b<b7b2b3b4b5bAb6PoP<P;P{P\P?P_PdPfPcPgP[P^P@Pa1QR0Ro%1RQ0<\`[R`1OE0RE1?0n=<T>\PRP1PT0RT%18?780\]R]1M:0R:140y1;y7'D\LRL1Nx0Rx%>}\SR}1R|0R|10~=\SRS1==0R=P313w0RwP3PuP4P5P9fEO2b1bCbBb?b>b=b<b7b2b3b4b5bAbEbFb69SQKD:13bKPQPKPKP<P;P{P\P?P_P[P^P@PaPdPfPcPgPoP`PEPPPTP]P:PLPxP}P|PSP=P3PwP3PiPhQ02Pk1JmV,5l,`lPqPsb8b9b:%>KPM[P5b1bCbBb?b>b=b<b7b2b3b4b5bAbEbFb6C_D:12WeP5E[b7POP5D:XGCP5O1n200100000021100011000bG1EA5RC/2e,ED/Ce/05e19DC/05ebPbLQ01%qID:GpQ001bAFD:16AH1bAGD:O4b7%o5R5/n7=8B5eWOo"). Qed.

Lemma and3_mod4 : forall a : word, c_eq (v_andi a 3) (Z_to_bv 64 0) = true -> (bv_unsigned a mod 4 = 0)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStep ()) [] "h02H0h11Hh22H1h36__sat2h42Hah57__arithh64__ffh74__p1h86__sat1h98__varmaph:5__with;4__x1h<1zh=1ah>1bh?1mh@1nhA2H2hB2H3hC2H4hD2H5hE2H6hF2H7hG2HlhH6__sat3hI6__sat4hJ6__sat5hK6__sat6hL1qhM1rp;1p;2p;6p;3p;7p;4p;8g002Fj19Tg003Pj1STg003nj1cTg002kj1ZTg009nj1FTg02P9j2PTg00CDj2MTg02Q4j2bTg01O[j2HTg01Qhj2XTg00BZj21Tg01nmj28Tg02Qmj23Tg020?j2QTg00gfj6=Tg01[`j1lTg00kij2LTg00moj22Tg019UR0j25Tg00kMj2;Tg01UUj2?Tg02RKj2_Tg00mGj2JTg00nKj3ITg00@Rj1^Tg001fj1]Tg011Kj1\Tg012Gj1[Tg012ej1YTg0143j2@Tg01fNj7WTg0159j2VTg00Ffj2UTg015[j2TTg016Gj3wTg016fj4vTg023]j26Tg026Ij2RTg024=j2uTg024nj2tTg01G]j1rTg025Oj2ATg025lj2pTg01]^j2oTg0270j2nTg027Wj2kTg028=j2iTg010mj2hTg014Vj3NTg00_0j1gTg013Pj2fTg02S0j1eTg02SNj3OTg001Hj6jTg01AEj4dTg01oSj3mTg006Wj3ETg01Wkj6aTg01:0j4KTg01:[j7qTg01XOj7`Tg01;?j8sTg00J]R1f0R2g00RXR33Ep=>g00LIR4f1R5;E2p=4g00MSR6/;2p=0P5g01<JR7g01<iR8P8g01=IR9P2Eap=GP4P5g01;cP2CKp=<P5P7P8P8P9P2g01=iFqp=7AE426p=:P4P5g01Y3P2CKp=Cf2R:P7P8P8P9P5P2F`p=Bf3R;P7P8P8P9P:P5P2Gsp=Dg00J8R<#9R=#9#9#9#9#9R>#SR?#c%Z<#FR@,P21M?6RA'b#>P01H52#>14:5[RB14521H:5#>RC[14;:\C1X52P5n2001000000120000000X?4X@4PB^?4^@4P21P:@,1?RB11?ARAP5O314BAP411?;18?@RB'3RC,M?,1?142AX<4P218?CRD1Q?CE=14DAP4PAf5RA,1?RD/3B,8?/42X<4P218?6RC1Q?6E=f4RE,1?/3B,8?/4C%lA%0D%F=RC%F>R>'LRB,2D'5f6RD,1?RF/3@RG#0RH1;G@RGP01352#0%0:%05RI'?RJ[%02RK,?I13:5#0[RL13;:#0\J1_52P2n2001000000120000000X>4X=4PL^>4^=4P2f7RL,1?RJP@1JC>RM126CRN%0>126B[[RO%0CRPg01?QRQAIC>5UW4R>%0B\Q^4PRRP0f9,1?RS#0RT12SBRSf:,1?RU#0RV%0@RW'?P;f;RX,1?RY#0RZf<,1?R[/2BR\p-0R]g01?mR^#^R_%]^R^%\4R`%[4Ra%Y4RbP7P8P8P91Gb:1@46R71@4@Rc'<,7bFW1Vb9R9P2P:1U131T2:#>dAw465CvR3b6b9b:W71?2W^7]P2f>,1?RW#0O1b5W2W0P5P2O2n2001000000120000000b8b3O3b2P41LCCR1,6F1;2@RdX<41RF11261Re16J1Rf#012f1'5[1JCCPe\P\NAICC5VQX4P%01RN\Q^4PPMPOP>PR1uY1f=RQ,1?Rf/61Rg#0\N\Z1t[1%:1Rh#r1Af1,p1/og,4f[1Rf116W1Rg#012g1'5\e1nW11216f?,1?Rg/61Ri,211;i6'5[1kg1f@,1?Rg/A1#:\h1ig1fA,1?Rg/61/4g\h1Ag1P4fBRg,1?/61P4P0fC,1?Rh#012hB1;5@RhPQfE,1?#0fF,1?/2BPXP5O1%0A\NP_P^1h45RNPaPbPb1@4CRA%S=5N4R=,C7,7b%g8R81Gb;1f4<R</C=,7b5BbCDP81<<c,7bRcCDP9P3b6b9b:X;4X7]1251,5:\ePh[^;4^7]P2%0DPDPgO3b5b3WFW0P5P2O2n2001000000121000000bMbLbEbDbCbBbAb3bHbIbJbKb2%eCRg,3FPMPOP>PRP0f8,1?RD#012DBPPP:12YBP_P^P`Pa1<7A,7bP9P3b6b9b:PPP2b5R`W2X0VP5P2O2n2001000000120000000b8b39OFCEjCd15HGP413J@RJ,8?%:2X<4RGP:PJPMPOP>PRP0PTPS13U@RS#012SB'5P;P_P^PNPaPb1<7<,7bR7=BbcP8AN4A?,C<,7b9Bb7CDP9P3b6b9b:X;415Kd125B,5I[^;4P213W@PLO2b5X2\X0ZP5P2O2n2001000000121000000b8b39m?JE=%:JP413DgPGP216D1R1PMPOP>PRP0PV12UBPPPE%0[12fBP`W2W0P5P2O2n2001000000120000000b8b39ODCE=%:1P2b1b1bGb0b1b1b1b0W1W=o"). Qed.

Ltac mach_cas Hp HS Hag HI :=
  let Hok := fresh "Hok" in let Hso := fresh "Hso" in let EQ := fresh "EQ" in
  unfold m_sb, m_sh, m_sw, m_sd in HS |- *;
  let body ma mv :=
    lazymatch type of Hok with acc_ok ?scur _ _ = true =>
    match goal with
    | Hrd : rdn _ (ms_mem _) ma 4%nat = Some ?bs, Hv : bytes_le_to_Z ?bs = _,
      Hal : c_eq (v_andi ma 3) (Z_to_bv 64 0) = true |- realizes ?segs _ _ =>
      (* [comment removed for export] *)
      eapply rz_step_p; [ mpure Hp | reflexivity
        | eapply (step_lrw segs _ _ _ _ _ _ _ ma bs (le_val bs));
          [ solveF | reflexivity | solveD | reflexivity
          | addr_tac
          | exact (and3_mod4 _ Hal)
          | exact (magree_rd _ _ _ 4%nat _ Hag (minv_lo64 _ _ HI) Hok Hrd)
          | exact Hv ]
        | ];
      (* [comment removed for export] *)
      eapply rz_step_p; [ mpure Hp | reflexivity
        | eapply step_bne_ft_r; [ solveF | reflexivity | solveD | regnorm; reflexivity ] | ];
      (* [comment removed for export] *)
      rewrite EQ in HS; rewrite EQ; clear EQ;
      eapply rz_step_p; [ mpure Hp | reflexivity
        | eapply (step_scw_ok segs _ _ _ _ _ _ _ _ ma mv);
          [ solveF | reflexivity | solveD | reflexivity
          | addr_tac | addr_tac
          | exact (and3_mod4 _ Hal)
          | exact (magree_sok _ _ _ 4%nat Hag (minv_lo64 _ _ HI) Hok Hso) ]
        | mpost HS ];
      apply (magree_wbytes scur _ ma (word_to_le_bytes 4 mv) (ms_vm scur)) in Hag;
      (* [comment removed for export] *)
      mach_br_dir Hp HS false ltac:(first [apply c_eq_refl | vm_compute; reflexivity]);
      (* [comment removed for export] *)
      mach Hp HS;
      mach_br_dir Hp HS false ltac:(rewrite ?v_addiw0_lw; apply c_eq_refl)
    end end in
  lazymatch type of HS with
  | tsafe (MallocTree.mbind (m_st _ ?ma ?mv) _ _) _ =>
      destruct (tsafe_st_inv _ _ _ _ _ _ HS) as (Hok & Hso & EQ); body ma mv
  | tsafe (m_st _ ?ma ?mv _) _ =>
      destruct (tsafe_st_inv0 _ _ _ _ _ HS) as (Hok & Hso & EQ); body ma mv
  end;
  mnorm HS.

(* [comment removed for export] *)
Ltac mstep Hp HS Hag HI HW :=
  cur_instr ltac:(fun w i =>
    let il := lit_instr i in
    lazymatch goal with
    | |- realizes _ _ (tshape (MallocTree.mbind (massert (c_eq (v_andi (at_ _ 28) 3) _)) _ _) _) =>
        (* [comment removed for export] *)
        mach_passert HS
    | |- _ =>
    lazymatch il with
    | Load _ _ _ (@BV _ 2 _) _ => mach_stk_ld Hp HS Hag HI
    | Store _ (@BV _ 2 _) _ _ => mach_stk_st Hp HS Hag HI
    | Load _ _ _ _ _ => mach_ld Hp HS Hag HI
    | Store _ _ _ _ => mach_st Hp HS Hag HI
    | Lr _ _ _ _ _ => mach_cas Hp HS Hag HI
    | Branch _ _ _ _ =>
        lazymatch goal with
        | |- realizes _ _ (tshape (MallocTree.mbind (massert _) _ _) _) => mach_assert Hp HS
        | |- _ => mach_branch Hp HS
        end
    | Jalr _ _ _ => mach_jr Hp HS
    | Jal (@BV _ 0 _) _ => mach Hp HS
    | Jal _ _ => fail "mstep: jal call: manual"
    | _ => mach Hp HS
    end end).

Ltac mrun Hp HS Hag HI HW := repeat (mstep Hp HS Hag HI HW).

(* [comment removed for export] *)
Ltac mrun_until Hp HS Hag HI HW pcZ :=
  let pcZ := eval vm_compute in pcZ in
  repeat (cur_pc ltac:(fun u => tryif constr_eq u pcZ then fail else mstep Hp HS Hag HI HW)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac regval r k :=
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R _ _ _) _) _ =>
      let H := fresh "Hrv" in
      eassert (H : getr R r = _) by (regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity);
      lazymatch type of H with _ = ?v => clear H; k v end
  end.

Ltac cur_mstate HS k :=
  lazymatch type of HS with tsafe (?f ?sb) _ => k sb end.

(* [comment removed for export] *)
Ltac apply_cut tac :=
  lazymatch goal with
  | |- realizes _ ?C (tshape ?tg ?L) =>
      eapply (rz_tshape_eq C _ tg L); [ tac | tnorm_eq ]
  end.

Ltac use_cut CUT res Hag HI HW HS :=
  cur_mstate HS ltac:(fun sb =>
    lazymatch res with
    | @nil Z => apply_cut ltac:(eapply (CUT tt sb))
    | @cons Z ?r1 (@nil Z) =>
        regval constr:(@BV 5 r1 I) ltac:(fun v1 => apply_cut ltac:(eapply (CUT v1 sb)))
    | @cons Z ?r1 (@cons Z ?r2 (@nil Z)) =>
        regval constr:(@BV 5 r1 I) ltac:(fun v1 =>
          regval constr:(@BV 5 r2 I) ltac:(fun v2 => apply_cut ltac:(eapply (CUT v1 v2 sb))))
    end);
  [ exact Hag | exact HI | win_same | keep_tac | .. ];
  [ .. | exact_HS HS ]; try (regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity).

Ltac join_intro Hag HI HW HS res :=
  let x := fresh "jv" in let s' := fresh "s" in let mm' := fresh "mm" in let R' := fresh "R" in
  let Hkeep := fresh "Hkeep" in let HJ := fresh "HJ" in let HInew := fresh "HI" in
  clear Hag HS;
  lazymatch res with
  | @nil Z => intros x s' mm' R' Hag HInew HJ Hkeep HS
  | @cons Z _ (@nil Z) => let Hres := fresh "Hres" in intros x s' mm' R' Hag HInew HJ Hkeep Hres HS
  | _ => let Hr1 := fresh "Hres" in let Hr2 := fresh "Hres" in let x2 := fresh "jv" in
         intros x x2 s' mm' R' Hag HInew HJ Hkeep Hr1 Hr2 HS
  end;
  clear HI; rename HInew into HI; note_win HI;
  frame_facts HW mm';
  keep_facts Hkeep; mnorm HS.

Ltac mach_join Hp HS Hag HI HW J wl res :=
  let J := eval vm_compute in J in
  let Jlit := constr:(@BV 64 J ltac:(vm_compute; exact I)) in
  lazymatch type of HI with minv ?s0 _ =>
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) (with_vmmaps _ ?md0)) (tshape (MallocTree.mbind ?M ?K ?s) ?L) =>
    lazymatch type of HS with tsafe _ ?P =>
    let CUT := fresh "CUT" in
    lazymatch res with
    | @nil Z =>
      enough (CUT : forall x (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        tsafe (K x s') P ->
        realizes segs (mkCfg (mkst R' Jlit mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (K x s') L))
    | @cons Z ?r1 (@nil Z) =>
      let R1 := constr:(@BV 5 r1 I) in
      enough (CUT : forall x (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        getr R' R1 = x ->
        tsafe (K x s') P ->
        realizes segs (mkCfg (mkst R' Jlit mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (K x s') L))
    | @cons Z ?r1 (@cons Z ?r2 (@nil Z)) =>
      let R1 := constr:(@BV 5 r1 I) in let R2 := constr:(@BV 5 r2 I) in
      enough (CUT : forall x1 x2 (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        getr R' R1 = x1 -> getr R' R2 = x2 ->
        tsafe (K (x1, x2) s') P ->
        realizes segs (mkCfg (mkst R' Jlit mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (K (x1, x2) s') L))
    end;
    [ (* [comment removed for export] *)
      repeat (cur_pc ltac:(fun u => tryif constr_eq u J then fail else mstep Hp HS Hag HI HW));
      [> use_cut CUT res Hag HI HW HS ..]
    | (* [comment removed for export] *)
      join_intro Hag HI HW HS res ]
    end
  end end.

(* [comment removed for export] *)
Ltac use_cut_bool CUT Jt Hag HI HW HS :=
  cur_mstate HS ltac:(fun sb =>
    cur_pc ltac:(fun u => tryif constr_eq u Jt then apply_cut ltac:(eapply (CUT true sb))
                          else apply_cut ltac:(eapply (CUT false sb))));
  [ exact Hag | exact HI | win_same | keep_tac
  | cbv beta iota; first [ exact I | regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity | repeat split ]
  | exact_HS HS ].

Ltac join_intro_bool Hag HI HW HS :=
  let x := fresh "jb" in let s' := fresh "s" in let mm' := fresh "mm" in let R' := fresh "R" in
  let Hkeep := fresh "Hkeep" in let HJ := fresh "HJ" in let HInew := fresh "HI" in let HX := fresh "HX" in
  clear Hag HS;
  intros x s' mm' R' Hag HInew HJ Hkeep HX HS;
  clear HI; rename HInew into HI; note_win HI;
  frame_facts HW mm';
  keep_facts Hkeep;
  destruct x; cbv beta iota in HX; mnorm HS.

Ltac mach_join_bool Hp HS Hag HI HW Jt Jf wl XR :=
  let Jt := eval vm_compute in Jt in let Jf := eval vm_compute in Jf in
  let Jtl := constr:(@BV 64 Jt ltac:(vm_compute; exact I)) in
  let Jfl := constr:(@BV 64 Jf ltac:(vm_compute; exact I)) in
  lazymatch type of HI with minv ?s0 _ =>
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) (with_vmmaps _ ?md0)) (tshape (MallocTree.mbind ?M ?K ?s) ?L) =>
    lazymatch type of HS with tsafe _ ?P =>
    let CUT := fresh "CUT" in
    enough (CUT : forall (x : bool) (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        XR x R' ->
        tsafe (K x s') P ->
        realizes segs (mkCfg (mkst R' (if x then Jtl else Jfl) mm' rom) (with_vmmaps (ms_vm s') md0))
                 (tshape (K x s') L));
    [ repeat (cur_pc ltac:(fun u => tryif constr_eq u Jt then fail else
                               tryif constr_eq u Jf then fail else mstep Hp HS Hag HI HW));
      [> use_cut_bool CUT Jt Hag HI HW HS ..]
    | join_intro_bool Hag HI HW HS ]
    end
  end end.

(* [comment removed for export] *)
Ltac mstepx Hp HS Hag HI HW HK Hret calls :=
  cur_instr ltac:(fun w i =>
    let il := lit_instr i in
    lazymatch il with
    | Jal (@BV _ 1 _) ?imm =>
        lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          let t := eval vm_compute in (bv_unsigned (v_addi pc (bv_signed imm))) in
          calls Hp HS Hag HI HW t
        end
    | Jalr (@BV _ 0 _) (@BV _ 1 _) _ => first [ mach_jr Hp HS | mach_ret Hp HS Hag HK HI Hret ]
    | _ => mstep Hp HS Hag HI HW
    end).

Ltac mrunx Hp HS Hag HI HW HK Hret calls := repeat (mstepx Hp HS Hag HI HW HK Hret calls).
Ltac mrunx_until Hp HS Hag HI HW HK Hret calls pcZ :=
  let pcZ := eval vm_compute in pcZ in
  repeat (cur_pc ltac:(fun u => tryif constr_eq u pcZ then fail else mstepx Hp HS Hag HI HW HK Hret calls)).

(* [comment removed for export] *)
Ltac no_calls Hp HS Hag HI HW t := mach_jal Hp HS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac use_cut_k CUT Kx Hag HI HS :=
  lazymatch goal with
  | |- realizes _ _ (tshape (Kx ?x ?sb) _) =>
      eapply (CUT x sb);
      [ exact Hag | exact HI | win_same | keep_tac
      | cbv beta match; repeat split;
        try (regnorm; imm_norm; rewrite ?v_addi_0; klitsg; first [reflexivity | bveq])
      | exact HS ]
  end.

Ltac join_intro_k Kx Hag HI HW HS :=
  let x := fresh "jv" in let s' := fresh "s" in let mm' := fresh "mm" in let R' := fresh "R" in
  let Hkeep := fresh "Hkeep" in let HJ := fresh "HJ" in let HInew := fresh "HI" in let HX := fresh "HX" in
  clear Hag HS;
  intros x s' mm' R' Hag HInew HJ Hkeep HX HS;
  clear HI; rename HInew into HI; note_win HI;
  frame_facts HW mm';
  keep_facts Hkeep;
  subst Kx; cbv beta in HS; cbv beta;
  (* [comment removed for export] *)
  revert HS; revert HX; revert x.

Ltac mach_join_k Hp HS Hag HI HW HK Hret calls XTY PCF wl XR :=
  lazymatch type of HI with minv ?s0 _ =>
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) (with_vmmaps _ ?md0)) (tshape (MallocTree.mbind ?M ?K ?s) ?L) =>
    lazymatch type of HS with tsafe _ ?P =>
    let Kx := fresh "Kx" in
    set (Kx := K) in HS |- *;
    let CUT := fresh "CUT" in
    enough (CUT : forall (x : XTY) (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        XR x R' ->
        tsafe (Kx x s') P ->
        realizes segs (mkCfg (mkst R' (PCF x) mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (Kx x s') L));
    [ repeat (lazymatch goal with
              | |- realizes _ (mkCfg (mkst _ ?pc _ _) _) (tshape (Kx ?x _) _) =>
                  (* [comment removed for export] *)
                  let u := eval vm_compute in (bv_unsigned pc) in
                  let j := eval lazy in (bv_unsigned (PCF x)) in
                  tryif constr_eq u j then fail else mach Hp HS
              | |- _ => mstepx Hp HS Hag HI HW HK Hret calls
              end);
      [> use_cut_k CUT Kx Hag HI HS ..]
    | join_intro_k Kx Hag HI HW HS ]
    end
  end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac mrun_to_k Hp HS Hag HI HW HK Hret calls Kx PCF :=
  repeat (lazymatch goal with
          | |- realizes _ (mkCfg (mkst _ ?pc _ _) _) (tshape (Kx ?x _) _) =>
              let u := eval vm_compute in (bv_unsigned pc) in
              let j := eval lazy in (bv_unsigned (PCF x)) in
              tryif constr_eq u j then fail else mach Hp HS
          | |- _ => mstepx Hp HS Hag HI HW HK Hret calls
          end).

(* [comment removed for export] *)
Ltac use_cut_kx CUT Kx Hag HI HS :=
  lazymatch goal with
  | |- realizes _ _ (tshape (Kx ?x ?sb) _) =>
      eapply (CUT x sb);
      [ exact Hag | exact HI | win_pres | win_nn | keep_tac
      | cbv beta match; repeat split;
        try (regnorm; imm_norm; rewrite ?v_addi_0; klitsg; first [reflexivity | bveq])
      | exact HS ]
  end.

Ltac mach_cut_core HS Hag HI HW XTY PCF wl XR exlo exhi CUT Kx :=
  lazymatch type of HI with minv ?s0 _ =>
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) (with_vmmaps _ ?md0)) (tshape (MallocTree.mbind ?M ?K ?s) ?L) =>
    lazymatch type of HS with tsafe _ ?P =>
    set (Kx := K) in HS |- *;
    enough (CUT : forall (x : XTY) (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 ->
                           ~ (exlo <= bv_unsigned a < exhi) -> mm' a = mmF a) ->
        (forall a : word, exlo <= bv_unsigned a < exhi -> mm' a <> None) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        XR x R' s' ->
        tsafe (Kx x s') P ->
        realizes segs (mkCfg (mkst R' (PCF x) mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (Kx x s') L));
    [ (* [comment removed for export] *)
    | let x := fresh "jv" in let s' := fresh "s" in let mm' := fresh "mm" in let R' := fresh "R" in
      let Hkeep := fresh "Hkeep" in let HJ := fresh "HJ" in let HJn := fresh "HJnn" in
      let HInew := fresh "HI" in let HX := fresh "HX" in
      clear Hag HS;
      intros x s' mm' R' Hag HInew HJ HJn Hkeep HX HS;
      clear HI; rename HInew into HI; note_win HI;
      uaddrH HJ; uaddrH HJn;
      frame_facts HW mm';
      keep_facts Hkeep;
      subst Kx; cbv beta in HS; cbv beta;
      revert HS; revert HX; revert x ]
    end
  end end.

Tactic Notation "mach_cut" constr(HS) constr(Hag) constr(HI) constr(HW)
    constr(XTY) constr(PCF) constr(wl) constr(XR) constr(exlo) constr(exhi) "as" ident(CUT) ident(Kx) :=
  mach_cut_core HS Hag HI HW XTY PCF wl XR exlo exhi CUT Kx.

(* [comment removed for export] *)
Ltac show := lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) (tshape ?t _) =>
  idtac "PC" pc; lazymatch t with
  | mbind ?a _ _ => idtac "HEAD" a
  | ?x => idtac "TERM" x end end.
