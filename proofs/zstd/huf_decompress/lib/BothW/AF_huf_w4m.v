(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4m.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_w4m () := "C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begI47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4m3W4MC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2ex00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m?z4_C8_of_u64arrC47Corelib4Init3Nat3mulC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m@z4_cells_size_C8C47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u64arrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init9Datatypes3nat00c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4m4W4F0K46Stdlib9micromega=RingMicromega3Op201c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4m<w4_sp_boundsC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2or00K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m9z4_magreeC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4m9w4_magreec5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4m8w4_aheapC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accK4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4m7AW4_EPIc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4m6w4_epiC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4m7AW4_ERR".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Definition AW4_SLOW : Z := 0x89a98.     (* [comment removed for export] *)
Definition AW4_ERR : Z := 0x8c660.      (* [comment removed for export] *)
Definition AW4_EPI : Z := 0x8c660.      (* [comment removed for export] *)
Definition AW4_M5 : Z := 14757395258967641293.    (* [comment removed for export] *)
Definition AW4_M7 : Z := 2635249153387078803.     (* [comment removed for export] *)
Definition AW4_FX : Z := 0x892c4.
Definition AW4_K21 : Z := 65620.
Definition AW4_KTB : Z := 134547.
Definition AW4_KSB : Z := 0x7fff8000.
Definition AW4_FA : Z := 0x87fe4.

Section CANSEC1. Context {rc : runConstT}.
Section W4.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl lo : Z) (src : list Z) (cbs : list byte) (pdt pb : aptr).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -480).
  Notation n := (zlen src).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis HDB : In (HB pb DST dcap) LB.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma w4_sp_bounds : 0x10007fff8000 <= SPF /\ SP <= 2^47 /\ ATOP + 4096 <= lo /\ lo + 8192 <= SP.
Proof using AH LOA LOS SPT.
  pose proof (AI_layout AI L RNG st LB m0 AH) as HL. pose proof (@ATOP_lo rc) as HA.
  unfold HUF_DEC_STACK_A in LOS. lia.
Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma w4_aheap : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> AHEAP AI L RNG st LB mm.
Proof using AH HDB LOA LOS SPT.
  intros mm MU WM. pose proof (AI_layout AI L RNG st LB m0 AH) as HL. unfold HUF_DEC_STACK_A in LOS.
  eapply (AI_frame AI); [exact AH | exact MU | exact WM |].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; unfold aclient_range, aclient_app_range.
  - left. left. lia.
  - right. left. exists (HB pb DST dcap). split; [exact HDB|]. cbn. lia.
Qed.

  Lemma w4_magree : forall mm, munch DW m0 mm -> wmono bsegs m0 mm ->
    magree bsegs (fun a => aclient_addr CI LB SP a /\ ~ (DST <= a < DST + dcap)) m0 mm.
Proof using AH HDB HDT LOA LOS SPT.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4m ()) ["CANSEC1"; "W4"] "h02MUh12WMh22mmp;1p;2p;4p;3p;Hg004Aj10Tg00@@j14Tg00`jj12Tg00aMj15Tg00fKj2<Tg00@^j2;Tg00fkj41Tg005Dj27Tg00HSj16Tg00I3j33Tg00oXj38Tg010Lj39Tg01JMlH:Tg00XC#0#0#0R0#0#0#0#4R1#2%40#2#5[g00U?R0/<0R2P0P0p,2loR3p,2spR4,;1C1P0P0p,3DSTR0p,4dcapR1,70C1%6253233p,2m0R2f0R538g016Sf1R6792p,2rcp,2AIp,1Lp,3RNGp,2stp,2LBP4P2P0P1p,2DTp,3mtlP3p,3pdtp,2pbp,2AHp,3HDTp,3HDBp,3LOAp,3LOSp,3SPTf2P6P5MH:W1W0W2o"). Qed.

  (* [comment removed for export] *)
  Lemma w4_epi : forall mm (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    stk bsegs mm lo (SP + -104) -> rw_cells bsegs mm (SP + -104) FRS ->
    mem_inv bsegs mm -> munch DW m0 mm -> wmono bsegs m0 mm ->
    rng RNG lo (al_top L - lo) ->
    evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) FR (Z_to_bv 64 AW4_EPI) fc None mm (seg_rom bsegs)).
Proof using AH HDB HDT LOA LOS SPT.
  intros mm t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra ST FRC MI MU WM RS.
  pose proof w4_sp_bounds as SPB.
  unfold AW4_EPI.
  do 15 zstep.
  release_frame FRC ST (bv_unsigned sp).
  apply evtF_done. unfold huf_dec_postA.
  do 15 eexists. exists mm.
  split; [reflexivity|].
  exact (conj MI (conj ST (conj (w4_magree mm MU WM) (w4_aheap mm MU WM)))).
Qed.

  (* [comment removed for export] *)
  Lemma w4_err : forall mm (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    stk bsegs mm lo (SP + -104) -> rw_cells bsegs mm (SP + -104) FRS ->
    mem_inv bsegs mm -> munch DW m0 mm -> wmono bsegs m0 mm ->
    rng RNG lo (al_top L - lo) ->
    evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) FR (Z_to_bv 64 AW4_ERR) fc None mm (seg_rom bsegs)).
Proof using AH HDB HDT LOA LOS SPT.
  exact w4_epi.
Qed.

End W4.

Section W4FR.
  Variables (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -480).
  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition W4F (mm : amem) (fr mid l256 l296 l336 : list cell) : Prop :=
    (exists buf, u8arr bsegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at bsegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at bsegs mm (DT + 4) cbs
    /\ bytes_at bsegs mm DT [Z_to_bv 8 mtl; Z_to_bv 8 0; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ stk bsegs mm lo SPF
    /\ rw_cells bsegs mm SPF fr /\ cells_size fr = 104%nat
    /\ rw_cells bsegs mm (SPF + 104) mid /\ cells_size mid = 152%nat
    /\ rw_cells bsegs mm (SPF + 256) l256 /\ cells_size l256 = 40%nat
    /\ rw_cells bsegs mm (SPF + 296) l296 /\ cells_size l296 = 40%nat
    /\ rw_cells bsegs mm (SPF + 336) l336 /\ cells_size l336 = 40%nat
    /\ rw_cells bsegs mm (SP + -104) FRS
    /\ mem_inv bsegs mm /\ munch DW m0 mm /\ wmono bsegs m0 mm.
End W4FR.

Section W4X.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -480).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation W4FX := (W4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs).

  Definition w4fx_goal : Prop :=
    forall (i0 o0 e0 i1 o1 e1 i2 o2 e2 i3 o3 e3 : Z) (c0 c1 c2 c3 : word)
           (ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew po4 pi4 pb4 : word)
           (w0 w8 w16 w24 w32 w64 w96 : word) (mm : amem)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 : word),
    W4FX mm [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 n); C8 w64;
             C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap)); C8 w96]
         [C8 ipa0; C8 ipa1; C8 ipa2; C8 ipa3; C8 opa0; C8 opa1; C8 opa2; C8 opa3; C8 ba0; C8 ba1; C8 ba2; C8 ba3;
          C8 adt; C8 (Z_to_bv 64 SS); C8 oew; C8 (Z_to_bv 64 (SS + e0)); C8 (Z_to_bv 64 (SS + e1));
          C8 (Z_to_bv 64 (SS + e2)); C8 (Z_to_bv 64 (SS + e3))]
         [C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3)); C8 po4]
         [C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3)); C8 pi4]
         [C8 c0; C8 c1; C8 c2; C8 c3; C8 pb4] ->
    DST + 3 * seg < DST + dcap -> 9 <= n ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= o0 <= dcap -> 1 <= bv_unsigned c0 -> 6 <= e0 <= n ->
    0 <= i1 -> i1 + 8 <= n -> 0 <= o1 <= dcap -> 1 <= bv_unsigned c1 -> 6 <= e1 <= n ->
    0 <= i2 -> i2 + 8 <= n -> 0 <= o2 <= dcap -> 1 <= bv_unsigned c2 -> 6 <= e2 <= n ->
    0 <= i3 -> i3 + 8 <= n -> 0 <= o3 <= dcap -> 1 <= bv_unsigned c3 -> 6 <= e3 <= n ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
               (Z_to_bv 64 AW4_K21) x22 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB)
               x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 AW4_FX) fc None mm (seg_rom bsegs)).

  Definition w4fa_goal : Prop :=
    forall (w0 w8 w16 w24 w32 w64 w96 : word) (j256 j296 j336 : list byte) (b0 b1 b2 b3 : Z) (mm : amem)
           (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    W4FX mm [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 n); C8 w64;
             C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap)); C8 w96]
         (fast_args_cells DST dcap SS DT src b0 b1 b2 b3) [CB 40 j256] [CB 40 j296] [CB 40 j336] ->
    tl = 11 -> 10 <= n ->
    8 <= jt_len src 0 -> 8 <= jt_len src 2 -> 8 <= jt_len src 4 ->
    jt_len src 0 + jt_len src 2 + jt_len src 4 + 6 + 8 <= n ->
    0 < dcap -> 3 * seg < dcap ->
    0 <= b0 < 2^64 -> 0 <= b1 < 2^64 -> 0 <= b2 < 2^64 -> 0 <= b3 < 2^64 ->
    b0 mod 512 <> 0 -> b1 mod 512 <> 0 -> b2 mod 512 <> 0 -> b3 mod 512 <> 0 ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) (Z_to_bv 64 1)
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 DT) (Z_to_bv 64 SS) s4 s5 s6
               (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 AW4_FA) fc None mm (seg_rom bsegs)).
End W4X.
End CANSEC1.
