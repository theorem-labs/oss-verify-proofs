(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.

From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4m AF_huf_w4m AF_huf_w4body AF_huf_w4blk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s3b Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require I_asan_memcpy.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AFrameD.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_w4fast () := "C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_blockK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=ablock_shadowC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atI47Corelib4Init9Datatypes6option00I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC35stdpp4base6lookupK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>chunk_user_begI47Corelib4Init5Logic2ex00K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeI47Corelib4Init5Logic2or00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega6VarMap1t03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXI47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4m<w4_sp_boundsC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow@unpoisoned_munchK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_w4fast9w4_blocksI47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4m3W4MK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4m4W4F0C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKitAbytes_of_unsignedK47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib5FrameFstk_transport_disjointC47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Arr@u64arr_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u64arrC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses8or_morphI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_w4fast6w4_dtlC46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4m6AW4_M5C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4m6AW4_M7C5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u8arr_transportI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_w4fast6w4_unpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m<z4_stk_of_wrC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF7rng_subC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_w4fast>w4_apart_sub_rC46Stdlib6ZArith4ZdivAZ_div_mod_eq_fullC47Corelib4Init5Logic6eq_symI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z7add_0_rC35stdpp7tactics<f_equal_helpc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_w4fast8w4m_stepK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01C56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6ltb_geK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_w4body7w4_bodyC47Corelib4Init5Logic6eq_indC47Corelib4Init9Datatypes7nat_indC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I46Stdlib;setoid_ring<Ring_polynom3Mon00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05I4ELinuxProcessSemantics5Riscv5Instr5instr00C47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4blk5w4_q7C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4blk5w4_q5c5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_w4fast7w4m_updC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z8max_specC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4blk;w4_blk_foldc5ARocqVerifyHarness?AgentSubmission5BothW=AF_huf_w4fast8w4_innerC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4blk<w4_blk_setupC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4blk<w4_blk_st104C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divK4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4blk;w4_blk_headC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5aluop01".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Module W4FS.
Import KXS.

Lemma w4f_shd_ap : forall E X B O k w H,
  bv_unsigned (edenot E X) < H -> 0 <= O -> O + H / 8 + 1 <= 2^64 -> 0 < w < 2^64 ->
  0 <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + w <= 2^64 ->
  bv_unsigned (edenot E B) + k + w <= O \/ O + H / 8 + 1 <= bv_unsigned (edenot E B) + k ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit w)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit w) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) O)).
Proof.
  intros E X B O k w H HX HO1 HO2 HW HB1 HB2 HAP.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite u_srl64.
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  change (2 ^ (3 mod 64)) with 8.
  rewrite (Z_to_bv_unsigned 64 w). unfold bv_wrap, bv_modulus. rewrite (Z.mod_small w) by lia.
  assert (HD : bv_unsigned (edenot E X) / 8 <= H / 8) by (apply Z.div_le_mono; lia).
  assert (HD0 : 0 <= bv_unsigned (edenot E X) / 8) by (apply Z.div_pos; lia).
  repeat split; lia.
Qed.

Ltac w4f_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Ltac w4fxb :=
  lazymatch goal with
  | |- bv_unsigned (edenot ?E ?X) < _ =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite (ez_ok zv E (kE_atoms zv xs) X);
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        repeat match goal with
        | |- context [?c mod 64] => w4f_zlit c; let v := eval vm_compute in (c mod 64) in change (c mod 64) with v
        end;
        rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64;
        first [lia | Z.div_mod_to_equations; lia]
      end
  end.

Lemma w4f_shd_ap2 : forall E X B O k w H,
  bv_unsigned (edenot E X) < H ->
  0 <= O /\ O + H / 8 + 1 <= 2^64 /\ 0 < w < 2^64 ->
  0 <= bv_unsigned (edenot E B) + k /\ bv_unsigned (edenot E B) + k + w <= 2^64 /\
  (bv_unsigned (edenot E B) + k + w <= O \/ O + H / 8 + 1 <= bv_unsigned (edenot E B) + k) ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit w)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit w) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) O)).
Proof.
  intros E X B O k w H HX (HO1 & HO2 & HW) (HB1 & HB2 & HAP).
  apply (w4f_shd_ap E X B O k w H); assumption.
Qed.

Ltac w4f_aplia :=
  first [ match goal with H : KXGoM.apart ?a _ _ _ |- context [?a] =>
            let H' := fresh "AP" in pose proof H as H'; unfold KXGoM.apart in H'; lia end
        | match goal with H : KXGoM.apart _ _ _ _ |- _ =>
            let H' := fresh "AP" in pose proof H as H'; unfold KXGoM.apart in H'; lia end ].

Ltac w4fshd H :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ ?E (ELit ?w)) /\ _ =>
      apply (w4f_shd_ap2 E X B O k w H);
      [ w4fxb
      | lia
      | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
        split; [lia | split; [lia | w4f_aplia]] ]
  end.
Lemma w4f_rd_nb : forall m A z,
  ztab_fact bsegs m A 4096 2 [(0, 0, 11)] -> A <= z < A + 4096 -> (z - A) mod 2 = 0 ->
  bv_unsigned (rdval bsegs m (Z_to_bv 64 z) 2 false) mod 64 <= 11.
Proof.
  intros m A z ZT HZ HM.
  assert (FF : find_field ((z - A) mod 2) [(0, 0, 11)] = Some (0, 11)) by (rewrite HM; reflexivity).
  destruct (ZT z HZ 0 11 FF) as (b & RB & HB).
  unfold rdval. cbn [rdn] in RB |- *.
  revert RB.
  lazymatch goal with |- (match ?x with Some _ => _ | None => _ end) = _ -> _ => destruct x as [b0|] eqn:L0 end;
    [| discriminate].
  intros RB. injection RB as Eb. subst b0.
  cbn beta iota.
  match goal with |- context [m ?X] =>
    destruct (m X) as [b1|] eqn:L1; [| destruct (seg_rom bsegs X) as [b1|] eqn:L2] end;
  cbn beta iota; unfold extz;
  rewrite ?bytes_le_to_Z_le_val; cbn [map le_val];
  rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64;
  try (pose proof (bv_unsigned_in_range _ b1) as R1; unfold bv_modulus in R1; change (Z.of_N 8) with 8 in R1);
  Z.div_mod_to_equations; lia.
Qed.

Lemma w4f_mod_div : forall a n m, 0 < n -> (n | m) -> 0 < m -> (a mod m) mod n = a mod n.
Proof.
  intros a n m Hn [c Hc] Hm. subst m.
  rewrite (Z.div_mod a (c * n)) at 2 by lia.
  rewrite Z.add_comm. replace (c * n * (a / (c * n))) with ((c * (a / (c * n))) * n) by ring.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma w4f_lb_shift : forall p s k x, 0 <= p -> 0 <= k <= s -> p + s <= 63 ->
  x mod 2^(p+1) <> 0 -> ((x * 2^k) mod 2^64) mod 2^(p + s + 1) <> 0.
Proof.
  intros p s k x Hp Hk Hps Hl.
  assert (P1 : 0 < 2^(p+s+1)) by (apply Z.pow_pos_nonneg; lia).
  assert (P2 : 0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  assert (P3 : 0 < 2^(p+s+1-k)) by (apply Z.pow_pos_nonneg; lia).
  assert (P4 : 0 < 2^(p+1)) by (apply Z.pow_pos_nonneg; lia).
  assert (D1 : (2^(p+s+1) | 2^64)).
  { exists (2^(63 - p - s)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (D2 : (2^(p+1) | 2^(p+s+1-k))).
  { exists (2^(s - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite (w4f_mod_div (x * 2^k) (2^(p+s+1)) (2^64) P1 D1 ltac:(lia)).
  replace (2^(p+s+1)) with (2^(p+s+1-k) * 2^k) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_mod_distr_r by lia.
  intro HZ. apply Z.mul_eq_0 in HZ. destruct HZ as [HZ|HZ]; [|lia].
  apply Hl. rewrite <- (w4f_mod_div x (2^(p+1)) (2^(p+s+1-k)) P4 D2 P3), HZ. reflexivity.
Qed.

Lemma w4f_sll_lb : forall (B : Z) (e : word) p, 0 <= p -> p + 11 <= 63 -> 0 <= B < 2^64 ->
  B mod 2^(p+1) <> 0 -> bv_unsigned e mod 64 <= 11 ->
  0 <= bv_unsigned (alu64 ALU_SLL (Z_to_bv 64 B) e) < 2^64 /\
  bv_unsigned (alu64 ALU_SLL (Z_to_bv 64 B) e) mod 2^(p + 11 + 1) <> 0.
Proof.
  intros B e p Hp Hp2 HB HL HE.
  rewrite u_sll64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite (Z.mod_small B) by lia.
  pose proof (Z.mod_pos_bound (bv_unsigned e) 64 ltac:(lia)) as HK.
  split; [apply Z.mod_pos_bound; lia |].
  apply (w4f_lb_shift p 11 (bv_unsigned e mod 64) B); [lia | lia | lia | exact HL].
Qed.

Lemma w4f_rd_nb2 : forall m A (x : word) k,
  ztab_fact bsegs m A 4096 2 [(0, 0, 11)] -> A <= bv_unsigned x + k < A + 4096 -> (bv_unsigned x + k - A) mod 2 = 0 ->
  bv_unsigned (rdval bsegs m (v_addi x k) 2 false) mod 64 <= 11.
Proof.
  intros m A x k ZT H1 H2. unfold v_addi. exact (w4f_rd_nb m A (bv_unsigned x + k) ZT H1 H2).
Qed.

Ltac w4f_nb_read ZT TA :=
  lazymatch goal with
  | |- bv_unsigned (rdval _ ?m (adenot ?E ?a) 2 false) mod 64 <= 11 =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        cbv [adenot a_base a_off];
        apply (w4f_rd_nb2 m TA); [exact ZT | |];
        rewrite (ez_ok zv E (kE_atoms zv xs)); rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        change (Z.of_N 64) with 64;
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        repeat match goal with
        | |- context [?c mod 64] => w4f_zlit c; let v := eval vm_compute in (c mod 64) in change (c mod 64) with v
        end;
        Z.div_mod_to_equations; lia
      end
  end.

Ltac w4f_bits A p ZT TA HB LBb e :=
  lazymatch goal with
  | H : rw_cells _ _ A [C8 (edenot ?E (EAlu ALU_SLL (EVar ?j) (EVar ?r)))] |- _ =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let HR := fresh "HR" in kx_read_eq r HR;
        let NB := fresh "NB" in
        assert (NB : bv_unsigned (ev E r) mod 64 <= 11) by (rewrite HR; w4f_nb_read ZT TA);
        clear HR;
        cbn [edenot] in H;
        set (e := ev E r) in *;
        change E with (kE zv xs) in H;
        rewrite (kE_atoms zv xs j ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)) in H;
        cbn [nth] in H;
        lazymatch type of H with
        | rw_cells _ _ _ [C8 (alu64 ALU_SLL (Z_to_bv 64 ?B) e)] =>
            let BR := fresh "BR" in let BL := fresh "BL" in
            pose proof (w4f_sll_lb B e p ltac:(lia) ltac:(lia) HB LBb NB) as [BR BL]
        end
      end
  end.

Lemma w4f_srl58 : forall E X, 0 <= bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58))) < 64.
Proof.
  intros E X. pose proof (bv_unsigned_in_range _ (edenot E X)) as [R0 R1]. unfold bv_modulus in R1.
  change (Z.of_N 64) with 64 in R1.
  cbn [edenot]. rewrite u_srl64. change (bv_unsigned (Z_to_bv 64 58) mod 64) with 58.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | change (2^58 * 64) with (2^64); lia]].
Qed.

Lemma w4f_ctz_rd : forall m E X off,
  ztab_fact bsegs m off 64 1 [(0, 0, 63)] -> 0 <= off -> off + 64 <= 2^64 ->
  exists bs, rdn bsegs m (adenot E (SA (EAlu ALU_SRL X (ELit 58)) off)) 1 = Some bs.
Proof.
  intros m E X off ZT H0 H1. pose proof (w4f_srl58 E X) as HV.
  cbv [adenot a_base a_off]. unfold v_addi.
  set (u := bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58)))) in *.
  assert (FF : find_field ((u + off - off) mod 1) [(0, 0, 63)] = Some (0, 63)) by (rewrite Z.mod_1_r; reflexivity).
  destruct (ZT (u + off) ltac:(lia) 0 63 FF) as (b & RB & _). exists [b]. exact RB.
Qed.

Lemma w4f_ctz_acc : forall RNG E X off, rng RNG off 64 -> accP RNG E (SA (EAlu ALU_SRL X (ELit 58)) off, 1%nat).
Proof.
  intros RNG E X off (R0 & R1 & R2). pose proof (w4f_srl58 E X) as HV.
  unfold accP. cbn [fst snd].
  set (u := bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58)))) in *.
  change (RNG (bv_unsigned (Z_to_bv 64 (u + off))) 1%nat).
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite Z.mod_small by lia. apply R2; cbn; lia.
Qed.

Lemma w4f_ctz_ap : forall E X B O k w,
  0 <= O -> O + 64 <= 2^64 -> 0 < w < 2^64 ->
  0 <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + w <= 2^64 ->
  bv_unsigned (edenot E B) + k + w <= O \/ O + 64 <= bv_unsigned (edenot E B) + k ->
  (flat E (SA (EAlu ALU_SRL X (ELit 58)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit w)) /\
   (estart E (SA (EAlu ALU_SRL X (ELit 58)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
    estart E (SA B k) + elenZ E (ELit w) <= estart E (SA (EAlu ALU_SRL X (ELit 58)) O))) /\
  (flat E (SA B k) (elenZ E (ELit w)) /\ flat E (SA (EAlu ALU_SRL X (ELit 58)) O) (elenZ E (ELit 1)) /\
   (estart E (SA B k) + elenZ E (ELit w) <= estart E (SA (EAlu ALU_SRL X (ELit 58)) O) \/
    estart E (SA (EAlu ALU_SRL X (ELit 58)) O) + elenZ E (ELit 1) <= estart E (SA B k))).
Proof.
  intros E X B O k w HO1 HO2 HW HB1 HB2 HAP. pose proof (w4f_srl58 E X) as HV.
  unfold flat, estart, elenZ. cbn [a_base a_off].
  set (u := bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58)))) in *.
  change (edenot E (ELit 1)) with (Z_to_bv 64 1). change (edenot E (ELit w)) with (Z_to_bv 64 w).
  change (bv_unsigned (Z_to_bv 64 1)) with 1.
  rewrite (Z_to_bv_unsigned 64 w). unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64. rewrite (Z.mod_small w) by lia.
  repeat split; lia.
Qed.

Ltac w4f_rngs :=
  repeat match goal with
  | |- context [EVar ?j] =>
      lazymatch goal with
      | _ : _ <= bv_unsigned (ev _ j) <= _ |- _ => fail
      | _ => let H := fresh "HR" in kx_range (EVar j) H
      end
  end.

Ltac w4fctz :=
  lazymatch goal with
  | |- exists bs, rdn _ ?m (adenot ?E (SA (EAlu ALU_SRL ?X (ELit 58)) ?O)) 1 = Some bs =>
      eapply (w4f_ctz_rd m E X O); [eassumption | lia | lia]
  | |- accP ?R ?E (SA (EAlu ALU_SRL ?X (ELit 58)) ?O, 1%nat) => apply (w4f_ctz_acc R E X O); assumption
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 58)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ ?E (ELit ?w)) /\ _ =>
      apply (proj1 (w4f_ctz_ap E X B O k w ltac:(lia) ltac:(lia) ltac:(lia) ltac:(w4uz) ltac:(w4uz) ltac:(w4uz)))
  | |- flat ?E (SA ?B ?k) (elenZ ?E (ELit ?w)) /\ flat ?E (SA (EAlu ALU_SRL ?X (ELit 58)) ?O) _ /\ _ =>
      apply (proj2 (w4f_ctz_ap E X B O k w ltac:(lia) ltac:(lia) ltac:(lia) ltac:(w4uz) ltac:(w4uz) ltac:(w4uz)))
  end.

Lemma w4f_br_nz : forall E P B,
  bv_unsigned (edenot E B) <= 64 -> 64 < bv_unsigned (edenot E P) ->
  branch_taken BC_NE
    (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR P (EAlu ALU_SRL B (ELit 3))) (ELit 1))))
    (edenot E (ELit 0)) = true.
Proof.
  intros E P B HB HP.
  pose proof (bv_unsigned_in_range _ (edenot E B)) as [RB _].
  cbn [edenot branch_taken].
  rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64, u_srl64.
  change (bv_unsigned (Z_to_bv 64 3) mod 64) with 3. change (2 ^ 3) with 8.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  assert (HL : 0 < Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
  { assert (0 <= Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
    { apply Z.lxor_nonneg; split; intros; Z.div_mod_to_equations; lia. }
    assert (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8) <> 0).
    { assert (HB8 : bv_unsigned (edenot E B) / 8 <= 8) by (apply Z.div_le_upper_bound; lia).
      intros H0. pose proof (Z.lxor_eq _ _ H0). lia. }
    lia. }
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)) 1); [lia|].
  reflexivity.
Qed.

Lemma w4f_lit_acc : forall RNG E off (n : nat) lo len, (1 <= n)%nat -> rng RNG lo len -> lo <= off -> off + Z.of_nat n <= lo + len ->
  accP RNG E (SA (ELit 0) off, n).
Proof.
  intros RNG E off n lo len HN (R0 & R1 & R2) H1 H2.
  unfold accP. cbn [fst snd].
  change (RNG (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + off))) n).
  change (bv_unsigned (Z_to_bv 64 0)) with 0.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite Z.mod_small by lia. apply R2; lia.
Qed.

Ltac w4fbr :=
  lazymatch goal with
  | |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR ?P (EAlu ALU_SRL ?B (ELit 3))) (ELit 1))))
         (edenot ?E (ELit 0)) = true => w4f_rngs; apply (w4f_br_nz E P B); w4uz
  end.

Ltac w4facc WIM :=
  lazymatch goal with
  | |- accP ?R ?E (SA (ELit 0) ?O, ?n) => eapply (w4f_lit_acc R E O n); [lia | exact WIM | lia | cbn; lia]
  end.

Lemma w4f_mod2_64 : forall x, (x mod 2^64) mod 2 = x mod 2.
Proof. intros x. apply (w4f_mod_div x 2 (2^64)); [lia | exists (2^63); reflexivity | lia]. Qed.

Lemma w4f_ev_add : forall E a b, bv_unsigned (edenot E a) mod 2 = 0 -> bv_unsigned (edenot E b) mod 2 = 0 ->
  bv_unsigned (edenot E (EAlu ALU_ADD a b)) mod 2 = 0.
Proof. intros E a b Ha Hb. cbn [edenot]. rewrite u_add64, w4f_mod2_64, Z.add_mod by lia. rewrite Ha, Hb. reflexivity. Qed.

Lemma w4f_ev_mul : forall E c b, c mod 2 = 0 -> bv_unsigned (edenot E (EMd M_MUL (ELit c) b)) mod 2 = 0.
Proof.
  intros E c b Hc. cbn [edenot]. rewrite u_mul64, w4f_mod2_64, Z.mul_mod by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64. rewrite w4f_mod2_64, Hc. reflexivity.
Qed.

Lemma w4f_ev_and : forall E b m, m mod 2 = 0 -> bv_unsigned (edenot E (EAlu ALU_AND b (ELit m))) mod 2 = 0.
Proof.
  intros E b m Hm. cbn [edenot]. rewrite u_and64, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  set (x := bv_unsigned (edenot E b)). set (y := m mod 2^64).
  assert (Hy : Z.land y (Z.ones 1) = 0) by (rewrite Z.land_ones by lia; change (2^1) with 2; unfold y; rewrite w4f_mod2_64; exact Hm).
  assert (H : Z.land x y mod 2 = Z.land (Z.land x y) (Z.ones 1)) by (rewrite Z.land_ones by lia; reflexivity).
  rewrite H, <- Z.land_assoc, Hy. apply Z.land_0_r.
Qed.

Ltac w4f_ev :=
  lazymatch goal with
  | |- bv_unsigned (edenot ?E (EAlu ALU_ADD ?a ?b)) mod 2 = 0 => apply (w4f_ev_add E a b); w4f_ev
  | |- bv_unsigned (edenot ?E (EMd M_MUL (ELit ?c) ?b)) mod 2 = 0 => apply (w4f_ev_mul E c b); reflexivity
  | |- bv_unsigned (edenot ?E (EAlu ALU_AND ?b (ELit ?m))) mod 2 = 0 => apply (w4f_ev_and E b m); reflexivity
  end.

Lemma w4f_rl_bits : forall E Y V, bv_unsigned (edenot E Y) mod 2 = 0 ->
  0 <= bv_unsigned (edenot E (EAlu ALU_SLL (EAlu ALU_ADD Y (ELit 1)) (EAlu ALU_AND V (ELit 7)))) < 2^64 /\
  bv_unsigned (edenot E (EAlu ALU_SLL (EAlu ALU_ADD Y (ELit 1)) (EAlu ALU_AND V (ELit 7)))) mod 2^8 <> 0.
Proof.
  intros E Y V HY.
  pose proof (bv_unsigned_in_range _ (edenot E Y)) as [Y0 Y1]. unfold bv_modulus in Y1. change (Z.of_N 64) with 64 in Y1.
  pose proof (bv_unsigned_in_range _ (edenot E V)) as [V0 _].
  cbn [edenot]. rewrite u_sll64, u_add64, u_and64.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 7)) with 7.
  set (y := bv_unsigned (edenot E Y)) in *. set (v := bv_unsigned (edenot E V)) in *.
  assert (HY2 : y + 1 < 2^64) by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (y + 1)) by lia.
  assert (HO : (y + 1) mod 2^(0+1) <> 0) by (change (2^(0+1)) with 2; Z.div_mod_to_equations; lia).
  assert (HL : 0 <= Z.land v 7 <= 7).
  { assert (E7 : Z.land v 7 = v mod 2^3) by (rewrite <- Z.land_ones by lia; reflexivity). rewrite E7.
    pose proof (Z.mod_pos_bound v (2^3) ltac:(lia)). change (2^3) with 8 in *. lia. }
  rewrite (Z.mod_small (Z.land v 7) 64) by lia.
  split; [apply Z.mod_pos_bound; lia |].
  change (2^8) with (2^(0+7+1)).
  apply (w4f_lb_shift 0 7 (Z.land v 7) (y + 1)); [lia | lia | lia | exact HO].
Qed.

Ltac w4f_rlb A c :=
  lazymatch goal with
  | H : rw_cells _ _ A [C8 (edenot ?E (EAlu ALU_SLL (EAlu ALU_ADD ?Y (ELit 1)) (EAlu ALU_AND ?V (ELit 7))))] |- _ =>
      let BR := fresh "BR" in let BL := fresh "BL" in
      pose proof (w4f_rl_bits E Y V ltac:(w4f_ev)) as [BR BL];
      set (c := edenot E (EAlu ALU_SLL (EAlu ALU_ADD Y (ELit 1)) (EAlu ALU_AND V (ELit 7)))) in *; clearbody c
  end.

Lemma w4f_ctz_val : forall m E X off, ztab_fact bsegs m off 64 1 [(0, 0, 63)] -> 0 <= off -> off + 64 <= 2^64 ->
  bv_unsigned (rdval bsegs m (adenot E (SA (EAlu ALU_SRL X (ELit 58)) off)) 1 false) <= 63.
Proof.
  intros m E X off ZT H0 H1. pose proof (w4f_srl58 E X) as HV.
  set (u := bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58)))) in *.
  change (bv_unsigned (rdval bsegs m (Z_to_bv 64 (u + off)) 1 false) <= 63).
  assert (FF : find_field ((u + off - off) mod 1) [(0, 0, 63)] = Some (0, 63)) by (rewrite Z.mod_1_r; reflexivity).
  destruct (ZT (u + off) ltac:(lia) 0 63 FF) as (b & RB & HB).
  unfold rdval. rewrite RB. unfold extz. cbn beta iota.
  rewrite bytes_le_to_Z_le_val. cbn [map le_val].
  pose proof (bv_unsigned_in_range _ b) as [B0 B1]. unfold bv_modulus in B1. change (Z.of_N 8) with 8 in B1.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite Z.mod_small by lia. lia.
Qed.

Ltac w4f_rlnb A nb :=
  lazymatch goal with
  | H : rw_cells _ _ A [C8 (Z_to_bv 64 (?S + (?i + -1 * (bv_unsigned ?Z mod ?M / ?D))))] |- _ =>
      lazymatch Z with
      | ?f ?j =>
          let HR := fresh "HR" in kx_read_eq j HR;
          let HV := fresh "HV" in
          lazymatch type of HR with
          | ?L = ?R =>
              assert (HV : 0 <= bv_unsigned L <= 63)
                by (rewrite HR; pose proof (bv_unsigned_in_range _ R) as [? _];
                    split; [lia | eapply w4f_ctz_val; [eassumption | lia | lia]]);
              change (0 <= bv_unsigned Z <= 63) in HV
          end;
          clear HR;
          let NB := fresh "NB" in
          assert (NB : 0 <= bv_unsigned Z mod M / D <= 7)
            by (change D with 8; change M with (2^64); rewrite Z.mod_small by lia;
                assert (bv_unsigned Z / 8 < 8) by (apply Z.div_lt_upper_bound; lia);
                assert (0 <= bv_unsigned Z / 8) by (apply Z.div_pos; lia); lia);
          set (nb := bv_unsigned Z mod M / D) in *; clearbody nb
      end
  end.

Ltac w4f_cell_gen H W off :=
  lazymatch goal with
  | HLF : log_flat ?E ?log |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      lazymatch type of H with
      | rw_cells ?segs m ?A [?c0] =>
          let rec go pre l :=
            lazymatch l with
            | SE ?a W ?v :: ?rest =>
                tryif (lazymatch a with {| a_base := _; a_off := off |} => idtac end) then
                  first [ let Hn := fresh "HC" in
                          assert (Hn : rw_cells segs (mem_denot E m (pre ++ SE a W v :: rest)) A
                                         [ltac:(lazymatch W with 8%nat => exact (C8 (edenot E v)) | _ => exact (C4 (edenot E v)) end)])
                            by (first [ eapply (kx_cell_store8 segs E m pre a v rest A)
                                      | eapply (kx_cell_store4 segs E m pre a v rest A) ];
                                [ change (pre ++ SE a W v :: rest) with log; exact HLF
                                | exact H
                                | change E with (kE zv xs); kx_estart_z zv
                                | change E with (kE zv xs); apply log_apart_ez_ok; kx_log_z zv ]);
                          change (pre ++ SE a W v :: rest) with log in Hn;
                          rewrite (ez_ok zv E (kE_atoms zv xs) v) in Hn;
                          let EQ := fresh "HCe" in let pf := w4_ez_pf zv E v in pose proof pf as EQ; rewrite EQ in Hn; clear EQ;
                          rewrite ?Z_to_bv_bv_unsigned in Hn;
                          clear H; rename Hn into H
                        | let pre' := eval cbn [app] in (pre ++ [SE a W v]) in go pre' rest ]
                else (let pre' := eval cbn [app] in (pre ++ [SE a W v]) in go pre' rest)
            | ?e :: ?rest => let pre' := eval cbn [app] in (pre ++ [e]) in go pre' rest
            | [] => fail "w4f_cell: no store found for" A
            end in
          let l := eval hnf in log in
          go constr:(@nil sentry) l
      end
    end
  end.

Ltac w4f_cells_post :=
  repeat match goal with
  | HLF : log_flat ?E ?log, H : rw_cells ?segs ?m ?A [?c] |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
      let l := eval hnf in log in
      lazymatch A with
      | _ + ?off => tryif kx_log_has_off l off
                    then first [ w4f_cell_gen H 8%nat off | w4f_cell_gen H 4%nat off | w4_cell H | w4_cell4 H | kx_frame H ]
                    else kx_frame H
      | _ => first [ w4_cell H | w4_cell4 H | kx_frame H ]
      end
  end.

Ltac w4f_frame3 MU :=
  repeat match goal with
  | H : rw_cells ?segs ?m (?P + ?off) [?c] |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
      lazymatch type of MU with munch ?W m ?m' =>
        first [ constr_eq off 288 | constr_eq off 328 | constr_eq off 368 ];
        let H' := fresh "HF" in
        pose proof (AFrameD.cells_frameD W m m' (P + off) [c] H MU ltac:(cbn [disjoint_from cells_size csize]; lia)) as H';
        clear H; rename H' into H
      end
  end.

End W4FS.
Import W4FS.

Section CANSEC1. Context {rc : runConstT}.
Section W4F.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (pdt pb : aptr) (SBL SBH : Z) (rstk : region).
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
  
  Hypothesis LCB : zlen cbs = 4096.
  Hypothesis MTL : 10 <= mtl <= 12.
  Variable cells : list deltX1.
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells).
  
  Hypothesis DC : 0 < dcap < 2^32.
  Hypothesis NSM : 10 <= n < 2^26.
  Hypothesis SBB : SBL <= SS /\ SS + n <= SBH.
  Hypothesis SBA : ablk SBL SBH /\ SBL mod 8 = 0.
  
  Hypothesis DJ1 : KXGoM.apart DST dcap DT DTL.
  Hypothesis DJ2 : KXGoM.apart DST dcap SS n.
  
  Hypothesis UDT : unpoisoned m0 DT (DT + DTL).
  Hypothesis UDB : unpoisoned m0 DST (DST + dcap).
  Hypothesis USB : unpoisoned m0 SBL SBH.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WDT : rng RNG DT DTL.
  Hypothesis WDB : rng RNG DST dcap.
  Hypothesis WSB : rng RNG SBL (SBH - SBL).
  Hypothesis WDTS : rng RNG (shad DT) (shlen (DTL + 7)).
  Hypothesis WDBS : rng RNG (shad DST) (shlen (dcap + 7)).
  Hypothesis WSBS : rng RNG (shad SBL) (shlen (SBH - SBL + 7)).
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : SP <= r_hi rstk.
  Hypothesis RRL : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).

  

  Lemma w4_blocks : AIMG_HI <= DT /\ DT + DTL <= ATOP /\ DT mod 16 = 0 /\ AIMG_HI <= DST /\ DST + dcap <= ATOP /\ DST mod 16 = 0
                    /\ ablk DST (DST + dcap) /\ AIMG_HI <= SBL /\ SBH <= ATOP.
Proof using All.
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH HDT) as (_ & BT & _). unfold ablock_range in BT.
  destruct BT as (BT1 & _ & BT3 & BT4).
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH HDB) as (_ & BB & _). unfold ablock_range in BB.
  destruct BB as (BB1 & _ & BB3 & BB4).
  destruct SBA as [SB1 _].
  pose proof (ablk_img _ _ BT1). pose proof (ablk_img _ _ BB1). pose proof (ablk_img _ _ SB1). pose proof (ablk_top _ _ SB1).
  repeat split; first [assumption | lia].
Qed.

  
  Lemma w4_unp : forall mm, munch DW m0 mm ->
    unpoisoned mm DT (DT + DTL) /\ unpoisoned mm DST (DST + dcap) /\ unpoisoned mm SBL SBH.
Proof using All.
  intros mm MU.
  pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
  pose proof (@ATOP_lo rc) as HA. pose proof (@ATOP_hi rc) as HA2.
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH HDT) as (_ & (K1 & _) & _).
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH HDB) as (_ & (K2 & _) & _).
  pose proof SBA as (K3 & _).
  unfold ablk, AIMG_HI, KLS in K1, K2, K3.
  split; [|split].
  - eapply unpoisoned_munch; [exact UDT | exact MU |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. lia.
  - eapply unpoisoned_munch; [exact UDB | exact MU |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. lia.
  - eapply unpoisoned_munch; [exact USB | exact MU |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. lia.
Qed.

  Lemma w4_dtl : 4100 <= DTL.
Proof using All.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4fast ()) ["CANSEC1"; "W4F"] "h02Hah17__sat19h27__sat21h34__p1h44__x1h51Hh67__arithh74__ffh87__sat17h97__sat18h:7__sat20h;7__sat22h<8__varmaph=5__with>4cstrh?5cstr0h@7__sat23hA4__x2hB2H0hC7__sat24p;1p;2p;3p;4p;5p;7p;6p;8g00BGj10Tg004Mj12Tg007oj13Tg01B:j1WTg00DDj1]Tg004kj24Tg00Cij2BTg00GEj2CTg00Gej1MTg00HJj1QTg00Hjj1LTg00IHj1mTg00Ikj2gTg00JUj2ITg00Blj2JTg00KFj2>Tg00Knj28Tg00LJj2;Tg00Lgj3=Tg00RUj2^Tg00S6j2HTg00SPj1\Tg00T0j1[Tg00_Fj1ZTg00Tnj1YTg00ULj1XTg00V7j2ETg00_dj4DTg00W_j2VTg00XAj2UTg00>Xj3RTg00Xmj3STg00YLj4TTg00TPj2PTg00VZj2OTg00W=j1oTg01C8j5nTg00\?j2GTg00[`j1ATg00]Qj3lTg00^:j2kTg019Ej2fTg00^fj3eTg00c^j4?Tg00Z>j3bTg018bj3cTg008Tj2dTg00Nbj2aTg002Hj1`Tg00`jj7hTg00aNj6_Tg00b2j7iTg00c:j8jTf0R0#3#3#3#3p=5%00#0p=9%00#0#0#0p=K%00#0#0#0#0#0#0#0p=:g00dZR1/40p=1g00d<R2/E0p=6f1R3g00e8R4g00eWR5P5g00f7R6P0g00g>Fhp=7P2P3g00fWP0CDp=<P3P4P5P5P6P0E_p=Nf2R7P4P5P5P6P3P0Fip=Ff3R8P4P5P5P6P7P3P0Gjp=@g00g^R4#0R9#2R:%39#0#2R;p,3mtlR<p,2rcR=#WR>%34R?#3#5#5#5R@#0#5#5#0#9#K#:#:#2%]=R='4%3@#5#5#0#9#K#:#:#2,4='BR=p,3src,C2R@#MRA%Q@#1R@%09R9#0RB#L#mp,3cbs'CRC#MRD%QC#1RC%0BRE#0RF#0RG#Lp,2sp'gRH%2ERE'IRI%1H%1E1JHE#1[[RE%2FRF,>:RH181:RJ%1F1;:FRK,81[RL[RM%1:RNg00olROA=:F3UW0RF%1K\O^0NRK%0?R?#3#0#2RP,>:RQ%1P1;:PRR,81[RS\JRTA=:P3VOX0NRP%1R\O^0NRRp,3SBLRU%2BRB'IRV%1U%1B1JUB#1[[RBP7g010d1^1:'HPJeRUO1RWPSf5PUO1RXPLg011JRY#\RZ%[YR[%Z2R\%Y2R]%X2R^P21E21g01AS%6:CD'71V^6R6P0P7g00l@R_g0126R`'H1U07=R_`dAS213CTR`b7b<b=PJP0b6b2b1b8b9b1b:b2b;b?b>b5P>P=PAP@PDPCPIPEPHPMPFPKPQPTPPPRPVPBPWPSPXPLp-0R_PZP[1P23P]P^%6;Ra1O24Rb'<,7^Rc1N^85F^%o5R5PcC@P6P`b7b<b=X42W314;0/B314;3[^42^3_P0%0?#2,4<R?P<p,3MTLRcO3b6b2b1b8b9b1b:b2b;b?b>b5Dn1;:;1;:<Rd'4P>P=PAP@PDPCPIPEPHPMPFPK1>:<%1<181d[R1\JA=:<3VOX0N%1d\O^0NPQPTPPPRPVPBPWPSPXP1f8PUO1PLg012VRL,G2RU%AL#A#A,G29l2Ug0135'k'f=eYZP[P2P\P3P2P21P27P7P\C?P7P\C?C?P]P^%0G#9RG#0#2R]#6/<b,7^P5P^%39,O2,<a,7^f4,N^5F^P5%3G#9#2RG#6%29R9#6%24R4#6=b2b5c2'<,7^C@C@P6P`b7b<b=X42XA2X3_14]014;7/B81d47,a9,4G[[^42^A2^3_P0P?P<Pdf?PcO5b6b@b2b1b8b9b1b:b2b;b@bCb?b>bBb5%`<,4Geo"). Qed.

  Lemma w4_apart_sub_r : forall A N B M B' M', KXGoM.apart A N B M -> B <= B' -> B' + M' <= B + M -> KXGoM.apart A N B' M'.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4fast ()) ["CANSEC1"; "W4F"] "h02Hah11ah21Ah31Bh42B'h53H10h62H4h71Mh82M'h91Nh:7__sat18h;7__sat19h<7__sat20h=7__sat21h>4__x1h?4__x2h@4__x3hA4__x4hB4__x5hC4__x6hD2zhhE3H11hF3H12hG3H13hH3H14hI2H2hJ2H3hK2H5hL2H6hM2H7hN2H8hO2H9hP7__arithhQ4__ffhR7__sat17hS7__sat22hT8__varmaphU5__withV4cstrhW5cstr0p;2p;1p;3p;4p;7p;8g008Tj24Tg004kj21Tg00Fkj2BTg01B:j1bTg007oj15Tg00BGj10Tg004Mj18Tg00DDj1aTg00Cij2=Tg00GEj2`Tg00Gej1^Tg00HJj1\Tg00Hjj1ZTg00IHj1lTg00Ikj2hTg00JUj2VTg00Blj2YTg00KFj2UTg00Knj23Tg00LJj2TTg00Lgj3RTg00MKj2QTg00Mlj1NTg00NEj2MTg00Nbj2LTg00>Xj39Tg00O?j2KTg00Ofj2JTg00PMj2ITg00Q3j2OTg00QYj2PTg00RUj2ETg00S6j2ATg00[`j1CTg00\?j2>Tg00]Qj3DTg00^:j2_Tg00SPj1tTg00^fj3]Tg00T0j1sTg00_Fj1rTg00TPj2[Tg00Tnj1qTg00ULj1pTg00VZj2:Tg00Z>j3FTg00W=j1kTg00W_j2gTg00XAj2iTg00Xmj3fTg00YLj4jTg01C_j4XTg00c^j4eTg00_dj4mTg00`jj7nTg00bVj7dTg00c:j8cTf0R0#5#5#5#5p=6%00#0p=H%00#0#0#0p=S%00#0#0#0#0#0#0#0p=?g00dZR1/10p=2g00d<R2?901p=@P2f2R3f1R4P0Cep=7%50#5p=oP2P4g00fWP0Cmp=<P4g00e8R5g00eWR6P6g00f7R7P0g00g>Fnp=;P3P5P6P6P7P4P0Fdp=Wf3R8P5P6P6P7P3P4P0Gcp=Gf5R5f4R9'4R:/181483R;/15'B1193R<11;:R;p,2rcR:#bg00g^R=#5R>#5#6#6#6R?#0#6#6#0#H#S#?#?#8%a:R:'1%5?#6#6#0#H#S#?#?#8,1:'=p,3src,`2R:#^%\:#2%0=R:#0R?#0R@#Z#lp,3cbs'`RA#^%\A#2%0@RA#0RB#0#Zp,2sp'hRC%8ARA'V%2C%2A1YCARD#2RE[[%8:RF%8BRB'U131FRG%2B1TFBRH,31[RI[%2FRJg00olRKARFB4UW0%2HRH\K^0J%0>#5#0#8RB,UF%2B1TFBRL,31[RM\GARFB4VKX0J%2LRL\K^0Jp,3SBLRB%8@R@'V%2B%2@1YB@RN#2RO[[1QB@%@@RP#N1MB@RQ,L@/4N992B[1KB@131@RR13N@,=ORO[1JB@13@113@N11N1'=[1IB@%@Q\P1OB@A92NB\Pg010HRP1PB@RBePB1QCA%@ARB#N1MCARN,LA/4D992C[1KCA131ARQ13DA,=ERE[1JCA13A113AD11D1'=[1ICA%@N\B1OCAA92DC\BPP1PCARCePCP9g010dRC1E1A'APQeO1PEf;1E1@,ACPReO1POP3PKfAP0P4O2X1JPL^1JfB1E1F,ACPGeRGO1PMP5PKfFP0P4O2X1JPH^1JfGPGO1PIg011JRIg012VRG#CRJ#CRH#CRK#C,>21>2HRH1>2G5D25D2g0135RG'_1>2K1>2J9D2H5D2/_G%tI5]I3]%sI%r2RIf6RG,[2?7GI779?73I1[25?7GI?7GI97I8774%q2%p2RI1:2>R>1:2?5F2RH%o?,:2R?%5:#H,:25F2RJ'<,;I%k6R6PI1<?>,;IP6PI1:2=R=1:2:5F2R:/<?,;I1<J=,;I5WIP61<:>,;I1<H=,;I5WICGCGCG1gI7P0P3g00l@RIg0126R7'A1i03=9I7dAf214CjbQbTbUX>2X?2X@2XA2XB2XC21438R41495'11158114Gf7R4,4G/13'B1489/15145G/18'B[[[^>2^?2^@2^A2^B2^C2P0fSfTfQfRfUfVfNfOfPO9bPb=b<bDb;b:bDb6b5fMR0fL'4fIRG'1fH,4G/10'BebHbGbFbEb5bObNbMbLbKb6bJbRb:b;b<b=bSbWbVbIUUUX82X42X72X32X92X22P5P9P8P3CXf8P4P9P8CX\;\<[^82^42^72^32^92^22eo"). Qed.

  

  

  

  

  

  

  Notation W4FX := (W4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs).

  Definition w4_ist (P pc : Z) (x8 x9 x10 x12 x18 x19 x20 x22 x25 : word) (mm : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (P + 296)) (Z_to_bv 64 P) gp tp (Z_to_bv 64 (-24)) (Z_to_bv 64 2) (Z_to_bv 64 3)
            x8 x9 x10 (Z_to_bv 64 (-1 * DT + -5)) x12 (Z_to_bv 64 (P + 256)) (Z_to_bv 64 (P + 336))
            (Z_to_bv 64 (-17)) (Z_to_bv 64 (-16)) (Z_to_bv 64 (-25)) x18 x19 x20 (Z_to_bv 64 AW4_K21) x22
            (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB) (Z_to_bv 64 (DT + 4))
            (Z_to_bv 64 4) (Z_to_bv 64 5) (Z_to_bv 64 6) (Z_to_bv 64 (-8)))
       FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs).

  Definition w4_lo (o0 o1 o2 o3 : Z) (po4 : word) : list cell :=
    [C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3)); C8 po4].
  Definition w4_li (i0 i1 i2 i3 : Z) (pi4 : word) : list cell :=
    [C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3)); C8 pi4].
  Definition w4_lb (b0 b1 b2 b3 : Z) (pb4 : word) : list cell :=
    [C8 (Z_to_bv 64 b0); C8 (Z_to_bv 64 b1); C8 (Z_to_bv 64 b2); C8 (Z_to_bv 64 b3); C8 pb4].

  Lemma w4_ablk_ap : forall a b, ablk a b -> a <= b -> KXGoM.apart a (b - a) ASHOFF (ATOP / 8 + 1).
  Proof.
    intros a b H HL. pose proof (@ATOP_lo rc). pose proof (@ATOP_hi rc).
    unfold KXGoM.apart, ablk, AIMG_HI, KLS, ASHOFF in *. lia.
  Qed.

  Lemma w4_stk_ap : forall a, ATOP + 4096 <= a -> KXGoM.apart a 480 ASHOFF (ATOP / 8 + 1).
  Proof.
    intros a H. pose proof (@ATOP_lo rc). pose proof (@ATOP_hi rc).
    unfold KXGoM.apart, ASHOFF in *. lia.
  Qed.

  Lemma w4_tab11 : forall mm, tl = 11 -> bytes_at bsegs mm (DT + 4) cbs -> ztab_fact bsegs mm (DT + 4) 4096 2 [(0, 0, 11)].
  Proof using All.
    intros mm T11 BA z HZ lo' hi' FF.
    pose proof TOK as (TL1 & TL2 & TC). rewrite T11 in TL2, TC, ECB.
    cbn [find_field] in FF. revert FF.
    destruct (Z.eqb_spec 0 ((z - (DT + 4)) mod 2)) as [E0|E0]; intro FF; [injection FF as <- <- | discriminate FF].
    set (v := (z - (DT + 4)) / 2).
    assert (HZv : z = DT + 4 + 2 * v) by (pose proof (Z.div_mod (z - (DT + 4)) 2 ltac:(lia)); unfold v; lia).
    assert (Hv : 0 <= v < 2^11) by (unfold v; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    rewrite ECB in BA. change (x1_bytes cells) with (x1_bytes' cells) in BA.
    unfold FseNCount.Zlength in TL2.
    destruct (x1_cell_rd bsegs mm (DT + 4) cells (Z.to_nat (2 * 2 ^ 11)) v BA ltac:(lia)
                ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia)) as [R0 _].
    destruct (TC v Hv) as [NB _].
    rewrite HZv. exists (Z_to_bv 8 (x1_nbBits (nth (Z.to_nat v) cells x1_default))).
    rewrite <- ov_rdn. split; [exact R0 |].
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 8) with 8.
    rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma w4_tr : forall (mm mm' : amem) (fr mid l256 l296 l336 l256' l296' l336' : list cell) (buf' : list Z),
    W4FX mm fr mid l256 l296 l336 ->
    munch [(SPF + 256, SPF + 376); (DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
    u8arr bsegs mm' DST (map (Z_to_bv 8) buf') -> zlen buf' = dcap ->
    rw_cells bsegs mm' (SPF + 256) l256' -> cells_size l256' = 40%nat ->
    rw_cells bsegs mm' (SPF + 296) l296' -> cells_size l296' = 40%nat ->
    rw_cells bsegs mm' (SPF + 336) l336' -> cells_size l336' = 40%nat ->
    W4FX mm' fr mid l256' l296' l336'.
  Proof using All.
    intros mm mm' fr mid l256 l296 l336 l256' l296' l336' buf' HW MU' WM' MI' OUT' LOUT2 C256' L256' C296' L296' C336' L336'.
    destruct HW as ((buf & OUT & LOUT) & SRCB & TB & DTH & STK & FRC & FRL & MIDC & MIDL & C256 & L256L & C296 & L296L
                    & C336 & L336L & FRSC & MI & MU & WM).
    pose proof w4_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
    pose proof w4_dtl as HDTL.
    pose proof DJ1 as DJ1u. pose proof DJ2 as DJ2u. unfold KXGoM.apart in DJ1u, DJ2u.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
              (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))))).
    - exists buf'. split; assumption.
    - eapply bytes_at_transport; [exact SRCB | exact MU' | cbn [disjoint_from]; rewrite length_map; lia].
    - eapply bytes_at_transport; [exact TB | exact MU' | cbn [disjoint_from]; lia].
    - eapply bytes_at_transport; [exact DTH | exact MU' | cbn [disjoint_from length]; lia].
    - eapply stk_transport_disjoint; [exact STK | exact MU' | exact WM' | cbn [disjoint_from]; lia].
    - eapply rw_cells_transport; [exact FRC | exact MU' | exact WM' | cbn [disjoint_from]; rewrite FRL; lia].
    - exact FRL.
    - eapply rw_cells_transport; [exact MIDC | exact MU' | exact WM' | cbn [disjoint_from]; rewrite MIDL; lia].
    - exact MIDL.
    - exact C256'.
    - exact L256'.
    - exact C296'.
    - exact L296'.
    - exact C336'.
    - exact L336'.
    - eapply rw_cells_transport; [exact FRSC | exact MU' | exact WM' | cbn [disjoint_from cells_size csize]; lia].
    - exact MI'.
    - eapply munch_trans; [exact MU |].
      apply (munch_weaken [(SPF + 256, SPF + 376); (DST, DST + dcap)]); [| exact MU'].
      intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx1 & Hx2 & _). repeat split; lia.
    - eapply wmono_trans; [exact WM | exact WM'].
  Qed.

  Definition w4_fr (w0 w8 w16 : word) : list cell :=
    [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 AW4_M5); C8 (Z_to_bv 64 AW4_M7); C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT);
     C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap));
     C8 (Z_to_bv 64 SS)].


  Definition w4_c117 (Q : machine_state -> Prop) (b0 b1 b2 b3 : Z) : Prop :=
    forall (mm : amem) (w0 w8 w16 po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25 : word),
      W4FX mm (w4_fr w0 w8 w16) (fast_args_cells DST dcap SS DT src b0 b1 b2 b3)
           (w4_lo 0 ((dcap + 3) / 4) (2 * ((dcap + 3) / 4)) (3 * ((dcap + 3) / 4)) po4)
           (w4_li (jt_len src 0 - 2) (jt_len src 0 + jt_len src 2 - 2) (jt_len src 0 + jt_len src 2 + jt_len src 4 - 2)
                  (n - 8) pi4)
           (w4_lb b0 b1 b2 b3 pb4) ->
      evtF bsegs RNG Q (w4_ist SPF 0x880d8 x8 x9 x10 x12 x18 x19 x20 x22 x25 mm).


  Let w4_d0 := @AF_huf_w4body.w4_d0 rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs pdt pb SBL SBH rstk AH HDT HDB LOA LOS SPT SP16 LCB MTL cells TOK ECB DC NSM SBB SBA DJ1 DJ2 UDT UDB USB WSK WIM WDT WDB WSB WDTS WDBS WSBS RCL RLO RHI RRL RRS w4_blocks w4_unp w4_dtl.
  Let w4_d1 := @AF_huf_w4body.w4_d1 rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs pdt pb SBL SBH rstk AH HDT HDB LOA LOS SPT SP16 LCB MTL cells TOK ECB DC NSM SBB SBA DJ1 DJ2 UDT UDB USB WSK WIM WDT WDB WSB WDTS WDBS WSBS RCL RLO RHI RRL RRS w4_blocks w4_unp w4_dtl.
  Let w4_d2 := @AF_huf_w4body.w4_d2 rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs pdt pb SBL SBH rstk AH HDT HDB LOA LOS SPT SP16 LCB MTL cells TOK ECB DC NSM SBB SBA DJ1 DJ2 UDT UDB USB WSK WIM WDT WDB WSB WDTS WDBS WSBS RCL RLO RHI RRL RRS w4_blocks w4_unp w4_dtl.
  Let w4_d3 := @AF_huf_w4body.w4_d3 rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs pdt pb SBL SBH rstk AH HDT HDB LOA LOS SPT SP16 LCB MTL cells TOK ECB DC NSM SBB SBA DJ1 DJ2 UDT UDB USB WSK WIM WDT WDB WSB WDTS WDBS WSBS RCL RLO RHI RRL RRS w4_blocks w4_unp w4_dtl.
  Let w4_d4 := @AF_huf_w4blk.w4_d4 rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs pdt pb SBL SBH rstk AH HDT HDB LOA LOS SPT SP16 LCB MTL cells TOK ECB DC NSM SBB SBA DJ1 DJ2 UDT UDB USB WSK WIM WDT WDB WSB WDTS WDBS WSBS RCL RLO RHI RRL RRS w4_blocks w4_unp w4_dtl.
  Let w4_rl := @AF_huf_w4blk.w4_rl rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs pdt pb SBL SBH rstk AH HDT HDB LOA LOS SPT SP16 LCB MTL cells TOK ECB DC NSM SBB SBA DJ1 DJ2 UDT UDB USB WSK WIM WDT WDB WSB WDTS WDBS WSBS RCL RLO RHI RRL RRS w4_blocks w4_unp w4_dtl.
  Let w4_hd := @AF_huf_w4blk.w4_hd rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs pdt pb SBL SBH rstk AH HDT HDB LOA LOS SPT SP16 LCB MTL cells TOK ECB DC NSM SBB SBA DJ1 DJ2 UDT UDB USB WSK WIM WDT WDB WSB WDTS WDBS WSBS RCL RLO RHI RRL RRS w4_blocks w4_unp w4_dtl.
  Let w4_pre := @AF_huf_w4blk.w4_pre rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs pdt pb SBL SBH rstk AH HDT HDB LOA LOS SPT SP16 LCB MTL cells TOK ECB DC NSM SBB SBA DJ1 DJ2 UDT UDB USB WSK WIM WDT WDB WSB WDTS WDBS WSBS RCL RLO RHI RRL RRS w4_blocks w4_unp w4_dtl.
  Lemma w4f_nz : forall C k, 0 <= C < k -> C mod k <> 0 -> 1 <= C < k.
  Proof.
    intros C k HC HM. destruct (Z.eq_dec C 0) as [E | E]; [subst C; rewrite Zmod_0_l in HM; congruence | lia].
  Qed.

  Lemma w4f_nz0 : forall C k, 0 <= C -> C mod k <> 0 -> 1 <= C.
  Proof.
    intros C k HC HM. destruct (Z.eq_dec C 0) as [E | E]; [subst C; rewrite Zmod_0_l in HM; congruence | lia].
  Qed.

  Lemma w4f_m89 : forall C, C mod 2^8 <> 0 -> C mod 2^9 <> 0.
  Proof.
    intros C H E. apply H.
    rewrite <- (w4f_mod_div C (2^8) (2^9)) by (try (exists 2; reflexivity); vm_compute; reflexivity).
    rewrite E. reflexivity.
  Qed.

  Lemma w4_it : forall (Q : machine_state -> Prop) (mm : amem) (fr mid : list cell) (o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 OL : Z)
      (po4 pi4 pb4 x9 x10 x12 x18 x19 x20 x22 x25 : word),
    tl = 11 ->
    W4FX mm fr mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb B0 B1 B2 B3 pb4) ->
    0 <= o0 -> o0 + 5 <= dcap -> 0 <= o1 -> o1 + 5 <= dcap -> 0 <= o2 -> o2 + 5 <= dcap -> 0 <= o3 -> o3 + 5 <= dcap ->
    7 <= i0 -> i0 + 8 <= n -> 7 <= i1 -> i1 + 8 <= n -> 7 <= i2 -> i2 + 8 <= n -> 7 <= i3 -> i3 + 8 <= n ->
    0 <= B0 < 2^64 -> 0 <= B1 < 2^64 -> 0 <= B2 < 2^64 -> 0 <= B3 < 2^64 ->
    B0 mod 2^9 <> 0 -> B1 mod 2^9 <> 0 -> B2 mod 2^9 <> 0 -> B3 mod 2^9 <> 0 ->
    DST <= OL <= DST + dcap ->
    (forall (mm' : amem) (C0 C1 C2 C3 nb0 nb1 nb2 nb3 : Z) (y9 y10 y12 y18 y19 y20 y22 y25 : word),
       W4FX mm' fr mid (w4_lo (o0 + 5) (o1 + 5) (o2 + 5) (o3 + 5) po4) (w4_li (i0 - nb0) (i1 - nb1) (i2 - nb2) (i3 - nb3) pi4)
         (w4_lb C0 C1 C2 C3 pb4) ->
       0 <= nb0 <= 7 -> 0 <= nb1 <= 7 -> 0 <= nb2 <= 7 -> 0 <= nb3 <= 7 ->
       0 <= C0 < 2^64 -> 0 <= C1 < 2^64 -> 0 <= C2 < 2^64 -> 0 <= C3 < 2^64 ->
       C0 mod 2^9 <> 0 -> C1 mod 2^9 <> 0 -> C2 mod 2^9 <> 0 -> C3 mod 2^9 <> 0 ->
       (DST + o3 + 5 < OL -> evtF bsegs RNG Q (w4_ist SPF 0x88170 (Z_to_bv 64 OL) y9 y10 y12 y18 y19 y20 y22 y25 mm')) /\
       (OL <= DST + o3 + 5 -> evtF bsegs RNG Q (w4_ist SPF 0x880d8 (Z_to_bv 64 OL) y9 y10 y12 y18 y19 y20 y22 y25 mm'))) ->
    evtF bsegs RNG Q (w4_ist SPF 0x88170 (Z_to_bv 64 OL) x9 x10 x12 x18 x19 x20 x22 x25 mm).
  Proof using All.
    intros Q mm fr mid o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 OL po4 pi4 pb4 x9 x10 x12 x18 x19 x20 x22 x25
      T11 HW HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3 HOL K.
    eapply w4_d0; [exact T11 | exact HW | first [assumption | lia] .. | idtac].
    clear HW HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3.
    intros ?mm ?C0 ?C1 ?C2 ?C3 ?y9 ?y10 ?y12 ?y18 ?y19 ?y20 ?y22 ?y25 HW HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3.
    eapply w4_d1; [exact T11 | exact HW | first [assumption | lia] .. | idtac].
    clear HW HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3.
    intros ?mm ?C0 ?C1 ?C2 ?C3 ?y9 ?y10 ?y12 ?y18 ?y19 ?y20 ?y22 ?y25 HW HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3.
    eapply w4_d2; [exact T11 | exact HW | first [assumption | lia] .. | idtac].
    clear HW HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3.
    intros ?mm ?C0 ?C1 ?C2 ?C3 ?y9 ?y10 ?y12 ?y18 ?y19 ?y20 ?y22 ?y25 HW HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3.
    eapply w4_d3; [exact T11 | exact HW | first [assumption | lia] .. | idtac].
    clear HW HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3.
    intros ?mm ?C0 ?C1 ?C2 ?C3 ?y9 ?y10 ?y12 ?y18 ?y19 ?y20 ?y22 ?y25 HW HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3.
    eapply w4_d4; [exact T11 | exact HW | first [assumption | lia] .. | idtac].
    clear HW HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3.
    intros ?mm ?C0 ?C1 ?C2 ?C3 ?y9 ?y10 ?y12 ?y18 ?y19 ?y20 ?y22 ?y25 HW HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3.
    apply (w4f_nz _ _ HB0) in LB0. apply (w4f_nz _ _ HB1) in LB1.
    apply (w4f_nz _ _ HB2) in LB2. apply (w4f_nz _ _ HB3) in LB3.
    eapply w4_rl; [exact HW | first [assumption | lia] .. | idtac].
    clear HW.
    intros ?mm ?C0 ?C1 ?C2 ?C3 nb0 nb1 nb2 nb3 ?y9 ?y10 ?y12 ?y18 ?y19 ?y20 ?y22 ?y25 HW N0 N1 N2 N3 HC0 HC1 HC2 HC3
      LC0 LC1 LC2 LC3.
    eapply K; [exact HW | first [assumption | apply w4f_m89; assumption | lia] ..].
  Qed.

  Lemma w4_inner : forall (r : nat) (Q : machine_state -> Prop) (mm : amem) (fr mid : list cell)
      (o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 OL e0 e1 e2 e3 : Z) (po4 pi4 pb4 x9 x10 x12 x18 x19 x20 x22 x25 : word),
    tl = 11 ->
    W4FX mm fr mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb B0 B1 B2 B3 pb4) ->
    0 <= o0 <= o3 -> 0 <= o1 <= o3 -> 0 <= o2 <= o3 -> 0 <= o3 -> o3 + 5 * Z.of_nat (S r) <= dcap ->
    7 * Z.of_nat (S r) <= i0 -> i0 + 8 <= n -> 7 * Z.of_nat (S r) <= i1 -> i1 + 8 <= n ->
    7 * Z.of_nat (S r) <= i2 -> i2 + 8 <= n -> 7 * Z.of_nat (S r) <= i3 -> i3 + 8 <= n ->
    0 <= B0 < 2^64 -> 0 <= B1 < 2^64 -> 0 <= B2 < 2^64 -> 0 <= B3 < 2^64 ->
    B0 mod 2^9 <> 0 -> B1 mod 2^9 <> 0 -> B2 mod 2^9 <> 0 -> B3 mod 2^9 <> 0 ->
    OL = DST + o3 + 5 * Z.of_nat (S r) ->
    e0 = o0 + 5 * Z.of_nat (S r) -> e1 = o1 + 5 * Z.of_nat (S r) -> e2 = o2 + 5 * Z.of_nat (S r) ->
    e3 = o3 + 5 * Z.of_nat (S r) ->
    (forall (mm' : amem) (j0 j1 j2 j3 C0 C1 C2 C3 : Z) (y9 y10 y12 y18 y19 y20 y22 y25 : word),
       W4FX mm' fr mid (w4_lo e0 e1 e2 e3 po4) (w4_li j0 j1 j2 j3 pi4) (w4_lb C0 C1 C2 C3 pb4) ->
       i0 - 7 * Z.of_nat (S r) <= j0 <= i0 -> i1 - 7 * Z.of_nat (S r) <= j1 <= i1 ->
       i2 - 7 * Z.of_nat (S r) <= j2 <= i2 -> i3 - 7 * Z.of_nat (S r) <= j3 <= i3 ->
       0 <= C0 < 2^64 -> 0 <= C1 < 2^64 -> 0 <= C2 < 2^64 -> 0 <= C3 < 2^64 ->
       C0 mod 2^9 <> 0 -> C1 mod 2^9 <> 0 -> C2 mod 2^9 <> 0 -> C3 mod 2^9 <> 0 ->
       evtF bsegs RNG Q (w4_ist SPF 0x880d8 (Z_to_bv 64 OL) y9 y10 y12 y18 y19 y20 y22 y25 mm')) ->
    evtF bsegs RNG Q (w4_ist SPF 0x88170 (Z_to_bv 64 OL) x9 x10 x12 x18 x19 x20 x22 x25 mm).
  Proof using All.
    induction r as [| r IH];
      intros Q mm fr mid o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 OL e0 e1 e2 e3 po4 pi4 pb4 x9 x10 x12 x18 x19 x20 x22 x25
        T11 HW HO0 HO1 HO2 HO3 HO3b HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3 HOL E0 E1 E2 E3 K;
      (eapply w4_it; [exact T11 | exact HW | first [assumption | lia] .. | idtac]);
      clear HW;
      intros mm' C0 C1 C2 C3 nb0 nb1 nb2 nb3 y9 y10 y12 y18 y19 y20 y22 y25 HW N0 N1 N2 N3 HC0 HC1 HC2 HC3 LC0 LC1 LC2 LC3.
    - split; intro HL; [exfalso; lia |].
      replace (o0 + 5) with e0 in HW by lia. replace (o1 + 5) with e1 in HW by lia.
      replace (o2 + 5) with e2 in HW by lia. replace (o3 + 5) with e3 in HW by lia.
      eapply K; [exact HW | first [assumption | lia] ..].
    - split; intro HL; [| exfalso; lia].
      eapply (IH Q mm' fr mid (o0 + 5) (o1 + 5) (o2 + 5) (o3 + 5) (i0 - nb0) (i1 - nb1) (i2 - nb2) (i3 - nb3)
                 C0 C1 C2 C3 OL e0 e1 e2 e3); [exact T11 | exact HW | first [assumption | lia] .. | idtac].
      clear HW.
      intros mm'' j0 j1 j2 j3 D0 D1 D2 D3 z9 z10 z12 z18 z19 z20 z22 z25 HW J0 J1 J2 J3 HD0 HD1 HD2 HD3 LD0 LD1 LD2 LD3.
      eapply K; [exact HW | first [assumption | lia] ..].
  Qed.

  Lemma w4_outer : forall (m : nat) (Q : machine_state -> Prop) (w0 w8 w16 : word) (mid : list cell),
    tl = 11 ->
    (forall (mm : amem) (o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 : Z) (po4 pi4 pb4 y8 y9 y10 y12 y18 x19 x20 x22 x25 : word),
       W4FX mm (w4_fr w0 w8 w16) mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb B0 B1 B2 B3 pb4) ->
       0 <= o0 <= dcap -> 0 <= o1 <= dcap -> 0 <= o2 <= dcap -> 0 <= o3 <= dcap ->
       0 <= i0 -> i0 + 8 <= n -> 0 <= i1 -> i1 + 8 <= n -> 0 <= i2 -> i2 + 8 <= n -> 0 <= i3 -> i3 + 8 <= n ->
       0 <= B0 < 2^64 -> 0 <= B1 < 2^64 -> 0 <= B2 < 2^64 -> 0 <= B3 < 2^64 ->
       B0 mod 2^9 <> 0 -> B1 mod 2^9 <> 0 -> B2 mod 2^9 <> 0 -> B3 mod 2^9 <> 0 ->
       evtF bsegs RNG Q (w4_ist SPF 0x892c4 y8 y9 y10 y12 y18 x19 x20 x22 x25 mm)) ->
    forall (mm : amem) (o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 : Z)
      (po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25 : word),
    W4FX mm (w4_fr w0 w8 w16) mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb B0 B1 B2 B3 pb4) ->
    0 <= o0 <= o3 -> 0 <= o1 <= o3 -> 0 <= o2 <= o3 -> 0 <= o3 <= dcap -> dcap - o3 < Z.of_nat m ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= i1 -> i1 + 8 <= n -> 0 <= i2 -> i2 + 8 <= n -> 0 <= i3 -> i3 + 8 <= n ->
    0 <= B0 < 2^64 -> 0 <= B1 < 2^64 -> 0 <= B2 < 2^64 -> 0 <= B3 < 2^64 ->
    B0 mod 2^9 <> 0 -> B1 mod 2^9 <> 0 -> B2 mod 2^9 <> 0 -> B3 mod 2^9 <> 0 ->
    evtF bsegs RNG Q (w4_ist SPF 0x880d8 x8 x9 x10 x12 x18 x19 x20 x22 x25 mm).
  Proof using All.
    induction m as [| m IH];
      intros Q w0 w8 w16 mid T11 KF mm o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25
        HW HO0 HO1 HO2 HO3 HM HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3.
    - exfalso; lia.
    - eapply w4_hd; [exact HW | lia .. | |].
      + intros HX y8 y9 y10 y12 y18. eapply KF; [exact HW | first [assumption | lia] ..].
      + intros HR HC1 HC2 HC3 y9 y10 y12 y18.
        assert (Q5 : 5 * ((dcap - o3) / 5) <= dcap - o3) by (apply Z.mul_div_le; lia).
        assert (Q7 : 7 * (i0 / 7) <= i0) by (apply Z.mul_div_le; lia).
        assert (ERX : exists R, R = Z.min ((dcap - o3) / 5) (i0 / 7)) by eauto.
        destruct ERX as [R ER0]. rewrite <- ER0 in *.
        assert (R5 : 5 * R <= dcap - o3) by lia. assert (R7 : 7 * R <= i0) by lia.
        assert (ER : Z.of_nat (S (Z.to_nat (R - 1))) = R) by lia.
        eapply (w4_inner (Z.to_nat (R - 1)) Q mm (w4_fr w0 w8 w16) mid o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3
                  (DST + o3 + 5 * R) (o0 + 5 * R) (o1 + 5 * R) (o2 + 5 * R) (o3 + 5 * R));
          [exact T11 | exact HW | first [assumption | lia] .. | idtac].
        clear HW.
        intros mm' j0 j1 j2 j3 C0 C1 C2 C3 z9 z10 z12 z18 z19 z20 z22 z25 HW J0 J1 J2 J3 HC0 HC1' HC2' HC3' LC0 LC1 LC2 LC3.
        eapply (IH Q w0 w8 w16 mid T11 KF); [exact HW | first [assumption | lia] ..].
  Qed.

  Hypothesis FX : w4fx_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cbs.

  Lemma w4_exit : forall (b0 b1 b2 b3 : Z) (w0 w8 w16 : word) (mm : amem) (o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 : Z)
      (po4 pi4 pb4 y8 y9 y10 y12 y18 x19 x20 x22 x25 : word),
    3 * ((dcap + 3) / 4) < dcap -> 8 <= jt_len src 0 -> 8 <= jt_len src 2 -> 8 <= jt_len src 4 ->
    jt_len src 0 + jt_len src 2 + jt_len src 4 + 6 + 8 <= n ->
    W4FX mm (w4_fr w0 w8 w16) (fast_args_cells DST dcap SS DT src b0 b1 b2 b3)
      (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb B0 B1 B2 B3 pb4) ->
    0 <= o0 <= dcap -> 0 <= o1 <= dcap -> 0 <= o2 <= dcap -> 0 <= o3 <= dcap ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= i1 -> i1 + 8 <= n -> 0 <= i2 -> i2 + 8 <= n -> 0 <= i3 -> i3 + 8 <= n ->
    0 <= B0 < 2^64 -> 0 <= B1 < 2^64 -> 0 <= B2 < 2^64 -> 0 <= B3 < 2^64 ->
    B0 mod 2^9 <> 0 -> B1 mod 2^9 <> 0 -> B2 mod 2^9 <> 0 -> B3 mod 2^9 <> 0 ->
    evtF bsegs RNG POST (w4_ist SPF 0x892c4 y8 y9 y10 y12 y18 x19 x20 x22 x25 mm).
  Proof using All.
    intros b0 b1 b2 b3 w0 w8 w16 mm o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 po4 pi4 pb4 y8 y9 y10 y12 y18 x19 x20 x22 x25
      HSG L1 L2 L3 LS HW HO0 HO1 HO2 HO3 HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3.
    unfold fast_args_cells, w4_fr, w4_lo, w4_li, w4_lb in HW. cbv zeta in HW.
    replace (SS + 6 + jt_len src 0 + jt_len src 2 + jt_len src 4)
      with (SS + (6 + jt_len src 0 + jt_len src 2 + jt_len src 4)) in HW by ring.
    replace (SS + 6 + jt_len src 0 + jt_len src 2) with (SS + (6 + jt_len src 0 + jt_len src 2)) in HW by ring.
    replace (SS + 6 + jt_len src 0) with (SS + (6 + jt_len src 0)) in HW by ring.
    pose proof NSM as HN.
    unfold w4fx_goal in FX. unfold w4_ist.
    eapply FX; [exact HW | first [lia | (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64;
                                         rewrite Z.mod_small by lia; eapply w4f_nz0; [| eassumption]; lia)] ..].
  Qed.

  Lemma w4_fast : w4fa_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cbs.
  Proof using All.
    unfold w4fa_goal.
    intros w0 w8 w16 w24 w32 w64 w96 j256 j296 j336 b0 b1 b2 b3 mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HW T11 HN L1 L2 L3 LS DC0 DS HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3.
    eapply w4_pre; [exact HW | first [assumption | lia] .. | idtac].
    unfold AF_huf_w4blk.w4_c117.
    intros mm' w0' w8' w16' po4 pi4 pb4 x8 x9 x10 x12' x18 x19 x20 x22 x25 HW'.
    pose proof NSM as HNS.
    assert (SG : 0 <= (dcap + 3) / 4) by (apply Z.div_pos; lia).
    eapply (w4_outer (S (Z.to_nat dcap)) POST w0' w8' w16' (fast_args_cells DST dcap SS DT src b0 b1 b2 b3) T11);
      [| exact HW' | first [assumption | lia | (change (2^9) with 512; assumption)] ..].
    intros mm'' o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 po4' pi4' pb4' y8 y9 y10 y12 y18 y19 y20 y22 y25 HW'' HO0 HO1 HO2 HO3
      HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b HC0 HC1 HC2 HC3 LC0 LC1 LC2 LC3.
    eapply w4_exit; [exact DS | exact L1 | exact L2 | exact L3 | exact LS | exact HW'' | first [assumption | lia] ..].
  Qed.
End W4F.
End CANSEC1.
