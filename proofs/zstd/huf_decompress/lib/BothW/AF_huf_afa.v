(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Cells.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require PropExec.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_afa () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission3Lib5Cells<cells_wf_appK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib5Cells7cell_wfK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission3Lib5Cells?cells_bytes_appC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow<le8_of_bytesC47Corelib4Init3Nat3addC5ARocqVerifyHarness?AgentSubmission3Lib5Cells>cells_size_appK47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib5CellsBcells_bytes_lengthC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00C46Stdlib5Lists4List9app_nil_rC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rK47Corelib4Init5Logic2ex01I47Corelib4Init5Logic4True00C5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenC56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission6Common4KXGo@estart_zsa_splitC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS6estartC47Corelib4Init5Peano2ltC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdC46Stdlib5Lists4List9nth_errorC46Stdlib5Lists4List:length_mapC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Peano2le00C6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS4flatC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26adenotC5ARocqVerifyHarness?AgentSubmission2AS8PropExec3rdnC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zleC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses;rew_iff_revC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26a_baseC45stdpp9bitvector;definitions;bv_unsignedC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25a_offC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9zsa_denotC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec3rdnC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6ov_rdnC56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4ListAnth_in_or_defaultC46Stdlib5Lists4List2InI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List=Forall_forallC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zle_okK5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk06C5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes6option01C46Stdlib9micromega;ZifyClasses5mkrelC47Corelib5Lists7ListDef3nthK47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op205I5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00I46Stdlib9micromega:ZMicromega;ZArithProof00C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27ext_valC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7div_1_rK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr07I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00K47Corelib4Init9Datatypes4bool02C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rhiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit7shcleanK47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac9kshz_factC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6hull64C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow7app_blkC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow?unpoisoned_fullC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega3Op201I5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFI47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z=testbit_neg_rC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z;shiftr_specC56Stdlib6ZArith6BinInt1Z<testbit_onesC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z;shiftl_specC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z9bits_inj'I46Stdlib;setoid_ring<Ring_polynom5PExpr00I47Corelib4Init9Datatypes4prod00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03I46Stdlib;setoid_ring<Ring_polynom3Pol00C56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z7add_0_lC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z7div_addK46Stdlib;setoid_ring<Ring_polynom5PExpr07K46Stdlib;setoid_ring<Ring_polynom5PExpr05C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterI46Stdlib;setoid_ring<Ring_polynom3Mon00C45stdpp9bitvector;definitions8bv_swrapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fa_ifaceDAHUF_FAST_ARGS_STACKC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa7afa_sp0C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa8afa_kshzC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8artcellsK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fa_iface?fast_args_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5apartC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa:afa_cb8_c8C5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC46Stdlib5Lists4List:Forall_appK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp03K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk03C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission6Common4KXGo8zk_wr_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9apart_subC5ARocqVerifyHarness?AgentSubmission6Common4KXGo:zk_disj_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM:zk_word_okK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF6win_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF5zw_okK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6unp_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM5zu_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8unp_raccC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6zur_okC5ARocqVerifyHarness?AgentSubmission6Common5KXGoF8shz_raccC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC46Stdlib5Lists4List7forallbC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry08K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01C5ARocqVerifyHarness?AgentSubmission6Common5KXChk8kxl_execC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM6rv_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9rv_chk_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk5rv_okC5ARocqVerifyHarness?AgentSubmission6Common5KXChk>kxl_know_finalC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM8sc_auto3C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_scs_bulk3C5ARocqVerifyHarness?AgentSubmission6Common5KXGoM9acc_auto3C5ARocqVerifyHarness?AgentSubmission6Common6KXFoot4accPC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM@kx_accs_ok_part3C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_in_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_in_okC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7win_ivlC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:log_insideC5ARocqVerifyHarness?AgentSubmission6Common6KXPost2ezC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS5elenZI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula02C56Stdlib5Arith8PeanoNat3Nat3ltbC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9elenZ_litC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<estart_ez_kEC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_inside_monoC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_munch_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem:kx_stk_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wmono_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_wr_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem>kx_mem_inv_logC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost9estart_ezC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<log_apart_ezC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?log_apart_ez_okC5ARocqVerifyHarness?AgentSubmission6Common6KXCell>kx_cell_store8C5ARocqVerifyHarness?AgentSubmission6Common6KXPost5ez_okC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission6Common5KXMem?kx_rw_cells_logC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr04K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fa_iface=fast_args_okAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeK47Corelib4Init5Logic2or01C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common5KXChk<kx_run_evtFLC5ARocqVerifyHarness?AgentSubmission6Common5KXGoM<kx_pendingFmC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission6Common6KXCell;kx_rwc_consC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib5Lists4List7Forall202K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickI5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00C56Stdlib6ZArith4Znat5Nat2Z7inj_addI6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fa_ifaceCAHUF_FAST_ARGS_INITI46Stdlib5Lists4List6Exists00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr5aluop07I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litI4ELinuxProcessSemantics5Riscv5Instr5instr00K47Corelib4Init5Logic2or02c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa7afa_boxC5ARocqVerifyHarness?AgentSubmission6Common5KXMem?kx_bytes_at_logC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=bytes_at_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit3>le4_four_bytesC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K4ELinuxProcessSemantics5Riscv5Instr5instr01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_luiC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5b_luiK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7eqb_neqK5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp05C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa;afa_desc_tlc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_afa>afa_sx32_smallC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK4ELinuxProcessSemantics5Riscv5Instr5msize03I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma afa_cb8_c8 : forall m A pre post bs, rw_cells bsegs m A (pre ++ CB 8 bs :: post) ->
  rw_cells bsegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_afa ()) [] "h01Hh11ah21bh32Hbh42Hwh53Hwfh61lh71Ah82H1h92H2h:2H3h;2bsh<1mh=1nh>4posth?3prep;1p;4p;2p;3p;6p-1p10000p4p710p9p1000\p4p710g0019R0p4p710R1p8p1001Wp4p7210P1p8g002Cj1:Tg002hj1MTg003Fj1LTg003ij1PTg004Kj1NTg004kj14Tg005Jj4=Tg006@j4ETg0077j12Tg0080j18Tg008Pj19Tg009Pj1;Tg00:Ej10Tg00;<j11Tg00<6R1j2BTg00<Qj2TTg00=Lj2ATg00>Aj1FTg00?7j4?Tg00?Rj33Tg00?oj2JTg00@mj6ITg00AIj1STg00B9j2RTP0j6DTg00C6j2GTg00CMj2HTg00DJj3@Tg00Djj4OTg00E\j4QTg00FQR0f3R2f2R3f1R4'Af0R55@033p=5g00GFR6P3P4P5COp=6A@0459303p=CP6P3P4P5CQp=7A3045p=<1A34=@05p=>A@045p=Kg00H;#:#:#:R7#:#:#:#M#L%M7#LR7#P[g00H`%N0R0%N7R8P6f4R9P2P3g00I>#4#4#4#4#4#4#4#4R:P5P4C5C=P1P6f5R;P9P2P:P4P3C5R<CE%2<#896;9P6f6R<P;%93#;=C92C=P5P6f7R=P<P;P:P2P9C5CEP1P<P:P9P;C5R9#0f8R>%1977=f9R9P=P:P;P<C5#2#876>P6f:R;P9%9<#;=C>=C=[P5P>P:P<P=C5#0f;R?P9P:P=P>C5#177;f<R=P;P:P>P9C5#2#876?P11<45#0%03R9%04R>'BR@[RA%05,B>1<34#0R>[RB%02/B9\>1T45R>P4n2001000000120000000X20X10PA^20^10P5P=A>:;?R9P2O3%0=%09'BP1f=R9#0A>:?=#0P6f@RCf?RDf>RE%9=#;;C9C=P5%0DA>:ED#0P11A:D#F%0CP6fDRDfCREfB%9C#;fARC3CC=P51A:C#F%0EP6fGR6fFRCfER9%9E#;/KDR='<RFCE%2FRG#8966C%0F%1FRF976CP1PAPB1<23#0\@P>P5n2001000000120000000X20X10PB^20^10P5PC%9DRB#;R>/K9R@%0C%0@P<%F>%09g00I]P4C?C?O3b0P8%19R>%1=537fHR<?765X68R2P8A>:EDRE,<9R:#1P2P?%1E937>R>1J9EEIA76C>P8PDfI%16%1CR>937553777<X68P5%SB1RD3ED%1@937>97<6eb3PF1J9=EDC?g00J9RF%29R>%2='G%8596<6X=FR7PF%2:P7P;%2E,G>R>1H9EEI%8>966CP5%2C%2@'G#896<6eb4PG1H9=EDC?W:W9P4P5O2n2001000000121000000W0W8P4P5O2n2001000000121000000b5b0W4W3W5P4P5O2n2001000000121000000W0P4P5O2n2001000000121000000W0W;X>0W?W7W<o"). Qed.

(* [comment removed for export] *)
Lemma afa_rwc_cb : forall m A cs, rw_cells bsegs m A cs -> exists ja', rw_cells bsegs m A [CB (cells_size cs) ja'].
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_afa ()) [] "h03ja'h11Hh21Ah32HLh42Hbh52Hwh63Hwfh72csh81lh91mh:1np;1p;4p;2p;3p;6g002Cj11Tg002hj1ATg003Fj1=Tg003ij1DTg004Kj1CTg005Jj46Tg006@j49Tg0077j10Tg0080j14Tg00Djj43Tg00=Lj25Tg00JXj1<Tg00DJj38Tg00K8j2BTg00:Ej1;Tg00;<j12Tg00E\j47Tg00KRj2JTg00LSj2@Tg00M3j3?Tg00?7j4:Tg00?Rj3ITg00MMj2GTg0019j6>Tg00Mkj2FTg00NKj1ETg00Noj4HTg00H;#1#1#1R0#1#1#1#A#=%A0#=R0#D[g00H`g00FQR1#Cg00GFR2f2R3f1R4f0R5C6g00<6R6P2f3R7P3P4C9P2P7P3%04#4C3%C0R8P2f5R9f4R:%07/55%<1R;581C6X08'BP5P2P9P:P7C9P6%;:P2f6R6P9%2:C7P2f7R:P6%09#4C3P2f9R9f8R7%0:/55=81;C6X08,B8[P5%;6P2P9P7%2:C7P2f:R:P9%07#4C3P8P2f<R7f;R6%0:R</55=81;C6X08%29R=1J93g00J9R>1@0=%093?P2P7P6%2:R:,5<=81;R;C9P2P7P6%0;#4C3R1%;;R9P2P7P6%2;C7R;1@0:=?><g00OIP5g00I]C:P9eP8P:P2f=R9P7P5C7X88P3%<09I0:1G0:E>P;eC:P>P<P2P9P7%45C3X:>P4g00I>,F<%E<E>P1eC:b3CHW5W4W6P4P5O2n2001000000121000000W1P4P5O2n2001000000121000000W1W7W2W9o"). Qed.

(* [comment removed for export] *)
Section ByteK.
Variable segs : list Segment.
Variable zv : list Z.
Variable xs : list word.
Variable m : word -> option byte.
Local Notation E := (kE zv xs).
Local Notation na := (length zv).

Lemma zk_byte_ok : forall a v b c S bs k,
  zatoms_lt na a = true -> zatoms_lt na v = true -> zsa a = SA b c ->
  0 <= zden zv a - c < 2^64 -> 0 <= zden zv a < 2^64 ->
  bytes_at segs m S (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs -> 0 <= k < zlen bs ->
  zden zv a = S + k -> zden zv v = Znth k bs ->
  kentry_ok segs E m (zk_ent (ZKWord a 1 v)).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_afa ()) ["ByteK"] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with54cstrh61zh71bh81ii001ih92BYh:1Hh;2RDh<2X2h=4__x2h>1ch?1xh@2ADhA2BKhB2EshC2H1hD2H2hE2HBhF3HB'hG2HDhH2HIhI2HahJ2HkhK2HshL2HvhM2R1hN2R2hO1ShP2X1hQ2_HhR1ahS2bshT1khU1lhV5lemmahW1nhX1ohY1si011shZ1vi021ep&0p;1p;2p;3p;4p;9p;6p;7p;8p;<p100Oep4p70R0g00P[R1p4p710p8P0g00Q7R2p4p710R3p8P0p100QXp4p710p8p100RWp4p70P3p8p100SMp4p70P3p8g004Kj1]Tg00TCk205Tg00M3j30Tg00UAj1XTg00V6k20ETg00W4j2ETg00Wmk204Tg002Cj1<Tg00XJj1OTg00Xhj2dTg00YEj29Tg002hj1kTg003Fj1iTg00Yak10Jj24Tg00E\k40ATP2j3\Tg0080R2j11Tg00ZGj25Tg00Zdj2CTg00[\m901Tg00\]j2|Tg00]Qj2aTg00LSj2>Tg00^Oj2WTg003ij1eTg00^gj1@Tg00_Vj3STg00`Fj3VTg00<6R3j22Tg00`dj4mTg00@mj6NTg00aCj1PTg00JXj1_Tg00ahj2^Tg00bFk10NTg00bdk40MTg00cBk10LTg00c`k10KTg00dKj2hTg00dnj3gTg00eQj2MTg00f4k30ITg00fWk10DTg00g9k20@Tg00g[j2LTg00h5k20>Tg00hak30=Tg00i@k40<Tg004kj1=Tg00j2R0k209Tg00jLk308Tg00kHj2cTg00lEj4QTg00m9j1YTg00mnj2RTg00nkj2DTg0103R4j2KTg010Ok402Tg0019j6ATg011:k100Tg0127j2bTg012aj1~Tg013]j4{Tg014Xj7zTg015Uj4`Tg00DJj3FTg016Zj4yTg017Oj4}Tg018Gj1JTg018gj4xTg019Mj3ITg019dR5j2wTg01:Dj2vTg01:]k306Tg01;Nk307Tg01<0j2uTg01<Vk10:Tg01=4k10;Tg01=]j3tTg01>Ij2sTg01?8j2rTg01@5j4qTg00?7j4fTg01@mk30?Tg01Acj1pTg01B[k40BTP1k40CTg01C\j4jTg01DGj7oTg01Dkj7nTg01EOk80FTg01F3k20GTg01FUm<0HTg01G:j4lTg00H`R1f0R6'>p=:g01GVR7f1R8'K/26p=8P1f2R9P8P6H0Cp=61K76p=71986,29p=T1598/K6p=3P1P8g01H4P6Cjp=GP8g01H[R:g01I:R;P;g01IZR<P6g01J:Fop=;P9P:P;P;P<P8P6Fnp=Bf3R=P:P;P;P<P9P8P6L0Fp=U20G8690=9p=?g00J9R:P1P0P2P4g01JZf5R4f4P=P9P8P6N<0Hp>03P1P8g01K<P6Cjp=[P1P8P6P7Clp=HA0167p=Zg01KcR2g01L^%]1g01M[R0p,2zvR>#:f6R?+05g01N;R@30RAg01N[f8RB#X20E?430f9RC,E>004?RDg00H;RE#<RF#ORG%<F#<RH#<#<#<RI#O'dRJ,9D'8f:RD,E>RK19KJ'8p,4segsRKp,1mRLf7RM%kHRN#iRO&0JNRP;6?H0A%76RQ%<I#<#ORR7T6RSX>1RT=\1M%:B#1,9M,8Mf>RU,E>RV15DB5011CCD901VP>p,2xsRVf@RDPUf=RWPCPMP?P4N9011|>VR?%XD'a1E>D501P3%7WRXf<RY96OP,>O#1=3WJA6OPW,>O,W6%eORZf?R[%18R\'5#@9SKLA6OPU=VO830[^8:'2%:WR]#1R^=3UJ,8UP4%7[A6OP[,>O#1=3DJA6OPD,>OR_,W6fBR`/5\#@9SKLfARa96OPRb=VO850Z[^8:'2P3%1_=3aJ1>Ob,W6fCRb/5\#@9SKLA6OP`R_=VO850Z[^8:%:aR3#1Rc=3`J,8`P61>O_#1=3bJfDR_96OP,>ORd,W6fFRe/5\#@9SKLfER\96OP=VO850Z[^8:P:Pd%16=3eJXW:P8%:_R:P1POPPP_CmEN%1:=3\J%:\R:#P%1:#7g01OYR:#_RP%]:R:P11^19P8&0N1ReH0M&0L1Rd&0K1RZ1h1ERf1h1F5g11M1G%kIRI60I1RF'G,;ZRg&0D;R;PZ1M17Rh/Gf,;ZRiP;ABZigCUCU20@Z<R<P6P91L0@20>69=00@dB0=178H0<R@b2b3b4X01X=1A368J%78R0A39=J,89[[^01^=1P6fG#:#1fHP9PBO4b1b5b<WQW<P8P6O2n2001000000121000000W:WPP8P6O2n2001000000121000000%:Y#1=3WJ,2Xg00I>#=RX%=X#=#=#=#=#=#=RB+09Rg%X`Rj%1XRk608?Rl%]ORm#eRnPKPL1c?jRoPXCQPm%Ya,R?,DXC?Rp'2Pg%OERE%OHRH'KRgPXPE1L1EPBPH1L1HJ03%P]R]%7^R^PPP:PePd1M1ERB1M1H'G,;ZP<P@b2b3b4PgP6b1b5H02PlPpP11E>`Rp196JRg%7kRHA36kJ'2'2,2QX61P]P^PPP:1^18R^PdPZ1[fF,;ZR]9BZiRqP;1GhB,;ZAg1fB/GF,;Z5BZ9BZ]9BZiCUP<P@b2b3b4X0112Qg198JRgA38EJ,8E'2,20[^01P61E>_PCO2b1b519pJA3pkJ,2H'2,8pe1a?jRHP8EAPleP1Pp%iIRl%Xb,c?Rk14I6RJ30X61Pl14IHRHA0lk6X7l&00j,R?,bI%~j'5,4I,LlA0loHe14IpRHP>PVP`f;RjC{EN15UYRYP=EN%@Y90loRoePoPl15[WRo#@PnPKPLP6PXCQPm%Yb,R?,DXC?X7lPlPHPnPKPL15DURH#@PXCQRYPm1DX6C?X7lP11CWURlPnPYPm1DXJC?X61PKPLP[PUPWPMP4FzPnPKPL14IoPXC`Pm14Nl%_ORl5FOC?PnPKPL14IHRHPXC`PnP6Pm1C[DRo,4N=FOlC?XXnP6PKPLPHPXCyR4PKPLPXPHC}ENPnP4Pm1CU[,4N=FOlC?P1%J[RUPDP7Cx1HUDRU=I1D%ZU'wP5%JD/HaR5=I1a%Z5%Ja/H`R5195R'8P6AI15`A\1TbAI16_PTP8O1RU[^?1R4'vA\1T_AI16\PU[^?1<066WVB071TbPjO2P4P6%Jb/H_P8O2b9WHP6O1%Z5P1P7PSX61%:bR5#P%15#7PPP:PePd1Ghh,;Z1M1RRe,[h,;Z5BZP<P@b2b3b41K77?T7RP6b1b5%J`/HbP6EAWGP6O1n200110100021010010102bY19oR,8oRoePoP11CDaRo,uIRR1Ca`Ra,4N=FOlR714N6=FOl50mX61RhP1PoPh14No=FOlRl,LmPR%P3%7cPPP:P^PdPZ1[fe,;Z9BZiP;PqCUP<P@b2b3b4X01120g\S^01P61C`bP9O2b1b5%7oRb&0:I,dG7Toe&0;I9Tboe9tIoEA14IoRb,bIRG1sIoEA1rXG90mle1DXb90mlRlePlPmP7PnPKPL15_`#@PXCQPmP6C?XUmP914Ia,DXP6ENb:bAb;b;PpP=EA%Y`,R?P>PVP`PjCqEAPkP6EAb@CfCfbFbBPKP?PLB0?DX[#pH0BeWLWIWJW9WEWNWMWKXDAWCXT1WSXO1X>1W7XZ2WRo"). Qed.
End ByteK.

(* [comment removed for export] *)
Ltac afa_kbyte S src BY SRC :=
  lazymatch goal with
  | |- kentry_ok ?segs (kE ?zv ?xs) ?m (zk_ent (ZKWord ?a 1 ?v)) =>
      let s1 := eval vm_compute in (zsa a) in
      lazymatch s1 with SA ?b ?c =>
        let za := eval cbv [zden nth] in (zden zv a) in
        let k := lazymatch za with
                 | S + ?k => k
                 | S => constr:(0)
                 end in
        eapply (zk_byte_ok segs zv xs m a v b c S src k);
        [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | kx_arith | kx_arith | exact SRC | exact BY | lia | cbv [zden nth]; lia | cbv [zden nth]; reflexivity ]
      end
  end.

(* [comment removed for export] *)
Lemma afa_ext_byte : forall E j b, ev E j = Z_to_bv 64 b -> 0 <= b < 256 ->
  bv_unsigned (edenot E (EExt false 0 1 (EVar j))) = b.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_afa ()) [] "h01zh14__x1h27__arithh34__ffh48__varmaph55__with61bh71Eh81Hh92Hbh:1jp;1p;2p;3p;4p;6p;7p;8g002Cj10Tg002hj1YTg003Fj1NTg01PEj2JTg00Yaj2>Tg00M3j3=Tg0103j2DTg00XJj16Tg00YEj2;Tg00<6j2<Tg004kj1LTg01Q>j4GTg0127j25Tg0080j1HTg01R<j2FTg00Xhj2ETg01RYj27Tg01S6j22Tg01<0j28Tg00JXj1XTg004Kj1WTg00ahj2VTg00cBj1UTg00c`j1TTg00eQj2?Tg00dKj2RTg01C\j49Tg00fWj1MTg00g9j2OTg00g[j2PTg00h5j2QTg00haj3KTg00i@j4STg01SVj3CTg0019j64Tg01T9j1`Tg01>Ij2ITg01TZj1_Tg01UWj4^Tg00mnj2]Tg01DGj7ZTg01Dkj7[Tg01EOj8\Tf0R0#0#0p=@g00H`R1f1R2;=0p=1%00#0#0#0#0#0#0#0p=3P2g01H[R3g01I:R4P4g01IZR5P0g01J:FZp=:f2R6P3P4P4P5P2P0F[p=Af3R7P3P4P4P5P6P2P0G\p=Bg01VTg00J9g00H;R3#0R8#@R9#0#@R:#YR;#NR<1J621>;03=g01GVR=/D2R>%@:R:#6R?,;2'<R@P<1>;6RAg01WPRBg00I>RC%LCRDP0CG,5;/17X6<P115;AR<%68R8%69R9%HC'F'ERE'7%HD,F9,E8R8'2R9,8;1107X01P118;6RF170E/28RG,8;/17X01P1P6%3:#3#3#3#3#3#3#6R:,2G/17X01P1P6120?/2:/17X01P1P6120:/17X01g01OYRG#XRH%WGRG1V12RI%U1RJ%T1RKP11?1=g01H41R13RLC9,:KRMP1PLg01K<RN1?1?C9,:K5AKRO%M4R4P1PLPN1?1:C9,:K9AKMCB1OK5R5P0P6g01M[RMg01N;RN'P1Q06==MNdAK1=2CSRNb3b4b5X111D=01;0?'<R=1;2:,<>[^11P0P7P2O2R0b29C6:R>126?PHPGPIPJPKPOP4POCBP5PNb3b4b5X11P@\=^11P0b29C6?E4%63,76%`6E4126:P>E417FE/28,8;/16eP<1I;6E41>;9,5;1I;9E4PBPCPDPACG,5;/16ef4RA/J7P2E4PBPCPD%_7C^,]A,5;/16eW9W8X61W:W7o"). Qed.

(* [comment removed for export] *)
Ltac afa_word_try segs zv xs m a v b c A cs H ks :=
  lazymatch ks with
  | nil => fail
  | cons ?k ?rest =>
      first [ eapply (zk_word_ok segs zv xs m a v b c A cs k _);
              [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
              | kx_arith | kx_arith | kx_arith | kx_arith | exact H | reflexivity
              | cbv [zden nth]; lia
              | cbv [zden nth]; first [ symmetry; apply Z_to_bv_bv_unsigned | f_equal; first [reflexivity | lia] ] ]
            | afa_word_try segs zv xs m a v b c A cs H rest ]
  end.
Ltac afa_wrange := lazymatch goal with |- 0 <= bv_unsigned ?w < 2 ^ 64 =>
  let RW := fresh "RW" in pose proof (bv_unsigned_in_range 64 w) as RW; unfold bv_modulus in RW; cbn in RW; lia end.
Ltac afa_kword :=
  lazymatch goal with
  | |- kentry_ok ?segs (kE ?zv ?xs) ?m (zk_ent (ZKWord ?a 8 ?v)) =>
      let s1 := eval vm_compute in (zsa a) in
      lazymatch s1 with SA ?b ?c =>
        match goal with H : rw_cells segs m ?A ?cs |- _ =>
          let ks := eval vm_compute in (c8_offsets 0 cs) in
          afa_word_try segs zv xs m a v b c A cs H ks end
      end
  end.

(* [comment removed for export] *)
Lemma afa_kshz : forall m r A N, rclean m r -> r_lo r <= A -> A + N <= r_hi r -> A mod 8 = 0 -> N mod 8 = 0 -> 0 <= N ->
  kshz_fact m 2147450880 A N.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_afa ()) [] "h01Hh12H0h23H13h32H7h44__p1h54__p2h64__x1h74__x2h84__x3h94__x4h:4__x5h;7__arithh<4__ffh=8__varmaph>5__with?3H10h@3H11hA3H12hB3H14hC3H15hD3H16hE2H3hF2H4hG2H5hH2H6hI2H9hJ5__x10hK4__x6hL4__x7hM4__x8hN4__x9hO1qhP2q0hQ2q1hR2r0hS2r1hT2r2hU1AhV2ABhW2H1hX2H2hY2H8hZ2HFh[2HNh\2HUh]2Hxh^2LTh_1Nh`2N8ha2SHhb1Uhc2WRhd1mhe1rhf1xhg1zp%0p&0p;1p;2p;5p;4p;3p;6p;7p;8g002Cj1CTg002hj1fTg003Fj1kTg003ik10ATg01X0k20?Tg01Xkj14Tg01Ydj12Tg01Z]j1:Tg01[Wj1=Tg01\Qj5_Tg00YEj2;Tg0103j20Tg00ZGj25Tg00XJj1UTg01S6j21Tg01]Mj1FTg01^2j4iTg01^mj3hTg01_hj4YTg01`cj19Tg00Wmj2QTg01a[j2OTg00<6R0j27Tg01bSj2VTg00Yaj2TTg01F3j2vTg00M3j3ETg01RYj26Tg01c3j5sTg00^gj1rTg00Xhj2qTg01d3j2^Tg01dTj1pTg01dmj2dTg01eTj2cTg01f;j2bTg01faj2aTg01gGk20@Tg00g[j2oTg004kj1?Tg01ghj2nTg01hQj2mTg00JXk10>Tg00DJj3lTg004Kk10=Tg00bFk10<Tg00cBk109Tg00c`k108Tg00eQj2XTg01C\j4]Tg00fWk106Tg01i=k605Tg01iaj3ZTg00dKj2eTg00g9k204Tg00h5k203Tg00hak302Tg00i@k401Tg01jDj1}Tg01jbj2|Tg01kCj3STg01klj2{Tg01lUj3~Tg01m>k200Tg01R<j2gTg01mjj3zTg0019j6yTg00Djj4xTg01nSj3jTg00ahk207Tg00bdj4wTg01o<k60:Tg01DGk70;Tg01Dkj7uTg00dnj3tTg01EOj8`Tf0R1#C#Cp=Hg00H`R2g01GVR37E1p=L1031p=<%F1#Fp=Rf2R4f1R5/;1'7p=Ag00GFP4P5P1Cxp=P1g45/51p=@AE251p=>1n21p=BAj2519j24p=G20721p=MP2P4P5P1Cwp=8P5g01H[R6g01I:R7P7g01IZR8P1J0:p=\1e21p=DP5P6P7P7P8P1g01J:K0;p=3P4P6P7P7P8P5P1Fup=[P2P5g01o`P1C]p=IAt251p=Kf3R9P6P7P7P8P4P5P1G`p=WP2P5g01H4P1C]p=Jf6R:P6P7P7P8f5R;f4R<P9P6P7P7P8P4P5P1G`G`p=Ng00H;R=#CR>#CR?#CR@#C#H#fRA#k%f@RB#kRC$0ARD[g020G20?94P0P<%49RE%29RF%:9%=9D_1;EF%4</0915<9%2;RF'0%U@RE,1;#LRG%<:f:RH%F=RI#FRJ#F#R#R#R#R#R#R#C#H#H#H#H#H#H#H#URKf8RLf7RMCi[\G[[[P1P:%4;PF%:;%=;D_%4:%2:';%4M/0:15M:%2L'011LE#LRFf9RG#<RNf<RO/01f;RP,5O7A1PLf?RQf>RR#4%2R%:R%=RD_P0f@RS%4QRT%2QRU3hPTPU%:QRV%=QRWCY%9VRV%9W/QV5PS1OTU'7'7fARU%UIRT,V9,5K,TAO11TB3,vCRC5EDP1fBRB%4U%2U3h%4BRV%2BRW%:BRX%=BRYCYfCRZ%9XRX%9Y/QX3P1OVW'7'7P0%4ZRW%2ZRV%:ZRX%=ZRYCYfDR[%9XRX%9Y/QX3P1OWV'7fERV1VMT,5K,TAO1=EDCP1%4V%2V%:V%=VCYfGRWfFRX#:#9RY%=X#9/QY3P%4X%2X'O'7P0fHR0%:W#9RX%=W#9/QX3P%4W%2W'OfIRW1VPT,5K,TAO1=EDCP1fJRX%:W#9RY%=W#9/QY3P%4X%2X'OfLRXfKRY#4RW%2Y16RERRPGDs%UJRY9@ER,0W16QE=@EE%2X'0fNRXg021D16SERW'5#rO1=EDC[[P2%U>/qT,6QPX15K1,TAO1=EDCXg2P11^QES00%LERC#pRD11SE9@EW,>S[S011dSES021;3ERW11UERA#<?AAE[S031cUES041;E3RA11BERX,;E10X3'7[S051bBES0616ZE#L\CS071aZES0811[E/>[\CS0916[ES0:P211VES0;P2fQ/^ES0<fRR[16[E11[E5@E'>\DS0=1d[ES0>fSR[/1ERX#<?AXE\WS0?1c[ES0@fTR[/1ERX,;E10X3'7\AS0A1b[ES0BfUR[/6E#L\CS0C1a[ES0DfVR[/1E/>[\CS0E16[ES0FP2fWR[/1ES0GP2fY/^ES0HfZRX16XE11XE5@E'>\DS0I1dXERDf[RR/1ER\#<?A\E\WR\1cRER]f\R^/1ER_,;E10_3'7\ARA1b^ER_f]R`/6E#L\CRa1a`ERbf^Rc/1E/>c\CRd16cERcP2f_/1EReP2P;g022>20@3E'oPWeRWO1Rf%<1?A1ERgf=RhPWO1Ri%<L?ALERjPVPWO1RW%<S?ASERSp-0RVg01OYRkg00I>Rl#?Rm#?Rn#?Ro#?Rp#BRq%BoRo%BnRn%BmRm1n2lRl3G3Gg022dRr'm&0>kRs3l&0=kRt%M<&0<2Ru789?84u%M;?8;u?8;u785&092Rv&082Rw1\wMP2%F?#DRxg01K<S0J1X2ERyC],3w5[w&067RzPwPwPwP6P7P7P81X23R7,Iy,3wJ05R6Pz%D@R@%D>R{9Z2yR|/Kx'I,3wCWPzPw%D?R?/J@,3w1\wL5[wPzPw1e2=R}/J?,3wPz1X2Y,K|,J},3wFNFN204w8R8P1P4g01M[R|g01N;R~'o20314=E|~dB02235H01R3b<b=b>X62X72X82X92X:2X4VW5AA;<Eg023P\CRCA@E9:,>;[10<;/7L109;A@E;Y,0<[[[[^62^72^82^92^:2^4V^5VP1fXRYfdR~fcS0K'5';%<BPBPYP~PZfeR|#4P5P0P[P`O;b;b1b3b2bTbQbDbCbBb2bAbSbPb@b?bIb3bHbRbObGbFbEb1b0Q00Q01Q02Q03Q04Q05Q06Q07Q08Q09Q0:P2Q0;P2Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FP2Q0GP2Q0HQ0IPDP\P]PAP_PaPbPdPcP2PeP2PfPgPiPjPWPS%?pRp#?RS#?RW#?Rj#BRi%BW%BS%}=,|2R=%Bp5S2AGqon3G3G1{2E=~2l%?j#B9S2=AS2=iAS2=qAS2=o?Gnm3G3G/mr+00=lksPt%MM?89u%MG?8;u784%ML?8<u%MH?8:u78H785PvPwPwP6Pz%F>R>#F#D9Z2y%CI#DRI'K,I?,3wCWPzPwPwP6Pz%D>R4%C>#D9Z2y%DJRJ'K'I,3wCWPzPw1J7x,3w1\wO5[wPzPwPwP6PzAZ2y}R}/Kx,I@,3wCWPzPw1\whP2P@Q0J1K?4R4C],3w5[wPzPw1IJ7,3wPzPw1II7,3wPzPw1J4{,3wPz1K}y/J{,3wFNFNFNFNP8P3b<b=b>X62X72X82X92X:2XK2XL2XM2XN2XJ2X4VX5V1gEHR{/5;,>9\C15{M,>;\C17NOA@E<P,>H\C15:M9AQH%LHRM15GH/0LA@ELE/0G[\M[[[[[[^62^72^82^92^:2^K2^L2^M2^N2^J2^4V^5VP110~Y1;BEP;POPBPYPPP<Q0KP~%2|PZPHPUP5P0P[PXPRP^ODb;b1b3b2bTbQbDbCbBb2bAbSbPb@b?bIb3bHbRbObGbFbEb1b0O21VQTPsPtPuPv1X2T,J7,3wP8P3b<b=b>%<TP1b;9zQTEybZWVWcP5P1O2n2001000000121000000W0W\P5P1O2n2001000000121000000W0WbP5P1O2n2001000000121000000b0W]Xf2PhPKPPPHCieW[X`FWYWXWWW^WaP5P1O2n2001000000121000000W0X_2XU2WeWdo"). Qed.

(* [comment removed for export] *)
Lemma afa_desc_tl : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 128 ->
  Z.land (a + 256 * b + 65536 * c + 16777216 * d) 16711680 = 65536 * c.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_afa ()) [] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with51zh61bi001bh71Hh84__x2h97fv_listh:8hyp_listh;3lmph<1Lh=4__p1h>4__p2h?4__p3h@4__p4hA4__x3hB4__x4hC1yhD1EhE2HahF2HbhG2HchH2HdhI2HihJ2HyhK1ahL2b0hM2b1hN1chO1dhP1ip&0p;1p;2p;3p;4p;6p;7p;8p;:p;<g002Cj16Tg00XJj1;Tg00YEj23Tg00<6j2<Tg01]Mj1DTg023mj2VTg01R<R0j22Tg024Kj20Tg024lj21Tg00g[j2]Tg025Jk10KTg025hj2jTg00Xhj2sTg00WmR1j2GTg026Hk20=Tg0103j2RTg026jj2QTg027GR2k308Tg01RYj2TTg01S6j2HTg00M3j3KTg00JXj1`Tg004Kj1ZTg00ahj2UTg00cBk102Tg00c`k100Tg00dKj2YTg00eQj2NTg00fWj1xTg027kj3wTg00g9j2vTg00h5k20NTg00hak30MTg00i@k40LTg028Nj3uTg0295k10JTg029Uj2kTg01bSj2tTg00ZGR3j27Tg00dnj3[Tg02:2k40ETg00bFk10DTg02:Wk30CTg02;=j3qTg02;`k30?Tg01mjk30>Tg02<Cj4pTg02<hk30<Tg02=Qk30;Tg02>4k10:Tg02>^j2fTg02?>j2WTg02?hj2eTg02@Rk106Tg01SVk305Tg0019j6>Tg02A:k404Tg02A[k103Tg004kj1PTg01ghj2MTg01hQj2aTg01m>j2nTg01klj2mTg01lUj3dTg00DJj3\Tg00bdj4hTg01iaj3gTg02B<k301Tg02B_j4~Tg01C\j4_Tg01DGj7rTg01EOj8}Tg00@mk60@Tg02C@j3|Tg02Cjk30ATg02DTm:0BTg02EEl<{Tg02F2j4zTg02FXk70FTg01Dkj7yTg01i=k60GTg01nSk30HTg01o<k60ITg01GVR4f0R5'Rp=?%65#6p>09%65#6#6#6p==f2R6f1R7'T/H5p=Bg01M[R8?K75p=4g00H`R9?K75p=5P9P7g01K<P5C_p=SP7g01H[R:g01I:R;P;g01IZR<P5g01J:R=Frp=Af3R>P:P;P;P<P6P7P5G}p=9g01N;R?9K85p=^P8g01WPR@P>P6P7P5E>p=lP9P7g01o`P5C_p=iP9f4RAP>P6P7P5J0@p=FP6P:P;P;P<P9P7g01H4P5C_P=Frp=:P8PAP>P6P7P5E>p=J1275,76p=8A\975p=EA|975p=@B0A975p=LP9P4P7P3P0P1g02GGR=g02GdRBg02HARCP5N:0Bp>07P9P4P6P3P0P1P=PBPCg02HbRCP7P5M<{p=OP9PBP7P5Czp=cPCPAP>P6P7g00I]P5K0Fp=bP6P:P;P;P<P7P5Fyp=IP7P:P;P;P<P5J0Gp=oB0H975p=CP7P:P;P;P<P5J0Ip=X%?>R:g00H;RC#6RB#6R=#6R1#6R0#6$09R3#6RD#;RE,3>'<RF%;3R3,3>,<:%?5RG%DCRH#D#D#D#D#D#D#=#=#=#=#;RI,V7RJ%=D#=RD#;RK=B7E/2KRL10>710I7'1ABAKE/2K/06,45X681]9I%;1R1$0KRM%;0R0'jRN/5IPNf5RO/0>RP105>RQ'1ABOKE/2K/0>'4X59%;BRR/s0RS=BAERT/j0RU10N>,1P/4QX591G60RQ,0M11P5ABOSE/j0/0>'4X6810TQ1G>0,0M,1P/45X6820=6013601R061Q604081Q>0P8P213A01R0Af8R2f6RP'0RQ1GP0RV,0MRW'11T2SRX/HERY/0VRZ'4P713O0f9R[f7R\'0R]/15AB[SE1G\0R^'0R_'4X68R`145_X68AK8@5X681]8@PZg01OYRZ#`R_%ZZRa1U97Rb&029Rc&009Rd1Y9CRe1N90Rf'S,Ad%x;R;Aw9efRg1N94Rh'S,AdC91vd<R<P5P61]8?R?20N56#^dB0M947H0LRib2b3b4X0913501G70Rj/34[^09P5P\P7O2Rkb1Rl9uYVCl11Q@&0JQClPWAuMVlClW<P5O11R0O1k4V1QV1'1RlP`1t20R`1k4^1Q^1'1RQ,1]R]1H5ER@/0^'4X591V`MRY105^,4]X5910`VRm/1W14]5X68Pl1t[0/0^/15,4]X6817V0Rl,02115Q,4]X68P_PaPbPcA[9gf,ie,AdP<Pib2b3b4X091G50/70,55^09P5P\O1b115PlP\f:Rl/021G20RQ,k41QQ1'1RQ'110l5/1Q'4X591]8]17^0P5DFb7PmP2P0PVP_PaPbPcPdA:dfeP;A:dhgC9P<Pib2b3b4X091R05%?j[^09Pkb1H0EDJPWP_Pa&0D9RkPc1N919:dhP<Pib2b3b4%?1P5b1Rj:0C1VRgDJ10YVAq`MVDJ1sR1,H`B0?`1jDFPXP_PaPkPcA:dhfP<Pib2b3b4%?0P5b1Rf:0>20DFPWPgDJW<P5O1n200210000000021100011000bMbL10U6PTP0P6P_PaPbPcPdA:dheRUP;PUC9P<Pib2b3b4X09%?7Rg\G^09P5P>P6O2b1RWCpDJ10N6PMP0P6PWCpDJ12TSB0<T0fDFPIP5DFb71V>I/07Aq>I7DJXIGXP940;WJXC915JL\G^C9P9A82E\RL12KPRJ'7%=D#=#;RD;8ORf?BKE/2K12K\RT,55X59&0:9R0/f0R0#`RS%Z0R0%`9RW,EP,E\,E2,E[%Z9RMP5P71W9CRN1e9ERX1W9BRj'@'LR`1W9HR11W9=RR,@X'L1e9KRV'@'LRY1@V1,L`1e9D/@R'LRRP?%;CRC0077R1g02IQ,f9&069'f#ZRmAOC5YAOC5R'cb;#^dDbb9b:12EORR,7P=8LK/5fRYePYA8[E2RYA8\EPR^;8KR]AB5KE/2K12K2R8'5X59P91TYKRQ/7^12@KR@/58X59RnP9P4175L/HE/2K/58X59P9P^PnPSP01E\W,E2PMP5P71@jX,LNRjP`P?P1PmAOC5jAOC5`'cb;#^dDbb9b:A8\PE/5^R`eP`A82\ER`12K[Rj,5@X59P91H2ER@125K/5jX59RjP9P2PjPSP01E[WPMP5P71@NVRM1@VNRVP?P1PmAOC5MAOC5V'cb;#^dDbb9b:122K/58eP@P_PaPbPcPd1N9ERb,Se,Ad9IdUR@P;P@C9P<Pib2b3b4X09135E,<G137E,<gRg[^09P5P[POO2b1:052EE>1H`EP2P\PEP_PaPkPc1ibh,Ad,odP<Pib2b3b4AK9E4g023PR`[P5b1H04E>PLP5DFb7174^&03^E>PQg00I>RQ#PRL#PRG,M91M9QRQ'C%PGRG#PR8#P,M9RV,CQg022dRC'a'n1m9ERM1M9GRG5d91M9L/CQRL'C/aC=\Z_5\ZPaP91U96P7PkChPcPd1Y9BRB9:dhRm1SBb,Ad5IdP;PdP@P;Ag9bB9[9eRe9:dh1N9KRB,Se,Ad5IdC9C9P<Pib2b3b4X09X89A86E>Rb#?13bK'<\g\g^09^89P5P[PlPOPPO4b1:01YKE>1T]KPYP^PKP_PaPkPc1iBh,Ad,odP<Pib2b3b4AK9K4P`[P5b1C~E>17YT?8DPP5DFb71VfIP5Pfp-0Rf1m9K=d9V1M989d9M/CG'C,CQ/aC,nL=\Z_PaP9P91U9AP6PkChP71U9>ChPcPd1Y9=R=9:dh1XdP5IdP;Pd1Y9HRH9:dh1Xd\5IdP;Pd1Xd29IdmP;Pd1Xd[9IdUP;Ag9BH9[9e1N9D=g9=5[99:dhC9C9C9C9P<Pib2b3b4X09X89XA9XB9X=fX>fX?fW@1<:A1<:P1<:21<:l17AR/7J?8D\#?[[[[^09^89^A9^B9^=f^>f^?f^@fP513[E132E13\E13P3PPP\P2P[P6P>PAPOO<b1O2E>bDWHXGFXFFWEXO9XN9X69XK9o"). Qed.

Lemma afa_sx32_small : forall v, 0 <= v < 2^31 -> bv_unsigned (Mem.sx32 (Z_to_bv 64 v)) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_afa ()) [] "h04__x1h11zh27__arithh34__ffh48__varmaph55__with61Hh72Hvh81vp;2p;1p;3p;4p;6p;7p;8g0103j2ATg002Cj10Tg00XJj17Tg01]Mj18Tg00Xhj2_Tg00YEj2@Tg00<6j2?Tg002hj1=Tg00Yaj2GTg0127j2<Tg02J9j2CTg01<0j2:Tg00ZGj2BTg01S6j23Tg00Wmj26Tg00JXj1YTg004Kj1XTg00ahj2WTg00cBj1VTg00c`j1TTg00dKj2STg00eQj25Tg00dnj3RTg027kj3QTg01C\j49Tg00g9j2OTg00g[j2NTg00h5j2MTg00M3j3FTg00haj3LTg00i@j4KTg00f4j3PTg00fWj1JTg01SVj3ETg00@mj6^Tg0019j6;Tg01>Ij2ITg02J`j1]Tg01DGj7\Tg01Dkj7ZTg01EOj8[Tf0R0#0#0#0#0p=Ug00H`R1f1R2;F0p=1%00#0#0#0#0#0#0#0p=2P2g01H[R3g01I:R4P4g01IZR5P0g01J:F\p=4P1P2g01K<P0C9p=Df2R6P3P4P4P5P2P0FZp=>f3R7P3P4P4P5P6P2P0G[p=Hg01GVR3/A0g00H;R8#0R9#7R:%88#8#8#8R;#7'_,@0'?R<P1%U9R9#0R=#=R>%=9R91G>2R?,<>R@'CRA':1106X11P11:>2RB1C90,:>/16X11P1P2%0=#2#2#2R=#7RC,B0RD%0=R=#7RE'3/6C%2=#2#2#2#7R='3/16X11P11B2CRF160C/3=/16X11g01OYRG#YRH%XGRG1W12RI%V1RJ%T1RKP11S18R8g01o`151CRL9R18RM=Q1LC9'41OK5R5P0P6g01M[RLg01N;RN'N1M06=FLNdAL132CKRNb3b4b5X0116DC,10^01P0P6O1b216FC,12P1P6130=/17X11PHPGPIPJPKP11513RDg01H4RLP8C9,4KRO151:%=;5P1,D8,4K5>KR;%J4R4151=,D8,4K9>KOCHP5PNb3b4b5X01RO1A321@2='?\<^01R8P0P7P6O2b29E6=1B6C/6CP0E^b613FEPHPGPIPJPKP;P4P1PDPLPMC9,4K151E,DM,4K5>KCHP5PNb3b4b5X011A3F1@FE'?\<^01P0P6P2O2R6b29EFEE;132=POP8P6b29E2=E;1C9B,:>/12eP@1I>2E;1G>A,<>1I>AE;%]?,<>/12eW7X81o"). Qed.

(* [comment removed for export] *)
Definition afa_box (P : Prop) : Prop := P.

Ltac w4ez :=
  repeat lazymatch goal with
  | |- context [edenot ?E _] =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite ?(ez_ok zv E (kE_atoms zv xs));
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
      end
  end.
Ltac w4br :=
  lazymatch goal with
  | |- branch_taken _ _ _ = _ =>
      w4ez; unfold branch_taken; rewrite ?bv_ltu_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      rewrite ?Z.mod_small by lia;
      first [ apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Z.ltb_lt; lia
            | apply Bool.negb_false_iff, Z.ltb_lt; lia | apply Z.ltb_ge; lia ]
  end.
Lemma afa_adenot_var : forall E i off z, ev E i = Z_to_bv 64 z -> 0 <= z < 2^64 ->
  adenot E {| a_base := EVar i; a_off := off |} = Z_to_bv 64 (z + off).
Proof.
  intros E i off z H Hz. unfold adenot, PropExec.v_addi. cbn [a_base a_off edenot]. rewrite H, Z_to_bv_small by (unfold bv_modulus; cbn; lia).
  reflexivity.
Qed.

Lemma afa_rd4 : forall segs (m : fmem) D a b c d,
  bytes_at segs m D [Z_to_bv 8 a; Z_to_bv 8 b; Z_to_bv 8 c; Z_to_bv 8 d] ->
  0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 128 ->
  rdval segs m (Z_to_bv 64 D) 4 true = Z_to_bv 64 (a + 256 * b + 65536 * c + 16777216 * d).
Proof.
  intros segs m D a b c d HB Ha Hb Hc Hd. unfold rdval.
  replace (Z_to_bv 64 D) with (wa (D + Z.of_nat 0)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_rdn segs m D _ 0 4 HB) by (cbn; lia).
  cbn [firstn skipn take drop bytes_le_to_Z].
  rewrite !(Z_to_bv_small 8) by (unfold bv_modulus; cbn -[Z.pow]; lia).
  change (0 ≪ 8) with 0. rewrite Z.lor_0_r.
  rewrite (lor_shiftl8_add c d) by lia. rewrite (lor_shiftl8_add b (c + 256 * d)) by lia.
  rewrite (lor_shiftl8_add a (b + 256 * (c + 256 * d))) by lia.
  unfold extz. rewrite bv_swrap_small by (unfold bv_half_modulus, bv_modulus; cbn -[Z.pow]; lia).
  f_equal; lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.

Lemma afa_sp0 : forall (sp : word) lo A, ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHUF_FAST_ARGS_STACK ->
  bv_unsigned sp <= A -> A + 152 <= 2^47 ->
  0x10007fff8000 <= bv_unsigned sp - 48 /\ bv_unsigned sp + 152 <= 2^47 /\ lo + 48 <= bv_unsigned sp.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_afa ()) ["CANSEC1"] "h04__p1h14__x1h24__x2h34__x3h44__x4h51Ah62ATh72H1h82H2h92H3h:2H4h;7__arithh<4__ffh=8__varmaph>5__with?2loh@2spp;1p;2p;3p;4p;6p;7p;8g002Cj10Tg002hj1FTg003Fj1MTg02KQj1bTg00XJj14Tg00ZGj28Tg0103j21Tg0127j2CTg00Wmj2BTg00Xhj2aTg02LGj1]Tg00<6j2ATg004kj1=Tg01ghj29Tg01nSj3<Tg01hQj2ITg00JXj1TTg00DJj3HTg004Kj1RTg00ahj2GTg00bFj1QTg00bdj4ETg00cBj1OTg00c`j1NTg01]Mj13Tg00dKj2?Tg01o<j6LTg00fWj1PTg00dnj3@Tg00f4j3JTg027kj3STg00g9j2`Tg00g[j2_Tg00h5j2^Tg00M3j3\Tg00haj3YTg00i@j4XTg00eQj2WTg01C\j4ZTg01DGj7[Tg01Dkj7VTg01EOj8UTf0R0#0#0#0#0p=7%00#0p=>%30#3p=K%30#3#3#3p=2%00#0#0#0#0#0#0#0p=:g00H`R1/W0p=6f2R2g01H[R3g01I:R4P4g01IZR5P1f1R6g01H4P0CZg01J:F[p=5P2P3P4P4P5P6P0FVp=Df3R7P3P4P4P5P2P6P0GUp=;g00H;R8#0R9#0R:#7R;#FR<#Mp,2rcR=#bR>%>;#7R;#4R?'8/161C<7g02MC'B,12f4R@,C</12%K:#0#>#4RA,87%49RB%29RC#4'aRD'1%]=g02NR/1>g02OL,1>'Ap-0R=g01OYREg00I>RF#=RG#=RH#=RI#=RJ,91191I191FRF5<15<1g022dRI'I%=J,91191H191G=<1F5<15<1/II%TE5HE3H%REP1P11G1@P2%Q1CEP61G17CE%O1%N1RE%38RI#3#2#2#2RF#0#2#2#0#>#7#:#:#4RG#61?1IRH55EPEP3P4P4P5f6R3EL5DE%P4R4PE1?1:R:%6ARJ5@1%6B%FC5J1RC55EP4PE1?18R8=5E:P4PE1?19R9%7I#4RI#6R:9S18RB55EP4PE%6?9@1H=5E9P4%0;#2#2#2#2#0#>#7#:#4R;#6=5EBA@18J=5ECA@19:=5E85DE5DEC;C;C;C;C;1`E5P0P2g01M[REg01N;R5'_1^02=\E5dg01GV=Y16CXb<b=b>X11X21X31X41W011G2/A@18@A/1Df5RG,121B7I,1@183?/1G1BGI,1;18GA/1D183I/1G'A'A[[[[[^11^21^31^41^0=P0%3F#2#2#0#>#7#:#:#4,1>P3P>f7f8,C<P6P2P7P@PGO:b;b6W:W9W8W7X51X?1W@o"). Qed.

Section AFA.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (A DST dcap S DT mtl tt tl mtl' : Z) (src : list Z) (ja : list byte) (lo : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis HA : rw_cells bsegs m0 A [CB 152 ja].
  Hypothesis A8 : A mod 8 = 0.
  Hypothesis DESC : bytes_at bsegs m0 DT [Z_to_bv 8 mtl; Z_to_bv 8 tt; Z_to_bv 8 tl; Z_to_bv 8 mtl'].
  Hypothesis RM1 : 0 <= mtl < 256.
  Hypothesis RTT : 0 <= tt < 256.
  Hypothesis RTL : 0 <= tl < 256.
  Hypothesis RM2 : 0 <= mtl' < 128.
  Hypothesis SRC : bytes_at bsegs m0 S (map (Z_to_bv 8) src).
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis NSM : n < 2^26.
  Hypothesis S0 : 0 < S.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DE : DST + dcap + 8 <= 2^64.
  Hypothesis DT0 : 0 < DT.
  Hypothesis DTL : DT + 4 <= lo.
  Hypothesis SL : 0 < n -> S + n <= lo.
  Hypothesis STK : stk bsegs m0 lo SP.
  Hypothesis LOS : lo <= SP - AHUF_FAST_ARGS_STACK.
  Hypothesis ASP : SP <= A.
  Hypothesis A47 : A + 152 <= 2^47.
  Hypothesis MI : mem_inv bsegs m0.
  Hypothesis UDT : unpoisoned m0 DT (DT + 4).
  Hypothesis USR : 0 < n -> unpoisoned m0 S (S + n).
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= A.
  Hypothesis RHI : A + 152 <= r_hi rstk.
  Hypothesis WFR : rng RNG (SP - AHUF_FAST_ARGS_STACK) AHUF_FAST_ARGS_STACK.
  Hypothesis WA : rng RNG A 152.
  Hypothesis WRS : rrng RNG rstk.
  Hypothesis WDT : rng RNG DT 4.
  Hypothesis WDTS : rng RNG (shad DT) 1.
  Hypothesis WSR : 0 < n -> rng RNG S n /\ rng RNG (shad S) (nshad (n + S mod 8)).
  Hypothesis WIM : rng_aimg RNG.
  (* [comment removed for export] *)
  Hypothesis ART : artcells m0.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis DT8 : DT mod 8 = 0.
  Hypothesis DPOS : 0 < dcap -> 0 < DST.

  Notation POST := (fast_args_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A DST dcap S DT src tl lo m0).
  Notation FRS := [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation MW := [(SP - AHUF_FAST_ARGS_STACK, SP); (A, A + 152)].


  (* [comment removed for export] *)
  Ltac afa_facts :=
    pose proof (afa_sp0 sp lo A LOA LOS ASP A47) as SPB;
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
    pose proof (afa_kshz m0 rstk A 152 RCL RLO RHI A8 eq_refl ltac:(lia)) as KSH;
    pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _);
    assert (RGOT' : rw_cells bsegs m0 0xaf758 [C8 (Z_to_bv 64 0x1494e8); C8 (Z_to_bv 64 0xb51b8); C8 (Z_to_bv 64 0xb79b8);
                                              C8 (Z_to_bv 64 0xb86a8); C8 (Z_to_bv 64 0xb86b0); C8 (Z_to_bv 64 0xb86a0)]) by exact RGOT;
    assert (RSHB' : rw_cells bsegs m0 0xb79b8 [C8 (Z_to_bv 64 0x7fff8000)]) by exact RSHB;
    clear RG0 RGOT RGRIC RMEM RSHB;
    assert (FAP : KXGoM.apart (SP - 48) 48 0x7fff8000 17592186044416) by (unfold KXGoM.apart; lia);
    assert (AAP : KXGoM.apart A 152 0x7fff8000 17592186044416) by (unfold KXGoM.apart; lia);
    unfold AHUF_FAST_ARGS_STACK in *.

  (* [comment removed for export] *)
  Lemma afa_dz : forall (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word), dcap = 0 ->
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 S)
                               (Z_to_bv 64 n) (Z_to_bv 64 DT) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 AHUF_FAST_ARGS_INIT) fc None m0 (seg_rom bsegs)).
Proof using All.
  intros t0 t1 t2 a6 a7 t3 t4 t5 t6 DZ.
  pose proof (afa_sp0 sp lo A LOA LOS ASP A47) as SPB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AHUF_FAST_ARGS_STACK in *.
  assert (SHD : Z.shiftr DT 3 + 0x7fff8000 + 1 <= SP - 48) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
  assert (WDTS2 : rng RNG (Z.shiftr DT 3 + 0x7fff8000) 1) by (unfold shad, ASHOFF in WDTS; rewrite Z.add_comm; exact WDTS).
  destruct (stk_carve bsegs m0 lo SP 48 STK ltac:(lia)) as (STK48 & junkf & FR48). change (Z.of_nat 48) with 48 in FR48.
  kx_runFm (@nil Z) 300%nat [KZRange dcap 0 0; KZRange DT 1 (2^47); KZAlign DT 8; KZRange SP 0x7fff7f801030 (2^47-152); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (SP - 48) 48; KZDisj (SP - 48) 48 0xb2128 8; KZDisj (SP - 48) 48 0xba2f8 8; KZDisj (SP - 48) 48 DT 4; KZDisj (SP - 48) 48 (Z.shiftr DT 3 + 0x7fff8000) 1] [(DT, 4)] [(SP - 48, 48); (0xb2128, 8); (0xba2f8, 8); (DT, 4)] [(DT, 4)].
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- region_ok _ _ _ _ => fail | |- _ =>
    (rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; cbn [cells_size csize]; lia) end).
  all: lazymatch goal with |- region_ok ?segs ?mm ?E (zr_reg (?a, ?n)) => let eb := eval unfold E in E in
    lazymatch eb with kx_env (map (Z_to_bv 64) ?zv) ?xs => let s1 := eval vm_compute in (zsa a) in
    lazymatch s1 with SA ?sb ?sc => refine (zr_ok_bytes_at segs zv xs mm a n sb sc DT _ _ _ _ _ _ _ DESC _ _);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | cbv [zden nth]; lia | cbv [zden nth]; lia | cbv [zden nth]; lia
      | cbv [zden nth]; lia | cbv [zden nth]; cbn [length]; lia ] end end | |- _ => idtac end.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- region_ok _ _ _ _ => fail | |- _ =>
    (rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; cbn [cells_size csize]; lia) end).
  apply (rw_cells_split_CB bsegs m0 (SP - 48) [] 48 junkf [] [8;8;8;8;8;8]%nat) in FR48; [| reflexivity]. cbn [app mk_CB_cells] in FR48. kx_cells_split FR48.
  pose proof (munch_refl [(SP - 48, SP); (A, A + 152)] m0) as MU.
  pose proof (wmono_refl bsegs m0) as WM.
  try kx_cell KC. try kx_cell KC0. try kx_cell KC1. try kx_cell KC2. try kx_cell KC3. try kx_cell FR48.
  kx_frame KC. kx_frame HA. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  zstep.
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold fast_args_postA.
  do 14 eexists. exists 0, m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|].
  split; [first [exact STK | exact STK48]|].
  split; [exists ja; exact HA|]. left; reflexivity.
Qed.

  (* [comment removed for export] *)
  Lemma afa_n10 : forall (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word), 1 <= dcap -> n < 10 ->
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 S)
                               (Z_to_bv 64 n) (Z_to_bv 64 DT) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 AHUF_FAST_ARGS_INIT) fc None m0 (seg_rom bsegs)).
Proof using All.
  intros t0 t1 t2 a6 a7 t3 t4 t5 t6 DC1 N10. pose proof (DPOS ltac:(lia)) as DP1.
  pose proof (afa_sp0 sp lo A LOA LOS ASP A47) as SPB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AHUF_FAST_ARGS_STACK in *.
  assert (SHD : Z.shiftr DT 3 + 0x7fff8000 + 1 <= SP - 48) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
  assert (WDTS2 : rng RNG (Z.shiftr DT 3 + 0x7fff8000) 1) by (unfold shad, ASHOFF in WDTS; rewrite Z.add_comm; exact WDTS).
  destruct (stk_carve bsegs m0 lo SP 48 STK ltac:(lia)) as (STK48 & junkf & FR48). change (Z.of_nat 48) with 48 in FR48.
  kx_runFm (@nil Z) 300%nat [KZRange dcap 1 (2^32 - 1); KZRange n 0 9; KZRange DST 1 (2^64 - 9); KZRange (DST + dcap) 2 (2^64 - 8); KZRange DT 1 (2^47); KZAlign DT 8; KZRange SP 0x7fff7f801030 (2^47-152); KZWord 0xb2128 8 0xba2f8; KZWord 0xba2f8 8 0x7fff8000; KZWr (SP - 48) 48; KZDisj (SP - 48) 48 0xb2128 8; KZDisj (SP - 48) 48 0xba2f8 8; KZDisj (SP - 48) 48 DT 4; KZDisj (SP - 48) 48 (Z.shiftr DT 3 + 0x7fff8000) 1] [(DT, 4)] [(SP - 48, 48); (0xb2128, 8); (0xba2f8, 8); (DT, 4)] [(DT, 4)].
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- region_ok _ _ _ _ => fail | |- _ =>
    (rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; cbn [cells_size csize]; lia) end).
  all: lazymatch goal with |- region_ok ?segs ?mm ?E (zr_reg (?a, ?n)) => let eb := eval unfold E in E in
    lazymatch eb with kx_env (map (Z_to_bv 64) ?zv) ?xs => let s1 := eval vm_compute in (zsa a) in
    lazymatch s1 with SA ?sb ?sc => refine (zr_ok_bytes_at segs zv xs mm a n sb sc DT _ _ _ _ _ _ _ DESC _ _);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | cbv [zden nth]; lia | cbv [zden nth]; lia | cbv [zden nth]; lia
      | cbv [zden nth]; lia | cbv [zden nth]; cbn [length]; lia ] end end | |- _ => idtac end.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- region_ok _ _ _ _ => fail | |- _ =>
    (rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; cbn [cells_size csize]; lia) end).
  all: try w4br.
  apply (rw_cells_split_CB bsegs m0 (SP - 48) [] 48 junkf [] [8;8;8;8;8;8]%nat) in FR48; [| reflexivity]. cbn [app mk_CB_cells] in FR48. kx_cells_split FR48.
  pose proof (munch_refl [(SP - 48, SP); (A, A + 152)] m0) as MU.
  pose proof (wmono_refl bsegs m0) as WM.
  try kx_cell KC. try kx_cell KC0. try kx_cell KC1. try kx_cell KC2. try kx_cell KC3. try kx_cell FR48.
  kx_frame KC. kx_frame HA. kx_munch MU.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
  kx_post_mem_free.
  lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
  kx_post_regs_keep.
  zstep.
  try clearbody KXE; try clearbody KXxs.
  apply evtF_done. unfold fast_args_postA.
  do 14 eexists. exists (2^64 - 20), m1. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|].
  split; [first [exact STK | exact STK48]|].
  split; [exists ja; exact HA|]. right; left; reflexivity.
Qed.


  Ltac afa_tlbr :=
    lazymatch goal with
    | |- branch_taken BC_NE (edenot ?E (EAlu ALU_AND (EVar ?j) (ELit ?mk))) (edenot ?E (ELit ?lt)) = _ =>
      let H := fresh "HR" in kx_read_eq j H;
      lazymatch type of H with
      | ev E j = rdval ?segs ?mm (adenot E {| a_base := EVar ?i; a_off := ?off |}) 4 true =>
        lazymatch goal with KXA : forall j, (j < length ?zv)%nat -> ev E j = _ |- _ =>
          rewrite (afa_adenot_var E i off _ (KXA i ltac:(vm_compute; lia))) in H by (cbv [nth]; lia);
          cbv [nth] in H; rewrite Z.add_0_r in H;
          rewrite (afa_rd4 segs mm DT mtl tt tl mtl' DESC RM1 RTT RTL RM2) in H;
          unfold branch_taken; cbn [edenot]; rewrite H, alu_and; unfold v_and;
          rewrite bv_eqb_Z;
          rewrite (Z_to_bv_small 64 (mtl + 256 * tt + 65536 * tl + 16777216 * mtl')) by (unfold bv_modulus; cbn -[Z.pow]; lia);
          rewrite (Z_to_bv_small 64 mk) by (unfold bv_modulus; cbn -[Z.pow]; lia);
          rewrite (afa_desc_tl mtl tt tl mtl' RM1 RTT RTL RM2);
          rewrite !Z_to_bv_small by (unfold bv_modulus; cbn -[Z.pow]; lia);
          first [ apply Bool.negb_false_iff, Z.eqb_eq; lia | apply Bool.negb_true_iff, Z.eqb_neq; lia ]
        end
      end
    end.

  (* [comment removed for export] *)
  Lemma afa_main : forall (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word), 1 <= dcap -> 10 <= n ->
    (tl = 11 -> 1 <= dcap -> 10 <= n -> forall mm (x15 x16 x17 : word),
       rw_cells bsegs mm (SP + -40) [C8 s3] -> rw_cells bsegs mm (SP + -32) [C8 s2] -> rw_cells bsegs mm (SP + -24) [C8 s1] ->
       rw_cells bsegs mm (SP + -16) [C8 s0] -> rw_cells bsegs mm (SP + -8) [C8 ra] ->
       rw_cells bsegs mm A [CB 152 ja] -> bytes_at bsegs mm S (map (Z_to_bv 8) src) ->
       stk bsegs mm lo (SP + -40) -> mem_inv bsegs mm -> munch [(SP - 48, SP); (A, A + 152)] m0 mm -> wmono bsegs m0 mm ->
       evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp t0 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880) s0 s1 (Z_to_bv 64 A)
                                  (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 S) (Z_to_bv 64 n) x15 x16 x17
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + dcap)) t4 t5 t6)
                             F (Z_to_bv 64 (AHUF_FAST_ARGS_INIT + 140)) fc None mm (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 S)
                               (Z_to_bv 64 n) (Z_to_bv 64 DT) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 AHUF_FAST_ARGS_INIT) fc None m0 (seg_rom bsegs)).
Proof using All.
  intros t0 t1 t2 a6 a7 t3 t4 t5 t6 DC1 N10 K. pose proof (DPOS ltac:(lia)) as DP1.
  pose proof (afa_sp0 sp lo A LOA LOS ASP A47) as SPB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof ART as (RG0 & RGOT & RGRIC & RMEM & RSHB & _).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AHUF_FAST_ARGS_STACK in *.
  assert (SHD : Z.shiftr DT 3 + 0x7fff8000 + 1 <= SP - 48) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
  assert (WDTS2 : rng RNG (Z.shiftr DT 3 + 0x7fff8000) 1) by (unfold shad, ASHOFF in WDTS; rewrite Z.add_comm; exact WDTS).
  destruct (stk_carve bsegs m0 lo SP 48 STK ltac:(lia)) as (STK48 & junkf & FR48). change (Z.of_nat 48) with 48 in FR48.
  pose proof (SL ltac:(lia)) as SLn.
  destruct (stk_split bsegs m0 lo (SP - 40) SP STK ltac:(lia)) as (STK40 & _).
  destruct (Z.eq_dec tl 11) as [TL|TL].
  - kx_runFm [AHUF_FAST_ARGS_INIT + 140] 300%nat [KZRange dcap 1 (2^32 - 1);
KZRange n 10 (2^26 - 1); KZRange S 1 (2^47);
KZRange DST 1 (2^64 - 9);
KZRange (DST + dcap) 2 (2^64 - 8);
KZRange DT 1 (2^47);
KZAlign DT 8;
KZRange SP 0x7fff7f801030 (2^47-152);
KZWord 0xb2128 8 0xba2f8;
KZWord 0xba2f8 8 0x7fff8000;
KZWr (SP - 48) 48;
KZDisj (SP - 48) 48 0xb2128 8;
KZDisj (SP - 48) 48 0xba2f8 8;
KZDisj (SP - 48) 48 DT 4;
KZDisj (SP - 48) 48 (Z.shiftr DT 3 + 0x7fff8000) 1]
[(DT, 4)]
[(SP - 48, 48); (0xb2128, 8); (0xba2f8, 8); (DT, 4)]
[(DT, 4)].
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- region_ok _ _ _ _ => fail | |- _ =>
      (rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; cbn [cells_size csize]; lia) end).
    all: try (lazymatch goal with |- region_ok ?segs ?mm ?E (zr_reg (?a, ?n)) => let eb := eval unfold E in E in
      lazymatch eb with kx_env (map (Z_to_bv 64) ?zv) ?xs => let s1 := eval vm_compute in (zsa a) in
      lazymatch s1 with SA ?sb ?sc => refine (zr_ok_bytes_at segs zv xs mm a n sb sc DT _ _ _ _ _ _ _ DESC _ _);
        [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | cbv [zden nth]; lia | cbv [zden nth]; lia | cbv [zden nth]; lia
        | cbv [zden nth]; lia | cbv [zden nth]; cbn [length]; lia ] end end end).
    all: try (lazymatch goal with |- branch_taken BC_NE _ _ = _ => afa_tlbr end).
    all: try (lazymatch goal with |- branch_taken BC_LTU _ _ = _ => w4br end).
    apply (rw_cells_split_CB bsegs m0 (SP - 48) [] 48 junkf [] [8;8;8;8;8;8]%nat) in FR48; [| reflexivity]. cbn [app mk_CB_cells] in FR48. kx_cells_split FR48.
    apply (afa_cb8_c8 m0 _ [] []) in KC0. apply (afa_cb8_c8 m0 _ [] []) in KC1. apply (afa_cb8_c8 m0 _ [] []) in KC2.
    apply (afa_cb8_c8 m0 _ [] []) in KC3. apply (afa_cb8_c8 m0 _ [] []) in FR48. cbn [app] in KC0, KC1, KC2, KC3, FR48.
    kx_cell KC0. kx_cell KC1. kx_cell KC2. kx_cell KC3. kx_cell FR48.
    pose proof (munch_refl [(SP - 48, SP); (A, A + 152)] m0) as MU.
    pose proof (wmono_refl bsegs m0) as WM.
    kx_frame HA. kx_frame SRC. kx_munch MU.
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
    lazymatch goal with |- context [mem_denot ?E ?mm ?l] => pose proof (kx_stk_log _ E mm l _ _ STK40) as STKm end.
    kx_post_mem_free.
    lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
    kx_post_regs_keep.
    try clearbody KXE; try clearbody KXxs.
    eapply K.
    all: first [ exact TL | lia | assumption
               | lazymatch goal with |- stk _ _ _ ?a => replace a with (SP - 40) by lia; assumption end
               | lazymatch goal with |- rw_cells _ ?mm ?a [C8 ?v] =>
                   match goal with H : rw_cells _ mm ?b [C8 v] |- _ => replace a with b by lia; exact H end end ].
  - kx_runFmd (@nil Z) 300%nat [false; true] [KZRange dcap 1 (2^32 - 1);
KZRange n 10 (2^26 - 1); KZRange S 1 (2^47);
KZRange DST 1 (2^64 - 9);
KZRange (DST + dcap) 2 (2^64 - 8);
KZRange DT 1 (2^47);
KZAlign DT 8;
KZRange SP 0x7fff7f801030 (2^47-152);
KZWord 0xb2128 8 0xba2f8;
KZWord 0xba2f8 8 0x7fff8000;
KZWr (SP - 48) 48;
KZDisj (SP - 48) 48 0xb2128 8;
KZDisj (SP - 48) 48 0xba2f8 8;
KZDisj (SP - 48) 48 DT 4;
KZDisj (SP - 48) 48 (Z.shiftr DT 3 + 0x7fff8000) 1]
[(DT, 4)]
[(SP - 48, 48); (0xb2128, 8); (0xba2f8, 8); (DT, 4)]
[(DT, 4)].
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- region_ok _ _ _ _ => fail | |- _ =>
      (rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; cbn [cells_size csize]; lia) end).
    all: try (lazymatch goal with |- region_ok ?segs ?mm ?E (zr_reg (?a, ?n)) => let eb := eval unfold E in E in
      lazymatch eb with kx_env (map (Z_to_bv 64) ?zv) ?xs => let s1 := eval vm_compute in (zsa a) in
      lazymatch s1 with SA ?sb ?sc => refine (zr_ok_bytes_at segs zv xs mm a n sb sc DT _ _ _ _ _ _ _ DESC _ _);
        [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | cbv [zden nth]; lia | cbv [zden nth]; lia | cbv [zden nth]; lia
        | cbv [zden nth]; lia | cbv [zden nth]; cbn [length]; lia ] end end end).
    all: try (lazymatch goal with |- branch_taken BC_NE _ _ = _ => afa_tlbr end).
    all: try (lazymatch goal with |- branch_taken BC_LTU _ _ = _ => w4br end).
    apply (rw_cells_split_CB bsegs m0 (SP - 48) [] 48 junkf [] [8;8;8;8;8;8]%nat) in FR48; [| reflexivity]. cbn [app mk_CB_cells] in FR48. kx_cells_split FR48.
    pose proof (munch_refl [(SP - 48, SP); (A, A + 152)] m0) as MU.
    pose proof (wmono_refl bsegs m0) as WM.
    try kx_cell KC. try kx_cell KC0. try kx_cell KC1. try kx_cell KC2. try kx_cell KC3. try kx_cell FR48.
    kx_frame KC. kx_frame HA. kx_munch MU.
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (rewrite ?length_map; cbn [cells_size csize]; lia) end).
    kx_post_mem_free.
    lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
    kx_post_regs_keep.
    zstep.
    try clearbody KXE; try clearbody KXxs.
    apply evtF_done. unfold fast_args_postA.
    do 14 eexists. exists 0, m1. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI0|].
    split; [first [exact STK | exact STK48]|].
    split; [exists ja; exact HA|]. left; reflexivity.
Qed.
End AFA.
End CANSEC1.
