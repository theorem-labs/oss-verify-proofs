(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT FseReadSound.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AFake0k_iface AF_fse_rd_iface
     AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_loop AF_fse_rd_hdr AF_fse_rd_seg AF_fse_rd_asm AF_fse_rd_err AF_fse_rd_err2 AF_fse_rd_err3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_fse_rd () := "C46Stdlib5Lists4List2hdC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2InC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface9fake0_lekC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit4u16sK47Corelib4Init9Datatypes4list01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02I47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface4bufAC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface6nhullAC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface6fcellAC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5nshadC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface?fse_readr_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm:spa_props2C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_seg4SPAzK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_aci_imgI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_aci_loC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr01C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_seg4RFRBK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_seg6RFFHDRC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic6eq_symK5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base6rdctxA01C5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base5a_SPAC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm:bufA_blockC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_subC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm9cl_shadowC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base5a_bufC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base6a_msv0C5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4a_SPC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4a_loC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4a_NCC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base6a_MSVPC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base5a_TLPC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base5a_BUFC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4a_FFK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base6rd_okAC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm7bufA_mgK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm9bufA_monoC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm?bufA_unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm9fcellA_mgC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base3a_mC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base6rd_shAC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base7rd_rngAC47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3mulC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm>cl_range_blockC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit;u16s_lengthC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm8u8arr_mgC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?rw_cells_magreeC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?bytes_at_magreeC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface6shullAI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm9shullA_mgC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>chunk_user_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=ablock_shadowC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm;block_hullRC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm8hull_loRC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm8hull_hiRC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_rtcellsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8artcellsK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm8blk_sepFC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm8frame_WAC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base5rd_WAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base5a_rt0K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeK47Corelib4Init5Logic2or01K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm3PAGC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree;magree_monoC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm@stack_not_clientC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asmAmagree_munch_stepC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas@Forall_all_bytesC5ARocqVerifyHarness?AgentSubmission4Spec<FseReadSoundGread_ncount_body8_totalI5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountAread_ncount_body8C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02C5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_loop=rd_mainA_postC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_hdr8rd_mainAC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base7rd_lstAC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base7rd_invAC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=stk_transportC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm<rffhdr_splitC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4a_gpC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4a_tpC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface>fse_read_postAC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base8FRA_mainC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm8rd_closeC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface;readr_of_okC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_monoC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8evtF_cutC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_errBread_body8_err_invC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit4le32C56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission6Common9FseRdKit25rd_s0K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount9r_charnumC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_err@rd_mainA_errpostC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_err2<rd_mainA_errC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base3a_FC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4a_fcC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_err:rd_errinvAC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface<readr_of_errC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm7rd_openC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC35stdpp4base6lookupC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4wsumC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5rloopC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount;r_remainingC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount:r_bitCountI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_seg5RFFSHK46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base:RDA_CALLEEI47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KENDK47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm9RD8_STACKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface<AFSE_RD_BODYK47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base6rdctxA00I47Corelib4Init5Logic5False00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableK47Corelib4Init5Logic4True01I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount6rstate00c5ARocqVerifyHarness?AgentSubmission5BothW9AF_fse_rd>rd_body8A_stmtC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm;shullA_monoC47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res04C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount;read_ncountC47Corelib5Lists7ListDef6repeatC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountNZSTD_error_corruption_detectedC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface4bufHC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List=repeat_lengthC46Stdlib5Lists4List:length_appC46Stdlib5Lists4List:Forall_appC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List;repeat_specC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface>fake0_lek_monoC56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asmBablock_unpoisonedRC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow>unpoisoned_subC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablk_app_blkC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm>app_not_clientC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asmAshadow_not_clientC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm=rffhdr5_splitC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC46Stdlib5Lists4List9app_nil_rC5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface?fake0_lek_push0C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm;fcellA_monoc5ARocqVerifyHarness?AgentSubmission5BothW9AF_fse_rd9nhullA_mgc5ARocqVerifyHarness?AgentSubmission5BothW9AF_fse_rd;nhullA_monoC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm<rffsh0_byte4C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm?c1z_unpoisonedRC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface=fse_read_resAC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm;pag_shadowRC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm9aca_monoAC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree<magree_transC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm:pag_blockRC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm:pag_stackRC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm=app_vs_shadowc5ARocqVerifyHarness?AgentSubmission5BothW9AF_fse_rd8zsize_c8K46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree:stk_magreeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u8arr_transportc5ARocqVerifyHarness?AgentSubmission5BothW9AF_fse_rd8zsize_c4C5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_err39small_resC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_err3:rd_small2GC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface=readr_of_err2C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_seg9rd_small1c5ARocqVerifyHarness?AgentSubmission5BothW9AF_fse_rdAread_ncount_smallK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_leC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_seg6RFFSH0C5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface@FSE_READ_STACK_AI46Stdlib5Lists4List6Exists00c5ARocqVerifyHarness?AgentSubmission5BothW9AF_fse_rd9rd_body8AC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00c5ARocqVerifyHarness?AgentSubmission5BothW9AF_fse_rd9rd_smallAC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface<bufA_of_bufHC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface?fse_readk_postAC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface?fse_readk_stmtAI5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<AMallocIface00C5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface=fake_flag_lawC5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface@fake_release_lawC5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_ifaceDstack_malloc_0k_stmtc5ARocqVerifyHarness?AgentSubmission5BothW9AF_fse_rd@fse_readk_proofA".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac boxH H := lazymatch type of H with ?T => change T with (bx T) in H end.
Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

Section CANSEC1. Context {rc : runConstT}.

Lemma zsize_c8 : forall c, Z.of_nat (cells_size [C8 c]) = 8.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_fse_rd ()) ["CANSEC1"] "h01cp;1p;2p-1p10000p4p710p8p1000Gp4p710p1000dp4p710p8g001@j10Tg001ej14Tg002Cj12Tg002fj11Tg003Dj23Tg003^#0#0#0R0#0#0#0#4#2g004C%10'3W0o"). Qed.
Lemma zsize_c4 : forall c, Z.of_nat (cells_size [C4 c]) = 4.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_fse_rd ()) ["CANSEC1"] "h01cp;1p;2g001@j10Tg001ej14Tg002Cj12Tg002fj11Tg003Dj23Tg003^#0#0R0#0#0#0#0#4#2g004C%10'3W0o"). Qed.

Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : fake_flag_law AI fflag.
Hypothesis FREL : fake_release_law AI fflag.
Variable kk : nat.
Hypothesis SM0K : stack_malloc_0k_stmt AI fflag rng_fs kk.
Notation FB0 F := (mkABlock (ABFake 0) F 64).

(* [comment removed for export] *)
Definition rd_body8A_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
         (SPV NC MSVP TLP BUF : Z) (rt0 buf : list Z) (msv0 lo : Z) (tl0 : word),
  AHEAP AI L RNG st LB m -> fake0_lek kk LB ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  u8arr bsegs m NC (u16s (map (Z_to_bv 64) rt0)) ->
  rw_cells bsegs m MSVP [C4 (Z_to_bv 64 msv0)] -> rw_cells bsegs m TLP [C4 tl0] ->
  bytes_at bsegs m BUF (map (Z_to_bv 8) buf) -> Forall (fun c => 0 <= c < 256) buf ->
  0 <= msv0 <= 255 -> msv0 + 1 <= zlen rt0 -> 8 <= zlen buf <= 65536 -> zlen rt0 <= 65536 ->
  bufA m LB NC (2 * zlen rt0) -> NC mod 8 = 0 -> nhullA RNG m LB NC (2 * zlen rt0) ->
  fcellA m LB MSVP 4 -> MSVP mod 4 = 0 -> fcellA m LB TLP 4 -> TLP mod 4 = 0 ->
  bufA m LB BUF (zlen buf) -> ablk BUF (BUF + zlen buf) ->
  (NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC) -> (NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC) ->
  (NC + 2 * zlen rt0 <= BUF \/ BUF + zlen buf <= NC) ->
  (MSVP + 4 <= TLP \/ TLP + 4 <= MSVP) ->
  (MSVP + 4 <= BUF \/ BUF + zlen buf <= MSVP) -> (TLP + 4 <= BUF \/ BUF + zlen buf <= TLP) ->
  stk bsegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - RD8_STACK ->
  SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  rng RNG NC (2 * zlen rt0) -> rng RNG (shad NC) (nshad (2 * zlen rt0)) ->
  rng RNG MSVP 4 -> rng RNG (shad MSVP) 1 -> rng RNG TLP 4 -> rng RNG (shad TLP) 1 ->
  rng RNG BUF (zlen buf) -> rng RNG (shad BUF) (nshad (zlen buf + BUF mod 8)) ->
  evtF bsegs RNG (fse_readr_postA AI L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB SPV NC MSVP TLP rt0
                    (read_ncount_body8 buf (msv0 + 1) rt0) lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
                (Z_to_bv 64 (zlen buf)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AFSE_RD_BODY) fc None m (seg_rom bsegs)).

Theorem rd_body8A : rd_body8A_stmt.
Proof.
unfold rd_body8A_stmt.
intros L RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB SPV NC MSVP TLP BUF rt0 buf
msv0 lo tl0
AH LE1 LBH ARR HMSV HTL HBUF FBY HM0 HM1 H8 HRT BFN N8 HULL FCM M4 FCT T4 BFA BBK SNM SNT SNB SMT SMB STB ST BOT LO SPT SP16 MI TP
RSTK RI RFS RN RNS RM RMS RT RTS RBf RBS.
pose proof atop_range as ATR.
pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
unfold RD8_STACK, SM0R_STACK in LO.
pose proof (spa_props2 SPV SP16) as (SPAB & SPA32).
assert (AR1 : ATOP <= SPAz SPV - 2224) by (clear - LO BOT SPAB; lia).
assert (AR2 : SPAz SPV + 192 <= SPV) by (clear - SPAB; lia).
assert (AR3 : ATOP + 4096 <= SPAz SPV - 2224) by (clear - LO BOT SPAB; lia).
assert (AR4 : SPAz SPV + 88 <= 2^47) by (clear - SPAB SPT LY3; lia).
assert (LOA : lo <= SPAz SPV - 2224) by (clear - LO SPAB; lia).
assert (SPK : SPV + 16 < KEND) by (clear - SPT LY3; unfold KEND; lia).
assert (LOC : ATOP <= lo) by (clear - BOT; lia).
assert (LO' : lo <= SPV - RD8_STACK) by (unfold RD8_STACK, SM0R_STACK; clear - LO; lia).
pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
lazymatch goal with |- evtF _ _ ?P _ =>
eapply evtF_cut; [eapply (rd_open AI fflag rng_fs kk SM0K L RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
FR fc m st LB SPV NC MSVP TLP BUF (zlen buf) lo (evtF bsegs RNG P));
[first [assumption| lia] .. | ]
| intros ms' Hms; exact Hms ] end.
intros FF m3 k0 k8 k16 k32 k40 k48 k64 junk x5 x6 x7 y10 y11 y12 x14 x15 x16 x17 x28 x29 x30 x31
F64 FH FC RFF RSFF FFD AH3 MG3 MI3 FRB3 FRA3 FFC3 SHF3 STL3 STG3.
replace (7 <? zlen buf) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
set (C := mkRDA gp tp FR fc m3 SPV FF NC MSVP TLP BUF lo rt0 buf msv0).
assert (ESPA : a_SPA C = SPAz SPV) by reflexivity.
assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
by (clear - FH; apply ablk_lin in FH; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
boxH SNM. boxH SNT. boxH SNB. boxH SMT. boxH SMB. boxH STB.
destruct (bufA_block m LB NC (2 * zlen rt0) BFN) as (bN & HbN & N1 & N2).
pose proof FCM as [(cM & FAM & FNM & HbM & M1 & M2 & M3 & M5) _].
pose proof FCT as [(cT & FAT & FNT & HbT & T1 & T2 & T3 & T5) _].
destruct (bufA_block m LB BUF (zlen buf) BFA) as (bB & HbB & B1 & B2).
assert (ABN : ablk NC (NC + 2 * zlen rt0)) by (eapply ablk_sub; [exact (LBH _ HbN)| lia| lia]).
assert (ABM : ablk MSVP (MSVP + 4)) by (eapply ablk_sub; [exact M3| lia| lia]).
assert (ABT : ablk TLP (TLP + 4)) by (eapply ablk_sub; [exact T3| lia| lia]).
assert (HPs : forall a', in_fake LB a' -> aclient_addr CI LB SPV (shad a')) by (intros a' Ha'; apply cl_shadow; right; right; exact Ha').
pose proof H8 as [H8a H8b]. pose proof HM0 as [HM0a HM0b].
assert (OKC : rd_okA C).
{ unfold rd_okA. rewrite ESPA. unfold C; cbn [a_buf a_msv0 a_rt0 a_SP a_lo a_NC a_MSVP a_TLP a_BUF a_FF]. unfold RDA_CALLEE.
repeat split; first [assumption | (pose proof (ablk_lin _ _ BBK); unfold AIMG_HI in *; lia)]. }
assert (SHC : rd_shA C).
{ unfold rd_shA, C; cbn [a_m a_NC a_rt0 a_MSVP a_TLP a_BUF a_buf].
split; [eapply (bufA_unpoisoned AI L RNG st (FB0 FF :: LB) m3); [exact AH3| | lia];
eapply bufA_mono; [eapply bufA_mg; [exact MG3| exact HPs| exact BFN]| intros b Hb; right; exact Hb]|].
split; [exact (proj2 (fcellA_mg _ _ _ _ _ _ MG3 HPs FCM))|].
split; [exact (proj2 (fcellA_mg _ _ _ _ _ _ MG3 HPs FCT))|].
eapply (bufA_unpoisoned AI L RNG st (FB0 FF :: LB) m3); [exact AH3| | lia].
eapply bufA_mono; [eapply bufA_mg; [exact MG3| exact HPs| exact BFA]| intros b Hb; right; exact Hb]. }
assert (RNGC : rd_rngA C RNG).
{ unfold rd_rngA, C; cbn [a_lo a_SP a_NC a_rt0 a_MSVP a_TLP a_BUF a_buf].
split; [assumption|]. split; [eapply rng_sub'; [exact RSTK| clear - SPT; lia]|]. repeat (split; [assumption|]). assumption. }
assert (ARR3 : u8arr bsegs m3 NC (u16s (map (Z_to_bv 64) rt0))).
{ eapply u8arr_mg; [exact MG3| exact ARR|]. rewrite u16s_length, length_map.
intros a Ha. apply (cl_range_block CI LB SPV _ NC (2 * zlen rt0) HbN); [exact N1| exact N2| clear - Ha; lia]. }
assert (HMSV3 : rw_cells bsegs m3 MSVP [C4 (Z_to_bv 64 msv0)]).
{ eapply rw_cells_magree; [exact MG3| exact HMSV|]. cbn [cells_size csize Nat.add].
intros a Ha. apply (cl_range_block CI LB SPV _ MSVP 4 HbM); cbn [ab_addr ab_size]; [exact M1| exact M2| clear - Ha; lia]. }
assert (HTL3 : rw_cells bsegs m3 TLP [C4 tl0]).
{ eapply rw_cells_magree; [exact MG3| exact HTL|]. cbn [cells_size csize Nat.add].
intros a Ha. apply (cl_range_block CI LB SPV _ TLP 4 HbT); cbn [ab_addr ab_size]; [exact T1| exact T2| clear - Ha; lia]. }
assert (HBUF3 : bytes_at bsegs m3 BUF (map (Z_to_bv 8) buf)).
{ eapply bytes_at_magree; [exact MG3| exact HBUF|]. rewrite length_map.
intros a Ha. apply (cl_range_block CI LB SPV _ BUF (zlen buf) HbB); [exact B1| exact B2| clear - Ha; lia]. }
assert (HHX : exists RLO RHI, (RLO <= NC /\ NC + 2 * zlen rt0 <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)
/\ wr_at bsegs m3 (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO)).
{ destruct HULL as [HULL | (p & B0 & N0 & HbP & P1 & P2)].
- pose proof (shullA_mg _ _ _ _ _ _ _ MG3 HPs HULL) as (hc & HFA & HFN & HbH & H1 & H2 & H3 & H4 & H5 & H6 & HW & HR).
assert (EH : shad (HFA + HFN) - shad HFA = HFN / 8) by (clear - H3 H4; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
assert (HH : HFA <= NC /\ NC + 2 * zlen rt0 <= HFA + HFN /\ HFA mod 64 = 0 /\ (HFA + HFN) mod 64 = 0 /\ 0 <= HFA /\ HFA + HFN <= KEND).
{ split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [clear - H3 H4; Z.div_mod_to_equations; lia|]. split; [exact H5| exact H6]. }
exists HFA, (HFA + HFN). split; [exact HH|]. rewrite EH. split; assumption.
- destruct (AI_block AI L RNG st (FB0 FF :: LB) m3 p B0 N0 AH3 (in_cons _ _ _ HbP))
as (_ & _ & _ & _ & _ & _ & _ & RLO & RHI & RL1 & RH1 & RL2 & RH2 & RRS & RWS).
pose proof (AI_block_bounds AI L RNG st (FB0 FF :: LB) m3 _ AH3 (in_cons _ _ _ HbP)) as (BB1 & BB2 & BB3).
cbn [ab_addr ab_size] in BB1, BB2, BB3.
destruct (block_hullR RNG m3 NC (2 * zlen rt0) RLO RHI ltac:(lia) RL1 RH1 ltac:(lia) ltac:(lia) ltac:(unfold AIMG_HI in *; lia) RRS RWS)
as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
exists (hull_loR NC), (hull_hiR NC (2 * zlen rt0)).
split; [| split; assumption]. repeat split; try assumption. unfold KEND in *. lia. }
destruct HHX as (RLO & RHI & HH & HW & HR).
pose proof (AI_rtcells AI _ _ _ _ _ AH3) as RTC. unfold artcells in RTC.
destruct RTC as (C0 & GOT & RIC & REAL & SHB & SUA & INI & LAY & _).
destruct (read_ncount_body8_total buf (msv0 + 1) rt0 (buf_all_bytesA C OKC) ltac:(unfold FseNCount.Zlength; lia)
ltac:(unfold FseNCount.Zlength; lia)) as [(rt & msv & tl & n & RB & _) | (e & RB)]; rewrite RB.
2: {
eapply evtF_cut.
{ eapply (rd_mainA_err C RNG OKC SHC RNGC e tl0 k0 k8 k16 k32 k40 k48 k64 RLO RHI);
first [exact ARR3| exact HMSV3| exact HTL3| exact HBUF3| exact FRA3| exact STL3| exact MI3| exact GOT| exact RIC| exact SHB
| exact INI| exact LAY| exact REAL| exact RB| exact HH| exact HW| exact HR]. }
assert (E120 : 0 < e < 120).
{ destruct (read_body8_err_inv buf (msv0 + 1) rt0 e (buf_all_bytesA C OKC) ltac:(unfold FseNCount.Zlength; lia)
ltac:(unfold FseNCount.Zlength; lia) RB) as [(_ & ->) | (_ & sF & _ & [(_ & ->) | [(_ & _ & ->) | (_ & _ & _ & ->)]])]; lia. }
cbv beta. intros ms' (m4 & z1 & z5 & z6 & z7 & z10 & z11 & z13 & z14 & z15 & z16 & z17 & z18 & z19 & z20 & z21 & z22 & z23 & z24
& z27 & z28 & z29 & z30 & z31 & -> & EINV).
destruct EINV as ((nc4 & ARR4 & LNC4) & (msvw & HMSV4) & (tlw & HTL4) & (q0 & q32 & FRM4) & STL4 & MU4 & WM4 & MI4).
clear C0 GOT RIC REAL SHB SUA INI LAY.
assert (AH4 : AHEAP AI L RNG st (FB0 FF :: LB) m4).
{ eapply (AI_frame AI); [exact AH3| exact MU4| exact WM4|]. unfold rd_WA. rewrite ESPA. unfold C; cbn [a_NC a_rt0 a_MSVP a_TLP].
constructor; [cbn; right; left; exists bN; split; [right; exact HbN| cbn; clear - N1 N2; lia]|].
constructor; [cbn; right; left; exists (mkABlock (ABFake cM) FAM FNM); split; [right; exact HbM| cbn; clear - M1 M2; lia]|].
constructor; [cbn; right; left; exists (mkABlock (ABFake cT) FAT FNT); split; [right; exact HbT| cbn; clear - T1 T2; lia]|].
constructor; [cbn; left; left; unfold RDA_CALLEE; clear - AR3 AR4; lia| constructor]. }
assert (MG4 : magree bsegs (PAG AI LB SPV NC MSVP TLP rt0) m m4).
{ eapply magree_munch_step; [eapply magree_mono; [exact MG3| intros a HP; destruct HP as (Ha & _); exact Ha]| exact MU4| exact WM4|].
intros a HP. destruct HP as (Ha & HN & HM & HT). unfold rd_WA. rewrite ESPA. unfold C; cbn [a_NC a_rt0 a_MSVP a_TLP outside].
unfold RDA_CALLEE.
split; [exact HN|]. split; [exact HM|]. split; [exact HT|]. split; [| exact I].
intros Hr. exact (stack_not_client CI LB SPV (SPAz SPV - 2224) a HCI HCI0 LBH AR1 ltac:(clear - Hr AR2; lia) Ha). }
destruct (frame_WA C FF ABN (blk_sepF FF NC (2 * zlen rt0) (ab_addr bN) (ab_size bN) N1 N2 (FFD _ HbN))
ABM (blk_sepF FF MSVP 4 FAM FNM M1 M2 (FFD _ HbM))
ABT (blk_sepF FF TLP 4 FAT FNT T1 T2 (FFD _ HbT))
FH (proj1 BSF) (proj2 BSF) ltac:(rewrite ESPA; unfold RDA_CALLEE; exact AR1) ltac:(rewrite ESPA; cbn [a_SP C]; exact AR2))
as (DS & DF & DR & DG).
pose proof (rw_cells_transport _ _ _ _ _ _ SHF3 MU4 WM4 DS) as SHF4.
pose proof (rw_cells_transport _ _ _ _ _ _ FFC3 MU4 WM4 DF) as FFC4.
pose proof (rw_cells_transport _ _ _ _ _ _ FRB3 MU4 WM4 DR) as FRB4.
assert (STG4 : stk bsegs m4 (SPAz SPV + 88) (SPV + -104))
by (eapply stk_transport; [exact STG3| exact MU4| exact WM4| intros x Hx; left; apply DG; rewrite ESPA; exact Hx]).
destruct (rffhdr_split m4 FF (fflag L 0 FF) junk FFC4) as [FF04 FF564].
rewrite ESPA in FRM4 |- *. unfold C in FRM4 |- *; cbn [a_gp a_tp a_F a_fc a_SP a_FF a_NC a_MSVP a_TLP a_BUF a_lo a_rt0 a_buf a_msv0] in FRM4 |- *.
rewrite <- (Z_to_bv_bv_unsigned msvw) in HMSV4. rewrite <- (Z_to_bv_bv_unsigned tlw) in HTL4.
eapply (evtF_mono _ _ (fse_read_postA AI L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB SPV NC MSVP TLP rt0
nc4 (bv_unsigned msvw) (bv_unsigned tlw) (- e) lo m));
[| intros ms' Hp; eapply readr_of_err; [exact Hp| exact E120| exact LNC4]].
eapply (rd_close AI fflag FFLAG FREL L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m4 st LB SPV NC MSVP TLP lo FF rt0 nc4 (bv_unsigned msvw) (bv_unsigned tlw) (- e)
(Z_to_bv 64 0x41b58ab3));
first [exact AH4| exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact MG4| exact MI4| exact SHF4
| exact FF04| exact FF564| exact FRB4| exact FRM4| reflexivity| exact STL4| exact STG4| exact BOT| exact RSTK| exact ARR4
| exact HMSV4| exact HTL4| exact LNC4| exact BFN| exact FCM| exact FCT| exact SP16| exact LO'| exact SPT].
}
eapply (evtF_mono _ _ (fse_read_postA AI L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB SPV NC MSVP TLP rt0 rt msv tl n lo m));
[| intros ms' Hp; apply readr_of_ok; exact Hp].
eapply evtF_cut.
{ eapply (rd_mainA C RNG OKC SHC RNGC rt msv tl n tl0 k0 k8 k16 k32 k40 k48 k64 RLO RHI);
first [exact ARR3| exact HMSV3| exact HTL3| exact HBUF3| exact FRA3| exact STL3| exact MI3| exact GOT| exact RIC| exact SHB
| exact INI| exact LAY| exact REAL| exact RB| exact HH| exact HW| exact HR]. }
cbv beta. intros ms' (m4 & z1 & z6 & z7 & z10 & z11 & z13 & z14 & z15 & z16 & z17 & z18 & z20 & z22 & z29 & -> & INV).
destruct INV as (ARR4 & LNC4 & HBUF4 & HMSV4 & HTL4 & (j0 & j64 & FRM4) & STL4 & MU4 & WM4 & MI4).
clear C0 GOT RIC REAL SHB SUA INI LAY.
assert (AH4 : AHEAP AI L RNG st (FB0 FF :: LB) m4).
{ eapply (AI_frame AI); [exact AH3| exact MU4| exact WM4|]. unfold rd_WA. rewrite ESPA. unfold C; cbn [a_NC a_rt0 a_MSVP a_TLP].
constructor; [cbn; right; left; exists bN; split; [right; exact HbN| cbn; clear - N1 N2; lia]|].
constructor; [cbn; right; left; exists (mkABlock (ABFake cM) FAM FNM); split; [right; exact HbM| cbn; clear - M1 M2; lia]|].
constructor; [cbn; right; left; exists (mkABlock (ABFake cT) FAT FNT); split; [right; exact HbT| cbn; clear - T1 T2; lia]|].
constructor; [cbn; left; left; unfold RDA_CALLEE; clear - AR3 AR4; lia| constructor]. }
assert (MG4 : magree bsegs (PAG AI LB SPV NC MSVP TLP rt0) m m4).
{ eapply magree_munch_step; [eapply magree_mono; [exact MG3| intros a HP; destruct HP as (Ha & _); exact Ha]| exact MU4| exact WM4|].
intros a HP. destruct HP as (Ha & HN & HM & HT). unfold rd_WA. rewrite ESPA. unfold C; cbn [a_NC a_rt0 a_MSVP a_TLP outside].
unfold RDA_CALLEE.
split; [exact HN|]. split; [exact HM|]. split; [exact HT|]. split; [| exact I].
intros Hr. exact (stack_not_client CI LB SPV (SPAz SPV - 2224) a HCI HCI0 LBH AR1 ltac:(clear - Hr AR2; lia) Ha). }
destruct (frame_WA C FF ABN (blk_sepF FF NC (2 * zlen rt0) (ab_addr bN) (ab_size bN) N1 N2 (FFD _ HbN))
ABM (blk_sepF FF MSVP 4 FAM FNM M1 M2 (FFD _ HbM))
ABT (blk_sepF FF TLP 4 FAT FNT T1 T2 (FFD _ HbT))
FH (proj1 BSF) (proj2 BSF) ltac:(rewrite ESPA; unfold RDA_CALLEE; exact AR1) ltac:(rewrite ESPA; cbn [a_SP C]; exact AR2))
as (DS & DF & DR & DG).
pose proof (rw_cells_transport _ _ _ _ _ _ SHF3 MU4 WM4 DS) as SHF4.
pose proof (rw_cells_transport _ _ _ _ _ _ FFC3 MU4 WM4 DF) as FFC4.
pose proof (rw_cells_transport _ _ _ _ _ _ FRB3 MU4 WM4 DR) as FRB4.
assert (STG4 : stk bsegs m4 (SPAz SPV + 88) (SPV + -104))
by (eapply stk_transport; [exact STG3| exact MU4| exact WM4| intros x Hx; left; apply DG; rewrite ESPA; exact Hx]).
destruct (rffhdr_split m4 FF (fflag L 0 FF) junk FFC4) as [FF04 FF564].
unfold FRA_main in FRM4.
change [CB 8 j0; C8 (Z_to_bv 64 (a_BUF C + zlen (a_buf C) + -4)); C8 (Z_to_bv 64 (Z.shiftr (a_MSVP C) 3 + ASHB)); C8 (Z_to_bv 64 (a_FF C));
C8 (Z_to_bv 64 16843009); C8 (Z_to_bv 64 252645135); C8 (Z_to_bv 64 1431655765); C8 (Z_to_bv 64 (a_MSVP C)); CB 16 j64; C8 (Z_to_bv 64 (a_FF C))]
with ([CB 8 j0; C8 (Z_to_bv 64 (a_BUF C + zlen (a_buf C) + -4)); C8 (Z_to_bv 64 (Z.shiftr (a_MSVP C) 3 + ASHB)); C8 (Z_to_bv 64 (a_FF C))]
++ [C8 (Z_to_bv 64 16843009); C8 (Z_to_bv 64 252645135); C8 (Z_to_bv 64 1431655765); C8 (Z_to_bv 64 (a_MSVP C)); CB 16 j64; C8 (Z_to_bv 64 (a_FF C))]
++ []) in FRM4.
apply rw_cells_merge in FRM4.
lazymatch type of FRM4 with rw_cells ?sg ?mm ?AA (?l ++ ?x) =>
change (rw_cells sg mm AA ([] ++ [CB 8 j0; C8 (Z_to_bv 64 (a_BUF C + zlen (a_buf C) + -4)); C8 (Z_to_bv 64 (Z.shiftr (a_MSVP C) 3 + ASHB))]
++ (C8 (Z_to_bv 64 (a_FF C)) :: x))) in FRM4 end.
apply rw_cells_merge in FRM4. cbn [app cells_size csize Nat.add] in FRM4.
unfold rd_epiA. rewrite ESPA in FRM4 |- *. unfold C in FRM4 |- *; cbn [a_gp a_tp a_F a_fc a_SP a_FF a_NC a_MSVP a_TLP a_BUF a_lo a_rt0 a_buf a_msv0] in FRM4 |- *.
eapply (rd_close AI fflag FFLAG FREL L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m4 st LB SPV NC MSVP TLP lo FF rt0 rt msv tl n
(Z_to_bv 64 0x41b58ab3));
first [exact AH4| exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact MG4| exact MI4| exact SHF4
| exact FF04| exact FF564| exact FRB4| exact FRM4| reflexivity| exact STL4| exact STG4| exact BOT| exact RSTK| exact ARR4
| exact HMSV4| exact HTL4| exact LNC4| exact BFN| exact FCM| exact FCT| exact SP16| exact LO'| exact SPT].
Qed.


Lemma nhullA_mg : forall (P : Z -> Prop) RNG m m' LB A n, magree bsegs P m m' -> (forall a', in_fake LB a' -> P (shad a')) ->
  nhullA RNG m LB A n -> nhullA RNG m' LB A n.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_fse_rd ()) ["CANSEC1"; "Asm"] "h01Bh11Nh21ph31Hh41Ah52H0h62HPh72LBh82MGh91Ph:3RNGh;2a'h<1mh=2m'h>1np;1p;4p;2p;5p;3p;:g001@j12Tg001ej1:Tg002Cj19Tg007^j1=Tg008@j1DTg00d_j4CTg019=j2?Tg00aij1>Tg00A_j58Tg01Z=j57Tg032@j1<Tg01H5j3;Tg005Xj36Tg00?dj23Tg00Caj25Tg00Iij20Tg01[>j24Tg01[Xl:BTg024Sj3@Tg01;Ij3ATg004CR0f0R1'4p=1p-0\0g03ODg003^#2#2#2R2#2#2#2#:#9%:2#9#=[R2g03=JR3#Dg03>Cf6R4f4R5f3R6CC1?51f9R7f1R8#>O1[^;0f7R9P4P5P6f2R:D8g01:of8R;P9f5R<P5P6D7g004aR=%<:?;81R:=63;138915941581R>'3'0'0X10#1X00#1X2='4P7P9P4P<P5D8P1P7P;P4P<P5D7f:R?P;P9P4P<D7R@A63:?1387157;/3>'0'0X10#1X00#1X2=,4=RAf;P?P7P;P9P4P<P5P6P1M:B3@W3P1O1A63:7138;15;9/3>'0'0X10#1X00#1X2=,4=AA@A1W3P1O1n200100000021000010000W5W6W8X>0X40W7X=2W<W:W9o"). Qed.
Lemma nhullA_mono : forall RNG m LB LB' A n, nhullA RNG m LB A n -> (forall b, In b LB -> In b LB') -> nhullA RNG m LB' A n.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_fse_rd ()) ["CANSEC1"; "Asm"] "p'0h01Nh11Bh21bh31Hh41ph53INCh61Ah72H0h82H1h92H2h:2Hbh;2LBh<3LB'h=3RNGh>1mh?1ni001xp;1p;5p;2p;8p;3p;4g001@j19Tg001ej1FTg002Cj1@Tg007^j1GTg008@j1KTg00A_j57Tg01Z=j5<Tg00Caj26Tg01[>R0j2;Tg00?dj22Tg03]Kj8JTg024Sj3ITg032@j1>Tg00IiR1j2:Tg01EZj4ATg01]Sj4=Tg01;Ij3HTg01H5j3DTg005Xj3?Tf2R2#>f1R3f0R43Dp=51623/24p=4g03=JR5f4R6f3R73?1223/:4':p=3g004CR8/;4p=1A?534p=01:34,:2p=E16721634'2p=8AD723=?54p=C12671623/24':p=Bg03ODg003^#9#9#9R9#9#9#9#F#@%F9#@#G[%K5R9f5R:P6P7P3P4D7g01:of6R;P:P6P2P3D<g004aR<A5234R=f7R>P3P:1634R?94:6D3X08#1X18#1X4<';104;103;[^25f8R@P>P:P6P7D7[P4P>P;P:P7P2D<104>103>[^25f9RAP@P;P:P6D<10=ARB123@A4@>?3EX08#1X18#1X4<,;<PAP@P>P;P:P6P3P4GJ3IW5W3P4O1P=P@P3P;A4;:?D3X08#1X18#1X4<,;<P0P<123>A4>;?5EBX08#1X18#1X4<104@103@[^25f:RBPAP>P;P:D7[P4P=f;RCP3PAA4A@?D3X08#1X18#1P0P8A5734f<RDP3PBA4BA?D3X08#1X18104D103D[^25f>REf=RFPCPBPAD7[P4A5:34PEP3PDA4DC?D3X08#1P0P8A5;24f?R0P2PFPFPDP2P4C8D3X08f@RG,04103G[^25fBRHfARIP0PEPFD7[P4A5@64PIP6P0P0PEP6P4C8D3P1%>AP:P3PHCCP:PGPGP016:3DBfDRG,04103G[^25fFRFfERJfCRKPHPID7[P4%>CP>P7PGCCP@PKPKPH16@6DBP112AGPGPKPAP:C8fHR:,04103:[^25fJRAfIR1fGR6PFPJD7[P412CFP6PFPDP@C8fKR@,04103@[^25fMR5fLRDPAP1P:D<P=P5P3PDA4D@?D3X08#1X18#1X4<R5,;<P<P5PHP8A5G34PDP3P@A4@A?D3X08#1X18PEP8A5K04P@P0PAPAP1P0P4C8D3X08PBA5HEBRH/0A12E1RAP1P:PEPBC8RB':P4PHP;O2PAPBP2P3CACAC=C=C=3HW5W9W8P3P4O2n2001000000120000000W3W:P3P4O2n2001000000121000000W3X08P3P4O2n2001000000121100000W3X18P3P4O2n2001000000121100000W3X4<P3P4O2n2001000000121100000W3P4O1n200100000021000011000W7X?8X68X<9W;W>W=o"). Qed.


Lemma read_ncount_small : forall rt0 msv0 buf, zlen buf < 8 ->
  read_ncount rt0 msv0 buf =
  match read_ncount_body8 (buf ++ repeat 0 (Z.to_nat (8 - zlen buf))) (msv0 + 1) rt0 with
  | Ok (nc, msv, tl, cs) => if zlen buf <? cs then Err ZSTD_error_corruption_detected else Ok (nc, msv, tl, cs)
  | Err e => Err e
  | Ub => Ub
  | NoFuel => NoFuel
  end.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_fse_rd ()) ["CANSEC1"; "Asm"] "p'0h01ri001rh11zi011zh21pi021ph32H0h44__x1h51mh61nh71Hh87__arithh94__ffh:8__varmaph;5__with<1bh=3bufh>2csi032csh?4cstrh@3msvi043msvhA4msv0hB2nci052nchC3rt0hD2tli062tli079countSizei081ei091li0:2p0i0;2p1i0<1xp;1p;2p;4p;7p;8p;3p;6g008@j1GTg001@j1BTg002fj1DTg00iFj28Tg00hij21Tg00ibj2RTg00@@j1@Tg00^dj1JTg00?dj2ITg00=nj1HTg02hij2aTg00Uaj1_Tg00V?j1[Tg00Vjj2YTg00aFj2WTg02jlj4VTg02kWj7UTg00Onj1TTg02mBj8STg00WMj2QTg003Dj27Tg00Woj2PTg00X[j3NTg00Y:j4MTg00jBj4LTg00Ekj32Tg00[RR0j2?Tg02=QR1j1KTg00FEj2;Tg00LZj1:Tg03^Oj3>Tg00Caj2ATg02>Jj36Tg02@Gj2ETg02TWj25Tg03^lj44Tg03_dj1`Tg03`]j1^Tg000dj6]Tg038Bj2FTg03aVj3ZTg01PKj2CTg03bUj3\Tg037bj4XTg004CR2f0R3'C#@p=9g03EAR4g03EaR5723p==1C23p=Og03?mR6=\23p=<f1R7,C2#@/13p=3f2R8P2P7P3CXp=0%G2R9%93g003^R:#B#B#B#DR;'8P4%97R</1;R=P5g00Ii1173#=1887R>[18731187#=[R?f3R@/18#=\>1R73P3n2001000000120000000X52X62P?^52^62P3%O8R?#@R>P;%J?1I6>g03AoR?#H%G?1a27%_2%[2R?g03B[RAg03C:RBPBg03CZRCP?PAPBPBPCP21Y2:g03FA1W2;CVg03DaFURA%TBPAGS1Q?CP3P817451P38#=dAN267CMb9b:b;X42183;187;[^42P3f4R6#9P@O2b8b?O3b3CLA245=P4P51?92R5/?2R=/?2RC#KR?P4P?P3PCPC%9@,;;#:#<9>2@%D:R:,A6RAf5RB36RDP0P=P2P?P3P0P5P2P?P7P0P9P2P?P7P4P?f:/36g03c4,ECREA0973RF=058=0=6,5CRGn0100000020000RHn200110:000120105104n200110200012010:106n2001100000120102107X0CC4A6@ABn0100000020000P1PCP?PDP0P=P2P?P3P0P5P2P?P7P0P9P2P?P7PHn200110;000120105104n200110:00012010;106n200110200012010:1031EC3RH%`CRD%^CRBn10110<00041010210108000032X<41;;>#:#<9>281A@:;66P?P1PCPCPCP3P0P=P2P?P3P0P5P2P?P7P0P9P2P?P7P4P?f;/36PEPGn0100000020000RAn200110:000120105104n200110200012010:106n2001100000120102107X0CC4P1PCP?P3P0P=P2P?P3P0P5P2P?P7P0P9P2P?P7PAn200110;000120105104n200110:00012010;106n200110200012010:103PHPDPBn10110<00041010210108000052?P3P0P=P2PCPC15C3P0P=P2P?P3P0P5P2P?P7P0P9P2P?P7P4P?f=/36PEPGn0100000020000n200110:000120105104n200110200012010:106n2001100000120102107X0CC4P0P=P2P?P3P0P5P2P?P7P0P9P2P?P7P4P?f</36PEPGn0100000020000n200110;000120105104n200110:00012010;106n200110200012010:10352?P3P0P5P2PCPCA0=73,5CP0P=P2P?P3P0P5P2P?P7P0P9P2P?P7P4P?fA#9RA/16PEPGn0100000020000n200110:000120105104n200110200012010:106n2001100000120102107X0CC4P0P5P2P?P7P0P9P2P?P7P4P?f>/36PEPGn0100000020000n200110;000120105104n200110:00012010;10652?^12P3P0P9P2PCPCA0587=0=3,5CP0P=P2P?P3P0P5P2P?P7P0P9P2P?P7P4P?fE/36PEPGn0100000020000n200110:000120105104n200110200012010:106n2001100000120102107X0CC4P0P9P2P?P8P4P?f@/38PEA05F@=0=8,5Cn0100000020000n200110;00012010510452?^12^12P3P4P?11A3PEA09@8=057=0=3,5Cn0100000020000,7?X>2XD2X@2XB9P7P3O2n2001102010120109101X25P7P3O2n2001102010121102101X2=P7P3O2n2001102010121102101X2CP3O117?HX12P3O117?D17?Bn101100010411102101010000b011>;P3E]b3P4P?1F27R>/1;PCPC1;;>#:#<9>271A8:R:;6@P0P=P2P?P3P0P5P2P?P7P0P9P2P?P7P4P?f8R>,F2/16PEPGn0100000020000n200110:000120105104n200110200012010:106n2001100000120102107X0CC4A67:@n0100000020000P1PCP?1;;<#:#<9>27?6:@P0P=P2P?P3P0P5P2P?P7P0P9P2P?P7P4P?13>6PEPGn0100000020000n200110;000120105104n200110:00012010;106n200110200012010:103PHPDPBn10110<000410102101080000RB52?eAZ@87=2?BeW7X=9XA2WCo"). Qed.


Theorem rd_smallA : forall (L : alayout) (RNG : footprint)
         (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
         (SPV NC MSVP TLP BUF : Z) (rt0 buf : list Z) (msv0 lo : Z) (tl0 : word) (kq : nat),
  kk = S kq ->
  AHEAP AI L RNG st LB m ->
  fake0_lek kq LB ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  u8arr bsegs m NC (u16s (map (Z_to_bv 64) rt0)) ->
  rw_cells bsegs m MSVP [C4 (Z_to_bv 64 msv0)] -> rw_cells bsegs m TLP [C4 tl0] ->
  bytes_at bsegs m BUF (map (Z_to_bv 8) buf) -> Forall (fun c => 0 <= c < 256) buf ->
  0 <= msv0 <= 255 -> msv0 + 1 <= zlen rt0 -> zlen buf < 8 -> zlen rt0 <= 65536 ->
  bufA m LB NC (2 * zlen rt0) -> NC mod 8 = 0 -> nhullA RNG m LB NC (2 * zlen rt0) ->
  fcellA m LB MSVP 4 -> MSVP mod 4 = 0 -> fcellA m LB TLP 4 -> TLP mod 4 = 0 ->
  bufH LB BUF (zlen buf) -> ablk BUF (BUF + zlen buf) ->
  (NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC) -> (NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC) ->
  (MSVP + 4 <= TLP \/ TLP + 4 <= MSVP) ->
  stk bsegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - FSE_READ_STACK_A ->
  SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  rng RNG NC (2 * zlen rt0) -> rng RNG (shad NC) (nshad (2 * zlen rt0)) ->
  rng RNG MSVP 4 -> rng RNG (shad MSVP) 1 -> rng RNG TLP 4 -> rng RNG (shad TLP) 1 ->
  evtF bsegs RNG (fse_readr_postA AI L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB SPV NC MSVP TLP rt0
                    (read_ncount rt0 msv0 buf) lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
                (Z_to_bv 64 (zlen buf)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AFSE_RD_BODY) fc None m (seg_rom bsegs)).
Proof.
intros L RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB SPV NC MSVP TLP BUF rt0 buf
msv0 lo tl0 kq EK
AH LEK LBH ARR HMSV HTL HBUF FBY HM0 HM1 H8 HRT BFN N8 HULL FCM M4 FCT T4 HBH BBK SNM SNT SMT ST BOT LO SPT SP16 MI TP
RSTK RI RFS RNc RNS RM RMS RT RTS.
pose proof atop_range as ATR.
pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
unfold FSE_READ_STACK_A in LO.
pose proof (spa_props2 SPV SP16) as (SPAB & SPA32).
assert (AR1 : ATOP <= SPAz SPV - 2224) by (clear - LO BOT SPAB; lia).
assert (AR2 : SPAz SPV + 192 <= SPV) by (clear - SPAB; lia).
assert (AR3 : ATOP + 4096 <= SPAz SPV - 2224) by (clear - LO BOT SPAB; lia).
assert (AR4 : SPAz SPV + 88 <= 2^47) by (clear - SPAB SPT LY3; lia).
assert (LOC : ATOP <= lo) by (clear - BOT; lia).
assert (LO8 : lo <= SPV - RD8_STACK) by (unfold RD8_STACK, SM0R_STACK; clear - LO; lia).
assert (LOI : lo <= SPAz SPV - RD8_STACK) by (unfold RD8_STACK, SM0R_STACK; clear - LO SPAB; lia).
assert (SPTI : SPAz SPV + 16 < al_top L) by (clear - SPAB SPT; lia).
assert (SPI16 : SPAz SPV mod 16 = 0) by (clear - SPA32; Z.div_mod_to_equations; lia).
assert (STOP : SPV <= al_top L) by (clear - SPT; lia).
assert (SPK : SPV + 16 < KEND) by (clear - SPT LY3; unfold KEND; lia).
pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
boxH SNM. boxH SNT. boxH SMT.
set (hb := zlen buf) in *. set (buf' := buf ++ repeat 0 (Z.to_nat (8 - hb))).
assert (HB8 : 0 <= hb < 8) by (subst hb; clear - H8; lia).
assert (HB64 : 0 <= hb < 2^64) by (clear - HB8; lia).
assert (LB' : zlen buf' = 8) by (subst buf' hb; rewrite length_app, repeat_length; clear - H8; lia).
assert (FB' : Forall (fun c => 0 <= c < 256) buf').
{ subst buf'. apply Forall_app. split; [exact FBY|]. apply Forall_forall. intros c Hc. apply repeat_spec in Hc. lia. }
destruct (bufA_block m LB NC (2 * zlen rt0) BFN) as (bN & HbN & N1' & N2).
pose proof FCM as [(cM & FAM & FNM & HbM & M1 & M2 & M3 & M5) _].
pose proof FCT as [(cT & FAT & FNT & HbT & T1 & T2 & T3 & T5) _].
assert (ABN : ablk NC (NC + 2 * zlen rt0)) by (eapply ablk_sub; [exact (LBH _ HbN)| clear - N1'; lia| clear - N2; lia]).
assert (ABM : ablk MSVP (MSVP + 4)) by (eapply ablk_sub; [exact M3| clear - M1; lia| clear - M2; lia]).
assert (ABT : ablk TLP (TLP + 4)) by (eapply ablk_sub; [exact T3| clear - T1; lia| clear - T2; lia]).
pose proof (ablk_lin _ _ ABN) as (ABNa & ABNb & ABNc & ABNd). pose proof (ablk_lin _ _ ABM) as (ABMa & ABMb & ABMc & ABMd).
pose proof (ablk_lin _ _ ABT) as (ABTa & ABTb & ABTc & ABTd).
assert (HPs : forall a', in_fake LB a' -> aclient_addr CI LB SPV (shad a')) by (intros a' Ha'; apply cl_shadow; right; right; exact Ha').
lazymatch goal with |- evtF _ _ ?P _ =>
eapply evtF_cut; [eapply (rd_open AI fflag rng_fs kk SM0K L RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
FR fc m st LB SPV NC MSVP TLP BUF hb lo (evtF bsegs RNG P));
[first [assumption| (rewrite EK; eapply fake0_lek_mono; [| exact LEK]; lia)| exact BBK| clear - HB8; lia] .. | ]
| intros ms' Hms; exact Hms ] end.
intros FF m3 k0 k8 k16 k32 k40 k48 k64 junk x5 x6 x7 y10 y11 y12 x14 x15 x16 x17 x28 x29 x30 x31
F64 FH FC RFF RSFF FFD AH3 MG3 MI3 FRB3 FRA3 FFC3 SHF3 STL3 STG3.
replace (7 <? hb) with false by (symmetry; apply Z.ltb_ge; clear - HB8; lia). cbv iota.
pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd).
assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
by (clear - FH; apply ablk_lin in FH; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
destruct BSF as [BSF1 BSF2].
destruct HBH as (p & BA0 & BN0 & HBB & BH1 & BH2).
destruct (AI_block AI _ _ _ _ _ _ _ _ AH3 (or_intror HBB))
as (HBN & (BR1 & BR2 & BR3 & BR4) & RBUF & RSB & SHBB & WRB & _ & (RLO & RHI & RL1 & RL2 & RL3 & RL4 & RLR & RLW)).
pose proof (ablk_lin _ _ BBK) as (BR1a & BR1b & BR1c & BR1d).
destruct (block_hullR RNG m3 BUF hb RLO RHI ltac:(clear - HB8; lia) RL1 RL2 ltac:(clear - RL3 BH1; lia) ltac:(clear - RL4 BH2; lia) ltac:(unfold AIMG_HI in BR1a; clear - BR1a; lia) RLR RLW)
as (HR1 & HW1 & HL1 & HL2 & HL3 & HL4 & HL5 & HL6).
assert (UB3 : unpoisoned m3 BUF (BUF + hb)).
{ eapply (bufA_unpoisoned AI L RNG st (FB0 FF :: LB) m3); [exact AH3| | clear - HB8; lia]. apply bufA_of_bufH. exists p, BA0, BN0. split; [right; exact HBB| split; lia]. }
assert (RBUF' : rng RNG BUF hb) by (eapply rng_sub'; [refine RBUF| lia]).
assert (HBUF3 : bytes_at bsegs m3 BUF (map (Z_to_bv 8) buf)).
{ eapply bytes_at_magree; [exact MG3| exact HBUF|]. rewrite length_map.
intros a Ha. apply (cl_range_block CI LB SPV _ BUF hb HBB); cbn [ab_addr ab_size]; clear - Ha BH1 BH2; lia. }
pose proof (AI_rtcells AI _ _ _ _ _ AH3) as RTC. unfold artcells in RTC.
destruct RTC as (C0 & GOT & RIC & REAL & SHB & SUA & INI & LAY & _).
pose proof (FFD _ HBB) as DFB. cbn [ab_addr ab_size] in DFB.
eapply (rd_small1 gp tp FR fc SPV lo);
first [exact HB8| exact FBY| exact HBUF3| exact FFC3| exact SHF3| exact FRA3| exact MI3| exact STL3| exact GOT| exact RIC| exact SHB| exact INI
| exact LAY| exact REAL| exact UB3| exact FH| exact FC| exact F64| exact DFB| exact BBK| exact RFF| exact RSFF| exact RBUF'
| exact SP16| exact RI| exact HW1| exact HR1| exact LOC| exact SPK
| apply ablk_app_blk; [exact BBK| clear - HB8; lia]
| split; [exact HL1|]; split; [exact HL2|]; split; [exact HL3|]; split; [exact HL4|]; split; [exact HL5| unfold KEND; clear - HL6 BR1c ATR; lia]
| eapply rng_sub'; [exact RSTK| clear - STOP; lia]
| unfold RD8_STACK, SM0R_STACK in LO8; clear - LO8; lia
| lazymatch goal with |- BUF + _ <= FF \/ FF + 64 <= BUF => clear - DFB BH1 BH2; lia end
| idtac].
intros m5 rs j16 y5 y6 y7 y16 y17 y28 y29 y30 y31 MU5 WM5 MI5 STL5 FFC5 SHF5 FRA5 HBUF5.
clear C0 GOT RIC REAL SHB SUA INI LAY.
assert (AH5 : AHEAP AI L RNG st (FB0 FF :: LB) m5).
{ eapply (AI_frame AI); [exact AH3| exact MU5| exact WM5|].
constructor; [cbn; left; left; clear - AR3 AR4; lia|].
constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]|].
constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
change (2 ^ 3) with 8; unfold ASHOFF; clear - F64 FHb; Z.div_mod_to_equations; lia]| constructor]. }
assert (MG5 : magree bsegs (aclient_addr CI LB SPV) m m5).
{ eapply magree_munch_step; [exact MG3| exact MU5| exact WM5|]. intros a Ha. cbn.
split; [intros Hr; exact (stack_not_client CI LB SPV (SPAz SPV - 2224) a HCI HCI0 LBH AR1 ltac:(clear - Hr AR2; lia) Ha)|].
split; [intros Hr; exact (app_not_client CI LB SPV FF 64 a HCI HCI0 FH ltac:(clear - AR1 AR2; lia) LBH FFD ltac:(clear - Hr; lia) Ha)|].
split; [intros Hr; refine (shadow_not_client CI LB SPV FF a HCI HCI0 FH F64 ltac:(clear - AR1 AR2; lia) LBH FFD _ Ha);
unfold shad, ASHOFF; clear - Hr; lia| exact I]. }
destruct (rffhdr5_split m5 FF rs _ j16 (fflag L 0 FF) FFC5) as (FF05 & FB5 & FF565).
pose proof rd_body8A as RB8. unfold rd_body8A_stmt in RB8.
assert (IARR : u8arr bsegs m5 NC (u16s (map (Z_to_bv 64) rt0))).
{ eapply u8arr_mg; [exact MG5| exact ARR|]. rewrite u16s_length, length_map.
intros a Ha. apply (cl_range_block CI LB SPV _ NC (2 * zlen rt0) HbN); cbn [ab_addr ab_size]; [exact N1'| exact N2| clear - Ha; lia]. }
assert (IHMSV : rw_cells bsegs m5 MSVP [C4 (Z_to_bv 64 msv0)]).
{ eapply rw_cells_magree; [exact MG5| exact HMSV|]. cbn [cells_size csize Nat.add].
intros a Ha. apply (cl_range_block CI LB SPV _ MSVP 4 HbM); cbn [ab_addr ab_size]; [exact M1| exact M2| clear - Ha; lia]. }
assert (IHTL : rw_cells bsegs m5 TLP [C4 tl0]).
{ eapply rw_cells_magree; [exact MG5| exact HTL|]. cbn [cells_size csize Nat.add].
intros a Ha. apply (cl_range_block CI LB SPV _ TLP 4 HbT); cbn [ab_addr ab_size]; [exact T1| exact T2| clear - Ha; lia]. }
assert (IHBUF : bytes_at bsegs m5 (FF + 32) (map (Z_to_bv 8) buf')).
{ destruct FB5 as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. exact BA. }
assert (ILE : fake0_lek kk (FB0 FF :: LB)) by (rewrite EK; apply fake0_lek_push0; exact LEK).
assert (ILBH : forall b, In b (FB0 FF :: LB) -> ablk (ab_addr b) (ab_addr b + ab_size b)).
{ intros b [<-|Hb]; [exact FH| exact (LBH b Hb)]. }
assert (INCL : forall b, In b LB -> In b (FB0 FF :: LB)) by (intros b Hb; right; exact Hb).
assert (IBFN : bufA m5 (FB0 FF :: LB) NC (2 * zlen rt0)) by (eapply bufA_mono; [eapply bufA_mg; [exact MG5| exact HPs| exact BFN]| exact INCL]).
assert (IFCM : fcellA m5 (FB0 FF :: LB) MSVP 4) by (eapply fcellA_mono; [eapply fcellA_mg; [exact MG5| exact HPs| exact FCM]| exact INCL]).
assert (IFCT : fcellA m5 (FB0 FF :: LB) TLP 4) by (eapply fcellA_mono; [eapply fcellA_mg; [exact MG5| exact HPs| exact FCT]| exact INCL]).
assert (IHULL : nhullA RNG m5 (FB0 FF :: LB) NC (2 * zlen rt0)) by (eapply nhullA_mono; [eapply nhullA_mg; [exact MG5| exact HPs| exact HULL]| exact INCL]).
assert (IBFA : bufA m5 (FB0 FF :: LB) (FF + 32) (zlen buf')).
{ right. rewrite LB'. split.
- exists 0, FF, 64. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact FH| clear - F64; Z.div_mod_to_equations; lia].
- apply c1z_unpoisonedR; [| clear - F64; Z.div_mod_to_equations; lia| lia| lia| lia].
replace (Z.shiftr (FF + 32) 3 + 2147450880) with (Z.shiftr FF 3 + 2147450880 + 4).
+ exact (rffsh0_byte4 _ _ SHF5).
+ rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - F64. Z.div_mod_to_equations. lia. }
assert (IBBK : ablk (FF + 32) (FF + 32 + zlen buf')) by (rewrite LB'; eapply ablk_sub; [exact FH| lia| lia]).
assert (IB8 : (FF + 32) mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
pose proof (blk_sepF FF NC (2 * zlen rt0) (ab_addr bN) (ab_size bN) N1' N2 (FFD _ HbN)) as DNF.
pose proof (blk_sepF FF MSVP 4 FAM FNM M1 M2 (FFD _ HbM)) as DMF.
pose proof (blk_sepF FF TLP 4 FAT FNT T1 T2 (FFD _ HbT)) as DTF.
assert (ISNB : NC + 2 * zlen rt0 <= FF + 32 \/ FF + 32 + zlen buf' <= NC) by (rewrite LB'; clear - DNF; lia).
assert (ISMB : MSVP + 4 <= FF + 32 \/ FF + 32 + zlen buf' <= MSVP) by (rewrite LB'; clear - DMF; lia).
assert (ISTB : TLP + 4 <= FF + 32 \/ FF + 32 + zlen buf' <= TLP) by (rewrite LB'; clear - DTF; lia).
boxH DNF. boxH DMF. boxH DTF. boxH ISNB. boxH ISMB. boxH ISTB.
assert (IH8 : 8 <= zlen buf' <= 65536) by (rewrite LB'; lia).
assert (IRBf : rng RNG (FF + 32) (zlen buf')) by (rewrite LB'; eapply rng_sub'; [exact RFF| lia]).
assert (IRBS : rng RNG (shad (FF + 32)) (nshad (zlen buf' + (FF + 32) mod 8))).
{ rewrite IB8, Z.add_0_r. rewrite LB'. eapply rng_sub'; [exact RSFF|]. rewrite !shad_div. unfold nshad. rewrite Z.shiftr_div_pow2 by lia.
change (2^3) with 8. clear - F64 FHb. Z.div_mod_to_equations. lia. }
replace (Z_to_bv 64 8) with (Z_to_bv 64 (zlen buf')) by (rewrite LB'; reflexivity).
eapply evtF_cut.
{ eapply (RB8 L RNG (Z_to_bv 64 0x96b90) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAz SPV)) (Z_to_bv 64 0) y16 y17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + hb)) s4 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 hb) (Z_to_bv 64 (FF + 32))
(Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) y28 y29 y30 y31 FR fc m5 st (FB0 FF :: LB)
(SPAz SPV) NC MSVP TLP (FF + 32) rt0 buf' msv0 lo tl0
AH5 ILE ILBH IARR IHMSV IHTL IHBUF FB' HM0 HM1 IH8 HRT IBFN N8 IHULL IFCM M4 IFCT T4 IBFA IBBK SNM SNT ISNB SMT ISMB ISTB
STL5 BOT LOI SPTI SPI16 MI5 TP RSTK RI RFS RNc RNS RM RMS RT RTS IRBf IRBS). }
cbv beta. intros ms' PO.
destruct PO as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & r & m7 & -> & MI7 & ST7 & MG7 & AH7 & RES7).
rd_retlit.
assert (UNI : exists rtX msvX tlX, length rtX = length rt0 /\ u8arr bsegs m7 NC (u16s (map (Z_to_bv 64) rtX))
/\ rw_cells bsegs m7 MSVP [C4 (Z_to_bv 64 msvX)] /\ rw_cells bsegs m7 TLP [C4 (Z_to_bv 64 tlX)] /\ 0 <= r < 2^64
/\ (forall ms', fse_read_postA AI L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB SPV NC MSVP TLP rt0 rtX msvX tlX (small_res hb r) lo m ms' ->
fse_readr_postA AI L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB SPV NC MSVP TLP rt0 (read_ncount rt0 msv0 buf) lo m ms')).
{ rewrite (read_ncount_small rt0 msv0 buf H8). change (zlen buf) with hb. change (buf ++ repeat 0 (Z.to_nat (8 - hb))) with buf'.
destruct (read_ncount_body8_total buf' (msv0 + 1) rt0 (Forall_all_bytes _ FB') ltac:(unfold FseNCount.Zlength; clear - LB'; lia)
ltac:(unfold FseNCount.Zlength; clear - HM1 HM0; lia)) as [(rt & msv & tl & n & RB & LRT & _ & _ & _ & N12 & _) | (e & RB)];
rewrite RB in RES7 |- *; cbn [fse_read_resA] in RES7.
- destruct RES7 as (-> & ARR7 & HMSV7 & HTL7). exists rt, msv, tl.
split; [exact LRT|]. split; [exact ARR7|]. split; [exact HMSV7|]. split; [exact HTL7|].
unfold FseNCount.Zlength in N12. rewrite LB' in N12. split; [lia|].
intros ms' Hp. unfold small_res in Hp. change (2^64 - 119) with 18446744073709551497 in Hp.
replace (n <? 18446744073709551497) with true in Hp by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in Hp.
destruct (Z.ltb_spec hb n).
+ eapply readr_of_err; [exact Hp| split; reflexivity| exact LRT].
+ apply readr_of_ok. exact Hp.
- destruct RES7 as (-> & E120 & (rt' & msv' & tl' & LRT & ARR7 & HMSV7 & HTL7)). exists rt', msv', tl'.
split; [exact LRT|]. split; [exact ARR7|]. split; [exact HMSV7|]. split; [exact HTL7|]. split; [lia|].
intros ms' Hp. unfold small_res in Hp.
replace (2^64 - e <? 2^64 - 119) with false in Hp by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in Hp.
eapply readr_of_err2; [exact Hp| exact E120| exact LRT]. }
destruct UNI as (rtX & msvX & tlX & LRT & ARR7 & HMSV7 & HTL7 & R64 & CONV).
assert (SPAV : SPAz SPV <= SPV) by (clear - AR2; lia).
assert (SHF7 : rw_cells bsegs m7 (Z.shiftr FF 3 + 2147450880) RFFSH0).
{ eapply rw_cells_magree; [exact MG7| exact SHF5|]. change (Z.of_nat (cells_size RFFSH0)) with 8.
intros a Ha. apply (pag_shadowR AI (FB0 FF :: LB) (SPAz SPV) NC MSVP TLP rt0 0 FF 64 (or_introl eq_refl));
[clear - F64; Z.div_mod_to_equations; lia| reflexivity| exact FHb| clear - FHd; lia| exact ABN| exact ABM| exact ABT|].
change (64 / 8) with 8. unfold shad, ASHOFF. clear - Ha. lia. }
eapply (rd_small2G gp tp FR fc SPV lo);
first [exact SHF7| exact MI7| exact FH| exact F64| exact RSFF| exact SP16| exact LOC| exact SPK
| eapply rng_sub'; [exact RSTK| clear - STOP; lia]
| unfold RD8_STACK, SM0R_STACK in LO8; clear - LO8; lia
| exact R64
| exact HB8
| idtac].
intros m6 z10 z12 MU6 WM6 MI6 SHF6.
assert (AH6 : AHEAP AI L RNG st (FB0 FF :: LB) m6).
{ eapply (AI_frame AI); [exact AH7| exact MU6| exact WM6|].
constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
change (2 ^ 3) with 8; unfold ASHOFF; clear - F64 FHb; Z.div_mod_to_equations; lia]| constructor]. }
assert (MG6 : magree bsegs (PAG AI LB SPV NC MSVP TLP rt0) m m6).
{ eapply magree_trans; [eapply magree_mono; [exact MG5| intros a HP; destruct HP as (Ha & _); exact Ha]|].
eapply magree_munch_step; [eapply magree_mono; [exact MG7|]| exact MU6| exact WM6|].
- intros a HP. destruct HP as (Ha & HN & HM & HT). split; [eapply aca_monoA; [exact Ha| exact INCL| exact SPAV]|].
split; [exact HN|]. split; [exact HM| exact HT].
- intros a HP. destruct HP as (Ha & _). cbn. split; [| exact I].
intros Hr. refine (shadow_not_client CI LB SPV FF a HCI HCI0 FH F64 ltac:(clear - AR1 AR2; lia) LBH FFD _ Ha).
unfold shad, ASHOFF. clear - Hr. lia. }
unfold bx in DNF, DMF, DTF.
assert (PFF : forall k, 0 <= k -> forall d, 0 <= d -> d + k <= 64 ->
forall a, FF + d <= a < FF + d + k -> PAG AI (FB0 FF :: LB) (SPAz SPV) NC MSVP TLP rt0 a).
{ intros k K0 d D0 DK. apply (pag_blockR AI (FB0 FF :: LB) (SPAz SPV) NC MSVP TLP rt0 (FB0 FF) (FF + d) k (or_introl eq_refl));
cbn [ab_addr ab_size]; clear - K0 D0 DK DNF DMF DTF; lia. }
assert (PST : forall X Y, SPAz SPV <= X -> Y <= SPV -> forall a, X <= a < Y -> PAG AI (FB0 FF :: LB) (SPAz SPV) NC MSVP TLP rt0 a).
{ intros X Y HX HY. apply pag_stackR; clear - HX HY SPK AR1 ABNc ABMc ABTc; unfold KEND in SPK; lia. }
assert (DW6 : forall A k, ablk A (A + k) -> disjoint_from [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] A k).
{ intros A k HA. cbn [disjoint_from]. split; [| exact I].
destruct (app_vs_shadow A k (Z.shiftr FF 3 + 2147450880 + 4) 1 HA ltac:(clear - BSF1; lia) ltac:(clear - BSF2; lia)); lia. }
assert (DW6s : forall A k, ATOP <= A -> disjoint_from [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] A k).
{ intros A k HA. cbn [disjoint_from]. split; [| exact I]. clear - HA BSF2 ATR. lia. }
assert (FF06 : rw_cells bsegs m6 FF [C8 (Z_to_bv 64 0x41b58ab3)]).
{ eapply rw_cells_transport; [| exact MU6| exact WM6| rewrite zsize_c8; apply DW6; eapply ablk_sub; [exact FH| clear; lia| clear; lia]].
eapply rw_cells_magree; [exact MG7| exact FF05|]. change (Z.of_nat (cells_size [C8 (Z_to_bv 64 0x41b58ab3)])) with 8.
intros a Ha. apply (PFF 8 ltac:(lia) 0 ltac:(lia) ltac:(lia)). clear - Ha. lia. }
assert (FF566 : rw_cells bsegs m6 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))]).
{ eapply rw_cells_transport; [| exact MU6| exact WM6| rewrite zsize_c8; apply DW6; eapply ablk_sub; [exact FH| clear; lia| clear; lia]].
eapply rw_cells_magree; [exact MG7| exact FF565|]. change (Z.of_nat (cells_size [C8 (Z_to_bv 64 (fflag L 0 FF))])) with 8.
intros a Ha. apply (PFF 8 ltac:(lia) 56 ltac:(lia) ltac:(lia)). clear - Ha. lia. }
assert (FRB6 : rw_cells bsegs m6 (SPV + -104) (RFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
{ eapply rw_cells_transport; [| exact MU6| exact WM6| apply DW6s; clear - AR1 AR2; lia].
eapply rw_cells_magree; [exact MG7| |].
- eapply rw_cells_transport; [exact FRB3| exact MU5| exact WM5|]. change (Z.of_nat (cells_size (RFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))) with 104.
cbn [disjoint_from]. clear - AR1 AR2 FHc BSF2 ATR. lia.
- change (Z.of_nat (cells_size (RFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))) with 104.
apply PST; clear - AR2; lia. }
assert (FRA6 : rw_cells bsegs m6 (SPAz SPV) [CB 8 k0; CB 8 k8; CB 8 k16; C8 (Z_to_bv 64 FF); CB 8 k32; CB 8 k40; CB 8 k48;
C8 (Z_to_bv 64 MSVP); CB 16 k64; C8 (Z_to_bv 64 FF)]).
{ eapply rw_cells_transport; [| exact MU6| exact WM6| apply DW6s; clear - AR1; lia].
eapply rw_cells_magree; [exact MG7| exact FRA5|].
change (Z.of_nat (cells_size [CB 8 k0; CB 8 k8; CB 8 k16; C8 (Z_to_bv 64 FF); CB 8 k32; CB 8 k40; CB 8 k48;
C8 (Z_to_bv 64 MSVP); CB 16 k64; C8 (Z_to_bv 64 FF)])) with 88. apply PST; clear - AR2; lia. }
change [CB 8 k0; CB 8 k8; CB 8 k16; C8 (Z_to_bv 64 FF); CB 8 k32; CB 8 k40; CB 8 k48; C8 (Z_to_bv 64 MSVP); CB 16 k64; C8 (Z_to_bv 64 FF)]
with ([CB 8 k0; CB 8 k8; CB 8 k16; C8 (Z_to_bv 64 FF)] ++ [CB 8 k32; CB 8 k40; CB 8 k48; C8 (Z_to_bv 64 MSVP); CB 16 k64; C8 (Z_to_bv 64 FF)] ++ []) in FRA6.
apply rw_cells_merge in FRA6.
lazymatch type of FRA6 with rw_cells ?sg ?mm ?AA (?l ++ ?x) =>
change (rw_cells sg mm AA ([] ++ [CB 8 k0; CB 8 k8; CB 8 k16] ++ (C8 (Z_to_bv 64 FF) :: x))) in FRA6 end.
apply rw_cells_merge in FRA6. cbn [app cells_size csize Nat.add] in FRA6.
assert (STG6 : stk bsegs m6 (SPAz SPV + 88) (SPV + -104)).
{ eapply stk_transport; [| exact MU6| exact WM6| intros x Hx; left; cbn; clear - Hx AR1 BSF2 ATR; lia].
eapply stk_magree; [exact MG7| | apply PST; clear - AR2; lia].
eapply stk_transport; [exact STG3| exact MU5| exact WM5| intros x Hx; left; cbn; clear - Hx AR1 AR2 FHc BSF2 ATR; lia]. }
assert (ST6 : stk bsegs m6 lo (SPAz SPV)).
{ eapply stk_transport; [exact ST7| exact MU6| exact WM6| intros x Hx; left; cbn; clear - Hx LOC BSF2 ATR; lia]. }
assert (LNC : Z.of_nat (length (u16s (map (Z_to_bv 64) rtX))) = 2 * zlen rt0) by (rewrite u16s_length, length_map, LRT; lia).
assert (ARR6 : u8arr bsegs m6 NC (u16s (map (Z_to_bv 64) rtX))).
{ eapply u8arr_transport; [exact ARR7| exact MU6| exact WM6|]. rewrite LNC. apply DW6. exact ABN. }
assert (HMSV6 : rw_cells bsegs m6 MSVP [C4 (Z_to_bv 64 msvX)]) by (eapply rw_cells_transport; [exact HMSV7| exact MU6| exact WM6| rewrite zsize_c4; apply DW6; exact ABM]).
assert (HTL6 : rw_cells bsegs m6 TLP [C4 (Z_to_bv 64 tlX)]) by (eapply rw_cells_transport; [exact HTL7| exact MU6| exact WM6| rewrite zsize_c4; apply DW6; exact ABT]).
eapply evtF_mono; [eapply (rd_close AI fflag FFLAG FREL L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m6 st LB SPV NC MSVP TLP lo FF rt0 rtX msvX tlX (small_res hb r)
(Z_to_bv 64 0x41b58ab3));
first [exact AH6| exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact MG6| exact MI6| exact SHF6
| exact FF06| exact FF566| exact FRB6| exact FRA6| reflexivity| exact ST6| exact STG6| exact BOT| exact RSTK| exact ARR6
| exact HMSV6| exact HTL6| exact LRT| exact BFN| exact FCM| exact FCT| exact SP16| exact LO8| exact SPT] | exact CONV].
Qed.


Theorem fse_readk_proofA : forall k, kk = S k -> fse_readk_stmtA AI rng_fs k.
Proof.
intros k EK. unfold fse_readk_stmtA, fse_readk_postA.
intros L RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB SPV NC MSVP TLP BUF
rt0 buf msv0 lo tl0
AH LEK LBH ARR HMSV HTL HBUF FBY HM0 HM1 HBL HRT BFN N8 HULL FCM M4 FCT T4 HBH BBK SNM SNT SNB SMT SMB STB ST BOT LO SPT SP16 MI TP
RSTK RI RFS RNc RNS RM RMS RT RTS RBf RBS.
destruct (Z_lt_le_dec (zlen buf) 8) as [LT|GE].
- exact (rd_smallA L RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB SPV NC MSVP TLP BUF
rt0 buf msv0 lo tl0 k EK AH LEK LBH ARR HMSV HTL HBUF FBY HM0 HM1 LT HRT BFN N8 HULL FCM M4 FCT T4 HBH BBK SNM SNT SMT ST BOT LO SPT SP16 MI TP
RSTK RI RFS RNc RNS RM RMS RT RTS).
- assert (RB : read_ncount rt0 msv0 buf = read_ncount_body8 buf (msv0 + 1) rt0).
{ unfold read_ncount, FseNCount.Zlength. replace (zlen buf <? 8) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
rewrite RB.
assert (LO8 : lo <= SPV - RD8_STACK) by (unfold RD8_STACK, SM0R_STACK; unfold FSE_READ_STACK_A in LO; clear - LO; lia).
exact (rd_body8A L RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB SPV NC MSVP TLP BUF
rt0 buf msv0 lo tl0 AH (fake0_lek_mono k kk LB ltac:(lia) LEK) LBH ARR HMSV HTL HBUF FBY HM0 HM1 ltac:(split; lia) HRT BFN N8 HULL
FCM M4 FCT T4 (bufA_of_bufH m LB BUF (zlen buf) HBH) BBK SNM SNT SNB SMT SMB STB ST BOT LO8 SPT SP16 MI TP
RSTK RI RFS RNc RNS RM RMS RT RTS RBf RBS).
Qed.

End Asm.


Theorem fse_readk_proof : forall (AI : AMallocIface) (fflag : alayout -> Z -> Z -> Z) (rng_fs : alayout -> footprint -> Prop) (k : nat),
  fake_flag_law AI fflag -> fake_release_law AI fflag -> stack_malloc_0k_stmt AI fflag rng_fs (S k) ->
  fse_readk_stmtA AI rng_fs k.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_fse_rd ()) ["CANSEC1"] "h02AIh15FFLAGh24FRELh34SM0Kh45fflagh51kh66rng_fsp;1p;3p;5p;2p;9g04]Ij16Tg04^Pj35Tg04_Vj31Tg00T;j10Tg04`_j54Tg003Dj22Tg04all93Tp,2rcR0#6g03NJR1g004CR2P2\2[[g03ODp-0[\1g03IQR1f3R2f2R3550f4R4=102P0f5R0P4P2%03D4f6P0P4P3f1%02R3f0P21213M93W3W2W1W5W6W4W0o"). Qed.
End CANSEC1.
