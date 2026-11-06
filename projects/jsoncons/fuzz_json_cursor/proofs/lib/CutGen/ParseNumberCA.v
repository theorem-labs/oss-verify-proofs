(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require ParseNumberCA_blobs1 ParseNumberCA_blobs2.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8PlanKit Pm8L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutShA CutShB CutShC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_pn_casan_T Cut_pn_casan_D Cut_pn_casan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsKitA PsSmA ParseNumberChkCA PnAuxCA PnLeafCA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import CurKitCA CurKitCA2.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Rpl.
Ltac2 rplG () : string array := Array.of_list ["Corelib.Numbers.BinNums.Zpos"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.CUR0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.WLEN"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.EMd"; "LinuxProcessSemantics.Riscv.Instr.M_MUL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.ELit"; "Corelib.Numbers.BinNums.Zneg"; "Corelib.Numbers.BinNums.xH"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.JV"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.env"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Npos"; "Corelib.Init.Datatypes.option"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.saddr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.expr"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.estart"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Numbers.BinNums.Z0"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.edenot"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.u32_at"; "Corelib.Init.Logic.eq_ind_r"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.micromega.ZifyClasses.rew_iff_rev"; "Stdlib.micromega.ZifyClasses.and_morph"; "Stdlib.micromega.ZifyClasses.eq_iff"; "Corelib.Init.Logic.eq_refl"; "Stdlib.micromega.ZifyClasses.mkrel"; "Corelib.Init.Logic.iff_refl"; "Stdlib.micromega.ZifyClasses.mkapp"; "Corelib.Init.Datatypes.nat"; "Stdlib.micromega.ZifyClasses.mkapp2"; "Stdlib.micromega.ZifyClasses.inj"; "Stdlib.micromega.ZifyInst.Inj_Z_Z"; "Stdlib.ZArith.BinInt.Z.pow_pos_nonneg"; "Corelib.Init.Logic.True"; "Stdlib.ZArith.BinInt.Z.pow_nonneg"; "Corelib.Init.Datatypes.nil"; "Stdlib.micromega.ZMicromega.ZArithProof"; "Stdlib.micromega.VarMap.Elt"; "Stdlib.micromega.VarMap.t"; "Stdlib.micromega.Tauto.IMPL"; "Stdlib.micromega.RingMicromega.Formula"; "Stdlib.micromega.Tauto.eKind"; "Corelib.Init.Datatypes.unit"; "Stdlib.micromega.Tauto.isProp"; "Stdlib.micromega.Tauto.A"; "Stdlib.micromega.RingMicromega.Build_Formula"; "Stdlib.micromega.EnvRing.PEadd"; "Stdlib.micromega.EnvRing.PEX"; "Stdlib.micromega.EnvRing.PEc"; "Stdlib.micromega.RingMicromega.OpLe"; "Stdlib.micromega.EnvRing.PEpow"; "Corelib.Init.Datatypes.tt"; "Corelib.Init.Datatypes.None"; "Stdlib.micromega.Tauto.AND"; "Stdlib.micromega.RingMicromega.OpLt"; "Stdlib.micromega.Tauto.BFormula"; "Stdlib.micromega.ZMicromega.ZTautoChecker_sound"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.true"; "Stdlib.micromega.ZMicromega.ZTautoChecker"; "Stdlib.micromega.VarMap.find"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.flat"; "Corelib.Init.Logic.conj"; "Corelib.Init.Peano.le"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.rdn"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.adenot"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Stdlib.ZArith.Znat.Nat2Z.inj_le"; "Stdlib.micromega.VarMap.Empty"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5.CL5.adenot_start"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.kentry_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.KWord"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ls_state"; "Corelib.Init.Logic.not"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.regJ"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.LS0"; "Corelib.Init.Logic.eq_ind"; "Corelib.Init.Logic.False"; "Corelib.Init.Logic.I"; "Corelib.Init.Logic.False_ind"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.LS1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.J"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.C"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.JC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.CJ"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.Env"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.reg_ev"; "Corelib.Lists.ListDef.nth"; "Corelib.Init.Nat.sub"; "Corelib.Init.Datatypes.cons"; "Corelib.Lists.ListDef.map"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.parser_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.hl_segs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.C_casan"; "Corelib.Init.Datatypes.prod"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_win"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.u64_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.VT_PARSER"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.u8_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.lstr_short"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.VT_FUNC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_level"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_st"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_sst"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_nst"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.b2z"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_more"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_done"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.str_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.SLong"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_bcap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_bptr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_buf"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_sb"; "Corelib.Init.Datatypes.length"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_stack"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_scap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.bytes_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.defined"; "Corelib.Init.Datatypes.pair"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ST_NUMBER"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.PAR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.wf_ps"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.ex"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ST_ROOT"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.Forall"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.is_container"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.handled"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.transient"; "Corelib.Init.Logic.or"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ST_EXPECT_COMMA_OR_END"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.num_prefix"; "Corelib.Init.Datatypes.S"; "Stdlib.ZArith.Znat.Nat2Z.inj_succ"; "Stdlib.ZArith.Znat.Nat2Z.is_nonneg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.b2z"; "Stdlib.micromega.Tauto.X"; "Stdlib.micromega.ZifyClasses.rew_iff"; "Stdlib.micromega.Tauto.OR"; "Stdlib.micromega.RingMicromega.OpEq"; "Stdlib.micromega.Tauto.FF"; "Stdlib.micromega.ZMicromega.RatProof"; "Stdlib.micromega.RingMicromega.PsatzAdd"; "Stdlib.micromega.RingMicromega.PsatzMulC"; "Stdlib.micromega.EnvRing.Pc"; "Stdlib.micromega.RingMicromega.PsatzIn"; "Corelib.Init.Datatypes.O"; "Stdlib.micromega.ZMicromega.DoneProof"; "Stdlib.micromega.VarMap.Branch"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Logic.proj1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.WFX"; "Corelib.Init.Logic.ex_intro"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.max"; "Stdlib.micromega.ZifyInst.of_nat_to_nat_eq"; "Stdlib.ZArith.BinInt.Z.max_spec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.esc_need"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.buf_bound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.winlen"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.buf_need"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.eqb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ST_STRING"; "Stdlib.micromega.EnvRing.PEsub"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.lstr_long"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.pcredit_xA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.pcreditA"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.kleft"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.hl_k_per_malloc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.hl_b_lin"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.bleft"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.hl_b_overhead"; "Stdlib.ZArith.Zdiv.Z_div_mod_eq_full"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg"; "Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg"; "Stdlib.ZArith.BinInt.Z.div_mod"; "Stdlib.ZArith.BinInt.Z.mod_pos_bound"; "Stdlib.ZArith.BinInt.Z.mod_neg_bound"; "Stdlib.omega.PreOmega.Z.div_0_r_ext"; "Stdlib.omega.PreOmega.Z.mod_0_r_ext"; "Stdlib.micromega.EnvRing.PEmul"; "Stdlib.ZArith.Zdiv.Z_mod_mult"; "Stdlib.micromega.Tauto.NOT"; "Stdlib.micromega.RingMicromega.PsatzMulE"; "Stdlib.micromega.RingMicromega.PsatzC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5.CL5.ev_reg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.ev"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.E0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.hl_tp"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8L5DefsA.L5A.aly_segs"; "OSSVerify.jsoncons.fuzz_json_cursor.images.Asan.M.loaded_segments"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8L5DefsA.L5A.aly_img_lo"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.hl_img_lo"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8L5DefsA.L5A.aly_img_hi"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.hl_img_hi"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.wf_of"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.vml_of"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.wf_facts"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.rng_of_wf"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.rng_facts"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.rf_ceil"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.ar_sptop"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.rf_sptop"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.wf_top"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.ar_stack_top"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.astk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.SCR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.fobj"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.ainfr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.shadow_zero"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.fframe"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.ff_addr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.ff_bytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.ff_class"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.infr_rng"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.ar_fs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.FS_BYTES"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.BIGSHADOW_LO"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.BIGSHADOW_HI"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.rf_fs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.app_mem"; "Corelib.Init.Logic.or_introl"; "Corelib.Init.Logic.or_intror"; "Stdlib.Lists.List.in_or_app"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_blocks"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.shadow_blk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.wf_blk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.ablock_range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.defined"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.shadow_allowed"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.blocks_apart"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.lb_remove"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.fframes_apart"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.mod8_of_16"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.BBX"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.BCX"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.ESCN"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.VV"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.LibSym.u64_of_Z"; "stdpp.bitvector.definitions.bv_wrap"; "Stdlib.ZArith.BinInt.Z.mod_small"; "stdpp.bitvector.definitions.bv_modulus"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.unsigned_lit"; "stdpp.bitvector.definitions.bv_add"; "stdpp.bitvector.definitions.bv_add_unsigned"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.EVar"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.uv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UU"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.uv_add_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5.CL5.u_lin"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.lin_of"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.lin"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.uE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.tden"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.lden"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap.CH.hd_scr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.GT.HDECL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.SCRV"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.GT.NF"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.W_parEc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.Wo"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.WW"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.ERRCAT_GUARD"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.ATEXIT_TAB"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmIcptIfaceA.ATEXIT_TAB_BYTES"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.W_parE"; "Stdlib.Lists.List.incl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.in_rng"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.aclientw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.in_shadow_of"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.S"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.infr_wok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SegPlan.SGP.region"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap.CH.hd_wrs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SegPlan.SGP.region_vars_lt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.in_reg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.shadow_range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.sclientA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.aclient"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.in_block"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.hl_rt_static"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.in_fframe"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.not_stk_shadow_app"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.SHR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.not_stk_shadow_sh"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.SB"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.shreg_in_shadow"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.div8_le"; "Stdlib.micromega.ZMicromega.CutProof"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap.CH.hd_crs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UBC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UVPK"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.BLKC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.aclientw_client"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.SA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.elenZ"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.estart_srl3'"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.infr_sh_wok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.BLKS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.shreg_sub"; "Stdlib.ZArith.Zdiv.Zplus_mod_idemp_l"; "Stdlib.ZArith.BinInt.Z.eq_decidable"; "Stdlib.ZArith.Zdiv.Z_div_plus"; "Stdlib.micromega.RingMicromega.OpGt"; "Stdlib.ZArith.BinInt.Z.gt"; "Stdlib.ZArith.Zdiv.Z_div_plus_full"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.rng_incl"; "Stdlib.Lists.List.incl_refl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.RFO"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.BLKCo"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.BLKSo"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap.CH.hd_img"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8L5DefsA.L5A.aly_static_lo"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.hl_rt_ro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8L5DefsA.L5A.aly_ro_img"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanAcct.segs_below_b"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8L5DefsA.L5A.segs_below"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanAcct.wx_segs_nowrap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8L5DefsA.L5A.wx_nowrap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.GT.SCELLS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.asc_cells"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8L5DefsA.L5A.aly_cells"; "Corelib.Lists.ListDef.Forall_cons"; "Corelib.Lists.ListDef.Forall_nil"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.asc_got_lo"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.GT.GLO"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.GT.GHI"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.asc_got_hi"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8L5DefsA.L5A.aly_got_hi"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8L5DefsA.L5A.aly_got_lo"; "Stdlib.ZArith.BinInt.Z.add_0_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.in_foot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.FOOT"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.inW"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.infr_clientw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.FOOTCL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.ERRNO"; "LinuxProcessSemantics.Riscv.Sem.alu64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.two64"; "Stdlib.ZArith.Zdiv.Zplus_mod_idemp_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.u_lit64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.u_add64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.mkAlu"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.mkAlu_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanPlanCore.APC.eaddz"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanPlanCore.APC.eadd"; "LinuxProcessSemantics.Riscv.Instr.ALU_SUB"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.u_sub64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanPlanCore.APC.esub"; "LinuxProcessSemantics.Riscv.Sem.mul_div"; "Stdlib.ZArith.Zdiv.Zmult_mod_idemp_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.u_mul64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.mkMd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.mkMd_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanPlanCore.APC.escale"; "Stdlib.ZArith.BinInt.Z.ltb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.u64_range"; "Stdlib.ZArith.BinInt.Z.eqb_spec"; "Corelib.Init.Datatypes.reflect"; "Stdlib.ZArith.BinInt.Z.sub_diag"; "Stdlib.ZArith.BinInt.Z.ltb_spec"; "Corelib.Init.Datatypes.BoolSpec"; "Stdlib.ZArith.BinInt.Z.divide"; "Stdlib.ZArith.BinInt.Z.mod_divide"; "LinuxProcessSemantics.Riscv.Instr.ALU_SLTU"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.u_sltu64"; "Stdlib.ZArith.BinInt.Z.opp"; "Corelib.Init.Logic.eq_sym"; "Stdlib.micromega.EnvRing.PEopp"; "Stdlib.ZArith.BinInt.Z.mod_add"; "stdpp.bitvector.definitions.Z_to_bv_unsigned"; "Stdlib.ZArith.Znat.Nat2Z.id"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.ESCV"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.img_clear"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymRun3.kimg_intro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCertA.CCA.vis"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanAcct.mrestrict"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.ahid"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.vis_def"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.At"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.GT.t0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UWL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.client_vis"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.visr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.aclient_scr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCertA.CCA.mem"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.defined_vis"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.wf_frm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmHeapIfaceA.PM_FS_CLASSES"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.ff_remove"; "Stdlib.ZArith.BinInt.Z.div_pos"; "Stdlib.ZArith.BinInt.Z.div_le_upper_bound"; "Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism"; "Corelib.Classes.RelationClasses.eq_Transitive"; "Corelib.Classes.Morphisms.reflexive_proper"; "Corelib.Classes.Morphisms.respectful"; "Stdlib.setoid_ring.Algebra_syntax.equality"; "Stdlib.setoid_ring.Ncring.eq_notation"; "Corelib.Numbers.BinNums.positive"; "Corelib.BinNums.PosDef.Pos.add"; "Stdlib.ZArith.BinInt.Z.pos_sub"; "Stdlib.setoid_ring.Ncring_initial.Zops"; "Corelib.Classes.Morphisms.reflexive_reflexive_proxy"; "Corelib.Classes.Morphisms.reflexive_eq_dom_reflexive"; "Corelib.Classes.RelationClasses.eq_Reflexive"; "Stdlib.setoid_ring.Ncring.ring_plus_comp"; "Stdlib.setoid_ring.Ncring_initial.Zr"; "Corelib.Classes.Morphisms.eq_proper_proxy"; "Stdlib.ZArith.BinInt.Z.div_add_l"; "Stdlib.ZArith.BinInt.Z.mul_comm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmHeapIfaceA.aio_small_high"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.SCFG"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.wf_nodup"; "stdpp.base.NoDup"; "stdpp.base.elem_of"; "stdpp.base.list_elem_of"; "stdpp.list_relations.list.NoDup_cons"; "stdpp.base.list_elem_of_In"; "Stdlib.Lists.List.in_map_iff"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Core.L5C.in_lb_remove_neq"; "Stdlib.ZArith.BinInt.Z.testbit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.ec_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.u32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.u64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.OBJ_JSON_CATEGORY"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.ls_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.img_ro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.atexit_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.foot_pristine"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.loc_done"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.errcat_guard"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.jbit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.convcat_guard"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.cbit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.byte_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.TLO"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.TSH"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5.CL5.kword64_intro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.a_base"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.a_off"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.u64_vis"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.visr_sub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.kword32_intro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.u32_vis"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.kword8_intro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.u8_vis"; "stdpp.bitvector.definitions.Z_to_bv_bv_unsigned"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.shz_intro"; "Stdlib.ZArith.BinInt.Z.div_lt_upper_bound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.byte_vis"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.KZero"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.regs_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_regs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.know_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_know"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.regs_ok_id"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.kentry"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.KImg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.KWr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.KRange"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.KAlign"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.KDisj"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.KUnk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.KBlob"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.KIMG"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.static_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.NF32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.SCOK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.GOTOK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.SLOT2"; "Corelib.Classes.RelationClasses.reflexivity"; "Corelib.Classes.RelationClasses.PreOrder_Reflexive"; "Stdlib.ZArith.BinInt.Z.le_preorder"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.ISH2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.kzero_intro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.vis_allowed"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5.CL5.kwr_intro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5.CL5.krange_intro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5.CL5.kalign_intro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UVP"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5.CL5.kdisj_intro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.VT_VISITOR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UVV"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5.CL5.kunk_intro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UVE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5.CL5.kblob_intro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.bytes_vis"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UVCH"; "stdpp.tactics.f_equal_help"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.akept"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.outside"; "Stdlib.Lists.List.in_app_or"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.WCL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.stksh_rng"; "Corelib.Init.Logic.proj2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.AL8"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.IMG_RO_LO"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.IMG_RO_HI"; "Stdlib.ZArith.ZArith_dec.Z_le_dec"; "Corelib.Init.Specif.sumbool"; "Stdlib.ZArith.ZArith_dec.Z_lt_dec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.GLOC_GUARD"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.GLOC_PTR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.SYSCAT_GUARD"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.NEED_LOCKS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.LOCALE_LOCK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.CONVCAT_GUARD"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibStaticsA.PMTA.C_casan_wf"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibStaticsA.PMTA.consts_wf"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibStaticsA.PMTA.cell_in_foot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.in_tab"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.IMGCL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.blk0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.blk1"; "Stdlib.ZArith.BinInt.Z.log2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.credit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.bufcredA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.bcapI"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.stk_kx"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.scapI"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.stk_bx"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8L5DefsA.L5A.aly_cost"; "Stdlib.ZArith.BinInt.Z.log2_nonneg"; "Stdlib.ZArith.BinInt.Z.mul_nonneg_nonneg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.pstate"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.stk_pot_nonneg"; "Corelib.Init.Logic.iff"; "Stdlib.ZArith.BinInt.Z.mul_add_distr_r"; "Stdlib.ZArith.BinInt.Z.mul_add_distr_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.FIXA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.FIXB"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cutpoint"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.G.CPS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutAuto.CA.dummy_cp"; "Corelib.Lists.ListDef.firstn"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.jrem"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.jremv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.cut_states"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.nl_run"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.text"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.ncons"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.nstc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.cutn"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.nst_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.final_ok"; "LinuxProcessSemantics.Riscv.Instr.aluop"; "LinuxProcessSemantics.Riscv.Instr.mulop"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.szc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.bptrI"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.appk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.sbI"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_set_win"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.parser_sh"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmCurDefs.PMCUR.wf_c"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.WINOK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.not_retreated"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.win_exhausted"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ST_ACCEPT"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmCurDefs.PMCUR.cur_post"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.PnAuxCA.PNX.gE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.ECV"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.curE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.win_okA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmCurDefs.PMCUR.ps_set_more"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmCurDefs.PMCUR.evp"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.FLF"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.kind"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.kind_of"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.AGFIX"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.AGBUF"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.PH0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.auto_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.POSTP"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.APPP"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.PHS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.ENDP"; "Corelib.Lists.ListDef.repeat"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.FR"; "Stdlib.Lists.List.nth_repeat_lt"; "Corelib.Init.Peano.lt"; "Stdlib.ZArith.Znat.Nat2Z.inj_lt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.FFS"; "Stdlib.Lists.List.forallb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutAuto.CA.blocks"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.G.BLS"; "Corelib.Lists.ListDef.seq"; "Corelib.Classes.Morphisms.iff_impl_subrelation"; "Stdlib.Lists.List.forallb_forall"; "Corelib.Init.Nat.add"; "Stdlib.Lists.List.in_seq"; "Stdlib.Arith.PeanoNat.Nat.add"; "Stdlib.ZArith.Znat.Nat2Z.inj_add"; "Stdlib.Lists.List.hd"; "Stdlib.Lists.List.tl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.KSm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.mem"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.aamb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.G.HDECL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.Cred"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.amodel_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.model_rt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymRun3.env_agree"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.ri_inv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.curB"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.curF"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.ffroom"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.FE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.den"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.bls_i"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.denF"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.ffs_i"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.rf_frm"; "Stdlib.ZArith.BinInt.Z.eqb_refl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.mod8_of_64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.FLE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SegRun.SR.post_spec"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.Lists.List.nth_error"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_nx"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCertA.CCA.leaf_factsA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutBridgeA.CBA.leaf_agree0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.G.NF_le"; "Stdlib.Arith.PeanoNat.Nat.leb"; "Stdlib.Arith.PeanoNat.Nat.leb_le"; "Stdlib.Lists.List.nth_error_nth"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.eb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SegRun.SR.ps_cells"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutLib.CL.ps_reg_is"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.outU"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.lf_cells"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCertA.CCA.lfa_vis"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutLib.CL.ps_reg_is_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCertA.CCA.lfa_frame"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.cpf_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_F"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.G.CPS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.cpf_all"; "Stdlib.Lists.List.nth_error_In"; "Stdlib.Lists.List.existsb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.region_eqb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.UREGS"; "Stdlib.Lists.List.Forall_forall"; "Stdlib.Lists.List.existsb_exists"; "Corelib.Init.Datatypes.andb_prop"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.expr_eqb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.expr_eqb_eq"; "Stdlib.ZArith.BinInt.Z.eqb_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.PE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.FE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.SRL3"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.SBz"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.FLR"; "Corelib.Init.Logic.f_equal"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.FLE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SegPlan.SGP.outside"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.PS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.out"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.u64_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.u32_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.u8_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.lstr_short_nil_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.bytes_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.SAFE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.FRM"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmHeapIfaceA.aio_wf"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmHeapIfaceA.shadow_blk_w"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.ar_stack_bottom"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.shadow_apart"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.apart"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.STATIC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.ls_ok_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.STATIC_lo"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.PTKF"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.ec_at_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.EC_mv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.LS_mv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.regJ_nz"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.F0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.FRM3"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.CPF_N"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.CPF_NM"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.CPF_MM"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.MORE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.CPF_E"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.CPF_X"; "Stdlib.Lists.List.nth_error_Some"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.len_cps"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.blocks_vars_lt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.G.BLS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.blv_all"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.den_agree"; "LinuxProcessSemantics.Riscv.Prelude.sext"; "LinuxProcessSemantics.Riscv.Sem.alu32"; "LinuxProcessSemantics.Riscv.Sem.low32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.ext_val"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.blob_val"; "stdpp.bitvector.definitions.BvWf"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.subst"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.is_leaf"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.G.TAGS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.TGoto"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.tag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_PSS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.leaves_all_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.G.TAGS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.leaf_chkA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.GT.NF"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.G.HDECL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.heap_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.foot_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.blocks_eqb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.bsubst"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.frames_eqb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.fsubst"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.env_over"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.blocks_eqb_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.den_bsubst"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.leaf_facts"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.GBLK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.BLKAG"; "Stdlib.Arith.PeanoNat.Nat.ltb_spec"; "Stdlib.Arith.PeanoNat.Nat.ltb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.slook"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.prove"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanPlanCore.APC.fact_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.PsKitA.PPVA.prove3"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanPlanSound.APS.fact_ok_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.PsKitA.PPVA.prove3_sound"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.Z_to_le_bytes"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.bytes_le_to_Z"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.bytes_le_Z_to_le"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanAcct.H_off_segments"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.u8_full"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.kword8_elim"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.u64_full"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.kword64_elim"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutAutoX.CAX.cell_at"; "Stdlib.Lists.List.find"; "Stdlib.Arith.PeanoNat.Nat.eqb"; "Stdlib.Lists.List.find_some"; "Stdlib.Arith.PeanoNat.Nat.eqb_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.KFill"; "Corelib.Init.Datatypes.list_ind"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.nl_step"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.zseq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.step_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.zseq_in"; "Corelib.Classes.RelationClasses.symmetry"; "Corelib.Classes.RelationClasses.eq_Symmetric"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.mod_neg64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.rng_is"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutOps.CX.range3"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutOps.CX.range3_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.lo_ge"; "Stdlib.ZArith.BinInt.Z.leb"; "Stdlib.ZArith.BinInt.Z.leb_le"; "Corelib.Init.Datatypes.comparison"; "Stdlib.ZArith.BinInt.Z.compare"; "Corelib.Init.Datatypes.Gt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.named_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.rng_is_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.uv_esub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.uv_eaddz"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.mod64_zero"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UVR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.flat_u"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutOps.CX.wle1_byte"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.CUR0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.WLEN"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.WEND"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.NST0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.SIZE0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.BX"; "Stdlib.ZArith.BinInt.Z.add_mod_idemp_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.FRZ"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.minus_fam"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.JV"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.CUR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.CURMOD"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.content_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.has_cell"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UCUR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.lo_ge_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.named_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5.CL5.kblob_elim"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.has_cell_In"; "Stdlib.Lists.List.Forall_nth"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.u8_inj"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.step_chk_sound"; "Corelib.Init.Logic.iff_sym"; "Stdlib.ZArith.Znat.Nat2Z.inj_iff"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.nl_run_app"; "Stdlib.Lists.List.app_assoc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.firstn_succ"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.PnAuxCA.PNX.bls_pre"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.NX56"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.JREM_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.KDecl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCertA.CCA.AtV"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.XI"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.LEAFK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.over_ge"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.BLPRE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.SAFEOUT"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.AGFIX_mv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.AGBUF_mv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.PH0_mv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.POUT"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.OUT_N"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.AUTO_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.esubstL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.esubstL_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.leaf_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.goto_common"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.NCUT"; "Corelib.Init.Datatypes.orb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.kind_eqb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.goto_decl_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.KRetx"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.goto_retx_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutBridgeA.CBA.regions_eqb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.cpf_of_kind"; "Corelib.Init.Datatypes.negb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutBridgeA.CBA.regions_eqb_eq"; "Stdlib.Arith.PeanoNat.Nat.ltb_lt"; "Stdlib.Bool.Bool.orb_prop"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.jtgt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.isSome"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.entry_states"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.KEntry"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.KAppr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.KErrh"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.KSetec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.KEnd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.DECL_CORE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.uv_over"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.content_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.mod64_sub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.existsb_eqb_in"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.NUMP"; "Stdlib.Lists.List.app_nil_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.kind_eqb_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmCurDefs.PMCUR.ICS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmCurDefs.PMCUR.lvl_ok"; "Corelib.Init.Nat.min"; "Stdlib.Arith.PeanoNat.Nat.min"; "Stdlib.Arith.PeanoNat.Nat.min_l"; "Stdlib.Lists.List.length_firstn"; "Stdlib.Lists.List.length_app"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.szok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.exit_exh"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.exit_err"; "Stdlib.Arith.PeanoNat.Nat.eqb_spec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.G.RETS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.ret_of_kind"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.G.RETS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.PC_SM"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.PC_APPR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.PC_ERRH"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.PC_SETEC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutBridgeA.CBA.amb_off"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.LYB"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5LazyA.L5LZ.sbm_ahid"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCertA.CCA.lfa_sbm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCertA.CCA.lfa_grows"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.PDEFM"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.PROVE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.SUBR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.str_long_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.shadow_blk_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmHeapIfaceA.shadow_cont"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.RD8"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.cell_at_has"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.uv_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.EAluw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.EMdw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.EExt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.EBlob"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanPlanCore.APC.expr_vars_lt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.text_len"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.nst_rng"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.cur_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.PSX"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.shadow_cont_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.WF_mk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.lvl_upd"; "Stdlib.ZArith.BinInt.Z.eq_dec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.CurKitCA.CKA.cur_post_more"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.CurKitCA.CKA.cur_post_err"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.SAFE2"; "Corelib.Init.Logic.and_ind"; "Corelib.Init.Logic.or_ind"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanPlanCore.APC.NCS"; "Stdlib.Arith.PeanoNat.Nat.sub"; "Stdlib.ZArith.Znat.Nat2Z.inj_sub_max"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.SAFEOUT2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.OUT_E"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.u8"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.def_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.defined_sub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.CurKitCA2.CKA2.evp_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmCurDefs.PMCUR.sevent"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmCurDefs.PMCUR.ev_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmCurDefs.PMCUR.ev_rel"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.CurKitCA.CKA.cur_post_event"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.CurKitCA2.CKA2.wf_c_set_win"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.CurKitCA2.CKA2.set_more_set_win"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.CurKitCA2.CKA2.ev_rel_set_win"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.PA_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.CurKitCA2.CKA2.cur_post_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.TOther"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCertA.CCA.leaf_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.AMBX"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.fp_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.row"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.r_sid"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.r_j"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.r_i"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.ROWS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.SID"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.RETPC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.PC_ENDI"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.PC_ENDF"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutBridgeA.CBA.exit_base_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.reg_of"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.call_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.find_row"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SegRun.SR.ps_pc"; "Stdlib.Bool.Bool.eqb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.row_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.mvar"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.KZB"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.TLO"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.TG"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.KZT"; "Stdlib.ZArith.BinInt.Z.eqb_neq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.find_row_In"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.r_pc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.rows_ok2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.rows_leaf"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.LYI"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.LYR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.LYN"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.STKF"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.SCRP"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.WINC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.WOKo"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.WRS_OK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.CH"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.TSH"; "Corelib.Init.Datatypes.Lt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShB.CSL1.site_chk1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.r_rd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.r_rs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.sites_ok_In"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.sites"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShA.CSL.shl_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.r_cur"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.r_a"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.r_b"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.goto_amb_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.r_tab"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.tab_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.text_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutShC.CSLR.ROW"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.TADDR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.SID_id"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.LEAF"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.KRETX47"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.retx_nth"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.CP"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SegRun.SR.PS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SegRun.SR.region"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_D.cp47"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.FPState"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCertA.CCA.IH"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.meas"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SpinAlg.srealizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.mkst"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.seg_rom"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutRtA.CRA.exit_retire"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.DEF0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.EV0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutLib.CL.is_ret_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.ret_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.retire_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.retx_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.regs_preserved"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.ahpres"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.OUT_X"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.POSTP_mv"; "Corelib.Classes.Morphisms.flip2"; "Corelib.Program.Basics.impl"; "Corelib.Classes.Morphisms.iff_flip_impl_subrelation"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.pcredit_bufcred"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.reg_of_is"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.SAFE0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.in_shadow_mono"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.ret_of"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.cinfo"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.custom_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.GT.SCELLS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.GT.GLO"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.GT.GHI"; "Stdlib.Lists.List.filter"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.sm_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.ci_nx"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.ci_csp"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.callee"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.NEWS_F"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.EE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.SETEC_W"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.STR_W"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.STR_NEWS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.gof"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.size_of"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.END_W"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.ENDE_W"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.END_NEWS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.VE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.ret_of"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.IMGHI"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.PsSmA.CRX.smalloc_leaf_x"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.CRS_OKo"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.IMG_OK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.ISHL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.SMUSER"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.hl_scr_stack_malloc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.hl_stack_malloc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.static_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutRtA.CRA.smalloc_fact_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.ambX"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutRtA.CRA.mem"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutRtA.CRA.sm_facts"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.retEx"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8L5DefsA.L5A.aly_scr_sm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.PC_SM"; "Stdlib.Lists.List.filter_In"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.BLK0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SegRun.SR.edenot_agree_AP"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.BLK48"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.cell_is"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.aheap_pres"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.retEx_agree"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.retEx_a0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.retEx_ghost"; "Stdlib.Arith.PeanoNat.Nat.add_0_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.ISH2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.env_agree_trans"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.ACL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.SAFEOUT0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.OUT_0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.aclient_incl"; "Stdlib.Lists.List.incl_tl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.K48"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.fs_vis"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmHeapIfaceA.aio_flagptr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.wf_fs_def"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.vis_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.stksh"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.stksh_mono"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.stksh_ag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.KSTK"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment"; "Stdlib.ZArith.BinInt.Z.of_N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_readable"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.segment_read_bytes"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_bytes"; "Stdlib.ZArith.BinInt.Z.to_N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_base"; "Stdlib.NArith.BinNat.N.to_nat"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanAcct.find_segment1_none_above"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.STCL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.CSET"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.OSET"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.FIX_CSET"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.PHS_mv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.vml"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.PnAuxCA.PNX.flc_all"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.vis_off_segments"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.PnAuxCA.PNX.retbls_k"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.PHASE_X"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.KEEP_PH"; "Stdlib.ZArith.BinInt.Z.ltb_lt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.RETBLS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.PHASE0_X"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutBridgeA.CBA.callee_leaf"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.common_facts"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutBridgeA.CBA.mem"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutBridgeA.CBA.cps_asanG"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_pc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.ci_regs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutAuto.CA.ps_reglist"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanPlanCore.APC.sr_vars_lt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanPlanCore.APC.kn_vars_lt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.ra_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.ffrs"; "Stdlib.ZArith.Zdiv.Z_div_mult"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.mem"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.a1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.ainfr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.u32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.a0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.estart_srl3"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.u8_byte_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.U8DEF"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.kword32_elim"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.u32_full"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.env_agree_le"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.RBLK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.ACLI"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.KEEP_FS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.OSET_CSET"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.NEWSF"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.FL64"; "LinuxProcessSemantics.Riscv.Instr.ALU_SLL"; "LinuxProcessSemantics.Riscv.Instr.ALU_SLT"; "LinuxProcessSemantics.Riscv.Instr.ALU_XOR"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRA"; "LinuxProcessSemantics.Riscv.Instr.ALU_OR"; "LinuxProcessSemantics.Riscv.Instr.ALU_AND"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.fobj"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.stksh"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.SETEC_SCR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.ls_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.ec_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.STKSH"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.OSET_OUT"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.GD"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.AXT"; "Stdlib.ZArith.Zbitwise.Z.add_lor_land"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.ones"; "Stdlib.ZArith.BinInt.Z.land_ones"; "Stdlib.ZArith.BinInt.Z.div_le_mono"; "Stdlib.ZArith.BinInt.Z.div_add"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.lor7"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.grow_cap"; "Stdlib.ZArith.BinInt.Z.div_le_compat_l"; "Stdlib.ZArith.BinInt.Z.div_div"; "Stdlib.ZArith.BinInt.Z.div_le_lower_bound"; "Stdlib.micromega.EnvRing.Pinj"; "Stdlib.micromega.EnvRing.PX"; "Stdlib.ZArith.BinInt.Z.log2_le_mono"; "Stdlib.ZArith.BinInt.Z.log2_double"; "Stdlib.ZArith.BinInt.Z.succ"; "Stdlib.ZArith.BinInt.Z.mul_div_le"; "Stdlib.micromega.RingMicromega.PsatzLet"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.acredit_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.adebit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.grow_cap_facts"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.log2_halves"; "Stdlib.micromega.RingMicromega.PsatzSquare"; "Stdlib.ZArith.BinInt.Z.mul_le_mono_nonneg_l"; "Stdlib.ZArith.BinInt.Z.mul_le_mono_nonneg_r"; "Stdlib.ZArith.BinInt.Z.mul_succ_l"; "Corelib.Lists.ListDef.skipn"; "Stdlib.Lists.List.length_skipn"; "Stdlib.ZArith.BinInt.Z.min"; "Stdlib.ZArith.Znat.Nat2Z.inj_min"; "Stdlib.ZArith.BinInt.Z.min_spec"; "Stdlib.Lists.List.nth_skipn"; "Stdlib.Lists.List.nth_firstn"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.sr_vars_lt_forallb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SegRun.SR.ps_regs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutAuto.CA.ps_reg"; "Stdlib.Lists.List.in_map"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.common_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutAuto.CA.regs_eqb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanPlanCore.APC.sr_fresh"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanPlanCore.APC.caller_saved"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap2.CH2.blk_in"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.frames_vars_lt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.frm_in"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.kept_chk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.PnAuxCA.PNX.retbls_s"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.PnAuxCA.PNX.gA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.BUFM"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UV_esub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UV_eadd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.MODB"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.a2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.str_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.APPR_SCR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.str_src_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.str_grownA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.aacc"; "Corelib.Classes.Morphisms.Reflexive_partial_app_morphism"; "Corelib.Program.Basics.flip"; "Corelib.Classes.RelationClasses.flip_Reflexive"; "Corelib.Classes.RelationClasses.impl_Reflexive"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.bytes_sub"; "Stdlib.Lists.List.skipn_0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.defined_same"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutRtCpsA.CRC.aacc_blk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.nodup_notin"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.bufcredA_push"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UV_mul2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.ACLX"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.FIX_OUT224"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL3"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL4"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL5"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL6"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL7"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL8"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL9"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL10"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL11"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL12"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL13"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL14"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL15"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL16"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL17"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL18"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL19"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL20"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL21"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL22"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL23"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL24"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL25"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL26"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL27"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL28"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL29"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL30"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL31"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL33"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL34"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL35"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL36"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL37"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL38"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL39"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL40"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL41"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL42"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL43"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL44"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL45"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL46"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_T.BL47"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p0.BL48"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p0.BL49"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p0.BL50"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p0.BL51"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p0.BL52"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p0.BL53"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p0.BL54"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p0.BL55"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p1.BL56"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p1.BL57"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p1.BL58"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p1.BL59"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p1.BL60"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p1.BL61"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p1.BL62"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p1.BL63"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R1p2.BL64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R2p0.BL65"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R2p0.BL66"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R2p0.BL67"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R2p0.BL68"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R2p0.BL69"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R2p0.BL70"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R2p0.BL71"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R2p0.BL72"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_pn_casan_R2p1.BL73"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UV_escale2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UV_eaddz"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.PC_ENDI"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.W_parAc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.PC_ENDF"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.cps_asan"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.ENDNUM_SCR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.std_args"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.num_final"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.parser_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.parser_sh"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmCurDefs.PMCUR.wf_c_stale"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.win_okA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.buf_bound_stale"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.vis_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.ENDW"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.STRS_mv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.ENDX_OK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.vis_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.wf_ps_stale"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ps_set_nst"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.KSHO"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberChkCA.PNA.ERRNO"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefsA.PMLA.W_parA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.W_parE_app"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ST_DONE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibDefs.PML.ws_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmCurDefs.PMCUR.evp_mono"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmCurDefs.PMCUR.win_le"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.ACLP"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.cfg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.PC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CatSim.msteps"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeapA.CHA.cert_soundA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.plan_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.G.plans"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.G.tags_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.GK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.G_CRED"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.G_DECL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.G_RETX_END"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.G_RETX"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.L_EXIT"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.L_SM"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.L_ERRH"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.L_SETEC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.L_APPR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.L_END"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.L_CSL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.G.cp0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.At0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5LazyA.L5LZ.sbm_model_rt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanAcct.same_but_materialized_refl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.env_agree_refl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.UVBP"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.ffs_0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PnMain.XI0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit.PtKitA.PTA.defined_bytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Core.L5C.bytes_at_rdn"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.bytes_le_to_Z_bound"; "Stdlib.Lists.List.length_map"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanPlanSoundSums.APSX.word_to_le_bytes_of_bytes_n"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.Ex.ex_un"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutL5A.CL5A.bytes1"; "Stdlib.Lists.List.length_seq"; "Stdlib.Lists.List.seq_nth"; "Stdlib.Lists.List.map_nth"; "Stdlib.Lists.List.nth_indep"; "stdpp.bitvector.definitions.bv_unsigned_in_range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.ScfgP"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.asan_layout"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.asan_run"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.asan_statics_cells"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.asan_iface"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.IcptIfaceA.icpt_layout"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmHeapIfaceA.asan_iface_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8L5DefsA.L5A.as0_layout"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.IcptIfaceA.rt_img_shadow"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.IcptIfaceA.icl_poison"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.str_append_range_specA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.PC_APPR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.end_integer_value_specA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.end_fraction_value_specA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.errh_specA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.PC_ERRH"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.set_ec_specA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.PNA0.PC_SETEC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.pstate"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.ShapeAlg.TSet"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.PF_SCR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.cur_args"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.a3"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.ex_u32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.ex_u64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.ex_u8"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.defined_bytes_r"; "Stdlib.ZArith.Znat.Z2Nat.id"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.ParseNumberCA.main"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmLibSpecsA.PMSA.parse_number_specA"].

Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module GT := PNA.GT.
Module G := PNA.G.
Abbreviation RSEGS := Pm8PlanKit.RSEGS.
Abbreviation mem := (word -> option byte).

Module PNA0.
Definition PC : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_001 ())).
Definition PC_SM : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_002 ())).
Definition PC_APPR : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_003 ())).
Definition PC_ENDI : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_004 ())).
Definition PC_ENDF : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_005 ())).
Definition PC_SETEC : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_006 ())).
Definition PC_ERRH : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_007 ())).
Definition RETPC : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_008 ())).
Definition SBz : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_009 ())).
Definition IMGHI : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_010 ())).
Definition SLOT2 : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_011 ())).
Definition ISH2 : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_012 ())).
Definition TLO : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_013 ())). Definition TSH : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_014 ())).
Definition GD : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_015 ())).
Definition AXT : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_016 ())).
Definition ERRNO : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_017 ())).
Definition SCR : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_018 ())).

Definition PE := EVar 10. Definition CUR0 := EVar 11. Definition VE := EVar 12. Definition EE := EVar 13.
Definition WLEN := EVar 32. Definition BX := EVar 33. Definition K0 := EVar 34. Definition SIZE0 := EVar 35. Definition P0 := EVar 36. Definition SBX := EVar 37. Definition SLEN := EVar 38.
Definition SCAP := EVar 39. Definition LVL := EVar 40. Definition SST0 := EVar 41. Definition NST := EVar 42. Definition DONE := EVar 43. Definition CP0 := EVar 44. Definition CP20 := EVar 45.
Definition POS0 := EVar 46. Definition CH := EVar 47. Definition ESC0 := EVar 48. Definition FLE := EVar 50. Definition JV := EVar 51. Definition FE := EVar 55. Definition BYTE := EVar 73.
Definition WEND : expr := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_019 ())).
Definition CUR : expr := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_020 ())).
End PNA0.
Import PNA0.

Definition hid (P : Prop) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs1.kr_b_021 ())).

Lemma kword32_intro : forall segs E (M : mem) a v A z, estart E a = A -> 0 <= A -> A + 4 <= 2 ^ 64 -> edenot E v = Z_to_bv 64 z ->
  L5.u32_at segs M A z -> kentry_ok segs E M (KWord a 4 v).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_022 ())).
Qed.

Lemma regJ_nz : forall g0, PML.regJ g0 <> PML.LS0.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_023 ())).
Qed.

Section PnMain.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Variable IL0 : icpt_layout.
Abbreviation IC := PMLA.C_casan.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis ISH : rt_img_shadow L IL0 HI.
Hypothesis POI2 : Forall (fun r : Z * Z => SLOT2 + 8 <= fst r \/ snd r <= SLOT2) (icl_poison IL0).
Hypothesis POI_TAB : Forall (fun r : Z * Z => TLO + 264 <= fst r \/ snd r <= TLO) (icl_poison IL0).
Hypothesis FOOTC : forall a, PMLA.in_foot IC a -> ~ hl_rt_static L a.
Hypothesis SM1 : hl_stack_malloc L 1 = PC_SM.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis APPR_OK : PMSA.str_append_range_specA L ar HI PC_APPR.
Hypothesis ENDI_OK : PMSA.end_integer_value_specA L ar HI IC PC_ENDI.
Hypothesis ENDF_OK : PMSA.end_fraction_value_specA L ar HI IC PC_ENDF.
Hypothesis ERRH_OK : PMSA.errh_specA L ar HI PC_ERRH.
Hypothesis SETEC_OK : PMSA.set_ec_specA L ar HI IC PC_SETEC.
Hypothesis TPV : hl_tp L = 6883920.
Hypothesis ERRNO_OK : forall a, ERRNO <= a < ERRNO + 4 -> ~ hl_rt_static L a.

Variables (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r P V E B kx bx : Z) (g : PML.ls_state) (ps : PML.pstate).
Variables (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : TSet).
Variables (p e : Z).
Let LB := PML.ps_blocks ps ++ LBo.
Hypothesis HH : ri_inv HI LB FF LK cr A M (vml_of model).
Hypothesis Hmo : CHA.amodel_ok A model.
Hypothesis HKnil : K [].
Hypothesis Hfp : PMSA.fp_ok fx.
Hypothesis Hra : getr R 1%bv = Z_to_bv 64 r.
Hypothesis Hraok : L5.ra_ok r.
Hypothesis Hsp : getr R 2%bv = Z_to_bv 64 sp.
Hypothesis Htp : getr R 4%bv = Z_to_bv 64 (hl_tp L).
Hypothesis Hstk : CHA.astk ar M sp SCR.
Hypothesis Hroom : CHA.ffroom FF LK 5.
Hypothesis Hffrs : CHA.ffrs FF sp.
Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 P.
Hypothesis Ha1 : getr R 11%bv = Z_to_bv 64 p.
Hypothesis Ha2 : getr R 12%bv = Z_to_bv 64 V.
Hypothesis Ha3 : getr R 13%bv = Z_to_bv 64 E.
Hypothesis Hwin : PML.ps_win ps = Some (p, e).
Hypothesis HMORE : PML.ps_more ps = true.
Hypothesis HST : PML.ps_st ps = PML.ST_NUMBER.
Hypothesis Hsp32 : sp mod 32 = 0.
Hypothesis Hstksh : PMLA.stksh ar M sp SCR.
Hypothesis HPA : PMLA.parser_at (hl_segs L) IC M P ps.
Hypothesis HPSH : PMLA.parser_sh M ps.
Hypothesis HWF : PML.wf_ps ps.
Hypothesis HLV : PMCUR.lvl_ok ps.
Hypothesis HWIN : PMLA.win_okA M LBo ps.
Hypothesis HBB : PML.buf_bound ps B.
Hypothesis HVIS : PMLA.vis_at (hl_segs L) IC M V.
Hypothesis HEC : PMLA.ec_at (hl_segs L) IC M E 0.
Hypothesis HLS : PMLA.ls_ok (hl_segs L) IC g M.
Hypothesis HG : g <> PML.LS0.
Hypothesis HPC : PMLA.pcredit_xA L cr ps kx bx.
Hypothesis OP : PMLA.fobj M FF P 272.
Hypothesis OV : PMLA.fobj M FF V 48.
Hypothesis OE : PMLA.fobj M FF E 16.
Hypothesis AP1 : PMLA.apart P 272 V 48.
Hypothesis AP2 : PMLA.apart P 272 E 16.
Hypothesis AP3 : PMLA.apart V 48 E 16.

Variables (cp0 cp20 pos0 esc0 ch : Z) (winb : list Z).
Hypothesis Hcp0 : L5.u32_at (hl_segs L) M (P + 148) cp0.
Hypothesis Hcp20 : L5.u32_at (hl_segs L) M (P + 152) cp20.
Hypothesis Hpos0 : L5.u64_at (hl_segs L) M (P + 168) pos0.
Hypothesis Hesc0 : L5.u8_at (hl_segs L) M (P + 220) esc0.
Hypothesis Hcpr : 0 <= cp0 < 2 ^ 32 /\ 0 <= cp20 < 2 ^ 32 /\ 0 <= pos0 < 2 ^ 64 /\ 0 <= esc0 < 2 ^ 8.
Hypothesis Hwinb : L5.bytes_at (hl_segs L) M p winb /\ Z.of_nat (length winb) = e - p.
Hypothesis HCH : In (ch, 16384) LBo /\ ch <= p /\ e <= ch + 16384 /\ L5.defined M p (e - p) /\ shadow_blk M ch 16384.

Hypothesis Hcont : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range)
   (LK' : list fframe) (A' : list (Z * Z)),
   PMSA.fp_ok fx' ->
   (exists (ps' : PML.pstate) (code : Z) (g' : PML.ls_state),
      PMLA.parser_at (hl_segs L) IC M' P (PML.ps_set_win ps' (PML.ps_win ps)) /\ PMLA.parser_sh M' ps' /\ PMCUR.wf_c ps' /\ PMLA.win_okA M' LBo ps' /\ PML.buf_bound ps' B /\
      PMLA.ec_at (hl_segs L) IC M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
      PMLA.ls_ok (hl_segs L) IC g' M' /\ (g' = g \/ (g' = PML.regJ g /\ code <> 0)) /\
      LB' = PML.ps_blocks ps' ++ LBo /\ LBk = LBo /\ W = PMSA.W_parEc L IC P V E /\ PMLA.pcredit_xA L cr' ps' kx bx /\
      (PMSA.not_retreated ps ps' /\ (exists p' e', PML.ps_win ps' = Some (p', e') /\ getr R' 10%bv = Z_to_bv 64 p') /\
       (code = 0 -> PML.ps_level ps' = PML.ps_level ps /\ (PML.ps_st ps' = PML.ST_NUMBER -> PMSA.win_exhausted ps') /\
                    In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_ACCEPT; PML.ST_EXPECT_COMMA_OR_END])) /\
      PMCUR.cur_post (hl_segs L) ps ps' code M' V) ->
   regs_preserved R R' -> CHA.ahpres L ar LBk FF sp SCR W M M' -> model_rt model model' -> incl A A' -> CHA.amodel_ok A' model' -> incl LK' LK ->
   ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
   srealizes (hl_segs L) SCFG (@PMSA.cfg L fx' R' r M' model') K.

Let LEAFOK : forall i c k ps0 t, CH2.is_leaf G.CPS G.TAGS i c k ps0 t -> PNA.leaf_chk i c k ps0 t = true := PNL.LEAFOK_all.

Hypothesis Hwinr : Forall (fun c => 0 <= c < 256) winb.

Let wlen := e - p.
Let bcap := PML.ps_bcap ps.
Let k0 := bcap / 2.
Let bptr := PML.ps_bptr ps.
Let buf := PML.ps_buf ps.
Let size0 := Z.of_nat (length (PML.ps_buf ps)).
Let sb := PML.ps_sb ps.
Let scap := PML.ps_scap ps.
Let stack := PML.ps_stack ps.
Let slen := Z.of_nat (length (PML.ps_stack ps)).
Let level := PML.ps_level ps.
Let sst0 := PML.ps_sst ps.
Let nst := PML.ps_nst ps.
Let done := PML.b2z (PML.ps_done ps).

Definition E0 : env := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_024 ())).
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.

Lemma PAR : L5.u64_at (hl_segs L) M P (PMLA.VT_PARSER IC) /\ L5.u32_at (hl_segs L) M (P + 8) 1024 /\
  L5.u8_at (hl_segs L) M (P + 12) 0 /\ L5.u8_at (hl_segs L) M (P + 13) 1 /\ L5.u8_at (hl_segs L) M (P + 14) 0 /\ L5.u8_at (hl_segs L) M (P + 15) 1 /\
  L5.u8_at (hl_segs L) M (P + 16) 0 /\ L5.u8_at (hl_segs L) M (P + 17) 0 /\ L5.u8_at (hl_segs L) M (P + 18) 0 /\
  L5.lstr_short (hl_segs L) M (P + 24) [] /\ L5.lstr_short (hl_segs L) M (P + 48) [] /\ L5.lstr_short (hl_segs L) M (P + 72) [] /\
  L5.u64_at (hl_segs L) M (P + 96) (PMLA.VT_FUNC IC) /\ L5.u64_at (hl_segs L) M (P + 128) (P + 96) /\ L5.u32_at (hl_segs L) M (P + 144) level /\
  (L5.u64_at (hl_segs L) M (P + 200) p /\ L5.u64_at (hl_segs L) M (P + 192) e /\ p <= e) /\
  L5.u8_at (hl_segs L) M (P + 208) 17 /\ L5.u8_at (hl_segs L) M (P + 209) sst0 /\ L5.u8_at (hl_segs L) M (P + 210) nst /\ L5.u8_at (hl_segs L) M (P + 211) 1 /\
  L5.u8_at (hl_segs L) M (P + 212) done /\ L5.u8_at (hl_segs L) M (P + 213) 1 /\ L5.u32_at (hl_segs L) M (P + 216) 0 /\
  PMLA.str_at (hl_segs L) M (P + 224) (PML.SLong bcap bptr buf) /\ 264 <= bcap /\
  L5.u64_at (hl_segs L) M (P + 248) sb /\ L5.u64_at (hl_segs L) M (P + 256) (sb + slen) /\ L5.u64_at (hl_segs L) M (P + 264) (sb + scap) /\
  L5.bytes_at (hl_segs L) M sb stack /\ slen <= scap /\ L5.defined M P 272.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_025 ())).
Qed.

Lemma PDEFM : L5.defined M P 272.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_026 ())).
Qed.

Lemma WFX : 0 <= sst0 <= 11 /\ 0 <= nst <= 7 /\ 1 <= slen <= 1027 /\ In scap [66; 132; 264; 528; 1056] /\ 66 <= scap <= 1056 /\ slen <= scap /\ 0 <= level <= 1024 /\ 0 <= done <= 1.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_027 ())).
Qed.

Lemma NUMP : PML.num_prefix nst buf.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_028 ())).
Qed.
Lemma ESCN : 0 <= PML.esc_need sst0 <= 3.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_029 ())).
Qed.
Lemma BBX : size0 + wlen <= B /\ B < 2 ^ 26 /\ 0 <= wlen /\ p <= e.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_030 ())).
Qed.
Lemma BCX : bcap mod 8 = 0 /\ 264 <= bcap <= 2 ^ 27 /\ size0 < bcap /\ bcap = 2 * k0 /\ 132 <= k0 <= 2 ^ 26.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_031 ())).
Qed.

Ltac pose_facts :=
  pose proof (L5A.aly_segs L C LAY) as LS; pose proof (L5A.aly_img_lo L C LAY) as ILO; pose proof (L5A.aly_img_hi L C LAY) as IHI;
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WFT; pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFT) as RFx;
  pose proof (CHA.rf_ceil _ _ _ _ RFx) as RC; destruct RC as (CL & C8); pose proof (CHA.rf_sptop _ _ _ _ RFx) as RS; destruct RS as (SP1 & SP16);
  pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WFT) as STOP;
  pose proof Hstk as Hstk'; destruct Hstk' as (S1 & S2 & S3 & S4 & S5 & S6); unfold SCR in S2, S5;
  pose proof OP as OP'; destruct OP' as (Pfr & P8 & Psh); pose proof OE as OE'; destruct OE' as (Efr & E8 & Esh); pose proof OV as OV'; destruct OV' as (Vfr48 & V8 & Vsh6);
  assert (Vfr : CL5A.ainfr FF V 8) by (destruct Vfr48 as (fvv & Hfvv & Fvv1 & Fvv2); exists fvv; split; [exact Hfvv | split; lia]);
  assert (Vsh : shadow_zero M V (8 / 8)) by (intros jj Hjj; apply Vsh6; change (8 / 8) with 1 in Hjj; change (48 / 8) with 6; clear - Hjj; lia);
  pose proof (CL5A.infr_rng L ar LB FF P 272 RFx Pfr ltac:(clear; lia)) as OO; destruct OO as (O1 & O2 & O3 & O4 & O5 & O6 & O7);
  pose proof (CL5A.infr_rng L ar LB FF E 16 RFx Efr ltac:(clear; lia)) as QQ; destruct QQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7);
  pose proof (CL5A.infr_rng L ar LB FF V 8 RFx Vfr ltac:(clear; lia)) as VRR; destruct VRR as (VR1 & VR2 & VR3 & VR4 & VR5 & VR6 & VR7);
  pose proof (CL5A.infr_rng L ar LB FF V 48 RFx Vfr48 ltac:(clear; lia)) as VQQ; destruct VQQ as (VQ1 & VQ2 & VQ3 & VQ4 & VQ5 & VQ6 & VQ7);
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in VQ1, VQ2, VQ3, VQ4, VQ5, VQ6, VQ7; change (hid (V + 48 <= 2147446784 \/ 17594333495296 <= V)) in VQ5;
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in O1, O2, O3, O4, O5, O6, O7, Q1, Q2, Q3, Q4, Q5, Q6, Q7, VR1, VR2, VR3, VR4, VR5, VR6, VR7;
  change (hid (P + 272 <= 2147446784 \/ 17594333495296 <= P)) in O5; change (hid (P + 272 <= hl_img_lo L \/ hl_img_hi L <= P)) in O7;
  change (hid (E + 16 <= 2147446784 \/ 17594333495296 <= E)) in Q5; change (hid (E + 16 <= hl_img_lo L \/ hl_img_hi L <= E)) in Q7;
  change (hid (V + 8 <= 2147446784 \/ 17594333495296 <= V)) in VR5; change (hid (V + 8 <= hl_img_lo L \/ hl_img_hi L <= V)) in VR7;
  assert (FSLO : 7024640 <= ar_fs ar) by (destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [unfold FS_BYTES in A4; rewrite ILO in A4; clear - A0' A4; lia | rewrite IHI in A4; exact A4]);
  assert (INB : In (bptr, bcap) LB) by (unfold LB, PML.ps_blocks; left; reflexivity);
  assert (INS : In (sb, scap) LB) by (unfold LB, PML.ps_blocks; right; left; reflexivity);
  assert (INC : In (ch, 16384) LB) by (unfold LB; apply in_or_app; right; exact (proj1 HCH));
  pose proof (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (bptr, bcap) INB) as KBB; destruct KBB as ((KB0 & KB1 & KB16 & KB3 & KB4 & (KB5 & KB6 & KB7)) & KBdef & KBsha & KBbap & KBfap);
  cbn [fst snd] in KB0, KB1, KB16, KB3, KB4, KB5, KB6, KB7, KBdef, KBsha, KBbap, KBfap;
  pose proof (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (sb, scap) INS) as KSS; destruct KSS as ((KS0 & KS1 & KS16 & KS3 & KS4 & (KS5 & KS6 & KS7)) & KSdef & KSsha & KSbap & KSfap);
  cbn [fst snd] in KS0, KS1, KS16, KS3, KS4, KS5, KS6, KS7, KSdef, KSsha, KSbap, KSfap;
  pose proof (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (ch, 16384) INC) as KCC; destruct KCC as ((KC0 & KC1 & KC16 & KC3 & KC4 & (KC5 & KC6 & KC7)) & KCdef & KCsha & KCbap & KCfap);
  cbn [fst snd] in KC0, KC1, KC16, KC3, KC4, KC5, KC6, KC7, KCdef, KCsha, KCbap, KCfap;
  unfold BIGSHADOW_LO, BIGSHADOW_HI in KB6, KS6, KC6;
  change (hid (bptr + bcap <= 2147446784 \/ 17594333495296 <= bptr)) in KB6; change (hid (sb + scap <= 2147446784 \/ 17594333495296 <= sb)) in KS6;
  change (hid (ch + 16384 <= 2147446784 \/ 17594333495296 <= ch)) in KC6;
  pose proof (CHA.mod8_of_16 _ KB16) as KB8; pose proof (CHA.mod8_of_16 _ KS16) as KS8; pose proof (CHA.mod8_of_16 _ KC16) as KC8;
  pose proof WFX as WFX'; destruct WFX' as (WF1 & WF2 & WF3 & WF4 & WF5 & WF6 & WF7 & WF8);
  pose proof BBX as BBX'; destruct BBX' as (BB1 & BB2 & BB3 & BB4);
  pose proof BCX as BCX'; destruct BCX' as (BC8 & BC1 & BLT & BK0 & BK1);
  pose proof HCH as HCH'; destruct HCH' as (_ & CH1 & CH2 & WDEF & CHSH);
  pose proof ESCN as EN.

Lemma EV0 : forall y : reg, ev E0 (ridx y) = getr R y.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_032 ())).
Qed.
Lemma VV : ev E0 2 = Z_to_bv 64 sp /\ ev E0 4 = Z_to_bv 64 (hl_tp L) /\ ev E0 10 = Z_to_bv 64 P /\ ev E0 11 = Z_to_bv 64 p /\ ev E0 12 = Z_to_bv 64 V /\ ev E0 13 = Z_to_bv 64 E
  /\ ev E0 32 = Z_to_bv 64 wlen /\ ev E0 33 = Z_to_bv 64 B /\ ev E0 34 = Z_to_bv 64 k0 /\ ev E0 35 = Z_to_bv 64 size0 /\ ev E0 36 = Z_to_bv 64 bptr /\ ev E0 37 = Z_to_bv 64 sb
  /\ ev E0 38 = Z_to_bv 64 slen /\ ev E0 39 = Z_to_bv 64 scap /\ ev E0 40 = Z_to_bv 64 level /\ ev E0 41 = Z_to_bv 64 sst0 /\ ev E0 42 = Z_to_bv 64 nst /\ ev E0 43 = Z_to_bv 64 done
  /\ ev E0 44 = Z_to_bv 64 cp0 /\ ev E0 45 = Z_to_bv 64 cp20 /\ ev E0 46 = Z_to_bv 64 pos0 /\ ev E0 47 = Z_to_bv 64 ch /\ ev E0 48 = Z_to_bv 64 esc0.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_033 ())).
Qed.
Lemma UU : bv_unsigned (ev E0 2) = sp /\ bv_unsigned (ev E0 10) = P /\ bv_unsigned (ev E0 11) = p /\ bv_unsigned (ev E0 12) = V /\ bv_unsigned (ev E0 13) = E
  /\ bv_unsigned (ev E0 32) = wlen /\ bv_unsigned (ev E0 33) = B /\ bv_unsigned (ev E0 34) = k0 /\ bv_unsigned (ev E0 35) = size0 /\ bv_unsigned (ev E0 36) = bptr
  /\ bv_unsigned (ev E0 37) = sb /\ bv_unsigned (ev E0 38) = slen /\ bv_unsigned (ev E0 39) = scap /\ bv_unsigned (ev E0 40) = level /\ bv_unsigned (ev E0 41) = sst0
  /\ bv_unsigned (ev E0 42) = nst /\ bv_unsigned (ev E0 43) = done /\ bv_unsigned (ev E0 44) = cp0 /\ bv_unsigned (ev E0 45) = cp20 /\ bv_unsigned (ev E0 46) = pos0
  /\ bv_unsigned (ev E0 47) = ch /\ bv_unsigned (ev E0 48) = esc0.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_034 ())).
Qed.

Ltac pose_U :=
  pose proof UU as UU'; destruct UU' as (U2 & U10 & U11 & U12 & U13 & U32 & U33 & U34 & U35 & U36 & U37 & U38 & U39 & U40 & U41 & U42 & U43 & U44 & U45 & U46 & U47 & U48).
Lemma uv_add_lit : forall (E1 : env) (F k : Z) (v : nat), bv_unsigned (ev E1 v) = F -> 0 <= F -> 0 <= k -> F + k < 2 ^ 64 -> CL5A.uv E1 (EAlu Instr.ALU_ADD (EVar v) (ELit k)) = F + k.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_035 ())).
Qed.
Lemma UVPK : forall k, 0 <= k <= 272 -> CL5A.uv E0 (EAlu Instr.ALU_ADD (EVar 10) (ELit k)) = P + k.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_036 ())).
Qed.
Lemma UVP : CL5A.uv E0 (EVar 10) = P. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_037 ())).
Qed.
Lemma UVE : CL5A.uv E0 (EVar 13) = E. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_038 ())).
Qed.
Lemma UVV : CL5A.uv E0 (EVar 12) = V. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_039 ())).
Qed.
Lemma UVC : CL5A.uv E0 (EVar 11) = p. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_040 ())).
Qed.
Lemma UVCH : CL5A.uv E0 (EVar 47) = ch. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_041 ())).
Qed.
Lemma UVBP : CL5A.uv E0 (EVar 36) = bptr. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_042 ())).
Qed.
Lemma UBC : bv_unsigned (edenot E0 (EMd Instr.M_MUL (ELit 2) (EVar 34))) = bcap.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_043 ())).
Qed.
Lemma UWL : bv_unsigned (edenot E0 (EVar 32)) = wlen. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_044 ())).
Qed.

Lemma SCRV : CH.hd_scr GT.HDECL = 9792. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_045 ())).
Qed.
Lemma STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr GT.HDECL <= sp /\ sp <= ar_sptop ar.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_046 ())).
Qed.
Lemma SCRP : 0 <= CH.hd_scr GT.HDECL. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_047 ())).
Qed.
Lemma NF32 : (32 <= GT.NF)%nat. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_048 ())).
Qed.
Definition WW : list L5.range := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_049 ())).
Definition Wo : list L5.range := ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_050 ())).
Lemma WINC : incl Wo WW. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_051 ())).
Qed.
Lemma WOK : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
  0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr GT.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_052 ())).
Qed.
Lemma WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs GT.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w Wo /\ L5.in_rng w a).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_053 ())).
Qed.
Lemma SHR : forall q n0 a, 0 <= q -> 0 < n0 -> q + n0 <= 2 ^ 47 -> in_shadow_of q n0 a -> 2147450880 <= a < 17594333495296.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_054 ())).
Qed.

Lemma BLKC : forall u n a, In (u, n) LB -> u <= a < u + n -> CHA.sclientA L ar LB FF sp GT.HDECL a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_055 ())).
Qed.
Lemma BLKS : forall u n a, In (u, n) LB -> in_shadow_of u n a -> CHA.sclientA L ar LB FF sp GT.HDECL a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_056 ())).
Qed.

Lemma shreg_sub : forall o n q gr a, o mod 8 = 0 -> q mod 8 = 0 -> o <= q -> q + 8 * gr <= o + n -> 0 < gr -> q / 8 + SB <= a < q / 8 + SB + gr -> in_shadow_of o n a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_057 ())).
Qed.
Lemma CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs GT.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp GT.HDECL a).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_058 ())).
Qed.

Lemma RFO : CHA.rng_facts L ar LBo FF.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_059 ())).
Qed.
Lemma WOKo : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
  0 <= a < 2 ^ 64 /\ aclientw L ar LBo FF sp (CH.hd_scr GT.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_060 ())).
Qed.
Lemma BLKCo : forall u n a, In (u, n) LBo -> u <= a < u + n -> CHA.sclientA L ar LBo FF sp GT.HDECL a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_061 ())).
Qed.
Lemma BLKSo : forall u n a, In (u, n) LBo -> in_shadow_of u n a -> CHA.sclientA L ar LBo FF sp GT.HDECL a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_062 ())).
Qed.

Lemma CRS_OKo : forall rg : SGP.region, In rg (CH.hd_crs GT.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LBo FF sp GT.HDECL a).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_063 ())).
Qed.

Lemma IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img GT.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_064 ())).
Qed.
Lemma DEF0 : L5.defined M (sp - CH.hd_scr GT.HDECL) (CH.hd_scr GT.HDECL). Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_065 ())).
Qed.

Lemma LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_066 ())).
Qed.
Lemma LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_067 ())).
Qed.
Lemma LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_068 ())).
Qed.
Lemma LYN : wx_segs_nowrap (hl_segs L). Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_069 ())).
Qed.
Lemma LYH : hl_img_hi L = IMGHI. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_070 ())).
Qed.
Lemma SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_071 ())).
Qed.
Lemma GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_072 ())).
Qed.
Lemma AL8 : sp mod 8 = 0 /\ (sp - 9792) mod 8 = 0 /\ (sp - 160) mod 32 = 0.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_073 ())).
Qed.

Definition inW (a : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs1.kr_b_074 ())).
Lemma FOOTCL : forall a, PMLA.in_foot IC a -> 65536 <= a < 7024640 /\ forall sp' scr', aclient L ar LB FF sp' scr' a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_075 ())).
Qed.
Lemma WCL : forall a, inW a -> 0 <= a /\ a < ahl_ceil ar /\ (a < 2147446784 \/ 17594333495296 <= a) /\ (forall sp' scr', aclient L ar LB FF sp' scr' a)
                           /\ ((P <= a < P + 272 \/ E <= a < E + 16) \/ a < 7024640).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_076 ())).
Qed.
Lemma INWP : forall y, P <= y < P + 272 -> inW y. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_077 ())).
Qed.
Lemma INWE : forall y, E <= y < E + 16 -> inW y. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_078 ())).
Qed.

Lemma uv_eaddz : forall Ex e0 z, CL5A.uv Ex (APC.eaddz e0 z) = (CL5A.uv Ex e0 + z) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_079 ())).
Qed.
Lemma uv_eadd : forall Ex a b, CL5A.uv Ex (APC.eadd a b) = (CL5A.uv Ex a + CL5A.uv Ex b) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_080 ())).
Qed.
Lemma uv_esub : forall Ex a b, CL5A.uv Ex (APC.esub a b) = (CL5A.uv Ex a - CL5A.uv Ex b) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_081 ())).
Qed.
Lemma uv_escale : forall Ex c e0, CL5A.uv Ex (APC.escale c e0) = (c * CL5A.uv Ex e0) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_082 ())).
Qed.
Lemma uv_lit : forall Ex z, 0 <= z < 2 ^ 64 -> CL5A.uv Ex (ELit z) = z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_083 ())).
Qed.

Lemma ind_val : forall Ex x c v, bv_unsigned (edenot Ex x) = v -> 0 <= c < 2 ^ 64 ->
  bv_unsigned (edenot Ex (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB x (ELit c)) (ELit 1))) = if Z.eqb v c then 1 else 0.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_084 ())).
Qed.
Lemma ind_valn : forall (w : word) d v, bv_unsigned w = v -> - 2 ^ 64 < d < 0 ->
  bv_unsigned (Sem.alu64 Instr.ALU_SLTU (Sem.alu64 Instr.ALU_ADD w (Z_to_bv 64 d)) (Z_to_bv 64 1)) = if Z.eqb v (- d) then 1 else 0.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_085 ())).
Qed.
Lemma ESCV : forall n : nat, (n <= 11)%nat ->
  (if Z.of_nat n =? 3 then 1 else 0) + 2 * (if Z.of_nat n =? 4 then 1 else 0) + 3 * (if Z.of_nat n =? 5 then 1 else 0) + (if Z.of_nat n =? 9 then 1 else 0)
  + 2 * (if Z.of_nat n =? 10 then 1 else 0) + 3 * (if Z.of_nat n =? 11 then 1 else 0) = PML.esc_need (Z.of_nat n).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_086 ())).
Qed.

Lemma ESCV2 : forall z, 0 <= z <= 11 ->
  (if z =? 3 then 1 else 0) + 2 * (if z =? 4 then 1 else 0) + 3 * (if z =? 5 then 1 else 0) + (if z =? 9 then 1 else 0) + 2 * (if z =? 10 then 1 else 0) + 3 * (if z =? 11 then 1 else 0)
  = PML.esc_need z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_087 ())).
Qed.

Lemma KIMG : forall Ex lo hi, L5.img_clear M 65536 1392640 -> 65536 <= lo -> hi <= 1392640 -> kentry_ok (hl_segs L) Ex (CCA.vis A model M) (KImg lo hi).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_088 ())).
Qed.

Lemma At0 : CC.At (hl_segs L) GT.t0 E0 R (CCA.vis A model M).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_089 ())).
Qed.

Lemma KSHO : forall o n a, CL5A.ainfr FF o n -> 0 < n -> o + n <= 2 ^ 47 -> in_shadow_of o n a -> CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_090 ())).
Qed.
Lemma KV : forall a, V <= a < V + 8 -> CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_091 ())).
Qed.
Lemma KLB : forall u n a, In (u, n) LBo -> u <= a < u + n \/ in_shadow_of u n a -> CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_092 ())).
Qed.
Lemma KSTK : forall a, S (sp - 9792) <= a < S (sp - 9792) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 9792)) / 8 -> CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_093 ())).
Qed.

Lemma DECW : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> inW a \/ L5.outside WW a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_094 ())).
Qed.
Lemma PTKF : forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 1
                 \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
                 \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 \/ PMLA.CONVCAT_GUARD IC <= a < PMLA.CONVCAT_GUARD IC + 2 -> PMLA.in_foot IC a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_095 ())).
Qed.
Lemma IMGCL : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> 65536 <= a < 7024640 /\ forall sp' scr', aclient L ar LB FF sp' scr' a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_096 ())).
Qed.

Lemma STCL : forall a LB' FF' sp' scr', PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> aclient L ar LB' FF' sp' scr' a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_097 ())).
Qed.

Lemma WFR : forall a F n, inW a -> ar_fs ar <= F -> fframes_apart F n FF -> 0 < n -> ~ (F <= a < F + n).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_098 ())).
Qed.

Definition bptrI (i : nat) (E1 : env) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 2 (ParseNumberCA_blobs1.kr_b_099 ())).
Definition bcapI (i : nat) (E1 : env) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 2 (ParseNumberCA_blobs1.kr_b_100 ())).
Definition sbI (i : nat) (E1 : env) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 2 (ParseNumberCA_blobs1.kr_b_101 ())).
Definition scapI (i : nat) (E1 : env) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 2 (ParseNumberCA_blobs1.kr_b_102 ())).

Definition stk_kx (sc : Z) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs1.kr_b_103 ())).
Definition stk_bx (sc : Z) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs1.kr_b_104 ())).
Definition Cred (i : nat) (E1 : env) (cr1 : credit) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 3 (ParseNumberCA_blobs1.kr_b_105 ())).
Lemma stk_pot_nonneg : forall sc, In sc [66; 132; 264; 528; 1056] -> 0 <= stk_kx sc /\ 0 <= stk_bx sc.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_106 ())).
Qed.
Lemma pcredit_bufcred : forall cr1 ps1, In (PML.ps_scap ps1) [66; 132; 264; 528; 1056] ->
  PMLA.pcredit_xA L cr1 ps1 kx bx <-> PMSA.bufcredA L cr1 (PML.ps_bcap ps1) (stk_kx (PML.ps_scap ps1) + kx) (stk_bx (PML.ps_scap ps1) + bx).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_107 ())).
Qed.

Definition FLF (E1 : env) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs1.kr_b_108 ())).

Definition FIXA (a : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs1.kr_b_109 ())).
Definition AGFIX (M1 : mem) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs1.kr_b_110 ())).

Definition FIXB (a : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs1.kr_b_111 ())).
Definition AGBUF (M1 : mem) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs1.kr_b_112 ())).

Definition PH0 (M1 : mem) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs1.kr_b_113 ())).
Definition PHS (M1 : mem) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs1.kr_b_114 ())).

Definition cutn (i : nat) : CC.cutpoint := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs1.kr_b_115 ())).
Definition text (n : Z) : list Z := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs1.kr_b_116 ())).
Definition jremv (i : nat) (E1 : env) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 2 (ParseNumberCA_blobs1.kr_b_117 ())).
Definition ncons (i : nat) (E1 : env) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 2 (ParseNumberCA_blobs1.kr_b_118 ())).
Definition auto_ok (i : nat) (E1 : env) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 2 (ParseNumberCA_blobs1.kr_b_119 ())).

Definition appk (i : nat) (k : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 2 (ParseNumberCA_blobs1.kr_b_120 ())).
Definition APPP (i : nat) (E1 : env) (M1 : mem) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 3 (ParseNumberCA_blobs1.kr_b_121 ())).

Definition WINOK (M1 : mem) (ps' : PML.pstate) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 2 (ParseNumberCA_blobs1.kr_b_122 ())).

Definition POSTP (M1 : mem) (q pp cc ss sc : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 6 (ParseNumberCA_blobs1.kr_b_123 ())).

Definition ECV (i : nat) (E1 : env) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 2 (ParseNumberCA_blobs1.kr_b_124 ())).
Definition ENDP (i : nat) (E1 : env) (M1 : mem) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 3 (ParseNumberCA_blobs1.kr_b_125 ())).
Definition XI (i : nat) (E1 : env) (A1 : list (Z * Z)) (M1 : mem) (m1 : Model) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 5 (ParseNumberCA_blobs1.kr_b_126 ())).

Lemma ffs_i : forall i, (1 <= i <= 73)%nat -> nth i PNA.FFS [] = [PNA.FR].
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_127 ())).
Qed.
Lemma ffs_0 : nth 0 PNA.FFS [] = []. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_128 ())).
Qed.
Lemma bls_i : forall i, (i <= 73)%nat -> nth i G.BLS [] = [PNA.blk0 i; PNA.blk1 i].
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_129 ())).
Qed.

Lemma BLK0 : PNA.blk0 0 = (EVar 36, EMd Instr.M_MUL (ELit 2) (EVar 34)) /\ PNA.blk1 0 = (EVar 37, EVar 39). Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_130 ())).
Qed.
Lemma BLK48 : PNA.blk0 48 = (EVar 36, EMd Instr.M_MUL (ELit 2) (EVar 34)) /\ PNA.blk1 48 = (EVar 37, EVar 39). Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_131 ())).
Qed.
Lemma K48 : PNA.kind_of 48 = PNA.KSm. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_132 ())).
Qed.

Lemma FRM : forall i E1 A1 M1 m1, (1 <= i <= 73)%nat ->
  CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 i E1 A1 M1 m1 ->
  let F := CL5A.uv E1 FE in let ob := [(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] in
  CHA.curB LBo G.BLS i E1 = ob ++ LBo /\ CHA.curF FF sp PNA.FFS i E1 = (F, 1, sp + -160 + 32) :: FF /\ env_agree GT.NF E0 E1 /\
  0 <= F /\ F + 128 <= 140737488355328 /\ F mod 8 = 0 /\ (F + 128 <= 2147446784 \/ 17594333495296 <= F) /\ ar_fs ar <= F /\ F + 128 <= ar_fs ar + 11571200 /\ fframes_apart F 128 FF /\
  (exists crX LKX, ri_inv HI (ob ++ LBo) ((F, 1, sp + -160 + 32) :: FF) LKX crX A1 M1 (vml_of m1) /\ Cred i E1 crX).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_133 ())).
Qed.

Definition outU (E' : env) (a : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 2 (ParseNumberCA_blobs1.kr_b_134 ())).

Lemma LEAFK : forall i c ps0 E1 A1 M1 m1 E' R' M' m', (1 <= i <= 73)%nat -> nth_error G.CPS i = Some c ->
  CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  (forall k, (k < 50)%nat -> ev E' k = ev E0 k) /\ CL5A.uv E' FE = CL5A.uv E1 FE /\ CL5A.uv E' FLE = CL5A.uv E1 FLE
  /\ (forall X0, In X0 (SR.ps_cells ps0) -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0)
  /\ (forall (q : nat) (e0 : expr) (z : Z), CL.ps_reg_is ps0 q e0 = true -> bv_unsigned (edenot E' e0) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z)
  /\ (forall a, 0 <= a < 2 ^ 64 -> outU E' a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_135 ())).
Qed.

Lemma PSX : forall (M' : mem) (nst' : Z) (more' : bool) (cc pp q : Z) (s' : list Z),
  (forall a, FIXA a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  L5.u8_at (hl_segs L) M' (P + 210) nst' -> L5.u8_at (hl_segs L) M' (P + 211) (PML.b2z more') ->
  PMLA.str_at (hl_segs L) M' (P + 224) (PML.SLong cc pp s') -> 264 <= cc ->
  (forall i, 0 <= i < 272 -> M' (Z_to_bv 64 (P + i)) <> None) ->
  PMLA.parser_at (hl_segs L) IC M' P (PML.ps_set_win (PML.PS PML.ST_NUMBER sst0 nst' more' (PML.ps_done ps) level stack sb scap cc pp s' (Some (q, e))) (PML.ps_win ps)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_136 ())).
Qed.

Definition SAFE (i : nat) (E1 : env) (a : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 3 (ParseNumberCA_blobs1.kr_b_137 ())).
Lemma SAFEOUT : forall i E1 A1 M1 m1 E' a, (1 <= i <= 73)%nat ->
  CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 i E1 A1 M1 m1 ->
  CL5A.uv E' FE = CL5A.uv E1 FE -> CL5A.uv E' FLE = CL5A.uv E1 FLE -> FLF E1 -> sbI i E1 = sb -> scapI i E1 = scap -> SAFE i E1 a -> 0 <= a < 2 ^ 64 /\ outU E' a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_138 ())).
Qed.

Lemma AGFIX_mv : forall (M1 M2 : mem), (forall a, FIXA a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> AGFIX M1 -> AGFIX M2.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_139 ())).
Qed.
Lemma AGBUF_mv : forall (M1 M2 : mem), (forall a, FIXB a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> AGBUF M1 -> AGBUF M2.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_140 ())).
Qed.
Definition STATIC (a : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs1.kr_b_141 ())).
Lemma STATIC_lo : forall a, STATIC a -> 0 <= a < 7024640.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_142 ())).
Qed.
Lemma LS_mv : forall g1 (M1 M2 : mem), (forall a, STATIC a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> g1 <> PML.LS0 ->
  PMLA.ls_ok (hl_segs L) IC g1 M1 -> PMLA.ls_ok (hl_segs L) IC g1 M2.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_143 ())).
Qed.
Lemma EC_mv : forall code (M1 M2 : mem), (forall a, E <= a < E + 16 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  PMLA.ec_at (hl_segs L) IC M1 E code -> PMLA.ec_at (hl_segs L) IC M2 E code.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_144 ())).
Qed.
Lemma PH0_mv : forall (M1 M2 : mem), (forall a, (E <= a < E + 16) \/ a = P + 211 \/ STATIC a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> PH0 M1 -> PH0 M2.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_145 ())).
Qed.
Lemma PHS_mv : forall (M1 M2 : mem), (forall a, (E <= a < E + 16) \/ STATIC a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> PHS M1 -> PHS M2.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_146 ())).
Qed.

Section Out.
Variables (E' : env) (a : Z).
Hypothesis W2 : bv_unsigned (ev E' 2) = sp.
Hypothesis W10 : bv_unsigned (ev E' 10) = P.
Hypothesis Ha : 0 <= a < 2 ^ 64.
Let F := CL5A.uv E' (EVar 55).
Let fl := CL5A.uv E' (EVar 50).
Ltac outgo := unfold PNA.CPF_N, PNA.CPF_NM, PNA.CPF_MM, PNA.CPF_E, PNA.CPF_X; unfold PNA.F0, PNA.FRM3, PNA.FLR, PNA.MORE; unfold PNA.PE, PNA.FE, PNA.FLE, CHA.SRL3, PNA.SBz, SGP.outside; cbn [app];
  repeat (apply Forall_cons); try (apply Forall_nil); rewrite ?CL5A.estart_srl3'; unfold estart, elenZ, CL5A.uv; cbn [a_base a_off edenot]; rewrite ?(L5.unsigned_lit a Ha).
Lemma OUT_0 : (a < sp - 9792 \/ sp <= a) -> ~ (P + 168 <= a < P + 176) -> a <> P + 210 -> SGP.outside E' PNA.F0 (Z_to_bv 64 a).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_147 ())).
Qed.
Lemma OUT_N : (a < sp - 9792 \/ sp <= a) -> ~ (P + 168 <= a < P + 176) -> a <> P + 210 ->
  ~ (F <= a < F + 128) -> ~ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16) -> SGP.outside E' PNA.CPF_N (Z_to_bv 64 a).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_148 ())).
Qed.
Lemma OUT_NM : (a < sp - 9792 \/ sp <= a) -> ~ (P + 168 <= a < P + 176) -> a <> P + 210 -> a <> P + 211 ->
  ~ (F <= a < F + 128) -> ~ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16) -> SGP.outside E' PNA.CPF_NM (Z_to_bv 64 a) /\ SGP.outside E' PNA.CPF_MM (Z_to_bv 64 a).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_149 ())).
Qed.
Lemma OUT_E : (a < sp - 9792 \/ sp <= a) -> ~ (F <= a < F + 128) -> ~ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16) -> SGP.outside E' PNA.CPF_E (Z_to_bv 64 a).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_150 ())).
Qed.
Lemma OUT_X : (a < sp - 9792 \/ sp <= a) -> ~ (F <= a < F + 24) -> ~ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16) -> a <> fl -> SGP.outside E' PNA.CPF_X (Z_to_bv 64 a).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_151 ())).
Qed.
Lemma OUT_FL : F + 120 <= a < F + 128 -> F + 128 <= sp - 9792 -> (P + 272 <= F \/ F + 128 <= P) -> (F + 128 <= 2147446784 \/ 17594333495296 <= F) -> F + 128 <= 2 ^ 47 ->
  SGP.outside E' PNA.CPF_N (Z_to_bv 64 a) /\ SGP.outside E' PNA.CPF_NM (Z_to_bv 64 a) /\ SGP.outside E' PNA.CPF_MM (Z_to_bv 64 a).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_152 ())).
Qed.
End Out.

Lemma BLKAG : forall i c E1 E', nth_error G.CPS i = Some c -> env_agree (CC.cp_nx c) E1 E' ->
  bptrI i E' = bptrI i E1 /\ bcapI i E' = bcapI i E1 /\ sbI i E' = sbI i E1 /\ scapI i E' = scapI i E1.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_153 ())).
Qed.
Lemma GBLK : forall i c k ps0 j s E', CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> (j <= 73)%nat ->
  let E'' := CC.env_over GT.NF s E' in
  bptrI j E'' = bptrI i E' /\ bcapI j E'' = bcapI i E' /\ sbI j E'' = sbI i E' /\ scapI j E'' = scapI i E'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_154 ())).
Qed.

Lemma G_CRED : forall i c k ps0 j s, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> (j <= 73)%nat ->
  forall E1 E' R' M1 M' cr1, env_agree GT.NF E0 E1 -> env_agree (CC.cp_nx c) E1 E' -> CC.leaf_facts (hl_segs L) c ps0 E' R' M1 M' -> Cred i E1 cr1 -> Cred j (CC.env_over GT.NF s E') cr1.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_155 ())).
Qed.

Lemma POUT : forall i E1 A1 M1 m1 k, (1 <= i <= 73)%nat ->
  CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 i E1 A1 M1 m1 -> FLF E1 -> 0 <= k < 272 ->
  let F := CL5A.uv E1 (EVar 55) in
  P + k < sp - 9792 /\ ~ (F <= P + k < F + 128) /\ ~ (F / 8 + 2147450880 <= P + k < F / 8 + 2147450880 + 16) /\ P + k <> CL5A.uv E1 (EVar 50).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_156 ())).
Qed.

Lemma over_ge : forall s E' v, (50 <= v)%nat -> ev (CC.env_over GT.NF s E') v = edenot E' (CC.slook s v).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_157 ())).
Qed.
Lemma over_lt : forall s E' v, (v < 50)%nat -> ev (CC.env_over GT.NF s E') v = ev E' v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_158 ())).
Qed.

Lemma PROVE : forall c ps0 E' R' A1 M1 m1 M' m' ex lo hi, CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  PNA.prove (SR.ps_cells ps0) (KRange ex lo hi) = true -> lo <= CL5A.uv E' ex <= hi.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_159 ())).
Qed.

Lemma UVR : forall Ex e0, 0 <= CL5A.uv Ex e0 < 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_160 ())).
Qed.
Lemma U64INJ : forall (Mx : mem) a v1 v2, L5.u64_at (hl_segs L) Mx a v1 -> L5.u64_at (hl_segs L) Mx a v2 -> 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_161 ())).
Qed.

Lemma SUBR : forall x y lo hi, 0 <= x < 2 ^ 62 -> 0 <= y < 2 ^ 62 -> lo <= (x - y) mod 2 ^ 64 <= hi -> 0 <= lo -> hi < 2 ^ 62 -> lo <= x - y <= hi.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_162 ())).
Qed.
Lemma MODB : forall X, 0 <= X <= 2 ^ 28 -> 0 <= (B - X) mod 2 ^ 64 <= 67108864 -> X <= B.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_163 ())).
Qed.

Lemma RD8 : forall E' A1 m' (M' : mem) k v, H_off_segments (hl_segs L) (ahid A1 m') -> bv_unsigned (ev E' 10) = P ->
  kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') (KWord (SA PNA.PE k) 1 v) -> L5.u8_at (hl_segs L) M' (P + k) (CL5A.uv E' v).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_164 ())).
Qed.
Lemma RD64 : forall E' A1 m' (M' : mem) k v, H_off_segments (hl_segs L) (ahid A1 m') -> bv_unsigned (ev E' 10) = P ->
  kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') (KWord (SA PNA.PE k) 8 v) -> L5.u64_at (hl_segs L) M' (P + k) (CL5A.uv E' v).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_165 ())).
Qed.

Lemma cell_at_has : forall cells b k w v, CAX.cell_at cells b k w = Some v -> In (KWord (SA b k) w v) cells.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_166 ())).
Qed.

Lemma nl_run_app : forall s1 s2 k, PML.nl_run k (s1 ++ s2) = match PML.nl_run k s1 with Some k1 => PML.nl_run k1 s2 | None => None end.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_167 ())).
Qed.
Lemma firstn_succ : forall (l : list Z) n, (n < length l)%nat -> firstn (Datatypes.S n) l = firstn n l ++ [nth n l 0].
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_168 ())).
Qed.
Lemma zseq_in : forall lo hi v, lo <= v <= hi -> In v (PNA.zseq lo hi).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_169 ())).
Qed.
Lemma step_chk_sound : forall Si lo hi okf k v, PNA.step_chk Si lo hi okf = true -> In k Si -> lo <= v <= hi -> exists k', PML.nl_step k v = Some k' /\ okf k' = true.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_170 ())).
Qed.
Lemma existsb_eqb_in : forall k S, existsb (Z.eqb k) S = true -> In k S.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_171 ())).
Qed.
Lemma mod_neg64 : forall x, - 2 ^ 64 <= x < 0 -> x mod 2 ^ 64 = x + 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_172 ())).
Qed.
Lemma mod64_zero : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> (x - y) mod 2 ^ 64 = 0 -> x = y.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_173 ())).
Qed.
Lemma mod64_diff : forall x y d, 0 <= x < 2 ^ 64 -> 0 <= y -> 0 <= d -> y + d < 2 ^ 64 -> (x - y) mod 2 ^ 64 = d -> x = y + d.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_174 ())).
Qed.
Lemma mod64_sub : forall a x y, 0 <= x < 2 ^ 64 -> 0 <= y <= a -> a < 2 ^ 64 -> (a - x) mod 2 ^ 64 = a - y -> x = y.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_175 ())).
Qed.
Lemma rng_is_sound : forall Ex Mv cells ex v, know_ok (hl_segs L) Ex Mv cells -> PNA.rng_is cells ex v = true -> CL5A.uv Ex ex = v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_176 ())).
Qed.
Lemma lo_ge_sound : forall Ex Mv cells ex v, know_ok (hl_segs L) Ex Mv cells -> PNA.lo_ge cells ex v = true -> v <= CL5A.uv Ex ex.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_177 ())).
Qed.

Lemma named_sound : forall Ex Mv cells cur a v lo hi, know_ok (hl_segs L) Ex Mv cells -> PNA.named_at cells cur = Some (a, v, lo, hi) ->
  L5.u8_at (hl_segs L) Mv (CL5A.uv Ex cur) (CL5A.uv Ex v) /\ lo <= CL5A.uv Ex v <= hi /\ 0 <= lo /\ hi <= 255.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_178 ())).
Qed.
Lemma u8_inj : forall (Mv : mem) a b1 b2, L5.u8_at (hl_segs L) Mv a b1 -> L5.u8_at (hl_segs L) Mv a b2 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> b1 = b2.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_179 ())).
Qed.

Lemma FRZ : forall E', (forall k, (k < 50)%nat -> ev E' k = ev E0 k) ->
  CL5A.uv E' PNA.CUR0 = p /\ CL5A.uv E' PNA.WLEN = wlen /\ CL5A.uv E' PNA.WEND = e /\ CL5A.uv E' PNA.PE = P /\ CL5A.uv E' PNA.NST0 = nst /\ CL5A.uv E' PNA.SIZE0 = size0 /\ CL5A.uv E' PNA.BX = B.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_180 ())).
Qed.

Lemma CURMOD : forall p' w j, 0 <= j <= w -> 0 <= p' -> p' + w < 2 ^ 64 ->
  (p' + ((w + (18446744073709551615 * j) mod 2 ^ 64) mod 2 ^ 64)) mod 2 ^ 64 = p' + w - j.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_181 ())).
Qed.
Lemma UCUR : forall i E', (forall k, (k < 50)%nat -> ev E' k = ev E0 k) -> 0 <= jremv i E' <= wlen -> CL5A.uv E' (PNA.curE i) = e - jremv i E'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_182 ())).
Qed.

Lemma content_sound : forall i cells dist okf E' Mv,
  PNA.content_chk i cells dist okf = true -> know_ok (hl_segs L) E' Mv cells -> (forall k, (k < 50)%nat -> ev E' k = ev E0 k) -> eb E' = eb E0 ->
  forall Si, PNA.cut_states i = Some Si -> 0 <= jremv i E' <= wlen -> forall k, PML.nl_run (-1) (text (wlen - jremv i E')) = Some k -> In k Si ->
  exists d k', 0 <= d <= 1 /\ d <= jremv i E' /\ CL5A.uv E' dist = d /\ PML.nl_run (-1) (text (wlen - jremv i E' + d)) = Some k' /\ okf k' = true.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_183 ())).
Qed.

Lemma BLPRE : forall i E1, (i < 74)%nat -> env_agree GT.NF E0 E1 ->
  match PNA.kind_of i with PNA.KEntry | PNA.KDecl | PNA.KSm | PNA.KErrh | PNA.KSetec => bptrI i E1 = bptr /\ bcapI i E1 = bcap /\ sbI i E1 = sb /\ scapI i E1 = scap | _ => True end.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_184 ())).
Qed.

Lemma NX56 : forall i c, (1 <= i <= 73)%nat -> nth_error G.CPS i = Some c -> (56 <= CC.cp_nx c)%nat.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_185 ())).
Qed.
Lemma JREM_ag : forall i c E1 E', (1 <= i <= 73)%nat -> nth_error G.CPS i = Some c -> env_agree (CC.cp_nx c) E1 E' -> jremv i E' = jremv i E1.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_186 ())).
Qed.
Lemma AUTO_ag : forall i c E1 E', (1 <= i <= 73)%nat -> nth_error G.CPS i = Some c -> env_agree (CC.cp_nx c) E1 E' -> auto_ok i E1 -> auto_ok i E'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_187 ())).
Qed.
Lemma DECL_CORE : forall i j s c ps0 E1 R1 E' R' A1 M1 m1 M' m',
  nth_error G.CPS i = Some c -> (1 <= i <= 73)%nat -> (j <= 73)%nat -> CC.slook s 50 = PNA.FLE -> CC.cp_F c = PNA.CPF_N -> PNA.kind_of j = PNA.KDecl ->
  (PNA.kind_of i = PNA.KDecl \/ PNA.kind_of i = PNA.KSm) ->
  (auto_ok i E' -> auto_ok j (CC.env_over GT.NF s E')) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XI i E1 A1 M1 m1 -> XI j (CC.env_over GT.NF s E') A1 M' m'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_188 ())).
Qed.

Lemma uv_over : forall s E' x, CL5A.uv (CC.env_over GT.NF s E') x = CL5A.uv E' (CC.esubstL GT.NF s x).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_189 ())).
Qed.
Lemma G_DECL : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m',
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> PNA.kind_of j = PNA.KDecl ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XI i E1 A1 M1 m1 -> XI j (CC.env_over GT.NF s E') A1 M' m'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_190 ())).
Qed.

Lemma WF_mk : forall nst' (more' : bool) cc pp bf w, 0 <= nst' <= 7 -> (more' = true -> PML.ps_more ps = true /\ PML.num_prefix nst' bf) ->
  PML.wf_ps (PML.PS PML.ST_NUMBER sst0 nst' more' (PML.ps_done ps) level stack sb scap cc pp bf w).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_191 ())).
Qed.

Lemma lvl_upd : forall nst' (more' : bool) cc pp bf w, PMCUR.lvl_ok (PML.PS PML.ST_NUMBER sst0 nst' more' (PML.ps_done ps) level stack sb scap cc pp bf w).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_192 ())).
Qed.
Lemma text_len : forall n, 0 <= n <= wlen -> Z.of_nat (length (text n)) = size0 + n.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_193 ())).
Qed.

Lemma G_RETX : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m',
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> PNA.kind_of j = PNA.KRetx -> PNA.kind_of i <> PNA.KEnd ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XI i E1 A1 M1 m1 -> XI j (CC.env_over GT.NF s E') A1 M' m'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_194 ())).
Qed.
Definition SAFE2 (i : nat) (E1 : env) (a : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 3 (ParseNumberCA_blobs1.kr_b_195 ())).
Lemma SAFEOUT2 : forall i E1 A1 M1 m1 E' a, (1 <= i <= 73)%nat ->
  CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 i E1 A1 M1 m1 ->
  CL5A.uv E' FE = CL5A.uv E1 FE -> SAFE2 i E1 a ->
  0 <= a < 2 ^ 64 /\ (a < sp - 9792 \/ sp <= a) /\ ~ (CL5A.uv E' (EVar 55) <= a < CL5A.uv E' (EVar 55) + 128) /\ ~ (CL5A.uv E' (EVar 55) / 8 + 2147450880 <= a < CL5A.uv E' (EVar 55) / 8 + 2147450880 + 16)
  /\ (FLF E1 -> a <> CL5A.uv E1 (EVar 50)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_196 ())).
Qed.

Ltac u64 AGS OPS H := apply (PTA.u64_ag _ _ _ _ AGS); [apply OPS; clear; lia | exact H].
Ltac u32 AGS OPS H := apply (PTA.u32_ag _ _ _ _ AGS); [apply OPS; clear; lia | exact H].
Ltac u8 AGS OPS H := apply (PTA.u8_ag _ _ _ _ AGS); [apply OPS; clear; lia | exact H].

Lemma G_RETX_END : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m',
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> PNA.kind_of j = PNA.KRetx -> PNA.kind_of i = PNA.KEnd ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XI i E1 A1 M1 m1 -> XI j (CC.env_over GT.NF s E') A1 M' m'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_197 ())).
Qed.

Lemma PA_ag : forall (M1 M2 : mem) (S : Z -> Prop) psx, (forall a, S a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, P <= a < P + 272 -> S a) -> (forall a, PML.ps_bptr psx <= a < PML.ps_bptr psx + PML.ps_bcap psx -> S a) ->
  (forall a, PML.ps_sb psx <= a < PML.ps_sb psx + PML.ps_scap psx -> S a) ->
  0 <= PML.ps_bptr psx -> PML.ps_bptr psx + PML.ps_bcap psx <= 2 ^ 64 -> 0 <= PML.ps_sb psx -> PML.ps_sb psx + PML.ps_scap psx <= 2 ^ 64 ->
  PMLA.parser_at (hl_segs L) IC M1 P psx -> PMLA.parser_at (hl_segs L) IC M2 P psx.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_198 ())).
Qed.
Lemma POSTP_mv : forall i E1 A1 M1 m1 (M2 : mem) q, (1 <= i <= 73)%nat ->
  CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 i E1 A1 M1 m1 ->
  (forall a, SAFE2 i E1 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> (forall a, 0 <= a < 2 ^ 64 -> M1 (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None) ->
  POSTP M1 q (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) -> POSTP M2 q (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_199 ())).
Qed.

Lemma GK : forall i c k ps0 j s, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> (j <= 73)%nat /\ (PNA.kind_of j = PNA.KDecl \/ PNA.kind_of j = PNA.KRetx).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_200 ())).
Qed.

Definition AMBX := CHA.ambX L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 XI.
Definition LEAF (pc : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs1.kr_b_201 ())).

Lemma rows_ok2 : forallb (fun rw => expr_eqb (CC.slook (CSLR.r_sid rw) 50) PNA.FLE && Nat.leb (CSLR.r_j rw) 73 && PNA.kind_eqb (PNA.kind_of (CSLR.r_j rw)) PNA.KDecl
                                   && PNA.kind_eqb (PNA.kind_of (CSLR.r_i rw)) PNA.KDecl && Nat.leb 1 (CSLR.r_i rw) && Nat.leb (CSLR.r_i rw) 73)%bool PNA.ROWS = true.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_202 ())).
Qed.

Lemma SID_id : CC.esubstL GT.NF PNA.SID PNA.JV = PNA.JV /\ CC.esubstL GT.NF PNA.SID PNA.WLEN = PNA.WLEN.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_203 ())).
Qed.
Lemma L_CSL : forall pc, pc <> PNA.RETPC -> pc <> PNA.PC_SM -> pc <> PNA.PC_ERRH -> pc <> PNA.PC_SETEC -> pc <> PNA.PC_APPR -> pc <> PNA.PC_ENDI -> pc <> PNA.PC_ENDF -> LEAF pc.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_204 ())).
Qed.

Lemma KRETX47 : forall i, PNA.kind_of i = PNA.KRetx -> i = 47%nat.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs1.kr_b_205 ())).
Qed.
Lemma L_EXIT : LEAF PNA.RETPC.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_206 ())).
Qed.

Definition SAFE0 (a : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs2.kr_b_207 ())).
Lemma SAFEOUT0 : forall a, SAFE0 a -> 0 <= a < 2 ^ 64 /\ (a < sp - 9792 \/ sp <= a) /\ ~ (P + 168 <= a < P + 176) /\ a <> P + 210.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_208 ())).
Qed.

Lemma ACL : forall a sp' scr',
  (P <= a < P + 272) \/ (E <= a < E + 16) \/ (V <= a < V + 8) \/ in_shadow_of P 272 a \/ in_shadow_of E 16 a \/ in_shadow_of V 8 a
  \/ (bptr <= a < bptr + bcap) \/ in_shadow_of bptr bcap a \/ (sb <= a < sb + scap) \/ in_shadow_of sb scap a \/ (ch <= a < ch + 16384) \/ in_shadow_of ch 16384 a \/ STATIC a ->
  0 <= a < 2 ^ 64 /\ aclient L ar LB FF sp' scr' a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_209 ())).
Qed.

Lemma L_SM : LEAF PNA.PC_SM.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_210 ())).
Qed.

Lemma NEWSF : forall E' E2 A1 A2 (M' M2 : mem) m' m2 LKa LKb cra crb LB1 LB2 F fl,
  ri_inv HI LB1 ((F, 1, sp + -160 + 32) :: FF) LKa cra A1 M' (vml_of m') -> ri_inv HI LB2 ((F, 1, sp + -160 + 32) :: FF) LKb crb A2 M2 (vml_of m2) ->
  H_off_segments (hl_segs L) (ahid A1 m') ->
  0 <= F -> F + 128 <= 140737488355328 -> ar_fs ar <= F -> F + 128 <= ar_fs ar + 11571200 -> ar_fs ar <= fl < ar_fs ar + 11571200 ->
  bv_unsigned (ev E' 55) = F -> bv_unsigned (ev E' 50) = fl -> bv_unsigned (ev E2 55) = F -> bv_unsigned (ev E2 50) = fl ->
  L5.u64_at (hl_segs L) M' (F + 120) fl ->
  forall X0, In X0 PNA.NEWS_F -> kentry_ok (hl_segs L) E2 (CCA.vis A2 m2 M2) X0.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_211 ())).
Qed.

Lemma STKSH : forall (M' : mem) scr, (forall a, CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  0 <= scr -> scr mod 8 = 0 -> 160 + scr <= 9792 -> PMLA.stksh ar M' (sp + -160) scr.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_212 ())).
Qed.

Lemma U8DEF : forall (Mx : mem) a v, L5.u8_at (hl_segs L) Mx a v -> hl_img_hi L <= a -> 0 <= a < 2 ^ 64 -> Mx (Z_to_bv 64 a) <> None.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_213 ())).
Qed.

Lemma ACLI : forall i E1 A1 M1 m1 a sp' scr', (1 <= i <= 73)%nat ->
  CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 i E1 A1 M1 m1 ->
  (P <= a < P + 272) \/ (E <= a < E + 16) \/ (V <= a < V + 8) \/ in_shadow_of P 272 a \/ in_shadow_of E 16 a \/ in_shadow_of V 8 a
  \/ (bptrI i E1 <= a < bptrI i E1 + bcapI i E1) \/ in_shadow_of (bptrI i E1) (bcapI i E1) a \/ (sbI i E1 <= a < sbI i E1 + scapI i E1) \/ in_shadow_of (sbI i E1) (scapI i E1) a
  \/ (ch <= a < ch + 16384) \/ in_shadow_of ch 16384 a \/ STATIC a ->
  0 <= a < 2 ^ 64 /\ aclient L ar (CHA.curB LBo G.BLS i E1) (CHA.curF FF sp PNA.FFS i E1) sp' scr' a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_214 ())).
Qed.

Definition CSET (i : nat) (E1 : env) (a : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 3 (ParseNumberCA_blobs2.kr_b_215 ())).
Lemma FIX_CSET : forall i E1 a, sbI i E1 = sb -> scapI i E1 = scap -> FIXA a -> CSET i E1 a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_216 ())).
Qed.

Definition OSET (i : nat) (E1 : env) (a : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 3 (ParseNumberCA_blobs2.kr_b_217 ())).
Lemma OSET_CSET : forall i E1 a, sbI i E1 = sb -> scapI i E1 = scap -> OSET i E1 a -> CSET i E1 a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_218 ())).
Qed.
Lemma KEEP_FS : forall i E1 (M' M2 : mem), bptrI i E1 = bptr -> bcapI i E1 = bcap ->
  (forall a, OSET i E1 a -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)) ->
  (AGFIX M' -> AGFIX M2) /\ (AGBUF M' -> AGBUF M2).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_219 ())).
Qed.
Lemma KEEP_PH : forall (M' M2 : mem), (forall a, (E <= a < E + 16) \/ a = P + 211 \/ STATIC a -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)) ->
  (PH0 M' -> PH0 M2) /\ (PHS M' -> PHS M2).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_220 ())).
Qed.

Lemma OSET_OUT : forall i E1 A1 M1 m1 a, (1 <= i <= 73)%nat ->
  CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 i E1 A1 M1 m1 -> sbI i E1 = sb -> scapI i E1 = scap ->
  OSET i E1 a -> ~ (E <= a < E + 16) /\ (a < hl_img_lo L \/ hl_img_hi L <= a) /\ a <> P + 211.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_221 ())).
Qed.

Lemma FL64 : forall i c E1 R1 A1 M1 m1 (M' : mem) (V' : vml) LB1 LKa cra Ax, (1 <= i <= 73)%nat -> nth_error G.CPS i = Some c ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 i E1 A1 M1 m1 ->
  ri_inv HI LB1 ((CL5A.uv E1 FE, 1, sp + -160 + 32) :: FF) LKa cra Ax M' V' ->
  L5.u64_at (hl_segs L) M' (CL5A.uv E1 FE + 120) (CL5A.uv E1 FLE).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_222 ())).
Qed.

Lemma RBLK : forall i j c E1 E2, nth_error G.CPS i = Some c -> nth j G.BLS [] = nth i G.BLS [] -> env_agree (CC.cp_nx c) E1 E2 ->
  bptrI j E2 = bptrI i E1 /\ bcapI j E2 = bcapI i E1 /\ sbI j E2 = sbI i E1 /\ scapI j E2 = scapI i E1 /\ CHA.curB LBo G.BLS j E2 = CHA.curB LBo G.BLS i E1.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_223 ())).
Qed.
Lemma RETBLS : forall i k j, CH2.ret_of G.RETS i k = Some j -> (PNA.kind_of j = PNA.KErrh \/ PNA.kind_of j = PNA.KSetec) -> nth j G.BLS [] = nth i G.BLS [].
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_224 ())).
Qed.

Lemma PHASE_X : forall i c ps0 E1 R1 E' R' A1 M1 m1 M' m',
  nth_error G.CPS i = Some c -> (1 <= i <= 73)%nat ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> FLF E1 -> sbI i E1 = sb -> scapI i E1 = scap ->
  (forall a, SAFE i E1 a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) /\
  0 <= bptrI i E1 /\ bptrI i E1 + bcapI i E1 <= 2 ^ 64 /\ bptrI i E1 mod 8 = 0 /\
  (AGFIX M1 -> AGFIX M') /\ (bptrI i E1 = bptr -> bcapI i E1 = bcap -> AGBUF M1 -> AGBUF M') /\ (PHS M1 -> PHS M') /\
  (forall code, PMLA.ec_at (hl_segs L) IC M1 E code -> PMLA.ec_at (hl_segs L) IC M' E code) /\
  (forall g1, g1 <> PML.LS0 -> PMLA.ls_ok (hl_segs L) IC g1 M1 -> PMLA.ls_ok (hl_segs L) IC g1 M').
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_225 ())).
Qed.

Lemma PHASE0_X : forall i c ps0 E1 R1 E' R' A1 M1 m1 M' m',
  nth_error G.CPS i = Some c -> (1 <= i <= 73)%nat -> (CC.cp_F c = PNA.F0 \/ CC.cp_F c = PNA.CPF_N) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PNA.FFS Cred 5 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> FLF E1 -> sbI i E1 = sb -> scapI i E1 = scap ->
  (forall a, SAFE i E1 a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) /\ M' (Z_to_bv 64 (P + 211)) = M1 (Z_to_bv 64 (P + 211)) /\
  0 <= bptrI i E1 /\ bptrI i E1 + bcapI i E1 <= 2 ^ 64 /\ bptrI i E1 mod 8 = 0 /\
  (AGFIX M1 -> AGFIX M') /\ (bptrI i E1 = bptr -> bcapI i E1 = bcap -> AGBUF M1 -> AGBUF M') /\ (PH0 M1 -> PH0 M') /\ (PHS M1 -> PHS M').
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_226 ())).
Qed.

Lemma L_ERRH : LEAF PNA.PC_ERRH.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_227 ())).
Qed.
Lemma L_SETEC : LEAF PNA.PC_SETEC.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_228 ())).
Qed.

Lemma ACLX : forall LBx FFx a sp' scr', incl FF FFx -> In (sb, scap) LBx -> In (ch, 16384) LBx ->
  (P <= a < P + 272) \/ (E <= a < E + 16) \/ (V <= a < V + 8) \/ in_shadow_of P 272 a \/ in_shadow_of E 16 a \/ in_shadow_of V 8 a
  \/ (sb <= a < sb + scap) \/ in_shadow_of sb scap a \/ (ch <= a < ch + 16384) \/ in_shadow_of ch 16384 a \/ STATIC a ->
  0 <= a < 2 ^ 64 /\ aclient L ar LBx FFx sp' scr' a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_229 ())).
Qed.

Lemma FIX_OUT224 : forall a, FIXA a -> ~ (P + 224 <= a < P + 248).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_230 ())).
Qed.

Lemma UV_eaddz : forall Ex ex z, CL5A.uv Ex (APC.eaddz ex z) = (CL5A.uv Ex ex + z) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_231 ())).
Qed.
Lemma UV_eadd : forall Ex a b, CL5A.uv Ex (APC.eadd a b) = (CL5A.uv Ex a + CL5A.uv Ex b) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_232 ())).
Qed.
Lemma UV_esub : forall Ex a b, CL5A.uv Ex (APC.esub a b) = (CL5A.uv Ex a - CL5A.uv Ex b) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_233 ())).
Qed.
Lemma UV_escale2 : forall Ex ex, CL5A.uv Ex (APC.escale 2 ex) = (2 * CL5A.uv Ex ex) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_234 ())).
Qed.
Lemma UV_mul2 : forall Ex ex, CL5A.uv Ex (EMd Instr.M_MUL (ELit 2) ex) = (2 * CL5A.uv Ex ex) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_235 ())).
Qed.

Lemma STRS_mv : forall i E1 (M1 M2 : mem) s1,
  (forall a, (P + 224 <= a < P + 248) \/ (bptrI i E1 <= a < bptrI i E1 + bcapI i E1) \/ in_shadow_of (bptrI i E1) (bcapI i E1) a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  0 <= bptrI i E1 -> bptrI i E1 + bcapI i E1 <= 2 ^ 64 -> bptrI i E1 mod 8 = 0 -> bcap <= bcapI i E1 ->
  PMLA.str_at (hl_segs L) M1 (P + 224) (PML.SLong (bcapI i E1) (bptrI i E1) s1) -> shadow_blk M1 (bptrI i E1) (bcapI i E1) ->
  PMLA.str_at (hl_segs L) M2 (P + 224) (PML.SLong (bcapI i E1) (bptrI i E1) s1) /\ shadow_blk M2 (bptrI i E1) (bcapI i E1).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_236 ())).
Qed.

Lemma lor7 : forall x, 0 <= x -> Z.lor x 7 = 8 * (x / 8) + 7.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_237 ())).
Qed.
Lemma grow_cap_facts : forall cap need, 24 <= cap -> cap mod 8 = 0 -> cap <= 2 ^ 26 -> 0 <= need < 2 ^ 26 ->
  let c := PML.grow_cap cap need in 2 * cap <= c /\ need < c /\ c <= 2 ^ 27 /\ c mod 8 = 0.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_238 ())).
Qed.
Lemma log2_halves : forall cap c, 24 <= cap -> 2 * cap <= c -> c <= 2 ^ 27 -> Z.log2 (2 ^ 27 / c) + 1 <= Z.log2 (2 ^ 27 / cap).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_239 ())).
Qed.
Lemma bufcredA_push : forall cr1 cap kx' bx' need, PMSA.bufcredA L cr1 cap kx' bx' -> 24 <= cap -> cap mod 8 = 0 -> cap <= need -> need < 2 ^ 26 ->
  let c := PML.grow_cap cap need in
  acredit_ok L cr1 c /\ PMSA.bufcredA L (adebit L cr1 c) c kx' bx' /\ 2 * cap <= c /\ need < c /\ c mod 8 = 0.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_240 ())).
Qed.
Lemma bytes_sub : forall (Mx : mem) q bs kk n, L5.bytes_at (hl_segs L) Mx q bs -> (kk + n <= length bs)%nat -> L5.bytes_at (hl_segs L) Mx (q + Z.of_nat kk) (firstn n (skipn kk bs)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_241 ())).
Qed.
Lemma sr_vars_lt_forallb : forall n l, APC.sr_vars_lt n l = forallb (APC.expr_vars_lt n) l.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_242 ())).
Qed.
Lemma REGV : forall ps0 n rg ex, APC.sr_vars_lt n (CA.ps_reglist ps0) = true -> (1 <= rg <= 31)%nat -> PNA.reg_of ps0 rg = ex -> ex <> ELit (-1) -> APC.expr_vars_lt n ex = true.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_243 ())).
Qed.
Lemma nodup_notin : forall (x : Z) (l : list Z), base.NoDup (x :: l) -> ~ In x l.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_244 ())).
Qed.

Lemma BUFM : forall (M' : mem), AGBUF M' -> PMLA.str_at (hl_segs L) M' (P + 224) (PML.SLong bcap bptr buf) /\ shadow_blk M' bptr bcap /\ 264 <= bcap <= 2 ^ 27.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_245 ())).
Qed.

Lemma L_APPR : LEAF PNA.PC_APPR.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_246 ())).
Qed.

Lemma ACLP : forall LBx FFx a sp' scr', incl FF FFx -> (P <= a < P + 272) \/ (E <= a < E + 16) \/ (V <= a < V + 8) -> 0 <= a < 2 ^ 64 /\ aclient L ar LBx FFx sp' scr' a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_247 ())).
Qed.

Definition ENDW (pc : Z) : list L5.range := ltac2:(Rpl.RP.run_k (rplG ()) 1 (ParseNumberCA_blobs2.kr_b_248 ())).
Lemma ENDX_OK : forall pc, pc = PC_ENDI \/ pc = PC_ENDF ->
  forall (mw : option (Z * Z)) (LBo' : list (Z * Z)) (FF' LK' : list fframe) (cr' : credit) (A' : list (Z * Z)) (sp' r' B' kx' bx' : Z) (g0 : PML.ls_state) (ps0 : PML.pstate),
    PMSA.cps_asan L ar HI pc r' sp' PMSA.ENDNUM_SCR (PML.ps_blocks ps0 ++ LBo') FF' LK' cr' A' 4
      (fun R0 M0 => (PMSA.std_args R0 M0 P V E ps0 /\ PML.ps_more ps0 = true /\ PML.ps_st ps0 = PML.ST_NUMBER /\ PML.num_final (PML.ps_buf ps0)) /\ (true = true -> sp' mod 32 = 0) /\ PMSA.stksh ar M0 sp' PMSA.ENDNUM_SCR /\
                  PMSA.parser_at L IC M0 P (PML.ps_set_win ps0 mw) /\ PMSA.parser_sh M0 ps0 /\ PMCUR.wf_c_stale ps0 /\ PMSA.win_okA M0 LBo' ps0 /\ PMSA.buf_bound_stale ps0 B' /\ PMSA.vis_at L IC M0 V /\ PMSA.ec_at L IC M0 E 0 /\ PMSA.ls_ok L IC g0 M0 /\ g0 <> PML.LS0 /\
                  PMLA.pcredit_xA L cr' ps0 kx' bx' /\ PMSA.fobj M0 FF' P 272 /\ PMSA.fobj M0 FF' V 48 /\ PMSA.fobj M0 FF' E 16 /\
                  PMLA.apart P 272 V 48 /\ PMLA.apart P 272 E 16 /\ PMLA.apart V 48 E 16)
      (fun R0 M0 R' M' LB' cr'' LBk W => exists (ps' : PML.pstate) (code : Z) (g' : PML.ls_state),
          (PMSA.parser_at L IC M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps0) /\ PMSA.parser_sh M' ps' /\ PMCUR.wf_c ps' /\ PMSA.win_okA M' LBo' ps' /\ PML.buf_bound ps' B' /\ PMSA.ec_at L IC M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
          PMSA.ls_ok L IC g' M' /\ (g' = g0 \/ (g' = PML.regJ g0 /\ code <> 0)) /\
          LB' = PML.ps_blocks ps' ++ LBo' /\ LBk = LBo' /\ W = ENDW pc /\ PMLA.pcredit_xA L cr'' ps' kx' bx' /\
          ((code = 0 /\ PML.ps_more ps' = false /\ PML.ps_st ps' = (if Z.eqb (PML.ps_level ps0) 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\
            PML.ps_stack ps' = PML.ps_stack ps0 /\ PML.ps_level ps' = PML.ps_level ps0 /\ PML.ps_win ps' = PML.ps_win ps0) \/ code = 19) /\
          PMCUR.cur_post (hl_segs L) ps0 ps' code M' V).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_249 ())).
Qed.

Lemma L_END : forall pc, pc = PC_ENDI \/ pc = PC_ENDF -> LEAF pc.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_250 ())).
Qed.

Lemma XI0 : XI 0 E0 A M model.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_251 ())).
Qed.

Lemma main : srealizes (hl_segs L) SCFG (@PMSA.cfg L fx R PNA0.PC M model) K.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_252 ())).
Qed.

End PnMain.

Section Ex.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Lemma ex_un : forall (M : mem) a (n : nat), (n <= 8)%nat -> L5.defined M a (Z.of_nat n) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  exists v, 0 <= v < 2 ^ (8 * Z.of_nat n) /\ rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_253 ())).
Qed.
Lemma ex_u32 : forall (M : mem) a, L5.defined M a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> exists v, 0 <= v < 2 ^ 32 /\ L5.u32_at segs M a v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_254 ())).
Qed.
Lemma ex_u64 : forall (M : mem) a, L5.defined M a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at segs M a v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_255 ())).
Qed.
Lemma ex_u8 : forall (M : mem) a, L5.defined M a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 -> exists v, 0 <= v < 2 ^ 8 /\ L5.u8_at segs M a v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_256 ())).
Qed.

Lemma defined_bytes_r : forall (M : mem) p (n : nat), L5.defined M p (Z.of_nat n) ->
  exists bs, length bs = n /\ L5.bytes_at segs M p bs /\ Forall (fun c => 0 <= c < 256) bs.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (ParseNumberCA_blobs2.kr_b_257 ())).
Qed.
End Ex.

Theorem parse_number_ok {SCFG_P : ScfgP} (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (IL0 : icpt_layout) :
  PmHeapIfaceA.asan_iface_ok L ar C SCFG HI -> L5A.as0_layout L C -> rt_img_shadow L IL0 HI ->
  Forall (fun r : Z * Z => SLOT2 + 8 <= fst r \/ snd r <= SLOT2) (icl_poison IL0) ->
  Forall (fun r : Z * Z => TLO + 264 <= fst r \/ snd r <= TLO) (icl_poison IL0) ->
  (forall a, PMLA.in_foot PMLA.C_casan a -> ~ hl_rt_static L a) ->
  hl_stack_malloc L 1 = PC_SM ->
  (forall (fx fx' : FPState) R pc M R' pc' M', msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx') ->
  PMSA.str_append_range_specA L ar HI PC_APPR -> PMSA.end_integer_value_specA L ar HI PMLA.C_casan PC_ENDI -> PMSA.end_fraction_value_specA L ar HI PMLA.C_casan PC_ENDF ->
  PMSA.errh_specA L ar HI PC_ERRH -> PMSA.set_ec_specA L ar HI PMLA.C_casan PC_SETEC ->
  hl_tp L = 6883920 -> (forall a, ERRNO <= a < ERRNO + 4 -> ~ hl_rt_static L a) ->
  PMSA.parse_number_specA L ar HI PMLA.C_casan PC.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 6 (ParseNumberCA_blobs2.kr_b_258 ())).
Qed.
