(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AxSymExec3 AxSymExec3Sound HeapIface LibIface L5Defs L5Core.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmCurDefs_u PmLibSpecs_u PmLayout_u PmLibSanity_u PmCurSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutLib.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ChunkKit_u CCtorTail_u HarnessCStretch_u.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Rpl.
Ltac2 rplG () : string array := Array.of_list ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Numbers.BinNums.Z0"; "Stdlib.ZArith.Zbitwise.Z.add_lor_land"; "Corelib.Numbers.BinNums.Zpos"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.land"; "Corelib.Init.Logic.eq_ind_r"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq_refl"; "Stdlib.ZArith.BinInt.Z.ones"; "Stdlib.ZArith.BinInt.Z.land_ones"; "Corelib.Init.Datatypes.nil"; "Stdlib.micromega.ZMicromega.ZArithProof"; "Corelib.Init.Datatypes.list"; "Stdlib.micromega.VarMap.Empty"; "Stdlib.micromega.VarMap.t"; "Stdlib.micromega.Tauto.A"; "Stdlib.micromega.RingMicromega.Formula"; "Stdlib.micromega.Tauto.eKind"; "Corelib.Init.Datatypes.unit"; "Stdlib.micromega.Tauto.isProp"; "Stdlib.micromega.RingMicromega.Build_Formula"; "Stdlib.micromega.EnvRing.PEc"; "Stdlib.micromega.RingMicromega.OpLe"; "Corelib.Init.Datatypes.tt"; "Stdlib.micromega.Tauto.BFormula"; "Stdlib.micromega.ZMicromega.ZTautoChecker_sound"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.true"; "Stdlib.micromega.ZMicromega.ZTautoChecker"; "Stdlib.micromega.VarMap.find"; "Corelib.Init.Logic.eq_ind"; "Stdlib.ZArith.BinInt.Z.mod_pos_bound"; "Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg"; "Stdlib.micromega.RingMicromega.OpLt"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.cons"; "Stdlib.micromega.ZMicromega.RatProof"; "Stdlib.micromega.RingMicromega.PsatzAdd"; "Stdlib.micromega.RingMicromega.PsatzIn"; "Stdlib.micromega.RingMicromega.PsatzMulC"; "Stdlib.micromega.EnvRing.Pc"; "Corelib.Numbers.BinNums.Zneg"; "Corelib.Numbers.BinNums.xH"; "Corelib.Init.Datatypes.O"; "Stdlib.micromega.ZMicromega.DoneProof"; "Stdlib.micromega.VarMap.Branch"; "Stdlib.micromega.VarMap.Elt"; "Stdlib.micromega.Tauto.IMPL"; "Stdlib.micromega.Tauto.AND"; "Stdlib.micromega.EnvRing.PEX"; "Corelib.Init.Datatypes.None"; "Stdlib.micromega.EnvRing.PEadd"; "Stdlib.micromega.RingMicromega.OpEq"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.lor7_bounds"; "Stdlib.ZArith.BinInt.Z.eqb_spec"; "Corelib.Init.Datatypes.reflect"; "Stdlib.ZArith.BinInt.Z.eqb"; "Corelib.Init.Logic.not"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.str_cap"; "Stdlib.ZArith.BinInt.Z.max"; "Stdlib.ZArith.BinInt.Z.max_spec"; "Corelib.Init.Logic.or"; "Stdlib.micromega.Tauto.OR"; "Stdlib.micromega.Tauto.X"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.copy_cap"; "Stdlib.ZArith.BinInt.Z.divide"; "Stdlib.ZArith.BinInt.Z.mod_divide"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.micromega.Tauto.NOT"; "Corelib.Init.Logic.False"; "Stdlib.ZArith.BinInt.Z.divide_sub_r"; "Stdlib.ZArith.BinInt.Z.divide_trans"; "Corelib.Init.Logic.ex_intro"; "Stdlib.ZArith.BinInt.Z.mul"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.range"; "Corelib.Init.Datatypes.list_ind"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.outside"; "Corelib.Init.Logic.ex"; "Stdlib.Lists.List.In"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.in_rng"; "Corelib.Init.Logic.False_ind"; "Stdlib.Logic.Classical_Prop.classic"; "Corelib.Init.Logic.conj"; "Corelib.Init.Logic.or_introl"; "Corelib.Init.Logic.or_intror"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Npos"; "Corelib.Init.Datatypes.option"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.frame_but"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.Logic.FunctionalExtensionality.functional_extensionality"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.mod_mul"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Logic.True"; "Corelib.Init.Logic.I"; "Stdlib.ZArith.BinInt.Z.mul_comm"; "Stdlib.ZArith.BinInt.Z.testbit"; "Stdlib.ZArith.BinInt.Z.b2z"; "Stdlib.ZArith.BinInt.Z.mod_pow2_bits_low"; "Stdlib.ZArith.BinInt.Z.bit0_mod"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.u8_at"; "OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Ubsan.M.loaded_segments"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.rdn"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.f_equal"; "stdpp.bitvector.definitions.bv_wrap"; "stdpp.bitvector.definitions.Z_to_bv_unsigned"; "Stdlib.ZArith.BinInt.Z.mod_small"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.lstr_short"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.bytes_at"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.u64_at"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.u64_u8_low"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.u8"; "Stdlib.micromega.ZifyClasses.rew_iff"; "Stdlib.micromega.ZifyClasses.mkrel"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.Znat.Nat2Z.inj_le"; "Stdlib.ZArith.Znat.Nat2Z.is_nonneg"; "Stdlib.ZArith.BinInt.Z.pow_pos_nonneg"; "Stdlib.ZArith.BinInt.Z.pow_nonneg"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.land1_even"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.u8_inj"; "Stdlib.micromega.ZMicromega.CutProof"; "Stdlib.micromega.RingMicromega.PsatzMulE"; "Stdlib.micromega.RingMicromega.PsatzC"; "Stdlib.micromega.EnvRing.PEmul"; "stdpp.bitvector.definitions.BV"; "stdpp.bitvector.definitions.BvWf"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.callee_saved_idx"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.ridx"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.KOH"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.ChunkKit_u.CK.CSR"; "Corelib.Init.Logic.or_ind"; "stdpp.bitvector.definitions.bv_unsigned_in_range"; "stdpp.bitvector.definitions.bv_modulus"; "Corelib.Init.Logic.and_ind"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Logic.iff_sym"; "Stdlib.ZArith.Znat.Nat2Z.inj_iff"; "Stdlib.micromega.ZifyClasses.mkapp"; "Stdlib.micromega.ZifyInst.of_nat_to_nat_eq"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.regs_preserved"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit_u.TK.keepsR_preserved"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit_u.TK.keepsR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.ChunkKit_u.CK.keepsR_sub"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.KOH_CSR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit_u.TK.keepsR_trans"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.getr"; "Corelib.Init.Logic.eq_sym"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3Sound.AX2S.ridx_roundtrip"; "stdpp.base.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.app"; "stdpp.base.elem_of"; "stdpp.base.list_elem_of"; "stdpp.base.list_elem_of_In"; "Stdlib.Lists.List.in_map"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.lb_remove"; "stdpp.tactics.f_equal_help"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.credit"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.heap_iface"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.heap_layout"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.ScfgP"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.heap_iface_ok"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.SCFG"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.hi_heap"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.hio_perm"; "Corelib.Init.Logic.iff"; "Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism"; "Corelib.Classes.RelationClasses.iff_Transitive"; "Corelib.Classes.Morphisms.eq_proper_proxy"; "Stdlib.Lists.List.in_app_iff"; "Corelib.Classes.Morphisms.Reflexive_partial_app_morphism"; "Corelib.Classes.Morphisms.respectful"; "Corelib.Classes.Morphisms_Prop.or_iff_morphism"; "Corelib.Classes.Morphisms.reflexive_proper_proxy"; "Corelib.Classes.Morphisms.reflexive_reflexive_proxy"; "Corelib.Classes.RelationClasses.iff_Reflexive"; "Corelib.Classes.Morphisms.trans_sym_co_inv_impl_morphism"; "Corelib.Classes.RelationClasses.Equivalence_PER"; "Corelib.Classes.RelationClasses.iff_equivalence"; "Corelib.Init.Datatypes.prod_ind"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.hio_wf"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.block_range"; "Corelib.Init.Datatypes.snd"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.defined"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.blocks_apart"; "Stdlib.Sorting.Permutation.Permutation_map"; "Stdlib.Sorting.Permutation.Permutation_app_swap_app"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Logic.proj1"; "stdpp.list_relations.list.NoDup_Permutation_proper"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.ra_ok"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.TP"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Core.L5C.stk"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.hl_sptop"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.FR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.client_addr"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.in_errno"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.defined"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.add_mod"; "Stdlib.ZArith.BinInt.Z.add_opp_r"; "Stdlib.micromega.EnvRing.PEopp"; "Stdlib.micromega.EnvRing.PEsub"; "Stdlib.micromega.EnvRing.PEpow"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.model_but_vm"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.model_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Core.L5C.halted_but_vm"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Core.L5C.lazy_but_vm"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Core.L5C.materialized_but_vm"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.src_at"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.u64"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.b2z"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.iosb_at"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.CLASSIC_IMP"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.source_at"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit_u.TK.samem"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.cov"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.u64_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.cov_sub"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.iosb_at_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.pstate"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.ps_cov"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.cursor_at"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.parser_at"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.vis_at"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.CURSOR_SIZE"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.u8_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.parser_at_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.vis_at_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.LIB_SCR_C"; "Stdlib.ZArith.BinInt.Z.le_max_l"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.CCTOR_SCR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.GETSTR_SCR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibSpecs_u.PMS.ISS_SCR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibSpecs_u.PMS.OPDEL_SCR"; "Stdlib.ZArith.BinInt.Z.le_max_r"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibSpecs_u.PMS.OPNEW_SCR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.ll_stack"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibSpecs_u.PMS.CTOR_SCR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.RN_SCR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.CCTOR_MAIN_SCR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.srep"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.str_at_w"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.str_cov"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.pers"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.str_at_w_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.StoreOk.mem_grows"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.srep_blocks"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.in_foot11"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.statics_cov"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.w_si"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.blocks_ok_heap"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.blocks_ok"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.pers_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.str_cov_out"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.FR_grows"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.not_outside"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.heap_stack_write"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit_u.TK.samem_weaken"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.statics_cov_out"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Core.L5C.hpres"; "Stdlib.Lists.List.incl"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.w_ok"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.keepH"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.mk_stk"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.hpres_samem"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.in_block"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.str_cov_keepH"; "Stdlib.Lists.List.in_or_app"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.FR_hpres"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.CCtorTail_u.CCTL.u64_of_defined"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.SCRv"; "stdpp.bitvector.definitions.Z_to_bv_bv_unsigned"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.FPState"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ls_state"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.fp_ok"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ls_ok"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.credit_le"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.credit_sub"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.ll_credit"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.LIB_POST"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibSpecs_u.PMS.pm_statics"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.ChunkKit_u.CK.rp_of_keeps"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.csr_of"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.ll_heap"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.in_foot"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ll_foot_csrc"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.ll_foot"; "Corelib.Init.Logic.proj2"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.R_LOCDTOR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.SpinAlg.srealizes"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.cfg"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.PC_LOCALE_DTOR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.ChunkKit_u.CK.spok"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.KO_4"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.entry"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.a0"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.mk_entry"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.ra_ok_lit"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.CS2"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.KT"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.KSP"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_rlocdtor"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.R_ISTRDTOR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.samem_all"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.PC_ISTREAM_DTOR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.KCO"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_ristrdtor"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.R_IOSBDTOR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.PC_IOSB_DTOR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopSpecs_u.TPS.IOSB_SCR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.obj_on_stack"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.al8"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.frame_but_samem"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.step_out_g"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.ls_ok_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.SShort"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.frame_word"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_riosbdtor"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.BR_S"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.sso_bit"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_ss"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.fin"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.SLong"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.lstr_long"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.hl_img_lo"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.hl_img_hi"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.land1_odd_low"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_sl"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.R_OPDEL_S"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.PC_OPDEL_SIZED"; "Stdlib.ZArith.BinInt.Z.eqb_refl"; "Stdlib.Lists.List.incl_refl"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.statics_cov_keepH"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.IMG_RO_HI"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_ropdel_s"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Core.L5C.model_but_vm_trans"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.frame_but_nil0"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.R_PDTOR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ps_blocks"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.isrc_at"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.PC_PARSER_DTOR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.img_ro"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.libc_quiet"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.foot_pristine"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.atexit_cells"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.loc_done"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.errcat_guard"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.jbit"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.convcat_guard"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.cbit"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ls_atexit"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.step_heap"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.isrc_at_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.source_at_xd"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.frame_def"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_rpdtor"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.R_SDTOR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.PC_SOURCE_DTOR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.VT_ISS"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.VT_STRINGBUF"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.srep_data"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.srep_chars"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.str_at"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.u32"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.VT_ISS_IOS"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.tail1"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_rsdtor"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.VTT_ISS"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.VT_ISS0"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.VT_SBUF0"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.VT_IOS0"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.BR_SB"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.iosb_at_xg"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_sbs"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.VT_SBUF1"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_sbl"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.R_OPDEL_SB"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_ropdel_sb"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.sbit"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.KEX"; "Corelib.Init.Datatypes.false"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.kex_out"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.tail0"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.ps_cov_out"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.src_source"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ps_done"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.BR_S2"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.VT_PARSER"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.VT_FUNC"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ps_level"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ps_win"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ps_st"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ps_sst"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ps_nst"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ps_more"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ps_bcap"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ps_bptr"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ps_buf"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ps_sb"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ps_stack"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ps_scap"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.b2z_0"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.b2z_land"; "Corelib.Init.Logic.eq_trans"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_s2s"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.b2z_rng"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.R_GET"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.PC_GET_STRING"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.VT_CURSOR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.VT_CURSOR_SER"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.exitk"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_s2l"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.R_OPDEL_S2"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.mok_of"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.cursor_at_xd"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.ps_cov_keepH"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.u32_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_test_opdel"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.wf_ps"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ST_ROOT"; "Corelib.Lists.ListDef.Forall"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.is_container"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.handled"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.transient"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ST_EXPECT_COMMA_OR_END"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ST_NUMBER"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.num_prefix"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.ps_set_more"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.pcredit_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.pcredit"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.kleft"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.hl_k_per_malloc"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.bleft"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.hl_b_overhead"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLayout_u.PmLayout.ly_kpm"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLayout_u.PmLayout.ly_bov"; "Stdlib.ZArith.BinInt.Z.log2_nonneg"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.log2"; "Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg"; "Stdlib.micromega.Tauto.FF"; "Stdlib.ZArith.BinInt.Z.mul_nonneg_nonneg"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ST_ACCEPT"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.rn_bound"; "Corelib.Init.Datatypes.andb"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ST_STRING"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.esc_need"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.undelivered"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.win_ok"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.defined_sub"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.sevent"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.wf_c"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.lvl_ok"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.ev_rel"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.conv_ok"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.after_value_st"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.ICS"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ST_EXPECT_MEMBER_NAME_OR_END"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ST_EXPECT_MEMBER_NAME"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ST_EXPECT_COLON"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ST_EXPECT_VALUE_OR_END"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ST_EXPECT_VALUE"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ST_MEMBER_NAME"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.EvNull"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.EvBool"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.EvI64"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.EvU64"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.EvDbl"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.EvStr"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.txt_ok"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.EvKey"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.EvBeginObj"; "Stdlib.micromega.Tauto.TT"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.EvEndObj"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.EvBeginArr"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.EvEndArr"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.LS0"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ec_at"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.evc"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.ec_at_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.CCtorTail_u.CCTL.evc_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.CCtorTail_u.CCTL.win_ok_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.evp"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurDefs_u.PMCUR.ev_at"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.ev_lvl0"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.winlen"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.buf_need"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.ev_src"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.str_cap_bounds"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.pcx_lb"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.scap_sm"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.credit_ok"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.a1"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.a3"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.apart"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.s2_post"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.regC"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Core.L5C.fresh_block"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.debit"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.in_foot11_iv"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.CS9"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.sbit_word"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.u32_at"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_rget"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.R_RN"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.PC_READ_NEXT_C"; "Stdlib.Lists.List.app_assoc"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.heap_swap"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.a2"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.RN0"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.win_ok_heap"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.rn_bound_sm"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.OBJ_JSON_CATEGORY"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.nodup_mid"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.regJ"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.rn_rel"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.ST_DONE"; "Stdlib.ZArith.BinInt.Z.eq_dec"; "Corelib.Init.Specif.sumbool"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_rrn"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.brs2"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.scap_wf"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_g11"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.pm_credit_c"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.PC_LIB"; "Stdlib.Lists.List.length_map"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLayout_u.PmLayout.ly_img_lo"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLayout_u.PmLayout.ly_img_hi"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_entry"; "Stdlib.micromega.ZifyClasses.or_morph"; "Stdlib.micromega.ZifyClasses.eq_iff"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.R_STRINIT"; "Stdlib.Logic.Classical_Prop.NNPP"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.lib_post"; "Corelib.Init.Peano.lt"; "Stdlib.ZArith.Znat.Nat2Z.inj_lt"; "Corelib.Lists.ListDef.nth"; "Stdlib.micromega.ZifyClasses.and_morph"; "Corelib.Init.Logic.iff_refl"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit_u.TK.bytes_samem"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.L5Core.L5C.rdn_bytes_at"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.PC_STRINIT"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.copy_cap_bounds"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.statics_cov_lo"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_rstrinit"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.R_ISS"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.PC_ISS_CTOR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibSpecs_u.PMS.ISLAND_SCR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibSpecs_u.PMS.statics_mid"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibSanity_u.ls_mid"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_riss"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.R_SYSCAT"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.PC_SYSTEM_CATEGORY"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.statics_mid_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibSpecs_u.PMS.gloc_done"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibDefs_u.PML.OBJ_SYSTEM_CATEGORY"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.heap_pure_write"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.mid_to_ls"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_rsyscat"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCT.R_CCTOR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.PC_CURSOR_CTOR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.TopKit2_u.TK2.gloc_done_x"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibSpecs_u.PMS.ps_init"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibSanity_u.bleft_init"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibSanity_u.kleft_init"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.CCtorTail_u.CCTL.regJ_ne"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessCStretch_u.HCS.s_h_test_cctor"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.Run.body"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.lib_layout"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.pm_layout_ok_c"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.ll_entry"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.ll_gp"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.ll_rw_lo"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLibSpecs_u.PMS.lib_call_ok_fp"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.ls_state"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.ShapeAlg.TSet"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.lib_pre"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.hl_segs"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.lib_cfg"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.hl_tp"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.ll_empty"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibIface.ls_ok"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLayout_u.PmLayout.ly_tp"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmLayout_u.PmLayout.ly_segs"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.mkst"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.seg_rom"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop.HarnessC_u.HNC.H.run_ok"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmCurSpecs_u.PMCS.lib_spec_c"].

Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module HNC.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Lemma lor7_bounds : forall x, 0 <= x -> x <= Z.lor x 7 <= x + 7.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "U27;A1;o4;Y2;3;A2;k6;r2;#0;Y1;0;Y1;1;A1;o4;#3;A1;o4;Y3;0;A2;k10;r4;#5;A2;k10;r3;#5;A1;o15;i16;A1;i17;i16;A1;o18;i0;A1;i19;i0;A1;i21;i0;A2;o26;i0;o2;A2;k29;#12;o24;A4;k30;r1;r3;cvA2;o12;i31;o32;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;A2;o26;i0;#5;A2;k10;r5;#5;N2;N1;A2;o44;i0;#19;A2;o44;i0;o49;A2;o55;i0;#3;A1;o56;i23;A2;o55;i0;#2;A2;o55;i0;o48;A3;o57;i0;#25;A2;o26;i0;#0;Lx;Ri0;LHx;RA2;k1;o2;r1;EH;RA2;k3;r2;#0;A3;i5;i0;A2;k6;A2;k7;r2;#0;A2;k8;r2;#0;#1;EL;RA6;k9;i0;A2;k10;r3;A2;k11;A1;o4;#2;#4;Lz;Ri0;A3;i5;i0;r1;#6;A2;o12;i0;#7;A2;k8;r3;A1;k13;#4;A3;k14;r3;#4;E__arith;RE__wit;R#8;#9;E__varmap;R#10;#11;E__ff;RA7;o20;#12;k22;i23;i23;o24;A4;o25;i0;#13;o27;A2;o26;i0;#4;o28;#14;#15;A2;k1;o2;#4;r1;A3;i5;i0;A2;k8;r3;#0;#7;EH;RA6;k35;i0;A2;k8;r4;#0;Lz;Ri0;A3;i5;i0;A2;k6;A2;k7;r5;#0;r1;A2;k6;r5;#0;r2;#6;r1;A3;i5;i0;A2;k6;A2;k7;r4;#0;#6;A2;k6;r4;#0;EH0;RA3;k36;r5;#5;E__sat0;RA3;k37;r5;#5;r4;P~RA2;k1;o2;#5;A2;k1;o2;A2;k10;r6;#5;E__arith;RE__wit;R#8;#9;E__varmap;R#10;#11;E__ff;RA7;o20;#12;k22;i23;i23;o24;A4;o25;i0;#13;o38;#16;o28;#14;#15;A2;k39;o2;#5;r1;A2;i40;A2;k1;o2;#17;A2;k39;#17;#5;Ea;RA2;k7;r6;#0;i0;Em;RA2;k10;r7;#5;i0;E__arith;RL__x3;Ri0;L__x2;Ri0;L__x1;Ri0;E__wit;RA3;o41;i16;A2;o42;A3;o43;i0;A2;o44;i0;#18;A3;o43;i0;A3;o45;i0;A2;o46;i0;A1;o47;o48;#20;#21;o50;A3;o41;i16;A2;o42;A3;o43;i0;A2;o44;i0;N3;A3;o43;i0;#20;#21;o50;#8;#9;E__varmap;RA4;o51;i0;A2;o52;i0;r3;r2;A2;o52;i0;r4;#11;E__ff;RA8;o53;#12;k22;i23;i23;o24;A7;o54;#12;k22;i23;i23;o24;A7;o20;#12;k22;i23;i23;o24;A4;o25;i0;#13;o27;#22;o28;A7;o20;#12;k22;i23;i23;o24;A4;o25;i0;#22;o38;#16;o28;#23;A8;o53;#12;k22;i23;i23;o24;A7;o20;#12;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#24;#22;o58;#26;o28;#23;A7;o54;#12;k22;i23;i23;o24;A7;o20;#12;k22;i23;i23;o24;A4;o25;i0;#25;o27;#24;o28;A7;o20;#12;k22;i23;i23;o24;A4;o25;i0;#24;o27;#26;o28;#14;#15;P__x3;Ri0;P__x2;Ri0;P__x1;Ri0;P~RA2;i40;A2;k1;o2;r3;A2;k39;r3;#5;P~RA3;i5;i0;A2;k6;r3;r4;#1;A2;i40;A2;k1;r3;r4;A2;k1;r4;A2;k6;r3;#0;A5;r1;r2;r3;r9;r4;r5;").
Qed.
Lemma str_cap_bounds : forall n, 0 <= n -> n < PML.str_cap n <= n + 10.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S33;A1;o4;Y2;3;A2;k7;r2;#0;A2;k6;r2;#0;A2;k7;r3;#0;A1;o4;Y4;7;A1;o4;Y4;a;A1;o4;o48;m31;RNL~Ri31;i0;r2;2;#5;A2;k6;A2;k7;r7;#0;#6;A1;o4;Y3;2;A3;i5;i0;A2;k7;r6;#0;#4;A2;o44;i0;N3;N2;A2;o44;i0;o49;N1;A1;o15;i16;A1;i17;i16;A4;o51;i0;A2;o52;i0;r3;r2;A1;o18;i0;A1;i19;i0;A1;i21;i0;Y1;0;A2;o55;i0;#19;A1;o56;i23;A2;o55;i0;o48;A7;o54;#18;k22;i23;i23;o24;A7;o20;#18;k22;i23;i23;o24;A4;o25;i0;#22;o27;#20;o28;A7;o20;#18;k22;i23;i23;o24;A4;o25;i0;#20;o27;A3;o57;i0;#22;A2;o26;i0;#0;o28;A2;o26;i0;#5;A3;o57;i0;#22;A2;o26;i0;#8;A2;k29;#18;o24;A4;k30;r1;r3;cvA2;o12;i31;o32;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;A2;k7;r8;#0;A3;o57;i0;#20;A2;o26;i0;#6;A2;k6;r3;#6;A2;k6;r2;#8;A1;k64;r2;Ln;Ri0;LHn;RA2;k1;o2;r1;cdEH;RA2;k59;r2;r1;A2;i40;A2;k1;r2;#1;A2;k1;#1;#2;Er;RA2;k60;#3;#4;A2;i61;A3;i5;i0;#3;#4;A2;k62;#3;#4;Eb;RA2;k62;A2;k7;r4;#0;#4;i31;m61;RNLb;Ri31;Lr;RA2;i61;A3;i5;i0;A2;k7;r6;#0;#4;r1;A2;i40;A2;k39;r7;#7;A2;k1;#7;A2;k6;r7;#8;r2;2;Le;RA3;i5;i0;A2;k7;r5;#0;#4;A1;Le;R#9;E__arith;RL__x2;Ri0;L__x1;Ri0;E__wit;RA3;o41;i16;A2;o42;A3;o43;i0;#10;A3;o43;i0;A2;o44;i0;#11;#12;o50;A3;o41;i16;A2;o42;A3;o43;i0;A3;o45;i0;A2;o46;i0;A1;o47;o48;#10;A3;o43;i0;A2;o44;i0;#13;#12;o50;#14;#15;E__varmap;R#16;#17;E__ff;RA8;o53;#18;k22;i23;i23;o24;A7;o20;#18;k22;i23;i23;o24;A4;o25;i0;#20;o58;A2;o26;i0;#4;o28;#21;A8;o53;#18;k22;i23;i23;o24;#23;#21;A7;o54;#18;k22;i23;i23;o24;A7;o20;#18;k22;i23;i23;o24;A4;o25;i0;#22;o38;#24;o28;A7;o20;#18;k22;i23;i23;o24;A4;o25;i0;#24;o27;#25;o28;#26;#27;P__x2;Ri0;P__x1;Ri0;P~RA3;i5;i0;r2;#4;P~RA2;i40;A2;k1;r2;r3;A2;k1;r3;#2;A2;i40;A2;k39;r3;#5;A2;k1;#5;A2;k6;r3;#8;A4;r1;#28;r8;r2;r6;r1;Ln;RA1;k63;A3;i5;i0;A2;k7;r5;#0;#4;A1;Ln0;RA1;k63;#9;E__arith;RL__x2;Ri0;L__x1;Ri0;E__wit;R#14;#15;E__varmap;R#16;#17;E__ff;RA8;o53;#18;k22;i23;i23;o24;#23;#21;A7;o54;#18;k22;i23;i23;o24;A7;o20;#18;k22;i23;i23;o24;A4;o25;i0;#22;o38;#29;o28;A7;o20;#18;k22;i23;i23;o24;A4;o25;i0;#29;o27;#25;o28;#26;#27;P__x2;Ri0;P__x1;Ri0;P~RA2;i40;A2;k1;r1;r2;A2;k1;r2;A2;k6;r1;#0;A2;i40;A2;k39;r2;#30;A2;k1;#30;#31;A3;r1;#28;r8;r6;r1;A2;i40;A2;k39;r2;#32;A2;k1;#32;#31;").
Qed.
Lemma copy_cap_bounds : forall n, 0 <= n -> 0 < PML.copy_cap n <= n + 52.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S38;A1;o4;Y5;0c;A2;k65;r2;#0;A2;k1;#0;r2;A2;k65;r3;#0;N2;A2;o44;i0;#4;A2;o46;i0;A1;o47;o48;N1;A2;o44;i0;#7;A2;o44;i0;o49;A3;o43;i0;A3;o45;i0;#6;#8;#9;A1;o15;i16;A1;i17;i16;A2;o52;i0;r3;A1;i19;i0;A1;i21;i0;A2;o55;i0;o48;A2;o26;i0;#0;Y1;0;A2;o55;i0;#18;A7;o20;#15;k22;i23;i23;o24;A4;o25;i0;#17;o27;#19;o28;A1;o56;i23;A2;o26;i0;o2;A2;k29;#15;o24;A4;k30;r1;r3;cvA2;o12;i31;o32;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;A1;o4;Y2;3;A2;k7;#1;#25;N4;A2;o44;i0;#27;N3;A3;o43;i0;A3;o45;i0;#6;#28;A3;o43;i0;A2;o44;i0;#29;#9;Y1;1;A2;o55;i0;#31;A1;o4;o48;A3;o57;i0;#16;A2;o26;i0;#33;A1;o4;Y5;14;A2;k6;r4;#33;A1;k70;r2;Ln;Ri0;LHn;RA2;k1;o2;r1;cdEH;RA2;k59;#1;EH0;RA2;k66;r2;#0;A2;i67;A2;i40;A2;k39;r2;#0;A3;i5;i0;#1;#0;A2;i40;#2;A3;i5;i0;#1;r2;Ez0;R#3;i0;E__arith;RL__p1;RpL__x2;Ri0;L__x1;Ri0;E__wit;RA3;o41;i16;A2;o42;A3;o43;i0;#5;#10;o50;A3;o41;i16;A2;o42;#10;o50;#11;#12;E__varmap;RA4;o51;i0;#13;r2;A1;o18;i0;#14;E__ff;RA8;o53;#15;k22;i23;i23;o24;A7;o68;#15;k22;i23;i23;o24;A7;o54;#15;k22;i23;i23;o24;A6;o69;#15;k22;i23;i23;o24;r5;A7;o20;#15;k22;i23;i23;o24;A4;o25;i0;#16;o58;#17;o28;A7;o54;#15;k22;i23;i23;o24;#20;A7;o20;#15;k22;i23;i23;o24;A4;o25;i0;#16;o58;#19;o28;#21;A7;o20;#15;k22;i23;i23;o24;A4;o25;i0;#22;o27;#16;o28;#23;#24;P__p1;RpP__x2;Ri0;P__x1;Ri0;P~RA2;i67;A2;i40;r3;A3;i5;i0;r1;#0;A2;i40;#2;A3;i5;i0;r1;r2;A2;k1;o2;r2;A4;r1;A2;k39;r5;#0;r5;r2;r3;A2;i40;A2;k1;#1;#26;A2;k1;#26;A2;k6;#1;#25;EH0;RA2;k66;r3;#0;A2;i67;A2;i40;A2;k39;r3;#0;A3;i5;i0;#3;#0;A2;i40;A2;k1;#0;r3;A3;i5;i0;#3;r3;Ez0;RA2;k65;r4;#0;i0;E__arith;RL__p1;RpL__x3;Ri0;L__x2;Ri0;L__x1;Ri0;E__wit;RA3;o41;i16;A2;o42;A3;o43;i0;A2;o44;i0;N5;#30;o50;A3;o41;i16;A2;o42;A3;o43;i0;#28;A3;o43;i0;#5;#9;o50;A3;o41;i16;A2;o42;A3;o43;i0;#28;A3;o43;i0;#5;A3;o43;i0;#8;#9;o50;A3;o41;i16;A2;o42;#30;o50;#11;#12;E__varmap;RA4;o51;i0;#13;r2;A2;o52;i0;r4;#14;E__ff;RA8;o53;#15;k22;i23;i23;o24;A7;o68;#15;k22;i23;i23;o24;A7;o54;#15;k22;i23;i23;o24;A6;o69;#15;k22;i23;i23;o24;r6;A7;o20;#15;k22;i23;i23;o24;A4;o25;i0;#32;o58;#17;o28;A7;o54;#15;k22;i23;i23;o24;#20;A7;o20;#15;k22;i23;i23;o24;A4;o25;i0;#32;o58;#19;o28;#21;A8;o53;#15;k22;i23;i23;o24;A7;o54;#15;k22;i23;i23;o24;A7;o20;#15;k22;i23;i23;o24;A4;o25;i0;#32;o27;#16;o28;A7;o20;#15;k22;i23;i23;o24;A4;o25;i0;#16;o27;A3;o57;i0;#32;A2;o26;i0;#25;o28;#21;A8;o53;#15;k22;i23;i23;o24;A7;o20;#15;k22;i23;i23;o24;A4;o25;i0;#22;o27;#19;o28;#21;A7;o54;#15;k22;i23;i23;o24;A7;o20;#15;k22;i23;i23;o24;A4;o25;i0;#22;o38;#34;o28;A7;o20;#15;k22;i23;i23;o24;A4;o25;i0;#34;o27;A3;o57;i0;#19;A2;o26;i0;#35;o28;#23;#24;P__p1;RpP__x3;Ri0;P__x2;Ri0;P__x1;Ri0;P~RA2;i67;A2;i40;r4;A3;i5;i0;r3;#0;A2;i40;#2;A3;i5;i0;r3;r2;P~RA2;i40;A2;k1;r4;r2;A2;k1;r2;A2;k6;r4;#25;P~RA2;k1;o2;r4;A2;i40;A2;k39;o2;#36;A2;k1;#36;A2;k6;r5;#35;A7;r1;A2;k39;r6;#0;r2;r6;A2;k7;r2;#25;r3;r4;r5;A2;i40;A2;k39;o2;#37;A2;k1;#37;A2;k6;r2;#35;").
Qed.

Lemma al8 : forall sp k, sp mod 16 = 0 -> k mod 8 = 0 -> (sp - k) mod 8 = 0.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S30;A1;o4;Y4;0;Y3;0;A1;o4;#1;A1;k63;A3;i5;i0;r1;o2;A2;k71;r3;r4;P~RA3;i5;i0;A2;k10;r3;r2;o2;#4;A3;i5;i0;A2;k10;r4;r3;o2;P~RA2;k71;r2;r3;#6;A3;k72;r3;r2;r1;A2;k1;o2;r5;A2;k1;o2;#0;A2;k1;o2;#2;A1;o15;i16;A1;i17;i16;A1;o18;i0;A1;i19;i0;A1;i21;i0;A2;o26;i0;o2;A2;k29;#16;o24;A4;k30;r1;r3;cvA2;o12;i31;o32;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;E__arith;RE__wit;R#12;#13;E__varmap;R#14;#15;E__ff;RA6;o74;#16;k22;i23;i23;o24;A7;o20;#16;k22;i23;i23;o24;A4;o25;i0;A2;o26;i0;#2;o58;#17;o28;#18;#19;P~RA3;i5;i0;#2;o2;i75;r1;Y1;0;A1;o4;#21;La;Ri0;Lb;Ri0;L~R#3;m40;RNL~RA2;i40;#5;#7;P~R#6;A2;k71;r4;r5;#8;1;L~R#5;L~RP~RA2;k71;r3;r4;A3;i5;i0;A2;k10;r5;r4;o2;r2;Pa;Ri0;Pb;Ri0;P~R#3;#5;A2;k37;r6;#0;A2;k1;o2;r6;P~R#26;P~R#10;A2;k1;o2;A2;k10;r8;#0;A2;k37;r6;#2;P~R#26;P~R#11;A2;k1;o2;A2;k10;r8;#2;Lsp;Ri0;Lk;Ri0;LH1;RA3;i5;i0;A2;k10;r2;#0;o2;LH2;RA3;i5;i0;A2;k10;r2;#2;o2;EH;RLa;Ri0;Lb;Ri0;L~R#3;m40;RNL~RA2;i40;#5;#7;P~R#4;A3;i5;i0;A2;k10;r5;r4;o2;#8;1;L~R#5;L~RP~RA2;k71;r3;r4;A3;i5;i0;A2;k10;r5;r4;o2;r1;Pa;Ri0;Pb;Ri0;P~R#3;#7;A4;r1;A2;k73;r5;r4;#2;E__sat4;RA2;k37;r5;#0;P~R#9;P~R#10;A2;k1;o2;A2;k10;r7;#0;E__sat3;RA2;k37;r5;#2;P~R#9;P~R#11;A2;k1;o2;A2;k10;r7;#2;#20;A5;k76;#2;r5;r4;A5;k77;#2;#0;r5;A4;o78;i0;Lz;Ri0;A3;i5;i0;#0;A2;k79;r1;#2;#22;A2;o12;i0;A2;k79;#22;#2;EH;R#23;#24;A4;r1;r6;#0;E__sat4;R#25;#27;E__sat3;R#28;#29;E__arith;RE__wit;R#12;#13;E__varmap;R#14;#15;E__ff;RA6;o74;#16;k22;i23;i23;o24;A7;o20;#16;k22;i23;i23;o24;A4;o25;i0;A2;o26;i0;#0;o58;#17;o28;#18;#19;P~RA3;i5;i0;#0;o2;i75;r1;r4;EH;R#23;#24;A4;r1;r5;#2;E__sat4;R#25;#27;E__sat3;R#28;#29;#20;r3;").
Qed.
Ltac oos Hal := unfold PML.obj_on_stack; split; [lia|]; split; [lia|]; apply (al8 _ _ Hal); reflexivity.

Lemma not_outside : forall F a, ~ L5.outside F a -> exists w, In w F /\ L5.in_rng w a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S12;A1;i17;k80;A2;k85;r1;r3;Pa;Ri0;P~RA1;k63;A2;k82;r2;r1;A2;i83;k80;Lw;Rk80;A2;i40;A3;k84;k80;r1;r4;#1;A1;o15;k80;A3;k84;k80;r1;#3;A2;k85;r5;r2;A2;k85;r6;r3;A3;o41;k80;r8;r7;A2;k85;r7;r4;A3;o41;k80;r9;r8;A2;k85;r1;r6;A2;k82;r7;r5;LF;R#0;A5;k81;k80;LF;R#0;#2;La;Ri0;LH;RA1;k63;A2;k82;#3;r1;A2;k86;A2;i83;k80;Lw;Rk80;A2;i40;#4;#1;A1;r1;cdLw;Rk80;LH0;R#4;m75;RNL~Ri75;A1;k63;A2;k85;r3;r5;r1;0;A2;k82;#3;r2;Lw;Rk80;LF;R#0;LIH;R#2;La;Ri0;LH;RA1;k63;A2;k82;A3;o41;k80;r4;r3;r1;Eo;RA1;k87;#5;A2;i67;#5;A1;k63;#5;m67;RNL~RA2;i67;#6;A1;k63;#6;A2;i83;k80;Lw;Rk80;A2;i40;A3;k84;k80;r1;#7;A2;k85;r1;r5;r1;2;L~R#6;A1;LY;R#8;A4;o78;k80;Lw;Rk80;A2;i40;A3;k84;k80;r1;#9;#10;r8;A4;o88;A3;k84;k80;r8;#7;A2;k85;r8;r5;A3;o89;A3;i5;k80;r8;r8;A3;k84;k80;r8;r7;A2;o12;k80;r8;r1;r1;L~RA1;k63;#6;A1;LN;RA1;k63;#8;Ee;RA2;r6;r5;cdLHo;R#11;A1;r5;cdLw0;Rk80;LH0;RA3;k84;k80;r1;A3;o41;k80;r10;r9;m67;RNL~RA2;i67;A3;i5;k80;r11;r2;A3;k84;k80;r2;r10;A1;k63;A2;k85;r3;r9;r1;2;L~RA3;i5;k80;r11;r2;A1;LH0;RA3;i5;k80;r12;r3;A6;k35;k80;r13;Lw0;Rk80;A1;k63;A2;k85;r1;r11;r6;r4;r1;r1;L~RA3;k84;k80;r2;r10;A1;LHw0;RA3;k84;k80;r3;r11;A2;r5;r4;r1;r1;A2;k82;#9;r6;A1;k63;#11;A2;i83;k80;Lw;Rk80;A2;i40;A3;k84;k80;r1;r8;#10;m83;RNL~RA2;i83;k80;Lw;Rk80;A2;i40;A3;k84;k80;r1;r9;A2;k85;r1;r7;A2;i83;k80;Lw;Rk80;A2;i40;A3;k84;k80;r1;A3;o41;k80;r11;r10;A2;k85;r1;r8;r1;1;Lx;Rk80;L~RA1;Lw;Rk80;A2;i40;A3;k84;k80;r1;r10;A2;k85;r1;r8;r1;A2;Lw';Rk80;LH0;RA2;i40;A3;k84;k80;r1;r11;A2;k85;r1;r9;m40;RNL~RA2;i40;A3;k84;k80;r2;r12;A2;k85;r2;r10;A2;i83;k80;Lw;Rk80;A2;i40;A3;k84;k80;r1;A3;o41;k80;r15;r14;A2;k85;r1;r12;r1;1;L~RA3;k84;k80;r2;r12;L~RA2;k85;r3;r11;A2;LHw';RA3;k84;k80;r4;r14;LHin;RA2;k85;r5;r13;A4;o78;k80;Lw;Rk80;A2;i40;A3;k84;k80;r1;A3;o41;k80;r18;r17;A2;k85;r1;r15;r6;A4;o88;A3;k84;k80;r6;A3;o41;k80;r17;r16;A2;k85;r6;r14;A3;o90;A3;i5;k80;r17;r6;A3;k84;k80;r6;r16;r2;r1;r2;r1;r2;r1;r1;r1;").
Qed.
Lemma frame_but_nil0 : forall (M M' : mem) a, L5.frame_but [(a, 0)] M M' -> M' = M.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S14;A1;o92;Y6;00;A1;i91;#0;Y3;0;A1;i93;A1;i91;A1;o92;#2;P~R#1;#3;A2;i95;i0;i0;A1;o15;#5;A4;o96;i0;i0;r7;o2;A2;k98;#0;r6;A2;k85;#7;A2;k98;#0;r5;A1;i21;i0;A2;o55;i0;o48;Y1;0;A2;o55;i0;#12;LM;R#4;LM';R#4;La;Ri0;LH;RA3;k94;A3;o41;#5;A4;o96;i0;i0;r1;o2;#6;r3;r2;A5;k97;#1;#3;r3;r4;Lx;R#1;A2;r2;r1;cdLw;Rk80;LH0;RA3;k84;k80;r1;A3;o41;#5;A4;o96;i0;i0;r4;o2;#6;m67;RNL~RA2;i67;A3;i5;k80;A4;o96;i0;i0;r5;o2;r2;A3;k84;k80;r2;#6;A1;k63;A2;k85;r3;A2;k98;#0;r4;r1;2;L~RA3;i5;k80;A4;o96;i0;i0;r5;o2;r2;A1;LH0;RA3;i5;k80;A4;o96;i0;i0;r6;o2;r3;A6;k35;k80;#7;Lw;Rk80;A1;k63;A2;k85;r1;#8;cdLHin;R#9;E__arith;RL__p1;RpL__x2;Ri0;L__x1;Ri0;E__wit;RA1;o15;i16;A1;i17;i16;E__varmap;RA4;o51;i0;A2;o52;i0;r3;r2;A1;o18;i0;A1;i19;i0;E__ff;RA8;o53;#10;k22;i23;i23;o24;A7;o54;#10;k22;i23;i23;o24;A7;o20;#10;k22;i23;i23;o24;A4;o25;i0;#11;o27;#13;o28;A7;o20;#10;k22;i23;i23;o24;A4;o25;i0;#13;o38;A3;o57;i0;#11;A2;o26;i0;o2;o28;A1;o56;i23;A6;o69;#10;k22;i23;i23;o24;r5;A2;k29;#10;o24;A4;k30;r1;r3;cvA2;o12;i31;o32;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;P__p1;RpP__x2;Ri0;P__x1;Ri0;P~RA2;i40;A2;k1;r1;r2;A2;k39;r2;A2;k6;r1;o2;r4;A4;r1;i75;A2;k98;#0;r7;r9;r2;A1;k63;#9;r4;r1;r1;L~RA3;k84;k80;r2;#6;A1;LH0;RA3;k84;k80;r3;#6;m75;RNL~Ri75;A1;k63;A2;k85;r5;#8;r1;0;r1;A2;k82;A3;o41;#5;A4;o96;i0;i0;r3;o2;#6;A2;k98;#0;r1;").
Qed.
Lemma land1_even : forall k, Z.land (2 * k) 1 = 0.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S6;A1;o4;Y1;0;A2;k79;#0;r1;A1;o4;o48;A2;k11;#0;#2;A3;i5;i0;#3;o2;A1;i21;i0;Lk;Ri0;A6;k9;i0;A2;k10;#1;#3;Lz;Ri0;A3;i5;i0;r1;o2;A6;k9;i0;A2;k79;r1;#0;Lz;Ri0;A3;i5;i0;A2;k10;r1;#3;o2;A3;k99;r1;#3;cdLH;R#4;EH0;RA6;k35;i0;#3;Le;Ri0;m0;RNLz;Ri0;pr1;3;i75;L~Ri100;i101;L~Ri100;i75;o102;o2;r1;i75;A2;k86;i75;r1;A1;k63;#4;#1;A2;k103;#0;r1;A2;k8;#1;A1;k13;#2;A3;k14;#1;#2;E__arith;RE__wit;RA1;o15;i16;A1;i17;i16;E__varmap;RA1;o18;i0;A1;i19;i0;E__ff;RA7;o20;#5;k22;i23;i23;o24;A4;o25;i0;A2;o26;i0;o2;o27;A2;o26;i0;#2;o28;A2;k29;#5;o24;A4;k30;r1;r3;cvA2;o12;i31;o32;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;A2;k1;o2;#2;r1;").
Qed.
Lemma land1_odd_low : forall w, Z.testbit w 0 = true -> Z.land (w mod 256) 1 = 1.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S17;A2;k10;r2;A1;o4;Y8;00;Y1;0;A1;o4;#1;A1;o4;o48;Lz;Ri0;A3;i5;i0;r1;#3;A2;k104;r2;o2;Lb;Ri31;A3;i5;i0;A1;k105;r1;#3;Y3;0;A1;o4;#7;A1;o15;i16;A1;i17;i16;A1;o18;i0;A1;i19;i0;A1;i21;i0;A2;o26;i0;o2;A2;k29;#13;o24;A4;k30;r1;r3;cvA2;o12;i31;o32;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;Lw;Ri0;LH;RA3;i5;i31;A2;k104;r1;o2;o32;A6;k9;i0;A2;k10;#0;A2;k11;#2;#3;#4;A6;k35;i0;A1;k105;A2;k104;#0;o2;#4;A6;k9;i31;#5;#6;A6;k9;i31;o32;#6;A2;o12;i0;#3;#5;r1;A2;k104;A2;k10;r2;A2;k11;#2;#8;o2;A4;k106;r2;#8;o2;E__arith;RE__wit;R#9;#10;E__varmap;R#11;#12;E__ff;RA7;o20;#13;k22;i23;i23;o24;A4;o25;i0;#14;o38;A2;o26;i0;#8;o28;#15;#16;A2;k39;o2;#8;r1;A2;k10;#0;#2;A1;k107;#0;A2;k8;#0;A1;k13;#3;A3;k14;#0;#3;E__arith;RE__wit;R#9;#10;E__varmap;R#11;#12;E__ff;RA7;o20;#13;k22;i23;i23;o24;A4;o25;i0;#14;o27;A2;o26;i0;#3;o28;#15;#16;A2;k1;o2;#3;r1;").
Qed.
Lemma u8_inj : forall (M : mem) a c1 c2, L5.u8_at RSEGS M a c1 -> L5.u8_at RSEGS M a c2 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> c1 = c2.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S27;Y6;00;A1;o92;#0;Y3;0;A1;o92;#2;A1;i91;#3;A1;o4;Y8;00;A2;i40;A2;k1;o2;r4;A2;k39;r4;#5;A1;i17;#4;A1;i93;#7;A2;k111;#3;r6;A1;o15;#4;A3;o41;#4;#9;#10;A2;o112;#7;#11;A2;k111;#3;r8;A2;k111;#3;r7;A3;o41;#4;#14;#10;A2;k98;#3;#13;A2;k98;#3;A2;k111;#3;r9;A2;k114;#3;r9;A2;k115;#3;r9;A2;k10;r11;#5;A2;k1;o2;#5;A1;i21;i0;A2;o55;i0;o48;A7;o54;#22;k22;i23;i23;o24;A7;o20;#22;k22;i23;i23;o24;A4;o25;i0;A2;o26;i0;o2;o27;#23;o28;A7;o20;#22;k22;i23;i23;o24;A4;o25;i0;#23;o38;A2;o26;i0;#5;o28;L__x1;Ri0;E__wit;RA1;o15;i16;A1;i17;i16;E__varmap;RA2;o52;i0;r2;A1;i19;i0;E__ff;RA8;o53;#22;k22;i23;i23;o24;#24;A1;o56;i23;#24;A2;k29;#22;o24;A4;k30;r1;r3;cvA2;o12;i31;o32;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;P__x1;Ri0;P~RA2;i40;A2;k1;o2;r1;A2;k39;r1;#5;A2;i40;A2;k1;o2;r2;A2;k39;r2;#5;LM;RP~RA1;i91;#1;A1;i93;#4;La;Ri0;Lc1;Ri0;Lc2;Ri0;LH1;RA4;k108;k109;r4;r3;r2;LH2;RA4;k108;k109;r5;r4;r2;LR1;R#6;LR2;R#6;cdEH2;RA6;k35;#8;A4;k110;k109;r8;A2;k111;#1;r7;N1;Lo;R#8;A3;i5;#8;r1;#12;r3;#12;r4;A3;i5;#8;#12;A2;o112;#7;A3;o41;#4;A2;k111;#3;r5;#10;EX;RA6;k113;#7;#4;Lt;R#7;m17;RNLl;RA1;i17;#4;#4;r1;2;#13;L~R#4;L~RA1;i17;#4;r2;#15;#11;A6;k113;#8;#7;Lt;R#8;m93;RNLo;RA1;i93;#7;#7;r1;2;L~R#7;r1;A3;o41;#4;#13;#10;A2;o112;#7;#15;#12;r1;A3;i5;#4;#14;#9;EX;RA6;k113;#4;i0;A1;k98;#3;#13;#14;r1;A3;i5;i0;#16;A2;k98;#3;#14;EH2;RA6;k35;i0;#17;Lz;Ri0;A3;i5;i0;r1;#17;r1;#18;#19;A3;i5;i0;#18;#16;EH2;RA6;k35;i0;#17;Lz;Ri0;A3;i5;i0;A2;k114;#3;r11;r1;r1;#18;#19;A3;i5;i0;A2;k114;#3;r10;#18;EH2;RA6;k35;i0;#20;Lz;Ri0;A3;i5;i0;r1;#20;r1;r11;A3;k116;r11;#5;E__sat4;RA2;k37;r10;#5;P~RA2;k1;o2;r10;P~R#21;A2;k1;o2;A2;k10;r12;#5;E__sat3;RA2;k37;r12;#5;P~RA2;k1;o2;r12;P~R#21;A2;k1;o2;A2;k10;r14;#5;E__arith;R#25;#26;A2;r1;r14;r10;A3;i5;i0;r11;A2;k10;r10;#5;EH2;RA6;k35;i0;#20;Lz;Ri0;A3;i5;i0;r13;r1;r1;r11;A3;k116;r11;#5;E__sat3;RA2;k37;r11;#5;P~RA2;k1;o2;r11;P~R#21;A2;k1;o2;A2;k10;r13;#5;E__arith;R#25;#26;A2;r1;r13;r9;A3;i5;i0;r12;r11;r1;A3;i5;i0;r6;r5;").
Qed.

Lemma sso_bit : forall (M : mem) o s w, 0 <= o -> o + 8 <= 2 ^ 64 -> L5.lstr_short RSEGS M o s -> L5.u64_at RSEGS M o w -> Z.land (w mod 256) 1 = 0.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S51;Y6;00;Y3;0;Y1;0;A1;o4;#2;A1;o4;#0;A2;k11;#3;#4;A2;k119;i0;r5;N22;A1;k120;#6;A1;o4;o48;A2;k6;r6;#9;A1;o4;Y8;00;A1;k120;A2;k119;i0;r8;A2;k6;r9;#9;A1;k120;A2;k119;i0;r9;A2;k6;r10;#9;A2;k6;r13;#9;A2;k119;i0;r15;A1;k120;#17;A1;o4;Y4;6;A2;k1;#18;#19;A2;o12;i0;#19;A2;k119;i0;r16;A1;k120;#22;A2;k1;o2;#11;A2;k130;#3;#4;P~RA2;k39;o2;#3;P~RA2;k1;o2;#4;A2;k39;o2;#5;A2;k1;o2;#3;LHa;R#27;L~Ri101;A3;k131;#3;#4;r2;PHa;R#27;P~Ri101;A2;k1;o2;#5;A1;o15;i16;A1;i17;i16;A1;i19;i0;A1;i21;i0;A2;o26;i0;o2;A2;o26;i0;#11;A2;k29;#33;o24;A2;o12;i31;o32;A3;k34;i0;o2;r2;A2;k10;r14;#11;A2;k79;#3;#23;A2;k10;r15;#11;A2;k1;#23;#19;A2;k119;i0;r17;A2;o44;i0;o49;N3;N1;A2;o55;i0;o48;A1;o56;i23;A3;o137;i0;A2;o26;i0;#3;#47;A2;k79;#3;r3;LM;RP~RA1;i91;A1;o92;#0;A1;i93;A1;i91;A1;o92;#1;Lo;Ri0;Ls;RA1;i17;i0;Lw;Ri0;LH1;RA2;k1;o2;r3;LH2;RA2;k1;A2;k6;r4;A1;o4;#1;#5;LH;RA4;k117;k109;r6;r5;r4;m40;RNL~RA2;i40;A2;i118;#6;#7;A2;i40;A4;k108;k109;r7;r6;A2;k79;#3;#8;A2;i40;A4;k121;k109;r7;#10;r5;A4;k108;k109;r7;A2;k6;#10;#8;o2;P~RA4;k122;k109;r8;r7;r5;A3;i5;i0;A2;k8;A2;k10;r6;#11;#9;o2;r1;1;L~RA2;i118;#6;#7;L~RA2;i40;A4;k108;k109;r8;r7;A2;k79;#3;A1;k120;A2;k119;i0;r6;A2;i40;A4;k121;k109;r8;A2;k6;r7;#9;r6;A4;k108;k109;r8;A2;k6;A2;k6;r7;#9;A1;k120;A2;k119;i0;r6;o2;A2;LHl;RA2;i118;A2;k119;i0;r7;#7;LH;RA2;i40;A4;k108;k109;r10;r9;A2;k79;#3;#12;A2;i40;A4;k121;k109;r10;#13;r8;A4;k108;k109;r10;A2;k6;#13;#12;o2;m40;RNL~RA2;i40;A4;k108;k109;r11;r10;A2;k79;#3;#14;A2;i40;A4;k121;k109;r11;#15;r9;A4;k108;k109;r11;A2;k6;#15;#14;o2;P~RA4;k122;k109;r12;r11;r9;A3;i5;i0;A2;k8;A2;k10;r10;#11;#9;o2;r1;1;L~RA4;k108;k109;r11;r10;A2;k79;#3;#14;L~RA2;i40;A4;k121;k109;r12;A2;k6;r11;#9;r10;A4;k108;k109;r12;A2;k6;A2;k6;r11;#9;A1;k120;A2;k119;i0;r10;o2;A2;LHb;RA4;k108;k109;r13;r12;A2;k79;#3;A1;k120;A2;k119;i0;r11;L_H;RA2;i40;A4;k121;k109;r14;#16;r12;A4;k108;k109;r14;A2;k6;#16;A1;k120;A2;k119;i0;r12;o2;LHw;RA4;k122;k109;r15;r14;r12;EHb';RA6;k123;r16;r15;r13;r12;r11;r1;A3;k124;r16;r15;A2;k10;r13;#11;ER;RA3;k36;r14;#11;EHl0;RA4;k125;A2;i118;#17;#7;#20;A12;k126;i127;i0;i118;k120;k1;k128;#17;#18;A2;o12;i0;#18;#7;#19;#21;r8;#20;Ecstr;RA1;k129;#22;A2;k1;o2;#23;E__sat5;RA2;k37;r16;#11;P~RA2;k1;o2;r16;P~R#24;A2;k1;o2;A2;k10;r18;#11;E__sat4;R#25;#26;E__sat3;R#28;#29;E__arith;RE__wit;R#30;#31;E__varmap;RA1;o18;i0;#32;E__ff;RA7;o20;#33;k22;i23;i23;o24;A4;o25;i0;#34;o38;#35;o28;#36;A4;k30;r1;r3;cv#37;A3;i5;i31;A2;k33;r1;r3;o32;#38;A2;k39;o2;#11;r1;A2;i40;A2;k1;o2;#39;A2;k39;#39;#11;A6;k35;i0;#40;Lz;Ri0;A3;i5;i0;A2;k8;r1;#9;o2;A1;k132;#23;#41;A8;k133;r18;r17;#40;#41;r5;r2;EHl0;RA4;k125;A2;i118;#22;#7;#42;A12;k126;i127;i0;i118;k120;k1;k128;#22;#23;A2;o12;i0;#23;#7;#19;#21;r9;#42;Ecstr;RA1;k129;#43;A2;k1;o2;A1;k120;#43;E__sat5;RA2;k37;r17;#11;P~RA2;k1;o2;r17;P~R#24;A2;k1;o2;A2;k10;r19;#11;E__sat4;R#25;#26;E__sat3;R#28;#29;E__arith;RL__x1;Ri0;E__wit;RA3;o41;i16;A2;o134;#44;A2;o42;A3;o43;i0;#44;A2;o44;i0;#45;o50;A3;o41;i16;A2;o42;A3;o43;i0;A3;o135;i0;A2;o136;i0;#3;A2;o44;i0;#46;#44;o50;#30;#31;E__varmap;RA2;o52;i0;r2;#32;E__ff;RA8;o53;#33;k22;i23;i23;o24;A7;o20;#33;k22;i23;i23;o24;A4;o25;i0;#34;o27;#47;o28;#48;A8;o53;#33;k22;i23;i23;o24;A7;o20;#33;k22;i23;i23;o24;A4;o25;i0;#47;o27;A2;o26;i0;#19;o28;#48;A7;o54;#33;k22;i23;i23;o24;A7;o20;#33;k22;i23;i23;o24;A4;o25;i0;#34;o27;#49;o28;A7;o20;#33;k22;i23;i23;o24;A4;o25;i0;#49;o38;#35;o28;#36;A4;k30;r1;r3;#37;#38;P__x1;Ri0;P~RA2;k1;o2;r1;P~RA2;k1;r2;#19;A2;i40;A2;k1;o2;#50;A2;k39;#50;#11;A3;r1;A1;k120;A2;k119;i0;r22;r5;r6;r1;r2;r1;r2;r1;").
Qed.

Ltac ow := unfold L5.outside; let w := fresh "w" in let Hw := fresh "Hw" in let Hin := fresh "Hin" in
  intros w Hw Hin; unfold PML.ll_foot_csrc in Hw; cbn [In map fst snd] in Hw;
  repeat (destruct Hw as [<-|Hw]; [unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia|]); destruct Hw.
Ltac cov_stack := let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; split; [ow | left; lia].
Ltac wsi := let w := fresh "w" in let Hw := fresh "Hw" in intros w Hw; unfold PML.ll_foot_csrc in Hw; cbn [In map fst snd] in Hw;
  repeat (destruct Hw as [<-|Hw]; [cbn [fst snd]; lia|]); destruct Hw.
Ltac foot_in := first [ apply (TK2.in_foot11_iv 0xd4df0 0xd4df2); [cbn; tauto | lia] | apply (TK2.in_foot11_iv 0xd4df8 0xd4dfa); [cbn; tauto | lia]
                      | apply (TK2.in_foot11_iv 0xd5030 0xd5032); [cbn; tauto | lia]
                      | apply (TK2.in_foot11_iv 0xd5040 0xd5238); [cbn; tauto | lia] | apply (TK2.in_foot11_iv 0xd52e8 0xd5768); [cbn; tauto | lia]
                      | apply (TK2.in_foot11_iv 0xd5e98 0xd5ef8); [cbn; tauto | lia] | apply (TK2.in_foot11_iv 0xf6848 0xf6a68); [cbn; tauto | lia] ].
Ltac wfoot := let w := fresh "w" in let a := fresh "a" in let Hw := fresh "Hw" in let Hin := fresh "Hin" in
  intros w a Hw Hin; unfold PML.ll_foot_csrc in Hw; cbn [In map fst snd] in Hw;
  repeat (destruct Hw as [<-|Hw]; [unfold L5.in_rng in Hin; cbn [fst snd] in Hin; first [left; lia | right; foot_in]|]); destruct Hw.
Ltac st_cov := apply TK2.statics_cov_keepH; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  assert (a < 0xf8000) by (destruct Ha as [(iv & Hiv & Hr)|Hr]; [unfold PML.ll_foot_csrc in Hiv; repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; lia|]); destruct Hiv | unfold PML.IMG_RO_HI in Hr; lia]); ow.

Lemma CS4 : In (bv_unsigned (4%bv : reg)) callee_saved_idx. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S12;Y1;0;Y2;1;A1;o92;#1;Y2;0;A1;o4;#3;A2;k98;#2;A3;o138;#2;#4;o102;Y1;1;A3;i5;i0;A1;o4;#6;#5;A3;i5;i0;#4;#5;Y3;1;A2;i67;A3;i5;i0;A1;o4;Y3;0;#5;A2;i67;A3;i5;i0;A1;o4;#9;#5;A2;i67;A3;i5;i0;A1;o4;Y4;2;#5;A2;i67;A3;i5;i0;A1;o4;Y4;3;#5;A2;i67;A3;i5;i0;A1;o4;Y4;4;#5;A2;i67;A3;i5;i0;A1;o4;Y4;5;#5;A2;i67;A3;i5;i0;A1;o4;Y4;6;#5;A2;i67;A3;i5;i0;A1;o4;Y4;7;#5;A2;i67;A3;i5;i0;A1;o4;Y4;8;#5;A2;i67;A3;i5;i0;A1;o4;Y4;9;#5;A2;i67;A3;i5;i0;A1;o4;Y4;a;#5;A2;i67;A3;i5;i0;A1;o4;Y4;b;#5;i75;A2;i67;#8;#10;cdA3;o90;A3;i5;i0;A1;o4;#0;#5;A2;i67;#7;#11;A3;o90;#7;#11;A3;o89;#8;#10;A2;o12;i0;#5;A3;k84;i0;A2;k98;#2;cdA3;o138;#2;#4;cvo102;A2;k139;#2;#4;A1;i91;#2;k140;").
Qed.
Lemma CS8 : In (bv_unsigned (8%bv : reg)) callee_saved_idx. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S14;Y1;0;Y2;1;A1;o92;#1;A1;o4;Y3;0;A2;k98;#2;A3;o138;#2;#3;o102;Y1;1;A3;i5;i0;A1;o4;#5;#4;Y2;0;A3;i5;i0;A1;o4;#7;#4;A3;i5;i0;#3;#4;Y3;1;A2;i67;A3;i5;i0;A1;o4;#10;#4;A2;i67;A3;i5;i0;A1;o4;Y4;2;#4;A2;i67;A3;i5;i0;A1;o4;Y4;3;#4;A2;i67;A3;i5;i0;A1;o4;Y4;4;#4;A2;i67;A3;i5;i0;A1;o4;Y4;5;#4;A2;i67;A3;i5;i0;A1;o4;Y4;6;#4;A2;i67;A3;i5;i0;A1;o4;Y4;7;#4;A2;i67;A3;i5;i0;A1;o4;Y4;8;#4;A2;i67;A3;i5;i0;A1;o4;Y4;9;#4;A2;i67;A3;i5;i0;A1;o4;Y4;a;#4;A2;i67;A3;i5;i0;A1;o4;Y4;b;#4;i75;A2;i67;#9;#11;A2;i67;#8;#12;cdA3;o90;A3;i5;i0;A1;o4;#0;#4;A2;i67;#6;#13;A3;o90;#6;#13;A3;o90;#8;#12;A3;o89;#9;#11;A2;o12;i0;#4;A3;k84;i0;A2;k98;#2;cdA3;o138;#2;#3;cvo102;A2;k139;#2;#3;A1;i91;#2;k140;").
Qed.
Lemma CS9 : In (bv_unsigned (9%bv : reg)) callee_saved_idx. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S16;Y1;0;Y2;1;A1;o92;#1;Y3;1;A1;o4;#3;A2;k98;#2;A3;o138;#2;#4;o102;Y1;1;A3;i5;i0;A1;o4;#6;#5;Y2;0;A3;i5;i0;A1;o4;#8;#5;A3;i5;i0;A1;o4;Y3;0;#5;A3;i5;i0;#4;#5;A2;i67;A3;i5;i0;A1;o4;Y4;2;#5;A2;i67;A3;i5;i0;A1;o4;Y4;3;#5;A2;i67;A3;i5;i0;A1;o4;Y4;4;#5;A2;i67;A3;i5;i0;A1;o4;Y4;5;#5;A2;i67;A3;i5;i0;A1;o4;Y4;6;#5;A2;i67;A3;i5;i0;A1;o4;Y4;7;#5;A2;i67;A3;i5;i0;A1;o4;Y4;8;#5;A2;i67;A3;i5;i0;A1;o4;Y4;9;#5;A2;i67;A3;i5;i0;A1;o4;Y4;a;#5;A2;i67;A3;i5;i0;A1;o4;Y4;b;#5;i75;A2;i67;#11;#12;A2;i67;#10;#13;A2;i67;#9;#14;cdA3;o90;A3;i5;i0;A1;o4;#0;#5;A2;i67;#7;#15;A3;o90;#7;#15;A3;o90;#9;#14;A3;o90;#10;#13;A3;o89;#11;#12;A2;o12;i0;#5;A3;k84;i0;A2;k98;#2;cdA3;o138;#2;#4;cvo102;A2;k139;#2;#4;A1;i91;#2;k140;").
Qed.
Lemma CS2 : In (bv_unsigned (2%bv : reg)) callee_saved_idx. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S8;Y1;0;A1;o4;#0;Y2;1;A1;o92;#2;A2;k98;#3;A3;o138;#3;#1;o102;Y1;1;Y2;0;Y3;1;cdA3;o89;A3;i5;i0;#1;#4;A2;i67;A3;i5;i0;A1;o4;#5;#4;A2;i67;A3;i5;i0;A1;o4;#6;#4;A2;i67;A3;i5;i0;A1;o4;Y3;0;#4;A2;i67;A3;i5;i0;A1;o4;#7;#4;A2;i67;A3;i5;i0;A1;o4;Y4;2;#4;A2;i67;A3;i5;i0;A1;o4;Y4;3;#4;A2;i67;A3;i5;i0;A1;o4;Y4;4;#4;A2;i67;A3;i5;i0;A1;o4;Y4;5;#4;A2;i67;A3;i5;i0;A1;o4;Y4;6;#4;A2;i67;A3;i5;i0;A1;o4;Y4;7;#4;A2;i67;A3;i5;i0;A1;o4;Y4;8;#4;A2;i67;A3;i5;i0;A1;o4;Y4;9;#4;A2;i67;A3;i5;i0;A1;o4;Y4;a;#4;A2;i67;A3;i5;i0;A1;o4;Y4;b;#4;i75;A2;o12;i0;#4;A3;k84;i0;A2;k98;#3;cdA3;o138;#3;#1;cvo102;A2;k139;#3;#1;A1;i91;#3;k140;").
Qed.
Lemma KO_4 : In (ridx (4%bv : reg)) HCS.KOH.
Proof.
  unfold HCS.KOH. cbn. tauto.
Qed.
Lemma KC_4 : In (ridx (4%bv : reg)) CK.CSR. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S18;N3;A1;o92;Y2;1;A1;o4;Y2;0;A1;k141;A3;o138;#1;#2;o102;N4;A3;i5;i127;#4;#3;N8;N9;N18;N19;N20;N21;N22;N23;N24;N25;N26;A2;i67;A3;i5;i127;#6;#3;A2;i67;A3;i5;i127;#7;#3;A2;i67;A3;i5;i127;#8;#3;A2;i67;A3;i5;i127;#9;#3;A2;i67;A3;i5;i127;#10;#3;A2;i67;A3;i5;i127;#11;#3;A2;i67;A3;i5;i127;#12;#3;A2;i67;A3;i5;i127;#13;#3;A2;i67;A3;i5;i127;#14;#3;A2;i67;A3;i5;i127;#15;#3;A2;i67;A3;i5;i127;#16;#3;A2;i67;A3;i5;i127;N27;#3;i75;cdA3;o90;A3;i5;i127;#0;#3;A2;i67;#5;#17;A3;o89;#5;#17;A2;o12;i127;#3;A3;k84;i127;A1;k141;cdA3;o138;#1;#2;cvo102;A2;k139;#1;#2;A1;i91;#1;k143;").
Qed.
Lemma KC_8 : In (ridx (8%bv : reg)) CK.CSR. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S20;N3;A1;o92;Y2;1;A1;o4;Y3;0;A1;k141;A3;o138;#1;#2;o102;N4;A3;i5;i127;#4;#3;N8;A3;i5;i127;#6;#3;N9;N18;N19;N20;N21;N22;N23;N24;N25;N26;A2;i67;A3;i5;i127;#8;#3;A2;i67;A3;i5;i127;#9;#3;A2;i67;A3;i5;i127;#10;#3;A2;i67;A3;i5;i127;#11;#3;A2;i67;A3;i5;i127;#12;#3;A2;i67;A3;i5;i127;#13;#3;A2;i67;A3;i5;i127;#14;#3;A2;i67;A3;i5;i127;#15;#3;A2;i67;A3;i5;i127;#16;#3;A2;i67;A3;i5;i127;#17;#3;A2;i67;A3;i5;i127;N27;#3;i75;A2;i67;#7;#18;cdA3;o90;A3;i5;i127;#0;#3;A2;i67;#5;#19;A3;o90;#5;#19;A3;o89;#7;#18;A2;o12;i127;#3;A3;k84;i127;A1;k141;cdA3;o138;#1;#2;cvo102;A2;k139;#1;#2;A1;i91;#1;k143;").
Qed.
Lemma KC_9 : In (ridx (9%bv : reg)) CK.CSR. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S22;N3;A1;o92;Y2;1;A1;o4;Y3;1;A1;k141;A3;o138;#1;#2;o102;N4;A3;i5;i127;#4;#3;N8;A3;i5;i127;#6;#3;N9;A3;i5;i127;#8;#3;N18;N19;N20;N21;N22;N23;N24;N25;N26;A2;i67;A3;i5;i127;#10;#3;A2;i67;A3;i5;i127;#11;#3;A2;i67;A3;i5;i127;#12;#3;A2;i67;A3;i5;i127;#13;#3;A2;i67;A3;i5;i127;#14;#3;A2;i67;A3;i5;i127;#15;#3;A2;i67;A3;i5;i127;#16;#3;A2;i67;A3;i5;i127;#17;#3;A2;i67;A3;i5;i127;#18;#3;A2;i67;A3;i5;i127;N27;#3;i75;A2;i67;#9;#19;A2;i67;#7;#20;cdA3;o90;A3;i5;i127;#0;#3;A2;i67;#5;#21;A3;o90;#5;#21;A3;o90;#7;#20;A3;o89;#9;#19;A2;o12;i127;#3;A3;k84;i127;A1;k141;cdA3;o138;#1;#2;cvo102;A2;k139;#1;#2;A1;i91;#1;k143;").
Qed.
Ltac kin := first [exact CS2 | exact CS4 | exact CS8 | exact CS9 | exact KO_4 | exact KC_4 | exact KC_8 | exact KC_9].
Lemma KOH_CSR : forall q, In q HCS.KOH -> In q CK.CSR.
Proof.
intros q Hq. unfold HCS.KOH in Hq. unfold CK.CSR. cbn [In] in *.
repeat (destruct Hq as [<-|Hq]; [tauto|]). destruct Hq.
Qed.
Lemma KOH_csaved : forall r : reg, In (ridx r) HCS.KOH -> In (bv_unsigned r) callee_saved_idx.
Proof.
intros r Hr. unfold HCS.KOH, ridx in Hr. unfold callee_saved_idx. cbn [In] in *.
repeat (destruct Hr as [Hr|Hr]; [lia|]). destruct Hr.
Qed.

Lemma KSP : forall Ra Rb, regs_preserved Ra Rb -> TK.keepsR HCS.KOH Ra Rb.
Proof.
intros Ra Rb H r Hr. apply H. apply KOH_csaved. exact Hr.
Qed.
Lemma KCO : forall Ra Rb, TK.keepsR CK.CSR Ra Rb -> TK.keepsR HCS.KOH Ra Rb.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S1;A2;k153;A1;o92;Y2;1;A1;i91;A1;o92;Y6;00;LRa;R#0;LRb;R#0;LH;RA3;k156;k143;r2;r1;A6;k157;k143;k142;r3;r2;r1;k158;").
Qed.
Lemma KT : forall Ra Rb Rc, TK.keepsR HCS.KOH Ra Rb -> TK.keepsR HCS.KOH Rb Rc -> TK.keepsR HCS.KOH Ra Rc.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S2;A2;k153;A1;o92;Y2;1;A1;i91;A1;o92;Y6;00;A3;k156;k142;r3;r2;LRa;R#0;LRb;R#0;LRc;R#0;LH1;R#1;LH2;R#1;A6;k159;k142;r5;r4;r3;r2;r1;").
Qed.

Lemma csr_of : forall Ra Rb : bvmap 5 word, TK.keepsR HCS.KOH Ra Rb -> getr Rb 8%bv = getr Ra 8%bv -> getr Rb 9%bv = getr Ra 9%bv -> getr Rb 18%bv = getr Ra 18%bv -> TK.keepsR CK.CSR Ra Rb.
Proof.
exact HCS.keeps_csr.
Qed.

Lemma nodup_mid : forall (A B : list (Z * Z)) (x : Z * Z), base.NoDup (map fst (A ++ x :: B)) -> forall b, In b B -> fst b <> fst x.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S51;A2;i95;i0;i0;A1;i17;#0;A2;k165;i0;i0;A3;o41;#0;r1;r2;A3;k84;#0;r1;r4;A3;k165;i0;i0;r4;PB;R#1;Px;R#0;P~RA2;i163;i0;A4;k164;#0;i0;#2;A3;k166;#0;r3;#3;Pb;R#0;P~R#4;A1;k63;A3;i5;i0;A3;k165;i0;i0;r2;#5;A1;i17;i0;A3;k165;i0;i0;r6;A3;o41;i0;#8;A4;k164;#0;i0;#2;r7;A3;k165;i0;i0;r5;A1;k63;A3;i5;i0;#10;A3;k165;i0;i0;r7;A1;o15;i0;A3;o41;i0;#5;A4;k164;#0;i0;#2;r5;A3;o41;i0;#10;A4;k164;#0;i0;#2;r6;Le;R#7;m17;RNLl;RA1;i17;i0;pr1;2;i101;L~Ri0;L~RA1;i17;i0;i75;A2;k86;#11;r1;A1;i168;i0;A1;k63;A5;k167;i0;#7;#17;r2;r1;A2;i163;i0;r2;A3;o41;i0;r4;r3;A3;o41;i0;r5;r4;Le;R#7;m17;RNLl;RA1;i17;i0;#7;r1;2;r6;Lz;Ri0;Ll;RA1;i17;i0;r1;A3;o41;i0;r6;r5;A4;k164;#0;i0;#2;r15;Le;R#7;m17;RNLl;RA1;i17;i0;i0;r1;2;r8;Lz;Ri0;Ll;RA1;i17;i0;r2;A3;o41;i0;r7;r6;A3;k165;i0;i0;r15;A3;k165;i0;i0;r16;A3;k165;i0;i0;r17;A3;k165;i0;i0;r18;A3;i5;#7;r10;A4;k164;#0;i0;#2;r20;A3;k165;i0;i0;r20;A3;k165;i0;i0;r22;A3;i5;i0;#32;#33;A1;k63;#34;PN1;RA1;k63;A5;k167;i0;#7;#17;r2;r11;PN2;RA2;i163;i0;r12;#35;A4;k164;#0;i0;#2;r21;A3;k165;i0;i0;r21;PN2;R#19;A1;k63;A3;i5;i0;#38;A3;k165;i0;i0;r23;A3;k84;i0;r2;r3;P~RA3;k84;i0;r1;r2;A5;k167;i0;#7;#17;r2;r3;A3;k165;i0;i0;r24;A1;k63;A3;i5;i0;#5;#8;A3;o41;i0;A3;k165;i0;i0;r10;A4;k164;#0;i0;#2;A3;k166;#0;r9;A3;o41;#0;r6;r7;A3;o41;i0;A3;k165;i0;i0;r8;A4;k164;#0;i0;#2;A3;k166;#0;r7;A3;o41;#0;r4;r5;A3;o41;i0;A3;k165;i0;i0;r9;A4;k164;#0;i0;#2;A3;k166;#0;r8;A3;o41;#0;r5;r6;A4;k164;#0;i0;#2;A3;k166;#0;r17;A3;o41;#0;r14;r15;A3;k165;i0;i0;r19;A3;i5;#7;r10;A4;k164;#0;i0;#2;A3;k166;#0;r22;A3;o41;#0;r19;r20;A4;k164;#0;i0;#2;A3;k166;#0;r23;A3;o41;#0;r20;r21;LA;R#1;A5;k81;#0;LA;R#1;#6;LB;R#1;Lx;R#0;LND;RA2;i163;i0;A4;k164;#0;i0;#2;A3;k166;#0;A1;o15;#0;#3;Lb;R#0;LHb;R#4;EH;Rm163;RNLl;RA1;i17;i0;L~RA2;i163;i0;r1;P~RA3;i5;#7;r2;#9;#11;r3;2;LH;RA3;i5;#7;#12;#13;A1;LH;RA3;i5;#7;#12;#14;EH0;RA6;k35;#7;#12;#15;o102;#9;r1;i75;#16;r1;Lx;Ri0;Ll;RA1;i17;i0;L~RA1;k63;A5;k167;i0;A1;i17;i0;A1;i168;i0;r2;r1;L~RA2;i163;i0;r2;A4;Ly;Ri0;Ll;R#7;LN1;R#18;LN2;R#19;LH;RA3;i5;#7;#20;A3;o41;i0;A3;k165;i0;i0;r12;A4;k164;#0;i0;#2;r13;A3;LH;RA3;i5;#7;#21;A3;o41;i0;A3;k165;i0;i0;r13;A4;k164;#0;i0;#2;r14;EH0;RA6;k113;#7;#7;#22;#23;A3;o41;i0;A3;k165;i0;i0;r14;#24;r1;A3;i5;#7;r5;#24;A1;EH0;RA6;k113;#7;i0;#25;#26;A3;o41;i0;#27;A4;k164;#0;i0;#2;r16;r2;A3;i5;i0;r7;#27;A1;LH;RA3;i5;i0;r8;#28;EH0;Rr1;A3;i5;i0;r9;#29;A6;k9;i0;#30;Lz;Ri0;P~R#31;#36;LH0;RA3;i5;#7;r9;A4;k164;#0;i0;#2;r19;EH1;Rr1;#31;A6;k9;#7;#37;Ll;R#7;PN1;RA1;k63;A5;k167;i0;#7;#17;#38;r1;#39;LN1;RA1;k63;A5;k167;i0;#7;#17;#32;#37;LN2;RA2;i163;i0;A4;k164;#0;i0;#2;r22;cdLX;R#34;A1;r3;EH;RLl;R#7;Lx;Ri0;m40;RNL~RA2;i40;P~RA5;k167;i0;#7;#17;r1;r2;#40;#41;P~R#40;A5;k167;i0;#7;#17;r3;r4;A3;k169;i0;r2;r1;1;L~RP~RA5;k167;i0;#7;#17;r1;r2;#40;L~RP~RA3;k84;i0;r2;r3;A5;k167;i0;#7;#17;r3;r4;r1;Pl;R#7;Px;Ri0;#41;A3;r1;A4;k164;#0;i0;#2;r25;#42;A6;k35;i0;#33;Lz;Ri0;A3;k84;i0;r1;A4;k164;#0;i0;#2;r26;A6;k170;#0;i0;#2;r25;r22;r21;#42;r2;#35;r11;r1;r10;r1;r1;r1;r1;r3;r2;r4;r3;r2;r1;A1;Ll;R#7;P~RA3;i5;#7;r1;#14;#43;#13;A1;r1;A2;o12;#7;#14;La;R#0;LA;R#1;LIH;R#6;LB;R#1;Lx;R#0;LND;RA2;i163;i0;A4;k164;#0;i0;#2;A3;k166;#0;A3;o41;#0;r5;r4;#3;Lb;R#0;LHb;R#4;EH;Rm163;RNLl;RA1;i17;i0;L~RA2;i163;i0;r1;P~RA3;i5;#7;r2;#44;#11;r3;2;LH;RA3;i5;#7;#12;#45;A1;LH;RA3;i5;#7;#12;#46;EH0;RA6;k35;#7;#12;#15;o102;#44;r1;i75;#16;r1;Lx;Ri0;Ll;RA1;i17;i0;L~RA1;k63;A5;k167;i0;A1;i17;i0;A1;i168;i0;r2;r1;L~RA2;i163;i0;r2;A4;Ly;Ri0;Ll;R#7;LN1;R#18;LN2;R#19;LH;RA3;i5;#7;#20;A3;o41;i0;#28;A4;k164;#0;i0;#2;A3;k166;#0;r15;A3;o41;#0;r12;r13;A3;LH;RA3;i5;#7;#21;A3;o41;i0;#29;A4;k164;#0;i0;#2;A3;k166;#0;r16;A3;o41;#0;r13;r14;EH0;RA6;k113;#7;#7;#22;#23;A3;o41;i0;#30;#47;r1;A3;i5;#7;r5;#47;A1;EH0;RA6;k113;#7;i0;#25;#26;A3;o41;i0;#48;A4;k164;#0;i0;#2;A3;k166;#0;r18;A3;o41;#0;r15;r16;r2;A3;i5;i0;r7;#48;A1;LH;RA3;i5;i0;r8;#32;EH0;Rr1;A3;i5;i0;r9;#38;A6;k9;i0;#33;Lz;Ri0;P~R#49;#36;LH0;RA3;i5;#7;r9;A4;k164;#0;i0;#2;A3;k166;#0;r21;A3;o41;#0;r18;r19;EH1;Rr1;#49;A6;k9;#7;#50;Ll;R#7;PN1;RA1;k63;A5;k167;i0;#7;#17;A3;k165;i0;i0;r25;r1;#39;LN1;RA1;k63;A5;k167;i0;#7;#17;#42;#50;LN2;RA2;i163;i0;A4;k164;#0;i0;#2;A3;k166;#0;r24;A3;o41;#0;r21;r22;A5;r24;r23;r22;r1;r20;r19;r11;r1;r10;r1;r1;r1;r1;r3;r2;r4;r3;r2;r1;A1;Ll;R#7;P~RA3;i5;#7;r1;#46;#43;#45;A1;r1;A2;o12;#7;#46;r1;").
Qed.
Lemma lb_remove_app : forall (A : list (Z * Z)) x l, (forall b, In b A -> fst b <> x) -> lb_remove x (A ++ l) = A ++ lb_remove x l.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S14;A2;i95;i0;i0;A1;i17;#0;A1;k63;A3;i5;i0;A3;k165;i0;i0;r2;r4;A2;k171;r3;r2;Px;Ri0;Pl;R#1;P~RPb;R#0;P~RA3;k84;#0;r1;r4;#2;A3;i5;#1;A2;k171;r3;A3;k166;#0;r4;r2;A3;k166;#0;r4;#3;A1;o15;#0;A3;o41;#0;r6;r5;A3;k165;i0;i0;r6;A3;k166;#0;r9;r6;A2;k171;r7;#8;A3;k166;#0;r9;A2;k171;r7;r6;A3;o41;#0;r10;#10;A3;i5;i0;A3;k165;i0;i0;r9;r6;A2;o41;#0;r10;LA;R#1;A5;k81;#0;LA;R#1;#4;Lx;Ri0;Ll;R#1;LH;RPb;R#0;P~RA3;k84;#0;r1;#5;#2;A2;o12;#1;A3;k166;#0;#5;#3;La;R#0;LA;R#1;LIH;R#4;Lx;Ri0;Ll;R#1;LH;RPb;R#0;P~RA3;k84;#0;r1;#6;#2;cdEr;RA2;k60;#7;r3;A2;i61;A3;i5;i0;#7;r3;A2;k62;#7;r3;Eb;RA2;k62;A3;k165;i0;i0;r7;r4;i31;m61;RNLb;Ri31;Lr;RA2;i61;A3;i5;i0;A3;k165;i0;i0;r9;r6;r1;A3;i5;#1;m31;RNL~Ri31;#1;r2;2;#8;A3;o41;#0;r10;#9;#11;r2;2;Le;RA3;i5;i0;A3;k165;i0;i0;r8;r5;A1;LE;R#12;A2;k86;A3;i5;#1;#8;#11;A3;r5;r10;A3;o89;A3;i5;#0;r10;r10;A2;f1;0;1;In;RPa;R#0;Pl;R#1;pLa;R#0;Ll;R#1;m17;RNLl;RA1;i17;#0;pr1;2;i75;Lb;R#0;Ll';RA1;i17;#0;A2;i67;A3;i5;#0;r2;r4;A2;r5;r4;r1;r10;r9;A2;o12;#0;r10;r1;r1;Ln;RA1;k63;A3;i5;i0;A3;k165;i0;i0;r8;r5;A1;LE;RA1;k63;#12;A8;k172;#1;#1;#13;#13;#9;#10;A2;o12;P~R#1;#1;#13;A3;r8;r7;r6;Lb;R#0;LHb;RA3;k84;#0;r1;r10;A2;r7;r2;A3;o90;A3;i5;#0;r12;r2;A3;k84;#0;r2;r11;r1;r1;A3;i5;#1;A2;k171;r3;A3;k166;#0;#6;r2;A3;k166;#0;#6;#3;r1;").
Qed.
Lemma heap_swap : forall (A B C : list (Z * Z)) cr (Mx : mem) VM (HI : heap_iface) L {SCFG_P : ScfgP}, heap_iface_ok L SCFG HI ->
  hi_heap HI (A ++ B ++ C) cr Mx VM -> hi_heap HI (B ++ A ++ C) cr Mx VM.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S70;A2;i95;i0;i0;A1;i17;#0;Y3;0;A1;k179;r3;A3;k166;#0;r11;A3;k166;#0;r10;r9;A3;k166;#0;r11;r10;A3;k166;#0;r12;#5;A3;k84;#0;r1;#6;A3;k84;#0;r1;r12;A3;k84;#0;r1;#5;A3;k166;#0;r12;r11;A3;k166;#0;r13;#10;A3;k84;#0;r2;r13;A3;k84;#0;r2;#10;A2;i67;#12;#13;A3;k166;#0;r13;r11;A3;k166;#0;r12;#15;A3;k84;#0;r2;#16;A2;k185;p#17;A3;k84;#0;r1;r11;A3;k84;#0;r1;r10;A3;k84;#0;r2;r12;A3;k84;#0;r2;r11;A2;i67;#21;#22;A2;i67;#12;#23;PB;RppA4;k188;ppk182;k182;A3;k191;pk182;k192;A3;k166;#0;r12;r10;A3;k84;#0;r1;#28;A3;k194;pk182;k195;A3;k84;#0;r2;#15;A2;i67;#21;#31;A2;i67;#12;#22;A3;k84;#0;r1;r13;A4;o96;i0;i0;r2;r1;A3;k84;#0;#35;r14;A3;k84;#0;#35;r13;A3;k84;#0;#35;r12;A2;i67;#36;A2;i67;#37;#38;A4;o96;i0;i0;r3;r2;A3;k84;#0;#40;r14;A3;k84;#0;#40;r15;A3;k84;#0;#40;r13;A2;i67;#42;#43;A2;i67;#41;#44;A2;i67;#37;A2;i67;#36;#38;A2;i67;#41;#43;A2;i67;#42;#47;A4;o96;i0;i0;r4;r3;A3;k84;#0;#49;r15;A3;k84;#0;#49;r16;A3;k84;#0;#49;r14;A2;i67;#51;#52;A4;o96;i0;i0;r5;r4;A3;k84;#0;#54;r16;A3;k84;#0;#54;r17;A3;k84;#0;#54;r15;A2;i67;#56;#57;A2;i67;#50;#52;A2;i67;#55;#57;A3;k165;i0;i0;r2;A3;k199;i0;i0;r2;A2;k165;i0;i0;A3;k166;#0;r15;A3;k166;#0;r14;r13;A3;k166;#0;r16;A3;k166;#0;r15;r14;A3;k166;#0;r20;A3;k166;#0;r19;r18;A3;k166;#0;r19;A3;k166;#0;r20;r18;A4;k164;#0;i0;#63;A3;k166;#0;r21;A3;k166;#0;r20;r19;A4;k164;#0;i0;#63;A3;k166;#0;r20;A3;k166;#0;r21;r19;LA;R#1;LB;R#1;LC;R#1;Lcr;Rk173;LMx;RP~RA1;i91;A1;o92;Y6;00;A1;i93;A1;i91;A1;o92;#2;LVM;Ri174;LHI;Ri175;LL;Ri176;LSCFG_P;Ri177;LHIok;RA3;i178;r2;A1;k179;r1;r3;LHH;RA5;k180;r4;A3;k166;#0;r10;A3;k166;#0;r9;r8;r7;r6;r5;A12;k181;r4;#3;r5;r2;#4;A3;k166;#0;r10;A3;k166;#0;r11;r9;r8;r7;r6;r1;Lb;R#0;A2;Llemma;RA2;k182;#7;A2;i67;#8;#9;A9;k183;pk182;k184;A3;k84;#0;r2;#11;#14;r1;#17;#17;#18;A4;k186;#0;r12;#5;r1;A2;Llemma;RA2;k182;#9;A2;i67;#19;#20;A9;k183;pk182;k184;#14;#24;A11;k187;p#25;k182;#26;i67;k189;#12;A4;k190;pk182;#27;#12;#13;#23;r1;#17;#17;#18;A4;k186;#0;r11;r10;r1;A2;Llemma;RA2;k182;A3;k84;#0;r1;A3;k166;#0;r11;#28;A2;i67;#19;#29;A7;k193;pk182;#30;#24;#17;#32;r1;A4;k186;#0;r11;#28;r1;A2;Llemma;RA2;k182;#29;A2;i67;#8;#20;A7;k193;pk182;#30;#24;#32;A2;i67;#21;#33;A11;k187;p#25;k182;#26;i67;k189;#21;A4;k190;pk182;#27;#21;#31;#33;r1;A4;k186;#0;r12;r10;r1;A5;k196;i0;i0;Lb;R#0;A2;k182;A2;i67;#34;A2;i67;#8;#19;A2;i67;#8;A2;i67;#34;#19;La;Ri0;Lb0;Ri0;A4;o88;P~R#39;#45;P~R#46;#48;LH;R#39;A6;k144;#42;#47;#45;LH0;R#42;A3;o90;#50;#53;A3;o89;#51;#52;r1;LH0;R#47;A6;k144;#50;#52;A2;i67;#50;#53;LH;R#50;A3;o89;#55;#58;r1;LH;R#52;A3;o90;#55;#58;A3;o90;#56;#57;r1;r1;r1;LH;R#46;A6;k144;#41;#44;#48;LH0;R#41;A3;o90;#51;#59;A3;o89;#50;#52;r1;LH0;R#44;A6;k144;#51;#52;A2;i67;#51;#59;LH;R#51;A3;o89;#56;#60;r1;LH;R#52;A3;o90;#56;#60;A3;o90;#55;#57;r1;r1;r1;r1;Ea;RA9;k197;r4;#3;r5;r2;#4;r8;r7;r6;r1;A2;i40;Pb;R#0;P~R#7;A2;i40;A3;k198;r6;#61;#62;A2;i40;A3;k200;r9;#61;#62;A3;k201;#61;#62;A2;k171;#61;#11;A2;i40;A2;i163;i0;A4;k164;#0;i0;#63;#4;A2;i40;A2;k1;o2;A3;k165;i0;i0;r8;A2;k1;o2;A3;k199;i0;i0;r8;m40;RNL~RA2;i40;Pb;R#0;P~RA3;k84;#0;r1;#11;A2;i40;A3;k198;r7;#61;#62;A2;i40;A3;k200;r10;#61;#62;A3;k201;#61;#62;A2;k171;#61;A3;k166;#0;r14;A3;k166;#0;r13;r12;A2;i40;A2;i163;i0;A4;k164;#0;i0;#63;#6;A2;i40;A2;k1;o2;A3;k165;i0;i0;r9;A2;k1;o2;A3;k199;i0;i0;r9;A2;i163;i0;A4;k164;#0;i0;#63;#16;r1;1;L~RPb;R#0;P~RA3;k84;#0;r1;#11;A2;i40;A3;k198;r7;#61;#62;A2;i40;A3;k200;r10;#61;#62;A3;k201;#61;#62;A2;k171;#61;A3;k166;#0;r14;A3;k166;#0;r13;r12;L~RA2;i40;A2;i163;i0;A4;k164;#0;i0;#63;A3;k166;#0;r13;A3;k166;#0;r12;r11;A2;i40;A2;k1;o2;A3;k165;i0;i0;r10;A2;k1;o2;A3;k199;i0;i0;r10;A2;L_H;RPb;R#0;P~RA3;k84;#0;r1;#64;A2;i40;A3;k198;r9;#61;#62;A2;i40;A3;k200;r12;#61;#62;A3;k201;#61;#62;A2;k171;#61;#65;LH;RA2;i40;A2;i163;i0;A4;k164;#0;i0;#63;#64;A2;i40;A2;k1;o2;A3;k165;i0;i0;r12;A2;k1;o2;A3;k199;i0;i0;r12;m40;RNL~RA2;i40;A2;i163;i0;A4;k164;#0;i0;#63;#65;A2;i40;A2;k1;o2;A3;k165;i0;i0;r13;A2;k1;o2;A3;k199;i0;i0;r13;A2;i163;i0;A4;k164;#0;i0;#63;A3;k166;#0;r16;A3;k166;#0;r17;r15;r1;1;L~RA2;i163;i0;A4;k164;#0;i0;#63;#65;L~RA2;i40;A2;k1;o2;A3;k165;i0;i0;r14;A2;k1;o2;A3;k199;i0;i0;r14;A2;LND;RA2;i163;i0;A4;k164;#0;i0;#63;A3;k166;#0;r18;A3;k166;#0;r17;r16;L_H0;RA2;i40;A2;k1;o2;A3;k165;i0;i0;r16;A2;k1;o2;A3;k199;i0;i0;r16;EP;RA6;k202;#0;i0;#63;#66;#67;A4;k203;#0;r20;r19;r18;A3;i204;i0;A4;k164;#0;i0;#63;#66;A4;k164;#0;i0;#63;#67;A4;k205;P~RA2;i163;i0;#68;A2;i163;i0;A4;k164;#0;i0;#63;A3;k166;#0;r21;A3;k166;#0;r22;r20;P~RA2;i163;i0;#69;A2;i163;i0;A4;k164;#0;i0;#63;A3;k166;#0;r22;A3;k166;#0;r21;r20;A4;k206;i0;#68;#69;r1;r3;r2;r1;r2;r1;").
Qed.

Section H.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable STRTOD_SCR : Z.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis HSS0 : 0 <= STRTOD_SCR.
Hypothesis STRINIT : PMS.strinit_spec L HI.
Hypothesis ISS : PMS.iss_ctor_spec L HI.
Hypothesis SYSCAT : PMS.system_category_spec L.
Hypothesis CCTOR : PMCS.cursor_ctor_spec L HI STRTOD_SCR.
Hypothesis GETSTR : PMCS.get_string_spec L HI STRTOD_SCR.
Hypothesis RNEXT : PMCS.read_next_spec L HI STRTOD_SCR.
Hypothesis PDTOR : PMS.parser_dtor_spec L HI.
Hypothesis SDTOR : PMS.source_dtor_spec L HI.
Hypothesis OPDELS : PMS.opdel_sized_spec L HI.
Hypothesis LOCDTOR : PMS.locale_dtor_spec L.
Hypothesis ISTRDTOR : TPS.istream_dtor_spec L.
Hypothesis IOSBDTOR : TPS.iosb_dtor_spec L.

Lemma mk_entry : forall R M spc r scr, getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 spc -> getr R 4%bv = Z_to_bv 64 PML.TP ->
  L5C.stk (hl_sptop L) M spc scr -> PML.entry L R M spc r scr.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S17;A1;o92;Y2;1;A1;o92;Y6;00;A1;i91;#1;Y3;0;A1;o4;o48;Y1;0;A1;o4;#5;Y2;0;A1;o4;#7;A2;k111;#1;k208;A1;k210;vL;A1;k207;r7;A3;i5;#2;A2;k160;r10;A3;o138;#0;#6;o102;A2;k111;#1;r8;A3;i5;#2;A2;k160;r10;A3;o138;#0;#8;o102;#9;A4;k209;#10;r9;r8;r6;A2;i40;#13;#14;A2;i40;#12;#15;LR;RA2;k153;#0;#2;LM;RP~R#2;A1;i93;A1;i91;A1;o92;#3;Lspc;Ri0;Lr;Ri0;Lscr;Ri0;LH1;RA3;i5;#2;A2;k160;r5;A3;o138;#0;#4;cvo102;A2;k139;#0;#4;A2;k111;#1;r2;LHra;RA1;k207;r3;LH2;RA3;i5;#2;A2;k160;r7;A3;o138;#0;#6;cvo102;A2;k139;#0;#6;A2;k111;#1;r5;LH4;RA3;i5;#2;A2;k160;r8;A3;o138;#0;#8;cvo102;A2;k139;#0;#8;#9;LHs;RA4;k209;#10;r8;r7;r5;A4;o88;A3;i5;#2;A2;k160;r10;A3;o138;#0;#4;o102;A2;k111;#1;r7;A2;i40;#11;#16;r5;A4;o88;#11;#16;r4;A4;o88;#12;#15;r3;A4;o88;#13;#14;r2;r1;").
Qed.
Lemma mk_stk : forall LB0 sp SS (foot : Z -> Prop) M0 M spc scr, TK2.FR L LB0 sp SS foot M0 M -> sp mod 16 = 0 -> spc = sp - 1040 -> 0 <= scr -> 1040 + scr <= SS ->
  hl_ceil L + SS <= sp -> sp <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 -> L5C.stk (hl_sptop L) M spc scr.
Proof.
intros LB0 sp0 SS0 foot M0 M1 spc scr [_ F2] Hal Hspc H0 H1 H2 H3 H4. subst spc.
split; [apply (CK.al16 _ _ Hal); reflexivity|].
split; [lia|]. split; [lia|]. split; [exact H4|].
intros i Hi. apply F2. lia.
Qed.
Lemma ra_ok_lit : forall r, 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> L5.ra_ok r.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S3;Y1;0;A1;o4;#0;A2;k11;#1;A1;o4;Y5;0f;Lr;Ri0;LH1;RA2;i40;A2;k1;o2;r1;A2;k39;r1;#2;LH2;RA3;i5;i0;A2;k10;r2;#1;o2;A4;o88;A2;i40;A2;k1;o2;r3;A2;k39;r3;#2;A3;i5;i0;A2;k10;r3;#1;o2;r2;r1;").
Qed.
Ltac mok BV Hh Hl Hmat := split; [rewrite (L5C.halted_but_vm _ _ BV); exact Hh | split; [rewrite (L5C.lazy_but_vm _ _ BV); exact Hl | rewrite (L5C.materialized_but_vm _ _ BV); exact Hmat]].
Lemma mok_of : forall m m', model_but_vm m m' -> PML.model_ok m -> PML.model_ok m'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S13;A1;i91;A1;o92;Y6;00;A1;i93;#0;A1;o56;#0;A2;i95;#0;#0;A1;i17;#3;A1;o15;#3;A1;i17;#0;A1;o15;#0;A1;k226;r11;A3;i5;#6;#8;#7;A1;k224;r11;A1;k225;r11;A3;i5;#4;#11;#5;Lm;Ri221;Lm';Ri221;LBV;RA2;k222;r2;r1;LH;RA1;k223;r3;m40;RNL~RA2;i40;A3;i5;#1;A1;k224;r4;#2;A2;i40;A3;i5;#4;A1;k225;r4;#5;A3;i5;#6;A1;k226;r4;#7;A1;k223;r4;r1;1;L~RA3;i5;#1;A1;k224;r4;#2;L~RA2;i40;A3;i5;#4;A1;k225;r5;#5;A3;i5;#6;A1;k226;r5;#7;A2;LHh;RA3;i5;#1;A1;k224;r6;#2;LH;RA2;i40;A3;i5;#4;A1;k225;r7;#5;A3;i5;#6;A1;k226;r7;#7;m40;RNL~RA2;i40;A3;i5;#4;A1;k225;r8;#5;A3;i5;#6;A1;k226;r8;#7;A1;k223;r8;r1;1;L~RA3;i5;#4;A1;k225;r8;#5;L~RA3;i5;#6;A1;k226;r9;#7;A2;LHl;RA3;i5;#4;A1;k225;r10;#5;LHmat;R#9;A4;o88;A3;i5;#1;#10;#2;A2;i40;#12;#9;A6;k9;#1;A1;k224;r12;Lo;R#1;A3;i5;#1;r1;#2;r6;#10;A3;k227;r12;r11;r10;A4;o88;#12;#9;A6;k9;#4;A1;k225;r12;Ll;R#4;A3;i5;#4;r1;#5;r2;#11;A3;k228;r12;r11;r10;A6;k9;#6;A1;k226;r12;Ll;R#6;A3;i5;#6;r1;#7;r1;#8;A3;k229;r12;r11;r10;r2;r1;r2;r1;").
Qed.

Lemma src_source : forall (Mx : mem) S IS ch bof, PMCS.src_at Mx S IS ch bof -> L5.defined Mx S 320 -> PML.source_at Mx S ch.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S23;Y6;00;Y3;0;A1;o4;Y7;70;A1;o4;Y7;78;Y4;0;A1;o4;#4;A1;o4;Y8;08;A1;o4;Y8;10;A1;o4;Y14;0000;A1;o4;Y8;18;A1;o4;Y8;20;A1;o4;Y8;28;A1;o4;Y6;18;A1;o4;Y4;8;Y5;00;A1;o4;#14;A1;o4;Y8;40;A3;k231;r39;A2;k6;r38;#7;#8;A2;i83;i0;Lst0;Ri0;A4;k233;r40;A2;k6;r39;#12;r1;A2;k6;r39;#13;A3;k231;r39;A2;k6;r38;#15;k234;A3;k214;r39;r38;#16;A2;i40;#19;#20;A2;i40;#18;#21;LMx;RP~RA1;i91;A1;o92;#0;A1;i93;A1;i91;A1;o92;#1;LS;Ri0;LIS;Ri0;Lch;Ri0;Lbof;Ri31;LH;RA5;k230;r5;r4;r3;r2;r1;m40;RNL~RA2;i40;A3;k231;r6;A2;k6;r5;#2;r4;A2;i40;A3;k231;r6;A2;k6;r5;#3;A2;k6;r4;#5;A2;i40;A3;k231;r6;A2;k6;r5;#6;r3;A2;i40;A3;k231;r6;A2;k6;r5;#7;#8;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r7;A2;k6;r6;#9;r1;A2;i40;A2;k1;r4;r1;A2;k1;r1;A2;k6;r4;#8;A2;i40;A3;k231;r6;A2;k6;r5;#10;o2;A2;i40;A3;k124;r6;A2;k6;r5;#11;A1;k232;r2;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r7;A2;k6;r6;#12;r1;A2;k6;r6;#13;A3;k231;r6;A2;k6;r5;#15;k234;P~RA3;k214;r7;r6;#16;A3;k235;r8;r7;r5;r1;1;L~RA3;k231;r6;A2;k6;r5;#2;r4;L~RA2;i40;A3;k231;r7;A2;k6;r6;#3;A2;k6;r5;#5;A2;i40;A3;k231;r7;A2;k6;r6;#6;r4;A2;i40;A3;k231;r7;A2;k6;r6;#7;#8;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r8;A2;k6;r7;#9;r1;A2;i40;A2;k1;r5;r1;A2;k1;r1;A2;k6;r5;#8;A2;i40;A3;k231;r7;A2;k6;r6;#10;o2;A2;i40;A3;k124;r7;A2;k6;r6;#11;A1;k232;r3;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r8;A2;k6;r7;#12;r1;A2;k6;r7;#13;A3;k231;r7;A2;k6;r6;#15;k234;A2;L_H;RA3;k231;r8;A2;k6;r7;#2;r6;LH;RA2;i40;A3;k231;r9;A2;k6;r8;#3;A2;k6;r7;#5;A2;i40;A3;k231;r9;A2;k6;r8;#6;r6;A2;i40;A3;k231;r9;A2;k6;r8;#7;#8;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r10;A2;k6;r9;#9;r1;A2;i40;A2;k1;r7;r1;A2;k1;r1;A2;k6;r7;#8;A2;i40;A3;k231;r9;A2;k6;r8;#10;o2;A2;i40;A3;k124;r9;A2;k6;r8;#11;A1;k232;r5;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r10;A2;k6;r9;#12;r1;A2;k6;r9;#13;A3;k231;r9;A2;k6;r8;#15;k234;m40;RNL~RA2;i40;A3;k231;r10;A2;k6;r9;#3;A2;k6;r8;#5;A2;i40;A3;k231;r10;A2;k6;r9;#6;r7;A2;i40;A3;k231;r10;A2;k6;r9;#7;#8;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r11;A2;k6;r10;#9;r1;A2;i40;A2;k1;r8;r1;A2;k1;r1;A2;k6;r8;#8;A2;i40;A3;k231;r10;A2;k6;r9;#10;o2;A2;i40;A3;k124;r10;A2;k6;r9;#11;A1;k232;r6;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r11;A2;k6;r10;#12;r1;A2;k6;r10;#13;A3;k231;r10;A2;k6;r9;#15;k234;P~RA3;k214;r11;r10;#16;A3;k235;r12;r11;r9;r1;1;L~RA3;k231;r10;A2;k6;r9;#3;A2;k6;r8;#5;L~RA2;i40;A3;k231;r11;A2;k6;r10;#6;r8;A2;i40;A3;k231;r11;A2;k6;r10;#7;#8;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r12;A2;k6;r11;#9;r1;A2;i40;A2;k1;r9;r1;A2;k1;r1;A2;k6;r9;#8;A2;i40;A3;k231;r11;A2;k6;r10;#10;o2;A2;i40;A3;k124;r11;A2;k6;r10;#11;A1;k232;r7;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r12;A2;k6;r11;#12;r1;A2;k6;r11;#13;A3;k231;r11;A2;k6;r10;#15;k234;A2;L_H0;RA3;k231;r12;A2;k6;r11;#3;A2;k6;r10;#5;LH;RA2;i40;A3;k231;r13;A2;k6;r12;#6;r10;A2;i40;A3;k231;r13;A2;k6;r12;#7;#8;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r14;A2;k6;r13;#9;r1;A2;i40;A2;k1;r11;r1;A2;k1;r1;A2;k6;r11;#8;A2;i40;A3;k231;r13;A2;k6;r12;#10;o2;A2;i40;A3;k124;r13;A2;k6;r12;#11;A1;k232;r9;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r14;A2;k6;r13;#12;r1;A2;k6;r13;#13;A3;k231;r13;A2;k6;r12;#15;k234;m40;RNL~RA2;i40;A3;k231;r14;A2;k6;r13;#6;r11;A2;i40;A3;k231;r14;A2;k6;r13;#7;#8;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r15;A2;k6;r14;#9;r1;A2;i40;A2;k1;r12;r1;A2;k1;r1;A2;k6;r12;#8;A2;i40;A3;k231;r14;A2;k6;r13;#10;o2;A2;i40;A3;k124;r14;A2;k6;r13;#11;A1;k232;r10;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r15;A2;k6;r14;#12;r1;A2;k6;r14;#13;A3;k231;r14;A2;k6;r13;#15;k234;P~RA3;k214;r15;r14;#16;A3;k235;r16;r15;r13;r1;1;L~RA3;k231;r14;A2;k6;r13;#6;r11;L~RA2;i40;A3;k231;r15;A2;k6;r14;#7;#8;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r16;A2;k6;r15;#9;r1;A2;i40;A2;k1;r13;r1;A2;k1;r1;A2;k6;r13;#8;A2;i40;A3;k231;r15;A2;k6;r14;#10;o2;A2;i40;A3;k124;r15;A2;k6;r14;#11;A1;k232;r11;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r16;A2;k6;r15;#12;r1;A2;k6;r15;#13;A3;k231;r15;A2;k6;r14;#15;k234;A2;LA;RA3;k231;r16;A2;k6;r15;#6;r13;LH;RA2;i40;A3;k231;r17;A2;k6;r16;#7;#8;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r18;A2;k6;r17;#9;r1;A2;i40;A2;k1;r15;r1;A2;k1;r1;A2;k6;r15;#8;A2;i40;A3;k231;r17;A2;k6;r16;#10;o2;A2;i40;A3;k124;r17;A2;k6;r16;#11;A1;k232;r13;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r18;A2;k6;r17;#12;r1;A2;k6;r17;#13;A3;k231;r17;A2;k6;r16;#15;k234;m40;RNL~RA2;i40;A3;k231;r18;A2;k6;r17;#7;#8;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r19;A2;k6;r18;#9;r1;A2;i40;A2;k1;r16;r1;A2;k1;r1;A2;k6;r16;#8;A2;i40;A3;k231;r18;A2;k6;r17;#10;o2;A2;i40;A3;k124;r18;A2;k6;r17;#11;A1;k232;r14;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r19;A2;k6;r18;#12;r1;A2;k6;r18;#13;A3;k231;r18;A2;k6;r17;#15;k234;P~RA3;k214;r19;r18;#16;A3;k235;r20;r19;r17;r1;1;L~RA3;k231;r18;A2;k6;r17;#7;#8;L~RA2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r20;A2;k6;r19;#9;r1;A2;i40;A2;k1;r17;r1;A2;k1;r1;A2;k6;r17;#8;A2;i40;A3;k231;r19;A2;k6;r18;#10;o2;A2;i40;A3;k124;r19;A2;k6;r18;#11;A1;k232;r15;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r20;A2;k6;r19;#12;r1;A2;k6;r19;#13;A3;k231;r19;A2;k6;r18;#15;k234;A2;LB;RA3;k231;r20;A2;k6;r19;#7;#8;LH;RA2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r22;A2;k6;r21;#9;r1;A2;i40;A2;k1;r19;r1;A2;k1;r1;A2;k6;r19;#8;A2;i40;A3;k231;r21;A2;k6;r20;#10;o2;A2;i40;A3;k124;r21;A2;k6;r20;#11;A1;k232;r17;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r22;A2;k6;r21;#12;r1;A2;k6;r21;#13;A3;k231;r21;A2;k6;r20;#15;k234;m40;RNL~RA2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r23;A2;k6;r22;#9;r1;A2;i40;A2;k1;r20;r1;A2;k1;r1;A2;k6;r20;#8;A2;i40;A3;k231;r22;A2;k6;r21;#10;o2;A2;i40;A3;k124;r22;A2;k6;r21;#11;A1;k232;r18;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r23;A2;k6;r22;#12;r1;A2;k6;r22;#13;A3;k231;r22;A2;k6;r21;#15;k234;P~RA3;k214;r23;r22;#16;A3;k235;r24;r23;r21;r1;1;L~RA2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r23;A2;k6;r22;#9;r1;A2;i40;A2;k1;r20;r1;A2;k1;r1;A2;k6;r20;#8;L~RA2;i40;A3;k231;r23;A2;k6;r22;#10;o2;A2;i40;A3;k124;r23;A2;k6;r22;#11;A1;k232;r19;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r24;A2;k6;r23;#12;r1;A2;k6;r23;#13;A3;k231;r23;A2;k6;r22;#15;k234;A2;L_H1;RA2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r25;A2;k6;r24;#9;r1;A2;i40;A2;k1;r22;r1;A2;k1;r1;A2;k6;r22;#8;LH;RA2;i40;A3;k231;r25;A2;k6;r24;#10;o2;A2;i40;A3;k124;r25;A2;k6;r24;#11;A1;k232;r21;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r26;A2;k6;r25;#12;r1;A2;k6;r25;#13;A3;k231;r25;A2;k6;r24;#15;k234;m40;RNL~RA2;i40;A3;k231;r26;A2;k6;r25;#10;o2;A2;i40;A3;k124;r26;A2;k6;r25;#11;A1;k232;r22;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r27;A2;k6;r26;#12;r1;A2;k6;r26;#13;A3;k231;r26;A2;k6;r25;#15;k234;P~RA3;k214;r27;r26;#16;A3;k235;r28;r27;r25;r1;1;L~RA3;k231;r26;A2;k6;r25;#10;o2;L~RA2;i40;A3;k124;r27;A2;k6;r26;#11;A1;k232;r23;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r28;A2;k6;r27;#12;r1;A2;k6;r27;#13;A3;k231;r27;A2;k6;r26;#15;k234;A2;L_H2;RA3;k231;r28;A2;k6;r27;#10;o2;LH;RA2;i40;A3;k124;r29;A2;k6;r28;#11;A1;k232;r25;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r30;A2;k6;r29;#12;r1;A2;k6;r29;#13;A3;k231;r29;A2;k6;r28;#15;k234;m40;RNL~RA2;i40;A3;k124;r30;A2;k6;r29;#11;A1;k232;r26;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r31;A2;k6;r30;#12;r1;A2;k6;r30;#13;A3;k231;r30;A2;k6;r29;#15;k234;P~RA3;k214;r31;r30;#16;A3;k235;r32;r31;r29;r1;1;L~RA3;k124;r30;A2;k6;r29;#11;A1;k232;r26;L~RA2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r32;A2;k6;r31;#12;r1;A2;k6;r31;#13;A3;k231;r31;A2;k6;r30;#15;k234;A2;L_H3;RA3;k124;r32;A2;k6;r31;#11;A1;k232;r28;LH;RA2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r34;A2;k6;r33;#12;r1;A2;k6;r33;#13;A3;k231;r33;A2;k6;r32;#15;k234;m40;RNL~RA2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r35;A2;k6;r34;#12;r1;A2;k6;r34;#13;A3;k231;r34;A2;k6;r33;#15;k234;P~RA3;k214;r35;r34;#16;A3;k235;r36;r35;r33;r1;1;L~RA2;i83;i0;Lst0;Ri0;A4;k233;r35;A2;k6;r34;#12;r1;A2;k6;r34;#13;L~RA3;k231;r35;A2;k6;r34;#15;k234;A2;LC;RA2;i83;i0;Lst0;Ri0;A4;k233;r37;A2;k6;r36;#12;r1;A2;k6;r36;#13;LD;RA3;k231;r37;A2;k6;r36;#15;k234;LHd;RA3;k214;r38;r37;#16;A4;o88;A3;k231;r39;A2;k6;r38;#6;r36;A2;i40;#17;#22;r23;A4;o88;#17;#22;r19;A4;o88;#18;#21;r3;A4;o88;#19;#20;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;").
Qed.

Lemma source_at_xd : forall (Kx : Z -> Prop) (Ma Mb : mem) S ch, TK.samem Kx Ma Mb -> 0 <= S < 2 ^ 60 -> TK2.cov Kx (S + 32) 8 -> TK2.cov Kx (S + 88) 192 ->
  L5.defined Mb S 320 -> PML.source_at Ma S ch -> PML.source_at Mb S ch.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S77;Y6;00;Y3;0;P~RA1;i91;A1;o92;#0;A1;i93;A1;i91;A1;o92;#1;Y1;0;A1;o4;#3;Y5;1c;A1;o4;#5;A2;k11;#4;#6;Y5;00;A1;o4;#8;A1;o4;#1;A1;o4;Y6;18;A1;o4;Y7;40;A1;o4;Y8;40;A1;o4;Y8;08;A1;o4;Y8;10;A1;o4;Y14;0000;Y4;8;A1;o4;#17;A2;k6;r28;#14;A2;k6;r28;#15;A3;k231;r29;#20;#16;Lst0;Ri0;A4;k233;r30;A2;k6;r29;#11;r1;A2;k6;r29;#18;A2;i83;i0;#22;A2;k6;r28;#9;A3;k231;r29;#24;k234;A3;k214;r29;r28;#13;A2;i40;#25;#26;A2;i40;#23;#27;A2;k130;#4;#6;A2;k39;o2;#4;P~R#30;P~RA2;k1;o2;#6;A2;k39;o2;#7;A2;k1;o2;#4;LHa;R#32;L~Ri101;A3;k131;#4;#6;r2;PHa;R#32;P~Ri101;A2;k1;o2;#7;Y5;1e;A1;o4;#35;A2;k130;#4;#36;A2;k11;#4;#36;P~R#30;P~RA2;k1;o2;#36;A2;k39;o2;#38;LHa;R#32;L~Ri101;A3;k131;#4;#36;r2;PHa;R#32;P~Ri101;A2;k1;o2;#38;A1;o15;i16;A1;i17;i16;A2;o52;i0;r2;A1;i19;i0;A1;i21;i0;A2;o26;i0;o2;A2;o55;i0;o48;A2;o26;i0;#4;A7;o54;#46;k22;i23;i23;o24;A7;o20;#46;k22;i23;i23;o24;A4;o25;i0;#47;o27;#48;o28;A7;o20;#46;k22;i23;i23;o24;A4;o25;i0;#48;o38;A3;o220;i0;#49;A1;o92;#5;o28;A1;o56;i23;A3;o57;i0;#48;A2;o26;i0;#14;A3;o220;i0;#49;A1;o92;#35;A2;k29;#46;o24;A4;k30;r1;r3;cvA2;o12;i31;o32;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;A2;i40;A2;k1;o2;r1;A2;k39;r1;#7;A2;k6;r2;#14;A2;r1;r33;r30;A2;k6;r28;#11;A3;o57;i0;#48;A2;o26;i0;#11;A2;k6;r1;#11;A2;k6;r1;#14;A1;r1;r31;A2;o26;i0;#10;A3;o57;i0;#60;A2;o26;i0;#12;A2;k6;#61;#12;A3;o57;i0;#48;A2;o26;i0;#15;A2;k6;r2;#15;A2;k6;r1;#15;Y5;1d;A1;o4;#70;A2;k11;#4;#71;A2;k6;r2;#11;A1;o4;Y7;18;A3;o57;i0;#48;A2;o26;i0;#9;A2;k6;r2;#9;LKx;RP~Ri0;pLMa;R#2;LMb;R#2;LS;Ri0;Lch;Ri0;LAG;RA3;k236;r5;r4;r3;LHS;RA2;i40;A2;k1;o2;r3;A2;k39;r3;#7;LC1;RA3;k237;r7;A2;k6;r4;#9;#10;LC2;RA3;k237;r8;A2;k6;r5;#11;#12;LHd;RA3;k214;r7;r6;#13;LH;RA3;k235;r9;r7;r6;m40;RNL~RA2;i40;A3;k231;r10;A2;k6;r8;#14;r7;A2;i40;A3;k231;r10;A2;k6;r8;#15;#16;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r11;A2;k6;r9;#11;r1;A2;k6;r9;#18;A2;i40;A3;k231;r10;A2;k6;r8;#9;k234;A3;k214;r10;r8;#13;A3;k235;r10;r9;r8;r1;1;L~RA3;k231;r10;A2;k6;r8;#14;r7;L~RA2;i40;A3;k231;r11;A2;k6;r9;#15;#16;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r12;A2;k6;r10;#11;r1;A2;k6;r10;#18;A2;i40;A3;k231;r11;A2;k6;r9;#9;k234;A3;k214;r11;r9;#13;A2;LA;RA3;k231;r12;A2;k6;r10;#14;r9;LH;RA2;i40;A3;k231;r13;A2;k6;r11;#15;#16;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r14;A2;k6;r12;#11;r1;A2;k6;r12;#18;A2;i40;A3;k231;r13;A2;k6;r11;#9;k234;A3;k214;r13;r11;#13;m40;RNL~RA2;i40;A3;k231;r14;A2;k6;r12;#15;#16;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r15;A2;k6;r13;#11;r1;A2;k6;r13;#18;A2;i40;A3;k231;r14;A2;k6;r12;#9;k234;A3;k214;r14;r12;#13;A3;k235;r14;r13;r12;r1;1;L~RA3;k231;r14;A2;k6;r12;#15;#16;L~RA2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r16;A2;k6;r14;#11;r1;A2;k6;r14;#18;A2;i40;A3;k231;r15;A2;k6;r13;#9;k234;A3;k214;r15;r13;#13;A2;LB;RA3;k231;r16;A2;k6;r14;#15;#16;LH;RA2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r18;A2;k6;r16;#11;r1;A2;k6;r16;#18;A2;i40;A3;k231;r17;A2;k6;r15;#9;k234;A3;k214;r17;r15;#13;m40;RNL~RA2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r19;A2;k6;r17;#11;r1;A2;k6;r17;#18;A2;i40;A3;k231;r18;A2;k6;r16;#9;k234;A3;k214;r18;r16;#13;A3;k235;r18;r17;r16;r1;1;L~RA2;i83;i0;Lst0;Ri0;A4;k233;r19;A2;k6;r17;#11;r1;A2;k6;r17;#18;L~RA2;i40;A3;k231;r19;A2;k6;r17;#9;k234;A3;k214;r19;r17;#13;A2;LH;RA2;i83;i0;Lst0;Ri0;A4;k233;r21;A2;k6;r19;#11;r1;A2;k6;r19;#18;m83;RNL~RA2;i83;i0;Lst0;Ri0;A4;k233;r22;A2;k6;r20;#11;r1;A2;k6;r20;#18;P~RA2;i40;A3;k231;r22;A2;k6;r20;#9;k234;A3;k214;r22;r20;#13;A3;k235;r22;r21;r20;r1;1;Lx;Ri0;L~RA1;Lst0;Ri0;A4;k233;r23;A2;k6;r21;#11;r1;A2;k6;r21;#18;r1;A2;Lst0;Ri0;LI;RA4;k233;r24;A2;k6;r22;#11;r1;A2;k6;r22;#18;LH;RA2;i40;A3;k231;r25;A2;k6;r23;#9;k234;A3;k214;r25;r23;#13;m40;RNL~RA2;i40;A3;k231;r26;A2;k6;r24;#9;k234;A3;k214;r26;r24;#13;A3;k235;r26;r25;r24;r1;1;L~RA3;k231;r26;A2;k6;r24;#9;k234;L~RA3;k214;r27;r25;#13;A2;LD;RA3;k231;r28;A2;k6;r26;#9;k234;L_H;RA3;k214;r29;r27;#13;A4;o88;A3;k231;r29;#19;r27;A2;i40;#21;#28;A9;k238;r31;r30;r29;r26;#19;r27;E__sat6;R#29;#31;E__sat5;R#33;#34;E__sat4;R#37;#39;E__sat3;R#40;#41;E__arith;RL__x1;Ri0;E__wit;R#42;#43;E__varmap;R#44;#45;E__ff;RA8;o53;#46;k22;i23;i23;o24;#50;#51;A7;o54;#46;k22;i23;i23;o24;A7;o20;#46;k22;i23;i23;o24;A4;o25;i0;#47;o27;#52;o28;A7;o20;#46;k22;i23;i23;o24;A4;o25;i0;#52;o38;#53;o28;#54;#55;P__x1;Ri0;P~R#56;A2;i40;A2;k1;o2;#57;A2;k39;#57;#38;#58;A8;k239;r31;#59;#12;#19;#10;r23;E__sat4;R#29;#31;E__sat3;R#33;#34;E__arith;RL__x1;Ri0;E__wit;R#42;#43;E__varmap;R#44;#45;E__ff;RA7;o20;#46;k22;i23;i23;o24;A4;o25;i0;#60;o27;#52;o28;#54;#55;P__x1;Ri0;A2;k1;#61;#62;#63;E__sat4;R#29;#31;E__sat3;R#33;#34;E__arith;RL__x1;Ri0;E__wit;R#42;#43;E__varmap;R#44;#45;E__ff;RA7;o20;#46;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#52;#64;o27;#65;o28;#54;#55;P__x1;Ri0;A2;k1;A2;k6;#62;#10;#66;#63;r18;A4;o88;#21;#28;A9;k238;r31;r30;r29;r26;#20;#16;E__sat6;R#29;#31;E__sat5;R#33;#34;E__sat4;R#37;#39;E__sat3;R#40;#41;E__arith;RL__x1;Ri0;E__wit;R#42;#43;E__varmap;R#44;#45;E__ff;RA8;o53;#46;k22;i23;i23;o24;#50;#51;A7;o54;#46;k22;i23;i23;o24;A7;o20;#46;k22;i23;i23;o24;A4;o25;i0;#47;o27;#67;o28;A7;o20;#46;k22;i23;i23;o24;A4;o25;i0;#67;o38;#53;o28;#54;#55;P__x1;Ri0;P~R#56;A2;i40;A2;k1;o2;#68;A2;k39;#68;#38;#58;A8;k239;r31;#59;#12;#20;#10;r23;E__sat4;R#29;#31;E__sat3;R#33;#34;E__arith;RL__x1;Ri0;E__wit;R#42;#43;E__varmap;R#44;#45;E__ff;RA7;o20;#46;k22;i23;i23;o24;A4;o25;i0;#60;o27;#67;o28;#54;#55;P__x1;Ri0;A2;k1;#61;#69;#63;E__sat4;R#29;#31;E__sat3;R#33;#34;E__arith;RL__x1;Ri0;E__wit;R#42;#43;E__varmap;R#44;#45;E__ff;RA7;o20;#46;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#67;#64;o27;#65;o28;#54;#55;P__x1;Ri0;A2;k1;A2;k6;#69;#10;#66;#63;r14;A4;o88;#23;#27;A4;o78;i0;#22;r7;A10;k240;r31;r30;r29;r26;#59;r7;A2;k6;r28;#18;E__sat6;RA2;k130;#4;#71;P~R#30;P~RA2;k1;o2;#71;A2;k39;o2;#72;E__sat5;RLHa;R#32;L~Ri101;A3;k131;#4;#71;r2;PHa;R#32;P~Ri101;A2;k1;o2;#72;E__sat4;R#29;#31;E__sat3;R#33;#34;E__arith;RL__x1;Ri0;E__wit;R#42;#43;E__varmap;R#44;#45;E__ff;RA8;o53;#46;k22;i23;i23;o24;#50;#51;A7;o54;#46;k22;i23;i23;o24;A7;o20;#46;k22;i23;i23;o24;A4;o25;i0;#47;o27;#60;o28;A7;o20;#46;k22;i23;i23;o24;A4;o25;i0;#60;o38;A3;o220;i0;#49;A1;o92;#70;o28;#54;#55;P__x1;Ri0;P~R#56;A2;i40;A2;k1;o2;#73;A2;k39;#73;#72;#58;A8;k239;r31;#59;#12;#59;#74;r23;E__sat4;R#29;#31;E__sat3;R#33;#34;E__arith;RL__x1;Ri0;E__wit;R#42;#43;E__varmap;R#44;#45;E__ff;RA7;o20;#46;k22;i23;i23;o24;A4;o25;i0;#60;o27;#60;o28;#54;#55;P__x1;Ri0;A2;k1;#61;#61;#63;E__sat4;R#29;#31;E__sat3;R#33;#34;E__arith;RL__x1;Ri0;E__wit;R#42;#43;E__varmap;R#44;#45;E__ff;RA7;o20;#46;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#60;A2;o26;i0;#74;o27;#65;o28;#54;#55;P__x1;Ri0;A2;k1;A2;k6;#61;#74;#66;#63;r6;A4;o88;#25;#26;A9;k238;r31;r30;r29;r26;#24;k234;E__sat6;R#29;#31;E__sat5;R#33;#34;E__sat4;R#37;#39;E__sat3;R#40;#41;E__arith;RL__x1;Ri0;E__wit;R#42;#43;E__varmap;R#44;#45;E__ff;RA8;o53;#46;k22;i23;i23;o24;#50;#51;A7;o54;#46;k22;i23;i23;o24;A7;o20;#46;k22;i23;i23;o24;A4;o25;i0;#47;o27;#75;o28;A7;o20;#46;k22;i23;i23;o24;A4;o25;i0;#75;o38;#53;o28;#54;#55;P__x1;Ri0;P~R#56;A2;i40;A2;k1;o2;#76;A2;k39;#76;#38;#58;r24;r2;r22;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;").
Qed.

Lemma cursor_at_xd : forall (Kx : Z -> Prop) (Ma Mb : mem) C IS ch bof dn ps, TK.samem Kx Ma Mb -> 0 <= C < 2 ^ 59 -> TK2.cov Kx (C + 8) 640 -> TK2.ps_cov Kx ps -> L5.defined Mb C 656 ->
  PMCS.cursor_at Ma C IS ch bof dn ps -> PMCS.cursor_at Mb C IS ch bof dn ps.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S189;Y6;00;Y3;0;P~RA1;i91;A1;o92;#0;A1;i93;A1;i91;A1;o92;#1;Y1;0;A1;o4;#3;Y5;1b;A1;o4;#5;A2;k11;#4;#6;A1;o4;#1;A1;o4;Y9;080;Y8;40;A1;o4;#10;A1;o4;Y9;050;A2;k6;r15;#8;A1;o4;Y7;70;A1;o4;Y7;78;Y4;0;A1;o4;#16;A1;o4;Y8;08;A1;o4;Y8;10;A1;o4;Y14;0000;A2;k6;r16;#8;A1;o4;Y8;18;A1;o4;Y8;20;Y8;28;A1;o4;#24;A1;k232;r12;A1;o4;Y6;18;Y4;8;A1;o4;#28;Y5;00;A1;o4;#30;A2;k6;r18;#8;A2;k6;r19;#8;A2;k6;r20;#8;A1;k232;r16;A2;k6;r22;#8;A2;k6;r23;#8;A2;k6;r24;#8;A1;k232;r20;A2;k6;r26;#8;A2;k6;r27;#8;A2;k6;r28;#8;A1;k232;r24;A2;k6;r31;#8;A2;k6;r30;#8;A2;k6;r32;#8;A1;k232;r28;A2;k6;r35;#8;A1;k232;r32;A2;k6;r36;#8;A2;k6;r39;#8;A1;k232;r36;A2;k6;r40;#8;A2;k6;r42;#8;A2;k6;r43;#8;A1;k232;r40;A2;k6;r44;#8;A2;k6;r46;#8;A2;k6;r47;#8;A1;k232;r44;A2;k6;r48;#8;A2;k6;r51;#8;A2;k6;r52;#8;A2;k6;r54;#8;A2;k6;r55;#8;A2;k6;r57;#8;A2;k6;r72;#8;A2;k6;r72;#11;A3;k244;r73;#68;r67;A2;k6;r72;#12;A2;k245;r73;#70;A2;k6;r72;#9;A1;k232;r68;A3;k124;r73;#72;#73;A3;k214;r73;r72;k246;A2;i40;#74;#75;A2;i40;#71;#76;A2;k6;#67;#14;A2;k6;#67;#15;A2;k6;r71;#17;A3;k231;r73;#79;#80;A2;k6;#67;#18;A3;k231;r73;#82;r70;A2;k6;#67;#19;A3;k231;r73;#84;#20;A2;k6;r73;#8;Lde;Ri0;A2;i40;A3;k231;r74;A2;k6;#86;#22;r1;A2;i40;A2;k1;r71;r1;A2;k1;r1;A2;k6;r71;#20;A2;i83;i0;#87;A2;k6;#67;#23;A3;k231;r73;#89;o2;A2;k6;#67;#25;A1;k232;r69;A3;k124;r73;#91;#92;Lst0;Ri0;A4;k233;r74;A2;k6;#86;#27;r1;A2;k6;#86;#29;A2;i83;i0;#94;A2;k6;#67;#31;A3;k231;r73;#96;k234;A2;i40;#95;#97;A2;i40;#93;#98;A2;i40;#90;#99;A2;i40;#88;#100;A2;i40;#85;#101;A2;i40;#83;#102;Y5;1e;A1;o4;#104;A2;k130;#4;#105;A2;k39;o2;#4;A2;k11;#4;#105;P~R#107;P~RA2;k1;o2;#105;A2;k39;o2;#108;A2;k1;o2;#4;LHa;R#110;L~Ri101;A3;k131;#4;#105;r2;PHa;R#110;P~Ri101;A2;k1;o2;#108;A2;k130;#4;#6;P~R#107;P~RA2;k1;o2;#6;A2;k39;o2;#7;LHa;R#110;L~Ri101;A3;k131;#4;#6;r2;PHa;R#110;P~Ri101;A2;k1;o2;#7;A1;o15;i16;A1;i17;i16;A2;o52;i0;r2;A1;i19;i0;A1;i21;i0;A2;o26;i0;o2;A2;o55;i0;o48;A2;o26;i0;#4;A7;o54;#121;k22;i23;i23;o24;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#122;o27;#123;o28;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#123;o38;A3;o220;i0;#124;A1;o92;#5;o28;A1;o56;i23;A2;o26;i0;#8;A3;o57;i0;#123;#127;A3;o57;i0;#128;A2;o26;i0;#14;A3;o220;i0;#124;A1;o92;#104;A2;k29;#121;o24;A4;k30;r1;r3;cvA2;o12;i31;o32;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;A2;i40;A2;k1;o2;r1;A2;k39;r1;#7;A2;k6;r2;#8;A2;k6;#134;#14;A2;r1;r77;r70;A2;k6;r1;#8;A2;k6;#137;#14;A1;r1;r75;A2;o26;i0;#9;A3;o57;i0;#128;#140;A2;k6;#137;#9;A3;o57;i0;#128;A2;o26;i0;#15;A2;k6;#134;#15;A2;k6;#137;#15;A3;o57;i0;#128;A2;o26;i0;#18;A2;k6;#134;#18;A2;k6;#137;#18;A2;o26;i0;#19;A3;o57;i0;#128;#149;A2;k6;#134;#19;A2;k6;#137;#19;A2;k6;#67;#22;A3;o57;i0;#128;A2;o26;i0;#22;A2;k6;#134;#22;A2;k6;#137;#22;A3;o57;i0;#128;A2;o26;i0;#23;A2;k6;#134;#23;A2;k6;#137;#23;A3;o57;i0;#128;A2;o26;i0;#25;A2;k6;#134;#25;A1;o4;o48;A2;k6;#137;#25;A2;o26;i0;#162;A2;k6;#67;#27;Y5;1d;A1;o4;#166;A2;k11;#4;#167;A3;o57;i0;#128;A2;o26;i0;#27;A2;k6;#134;#27;A1;o4;Y7;18;A2;k6;#137;#27;A3;o57;i0;#128;A2;o26;i0;#31;A2;k6;#134;#31;A2;k6;#137;#31;Y5;1c;A1;o4;#176;A2;k11;#4;#177;A3;o57;i0;#123;A2;o26;i0;#11;A2;k6;r2;#11;A2;k6;r1;#11;A3;o57;i0;#123;A2;o26;i0;#12;A2;k6;r2;#12;A1;o4;Y5;10;A2;k6;r1;#12;A3;o57;i0;#123;#140;A2;k6;r2;#9;A2;k6;r1;#9;LKx;RP~Ri0;pLMa;R#2;LMb;R#2;LC;Ri0;LIS;Ri0;Lch;Ri0;Lbof;Ri31;Ldn;Ri31;Lps;Ri241;LAG;RA3;k236;r9;r8;r7;LHC;RA2;i40;A2;k1;o2;r7;A2;k39;r7;#7;LHK;RA3;k237;r11;A2;k6;r8;#8;#9;LHP;RA2;k242;r12;r4;LDEF';RA3;k214;r11;r10;A1;o4;Y9;090;LH;RA7;k243;r13;r11;r10;r9;r8;r7;r6;m40;RNL~RA2;i40;A5;k230;r14;A2;k6;r12;#8;r11;r10;r9;A2;i40;A3;k244;r14;A2;k6;r12;#11;r7;A2;i40;A2;k245;r14;A2;k6;r12;#12;A2;i40;A3;k124;r14;A2;k6;r12;#9;A1;k232;r8;A3;k214;r14;r12;k246;A7;k243;r14;r13;r12;r11;r10;r9;r8;r1;1;L~RA5;k230;r14;A2;k6;r12;#8;r11;r10;r9;L~RA2;i40;A3;k244;r15;A2;k6;r13;#11;r8;A2;i40;A2;k245;r15;A2;k6;r13;#12;A2;i40;A3;k124;r15;A2;k6;r13;#9;A1;k232;r9;A3;k214;r15;r13;k246;A2;LH;RA5;k230;r16;A2;k6;r14;#8;r13;r12;r11;m40;RNL~RA2;i40;A3;k231;r17;A2;k6;#13;#14;r14;A2;i40;A3;k231;r17;A2;k6;#13;#15;A2;k6;r14;#17;A2;i40;A3;k231;r17;A2;k6;#13;#18;r13;A2;i40;A3;k231;r17;A2;k6;#13;#19;#20;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r18;A2;k6;#21;#22;r1;A2;i40;A2;k1;r14;r1;A2;k1;r1;A2;k6;r14;#20;A2;i40;A3;k231;r17;A2;k6;#13;#23;o2;A2;i40;A3;k124;r17;A2;k6;#13;#25;#26;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r18;A2;k6;#21;#27;r1;A2;k6;#21;#29;A3;k231;r17;A2;k6;#13;#31;k234;P~RA2;i40;A3;k244;r18;A2;k6;r16;#11;r11;A2;i40;A2;k245;r18;A2;k6;r16;#12;A2;i40;A3;k124;r18;A2;k6;r16;#9;#26;A3;k214;r18;r16;k246;A7;k243;r18;r17;r16;r15;r14;r13;r12;r1;1;L~RA3;k231;r17;A2;k6;#13;#14;r14;L~RA2;i40;A3;k231;r18;A2;k6;A2;k6;r16;#8;#15;A2;k6;r15;#17;A2;i40;A3;k231;r18;A2;k6;A2;k6;r16;#8;#18;r14;A2;i40;A3;k231;r18;A2;k6;A2;k6;r16;#8;#19;#20;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r19;A2;k6;A2;k6;r17;#8;#22;r1;A2;i40;A2;k1;r15;r1;A2;k1;r1;A2;k6;r15;#20;A2;i40;A3;k231;r18;A2;k6;A2;k6;r16;#8;#23;o2;A2;i40;A3;k124;r18;A2;k6;A2;k6;r16;#8;#25;A1;k232;r13;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r19;A2;k6;A2;k6;r17;#8;#27;r1;A2;k6;A2;k6;r17;#8;#29;A3;k231;r18;A2;k6;A2;k6;r16;#8;#31;k234;A2;LS240;RA3;k231;r19;A2;k6;A2;k6;r17;#8;#14;r16;LH;RA2;i40;A3;k231;r20;A2;k6;#32;#15;A2;k6;r17;#17;A2;i40;A3;k231;r20;A2;k6;#32;#18;r16;A2;i40;A3;k231;r20;A2;k6;#32;#19;#20;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r21;A2;k6;#33;#22;r1;A2;i40;A2;k1;r17;r1;A2;k1;r1;A2;k6;r17;#20;A2;i40;A3;k231;r20;A2;k6;#32;#23;o2;A2;i40;A3;k124;r20;A2;k6;#32;#25;A1;k232;r15;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r21;A2;k6;#33;#27;r1;A2;k6;#33;#29;A3;k231;r20;A2;k6;#32;#31;k234;m40;RNL~RA2;i40;A3;k231;r21;A2;k6;#33;#15;A2;k6;r18;#17;A2;i40;A3;k231;r21;A2;k6;#33;#18;r17;A2;i40;A3;k231;r21;A2;k6;#33;#19;#20;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r22;A2;k6;#34;#22;r1;A2;i40;A2;k1;r18;r1;A2;k1;r1;A2;k6;r18;#20;A2;i40;A3;k231;r21;A2;k6;#33;#23;o2;A2;i40;A3;k124;r21;A2;k6;#33;#25;#35;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r22;A2;k6;#34;#27;r1;A2;k6;#34;#29;A3;k231;r21;A2;k6;#33;#31;k234;P~RA2;i40;A3;k244;r22;A2;k6;r20;#11;r15;A2;i40;A2;k245;r22;A2;k6;r20;#12;A2;i40;A3;k124;r22;A2;k6;r20;#9;#35;A3;k214;r22;r20;k246;A7;k243;r22;r21;r20;r19;r18;r17;r16;r1;1;L~RA3;k231;r21;A2;k6;#33;#15;A2;k6;r18;#17;L~RA2;i40;A3;k231;r22;A2;k6;A2;k6;r20;#8;#18;r18;A2;i40;A3;k231;r22;A2;k6;A2;k6;r20;#8;#19;#20;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r23;A2;k6;A2;k6;r21;#8;#22;r1;A2;i40;A2;k1;r19;r1;A2;k1;r1;A2;k6;r19;#20;A2;i40;A3;k231;r22;A2;k6;A2;k6;r20;#8;#23;o2;A2;i40;A3;k124;r22;A2;k6;A2;k6;r20;#8;#25;A1;k232;r17;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r23;A2;k6;A2;k6;r21;#8;#27;r1;A2;k6;A2;k6;r21;#8;#29;A3;k231;r22;A2;k6;A2;k6;r20;#8;#31;k234;A2;LS248;RA3;k231;r23;A2;k6;A2;k6;r21;#8;#15;A2;k6;r20;#17;LH;RA2;i40;A3;k231;r24;A2;k6;#36;#18;r20;A2;i40;A3;k231;r24;A2;k6;#36;#19;#20;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r25;A2;k6;#37;#22;r1;A2;i40;A2;k1;r21;r1;A2;k1;r1;A2;k6;r21;#20;A2;i40;A3;k231;r24;A2;k6;#36;#23;o2;A2;i40;A3;k124;r24;A2;k6;#36;#25;A1;k232;r19;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r25;A2;k6;#37;#27;r1;A2;k6;#37;#29;A3;k231;r24;A2;k6;#36;#31;k234;m40;RNL~RA2;i40;A3;k231;r25;A2;k6;#37;#18;r21;A2;i40;A3;k231;r25;A2;k6;#37;#19;#20;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r26;A2;k6;#38;#22;r1;A2;i40;A2;k1;r22;r1;A2;k1;r1;A2;k6;r22;#20;A2;i40;A3;k231;r25;A2;k6;#37;#23;o2;A2;i40;A3;k124;r25;A2;k6;#37;#25;#39;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r26;A2;k6;#38;#27;r1;A2;k6;#38;#29;A3;k231;r25;A2;k6;#37;#31;k234;P~RA2;i40;A3;k244;r26;A2;k6;r24;#11;r19;A2;i40;A2;k245;r26;A2;k6;r24;#12;A2;i40;A3;k124;r26;A2;k6;r24;#9;#39;A3;k214;r26;r24;k246;A7;k243;r26;r25;r24;r23;r22;r21;r20;r1;1;L~RA3;k231;r25;A2;k6;#37;#18;r21;L~RA2;i40;A3;k231;r26;A2;k6;A2;k6;r24;#8;#19;#20;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r27;A2;k6;A2;k6;r25;#8;#22;r1;A2;i40;A2;k1;r23;r1;A2;k1;r1;A2;k6;r23;#20;A2;i40;A3;k231;r26;A2;k6;A2;k6;r24;#8;#23;o2;A2;i40;A3;k124;r26;A2;k6;A2;k6;r24;#8;#25;A1;k232;r21;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r27;A2;k6;A2;k6;r25;#8;#27;r1;A2;k6;A2;k6;r25;#8;#29;A3;k231;r26;A2;k6;A2;k6;r24;#8;#31;k234;A2;LS264;RA3;k231;r27;A2;k6;A2;k6;r25;#8;#18;r23;LH;RA2;i40;A3;k231;r28;A2;k6;#40;#19;#20;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r29;A2;k6;#41;#22;r1;A2;i40;A2;k1;r25;r1;A2;k1;r1;A2;k6;r25;#20;A2;i40;A3;k231;r28;A2;k6;#40;#23;o2;A2;i40;A3;k124;r28;A2;k6;#40;#25;A1;k232;r23;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r29;A2;k6;#41;#27;r1;A2;k6;#41;#29;A3;k231;r28;A2;k6;#40;#31;k234;m40;RNL~RA2;i40;A3;k231;r29;A2;k6;#41;#19;#20;A2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r30;A2;k6;#42;#22;r1;A2;i40;A2;k1;r26;r1;A2;k1;r1;A2;k6;r26;#20;A2;i40;A3;k231;r29;A2;k6;#41;#23;o2;A2;i40;A3;k124;r29;A2;k6;#41;#25;#43;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r30;A2;k6;#42;#27;r1;A2;k6;#42;#29;A3;k231;r29;A2;k6;#41;#31;k234;P~RA2;i40;A3;k244;r30;A2;k6;r28;#11;r23;A2;i40;A2;k245;r30;A2;k6;r28;#12;A2;i40;A3;k124;r30;A2;k6;r28;#9;#43;A3;k214;r30;r28;k246;A7;k243;r30;r29;r28;r27;r26;r25;r24;r1;1;L~RA3;k231;r29;A2;k6;#41;#19;#20;L~RA2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r31;A2;k6;A2;k6;r29;#8;#22;r1;A2;i40;A2;k1;r27;r1;A2;k1;r1;A2;k6;r27;#20;A2;i40;A3;k231;r30;A2;k6;A2;k6;r28;#8;#23;o2;A2;i40;A3;k124;r30;A2;k6;A2;k6;r28;#8;#25;A1;k232;r25;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r31;A2;k6;A2;k6;r29;#8;#27;r1;A2;k6;A2;k6;r29;#8;#29;A3;k231;r30;A2;k6;A2;k6;r28;#8;#31;k234;A2;LS272;RA3;k231;r31;A2;k6;A2;k6;r29;#8;#19;#20;LH;RA2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r33;A2;k6;#44;#22;r1;A2;i40;A2;k1;r29;r1;A2;k1;r1;A2;k6;r29;#20;A2;i40;A3;k231;r32;A2;k6;#45;#23;o2;A2;i40;A3;k124;r32;A2;k6;#45;#25;A1;k232;r27;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r33;A2;k6;#44;#27;r1;A2;k6;#44;#29;A3;k231;r32;A2;k6;#45;#31;k234;m40;RNL~RA2;i40;A2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r34;A2;k6;#46;#22;r1;A2;i40;A2;k1;r30;r1;A2;k1;r1;A2;k6;r30;#20;A2;i40;A3;k231;r33;A2;k6;#44;#23;o2;A2;i40;A3;k124;r33;A2;k6;#44;#25;#47;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r34;A2;k6;#46;#27;r1;A2;k6;#46;#29;A3;k231;r33;A2;k6;#44;#31;k234;P~RA2;i40;A3;k244;r34;A2;k6;r32;#11;r27;A2;i40;A2;k245;r34;A2;k6;r32;#12;A2;i40;A3;k124;r34;A2;k6;r32;#9;#47;A3;k214;r34;r32;k246;A7;k243;r34;r33;r32;r31;r30;r29;r28;r1;1;L~RA2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r34;A2;k6;#46;#22;r1;A2;i40;A2;k1;r30;r1;A2;k1;r1;A2;k6;r30;#20;L~RA2;i40;A3;k231;r34;A2;k6;A2;k6;r32;#8;#23;o2;A2;i40;A3;k124;r34;A2;k6;A2;k6;r32;#8;#25;A1;k232;r29;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r35;A2;k6;A2;k6;r33;#8;#27;r1;A2;k6;A2;k6;r33;#8;#29;A3;k231;r34;A2;k6;A2;k6;r32;#8;#31;k234;A2;LH;RA2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r36;A2;k6;A2;k6;r34;#8;#22;r1;A2;i40;A2;k1;r32;r1;A2;k1;r1;A2;k6;r32;#20;m83;RNL~RA2;i83;i0;Lde;Ri0;A2;i40;A3;k231;r37;A2;k6;#48;#22;r1;A2;i40;A2;k1;r33;r1;A2;k1;r1;A2;k6;r33;#20;P~RA2;i40;A3;k231;r37;A2;k6;#48;#23;o2;A2;i40;A3;k124;r37;A2;k6;#48;#25;#49;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r38;A2;k6;#50;#27;r1;A2;k6;#50;#29;A3;k231;r37;A2;k6;#48;#31;k234;P~RA2;i40;A3;k244;r38;A2;k6;r36;#11;r31;A2;i40;A2;k245;r38;A2;k6;r36;#12;A2;i40;A3;k124;r38;A2;k6;r36;#9;#49;A3;k214;r38;r36;k246;A7;k243;r38;r37;r36;r35;r34;r33;r32;r1;1;Lx;Ri0;L~RA1;Lde;Ri0;A2;i40;A3;k231;r38;A2;k6;A2;k6;r36;#8;#22;r1;A2;i40;A2;k1;r34;r1;A2;k1;r1;A2;k6;r34;#20;r1;A2;Lde;Ri0;LH;RA2;i40;A3;k231;r39;A2;k6;A2;k6;r37;#8;#22;r1;A2;i40;A2;k1;r35;r1;A2;k1;r1;A2;k6;r35;#20;m40;RNL~RA2;i40;A3;k231;r40;A2;k6;A2;k6;r38;#8;#22;r2;A2;i40;A2;k1;r36;r2;A2;k1;r2;A2;k6;r36;#20;P~RA2;i40;A3;k231;r41;A2;k6;#51;#23;o2;A2;i40;A3;k124;r41;A2;k6;#51;#25;#52;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r42;A2;k6;#53;#27;r1;A2;k6;#53;#29;A3;k231;r41;A2;k6;#51;#31;k234;P~RA2;i40;A3;k244;r42;A2;k6;r40;#11;r35;A2;i40;A2;k245;r42;A2;k6;r40;#12;A2;i40;A3;k124;r42;A2;k6;r40;#9;#52;A3;k214;r42;r40;k246;A7;k243;r42;r41;r40;r39;r38;r37;r36;r1;1;L~RA3;k231;r40;A2;k6;A2;k6;r38;#8;#22;r2;L~RA2;i40;A2;k1;r37;r3;A2;k1;r3;A2;k6;r37;#20;A2;LS280;RA3;k231;r42;A2;k6;#53;#22;r4;LHde;RA2;i40;A2;k1;r39;r5;A2;k1;r5;A2;k6;r39;#20;LH;RA2;i40;A3;k231;r44;A2;k6;#54;#23;o2;A2;i40;A3;k124;r44;A2;k6;#54;#25;A1;k232;r39;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r45;A2;k6;#55;#27;r1;A2;k6;#55;#29;A3;k231;r44;A2;k6;#54;#31;k234;m40;RNL~RA2;i40;A3;k231;r45;A2;k6;#55;#23;o2;A2;i40;A3;k124;r45;A2;k6;#55;#25;#56;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r46;A2;k6;#57;#27;r1;A2;k6;#57;#29;A3;k231;r45;A2;k6;#55;#31;k234;P~RA2;i40;A3;k244;r46;A2;k6;r44;#11;r39;A2;i40;A2;k245;r46;A2;k6;r44;#12;A2;i40;A3;k124;r46;A2;k6;r44;#9;#56;A3;k214;r46;r44;k246;A7;k243;r46;r45;r44;r43;r42;r41;r40;r1;1;L~RA3;k231;r45;A2;k6;#55;#23;o2;L~RA2;i40;A3;k124;r46;A2;k6;A2;k6;r44;#8;#25;A1;k232;r41;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r47;A2;k6;A2;k6;r45;#8;#27;r1;A2;k6;A2;k6;r45;#8;#29;A3;k231;r46;A2;k6;A2;k6;r44;#8;#31;k234;A2;LS288;RA3;k231;r47;A2;k6;A2;k6;r45;#8;#23;o2;LH;RA2;i40;A3;k124;r48;A2;k6;#58;#25;A1;k232;r43;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r49;A2;k6;#59;#27;r1;A2;k6;#59;#29;A3;k231;r48;A2;k6;#58;#31;k234;m40;RNL~RA2;i40;A3;k124;r49;A2;k6;#59;#25;#60;A2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r50;A2;k6;#61;#27;r1;A2;k6;#61;#29;A3;k231;r49;A2;k6;#59;#31;k234;P~RA2;i40;A3;k244;r50;A2;k6;r48;#11;r43;A2;i40;A2;k245;r50;A2;k6;r48;#12;A2;i40;A3;k124;r50;A2;k6;r48;#9;#60;A3;k214;r50;r48;k246;A7;k243;r50;r49;r48;r47;r46;r45;r44;r1;1;L~RA3;k124;r49;A2;k6;#59;#25;#60;L~RA2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r51;A2;k6;A2;k6;r49;#8;#27;r1;A2;k6;A2;k6;r49;#8;#29;A3;k231;r50;A2;k6;A2;k6;r48;#8;#31;k234;A2;LS296;RA3;k124;r51;A2;k6;A2;k6;r49;#8;#25;A1;k232;r46;LH;RA2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r53;A2;k6;#62;#27;r1;A2;k6;#62;#29;A3;k231;r52;A2;k6;A2;k6;r50;#8;#31;k234;m40;RNL~RA2;i40;A2;i83;i0;Lst0;Ri0;A4;k233;r54;A2;k6;#63;#27;r1;A2;k6;#63;#29;A3;k231;r53;A2;k6;#62;#31;k234;P~RA2;i40;A3;k244;r54;A2;k6;r52;#11;r47;A2;i40;A2;k245;r54;A2;k6;r52;#12;A2;i40;A3;k124;r54;A2;k6;r52;#9;A1;k232;r48;A3;k214;r54;r52;k246;A7;k243;r54;r53;r52;r51;r50;r49;r48;r1;1;L~RA2;i83;i0;Lst0;Ri0;A4;k233;r54;A2;k6;#63;#27;r1;A2;k6;#63;#29;L~RA3;k231;r54;A2;k6;A2;k6;r52;#8;#31;k234;A2;LH;RA2;i83;i0;Lst0;Ri0;A4;k233;r56;A2;k6;#64;#27;r1;A2;k6;#64;#29;m83;RNL~RA2;i83;i0;Lst0;Ri0;A4;k233;r57;A2;k6;#65;#27;r1;A2;k6;#65;#29;P~RA3;k231;r57;A2;k6;#65;#31;k234;P~RA2;i40;A3;k244;r58;A2;k6;r56;#11;r51;A2;i40;A2;k245;r58;A2;k6;r56;#12;A2;i40;A3;k124;r58;A2;k6;r56;#9;A1;k232;r52;A3;k214;r58;r56;k246;A7;k243;r58;r57;r56;r55;r54;r53;r52;r1;1;Lx;Ri0;L~RA1;Lst0;Ri0;A4;k233;r58;A2;k6;A2;k6;r56;#8;#27;r1;A2;k6;A2;k6;r56;#8;#29;r1;A2;Lst0;Ri0;LIOSB;RA4;k233;r59;A2;k6;#66;#27;r1;A2;k6;#66;#29;LS32;RA3;k231;r60;A2;k6;A2;k6;r58;#8;#31;k234;LH;RA2;i40;A3;k244;r61;A2;k6;r59;#11;r54;A2;i40;A2;k245;r61;A2;k6;r59;#12;A2;i40;A3;k124;r61;A2;k6;r59;#9;A1;k232;r55;A3;k214;r61;r59;k246;m40;RNL~RA2;i40;A3;k244;r62;A2;k6;r60;#11;r55;A2;i40;A2;k245;r62;A2;k6;r60;#12;A2;i40;A3;k124;r62;A2;k6;r60;#9;A1;k232;r56;A3;k214;r62;r60;k246;A7;k243;r62;r61;r60;r59;r58;r57;r56;r1;1;L~RA3;k244;r62;A2;k6;r60;#11;r55;L~RA2;i40;A2;k245;r63;A2;k6;r61;#12;A2;i40;A3;k124;r63;A2;k6;r61;#9;A1;k232;r57;A3;k214;r63;r61;k246;A2;LPA;RA3;k244;r64;A2;k6;r62;#11;r57;LH;RA2;i40;A2;k245;r65;A2;k6;r63;#12;A2;i40;A3;k124;r65;A2;k6;r63;#9;A1;k232;r59;A3;k214;r65;r63;k246;m40;RNL~RA2;i40;A2;k245;r66;A2;k6;r64;#12;A2;i40;A3;k124;r66;A2;k6;r64;#9;A1;k232;r60;A3;k214;r66;r64;k246;A7;k243;r66;r65;r64;r63;r62;r61;r60;r1;1;L~RA2;k245;r66;A2;k6;r64;#12;L~RA2;i40;A3;k124;r67;A2;k6;r65;#9;A1;k232;r61;A3;k214;r67;r65;k246;A2;LVA;RA2;k245;r68;A2;k6;r66;#12;LH;RA2;i40;A3;k124;r69;A2;k6;r67;#9;A1;k232;r63;A3;k214;r69;r67;k246;m40;RNL~RA2;i40;A3;k124;r70;A2;k6;r68;#9;A1;k232;r64;A3;k214;r70;r68;k246;A7;k243;r70;r69;r68;r67;r66;r65;r64;r1;1;L~RA3;k124;r70;A2;k6;r68;#9;A1;k232;r64;L~RA3;k214;r71;r69;k246;A2;LDN;RA3;k124;r72;A2;k6;r70;#9;A1;k232;r66;LDEF;RA3;k214;r73;r71;k246;A4;o88;A5;k230;r73;#67;r71;r70;r69;A2;i40;#69;#77;A4;o88;A3;k231;r73;#78;r71;A2;i40;#81;#103;A9;k238;r75;r74;r73;r66;#78;r71;E__sat300;R#106;#109;E__sat299;R#111;#112;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA8;o53;#121;k22;i23;i23;o24;#125;#126;A7;o54;#121;k22;i23;i23;o24;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#122;o27;#129;o28;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#129;o38;#130;o28;#131;#132;P__x1;Ri0;P~R#133;A2;i40;A2;k1;o2;#135;A2;k39;#135;#108;#136;A8;k239;r75;#67;#9;#78;#8;r64;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#128;o27;#129;o28;#131;#132;P__x1;Ri0;A2;k1;#137;#138;#139;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#129;#127;o27;#141;o28;#131;#132;P__x1;Ri0;A2;k1;A2;k6;#138;#8;#142;#139;r55;A4;o88;#81;#103;A9;k238;r75;r74;r73;r66;#79;#80;E__sat300;R#106;#109;E__sat299;R#111;#112;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA8;o53;#121;k22;i23;i23;o24;#125;#126;A7;o54;#121;k22;i23;i23;o24;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#122;o27;#143;o28;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#143;o38;#130;o28;#131;#132;P__x1;Ri0;P~R#133;A2;i40;A2;k1;o2;#144;A2;k39;#144;#108;#136;A8;k239;r75;#67;#9;#79;#8;r64;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#128;o27;#143;o28;#131;#132;P__x1;Ri0;A2;k1;#137;#145;#139;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#143;#127;o27;#141;o28;#131;#132;P__x1;Ri0;A2;k1;A2;k6;#145;#8;#142;#139;r51;A4;o88;#83;#102;A9;k238;r75;r74;r73;r66;#82;r70;E__sat300;R#106;#109;E__sat299;R#111;#112;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA8;o53;#121;k22;i23;i23;o24;#125;#126;A7;o54;#121;k22;i23;i23;o24;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#122;o27;#146;o28;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#146;o38;#130;o28;#131;#132;P__x1;Ri0;P~R#133;A2;i40;A2;k1;o2;#147;A2;k39;#147;#108;#136;A8;k239;r75;#67;#9;#82;#8;r64;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#128;o27;#146;o28;#131;#132;P__x1;Ri0;A2;k1;#137;#148;#139;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#146;#127;o27;#141;o28;#131;#132;P__x1;Ri0;A2;k1;A2;k6;#148;#8;#142;#139;r47;A4;o88;#85;#101;A9;k238;r75;r74;r73;r66;#84;#20;E__sat300;R#106;#109;E__sat299;R#111;#112;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA8;o53;#121;k22;i23;i23;o24;#125;#126;A7;o54;#121;k22;i23;i23;o24;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#122;o27;#150;o28;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#150;o38;#130;o28;#131;#132;P__x1;Ri0;P~R#133;A2;i40;A2;k1;o2;#151;A2;k39;#151;#108;#136;A8;k239;r75;#67;#9;#84;#8;r64;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#128;o27;#150;o28;#131;#132;P__x1;Ri0;A2;k1;#137;#152;#139;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#150;#127;o27;#141;o28;#131;#132;P__x1;Ri0;A2;k1;A2;k6;#152;#8;#142;#139;r43;A4;o88;#88;#100;A4;o78;i0;#87;r36;A4;o88;A3;k231;r73;#153;r36;A2;i40;A2;k1;r70;r36;A2;k1;r36;A2;k6;r70;#20;A9;k238;r75;r74;r73;r66;#153;r36;E__sat300;R#106;#109;E__sat299;R#111;#112;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA8;o53;#121;k22;i23;i23;o24;#125;#126;A7;o54;#121;k22;i23;i23;o24;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#122;o27;#154;o28;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#154;o38;#130;o28;#131;#132;P__x1;Ri0;P~R#133;A2;i40;A2;k1;o2;#155;A2;k39;#155;#108;#136;A8;k239;r75;#67;#9;#153;#8;r64;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#128;o27;#154;o28;#131;#132;P__x1;Ri0;A2;k1;#137;#156;#139;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#154;#127;o27;#141;o28;#131;#132;P__x1;Ri0;A2;k1;A2;k6;#156;#8;#142;#139;r32;r31;A4;o88;#90;#99;A9;k238;r75;r74;r73;r66;#89;o2;E__sat300;R#106;#109;E__sat299;R#111;#112;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA8;o53;#121;k22;i23;i23;o24;#125;#126;A7;o54;#121;k22;i23;i23;o24;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#122;o27;#157;o28;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#157;o38;#130;o28;#131;#132;P__x1;Ri0;P~R#133;A2;i40;A2;k1;o2;#158;A2;k39;#158;#108;#136;A8;k239;r75;#67;#9;#89;#8;r64;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#128;o27;#157;o28;#131;#132;P__x1;Ri0;A2;k1;#137;#159;#139;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#157;#127;o27;#141;o28;#131;#132;P__x1;Ri0;A2;k1;A2;k6;#159;#8;#142;#139;r27;A4;o88;#93;#98;A9;k247;r75;r74;r73;r66;#91;#92;E__sat300;R#106;#109;E__sat299;R#111;#112;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA8;o53;#121;k22;i23;i23;o24;#125;#126;A7;o54;#121;k22;i23;i23;o24;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#122;o27;#160;o28;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#160;o38;#130;o28;#131;#132;P__x1;Ri0;P~R#133;A2;i40;A2;k1;o2;#161;A2;k39;#161;#108;#136;A8;k239;r75;#67;#9;#91;#162;r64;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#128;o27;#160;o28;#131;#132;P__x1;Ri0;A2;k1;#137;#163;#139;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#160;#164;o27;#141;o28;#131;#132;P__x1;Ri0;A2;k1;A2;k6;#163;#162;#142;#139;r23;A4;o88;#95;#97;A4;o78;i0;#94;r16;A10;k240;r75;r74;r73;r66;#165;r16;A2;k6;#67;#29;E__sat300;RA2;k130;#4;#167;P~R#107;P~RA2;k1;o2;#167;A2;k39;o2;#168;E__sat299;RLHa;R#110;L~Ri101;A3;k131;#4;#167;r2;PHa;R#110;P~Ri101;A2;k1;o2;#168;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA8;o53;#121;k22;i23;i23;o24;#125;#126;A7;o54;#121;k22;i23;i23;o24;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#122;o27;#169;o28;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#169;o38;A3;o220;i0;#124;A1;o92;#166;o28;#131;#132;P__x1;Ri0;P~R#133;A2;i40;A2;k1;o2;#170;A2;k39;#170;#168;#136;A8;k239;r75;#67;#9;#165;#171;r64;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#128;o27;#169;o28;#131;#132;P__x1;Ri0;A2;k1;#137;#172;#139;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#169;A2;o26;i0;#171;o27;#141;o28;#131;#132;P__x1;Ri0;A2;k1;A2;k6;#172;#171;#142;#139;r15;A9;k238;r75;r74;r73;r66;#96;k234;E__sat300;R#106;#109;E__sat299;R#111;#112;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA8;o53;#121;k22;i23;i23;o24;#125;#126;A7;o54;#121;k22;i23;i23;o24;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#122;o27;#173;o28;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#173;o38;#130;o28;#131;#132;P__x1;Ri0;P~R#133;A2;i40;A2;k1;o2;#174;A2;k39;#174;#108;#136;A8;k239;r75;#67;#9;#96;#8;r64;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#128;o27;#173;o28;#131;#132;P__x1;Ri0;A2;k1;#137;#175;#139;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#173;#127;o27;#141;o28;#131;#132;P__x1;Ri0;A2;k1;A2;k6;#175;#8;#142;#139;r14;A4;o88;#69;#77;A10;k248;r75;r74;r73;r66;#68;r67;E__sat300;RA2;k130;#4;#177;P~R#107;P~RA2;k1;o2;#177;A2;k39;o2;#178;E__sat299;RLHa;R#110;L~Ri101;A3;k131;#4;#177;r2;PHa;R#110;P~Ri101;A2;k1;o2;#178;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA8;o53;#121;k22;i23;i23;o24;#125;#126;A7;o54;#121;k22;i23;i23;o24;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#122;o27;#179;o28;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#179;o38;A3;o220;i0;#124;A1;o92;#176;o28;#131;#132;P__x1;Ri0;P~R#133;A2;i40;A2;k1;o2;#180;A2;k39;#180;#178;#136;A8;k239;r75;#67;#9;#68;#19;r64;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#128;o27;#179;o28;#131;#132;P__x1;Ri0;A2;k1;#137;#181;#139;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#179;#149;o27;#141;o28;#131;#132;P__x1;Ri0;A2;k1;A2;k6;#181;#19;#142;#139;r63;r10;A4;o88;#71;#76;A8;k249;r75;r74;r73;r66;#70;E__sat300;R#106;#109;E__sat299;R#111;#112;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA8;o53;#121;k22;i23;i23;o24;#125;#126;A7;o54;#121;k22;i23;i23;o24;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#122;o27;#182;o28;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#182;o38;#130;o28;#131;#132;P__x1;Ri0;P~R#133;A2;i40;A2;k1;o2;#183;A2;k39;#183;#108;#136;A8;k239;r75;#67;#9;#70;#184;r64;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#128;o27;#182;o28;#131;#132;P__x1;Ri0;A2;k1;#137;#185;#139;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#182;A2;o26;i0;#184;o27;#141;o28;#131;#132;P__x1;Ri0;A2;k1;A2;k6;#185;#184;#142;#139;r6;A4;o88;#74;#75;A9;k247;r75;r74;r73;r66;#72;#73;E__sat300;R#106;#109;E__sat299;R#111;#112;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA8;o53;#121;k22;i23;i23;o24;#125;#126;A7;o54;#121;k22;i23;i23;o24;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#122;o27;#186;o28;A7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#186;o38;#130;o28;#131;#132;P__x1;Ri0;P~R#133;A2;i40;A2;k1;o2;#187;A2;k39;#187;#108;#136;A8;k239;r75;#67;#9;#72;#162;r64;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;#128;o27;#186;o28;#131;#132;P__x1;Ri0;A2;k1;#137;#188;#139;E__sat298;R#113;#114;E__sat297;R#115;#116;E__arith;RL__x1;Ri0;E__wit;R#117;#118;E__varmap;R#119;#120;E__ff;RA7;o20;#121;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#186;#164;o27;#141;o28;#131;#132;P__x1;Ri0;A2;k1;A2;k6;#188;#162;#142;#139;r2;r62;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;").
Qed.

Section Run.
Variable Lay : lib_layout.
Hypothesis LH : ll_heap Lay = L.
Hypothesis LF : ll_foot Lay = PML.ll_foot_csrc.
Hypothesis LC : forall n, ll_credit Lay n = PMCS.pm_credit_c L n.
Let SS := ll_stack Lay.
Hypothesis HSS : PMCS.LIB_SCR_C STRTOD_SCR <= SS.
Variables (LB : list (Z * Z)) (cr : credit) (sp ra : Z) (payload : list byte) (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet).
Let n := Z.of_nat (length payload).
Hypothesis Psp : getr R 2%bv = Z_to_bv 64 sp.
Hypothesis Ptp : getr R 4%bv = Z_to_bv 64 PML.TP.
Hypothesis Plen : 0 <= n < 2 ^ 26.
Hypothesis Prok : L5.ra_ok ra.
Hypothesis SPOK : CK.spok sp.
Hypothesis Hceil : hl_ceil L + SS <= sp.
Hypothesis Hsptop : sp <= hl_sptop L.
Hypothesis Htop : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis BOK0 : TK2.blocks_ok L LB.
Hypothesis HK0 : K [].
Hypothesis CONT : forall (fx' : FPState) (g' : PML.ls_state) (R' : bvmap 5 word) (M' : mem) (model' : Model) (cr' : credit),
  PML.fp_ok fx' -> lib_post Lay PMS.pm_statics g' LB cr sp payload R M R' M' cr' -> hi_heap HI LB cr' M' (m_vmmaps model') -> model_but_vm model model' ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' ra M' model') K.

Lemma SCRv : 1040 + PMCS.CCTOR_SCR STRTOD_SCR <= SS /\ 1040 + PMCS.GETSTR_SCR STRTOD_SCR <= SS /\ 1040 + PMS.ISS_SCR <= SS /\ 1040 + 96 + PMS.OPDEL_SCR <= SS /\
  1040 + PMCS.RN_SCR STRTOD_SCR <= SS /\ PMS.OPDEL_SCR = 8224 /\ PMS.OPNEW_SCR = 8240 /\ PMS.ISS_SCR = 9344 /\ 9264 <= PMCS.CCTOR_MAIN_SCR STRTOD_SCR.
Proof.
pose proof HSS as H.
cbv [PMCS.LIB_SCR_C PMCS.CCTOR_SCR PMCS.CCTOR_MAIN_SCR PMCS.GETSTR_SCR PMS.ISS_SCR PMS.OPDEL_SCR PMS.OPNEW_SCR PMS.CTOR_SCR PMS.ISLAND_SCR PML.HEAP_STACK] in H |- *.
lia.
Qed.

Lemma RN0 : 0 <= PMCS.RN_SCR STRTOD_SCR.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S28;A2;k65;k257;vSTRTOD_SCR;Y3;0;A2;k119;A1;i91;A1;o92;#1;vpayload;A1;k120;#2;A3;i5;i0;vn;#3;A1;k258;vLay;A3;i5;i0;vSS;#5;Y4;0;A1;o4;#7;A1;o4;Y13;0020;A2;k6;#8;#9;A2;k65;#10;vSTRTOD_SCR;Y1;0;A1;o4;#12;A1;o4;Y5;0f;A2;k39;o2;#13;A2;k11;#13;#14;A2;k1;o2;#13;A1;o4;Y4;a;A2;k11;#13;#18;A1;i21;i0;A2;o55;i0;o48;A1;o4;Y6;10;Y6;00;A1;o4;#23;A1;o4;Y7;00;A1;o4;Y10;000;A2;k6;#22;#24;cdEH;RA2;k251;k257;vSTRTOD_SCR;A2;k1;k257;#0;cdEheq_n;RcdA2;o12;i0;#3;#4;#4;Eheq_SS;RcdA2;o12;i0;#5;#6;#6;Ecstr;RA1;k129;#2;A2;k1;o2;#3;EH1;RA2;k66;#10;vSTRTOD_SCR;A2;i67;A2;i40;A2;k39;#10;vSTRTOD_SCR;A3;i5;i0;#11;vSTRTOD_SCR;A2;i40;A2;k1;vSTRTOD_SCR;#10;A3;i5;i0;#11;#10;Ez1;R#11;i0;E__sat5;RA2;k130;#13;#14;P~R#15;P~RA2;k1;o2;#14;A2;k39;o2;#16;E__sat4;RLHa;R#17;L~Ri101;A3;k131;#13;#14;r2;PHa;R#17;P~Ri101;A2;k1;o2;#16;E__sat3;RA2;k130;#13;#18;P~R#15;P~RA2;k1;o2;#18;A2;k39;o2;#19;E__sat2;RLHa;R#17;L~Ri101;A3;k131;#13;#18;r2;PHa;R#17;P~Ri101;A2;k1;o2;#19;E__arith;RL__x1;Ri0;E__wit;RA1;o15;i16;A1;i17;i16;E__varmap;RA2;o52;i0;r2;A1;i19;i0;E__ff;RA8;o53;#20;k22;i23;i23;o24;A7;o20;#20;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;A2;o26;i0;#8;A2;o26;i0;#9;o27;#21;o28;A1;o56;i23;A7;o20;#20;k22;i23;i23;o24;A4;o25;i0;A2;o26;i0;o2;o27;A3;o57;i0;A3;o57;i0;A2;o26;i0;#22;A2;o26;i0;#24;A3;o57;i0;A2;o26;i0;#25;A3;o57;i0;A2;o26;i0;#26;#21;o28;A2;k29;#20;o24;A4;k30;r1;r3;cvA2;o12;i31;o32;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;P__x1;Ri0;P~RA2;k1;#10;r1;A2;k1;o2;A2;k6;#27;A2;k6;#25;A2;k6;#26;r2;A2;r1;r6;r11;A2;k1;o2;A2;k6;#27;A2;k6;#25;A2;k6;#26;#0;A2;k1;o2;A1;k260;vSTRTOD_SCR;").
Qed.

Definition pers (reps : PML.srep) (Mk : mem) : Prop :=
  L5.u64_at RSEGS Mk (sp - 8) ra /\ L5.u64_at RSEGS Mk (sp - 16) (bv_unsigned (getr R 8%bv)) /\ L5.u64_at RSEGS Mk (sp - 24) (bv_unsigned (getr R 9%bv)) /\
  L5.u64_at RSEGS Mk (sp - 32) (bv_unsigned (getr R 18%bv)) /\ PML.str_at_w Mk (sp - 56) reps.
Lemma pers_x : forall (Kc : Z -> Prop) M1 M2 reps, TK.samem Kc M1 M2 -> TK2.cov Kc (sp - 56) 56 -> TK2.str_cov Kc (sp - 56) reps -> pers reps M1 -> pers reps M2.
Proof.
intros Kc M1 M2 reps AG HC HS P. unfold pers in *. destruct P as (P1 & P2 & P3 & P4 & P5). pose proof SPOK as [S1 S2].
split; [apply (TK.u64_samem Kc M1 M2 _ _ AG); [lia | intros i Hi; apply HC; lia | exact P1]|].
split; [apply (TK.u64_samem Kc M1 M2 _ _ AG); [lia | intros i Hi; apply HC; lia | exact P2]|].
split; [apply (TK.u64_samem Kc M1 M2 _ _ AG); [lia | intros i Hi; apply HC; lia | exact P3]|].
split; [apply (TK.u64_samem Kc M1 M2 _ _ AG); [lia | intros i Hi; apply HC; lia | exact P4]|].
apply (TK2.str_at_w_x Kc M1 M2 AG); [lia | exact HS | exact P5].
Qed.

Lemma step_out_g : forall F reps M1 M2 LBx crk modelk,
  TK.samem (L5.outside F) M1 M2 -> mem_grows M1 M2 ->
  (forall w, In w F -> (sp - SS <= fst w /\ fst w + snd w <= sp - 56 /\ 0 <= snd w)) -> (forall b, In b (PML.srep_blocks reps) -> In b LBx) ->
  pers reps M1 -> TK2.FR L LB sp SS PML.in_foot11 M M1 -> hi_heap HI LBx crk M1 (m_vmmaps modelk) ->
  pers reps M2 /\ TK2.FR L LB sp SS PML.in_foot11 M M2 /\ hi_heap HI LBx crk M2 (m_vmmaps modelk) /\ TK2.statics_cov (L5.outside F) /\ TK2.w_si L F.
Proof.
intros F reps M1 M2 LBx crk modelk AG MG HF HRB P FR1 HH.
pose proof SPOK as [S1 S2]. pose proof Htop as [T1 T2].
assert (WS : TK2.w_si L F) by (intros w Hw; left; destruct (HF w Hw) as (X1 & X2 & X3); lia).
assert (NO : forall a, ~ L5.outside F a -> sp - SS <= a < sp - 56).
{ intros a Ha. destruct (not_outside F a Ha) as (w & Hw & Hin). destruct (HF w Hw) as (X1 & X2 & X3). unfold L5.in_rng in Hin. lia. }
assert (BOx : TK2.blocks_ok L LBx) by exact (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH).
assert (CV : TK2.cov (L5.outside F) (sp - 56) 56).
{ intros i Hi w Hw Hin. destruct (HF w Hw) as (X1 & X2 & X3). unfold L5.in_rng in Hin. lia. }
split; [|split; [|split; [|split]]].
- apply (pers_x (L5.outside F) M1 M2 reps AG CV); [|exact P].
  apply (TK2.str_cov_out L LAY); [lia | eapply TK2.cov_sub; [exact CV | lia | lia] | exact WS | ].
  intros b Hb. apply BOx. apply HRB. exact Hb.
- apply (TK2.FR_grows L LAY _ _ _ _ _ M1 M2 (L5.outside F) FR1 AG MG BOK0 Hceil T1).
  intros a Ha. left. pose proof (NO a Ha). lia.
- apply (TK2.heap_pure_write L HI HIok LAY _ _ M1 M2 _ (L5.outside F) HH T1 AG MG).
  intros a Ha Hn. left. pose proof (NO a Hn). lia.
- apply (TK2.statics_cov_out L F); [intros w Hw; destruct (HF w Hw) as (X1 & X2 & X3); lia | exact T1].
- exact WS.
Qed.

Definition w_ok (W : list L5.range) : Prop :=
  forall w, In w W -> (sp - 1040 <= fst w /\ fst w + snd w <= sp - 56) \/ (0x10000 <= fst w /\ fst w + snd w <= 0xf8000 /\ forall a, L5.in_rng w a -> PML.in_foot11 a).
Lemma step_heap : forall reps M1 M2 LBk scr W,
  L5C.hpres L LBk (sp - 1040) scr W M1 M2 -> TK2.blocks_ok L LBk -> incl (PML.srep_blocks reps ++ LB) LBk -> 0 <= scr -> 1040 + scr <= SS -> w_ok W ->
  pers reps M1 -> TK2.FR L LB sp SS PML.in_foot11 M M1 ->
  pers reps M2 /\ TK2.FR L LB sp SS PML.in_foot11 M M2 /\ TK.samem (TK2.keepH L LBk W (sp - 1040) scr) M1 M2 /\ TK2.w_si L W.
Proof.
intros reps M1 M2 LBk scr W HP HB HI0 Hscr H1040 WO P FR1.
pose proof SPOK as [S1 S2]. pose proof Htop as [T1 T2].
assert (STK : L5C.stk (hl_sptop L) M1 (sp - 1040) scr) by exact (mk_stk LB sp SS PML.in_foot11 M M1 (sp - 1040) scr FR1 S2 eq_refl Hscr H1040 Hceil Hsptop Htop).
assert (WS : TK2.w_si L W) by (intros w Hw; destruct (WO w Hw) as [(X1 & X2)|(X1 & X2 & X3)]; [left; lia | right; lia]).
assert (AG : TK.samem (TK2.keepH L LBk W (sp - 1040) scr) M1 M2) by exact (TK2.hpres_samem L LAY LBk (sp - 1040) scr W M1 M2 HP HB STK Hscr).
assert (CV : TK2.cov (TK2.keepH L LBk W (sp - 1040) scr) (sp - 56) 56).
{ intros i Hi. split; [|left; lia]. intros w Hw Hin. unfold L5.in_rng in Hin. destruct (WO w Hw) as [(X1 & X2)|(X1 & X2 & X3)]; lia. }
split; [|split; [|split; [exact AG | exact WS]]].
- apply (pers_x _ M1 M2 reps AG CV); [|exact P].
  apply (TK2.str_cov_keepH L LAY); [lia | eapply TK2.cov_sub; [exact CV | lia | lia] | exact WS | ].
  intros b Hb. assert (Hb' : In b LBk) by (apply HI0; apply in_or_app; left; exact Hb). split; [exact Hb' | exact (HB b Hb')].
- apply (TK2.FR_hpres L LAY _ _ _ _ _ M1 M2 LBk (sp - 1040) scr W FR1 HP BOK0); [ | lia | lia | lia | lia | lia | lia | ].
  + intros b Hb. apply HI0. apply in_or_app. right. exact Hb.
  + intros w a Hw Hin. unfold L5.in_rng in Hin. destruct (WO w Hw) as [(X1 & X2)|(X1 & X2 & X3)]; [left; lia | right; apply X3; exact Hin].
Qed.

Ltac wok := let w := fresh "w" in let Hw := fresh "Hw" in intros w Hw; unfold PML.ll_foot_csrc in Hw; cbn [In map fst snd] in Hw;
  repeat (destruct Hw as [<-|Hw]; [cbn [fst snd]; first [left; lia | right; split; [lia|]; split; [lia|]; let a := fresh "a" in let Hi := fresh "Hi" in intros a Hi; unfold L5.in_rng in Hi; cbn [fst snd] in Hi; foot_in]|]); destruct Hw.
Ltac to_out AG lo len := apply (TK.samem_weaken _ _ _ _ AG); let a := fresh "a" in let Ho := fresh "Ho" in let Hin := fresh "Hin" in
  intros a Ho Hin; apply (Ho (lo, len) (or_introl eq_refl)); unfold L5.in_rng; cbn [fst snd]; lia.

Lemma frame_word : forall Mk a, TK2.FR L LB sp SS PML.in_foot11 M Mk -> sp - 1040 <= a -> a + 8 <= sp -> exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at RSEGS Mk a v.
Proof.
intros Mk a [_ F2] H1 H2. pose proof SCRv as (_ & _ & _ & S4 & _ & S6 & _).
apply CCTL.u64_of_defined. intros i Hi. apply F2. lia.
Qed.
Lemma frame_def : forall Mk a k, TK2.FR L LB sp SS PML.in_foot11 M Mk -> sp - 1040 <= a -> a + k <= sp -> L5.defined Mk a k.
Proof.
intros Mk a k [_ F2] H1 H2. pose proof SCRv as (_ & _ & _ & S4 & _ & S6 & _).
intros i Hi. apply F2. lia.
Qed.

Lemma samem_all : forall (Ma Mb : mem), TK.samem (fun _ => True) Ma Mb -> Mb = Ma.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S26;Y6;00;A1;o92;#0;A1;i91;#1;Y3;0;A1;i91;A1;o92;#3;A1;i93;#4;P~R#2;#5;A2;k98;#1;r1;A2;k119;#4;vpayload;A1;k120;#8;A3;i5;i0;vn;#9;A1;k258;vLay;A3;i5;i0;vSS;#11;Y1;0;A1;o4;#13;A1;o4;Y5;0f;A2;k39;o2;#14;A2;k11;#14;#15;A2;k1;o2;#14;A1;o4;#0;A2;k11;#14;#19;A1;o4;Y4;a;A2;k11;#14;#21;A1;i21;i0;A2;o55;i0;o48;A7;o54;#23;k22;i23;i23;o24;A7;o20;#23;k22;i23;i23;o24;A4;o25;i0;A2;o26;i0;o2;o27;#24;o28;A7;o20;#23;k22;i23;i23;o24;A4;o25;i0;#24;o38;A3;o220;i0;A2;o26;i0;#14;#1;o28;LMa;R#6;LMb;R#6;LH;RA3;k236;L~Ri0;i101;r2;r1;A5;k97;#2;#5;r2;r3;Lx;R#2;A6;k35;#2;A2;k111;#1;#7;Lx;R#2;A3;i5;#5;A1;r4;r1;A1;r5;r1;A3;r2;#7;EX;RA2;k145;#1;r1;A2;i40;A2;k1;o2;#7;A2;k39;#7;A1;k146;#1;Eheq_n;RcdA2;o12;i0;#9;#10;#10;Eheq_SS;RcdA2;o12;i0;#11;#12;#12;Ecstr;RA1;k129;#8;A2;k1;o2;#9;E__sat6;RA2;k130;#14;#15;P~R#16;P~RA2;k1;o2;#15;A2;k39;o2;#17;E__sat5;RLHa;R#18;L~Ri101;A3;k131;#14;#15;r2;PHa;R#18;P~Ri101;A2;k1;o2;#17;E__sat4;RA2;k130;#14;#19;P~R#16;P~RA2;k1;o2;#19;A2;k39;o2;#20;E__sat3;RLHa;R#18;L~Ri101;A3;k131;#14;#19;r2;PHa;R#18;P~Ri101;A2;k1;o2;#20;E__sat2;RA2;k130;#14;#21;P~R#16;P~RA2;k1;o2;#21;A2;k39;o2;#22;E__sat1;RLHa;R#18;L~Ri101;A3;k131;#14;#21;r2;PHa;R#18;P~Ri101;A2;k1;o2;#22;E__arith;RL__x1;Ri0;E__wit;RA1;o15;i16;A1;i17;i16;E__varmap;RA2;o52;i0;r2;A1;i19;i0;E__ff;RA8;o53;#23;k22;i23;i23;o24;#25;A1;o56;i23;#25;A2;k29;#23;o24;A4;k30;r1;r3;cvA2;o12;i31;o32;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;P__x1;Ri0;P~RA2;i40;A2;k1;o2;r1;A2;k39;r1;#20;A2;i40;A2;k1;o2;r2;A2;k39;r2;#20;A2;r1;A2;k98;#1;r12;r11;o102;r1;A2;k294;#1;r1;").
Qed.

Lemma fin : forall (fx' : FPState) R' Mk modelk crk gk,
  PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp -> getr R' 8%bv = Z_to_bv 64 (bv_unsigned (getr R 8%bv)) -> getr R' 9%bv = Z_to_bv 64 (bv_unsigned (getr R 9%bv)) ->
  getr R' 18%bv = Z_to_bv 64 (bv_unsigned (getr R 18%bv)) ->
  getr R' 10%bv = Z_to_bv 64 0 -> TK.keepsR HCS.KOH R R' ->
  TK2.FR L LB sp SS PML.in_foot11 M Mk -> model_but_vm model modelk -> hi_heap HI LB crk Mk (m_vmmaps modelk) -> PML.ls_ok gk Mk ->
  credit_le (credit_sub cr (ll_credit Lay n)) crk ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' ra Mk modelk) K.
Proof.
intros fx' R' Mk modelk crk gk Hfp H2 H8 H9 H18 H10 HK [F1 F2] BV HH LSK CR.
apply (CONT fx' gk R' Mk modelk crk Hfp); [|exact HH|exact BV].
constructor.
- exact H10.
- apply CK.rp_of_keeps; [rewrite H2, Psp; reflexivity|].
  apply csr_of; [exact HK | rewrite H8; apply Z_to_bv_bv_unsigned | rewrite H9; apply Z_to_bv_bv_unsigned | rewrite H18; apply Z_to_bv_bv_unsigned].
- exact CR.
- intros a Ha HC HF HE. rewrite LH in HC, HE. apply F1; [exact Ha | exact HC | | exact HE].
  intros X. apply HF. unfold in_foot. rewrite LF. exact X.
- intros a Ha. apply F2. exact Ha.
- exact LSK.
Qed.

Lemma t1_ur : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.

Lemma t1_short : forall (fx : FPState) Rx Mx modelk crk gk s,
  PML.fp_ok fx -> getr Rx 2%bv = Z_to_bv 64 (sp - 1040) -> getr Rx 10%bv = Z_to_bv 64 0 -> TK.keepsR HCS.KOH R Rx ->
  pers (PML.SShort s) Mx -> TK2.FR L LB sp SS PML.in_foot11 M Mx -> model_but_vm model modelk -> PML.model_ok modelk ->
  hi_heap HI LB crk Mx (m_vmmaps modelk) -> PML.ls_ok gk Mx -> credit_le (credit_sub cr (ll_credit Lay n)) crk ->
  srealizes RSEGS SCFG (@PML.cfg fx Rx HCT.BR_S Mx modelk) K.
Proof.
  intros fx Rx Mx modelk crk gk s Hfp H2 H10 KOx Hp FR BV Hmok HH LS CR.
  destruct Hmok as (Hh & Hl & _). destruct Hp as (P8 & P16 & P24 & P32 & _).
  apply (HCS.s_h_ss FPM fx Rx Mx modelk K sp ra (bv_unsigned (getr R 8%bv)) (bv_unsigned (getr R 9%bv)) (bv_unsigned (getr R 18%bv))
           Hh Hl Hfp H2 SPOK H10 Prok (t1_ur _) (t1_ur _) (t1_ur _) P8 P16 P24 P32).
  intros fx' R' M' Hfp' H2' H8' H9' H18' H10' KO' AG' _. pose proof (samem_all _ _ AG') as ->.
  exact (fin fx' R' Mx modelk crk gk Hfp' H2' H8' H9' H18' H10' (KT _ _ _ KOx KO') FR BV HH LS CR).
Qed.

Lemma t1_long : forall (fx : FPState) Rx Mx modelk crk gk cap p s,
  PML.fp_ok fx -> getr Rx 2%bv = Z_to_bv 64 (sp - 1040) -> getr Rx 10%bv = Z_to_bv 64 1 -> TK.keepsR HCS.KOH R Rx ->
  pers (PML.SLong cap p s) Mx -> 0 <= cap <= n + 10 ->
  TK2.FR L LB sp SS PML.in_foot11 M Mx -> model_but_vm model modelk -> PML.model_ok modelk ->
  hi_heap HI ((p, cap) :: LB) crk Mx (m_vmmaps modelk) -> PML.ls_ok gk Mx -> credit_le (credit_sub cr (ll_credit Lay n)) crk ->
  srealizes RSEGS SCFG (@PML.cfg fx Rx HCT.BR_S Mx modelk) K.
Proof.
  intros fx Rx Mx modelk crk gk cap p s Hfp H2 H10 KOx Hp Hcap FR BV Hmok HH LS CR.
  pose proof Hmok as (Hh & Hl & _). pose proof SPOK as (SPr & Hal).
  pose proof SCRv as (_ & _ & _ & S4 & _ & S6 & _).
  destruct Hp as (P8 & P16 & P24 & P32 & PS). cbn [PML.str_at_w] in PS. destruct PS as ((_ & W0 & _ & W16 & _) & _).
  replace (sp - 56 + 16) with (sp - 40) in W16 by lia.
  destruct (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH (p, cap) (or_introl eq_refl)) as (B0 & _ & _ & _ & B4). cbn [fst snd] in B0, B4.
  assert (Hpr : 0 <= p < 2 ^ 64) by lia.
  apply (HCS.s_h_sl FPM fx Rx Mx modelk K sp (cap + 1) p Hh Hl Hfp H2 SPOK H10 ltac:(lia) Hpr W0 W16).
  intros fx1 R1 M1 Hfp1 H2a H1a H10a KC1 AG1 _. pose proof (samem_all _ _ AG1) as ->.
  assert (KO1 : TK.keepsR HCS.KOH R R1) by exact (KT _ _ _ KOx (KCO _ _ KC1)).
  assert (TP1 : getr R1 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO1 4%bv KO_4); exact Ptp).
  assert (STK : L5C.stk (hl_sptop L) Mx (sp - 1040) PMS.OPDEL_SCR)
    by (apply (mk_stk LB sp SS PML.in_foot11 M Mx (sp - 1040) PMS.OPDEL_SCR FR Hal eq_refl); lia).
  assert (RA : L5.ra_ok HCT.R_OPDEL_S) by (split; [unfold HCT.R_OPDEL_S; lia | reflexivity]).
  apply (OPDELS ((p, cap) :: LB) crk p cap (sp - 1040) HCT.R_OPDEL_S fx1 R1 Mx modelk K HH Hmok HK0 Hfp1).
  { split; [exact (mk_entry R1 Mx (sp - 1040) HCT.R_OPDEL_S PMS.OPDEL_SCR H1a RA H2a TP1 STK)|]. split; [exact H10a | left; reflexivity]. }
  intros fx2 R2 M2 model2 LB2 cr2 LBk2 W2 Hfp2 (-> & -> & -> & ->) RP2 HP2 BV2 HH2.
  assert (LR : lb_remove p ((p, cap) :: LB) = LB) by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
  rewrite LR in HP2, HH2.
  pose proof (TK2.hpres_samem L LAY LB (sp - 1040) PMS.OPDEL_SCR [] Mx M2 HP2 BOK0 STK ltac:(lia)) as AG2.
  assert (KH : forall a, sp - 1040 <= a -> TK2.keepH L LB [] (sp - 1040) PMS.OPDEL_SCR a) by (intros a Ha; split; [intros w [] | left; exact Ha]).
  assert (FR2 : TK2.FR L LB sp SS PML.in_foot11 M M2).
  { apply (TK2.FR_hpres L LAY LB sp SS PML.in_foot11 M Mx M2 LB (sp - 1040) PMS.OPDEL_SCR [] FR HP2 BOK0 (incl_refl _)); try lia. intros w a []. }
  assert (LS2 : PML.ls_ok gk M2).
  { apply (TK2.ls_ok_x _ Mx M2 AG2); [apply TK2.statics_cov_keepH; intros a _ w [] | exact LS]. }
  assert (P8' : L5.u64_at RSEGS M2 (sp - 8) ra) by (apply (TK.u64_samem _ Mx M2 _ _ AG2); [lia | intros i Hi; apply KH; lia | exact P8]).
  assert (P16' : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R 8%bv))) by (apply (TK.u64_samem _ Mx M2 _ _ AG2); [lia | intros i Hi; apply KH; lia | exact P16]).
  assert (P24' : L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R 9%bv))) by (apply (TK.u64_samem _ Mx M2 _ _ AG2); [lia | intros i Hi; apply KH; lia | exact P24]).
  assert (P32' : L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R 18%bv))) by (apply (TK.u64_samem _ Mx M2 _ _ AG2); [lia | intros i Hi; apply KH; lia | exact P32]).
  pose proof (mok_of _ _ BV2 Hmok) as (Hh2 & Hl2 & _).
  assert (H2b : getr R2 2%bv = Z_to_bv 64 (sp - 1040)) by (rewrite (RP2 2%bv CS2); exact H2a).
  apply (HCS.s_h_ropdel_s FPM fx2 R2 M2 model2 K sp ra (bv_unsigned (getr R 8%bv)) (bv_unsigned (getr R 9%bv)) (bv_unsigned (getr R 18%bv))
           Hh2 Hl2 Hfp2 H2b SPOK Prok (t1_ur _) (t1_ur _) (t1_ur _) P8' P16' P24' P32').
  intros fx3 R3 M3 Hfp3 H2c H8c H9c H18c H10c KO3 AG3 _. pose proof (samem_all _ _ AG3) as ->.
  exact (fin fx3 R3 M2 model2 crk gk Hfp3 H2c H8c H9c H18c H10c (KT _ _ _ (KT _ _ _ KO1 (KSP _ _ RP2)) KO3) FR2 (L5C.model_but_vm_trans _ _ _ BV BV2) HH2 LS2 CR).
Qed.

Lemma t1_iosb : forall (fx : FPState) Rx Mx modelk crk gk reps rd,
  PML.fp_ok fx -> getr Rx 2%bv = Z_to_bv 64 (sp - 1040) -> getr Rx 1%bv = Z_to_bv 64 HCT.R_IOSBDTOR -> getr Rx 10%bv = Z_to_bv 64 (sp - 208) ->
  TK.keepsR HCS.KOH R Rx -> pers reps Mx -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) ->
  TK2.FR L LB sp SS PML.in_foot11 M Mx -> model_but_vm model modelk -> PML.model_ok modelk -> hi_heap HI (PML.srep_blocks reps ++ LB) crk Mx (m_vmmaps modelk) ->
  PML.ls_ok gk Mx -> credit_le (credit_sub cr (ll_credit Lay n)) crk -> PML.iosb_at Mx (sp - 208) rd (sp - 312) ->
  srealizes RSEGS SCFG (@PML.cfg fx Rx PML.PC_IOSB_DTOR Mx modelk) K.
Proof.
  intros fx Rx Mx modelk crk gk reps rd Hfp H2 H1 H10 KOx Hp Hrb FR BV Hmok HH LS CR IOSB.
  pose proof Hmok as (Hh & Hl & _). pose proof SPOK as (SPr & Hal).
  pose proof SCRv as (_ & _ & _ & S4 & _ & S6 & _).
  assert (TP : getr Rx 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KOx 4%bv KO_4); exact Ptp).
  assert (STK : L5C.stk (hl_sptop L) Mx (sp - 1040) TPS.IOSB_SCR)
    by (apply (mk_stk LB sp SS PML.in_foot11 M Mx (sp - 1040) TPS.IOSB_SCR FR Hal eq_refl); unfold TPS.IOSB_SCR; lia).
  assert (RA : L5.ra_ok HCT.R_IOSBDTOR) by (split; [unfold HCT.R_IOSBDTOR; lia | reflexivity]).
  apply (IOSBDTOR (sp - 208) rd (sp - 312) (sp - 1040) HCT.R_IOSBDTOR fx Rx Mx modelk K Hh Hl HK0 Hfp).
  { split; [exact (mk_entry Rx Mx (sp - 1040) HCT.R_IOSBDTOR TPS.IOSB_SCR H1 RA H2 TP STK)|]. split; [exact H10|]. split; [exact IOSB|]. oos Hal. }
  intros fx1 R1 M1 Hfp1 _ RP1 FB1 MG1. unfold TPS.IOSB_SCR in FB1. pose proof (TK2.frame_but_samem _ _ _ FB1) as AG1.
  assert (FW : forall w, In w ((sp - 1040 - 64, 64) :: [(sp - 208, 8)]) -> sp - SS <= fst w /\ fst w + snd w <= sp - 56 /\ 0 <= snd w)
    by (intros w Hw; destruct Hw as [<-|[<-|[]]]; cbn [fst snd]; lia).
  assert (IB : forall b, In b (PML.srep_blocks reps) -> In b (PML.srep_blocks reps ++ LB)) by (intros b Hb; apply in_or_app; left; exact Hb).
  destruct (step_out_g _ reps Mx M1 _ crk modelk AG1 MG1 FW IB Hp FR HH) as (P1 & FR1 & HH1 & SC1 & _).
  pose proof (TK2.ls_ok_x _ Mx M1 AG1 SC1 gk LS) as LS1.
  assert (H2a : getr R1 2%bv = Z_to_bv 64 (sp - 1040)) by (rewrite (RP1 2%bv CS2); exact H2).
  assert (KO1 : TK.keepsR HCS.KOH R R1) by exact (KT _ _ _ KOx (KSP _ _ RP1)).
  assert (RAB : 0 <= ra < 2 ^ 64) by (destruct Prok; lia).
  pose proof P1 as (P8 & P16 & P24 & P32 & PS).
  destruct reps as [s | cap p s]; cbn [PML.str_at_w] in PS.
  - destruct (frame_word M1 (sp - 56) FR1 ltac:(lia) ltac:(lia)) as (w & Hw & W0).
    destruct (frame_word M1 (sp - 40) FR1 ltac:(lia) ltac:(lia)) as (q & Hq & W16).
    pose proof (sso_bit M1 (sp - 56) s w ltac:(lia) ltac:(lia) PS W0) as BIT.
    apply (HCS.s_h_riosbdtor FPM fx1 R1 M1 modelk K sp w q ra (bv_unsigned (getr R 8%bv)) (bv_unsigned (getr R 9%bv)) (bv_unsigned (getr R 18%bv))
             Hh Hl Hfp1 H2a SPOK Hw Hq RAB (t1_ur _) (t1_ur _) (t1_ur _) W0 W16 P8 P16 P24 P32).
    intros fx2 R2 M2 Hfp2 H2b H10b KC2 AG2 _. pose proof (samem_all _ _ AG2) as ->. rewrite BIT in H10b.
    exact (t1_short fx2 R2 M1 modelk crk gk s Hfp2 H2b H10b (KT _ _ _ KO1 (KCO _ _ KC2)) P1 FR1 BV Hmok HH1 LS1 CR).
  - destruct PS as ((Hbit & W0 & _ & W16 & _) & _). replace (sp - 56 + 16) with (sp - 40) in W16 by lia.
    pose proof (Hrb (p, cap) (or_introl eq_refl)) as Hcap. cbn [snd] in Hcap.
    destruct (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH1 (p, cap) (or_introl eq_refl)) as (B0 & _ & _ & _ & B4). cbn [fst snd] in B0, B4.
    apply (HCS.s_h_riosbdtor FPM fx1 R1 M1 modelk K sp (cap + 1) p ra (bv_unsigned (getr R 8%bv)) (bv_unsigned (getr R 9%bv)) (bv_unsigned (getr R 18%bv))
             Hh Hl Hfp1 H2a SPOK ltac:(lia) ltac:(lia) RAB (t1_ur _) (t1_ur _) (t1_ur _) W0 W16 P8 P16 P24 P32).
    intros fx2 R2 M2 Hfp2 H2b H10b KC2 AG2 _. pose proof (samem_all _ _ AG2) as ->. rewrite (land1_odd_low (cap + 1) Hbit) in H10b.
    exact (t1_long fx2 R2 M1 modelk crk gk cap p s Hfp2 H2b H10b (KT _ _ _ KO1 (KCO _ _ KC2)) P1 Hcap FR1 BV Hmok HH1 LS1 CR).
Qed.
Lemma tail1 : forall (fxk : FPState) Rk Mk modelk crk gk reps rd,
  PML.fp_ok fxk -> getr Rk 2%bv = Z_to_bv 64 (sp - 1040) -> getr Rk 1%bv = Z_to_bv 64 HCT.R_LOCDTOR -> getr Rk 10%bv = Z_to_bv 64 (sp - 304) -> TK.keepsR HCS.KOH R Rk ->
  pers reps Mk -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) ->
  TK2.FR L LB sp SS PML.in_foot11 M Mk -> model_but_vm model modelk -> PML.model_ok modelk -> hi_heap HI (PML.srep_blocks reps ++ LB) crk Mk (m_vmmaps modelk) ->
  PML.ls_ok gk Mk -> credit_le (credit_sub cr (ll_credit Lay n)) crk ->
  L5.u64_at RSEGS Mk (sp - 304) PML.CLASSIC_IMP -> PML.iosb_at Mk (sp - 208) rd (sp - 312) ->
  srealizes RSEGS SCFG (@PML.cfg fxk Rk PML.PC_LOCALE_DTOR Mk modelk) K.
Proof.
  intros fxk Rk Mk modelk crk gk reps rd Hfp H2 H1 H10 KOk Hp Hrb FR BV Hmok HH LS CR Hloc IOSB.
  pose proof Hmok as (Hh & Hl & _). pose proof SPOK as (SPr & Hal).
  pose proof SCRv as (_ & _ & _ & S4 & _ & S6 & _).
  assert (TPk : getr Rk 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KOk 4%bv KO_4); exact Ptp).
  assert (STK : L5C.stk (hl_sptop L) Mk (sp - 1040) 0)
    by (apply (mk_stk LB sp SS PML.in_foot11 M Mk (sp - 1040) 0 FR Hal eq_refl); lia).
  assert (RA1 : L5.ra_ok HCT.R_LOCDTOR) by (split; [unfold HCT.R_LOCDTOR; lia | reflexivity]).
  assert (RA2 : L5.ra_ok HCT.R_ISTRDTOR) by (split; [unfold HCT.R_ISTRDTOR; lia | reflexivity]).
  apply (LOCDTOR (sp - 304) (sp - 1040) HCT.R_LOCDTOR fxk Rk Mk modelk K Hh Hl HK0 Hfp).
  { split; [exact (mk_entry Rk Mk (sp - 1040) HCT.R_LOCDTOR 0 H1 RA1 H2 TPk STK)|]. split; [exact H10|]. split; [lia | exact Hloc]. }
  intros fx1 R1 M1 Hfp1 _ RP1 FB1 _. rewrite (frame_but_nil0 Mk M1 _ FB1). clear FB1 M1.
  apply (HCS.s_h_rlocdtor FPM fx1 R1 Mk modelk K sp Hh Hl Hfp1 ltac:(rewrite (RP1 2%bv CS2); exact H2) SPOK).
  intros fx2 R2 M2 Hfp2 H2b H1b H10b KC2 AG2 _. pose proof (samem_all _ _ AG2) as ->.
  assert (KO2 : TK.keepsR HCS.KOH R R2) by exact (KT _ _ _ (KT _ _ _ KOk (KSP _ _ RP1)) (KCO _ _ KC2)).
  assert (TP2 : getr R2 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO2 4%bv KO_4); exact Ptp).
  apply (ISTRDTOR (sp - 1040) HCT.R_ISTRDTOR fx2 R2 Mk modelk K Hh Hl HK0 Hfp2).
  { exact (mk_entry R2 Mk (sp - 1040) HCT.R_ISTRDTOR 0 H1b RA2 H2b TP2 STK). }
  intros fx3 R3 M3 Hfp3 _ RP3 FB3 _. rewrite (frame_but_nil0 Mk M3 _ FB3). clear FB3 M3.
  apply (HCS.s_h_ristrdtor FPM fx3 R3 Mk modelk K sp Hh Hl Hfp3 ltac:(rewrite (RP3 2%bv CS2); exact H2b) SPOK).
  intros fx4 R4 M4 Hfp4 H2d H1d H10d KC4 AG4 _. pose proof (samem_all _ _ AG4) as ->.
  exact (t1_iosb fx4 R4 Mk modelk crk gk reps rd Hfp4 H2d H1d H10d (KT _ _ _ (KT _ _ _ KO2 (KSP _ _ RP3)) (KCO _ _ KC4)) Hp Hrb FR BV Hmok HH LS CR IOSB).
Qed.

Definition t0_rel (rep : PML.srep) (w p : Z) : Prop :=
  match rep with PML.SShort _ => Z.land (w mod 256) 1 = 0 | PML.SLong _ q _ => Z.land (w mod 256) 1 = 1 /\ q = p end.
Lemma t0_lbr : forall (A k : Z) (l : list (Z * Z)), lb_remove A ((A, k) :: l) = l.
Proof. intros A k l. cbn [lb_remove fst]. rewrite Z.eqb_refl. reflexivity. Qed.
Ltac t0_cv := unfold TK2.cov; let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
  first [ let w := fresh "w" in let Hw := fresh "Hw" in let Hin := fresh "Hin" in intros w Hw Hin; cbn [In] in Hw;
          repeat (destruct Hw as [<-|Hw]; [unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia|]); destruct Hw
        | unfold TK2.keepH; split; [let w := fresh "w" in let Hw := fresh "Hw" in let Hin := fresh "Hin" in intros w Hw Hin; cbn [In] in Hw;
          repeat (destruct Hw as [<-|Hw]; [unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia|]); destruct Hw | left; lia] ].
Ltac t0_frg := let w := fresh "w" in let Hw := fresh "Hw" in intros w Hw; cbn [In] in Hw;
  repeat (destruct Hw as [<-|Hw]; [cbn [fst snd]; lia|]); destruct Hw.

Lemma t0_wp : forall (Mk : mem) rep, TK2.FR L LB sp SS PML.in_foot11 M Mk -> PML.str_at Mk (sp - 248) rep -> TK2.blocks_ok L (PML.srep_blocks rep) ->
  (forall b, In b (PML.srep_blocks rep) -> 0 <= snd b <= n + 52) ->
  exists w p, 0 <= w < 2 ^ 64 /\ 0 <= p < 2 ^ 64 /\ L5.u64_at RSEGS Mk (sp - 248) w /\ L5.u64_at RSEGS Mk (sp - 232) p /\ t0_rel rep w p.
Proof.
  intros Mk rep FR HS HB HN. pose proof SPOK as [SP1 SP2]. pose proof SCRv as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  destruct rep as [s | cap q s]; cbn [PML.str_at t0_rel] in HS |- *.
  - destruct (frame_word Mk (sp - 248) FR ltac:(lia) ltac:(lia)) as (w & Hw & Uw).
    destruct (frame_word Mk (sp - 232) FR ltac:(lia) ltac:(lia)) as (p & Hp & Up).
    exists w, p. split; [exact Hw|]. split; [exact Hp|]. split; [exact Uw|]. split; [exact Up|].
    exact (sso_bit Mk (sp - 248) s w ltac:(lia) ltac:(lia) HS Uw).
  - destruct HS as ((Hb & U0 & U8 & U16 & Hbs & Hz) & Hm & Hl).
    pose proof (HN (q, cap) (or_introl eq_refl)) as Hc. pose proof (HB (q, cap) (or_introl eq_refl)) as (B0 & B1 & B2 & B3 & B4).
    cbn [fst snd] in Hc, B0, B1, B2, B3, B4.
    exists (cap + 1), q. split; [lia|]. split; [lia|]. split; [exact U0|].
    split; [replace (sp - 232) with (sp - 248 + 16) by lia; exact U16|]. split; [exact (land1_odd_low _ Hb) | reflexivity].
Qed.

Lemma t0_k : forall Rb (Mb : mem) modelb crk gk reps rd,
  TK.keepsR HCS.KOH R Rb -> pers reps Mb -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) ->
  TK2.FR L LB sp SS PML.in_foot11 M Mb -> model_but_vm model modelb -> PML.model_ok modelb ->
  hi_heap HI (PML.srep_blocks reps ++ LB) crk Mb (m_vmmaps modelb) -> PML.ls_ok gk Mb -> credit_le (credit_sub cr (ll_credit Lay n)) crk ->
  L5.u64_at RSEGS Mb (sp - 304) PML.CLASSIC_IMP -> PML.iosb_at Mb (sp - 208) rd (sp - 312) ->
  forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_LOCDTOR -> getr R' 10%bv = Z_to_bv 64 (sp - 304) ->
    TK.keepsR CK.CSR Rb R' -> L5.u64_at RSEGS M' (sp - 312) HCT.VT_SBUF1 -> TK.samem (fun a => ~ (sp - 312 <= a < sp - 304)) Mb M' -> mem_grows Mb M' ->
    srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_LOCALE_DTOR M' modelb) K.
Proof.
  intros Rb Mb modelb crk gk reps rd KR P B FR BV MO HH LS CR U304 IO fx' R' M' Hfp X2 X1 X10 KC V AG MG.
  pose proof SPOK as [SP1 SP2]. pose proof SCRv as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  assert (AG' : TK.samem (L5.outside [(sp - 312, 8)]) Mb M') by (to_out AG (sp - 312) 8).
  assert (FRG : forall w0, In w0 [(sp - 312, 8)] -> sp - SS <= fst w0 /\ fst w0 + snd w0 <= sp - 56 /\ 0 <= snd w0) by t0_frg.
  assert (INB : forall b, In b (PML.srep_blocks reps) -> In b (PML.srep_blocks reps ++ LB)) by (intros b Hb; apply in_or_app; left; exact Hb).
  destruct (step_out_g _ reps Mb M' _ crk modelb AG' MG FRG INB P FR HH) as (P' & FR' & HH' & SC' & WS').
  apply (tail1 fx' R' M' modelb crk gk reps rd Hfp X2 X1 X10 (KT _ _ _ KR (KCO _ _ KC)) P' B FR' BV MO HH' (TK2.ls_ok_x _ _ _ AG' SC' gk LS) CR).
  - apply (TK2.u64_x _ _ _ AG'); [lia | t0_cv | exact U304].
  - apply (TK2.iosb_at_xg _ _ _ AG'); [lia | t0_cv | exact MG | exact IO].
Qed.

Lemma t0_sb : forall (fxk : FPState) Rk (Mk : mem) modelk crk gk reps rep rd w p,
  PML.fp_ok fxk -> getr Rk 2%bv = Z_to_bv 64 (sp - 1040) -> getr Rk 11%bv = Z_to_bv 64 (Z.land (w mod 256) 1) -> TK.keepsR HCS.KOH R Rk ->
  pers reps Mk -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) ->
  TK2.FR L LB sp SS PML.in_foot11 M Mk -> model_but_vm model modelk -> PML.model_ok modelk ->
  hi_heap HI (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) crk Mk (m_vmmaps modelk) ->
  PML.ls_ok gk Mk -> credit_le (credit_sub cr (ll_credit Lay n)) crk ->
  0 <= w < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> L5.u64_at RSEGS Mk (sp - 248) w -> L5.u64_at RSEGS Mk (sp - 232) p -> t0_rel rep w p ->
  L5.u64_at RSEGS Mk (sp - 304) PML.CLASSIC_IMP -> PML.iosb_at Mk (sp - 208) rd (sp - 312) ->
  srealizes RSEGS SCFG (@PML.cfg fxk Rk HCT.BR_SB Mk modelk) K.
Proof.
  intros fxk Rk Mk modelk crk gk reps rep rd w p Hfp X2 X11 KR P B FR BV MO HH LS CR Hw Hp U248 U232 REL U304 IO.
  pose proof SPOK as [SP1 SP2]. pose proof SCRv as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  pose proof MO as (Hh & Hl & Hm).
  destruct rep as [s | cap q s]; cbn [t0_rel PML.srep_blocks app] in REL, HH.
  - apply (HCS.s_h_sbs FPM fxk Rk Mk modelk K sp Hh Hl Hfp X2 SPOK).
    + rewrite X11, REL. reflexivity.
    + exact (proj1 LS).
    + exact (frame_def Mk (sp - 312) 8 FR ltac:(lia) ltac:(lia)).
    + exact (t0_k Rk Mk modelk crk gk reps rd KR P B FR BV MO HH LS CR U304 IO).
  - destruct REL as [Hb Hq]. subst q.
    apply (HCS.s_h_sbl FPM fxk Rk Mk modelk K sp w p Hh Hl Hfp X2 SPOK); [rewrite X11, Hb; reflexivity | exact Hw | exact Hp | exact U248 | exact U232 |].
    intros fx1 R1 M1 Hfp1 Y2 Y1 Y10 KC1 AG1 MG1. apply samem_all in AG1. subst M1.
    apply (OPDELS ((p, cap) :: PML.srep_blocks reps ++ LB) crk p cap (sp - 1040) HCT.R_OPDEL_SB fx1 R1 Mk modelk K HH MO HK0 Hfp1).
    + cbv beta. split; [|split; [exact Y10 | left; reflexivity]].
      apply mk_entry; [exact Y1 | apply ra_ok_lit; unfold HCT.R_OPDEL_SB; [lia | reflexivity] | exact Y2 | rewrite (KC1 4%bv KC_4), (KR 4%bv KO_4); exact Ptp |].
      exact (mk_stk LB sp SS PML.in_foot11 M Mk (sp - 1040) PMS.OPDEL_SCR FR SP2 eq_refl ltac:(lia) ltac:(lia) Hceil Hsptop Htop).
    + intros fx2 R2 M2 model2 LB2 cr2 LBk2 W2 Hfp2 (-> & -> & -> & ->) RP2 HP2 BV2 HH2.
      rewrite t0_lbr in HP2, HH2.
      assert (WK : w_ok []) by (intros w0 []).
      destruct (step_heap reps Mk M2 _ PMS.OPDEL_SCR _ HP2 (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH2) (incl_refl _) ltac:(lia) ltac:(lia) WK P FR) as (P2 & FR2 & AG2 & WS2).
      pose proof (mok_of _ _ BV2 MO) as MO2. pose proof MO2 as (Hh2 & Hl2 & Hm2).
      assert (LS2 : PML.ls_ok gk M2) by (apply (TK2.ls_ok_x _ _ _ AG2); [st_cov | exact LS]).
      assert (U304b : L5.u64_at RSEGS M2 (sp - 304) PML.CLASSIC_IMP) by (apply (TK2.u64_x _ _ _ AG2); [lia | t0_cv | exact U304]).
      assert (IOb : PML.iosb_at M2 (sp - 208) rd (sp - 312)) by (apply (TK2.iosb_at_x _ _ _ AG2); [lia | t0_cv | exact IO]).
      apply (HCS.s_h_ropdel_sb FPM fx2 R2 M2 model2 K sp Hh2 Hl2 Hfp2); [rewrite (RP2 _ CS2); exact Y2 | exact SPOK | exact (proj1 LS2)
        | exact (frame_def M2 (sp - 312) 8 FR2 ltac:(lia) ltac:(lia)) |].
      exact (t0_k R2 M2 model2 crk gk reps rd (KT _ _ _ (KT _ _ _ KR (KCO _ _ KC1)) (KSP _ _ RP2)) P2 B FR2 (L5C.model_but_vm_trans _ _ _ BV BV2) MO2 HH2 LS2 CR U304b IOb).
Qed.

Lemma t0_sd : forall (fxk : FPState) Rk (Mk : mem) modelk crk gk reps rep ch rd w p,
  PML.fp_ok fxk -> getr Rk 2%bv = Z_to_bv 64 (sp - 1040) -> getr Rk 1%bv = Z_to_bv 64 HCT.R_SDTOR -> getr Rk 10%bv = Z_to_bv 64 (sp - 1000) -> TK.keepsR HCS.KOH R Rk ->
  pers reps Mk -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) ->
  TK2.FR L LB sp SS PML.in_foot11 M Mk -> model_but_vm model modelk -> PML.model_ok modelk ->
  hi_heap HI ((ch, 16384) :: PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) crk Mk (m_vmmaps modelk) ->
  PML.ls_ok gk Mk -> credit_le (credit_sub cr (ll_credit Lay n)) crk -> PML.source_at Mk (sp - 1000) ch ->
  0 <= w < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> L5.u64_at RSEGS Mk (sp - 248) w -> L5.u64_at RSEGS Mk (sp - 232) p -> t0_rel rep w p ->
  L5.u64_at RSEGS Mk (sp - 304) PML.CLASSIC_IMP -> PML.iosb_at Mk (sp - 208) rd (sp - 312) ->
  srealizes RSEGS SCFG (@PML.cfg fxk Rk PML.PC_SOURCE_DTOR Mk modelk) K.
Proof.
  intros fxk Rk Mk modelk crk gk reps rep ch rd w p Hfp X2 X1 X10 KR P B FR BV MO HH LS CR SRC Hw Hp U248 U232 REL U304 IO.
  pose proof SPOK as [SP1 SP2]. pose proof SCRv as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  apply (SDTOR _ crk (sp - 1000) ch (sp - 1040) HCT.R_SDTOR fxk Rk Mk modelk K HH MO HK0 Hfp).
  - cbv beta. split.
    + apply mk_entry; [exact X1 | apply ra_ok_lit; unfold HCT.R_SDTOR; [lia | reflexivity] | exact X2 | rewrite (KR 4%bv KO_4); exact Ptp |].
      exact (mk_stk LB sp SS PML.in_foot11 M Mk (sp - 1040) (96 + PMS.OPDEL_SCR) FR SP2 eq_refl ltac:(lia) ltac:(lia) Hceil Hsptop Htop).
    + split; [exact X10|]. split; [exact SRC|]. split; [left; reflexivity|]. split; [exact (proj1 LS)|]. oos SP2.
  - intros fx1 R1 M1 model1 LB1 cr1 LBk1 W1 Hfp1 (-> & -> & -> & ->) RP1 HP1 BV1 HH1.
    rewrite t0_lbr in HP1, HH1.
    assert (WK : w_ok [(sp - 1000, 592)]) by (intros w0 Hw0; destruct Hw0 as [<-|[]]; left; cbn [fst snd]; lia).
    assert (INC : incl (PML.srep_blocks reps ++ LB) (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    destruct (step_heap reps Mk M1 _ (96 + PMS.OPDEL_SCR) _ HP1 (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH1) INC ltac:(lia) ltac:(lia) WK P FR) as (P1 & FR1 & AG1 & WS1).
    pose proof (mok_of _ _ BV1 MO) as MO1. pose proof MO1 as (Hh1 & Hl1 & Hm1).
    assert (LS1 : PML.ls_ok gk M1) by (apply (TK2.ls_ok_x _ _ _ AG1); [st_cov | exact LS]).
    assert (U248a : L5.u64_at RSEGS M1 (sp - 248) w) by (apply (TK2.u64_x _ _ _ AG1); [lia | t0_cv | exact U248]).
    assert (U232a : L5.u64_at RSEGS M1 (sp - 232) p) by (apply (TK2.u64_x _ _ _ AG1); [lia | t0_cv | exact U232]).
    assert (U304a : L5.u64_at RSEGS M1 (sp - 304) PML.CLASSIC_IMP) by (apply (TK2.u64_x _ _ _ AG1); [lia | t0_cv | exact U304]).
    assert (IOa : PML.iosb_at M1 (sp - 208) rd (sp - 312)) by (apply (TK2.iosb_at_x _ _ _ AG1); [lia | t0_cv | exact IO]).
    apply (HCS.s_h_rsdtor FPM fx1 R1 M1 model1 K sp w p Hh1 Hl1 Hfp1); [rewrite (RP1 _ CS2); exact X2 | exact SPOK | exact Hw | exact Hp | exact (proj1 LS1)
      | exact (frame_def M1 (sp - 328) 8 FR1 ltac:(lia) ltac:(lia)) | exact (frame_def M1 (sp - 312) 8 FR1 ltac:(lia) ltac:(lia))
      | exact (frame_def M1 (sp - 208) 8 FR1 ltac:(lia) ltac:(lia)) | exact U248a | exact U232a |].
    intros fx2 R2 M2 Hfp2 Y2 Y11 Y8 Y9 KR2 V1 V2 V3 AG2 MG2.
    assert (AG2' : TK.samem (L5.outside [(sp - 328, 8); (sp - 312, 8); (sp - 208, 8)]) M1 M2).
    { apply (TK.samem_weaken _ _ _ _ AG2). intros a Ho. split; [|split]; intros Hin;
        [apply (Ho (sp - 328, 8) (or_introl eq_refl)) | apply (Ho (sp - 312, 8) (or_intror (or_introl eq_refl)))
        | apply (Ho (sp - 208, 8) (or_intror (or_intror (or_introl eq_refl))))]; unfold L5.in_rng; cbn [fst snd]; lia. }
    assert (FRG : forall w0, In w0 [(sp - 328, 8); (sp - 312, 8); (sp - 208, 8)] -> sp - SS <= fst w0 /\ fst w0 + snd w0 <= sp - 56 /\ 0 <= snd w0) by t0_frg.
    assert (INB : forall b, In b (PML.srep_blocks reps) -> In b (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB)) by (intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb).
    destruct (step_out_g _ reps M1 M2 _ crk model1 AG2' MG2 FRG INB P1 FR1 HH1) as (P2 & FR2 & HH2 & SC2 & WS2).
    assert (U248b : L5.u64_at RSEGS M2 (sp - 248) w) by (apply (TK2.u64_x _ _ _ AG2'); [lia | t0_cv | exact U248a]).
    assert (U232b : L5.u64_at RSEGS M2 (sp - 232) p) by (apply (TK2.u64_x _ _ _ AG2'); [lia | t0_cv | exact U232a]).
    assert (U304b : L5.u64_at RSEGS M2 (sp - 304) PML.CLASSIC_IMP) by (apply (TK2.u64_x _ _ _ AG2'); [lia | t0_cv | exact U304a]).
    assert (IOb : PML.iosb_at M2 (sp - 208) rd (sp - 312)) by (apply (TK2.iosb_at_xg _ _ _ AG2'); [lia | t0_cv | exact MG2 | exact IOa]).
    exact (t0_sb fx2 R2 M2 model1 crk gk reps rep rd w p Hfp2 Y2 Y11 (KT _ _ _ (KT _ _ _ KR (KSP _ _ RP1)) KR2) P2 B FR2 (L5C.model_but_vm_trans _ _ _ BV BV1) MO1 HH2
             (TK2.ls_ok_x _ _ _ AG2' SC2 gk LS1) CR Hw Hp U248b U232b REL U304b IOb).
Qed.
Lemma tail0 : forall (fxk : FPState) Rk Mk modelk crk gk reps rep ps ch gp rd,
  PML.fp_ok fxk -> getr Rk 2%bv = Z_to_bv 64 (sp - 1040) -> getr Rk 1%bv = Z_to_bv 64 HCT.R_PDTOR -> getr Rk 10%bv = Z_to_bv 64 (sp - 688) -> TK.keepsR HCS.KOH R Rk ->
  pers reps Mk -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) -> (forall b, In b (PML.srep_blocks rep) -> 0 <= snd b <= n + 52) ->
  TK2.FR L LB sp SS PML.in_foot11 M Mk -> model_but_vm model modelk -> PML.model_ok modelk ->
  hi_heap HI (PML.ps_blocks ps ++ (ch, 16384) :: PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) crk Mk (m_vmmaps modelk) ->
  PML.ls_ok gk Mk -> credit_le (credit_sub cr (ll_credit Lay n)) crk ->
  PML.parser_at Mk (sp - 688) ps -> 0 < PML.ps_scap ps <= 4096 -> PML.source_at Mk (sp - 1000) ch -> PML.isrc_at Mk (sp - 328) rep gp rd ->
  srealizes RSEGS SCFG (@PML.cfg fxk Rk PML.PC_PARSER_DTOR Mk modelk) K.
Proof.
  intros fxk Rk Mk modelk crk gk reps rep ps ch gp rd Hfp X2 X1 X10 KR P B BR FR BV MO HH LS CR PA SCAP SRC ISRC.
  pose proof SPOK as [SP1 SP2]. pose proof SCRv as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOKH.
  unfold PML.isrc_at in ISRC. cbv zeta in ISRC.
  destruct ISRC as (A0 & A16 & A24 & A32 & A40 & A48 & Ag & A56 & A64 & A72 & As & A104 & A112 & A120 & Aio & Ard & Adef).
  replace (sp - 328 + 24) with (sp - 304) in A24 by lia.
  replace (sp - 328 + 80) with (sp - 248) in As by lia.
  replace (sp - 328 + 120) with (sp - 208) in Aio by lia.
  replace (sp - 328 + 16) with (sp - 312) in Aio by lia.
  assert (BKR : TK2.blocks_ok L (PML.srep_blocks rep)) by (intros b Hb; apply BOKH; apply in_or_app; right; right; apply in_or_app; left; exact Hb).
  destruct (t0_wp Mk rep FR As BKR BR) as (w & p & Hw & Hp & U248 & U232 & REL).
  apply (PDTOR _ crk (sp - 1040) HCT.R_PDTOR (sp - 688) ps fxk Rk Mk modelk K HH MO HK0 Hfp).
  - cbv beta. split.
    + apply mk_entry; [exact X1 | apply ra_ok_lit; unfold HCT.R_PDTOR; [lia | reflexivity] | exact X2 | rewrite (KR 4%bv KO_4); exact Ptp |].
      exact (mk_stk LB sp SS PML.in_foot11 M Mk (sp - 1040) (64 + PMS.OPDEL_SCR) FR SP2 eq_refl ltac:(lia) ltac:(lia) Hceil Hsptop Htop).
    + split; [exact X10|]. split; [exact PA|]. split; [exact (proj1 LS)|]. split; [oos SP2 | exact SCAP].
  - intros fx1 R1 M1 model1 LB1 cr1 LBk1 W1 Hfp1 (-> & -> & -> & ->) RP1 HP1 BV1 HH1.
    assert (WK : w_ok [(sp - 688, 272)]) by (intros w0 Hw0; destruct Hw0 as [<-|[]]; left; cbn [fst snd]; lia).
    assert (INC : incl (PML.srep_blocks reps ++ LB) ((ch, 16384) :: PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB))
      by (intros b Hb; right; apply in_or_app; right; exact Hb).
    destruct (step_heap reps Mk M1 _ (64 + PMS.OPDEL_SCR) _ HP1 (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH1) INC ltac:(lia) ltac:(lia) WK P FR) as (P1 & FR1 & AG1 & WS1).
    pose proof (mok_of _ _ BV1 MO) as MO1. pose proof MO1 as (Hh1 & Hl1 & Hm1).
    assert (LS1 : PML.ls_ok gk M1) by (apply (TK2.ls_ok_x _ _ _ AG1); [st_cov | exact LS]).
    assert (SRC1 : PML.source_at M1 (sp - 1000) ch)
      by (apply (source_at_xd _ Mk M1 _ _ AG1); [lia | t0_cv | t0_cv | exact (frame_def M1 (sp - 1000) 320 FR1 ltac:(lia) ltac:(lia)) | exact SRC]).
    assert (U248a : L5.u64_at RSEGS M1 (sp - 248) w) by (apply (TK2.u64_x _ _ _ AG1); [lia | t0_cv | exact U248]).
    assert (U232a : L5.u64_at RSEGS M1 (sp - 232) p) by (apply (TK2.u64_x _ _ _ AG1); [lia | t0_cv | exact U232]).
    assert (U304a : L5.u64_at RSEGS M1 (sp - 304) PML.CLASSIC_IMP) by (apply (TK2.u64_x _ _ _ AG1); [lia | t0_cv | exact A24]).
    assert (IOa : PML.iosb_at M1 (sp - 208) rd (sp - 312)) by (apply (TK2.iosb_at_x _ _ _ AG1); [lia | t0_cv | exact Aio]).
    apply (HCS.s_h_rpdtor FPM fx1 R1 M1 model1 K sp Hh1 Hl1 Hfp1); [rewrite (RP1 _ CS2); exact X2 | exact SPOK |].
    intros fx2 R2 M2 Hfp2 Y2 Y1 Y10 KC2 AG2 MG2. apply samem_all in AG2. subst M2.
    exact (t0_sd fx2 R2 M1 model1 crk gk reps rep ch rd w p Hfp2 Y2 Y1 Y10 (KT _ _ _ (KT _ _ _ KR (KSP _ _ RP1)) (KCO _ _ KC2)) P1 B FR1
             (L5C.model_but_vm_trans _ _ _ BV BV1) MO1 HH1 LS1 CR SRC1 Hw Hp U248a U232a REL U304a IOa).
Qed.

Definition sbit (r : PML.srep) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 1 "S0;Lr;Ri262;m262;RNLr;Ri262;i0;r1;2;Ls;RA1;i17;i0;o2;Lcap;Ri0;Lp;Ri0;Ls;RA1;i17;i0;A1;o4;o48;").
Lemma sbit_word : forall Mk o r, TK2.FR L LB sp SS PML.in_foot11 M Mk -> sp - 1040 <= o -> o + 24 <= sp -> PML.str_at_w Mk o r ->
  (forall b, In b (PML.srep_blocks r) -> block_range L (fst b) (snd b)) ->
  exists w p, 0 <= w < 2 ^ 64 /\ 0 <= p < 2 ^ 64 /\ L5.u64_at RSEGS Mk o w /\ L5.u64_at RSEGS Mk (o + 16) p /\ Z.land (w mod 256) 1 = sbit r.
Proof.
intros Mk o r HF Ho1 Ho2 HS HB.
pose proof SPOK as [S1 S2]. pose proof Htop as [T1 T2].
destruct r as [s|cap p s].
- destruct (CCTL.u64_of_defined Mk o (frame_def Mk o 8 HF Ho1 ltac:(lia))) as (w & Hw & Hu).
  destruct (CCTL.u64_of_defined Mk (o + 16) (frame_def Mk (o + 16) 8 HF ltac:(lia) ltac:(lia))) as (p & Hp & Hu2).
  exists w, p. split; [exact Hw|]. split; [exact Hp|]. split; [exact Hu|]. split; [exact Hu2|].
  cbn [PML.str_at_w] in HS. rewrite (sso_bit Mk o s w ltac:(lia) ltac:(lia) HS Hu). reflexivity.
- cbn [PML.str_at_w] in HS. destruct HS as [(Hb & H0 & H8 & H16 & _) Hlt].
  pose proof (HB (p, cap) (or_introl eq_refl)) as (B0 & B1 & B2 & B3 & B4). cbn [fst snd] in *.
  exists (cap + 1), p. split; [lia|]. split; [lia|]. split; [exact H0|]. split; [exact H16|].
  rewrite (land1_odd_low _ Hb). reflexivity.
Qed.
Lemma kex_out : forall (Ma Mb : mem), TK.samem (HCS.KEX sp) Ma Mb -> TK.samem (L5.outside [(sp - 1008, 8); (sp - 360, 8)]) Ma Mb.
Proof.
intros Ma Mb H. apply (TK.samem_weaken _ _ _ _ H). intros a Ho. unfold HCS.KEX. split; intros X;
  [apply (Ho (sp - 1008, 8) (or_introl eq_refl)) | apply (Ho (sp - 360, 8) (or_intror (or_introl eq_refl)))];
  unfold L5.in_rng; cbn [fst snd]; lia.
Qed.
Lemma b2z_0 : forall b, PML.b2z b = 0 -> b = false. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S1;A1;k232;o32;Lb;Ri31;m31;RNLb;Ri31;P~RA3;i5;i0;A1;k232;r1;o2;A3;i5;i31;r2;o403;r1;2;LH;RA3;i5;i0;#0;o2;EH0;RA6;k35;i0;#0;Le;Ri0;m0;RNLz;Ri0;pr1;3;i75;L~Ri100;i101;L~Ri100;i75;o102;o2;r1;i75;A2;k86;A3;i5;i31;o32;o403;r1;LH;RA3;i5;i0;A1;k232;o403;o2;A2;o12;i31;o403;").
Qed.
Lemma b2z_land : forall b, Z.land (PML.b2z b) 1 = 0 -> b = false. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S2;A1;o4;o48;A2;k8;A1;k232;o32;#0;Lb;Ri31;m31;RNLb;Ri31;P~RA3;i5;i0;A2;k8;A1;k232;r1;#0;o2;A3;i5;i31;r2;o403;r1;2;LH;RA3;i5;i0;#1;o2;EH0;RA6;k35;i0;#1;Le;Ri0;m0;RNLz;Ri0;pr1;3;i75;L~Ri100;i101;L~Ri100;i75;o102;o2;r1;i75;A2;k86;A3;i5;i31;o32;o403;r1;LH;RA3;i5;i0;A2;k8;A1;k232;o403;#0;o2;A2;o12;i31;o403;").
Qed.
Lemma b2z_rng : forall b, 0 <= PML.b2z b < 256. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S41;A1;k232;r1;A1;o4;Y8;00;Y3;0;A2;k119;A1;i91;A1;o92;#2;vpayload;A1;k120;#3;A3;i5;i0;vn;#4;cdA2;o12;i0;#4;#5;A1;k258;vLay;A3;i5;i0;vSS;#7;cdA2;o12;i0;#7;#8;A1;k129;#3;A2;k1;o2;#4;Y1;0;A1;o4;#12;A1;o4;Y5;0f;A2;k130;#13;#14;A2;k39;o2;#13;A2;k11;#13;#14;P~R#16;P~RA2;k1;o2;#14;A2;k39;o2;#17;A2;k1;o2;#13;LHa;R#19;L~Ri101;A3;k131;#13;#14;r2;PHa;R#19;P~Ri101;A2;k1;o2;#17;A1;o4;Y4;a;A2;k130;#13;#22;A2;k11;#13;#22;P~R#16;P~RA2;k1;o2;#22;A2;k39;o2;#24;LHa;R#19;L~Ri101;A3;k131;#13;#22;r2;PHa;R#19;P~Ri101;A2;k1;o2;#24;A1;o15;i16;A1;i17;i16;A1;o18;i0;A1;i19;i0;A1;i21;i0;A2;o26;i0;o2;A1;o4;o48;A2;o26;i0;#34;A2;o26;i0;#1;A2;k29;#32;o24;A4;k30;r1;r3;cvA2;o12;i31;o32;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;A1;k232;o32;A1;k232;o403;Lb;Ri31;m31;RNLb;Ri31;A2;i40;A2;k1;o2;#0;A2;k39;#0;#1;r1;2;cdEheq_n;R#6;#5;Eheq_SS;R#9;#8;Ecstr;R#10;#11;E__sat4;R#15;#18;E__sat3;R#20;#21;E__sat2;R#23;#25;E__sat1;R#26;#27;E__arith;RE__wit;R#28;#29;E__varmap;R#30;#31;E__ff;RA7;o54;#32;k22;i23;i23;o24;A7;o20;#32;k22;i23;i23;o24;A4;o25;i0;#33;o27;#35;o28;A7;o20;#32;k22;i23;i23;o24;A4;o25;i0;#35;o38;#36;o28;#37;#38;A2;i40;A2;k1;o2;#34;A2;k39;#34;#1;r1;A2;i40;A2;k1;o2;#39;A2;k39;#39;#1;cdEheq_n;R#6;#5;Eheq_SS;R#9;#8;Ecstr;R#10;#11;E__sat4;R#15;#18;E__sat3;R#20;#21;E__sat2;R#23;#25;E__sat1;R#26;#27;E__arith;RE__wit;R#28;#29;E__varmap;R#30;#31;E__ff;RA7;o54;#32;k22;i23;i23;o24;A7;o20;#32;k22;i23;i23;o24;A4;o25;i0;#33;o27;#33;o28;A7;o20;#32;k22;i23;i23;o24;A4;o25;i0;#33;o38;#36;o28;#37;#38;A2;i40;A2;k1;o2;o2;A2;k39;o2;#1;r1;A2;i40;A2;k1;o2;#40;A2;k39;#40;#1;").
Qed.

Lemma exitk : forall (fx' : FPState) R' Mx M' modelk crk gk reps rep ps ch bof dn gp rd,
  PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_PDTOR -> getr R' 10%bv = Z_to_bv 64 (sp - 688) -> TK.keepsR HCS.KOH R R' ->
  TK.samem (HCS.KEX sp) Mx M' -> mem_grows Mx M' ->
  pers reps Mx -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) -> (forall b, In b (PML.srep_blocks rep) -> 0 <= snd b <= n + 52) ->
  TK2.FR L LB sp SS PML.in_foot11 M Mx -> model_but_vm model modelk -> PML.model_ok modelk ->
  hi_heap HI (PML.ps_blocks ps ++ (ch, 16384) :: PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) crk Mx (m_vmmaps modelk) ->
  PML.ls_ok gk Mx -> credit_le (credit_sub cr (ll_credit Lay n)) crk ->
  PMCS.cursor_at Mx (sp - 1008) (sp - 328) ch bof dn ps -> 0 < PML.ps_scap ps <= 4096 -> PML.isrc_at Mx (sp - 328) rep gp rd ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_PARSER_DTOR M' modelk) K.
Proof.
  intros fx' R' Mx M' modelk crk gk reps rep ps ch bof dn gp rd Hfp H2 H1 H10 HK AG MG Hp Hreps Hrep HFR Hbv Hmok HH Hls Hcr Hcur Hscap Hisrc.
  destruct SCRv as (_ & _ & _ & S4 & _ & S6 & _).
  destruct SPOK as [Hsp Hal].
  pose proof (kex_out Mx M' AG) as AGo.
  assert (HF : forall w, In w [(sp - 1008, 8); (sp - 360, 8)] -> sp - SS <= fst w /\ fst w + snd w <= sp - 56 /\ 0 <= snd w).
  { intros w Hw. cbn [In] in Hw. destruct Hw as [<-|[<-|[]]]; cbn [fst snd]; lia. }
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK.
  match type of HH with hi_heap _ ?l _ _ _ =>
    assert (HB : forall b, In b (PML.srep_blocks reps) -> In b l)
      by (intros b Hb; apply in_or_app; right; right; apply in_or_app; right; apply in_or_app; left; exact Hb);
    assert (HBps : forall b, In b (PML.ps_blocks ps) -> block_range L (fst b) (snd b))
      by (intros b Hb; apply BOK; apply in_or_app; left; exact Hb);
    assert (HBrep : forall b, In b (PML.srep_blocks rep) -> block_range L (fst b) (snd b))
      by (intros b Hb; apply BOK; apply in_or_app; right; right; apply in_or_app; left; exact Hb)
  end.
  destruct (step_out_g _ reps Mx M' _ crk modelk AGo MG HF HB Hp HFR HH) as (Hp' & HFR' & HH' & HSC & HW).
  destruct Hcur as (Hsrc & Hpar & _ & _ & _).
  replace (sp - 1008 + 8) with (sp - 1000) in Hsrc by lia.
  replace (sp - 1008 + 320) with (sp - 688) in Hpar by lia.
  assert (COV : forall a k, (sp - 1000 <= a /\ a + k <= sp - 360) \/ sp - 352 <= a -> TK2.cov (L5.outside [(sp - 1008, 8); (sp - 360, 8)]) a k).
  { intros a k Ha i Hi r Hr Hin. unfold L5.in_rng in Hin. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in Hin; lia. }
  apply (tail0 fx' R' M' modelk crk gk reps rep ps ch gp rd Hfp H2 H1 H10 HK Hp' Hreps Hrep HFR' Hbv Hmok HH').
  - exact (TK2.ls_ok_x _ _ _ AGo HSC gk Hls).
  - exact Hcr.
  - apply (TK2.parser_at_x _ _ _ AGo); [lia | apply COV; lia | | exact Hpar].
    apply (TK2.ps_cov_out L LAY); [lia | exact HW | exact HBps].
  - exact Hscap.
  - apply (source_at_xd _ Mx M' _ ch AGo); [lia | apply COV; lia | apply COV; lia | apply (frame_def M' _ _ HFR'); lia |].
    apply (src_source Mx _ _ ch bof Hsrc). apply (frame_def Mx _ _ HFR); lia.
  - apply (TK2.isrc_at_x _ _ _ AGo); [lia | apply COV; lia | | exact Hisrc].
    apply (TK2.str_cov_out L LAY); [lia | apply COV; lia | exact HW | exact HBrep].
Qed.

Ltac bs_in := vm_compute; repeat (first [left; reflexivity | right]).
Ltac bs_get_refute Hexit := let E1 := fresh "E" in let E2 := fresh "E" in let E3 := fresh "E" in
  intros E1 E2 E3; exfalso; destruct Hexit as [X|[X|X]];
  [rewrite X in E1; cbn in E1; discriminate E1 | rewrite X in E2; vm_compute in E2; discriminate E2 | exact (X E3)].
Ltac bs_b01 b := unfold PML.b2z; destruct b; lia.
Lemma brs2 : forall (fxk : FPState) Rk Mk modelk crk gk reps rep r2 ps ch bof dn ec gp rd,
  PML.fp_ok fxk -> getr Rk 2%bv = Z_to_bv 64 (sp - 1040) -> getr Rk 10%bv = Z_to_bv 64 (sbit r2) -> TK.keepsR HCS.KOH R Rk -> getr Rk 18%bv = Z_to_bv 64 2 ->
  PML.str_at_w Mk (sp - 1032) r2 ->
  pers reps Mk -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) -> (forall b, In b (PML.srep_blocks rep) -> 0 <= snd b <= n + 52) ->
  TK2.FR L LB sp SS PML.in_foot11 M Mk -> model_but_vm model modelk -> PML.model_ok modelk ->
  hi_heap HI (PML.srep_blocks r2 ++ PML.ps_blocks ps ++ (ch, 16384) :: PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) crk Mk (m_vmmaps modelk) ->
  PML.ls_ok gk Mk -> credit_le (credit_sub cr (ll_credit Lay n)) crk ->
  PMCS.cursor_at Mk (sp - 1008) (sp - 328) ch bof dn ps -> 0 < PML.ps_scap ps <= 4096 -> PML.isrc_at Mk (sp - 328) rep gp rd -> PML.u32 Mk (sp - 344) ec -> 0 <= ec < 2 ^ 31 ->
  (PML.ps_done ps = true \/ dn = true \/ ec <> 0) ->
  srealizes RSEGS SCFG (@PML.cfg fxk Rk HCT.BR_S2 Mk modelk) K.
Proof.
  intros fxk Rk Mk modelk crk gk reps rep r2 ps ch bof dn ec gp rd Hfp H2 H10 HK H18 Hr2 Hp Hreps Hrep HFR Hbv Hmok HH Hls Hcr Hcur Hscap Hisrc Hec Hecr Hexit.
  destruct SCRv as (_ & _ & _ & S4 & _ & S6 & _).
  pose proof SPOK as [Hsp Hal].
  pose proof Hmok as (Hh & Hl & Hmat).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK.
  destruct r2 as [s | cap p s].
  -
    assert (H10' : getr Rk 10%bv = Z_to_bv 64 0) by (rewrite H10; reflexivity).
    cbn [PML.srep_blocks app] in HH.
    pose proof Hcur as (_ & Hpar & _ & Hdn & _).
    destruct Hpar as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpd & _).
    unfold PML.u8 in Hpd, Hdn. unfold PML.u32 in Hec.
    replace (sp - 1008 + 320 + 212) with (sp - 476) in Hpd by lia.
    replace (sp - 1008 + 640) with (sp - 368) in Hdn by lia.
    apply (HCS.s_h_s2s FPM fxk Rk Mk modelk K sp (PML.b2z (PML.ps_done ps)) (PML.b2z dn) ec Hh Hl Hfp H2 SPOK H10' H18).
    + bs_b01 (PML.ps_done ps).
    + bs_b01 dn.
    + exact Hecr.
    + exact Hpd.
    + exact Hdn.
    + exact Hec.
    + apply (frame_def Mk _ _ HFR); lia.
    + apply (frame_def Mk _ _ HFR); lia.
    + bs_get_refute Hexit.
    + intros _ fx' R' M' Hfp' H2' H1' H10'' HK' _ _ AG MG.
      exact (exitk fx' R' Mk M' modelk crk gk reps rep ps ch bof dn gp rd Hfp' H2' H1' H10'' (KT _ _ _ HK HK') AG MG Hp Hreps Hrep HFR Hbv Hmok HH Hls Hcr Hcur Hscap Hisrc).
  -
    pose proof Hr2 as Hr2w.
    cbn [PML.str_at_w] in Hr2. destruct Hr2 as [(Hbit & Hw0 & Hlen & Hp16 & Hbytes & Hnul) Hlt].
    assert (BR2 : forall b, In b (PML.srep_blocks (PML.SLong cap p s)) -> block_range L (fst b) (snd b))
      by (intros b Hb; apply BOK; apply in_or_app; left; exact Hb).
    pose proof (BR2 (p, cap) (or_introl eq_refl)) as (B0 & B1 & B2 & B3 & B4). cbn [fst snd] in B0, B1, B2, B3, B4.
    destruct (sbit_word Mk (sp - 1032) (PML.SLong cap p s) HFR ltac:(lia) ltac:(lia) Hr2w BR2) as (w & p' & Hwr & _ & Hw & _ & _).
    assert (H10' : getr Rk 10%bv = Z_to_bv 64 1) by (rewrite H10; reflexivity).
    replace (sp - 1032 + 16) with (sp - 1016) in Hp16 by lia.
    apply (HCS.s_h_s2l FPM fxk Rk Mk modelk K sp w p Hh Hl Hfp H2 SPOK H10' Hwr ltac:(lia) Hw Hp16).
    intros fx1 R1 M1 Hfp1 H2_1 H1_1 H10_1 HK1 AG1 MG1.
    pose proof (samem_all Mk M1 AG1) as E. subst M1.
    cbn [PML.srep_blocks app] in HH.
    apply (OPDELS _ crk p cap (sp - 1040) HCT.R_OPDEL_S2 fx1 R1 Mk modelk K HH Hmok HK0 Hfp1).
    { split; [|split; [exact H10_1 | left; reflexivity]].
      apply (mk_entry R1 Mk (sp - 1040) HCT.R_OPDEL_S2 PMS.OPDEL_SCR H1_1).
      - apply ra_ok_lit; unfold HCT.R_OPDEL_S2; [lia | reflexivity].
      - exact H2_1.
      - rewrite (HK1 4%bv KC_4), (HK 4%bv KO_4). exact Ptp.
      - apply (mk_stk LB sp SS PML.in_foot11 M Mk (sp - 1040) PMS.OPDEL_SCR HFR); [lia | reflexivity | lia | lia | exact Hceil | exact Hsptop | exact Htop]. }
    intros fx2 R2 M2 model2 LB2 cr2 LBk2 W2 Hfp2 (-> & -> & -> & ->) RP2 HP2 BV2 HH2.
    cbn [lb_remove fst] in HP2, HH2. rewrite Z.eqb_refl in HP2, HH2.
    pose proof (mok_of _ _ BV2 Hmok) as Hmok2. pose proof Hmok2 as (Hh2 & Hl2 & _).
    pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH2) as BOK2.
    assert (WOK : w_ok []) by (intros w' Hw'; destruct Hw').
    match type of HH2 with hi_heap _ ?l _ _ _ =>
      assert (INCL : incl (PML.srep_blocks reps ++ LB) l) by
        (intros b Hb; rewrite !in_app_iff in *; cbn [In]; rewrite !in_app_iff; tauto);
      assert (BIN : forall b, In b (PML.ps_blocks ps) \/ In b (PML.srep_blocks rep) -> In b l /\ block_range L (fst b) (snd b)) by
        (intros b Hb; assert (X : In b l) by (rewrite !in_app_iff; cbn [In]; rewrite !in_app_iff; tauto); split; [exact X | exact (BOK2 b X)])
    end.
    destruct (step_heap reps Mk M2 _ PMS.OPDEL_SCR [] HP2 BOK2 INCL ltac:(lia) ltac:(lia) WOK Hp HFR) as (Hp2 & HFR2 & AG2 & HW2).
    assert (COVK : forall LBk a k, sp - 1040 <= a -> TK2.cov (TK2.keepH L LBk [] (sp - 1040) PMS.OPDEL_SCR) a k).
    { intros LBk a k Ha i Hi. split; [intros r' Hr'; destruct Hr' | left; lia]. }
    assert (Hcur2 : PMCS.cursor_at M2 (sp - 1008) (sp - 328) ch bof dn ps).
    { apply (cursor_at_xd _ Mk M2 (sp - 1008) (sp - 328) ch bof dn ps AG2); [lia | apply COVK; lia | | apply (frame_def M2 _ _ HFR2); lia | exact Hcur].
      apply (TK2.ps_cov_keepH L LAY); [lia | exact HW2 | intros b Hb; apply BIN; left; exact Hb]. }
    assert (Hisrc2 : PML.isrc_at M2 (sp - 328) rep gp rd).
    { apply (TK2.isrc_at_x _ Mk M2 AG2); [lia | apply COVK; lia | | exact Hisrc].
      apply (TK2.str_cov_keepH L LAY); [lia | apply COVK; lia | exact HW2 | intros b Hb; apply BIN; right; exact Hb]. }
    assert (Hec2 : PML.u32 M2 (sp - 344) ec) by (apply (TK2.u32_x _ Mk M2 AG2); [lia | apply COVK; lia | exact Hec]).
    assert (Hls2 : PML.ls_ok gk M2) by (apply (TK2.ls_ok_x _ Mk M2 AG2); [st_cov | exact Hls]).
    pose proof (L5C.model_but_vm_trans _ _ _ Hbv BV2) as Hbv2.
    assert (H2_2 : getr R2 2%bv = Z_to_bv 64 (sp - 1040)) by (rewrite (RP2 2%bv CS2); exact H2_1).
    assert (H18_2 : getr R2 18%bv = Z_to_bv 64 2) by (rewrite (RP2 18%bv ltac:(bs_in)), (HK1 18%bv ltac:(bs_in)); exact H18).
    pose proof Hcur2 as (_ & Hpar & _ & Hdn & _).
    destruct Hpar as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpd & _).
    unfold PML.u8 in Hpd, Hdn. unfold PML.u32 in Hec2.
    replace (sp - 1008 + 320 + 212) with (sp - 476) in Hpd by lia.
    replace (sp - 1008 + 640) with (sp - 368) in Hdn by lia.
    apply (HCS.s_h_test_opdel FPM fx2 R2 M2 model2 K sp (PML.b2z (PML.ps_done ps)) (PML.b2z dn) ec Hh2 Hl2 Hfp2 H2_2 SPOK H18_2).
    + bs_b01 (PML.ps_done ps).
    + bs_b01 dn.
    + exact Hecr.
    + exact Hpd.
    + exact Hdn.
    + exact Hec2.
    + apply (frame_def M2 _ _ HFR2); lia.
    + apply (frame_def M2 _ _ HFR2); lia.
    + bs_get_refute Hexit.
    + intros _ fx' R' M' Hfp' H2' H1' H10'' HK' _ _ AG MG.
      exact (exitk fx' R' M2 M' model2 crk gk reps rep ps ch bof dn gp rd Hfp' H2' H1' H10''
               (KT _ _ _ (KT _ _ _ HK (KCO _ _ HK1)) (KT _ _ _ (KSP _ _ RP2) HK')) AG MG Hp2 Hreps Hrep HFR2 Hbv2 Hmok2 HH2 Hls2 Hcr Hcur2 Hscap Hisrc2).
Qed.

Lemma scap_wf : forall ps, PML.wf_ps ps -> In (PML.ps_scap ps) [66; 132; 264; 528; 1056].
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S38;A1;k415;r2;A1;o4;Y3;3;A1;k416;r2;A1;o4;Y2;3;N1027;Y6;02;Y7;04;Y8;08;Y9;010;A3;o41;i0;A1;o4;#5;A3;o41;i0;A1;o4;#6;A3;o41;i0;A1;o4;#7;A3;o41;i0;A1;o4;#8;A3;o41;i0;A1;o4;Y10;020;A1;o15;i0;A1;i17;i0;A3;o41;i0;k442;A3;k166;i0;r2;r1;A3;i443;i0;k444;r2;A1;k120;A2;k119;i0;r3;A1;k412;r5;A1;o4;Y10;000;A1;k414;r5;A3;k84;i0;k447;r2;A1;o4;o48;A1;k416;r6;A1;k415;r4;A1;k416;r5;A1;k412;r8;A1;k414;r8;A1;k412;r9;A1;k414;r9;A1;k416;r8;A1;k412;r12;A1;k414;r12;A1;k412;r13;A1;k422;r12;A1;k414;r13;A1;k412;r16;A1;k414;r16;A1;k412;r17;A1;k414;r17;A1;k412;r20;A1;k414;r20;Lps;Ri241;LH0;RA1;k441;r1;m40;RNL~RA2;i40;A2;i40;A2;k1;o2;#0;A2;k1;#0;#1;A2;i40;A2;i40;A2;k1;o2;#2;A2;k1;#2;#3;A2;i40;A2;i118;A2;k119;i0;A1;k422;r2;#4;A2;i40;A3;k84;i0;A1;k423;r2;#9;A2;i83;#10;LC;R#10;A2;i83;#10;LT;R#10;A2;i40;A3;i5;#10;A1;k422;r4;#11;A2;i40;#12;P~RA3;i5;i31;A1;k417;r4;o32;A2;i40;A3;i5;i0;#13;#14;A2;i40;A2;i40;A2;k1;o2;#14;A2;k1;#14;#15;A2;i40;A1;k445;#16;A2;i40;A2;k446;#16;r2;A2;i40;P~RA2;i67;A3;i5;i0;#16;k447;#17;A2;k1;#18;A1;k412;r6;P~RA3;i5;i0;#16;k448;A2;k449;#19;A1;k420;r6;A3;k84;i0;A1;k423;r3;#9;r1;1;L~RA2;i40;A2;k1;o2;#0;A2;k1;#0;#1;L~RA2;i40;A2;i40;A2;k1;o2;A1;k416;r3;A2;k1;A1;k416;r3;#3;A2;i40;A2;i118;A2;k119;i0;A1;k422;r3;#4;A2;i40;A3;k84;i0;A1;k423;r3;#9;A2;i83;#10;LC;R#10;A2;i83;#10;LT;R#10;A2;i40;A3;i5;#10;A1;k422;r5;#11;A2;i40;#12;P~RA3;i5;i31;A1;k417;r5;o32;A2;i40;A3;i5;i0;#13;A1;k412;r6;A2;i40;A2;i40;A2;k1;o2;A1;k412;r6;A2;k1;A1;k412;r6;#15;A2;i40;A1;k445;A1;k414;r6;A2;i40;A2;k446;A1;k414;r6;r2;A2;i40;P~RA2;i67;A3;i5;i0;A1;k414;r6;k447;#17;A2;k1;#18;A1;k412;r7;P~RA3;i5;i0;A1;k414;r6;k448;A2;k449;A1;k416;r7;A1;k420;r7;A2;L_H;RA2;i40;A2;k1;o2;#20;A2;k1;#20;#1;LH0;RA2;i40;A2;i40;A2;k1;o2;#21;A2;k1;#21;#3;A2;i40;A2;i118;A2;k119;i0;A1;k422;r5;#4;A2;i40;A3;k84;i0;A1;k423;r5;#9;A2;i83;#10;LC;R#10;A2;i83;#10;LT;R#10;A2;i40;A3;i5;#10;A1;k422;r7;#11;A2;i40;#12;P~RA3;i5;i31;A1;k417;r7;o32;A2;i40;A3;i5;i0;#13;#22;A2;i40;A2;i40;A2;k1;o2;#22;A2;k1;#22;#15;A2;i40;A1;k445;#23;A2;i40;A2;k446;#23;r2;A2;i40;P~RA2;i67;A3;i5;i0;#23;k447;#17;A2;k1;#18;#24;P~RA3;i5;i0;#23;k448;A2;k449;A1;k416;r9;A1;k420;r9;m40;RNL~RA2;i40;A2;i40;A2;k1;o2;#19;A2;k1;#19;#3;A2;i40;A2;i118;A2;k119;i0;A1;k422;r6;#4;A2;i40;A3;k84;i0;A1;k423;r6;#9;A2;i83;#10;LC;R#10;A2;i83;#10;LT;R#10;A2;i40;A3;i5;#10;A1;k422;r8;#11;A2;i40;#12;P~RA3;i5;i31;A1;k417;r8;o32;A2;i40;A3;i5;i0;#13;#24;A2;i40;A2;i40;A2;k1;o2;#24;A2;k1;#24;#15;A2;i40;A1;k445;#25;A2;i40;A2;k446;#25;r2;A2;i40;P~RA2;i67;A3;i5;i0;#25;k447;#17;A2;k1;#18;A1;k412;r10;P~RA3;i5;i0;#25;k448;A2;k449;A1;k416;r10;A1;k420;r10;A3;k84;i0;A1;k423;r7;#9;r1;1;L~RA2;i40;A2;k1;o2;#19;A2;k1;#19;#3;L~RA2;i40;A2;i118;A2;k119;i0;A1;k422;r7;#4;A2;i40;A3;k84;i0;A1;k423;r7;#9;A2;i83;#10;LC;R#10;A2;i83;#10;LT;R#10;A2;i40;A3;i5;#10;A1;k422;r9;#11;A2;i40;#12;P~RA3;i5;i31;A1;k417;r9;o32;A2;i40;A3;i5;i0;#13;A1;k412;r10;A2;i40;A2;i40;A2;k1;o2;A1;k412;r10;A2;k1;A1;k412;r10;#15;A2;i40;A1;k445;A1;k414;r10;A2;i40;A2;k446;A1;k414;r10;r2;A2;i40;P~RA2;i67;A3;i5;i0;A1;k414;r10;k447;#17;A2;k1;#18;A1;k412;r11;P~RA3;i5;i0;A1;k414;r10;k448;A2;k449;A1;k416;r11;A1;k420;r11;A2;L_H0;RA2;i40;A2;k1;o2;#26;A2;k1;#26;#3;LH0;RA2;i40;A2;i118;A2;k119;i0;A1;k422;r9;#4;A2;i40;A3;k84;i0;A1;k423;r9;#9;A2;i83;#10;LC;R#10;A2;i83;#10;LT;R#10;A2;i40;A3;i5;#10;A1;k422;r11;#11;A2;i40;#12;P~RA3;i5;i31;A1;k417;r11;o32;A2;i40;A3;i5;i0;#13;#27;A2;i40;A2;i40;A2;k1;o2;#27;A2;k1;#27;#15;A2;i40;A1;k445;#28;A2;i40;A2;k446;#28;r2;A2;i40;P~RA2;i67;A3;i5;i0;#28;k447;#17;A2;k1;#18;#29;P~RA3;i5;i0;#28;k448;A2;k449;A1;k416;r13;A1;k420;r13;m40;RNL~RA2;i40;A2;i118;A2;k119;i0;A1;k422;r10;#4;A2;i40;A3;k84;i0;A1;k423;r10;#9;A2;i83;#10;LC;R#10;A2;i83;#10;LT;R#10;A2;i40;A3;i5;#10;#30;#11;A2;i40;#12;P~RA3;i5;i31;A1;k417;r12;o32;A2;i40;A3;i5;i0;#13;#29;A2;i40;A2;i40;A2;k1;o2;#29;A2;k1;#29;#15;A2;i40;A1;k445;#31;A2;i40;A2;k446;#31;r2;A2;i40;P~RA2;i67;A3;i5;i0;#31;k447;#17;A2;k1;#18;A1;k412;r14;P~RA3;i5;i0;#31;k448;A2;k449;A1;k416;r14;A1;k420;r14;A3;k84;i0;A1;k423;r11;#9;r1;1;L~RA2;i118;A2;k119;i0;A1;k422;r10;#4;L~RA2;i40;A3;k84;i0;A1;k423;r11;#9;A2;i83;#10;LC;R#10;A2;i83;#10;LT;R#10;A2;i40;A3;i5;#10;A1;k422;r13;#11;A2;i40;#12;P~RA3;i5;i31;A1;k417;r13;o32;A2;i40;A3;i5;i0;#13;A1;k412;r14;A2;i40;A2;i40;A2;k1;o2;A1;k412;r14;A2;k1;A1;k412;r14;#15;A2;i40;A1;k445;A1;k414;r14;A2;i40;A2;k446;A1;k414;r14;r2;A2;i40;P~RA2;i67;A3;i5;i0;A1;k414;r14;k447;#17;A2;k1;#18;A1;k412;r15;P~RA3;i5;i0;A1;k414;r14;k448;A2;k449;A1;k416;r15;A1;k420;r15;A2;L_H1;RA2;i118;A2;k119;i0;#30;#4;LH0;RA2;i40;A3;k84;i0;A1;k423;r13;#9;A2;i83;#10;LC;R#10;A2;i83;#10;LT;R#10;A2;i40;A3;i5;#10;A1;k422;r15;#11;A2;i40;#12;P~RA3;i5;i31;A1;k417;r15;o32;A2;i40;A3;i5;i0;#13;#32;A2;i40;A2;i40;A2;k1;o2;#32;A2;k1;#32;#15;A2;i40;A1;k445;#33;A2;i40;A2;k446;#33;r2;A2;i40;P~RA2;i67;A3;i5;i0;#33;k447;#17;A2;k1;#18;#34;P~RA3;i5;i0;#33;k448;A2;k449;A1;k416;r17;A1;k420;r17;m40;RNL~RA2;i40;A3;k84;i0;A1;k423;r14;#9;A2;i83;#10;LC;R#10;A2;i83;#10;LT;R#10;A2;i40;A3;i5;#10;A1;k422;r16;#11;A2;i40;#12;P~RA3;i5;i31;A1;k417;r16;o32;A2;i40;A3;i5;i0;#13;#34;A2;i40;A2;i40;A2;k1;o2;#34;A2;k1;#34;#15;A2;i40;A1;k445;#35;A2;i40;A2;k446;#35;r2;A2;i40;P~RA2;i67;A3;i5;i0;#35;k447;#17;A2;k1;#18;A1;k412;r18;P~RA3;i5;i0;#35;k448;A2;k449;A1;k416;r18;A1;k420;r18;A3;k84;i0;A1;k423;r15;#9;r1;1;L~RA3;k84;i0;A1;k423;r14;#9;L~RA2;i83;#10;LC;R#10;A2;i83;#10;LT;R#10;A2;i40;A3;i5;#10;A1;k422;r17;#11;A2;i40;#12;P~RA3;i5;i31;A1;k417;r17;o32;A2;i40;A3;i5;i0;#13;A1;k412;r18;A2;i40;A2;i40;A2;k1;o2;A1;k412;r18;A2;k1;A1;k412;r18;#15;A2;i40;A1;k445;A1;k414;r18;A2;i40;A2;k446;A1;k414;r18;r2;A2;i40;P~RA2;i67;A3;i5;i0;A1;k414;r18;k447;#17;A2;k1;#18;A1;k412;r19;P~RA3;i5;i0;A1;k414;r18;k448;A2;k449;A1;k416;r19;A1;k420;r19;A2;LH;RA3;k84;i0;A1;k423;r16;#9;L_H2;RA2;i83;#10;LC;R#10;A2;i83;#10;LT;R#10;A2;i40;A3;i5;#10;A1;k422;r19;#11;A2;i40;#12;P~RA3;i5;i31;A1;k417;r19;o32;A2;i40;A3;i5;i0;#13;#36;A2;i40;A2;i40;A2;k1;o2;#36;A2;k1;#36;#15;A2;i40;A1;k445;#37;A2;i40;A2;k446;#37;r2;A2;i40;P~RA2;i67;A3;i5;i0;#37;k447;#17;A2;k1;#18;A1;k412;r21;P~RA3;i5;i0;#37;k448;A2;k449;A1;k416;r21;A1;k420;r21;r2;r2;r1;r2;r1;r2;r1;r2;r1;").
Qed.
Lemma scap_sm : forall ps m, PML.wf_ps (PMCUR.ps_set_more ps m) -> In (PML.ps_scap ps) [66; 132; 264; 528; 1056].
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S57;A2;k450;r3;r2;A1;k415;#0;A1;o4;Y3;3;A1;k416;#0;A1;o4;Y2;3;N1027;Y6;02;Y7;04;Y8;08;Y9;010;A3;o41;i0;A1;o4;#6;A3;o41;i0;A1;o4;#7;A3;o41;i0;A1;o4;#8;A3;o41;i0;A1;o4;#9;A3;o41;i0;A1;o4;Y10;020;A1;o15;i0;A1;i17;i0;A2;k450;r5;r4;A3;o41;i0;k442;A3;k166;i0;r2;r1;A3;i443;i0;k444;r2;A1;k120;A2;k119;i0;r3;A2;k450;r6;r5;A1;k412;#16;A1;o4;Y10;000;A1;k414;#16;A3;k84;i0;k447;r2;A1;o4;o48;A2;k450;r7;r6;A1;k416;#22;A1;k415;#12;A1;k416;#16;A2;k450;r8;r7;A2;k450;r9;r8;A1;k412;#27;A1;k414;#27;A2;k450;r10;r9;A1;k412;#30;A1;k414;#30;A2;k450;r11;r10;A1;k416;#27;A2;k450;r12;r11;A2;k450;r13;r12;A1;k412;#36;A1;k414;#36;A2;k450;r14;r13;A1;k412;#39;A1;k422;#36;A1;k414;#39;A2;k450;r15;r14;A2;k450;r16;r15;A2;k450;r17;r16;A1;k412;#45;A1;k414;#45;A2;k450;r18;r17;A1;k412;#48;A1;k414;#48;A2;k450;r19;r18;A2;k450;r20;r19;A2;k450;r21;r20;A1;k412;#53;A1;k414;#53;A2;k450;r22;r21;Lps;Ri241;Lm;Ri31;LH0;RA1;k441;A2;k450;r2;r1;m40;RNL~RA2;i40;A2;i40;A2;k1;o2;#1;A2;k1;#1;#2;A2;i40;A2;i40;A2;k1;o2;#3;A2;k1;#3;#4;A2;i40;A2;i118;A2;k119;i0;A1;k422;#0;#5;A2;i40;A3;k84;i0;A1;k423;#0;#10;A2;i83;#11;LC;R#11;A2;i83;#11;LT;R#11;A2;i40;A3;i5;#11;A1;k422;#12;#13;A2;i40;#14;P~RA3;i5;i31;A1;k417;#12;o32;A2;i40;A3;i5;i0;#15;#17;A2;i40;A2;i40;A2;k1;o2;#17;A2;k1;#17;#18;A2;i40;A1;k445;#19;A2;i40;A2;k446;#19;r2;A2;i40;P~RA2;i67;A3;i5;i0;#19;k447;#20;A2;k1;#21;A1;k412;#22;P~RA3;i5;i0;#19;k448;A2;k449;#23;A1;k420;#22;A3;k84;i0;A1;k423;r4;#10;r1;1;L~RA2;i40;A2;k1;o2;#1;A2;k1;#1;#2;L~RA2;i40;A2;i40;A2;k1;o2;A1;k416;A2;k450;r4;r3;A2;k1;A1;k416;A2;k450;r4;r3;#4;A2;i40;A2;i118;A2;k119;i0;A1;k422;A2;k450;r4;r3;#5;A2;i40;A3;k84;i0;A1;k423;A2;k450;r4;r3;#10;A2;i83;#11;LC;R#11;A2;i83;#11;LT;R#11;A2;i40;A3;i5;#11;A1;k422;A2;k450;r6;r5;#13;A2;i40;#14;P~RA3;i5;i31;A1;k417;A2;k450;r6;r5;o32;A2;i40;A3;i5;i0;#15;A1;k412;A2;k450;r7;r6;A2;i40;A2;i40;A2;k1;o2;A1;k412;A2;k450;r7;r6;A2;k1;A1;k412;A2;k450;r7;r6;#18;A2;i40;A1;k445;A1;k414;A2;k450;r7;r6;A2;i40;A2;k446;A1;k414;A2;k450;r7;r6;r2;A2;i40;P~RA2;i67;A3;i5;i0;A1;k414;A2;k450;r7;r6;k447;#20;A2;k1;#21;A1;k412;A2;k450;r8;r7;P~RA3;i5;i0;A1;k414;A2;k450;r7;r6;k448;A2;k449;A1;k416;A2;k450;r8;r7;A1;k420;A2;k450;r8;r7;A2;L_H;RA2;i40;A2;k1;o2;#24;A2;k1;#24;#2;LH0;RA2;i40;A2;i40;A2;k1;o2;#25;A2;k1;#25;#4;A2;i40;A2;i118;A2;k119;i0;A1;k422;#16;#5;A2;i40;A3;k84;i0;A1;k423;#16;#10;A2;i83;#11;LC;R#11;A2;i83;#11;LT;R#11;A2;i40;A3;i5;#11;A1;k422;#26;#13;A2;i40;#14;P~RA3;i5;i31;A1;k417;#26;o32;A2;i40;A3;i5;i0;#15;#28;A2;i40;A2;i40;A2;k1;o2;#28;A2;k1;#28;#18;A2;i40;A1;k445;#29;A2;i40;A2;k446;#29;r2;A2;i40;P~RA2;i67;A3;i5;i0;#29;k447;#20;A2;k1;#21;#31;P~RA3;i5;i0;#29;k448;A2;k449;A1;k416;#30;A1;k420;#30;m40;RNL~RA2;i40;A2;i40;A2;k1;o2;#23;A2;k1;#23;#4;A2;i40;A2;i118;A2;k119;i0;A1;k422;#22;#5;A2;i40;A3;k84;i0;A1;k423;#22;#10;A2;i83;#11;LC;R#11;A2;i83;#11;LT;R#11;A2;i40;A3;i5;#11;A1;k422;#27;#13;A2;i40;#14;P~RA3;i5;i31;A1;k417;#27;o32;A2;i40;A3;i5;i0;#15;#31;A2;i40;A2;i40;A2;k1;o2;#31;A2;k1;#31;#18;A2;i40;A1;k445;#32;A2;i40;A2;k446;#32;r2;A2;i40;P~RA2;i67;A3;i5;i0;#32;k447;#20;A2;k1;#21;A1;k412;#33;P~RA3;i5;i0;#32;k448;A2;k449;A1;k416;#33;A1;k420;#33;A3;k84;i0;A1;k423;r8;#10;r1;1;L~RA2;i40;A2;k1;o2;#23;A2;k1;#23;#4;L~RA2;i40;A2;i118;A2;k119;i0;A1;k422;A2;k450;r8;r7;#5;A2;i40;A3;k84;i0;A1;k423;A2;k450;r8;r7;#10;A2;i83;#11;LC;R#11;A2;i83;#11;LT;R#11;A2;i40;A3;i5;#11;A1;k422;A2;k450;r10;r9;#13;A2;i40;#14;P~RA3;i5;i31;A1;k417;A2;k450;r10;r9;o32;A2;i40;A3;i5;i0;#15;A1;k412;A2;k450;r11;r10;A2;i40;A2;i40;A2;k1;o2;A1;k412;A2;k450;r11;r10;A2;k1;A1;k412;A2;k450;r11;r10;#18;A2;i40;A1;k445;A1;k414;A2;k450;r11;r10;A2;i40;A2;k446;A1;k414;A2;k450;r11;r10;r2;A2;i40;P~RA2;i67;A3;i5;i0;A1;k414;A2;k450;r11;r10;k447;#20;A2;k1;#21;A1;k412;A2;k450;r12;r11;P~RA3;i5;i0;A1;k414;A2;k450;r11;r10;k448;A2;k449;A1;k416;A2;k450;r12;r11;A1;k420;A2;k450;r12;r11;A2;L_H0;RA2;i40;A2;k1;o2;#34;A2;k1;#34;#4;LH0;RA2;i40;A2;i118;A2;k119;i0;A1;k422;#30;#5;A2;i40;A3;k84;i0;A1;k423;#30;#10;A2;i83;#11;LC;R#11;A2;i83;#11;LT;R#11;A2;i40;A3;i5;#11;A1;k422;#35;#13;A2;i40;#14;P~RA3;i5;i31;A1;k417;#35;o32;A2;i40;A3;i5;i0;#15;#37;A2;i40;A2;i40;A2;k1;o2;#37;A2;k1;#37;#18;A2;i40;A1;k445;#38;A2;i40;A2;k446;#38;r2;A2;i40;P~RA2;i67;A3;i5;i0;#38;k447;#20;A2;k1;#21;#40;P~RA3;i5;i0;#38;k448;A2;k449;A1;k416;#39;A1;k420;#39;m40;RNL~RA2;i40;A2;i118;A2;k119;i0;A1;k422;#33;#5;A2;i40;A3;k84;i0;A1;k423;#33;#10;A2;i83;#11;LC;R#11;A2;i83;#11;LT;R#11;A2;i40;A3;i5;#11;#41;#13;A2;i40;#14;P~RA3;i5;i31;A1;k417;#36;o32;A2;i40;A3;i5;i0;#15;#40;A2;i40;A2;i40;A2;k1;o2;#40;A2;k1;#40;#18;A2;i40;A1;k445;#42;A2;i40;A2;k446;#42;r2;A2;i40;P~RA2;i67;A3;i5;i0;#42;k447;#20;A2;k1;#21;A1;k412;#43;P~RA3;i5;i0;#42;k448;A2;k449;A1;k416;#43;A1;k420;#43;A3;k84;i0;A1;k423;r12;#10;r1;1;L~RA2;i118;A2;k119;i0;A1;k422;#33;#5;L~RA2;i40;A3;k84;i0;A1;k423;A2;k450;r12;r11;#10;A2;i83;#11;LC;R#11;A2;i83;#11;LT;R#11;A2;i40;A3;i5;#11;A1;k422;A2;k450;r14;r13;#13;A2;i40;#14;P~RA3;i5;i31;A1;k417;A2;k450;r14;r13;o32;A2;i40;A3;i5;i0;#15;A1;k412;A2;k450;r15;r14;A2;i40;A2;i40;A2;k1;o2;A1;k412;A2;k450;r15;r14;A2;k1;A1;k412;A2;k450;r15;r14;#18;A2;i40;A1;k445;A1;k414;A2;k450;r15;r14;A2;i40;A2;k446;A1;k414;A2;k450;r15;r14;r2;A2;i40;P~RA2;i67;A3;i5;i0;A1;k414;A2;k450;r15;r14;k447;#20;A2;k1;#21;A1;k412;A2;k450;r16;r15;P~RA3;i5;i0;A1;k414;A2;k450;r15;r14;k448;A2;k449;A1;k416;A2;k450;r16;r15;A1;k420;A2;k450;r16;r15;A2;L_H1;RA2;i118;A2;k119;i0;#41;#5;LH0;RA2;i40;A3;k84;i0;A1;k423;#39;#10;A2;i83;#11;LC;R#11;A2;i83;#11;LT;R#11;A2;i40;A3;i5;#11;A1;k422;#44;#13;A2;i40;#14;P~RA3;i5;i31;A1;k417;#44;o32;A2;i40;A3;i5;i0;#15;#46;A2;i40;A2;i40;A2;k1;o2;#46;A2;k1;#46;#18;A2;i40;A1;k445;#47;A2;i40;A2;k446;#47;r2;A2;i40;P~RA2;i67;A3;i5;i0;#47;k447;#20;A2;k1;#21;#49;P~RA3;i5;i0;#47;k448;A2;k449;A1;k416;#48;A1;k420;#48;m40;RNL~RA2;i40;A3;k84;i0;A1;k423;#43;#10;A2;i83;#11;LC;R#11;A2;i83;#11;LT;R#11;A2;i40;A3;i5;#11;A1;k422;#45;#13;A2;i40;#14;P~RA3;i5;i31;A1;k417;#45;o32;A2;i40;A3;i5;i0;#15;#49;A2;i40;A2;i40;A2;k1;o2;#49;A2;k1;#49;#18;A2;i40;A1;k445;#50;A2;i40;A2;k446;#50;r2;A2;i40;P~RA2;i67;A3;i5;i0;#50;k447;#20;A2;k1;#21;A1;k412;#51;P~RA3;i5;i0;#50;k448;A2;k449;A1;k416;#51;A1;k420;#51;A3;k84;i0;A1;k423;r16;#10;r1;1;L~RA3;k84;i0;A1;k423;#43;#10;L~RA2;i83;#11;LC;R#11;A2;i83;#11;LT;R#11;A2;i40;A3;i5;#11;A1;k422;A2;k450;r18;r17;#13;A2;i40;#14;P~RA3;i5;i31;A1;k417;A2;k450;r18;r17;o32;A2;i40;A3;i5;i0;#15;A1;k412;A2;k450;r19;r18;A2;i40;A2;i40;A2;k1;o2;A1;k412;A2;k450;r19;r18;A2;k1;A1;k412;A2;k450;r19;r18;#18;A2;i40;A1;k445;A1;k414;A2;k450;r19;r18;A2;i40;A2;k446;A1;k414;A2;k450;r19;r18;r2;A2;i40;P~RA2;i67;A3;i5;i0;A1;k414;A2;k450;r19;r18;k447;#20;A2;k1;#21;A1;k412;A2;k450;r20;r19;P~RA3;i5;i0;A1;k414;A2;k450;r19;r18;k448;A2;k449;A1;k416;A2;k450;r20;r19;A1;k420;A2;k450;r20;r19;A2;LH;RA3;k84;i0;A1;k423;#45;#10;L_H2;RA2;i83;#11;LC;R#11;A2;i83;#11;LT;R#11;A2;i40;A3;i5;#11;A1;k422;#52;#13;A2;i40;#14;P~RA3;i5;i31;A1;k417;#52;o32;A2;i40;A3;i5;i0;#15;#54;A2;i40;A2;i40;A2;k1;o2;#54;A2;k1;#54;#18;A2;i40;A1;k445;#55;A2;i40;A2;k446;#55;r2;A2;i40;P~RA2;i67;A3;i5;i0;#55;k447;#20;A2;k1;#21;A1;k412;#56;P~RA3;i5;i0;#55;k448;A2;k449;A1;k416;#56;A1;k420;#56;r2;r2;r1;r2;r1;r2;r1;r2;r1;").
Qed.
Lemma pcx_lb : forall crx ps kx bx, PML.pcredit_x L crx ps kx bx -> In (PML.ps_scap ps) [66; 132; 264; 528; 1056] -> kx <= fst crx /\ bx <= snd crx.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S109;A2;k1;o2;r2;Y6;02;A1;o4;#1;Y7;04;A1;o4;#3;Y8;08;A1;o4;#5;Y9;010;A1;o4;#7;Y10;020;A1;o4;#9;A3;o41;i0;#2;A3;o41;i0;#4;A3;o41;i0;#6;A3;o41;i0;#8;A3;o41;i0;#10;A1;o15;i0;A2;k1;o2;r5;A2;k1;o2;r8;Y1;0;A1;o4;#14;Y4;b;A1;o4;#16;A2;k11;#15;#17;A1;k453;r12;A1;k454;vL;A4;o96;i0;i0;A2;k73;A3;k165;i0;i0;r13;r11;A2;k73;A3;k199;i0;i0;r13;r10;A1;k456;vL;A1;k453;r15;A4;o96;i0;i0;A2;k73;A3;k165;i0;i0;r16;r14;A2;k73;A3;k199;i0;i0;r16;r13;A1;k453;r16;A4;o96;i0;i0;A2;k73;A3;k165;i0;i0;r17;r15;A2;k73;A3;k199;i0;i0;r17;r14;A3;k165;i0;i0;r19;A3;k199;i0;i0;r19;A2;k460;#18;A1;k418;r23;A2;k460;#10;A1;k423;r24;Y3;0;A2;k119;A1;i91;A1;o92;#31;vpayload;A1;k120;#32;A3;i5;i0;vn;#33;cdA2;o12;i0;#33;#34;A1;k258;vLay;A3;i5;i0;vSS;#36;cdA2;o12;i0;#36;#37;A1;k129;#32;A2;k1;o2;#33;A1;o4;Y5;0f;A2;k130;#15;#41;A2;k39;o2;#15;A2;k11;#15;#41;P~R#43;P~RA2;k1;o2;#41;A2;k39;o2;#44;A2;k1;o2;#15;LHa;R#46;L~Ri101;A3;k131;#15;#41;r2;PHa;R#46;P~Ri101;A2;k1;o2;#44;A2;k1;o2;#18;A1;k418;r31;A1;k418;r32;A2;k130;#15;#17;P~R#43;P~RA2;k1;o2;#17;A2;k39;o2;#18;LHa;R#46;L~Ri101;A3;k131;#15;#17;r2;PHa;R#46;P~Ri101;#49;A1;o4;Y4;a;A2;k130;#15;#56;A2;k11;#15;#56;P~R#43;P~RA2;k1;o2;#56;A2;k39;o2;#58;LHa;R#46;L~Ri101;A3;k131;#15;#56;r2;PHa;R#46;P~Ri101;A2;k1;o2;#58;A2;k1;o2;#10;A2;k460;#10;A1;k423;r37;N2;A2;o44;i0;#64;N1;A2;o44;i0;o49;A3;o43;i0;A2;o44;i0;#66;#67;A1;o15;i16;A1;i17;i16;A1;o18;i0;A4;o51;i0;A2;o52;i0;r3;r2;#71;A1;i19;i0;A1;i21;i0;A2;o26;i0;o2;A2;o55;i0;#14;A1;o56;i23;A2;o55;i0;o48;A2;k29;#74;o24;A4;k30;r1;r3;cvA2;o12;i31;o32;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;A2;k1;o2;A1;k453;r25;Y4;c;A1;o4;#82;A2;k11;#15;#83;A1;k423;r39;A1;k423;r40;N3;A2;o44;i0;#87;A2;o134;#67;A2;o42;A3;o43;i0;#67;A3;o43;i0;A3;o45;i0;A2;o46;i0;A1;o47;o48;#88;#65;o50;A2;o26;i0;#15;A1;o4;Y11;040;A2;k1;o2;A1;k455;r26;A1;k453;r27;A1;k453;r28;N5;N6;A2;o55;i0;Y3;4;A2;o55;i0;Y3;7;A3;o137;i0;#97;#98;Y3;5;A2;o55;i0;#100;A3;o137;i0;#97;#101;Y3;6;A2;o55;i0;#103;Y2;0;A2;o55;i0;#105;Y1;1;A2;o55;i0;#107;Lcrx;Rk173;Lps;Ri241;Lkx;Ri0;Lbx;Ri0;LH;RA5;k451;vL;r4;r3;r2;r1;m40;RNL~RA2;i40;A2;k1;o2;r3;A2;i40;#0;A3;k452;vL;A4;o96;i0;i0;A2;k73;A3;k165;i0;i0;r5;r3;A2;k73;A3;k199;i0;i0;r5;r2;r4;P~RA3;k84;i0;A1;k423;r5;#11;A2;i40;A2;k1;r5;A3;k165;i0;i0;r7;A2;k1;r4;A3;k199;i0;i0;r7;r1;1;L~RA2;k1;o2;r3;L~RA2;i40;A2;k1;o2;r3;A3;k452;vL;A4;o96;i0;i0;A2;k73;A3;k165;i0;i0;r6;r4;A2;k73;A3;k199;i0;i0;r6;r3;r5;A2;LH1;R#12;LH;RA2;i40;#12;A3;k452;vL;A4;o96;i0;i0;A2;k73;A3;k165;i0;i0;r8;r6;A2;k73;A3;k199;i0;i0;r8;r5;r7;m40;RNL~RA2;i40;A2;k1;o2;r6;A3;k452;vL;A4;o96;i0;i0;A2;k73;A3;k165;i0;i0;r9;r7;A2;k73;A3;k199;i0;i0;r9;r6;r8;P~RA3;k84;i0;A1;k423;r9;#11;A2;i40;A2;k1;r9;A3;k165;i0;i0;r11;A2;k1;r8;A3;k199;i0;i0;r11;r1;1;L~RA2;k1;o2;r6;L~RA3;k452;vL;A4;o96;i0;i0;A2;k73;A3;k165;i0;i0;r10;r8;A2;k73;A3;k199;i0;i0;r10;r7;r9;A2;LH2;R#13;LH;RA3;k452;vL;A4;o96;i0;i0;A2;k73;A3;k165;i0;i0;r12;r10;A2;k73;A3;k199;i0;i0;r12;r9;r11;m40;RNL~RA2;i40;A2;k1;A1;k418;r12;#18;A2;i40;A2;k1;A2;k79;#19;#20;A3;k165;i0;i0;#21;A2;k1;A2;k6;A1;k455;r12;A2;k79;#19;#22;A3;k199;i0;i0;#21;P~RA3;k84;i0;A1;k423;r13;#11;A2;i40;A2;k1;r13;A3;k165;i0;i0;r15;A2;k1;r12;A3;k199;i0;i0;r15;r1;1;L~RA2;k1;A1;k418;r12;#18;L~RA2;i40;A2;k1;A2;k79;A1;k453;r13;#20;A3;k165;i0;i0;A4;o96;i0;i0;A2;k73;A3;k165;i0;i0;r14;r12;A2;k73;A3;k199;i0;i0;r14;r11;A2;k1;A2;k6;A1;k455;r13;A2;k79;A1;k453;r13;#22;A3;k199;i0;i0;A4;o96;i0;i0;A2;k73;A3;k165;i0;i0;r14;r12;A2;k73;A3;k199;i0;i0;r14;r11;A2;LH3;RA2;k1;A1;k418;r14;#18;LH;RA2;i40;A2;k1;A2;k79;#23;#20;A3;k165;i0;i0;#24;A2;k1;A2;k6;A1;k455;r15;A2;k79;#23;#22;A3;k199;i0;i0;#24;m40;RNL~RA2;i40;A2;k1;A2;k79;#25;#20;A3;k165;i0;i0;#26;A2;k1;A2;k6;A1;k455;r16;A2;k79;#25;#22;A3;k199;i0;i0;#26;P~RA3;k84;i0;A1;k423;r17;#11;A2;i40;A2;k1;r17;#27;A2;k1;r16;#28;r1;1;L~RA2;k1;A2;k79;#25;#20;A3;k165;i0;i0;#26;L~RA2;k1;A2;k6;A1;k455;r17;A2;k79;A1;k453;r17;#22;A3;k199;i0;i0;A4;o96;i0;i0;A2;k73;A3;k165;i0;i0;r18;r16;A2;k73;A3;k199;i0;i0;r18;r15;A2;LH4;RA2;k1;A2;k79;A1;k453;r18;#20;A3;k165;i0;i0;A4;o96;i0;i0;A2;k73;#27;r17;A2;k73;#28;r16;LH5;RA2;k1;A2;k6;A1;k455;r19;A2;k79;A1;k453;r19;#22;A3;k199;i0;i0;A4;o96;i0;i0;A2;k73;A3;k165;i0;i0;r20;r18;A2;k73;A3;k199;i0;i0;r20;r17;LWFs;RA3;k84;i0;A1;k423;r20;#11;EKPM0;RA2;k457;vL;vLAY;A2;k1;o2;#20;EBOV0;RA2;k458;vL;vLAY;A2;k1;o2;#22;cdEL1;RA1;k459;#29;A2;k1;o2;A1;k461;#29;EL2;RA1;k459;#30;A2;k1;o2;A1;k461;#30;EKL;RcdEheq_n;R#35;#34;Eheq_SS;R#38;#37;Ecstr;R#39;#40;E__sat13;R#42;#45;E__sat12;R#47;#48;E__sat11;RA2;k462;#18;A1;k418;r30;P~R#49;P~RA2;k1;o2;#50;A2;k1;o2;A2;k460;#18;#51;E__sat10;R#52;#53;E__sat9;R#54;#55;E__sat8;R#57;#59;E__sat7;R#60;#61;E__sat6;RA2;k462;#10;A1;k423;r35;P~R#62;P~RA2;k1;o2;A1;k423;r36;A2;k1;o2;#63;E__arith;RL__x2;Ri0;L__x1;Ri0;E__wit;RA3;o41;i16;A2;o42;A3;o43;i0;#65;#68;o50;#69;#70;E__varmap;R#72;#73;E__ff;RA8;o53;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;#75;o27;#76;o28;#77;A8;o53;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;#75;o27;#78;o28;#77;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;#75;o27;A3;o57;i0;#78;#76;o28;#79;#80;P__x2;Ri0;P__x1;Ri0;P~R#0;P~R#0;A2;k1;o2;A2;k6;r3;r4;A4;r1;A1;k461;#63;A1;k461;A2;k460;#18;A1;k418;r37;r13;r14;#81;#81;EBL;RcdEheq_n;R#35;#34;Eheq_SS;R#38;#37;Ecstr;R#39;#40;E__sat15;R#42;#45;E__sat14;R#47;#48;E__sat13;RA2;k462;#18;#50;P~R#49;P~RA2;k1;o2;#51;A2;k1;o2;A2;k460;#18;A1;k418;r33;E__sat12;RA2;k130;#15;#83;P~R#43;P~RA2;k1;o2;#83;A2;k39;o2;#84;E__sat11;RLHa;R#46;L~Ri101;A3;k131;#15;#83;r2;PHa;R#46;P~Ri101;A2;k1;o2;#84;E__sat10;R#52;#53;E__sat9;R#54;#55;E__sat8;R#57;#59;E__sat7;R#60;#61;E__sat6;RA2;k462;#10;A1;k423;r38;P~R#62;P~RA2;k1;o2;#85;A2;k1;o2;A2;k460;#10;#86;E__arith;RL__x2;Ri0;L__x1;Ri0;E__wit;RA3;o41;i16;#89;A3;o41;i16;#89;A3;o41;i16;#89;A3;o41;i16;#89;A3;o41;i16;#89;#69;#70;E__varmap;R#72;#73;E__ff;RA8;o53;#74;k22;i23;i23;o24;A7;o68;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;A2;o26;i0;#2;o58;#76;o28;A7;o68;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;A2;o26;i0;#4;o58;#76;o28;A7;o68;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;A2;o26;i0;#6;o58;#76;o28;A7;o68;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;A2;o26;i0;#8;o58;#76;o28;A7;o68;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;A2;o26;i0;#10;o58;#76;o28;A5;o463;#74;k22;i23;i23;o24;#77;A8;o53;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;#78;o27;A3;o220;i0;#90;A1;o92;#16;o28;#77;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;#75;o27;A3;o57;i0;A3;o219;i0;A3;o220;i0;#90;A1;o92;#82;A3;o137;i0;#90;#78;A3;o219;i0;A2;o26;i0;#91;A3;o137;i0;#90;#76;o28;#79;#80;P__x2;Ri0;P__x1;Ri0;P~RA2;i67;A3;i5;i0;#2;r2;A2;i67;A3;i5;i0;#4;r2;A2;i67;A3;i5;i0;#6;r2;A2;i67;A3;i5;i0;#8;r2;A2;i67;A3;i5;i0;#10;r2;i75;P~RA2;k1;r2;#18;A2;k1;o2;A2;k6;A2;k73;#84;A2;k79;#15;r3;A2;k73;#91;A2;k79;#15;r4;A4;r1;#86;A1;k418;r40;r20;r26;#92;#92;EH;RA4;k464;#93;#20;r2;r6;A2;k1;o2;A2;k79;#93;#20;EH0;RA4;k464;#94;#22;r3;r6;A2;k1;o2;A2;k79;#94;#22;Eheq_n;R#35;#34;Eheq_SS;R#38;#37;Ecstr;R#39;#40;E__sat13;R#42;#45;E__sat12;R#47;#48;E__sat11;RA2;k462;#18;A1;k418;r34;P~R#49;P~RA2;k1;o2;A1;k418;r35;A2;k1;o2;A2;k460;#18;A1;k418;r36;E__sat10;R#52;#53;E__sat9;R#54;#55;E__sat8;R#57;#59;E__sat7;R#60;#61;E__sat6;RA2;k462;#10;#85;P~R#62;P~RA2;k1;o2;#86;A2;k1;o2;A2;k460;#10;A1;k423;r41;E__arith;RL__x8;Ri0;L__x7;Ri0;L__x6;Ri0;L__x5;Ri0;L__x4;Ri0;L__x3;Ri0;L__x2;Ri0;L__x1;Ri0;E__wit;RA3;o41;i16;A2;o42;A3;o43;i0;A3;o135;i0;A2;o44;i0;#95;#88;#68;o50;A3;o41;i16;A2;o42;A3;o43;i0;A2;o44;i0;N8;A3;o43;i0;A2;o44;i0;#96;A3;o43;i0;#65;#67;o50;#69;#70;E__varmap;RA4;o51;i0;A4;o51;i0;A4;o51;i0;#71;r5;A2;o52;i0;r6;r3;A4;o51;i0;#71;r9;A2;o52;i0;r8;r2;A4;o51;i0;A4;o51;i0;#71;r9;A2;o52;i0;r7;r4;A4;o51;i0;#71;r9;A2;o52;i0;r9;#73;E__ff;RA8;o53;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;#75;o27;#99;o28;#77;A8;o53;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;#75;o27;#102;o28;#77;A8;o53;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;#75;o27;#104;o28;#77;A8;o53;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;#75;o27;#97;o28;#77;A8;o53;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;#75;o27;#98;o28;#77;A8;o53;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;#75;o27;#101;o28;#77;A8;o53;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#104;#99;o27;A3;o219;i0;#106;#108;o28;#77;A8;o53;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;#102;o27;A3;o219;i0;#76;#78;o28;#77;A7;o54;#74;k22;i23;i23;o24;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;#78;o27;#76;o28;A7;o20;#74;k22;i23;i23;o24;A4;o25;i0;#108;o27;#106;o28;#79;#80;P__x8;Ri0;P__x7;Ri0;P__x6;Ri0;P__x5;Ri0;P__x4;Ri0;P__x3;Ri0;P__x2;Ri0;P__x1;Ri0;P~RA2;k1;o2;A2;k79;r5;r8;P~RA2;k1;o2;A2;k79;r6;r7;P~RA2;k1;o2;r9;P~R#13;P~RA2;k1;o2;r12;P~RA2;k1;o2;r11;P~RA2;k1;A2;k6;r13;A2;k79;r11;r14;A2;k73;r10;r9;P~RA2;k1;A2;k79;r12;r13;A2;k73;r9;r8;A2;i40;A2;k1;r9;r10;A2;k1;r11;r12;A16;r1;#22;A1;k455;r41;#20;A1;k453;r41;A3;k199;i0;i0;r42;r39;A3;k165;i0;i0;r42;r40;r13;r14;r15;r16;r19;r20;r22;r23;A2;i40;A2;k1;r22;A3;k165;i0;i0;r24;A2;k1;r21;A3;k199;i0;i0;r24;r2;r1;r2;r1;r2;r1;r2;r1;").
Qed.
Lemma rn_bound_sm : forall ps IS rep gp B, PML.ps_st ps = PML.ST_ACCEPT -> PMCS.rn_bound ps IS rep gp B -> PMCS.rn_bound (PMCUR.ps_set_more ps true) IS rep gp B.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S30;A2;i95;i0;i0;m95;RNLp0;RA2;i95;i0;i0;i0;r1;1;Lp;Ri0;Le;Ri0;A2;k73;r1;r2;m93;RNLx;RA1;i93;#0;i0;A1;k413;r8;2;Lp0;R#0;#1;o2;A2;k6;A1;k120;A2;k119;i0;A1;k420;r8;#2;A2;k62;r1;k468;A1;k469;A1;k415;r8;A3;k470;r7;r6;r5;A2;k11;A1;o4;Y1;0;A1;o4;Y4;a;A2;i40;A2;k39;r4;#7;A2;k1;o2;#2;A1;k414;r7;A1;k417;r8;m93;RNLx;RA1;i93;#0;i0;A1;k413;r7;2;Lp0;R#0;#1;o2;A2;k62;k465;k468;A3;k470;r6;r5;r4;A2;k39;r3;#7;m93;RNLx;RA1;i93;#0;i0;A1;k413;r10;2;Lp0;R#0;#1;o2;A2;k6;A1;k120;A2;k119;i0;A1;k420;r10;#15;A1;k469;A1;k415;r10;A3;k470;r9;r8;r7;A2;i40;A2;k39;r6;#7;A2;k1;o2;#15;m93;RNLx;RA1;i93;#0;i0;A1;k413;r11;2;Lp0;R#0;#1;o2;A2;k467;o32;#12;m93;RNLx;RA1;i93;#0;i0;A1;k413;r9;2;Lp0;R#0;#1;o2;A2;k6;A1;k120;A2;k119;i0;A1;k420;r9;#22;A1;k469;A1;k415;r9;A3;k470;r8;r7;r6;A2;i40;A2;k39;r5;#7;A2;k1;o2;#22;cdr1;A2;i40;A2;k1;A2;k6;A2;k6;#16;m31;RNL~Ri31;i0;#21;2;#17;o2;#18;r6;#19;A2;k450;r7;o32;m93;RNLx;RA1;i93;#0;i0;A1;k413;#28;2;Lp0;R#0;#1;o2;Lps;Ri241;LIS;Ri0;Lrep;Ri262;Lgp;Ri0;LB;Ri0;LHst;RA3;i5;i0;A1;k414;r5;k465;LH;RA5;k466;r6;r5;r4;r3;r2;cdcdA6;k9;i0;k465;Lz;Ri0;A2;i40;A2;k1;A2;k6;A2;k6;#3;m31;RNL~Ri31;i0;A2;k467;o32;#4;2;#5;o2;#6;r4;#8;EH;RA6;k35;i0;#9;Lz;Ri0;A2;i40;A2;k1;A2;k6;A2;k6;#3;m31;RNL~Ri31;i0;A2;k467;#10;#4;2;#5;o2;#6;r4;#8;r1;k465;r2;A2;i40;A2;k1;A2;k6;A2;k6;A2;k6;A1;k120;A2;k119;i0;A1;k420;r7;#11;m31;RNL~Ri31;i0;A2;k467;A1;k417;r7;#12;2;A1;k469;A1;k415;r7;o2;#13;r3;A2;i40;#14;A2;k1;o2;#11;Eb;R#10;i31;A1;m31;RNLb;Ri31;PH;RA2;i40;A2;k1;A2;k6;A2;k6;#16;m31;RNL~Ri31;i0;A2;k467;r1;#12;2;#17;o2;#18;r6;#19;A2;i40;A2;k1;A2;k6;A2;k6;A2;k6;A1;k120;A2;k119;i0;A1;k420;r11;#20;m31;RNL~Ri31;i0;#21;2;A1;k469;A1;k415;r11;o2;A3;k470;r10;r9;r8;r7;A2;i40;A2;k39;r7;#7;A2;k1;o2;#20;r1;2;LH;RA2;i40;A2;k1;A2;k6;A2;k6;#23;m31;RNL~Ri31;i0;#21;2;#24;o2;#25;r5;#26;#27;LH;RA2;i40;A2;k1;A2;k6;A2;k6;#23;m31;RNL~Ri31;i0;A2;k467;o403;#12;2;#24;o2;#25;r5;#26;#27;r2;#9;r2;A2;i40;A2;k1;A2;k6;A2;k6;A2;k6;A1;k120;A2;k119;i0;A1;k420;#28;#29;m31;RNL~Ri31;i0;A2;k467;A1;k417;#28;A2;k62;A1;k414;#28;k468;2;A1;k469;A1;k415;#28;o2;#13;r3;A2;i40;#14;A2;k1;o2;#29;A5;k466;#28;r6;r5;r4;r3;").
Qed.
Lemma win_ok_heap : forall (Ma Mb : mem) l l' LBh crx VM ps, PML.win_ok Ma l ps -> (forall b, In b l -> In b l') -> (forall b, In b l -> In b LBh) -> hi_heap HI LBh crx Mb VM ->
  PML.win_ok Mb l' ps.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S79;Y6;00;Y3;0;A1;i91;A1;o92;#1;P~RA1;i91;A1;o92;#0;A1;i93;#2;A2;i95;i0;i0;A1;i17;#4;A3;k84;#4;r2;r8;A1;o4;Y14;0000;A4;o96;i0;i0;r1;#7;A2;k1;r1;r3;A2;k6;r1;#7;A2;k1;r2;#10;A2;k73;r2;r3;m95;RNLp0;RA2;i95;i0;i0;pr1;1;Lp;Ri0;Le;Ri0;A2;i83;i0;Lch;Ri0;A2;i40;A3;k84;#4;#8;r16;A2;i40;#9;A2;i40;#11;A3;k214;r18;r3;#12;A2;i83;i0;Lch;Ri0;A2;i40;A3;k84;#4;#8;r17;A2;i40;#9;A2;i40;#11;A3;k214;r19;r3;#12;A3;k84;#4;#8;r19;A4;o96;i0;i0;r14;#7;A2;k1;r14;r19;A2;k1;r18;A2;k6;r14;#7;A3;k214;r35;r19;A2;k73;r18;r19;A2;i40;#18;#19;A3;k165;i0;i0;r2;A3;k199;i0;i0;r2;A3;k198;vL;#21;#22;A2;k165;i0;i0;A4;o96;i0;i0;r19;#7;A3;k165;i0;i0;#25;A3;k199;i0;i0;#25;A4;o96;i0;i0;r20;#7;A3;k165;i0;i0;#28;A3;k199;i0;i0;#28;A4;o96;i0;i0;r22;#7;A4;o96;i0;i0;r23;#7;A3;k165;i0;i0;#32;A3;k199;i0;i0;#32;A4;o96;i0;i0;r24;#7;A3;k165;i0;i0;#35;A3;k199;i0;i0;#35;A4;o96;i0;i0;r26;#7;A4;o96;i0;i0;r27;#7;A3;k165;i0;i0;#39;A2;k119;#2;vpayload;A1;k120;#41;A3;i5;i0;vn;#42;cdA2;o12;i0;#42;#43;A1;k258;vLay;A3;i5;i0;vSS;#45;cdA2;o12;i0;#45;#46;A1;k129;#41;A2;k1;o2;#42;Y1;0;A1;o4;#50;A1;o4;Y5;0f;A2;k130;#51;#52;A2;k39;o2;#51;A2;k11;#51;#52;P~R#54;P~RA2;k1;o2;#52;A2;k39;o2;#55;A2;k1;o2;#51;LHa;R#57;L~Ri101;A3;k131;#51;#52;r2;PHa;R#57;P~Ri101;A2;k1;o2;#55;A1;o4;Y4;a;A2;k130;#51;#60;A2;k11;#51;#60;P~R#54;P~RA2;k1;o2;#60;A2;k39;o2;#62;LHa;R#57;L~Ri101;A3;k131;#51;#60;r2;PHa;R#57;P~Ri101;A2;k1;o2;#62;A1;o15;i16;A1;i17;i16;A2;o52;i0;r3;A1;i19;i0;A1;i21;i0;A2;o55;i0;o48;A2;o55;i0;#50;A7;o20;#70;k22;i23;i23;o24;A4;o25;i0;#71;o27;#72;o28;A1;o56;i23;A2;k29;#70;o24;A4;k30;r1;r3;cvA2;o12;i31;o32;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;Y1;1;A3;o57;i0;A2;o55;i0;#77;A2;o26;i0;#7;LMa;R#3;LMb;R#3;Ll;R#5;Ll';R#5;LLBh;R#5;Lcrx;Rk173;LVM;Ri174;Lps;Ri241;LW;RA3;k471;r8;r6;r1;LHl';RPb;R#4;P~RA3;k84;#4;r1;r8;#6;LHin;RPb;R#4;P~RA3;k84;#4;r1;r9;#6;LHH;RA5;k180;vHI;r7;r6;r10;r5;cdEo;RA1;k413;r5;A1;i93;#4;A1;m93;RNLo;RA1;i93;#4;PW;Rm93;RNLx;RA1;i93;#4;pr1;2;Lp0;R#4;#13;i101;m93;RNLx;RA1;i93;#4;pr2;2;Lp0;R#4;#13;i101;r1;2;Lp;R#4;A1;Lp0;R#4;m95;RNLp;RA2;i95;i0;i0;PW;Rm95;RNLp0;RA2;i95;i0;i0;pr1;1;Lp;Ri0;Le;Ri0;#14;m95;RNLp0;RA2;i95;i0;i0;pr2;1;Lp;Ri0;Le;Ri0;#14;r1;1;Lz;Ri0;Lz;Ri0;A2;Lp;Ri0;Le;Ri0;LW;RA2;i83;i0;Lch;Ri0;A2;i40;A3;k84;#4;#8;r18;A2;i40;#9;A2;i40;#11;A3;k214;r20;r3;#12;m83;RNL~RA2;i83;i0;Lch;Ri0;A2;i40;#15;A2;i40;A2;k1;r1;r4;A2;i40;A2;k1;r3;#10;A3;k214;r21;r4;A2;k73;r3;r4;A2;i83;i0;Lch;Ri0;A2;i40;#15;A2;i40;A2;k1;r1;r5;A2;i40;A2;k1;r4;#10;A3;k214;r21;r5;A2;k73;r4;r5;r1;1;Lx;Ri0;L~RA1;Lch;Ri0;A2;i40;A3;k84;#4;#8;r20;A2;i40;A2;k1;r1;r5;A2;i40;A2;k1;r4;#10;A3;k214;r22;r5;A2;k73;r4;r5;r1;A2;Lc;Ri0;LH;RA2;i40;A3;k84;#4;#8;r21;A2;i40;A2;k1;r1;r6;A2;i40;A2;k1;r5;#10;A3;k214;r23;r6;A2;k73;r5;r6;m40;RNL~RA2;i40;A3;k84;#4;A4;o96;i0;i0;r2;#7;r22;A2;i40;A2;k1;r2;r7;A2;i40;A2;k1;r6;A2;k6;r2;#7;A3;k214;r24;r7;A2;k73;r6;r7;A2;i83;i0;Lch;Ri0;A2;i40;A3;k84;#4;#8;r23;A2;i40;A2;k1;r1;r9;A2;i40;A2;k1;r8;#10;A3;k214;r25;r9;A2;k73;r8;r9;r1;1;L~RA3;k84;#4;A4;o96;i0;i0;r2;#7;r22;L~RA2;i40;A2;k1;r3;r8;A2;i40;A2;k1;r7;A2;k6;r3;#7;A3;k214;r25;r8;A2;k73;r7;r8;A2;LH1;RA3;k84;#4;A4;o96;i0;i0;r4;#7;r24;LH;RA2;i40;A2;k1;r5;r10;A2;i40;A2;k1;r9;A2;k6;r5;#7;A3;k214;r27;r10;A2;k73;r9;r10;m40;RNL~RA2;i40;A2;k1;r6;r11;A2;i40;A2;k1;r10;A2;k6;r6;#7;A3;k214;r28;r11;A2;k73;r10;r11;A2;i83;i0;Lch;Ri0;A2;i40;A3;k84;#4;#8;r27;A2;i40;A2;k1;r1;r13;A2;i40;A2;k1;r12;#10;A3;k214;r29;r13;A2;k73;r12;r13;r1;1;L~RA2;k1;r6;r11;L~RA2;i40;A2;k1;r11;A2;k6;r7;#7;A3;k214;r29;r12;A2;k73;r11;r12;A2;LH2;RA2;k1;r8;r13;LH;RA2;i40;A2;k1;r13;A2;k6;r9;#7;A3;k214;r31;r14;A2;k73;r13;r14;m40;RNL~RA2;i40;A2;k1;r14;A2;k6;r10;#7;A3;k214;r32;r15;A2;k73;r14;r15;A2;i83;i0;Lch;Ri0;A2;i40;A3;k84;#4;#8;r31;A2;i40;A2;k1;r1;r17;A2;i40;A2;k1;r16;#10;A3;k214;r33;r17;A2;k73;r16;r17;r1;1;L~RA2;k1;r14;A2;k6;r10;#7;L~RA3;k214;r33;r16;A2;k73;r15;r16;A2;LH3;RA2;k1;r16;A2;k6;r12;#7;L_H;RA3;k214;r35;r18;A2;k73;r17;r18;A4;o78;i0;Lch;Ri0;A2;i40;A3;k84;#4;#8;r34;A2;i40;A2;k1;r1;r20;A2;i40;A2;k1;r19;#10;A3;k214;r36;r20;A2;k73;r19;r20;r14;A4;o88;A3;k84;#4;#16;r33;A2;i40;#17;#20;A2;r27;#16;r10;A4;o88;#17;#20;r6;A4;o88;#18;#19;r2;Ea;RA9;k197;vL;A1;k179;vSCFG_P;vHI;vHIok;r32;r31;r35;r30;r25;A2;i40;Pb;R#4;P~RA3;k84;#4;r1;r33;A2;i40;#23;A2;i40;A3;k200;r37;#21;#22;A3;k201;#21;#22;A2;k171;#21;r34;A2;i40;A2;i163;i0;A4;k164;#4;i0;#24;r32;A2;i40;A2;k1;o2;A3;k165;i0;i0;r31;A2;k1;o2;A3;k199;i0;i0;r31;m40;RNL~RA2;i40;Pb;R#4;P~RA3;k84;#4;r1;r34;A2;i40;#23;A2;i40;A3;k200;r38;#21;#22;A3;k201;#21;#22;A2;k171;#21;r35;A2;i40;A2;i163;i0;A4;k164;#4;i0;#24;r33;A2;i40;A2;k1;o2;A3;k165;i0;i0;r32;A2;k1;o2;A3;k199;i0;i0;r32;A3;k214;r37;r21;A2;k73;r20;r21;r1;1;L~RPb;R#4;P~RA3;k84;#4;r1;r34;A2;i40;#23;A2;i40;A3;k200;r38;#21;#22;A3;k201;#21;#22;A2;k171;#21;r35;L~RA2;i40;A2;i163;i0;A4;k164;#4;i0;#24;r34;A2;i40;A2;k1;o2;A3;k165;i0;i0;r33;A2;k1;o2;A3;k199;i0;i0;r33;A2;LHwf;RPb;R#4;P~RA3;k84;#4;r1;r36;A2;i40;#23;A2;i40;A3;k200;r40;#21;#22;A3;k201;#21;#22;A2;k171;#21;r37;L_H;RA2;i40;A2;i163;i0;A4;k164;#4;i0;#24;r36;A2;i40;A2;k1;o2;A3;k165;i0;i0;r35;A2;k1;o2;A3;k199;i0;i0;r35;Ea;RA2;r2;#25;A2;r31;#25;r15;A2;i40;A3;k198;vL;#26;#27;A2;i40;A3;k200;r40;#26;#27;A3;k201;#26;#27;A2;k171;#26;r37;m40;RNL~RA2;i40;A3;k198;vL;#29;#30;A2;i40;A3;k200;r41;#29;#30;A3;k201;#29;#30;A2;k171;#29;r38;A3;k214;r42;r26;A2;k73;r25;r26;r1;1;L~RA3;k198;vL;#29;#30;L~RA2;i40;A3;k200;r42;A3;k165;i0;i0;A4;o96;i0;i0;r21;#7;A3;k199;i0;i0;A4;o96;i0;i0;r21;#7;A3;k201;A3;k165;i0;i0;A4;o96;i0;i0;r21;#7;A3;k199;i0;i0;A4;o96;i0;i0;r21;#7;A2;k171;A3;k165;i0;i0;A4;o96;i0;i0;r21;#7;r39;A2;L_H;RA3;k198;vL;A3;k165;i0;i0;#31;A3;k199;i0;i0;#31;LH;RA2;i40;A3;k200;r44;#33;#34;A3;k201;#33;#34;A2;k171;#33;r41;m40;RNL~RA2;i40;A3;k200;r45;#36;#37;A3;k201;#36;#37;A2;k171;#36;r42;A3;k214;r46;r30;A2;k73;r29;r30;r1;1;L~RA3;k200;r45;#36;#37;L~RA3;k201;A3;k165;i0;i0;A4;o96;i0;i0;r25;#7;A3;k199;i0;i0;A4;o96;i0;i0;r25;#7;A2;k171;A3;k165;i0;i0;A4;o96;i0;i0;r25;#7;r43;A2;LD;RA3;k200;r47;A3;k165;i0;i0;#38;A3;k199;i0;i0;#38;L_H0;RA3;k201;#40;A3;k199;i0;i0;#39;A2;k171;#40;r45;A8;k472;r49;r28;#7;r33;A2;k73;r32;r33;r2;Eheq_n;R#44;#43;Eheq_SS;R#47;#46;Ecstr;R#48;#49;E__sat7;R#53;#56;E__sat6;R#58;#59;E__sat5;R#61;#63;E__sat4;R#64;#65;E__arith;RL__x2;Ri0;L__x1;Ri0;E__wit;R#66;#67;E__varmap;RA4;o51;i0;#68;r2;A1;o18;i0;#69;E__ff;RA8;o53;#70;k22;i23;i23;o24;#73;#74;#73;#75;#76;P__x2;Ri0;P__x1;Ri0;P~RA2;k1;r1;r2;A2;k1;r2;r3;A3;r1;r41;r36;r28;Eheq_n;R#44;#43;Eheq_SS;R#47;#46;Ecstr;R#48;#49;E__sat7;R#53;#56;E__sat6;R#58;#59;E__sat5;R#61;#63;E__sat4;R#64;#65;E__arith;RL__x3;Ri0;L__x2;Ri0;L__x1;Ri0;E__wit;R#66;#67;E__varmap;RA4;o51;i0;#68;r2;A2;o52;i0;r4;#69;E__ff;RA8;o53;#70;k22;i23;i23;o24;A7;o20;#70;k22;i23;i23;o24;A4;o25;i0;#72;o27;#78;o28;#74;A7;o20;#70;k22;i23;i23;o24;A4;o25;i0;A3;o57;i0;#71;A3;o219;i0;#72;#71;o27;#78;o28;#75;#76;P__x3;Ri0;P__x2;Ri0;P__x1;Ri0;P~RA2;k1;r2;A2;k6;r3;#7;A2;k1;A2;k6;r2;A2;k73;r3;r2;A2;k6;r4;#7;A4;r1;r36;r40;r41;r24;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r2;r1;r1;LW;Ri101;o102;r5;A3;k471;r11;r9;r5;").
Qed.

Lemma ev_lvl0 : forall ps w0 e, PMCUR.wf_c (PMCUR.ps_set_more ps true) -> PMCUR.ev_rel 0 w0 ps e ->
  (PMCS.conv_ok e -> PML.ps_st ps = PML.ST_ACCEPT) /\ match e with PMCUR.EvKey _ _ | PMCUR.EvEndObj | PMCUR.EvEndArr => False | _ => True end.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S83;A2;k450;r4;o32;A1;k478;r9;A3;i5;i0;A1;k412;r10;o2;A1;k414;r11;A1;k414;r12;A3;i5;i0;#4;k465;A1;k414;r13;A1;k414;r14;A3;i5;i0;#7;k465;A1;k414;r15;A3;i5;i0;#9;k465;A2;o12;i31;o32;A3;k84;i0;r1;k479;A2;k1;o2;vn;Y1;0;A1;o4;#14;A1;o4;Y4;a;A2;k11;#15;#16;A2;k39;vn;#17;A3;i5;i0;k447;k447;A2;i67;A3;i5;i0;k480;k447;A2;i67;A3;i5;i0;k481;k447;A2;i67;A3;i5;i0;k482;k447;A2;i67;A3;i5;i0;k483;k447;A2;i67;A3;i5;i0;k484;k447;A2;i67;A3;i5;i0;k485;k447;i75;A2;i67;#19;#20;A1;k210;vL;A2;k1;A1;o4;Y46;3fff80000000;#22;A1;o4;Y5;0f;A2;k11;#15;#24;A2;k1;#22;#25;A1;k414;r19;A1;o4;o48;A1;k412;r20;A1;k414;r20;A1;k414;r21;A3;k84;i0;#31;k479;A2;i83;i0;Lx;Ri0;A2;i40;A3;k84;i0;r1;A1;k422;r23;#12;A1;k412;r22;A1;k414;r23;A1;k412;r23;A1;k412;r15;A2;k119;A1;i91;A1;o92;Y3;0;vpayload;A1;k120;#38;A3;i5;i0;vn;#39;cdA2;o12;i0;#39;#40;A1;k258;vLay;A3;i5;i0;vSS;#42;cdA2;o12;i0;#42;#43;A1;k129;#38;A2;k1;o2;#39;A2;k130;#15;#24;A2;k39;o2;#15;P~R#48;P~RA2;k1;o2;#24;A2;k39;o2;#25;A2;k1;o2;#15;LHa;R#50;L~Ri101;A3;k131;#15;#24;r2;PHa;R#50;P~Ri101;A2;k1;o2;#25;A2;k130;#15;#16;P~R#48;P~RA2;k1;o2;#16;A2;k39;o2;#17;LHa;R#50;L~Ri101;A3;k131;#15;#16;r2;PHa;R#50;P~Ri101;A2;k1;o2;#17;A1;o15;i16;A1;i17;i16;A1;o18;i0;A1;i19;i0;A1;i21;i0;A2;o26;i0;#28;Y2;3;A2;o55;i0;#63;A1;o56;i23;A2;o26;i0;o2;A6;o69;#61;k22;i23;i23;o24;r4;A2;k29;#61;o24;A4;k30;r1;r3;cv#11;A3;i5;i31;A2;k33;r1;r3;o32;A3;k34;i0;o2;r2;A3;i5;i0;A1;k414;r16;k465;A3;i5;i0;#6;k465;A1;k478;r14;A1;k478;r16;A4;o88;P~Ri101;#8;i101;L_H;Ri101;m40;RNL~RA2;i40;#72;A3;i5;i0;A1;k412;r14;o2;#10;r2;1;L~R#72;L~RA3;i5;i0;A1;k412;r15;o2;A2;LA;R#73;LB;RA3;i5;i0;A1;k412;r17;o2;A2;r9;r2;r1;r2;r1;o102;A1;k412;r19;A4;k492;r22;r23;r11;r10;A6;o69;#61;k22;i23;i23;o24;r3;A7;o20;#61;k22;i23;i23;o24;A4;o25;i0;#62;o27;#66;o28;A6;o69;#61;k22;i23;i23;o24;r5;A2;k1;#28;o2;Eheq_n;R#41;#40;Eheq_SS;R#44;#43;Ecstr;R#45;#46;E__sat4;R#47;#49;E__sat3;R#51;#52;E__sat2;R#53;#54;E__sat1;R#55;#56;E__arith;RL__p1;RpE__wit;R#57;#58;E__varmap;R#59;#60;E__ff;RA7;o54;#61;k22;i23;i23;o24;A8;o53;#61;k22;i23;i23;o24;A5;o463;#61;k22;i23;i23;o24;#65;#77;A5;o495;#61;k22;i23;i23;o24;#68;#69;P__p1;RpA2;i40;P~Ri75;r2;i101;A1;r1;A3;i5;i0;#27;k465;Eheq_n;R#41;#40;Eheq_SS;R#44;#43;Ecstr;R#45;#46;E__sat4;R#47;#49;E__sat3;R#51;#52;E__sat2;R#53;#54;E__sat1;R#55;#56;E__arith;RL__p3;RpL__p2;RpL__p1;RpE__wit;R#57;#58;E__varmap;R#59;#60;E__ff;RA8;o53;#61;k22;i23;i23;o24;A7;o54;#61;k22;i23;i23;o24;#77;A7;o54;#61;k22;i23;i23;o24;#67;#78;#65;#79;#68;#69;P__p3;RpP__p2;RpP__p1;RpP~RA2;i40;r1;A2;i40;r2;#80;r4;A4;r1;A2;i40;P~Ri75;A3;i5;i0;#30;k465;i75;A3;i5;i0;#75;A2;k73;o2;#28;A1;k478;r19;r9;Lps;Ri241;Lw0;RA1;i93;A2;i95;i0;i0;Le;Ri473;LH;RA1;k474;A2;k450;r3;o32;m40;RNL~RA2;i40;A1;k441;#0;A1;k475;#0;P~RA4;k476;o2;r4;r5;r3;A2;i40;P~RA1;k477;r4;A3;i5;i0;A1;k414;r7;k465;m473;RNLe;Ri473;pr4;11;i101;Lb;Ri31;i101;Lv;Ri0;i101;Lv;Ri0;i101;Lbits;Ri0;i101;Lp;Ri0;Ln0;Ri0;i101;Lp;Ri0;Ln0;Ri0;i75;i101;i75;i101;i75;r1;1;L~RA1;k441;#0;L~RA1;k475;A2;k450;r5;o32;A2;L_H;RA1;k441;A2;k450;r6;o32;LLV;RA1;k475;A2;k450;r7;o32;LHR;RA4;k476;o2;r7;r8;r6;EAV;RLA;R#1;LHl;R#2;m67;RNL~RA2;i67;A3;i5;i0;k465;#3;A2;i67;A3;i5;i0;k447;#3;i75;#5;r2;2;L~RA3;i5;i0;k465;#3;A1;LA;RA3;i5;i0;k465;#4;A4;k161;i0;k465;#6;r1;r1;L~RA2;i67;A3;i5;i0;k447;#3;i75;A1;LH;RA2;i67;A3;i5;i0;k447;#4;i75;m67;RNL~RA2;i67;A3;i5;i0;k447;#6;i75;#8;r1;2;L~RA3;i5;i0;k447;#6;A1;LA;RA3;i5;i0;k447;#7;A2;k86;#10;EX;RA2;r8;#11;A3;o89;A3;k84;i0;#9;k479;A2;i83;i0;Lx;Ri0;A2;i40;A3;k84;i0;r1;A1;k422;r16;#12;A6;k35;i0;k447;Lz;Ri0;#12;cdA5;k147;#13;#18;#21;LH;R#13;LH0;R#18;A5;k147;#23;#26;#21;LH1;R#23;LH2;R#26;EH3;REH3;R#11;A3;i5;i31;o32;o32;A1;r13;r1;P~RA2;i67;A3;k84;i0;#27;k479;A2;i83;i0;Lx;Ri0;A2;i40;A3;k84;i0;r1;A1;k422;r20;#12;A2;k1;#28;#29;A1;LH3;RP~RA2;i67;A3;k84;i0;#30;k479;A2;i83;i0;Lx;Ri0;A2;i40;A3;k84;i0;r1;A1;k422;r21;#12;A2;k1;#28;A1;k412;r21;EH4;RLH4;R#32;A1;r2;A3;o89;A3;k84;i0;A1;k414;r22;k479;#33;r1;P~R#32;A2;k1;#28;#34;EH5;RLH5;R#33;A1;r3;A3;o90;A3;k84;i0;#35;k479;A2;i83;i0;Lx;Ri0;A2;i40;A3;k84;i0;r1;A1;k422;r24;#12;r1;P~R#33;A2;k1;#28;#36;A3;o89;#19;#20;A2;o12;i0;k447;r1;vHtop;vPlen;A3;k84;i0;k447;k479;#9;r1;A2;k1;#28;#37;Eheq_n;R#41;#40;Eheq_SS;R#44;#43;Ecstr;R#45;#46;E__sat4;R#47;#49;E__sat3;R#51;#52;E__sat2;R#53;#54;E__sat1;R#55;#56;E__arith;RL__p1;RpL__x1;Ri0;E__wit;R#57;#58;E__varmap;RA4;o51;i0;#59;r2;A4;o51;i0;#59;r2;A2;o52;i0;r2;#60;E__ff;RA8;o53;#61;k22;i23;i23;o24;A7;o20;#61;k22;i23;i23;o24;A4;o25;i0;#62;o27;#64;o28;#65;A8;o53;#61;k22;i23;i23;o24;A7;o20;#61;k22;i23;i23;o24;A4;o25;i0;#64;o58;#66;o28;#65;#67;#68;#69;P__p1;RpP__x1;Ri0;P~RA2;k1;#28;r1;P~RA3;i5;i0;r2;o2;r4;A4;r1;i75;A1;k412;r24;r9;r14;r1;L~Ri75;A1;LH;Ri75;m75;RNL~Ri75;#70;r1;0;r1;r1;P~R#1;P~R#2;A3;i5;i0;#3;k465;A1;m473;RNLs;Ri473;PHR;RA4;k476;o2;r10;r11;r1;A2;i40;P~RA1;k477;r2;#71;m473;RNLe;Ri473;pr2;11;i101;Lb;Ri31;i101;Lv;Ri0;i101;Lv;Ri0;i101;Lbits;Ri0;i101;Lp;Ri0;Ln0;Ri0;i101;Lp;Ri0;Ln0;Ri0;i75;i101;i75;i101;i75;r8;11;LHR;RA4;k476;o2;r9;r10;o486;cdA4;o88;P~Ri101;#5;i101;L_H;Ri101;m40;RNL~RA2;i40;A1;k478;r12;A3;i5;i0;A1;k412;r12;o2;#71;r2;1;L~RA1;k478;r12;L~RA3;i5;i0;A1;k412;r13;o2;A2;LA;R#72;LB;RA3;i5;i0;#37;o2;A2;r7;r2;r1;r2;r1;o102;A2;i40;P~RA1;k477;o486;#5;i101;Lb;Ri31;A1;Lb;Ri31;LHR;RA4;k476;o2;r11;r12;A1;o487;r1;cd#74;A2;i40;P~RA1;k477;A1;o487;r2;#8;i101;r1;Lv;Ri0;A1;Lv;Ri0;LHR;RA4;k476;o2;r11;r12;A1;o488;r1;cd#74;A2;i40;P~RA1;k477;A1;o488;r2;#8;i101;r1;Lv;Ri0;A1;Lv;Ri0;LHR;RA4;k476;o2;r11;r12;A1;o489;r1;cd#74;A2;i40;P~RA1;k477;A1;o489;r2;#8;i101;r1;Lbits;Ri0;A1;Lbits;Ri0;LHR;RA4;k476;o2;r11;r12;A1;o490;r1;cd#74;A2;i40;P~RA1;k477;A1;o490;r2;#8;i101;r1;Lp;Ri0;Ln;Ri0;A2;Lp;Ri0;Ln0;Ri0;LHR;RA4;k476;o2;r13;r14;A2;o491;r2;r1;cdA4;o88;P~Ri101;#70;i101;L_H;Ri101;m40;RNL~RA2;i40;#73;A2;i40;A3;i5;i0;A1;k412;r16;o2;A4;k492;r15;r16;r4;r3;A3;i5;i0;A1;k414;r17;k465;r2;1;L~R#73;L~RA2;i40;A3;i5;i0;A1;k412;r17;o2;A4;k492;r16;r17;r5;r4;A2;LA;RA1;k478;r18;LH;RA2;i40;A3;i5;i0;#75;o2;A4;k492;r18;r19;r7;r6;m40;RNL~RA2;i40;A3;i5;i0;#29;o2;A4;k492;r19;r20;r8;r7;A3;i5;i0;#31;k465;r1;1;L~RA3;i5;i0;#29;o2;L~RA4;k492;r20;r21;r9;r8;A2;LB;RA3;i5;i0;#34;o2;L_H;R#76;A2;r15;r6;r2;r2;r1;r2;r1;o102;A2;i40;P~RA1;k477;A2;o491;r3;r2;#70;i101;r2;r1;Lp;Ri0;Ln;Ri0;A2;Lp;Ri0;Ln0;Ri0;LHR;RA4;k476;o2;r13;r14;A2;o493;r2;r1;cdEheq_n;R#41;#40;Eheq_SS;R#44;#43;Ecstr;R#45;#46;E__sat4;R#47;#49;E__sat3;R#51;#52;E__sat2;R#53;#54;E__sat1;R#55;#56;E__arith;RL__p4;RpL__p3;RpL__p2;RpL__p1;RpE__wit;R#57;#58;E__varmap;R#59;#60;E__ff;RA8;o53;#61;k22;i23;i23;o24;A7;o54;#61;k22;i23;i23;o24;#77;A7;o54;#61;k22;i23;i23;o24;#67;A7;o54;#61;k22;i23;i23;o24;#78;#79;#65;A6;o69;#61;k22;i23;i23;o24;r6;#68;#69;P__p4;RpP__p3;RpP__p2;RpP__p1;RpP~RA2;i40;r1;A2;i40;r2;A2;i40;#80;r3;r5;A5;r1;A2;i40;P~Ri101;A3;i5;i0;A1;k414;r24;k465;i75;#76;A3;i5;i0;#36;o2;A3;i5;i0;#35;k482;r9;A2;i40;P~RA1;k477;A2;o493;r3;r2;#70;i75;r2;r1;LHR;RA4;k476;o2;r9;r10;o494;cd#81;A2;i40;P~RA1;k477;o494;#5;i101;LHR;RA4;k476;o2;r9;r10;o496;cd#82;A2;i40;P~RA1;k477;o496;#5;i75;LHR;RA4;k476;o2;r9;r10;o497;cd#81;A2;i40;P~RA1;k477;o497;#5;i101;LHR;RA4;k476;o2;r9;r10;o498;cd#82;A2;i40;P~RA1;k477;o498;#5;i75;r2;r2;r1;").
Qed.

Ltac bd_inn := auto 30 using in_or_app, in_cons, in_eq.
Ltac bd_brk H := repeat match type of H with | In _ (_ ++ _) => apply in_app_or in H; destruct H as [H|H] | In _ (_ :: _) => destruct H as [<-|H] end.
Ltac bd_in := let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; bd_inn.
Lemma bd_rp_csr : forall Ra Rb : bvmap 5 word, regs_preserved Ra Rb -> TK.keepsR CK.CSR Ra Rb.
Proof.
  intros Ra Rb H. apply TK.keepsR_preserved; [exact H|]. intros q Hq. unfold CK.CSR in Hq. unfold callee_saved_idx.
  repeat (destruct Hq as [<-|Hq]; [ck_in|]). destruct Hq.
Qed.
Lemma bd_lbr_rest : forall (A : list (Z * Z)) x c l, incl l (lb_remove x (A ++ (x, c) :: l)).
Proof.
  induction A as [|a A IH]; intros x c l b Hb.
  - cbn [app lb_remove fst]. rewrite Z.eqb_refl. exact Hb.
  - cbn [app lb_remove]. destruct (Z.eqb (fst a) x).
    + apply in_or_app. right. apply in_cons. exact Hb.
    + apply in_cons. exact (IH x c l b Hb).
Qed.
Lemma bd_scap : forall s, In s [66; 132; 264; 528; 1056] -> 0 < s <= 4096.
Proof. intros s H. cbn [In] in H. lia. Qed.

Lemma bd_rn : forall (fx3 : FPState) R3 M3 model3 cr3 g3 reps rep r2 ps3 ch bof3 dn3 code gp3 rd3 w p,
  PML.fp_ok fx3 -> getr R3 2%bv = Z_to_bv 64 (sp - 1040) -> TK.keepsR HCS.KOH R R3 -> getr R3 18%bv = Z_to_bv 64 2 ->
  0 <= w < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> L5.u64_at RSEGS M3 (sp - 1032) w -> L5.u64_at RSEGS M3 (sp - 1016) p -> Z.land (w mod 256) 1 = sbit r2 ->
  PML.str_at_w M3 (sp - 1032) r2 ->
  pers reps M3 -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) -> (forall b, In b (PML.srep_blocks rep) -> 0 <= snd b <= n + 52) ->
  TK2.FR L LB sp SS PML.in_foot11 M M3 -> model_but_vm model model3 -> PML.model_ok model3 ->
  hi_heap HI (PML.srep_blocks r2 ++ PML.ps_blocks ps3 ++ (ch, 16384) :: PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) cr3 M3 (m_vmmaps model3) ->
  PML.ls_ok g3 M3 -> credit_le (credit_sub cr (ll_credit Lay n)) cr3 ->
  PMCS.cursor_at M3 (sp - 1008) (sp - 328) ch bof3 dn3 ps3 -> 0 < PML.ps_scap ps3 <= 4096 -> PML.isrc_at M3 (sp - 328) rep gp3 rd3 -> PML.ec_at M3 (sp - 344) code ->
  (PML.ps_done ps3 = true \/ dn3 = true \/ code <> 0) ->
  srealizes RSEGS SCFG (@PML.cfg fx3 R3 HCT.R_RN M3 model3) K.
Proof.
  intros fx3 R3 M3 model3 cr3 g3 reps rep r2 ps3 ch bof3 dn3 code gp3 rd3 w p Hfp H2 HKO H18 Hw Hp W1 W2 SB STR PRS BR BP FR3 BV3 MOK3 HH3 LS3 CLE CUR3 SCAP ISR3 EC3 DONE.
  pose proof MOK3 as (Hh & Hl & Hm).
  pose proof CUR3 as (_ & PA3 & _ & DN3 & DEF3).
  pose proof PA3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PD212 & _).
  pose proof EC3 as (EC3a & EC3d & EC3c).
  assert (Hcode : 0 <= code < 2 ^ 31) by (destruct EC3c as [X|(X & _)]; lia).
  assert (F460 : L5.u8_at RSEGS M3 (sp - 476) (PML.b2z (PML.ps_done ps3))) by (replace (sp - 476) with (sp - 1008 + 320 + 212) by lia; exact PD212).
  assert (F352 : L5.u8_at RSEGS M3 (sp - 368) (PML.b2z dn3)) by (replace (sp - 368) with (sp - 1008 + 640) by lia; exact DN3).
  assert (D992 : L5.defined M3 (sp - 1008) 8) by (intros i Hi; apply DEF3; unfold PMCS.CURSOR_SIZE; lia).
  assert (D344 : L5.defined M3 (sp - 360) 8) by (intros i Hi; replace (sp - 360 + i) with (sp - 1008 + (648 + i)) by lia; apply DEF3; unfold PMCS.CURSOR_SIZE; lia).
  pose proof SPOK as (SP1 & Hal).
  assert (Htop47 : hl_sptop L <= 2 ^ 47) by lia.
  pose proof SCRv as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH3) as BOK3.
  apply (HCS.s_h_rrn FPM fx3 R3 M3 model3 K sp w p (PML.b2z (PML.ps_done ps3)) (PML.b2z dn3) code Hh Hl Hfp H2 SPOK Hw Hp (b2z_rng _) (b2z_rng _) ltac:(lia)
           W1 W2 F460 F352 EC3a D992 D344).
  intros fx4 R4 M4 Hfp4 H2b H10b HK4 AG4 MG4.
  pose proof (kex_out M3 M4 AG4) as AGo.
  assert (FW : forall w0 : L5.range, In w0 [(sp - 1008, 8); (sp - 360, 8)] -> sp - SS <= fst w0 /\ fst w0 + snd w0 <= sp - 56 /\ 0 <= snd w0).
  { intros w0 Hw0. cbn [In] in Hw0. destruct Hw0 as [<-|[<-|[]]]; cbn [fst snd]; lia. }
  assert (PRSin : forall b, In b (PML.srep_blocks reps) -> In b (PML.srep_blocks r2 ++ PML.ps_blocks ps3 ++ (ch, 16384) :: PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB)) by bd_in.
  destruct (step_out_g _ reps M3 M4 _ cr3 model3 AGo MG4 FW PRSin PRS FR3 HH3) as (PRS4 & FR4 & HH4 & SC4 & WSI4).
  assert (A1 : getr R4 10%bv = Z_to_bv 64 (sbit r2)) by (rewrite H10b, SB; reflexivity).
  assert (A2 : TK.keepsR HCS.KOH R R4) by exact (KT R R3 R4 HKO (KCO R3 R4 HK4)).
  assert (A3 : getr R4 18%bv = Z_to_bv 64 2) by (rewrite (HK4 18%bv ltac:(ck_in)); exact H18).
  assert (A4 : PML.str_at_w M4 (sp - 1032) r2).
  { apply (TK2.str_at_w_x _ _ _ AGo (sp - 1032) r2 ltac:(lia)); [|exact STR].
    apply (TK2.str_cov_out L LAY _ (sp - 1032) r2 Htop47); [intros i Hi; ow | exact WSI4 | intros b Hb; apply BOK3; bd_inn]. }
  assert (A5 : PML.ls_ok g3 M4) by exact (TK2.ls_ok_x _ _ _ AGo SC4 g3 LS3).
  assert (A6 : PMCS.cursor_at M4 (sp - 1008) (sp - 328) ch bof3 dn3 ps3).
  { apply (cursor_at_xd _ M3 M4 (sp - 1008) (sp - 328) ch bof3 dn3 ps3 AGo ltac:(lia)); [intros i Hi; ow | | exact (frame_def M4 (sp - 1008) 656 FR4 ltac:(lia) ltac:(lia)) | exact CUR3].
    apply (TK2.ps_cov_out L LAY _ ps3 Htop47 WSI4). intros b Hb. apply BOK3. bd_inn. }
  assert (A7 : PML.isrc_at M4 (sp - 328) rep gp3 rd3).
  { apply (TK2.isrc_at_x _ _ _ AGo (sp - 328) rep gp3 rd3 ltac:(lia)); [intros i Hi; ow | | exact ISR3].
    apply (TK2.str_cov_out L LAY _ (sp - 328 + 80) rep Htop47); [intros i Hi; ow | exact WSI4 | intros b Hb; apply BOK3; bd_inn]. }
  assert (A8 : PML.u32 M4 (sp - 344) code) by (apply (TK2.u32_x _ _ _ AGo (sp - 344) code ltac:(lia)); [intros i Hi; ow | exact EC3a]).
  exact (brs2 fx4 R4 M4 model3 cr3 g3 reps rep r2 ps3 ch bof3 dn3 code gp3 rd3 Hfp4 H2b A1 A2 A3 A4 PRS4 BR BP FR4 BV3 MOK3 HH4 A5 CLE A6 SCAP A7 A8 Hcode DONE).
Qed.

Lemma bd_g11 : forall (fx1 : FPState) R1 M1 model1 cr1 g1 reps rep r2 ps ch bof gp rd,
  PML.fp_ok fx1 -> getr R1 2%bv = Z_to_bv 64 (sp - 1040) -> TK.keepsR HCS.KOH R R1 -> getr R1 18%bv = Z_to_bv 64 2 ->
  PML.str_at_w M1 (sp - 1032) r2 ->
  pers reps M1 -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) -> (forall b, In b (PML.srep_blocks rep) -> 0 <= snd b <= n + 52) ->
  TK2.FR L LB sp SS PML.in_foot11 M M1 -> model_but_vm model model1 -> PML.model_ok model1 ->
  hi_heap HI (PML.srep_blocks r2 ++ PML.ps_blocks ps ++ (ch, 16384) :: PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) cr1 M1 (m_vmmaps model1) ->
  PML.ls_ok g1 M1 -> credit_le (credit_sub cr (ll_credit Lay n)) cr1 ->
  PMCS.cursor_at M1 (sp - 1008) (sp - 328) ch bof false ps -> 0 < PML.ps_scap ps <= 4096 -> PML.isrc_at M1 (sp - 328) rep gp rd -> PML.u32 M1 (sp - 344) 11 ->
  srealizes RSEGS SCFG (@PML.cfg fx1 R1 HCT.R_GET M1 model1) K.
Proof.
  intros fx1 R1 M1 model1 cr1 g1 reps rep r2 ps ch bof gp rd Hfp H2 HKO H18 STR PRS BR BP FR1 BV1 MOK1 HH1 LS1 CLE CUR1 SCAP ISR1 E11.
  pose proof MOK1 as (Hh & Hl & Hm).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH1) as BOK1.
  assert (BLK : forall b, In b (PML.srep_blocks r2) -> block_range L (fst b) (snd b)) by (intros b Hb; apply BOK1; bd_inn).
  destruct (sbit_word M1 (sp - 1032) r2 FR1 ltac:(lia) ltac:(lia) STR BLK) as (w & p & Hw & Hp & W1 & W2 & SB).
  assert (W2' : L5.u64_at RSEGS M1 (sp - 1016) p) by (replace (sp - 1016) with (sp - 1032 + 16) by lia; exact W2).
  apply (HCS.s_h_g11 FPM fx1 R1 M1 model1 K sp w p Hh Hl Hfp H2 SPOK Hw Hp W1 W2' E11).
  intros fx2 R2 M2 Hfp2 H2b H10b HK2 AG2 MG2. apply samem_all in AG2. subst M2.
  assert (A1 : getr R2 10%bv = Z_to_bv 64 (sbit r2)) by (rewrite H10b, SB; reflexivity).
  assert (A2 : TK.keepsR HCS.KOH R R2) by exact (KT R R1 R2 HKO (KCO R1 R2 HK2)).
  assert (A3 : getr R2 18%bv = Z_to_bv 64 2) by (rewrite (HK2 18%bv ltac:(ck_in)); exact H18).
  assert (A4 : 0 <= 11 < 2 ^ 31) by lia.
  assert (A5 : PML.ps_done ps = true \/ false = true \/ 11 <> 0) by (right; right; lia).
  exact (brs2 fx2 R2 M1 model1 cr1 g1 reps rep r2 ps ch bof false 11 gp rd Hfp2 H2b A1 A2 A3 STR PRS BR BP FR1 BV1 MOK1 HH1 LS1 CLE CUR1 SCAP ISR1 E11 A4 A5).
Qed.

Lemma bd_rget : forall (fx1 : FPState) R1 M1 model1 cr1 g1 reps rep r2 ps ch bof gp rd kx1 bx1,
  PML.fp_ok fx1 -> getr R1 2%bv = Z_to_bv 64 (sp - 1040) -> getr R1 8%bv = Z_to_bv 64 (sp - 416) -> TK.keepsR HCS.KOH R R1 -> getr R1 18%bv = Z_to_bv 64 2 ->
  PML.str_at_w M1 (sp - 1032) r2 ->
  pers reps M1 -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) -> (forall b, In b (PML.srep_blocks rep) -> 0 <= snd b <= n + 52) ->
  TK2.FR L LB sp SS PML.in_foot11 M M1 -> model_but_vm model model1 -> PML.model_ok model1 ->
  hi_heap HI (PML.srep_blocks r2 ++ PML.ps_blocks ps ++ (ch, 16384) :: PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) cr1 M1 (m_vmmaps model1) ->
  PML.ls_ok g1 M1 -> g1 <> PML.LS0 ->
  PMCS.cursor_at M1 (sp - 1008) (sp - 328) ch bof false ps -> PML.isrc_at M1 (sp - 328) rep gp rd -> PML.ec_at M1 (sp - 344) 0 ->
  Z.of_nat (length (PML.srep_chars rep)) = n -> PMCS.rn_bound (PMCUR.ps_set_more ps true) (sp - 328) rep gp n -> PMCUR.wf_c (PMCUR.ps_set_more ps true) ->
  PML.ps_st ps = PML.ST_ACCEPT ->
  PML.win_ok M1 (PML.srep_blocks r2 ++ (ch, 16384) :: PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) ps ->
  (forall b, In b (PML.srep_blocks rep) -> fst b <> ch) -> (forall b, In b (PML.srep_blocks r2) -> fst b <> ch) ->
  PML.pcredit_x L cr1 ps kx1 bx1 -> credit_le (credit_sub cr (ll_credit Lay n)) (kx1, bx1) ->
  srealizes RSEGS SCFG (@PML.cfg fx1 R1 HCT.R_GET M1 model1) K.
Proof.
  intros fx1 R1 M1 model1 cr1 g1 reps rep r2 ps ch bof gp rd kx1 bx1 Hfp H2 H8 HKO H18 STR PRS BR BP FR1 BV1 MOK1 HH1 LS1 HG1 CUR1 ISR1 EC1 Hn RNB WFC HACC WIN CHN R2N PCX CLE.
  pose proof MOK1 as (Hh & Hl & Hm).
  pose proof EC1 as (EC1a & EC1d & _).
  pose proof SPOK as (SP1 & Hal).
  assert (Htop47 : hl_sptop L <= 2 ^ 47) by lia.
  pose proof SCRv as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH1) as BOK1.
  assert (BLK : forall b, In b (PML.srep_blocks r2) -> block_range L (fst b) (snd b)) by (intros b Hb; apply BOK1; bd_inn).
  destruct (sbit_word M1 (sp - 1032) r2 FR1 ltac:(lia) ltac:(lia) STR BLK) as (w & p & Hw & Hp & W1 & W2 & SB).
  assert (W2' : L5.u64_at RSEGS M1 (sp - 1016) p) by (replace (sp - 1016) with (sp - 1032 + 16) by lia; exact W2).
  apply (HCS.s_h_rget FPM fx1 R1 M1 model1 K sp w p Hh Hl Hfp H2 SPOK Hw Hp W1 W2' EC1a).
  intros fx2 R2 M2 Hfp2 H2b H1b H10b H11b H12b HK2 AG2 MG2. apply samem_all in AG2. subst M2.
  assert (KOR2 : TK.keepsR HCS.KOH R R2) by exact (KT R R1 R2 HKO (KCO R1 R2 HK2)).
  assert (H4b : getr R2 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KOR2 4%bv KO_4); exact Ptp).
  assert (STK : L5C.stk (hl_sptop L) M1 (sp - 1040) (PMCS.RN_SCR STRTOD_SCR)) by exact (mk_stk LB sp SS PML.in_foot11 M M1 (sp - 1040) _ FR1 Hal eq_refl RN0 S5 Hceil Hsptop Htop).
  set (rest := PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) in *.
  assert (HHr : hi_heap HI (PML.ps_blocks ps ++ PML.srep_blocks r2 ++ (ch, 16384) :: rest) cr1 M1 (m_vmmaps model1)) by exact (heap_swap _ _ _ cr1 M1 _ HI L HIok HH1).
  apply (RNEXT (PML.srep_blocks r2 ++ (ch, 16384) :: rest) cr1 (sp - 1040) HCT.R_RN (sp - 1008) (sp - 328) (sp - 344) ch gp rd n kx1 bx1 rep g1 bof ps fx2 R2 M1 model1 K HHr MOK1 HK0 Hfp2).
  - split; [exact (mk_entry R2 M1 (sp - 1040) HCT.R_RN _ H1b (ra_ok_lit HCT.R_RN ltac:(unfold HCT.R_RN; lia) eq_refl) H2b H4b STK)|].
    split; [exact H10b|]. split; [unfold PML.a1; rewrite H11b, H8; f_equal; lia|]. split; [exact H12b|].
    split; [exact CUR1|]. split; [exact WFC|]. split; [exact WIN|]. split; [exact ISR1|]. split; [exact RNB|]. split; [exact EC1|].
    split; [bd_inn|]. split; [intros b Hb; split; [unfold rest; bd_inn | exact (CHN b Hb)]|]. split; [lia|]. split; [exact LS1|]. split; [exact HG1|]. split; [exact PCX|].
    unfold PMCS.CURSOR_SIZE. split; [oos Hal|]. split; [oos Hal|]. split; [oos Hal|]. unfold PML.apart. split; [lia|]. split; lia.
  - intros fx3 R3 M3 model3 LB3 cr3 LBk3 W3 Hfp3 (ps3 & code & gp3 & rd3 & g3 & bof3 & dn3 & CUR3 & ISR3 & RNB3 & EC3 & LS3 & HG3 & WF3 & WIN3 & -> & -> & PC3 & HW3 & RNR3) RP3 HP3 BV3 HH3.
    assert (KOR3 : TK.keepsR HCS.KOH R R3) by exact (KT R R2 R3 KOR2 (KSP R2 R3 RP3)).
    assert (H2c : getr R3 2%bv = Z_to_bv 64 (sp - 1040)) by (rewrite (RP3 2%bv CS2); exact H2b).
    assert (H18c : getr R3 18%bv = Z_to_bv 64 2) by (rewrite (bd_rp_csr R2 R3 RP3 18%bv ltac:(ck_in)), (HK2 18%bv ltac:(ck_in)); exact H18).
    assert (WOK : w_ok W3) by (rewrite HW3; unfold w_ok, PMCS.CURSOR_SIZE; wok).
    assert (BOKk : TK2.blocks_ok L (lb_remove ch (PML.srep_blocks r2 ++ (ch, 16384) :: rest))).
    { intros b Hb. apply L5C.in_lb_remove in Hb. apply BOK1. bd_brk Hb; bd_inn. }
    assert (INCL : incl (PML.srep_blocks reps ++ LB) (lb_remove ch (PML.srep_blocks r2 ++ (ch, 16384) :: rest))).
    { intros b Hb. apply (bd_lbr_rest _ ch 16384 rest). unfold rest. bd_brk Hb; bd_inn. }
    destruct (step_heap reps M1 M3 _ _ W3 HP3 BOKk INCL RN0 S5 WOK PRS FR1) as (PRS3 & FR3 & AG3 & WSI3).
    subst W3. unfold PMCS.CURSOR_SIZE in AG3, WSI3.
    assert (W1c : L5.u64_at RSEGS M3 (sp - 1032) w) by (apply (TK2.u64_x _ _ _ AG3 (sp - 1032) w ltac:(lia)); [intros i Hi; split; [ow | left; lia] | exact W1]).
    assert (W2c : L5.u64_at RSEGS M3 (sp - 1016) p) by (apply (TK2.u64_x _ _ _ AG3 (sp - 1016) p ltac:(lia)); [intros i Hi; split; [ow | left; lia] | exact W2']).
    assert (STR3 : PML.str_at_w M3 (sp - 1032) r2).
    { apply (TK2.str_at_w_x _ _ _ AG3 (sp - 1032) r2 ltac:(lia)); [|exact STR].
      apply (TK2.str_cov_keepH L LAY _ _ (sp - 1040) _ (sp - 1032) r2 Htop47); [intros i Hi; split; [ow | left; lia] | exact WSI3 |].
      intros [b1 b2] Hb. split; [|exact (BLK _ Hb)]. apply L5C.in_lb_remove_neq; [bd_inn | exact (R2N _ Hb)]. }
    assert (HH3' : hi_heap HI (PML.srep_blocks r2 ++ PML.ps_blocks ps3 ++ (ch, 16384) :: rest) cr3 M3 (m_vmmaps model3)) by exact (heap_swap _ _ _ cr3 M3 _ HI L HIok HH3).
    assert (CLE3 : credit_le (credit_sub cr (ll_credit Lay n)) cr3).
    { destruct (pcx_lb cr3 ps3 kx1 bx1 PC3 (scap_wf ps3 (proj1 WF3))) as (KX3 & BX3). unfold credit_le in *. cbn [fst snd] in CLE. lia. }
    assert (DONE3 : PML.ps_done ps3 = true \/ dn3 = true \/ code <> 0).
    { destruct (Z.eq_dec code 0) as [Hc|Hc]; [left; subst code; exact (proj2 (proj1 RNR3 HACC eq_refl)) | right; right; exact Hc]. }
    exact (bd_rn fx3 R3 M3 model3 cr3 g3 reps rep r2 ps3 ch bof3 dn3 code gp3 rd3 w p Hfp3 H2c KOR3 H18c Hw Hp W1c W2c SB STR3 PRS3 BR BP FR3
             (L5C.model_but_vm_trans _ _ _ BV1 BV3) (mok_of model1 model3 BV3 MOK1) HH3' LS3 CLE3 CUR3 (bd_scap _ (scap_wf ps3 (proj1 WF3))) ISR3 EC3 DONE3).
Qed.
Lemma body : forall (fx' : FPState) R' Mx M' modelk crk gk reps rep ps ch bof gp rd kx bx,
  PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp - 1040) -> getr R' 1%bv = Z_to_bv 64 HCT.R_GET ->
  getr R' 10%bv = Z_to_bv 64 (sp - 1032) -> getr R' 11%bv = Z_to_bv 64 (sp - 408) -> getr R' 13%bv = Z_to_bv 64 (sp - 344) -> getr R' 9%bv = Z_to_bv 64 (sp - 408) ->
  getr R' 8%bv = Z_to_bv 64 (sp - 416) -> getr R' 18%bv = Z_to_bv 64 2 ->
  TK.keepsR HCS.KOH R R' -> TK.samem (HCS.KEX sp) Mx M' -> mem_grows Mx M' ->
  pers reps Mx -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) -> (forall b, In b (PML.srep_blocks rep) -> 0 <= snd b <= n + 52) ->
  TK2.FR L LB sp SS PML.in_foot11 M Mx -> model_but_vm model modelk -> PML.model_ok modelk ->
  hi_heap HI (PML.ps_blocks ps ++ (ch, 16384) :: PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) crk Mx (m_vmmaps modelk) ->
  PML.ls_ok gk Mx -> gk <> PML.LS0 ->
  PMCS.cursor_at Mx (sp - 1008) (sp - 328) ch bof false ps -> PML.isrc_at Mx (sp - 328) rep gp rd -> PML.ec_at Mx (sp - 344) 0 ->
  Z.of_nat (length (PML.srep_chars rep)) = n -> PMCS.rn_bound ps (sp - 328) rep gp n -> PMCUR.wf_c (PMCUR.ps_set_more ps true) ->
  PMCS.evc Mx (sp - 416) 0 ((ch, 16384) :: PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) ps ->
  PML.win_ok Mx ((ch, 16384) :: PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) ps ->
  PML.ps_more ps = false -> PML.ps_done ps = false ->
  PML.pcredit_x L crk ps kx bx -> hl_k_per_malloc L <= kx -> n + 16394 + hl_b_overhead L <= bx ->
  credit_le (credit_sub cr (ll_credit Lay n)) (kx - hl_k_per_malloc L, bx - (n + 16394 + hl_b_overhead L)) ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' PMCS.PC_GET_STRING M' modelk) K.
Proof.
  intros fx' R' Mx M' modelk crk gk reps rep ps ch bof gp rd kx bx Hfp H2 H1 H10 H11 H13 H9 H8 H18 HKO AGx MGx PRS BR BP FRx BVk MOKk HHx LSx HGk CURx ISRx ECx Hn RNB WFC EVC WIN HMORE HDONE PCX HKX HBX CLE.
  pose proof SPOK as (SP1 & Hal).
  assert (Htop47 : hl_sptop L <= 2 ^ 47) by lia.
  pose proof SCRv as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  pose proof (PmLayout.ly_kpm L LAY) as KPM0. pose proof (PmLayout.ly_bov L LAY) as BOV0.
  set (rest := PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) in *.
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HHx) as BOKx.
  destruct (hio_wf _ _ _ HIok _ _ _ _ HHx) as (_ & NDx & _).
  assert (CHN : forall b, In b (PML.srep_blocks rep) -> fst b <> ch) by (intros b Hb; apply (nodup_mid _ _ _ NDx); unfold rest; bd_inn).
  pose proof (kex_out Mx M' AGx) as AGo.
  assert (FW : forall w0 : L5.range, In w0 [(sp - 1008, 8); (sp - 360, 8)] -> sp - SS <= fst w0 /\ fst w0 + snd w0 <= sp - 56 /\ 0 <= snd w0).
  { intros w0 Hw0. cbn [In] in Hw0. destruct Hw0 as [<-|[<-|[]]]; cbn [fst snd]; lia. }
  assert (PRSin : forall b, In b (PML.srep_blocks reps) -> In b (PML.ps_blocks ps ++ (ch, 16384) :: rest)) by (intros b Hb; unfold rest; bd_inn).
  destruct (step_out_g _ reps Mx M' _ crk modelk AGo MGx FW PRSin PRS FRx HHx) as (PRS' & FR' & HH' & SC' & WSI').
  assert (LS' : PML.ls_ok gk M') by exact (TK2.ls_ok_x _ _ _ AGo SC' gk LSx).
  assert (CUR' : PMCS.cursor_at M' (sp - 1008) (sp - 328) ch bof false ps).
  { apply (cursor_at_xd _ Mx M' (sp - 1008) (sp - 328) ch bof false ps AGo ltac:(lia)); [intros i Hi; ow | | exact (frame_def M' (sp - 1008) 656 FR' ltac:(lia) ltac:(lia)) | exact CURx].
    apply (TK2.ps_cov_out L LAY _ ps Htop47 WSI'). intros b Hb. apply BOKx. bd_inn. }
  assert (ISR' : PML.isrc_at M' (sp - 328) rep gp rd).
  { apply (TK2.isrc_at_x _ _ _ AGo (sp - 328) rep gp rd ltac:(lia)); [intros i Hi; ow | | exact ISRx].
    apply (TK2.str_cov_out L LAY _ (sp - 328 + 80) rep Htop47); [intros i Hi; ow | exact WSI' | intros b Hb; apply BOKx; unfold rest; bd_inn]. }
  assert (EC' : PML.ec_at M' (sp - 344) 0) by (apply (TK2.ec_at_x _ _ _ AGo (sp - 344) 0 ltac:(lia)); [intros i Hi; ow | exact ECx]).
  assert (EVC' : PMCS.evc M' (sp - 416) 0 ((ch, 16384) :: rest) ps) by (apply (CCTL.evc_x _ Mx M' (sp - 416) 0 _ ps AGo MGx ltac:(lia)); [intros i Hi; ow | exact EVC]).
  destruct (pcx_lb crk ps kx bx PCX (scap_sm ps true (proj1 WFC))) as (PLK & PLB).
  destruct EVC' as (w0 & Hw0 & e & EVA & EVR).
  destruct (ev_lvl0 ps w0 e WFC EVR) as (CONV & NOKEY).
  destruct (hio_wf _ _ _ HIok _ _ _ _ HH') as (WF' & _ & _).
  assert (ES : PMCS.ev_src M' (PML.ps_blocks ps ++ (ch, 16384) :: rest) e /\ Z.max 48 (match e with PMCUR.EvStr _ k | PMCUR.EvKey _ k => PML.str_cap k | _ => 0 end) <= n + 16394).
  { destruct e as [| bb | v | v | v | p0 ne | p0 ne | | | |]; cbn [PMCS.ev_src]; try (split; [exact I | lia]).
    - destruct EVR as (_ & _ & [(Hp0 & Hne) | (p1 & e1 & Hw1 & Hp1 & Hne0 & Hne1)]).
      + pose proof CURx as (_ & PAx & _).
        pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & HLEN) & _).
        pose proof ISRx as (_ & _ & _ & _ & _ & _ & HG & _).
        destruct RNB as (RB1 & RB2 & RB3).
        assert (BN : PML.buf_need ps = 0) by (unfold PML.buf_need; rewrite HMORE; reflexivity).
        unfold PMCS.undelivered in RB1.
        destruct (WF' (PML.ps_bptr ps, PML.ps_bcap ps) ltac:(apply in_or_app; left; unfold PML.ps_blocks; left; reflexivity)) as (_ & DB & _).
        cbn [fst snd] in DB.
        pose proof (str_cap_bounds ne ltac:(lia)) as SCB.
        split; [split; [lia|]; split; [intros i Hi; subst p0; apply DB; lia | right; exists (PML.ps_bptr ps, PML.ps_bcap ps); split; [apply in_or_app; left; unfold PML.ps_blocks; left; reflexivity | cbn [fst snd]; lia]] | lia].
      + subst w0. destruct Hw0 as (b & Hb & Hb1 & Hb2 & _).
        destruct (WF' (b, 16384) ltac:(apply in_or_app; right; exact Hb)) as (_ & DB & _).
        cbn [fst snd] in DB.
        pose proof (str_cap_bounds ne ltac:(lia)) as SCB.
        split; [split; [lia|]; split; [intros i Hi; replace (p0 + i) with (b + (p0 - b + i)) by lia; apply DB; lia | right; exists (b, 16384); split; [apply in_or_app; right; exact Hb | cbn [fst snd]; lia]] | lia].
    - exfalso. exact NOKEY. }
  assert (COK : credit_ok L crk (Z.max 48 (match e with PMCUR.EvStr _ k | PMCUR.EvKey _ k => PML.str_cap k | _ => 0 end))) by (destruct ES as (_ & ES2); unfold credit_ok; split; lia).
  assert (CAPB : forall k, k <= Z.max 48 (match e with PMCUR.EvStr _ k | PMCUR.EvKey _ k => PML.str_cap k | _ => 0 end) -> k <= n + 16394) by (intros k Hk; destruct ES as (_ & ES2); lia).
  pose proof MOKk as (Hh & Hl & Hm).
  assert (H4' : getr R' 4%bv = Z_to_bv 64 PML.TP) by (rewrite (HKO 4%bv KO_4); exact Ptp).
  assert (GS0 : 0 <= PMCS.GETSTR_SCR STRTOD_SCR) by (unfold PMCS.GETSTR_SCR; lia).
  assert (STK' : L5C.stk (hl_sptop L) M' (sp - 1040) (PMCS.GETSTR_SCR STRTOD_SCR)) by exact (mk_stk LB sp SS PML.in_foot11 M M' (sp - 1040) _ FR' Hal eq_refl GS0 S2 Hceil Hsptop Htop).
  apply (GETSTR (PML.ps_blocks ps ++ (ch, 16384) :: rest) crk (sp - 1032) (sp - 416) (sp - 344) (sp - 1040) HCT.R_GET e gk fx' R' M' modelk K HH' MOKk HK0 Hfp).
  - split; [exact (mk_entry R' M' (sp - 1040) HCT.R_GET _ H1 (ra_ok_lit HCT.R_GET ltac:(unfold HCT.R_GET; lia) eq_refl) H2 H4' STK')|].
    split; [exact H10|]. split; [unfold PML.a1; rewrite H11; f_equal; lia|]. split; [exact H13|].
    split; [exact EVA|]. split; [exact (proj1 ES)|]. split; [exact (frame_def M' (sp - 416) 48 FR' ltac:(lia) ltac:(lia))|]. split; [exact EC'|].
    split; [exact (proj1 LS')|]. split; [exact LS'|]. split; [exact HGk|].
    split; [oos Hal|]. split; [exact (frame_def M' (sp - 1032) 24 FR' ltac:(lia) ltac:(lia))|]. split; [oos Hal|]. split; [oos Hal|].
    unfold PML.apart. split; [lia|]. split; [lia|]. split; [lia|]. exact COK.
  - intros fx1 R1 M1 model1 LB1 cr1 LBk1 W1 Hfp1 (code & g1 & (r2 & STR1 & -> & CR0 & CRB) & -> & EC1 & ED1 & LS1 & CASE & HW1) RP1 HP1 BV1 HH1.
    assert (WOK1 : w_ok W1) by (rewrite HW1; unfold w_ok; wok).
    assert (INCLh : incl (PML.srep_blocks reps ++ LB) (PML.ps_blocks ps ++ (ch, 16384) :: rest)) by (intros b Hb; unfold rest; bd_brk Hb; bd_inn).
    destruct (step_heap reps M' M1 _ _ W1 HP1 BOKx INCLh GS0 S2 WOK1 PRS' FR') as (PRS1 & FR1 & AG1 & WSI1).
    subst W1.
    assert (CUR1 : PMCS.cursor_at M1 (sp - 1008) (sp - 328) ch bof false ps).
    { apply (cursor_at_xd _ M' M1 (sp - 1008) (sp - 328) ch bof false ps AG1 ltac:(lia)); [intros i Hi; split; [ow | left; lia] | | exact (frame_def M1 (sp - 1008) 656 FR1 ltac:(lia) ltac:(lia)) | exact CUR'].
      apply (TK2.ps_cov_keepH L LAY _ _ (sp - 1040) _ ps Htop47 WSI1). intros b Hb. split; [bd_inn | apply BOKx; bd_inn]. }
    assert (ISR1 : PML.isrc_at M1 (sp - 328) rep gp rd).
    { apply (TK2.isrc_at_x _ _ _ AG1 (sp - 328) rep gp rd ltac:(lia)); [intros i Hi; split; [ow | left; lia] | | exact ISR'].
      apply (TK2.str_cov_keepH L LAY _ _ (sp - 1040) _ (sp - 328 + 80) rep Htop47); [intros i Hi; split; [ow | left; lia] | exact WSI1 |].
      intros b Hb. split; [unfold rest; bd_inn | apply BOKx; unfold rest; bd_inn]. }
    assert (CRF : fst crk - hl_k_per_malloc L <= fst cr1 <= fst crk /\ snd crk - (n + 16394 + hl_b_overhead L) <= snd cr1 <= snd crk).
    { destruct r2 as [s|cap p s]; [rewrite (CR0 eq_refl); lia|].
      destruct (CRB (p, cap) (or_introl eq_refl)) as ((BRp & _ & _) & -> & Hcap). destruct BRp as (_ & _ & _ & Hc0 & _).
      apply CAPB in Hcap. unfold debit. cbn [fst snd] in *. lia. }
    assert (R2N : forall b, In b (PML.srep_blocks r2) -> fst b <> ch).
    { intros b Hb. destruct (CRB b Hb) as ((BRb & APb & _) & _ & _). destruct BRb as (_ & _ & _ & Hc0 & _).
      destruct (APb (ch, 16384) ltac:(apply in_or_app; right; left; reflexivity)) as [X|X]; cbn [fst snd] in X; lia. }
    assert (CLE1 : credit_le (credit_sub cr (ll_credit Lay n)) (kx - (fst crk - fst cr1), bx - (snd crk - snd cr1))).
    { unfold credit_le in *. cbn [fst snd] in CLE |- *. lia. }
    assert (PCX1 : PML.pcredit_x L cr1 ps (kx - (fst crk - fst cr1)) (bx - (snd crk - snd cr1))).
    { unfold PML.pcredit_x in *. destruct PCX as (_ & _ & PC0). split; [lia|]. split; [lia|].
      replace (fst cr1 - (kx - (fst crk - fst cr1)), snd cr1 - (bx - (snd crk - snd cr1))) with (fst crk - kx, snd crk - bx) by (f_equal; lia). exact PC0. }
    assert (H2_1 : getr R1 2%bv = Z_to_bv 64 (sp - 1040)) by (rewrite (RP1 2%bv CS2); exact H2).
    assert (H8_1 : getr R1 8%bv = Z_to_bv 64 (sp - 416)) by (rewrite (RP1 8%bv CS8); exact H8).
    assert (KOR1 : TK.keepsR HCS.KOH R R1) by exact (KT R R' R1 HKO (KSP R' R1 RP1)).
    assert (H18_1 : getr R1 18%bv = Z_to_bv 64 2) by (rewrite (bd_rp_csr R' R1 RP1 18%bv ltac:(ck_in)); exact H18).
    assert (BV1' : model_but_vm model model1) by exact (L5C.model_but_vm_trans _ _ _ BVk BV1).
    assert (MOK1 : PML.model_ok model1) by exact (mok_of modelk model1 BV1 MOKk).
    destruct CASE as [(CV & -> & ->) | (NCV & -> & ->)].
    + assert (HACC : PML.ps_st ps = PML.ST_ACCEPT) by exact (CONV CV).
      assert (EC1' : PML.ec_at M1 (sp - 344) 0) by (split; [exact EC1|]; split; [exact ED1 | left; reflexivity]).
      assert (WIN1 : PML.win_ok M1 (PML.srep_blocks r2 ++ (ch, 16384) :: rest) ps).
      { apply (win_ok_heap Mx M1 ((ch, 16384) :: rest) (PML.srep_blocks r2 ++ (ch, 16384) :: rest) (PML.srep_blocks r2 ++ PML.ps_blocks ps ++ (ch, 16384) :: rest) cr1 (m_vmmaps model1) ps WIN); [intros b Hb; apply in_or_app; right; exact Hb | | exact HH1].
        intros b Hb. apply in_or_app. right. apply in_or_app. right. exact Hb. }
      exact (bd_rget fx1 R1 M1 model1 cr1 gk reps rep r2 ps ch bof gp rd _ _ Hfp1 H2_1 H8_1 KOR1 H18_1 STR1 PRS1 BR BP FR1 BV1' MOK1 HH1 LS1 HGk CUR1 ISR1 EC1'
               Hn (rn_bound_sm ps (sp - 328) rep gp n HACC RNB) WFC HACC WIN1 CHN R2N PCX1 CLE1).
    + assert (CLE11 : credit_le (credit_sub cr (ll_credit Lay n)) cr1) by (unfold credit_le in *; cbn [fst snd] in CLE; lia).
      exact (bd_g11 fx1 R1 M1 model1 cr1 (PML.regC gk) reps rep r2 ps ch bof gp rd Hfp1 H2_1 KOR1 H18_1 STR1 PRS1 BR BP FR1 BV1' MOK1 HH1 LS1 CLE11 CUR1
               (bd_scap _ (scap_sm ps true (proj1 WFC))) ISR1 EC1).
Qed.

Ltac rl_out := let w := fresh "w" in let Hw := fresh "Hw" in let Hin := fresh "Hin" in
  intros w Hw Hin; repeat (destruct Hw as [<-|Hw]; [unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia|]); destruct Hw.

Lemma rl_cctor : forall (fx7 : FPState) R7 M7 model7 cr4 reps rep g7,
  PML.fp_ok fx7 -> getr R7 2%bv = Z_to_bv 64 (sp - 1040) -> getr R7 1%bv = Z_to_bv 64 HCT.R_CCTOR ->
  getr R7 10%bv = Z_to_bv 64 (sp - 1008) -> getr R7 11%bv = Z_to_bv 64 (sp - 328) -> getr R7 12%bv = Z_to_bv 64 (sp - 344) ->
  TK.keepsR HCS.KOH R R7 ->
  pers reps M7 -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) -> (forall b, In b (PML.srep_blocks rep) -> 0 <= snd b <= n + 52) ->
  Z.of_nat (length (PML.srep_chars rep)) = n ->
  TK2.FR L LB sp SS PML.in_foot11 M M7 -> model_but_vm model model7 -> PML.model_ok model7 ->
  hi_heap HI (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) cr4 M7 (m_vmmaps model7) ->
  PML.ls_ok g7 M7 -> g7 <> PML.LS0 ->
  PML.isrc_at M7 (sp - 328) rep (PML.srep_data (sp - 328 + 80) rep) 0 -> PML.ec_at M7 (sp - 344) 0 ->
  credit_le (PMCS.pm_credit_c L n) cr -> fst cr - 2 * hl_k_per_malloc L <= fst cr4 -> snd cr - (2 * n + 62 + 2 * hl_b_overhead L) <= snd cr4 ->
  srealizes RSEGS SCFG (@PML.cfg fx7 R7 PMCS.PC_CURSOR_CTOR M7 model7) K.
Proof.
  intros fx7 R7 M7 model7 cr4 reps rep g7 Hfp H2 H1 H10 H11 H12 KO PE BS BR LEN FR7 BV7 MOK7 HH7 LS7 G7 IS7 EC7 CR C1 C2.
  pose proof SCRv as (SC1 & SC2 & SC3 & SC4 & SC5 & SC6 & SC7 & SC8 & SC9).
  pose proof SPOK as (Hsp & Hal).
  pose proof (PmLayout.ly_kpm L LAY) as KP. pose proof (PmLayout.ly_bov L LAY) as BP.
  pose proof MOK7 as (Hh7 & Hl7 & Hm7).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH7) as BOK7.
  unfold credit_le, PMCS.pm_credit_c in CR. cbn [fst snd] in CR.
  assert (LD7 : PML.loc_done M7).
  { destruct LS7 as (_ & _ & X). destruct g7; [exfalso; apply G7; reflexivity | exact (proj1 X) ..]. }
  eapply (CCTOR (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) cr4 (sp - 1008) (sp - 328) (sp - 344) (sp - 1040) HCT.R_CCTOR
            (fst cr4 - 25 * hl_k_per_malloc L) _ rep g7 fx7 R7 M7 model7 K HH7 MOK7 HK0 Hfp).
  - cbv beta. rewrite kleft_init, bleft_init.
    match goal with |- context [?l + ?e <= snd cr4] => is_evar e; unify e (snd cr4 - l) end.
    unfold PMCS.CURSOR_SIZE.
    split.
    { apply mk_entry; [exact H1 | apply ra_ok_lit; [unfold HCT.R_CCTOR; lia | reflexivity] | exact H2 | rewrite (KO 4%bv KO_4); exact Ptp |].
      apply (mk_stk LB sp SS PML.in_foot11 M M7); [exact FR7 | exact Hal | reflexivity | unfold PMCS.CCTOR_SCR; lia | exact SC1 | exact Hceil | exact Hsptop | exact Htop]. }
    split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact IS7|]. split; [exact EC7|].
    split; [exact (proj1 LS7)|]. split; [split; [exact (proj1 LD7) | exact (proj1 (proj2 LD7))]|].
    split; [exact LS7|]. split; [exact G7|]. split; [right; exact (proj2 (proj2 LD7))|].
    split; [intros x Hx; apply in_or_app; left; exact Hx|]. split; [lia|].
    split; [oos Hal|]. split; [oos Hal|]. split; [oos Hal|].
    split; [unfold PML.apart; lia|]. split; [unfold PML.apart; lia|]. split; [unfold PML.apart; lia|].
    split; [apply (frame_def M7 (sp - 1008) 656 FR7); lia|].
    split; [lia|]. split; [lia|]. split; lia.
  - intros fx8 R8 M8 model8 LB8 cr8 LBk8 W8 Hfp8 (ch & ps & code & gp & rd & g8 & bof & dn & CUR & ISR & RNB & EC & LS8 & HG8 & WF & WIN & U8 & -> & -> & PCX & EW & IMP) RP8 HP8 BV8 HH8.
    assert (WOK : w_ok W8) by (rewrite EW; unfold w_ok, PMCS.CURSOR_SIZE; wok).
    assert (INCL : incl (PML.srep_blocks reps ++ LB) (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB)) by (intros x Hx; apply in_or_app; right; exact Hx).
    assert (SCR0 : 0 <= PMCS.CCTOR_SCR STRTOD_SCR) by (unfold PMCS.CCTOR_SCR; lia).
    pose proof (step_heap reps M7 M8 _ _ _ HP8 BOK7 INCL SCR0 SC1 WOK PE FR7) as (PE8 & FR8 & AG8 & WS8).
    pose proof (L5C.model_but_vm_trans _ _ _ BV7 BV8) as BV8'.
    pose proof (mok_of _ _ BV8 MOK7) as MOK8. pose proof MOK8 as (Hh8 & Hl8 & Hm8).
    assert (H2_8 : getr R8 2%bv = Z_to_bv 64 (sp - 1040)) by (rewrite (RP8 _ CS2); exact H2).
    assert (KO8 : TK.keepsR HCS.KOH R R8) by exact (KT _ _ _ KO (KSP _ _ RP8)).
    assert (G8 : g8 <> PML.LS0) by (destruct HG8 as [-> | ->]; [exact G7 | apply CCTL.regJ_ne]).
    pose proof CUR as (SRC & PA & VIS & UDN & DEFC).
    pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UPD & _).
    pose proof EC as (UEC & DEC & CEC).
    apply (HCS.s_h_test_cctor FPM fx8 R8 M8 model8 K sp (PML.b2z (PML.ps_done ps)) (PML.b2z dn) code Hh8 Hl8 Hfp8 H2_8 SPOK).
    + destruct (PML.ps_done ps); cbn; lia.
    + destruct dn; cbn; lia.
    + destruct CEC as [-> | (X & _)]; lia.
    + replace (sp - 476) with (sp - 1008 + 320 + 212) by lia. exact UPD.
    + replace (sp - 368) with (sp - 1008 + 640) by lia. exact UDN.
    + exact UEC.
    + apply (frame_def M8 (sp - 1008) 8 FR8); lia.
    + apply (frame_def M8 (sp - 360) 8 FR8); lia.
    + intros Hpd Hdn Hec fx9 R9 M9 Hfp9 H2_9 H1_9 H10_9 H11_9 H12_9 H13_9 H8_9 H9_9 H18_9 KO9 AG9 MG9.
      apply b2z_0 in Hpd. apply b2z_land in Hdn. subst code dn.
      destruct (IMP eq_refl eq_refl) as (MORE & [(DONE & _) | (WFC & EVC)]); [congruence|].
      replace (sp - 1008 + 592) with (sp - 416) in EVC by lia.
      rewrite LEN in RNB.
      eapply (body fx9 R9 M8 M9 model8 cr8 g8 reps rep ps ch bof gp rd _ _ Hfp9 H2_9 H1_9 H10_9 H11_9 H13_9 H9_9 H8_9 H18_9 (KT _ _ _ KO8 KO9) AG9 MG9
                   PE8 BS BR FR8 BV8' MOK8 HH8 LS8 G8 CUR ISR EC LEN RNB WFC EVC WIN MORE Hpd PCX).
      * lia.
      * lia.
      * unfold credit_le, credit_sub. rewrite LC. unfold PMCS.pm_credit_c. cbn [fst snd]. lia.
    + intros Hor fx9 R9 M9 Hfp9 H2_9 H1_9 H10_9 KO9 V1 V2 AG9 MG9.
      pose proof (scap_wf ps (proj1 WF)) as SW.
      assert (SCAP : 0 < PML.ps_scap ps <= 4096) by (cbn [In] in SW; lia).
      pose proof (pcx_lb _ _ _ _ PCX SW) as (KX8 & BX8).
      apply (exitk fx9 R9 M8 M9 model8 cr8 g8 reps rep ps ch bof dn gp rd Hfp9 H2_9 H1_9 H10_9 (KT _ _ _ KO8 KO9) AG9 MG9 PE8 BS BR FR8 BV8' MOK8 HH8 LS8); [| exact CUR | exact SCAP | exact ISR].
      unfold credit_le, credit_sub. rewrite LC. unfold PMCS.pm_credit_c. cbn [fst snd]. lia.
Qed.

Lemma rl_syscat : forall (fx5 : FPState) R5 M5 model5 cr4 reps rep,
  PML.fp_ok fx5 -> getr R5 2%bv = Z_to_bv 64 (sp - 1040) -> getr R5 1%bv = Z_to_bv 64 HCT.R_SYSCAT -> TK.keepsR HCS.KOH R R5 ->
  pers reps M5 -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) -> (forall b, In b (PML.srep_blocks rep) -> 0 <= snd b <= n + 52) ->
  Z.of_nat (length (PML.srep_chars rep)) = n ->
  TK2.FR L LB sp SS PML.in_foot11 M M5 -> model_but_vm model model5 -> PML.model_ok model5 ->
  hi_heap HI (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) cr4 M5 (m_vmmaps model5) ->
  PMS.statics_mid M5 ->
  PML.isrc_at M5 (sp - 328) rep (PML.srep_data (sp - 328 + 80) rep) 0 -> L5.u32_at RSEGS M5 (sp - 344) 0 ->
  credit_le (PMCS.pm_credit_c L n) cr -> fst cr - 2 * hl_k_per_malloc L <= fst cr4 -> snd cr - (2 * n + 62 + 2 * hl_b_overhead L) <= snd cr4 ->
  srealizes RSEGS SCFG (@PML.cfg fx5 R5 PML.PC_SYSTEM_CATEGORY M5 model5) K.
Proof.
  intros fx5 R5 M5 model5 cr4 reps rep Hfp H2 H1 KO PE BS BR LEN FR5 BV5 MOK5 HH5 MID5 IS5 U5 CR C1 C2.
  pose proof SCRv as (SC1 & SC2 & SC3 & SC4 & SC5 & SC6 & SC7 & SC8 & SC9).
  pose proof SPOK as (Hsp & Hal).
  pose proof MOK5 as (Hh5 & Hl5 & Hm5).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH5) as BOK5.
  pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  pose proof MID5 as (RO5 & LQ5 & GL5 & SG5 & EC5).
  apply (SYSCAT (sp - 1040) HCT.R_SYSCAT fx5 R5 M5 model5 K Hh5 Hl5 HK0 Hfp).
  - cbv beta. split; [|split; [exact RO5 | exact SG5]].
    apply mk_entry; [exact H1 | apply ra_ok_lit; [unfold HCT.R_SYSCAT; lia | reflexivity] | exact H2 | rewrite (KO 4%bv KO_4); exact Ptp |].
    apply (mk_stk LB sp SS PML.in_foot11 M M5); [exact FR5 | exact Hal | reflexivity | lia | lia | exact Hceil | exact Hsptop | exact Htop].
  - intros fx6 R6 M6 Hfp6 (A0 & U8g) RP6 FB6 MG6.
    pose proof (TK2.frame_but_samem _ _ _ FB6) as AG6.
    assert (H2_6 : getr R6 2%bv = Z_to_bv 64 (sp - 1040)) by (rewrite (RP6 _ CS2); exact H2).
    assert (KO6 : TK.keepsR HCS.KOH R R6) by exact (KT _ _ _ KO (KSP _ _ RP6)).
    assert (BR5 : forall x, In x (PML.srep_blocks rep) -> block_range L (fst x) (snd x)) by (intros x Hx; apply BOK5; apply in_or_app; left; exact Hx).
    assert (BS5 : forall x, In x (PML.srep_blocks reps) -> block_range L (fst x) (snd x)) by (intros x Hx; apply BOK5; apply in_or_app; right; apply in_or_app; left; exact Hx).
    match type of AG6 with TK.samem (L5.outside ?F) _ _ =>
      assert (WS6 : TK2.w_si L F) by (intros w Hw; destruct Hw as [<-|[<-|[]]]; cbn [fst snd]; [left; lia | right; lia]) end.
    pose proof (pers_x _ M5 M6 reps AG6 ltac:(intros i Hi; rl_out) ltac:(eapply (TK2.str_cov_out L LAY); [exact (proj2 Htop) | intros i Hi; rl_out | exact WS6 | exact BS5]) PE) as PE6.
    assert (FR6 : TK2.FR L LB sp SS PML.in_foot11 M M6).
    { eapply TK2.FR_samem; [exact FR5 | exact AG6 | |].
      - intros a Ha HC HF HE w Hw Hin. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
        + destruct HC as [(x & Hx & Hr) | [(X1 & X2) | (X1 & X2)]]; [destruct (BOK0 x Hx) as (B0 & B1 & B2 & B3 & B4); lia | lia | rewrite IHI in X1; lia].
        + apply HF. foot_in.
      - intros a _ X. apply MG6. exact X. }
    assert (HH6 : hi_heap HI (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) cr4 M6 (m_vmmaps model5)).
    { apply (TK2.heap_pure_write L HI HIok LAY _ _ M5 M6 _ _ HH5 ltac:(lia) AG6 MG6). intros a Hz Ha.
      destruct (not_outside _ a Ha) as (w & Hw & Hin). destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; [left; lia | right; lia]. }
    assert (LSX : exists g', g' <> PML.LS0 /\ PML.ls_ok g' M6).
    { apply (TK2.mid_to_ls _ M5 M6 AG6); [| | exact MID5 | exact U8g].
      - intros a HF HN w Hw Hin. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; [|lia].
        destruct HF as (iv & Hiv & Hr). unfold PML.ll_foot_csrc in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; lia|]). destruct Hiv.
      - intros a Ha w Hw Hin. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; unfold PML.IMG_RO_HI in Ha; lia. }
    destruct LSX as (g6 & G6 & LS6).
    assert (IS6 : PML.isrc_at M6 (sp - 328) rep (PML.srep_data (sp - 328 + 80) rep) 0).
    { apply (TK2.isrc_at_x _ M5 M6 AG6); [lia | intros i Hi; rl_out | | exact IS5].
      eapply (TK2.str_cov_out L LAY); [exact (proj2 Htop) | intros i Hi; rl_out | exact WS6 | exact BR5]. }
    assert (U6 : L5.u32_at RSEGS M6 (sp - 344) 0) by (apply (TK.u32_samem _ M5 M6 _ _ AG6); [lia | intros i Hi; rl_out | exact U5]).
    apply (HCS.s_h_rsyscat FPM fx6 R6 M6 model5 K sp PML.OBJ_SYSTEM_CATEGORY Hh5 Hl5 Hfp6 H2_6 SPOK A0); [unfold PML.OBJ_SYSTEM_CATEGORY; lia | apply (frame_def M6 (sp - 336) 8 FR6); lia |].
    intros fx7 R7 M7 Hfp7 H2_7 H1_7 H10_7 H11_7 H12_7 KC7 U336 AG7 MG7.
    assert (AG7' : TK.samem (L5.outside [(sp - 336, 8)]) M6 M7) by (to_out AG7 (sp - 336) 8).
    assert (FC7 : forall w, In w [(sp - 336, 8)] -> sp - SS <= fst w /\ fst w + snd w <= sp - 56 /\ 0 <= snd w) by (intros w [<-|[]]; cbn [fst snd]; lia).
    assert (BI : forall x, In x (PML.srep_blocks reps) -> In x (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB)) by (intros x Hx; apply in_or_app; right; apply in_or_app; left; exact Hx).
    pose proof (step_out_g _ reps M6 M7 _ _ _ AG7' MG7 FC7 BI PE6 FR6 HH6) as (PE7 & FR7 & HH7 & SV7 & WS7).
    assert (LS7 : PML.ls_ok g6 M7) by (eapply TK2.ls_ok_x; [exact AG7' | exact SV7 | exact LS6]).
    assert (IS7 : PML.isrc_at M7 (sp - 328) rep (PML.srep_data (sp - 328 + 80) rep) 0).
    { apply (TK2.isrc_at_x _ M6 M7 AG7'); [lia | intros i Hi; rl_out | | exact IS6].
      eapply (TK2.str_cov_out L LAY); [exact (proj2 Htop) | intros i Hi; rl_out | exact WS7 | exact BR5]. }
    assert (EC7 : PML.ec_at M7 (sp - 344) 0).
    { split; [apply (TK.u32_samem _ M6 M7 _ _ AG7'); [lia | intros i Hi; rl_out | exact U6]|].
      split; [apply (frame_def M7 (sp - 344) 16 FR7); lia | left; reflexivity]. }
    exact (rl_cctor fx7 R7 M7 model5 cr4 reps rep g6 Hfp7 H2_7 H1_7 H10_7 H11_7 H12_7 (KT _ _ _ KO6 (KCO _ _ KC7)) PE7 BS BR LEN FR7 BV5 MOK5 HH7 LS7 G6 IS7 EC7 CR C1 C2).
Qed.

Lemma rl_iss : forall (fx3 : FPState) R3 M3 model3 cr2 reps,
  PML.fp_ok fx3 -> getr R3 2%bv = Z_to_bv 64 (sp - 1040) -> getr R3 1%bv = Z_to_bv 64 HCT.R_ISS ->
  getr R3 10%bv = Z_to_bv 64 (sp - 328) -> getr R3 11%bv = Z_to_bv 64 (sp - 56) -> getr R3 12%bv = Z_to_bv 64 8 ->
  TK.keepsR HCS.KOH R R3 ->
  pers reps M3 -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) -> Z.of_nat (length (PML.srep_chars reps)) = n ->
  TK2.FR L LB sp SS PML.in_foot11 M M3 -> model_but_vm model model3 -> PML.model_ok model3 ->
  hi_heap HI (PML.srep_blocks reps ++ LB) cr2 M3 (m_vmmaps model3) ->
  (PML.ls_ok PML.LS0 M3 \/ PMS.statics_mid M3) ->
  credit_le (PMCS.pm_credit_c L n) cr -> fst cr - hl_k_per_malloc L <= fst cr2 -> snd cr - (n + 10 + hl_b_overhead L) <= snd cr2 ->
  srealizes RSEGS SCFG (@PML.cfg fx3 R3 PML.PC_ISS_CTOR M3 model3) K.
Proof.
  intros fx3 R3 M3 model3 cr2 reps Hfp H2 H1 H10 H11 H12 KO PE BS LEN FR3 BV3 MOK3 HH3 ST3 CR C1 C2.
  pose proof SCRv as (SC1 & SC2 & SC3 & SC4 & SC5 & SC6 & SC7 & SC8 & SC9).
  pose proof SPOK as (Hsp & Hal).
  pose proof (PmLayout.ly_kpm L LAY) as KP. pose proof (PmLayout.ly_bov L LAY) as BP.
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH3) as BOK3.
  pose proof (copy_cap_bounds n (proj1 Plen)) as CCB.
  pose proof CR as CR0. unfold credit_le, PMCS.pm_credit_c in CR. cbn [fst snd] in CR.
  pose proof PE as (_ & _ & _ & _ & STR3).
  eapply (ISS (PML.srep_blocks reps ++ LB) cr2 (sp - 328) (sp - 56) (sp - 1040) HCT.R_ISS reps fx3 R3 M3 model3 K HH3 MOK3 HK0 Hfp).
  - cbv beta. change (80 + Z.max PMS.CTOR_SCR PMS.ISLAND_SCR) with PMS.ISS_SCR. rewrite LEN.
    split.
    { apply mk_entry; [exact H1 | apply ra_ok_lit; [unfold HCT.R_ISS; lia | reflexivity] | exact H2 | rewrite (KO 4%bv KO_4); exact Ptp |].
      apply (mk_stk LB sp SS PML.in_foot11 M M3); [exact FR3 | exact Hal | reflexivity | lia | exact SC3 | exact Hceil | exact Hsptop | exact Htop]. }
    split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact STR3|].
    split; [intros x Hx; apply in_or_app; left; exact Hx|]. split; [lia|].
    split; [oos Hal|]. split; [oos Hal|]. split; [unfold PML.apart; lia|].
    split; [apply (frame_def M3 (sp - 328) 272 FR3); lia|]. split; [apply (frame_def M3 (sp - 56) 24 FR3); lia|].
    split; [exact ST3|].
    unfold credit_ok. split; lia.
  - intros fx4 R4 M4 model4 LB4 cr4 LBk4 W4 Hfp4 (rep & CH & ISR & MID & -> & -> & FB & NB & EW) RP4 HP4 BV4 HH4.
    assert (WOK : w_ok W4) by (rewrite EW; unfold w_ok; wok).
    assert (S0 : 0 <= 80 + Z.max PMS.CTOR_SCR PMS.ISLAND_SCR) by (change (80 + Z.max PMS.CTOR_SCR PMS.ISLAND_SCR) with PMS.ISS_SCR; lia).
    pose proof (step_heap reps M3 M4 _ _ _ HP4 BOK3 (incl_refl _) S0 SC3 WOK PE FR3) as (PE4 & FR4 & AG4 & WS4).
    pose proof (L5C.model_but_vm_trans _ _ _ BV3 BV4) as BV4'.
    pose proof (mok_of _ _ BV4 MOK3) as MOK4. pose proof MOK4 as (Hh4 & Hl4 & Hm4).
    pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH4) as BOK4.
    assert (H2_4 : getr R4 2%bv = Z_to_bv 64 (sp - 1040)) by (rewrite (RP4 _ CS2); exact H2).
    assert (KO4 : TK.keepsR HCS.KOH R R4) by exact (KT _ _ _ KO (KSP _ _ RP4)).
    assert (RB : forall b, In b (PML.srep_blocks rep) -> 0 <= snd b <= n + 52) by (intros x Hx; destruct (FB x Hx) as (_ & E & _); rewrite E, LEN; lia).
    assert (LENr : Z.of_nat (length (PML.srep_chars rep)) = n) by (rewrite CH; exact LEN).
    assert (CRB : fst cr - 2 * hl_k_per_malloc L <= fst cr4 /\ snd cr - (2 * n + 62 + 2 * hl_b_overhead L) <= snd cr4).
    { destruct rep as [s | cap p s]; cbn [PML.srep_blocks] in FB, NB.
      - rewrite (NB eq_refl). lia.
      - destruct (FB (p, cap) (or_introl eq_refl)) as (_ & E & ->). cbn [fst snd] in E. unfold debit. cbn [fst snd]. rewrite E, LEN. lia. }
    assert (BR4 : forall x, In x (PML.srep_blocks rep) -> block_range L (fst x) (snd x)) by (intros x Hx; apply BOK4; apply in_or_app; left; exact Hx).
    apply (HCS.s_h_riss FPM fx4 R4 M4 model4 K sp Hh4 Hl4 Hfp4 H2_4 SPOK (frame_def M4 (sp - 344) 4 FR4 ltac:(lia) ltac:(lia))).
    intros fx5 R5 M5 Hfp5 H2_5 H1_5 KC5 U5 AG5 MG5.
    assert (AG5' : TK.samem (L5.outside [(sp - 344, 4)]) M4 M5) by (to_out AG5 (sp - 344) 4).
    assert (FC5 : forall w, In w [(sp - 344, 4)] -> sp - SS <= fst w /\ fst w + snd w <= sp - 56 /\ 0 <= snd w) by (intros w [<-|[]]; cbn [fst snd]; lia).
    assert (BI : forall x, In x (PML.srep_blocks reps) -> In x (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB)) by (intros x Hx; apply in_or_app; right; apply in_or_app; left; exact Hx).
    pose proof (step_out_g _ reps M4 M5 _ _ _ AG5' MG5 FC5 BI PE4 FR4 HH4) as (PE5 & FR5 & HH5 & SV5 & WS5).
    assert (MID5 : PMS.statics_mid M5) by (eapply TK2.statics_mid_x; [exact AG5' | exact SV5 | exact MID]).
    assert (IS5 : PML.isrc_at M5 (sp - 328) rep (PML.srep_data (sp - 328 + 80) rep) 0).
    { apply (TK2.isrc_at_x _ M4 M5 AG5'); [lia | intros i Hi; rl_out | | exact ISR].
      eapply (TK2.str_cov_out L LAY); [exact (proj2 Htop) | intros i Hi; rl_out | exact WS5 | exact BR4]. }
    exact (rl_syscat fx5 R5 M5 model4 cr4 reps rep Hfp5 H2_5 H1_5 (KT _ _ _ KO4 (KCO _ _ KC5)) PE5 BS RB LENr FR5 BV4' MOK4 HH5 MID5 IS5 U5 CR0 (proj1 CRB) (proj2 CRB)).
Qed.

Lemma rl_hstep0 : forall M1 M2 LBk scr W, L5C.hpres L LBk (sp - 1040) scr W M1 M2 -> incl LB LBk -> 0 <= scr -> 1040 + scr <= SS ->
  (forall w, In w W -> sp - 1040 <= fst w /\ fst w + snd w <= sp) ->
  TK2.FR L LB sp SS PML.in_foot11 M M1 -> TK2.FR L LB sp SS PML.in_foot11 M M2.
Proof.
  intros M1 M2 LBk scr W HP INC H0 H1 HW (F1 & F2).
  pose proof SPOK as (Hsp & Hal).
  pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_errno L LAY) as ERR.
  destruct HP as (HK & HD & HC).
  split.
  - intros a Ha HCa HF HE. rewrite (HK a); [apply F1; assumption|].
    split; [exact Ha|]. split; [|split; [exact HE|]].
    + destruct HCa as [(x & Hx & Hr) | [(X1 & X2) | (X1 & X2)]].
      * left. exists x. split; [apply INC; exact Hx | exact Hr].
      * right; left. split; lia.
      * right; right. split; assumption.
    + intros w Hw Hin. destruct (HW w Hw) as (W1 & W2). unfold L5.in_rng in Hin.
      destruct HCa as [(x & Hx & Hr) | [(X1 & X2) | (X1 & X2)]].
      * destruct (BOK0 x Hx) as (B0 & B1 & B2 & B3 & B4). lia.
      * lia.
      * rewrite IHI in X1. lia.
  - intros a Ha. destruct (Z_lt_le_dec a (sp - 1040 - scr)) as [Hlt|Hge].
    + apply HC; [lia | right; left; split; lia | unfold in_errno; rewrite ERR; lia | apply F2; lia].
    + destruct (Z_lt_le_dec a (sp - 1040)) as [Hlt2|Hge2].
      * pose proof (HD (a - (sp - 1040 - scr)) ltac:(lia)) as X. replace (sp - 1040 - scr + (a - (sp - 1040 - scr))) with a in X by lia. exact X.
      * apply HC; [lia | right; left; split; lia | unfold in_errno; rewrite ERR; lia | apply F2; lia].
Qed.

Lemma rl_strinit : forall (fx1 : FPState) R1 M1 ptr,
  PML.fp_ok fx1 -> getr R1 2%bv = Z_to_bv 64 (sp - 1040) -> getr R1 1%bv = Z_to_bv 64 HCT.R_STRINIT -> getr R1 10%bv = Z_to_bv 64 (sp - 56) ->
  getr R1 11%bv = Z_to_bv 64 ptr -> getr R1 12%bv = Z_to_bv 64 n -> TK.keepsR HCS.KOH R R1 ->
  L5.u64_at RSEGS M1 (sp - 8) ra -> L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R 9%bv)) ->
  L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R 18%bv)) ->
  TK2.FR L LB sp SS PML.in_foot11 M M1 -> hi_heap HI LB cr M1 (m_vmmaps model) -> PML.model_ok model ->
  (PML.ls_ok PML.LS0 M1 \/ PMS.statics_mid M1) ->
  L5.bytes_at RSEGS M1 ptr (map bv_unsigned payload) -> L5.defined M1 ptr n ->
  ((length payload = 0%nat) \/ (0 < n /\ In (ptr, n) LB)) ->
  credit_le (PMCS.pm_credit_c L n) cr ->
  srealizes RSEGS SCFG (@PML.cfg fx1 R1 PML.PC_STRINIT M1 model) K.
Proof.
  intros fx1 R1 M1 ptr Hfp H2 H1 H10 H11 H12 KO W8 W16 W24 W32 FR1 HH1 MOK ST1 BY1 DF1 PL CR.
  pose proof SCRv as (SC1 & SC2 & SC3 & SC4 & SC5 & SC6 & SC7 & SC8 & SC9).
  pose proof SPOK as (Hsp & Hal).
  pose proof (PmLayout.ly_kpm L LAY) as KP. pose proof (PmLayout.ly_bov L LAY) as BP.
  pose proof (str_cap_bounds n (proj1 Plen)) as SCB.
  pose proof CR as CR0. unfold credit_le, PMCS.pm_credit_c in CR. cbn [fst snd] in CR.
  assert (STK1 : L5C.stk (hl_sptop L) M1 (sp - 1040) (48 + PMS.OPNEW_SCR))
    by (apply (mk_stk LB sp SS PML.in_foot11 M M1); [exact FR1 | exact Hal | reflexivity | lia | lia | exact Hceil | exact Hsptop | exact Htop]).
  eapply (STRINIT LB cr (sp - 56) ptr (sp - 1040) HCT.R_STRINIT (map bv_unsigned payload) fx1 R1 M1 model K HH1 MOK HK0 Hfp).
  - cbv beta. rewrite length_map. change (Z.of_nat (length payload)) with n.
    split; [apply mk_entry; [exact H1 | apply ra_ok_lit; [unfold HCT.R_STRINIT; lia | reflexivity] | exact H2 | rewrite (KO 4%bv KO_4); exact Ptp | exact STK1]|].
    split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [lia|]. split; [exact BY1|]. split; [exact DF1|].
    split; [oos Hal|]. split; [apply (frame_def M1 (sp - 56) 24 FR1); lia|].
    split.
    { destruct PL as [X|(X & Y)]; [left; apply length_zero_iff_nil; rewrite length_map; exact X | right; exists (ptr, n); split; [exact Y | cbn [fst snd]; lia]]. }
    intros HL. unfold credit_ok. split; lia.
  - intros fx2 R2 M2 model2 LB2 cr2 LBk2 W2 Hfp2 (EW & -> & POST) RP2 HP2 BV2 HH2.
    cbv zeta in POST. rewrite length_map in POST. change (Z.of_nat (length payload)) with n in POST.
    subst W2.
    assert (RPX : exists reps, PML.str_at_w M2 (sp - 56) reps /\ LB2 = PML.srep_blocks reps ++ LB /\ PML.srep_chars reps = map bv_unsigned payload /\
              (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) /\ fst cr - hl_k_per_malloc L <= fst cr2 /\ snd cr - (n + 10 + hl_b_overhead L) <= snd cr2).
    { destruct POST as [(_ & S & -> & ->) | (_ & p & S & _ & -> & ->)].
      - exists (PML.SShort (map bv_unsigned payload)). split; [exact S|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros x []|]. lia.
      - exists (PML.SLong (PML.str_cap n) p (map bv_unsigned payload)). split; [exact S|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros x [<-|[]]; cbn [snd]; lia|]. unfold debit. cbn [fst snd]. lia. }
    destruct RPX as (reps & STR2 & -> & CHR & BS & C1 & C2).
    pose proof (mok_of _ _ BV2 MOK) as MOK2. pose proof MOK2 as (Hh2 & Hl2 & Hm2).
    assert (AGH : TK.samem (TK2.keepH L LB [(sp - 56, 24)] (sp - 1040) (48 + PMS.OPNEW_SCR)) M1 M2)
      by exact (TK2.hpres_samem L LAY _ _ _ _ M1 M2 HP2 BOK0 STK1 ltac:(lia)).
    assert (KH : forall i, sp - 32 <= i < sp -> TK2.keepH L LB [(sp - 56, 24)] (sp - 1040) (48 + PMS.OPNEW_SCR) i) by (intros i Hi; split; [rl_out | left; lia]).
    assert (PE2 : pers reps M2).
    { split; [apply (TK.u64_samem _ M1 M2 _ _ AGH); [lia | intros i Hi; apply KH; lia | exact W8]|].
      split; [apply (TK.u64_samem _ M1 M2 _ _ AGH); [lia | intros i Hi; apply KH; lia | exact W16]|].
      split; [apply (TK.u64_samem _ M1 M2 _ _ AGH); [lia | intros i Hi; apply KH; lia | exact W24]|].
      split; [apply (TK.u64_samem _ M1 M2 _ _ AGH); [lia | intros i Hi; apply KH; lia | exact W32]|].
      exact STR2. }
    assert (FR2 : TK2.FR L LB sp SS PML.in_foot11 M M2)
      by (apply (rl_hstep0 M1 M2 LB (48 + PMS.OPNEW_SCR) [(sp - 56, 24)] HP2 (incl_refl _)); [lia | lia | intros w [<-|[]]; cbn [fst snd]; lia | exact FR1]).
    assert (SCH : TK2.statics_cov (TK2.keepH L LB [(sp - 56, 24)] (sp - 1040) (48 + PMS.OPNEW_SCR))) by st_cov.
    assert (ST2 : PML.ls_ok PML.LS0 M2 \/ PMS.statics_mid M2)
      by (destruct ST1 as [X|X]; [left; eapply TK2.ls_ok_x; [exact AGH | exact SCH | exact X] | right; eapply TK2.statics_mid_x; [exact AGH | exact SCH | exact X]]).
    assert (H2_2 : getr R2 2%bv = Z_to_bv 64 (sp - 1040)) by (rewrite (RP2 _ CS2); exact H2).
    assert (KO2 : TK.keepsR HCS.KOH R R2) by exact (KT _ _ _ KO (KSP _ _ RP2)).
    assert (LEN2 : Z.of_nat (length (PML.srep_chars reps)) = n) by (rewrite CHR, length_map; reflexivity).
    apply (HCS.s_h_rstrinit FPM fx2 R2 M2 model2 K sp Hh2 Hl2 Hfp2 H2_2 SPOK).
    intros fx3 R3 M3 Hfp3 H2_3 H1_3 H10_3 H11_3 H12_3 KC3 AG3 MG3.
    pose proof (samem_all _ _ AG3) as E3. subst M3.
    exact (rl_iss fx3 R3 M2 model2 cr2 reps Hfp3 H2_3 H1_3 H10_3 H11_3 H12_3 (KT _ _ _ KO2 (KCO _ _ KC3)) PE2 BS LEN2 FR2 BV2 MOK2 HH2 ST2 CR0 C1 C2).
Qed.
Lemma run_ok : forall (fx : FPState) (g : PML.ls_state) ptr,
  PML.fp_ok fx -> getr R 1%bv = Z_to_bv 64 ra -> getr R 10%bv = Z_to_bv 64 ptr -> getr R 11%bv = Z_to_bv 64 n ->
  ((length payload = 0%nat) \/ (0 < n /\ In (ptr, n) LB)) -> rdn RSEGS M (Z_to_bv 64 ptr) (length payload) = Some payload ->
  credit_le (PMCS.pm_credit_c L n) cr -> PML.ls_ok g M -> hi_heap HI LB cr M (m_vmmaps model) -> PML.model_ok model ->
  (forall a, sp - SS <= a < sp -> M (Z_to_bv 64 a) <> None) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_LIB M model) K.
Proof.
  intros fx g ptr Hfp Hra Hptr Hn Hpl Hrdn Hcr Hls Hheap Hmok Hdef.
  pose proof SCRv as (SC1 & SC2 & SC3 & SC4 & SC5 & SC6 & SC7 & SC8 & SC9).
  pose proof SPOK as (Hsp & Hal).
  pose proof Hmok as (Hh & Hl & Hm).
  pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  apply (HCS.s_h_entry FPM fx R M model K sp ra Hh Hl Hfp Psp Hra).
  - destruct Prok as (X & _). lia.
  - exact SPOK.
  - intros i Hi. apply Hdef. lia.
  - intros fx1 R1 M1 Hfp1 H2_1 H1_1 H10_1 H11_1 H12_1 KC1 W8 W16 W24 W32 AG1 MG1.
    rewrite Hptr in H11_1. rewrite Hn in H12_1.
    assert (FR1 : TK2.FR L LB sp SS PML.in_foot11 M M1).
    { eapply TK2.FR_samem; [split; [intros; reflexivity | exact Hdef] | exact AG1 | |].
      - intros a Ha HC HF HE Hin. destruct HC as [(x & Hx & Hr) | [(X1 & X2) | (X1 & X2)]]; [destruct (BOK0 x Hx) as (B0 & B1 & B2 & B3 & B4); lia | lia | rewrite IHI in X1; lia].
      - intros a _ X. apply MG1. exact X. }
    assert (HH1 : hi_heap HI LB cr M1 (m_vmmaps model)) by exact (TK2.heap_stack_write L HI HIok LAY LB cr M M1 _ (sp - 1040) sp Hheap ltac:(lia) ltac:(lia) ltac:(lia) AG1 MG1).
    assert (SCX : TK2.statics_cov (fun a => ~ (sp - 1040 <= a < sp))) by (apply TK2.statics_cov_lo; intros a Ha; lia).
    assert (ST1 : PML.ls_ok PML.LS0 M1 \/ PMS.statics_mid M1).
    { destruct g; [left; eapply TK2.ls_ok_x; [exact AG1 | exact SCX | exact Hls]
                  | right; eapply TK2.statics_mid_x; [exact AG1 | exact SCX | refine (ls_mid _ M _ Hls); discriminate] ..]. }
    assert (BD1 : L5.bytes_at RSEGS M1 ptr (map bv_unsigned payload) /\ L5.defined M1 ptr n).
    { destruct Hpl as [L0 | (Hpos & Hin)].
      - split.
        + intros i Hi. rewrite length_map, L0 in Hi. lia.
        + intros i Hi. exfalso. change n with (Z.of_nat (length payload)) in Hi. rewrite L0 in Hi. cbn in Hi. lia.
      - destruct (BOK0 _ Hin) as (B0 & B1 & B2 & B3 & B4). cbn [fst snd] in B0, B1, B2, B3, B4.
        split.
        + apply (TK.bytes_samem _ M M1 _ _ AG1).
          * lia.
          * rewrite length_map. change (Z.of_nat (length payload)) with n. lia.
          * rewrite length_map. change (Z.of_nat (length payload)) with n. intros i Hi. lia.
          * apply (L5C.rdn_bytes_at RSEGS M payload ptr); [lia | change (Z.of_nat (length payload)) with n; lia | exact Hrdn].
        + destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _). destruct (Hwf _ Hin) as (_ & D & _). exact D. }
    destruct BD1 as (BY1 & DF1).
    exact (rl_strinit fx1 R1 M1 ptr Hfp1 H2_1 H1_1 H10_1 H11_1 H12_1 (KCO _ _ KC1) W8 W16 W24 W32 FR1 HH1 Hmok ST1 BY1 DF1 Hpl Hcr).
Qed.
End Run.

Theorem lib_ok : forall Lay, PMCS.lib_spec_c L HI STRTOD_SCR Lay.
Proof.
  intros Lay (LH & LE & LG & HSS & LF & LC & LRW).
  unfold PMS.lib_call_ok_fp.
  intros fx g LB cr sp ptr ra pyld R M model K Hfp Hpre Hheap Hh Hl Hmat HK Hcont.
  destruct Hpre as [Pra Praok Psp Pgp Ptp Pa0 Pa1 Plen Pptr Ppyld Pstk Pcr Pst].
  pose proof (PmLayout.ly_segs L LAY) as SEG. pose proof (PmLayout.ly_tp L LAY) as TPe.
  rewrite LH, TPe in Ptp. rewrite LH, SEG in Ppyld. rewrite LH in Pstk. rewrite LC in Pcr.
  destruct Pstk as (Sal & Sceil & Stop & Shi & _ & Sdef).
  assert (Plen' : 0 <= Z.of_nat (length pyld) < 2 ^ 26) by lia.
  assert (Prok' : L5.ra_ok ra) by (unfold L5.ra_ok; exact Praok).
  assert (ISSv : PMS.ISS_SCR = 9344) by reflexivity.
  assert (SPOK' : CK.spok sp) by (unfold CK.spok; unfold PMCS.LIB_SCR_C in HSS; split; [lia | exact Sal]).
  assert (BOK0 : TK2.blocks_ok L LB) by exact (TK2.blocks_ok_heap L HI HIok LB cr M _ Hheap).
  assert (Hmok : PML.model_ok model) by (split; [exact Hh | split; [exact Hl | exact Hmat]]).
  assert (Pptr' : (length pyld = 0%nat) \/ (0 < Z.of_nat (length pyld) /\ In (ptr, Z.of_nat (length pyld)) LB)) by (destruct Pptr as [(X & _)|X]; [left; exact X | right; exact X]).
  assert (CONT : forall (fx' : FPState) (g' : PML.ls_state) (R' : bvmap 5 word) (M' : mem) (model' : Model) (cr' : credit),
    PML.fp_ok fx' -> lib_post Lay PMS.pm_statics g' LB cr sp pyld R M R' M' cr' -> hi_heap HI LB cr' M' (m_vmmaps model') -> model_but_vm model model' ->
    srealizes RSEGS SCFG (@PML.cfg fx' R' ra M' model') K).
  { intros fx' g' R' M' model' cr' F1 F2 F3 F4. pose proof (Hcont fx' g' R' M' model' cr' F1 F2 F3 F4) as X.
    unfold lib_cfg in X. rewrite LH, SEG in X. exact X. }
  unfold lib_cfg. rewrite LH, SEG, LE.
  change (srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_LIB M model) K).
  eapply run_ok.
  all: first [ eassumption | exact Pst | exact Sdef ].
Qed.
End H.
End HNC.

