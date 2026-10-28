(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "True"; "False"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "Zpos"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "option"; "list"; "prod"; "pair"; "nil"; "nat"; "Some"; "false"; "None"; "fst"; "andb"; "negb"; "snd"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "modulo"; "sub"; "mul"; "eqb"; "opp"; "even"; "leb"; "of_nat"; "to_nat"; "ltb"; "lor"; "of_N"; "land"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "callee_saved"; "pre_fregs"; "pre_reg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "sobj"; "valuation"; "SVar"; "SPBranch"; "cell"; "obj_range"; "rw"; "eval"; "SAlu"; "rm"; "ob_base"; "obj_holds"; "ss_facts"; "ss_next"; "ss_lenient"; "DUnknown"; "soff"; "sstate"; "swf"; "c_off"; "c_width"; "mkCell"; "mkObj"; "ob_cells"; "c_val"; "rd"; "smatch"; "ss_objs"; "SExt"; "sprop_eqb"; "SPNot"; "ob_dflt"; "odefault"; "SPUle"; "holds"; "ob_hi"; "ob_lo"; "outside_all"; "reg_sv"; "rl"; "ro_addr"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_resv"; "FcsrFrm0"; "covered"; "enc_bytes"; "image_byte"; "mkSS"; "mkVal"; "rom_ok"; "sfcsr"; "ss_regs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs"; "pvar"; "PB2"; "PB3"; "CALL"; "P0"; "PA"; "POBJS"; "O_actv"; "O_usgv"; "O_metaA"; "O_metaAF"; "O_stk_frame"; "PB1"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G3.Mal_mslow_C.InstC"; "pd"; "K"; "LS"; "DS"; "obj_of"; "dlo"; "QC"; "dhi"; "dsF"; "DCtz"; "DNl"; "DSct"; "dcells"; "CALLX"; "DUsg0"; "drom"; "DAct0"; "DAct1"; "DUsg1"; "bonus"; "D05c"; "D0kc"; "D11c"; "D22c"; "D33c"; "D44c"; "D5ac"; "D5bc"; "D5oc"; "DMetaA"; "DMetaAF"; "NF0"; "SETS5"; "SETS5a"; "SETS5b"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "RsCut"; "lf_state"; "RsMem"; "sym_run"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_I0"; "zr1"; "zl1"; "pv"; "sc0"; "crb"; "kq"; "u1"; "j1"; "av1"; "cl"; "g0o"; "g1o"; "fr1"; "u0"; "zg0"; "zg1"; "N_all"; "rw1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "MR_P"; "NX"; "vkind"; "voff"; "vrsv"; "O_sct"; "E_p0"; "O_act"; "O_ctr"; "O_lock"; "E_stride"; "O_stk"; "CUTS"; "E_p"; "O_ctz"; "O_nl"; "lf0"; "mr_ret"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "below200"; "in_vars"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "tl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "astate"; "st_metas"; "NEST_FUEL"; "alloc_slot"; "am_avail"; "am_freed"; "ameta"; "mlookup"; "nth_slot"; "ss_hdr"; "st_init_done"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zholds"; "zsupported"; "psupported"; "zeval"; "toS"; "zl_of"; "zr_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sv_vars_all"; "state_vars_all"; "sprop_vars_all"; "agree_vals"; "obj_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G3.Mal_mslow_G.ReabG"; "NL"; "m'"; "oStk"; "oMeta"; "oSlot"; "Lf"; "rw'"; "rho'"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs.RS"; "C5"; "LF"; "L6"; "L0k"; "L0s"; "L5a"; "L5b"; "C1"; "C2"; "C3"; "C4"; "C5o"; "Ck"; "L1s"; "L2s"; "L3s"; "L4s"; "L6o"; "R0"; "L0"; "L1"; "L2"; "L3"; "L4"; "L5"; "Sok"; "d0"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab"; "POST"; "setp"; "m'"; "objs_matchb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "machine_state"; "wview"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "diffs_ok"; "with_mem"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "BC_NE"; "BC_EQ"; "ALU_AND"; "ALU_SLL"; "ALU_SRL"; "aluop"; "mulop"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "in_ranges_dec"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "wz"; "topL"; "byteview_of"; "malloc_stack"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_I1"; "zSt"; "kd"; "zG"; "N_all"; "sc"; "stv"; "D0"; "sp0"; "zl1"; "zr1"; "Q_stk"; "rho1"; "rw1"; "Q_act"; "Q_ctr"; "Q_lock"; "Q_meta"; "Q_slot"; "off"; "rl1"; "zE"; "zMem"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "MInv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G3.Mal_mslow_C.InstC.Leaf"; "mR"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "mem_kept"; "rd_of"; "EC_U"; "Pre_malloc"; "client_addr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_D"; "vo"; "vr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G3.Mal_mslow_G"; "slot_cells"; "stk_cells"; "meta_cells'"; "@Corelib.Init.Specif"; "sumbool"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "auxv_init"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs.RP"; "P5a"; "P5b"; "F3"; "F4"; "@Corelib.Init.Peano"; "lt"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "seg_base"; "seg_size"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost"; "malloc_class"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost"; "in_zone"; "as_ok_facts"; "slow_case"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_K"; "JC"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "ltb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "cell_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK"; "J_alloc_preI";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "U0"; "layout"; "le_byte"; "yields"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes"; "release_mem"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require stdpp.bitvector.bitvector.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.State.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.Riscv.Prelude.
Require LinuxProcessSemantics.Riscv.Instr.
Require LinuxProcessSemantics.Riscv.Decode.
Require LinuxProcessSemantics.Riscv.DecodeC.
Require LinuxProcessSemantics.Riscv.Sem.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMalloc.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_mslow_G.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quick2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_I1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_D.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RS.

Lemma ro_tables : ltac2:(tb__ "0|0|
S8S1S1dZ0R1A2S1eR1Z80A2A2S0ScS5dS2dS7aQ40S1cZ108ccR2A2A2A2SdA3F_;Fkk;").
Proof.
  intros kk Hk. exact (forall_range_dec (fun kk => ro_addr segsU (Z_to_bv 64 (0x108cc + kk))) 0 128 ltac:(vm_compute; reflexivity) kk ltac:(lia)).
Qed.

Lemma cell_bytes_sym : ltac2:(tb__ "0|3|
S36S11aS35S39S14S40S2dR5R4R3A4ScbS39R3S4cR4A1A3S15fR3S28S49R4A1A1A2S0SfS78Q8M0A1M1A1S4eR7S7aQ40M2S1cS1cS79G2S3cR8S3fR6A1A2A2S45R8S48R5A1A2A2S27R4A1A2A2A2S15G1S114G1R4S64S28S49R5A1A1S3cR8S4dR5A1A2A2S7aG0Z0A2A4A2A3F_;F_;F_;Fj;Fc;Fo;FmsX;FrhoX;").
Proof.
  intros rhoX msX o c j (Hb & _ & Hc & _) Hin Hj.
  pose proof (proj1 (Forall_forall _ _) Hc c Hin) as (C1 & C2 & C3).
  unfold obj_lo_of, obj_hi_of in *.
  pose proof (rd_bytes_nth msX (Z.to_nat (c_width c)) _ _ j C3 Hj) as R.
  unfold oaddr in R. rewrite Z_to_bv_unsigned in R.
  assert (W : bv_wrap 64 (bv_unsigned (eval rhoX (ob_base o)) + soff rhoX (c_off c)) = bv_unsigned (eval rhoX (ob_base o)) + soff rhoX (c_off c)).
  { apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
  rewrite W in R. apply R. lia.
Qed.

Lemma covered_dec : ltac2:(tb__ "0|1|
S36S10S39A1S8S158S63R3R2R1A3M0S2G0A1A2Foff;Fcs;FrhoX;").
Proof. intros rhoX cs off. unfold covered. apply Exists_dec. intros c. apply in_cell_dec. Qed.

Lemma dunk_byte : ltac2:(tb__ "0|4|
S36S11aS35S8S40S2dR4R3R2A4S0S55S54R3A1S44A3S1S1dS18S8S8S3aR6R4A2M0A3R3A2S1eR3S1bS8S8G0A3A2A2S1S4S78Q8A1M1G1S0SfG1A1M2S4eR7S7aQ40M3R5A2A2S15G1R1A2A3Lb;A2S2S0G2S11bS2dS119R6A1S7aG3R4A2A3S17G1A1A3A1A2F_;F_;F_;Fx;Fo;FmsX;FrhoX;").
Proof.
  intros rhoX msX o x HO Hd Hx. pose proof HO as (Hb & Hw & Hc & Hdf & _).
  unfold obj_range, obj_lo_of, obj_hi_of in *. cbn [fst snd] in Hx.
  set (b := bv_unsigned (eval rhoX (ob_base o))) in *.
  replace x with (b + (x - b)) by lia. split.
  - destruct (covered_dec rhoX (ob_cells o) (x - b)) as [C|NC].
    + unfold covered in C. apply Exists_exists in C as (c & Hcin & IC). unfold in_cell in IC.
      pose proof (cell_bytes_sym rhoX msX o c (Z.to_nat (x - b - soff rhoX (c_off c))) HO Hcin ltac:(lia)) as R.
      fold b in R. rewrite Z2Nat.id in R by lia. replace (b + soff rhoX (c_off c) + (x - b - soff rhoX (c_off c))) with (b + (x - b)) in R by lia.
      eexists. exact R.
    + specialize (Hdf (x - b) ltac:(lia) NC). rewrite Hd in Hdf. exact Hdf.
  - apply Hw; [lia|]. rewrite Hd. reflexivity.
Qed.

Lemma rd_of_at : ltac2:(tb__ "0|2|
S78Q40A1M0SfS78Q8A1A1M1F_;S11aG0S68S2dR2A2S0G1R4R2A1S119R3R2A2A3S0G1SedS2dR5R3A3S4eR4R3A2A3F_;F_;Fa;FmsX;Fm;").
Proof. intros. apply rd_of_eq_rd; assumption. Qed.
Lemma wok_of_at : ltac2:(tb__ "0|3|
S78Q40A1M0SfS78Q8A1M1A1M2F_;S11aG0S0G2R3R1A1S119R2R1A2A3S2S0G2S11bS2dS119R3A1R2A3S17G1A1A3A1S0ScSeeS2dR5R3A3SdA3F_;F_;Fa;FmsX;Fm;").
Proof. intros m msX a E W. rewrite (wok_of_mem m (ms_mem msX) a E). apply wok_of_wview. exact W. Qed.

Lemma shape_range : ltac2:(tb__ "0|0|
S36S35S35S0S32S3fR2A1S3fR1A1A3S0S32S59R3A1S59R2A1A3S0S32S58R4A1S58R3A1A3S0S11S8S8A2S3aR6R5A2S3aR6R4A2A3F_;F_;F_;Fb;Fa;FrhoX;").
Proof. intros rhoX a b E1 E2 E3. unfold obj_range, obj_lo_of, obj_hi_of. rewrite E1, E2, E3. reflexivity. Qed.

Lemma lor_low5 : ltac2:(tb__ "0|3|
S8S8S1dZ0M0R2A2M1S1G1S1eR2Z20M2A2A2S0S8S20R4G2A2G0A3S0S8S2aR5R4A2S1cR5R4A2A3F_;F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb Hm.
  assert (L0 : Z.land a b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_dec i 5) as [Hi5|Hi5].
    - replace a with ((a / 32) * 2 ^ 5) by (change (2 ^ 5) with 32; pose proof (Z.div_mod a 32 ltac:(lia)); lia).
      rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
      rewrite (Z.bits_above_log2 b i); [apply Bool.andb_false_r|lia|].
      apply (Z.le_lt_trans _ (Z.log2 31)); [apply Z.log2_le_mono; lia|]. cbn. lia. }
  rewrite <- Z.lxor_lor by exact L0. symmetry. apply Z.add_nocarry_lxor. exact L0.
Qed.

Definition meta_cells' : list cell := ltac2:(tb__ "0|2|
SeS39S4aS33Z10A1Z8M0S37P9cA1A3SeS39S4aS33Z18A1Z4M1S37P98A1A3SeS39S4aS33Z1cA1G1S37P9aA1A3SeS39S4aS33Z20A1G0S37P9bA1A3S13S39A1A3A3A3A3").
Definition stk_cells (kd0 : vkind) (o : voff) (r : vrsv) : list cell := ltac2:(tb__ "0|0|
S4cS114S35U0S50Sf8Vkd0;Vo;Vr;A3A1Sc1A4A1").
Definition slot_cells (kd0 : vkind) (o : voff) (r : vrsv) : list cell := ltac2:(tb__ "0|0|
S4cS114S35U6S50Sf8Vkd0;Vo;Vr;A3A1Sc1A4A1").

Lemma LF_objs : ltac2:(tb__ "0|1|
Sb8Sb9SbaS0S10S35A1S50Sf8R3R2R1A3A1SeS35S4bS37PaA1S37PfA1S33Z0A1S156R3R2R1A3S44A5SeS35SbfSb6A1SeS35SbeSb6A1SeS35SbdSb6A1SeS35SbbSb6A1SeS35S4bSe5P97A1S33Z10A1S33Z28A1S157S44A5SeS35S4bSbcR3A1S33N4A1M0S3dS11fSc0R3A1G0A3S155R3R2R1A3S44A5S13S35A1A3A3A3A3A3A3A3A3Fr;Fo;Fkd0;").
Proof. intros [| |] [|] [| | |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list sobj) l) end. Qed.

Lemma LF_misc : ltac2:(tb__ "0|1|
Sb8Sb9SbaS1S0S8S60Sf8R3R2R1A3M0A1Sc7Sb6A1A3S1S0S9S42G0A1Sb7A3S1S0S10S32A1S5fG0A1S30A3S1S0S69S5eG0A1S62A3S0SfS32A1S61G0A1S17S32A1A3A2A2A2A2Fr;Fo;Fkd0;").
Proof. intros [| |] [|] [| | |]; repeat split; match goal with |- ?l = _ => vm_cast_no_check (eq_refl l) end. Qed.

Lemma LF_regs : ltac2:(tb__ "0|3|
Sb8Sb9SbaS8S1S1dZ1R1A2S1dR1Z1fA2A2S0S32S5bSf8R5R4R3A3R2A2M0ScS32L_;M1S2fS28R2A1M2A1S31G2A1G1S23R2ZaA2Sc3R5R4A2G0Xcx2Xcx2A3F_;Fz;Fr;Fo;Fkd0;").
Proof.
  intros kd0 o r z Hz.
  pose proof (forall_range_dec (fun z => sv_eqb (reg_sv (LF kd0 o r) z)
     (if callee_saved (Z.to_nat z) then pre_reg (Z.to_nat z) else if z =? 10 then E_p kd0 o else reg_sv (LF kd0 o r) z)) 1 31
     ltac:(destruct kd0, o, r; vm_cast_no_check (@eq_refl bool true)) z ltac:(lia)) as H.
  apply sv_eqb_sound in H. exact H.
Qed.

Lemma LF_slot_cells_ok : ltac2:(tb__ "0|b|
Sb8Sb9SbaS1S0ScSccS39S39S19S19S19S19S19Se8Sc9S48R1A1M0A2SdfG0A1A2Se8Sc9S4dR1A1M1A2A2SdfG1A1A2S29Z0M2S49R1A1M3A2A2S26G3Z8A2A2Lc;S155R3R2R1A3M4A3SdA3S1S0ScScdS39S16cS4aS33N4A1Z1S33G2A1A3A1G4A3SdA3S0ScSccS39S39S19S32ScLx;M5G1S8S16Lz;S9S16bR1P64A2Lj;S126S32S32S16Lb;La;M6Lop;M7G7S127G6Lop;M8G8ScSaS32S16La;Lw;Lsgn;M9S9S32S8S16Lk;Li;Ll;MaX32x8G5G0S8S19S26S24S1fZ2Z3eA2A1R1A2S29R1G2A2A2Lz;S9S16Li;G7G7G8G8G9GaX32x8A2Lc;S156R3R2R1A3A3SdA3A2A2Fr;Fo;Fkd0;").
Proof. intros kd0 o r; repeat split; destruct kd0, o, r; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma C4_in : ltac2:(tb__ "0|0|
Sb8Sb9SbaScbS39S4aS33N4A1Z1S33Z0A1A3S155R3R2R1A3A3Fr;Fo;Fkd0;").
Proof.
  intros kd0 o r. destruct (LF_slot_cells_ok kd0 o r) as (_ & H & _).
  apply existsb_exists in H as (c & Hc & E). apply cell_eqb_sound in E. subst c. exact Hc.
Qed.

Section ReabG.

Variables (s0 s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta) (idx : Z) (ktr : list (kreq * Z)).
Variable rho : valuation.
Variables (b3 b16 : Z).
Hypothesis HW0 : WF s0.
Hypothesis HCS : slow_case s0 n.
Hypothesis HF : ltac2:(tb__ "0|0|
S167Vs;S165Vs0;Vn;A2Vn;Vg;Vam;Vidx;A6").
Hypothesis HUB : ub_same s0 s.
Hypothesis HYA : ltac2:(tb__ "0|0|
S172S11S8Sd3A2Sd6Sd5S165Vs0;Vn;A2Vn;Vs0;A4Vktr;S12S8Sd3Vidx;Vs;A4A4").
Hypothesis HLok : layout_ok L s.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S8S79Q40S3bVrho;PcA2A2Vn;A3").
Hypothesis Hb3 : 0 <= b3 < 256.
Hypothesis Hb16 : 0 <= b16 < 65536.
Hypothesis Hhdr : ltac2:(tb__ "0|1|
S8S8S0SfS11S8S8A2M0A1SdcSdbVam;Vidx;A2A1S15G0S12S8S8R2R1A4A2A3S1S0S8Vb3;R3A3S0S8Vb16;R2A3A2F_;Fh16;Fh3;").
Local Abbreviation sc := (@U.Mal_mslow__G2.Mal_mslow_I1.sc am).
Local Abbreviation stv := (@U.Mal_mslow__G2.Mal_mslow_I1.stv am).
Local Abbreviation zG := (@U.Mal_mslow__G2.Mal_mslow_I1.zG L g).
Local Abbreviation zMem := (@U.Mal_mslow__G2.Mal_mslow_I1.zMem L am).
Local Abbreviation zSt := (@U.Mal_mslow__G2.Mal_mslow_I1.zSt L am idx).
Local Abbreviation zE := (@U.Mal_mslow__G2.Mal_mslow_I1.zE L am idx).
Local Notation "§1§ h__" := (h__ s n am b3 b16) (at level 10, h__ global).
Local Abbreviation off := (§1§ U.Mal_mslow__G2.Mal_mslow_I1.off).
Local Abbreviation kd := (@U.Mal_mslow__G2.Mal_mslow_I1.kd am).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S16eS12aS13Sd1A1S15S11Sd1S8A2S12Sd1S8Vg;Vidx;A4A2S16fS14bVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Notation "§2§ h__" := (h__ s L n g am idx rho b3 b16) (at level 10, h__ global).
Local Abbreviation rw1 := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.rw1).
Local Abbreviation rw1_changed := (@U.Mal_mslow__G2.Mal_mslow_I1.rw1_changed).
Local Abbreviation rw1_other := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.rw1_other).
Local Abbreviation rl1 := (@U.Mal_mslow__G2.Mal_mslow_I1.rl1 rho).
Local Abbreviation rho1 := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.rho1).
Local Abbreviation zr1 := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.zr1).
Local Abbreviation zl1 := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.zl1).
Local Abbreviation R_all := (@U.Mal_mslow__G2.Mal_mslow_I1.R_all s0 s L n g am idx b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI).
Local Abbreviation ze_var := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_var).
Local Abbreviation ze_lit := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_lit).
Local Abbreviation ze_alu := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_alu).
Local Abbreviation ze_aluw := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_aluw).
Local Abbreviation ze_mul := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_mul).
Local Abbreviation ze_ext := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_ext).
Local Abbreviation ze_lbytes := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_lbytes).
Local Notation "§3§ h__" := (h__ s0 s L n g am idx rho b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation ze151 := (§3§ U.Mal_mslow__G2.Mal_mslow_I1.ze151).
Local Abbreviation ze_p0 := (§3§ U.Mal_mslow__G2.Mal_mslow_I1.ze_p0).
Local Abbreviation ze_actoff := (§3§ U.Mal_mslow__G2.Mal_mslow_I1.ze_actoff).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S1dZ1000S79Q40S3bVrho;PaA2A2M0A2S0S8S20G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S1dSe2Z40S79Q40S3bVrho;PfA2A2A2M0S24S12eA1A2S1dS24S1fZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S1dS12cVL;A1S1cS79Q40M0S3bVrho;PaA2A2Se2Z40S79G0S3bVrho;PfA2A2A2A2A2").
Variable m0 : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0S78Q40A1SfS78Q8A1A1F_;Vrd0;SedS2dVm0;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0S78Q40A1ScF_;Vwok0;SeeS2dVm0;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm0_sct : ltac2:(tb__ "0|1|
S8S1S1dZ0R1A2S1eR1Z60A2A2S0SfS78Q8A1M0A1Vm0;S7aQ40S1cZ108ecR2A2A2A1S17G0A1A3F_;Fkk;").
Hypothesis Hm3 : ltac2:(tb__ "0|2|
S0SfS78Q8M0A1M1A1SedS2dVm0;S7aQ40S21S12fVL;Vam;Vidx;A3Z3A2A2A3S15G1S7aG0Vb3;A2A2A3").
Hypothesis Hm16 : ltac2:(tb__ "0|3|
S14S15fR1U2M0A2S0SfS78Q8M1A1M2A1SedS2dVm0;S7aQ40S1cS21S12fVL;Vam;Vidx;A3Z2A2S27R2A1A2A2A3S15G2S7aG1S171Vb16;G0R2A3A2A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S12dSedS2dVm0;A2SeeS2dVm0;A2A2").
Local Abbreviation ev1 := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ev1).
Local Abbreviation Q_lock := (@U.Mal_mslow__G2.Mal_mslow_I1.Q_lock).
Local Abbreviation Q_ctr := (@U.Mal_mslow__G2.Mal_mslow_I1.Q_ctr).
Local Abbreviation Q_act := (@U.Mal_mslow__G2.Mal_mslow_I1.Q_act).
Local Abbreviation Q_sct := (@U.Mal_mslow__G2.Mal_mslow_I1.Q_sct).
Local Abbreviation Q_meta := (@U.Mal_mslow__G2.Mal_mslow_I1.Q_meta).
Local Abbreviation Q_slot := (@U.Mal_mslow__G2.Mal_mslow_I1.Q_slot am).
Local Abbreviation Q_stk := (@U.Mal_mslow__G2.Mal_mslow_I1.Q_stk).
Local Notation "§4§ h__" := (h__ s L n g am idx rho b3 b16 Hb3 Hb16 m0) (at level 10, h__ global).
Local Abbreviation soff_of_ev := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.soff_of_ev).
Local Abbreviation sp0 := (@U.Mal_mslow__G2.Mal_mslow_I1.sp0 rho).
Local Abbreviation D0 := (@U.Mal_mslow__G2.Mal_mslow_I1.D0 rho).
Local Abbreviation rng_stk := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.rng_stk).
Local Abbreviation rng_lock := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.rng_lock).
Local Abbreviation rng_ctr := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.rng_ctr).
Local Abbreviation rng_act := (@U.Mal_mslow__G2.Mal_mslow_I1.rng_act s0 s L n g am idx rho b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp m0).
Local Abbreviation rng_sct := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.rng_sct).
Local Notation "§5§ h__" := (h__ s0 s L n g am idx rho b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI m0) (at level 10, h__ global).
Local Abbreviation rng_meta := (§5§ U.Mal_mslow__G2.Mal_mslow_I1.rng_meta).
Local Abbreviation rng_slot := (§5§ U.Mal_mslow__G2.Mal_mslow_I1.rng_slot).
Local Abbreviation Zones := (@U.Mal_mslow__G2.Mal_mslow_I1.Zones s0 s L n g am idx rho b3 b16 HCS HF HLok Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hsp_high).
Local Abbreviation N_all := (@U.Mal_mslow__G2.Mal_mslow_I1.N_all am).
Local Abbreviation OBJS_eq := (@U.Mal_mslow__G2.Mal_mslow_I1.OBJS_eq).
Local Abbreviation S2 := (@U.Mal_mslow__G2.Mal_mslow_I1.S2 am).
Local Abbreviation R0_eq := (@U.Mal_mslow__G2.Mal_mslow_I1.R0_eq am).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S15aS2dVKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S10S147A1S148OF_;F_;").
Hypothesis HK : implK Kc K.
Variable mW : word -> option byte.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EV := (@U.Mal_mslow__G2.Mal_mslow_D.EV s L n g am idx rho b3 b16 mW).
Local Abbreviation Zv12 := (@U.Mal_mslow__G2.Mal_mslow_D.Zv12 s0 s L n g am idx rho b3 b16 HCS HF HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI).
Local Abbreviation Zv142 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv142).
Local Abbreviation Zv143 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv143).
Local Abbreviation Zv150 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv150).
Local Abbreviation Zv151 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv151).
Local Abbreviation Zv152 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv152).
Local Abbreviation Zv153 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv153).
Local Abbreviation Zv154 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv154).
Local Abbreviation Zv155 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv155).
Local Abbreviation Zv156 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv156).
Local Abbreviation Zv157 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv157).
Local Abbreviation Zv158 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv158).
Local Abbreviation ZE_S := (§3§ U.Mal_mslow__G2.Mal_mslow_D.ZE_S).
Local Abbreviation ZE_strideT := (§3§ U.Mal_mslow__G2.Mal_mslow_D.ZE_strideT).
Local Notation "§6§ h__" := (h__ s0 s L n g am idx rho b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp) (at level 10, h__ global).
Local Abbreviation ZE_and155 := (§6§ U.Mal_mslow__G2.Mal_mslow_D.ZE_and155).
Local Abbreviation ZE_strideM := (§3§ U.Mal_mslow__G2.Mal_mslow_D.ZE_strideM).
Local Abbreviation ZE_sll := (§6§ U.Mal_mslow__G2.Mal_mslow_D.ZE_sll).
Local Notation "§7§ h__" := (h__ rho b3 b16 Hb3 Hb16) (at level 10, h__ global).
Local Abbreviation land_255 := (§7§ U.Mal_mslow__G2.Mal_mslow_D.land_255).
Local Abbreviation land_31' := (§7§ U.Mal_mslow__G2.Mal_mslow_D.land_31').
Local Abbreviation vo := (§1§ U.Mal_mslow__G2.Mal_mslow_D.vo).
Local Abbreviation vr := (§1§ U.Mal_mslow__G2.Mal_mslow_D.vr).
Local Abbreviation kd_cases := (@U.Mal_mslow__G2.Mal_mslow_D.kd_cases s0 s n g am idx rho b3 b16 HF Hb3 Hb16 Hsp).

Ltac zlits :=
  repeat match goal with
  | |- context [ (?x mod ?y) ] =>
      lazymatch x with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      lazymatch y with Zpos _ => idtac | Z.pow (Zpos _) (Zpos _) => idtac end;
      let vv := eval vm_compute in (x mod y) in change (x mod y) with vv
  end.
Ltac mlia := Z.to_euclidean_division_equations; lia.

Ltac zpeel side :=
  repeat (first
    [ rewrite ZE_strideT | rewrite ZE_strideM by side | rewrite ZE_and155 by side | rewrite ZE_sll | rewrite ZE_S
    | rewrite ze_alu | rewrite ze_aluw | rewrite ze_mul | rewrite ze_ext | rewrite ze_lbytes | rewrite ze_var | rewrite ze_lit ]).
Ltac flat_mods := repeat (first [rewrite Zplus_mod_idemp_l | rewrite Zplus_mod_idemp_r | rewrite Zminus_mod_idemp_l | rewrite Zminus_mod_idemp_r
                               | rewrite Zmult_mod_idemp_l | rewrite Zmult_mod_idemp_r | rewrite Zmod_mod]).

Ltac small_mods := repeat match goal with |- context [?a mod 2 ^ 64] =>
        lazymatch a with context [_ mod _] => fail | _ => idtac end;
        rewrite (Z.mod_small a (2 ^ 64)) by lia end.
Ltac zev2 side :=
  cbn [E_pn E_p E_p0 E_stride E_strideT E_strideM E_S E_sll E_X E_X0 E_X1 E_lowbit v];
  zpeel side; cbn [zalu Z.of_N];
  rewrite ?Zv12, ?Zv142, ?Zv143, ?Zv150, ?Zv151, ?Zv152, ?Zv153, ?Zv154, ?Zv155, ?Zv156, ?Zv157, ?Zv158;
  flat_mods; zlits;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by (clear; lia);
  rewrite ?land_255, ?land_31'.

Variables (tr : list event) (md : Model) (ms' : machine_state) (rhoF : valuation).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0S78Q40A1SfS78Q8A1A1F_;VmW;S3eVrho;A1A3").
Hypothesis Em0 : ltac2:(tb__ "0|0|
S0S78Q40A1SfS78Q8A1A1F_;Vm0;S3eVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0S149Vvm;S14aVmd;A1A3").

Hypothesis Hsm : ltac2:(tb__ "0|0|
S4fS2dVrho;S110S12S10S147A1S145Vtr;S146Vms;Vmd;A2A4A4").
Hypothesis Hsm0 : ltac2:(tb__ "0|0|
S4fS2dVrhoW;S109S130Vam;A1A1S12S10S147A1S145Vtr;S146Vms;Vmd;A2A4A4").
Hypothesis HagF : agrees rhoW rhoF.
Hypothesis HsmF : ltac2:(tb__ "0|0|
S4fS2dVrhoF;Sf8S130Vam;A1S153Vs;Vn;Vam;Vb3;Vb16;A5S154Vs;Vn;Vam;Vb3;Vb16;A5A3S12S10S147A1S145Vtr;S146Vms';Vmd;A2A4A4").

Definition Lf : sstate := ltac2:(tb__ "0|0|
Sf8S130Vam;A1S153Vs;Vn;Vam;Vb3;Vb16;A5S154Vs;Vn;Vam;Vb3;Vb16;A5A3").
Definition oStk : sobj := ltac2:(tb__ "0|0|
S4bS37PaA1S37PfA1S33Z0A1S156S130Vam;A1S153Vs;Vn;Vam;Vb3;Vb16;A5S154Vs;Vn;Vam;Vb3;Vb16;A5A3S44A5").
Definition oMeta : sobj := ltac2:(tb__ "0|0|
S4bSe5P97A1S33Z10A1S33Z28A1S157S44A5").
Definition oSlot : sobj := ltac2:(tb__ "0|2|
S4bSbcS130Vam;A1M0A1S33N4A1M1S3dS11fSc0G0A1G1A3S155G0S153Vs;Vn;Vam;Vb3;Vb16;A5S154Vs;Vn;Vam;Vb3;Vb16;A5A3S44A5").
Definition NL : list sobj := ltac2:(tb__ "0|0|
SeS35SbfSb6A1SeS35SbeSb6A1SeS35SbdSb6A1SeS35SbbSb6A1SeS35Sf2SeS35Sf3S13S35A1A3A3A3A3A3A3").
Definition m' : word -> option byte := ltac2:(tb__ "0|2|
S78Q40A1S158S128VrhoF;SefR1A3M0S2G0A1M1A2SfS78Q8A1A1L_;S129VrhoF;SefR1A3G0S119Vms';R2A2L_;G1S3eVrho;R2A2L_;X158x2La;").
Definition rw' (j : positive) : word := ltac2:(tb__ "0|2|
ScS78Q40A1L_;S19S26Z64M0SbVj;A1M1A2S29G1Z84A2A2S3cVrhoF;S5bSf4S21G1G0A2A2A2S3bVrho;Vj;A2Xcx2").
Definition rho' : valuation := ltac2:(tb__ "0|0|
S67Sf5S5cVrho;A1Sf0A3").

Lemma Lf_objs : ltac2:(tb__ "0|0|
S0S10S35A1S50Sf4A1SeS35Sf1SefA3A3").
Proof using . unfold Lf, NL, oStk, oMeta, oSlot. rewrite LF_objs. reflexivity. Qed.

Lemma rwF : ltac2:(tb__ "0|0|
S9S0ScSc9R1A1SdA3S0S78Q40A1S3bVrhoF;R2A2S13bVs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;R2AaA3F_;Fj;").
Proof using HagF. intros j Hj. destruct HagF as (A & _ & _). rewrite (A j Hj). reflexivity. Qed.
Lemma rmF : ltac2:(tb__ "0|0|
S78Q40A1S0SfS78Q8A1A1S3eVrhoF;R1A2S3eVrho;R1A2A3Fa;").
Proof using EmW HagF. intros a. destruct HagF as (_ & _ & C). rewrite C. unfold rhoW. cbn [rm U.Mal_mslow__G2.Mal_mslow_I1.rho1]. rewrite EmW. reflexivity. Qed.
Lemma rlF : ltac2:(tb__ "0|0|
S9S0S10S78Q8A1A1S5cVrhoF;R1A2S142Vrho;R1A2A3Fl;").
Proof using HagF. intros l. destruct HagF as (_ & B & _). rewrite (B l). reflexivity. Qed.
Lemma rw1_low : ltac2:(tb__ "0|0|
S9S16aR1P64A2S0S78Q40A1S13bVs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;R2AaS3bVrho;R2A2A3F_;Fj;").
Proof using Hb16 Hb3 Hsp.
  intros j Hj. apply rw1_other. unfold U.Mal_mslow__G2.Mal_mslow_I1.rw1_changed.
  repeat (rewrite (proj2 (Pos.eqb_neq j _)) by lia). reflexivity.
Qed.
Lemma rw'_low : ltac2:(tb__ "0|0|
S9S16aR1P64A2S0S78Q40A1Sf5R2A1S3bVrho;R2A2A3F_;Fj;").
Proof using Hb16 Hb3.
  intros j Hj. unfold rw'.
  replace ((100 <=? Z.pos j) && (Z.pos j <? 132))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
  reflexivity.
Qed.
Lemma agree_vals_rho' : ltac2:(tb__ "0|0|
SebS2eVrho;Sf6A3").
Proof using Hb16 Hb3. split; [|reflexivity]. intros j Hj. cbn [rw rho']. symmetry. apply rw'_low. exact Hj. Qed.

Lemma evF : ltac2:(tb__ "0|1|
S32S0ScSe8Sc9R1A2SdA3S0ScSdfR2A1SdA3S0S78Q40M0A1S3cVrhoF;R3A2S7aG0Se1S138Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S137Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9R3A3A2A3F_;F_;Fe;").
Proof using HagF. intros e Hv Hs. exact (EV rhoF e HagF Hv Hs). Qed.
Lemma evFu : ltac2:(tb__ "0|0|
S32S0ScSe8Sc9R1A2SdA3S0ScSdfR2A1SdA3S0S8S79Q40S3cVrhoF;R3A2A2Se1S138Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S137Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9R3A3A3F_;F_;Fe;").
Proof using HagF. intros e Hv Hs. rewrite (evF e Hv Hs). apply u64. apply zeval_range. exact Hs. Qed.
Lemma evW : ltac2:(tb__ "0|1|
S32S0ScSdfR1A1SdA3S0S78Q40M0A1S3cVrhoW;R2A2S7aG0Se1S138Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S137Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9R2A3A2A3F_;Fe;").
Proof using mW. intros e Hs. unfold rhoW. apply ev1. exact Hs. Qed.

Lemma rhoW_m0 : ltac2:(tb__ "0|0|
S0S36VrhoW;S13aVs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;Vm0;AaA3").
Proof using Em0 EmW. unfold rhoW. rewrite EmW, Em0. reflexivity. Qed.

Lemma rngF : ltac2:(tb__ "0|0|
S35S0ScSecSc9R1A2SdA3S0S11S8S8A2S3aVrhoF;R2A2S3aS13aVs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;Vm0;AaR2A2A3F_;Fo;").
Proof using Em0 EmW HagF.
  intros o Ho. rewrite <- rhoW_m0. apply (obj_range_agree_vars below200 rhoW rhoF o); [| |exact Ho].
  - intros j Hj. symmetry. apply rwF. exact Hj.
  - intros l. symmetry. apply rlF.
Qed.

Lemma RNF : ltac2:(tb__ "0|a|
S1S0S11S8S8A2M0S3aVrhoF;SbfSb6A1A2S12S8S8S1cZ5a3c8M1Z0M2A2S1cG1Z4M3A2A4A3S1S0G0S3aVrhoF;SbeSb6A1A2S12S8S8S1cG1Z14A2S1cG1Z18A2A4A3S1S0G0S3aVrhoF;SbdSb6A1A2S12S8S8S1cG1S1cS22Z8S133Vam;A1A2M4Z58A2A2S1cG1S1cG4Z60M5A2A2A4A3S1S0G0S3aVrhoF;SbbSb6A1A2S12S8S8S1cZ108ecM6G2A2S1cG6G5A2A4A3S1S0G0S3aVrhoF;Sf2A2S12S8S8S1cS131VL;Vg;A2M7Z10A2S1cG7Z28A2A4A3S1S0G0S3aVrhoF;Sf3A2S12S8S8S1cS12fVL;Vam;Vidx;A3M8N4A2S1cG8S21S134Vam;A1G3A2A2A4A3S0G0S3aVrhoF;Sf1A2S12S8S8S1cS136Vrho;A1M9S135Vrho;A1A2G9A4A3A2A2A2A2A2A2").
Proof using Em0 EmW HCS HF HMI HagF Hb16 Hb3 Hdepth Hhdr Hsp.
  assert (V : forall kd0, forallb (obj_vars_all below200) (Q_stk :: OBJS1_tail MR_P kd0) = true) by (intros [| |]; vm_cast_no_check (@eq_refl bool true)).
  pose proof (proj1 (forallb_forall _ _) (V kd)) as V'. rewrite OBJS_eq in V'. unfold N_all in V'.
  assert (X : forall o o', In o' (Q_stk :: [Q_lock; Q_ctr; Q_act; Q_sct; Q_meta; Q_slot]) ->
              ob_base o = ob_base o' -> ob_lo o = ob_lo o' -> ob_hi o = ob_hi o' -> obj_range rhoF o = obj_range (rho1 m0) o').
  { intros o o' Hin E1 E2 E3. rewrite (shape_range rhoF o o' E1 E2 E3). apply rngF. apply V'. exact Hin. }
  repeat match goal with |- _ /\ _ => split end.
  - rewrite (X _ Q_lock); [apply rng_lock | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_ctr); [apply rng_ctr | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_act); [apply rng_act | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_sct); [apply rng_sct | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_meta); [apply rng_meta | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_slot); [apply rng_slot | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_stk); [apply rng_stk | cbn; tauto | reflexivity ..].
Qed.

Lemma RZ : ltac2:(tb__ "0|e|
S1S1dZ0M0Vn;A2S1S1S1dG0S141Vs;Vn;Vam;Vb3;Vb16;A5M1A2S1dG1ZffA2A2S1S1dS1cS1cS22Z10M2G1A2Vn;A2Z4M3A2S134Vam;A1M4A2S1S1dG2G4A2S1S1eG4S1fZ2M5Z14A2A2S1S1dZ1000M6S144VL;Vam;A2M7A2S1S0S8S12fVL;Vam;Vidx;A3M8S1cS1cG7G2A2S22G4Vidx;A2M9A2A3S1S0S8S143VL;Vam;Vidx;A3MaS21S1cG8G4A2G3A2A3S1S1dG0G9A2S1S1dS1cGaG3A2S12cVL;A1MbA2S1S1eGbS1fG5Z2fA2A2S1S1dG6S131VL;Vg;A2McA2S1S1dS1cGcZ28A2GbA2S1S1dGbS1cS136Vrho;A1S135Vrho;A1A2A2S1S1dS1cZ5b000G2A2GbA2S1S1dG0S133Vam;A1MdA2S1eGdZ30A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using HCS HF HLok HMI Hb16 Hb3 Hhdr Hsp Hsp_high.
  pose proof R_all as R. pose proof Zones as (_ & SH & AC). repeat match goal with |- _ /\ _ => split end; try lia.
Qed.

Lemma R0_objs : ltac2:(tb__ "0|0|
S0S10S35A1S50S109S130Vam;A1A1A1SeS35S139S132Vam;A1A3A3").
Proof using . rewrite R0_eq. cbn [ss_objs]. unfold S2. reflexivity. Qed.
Lemma HO0 : ltac2:(tb__ "0|0|
S113S35S40S2dVrhoW;Vms;A3SeS35S139S132Vam;A1A3A3").
Proof using Hsm0.
  pose proof Hsm0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
  rewrite <- R0_objs. exact Hall.
Qed.
Lemma HOF : ltac2:(tb__ "0|0|
S113S35S40S2dVrhoF;Vms';A3SeS35Sf1SefA3A3").
Proof using HsmF.
  pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
  fold Lf in Hall. rewrite Lf_objs in Hall. exact Hall.
Qed.
Lemma Hfr0 : ltac2:(tb__ "0|0|
S78Q40A1S5aVrhoW;SeS35S139S132Vam;A1A3R1A3S0SfS78Q8A1A1S119Vms;R2A2S3eVrho;R2A2A3F_;Fa;").
Proof using EmW Hsm0.
  pose proof Hsm0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr.
  intros a Ha. rewrite <- R0_objs in Ha. rewrite (Hfr a Ha). unfold rhoW. cbn [rm U.Mal_mslow__G2.Mal_mslow_I1.rho1]. exact (f_equal (fun f => f a) EmW).
Qed.
Lemma HfrF : ltac2:(tb__ "0|0|
S78Q40A1S5aVrhoF;SeS35Sf1SefA3R1A3S0SfS78Q8A1A1S119Vms';R2A2S3eVrho;R2A2A3F_;Fa;").
Proof using EmW HagF HsmF.
  pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr.
  intros a Ha. fold Lf in Hfr. rewrite Lf_objs in Hfr. rewrite (Hfr a Ha). apply rmF.
Qed.

Lemma Hfr00 : ltac2:(tb__ "0|1|
S78Q40M0A1S1eS79G0R1A2S1cS136Vrho;A1S135Vrho;A1A2A2S0SfS78Q8A1A1S119Vms;R2A2S3eVrho;R2A2A3F_;Fa;").
Proof using Hb16 Hb3 Hsm.
  intros a Ha. pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr.
  apply Hfr. change (ss_objs Sok) with [O_stk_frame]. constructor; [|constructor].
  unfold obj_range, obj_lo_of, obj_hi_of, O_stk_frame. cbn [ob_base ob_lo ob_hi eval fst snd]. rewrite soff_lit_small by lia. unfold soff. cbn [eval].
  rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. change (toS 64 (bv_unsigned (rw rho 15%positive))) with D0. fold sp0. lia.
Qed.

Lemma Hrom0 : rom_ok segsU ms. Proof using Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). Qed.
Lemma HromF : rom_ok segsU ms'. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.
Lemma HroF : ro_clear segsU ms'. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmF)))))). Qed.
Lemma Hro0 : ro_clear segsU ms. Proof using Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm)))))). Qed.

Lemma m'_in : ltac2:(tb__ "0|0|
S78Q40A1S128VrhoF;SefR1A3S0SfS78Q8A1A1Sf0R2A1S119Vms';R2A2A3F_;Fa;").
Proof using . intros a Ha. unfold m'. destruct (in_ranges_dec rhoF NL a) as [|N]; [reflexivity|]. exfalso. exact (N Ha). Qed.
Lemma m'_out : ltac2:(tb__ "0|0|
S78Q40A1S2S128VrhoF;SefR1A3A1S0SfS78Q8A1A1Sf0R2A1S3eVrho;R2A2A3F_;Fa;").
Proof using . intros a Ha. unfold m'. destruct (in_ranges_dec rhoF NL a) as [Y|]; [|reflexivity]. exfalso. exact (Ha Y). Qed.

Lemma NL_cases : ltac2:(tb__ "0|8|
S78Q40M0A1S128VrhoF;SefR1A3S79G0R2A2S8S3S1S1dZ5a3c8M1R1A2S1eR1S1cG1Z4M2A2A2A2S3S1S1dS1cG1Z14A2R1A2S1eR1S1cG1Z18A2A2A2S3S1S1dS1cG1S1cS22Z8S133Vam;A1A2M3Z58A2A2R1A2S1eR1S1cG1S1cG3Z60M4A2A2A2A2S3S1S1dZ108ecM5R1A2S1eR1S1cG5G4A2A2A2S3S1S1dS1cS131VL;Vg;A2M6Z10A2R1A2S1eR1S1cG6Z28A2A2A2S1S1dS21S12fVL;Vam;Vidx;A3M7G2A2R1A2S1eR1S21S1cG7S134Vam;A1A2G2A2A2A2A2A2A2A2A2Tx;F_;Fa;").
Proof using Em0 EmW HCS HF HMI HagF Hb16 Hb3 Hdepth Hhdr Hsp.
  intros a (o & Ho & R) x. pose proof RNF as (R2 & R3 & R4 & R5 & R7 & R8 & R9).
  unfold NL in Ho. cbn [In] in Ho.
  destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    rewrite ?R2, ?R3, ?R4, ?R5, ?R7, ?R8 in R; cbn [fst snd] in R; subst x; lia.
Qed.

Lemma NL_below_stack : ltac2:(tb__ "0|1|
S78Q40M0A1S128VrhoF;SefR1A3S1eS79G0R2A2S1cS136Vrho;A1S135Vrho;A1A2A2F_;Fa;").
Proof using Em0 EmW HCS HF HLok HMI HagF Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high. intros a Ha. pose proof RZ as Z0. pose proof (NL_cases a Ha) as C. cbn zeta in C. top_ranges. lia. Qed.

Lemma HoSlotF : ltac2:(tb__ "0|0|
S40S2dVrhoF;Vms';Sf3A4").
Proof using Hb16 Hb3 Hdepth HsmF Hsp. apply (proj1 (Forall_forall _ _) HOF). right. unfold NL. cbn. tauto. Qed.
Lemma HoMetaF : ltac2:(tb__ "0|0|
S40S2dVrhoF;Vms';Sf2A4").
Proof using Hb16 Hb3 Hdepth HsmF Hsp. apply (proj1 (Forall_forall _ _) HOF). right. unfold NL. cbn. tauto. Qed.

Lemma slot_in_NL : ltac2:(tb__ "0|2|
S8S1S1dS21S12fVL;Vam;Vidx;A3M0Z4M1A2R1A2S1eR1S21S1cG0S134Vam;A1A2G1A2A2A2S128VrhoF;SefS12bR2A1A3F_;Fx;").
Proof using Em0 EmW HCS HF HLok HMI HagF Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high.
  intros x Hx. pose proof RZ. exists oSlot. split; [unfold NL; cbn; tauto|].
  rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 RNF)))))). cbn [fst snd]. unfold wz. rewrite u64 by (top_ranges; lia). lia.
Qed.
Lemma meta_in_NL : ltac2:(tb__ "0|1|
S8S1S1dS1cS131VL;Vg;A2M0Z10A2R1A2S1eR1S1cG0Z28A2A2A2S128VrhoF;SefS12bR2A1A3F_;Fx;").
Proof using Em0 EmW HCS HF HLok HMI HagF Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high.
  intros x Hx. pose proof RZ. exists oMeta. split; [unfold NL; cbn; tauto|].
  rewrite (proj1 (proj2 (proj2 (proj2 (proj2 RNF))))). cbn [fst snd]. unfold wz. rewrite u64 by (top_ranges; lia). lia.
Qed.

Theorem V2 : ltac2:(tb__ "0|1|
S8S166VL;Vam;Vidx;R1A4S1S0ScSeeS2dSf0S12bR2A1A3SdA3S4S78Q8A1M0G0S0SfG0A1SedS2dSf0S12bR3A1A3S15G0R1A2A3Lb;A2A2F_;Fx;").
Proof using Em0 EmW HCS HF HLok HMI HagF Hb16 Hb3 Hdepth Hhdr HsmF Hsp Hsp_high.
  intros x Hx. unfold MallocSlowPost.in_zone, MallocSlowPost.f_st, MallocSlowPost.f_e in Hx. change (addr_of L (slot_start am idx)) with zSt in Hx. change (addr_of L (slot_end am idx)) with zE in Hx.
  pose proof RZ as Z0.
  assert (R : zSt - 4 <= x < zSt + stv - 4) by lia.
  pose proof (m'_in (wz x) (slot_in_NL x R)) as E.
  destruct (dunk_byte rhoF ms' oSlot x HoSlotF eq_refl ltac:(rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 RNF)))))); cbn [fst snd]; lia)) as [[b Hb] W].
  split; [apply (wok_of_at m' ms'); [exact E | exact W]|].
  exists b. rewrite (rd_of_at m' ms' (wz x) HromF E). exact Hb.
Qed.

Lemma evFW : ltac2:(tb__ "0|0|
S32S0ScSe8Sc9R1A2SdA3S0S78Q40A1S3cVrhoF;R2A2S3cVrhoW;R2A2A3F_;Fe;").
Proof using HagF. intros e He. exact (eval_agrees rhoW rhoF e HagF He). Qed.
Lemma soffFW : ltac2:(tb__ "0|0|
S32S0ScSe8Sc9R1A2SdA3S0S8S45VrhoF;R2A2S45VrhoW;R2A2A3F_;Fe;").
Proof using HagF. intros e He. unfold soff. rewrite (evFW e He). reflexivity. Qed.

Lemma same_cell_bytes : ltac2:(tb__ "0|3|
S35S35S39S8S40S2dVrhoW;Vms;R4A4S40S2dVrhoF;Vms';R4A4ScbS39R4S4cR6A1M0A3ScbS39R5G0A3S0S32S3fR8A1S3fR7A1A3S0ScSe8Sc9S3fR9A1A2SdA3S0ScSe8Sc9S48R8A1A2SdA3S0ScSe8Sc9S4dR9A1A2SdA3S1S1dS1cS79Q40S3cVrhoF;S3fRbA1A2A2S45VrhoF;S48RaA1A2A2M1R9A2S1eR9S1cG1S49RaA1A2A2A2S0SfS78Q8A1A1S4eVms';S12bRaA1M2A2S4eVms;G2A2A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fx;Fc;FoB;FoA;").
Proof using HagF Hb16 Hb3 Hsp.
  intros oA oB c x HA HB InA InB Eb Vb Vo Vv Hx.
  set (j := Z.to_nat (x - (bv_unsigned (eval rhoF (ob_base oB)) + soff rhoF (c_off c)))).
  pose proof (cell_bytes_sym rhoF ms' oB c j HB InB ltac:(lia)) as RB.
  pose proof (cell_bytes_sym rhoW ms oA c j HA InA ltac:(lia)) as RA.
  rewrite <- (evFW _ Vb), <- (soffFW _ Vo), <- (evFW _ Vv) in RA. rewrite Eb in RA.
  subst j. rewrite Z2Nat.id in RA, RB by lia.
  replace (bv_unsigned (eval rhoF (ob_base oB)) + soff rhoF (c_off c) + (x - (bv_unsigned (eval rhoF (ob_base oB)) + soff rhoF (c_off c)))) with x in RA, RB by lia.
  unfold wz. rewrite RA, RB. reflexivity.
Qed.

Lemma ro_tab : ltac2:(tb__ "0|6|
S78Q40M0A1S1S1dZ108ecM1S79G0R1A2M2A2S1eG2S1cG1Z60A2A2A2S1S0SfS78Q8A1M3A1M4S119Vms';R2A2S17G3A1M5A3S0G4S3eVrho;R2A2G5A3A2F_;Fa;").
Proof using Em0 Hb16 Hb3 Hm0_sct HsmF.
  intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a). split.
  - apply HroF. replace (bv_unsigned a) with (0x108cc + (bv_unsigned a - 0x108cc)) by lia. apply ro_tables. lia.
  - rewrite <- Em0. replace (bv_unsigned a) with (0x108ec + (bv_unsigned a - 0x108ec)) by lia. apply Hm0_sct. lia.
Qed.

Lemma HoldA : ltac2:(tb__ "0|0|
S35ScbS35R1S132Vam;A1A3S40S2dVrhoW;Vms;R2A4F_;Fo;").
Proof using Hsm0. intros o Ho. apply (proj1 (Forall_forall _ _) HO0). right. exact Ho. Qed.
Lemma HoldB : ltac2:(tb__ "0|0|
S35ScbS35R1SefA3S40S2dVrhoF;Vms';R2A4F_;Fo;").
Proof using HsmF. intros o Ho. apply (proj1 (Forall_forall _ _) HOF). right. exact Ho. Qed.

Ltac inN := unfold N_all, NL; cbn; tauto.

Lemma V1_cell : ltac2:(tb__ "0|7|
S35S35S39S8ScbS35R4S132Vam;A1A3ScbS35R4SefA3S0S55S54R6A1S44A3M0G0ScbS39R6S4cR8A1M1A3ScbS39R7G1A3S0S32S3fRaA1S3fR9A1A3S0ScSe8Sc9S3fRbA1A2SdA3S0ScSe8Sc9S48RaA1A2SdA3S0ScSe8Sc9S4dRbA1A2SdA3S1S1dS1cS79Q40S3cVrhoF;S3fRdA1A2A2S45VrhoF;S48RcA1A2A2M2RbA2S1eRbS1cG2S49RcA1A2A2A2S1S1dS18S8S8S3aVrhoF;ReA2M3A3RcA2S1eRcS1bS8S8G3A3A2A2S1S1dS18S8S8S3aVrhoW;R10A2M4A3RdA2S1eRdS1bS8S8G4A3A2A2S128VrhoF;SefS12bReA1A3S1S1dZ0RfA2S1eRfS1fZ2Z40A2A2A2S1S0SfS78Q8A1A1SedS2dSf0S12bR10A1M5A3SedS2dS3eVrho;A1M6G5A3A3S0ScSeeS2dSf0G5A3SeeS2dG6G5A3A3A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fx;Fc;FoB;FoA;").
Proof using Em0 EmW HCS HF HLok HMI HagF Hb16 Hb3 Hdepth Hhdr Hsm Hsm0 HsmF Hsp Hsp_high.
  intros oA oB c x InA InB DA DB CA CB Eb Vb Vo Vv Hx RB RA IN Hx64.
  pose proof (m'_in _ IN) as E.
  assert (E0 : ms_mem ms (wz x) = rm rho (wz x)).
  { apply Hfr00. exact (NL_below_stack _ IN). }
  pose proof (same_cell_bytes oA oB c x (HoldA oA InA) (HoldB oB InB) CA CB Eb Vb Vo Vv Hx) as C.
  destruct (dunk_byte rhoF ms' oB x (HoldB oB InB) DB RB) as [_ WB].
  destruct (dunk_byte rhoW ms oA x (HoldA oA InA) DA RA) as [_ WA].
  rewrite (rd_of_at m' ms' _ HromF E), (rd_of_at (rm rho) ms _ Hrom0 (eq_sym E0)), C. split; [reflexivity|].
  rewrite (wok_of_at m' ms' _ E WB), (wok_of_at (rm rho) ms _ (eq_sym E0) WA). reflexivity.
Qed.

Lemma RW : ltac2:(tb__ "0|6|
S1S0S11S8S8A2M0S3aVrhoW;S13eA2S12S8S8S1cZ5a3c8M1Z0A2S1cG1Z4M2A2A4A3S1S0G0S3aVrhoW;S13dA2S12S8S8S1cG1Z14A2S1cG1Z18A2A4A3S1S0G0S3aVrhoW;S13cA2S12S8S8S1cG1S1cS22Z8S133Vam;A1A2M3Z58A2A2S1cG1S1cG3Z60A2A2A4A3S1S0G0S3aVrhoW;S13fA2S12S8S8S1cS131VL;Vg;A2M4Z10A2S1cG4Z28A2A4A3S0G0S3aVrhoW;S140Vam;A1A2S12S8S8S1cS12fVL;Vam;Vidx;A3M5N4A2S1cG5S21S134Vam;A1G2A2A2A4A3A2A2A2A2").
Proof using Em0 EmW HCS HF HMI Hb16 Hb3 Hhdr Hsp. rewrite rhoW_m0. repeat match goal with |- _ /\ _ => split end; first [apply rng_lock|apply rng_ctr|apply rng_act|apply rng_meta|apply rng_slot]. Qed.

Lemma baseF_lit : ltac2:(tb__ "0|0|
S8S1S1dZ0R1A2S1eR1S1fZ2Z40A2A2A2S0S8S79Q40S3cVrhoF;S33R2A1A2A2R2A3F_;Fz;").
Proof using . intros z Hz. cbn [eval]. apply u64. exact Hz. Qed.
Lemma baseF_151 : ltac2:(tb__ "0|0|
S0S8S79Q40S3cVrhoF;Se5P97A1A2A2S131VL;Vg;A2A3").
Proof using HCS HF HMI HagF Hb16 Hb3 Hhdr. rewrite (evFu (v 151)) by reflexivity. exact ze151. Qed.
Lemma baseF_p0 : ltac2:(tb__ "0|0|
S0S8S79Q40S3cVrhoF;SbcS130Vam;A1A1A2A2S12fVL;Vam;Vidx;A3A3").
Proof using HCS HF HMI HagF Hb16 Hb3 Hhdr Hsp. rewrite evFu; [exact ze_p0 | destruct kd_cases as [[-> _]|[[-> _]|[-> _]]]; reflexivity ..]. Qed.
Lemma soffF_lit : ltac2:(tb__ "0|1|
S8S1S1dS24S1fZ2Z3eA2M0A1R1A2S1dR1G0A2A2S0S8S45VrhoF;S33R2A1A2R2A3F_;Fz;").
Proof using Hb16 Hb3 rho. intros. apply soff_lit_small. lia. Qed.
Lemma soffF_act : ltac2:(tb__ "0|1|
S0S8S45VrhoF;S3dS11fS3dS124Se5P96A1S33Z3A1A3S33Z58M0A1A3A2S1cS22Z8S133Vam;A1A2G0A2A3").
Proof using Em0 EmW HCS HF HLok HMI HagF Hb16 Hb3 Hhdr Hsp Hsp_high.
  rewrite soffFW by reflexivity. rewrite rhoW_m0. apply (soff_of_ev (SAlu ALU_ADD (SAlu ALU_SLL (v 150) (SLit 3)) (SLit 88)) (8 * sc + 88) eq_refl ze_actoff). pose proof RZ. lia.
Qed.

Lemma soffF_ofZ : ltac2:(tb__ "0|0|
S32S8S0ScSdfR2A1SdA3S0S8Se1S138Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S137Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9R3A3R2A3S1S1dZ0R3A2S1eR3S1fZ2Z3fA2A2A2S0ScSe8Sc9R5A2SdA3S0S8S45VrhoF;R6A2R5A3F_;F_;F_;F_;Fz;Fe;").
Proof using Em0 EmW HagF Hb16 Hb3. intros e z Hs Hz Hr Hv. rewrite soffFW by exact Hv. rewrite rhoW_m0. apply (soff_of_ev e z Hs Hz Hr). Qed.

Theorem V1 : ltac2:(tb__ "0|2|
S8S1S1dZ0R1A2S1eR1S1fZ2Z40A2A2A2S2S166VL;Vam;Vidx;R2A4A1S1S0SfS78Q8A1A1SedS2dSf0S12bR3A1M0A3SedS2dS3eVrho;A1M1G0A3A3S0ScSeeS2dSf0G0A3SeeS2dG1G0A3A3A2F_;F_;Fx;").
Proof using Em0 EmW HCS HF HLok HMI HagF Hb16 Hb3 Hdepth Hhdr Hm0_sct Hsm Hsm0 HsmF Hsp Hsp_high.
  intros x Hx NZ.
  unfold MallocSlowPost.in_zone, MallocSlowPost.f_st, MallocSlowPost.f_e in NZ. change (addr_of L (slot_start am idx)) with zSt in NZ. change (addr_of L (slot_end am idx)) with zE in NZ.
  pose proof RZ as Z0. pose proof RNF as (F2 & F3 & F4 & F5 & F7 & F8 & F9). pose proof RW as (W2 & W3 & W4 & W5 & W6).
  destruct (in_ranges_dec rhoF NL (wz x)) as [IN|OUT].
  2:{ unfold Glue.rd_of, Glue.wok_of. rewrite (m'_out _ OUT). split; reflexivity. }
  pose proof IN as (o & Ho & R). unfold wz in R. rewrite u64 in R by lia.
  unfold NL in Ho. cbn [In] in Ho.
  destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
  -   rewrite F2 in R. cbn [fst snd] in R.
    apply (V1_cell Q_lock (U.Mal_malloc__G1.Mal_malloc_fast_runs.O_lock MR_P) (mkCell (SLit 0) 4 (SLit 0)) x); try inN; try reflexivity;
      rewrite ?F2, ?W2; cbn [fst snd ob_base U.Mal_malloc__G1.Mal_malloc_fast_runs.O_lock c_off c_width mr_LK MR_P]; rewrite ?baseF_lit, ?soffF_lit by lia; try lia; exact IN.
  -   rewrite F3 in R. cbn [fst snd] in R.
    apply (V1_cell Q_ctr (U.Mal_malloc__G1.Mal_malloc_fast_runs.O_ctr MR_P) (mkCell (SLit 20) 4 (v 153)) x); try inN; try reflexivity;
      rewrite ?F3, ?W3; cbn [fst snd ob_base U.Mal_malloc__G1.Mal_malloc_fast_runs.O_ctr c_off c_width mr_LK MR_P]; rewrite ?baseF_lit, ?soffF_lit by lia; try lia; exact IN.
  -   rewrite F4 in R. cbn [fst snd] in R.
    apply (V1_cell Q_act (U.Mal_malloc__G1.Mal_malloc_fast_runs.O_act MR_P) (mkCell (SAlu ALU_ADD (SAlu ALU_SLL (v 150) (SLit 3)) (SLit 88)) 8 (v 151)) x); try inN; try reflexivity;
      rewrite ?F4, ?W4; cbn [fst snd ob_base U.Mal_malloc__G1.Mal_malloc_fast_runs.O_act c_off c_width mr_LK MR_P]; rewrite ?baseF_lit, ?soffF_act by lia; try lia; exact IN.
  -   rewrite F5 in R. cbn [fst snd] in R.
    destruct (ro_tab (wz x) ltac:(unfold wz; rewrite u64 by lia; lia)) as [M1 M2].
    rewrite <- M1, <- (m'_in _ IN) in M2. unfold Glue.rd_of, Glue.wok_of, Contract.rd_of, Contract.wok_of. rewrite <- M2. split; reflexivity.
  -   rewrite F7 in R. cbn [fst snd] in R.
    assert (KM : exists c, In c (ob_cells Q_meta) /\ In c meta_cells' /\ exists offc, c_off c = SLit offc /\ - 100 <= offc <= 100 /\ sv_vars_all below200 (c_val c) = true
                 /\ zG + offc <= x < zG + offc + c_width c).
    { destruct (Z_lt_dec x (zG + 24)) as [A|A].
      - exists (mkCell (SLit 16) 8 (v 156)). split; [cbn; tauto|]. split; [cbn; tauto|]. exists 16. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. cbn [c_width]. lia.
      - destruct (Z_lt_dec x (zG + 28)) as [A2|A2].
        + exists (mkCell (SLit 24) 4 (v 152)). split; [cbn; tauto|]. split; [cbn; tauto|]. exists 24. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. cbn [c_width]. lia.
        + destruct (Z_lt_dec x (zG + 32)) as [B|B].
          * exists (mkCell (SLit 28) 4 (v 154)). split; [cbn; tauto|]. split; [cbn; tauto|]. exists 28. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. cbn [c_width]. lia.
          * exists (mkCell (SLit 32) 8 (v 155)). split; [cbn; tauto|]. split; [cbn; tauto|]. exists 32. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. cbn [c_width]. lia. }
    destruct KM as (c & C1 & C2 & offc & Eoff & Hoffc & Vc & Hxc).
    apply (V1_cell Q_meta oMeta c x); try inN; try reflexivity; try exact C1; try exact C2; try exact Vc;
      rewrite ?Eoff, ?F7, ?W5; cbn [fst snd ob_base oMeta]; rewrite ?baseF_151, ?soffF_lit by lia; try reflexivity; try lia; exact IN.
  -   rewrite F8 in R. cbn [fst snd] in R.
    assert (Ex : x = zSt - 4) by lia.
    apply (V1_cell Q_slot oSlot (mkCell (SLit (-4)) 1 (SLit 0)) x);
      [ inN | inN | reflexivity | reflexivity
      | unfold U.Mal_mslow__G2.Mal_mslow_I1.Q_slot, U.Mal_malloc__G1.Mal_malloc_fast_runs.O_slot; cbn [ob_cells]; left; reflexivity
      | apply C4_in
      | reflexivity
      | unfold U.Mal_mslow__G2.Mal_mslow_I1.Q_slot; cbn [ob_base U.Mal_malloc__G1.Mal_malloc_fast_runs.O_slot]; destruct kd_cases as [[Ek _]|[[Ek _]|[Ek _]]]; rewrite Ek; reflexivity
      | reflexivity | reflexivity
      | cbn [ob_base oSlot c_off c_width]; rewrite baseF_p0, soffF_lit by lia; lia
      | rewrite F8; cbn [fst snd]; lia
      | rewrite W6; cbn [fst snd]; lia
      | exact IN | lia ].
Qed.

End ReabG.
End Mal_mslow_G.

Module Mal_mslow_C.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMalloc OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractMK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fast_enum OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_K OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_I0.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.
Import RS.

Lemma land1_even a : ltac2:(tb__ "0|0|
S0ScS23S2cVa;Z1A2Z0A2S25Va;A1A3").
Proof.
  change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2. rewrite Zeven_mod. reflexivity.
Qed.
Lemma lor1_even a : ltac2:(tb__ "0|1|
S1dZ0Va;A2S0ScS25Va;A1SdA3S0S8S2aVa;Z1M0A2S1cVa;G0A2A3F_;F_;").
Proof.
  intros Ha He. rewrite <- Z.lxor_lor.
  - rewrite <- Z.add_nocarry_lxor; [reflexivity|]. rewrite <- land1_even in He. apply Z.eqb_eq in He. exact He.
  - rewrite <- land1_even in He. apply Z.eqb_eq in He. exact He.
Qed.

Lemma sext32_zero x : ltac2:(tb__ "0|3|
S1S1dZ0M0Vx;A2S1eVx;S1fZ2M1Z20M2A2A2A2S0ScS23S20Se2G2Vx;A2S1fG1Z40A2A2G0A2S23Vx;G0A2A3F_;").
Proof.
  intros Hx. unfold toS. rewrite (Z.mod_small x) by lia. change (2 ^ (32 - 1)) with (2 ^ 31).
  destruct (x <? 2 ^ 31) eqn:C; [apply Z.ltb_lt in C | apply Z.ltb_ge in C].
  - rewrite Z.mod_small by lia. reflexivity.
  - replace ((x - 2 ^ 32) mod 2 ^ 64) with (x - 2 ^ 32 + 2 ^ 64).
    + destruct (x =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. apply Z.eqb_neq. lia.
    + symmetry. replace (x - 2 ^ 32) with ((x - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma segs_insideC : ltac2:(tb__ "0|1|
S0ScSccS161S161S19S26Z10000S2bS162R1A1A1M0A2S26S1cG0S2bS163R1A1A1A2Z5b000A2A2Lseg;S2dA3SdA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma off_image_none (x : word) : ltac2:(tb__ "0|2|
S3S1dS1cS79Q40Vx;A2M0Z1A2Z10000A2S1dZ5b000G0A2A2S0SfS78Q8A1M1A1S65S2dVx;A2S17G1A1A3F_;").
Proof.
  intros Hx. unfold image_byte, memory_read. change (Z.of_N 1%N) with 1.
  destruct (find_segment segsU (bv_unsigned x) 1) as [seg|] eqn:E; [|reflexivity]. exfalso.
  destruct (ClientLaws.find_segment_In _ _ _ _ E) as (Hin & H1 & H2).
  pose proof (proj1 (forallb_forall _ _) segs_insideC seg Hin) as Q. apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.leb_le in Q2. lia.
Qed.

Lemma rd_of_off_image (m : word -> option byte) (x : word) : ltac2:(tb__ "0|1|
S3S1dS1cS79Q40Vx;A2M0Z1A2Z10000A2S1dZ5b000G0A2A2S0SfS78Q8A1A1SedS2dVm;Vx;A3Vm;Vx;A1A3F_;").
Proof. intros Hx. unfold Glue.rd_of. rewrite (off_image_none x Hx). destruct (m x); reflexivity. Qed.

Lemma auxv_init_rdext Ly (r r' : valuation) : ltac2:(tb__ "0|2|
S159S2dS12aVLy;Vr;A4S78Q40A1M0S0SfS78Q8A1A1S14fS2dS3eVr';A1R1A3S14fS2dS3eVr;A1R1A3A3Fa;S0G0S3bVr';PaM1A2S3bVr;G1A2A3S159S2dS12aVLy;Vr';A4F_;F_;F_;").
Proof.
  intros (av & q & R1 & R2 & R3 & R4 & R5 & REST) AG Hsp.
  assert (T : forall a w v, am_reads segsU (rm r) a w v -> am_reads segsU (rm r') a w v).
  { intros a w v H k Hk. rewrite AG. exact (H k Hk). }
  exists av, q. rewrite Hsp.
  split; [apply T; exact R1|]. split; [intros j Hj; apply T; exact (R2 j Hj)|].
  split; [intros j Hj; destruct (R3 j Hj) as [v Hv]; exists v; apply T; exact Hv|].
  split; [apply T; exact R4|]. split; [apply T; exact R5|]. exact REST.
Qed.

Lemma mem_kept_trans00 C A A2 (m0 m1 m2 : word -> option byte) : ltac2:(tb__ "0|0|
S14eS2dVC;VA;VA;Vm0;Vm1;A6S14eS2dVC;VA;VA2;Vm1;Vm2;A6S14eS2dVC;VA;VA2;Vm0;Vm2;A6F_;F_;").
Proof. intros H1 H2 a Ha Hc Hc2 He Hs. rewrite (H2 a Ha Hc Hc2 He Hs). exact (H1 a Ha Hc Hc He Hs). Qed.

Section InstC.

Variables (s : astate) (L : layout) (n : Z).
Variable rho : valuation.
Hypothesis HW : WF s.
Hypothesis HCS : slow_case s n.
Hypothesis HLok : layout_ok L s.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S8S79Q40S3bVrho;PcA2A2Vn;A3").
Local Abbreviation sc0 := (@U.Mal_mslow__G1.Mal_mslow_I0.sc0 n).
Local Abbreviation kq := (@U.Mal_mslow__G1.Mal_mslow_I0.kq n).
Local Notation "§8§ h__" := (h__ s n) (at level 10, h__ global).
Local Abbreviation cl := (§8§ U.Mal_mslow__G1.Mal_mslow_I0.cl).
Local Abbreviation g0o := (§8§ U.Mal_mslow__G1.Mal_mslow_I0.g0o).
Local Abbreviation j1 := (@U.Mal_mslow__G1.Mal_mslow_I0.j1 n).
Local Abbreviation g1o := (§8§ U.Mal_mslow__G1.Mal_mslow_I0.g1o).
Local Abbreviation u0 := (§8§ U.Mal_mslow__G1.Mal_mslow_I0.u0).
Local Abbreviation u1 := (§8§ U.Mal_mslow__G1.Mal_mslow_I0.u1).
Local Abbreviation zg0 := (@U.Mal_mslow__G1.Mal_mslow_I0.zg0 s L n).
Local Abbreviation zg1 := (@U.Mal_mslow__G1.Mal_mslow_I0.zg1 s L n).
Local Abbreviation av1 := (§8§ U.Mal_mslow__G1.Mal_mslow_I0.av1).
Local Abbreviation fr1 := (§8§ U.Mal_mslow__G1.Mal_mslow_I0.fr1).
Local Abbreviation crb := (§8§ U.Mal_mslow__G1.Mal_mslow_I0.crb).
Local Abbreviation pv := (§8§ U.Mal_mslow__G1.Mal_mslow_I0.pv).
Local Abbreviation Hn := (@U.Mal_mslow__G1.Mal_mslow_I0.Hn s n HCS).
Local Abbreviation Gk_range := (@U.Mal_mslow__G1.Mal_mslow_I0.Gk_range n).
Local Abbreviation cl_cases := (§8§ U.Mal_mslow__G1.Mal_mslow_I0.cl_cases).
Local Abbreviation crb_true := (§8§ U.Mal_mslow__G1.Mal_mslow_I0.crb_true).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S14cS12aS14bVs;VL;A2Vrd0;Vwok0;Vvm;A5").
Local Abbreviation g1_facts := (@U.Mal_mslow__G1.Mal_mslow_I0.g1_facts s n HW).
Local Notation "§9§ h__" := (h__ s L n HW HCS HLok rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation zg0_range := (§9§ U.Mal_mslow__G1.Mal_mslow_I0.zg0_range).
Local Abbreviation zg1_range := (@U.Mal_mslow__G1.Mal_mslow_I0.zg1_range s L n HW HLok rd0 wok0 vm HMI).
Local Abbreviation R_all := (§9§ U.Mal_mslow__G1.Mal_mslow_I0.R_all).
Local Notation "§10§ h__" := (h__ s L n rho) (at level 10, h__ global).
Local Abbreviation rw1 := (§10§ U.Mal_mslow__G1.Mal_mslow_I0.rw1).
Local Abbreviation rw1_low := (§10§ U.Mal_mslow__G1.Mal_mslow_I0.rw1_low).
Local Abbreviation rl1 := (@U.Mal_mslow__G1.Mal_mslow_I0.rl1 rho).
Local Abbreviation rho1 := (§10§ U.Mal_mslow__G1.Mal_mslow_I0.rho1).
Local Abbreviation zr1 := (§10§ U.Mal_mslow__G1.Mal_mslow_I0.zr1).
Local Abbreviation zl1 := (§10§ U.Mal_mslow__G1.Mal_mslow_I0.zl1).
Local Abbreviation zr1_12 := (@U.Mal_mslow__G1.Mal_mslow_I0.zr1_12 s L n rho HP12).
Local Notation "§11§ h__" := (h__ s L n rho HW HCS HLok rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation zr1_160 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.zr1_160).
Local Abbreviation zr1_161 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.zr1_161).
Local Abbreviation zr1_162 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.zr1_162).
Local Abbreviation zr1_163 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.zr1_163).
Local Abbreviation zr1_10 := (§10§ U.Mal_mslow__G1.Mal_mslow_I0.zr1_10).
Local Abbreviation ze_var := (§10§ U.Mal_mslow__G1.Mal_mslow_I0.ze_var).
Local Abbreviation ze_lit := (§10§ U.Mal_mslow__G1.Mal_mslow_I0.ze_lit).
Local Notation "§12§ h__" := (h__ s L n rho HW HCS HLok HP12 rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation ze12 := (§12§ U.Mal_mslow__G1.Mal_mslow_I0.ze12).
Local Abbreviation ze149 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.ze149).
Local Abbreviation ze150 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.ze150).
Local Abbreviation ze164 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.ze164).
Local Abbreviation ze165 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.ze165).
Local Abbreviation ze166 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.ze166).
Local Abbreviation ze167 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.ze167).
Local Abbreviation ze168 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.ze168).
Local Abbreviation ze172 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.ze172).
Local Abbreviation ze173 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.ze173).
Local Abbreviation ze174 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.ze174).
Local Abbreviation ze_off150 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.ze_off150).
Local Abbreviation ze_off164 := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.ze_off164).
Local Abbreviation ze_kq := (§12§ U.Mal_mslow__G1.Mal_mslow_I0.ze_kq).
Local Abbreviation zr1_stages := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.zr1_stages).
Local Abbreviation stage_cert := (§11§ U.Mal_mslow__G1.Mal_mslow_I0.stage_cert).
Local Abbreviation n157_kq := (§9§ U.Mal_mslow__G1.Mal_mslow_I0.n157_kq).
Local Abbreviation kq_small := (§9§ U.Mal_mslow__G1.Mal_mslow_I0.kq_small).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S1dZ1000S79Q40S3bVrho;PaA2A2M0A2S0S8S20G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S1dSe2Z40S79Q40S3bVrho;PfA2A2A2M0S24S12eA1A2S1dS24S1fZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S1dS12cVL;A1S1cS79Q40M0S3bVrho;PaA2A2Se2Z40S79G0S3bVrho;PfA2A2A2A2A2").
Variable m0 : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0S78Q40A1SfS78Q8A1A1F_;Vrd0;SedS2dVm0;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0S78Q40A1ScF_;Vwok0;SeeS2dVm0;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm0_sct : ltac2:(tb__ "0|1|
S8S1S1dZ0R1A2S1eR1Z60A2A2S0SfS78Q8A1M0A1Vm0;S7aQ40S1cZ108ecR2A2A2A1S17G0A1A3F_;Fkk;").
Hypothesis Hm0_ctz : ltac2:(tb__ "0|1|
S8S1S1dZ0R1A2S1eR1Z20A2A2S0SfS78Q8A1M0A1Vm0;S7aQ40S1cZ108ccR2A2A2A1S17G0A1A3F_;Fkk;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S12dSedS2dVm0;A2SeeS2dVm0;A2A2").
Local Notation "§13§ h__" := (h__ s L n rho m0) (at level 10, h__ global).
Local Abbreviation rng_nl := (§13§ U.Mal_mslow__G1.Mal_mslow_I0.rng_nl).
Local Abbreviation rng_sct := (§13§ U.Mal_mslow__G1.Mal_mslow_I0.rng_sct).
Local Abbreviation rng_ctz := (§13§ U.Mal_mslow__G1.Mal_mslow_I0.rng_ctz).
Local Notation "§14§ h__" := (h__ s L n rho HW HCS HLok rd0 wok0 vm HMI Hsp m0) (at level 10, h__ global).
Local Abbreviation rng_act150 := (§14§ U.Mal_mslow__G1.Mal_mslow_I0.rng_act150).
Local Abbreviation rng_usg150 := (§14§ U.Mal_mslow__G1.Mal_mslow_I0.rng_usg150).
Local Abbreviation rng_act164 := (§14§ U.Mal_mslow__G1.Mal_mslow_I0.rng_act164).
Local Abbreviation rng_usg164 := (§14§ U.Mal_mslow__G1.Mal_mslow_I0.rng_usg164).
Local Notation "§15§ h__" := (h__ s L n rho HW HCS HLok rd0 wok0 vm HMI m0) (at level 10, h__ global).
Local Abbreviation rng_metaA := (§15§ U.Mal_mslow__G1.Mal_mslow_I0.rng_metaA).
Local Abbreviation rng_metaAF := (§15§ U.Mal_mslow__G1.Mal_mslow_I0.rng_metaAF).
Local Abbreviation N_all := (§8§ U.Mal_mslow__G1.Mal_mslow_I0.N_all).
Local Abbreviation N_hold := (@U.Mal_mslow__G1.Mal_mslow_I0.N_hold s L n rho HW HCS HLok rd0 wok0 vm HMI Hsp Hsp_high m0 Erd Ewok ms Hrom Hm0_sct Hm0_ctz).

Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S15aS2dVKc;VRF;VGF;VTR;A5").

Definition K (tr' : list event) (md' : Model) : Prop := ltac2:(tb__ "0|0|
S1VKc;Vtr';Vmd';A2S0S149S14aVmd';A1Vvm;A3A2").
Lemma HK : implK Kc K. Proof using . intros tr' md' [H _]. exact H. Qed.

Let rhoW : valuation := rho1 m0.
Lemma Hzr : ltac2:(tb__ "0|0|
S9S0S8Se4VrhoW;R1A2Sa4Vs;VL;Vn;Vrho;R1A5A3Fi;"). Proof using m0. intros i. reflexivity. Qed.
Lemma Hzl : ltac2:(tb__ "0|0|
S9S0S10S8A1Se3VrhoW;R1A2Sa5Vs;VL;Vn;Vrho;R1A5A3Fl;"). Proof using m0. intros l. reflexivity. Qed.

Lemma EV : ltac2:(tb__ "0|1|
S36S32Sc8VrhoW;R2A2S0ScSe8Sc9R2A2SdA3S0ScSdfR3A1SdA3S0S78Q40M0A1S3cR5R4A2S7aG0Se1Sa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4R4A3A2A3F_;F_;F_;Fe;Frho';").
Proof using m0. exact (WalkReab.EV rhoW zr1 zl1 Hzr Hzl). Qed.
Lemma EVu : ltac2:(tb__ "0|0|
S36S32Sc8VrhoW;R2A2S0ScSe8Sc9R2A2SdA3S0ScSdfR3A1SdA3S0S8S79Q40S3cR5R4A2A2Se1Sa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4R4A3A3F_;F_;F_;Fe;Frho';").
Proof using m0. exact (WalkReab.EVu rhoW zr1 zl1 Hzr Hzl). Qed.
Lemma HOLDS : ltac2:(tb__ "0|0|
S36S34Sc8VrhoW;R2A2S0ScSeaSc9R2A2SdA3S0ScSe0R3A1SdA3S7S57R5R4A2SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4R4A3A2F_;F_;F_;Fp;Frho';").
Proof using m0. exact (WalkReab.HOLDS rhoW zr1 zl1 Hzr Hzl). Qed.
Lemma rw_agrees : ltac2:(tb__ "0|0|
S36S9Sc8VrhoW;R2A2S0ScSc9R2A1SdA3S0S78Q40A1S3bR4R3A2Sb5Vs;VL;Vn;Vrho;R3A5A3F_;F_;Fj;Frho';").
Proof using m0. intros rho' j Hag Hj. exact (WalkReab.rw_agrees rhoW rho' j Hag Hj). Qed.
Lemma leaf_fact : ltac2:(tb__ "0|0|
S36S46Se6S34Sc8VrhoW;R4A2ScfS2dS7cR4R5R3A5ScbS34R3S41R5A1A3S0ScSeaSc9R4A2SdA3S0ScSe0R5A1SdA3SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4R6A3F_;F_;F_;F_;F_;Fp;Fw;FLf;Frho';").
Proof using m0. exact (WalkReab.leaf_fact segsU rhoW zr1 zl1 Hzr Hzl K). Qed.
Lemma ZF_holds : ltac2:(tb__ "0|0|
S36S10S34A1Sc8VrhoW;R2A2S0ScSccS34SeaSc9A1R2A3SdA3S0ScSccS34Se0R3A3SdA3S113S34SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4A2R4A3S113S34S57R6A1R5A3F_;F_;F_;F_;Fl;Frho';").
Proof using m0. exact (WalkReab.ZF_holds rhoW zr1 zl1 Hzr Hzl). Qed.

Local Abbreviation POST := (WalkReab.POST segsU rhoW K).

Lemma seg_run : ltac2:(tb__ "0|2|
S14S46S10S9eA1M0Se7S36S0ScS43R4A1S16A3S0S9S42R5A1Sb7A3S0SfG0A1Sa3S2dR7Sc2Sb6A1R6SdA5S15G0R5A2A3Sc8VrhoW;R4A2S9eS36ScbS9eR2R9A3Sc8VrhoW;R2A2VTR;Z0M1ScfS2dS7cSa1R4A1R3A4RaA3F_;F_;Frho'';FLf;VTR;G1ScfS2dS7cR9R6A4R7A3F_;F_;F_;F_;F_;Frho';FQ;Fleaves;FS;Ffuel;").
Proof using L RR m0 n rho s.
  intros fuel S leaves Q rho' Hl Hn Hrun Hag HQ.
  apply (trr_run RR 0 fuel (CUTS MR_P) K S leaves rho' Q); [lia | exact Hrun | exact Hl | exact HK |].
  intros Lf rho'' Hin Hab. apply (HQ Lf rho'' Hin).
  eapply agrees_below; [exact Hag | exact Hab | rewrite Hn; unfold NX; lia].
Qed.

Lemma seg_leaf : ltac2:(tb__ "0|0|
Se7Se7Se6R3R1A1R3R2A1F_;Fw;VTR;Z0R3R2A3F_;FQ;FP;").
Proof using RR rho. intros P Q H. apply (trr_skip RR); [lia | exact H]. Qed.
Lemma seg_dead : ltac2:(tb__ "0|0|
Se7Se7Se6R3R1A1S6F_;Fw;VTR;Z0R3R2A3F_;FQ;FP;").
Proof using RR rho. intros P Q H. apply (trr_false RR); [lia | exact H]. Qed.

Lemma from_POST : ltac2:(tb__ "0|1|
S46Se7S36Sc8VrhoW;R1A2VTR;Z0M0ScfS2dS7cR4R2A4R3A3F_;Frho';VTR;G0S115S2dVrhoW;S7cR3A4R2A3F_;FQ;FC;").
Proof using L RR m0 n rho s.
  intros C Q H. unfold WalkReab.POST. apply (trr_ex RR); [lia|]. intros rho'. apply (trr_inh RR); [lia|].
  intros w [Hag _]. eapply (trr_pre RR); [|exact (H rho' Hag)]. intros w' [_ X]. exact X.
Qed.
Lemma seq0 : ltac2:(tb__ "0|2|
Se7Se7Se7VTR;Z0M0R3R2A3M1G1VTR;G0R5R3A3F_;F_;FQ;FR;FP;").
Proof using RR. intros P R Q H1 H2. exact (trr_seq0 RR 0 P R Q H1 H2). Qed.

Fixpoint scratch_of (d : list (sv * sv)) : list (positive * sv) :=
  match d with
  | [] => []
  | (e, SVar j) :: t => if (200 <=? j)%positive then (j, e) :: scratch_of t else scratch_of t
  | _ :: t => scratch_of t
  end.

Lemma Zv12 : ltac2:(tb__ "0|0|
S0S8S20Sa4Vs;VL;Vn;Vrho;PcA5S1fZ2Z40A2A2Vn;A3"). Proof using HCS HLok HMI HP12 HW. exact ze12. Qed.
Lemma Zv149 : ltac2:(tb__ "0|0|
S0S8S20Sa4Vs;VL;Vn;Vrho;P95A5S1fZ2Z40A2A2Sa9Vn;A1A3"). Proof using HCS HLok HMI HW. exact ze149. Qed.
Lemma Zv150 : ltac2:(tb__ "0|0|
S0S8S20Sa4Vs;VL;Vn;Vrho;P96A5S1fZ2Z40A2A2Sa7Vn;A1A3"). Proof using HCS HLok HMI HW. exact ze150. Qed.
Lemma Zv164 : ltac2:(tb__ "0|0|
S0S8S20Sa4Vs;VL;Vn;Vrho;Pa4A5S1fZ2Z40A2A2SabVn;A1A3"). Proof using HCS HLok HMI HW. exact ze164. Qed.
Lemma Zv165 : ltac2:(tb__ "0|0|
S0S8S20Sa4Vs;VL;Vn;Vrho;Pa5A5S1fZ2Z40A2A2Sb1Vs;Vn;A2A3"). Proof using HCS HLok HMI HW. exact ze165. Qed.
Lemma Zv166 : ltac2:(tb__ "0|0|
S0S8S20Sa4Vs;VL;Vn;Vrho;Pa6A5S1fZ2Z40A2A2Sb3Vs;VL;Vn;A3A3"). Proof using HCS HLok HMI HW. exact ze166. Qed.
Lemma Zv167 : ltac2:(tb__ "0|0|
S0S8S20Sa4Vs;VL;Vn;Vrho;Pa7A5S1fZ2Z40A2A2SaaVs;Vn;A2A3"). Proof using HCS HLok HMI HW. exact ze167. Qed.
Lemma Zv168 : ltac2:(tb__ "0|0|
S0S8S20Sa4Vs;VL;Vn;Vrho;Pa8A5S1fZ2Z40A2A2SadVs;Vn;A2A3"). Proof using HCS HLok HMI HW. exact ze168. Qed.
Lemma Zv172 : ltac2:(tb__ "0|0|
S0S8S20Sa4Vs;VL;Vn;Vrho;PacA5S1fZ2Z40A2A2Sb2Vs;VL;Vn;A3A3"). Proof using HCS HLok HMI HW. exact ze172. Qed.
Lemma Zv173 : ltac2:(tb__ "0|0|
S0S8S20Sa4Vs;VL;Vn;Vrho;PadA5S1fZ2Z40A2A2SacVs;Vn;A2A3"). Proof using HCS HLok HMI HW. exact ze173. Qed.
Lemma Zv174 : ltac2:(tb__ "0|0|
S0S8S20Sa4Vs;VL;Vn;Vrho;PaeA5S1fZ2Z40A2A2Sb0Vs;Vn;A2A3"). Proof using HCS HLok HMI HW. exact ze174. Qed.

Ltac zlits :=
  repeat match goal with
  | |- context [ (?x mod ?y) ] =>
      lazymatch x with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      lazymatch y with Zpos _ => idtac | Z.pow (Zpos _) (Zpos _) => idtac end;
      let vv := eval vm_compute in (x mod y) in change (x mod y) with vv
  end.
Ltac mlia := Z.to_euclidean_division_equations; lia.

Ltac zev :=
  cbn [zeval zholds zcond zalu Z.of_N];
  zlits;
  rewrite ?Zv12, ?Zv149, ?Zv150, ?Zv164, ?Zv165, ?Zv166, ?Zv167, ?Zv168, ?Zv172, ?Zv173, ?Zv174;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia.

Local Ltac hfact Hag :=
  match goal with |- SymState.holds ?r ?p => apply (proj2 (HOLDS r p Hag eq_refl eq_refl)); cbn [zholds zcond] end.

Ltac scratch_pair Hag HagS :=
  lazymatch goal with |- eval (setp ?r0 ?l) ?e = eval (setp ?r0 ?l) (SVar ?j) =>
    change (eval (setp r0 l) (SVar j)) with (rw (setp r0 l) j);
    rewrite (setp_get r0 l j e eq_refl) by (cbn; tauto);
    rewrite (eval_agrees rhoW (setp r0 l) e HagS) by reflexivity;
    rewrite (eval_agrees rhoW r0 e Hag) by reflexivity; reflexivity
  end.
Ltac sem_pair HagS :=
  rewrite !(EV _ _ HagS) by reflexivity; f_equal.

Local Ltac by_pv := intros [| | |]; vm_compute; reflexivity.

Lemma L0_cases : ltac2:(tb__ "0|1|
S6bS9eScbS9eR1S10aR2A1A3S3S0S46Sa1R2A1M0SfbR3A1A3S0S46G0SfaR3A1A3A2F_;FLf;Fpv0;").
Proof using .
  intros pv0 Lf Hin.
  assert (E : L0 pv0 = [mkLeaf (L0s pv0) RsCut; mkLeaf (L0k pv0) RsCut]).
  { destruct pv0; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. }
  rewrite E in Hin. destruct Hin as [<-|[<-|[]]]; cbn; auto.
Qed.
Lemma L0s_fact : ltac2:(tb__ "0|0|
S6bScbS34S38S120S37PcA1S33Z9dA1A3S41SfbR1A1A1A3Fpv0;").
Proof using Hdepth Hsp. intros [| | |]; vm_compute; tauto. Qed.
Lemma L0k_fact : ltac2:(tb__ "0|0|
S6bScbS34S53S38S120S37PcA1S33Z9dA1A3A1S41SfaR1A1A1A3Fpv0;").
Proof using Hdepth Hsp. intros [| | |]; vm_compute; tauto. Qed.

Definition D0kc : list (sv * sv) * list sprop := Eval vm_compute in D0k PA.
Definition D05c : list (sv * sv) * list sprop := Eval vm_compute in D05 PA.
Definition D5ac : list (sv * sv) * list sprop := Eval vm_compute in D5a PA.
Definition D5bc : list (sv * sv) * list sprop := Eval vm_compute in D5b PA.
Definition D11c : list (sv * sv) * list sprop := Eval vm_compute in D11 PA.
Definition D22c : list (sv * sv) * list sprop := Eval vm_compute in D22 PA.
Definition D33c : list (sv * sv) * list sprop := Eval vm_compute in D33 PA.
Definition D44c : list (sv * sv) * list sprop := Eval vm_compute in D44 PA.
Local Ltac sd_tac D := intros [| | |]; vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some D)).
Lemma sd_0k : ltac2:(tb__ "0|1|
S6bS0SfS11S10S11S32S32A2A1S10S34A1A2M0A1S11cSfaR1A1S103R1A1A2S15G0S90A2A3Fpv0;"). Proof using . sd_tac D0kc. Qed.
Lemma sd_05 : ltac2:(tb__ "0|1|
S6bS0SfS11S10S11S32S32A2A1S10S34A1A2M0A1S11cSfbR1A1Sf7R1A1A2S15G0S8fA2A3Fpv0;"). Proof using . sd_tac D05c. Qed.
Lemma sd_5a : ltac2:(tb__ "0|1|
S6bS0SfS11S10S11S32S32A2A1S10S34A1A2M0A1S11cSfcR1A1Sf7R1A1A2S15G0S95A2A3Fpv0;"). Proof using . sd_tac D5ac. Qed.
Lemma sd_5b : ltac2:(tb__ "0|1|
S6bS0SfS11S10S11S32S32A2A1S10S34A1A2M0A1S11cSfdR1A1Sf7R1A1A2S15G0S96A2A3Fpv0;"). Proof using . sd_tac D5bc. Qed.
Lemma sd_11 : ltac2:(tb__ "0|1|
S6bS0SfS11S10S11S32S32A2A1S10S34A1A2M0A1S11cS104R1A1SfeR1A1A2S15G0S91A2A3Fpv0;"). Proof using . sd_tac D11c. Qed.
Lemma sd_22 : ltac2:(tb__ "0|1|
S6bS0SfS11S10S11S32S32A2A1S10S34A1A2M0A1S11cS105R1A1SffR1A1A2S15G0S92A2A3Fpv0;"). Proof using . sd_tac D22c. Qed.
Lemma sd_33 : ltac2:(tb__ "0|1|
S6bS0SfS11S10S11S32S32A2A1S10S34A1A2M0A1S11cS106R1A1S100R1A1A2S15G0S93A2A3Fpv0;"). Proof using . sd_tac D33c. Qed.
Lemma sd_44 : ltac2:(tb__ "0|1|
S6bS0SfS11S10S11S32S32A2A1S10S34A1A2M0A1S11cS107R1A1S101R1A1A2S15G0S94A2A3Fpv0;"). Proof using . sd_tac D44c. Qed.

Lemma L1_eq : ltac2:(tb__ "0|0|
S6bS0S10S9eA1S10bR1A1SeS9eS9fS104R1A1Sa0A2S13S9eA1A3A3Fpv0;"). Proof using . intros [| | |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. Qed.
Lemma L2_eq : ltac2:(tb__ "0|0|
S6bS0S10S9eA1S10cR1A1SeS9eS9fS105R1A1Sa0A2S13S9eA1A3A3Fpv0;"). Proof using . intros [| | |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. Qed.
Lemma L3_eq : ltac2:(tb__ "0|0|
S6bS0S10S9eA1S10dR1A1SeS9eS9fS106R1A1Sa0A2S13S9eA1A3A3Fpv0;"). Proof using . intros [| | |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. Qed.
Lemma L4_eq : ltac2:(tb__ "0|0|
S6bS0S10S9eA1S10eR1A1SeS9eS9fS107R1A1Sa0A2S13S9eA1A3A3Fpv0;"). Proof using . intros [| | |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. Qed.
Lemma L5_eq : ltac2:(tb__ "0|0|
S6bS0S10S9eA1S10fR1A1SeS9eS9fSfcR1A1Sa0A2SeS9eS9fSfdR1A1Sa0A2S13S9eA1A3A3A3Fpv0;"). Proof using . intros [| | |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end. Qed.

Lemma swf_C5 : ltac2:(tb__ "0|0|
S6bS0ScS47Sf7R1A1A1SdA3Fpv0;"). Proof using . by_pv. Qed.
Lemma swf_Ck : ltac2:(tb__ "0|0|
S6bS0ScS47S103R1A1A1SdA3Fpv0;"). Proof using . by_pv. Qed.
Lemma swf_C1 : ltac2:(tb__ "0|0|
S6bS0ScS47SfeR1A1A1SdA3Fpv0;"). Proof using . by_pv. Qed.
Lemma swf_C2 : ltac2:(tb__ "0|0|
S6bS0ScS47SffR1A1A1SdA3Fpv0;"). Proof using . by_pv. Qed.
Lemma swf_C3 : ltac2:(tb__ "0|0|
S6bS0ScS47S100R1A1A1SdA3Fpv0;"). Proof using . by_pv. Qed.
Lemma swf_C4 : ltac2:(tb__ "0|0|
S6bS0ScS47S101R1A1A1SdA3Fpv0;"). Proof using . by_pv. Qed.

Definition SETS5 : list (positive * sv) := scratch_of (fst D05c).
Definition SETS5a : list (positive * sv) := scratch_of (fst D5ac).
Definition SETS5b : list (positive * sv) := scratch_of (fst D5bc).
Lemma vars_05 : ltac2:(tb__ "0|0|
S6bS0ScSe9S9S1aScaS112S11S9S32A2S9S18S9S32A2S9bA4R1A2A1Lu;SfbR1A1A2SdA3Fpv0;"). Proof using . by_pv. Qed.
Lemma vars_5a : ltac2:(tb__ "0|0|
S6bS0ScSe9S9S1aScaS112S11S9S32A2S9S18S9S32A2S9cA4R1A2A1Lu;SfcR1A1A2SdA3Fpv0;"). Proof using . by_pv. Qed.
Lemma vars_5b : ltac2:(tb__ "0|0|
S6bS0ScSe9S9S1aScaS112S11S9S32A2S9S18S9S32A2S9dA4R1A2A1Lu;SfdR1A1A2SdA3Fpv0;"). Proof using . by_pv. Qed.
Lemma vars_L0k : ltac2:(tb__ "0|1|
S6bS0ScSe9S9S1aScaS112S11S9S32A2M0S9S18S9S32A2S13G0A1A4R1A2A1Lu;SfaR1A1A2SdA3Fpv0;"). Proof using . by_pv. Qed.
Lemma vars_L1s : ltac2:(tb__ "0|1|
S6bS0ScSe9S9S1aScaS112S11S9S32A2M0S9S18S9S32A2S13G0A1A4R1A2A1Lu;S104R1A1A2SdA3Fpv0;"). Proof using . by_pv. Qed.
Lemma vars_L2s : ltac2:(tb__ "0|1|
S6bS0ScSe9S9S1aScaS112S11S9S32A2M0S9S18S9S32A2S13G0A1A4R1A2A1Lu;S105R1A1A2SdA3Fpv0;"). Proof using . by_pv. Qed.
Lemma vars_L3s : ltac2:(tb__ "0|1|
S6bS0ScSe9S9S1aScaS112S11S9S32A2M0S9S18S9S32A2S13G0A1A4R1A2A1Lu;S106R1A1A2SdA3Fpv0;"). Proof using . by_pv. Qed.
Lemma vars_L4s : ltac2:(tb__ "0|1|
S6bS0ScSe9S9S1aScaS112S11S9S32A2M0S9S18S9S32A2S13G0A1A4R1A2A1Lu;S107R1A1A2SdA3Fpv0;"). Proof using . by_pv. Qed.

Lemma P5a_in : ltac2:(tb__ "0|0|
S6bS0ScSccS34S34ScdS34S52R1A1S41SfcR2A1A1A3Lp;S15bA3SdA3Fpv0;"). Proof using . by_pv. Qed.
Lemma P5b_in : ltac2:(tb__ "0|0|
S6bS0ScSccS34S34ScdS34S52R1A1S41SfdR2A1A1A3Lp;S15cA3SdA3Fpv0;"). Proof using . by_pv. Qed.
Lemma P5_supported : ltac2:(tb__ "0|1|
S1S0ScSccS34SeaSc9A1M0S15bA3SdA3S1S0ScSccS34Se0S15bA3SdA3S1S0ScSccS34G0S15cA3SdA3S0ScSccS34Se0S15cA3SdA3A2A2A2").
Proof using . repeat split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma F34_supported : ltac2:(tb__ "0|1|
S1S0ScSccS34SeaSc9A1M0S15dA3SdA3S1S0ScSccS34Se0S15dA3SdA3S1S0ScSccS34G0S15eA3SdA3S0ScSccS34Se0S15eA3SdA3A2A2A2").
Proof using . repeat split; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma in_facts_b : ltac2:(tb__ "0|0|
S34S46S0ScScdS34S52R2A1S41R1A1A3SdA3ScbS34R3S41R2A1A3F_;FS;Fp;").
Proof using . intros p S H. apply existsb_exists in H as (q & Hq & E). apply sprop_eqb_sound in E. subst q. exact Hq. Qed.
Lemma leaf_facts_Z : ltac2:(tb__ "0|0|
S36S46Se6S10S34A1Sc8VrhoW;R4A2ScfS2dS7cR4R5R3A5S0ScSccS34S34ScdS34S52R1A1S41R6A1A3Lp;R3A3SdA3S0ScSccS34SeaSc9A1R4A3SdA3S0ScSccS34Se0R5A3SdA3S113S34SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4A2R6A3F_;F_;F_;F_;F_;Fl;Fw;FS;Frho';").
Proof using m0.
  intros rho' S w l Hag HSP Hin Hv Hs. apply Forall_forall. intros p Hp.
  apply (leaf_fact rho' S w p Hag HSP).
  - apply in_facts_b. exact (proj1 (forallb_forall _ _) Hin p Hp).
  - exact (proj1 (forallb_forall _ _) Hv p Hp).
  - exact (proj1 (forallb_forall _ _) Hs p Hp).
Qed.

Lemma ze_kexpr : ltac2:(tb__ "0|0|
S0S8Se1Sa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S3dS125S3dS11fS37PcA1S33Z3A1A3S33Z4A1A3A3Sa9Vn;A1A3").
Proof using HCS HLok HMI HP12 HW. exact ze_kq. Qed.

Lemma link_0k : ltac2:(tb__ "0|1|
S36Se6Sc8VrhoW;R2A2ScfS2dS7cSfaSa6Vs;Vn;A2M0A1R3R2A5S1S1dZaSa9Vn;A1A2S115S2dVrhoW;S7cS103G0A1R3A5A2F_;F_;Fw;Frho';").
Proof using HCS HLok HMI HP12 HW Hdepth Hsp m0.
  intros rho' w Hag HSP. pose proof R_all as R.
  assert (Hk : 10 <= kq).
  { pose proof (leaf_fact rho' _ w _ Hag HSP (L0k_fact pv) eq_refl eq_refl) as F. cbn [zholds zcond] in F.
    rewrite ze_lit, (ze_var), zr1_12 in F. change (157 mod 2 ^ 64) with 157 in F. rewrite Z.mod_small in F by (unfold MMAP_THRESHOLD in R; lia).
    destruct (n <? 157) eqn:E; [exfalso; apply F; reflexivity|]. apply Z.ltb_ge in E. pose proof n157_kq. lia. }
  split; [exact Hk|].
  eapply (linkp segsU rhoW K (L0k pv) (Ck pv) [] _ _ rho' w); [apply vars_L0k | reflexivity | apply swf_Ck | apply sd_0k | exact Hag | | exact HSP].
  intros HagS _. cbn [D0kc fst snd]. split.
  - unfold diffs_ok. apply Forall_cons; [cbn [fst snd]|apply Forall_nil]. sem_pair HagS.
    rewrite ze_kexpr. symmetry. exact ze149.
  - constructor; [|constructor; [|constructor]]; hfact HagS; zev; lia.
Qed.

Lemma link_05 : ltac2:(tb__ "0|1|
S36Se6Sc8VrhoW;R2A2ScfS2dS7cSfbSa6Vs;Vn;A2M0A1R3R2A5S115S2dVrhoW;S7cSf7G0A1R3A5F_;F_;Fw;Frho';").
Proof using HCS HLok HMI HP12 HW Hdepth Hsp m0.
  intros rho' w Hag HSP. pose proof R_all as R.
  assert (Hn157 : n < 157).
  { pose proof (leaf_fact rho' _ w _ Hag HSP (L0s_fact pv) eq_refl eq_refl) as F. cbn [zholds zcond] in F.
    rewrite ze_lit, ze_var, zr1_12 in F. change (157 mod 2 ^ 64) with 157 in F. rewrite Z.mod_small in F by (unfold MMAP_THRESHOLD in R; lia).
    destruct (n <? 157) eqn:E; [apply Z.ltb_lt in E; exact E | discriminate]. }
  eapply (linkp segsU rhoW K (L0s pv) (C5 pv) SETS5 _ _ rho' w); [apply vars_05 | reflexivity | apply swf_C5 | apply sd_05 | exact Hag | | exact HSP].
  intros HagS _. cbn [D05c fst snd]. split; [|constructor].
  unfold diffs_ok.
  repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
  all: first [scratch_pair Hag HagS | sem_pair HagS].
  rewrite ze_kexpr. cbn [zeval]. rewrite Zv150. apply kq_small. exact Hn157.
Qed.

Lemma link_5a : ltac2:(tb__ "0|1|
S36Se6S1dZaSa9Vn;A1A2Sc8VrhoW;R3A2ScfS2dS7cSfcSa6Vs;Vn;A2M0A1R4R3A5S115S2dVrhoW;S7cSf7G0A1R4A5F_;F_;F_;Fw;Frho';").
Proof using HCS HLok HMI HW Hdepth Hsp m0.
  intros rho' w Hk Hag HSP. pose proof R_all as R.
  pose proof (stage_cert Hk) as (_ & _ & _ & S5a & _).
  pose proof P5_supported as (Pv & Ps & _ & _).
  pose proof (S5a (leaf_facts_Z rho' _ w P5a Hag HSP (P5a_in pv) Pv Ps)) as E5.
  eapply (linkp segsU rhoW K (L5a pv) (C5 pv) SETS5a _ _ rho' w); [apply vars_5a | reflexivity | apply swf_C5 | apply sd_5a | exact Hag | | exact HSP].
  intros HagS _. cbn [D5ac fst snd]. split; [|constructor].
  unfold diffs_ok.
  repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
  all: first [scratch_pair Hag HagS | sem_pair HagS].
  transitivity (sc0 : Z); [exact E5 | exact (eq_sym Zv150)].
Qed.
Lemma link_5b : ltac2:(tb__ "0|1|
S36Se6S1dZaSa9Vn;A1A2Sc8VrhoW;R3A2ScfS2dS7cSfdSa6Vs;Vn;A2M0A1R4R3A5S115S2dVrhoW;S7cSf7G0A1R4A5F_;F_;F_;Fw;Frho';").
Proof using HCS HLok HMI HW Hdepth Hsp m0.
  intros rho' w Hk Hag HSP. pose proof R_all as R.
  pose proof (stage_cert Hk) as (_ & _ & _ & _ & S5b).
  pose proof P5_supported as (_ & _ & Pv & Ps).
  pose proof (S5b (leaf_facts_Z rho' _ w P5b Hag HSP (P5b_in pv) Pv Ps)) as E5.
  eapply (linkp segsU rhoW K (L5b pv) (C5 pv) SETS5b _ _ rho' w); [apply vars_5b | reflexivity | apply swf_C5 | apply sd_5b | exact Hag | | exact HSP].
  intros HagS _. cbn [D5bc fst snd]. split; [|constructor].
  unfold diffs_ok.
  repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
  all: first [scratch_pair Hag HagS | sem_pair HagS].
  transitivity (sc0 : Z); [exact E5 | exact (eq_sym Zv150)].
Qed.

Lemma link_11 : ltac2:(tb__ "0|1|
S36Se6S1dZaSa9Vn;A1A2Sc8VrhoW;R3A2ScfS2dS7cS104Sa6Vs;Vn;A2M0A1R4R3A5S115S2dVrhoW;S7cSfeG0A1R4A5F_;F_;F_;Fw;Frho';").
Proof using HCS HLok HMI HW m0 rho.
  intros rho' w Hk Hag HSP. destruct zr1_stages as (E149 & E160 & E161 & E162 & E163 & El1 & El4). pose proof Gk_range as GR.
  eapply (linkp segsU rhoW K (L1s pv) (C1 pv) [] _ _ rho' w); [apply vars_L1s | reflexivity | apply swf_C1 | apply sd_11 | exact Hag | | exact HSP].
  intros HagS _. cbn [D11c fst snd]. split; [|constructor].
  unfold diffs_ok. apply Forall_cons; [cbn [fst snd]|apply Forall_nil]. sem_pair HagS.
  transitivity (zr1 160%positive); [exact (eq_sym E160) | change (zeval zr1 zl1 (SVar 160)) with (zr1 160%positive mod 2 ^ 64); rewrite zr1_160; symmetry; apply Z.mod_small; lia].
Qed.
Lemma link_22 : ltac2:(tb__ "0|1|
S36Se6S1dZaSa9Vn;A1A2Sc8VrhoW;R3A2ScfS2dS7cS105Sa6Vs;Vn;A2M0A1R4R3A5S115S2dVrhoW;S7cSffG0A1R4A5F_;F_;F_;Fw;Frho';").
Proof using HCS HLok HMI HW m0 rho.
  intros rho' w Hk Hag HSP. destruct zr1_stages as (E149 & E160 & E161 & E162 & E163 & El1 & El4). pose proof Gk_range as GR.
  eapply (linkp segsU rhoW K (L2s pv) (C2 pv) [] _ _ rho' w); [apply vars_L2s | reflexivity | apply swf_C2 | apply sd_22 | exact Hag | | exact HSP].
  intros HagS _. cbn [D22c fst snd]. split; [|constructor].
  unfold diffs_ok. apply Forall_cons; [cbn [fst snd]|apply Forall_nil]. sem_pair HagS.
  transitivity (zr1 161%positive); [exact (eq_sym E161) | change (zeval zr1 zl1 (SVar 161)) with (zr1 161%positive mod 2 ^ 64); rewrite zr1_161; symmetry; apply Z.mod_small; lia].
Qed.
Lemma link_33 : ltac2:(tb__ "0|1|
S36Se6S1dZaSa9Vn;A1A2Sc8VrhoW;R3A2ScfS2dS7cS106Sa6Vs;Vn;A2M0A1R4R3A5S115S2dVrhoW;S7cS100G0A1R4A5F_;F_;F_;Fw;Frho';").
Proof using HCS HLok HMI HW m0 rho.
  intros rho' w Hk Hag HSP. destruct zr1_stages as (E149 & E160 & E161 & E162 & E163 & El1 & El4). pose proof Gk_range as GR.
  pose proof (stage_cert Hk) as (S3 & _).
  pose proof F34_supported as (F3v & F3s & _ & _).
  eapply (linkp segsU rhoW K (L3s pv) (C3 pv) [] _ _ rho' w); [apply vars_L3s | reflexivity | apply swf_C3 | apply sd_33 | exact Hag | | exact HSP].
  intros HagS _. cbn [D33c fst snd]. split.
  - unfold diffs_ok. apply Forall_cons; [cbn [fst snd]|apply Forall_nil]. sem_pair HagS.
    transitivity (zr1 162%positive); [exact (eq_sym E162) | change (zeval zr1 zl1 (SVar 162)) with (zr1 162%positive mod 2 ^ 64); rewrite zr1_162; symmetry; apply Z.mod_small; lia].
  - exact (ZF_holds _ F3 HagS F3v F3s S3).
Qed.
Lemma link_44 : ltac2:(tb__ "0|1|
S36Se6S1dZaSa9Vn;A1A2Sc8VrhoW;R3A2ScfS2dS7cS107Sa6Vs;Vn;A2M0A1R4R3A5S115S2dVrhoW;S7cS101G0A1R4A5F_;F_;F_;Fw;Frho';").
Proof using HCS HLok HMI HW m0 rho.
  intros rho' w Hk Hag HSP. destruct zr1_stages as (E149 & E160 & E161 & E162 & E163 & El1 & El4). pose proof Gk_range as GR.
  pose proof (stage_cert Hk) as (_ & S4 & _).
  pose proof F34_supported as (_ & _ & F4v & F4s).
  eapply (linkp segsU rhoW K (L4s pv) (C4 pv) [] _ _ rho' w); [apply vars_L4s | reflexivity | apply swf_C4 | apply sd_44 | exact Hag | | exact HSP].
  intros HagS _. cbn [D44c fst snd]. split.
  - unfold diffs_ok. apply Forall_cons; [cbn [fst snd]|apply Forall_nil]. sem_pair HagS.
    transitivity (zr1 163%positive); [exact (eq_sym E163) | change (zeval zr1 zl1 (SVar 163)) with (zr1 163%positive mod 2 ^ 64); rewrite zr1_163; symmetry; apply Z.mod_small; lia].
  - exact (ZF_holds _ F4 HagS F4v F4s S4).
Qed.

Lemma lnx_P0 : ltac2:(tb__ "0|1|
S6bS1S0ScS43S6fSb6R1A2M0A1S16A3S0S9S42G0A1Sb7A3A2Fpv0;"). Proof using . intros [| | |]; split; reflexivity. Qed.
Lemma lnx_Ck : ltac2:(tb__ "0|1|
S6bS1S0ScS43S103R1A1M0A1S16A3S0S9S42G0A1Sb7A3A2Fpv0;"). Proof using . intros [| | |]; split; reflexivity. Qed.
Lemma lnx_C1 : ltac2:(tb__ "0|1|
S6bS1S0ScS43SfeR1A1M0A1S16A3S0S9S42G0A1Sb7A3A2Fpv0;"). Proof using . intros [| | |]; split; reflexivity. Qed.
Lemma lnx_C2 : ltac2:(tb__ "0|1|
S6bS1S0ScS43SffR1A1M0A1S16A3S0S9S42G0A1Sb7A3A2Fpv0;"). Proof using . intros [| | |]; split; reflexivity. Qed.
Lemma lnx_C3 : ltac2:(tb__ "0|1|
S6bS1S0ScS43S100R1A1M0A1S16A3S0S9S42G0A1Sb7A3A2Fpv0;"). Proof using . intros [| | |]; split; reflexivity. Qed.
Lemma lnx_C4 : ltac2:(tb__ "0|1|
S6bS1S0ScS43S101R1A1M0A1S16A3S0S9S42G0A1Sb7A3A2Fpv0;"). Proof using . intros [| | |]; split; reflexivity. Qed.
Lemma lnx_C5 : ltac2:(tb__ "0|1|
S6bS1S0ScS43Sf7R1A1M0A1S16A3S0S9S42G0A1Sb7A3A2Fpv0;"). Proof using . intros [| | |]; split; reflexivity. Qed.
Lemma lnx_C5o : ltac2:(tb__ "0|1|
S6bS1S0ScS43S102R1A1M0A1S16A3S0S9S42G0A1Sb7A3A2Fpv0;"). Proof using . intros [| | |]; split; reflexivity. Qed.

Theorem pro_C5 : ltac2:(tb__ "0|1|
VTR;Z0ScfS2dS7cS6fSb6Sa6Vs;Vn;A2M0A2VrhoW;A4S115S2dVrhoW;S7cSf7G0A1A4A3").
Proof using HCS HLok HMI HP12 HW Hdepth Hsp RR m0.
  eapply seq0.
  - apply (seg_run 400 (P0 MR_P pv) (L0 pv) (fun w => POST (C5 pv) w \/ (10 <= kq /\ POST (Ck pv) w)) rhoW);
      [apply (proj1 (lnx_P0 pv)) | apply (proj2 (lnx_P0 pv)) | apply run0 | apply agrees_refl |].
    intros Lf rho'' Hin Hag. apply seg_leaf. intros w HSP. destruct (L0_cases pv Lf Hin) as [E|E]; rewrite E in HSP.
    + left. exact (link_05 rho'' w Hag HSP).
    + right. exact (link_0k rho'' w Hag HSP).
  - apply (trr_disj RR); [lia | apply (trr_skip RR); [lia | intros w Hw; exact Hw] |].
    apply (trr_inh RR); [lia|]. intros w0 [Hk _]. eapply (trr_pre RR); [intros w [_ X]; exact X|].

    apply from_POST. intros r0 Hag0.
    eapply seq0; [apply (seg_run 100 (Ck pv) (L1 pv) (POST (C1 pv)) r0); [apply (proj1 (lnx_Ck pv)) | apply (proj2 (lnx_Ck pv)) | apply run1 | exact Hag0 |];
      intros Lf rho'' Hin Hag; apply seg_leaf; intros w HSP; rewrite L1_eq in Hin; destruct Hin as [<-|[]]; exact (link_11 rho'' w Hk Hag HSP) |].
    apply from_POST. intros r1 Hag1.
    eapply seq0; [apply (seg_run 100 (C1 pv) (L2 pv) (POST (C2 pv)) r1); [apply (proj1 (lnx_C1 pv)) | apply (proj2 (lnx_C1 pv)) | apply run2 | exact Hag1 |];
      intros Lf rho'' Hin Hag; apply seg_leaf; intros w HSP; rewrite L2_eq in Hin; destruct Hin as [<-|[]]; exact (link_22 rho'' w Hk Hag HSP) |].
    apply from_POST. intros r2 Hag2.
    eapply seq0; [apply (seg_run 100 (C2 pv) (L3 pv) (POST (C3 pv)) r2); [apply (proj1 (lnx_C2 pv)) | apply (proj2 (lnx_C2 pv)) | apply run3 | exact Hag2 |];
      intros Lf rho'' Hin Hag; apply seg_leaf; intros w HSP; rewrite L3_eq in Hin; destruct Hin as [<-|[]]; exact (link_33 rho'' w Hk Hag HSP) |].
    apply from_POST. intros r3 Hag3.
    eapply seq0; [apply (seg_run 100 (C3 pv) (L4 pv) (POST (C4 pv)) r3); [apply (proj1 (lnx_C3 pv)) | apply (proj2 (lnx_C3 pv)) | apply run4 | exact Hag3 |];
      intros Lf rho'' Hin Hag; apply seg_leaf; intros w HSP; rewrite L4_eq in Hin; destruct Hin as [<-|[]]; exact (link_44 rho'' w Hk Hag HSP) |].
    apply from_POST. intros r4 Hag4.
    apply (seg_run 100 (C4 pv) (L5 pv) (POST (C5 pv)) r4); [apply (proj1 (lnx_C4 pv)) | apply (proj2 (lnx_C4 pv)) | apply run5 | exact Hag4 |].
    intros Lf rho'' Hin Hag. apply seg_leaf. intros w HSP. rewrite L5_eq in Hin. destruct Hin as [<-|[<-|[]]].
    + exact (link_5a rho'' w Hk Hag HSP).
    + exact (link_5b rho'' w Hk Hag HSP).
Qed.

Lemma pv_cases : ltac2:(tb__ "0|6|
S6bOLx;Sa6Vs;Vn;A2S2S0SfSd1A1M0SaeVs;Vn;A2S17Sd1A1M1A3M2A1S1G2S0ScSa8Vs;Vn;A2M3S16A3A2S1G2S1S0ScG3SdA3M4S0G0SafVs;Vn;A2G1A3M5A2A2S1G2S1G4S2G5A1A2A2X6bx4").
Proof using .
  unfold U.Mal_mslow__G1.Mal_mslow_I0.pv. destruct (U.Mal_mslow__G1.Mal_mslow_I0.g0o s n); [discriminate|].
  destruct (U.Mal_mslow__G1.Mal_mslow_I0.crb s n); [|split; reflexivity].
  destruct (U.Mal_mslow__G1.Mal_mslow_I0.g1o s n); repeat split; try reflexivity. discriminate.
Qed.

Definition bonus : Z := ltac2:(tb__ "0|2|
SfSd1A1S8Lx;SafVs;Vn;A2Sd1ScS8L_;S19S23SacVs;Vn;A2Z0M0A2S23Sb0Vs;Vn;A2G0A2A2Z3M1G0Xcx2Ls0;G1Xfx2").

Lemma bonus_eq : ltac2:(tb__ "0|2|
S0ScSa8Vs;Vn;A2SdA3S0S8ScS8L_;SfSd1A1M0ScLx;SafVs;Vn;A2Sd1SfSd2A1ScLx;SdaSd4Vs;A1R1A2Sd2Sd2ScLm;R1G0G0SdLnext;Lprev;SdSd9S19S23Sd7R1A1Z0M1A2S23Sd8R1A1G1A2A2Lam;Xd2x3Lm;SdXfx2Lh;SdXfx2Z3G1Xcx2S8eA3F_;").
Proof using HW.
  intros Hc. unfold bonus. destruct (U.Mal_mslow__G1.Mal_mslow_I0.g1o s n) as [g1|] eqn:E; [|reflexivity].
  destruct (g1_facts g1 Hc E) as (a1 & _ & HM & Ham & _).
  change (mlookup (st_metas s) g1) with (MT s g1). rewrite HM.
  unfold U.Mal_mslow__G1.Mal_mslow_I0.av1, U.Mal_mslow__G1.Mal_mslow_I0.fr1. rewrite Ham. reflexivity.
Qed.

Lemma cl_A : ltac2:(tb__ "0|0|
S2S0SfSd1A1SaeVs;Vn;A2S17Sd1A1A3A1S0S8SadVs;Vn;A2Sa7Vn;A1A3F_;").
Proof using . intros Hg. destruct cl_cases as [[E _]|(_ & G & _)]; [exact E | exfalso; exact (Hg G)]. Qed.
Lemma cl_B1 : ltac2:(tb__ "0|0|
S0ScSa8Vs;Vn;A2S16A3S0S8SadVs;Vn;A2Sa7Vn;A1A3F_;").
Proof using . intros Hc. destruct cl_cases as [[E _]|(_ & _ & C & _)]; [exact E | rewrite C in Hc; discriminate]. Qed.
Lemma cl_B : ltac2:(tb__ "0|3|
S0SfSd1A1SaeVs;Vn;A2S17Sd1A1A3S0ScSa8Vs;Vn;A2SdA3S1S1dS1cSaaVs;Vn;A2S8eA2M0ZcM1A2S0S8SadVs;Vn;A2M2SabVn;A1A3F_;S1eG1G0A2S0S8G2Sa7Vn;A1A3F_;A2F_;F_;").
Proof using HW rho.
  intros Hg Hc. rewrite <- (bonus_eq Hc).
  destruct cl_cases as [[E C]|(E & _ & _ & LE)].
  - split; [|intros; exact E]. intros HLE. exfalso. destruct C as [C|[C|C]]; [exact (C Hg) | rewrite C in Hc; discriminate | lia].
  - split; [intros; exact E|]. intros HLT. exfalso. lia.
Qed.

Lemma dead_av1 : ltac2:(tb__ "0|2|
S0SfSd1A1M0SaeVs;Vn;A2S17Sd1A1M1A3S0ScSa8Vs;Vn;A2SdA3S2S0G0SafVs;Vn;A2G1A3A1S2S0S8SacVs;Vn;A2Z0A3A1S1dSaaVs;Vn;A2ZcA2S6F_;F_;F_;F_;F_;").
Proof using HCS HW Hsp.
  intros Hg Hc Hg1 Hav Hu.
  destruct (U.Mal_mslow__G1.Mal_mslow_I0.g1o s n) as [g1|] eqn:E; [|exact (Hg1 eq_refl)].
  destruct (g1_facts g1 Hc E) as (a1 & _ & HM & Ham & _).
  assert (B : bonus = 0).
  { unfold bonus. rewrite E. unfold U.Mal_mslow__G1.Mal_mslow_I0.av1 in Hav. rewrite Ham in Hav.
    unfold U.Mal_mslow__G1.Mal_mslow_I0.av1, U.Mal_mslow__G1.Mal_mslow_I0.fr1. rewrite Ham. destruct (am_avail a1 =? 0) eqn:X; [apply Z.eqb_eq in X; exfalso; exact (Hav X) | reflexivity]. }
  pose proof (proj1 (cl_B Hg Hc) ltac:(lia)) as Ecl.
  apply Hav. unfold U.Mal_mslow__G1.Mal_mslow_I0.av1. rewrite Ham.
  apply (proj2 HCS g1 a1); [|exact HM].
  change (malloc_class s n) with (cl : Z). rewrite Ecl. exact E.
Qed.

Lemma zf_sc6 : ltac2:(tb__ "0|1|
SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S122S37P96A1S33Z6M0A1A3A3S0S8Sa7Vn;A1G0A3F_;").
Proof using HCS HLok HMI HW. intros F. pose proof R_all. revert F. zev. intros F. apply Z.eqb_eq in F. exact F. Qed.
Lemma zf_nsc6 : ltac2:(tb__ "0|1|
S2SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S122S37P96A1S33Z6M0A1A3A3A1S2S0S8Sa7Vn;A1G0A3A1F_;").
Proof using HCS HLok HMI HW. intros F E. apply F. pose proof R_all. zev. apply Z.eqb_eq. exact E. Qed.
Lemma zf_big : ltac2:(tb__ "0|1|
SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S120S33Z1bA1S3dS11fS37P96A1S33N4A1A3A3A3S3S1eSa7Vn;A1M0Z4A2S1eZ1fG0A2A2F_;").
Proof using HCS HLok HMI HW. intros F. pose proof R_all. revert F. zev. intros F. apply Z.ltb_lt in F. mlia. Qed.
Lemma zf_nbig : ltac2:(tb__ "0|1|
S2SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S120S33Z1bA1S3dS11fS37P96A1S33N4A1A3A3A3A1S1S1dZ4Sa7Vn;A1M0A2S1dG0Z1fA2A2F_;").
Proof using HCS HLok HMI HW. intros F. pose proof R_all. destruct (Z_lt_dec sc0 4) as [A|A]; [exfalso|destruct (Z_lt_dec 31 sc0) as [B|B]; [exfalso|lia]]; apply F; zev; apply Z.ltb_lt; mlia. Qed.
Lemma zf_odd : ltac2:(tb__ "0|0|
SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S121S3dS123S37P96A1S33Z1A1A3S33Z0A1A3A3S0ScS25Sa7Vn;A1A1S16A3F_;").
Proof using HCS HLok HMI HW. intros F. pose proof R_all. revert F. zev. rewrite (Z.mod_small sc0) by lia. intros F. rewrite <- land1_even. destruct (Z.land sc0 1 =? 0); [discriminate|reflexivity]. Qed.
Lemma zf_even : ltac2:(tb__ "0|0|
S2SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S121S3dS123S37P96A1S33Z1A1A3S33Z0A1A3A3A1S0ScS25Sa7Vn;A1A1SdA3F_;").
Proof using HCS HLok HMI HW. intros F. pose proof R_all. rewrite <- land1_even. destruct (Z.land sc0 1 =? 0) eqn:E; [reflexivity|]. exfalso. apply F. zev. rewrite (Z.mod_small sc0) by lia. rewrite E. reflexivity. Qed.
Lemma zf_u0 : ltac2:(tb__ "0|1|
SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S122S37Pa5A1S33Z0M0A1A3A3S0S8Sb1Vs;Vn;A2G0A3F_;").
Proof using HCS HLok HMI HW. intros F. pose proof R_all. revert F. zev. intros F. apply Z.eqb_eq in F. exact F. Qed.
Lemma zf_nu0 : ltac2:(tb__ "0|1|
S2SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S122S37Pa5A1S33Z0M0A1A3A3A1S2S0S8Sb1Vs;Vn;A2G0A3A1F_;").
Proof using HCS HLok HMI HW. intros F E. apply F. pose proof R_all. zev. apply Z.eqb_eq. exact E. Qed.
Lemma zf_u13 : ltac2:(tb__ "0|0|
SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S120S37Pa7A1S33ZdA1A3A3S1dSaaVs;Vn;A2ZcA2F_;").
Proof using HCS HLok HMI HW. intros F. pose proof R_all. revert F. zev. intros F. apply Z.ltb_lt in F. lia. Qed.
Lemma zf_nu13 : ltac2:(tb__ "0|0|
S2SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S120S37Pa7A1S33ZdA1A3A3A1S1eZcSaaVs;Vn;A2A2F_;").
Proof using HCS HLok HMI HW. intros F. pose proof R_all. destruct (Z_lt_dec 12 u1) as [A|A]; [exact A|]. exfalso. apply F. zev. apply Z.ltb_lt. lia. Qed.
Lemma zf_u3_13 : ltac2:(tb__ "0|1|
SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S120S3dS11fS37Pa7A1S33Z3M0A1A3S33ZdA1A3A3S1dS1cSaaVs;Vn;A2G0A2ZcA2F_;").
Proof using HCS HLok HMI HW. intros F. pose proof R_all. revert F. zev. intros F. apply Z.ltb_lt in F. mlia. Qed.
Lemma zf_nu3_13 : ltac2:(tb__ "0|1|
S2SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S120S3dS11fS37Pa7A1S33Z3M0A1A3S33ZdA1A3A3A1S1eZcS1cSaaVs;Vn;A2G0A2A2F_;").
Proof using HCS HLok HMI HW. intros F. pose proof R_all. destruct (Z_lt_dec 12 (u1 + 3)) as [A|A]; [exact A|]. exfalso. apply F. zev. apply Z.ltb_lt. mlia. Qed.
Lemma zf_av : ltac2:(tb__ "0|1|
SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S121S51SdQ20S37PadA1A3S33Z0M0A1A3A3S2S0S8SacVs;Vn;A2G0A3A1F_;").
Proof using HCS HLok HMI HW. intros F. pose proof R_all. revert F. zev. rewrite sext32_zero by lia. intros F E. apply Z.eqb_eq in E. rewrite E in F. discriminate. Qed.
Lemma zf_nav : ltac2:(tb__ "0|1|
S2SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S121S51SdQ20S37PadA1A3S33Z0M0A1A3A3A1S0S8SacVs;Vn;A2G0A3F_;").
Proof using HCS HLok HMI HW. intros F. pose proof R_all. destruct (Z.eq_dec av1 0) as [A|A]; [exact A|]. exfalso. apply F. zev. rewrite sext32_zero by lia. apply Z.eqb_neq in A. rewrite A. reflexivity. Qed.
Lemma zf_fr : ltac2:(tb__ "0|1|
SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S121S51SdQ20S37PaeA1A3S33Z0M0A1A3A3S2S0S8Sb0Vs;Vn;A2G0A3A1F_;").
Proof using HCS HLok HMI HW. intros F. pose proof R_all. revert F. zev. rewrite sext32_zero by lia. intros F E. apply Z.eqb_eq in E. rewrite E in F. discriminate. Qed.
Lemma zf_nfr : ltac2:(tb__ "0|1|
S2SdeSa4Vs;VL;Vn;Vrho;A4Sa5Vs;VL;Vn;Vrho;A4S38S121S51SdQ20S37PaeA1A3S33Z0M0A1A3A3A1S0S8Sb0Vs;Vn;A2G0A3F_;").
Proof using HCS HLok HMI HW. intros F. pose proof R_all. destruct (Z.eq_dec fr1 0) as [A|A]; [exact A|]. exfalso. apply F. zev. rewrite sext32_zero by lia. apply Z.eqb_neq in A. rewrite A. reflexivity. Qed.

Inductive pd := DNl | DSct | DCtz | DAct0 (e : sv) | DUsg0 | DAct1 (e : sv) | DUsg1 | DMetaA | DMetaAF.

Definition obj_of (d : pd) : sobj := ltac2:(tb__ "0|2|
S7bS35Ld;Vd;Sc5Sb6A1SbbSb6A1Sc4Sb6A1S32S72Sb6Se5P96A1M0R1A3Le;S73Sb6G0Se5Pa5A1A3S32S72Sb6Se5Pa4A1M1R1A3Le;S73Sb6G1Se5Pa7A1A3S74Se5PacA1A1S75Se5Pa6A1Se5PadA1Se5PaeA1A3X7bx9").
Definition dlo (d : pd) : Z := ltac2:(tb__ "0|8|
S7bS8Ld;Vd;S1cZ5a35bZ0M0A2S1cZ108ecG0A2S1cZ108ccG0A2S32S1cZ5a3c8M1S1cS22Z8M2Sa7Vn;A1A2M3Z58M4A2A2Le;S1cG1S1cG3Z1d8M5A2A2S32S1cG1S1cS22G2SabVn;A1A2M6G4A2A2Le;S1cG1S1cG6G5A2A2S1cSb2Vs;VL;Vn;A3Z18M7A2S1cSb3Vs;VL;Vn;A3G7A2X7bx9").
Definition dhi (d : pd) : Z := ltac2:(tb__ "0|7|
S7bS8Ld;Vd;S1cZ5a35bZ1A2S1cZ108ecZ60A2S1cZ108ccZ20M0A2S32S1cZ5a3c8M1S1cS1cS22Z8M2Sa7Vn;A1A2M3Z58M4A2G2A2A2Le;S1cG1S1cS1cG3Z1d8M5A2G2A2A2S32S1cG1S1cS1cS22G2SabVn;A1A2M6G4A2G2A2A2Le;S1cG1S1cS1cG6G5A2G2A2A2S1cSb2Vs;VL;Vn;A3Z1cA2S1cSb3Vs;VL;Vn;A3G0A2X7bx9").
Definition dcells (d : pd) : list (Z * nat * sv) := ltac2:(tb__ "0|9|
S7bS10S11S11S8S14A2M0S32A2M1A1Ld;Vd;SeG1S12G0S32S12S8S14Z0M2U1A4S33G2A1M3A4S13G1A1M4A3G4G4S32SeG1S12G0S32S12S8S14G2U8A4M5R1A4G4A3Le;M6SeG1S12G0S32G5Se5Pa5A1A4G4A3G6SeG1S12G0S32G5Se5Pa7A1A4G4A3SeG1S12G0S32S12S8S14G2U4M7A4M8G3A4G4A3SeG1S12G0S32G8Se5PadA1A4SeG1S12G0S32S12S8S14Z4G7A4Se5PaeA1A4G4A3A3X7bx9").
Definition drom (d : pd) : option positive := ltac2:(tb__ "0|2|
S7bSfS9A1Ld;Vd;S17S9A1M0S15S9P1A2S15S9P4A2S32G0Le;M1G0G1G0G0G0X7bx9").
Definition DS (d : pd) : Prop := ltac2:(tb__ "0|2|
S7bOLd;Vd;S5S5S5S32S3S0S32R1Se5PacA1A3S0S32R1S33Z0A1A3M0A2Le;S5S32S1S3S0S32R1Se5Pa6A1A3G0A2S1eSabVn;A1Z30A2M1A2Le;G1S5S5X7bx9").

Definition dsF (pv0 : pvar) : list pd := ltac2:(tb__ "0|3|
S6bS10S7bA1Lpv0;Vpv0;SeS7bS85SeS7bS86SeS7bS84SeS7bS8bSe5PacA1A1SeS7bS98S13S7bA1M0A3A3A3A3A3SeS7bS85SeS7bS86SeS7bS84SeS7bS8bS33Z0A1M1A1M2SeS7bS89G0A3A3A3A3A3SeS7bS85SeS7bS86SeS7bS84SeS7bG2SeS7bS89SeS7bS8cG1A1SeS7bS8dG0A3A3A3A3A3A3A3SeS7bS85SeS7bS86SeS7bS84SeS7bG2SeS7bS89SeS7bS8cSe5Pa6A1A1SeS7bS8dSeS7bS99G0A3A3A3A3A3A3A3A3X6bx4").
Lemma dsF_objs : ltac2:(tb__ "0|0|
S6bS0S10S35A1S112S7bS35S7fS83R1A1A4SceS35S71Sb6R1A2A2A3Fpv0;").
Proof using . intros [| | |]; reflexivity. Qed.
Lemma crb_j1 : ltac2:(tb__ "0|0|
S0ScSa8Vs;Vn;A2SdA3S1eSabVn;A1Z30A2F_;").
Proof using rho. intros Hc. pose proof (crb_true Hc) as (R & _). change (j1 : Z) with (sc0 + 1). lia. Qed.
Lemma HdsF : ltac2:(tb__ "0|0|
S7bScbS7bR1S83Sa6Vs;Vn;A2A1A3S7eR2A1F_;Fd;").
Proof using Hdepth Hsp.
  pose proof pv_cases as PC. unfold dsF. destruct (U.Mal_mslow__G1.Mal_mslow_I0.pv s n);
    intros d Hd; cbn in Hd; repeat (destruct Hd as [<-|Hd]); try (destruct Hd; fail); cbn; auto.
  - split; [auto | apply crb_j1; tauto].
  - apply crb_j1; tauto.
  - split; [auto | apply crb_j1; tauto].
  - apply crb_j1; tauto.
Qed.

Lemma rngD : ltac2:(tb__ "0|0|
S7bS36S7eR2A1Sc8VrhoW;R2A2S0S11S8S8A2S3aR3S7fR4A1A2S12S8S8S80R4A1S82R4A1A4A3F_;F_;FrhoX;Fd;").
Proof using HCS HLok HMI HW Hsp m0.
  intros d rhoX HDS (Hw & Hl & _).
  rewrite (obj_range_agreeing below200 rhoW rhoX (obj_of d) Hw Hl).
  2:{ destruct d; cbn in HDS;
        [ | | | destruct HDS as [-> | ->] | | destruct HDS as [[-> | ->] _] | | | ]; vm_compute; reflexivity. }
  destruct d; cbn in HDS.
  - exact rng_nl. - exact rng_sct. - exact rng_ctz.
  - exact (rng_act150 e). - exact rng_usg150.
  - exact (rng_act164 e (proj2 HDS)). - exact (rng_usg164 HDS).
  - exact rng_metaA. - exact rng_metaAF.
Qed.
Lemma range64D : ltac2:(tb__ "0|0|
S7bS7eR1A1S1S1dZ0S80R2A1A2S1eS82R2A1S1fZ2Z3fA2A2A2F_;Fd;").
Proof using HCS HLok HMI HW Hsp. intros d HDS. pose proof R_all. destruct d; cbn in HDS; unfold dlo, dhi; try (change (j1 : Z) with (sc0 + 1)); lia. Qed.

Lemma base_lit : ltac2:(tb__ "0|0|
S36S8Sc8VrhoW;R2A2S1S1dZ0R2A2S1eR2S1fZ2Z3eA2A2A2S0S8S79Q40S3cR4S33R3A1A2A2R3A3F_;F_;Fz;FrhoX;").
Proof using L m0 n rho s. intros rhoX z Hag Hz. rewrite (EVu rhoX (SLit z) Hag eq_refl eq_refl). cbn [zeval]. apply Z.mod_small. lia. Qed.

Lemma cellsD : ltac2:(tb__ "0|1|
S7bS8S14S32S7eR4A1ScbS11S11S8S14A2M0S32A2S12G0S32S12S8S14R4R3A4R2A4S87R5A1A3S4S39S39S1ScbS39R1S4cS7fR7A1A1A3S1S0S32S4dR1A1R4A3S1S0S14S28S49R1A1A1R5A3S36Sc8VrhoW;R1A2S0S8S1cS79Q40S3cR2S3fS7fR9A1A1A2A2S45R2S48R3A1A2A2S1cS80R9A1R8A2A3F_;FrhoX;A2A2A2Lc;A2F_;F_;Fe;Fw;Foff;Fd;").
Proof using HCS HLok HMI HW Hsp m0.
  intros d off w e HDS Hin. pose proof R_all as R.
  destruct d; cbn in Hin, HDS;
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-|]); try (destruct Hin; fail);
    (eexists; (split; [|split; [|split]]);
       [ cbn; ((left; reflexivity) + (right; left; reflexivity)) | reflexivity | reflexivity
       | intros rhoX HagX; cbn [ob_base c_off obj_of O_nl O_actv O_usgv O_metaA O_metaAF mr_nl mr_LK MR_P]; unfold dlo ]).
  - rewrite (base_lit rhoX) by (auto; lia). rewrite soff_lit_small by lia. lia.
  - rewrite (base_lit rhoX) by (auto; lia).
    rewrite (WalkReab.soff_semX rhoW zr1 zl1 Hzr Hzl rhoX (SAlu ALU_ADD (SAlu ALU_SLL (v 150) (SLit 3)) (SLit 88)) (8 * sc0 + 88) HagX eq_refl eq_refl (ze_off150 88 ltac:(lia))) by lia. lia.
  - rewrite (base_lit rhoX) by (auto; lia).
    rewrite (WalkReab.soff_semX rhoW zr1 zl1 Hzr Hzl rhoX (SAlu ALU_ADD (SAlu ALU_SLL (v 150) (SLit 3)) (SLit 472)) (8 * sc0 + 472) HagX eq_refl eq_refl (ze_off150 472 ltac:(lia))) by lia. lia.
  - destruct HDS as [_ Hj]. rewrite (base_lit rhoX) by (auto; lia).
    rewrite (WalkReab.soff_semX rhoW zr1 zl1 Hzr Hzl rhoX (SAlu ALU_ADD (SAlu ALU_SLL (v 164) (SLit 3)) (SLit 88)) (8 * j1 + 88) HagX eq_refl eq_refl (ze_off164 88 ltac:(lia))) by (change (j1 : Z) with (sc0 + 1); lia). lia.
  - rewrite (base_lit rhoX) by (auto; lia).
    rewrite (WalkReab.soff_semX rhoW zr1 zl1 Hzr Hzl rhoX (SAlu ALU_ADD (SAlu ALU_SLL (v 164) (SLit 3)) (SLit 472)) (8 * j1 + 472) HagX eq_refl eq_refl (ze_off164 472 ltac:(lia))) by (change (j1 : Z) with (sc0 + 1); lia). lia.
  - rewrite (EVu rhoX (v 172) HagX eq_refl eq_refl), ze172. rewrite soff_lit_small by lia. lia.
  - rewrite (EVu rhoX (v 166) HagX eq_refl eq_refl), ze166. rewrite soff_lit_small by lia. lia.
  - rewrite (EVu rhoX (v 166) HagX eq_refl eq_refl), ze166. rewrite soff_lit_small by lia. lia.
Qed.
Lemma cellsInD : ltac2:(tb__ "0|1|
S7bS8S14S32S7eR4A1ScbS11S11S8S14A2M0S32A2S12G0S32S12S8S14R4R3A4R2A4S87R5A1A3S1S1dZ0R5A2S1S1dS1cR5S27R4A1A2S21S82R6A1S80R6A1A2A2S160R4U8A2A2A2F_;F_;Fe;Fw;Foff;Fd;").
Proof using rho.
  intros d off w e HDS Hin. destruct d; cbn in Hin;
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-|]); try (destruct Hin; fail); unfold dlo, dhi; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.
Lemma semD : ltac2:(tb__ "0|1|
S7bS8S14S32S7eR4A1ScbS11S11S8S14A2M0S32A2S12G0S32S12S8S14R4R3A4R2A4S87R5A1A3S1S0ScSe8Sc9R3A2SdA3S0ScSdfR3A1SdA3A2F_;F_;Fe;Fw;Foff;Fd;").
Proof using .
  intros d off w e HDS Hin. destruct d; cbn in Hin, HDS;
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-|]); try (destruct Hin; fail); try (split; reflexivity).
  - destruct HDS as [-> | ->]; split; reflexivity.
  - destruct HDS as [[-> | ->] _]; split; reflexivity.
Qed.
Lemma coverD : ltac2:(tb__ "0|2|
S7bS8S7eR2A1S0SfS9A1S8aR3A1S17S9A1A3S1S1dS80R4A1R3A2S1eR3S82R4A1A2A2S4S8S8S4S14S14S4S32S32S1ScbS11S11S8S14A2M0S32A2S12G0S32S12S8S14R3R2A4R1A4S87R8A1A3S1S1dR3S21R7S80R8A1A2M1A2S1eG1S1cR3S27R2A1A2A2A2A2Le;A2Lw;A2Loff;A2F_;F_;F_;Fx;Fd;").
Proof using rho.
  intros d x HDS Hr Hx. destruct d; try discriminate Hr; unfold dlo, dhi in Hx; unfold dlo.
  - exists 0, 1%nat, (SLit 0). split; [left; reflexivity | cbn [Z.of_nat]; lia].
  - exists 0, 8%nat, e. split; [left; reflexivity | cbn [Z.of_nat]; lia].
  - exists 0, 8%nat, (v 165). split; [left; reflexivity | cbn [Z.of_nat]; lia].
  - exists 0, 8%nat, e. split; [left; reflexivity | cbn [Z.of_nat]; lia].
  - exists 0, 8%nat, (v 167). split; [left; reflexivity | cbn [Z.of_nat]; lia].
  - exists 0, 4%nat, (SLit 0). split; [left; reflexivity | cbn [Z.of_nat]; lia].
  - destruct (Z_lt_dec x (zg1 + 28)).
    + exists 0, 4%nat, (v 173). split; [left; reflexivity | cbn [Z.of_nat]; lia].
    + exists 4, 4%nat, (v 174). split; [right; left; reflexivity | cbn [Z.of_nat]; lia].
Qed.
Lemma dunkD : ltac2:(tb__ "0|0|
S7bS7eR1A1S0SfS9A1S8aR2A1S17S9A1A3S0S55S54S7fR3A1A1S44A3F_;F_;Fd;").
Proof using . intros d _ Hr. destruct d; try discriminate Hr; reflexivity. Qed.
Lemma romD : ltac2:(tb__ "0|2|
S7bS9S8S7eR3A1S0SfS9A1S8aR4A1S15S9R3A2A3S1S1dS80R5A1R3A2S1eR3S82R5A1A2A2S1S0ScS5dS2dS7aQ40R4A2M0A2SdA3S0SfS78Q8A1M1A1Vm0;G0A1S17G1A1A3A2F_;F_;F_;Fx;Fl;Fd;").
Proof using Hm0_ctz Hm0_sct rho.
  intros d l x _ Hr Hx. destruct d; try discriminate Hr; unfold dlo, dhi in Hx.
  - split; [replace x with (0x108cc + (x - 0x108cc)) by lia; apply U.Mal_mslow__G1.Mal_mslow_I0.ro_tables; lia
          | replace x with (0x108ec + (x - 0x108ec)) by lia; apply Hm0_sct; lia].
  - split; [replace x with (0x108cc + (x - 0x108cc)) by lia; apply U.Mal_mslow__G1.Mal_mslow_I0.ro_tables; lia
          | replace x with (0x108cc + (x - 0x108cc)) by lia; apply Hm0_ctz; lia].
Qed.

Lemma Hent_hold : ltac2:(tb__ "0|0|
S7bScbS7bR1S83Sa6Vs;Vn;A2A1A3S5S40S2dVrhoW;S11eVms;Vm0;A2S7fR3A1A4F_;F_;Fd;").
Proof using Erd Ewok HCS HLok HMI HW Hm0_ctz Hm0_sct Hrom Hsp Hsp_high.
  intros d Hd _. apply (proj1 (Forall_forall _ _) N_hold (obj_of d)).
  change (N_all : list sobj) with (tl (POBJS MR_P pv)). rewrite <- dsF_objs. apply in_map. exact Hd.
Qed.

Hypothesis Htp : tp_ok C_U rho.
Hypothesis Hinit : ltac2:(tb__ "0|1|
S0ScSddVs;A1S16A3S1S159S2dS12aVL;Vrho;A4S0S10S11Sd1Sd2A2M0A1Sd4Vs;A1S13G0A1A3A2F_;").
Hypothesis Erm : ltac2:(tb__ "0|0|
S0S78Q40A1SfS78Q8A1A1F_;S3eVrho;A1Vm0;A3").

Definition CALLX (pv0 : pvar) : sstate := ltac2:(tb__ "0|1|
S66S60S6eSb6A1M0A1S6aG0A1S5fG0A1S5eG0A1S61G0A1SeS35S76SceS35S71Sb6Vpv0;A2A2A3S41G0A1S42G0A1S43G0A1A9").
Lemma swf_CALLX : ltac2:(tb__ "0|0|
S6bS0ScS47S88R1A1A1SdA3Fpv0;"). Proof using . by_pv. Qed.
Lemma swf_CALL : ltac2:(tb__ "0|0|
S0ScS47S6eSb6A1A1SdA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma CALL_norl1 : ltac2:(tb__ "0|0|
S0ScS164P1S6eSb6A1A2S16A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma CALL_norl4 : ltac2:(tb__ "0|0|
S0ScS164P4S6eSb6A1A2S16A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma CALLX_match : ltac2:(tb__ "0|0|
S6bS0ScS118SceS35S71Sb6R1A2A2S112S7bS35S7fS83R1A1A4A2SdA3Fpv0;"). Proof using . by_pv. Qed.

Definition NF0 : list sprop := ltac2:(tb__ "0|0|
SeS34S56S37Pa8A1S33Z2fA1A2SeS34S56S33Z1000A1S37PaA1A2S13S34A1A3A3").

Definition QC : assn := ltac2:(tb__ "0|0|
Se6S4S36S36Sd0S2dS169VKc;Vs;VL;Vn;Vrho;A5S6eSb6A1R1R2A5LrhoC;A2Lw;").

Lemma exist_pv : ltac2:(tb__ "0|0|
S4S6bS6bS0S6bSa6Vs;Vn;A2R1A3Lp;A2"). Proof using . eexists. reflexivity. Qed.

Section Leaf.
Variables (rhoF : valuation) (trF : list event) (msF : machine_state) (mdF : Model).
Hypothesis HagF : agrees rhoW rhoF.
Hypothesis HsmF : ltac2:(tb__ "0|0|
S4fS2dVrhoF;S88Sa6Vs;Vn;A2A1S12S10S147A1S145VtrF;S146VmsF;VmdF;A2A4A4").

Definition mR : word -> option byte := ltac2:(tb__ "0|0|
S173VrhoF;Sb4Vs;Vn;A2VmsF;A3").

Lemma mR_eq : ltac2:(tb__ "0|0|
S0S78Q40A1SfS78Q8A1A1F_;S117S7bS7fVmsF;VrhoF;S83Sa6Vs;Vn;A2A1A5S14dA3").
Proof using . unfold WalkReab.m', WalkReab.NREL, mR. rewrite dsF_objs. reflexivity. Qed.

Lemma HroF : ro_clear segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmF)))))). Qed.

Lemma view_same : ltac2:(tb__ "0|1|
S8S1S1dZ0R1A2S1eR1S1fZ2Z40A2A2A2S1S0SfS78Q8A1A1SedS2dS14dS7aQ40R2A2M0A3SedS2dVm0;G0A3A3S0ScSeeS2dS14dG0A3SeeS2dVm0;G0A3A3A2F_;Fa;").
Proof using Erd Ewok HCS HLok HMI HW HagF Hdepth Hm0_ctz Hm0_sct Hrom HsmF Hsp Hsp_high.
  intros a Ha.
  destruct (WalkReab.in_ranges_decD pd dlo dhi (dsF pv) a) as [(d & Hd & R)|OUT].
  - rewrite <- mR_eq.
    exact (WalkReab.od_byte_same segsU rhoW zr1 zl1 Hzr Hzl pd obj_of dlo dhi dcells drom DS m0
             rngD range64D cellsD cellsInD semD coverD dunkD romD ms Hrom trF mdF msF rhoF HagF
             (CALLX pv) O_stk_frame _ (dsF pv) eq_refl (CALLX_match pv) HsmF HdsF (fun _ => True) Hent_hold d a Hd I R).
  - assert (E : mR (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)).
    { rewrite <- mR_eq. apply (WalkReab.m'_out rhoW pd obj_of dlo dhi DS m0 eq_refl rngD msF rhoF HagF (dsF pv) HdsF a Ha).
      intros d Hd R. apply OUT. exists d. auto. }
    unfold Glue.rd_of, Glue.wok_of. rewrite E. split; reflexivity.
Qed.

Lemma kept_ctx : ltac2:(tb__ "0|1|
S8S152S2dS12aS14bVs;VL;A2R1A4S1S1dZ5a3d0M0R2A2S1eR2S1cG0Z3a0A2A2A2S6F_;F_;Fa;").
Proof using HMI Hsp.
  intros a [A | [(b & nb & Hin & Hr) | (_ & NC & _)]] Ha.
  - top_ranges. lia.
  - pose proof (minv_block_geom C_U (mkMA s L) rd0 wok0 vm b nb HMI Hin) as (_ & _ & _ & _ & G).
    cbn [mc_img_lo mc_img_hi C_U] in G. unfold UNIT, IB in G. lia.
  - apply NC. cbn [mc_ctx C_U]. unfold CTX_SIZE. lia.
Qed.
Lemma kept_off_image : ltac2:(tb__ "0|1|
S8S1S1dZ0R1A2S1eR1S1fZ2Z40A2A2A2S3S1dS1cR2Z1A2Z10000A2S1dZ5b000R2A2A2S0SfS78Q8A1A1S14dS7aQ40R3A2M0A1Vm0;G0A1A3F_;F_;Fa;").
Proof using Erd Ewok HCS HLok HMI HW HagF Hdepth Hm0_ctz Hm0_sct Hrom HsmF Hsp Hsp_high.
  intros a Ha Hoff. pose proof (proj1 (view_same a Ha)) as V.
  rewrite !rd_of_off_image in V by (rewrite u64 by lia; exact Hoff). exact V.
Qed.
Lemma kept_same : ltac2:(tb__ "0|1|
S14eS2dS12aS14bVs;VL;A2M0G0Vm0;S14dA6").
Proof using Erd Ewok HCS HLok HMI HW HagF Hdepth Hm0_ctz Hm0_sct Hrom HsmF Hsp Hsp_high.
  intros a Ha Hc _ He Hs. pose proof R_all as RA.
  destruct (WalkReab.in_ranges_decD pd dlo dhi (dsF pv) a) as [(d & Hd & R)|OUT].
  2:{ rewrite <- mR_eq. apply (WalkReab.m'_out rhoW pd obj_of dlo dhi DS m0 eq_refl rngD msF rhoF HagF (dsF pv) HdsF a Ha).
      intros d Hd R. apply OUT. exists d. auto. }
  pose proof pv_cases as PC. pose proof Hd as Hd0. pose proof HroF as ROF.
  destruct (exist_pv) as [p Epv]. rewrite Epv in Hd, PC. unfold dsF in Hd.
  destruct p; cbn in Hd, PC;
    repeat (destruct Hd as [<-|Hd]); try (destruct Hd; fail); unfold dlo, dhi in R.
  all: first
    [
      exfalso; apply Hs; left; cbn [mc_libc C_U]; lia
    |
      rewrite <- mR_eq;
      rewrite (WalkReab.m'_in rhoW pd obj_of dlo dhi DS rngD msF rhoF HagF _ HdsF _ a Hd0 ltac:(unfold dlo, dhi; lia) Ha);
      rewrite (ROF (Z_to_bv 64 a) ltac:(replace a with (0x108cc + (a - 0x108cc)) by lia; apply U.Mal_mslow__G1.Mal_mslow_I0.ro_tables; lia));
      symmetry; first [ replace a with (0x108ec + (a - 0x108ec)) by lia; apply Hm0_sct; lia
                      | replace a with (0x108cc + (a - 0x108cc)) by lia; apply Hm0_ctz; lia ]
    |
      exfalso; apply (kept_ctx a Hc); try (change (j1 : Z) with (sc0 + 1) in R); lia
    |
      apply (kept_off_image a Ha);
      first [ pose proof (zg0_range ltac:(tauto)); lia
            | pose proof (zg1_range ltac:(tauto) ltac:(tauto)); lia ] ].
Qed.
End Leaf.

Lemma leaf_call : ltac2:(tb__ "0|5|
S6bS0S6bSa6Vs;Vn;A2R1A3S46S10S11S9S32A2M0A1S10S11S32S32A2A1M1S36Se6S0ScSe9S9S1aScaS112G0S9S18S9S32A2R5A4M2R1A2A1Lu;R5A2SdA3S0ScSccS9S9S1aSc9R1A1A1Lj;G2A3SdA3S0SfS11G1S10S34A1M3A2M4A1S11cR7S88R9A1A2S15G4S12G1G3R5S9aA4A2A3Sc8VrhoW;R5A2Sc8VrhoW;S116R6R8A2A2S11dS116R7R9A2R8A2F_;ScfS2dS7cRaR7R6A5S81R7A1F_;F_;F_;F_;F_;F_;Fw;Frho';Fd;Fsets;FLf;F_;Fpv0;").
Proof using Erd Erm Ewok HCS HLok HMI HP12 HW Hdepth Hinit Hm0_ctz Hm0_sct Hrom Hsp Hsp_high Htp.
  intros pv0 Epv Lf sets d rho' w Hvars Hb Hsd Hag Hd HSP. subst pv0.
  pose proof (WalkReab.agrees_setp rhoW rho' sets Hag Hb) as HagS.
  set (rhoS := setp rho' sets) in *. pose proof R_all as RA.

  assert (HSPX : SymSoundR.SP segsU K (CALLX pv) rhoS w).
  { apply (WalkReab.relinkp segsU K rho' Lf (CALLX pv) w sets d NF0 Hvars (swf_CALLX pv) Hsd (Hd HagS)); [|exact HSP].
    constructor; [|constructor; [|constructor]]; hfact HagS; zev; [lia|].
    rewrite zr1_10. rewrite (Z.mod_small _ _ (urange _)). exact (proj1 Hsp). }
  destruct w as [trw [msw mdw]]. destruct HSPX as [HsmX HKX]. cbn [w_tr w_cfg cfg_model] in HKX. destruct HKX as [HKc Hvm].

  pose proof (smatch_release_tail segsU rhoS (CALLX pv) trw msw mdw O_stk_frame N_all NX HsmX eq_refl swf_CALL) as HsmR.
  cbn zeta in HsmR. change (smatch segsU (mkVal (rw rhoS) (rl rhoS) (mR rhoS msw)) (CALL MR_P) (trw, mkCfg msw mdw)) in HsmR.

  set (rhoC := rho_set_rl (rho_set_rl (mkVal (rw rhoS) (rl rhoS) (mR rhoS msw)) 4 (rl rho 4)) 1 (rl rho 1)).
  assert (HsmC : smatch segsU rhoC (CALL MR_P) (trw, mkCfg msw mdw)).
  { unfold rhoC. apply SymCall.smatch_set_rl; [apply CALL_norl1|]. apply SymCall.smatch_set_rl; [apply CALL_norl4|]. exact HsmR. }
  exists rhoC. split; [exact HsmC|]. cbn [w_tr w_cfg cfg_model].

  assert (RW : forall j, (j < 100)%positive -> rw rhoC j = rw rho j).
  { intros j Hj. change (rw rhoC j) with (rw rhoS j). rewrite (rw_agrees rhoS j HagS) by (unfold below200; apply Pos.ltb_lt; lia). apply rw1_low. exact Hj. }
  assert (RL : forall l, rl rhoC l = rl rho l).
  { intros l. unfold rhoC, rho_set_rl. cbn [rl]. destruct (l =? 1)%positive eqn:E1; [apply Pos.eqb_eq in E1; subst l; reflexivity|].
    destruct (l =? 4)%positive eqn:E4; [apply Pos.eqb_eq in E4; subst l; reflexivity|].
    unfold rhoS. rewrite WalkReab.setp_rl. rewrite (proj1 (proj2 Hag) l). cbn [rhoW rho1 rl U.Mal_mslow__G1.Mal_mslow_I0.rl1]. unfold U.Mal_mslow__G1.Mal_mslow_I0.rl1. rewrite E1, E4. reflexivity. }
  assert (RM : rm rhoC = mR rhoS msw) by reflexivity.
  pose proof (view_same rhoS trw msw mdw HagS HsmX) as VIEW.
  assert (VIEWw : forall a : word, Glue.rd_of segsU (mR rhoS msw) a = Glue.rd_of segsU m0 a).
  { intros a. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (proj1 (VIEW _ (urange a))). }
  unfold JC, U.Mal_mslow__G2.Mal_mslow_K.agC. cbn zeta.
  split.
  {
    unfold MInvR. rewrite RM, Hvm.
    pose proof (proj1 (MInv_MInvI C_U (mkMA s L) rd0 wok0 vm) HMI) as [MI RO].
    apply (proj2 (MInv_MInvI C_U (mkMA s L) _ _ vm)). split; [|exact RO]. unfold MInvI.
    apply (minvG_frame C_U [] None U0 s L rd0 (Contract.rd_of segsU (mR rhoS msw)) wok0 (Contract.wok_of segsU (mR rhoS msw)) vm (fun _ => False) MI (Zones2.xraw_nil s));
      [| intros a [] | intros a; right; intros [] | intros a [] | intros a [] | intros a [] | intros a []].
    intros a Ha _. rewrite Erd, Ewok. exact (VIEW a Ha). }
  split; [exact HKc|].
  split; [unfold tp_ok; rewrite (RW 24%positive) by lia; exact Htp|].
  split.
  { intros Hf. destruct (Hinit Hf) as [HA HM]. split; [|exact HM].
    apply (auxv_init_rdext L rho rhoC HA); [|apply RW; lia].
    intros a. rewrite RM, Erm. apply VIEWw. }
  split; [rewrite (RW 12%positive) by lia; exact HP12|].
  split.
  { change (rw rhoC 168%positive) with (rw rhoS 168%positive). rewrite (rw_agrees rhoS 168%positive HagS eq_refl).
    cbn [U.Mal_mslow__G1.Mal_mslow_I0.rw1 Pos.eqb]. rewrite u64 by lia. reflexivity. }
  split.
  { split; [exact RW|]. split; [exact RL|].
    rewrite RM, Erm. exact (kept_same rhoS trw msw mdw HagS HsmX). }

  unfold top_high, V_DEPTH. cbn [ma_L]. rewrite (RW 10%positive), (RW 15%positive) by lia. exact Hsp_high.
Qed.

Definition LS (l : list leaf) (i : nat) : sstate := ltac2:(tb__ "0|0|
Sc6Vl;Vi;S111A3").

Local Ltac leaf_list := match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list leaf) l) end.
Lemma L6_PA : ltac2:(tb__ "0|1|
S0S10S9eA1Sf9S70A1M0SeS9eS9fS7dG0U0A2Sa0A2S13S9eA1A3A3"). Proof using . leaf_list. Qed.
Lemma L6_PB : ltac2:(tb__ "0|1|
S6bS2S0S6bR1S70A3A1S0S10S9eA1Sf9R2A1M0SeS9eS9fS7dG0U0A2Sa0A2SeS9eS9fS7dG0U1A2Sa0A2SeS9eS9fS7dG0U2A2Sa0A2SeS9eS9fS7dG0U3A2Sa0A2SeS9eS9fS7dG0U4A2Sa0A2S13S9eA1A3A3A3A3A3A3F_;Fpv0;").
Proof using . intros [| | |] H; [exfalso; exact (H eq_refl) | | |]; leaf_list. Qed.
Lemma L6o_PB2 : ltac2:(tb__ "0|1|
S0S10S9eA1S108S6cA1M0SeS9eS9fS7dG0U0A2Sa0A2SeS9eS9fS7dG0U1A2Sa0A2S13S9eA1A3A3A3"). Proof using . leaf_list. Qed.
Lemma L6o_PB3 : ltac2:(tb__ "0|1|
S0S10S9eA1S108S6dA1M0SeS9eS9fS7dG0U0A2Sa0A2SeS9eS9fS7dG0U1A2Sa2A2SeS9eS9fS7dG0U2A2Sa0A2SeS9eS9fS7dG0U3A2Sa0A2SeS9eS9fS7dG0U4A2Sa0A2SeS9eS9fS7dG0U5A2Sa0A2SeS9eS9fS7dG0U6A2Sa0A2S13S9eA1A3A3A3A3A3A3A3A3"). Proof using . leaf_list. Qed.

Definition D5oc : list (sv * sv) * list sprop := Eval vm_compute in D5o PB2.
Lemma sd_5o : ltac2:(tb__ "0|1|
S6bS3S0S6bR1S6cA3S0S6bR1S6dA3A2S0SfS11S10S11S32S32A2A1S10S34A1A2M0A1S11cS7dSf9R2A1U3A2S102R2A1A2S15G0S97A2A3F_;Fpv0;").
Proof using . intros pv0 [-> | ->]; vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some D5oc)). Qed.
Lemma swf_C5o : ltac2:(tb__ "0|0|
S6bS3S0S6bR1S6cA3S0S6bR1S6dA3A2S0ScS47S102R2A1A1SdA3F_;Fpv0;"). Proof using . intros pv0 [-> | ->]; vm_compute; reflexivity. Qed.
Lemma vars_L6q : ltac2:(tb__ "0|1|
S6bS3S0S6bR1S6cA3S0S6bR1S6dA3A2S0ScSe9S9S1aScaS112S11S9S32A2M0S9S18S9S32A2S13G0A1A4R1A2A1Lu;S7dSf9R2A1U3A2A2SdA3F_;Fpv0;").
Proof using . intros pv0 [-> | ->]; vm_compute; reflexivity. Qed.
Lemma L6q_even : ltac2:(tb__ "0|0|
S6bS3S0S6bR1S6cA3S0S6bR1S6dA3A2ScbS34S53S38S121S3dS123S37P96A1S33Z1A1A3S33Z0A1A3A1S41S7dSf9R2A1U3A2A1A3F_;Fpv0;").
Proof using . intros pv0 [-> | ->]; apply in_facts_b; vm_compute; reflexivity. Qed.
Lemma link_5o : ltac2:(tb__ "0|1|
S3S0S6bSa6Vs;Vn;A2M0S6cA3S0S6bG0S6dA3A2S36Se6Sc8VrhoW;R2A2ScfS2dS7cS7dSf9G0A1U3A2R3R2A5S115S2dVrhoW;S7cS102G0A1R3A5F_;F_;Fw;Frho';F_;").
Proof using HCS HLok HMI HW m0 rho.
  intros Hpv rho' w Hag HSP. pose proof R_all as R.
  pose proof (zf_even (leaf_fact rho' _ w _ Hag HSP (L6q_even pv Hpv) eq_refl eq_refl)) as Hev.
  eapply (linkp segsU rhoW K (LS (L6 pv) 3) (C5o pv) [] _ _ rho' w); [apply (vars_L6q pv Hpv) | reflexivity | apply (swf_C5o pv Hpv) | apply (sd_5o pv Hpv) | exact Hag | | exact HSP].
  intros HagS _. cbn [D5oc fst snd]. split; [|constructor].
  unfold diffs_ok. apply Forall_cons; [cbn [fst snd]|apply Forall_nil]. sem_pair HagS.
  zev. rewrite (Z.mod_small sc0) by lia. rewrite (lor1_even sc0) by (lia || exact Hev). change (j1 : Z) with (sc0 + 1). reflexivity.
Qed.

Lemma crb_intro : ltac2:(tb__ "0|1|
S1S1dZ4Sa7Vn;A1M0A2S1dG0Z1fA2A2S2S0S8G0Z6A3A1S0ScS25G0A1SdA3S0S8Sb1Vs;Vn;A2Z0A3S0ScSa8Vs;Vn;A2SdA3F_;F_;F_;F_;").
Proof using Hsp.
  intros H1 H2 H3 H4. unfold U.Mal_mslow__G1.Mal_mslow_I0.crb.
  replace (4 <=? sc0) with true by (symmetry; apply Z.leb_le; lia).
  replace (sc0 <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (sc0 =? 6) with false by (symmetry; apply Z.eqb_neq; lia).
  change (U.Mal_mslow__G1.Mal_mslow_I0.u0 s n) with (u0 : Z). rewrite H3, H4. reflexivity.
Qed.
Lemma cl_B2x : ltac2:(tb__ "0|5|
S0SfSd1A1M0SaeVs;Vn;A2S17Sd1A1M1A3S0ScSa8Vs;Vn;A2SdA3S0G0SafVs;Vn;A2G1A3S1S1dS1cSaaVs;Vn;A2Z3A2M2ZcM3A2S0S8SadVs;Vn;A2M4SabVn;A1A3F_;S1eG3G2A2S0S8G4Sa7Vn;A1A3F_;A2F_;F_;F_;").
Proof using HW rho. intros Hg Hc Hg1. pose proof (cl_B Hg Hc) as X. unfold bonus in X. rewrite Hg1 in X. exact X. Qed.
Lemma cl_B3x : ltac2:(tb__ "0|b|
S0SfSd1A1M0SaeVs;Vn;A2S17Sd1A1M1A3S0ScSa8Vs;Vn;A2SdA3S2S0G0SafVs;Vn;A2G1A3A1S1S3S2S0S8SacVs;Vn;A2Z0M2A3M3A1S2S0S8Sb0Vs;Vn;A2G2A3M4A1A2S1S1dSaaVs;Vn;A2M5ZcM6A2S0S8SadVs;Vn;A2M7SabVn;A1A3M8F_;S1eG6G5A2S0S8G7Sa7Vn;A1A3M9F_;A2F_;G3G4S1S1dS1cG5Z3A2MaG6A2G8F_;S1eG6GaA2G9F_;A2F_;F_;A2F_;F_;F_;").
Proof using HW rho.
  intros Hg Hc Hg1. pose proof (cl_B Hg Hc) as X. unfold bonus in X.
  destruct (U.Mal_mslow__G1.Mal_mslow_I0.g1o s n) as [g1|]; [|exfalso; exact (Hg1 eq_refl)].
  split.
  - intros Hnz. replace ((av1 =? 0) && (fr1 =? 0))%bool with false in X; [rewrite Z.add_0_r in X; exact X|].
    symmetry. destruct Hnz as [Hnz|Hnz]; apply Z.eqb_neq in Hnz; rewrite Hnz; [reflexivity | apply Bool.andb_false_r].
  - intros Ha Hf. rewrite Ha, Hf in X. exact X.
Qed.

Local Ltac zfact zf Hag HSP :=
  lazymatch type of zf with
  | (~ zholds _ _ ?P -> _) => pose proof (zf (leaf_fact _ _ _ (SPNot P) Hag HSP ltac:(apply in_facts_b; vm_compute; reflexivity) eq_refl eq_refl))
  | (zholds _ _ ?P -> _) => pose proof (zf (leaf_fact _ _ _ P Hag HSP ltac:(apply in_facts_b; vm_compute; reflexivity) eq_refl eq_refl))
  end.

Local Ltac call_leaf Epv Hag HSP ztac :=
  lazymatch type of HSP with SymSoundR.SP _ _ ?Lf ?r _ =>
  lazymatch type of Epv with _ = ?pv0 =>
    let dv := eval vm_compute in (state_diff Lf (CALLX pv0)) in
    lazymatch dv with Some (?d, _) =>
      let sets := eval vm_compute in (scratch_of d) in
      apply (leaf_call pv0 Epv Lf sets d r _ ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(vm_compute; reflexivity) Hag);
      [ intros HagS; ztac; unfold diffs_ok;
        repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil];
        first [scratch_pair Hag HagS | sem_pair HagS; zev; lia]
      | exact HSP ]
    end end end.

Lemma tail_A : ltac2:(tb__ "0|1|
S0S6bSa6Vs;Vn;A2M0S70A3S36Sc8VrhoW;R1A2VTR;Z0ScfS2dS7cSf7G0A1R2A4S81A3F_;Fr5;F_;").
Proof using Erd Erm Ewok HCS HLok HMI HP12 HW Hdepth Hinit Hm0_ctz Hm0_sct Hrom Hsp Hsp_high Htp RR.
  intros E r5 Hag5. pose proof pv_cases as PC. rewrite E in PC. cbn in PC. pose proof (cl_A PC) as Hcl. pose proof R_all as RA.
  rewrite E. apply (seg_run 300 (C5 PA) (L6 PA) QC r5 (proj1 (lnx_C5 PA)) (proj2 (lnx_C5 PA)) (run6 PA) Hag5).
  intros Lf rho' Hin Hag. rewrite L6_PA in Hin. destruct Hin as [<-|[]]; cbn [lf_state].
  apply seg_leaf. intros w HSP. call_leaf E Hag HSP idtac.
Qed.

Lemma tail_B1 : ltac2:(tb__ "0|1|
S0S6bSa6Vs;Vn;A2M0S77A3S36Sc8VrhoW;R1A2VTR;Z0ScfS2dS7cSf7G0A1R2A4S81A3F_;Fr5;F_;").
Proof using Erd Erm Ewok HCS HLok HMI HP12 HW Hdepth Hinit Hm0_ctz Hm0_sct Hrom Hsp Hsp_high Htp RR.
  intros E r5 Hag5. pose proof pv_cases as PC. rewrite E in PC. cbn in PC. destruct PC as [G0 CR]. pose proof (cl_B1 CR) as Hcl. pose proof R_all as RA.
  rewrite E. apply (seg_run 300 (C5 PB1) (L6 PB1) QC r5 (proj1 (lnx_C5 PB1)) (proj2 (lnx_C5 PB1)) (run6 PB1) Hag5).
  intros Lf rho' Hin Hag. rewrite (L6_PB PB1 ltac:(discriminate)) in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [lf_state].
  - apply seg_leaf. intros w HSP. call_leaf E Hag HSP ltac:(zfact zf_sc6 Hag HSP).
  - apply seg_leaf. intros w HSP. call_leaf E Hag HSP idtac.
  - apply seg_leaf. intros w HSP. call_leaf E Hag HSP idtac.
  - apply seg_dead. intros w HSP.
    zfact zf_u0 Hag HSP. zfact zf_even Hag HSP. zfact zf_nbig Hag HSP. zfact zf_nsc6 Hag HSP.
    pose proof (crb_intro ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)) as X. rewrite CR in X. discriminate X.
  - apply seg_leaf. intros w HSP. call_leaf E Hag HSP idtac.
Qed.

Lemma dead_L6_0124 : ltac2:(tb__ "0|3|
S0ScSa8Vs;Vn;A2SdA3S36Se6S46Sc8VrhoW;R3A2ScfS2dS7cR2R4R3A5S3ScbS34S38S122S37P96A1M0S33Z6A1A3S41R3A1M1A3S3ScbS34S38S120S33Z1bA1S3dS11fG0S33N4A1A3A3G1A3S3ScbS34S38S121S3dS123G0S33Z1A1A3S33Z0A1M2A3G1A3ScbS34S53S38S122S37Pa5A1G2A3A1G1A3A2A2A2S6F_;F_;F_;FLf;Fw;Frho';F_;").
Proof using HCS HLok HMI HW Hsp m0.
  intros CR rho' w Lf Hag HSP Hin. pose proof (crb_true CR) as (R1 & R2 & R3 & R4).
  destruct Hin as [H|[H|[H|H]]]; pose proof (leaf_fact rho' Lf w _ Hag HSP H eq_refl eq_refl) as F.
  - apply zf_sc6 in F. lia.
  - apply zf_big in F. lia.
  - apply zf_odd in F. rewrite F in R3. discriminate R3.
  - apply zf_nu0 in F. exact (F R4).
Qed.
Local Ltac dead0124 CR Hag HSP :=
  apply (dead_L6_0124 CR _ _ _ Hag HSP);
  first [ left; apply in_facts_b; vm_compute; reflexivity
        | right; left; apply in_facts_b; vm_compute; reflexivity
        | right; right; left; apply in_facts_b; vm_compute; reflexivity
        | right; right; right; apply in_facts_b; vm_compute; reflexivity ].

Lemma tail_B2 : ltac2:(tb__ "0|1|
S0S6bSa6Vs;Vn;A2M0S6cA3S36Sc8VrhoW;R1A2VTR;Z0ScfS2dS7cSf7G0A1R2A4S81A3F_;Fr5;F_;").
Proof using Erd Erm Ewok HCS HLok HMI HP12 HW Hdepth Hinit Hm0_ctz Hm0_sct Hrom Hsp Hsp_high Htp RR.
  intros E r5 Hag5. pose proof pv_cases as PC. rewrite E in PC. cbn in PC. destruct PC as (G0 & CR & G1).
  pose proof (cl_B2x G0 CR G1) as [HclA HclB]. pose proof R_all as RA.
  pose proof (link_5o ltac:(rewrite E; left; reflexivity)) as L5o. rewrite E in L5o.
  rewrite E. eapply seq0.
  { apply (seg_run 300 (C5 PB2) (L6 PB2) (POST (C5o PB2)) r5 (proj1 (lnx_C5 PB2)) (proj2 (lnx_C5 PB2)) (run6 PB2) Hag5).
    intros Lf rho' Hin Hag. rewrite (L6_PB PB2 ltac:(discriminate)) in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [lf_state];
      [ apply seg_dead; intros w HSP; dead0124 CR Hag HSP
      | apply seg_dead; intros w HSP; dead0124 CR Hag HSP
      | apply seg_dead; intros w HSP; dead0124 CR Hag HSP
      | apply seg_leaf; intros w HSP; exact (L5o rho' w Hag HSP)
      | apply seg_dead; intros w HSP; dead0124 CR Hag HSP ]. }
  apply from_POST. intros r6 Hag6.
  apply (seg_run 300 (C5o PB2) (L6o PB2) QC r6 (proj1 (lnx_C5o PB2)) (proj2 (lnx_C5o PB2)) (run6o PB2 (or_introl eq_refl)) Hag6).
  intros Lf rho' Hin Hag. rewrite L6o_PB2 in Hin.
  destruct Hin as [<-|[<-|[]]]; cbn [lf_state].
  - apply seg_leaf. intros w HSP. call_leaf E Hag HSP ltac:(zfact zf_u3_13 Hag HSP).
  - apply seg_leaf. intros w HSP. call_leaf E Hag HSP ltac:(zfact zf_nu3_13 Hag HSP).
Qed.

Lemma tail_B3 : ltac2:(tb__ "0|1|
S0S6bSa6Vs;Vn;A2M0S6dA3S36Sc8VrhoW;R1A2VTR;Z0ScfS2dS7cSf7G0A1R2A4S81A3F_;Fr5;F_;").
Proof using Erd Erm Ewok HCS HLok HMI HP12 HW Hdepth Hinit Hm0_ctz Hm0_sct Hrom Hsp Hsp_high Htp RR.
  intros E r5 Hag5. pose proof pv_cases as PC. rewrite E in PC. cbn in PC. destruct PC as (G0 & CR & G1).
  pose proof (cl_B3x G0 CR G1) as [HclA HclB]. pose proof R_all as RA.
  pose proof (link_5o ltac:(rewrite E; right; reflexivity)) as L5o. rewrite E in L5o.
  rewrite E. eapply seq0.
  { apply (seg_run 300 (C5 PB3) (L6 PB3) (POST (C5o PB3)) r5 (proj1 (lnx_C5 PB3)) (proj2 (lnx_C5 PB3)) (run6 PB3) Hag5).
    intros Lf rho' Hin Hag. rewrite (L6_PB PB3 ltac:(discriminate)) in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [lf_state];
      [ apply seg_dead; intros w HSP; dead0124 CR Hag HSP
      | apply seg_dead; intros w HSP; dead0124 CR Hag HSP
      | apply seg_dead; intros w HSP; dead0124 CR Hag HSP
      | apply seg_leaf; intros w HSP; exact (L5o rho' w Hag HSP)
      | apply seg_dead; intros w HSP; dead0124 CR Hag HSP ]. }
  apply from_POST. intros r6 Hag6.
  apply (seg_run 300 (C5o PB3) (L6o PB3) QC r6 (proj1 (lnx_C5o PB3)) (proj2 (lnx_C5o PB3)) (run6o PB3 (or_intror eq_refl)) Hag6).
  intros Lf rho' Hin Hag. rewrite L6o_PB3 in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [lf_state].
  - apply seg_leaf. intros w HSP. call_leaf E Hag HSP ltac:(zfact zf_u13 Hag HSP; zfact zf_av Hag HSP; pose proof (HclA ltac:(left; assumption)) as [? ?]).
  - apply seg_dead. intros w HSP. zfact zf_u13 Hag HSP. zfact zf_av Hag HSP. eapply (dead_av1 G0 CR G1); eassumption.
  - apply seg_leaf. intros w HSP. call_leaf E Hag HSP ltac:(zfact zf_nu13 Hag HSP; zfact zf_av Hag HSP; pose proof (HclA ltac:(left; assumption)) as [? ?]).
  - apply seg_leaf. intros w HSP. call_leaf E Hag HSP ltac:(zfact zf_u13 Hag HSP; zfact zf_fr Hag HSP; pose proof (HclA ltac:(right; assumption)) as [? ?]).
  - apply seg_leaf. intros w HSP. call_leaf E Hag HSP ltac:(zfact zf_nu13 Hag HSP; zfact zf_fr Hag HSP; pose proof (HclA ltac:(right; assumption)) as [? ?]).
  - apply seg_leaf. intros w HSP. call_leaf E Hag HSP ltac:(zfact zf_u3_13 Hag HSP; zfact zf_nfr Hag HSP; zfact zf_nav Hag HSP; pose proof (HclB ltac:(assumption) ltac:(assumption)) as [? ?]).
  - apply seg_leaf. intros w HSP. call_leaf E Hag HSP ltac:(zfact zf_nu3_13 Hag HSP; zfact zf_nfr Hag HSP; zfact zf_nav Hag HSP; pose proof (HclB ltac:(assumption) ltac:(assumption)) as [? ?]).
Qed.

Theorem chain : ltac2:(tb__ "0|0|
VTR;Z0ScfS2dS7cS6fSb6Sa6Vs;Vn;A2A2VrhoW;A4S81A3").
Proof using Erd Erm Ewok HCS HLok HMI HP12 HW Hdepth Hinit Hm0_ctz Hm0_sct Hrom Hsp Hsp_high Htp RR.
  eapply seq0; [apply pro_C5|]. apply from_POST.
  destruct exist_pv as [p E]. destruct p; [apply (tail_A E) | apply (tail_B1 E) | apply (tail_B2 E) | apply (tail_B3 E)].
Qed.
End InstC.

Theorem prefix_C : ltac2:(tb__ "0|1|
S10S147A1M0S148OF_;F_;OOS8Se7Se7OF_;F_;F_;S15aS2dR4R3R2R1A5Sd3S170S36G0S11aS148S79Q40S3bR4PcA2A2S8S4fS2dR5S151S150A1S12G0S145R4S146R3R2A2A4A4S16dS2dS12aS14bR8R7A2RdR6R5R3A7S168R9R3A2S8Se7S1dZ0R2A2S36R10R4Sd0S2dS169R13ReRdR8RcA5S6eSb6A1R1A4R3A3FrhoC;R10R4S0S11G0S145A2S12G0S145RbS146RaR9A2A4A2R3A3F_;F_;FQ;Fk;F_;F_;F_;Tn;Fmd;Fms;Ftr;Frho0;FL0;Fs0;F_;FTR;FGF;FRF;FKc;").
Proof.
  intros Kc RF GF TR RR s0 L0 rho0 tr ms md n Hsm HJ HC k Q Hk HQ.
  destruct HJ as (HM & HKc & Htp & Hini & Htop). cbn [ma_s ma_L] in Hini.
  pose proof (inst0 s0 L0 n rho0 tr ms md Hsm HM HC eq_refl Htop) as IH.
  pose proof (instantiate s0 L0 n rho0 tr ms md Hsm HM HC eq_refl Htop) as HsmW.
  pose proof (chain s0 L0 n rho0 (ih_W _ _ _ _ _ _ IH) HC (ih_L _ _ _ _ _ _ IH) eq_refl _ _ _ (ih_MI _ _ _ _ _ _ IH)
                (ih_sp _ _ _ _ _ _ IH) (ih_depth _ _ _ _ _ _ IH) (ih_high _ _ _ _ _ _ IH) (rm rho0) eq_refl eq_refl ms
                (ih_rom _ _ _ _ _ _ IH) (ih_sct _ _ _ _ _ _ IH) (ih_ctz _ _ _ _ _ _ IH) Kc RF GF TR RR Htp Hini eq_refl) as CH.
  replace k with (0 + k) by lia.
  apply (trr_seq RR 0 k (eq (tr, mkCfg ms md)) (QC s0 L0 n rho0 Kc) Q).
  - eapply (trr_pre RR); [|exact CH]. intros w <-. split; [exact HsmW|]. split; [exact HKc | reflexivity].
  - unfold QC. apply (trr_ex RR); [exact Hk|]. exact HQ.
Qed.
End Mal_mslow_C.
