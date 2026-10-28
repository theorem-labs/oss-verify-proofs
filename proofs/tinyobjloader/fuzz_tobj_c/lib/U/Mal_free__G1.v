(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "pow"; "lt"; "mul"; "modulo"; "sub"; "eqb"; "min"; "of_nat"; "lor"; "opp"; "div"; "ltb"; "leb"; "to_nat"; "land"; "of_N"; "testbit"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "pair"; "option"; "false"; "list"; "prod"; "true"; "nat"; "app"; "Some"; "orb"; "None"; "andb"; "fst"; "snd"; "length"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sobj"; "cell"; "sv"; "mkObj"; "mkCell"; "SVar"; "DUnknown"; "SAlu"; "SPBranch"; "obj_range"; "rw"; "sstate"; "SAluW"; "obj_holds"; "valuation"; "SExt"; "SPNot"; "mkSS"; "SPUle"; "FcsrFrm0"; "ss_facts"; "eval"; "odefault"; "smatch"; "ss_pc"; "ob_cells"; "ss_regs"; "SPAlign"; "rl"; "rm"; "ss_lenient"; "DRom"; "SLBytes"; "SMd"; "agree_below"; "c_off"; "c_width"; "holds"; "ob_dflt"; "pairwise_disjoint"; "ss_fcsr"; "ss_fregs"; "ss_next"; "ss_objs"; "ss_resv"; "tfact"; "enc_bytes"; "image_byte"; "mkVal"; "ob_hi"; "ob_lo"; "ranges_disjoint"; "rd"; "ro_addr"; "soff"; "swf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick.Inst"; "zr1"; "zl1"; "rho1"; "zP"; "zA"; "zMem"; "n"; "rsv"; "zEnd"; "rvv"; "st"; "S2"; "h16"; "sti"; "sz"; "kv"; "N_all"; "bits"; "zG"; "O_grp"; "h3"; "stl"; "O_area"; "O_ctx"; "O_hdr"; "O_libc"; "O_lock"; "O_meta"; "O_stk"; "sp0"; "D0"; "O_sctab"; "Ea"; "Eg"; "p"; "rw1"; "N_common"; "in_G_after_block"; "rl1"; "rw1_changed"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "segsU"; "NF"; "pre_fregs"; "pre_regs"; "setregs"; "cut_regs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "sx32"; "zholds"; "toS"; "zsupported"; "zalu"; "zle"; "zsublist"; "zl_of"; "zr_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "NFM"; "L_SIZECLASSES"; "gm_mem_sv"; "MASK_PAGE"; "gm_facts"; "GMC"; "GM_A0"; "GM_A1"; "gm_bit"; "gm_facts_common"; "gm_facts_map"; "gm_facts_nomap"; "gm_facts_sized"; "gm_idx"; "gm_last"; "gm_maplen"; "gm_objs"; "gm_sc"; "gm_scsize"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "stop_reason"; "sym_run"; "lf_state"; "lf_reason"; "RsSymJump"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "am_freed"; "ameta"; "frame"; "am_avail"; "am_mem"; "PGSZ"; "am_maplen"; "rg_len"; "am_last"; "poff"; "am_sc"; "fr_n"; "fr_off"; "prid"; "FUser"; "IB"; "fkind"; "fr_kind"; "size_classes"; "znth"; "AREA_HDR"; "META_SIZE"; "padd"; "region"; "METAS_PER_AREA"; "SP"; "UNIT"; "astate"; "st_areas"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_slow"; "fs_seg"; "FS_P"; "FS_U"; "Pre_fs"; "FS_FUEL"; "fs_cuts"; "fs_why"; "fs_leaf_ok"; "fs_okb"; "Posts_fs_P"; "Posts_fs_U"; "Pre_fs0"; "fs_consts"; "fs_ret_call"; "run_fs"; "FSC"; "FS_unmap"; "fs_chkfail"; "fs_ecall"; "fs_ff"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "firstn"; "seq"; "skipn";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast"; "ff_rsv"; "ff_kind"; "FF_P"; "Pre_free_fast"; "ff_end"; "FF_U"; "ff_self"; "Posts_free_fast_P"; "ff_mask"; "FF_FUEL"; "Posts_free_fast_U"; "ff_code"; "ff_cuts"; "ff_nontrivial_free"; "ff_objs_rsv"; "ff_ret"; "ff_cas_loop"; "ff_entry"; "ff_facts_kind"; "ff_facts_rsv"; "ff_lock"; "ff_lockword"; "ff_objs"; "ff_sctab"; "FFC"; "FM"; "FN"; "R0"; "R14"; "R5E"; "R5G"; "ff_S"; "ff_ctx"; "ff_facts_depth"; "ff_facts_quick"; "ff_idx"; "ff_libc"; "ff_objs_common"; "ff_stride"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "existsb"; "incl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "frame_ptr"; "loc"; "LMem"; "image"; "loc_addr"; "MCell"; "group_extent"; "mc_w"; "frames"; "ly_reg"; "mc_loc"; "LCtx"; "VSec"; "ly_sec"; "user_blocks"; "CTX_SIZE"; "CTX_secret"; "VZ"; "hdr_byte3"; "hdr_off16"; "le_byte"; "region_of"; "rsv_code"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "ALU_AND"; "ALU_SUB"; "ALU_SLL"; "BC_GEU"; "ALU_SRL"; "aluop"; "BC_GE"; "BC_LTU"; "M_MUL"; "ALU_OR"; "mulop"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "free_stack"; "topL"; "addr_of"; "size_classes_bytes"; "C_U"; "byteview_of"; "ledger_ok"; "statics_ok"; "vm_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "state_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost"; "quick_case"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast.States"; "ff_end"; "ff_code"; "ff_idx"; "ff_mask"; "ff_self"; "ff_stride"; "ff_facts_depth"; "ff_facts_kind"; "ff_facts_quick"; "ff_facts_rsv"; "ff_objs"; "ff_objs_common"; "ff_objs_rsv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "SPJ"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "J_free_preT"; "Pre_freeI"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "JL_free"; "L_free"; "V_FREE_A1"; "ok_sideK"; "stack_win"; "EC_U"; "rd_of"; "top_high"; "wok_of"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "slot_end"; "reprO"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_s"; "mkMA"; "MInv"; "ma_L"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick"; "lit_of"; "obj_coveredb"; "pg_aligned"; "S1"; "S1r"; "S2"; "covers_lit"; "kv"; "rho1"; "rvv"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "wview"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel"; "frame_facts";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_slow.States"; "fs_after_facts"; "fs_after_regs"; "fs_frame"; "fs_lock"; "fs_errno"; "fs_facts_common"; "fs_facts_why"; "fs_sp"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick.Instantiate"; "InstH"; "f_keep"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_free_fast.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record ff_consts := FFC {
  ff_entry : Z; ff_ret : Z;
  ff_nontrivial_free : Z; ff_lock : Z; ff_cas_loop : Z;
  ff_ctx : Z; ff_libc : Z; ff_lockword : Z; ff_sctab : Z }.
Definition FF_P : ff_consts := FFC 0x20570 0x20738 0x2084c 0x278e0 0x206a4 0x5a3d0 0x5a358 0x5a3c8 0x108ec.
Definition FF_U : ff_consts := ltac2:(tb__ "0|1|
S10eS8Z1fe30Z740M0A2S8Z1fff8G0A2S8Z2010cG0A2S8Z271a0G0A2S8Z1ff64G0A2Z5a3d0Z5a358Z5a3c8Z108ecA9").

Inductive ff_kind := FN | FM.
Inductive ff_rsv := R0 | R14 | R5E | R5G.

Section States.
Variable c : ff_consts.

Definition ff_S : sv := ltac2:(tb__ "0|0|
S3eS20Q10S4fSa2S36S13cS36S140Sa0P87A1S2dZ5A1A3S2dZ7eA1A3Z2A3A3").
Definition ff_stride : sv := SAlu ALU_SLL ff_S (SLit 4).
Definition ff_idx : sv := SAlu ALU_AND (v 130) (SLit 31).

Definition ff_end : sv := ltac2:(tb__ "0|0|
S36S13aS36S13aS36S13aS36S13aSa3S2dN10A1A3S162A3S50S144S162S15fA3A3S2dZcA1A3").
Definition ff_code : sv := SAlu ALU_SRL (v 130) (SLit 5).

Definition ff_objs_common : list sobj := ltac2:(tb__ "0|6|
S25S2fS1bS2fS32S34PaA1Sa0P8bA1S2dZ0M0A1M1S1cS30A1M2S35A5S1cS2fA1M3A3S25S2fSf3S2fU5Sb1Sa6G0G0S116Vc;A1S10dVc;A1A4A1A3S1bS2fS32S2dS8S11aVc;A1Z3A2A1G1S2dZ1M4A1S1bS30S33G1G4G1A3G2A3S35A5S1bS2fS32S2dS10bVc;A1A1G1S2dZ4M5A1S1bS30S33G1G5G1A3G2A3S35A5G3A3A3A3A3").

Definition ff_objs_rsv (r : ff_rsv) : list sobj := ltac2:(tb__ "0|b|
Sf6S21S2fA1Lr;Vr;S1bS2fS32S15dS2dZ0A1M0S2dZ1M1A1M2S1bS30S33G0G1G0A3S1cS30A1A3M3S35A5S1cS2fA1M4A3M5S1bS2fS32S36S13dS15dS15eA3G0G2G3S35A5G5A3S1bS2fS32S15dS2dN5A1M6G2S1bS30S33G6G1G0A3M7S1bS30S33S2dN4A1M8Z4M9S2dZ5A1A3G3A3A3S35A5G4A3S1bS2fS32S15dG6G2S1bS30G7S1bS30S33G8G9Sa0P89A1MaA3G3A3A3S35A5S1bS2fS32S36S13dS15dGaA3G0G2G3S35A5G4A3A3Xf6x4").

Definition ff_objs (k : ff_kind) (r : ff_rsv) : list sobj := ltac2:(tb__ "0|0|
S25S2fS168S25S2fS169Vr;A1S1bS2fS32S2dS10dVc;A1A1S2dZ0A1S2dZ60A1S1cS30A1S4eSa2A1A5S1cS2fA1A3A3A3").

Definition ff_facts_depth : list sprop := ltac2:(tb__ "0|1|
S1bS2eS37S142S2dN30A1Sa0P8bA1M0A3S1bS2eS37S142G0S2dS13SaZ2Z28A2A1A1A3S1cS2eA1A3A3").

Definition ff_facts_kind (k : ff_kind) : list sprop := ltac2:(tb__ "0|0|
S25S2eSf7S21S2eA1Lk;Vk;Sa5Sa7A1S25S2eSa5Sa8A1S1bS2eS3fS37S13bS36S13cSa0P87A1S2dZ1fA1A3S2dZ0A1A3A1S1cS2eA1A3A3Xf7x2S163A3").

Definition ff_facts_rsv (r : ff_rsv) : list sprop := ltac2:(tb__ "0|9|
Sf6S21S2eA1Lr;Vr;S1bS2eS41Sa0P82A1M0S2dZ1fA1A2S1bS2eS37S13fS36S13dS15dSa0PcA1A3M1S2dZ0A1M2A3S1cS2eA1M3A3A3S1bS2eS37S143G0S2dZa0A1A3M4S1bS2eS3fS37S13bS15eG2A3A1S1bS2eS37S13fG1S15eA3G3A3A3A3S1bS2eS3fG4A1M5S1bS2eS37S13bS15eS2dZ5A1M6A3M7S1bS2eS37S13fG1G6A3G3A3A3A3S1bS2eG5S1bS2eG7S1bS2eS41Sa0P89A1M8S2dZffffffffA1A2S1bS2eS37S143S2dZ4A1G8A3S1bS2eS37S13fG1G8A3G3A3A3A3A3A3Xf6x4").

Definition ff_mask : sv := ltac2:(tb__ "0|1|
S36S145S3eS23Q20M0Sa0P85A1A3S3eS23G0Sa0P86A1A3A3").
Definition ff_self : sv := ltac2:(tb__ "0|0|
S3bS13eS2dZ1A1S15fA3").
Definition ff_facts_quick : list sprop := ltac2:(tb__ "0|3|
S1bS2eS37S13bS36S13cS160S161A3S2dZ0A1M0A3S1bS2eS3fS37S13bS3eS23Q20Sa0P86A1A3G0A3A1S1bS2eS3fS37S13bS3bS13aS160S161A3S3bS13aS3bS13eS2dZ2A1Sa0P87A1M1A3S2dZffffffffffffffffA1A3A3A1S1bS2eS41S36S13cS36S140G1S2dZ5A1A3S2dZ7eA1A3S2dZ5eA1A2S1bS2eS4aPaM2Z4A2S1bS2eS41S2dZ1000A1S34G2A1A2S1bS2eS3fS37S13bSa0PcA1G0A3A1S1cS2eA1A3A3A3A3A3A3A3").

Definition Pre_free_fast (k : ff_kind) (r : ff_rsv) : sstate := ltac2:(tb__ "0|0|
S40S107Vc;A1S93S92S42S28S31A1S167Vk;Vr;A2S25S2eS164Vk;A1S25S2eS166Vr;A1S165A3A3Sa1S20A9").

Definition ff_cuts : list Z := ltac2:(tb__ "0|0|
S1bS0S103Vc;A1S1bS0S10aVc;A1S1bS0S106Vc;A1S1cS0A1A3A3A3").
End States.

Definition FF_FUEL : nat := 400%nat.

Definition run_ff (segs : list Segment) (c : ff_consts) (k : ff_kind) (r : ff_rsv) : list leaf := ltac2:(tb__ "0|1|
S1fS21Sb7A1M0A1G0Lx;Sb9Vsegs;SffS102Vc;A1Sf9Vc;Vk;Vr;A3S23A5G0R1Ll;S1cSb7A1X1fx2").

Definition Posts_free_fast_P (k : ff_kind) (r : ff_rsv) : list leaf :=
  Eval vm_compute in
  match k, r with
  | FN, R0 => run_ff segsU FF_P FN R0 | FM, R0 => run_ff segsU FF_P FM R0
  | FN, R14 => run_ff segsU FF_P FN R14 | FN, R5E => run_ff segsU FF_P FN R5E | FN, R5G => run_ff segsU FF_P FN R5G
  | FM, R14 => run_ff segsU FF_P FM R14 | FM, R5E => run_ff segsU FF_P FM R5E | FM, R5G => run_ff segsU FF_P FM R5G
  end.
Definition Posts_free_fast_U (k : ff_kind) (r : ff_rsv) : list leaf :=
  Eval vm_compute in
  match k, r with
  | FN, R0 => run_ff segsU FF_U FN R0 | FM, R0 => run_ff segsU FF_U FM R0
  | FN, R14 => run_ff segsU FF_U FN R14 | FN, R5E => run_ff segsU FF_U FN R5E | FN, R5G => run_ff segsU FF_U FN R5G
  | FM, R14 => run_ff segsU FF_U FM R14 | FM, R5E => run_ff segsU FF_U FM R5E | FM, R5G => run_ff segsU FF_U FM R5G
  end.

Lemma Posts_free_fast_P_shape : ltac2:(tb__ "0|1|
Sf7Sf6S3S21S22S0Sb8A2M0A1Sf1Sb7G0Sb7S1eS0Sb8S47SbaR1A1A1SbbR1A1A4LL;SfdR2R1A2A4S1bG0S1eS0Sb8S105Sf8A1SbcA4S1cG0A1A3A3Fr;Fk;").
Proof. intros [|] [| | |]; vm_compute; reflexivity. Qed.
Lemma Posts_free_fast_U_shape : ltac2:(tb__ "0|1|
Sf7Sf6S3S21S22S0Sb8A2M0A1Sf1Sb7G0Sb7S1eS0Sb8S47SbaR1A1A1SbbR1A1A4LL;S100R2R1A2A4S1bG0S1eS0Sb8S105SfbA1SbcA4S1cG0A1A3A3Fr;Fk;").
Proof. intros [|] [| | |]; vm_compute; reflexivity. Qed.

Lemma run_free_fast_P : ltac2:(tb__ "0|1|
Sf7Sf6S3S1fS21Sb7A1M0A1Sb9S8fSffS102Sf8A1Sf9Sf8R2R1A3S23A5S26G0SfdR2R1A2A2A3Fr;Fk;").
Proof. intros [|] [| | |]; vm_compute; reflexivity. Qed.
Lemma run_free_fast_U : ltac2:(tb__ "0|1|
Sf7Sf6S3S1fS21Sb7A1M0A1Sb9S90SffS102SfbA1Sf9SfbR2R1A3S23A5S26G0S100R2R1A2A2A3Fr;Fk;").
Proof. intros [|] [| | |]; vm_compute; reflexivity. Qed.

Theorem free_fast_sum_P : ltac2:(tb__ "0|0|
Sf7Sf6S14eOF_;S21S147A1S148OF_;F_;S3dS16dS8fR3R2A3S14fS8fR4S16bS8fR3Sf9Sf8R6R5A3R2A4S16aS8fR3Sa1R2SfdR6R5A2A5A4F_;Frho;FK;Fok;Fr;Fk;").
Proof.
  intros k r ok K rho Hok. apply triple1_triple.
  apply (sym_run_sound_strict segsU FF_FUEL (ff_cuts FF_P) (Pre_free_fast FF_P k r) (Posts_free_fast_P k r) ok K rho eq_refl (run_free_fast_P k r) Hok).
Qed.

Theorem free_fast_sum_U : ltac2:(tb__ "0|0|
Sf7Sf6S14eOF_;S21S147A1S148OF_;F_;S3dS16dS90R3R2A3S14fS90R4S16bS90R3Sf9SfbR6R5A3R2A4S16aS90R3Sa1R2S100R6R5A2A5A4F_;Frho;FK;Fok;Fr;Fk;").
Proof.
  intros k r ok K rho Hok. apply triple1_triple.
  apply (sym_run_sound_strict segsU FF_FUEL (ff_cuts FF_U) (Pre_free_fast FF_U k r) (Posts_free_fast_U k r) ok K rho eq_refl (run_free_fast_U k r) Hok).
Qed.
End Mal_free_fast.

Module Mal_free_contract.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Local Open Scope mm_scope.

Section P.
Let segs := segsU. Let C := C_U. Let E := EC_U.

Definition free_contract_quick_P : Prop := ltac2:(tb__ "0|2|
S14eOF_;S181S21S147A1S148OF_;F_;S3dSbeSc0S0Sc1S176Vsegs;R8R6A3S15cS182R8A1S123R4R3R2A3R5R4R3R2A6S3S0S152S185R9A1S123R5R4R3A3A2Sb6Q40M0S39R7PcA2A2A3S3S0ScaR4A1Sb6G0S39R8PdA2A2A3S14fVsegs;RcS16cVsegs;S16eVsegs;VC;RbRaA4S16fVE;A1R9A4S15aVsegs;S91R9S1bS22S3aS159A2M1S1eS3aS159S174VE;A1S173Vsegs;VC;RbRaA4A4S1cG1A1A3A4A4F_;F_;F_;F_;Ffr;Fi;Fam;Fg;Frho;FKc;FA;Fok;").

Definition free_quick_instantiate_stmt : Prop := ltac2:(tb__ "0|0|
S181S21S147A1S148OF_;F_;S3dS14eSbeSc0S0Sc1S16cVsegs;S16eVsegs;VC;R8R7A4S16fVE;A1R6R5A5S15cS182R9A1S123R4R3R2A3R5R4R3R2A6S3S0S152S185RaA1S123R5R4R3A3A2Sb6Q40S39R8PcA2A2A3S6Sf7Sf7S6Sf6Sf6S6S3dS3dS4S51S91RcR1A3S46Vsegs;R1Sf9Sf8R3R2A3RbA4A2Lrho1;A2Lr;A2Lk;A2F_;F_;F_;Ffr;Fi;Fam;Fg;Fw;Frho;FKc;FA;").

Definition free_quick_reabstract_stmt : Prop := ltac2:(tb__ "0|2|
S181S21S147A1M0S148OF_;F_;S3dS3dSf7Sf6S14eS14eSbeSc0S0Sc1S16cVsegs;S16eVsegs;VC;RcRbA4S16fVE;A1RaR6A5S15cS182RdA1S123R4R3R2A3R5R4R3R2A6S51S91RcRbA3S16aVsegs;G0S148S16eVsegs;VC;R11R10RfR2R1A7Lmd;Ltr;Sa1RcSfdRbRaA2R8A6S15aVsegs;S91ReS1bS22S3aS159A2M1S1eS3aS159S174VE;A1S173Vsegs;VC;R10RfA4A4S1cG1A1A3R9A5F_;F_;F_;F_;Ffr;Fi;Fam;Fg;Fw;Fw0;Fr;Fk;Frho1;Frho;FKc;FA;").

End P.

Section U.
Let segs := segsU. Let C := C_U. Let E := EC_U.
Definition free_contract_quick_U : Prop := ltac2:(tb__ "0|2|
S14eOF_;S181S21S147A1S148OF_;F_;S3dSbeSc0S0Sc1S176Vsegs;R8R6A3S15cS182R8A1S123R4R3R2A3R5R4R3R2A6S3S0S152S185R9A1S123R5R4R3A3A2Sb6Q40M0S39R7PcA2A2A3S3S0ScaR4A1Sb6G0S39R8PdA2A2A3S14fVsegs;RcS16cVsegs;S16eVsegs;VC;RbRaA4S16fVE;A1R9A4S15aVsegs;S91R9S1bS22S3aS159A2M1S1eS3aS159S174VE;A1S173Vsegs;VC;RbRaA4A4S1cG1A1A3A4A4F_;F_;F_;F_;Ffr;Fi;Fam;Fg;Frho;FKc;FA;Fok;").

End U.
End Mal_free_contract.

Module Mal_free_slow.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record fs_consts := FSC {
  fs_ff : ff_consts;
  fs_ret_call : Z;
  fs_ecall : Z;
  fs_chkfail : Z }.
Definition FS_P : fs_consts := FSC FF_P 0x206e4 0x21f38 0x202a8.
Definition FS_U : fs_consts := ltac2:(tb__ "0|1|
SebSfbS8Z1ffa4Z740M0A2S8Z217f8G0A2S8Z1fb68G0A2A4").

Inductive fs_why := WF0 | WALL.
Inductive fs_seg :=
| FS_call (k : ff_kind) (r : ff_rsv) (w : fs_why)
| FS_ret0
| FS_unmap
| FS_after.

Section States.
Variable c : fs_consts.
Let f : ff_consts := fs_ff c.

Definition fs_facts_why (w : fs_why) : list sprop := ltac2:(tb__ "0|2|
Se2S21S2eA1Lw;Vw;S1bS2eS37S13bS3eS23Q20Sa0P86A1A3S2dZ0A1A3M0S1cS2eA1M1A3S1bS2eS3fG0A1S1bS2eS37S13bS3bS13aSfeSfcA3S3bS13aS3bS13eS2dZ2A1Sa0P87A1A3S2dZffffffffffffffffA1A3A3G1A3A3Xe2x2").
Definition fs_facts_common : list sprop := ltac2:(tb__ "0|2|
S1bS2eS37S13bS36S13cSfeSfcA3S2dZ0A1M0A3S1bS2eS41S36S13cS36S140Sa0P87A1S2dZ5A1A3S2dZ7eA1A3S2dZ5eA1A2S1bS2eS4aPaM1Z4A2S1bS2eS41S2dZ1000A1S34G1A1A2S1bS2eS3fS37S13bSa0PcA1G0A3A1S1cS2eA1A3A3A3A3A3").

Definition fs_sp : sv := SAlu ALU_ADD (SVar 10) (SLit (-48)).
Definition fs_frame : sobj := ltac2:(tb__ "0|1|
S32S34PaA1S2dN50A1S2dZ0A1S1bS30S33S2dN8A1Z8M0S34PbA1A3S1bS30S33S2dN10A1G0S34P1cA1A3S1bS30S33S2dN18A1G0S34P1dA1A3S1bS30S33S2dN20A1G0S34P26A1A3S1bS30S33S2dN28A1G0S34P27A1A3S1cS30A1A3A3A3A3A3S35A5").
Definition fs_lock : sobj := ltac2:(tb__ "0|2|
S32S2dS10bVf;A1A1S2dZ0A1M0S2dZ4M1A1S1bS30S33G0G1G0A3S1cS30A1A3S35A5").
Definition fs_errno : sobj := ltac2:(tb__ "0|1|
S32S34P18A1S2dNa4A1M0S2dNa0A1S1bS30S33G0Z4Sa0Pb6A1A3S1cS30A1A3S35A5").

Definition fs_after_regs : list sv := ltac2:(tb__ "0|1|
S94S95S91A1S1bS22S24S31A2M0S1eS24S31U2S19dA4S1bG0S1eS24S31U8S34P6cA1A4S1bG0S1eS24S31U9Sa0PcA1A4S1bG0S1eS24S31U12S34P26A1A4S1bG0S1eS24S31U13S34P27A1A4S1bG0S1eS24S31UaSa0Pb4A1A4S1bG0S1eS24S31UbSa0Pb5A1A4S1cG0A1A3A3A3A3A3A3A3A2").
Definition fs_after_facts (len0 : bool) : list sprop := ltac2:(tb__ "0|4|
S25S2eS1dS21S2eA1Llen0;Vlen0;S1bS2eS37S13bSa0Pb5A1S2dZ0A1A3M0S1cS2eA1M1A3S1bS2eS3fG0A1G1A3X1dx2S1bS2eS4aPaM2Z4A2S1bS2eS41S2dZ1000A1M3S34G2A1A2S1bS2eS41G3S34P18A1A2G1A3A3A3A3").

Definition fs_cuts : list Z := ltac2:(tb__ "0|0|
S1bS0S103Vf;A1S1bS0S10aVf;A1S1bS0S106Vf;A1S1bS0SedVc;A1S1cS0A1A3A3A3A3").
Definition FS_FUEL : nat := 400%nat.

Definition Pre_fs0 (x : fs_seg) : sstate := ltac2:(tb__ "0|4|
SdcS3aLx;Vx;Sf7Sf6Se2S40S107Vf;A1S93S92S42S28S31A1M0S10cVf;R3R2A3S25S2eS108R3A1S25S2eS109R2A1S25S2eS19cR1A1S19bA3A3A3Sa1S20A9Lw;Lr;Lk;S40Se9Vc;A1M1S197S92S42G0S1bS2fS198S1bS2fS199S1cS2fA1M2A3A3S196S23A1Sa1S20A9S40G1S197S92S42G0S1bS2fS198S1bS2fS199S1bS2fS19aG2A3A3A3S196S20A1Sa1S20A9M3G3Xdcx4").
End States.

Definition Pre_fs (segs : list Segment) (c : fs_consts) (x : fs_seg) : sstate := ltac2:(tb__ "0|3|
SdcS3aLx;Vx;Sf7Sf6Se2Se7Vc;Vx;A2M0Lw;Lr;Lk;G0G0S1fS21Sb7A1M1A1S3aLx;Sb9Vsegs;Se0Se1Vc;A1Se7Vc;SecA2M2S23A5G1G1S3aLl;R1G2Sb7G1G1S3aLl0;R1S19eSbaR2A1Z0A2Sb7G1G2Ll2;Ll1;X21x2Ll0;LL;X21x2Ll;G2X1fx2Xdcx4").

Definition fs_leaf_ok (c : fs_consts) (x : fs_seg) (L : leaf) : bool := ltac2:(tb__ "0|d|
SbaVL;A1S3aSdcS1dLx;Vx;Sf7Sf6Se2Sb8S1dLx;M0SbbVL;A1M1S20S29SfS47R4A1S103SefVc;A1M2A1A2S1fS31A1S1dLx;M3S11fS31S49R4A1U1A3S31S31S1dLs;M4R1S0SfR1Se9Vc;A1A2Lra;S1S20Li;M5S141S31S31S20Lb;La;M6Lop;M7G7S146G6Lop;M8G8S1dS2S31S20La;Lw;Lsgn;M9S1S31S0S20Lk;Li;Ll;MaX31x8Ls;S20X1fx2A2S20S20S20S20S20Xb8x7Lw;Lr;Lk;G0G1S20S20S20S20SfS47R1A1MbS105G2A1A2S20S20Xb8x7McG0G1S29SfGbSeeVc;A1A2G3S11fS31S49R1A1U11A3S31G4R1S0SfR1Zd7A2Ln;G5G7G7G8G8G9GaX31x8Ls;S20X1fx2A2S20S20S20S20S20S20Xb8x7GcXdcx4TS;").

Definition fs_okb (c : fs_consts) (x : fs_seg) (o : option (list leaf)) : bool := ltac2:(tb__ "0|1|
S1fS21Sb7A1M0A1S1dLo;Vo;G0S11eSb7Se3Vc;Vx;A2R1A3Ll;S20X1fx2").
Lemma fs_okb_run : ltac2:(tb__ "0|2|
Se8SdcS1fS21Sb7A1M0A1M1S3S1dSe4R3R2R1A3S23A3S3G1R2S26G0G1G0Lo;R2G0R1Ll;S1cSb7A1X1fx2A2A3F_;Fo;Fx;Fc;").
Proof. intros c x [l|]; simpl; [reflexivity|discriminate]. Qed.
Lemma fs_okb_shape : ltac2:(tb__ "0|2|
Se8SdcS1fS21Sb7A1M0A1M1S3S1dSe4R3R2R1A3S23A3S3S1dS11eSb7Se3R4R3A2G1G0Lo;R2G0R1Ll;S1cSb7A1X1fx2A3S23A3F_;Fo;Fx;Fc;").
Proof. intros c x [l|]; simpl; auto. Qed.

Definition run_fs (segs : list Segment) (c : fs_consts) (x : fs_seg) : list leaf := ltac2:(tb__ "0|1|
S1fS21Sb7A1M0A1G0Lx;Sb9Vsegs;Se0Se1Vc;A1SdfVsegs;Vc;Vx;A3S23A5G0R1Ll;S1cSb7A1X1fx2").
Definition Posts_fs_P (x : fs_seg) : list leaf := ltac2:(tb__ "0|0|
SeaS8fSddVx;A3").
Definition Posts_fs_U (x : fs_seg) : list leaf := ltac2:(tb__ "0|0|
SeaS90SdeVx;A3").

Ltac fs_cases x := destruct x as [ [ | ] [ | | | ] [ | ] | | | ].

Lemma Pre_fs_P_strict : ltac2:(tb__ "0|0|
SdcS3S1dS4dSdfS8fSddR1A3A1S20A3Fx;").
Proof. intros x. fs_cases x; vm_compute; reflexivity. Qed.
Lemma fs_ok_P : ltac2:(tb__ "0|0|
SdcS3S1dSe4SddR1Sb9S8fSe0Se1SddA1SdfS8fSddR1A3S23A5A3S23A3Fx;").
Proof. intros x. fs_cases x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_fs_P : ltac2:(tb__ "0|1|
SdcS3S1fS21Sb7A1M0A1Sb9S8fSe0Se1SddA1SdfS8fSddR1A3S23A5S26G0Se5R1A1A2A3Fx;").
Proof. intros x. exact (fs_okb_run FS_P x _ (fs_ok_P x)). Qed.
Lemma Posts_fs_P_shape : ltac2:(tb__ "0|0|
SdcS3S1dS11eSb7Se3SddR1A2Se5R1A1A3S23A3Fx;").
Proof. intros x. exact (fs_okb_shape FS_P x _ (fs_ok_P x)). Qed.

Theorem free_slow_sum_P : ltac2:(tb__ "0|1|
SdcS14eOF_;S21S147A1S148OF_;F_;S3dS16dS8fR3R2A3S14fS8fR4S16bS8fR3SdfS8fSddR5A3M0R2A4S16aS8fR3S59G0A1R2Se5R5A1A5A4F_;Frho;FK;Fok;Fx;").
Proof.
  intros x ok K rho Hok. apply triple1_triple.
  apply (sym_run_sound_strict segsU FS_FUEL (fs_cuts FS_P) (Pre_fs segsU FS_P x) (Posts_fs_P x) ok K rho (Pre_fs_P_strict x) (run_fs_P x) Hok).
Qed.

Lemma Pre_fs_U_strict : ltac2:(tb__ "0|0|
SdcS3S1dS4dSdfS90SdeR1A3A1S20A3Fx;").
Proof. intros x. fs_cases x; vm_compute; reflexivity. Qed.
Lemma fs_ok_U : ltac2:(tb__ "0|0|
SdcS3S1dSe4SdeR1Sb9S90Se0Se1SdeA1SdfS90SdeR1A3S23A5A3S23A3Fx;").
Proof. intros x. fs_cases x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_fs_U : ltac2:(tb__ "0|1|
SdcS3S1fS21Sb7A1M0A1Sb9S90Se0Se1SdeA1SdfS90SdeR1A3S23A5S26G0Se6R1A1A2A3Fx;").
Proof. intros x. exact (fs_okb_run FS_U x _ (fs_ok_U x)). Qed.
Lemma Posts_fs_U_shape : ltac2:(tb__ "0|0|
SdcS3S1dS11eSb7Se3SdeR1A2Se6R1A1A3S23A3Fx;").
Proof. intros x. exact (fs_okb_shape FS_U x _ (fs_ok_U x)). Qed.

Theorem free_slow_sum_U : ltac2:(tb__ "0|1|
SdcS14eOF_;S21S147A1S148OF_;F_;S3dS16dS90R3R2A3S14fS90R4S16bS90R3SdfS90SdeR5A3M0R2A4S16aS90R3S59G0A1R2Se6R5A1A5A4F_;Frho;FK;Fok;Fx;").
Proof.
  intros x ok K rho Hok. apply triple1_triple.
  apply (sym_run_sound_strict segsU FS_FUEL (fs_cuts FS_U) (Pre_fs segsU FS_U x) (Posts_fs_U x) ok K rho (Pre_fs_U_strict x) (run_fs_U x) Hok).
Qed.
End Mal_free_slow.

Module Mal_free_quick.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_contract.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma size_classes_bytes_range : ltac2:(tb__ "0|0|
Sf0S0S0S4S9Z0R1A2SbR1Z100A2A2Lb;S153A3").
Proof.
  apply Forall_forall. intros b Hb.
  assert (H : forallb (fun b => (0 <=? b) && (b <? 256))%bool size_classes_bytes = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) H b Hb) as Hb'. apply andb_prop in Hb' as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma zl_table : ltac2:(tb__ "0|2|
S3S21S0A1Sf1Sb4Q8M0A1M1S0G1Sb6G0R1A2Lb;Sf1S0G1Sb5G0A1S153A4A4S153A3").
Proof.
  rewrite map_map. rewrite <- (map_id size_classes_bytes) at 2. apply map_ext_in.
  intros b Hb. pose proof (proj1 (Forall_forall _ _) size_classes_bytes_range b Hb) as R.
  cbn beta in R. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= b < 256). lia.
Qed.

Lemma table_u16 : ltac2:(tb__ "0|1|
S0S4S9Z0R1A2SbR1Z30A2A2S3S0S9cS9dScZ2M0R2A2G0S153A3A1Sd2R2Sd1A2A3F_;Fsc;").
Proof.
  intros sc Hsc.
  pose proof (forall_range_dec (fun sc => zle (zsublist (2 * sc) 2 size_classes_bytes) =? znth sc size_classes) 0 48
                ltac:(vm_compute; reflexivity) sc ltac:(lia)) as H.
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma znth_size_classes_range : ltac2:(tb__ "0|1|
S0S4S9Z0R1A2SbR1Z30A2A2S4S9Z1Sd2R2Sd1A2M0A2S9G0Z1fffA2A2F_;Fsc;").
Proof.
  intros sc Hsc.
  pose proof (forall_range_dec (fun sc => (1 <=? znth sc size_classes) && (znth sc size_classes <=? 8191))%bool 0 48
                ltac:(vm_compute; reflexivity) sc ltac:(lia)) as H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma land_126_odd : ltac2:(tb__ "0|2|
S0S0S4S9Z0R2A2M0SbR2Z30A2A2G0S3S0S18S8S8Z1ScZ2R4A2M1A2ScZ80R3A2A2Z7eA2G1A3F_;F_;Fm;Fsc;").
Proof.
  intros sc m Hsc Hm.
  rewrite (land_low_congr (1 + 2 * sc + 128 * m) (1 + 2 * sc) 126 7); [| lia | cbn; lia | change (2 ^ 7) with 128; lia].
  pose proof (forall_range_dec (fun sc => Z.land (1 + 2 * sc) 126 =? 2 * sc) 0 48 ltac:(vm_compute; reflexivity) sc ltac:(lia)) as H.
  apply Z.eqb_eq in H. exact H.
Qed.

Definition lit_of (e : sv) : option Z := match e with SLit z => Some z | _ => None end.

Definition covers_lit (cs : list cell) (off : Z) : bool := ltac2:(tb__ "0|0|
S120S30S30S1fS0A1S1dLx;S186S52R1A1A1S0S29S16R1Voff;A2S15Voff;S8R1S53R2A1A2A2A2Lo;S20X1fx2Lc;Vcs;A3").

Definition obj_coveredb (o : sobj) : bool := ltac2:(tb__ "0|1|
S45S1dLx;S55Vo;A1S1fS0A1S1dLx;M0S186S61Vo;A1A1S0G0S186S60Vo;A1A1S0S11eS24S24S18cS48Vo;A1S8R3S11R1A1A2A2Lk;Sf4U0S17SeR1R2A2A1A2A3Lhi;S20X1fx2Llo;S20X1fx2S20S20S1S20Ll;S1S23Ll;S0S31S21S22S0S0A2A1S21S5cA1S20Ltmpl;Lflds;Lcnt;Lesz;X45x6").

Definition pg_aligned (x : Z) : Prop := x mod 4096 = 0.

Section Inst.
Variables (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame).
Variables (a : sptr) (k : Z).
Variable rho : valuation.

Hypothesis FFx : ltac2:(tb__ "0|0|
S195Vs;Vg;Vam;Vi;Vfr;A5").
Hypothesis HQ : ltac2:(tb__ "0|0|
S15cVs;S123Vam;Vi;Vfr;A3Vg;Vam;Vi;Vfr;A6").
Hypothesis HLok : layout_ok L s.
Hypothesis Harea : ltac2:(tb__ "0|0|
S4S11dSbeVa;SdbVs;A1A3S4S4S9Z0Vk;A2SbVk;Sd7A2A2S4S3SbeVg;Sd5Va;S8Sd3ScSd4Vk;A2A2A2A3S4S188Sc8Va;A1A1S188S12cVL;SccVa;A1A2A1A2A2A2A2").
Hypothesis Hmem_pg : ltac2:(tb__ "0|0|
S188S12cVL;SccSc3Vam;A1A1A2A1").

Definition p : sptr := ltac2:(tb__ "0|0|
S123Vam;Vi;Vfr;A3").
Definition n : Z := fr_n fr.
Definition st : Z := stride_of am.
Definition zP : Z := addr_of L p.
Definition zMem : Z := ltac2:(tb__ "0|0|
S152VL;Sc3Vam;A1A2").
Definition zG : Z := addr_of L g.
Definition zA : Z := addr_of L a.
Definition zEnd : Z := ltac2:(tb__ "0|0|
S152VL;S17fVam;Vi;A2A2").
Definition h3 : Z := ltac2:(tb__ "0|0|
S135Vam;Vi;Vfr;A3").
Definition h16 : Z := ltac2:(tb__ "0|0|
S136Vam;Vi;Vfr;A3").
Definition bits : Z := meta_bits am.
Definition rsv : Z := reserved_of am fr.
Definition sz : Z := ltac2:(tb__ "0|0|
Sd2Sc9Vam;A1Sd1A2").

Definition sti : Z := st * i.
Definition stl : Z := ltac2:(tb__ "0|0|
ScS71S8Sc7Vam;A1Z1A2A2").

Hypothesis HP12 : ltac2:(tb__ "0|0|
S3S0Sb6Q40S39Vrho;PcA2A2S6aA3").

Variable rgm : region.
Hypothesis Hrgm : ltac2:(tb__ "0|2|
S4S3S1fSd6A1S138Vs;SccSc3Vam;A1A1M0A2S26Sd6Vrgm;A2A3S4S9Sc4S12cVL;G0A2M1A2S9S8G1Sc6Vrgm;A1A2S151VL;A1A2A2A2").
Hypothesis HzA : ltac2:(tb__ "0|0|
S4S9Sc4S6bA2S9S8S6bSc4A2S151VL;A1A2A2").

Lemma Hreg : ltac2:(tb__ "0|4|
S4S9Z0M0Sc8Sc3Vam;A1A1M1A2S4S9S8S8G1S129Vam;A1A2SceA2Sc6Vrgm;A1M2A2SbG0Sc5Vam;A1M3A2S4S3S0G1G0A3S3S0G2ScG3Sc4A2A3A2F_;A2A2").
Proof using FFx Hrgm.
  destruct (ff_region _ _ _ _ _ FFx) as (rg & Hr & _ & _ & Ho & He & Hm).
  destruct Hrgm as (Hr' & _). rewrite Hr in Hr'. injection Hr' as ->. auto.
Qed.

Lemma HzMem : ltac2:(tb__ "0|1|
S4S9Sc4S6cA2S4S9S8S8S6cS129Vam;A1A2SceA2S151VL;A1M0A2S9Sc6Vrgm;A1G0A2A2A2").
Proof using FFx Hmem_pg Hrgm.
  pose proof Hreg as (Ho & He & _). destruct Hrgm as (_ & H1 & H2).
  unfold zMem, addr_of, loc_addr. destruct (am_mem am) as [r o]. cbn [prid poff] in *. unfold PGSZ in *. lia.
Qed.

Lemma Hsc48 : ltac2:(tb__ "0|1|
S4S9Z0Sc9Vam;A1M0A2SbG0Z30A2A2").
Proof using FFx HQ. destruct HQ as (_ & _ & _ & _ & _ & Hsc & _). destruct (ff_sc _ _ _ _ _ FFx) as [[H _]|[H _]]; lia. Qed.

Lemma Hlast1 : ltac2:(tb__ "0|1|
S4S9Z1Sc7Vam;A1M0A2S9G0Z1fA2A2").
Proof using FFx HQ. destruct HQ as (_ & _ & _ & _ & _ & _ & Hl). pose proof (ff_last _ _ _ _ _ FFx). lia. Qed.

Lemma Hst : st = 16 * sz.
Proof using FFx HQ.
  unfold st, sz. destruct (ff_sc _ _ _ _ _ FFx) as [[_ H]|[H _]]; [|pose proof Hsc48; lia].
  rewrite H by (pose proof Hlast1; lia). unfold class_size, UNIT. reflexivity.
Qed.

Lemma Hsz : 1 <= sz <= 8191.
Proof using FFx HQ. unfold sz. apply znth_size_classes_range. apply Hsc48. Qed.

Lemma Hkind : ltac2:(tb__ "0|0|
S3ScfSd0Vfr;A1ScdA3").
Proof using HQ. destruct HQ as (_ & H & _). exact H. Qed.

Lemma Hrsv_nn : 0 <= rsv.
Proof using FFx. unfold rsv, reserved_of. pose proof (ff_fit _ _ _ _ _ FFx). pose proof (ff_n _ _ _ _ _ FFx). lia. Qed.

Lemma Hrsv_code : ltac2:(tb__ "0|0|
S3S0S139Vam;Vfr;A2S10S6eZ5A2A3").
Proof using . unfold rsv_code, rsv, reserved_of. destruct (5 <=? _) eqn:E; [apply Z.leb_le in E|apply Z.leb_gt in E]; lia. Qed.

Lemma Hh3 : ltac2:(tb__ "0|0|
S3S0S7bS8Vi;ScZ20S10S6eZ5A2A2A2A3").
Proof using HQ. unfold h3, hdr_byte3. rewrite Hkind, Hrsv_code. reflexivity. Qed.

Lemma Hh3_range : 0 <= h3 <= 191.
Proof using FFx HQ.
  rewrite Hh3. pose proof (ff_i _ _ _ _ _ FFx). pose proof (ff_last _ _ _ _ _ FFx). pose proof Hrsv_nn.
  pose proof (Z.le_min_r rsv 5). pose proof (Z.min_glb rsv 5 0 ltac:(lia) ltac:(lia)).
  generalize dependent (Z.min rsv 5). intros m Hm1 Hm2. lia.
Qed.

Lemma Hh16 : ltac2:(tb__ "0|1|
S3S0ScZ10M0S73A2S8S74ScG0ScbVfr;A1A2A2A3").
Proof using FFx HQ.
  pose proof Hst as E. unfold h16, hdr_off16, sti, st in *. rewrite E. unfold UNIT.
  replace (16 * sz * i) with ((sz * i) * 16) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Lemma Hbits : ltac2:(tb__ "0|0|
S3S0S78S8S8S8Sc7Vam;A1Z20A2ScZ40Sc9Vam;A1A2A2ScZ1000Sc5Vam;A1A2A2A3").
Proof using . reflexivity. Qed.

Lemma HzP : ltac2:(tb__ "0|1|
S3S0S6aS8S8S8S6cZ10M0A2S74A2ScG0ScbVfr;A1A2A2A3").
Proof using Hmem_pg Hrgm.
  unfold zP, zMem, p, frame_ptr, slot_start, addr_of, loc_addr, sti, st. destruct (am_mem am) as [r o]. cbn [padd]. unfold UNIT. lia.
Qed.

Lemma HzEnd : ltac2:(tb__ "0|0|
S3S0S6fSeS8S8S8S6cZ10A2S74A2S71A2Z4A2A3").
Proof using Hmem_pg Hrgm.
  unfold zEnd, zMem, slot_end, slot_start, addr_of, loc_addr, sti, st. destruct (am_mem am) as [r o]. cbn [padd]. unfold UNIT, IB. lia.
Qed.

Lemma HzG : ltac2:(tb__ "0|0|
S3S0S79S8S8S6bSd3A2ScSd4Vk;A2A2A3").
Proof using Harea.
  destruct Harea as (_ & _ & E & _). unfold zG, zA, addr_of, loc_addr. rewrite E. destruct a as [r o]. cbn [padd]. lia.
Qed.

Lemma HzA_pg : pg_aligned zA.
Proof using Harea HzA am.
  destruct Harea as (_ & _ & _ & Ho & Hr). unfold pg_aligned, zA, addr_of, loc_addr in *. destruct a as [r o]. cbn [prid poff] in *.
  rewrite Z.add_mod, Ho, Hr by lia. reflexivity.
Qed.

Lemma HzP16 : zP mod 16 = 0.
Proof using FFx Hmem_pg Hrgm.
  rewrite HzP. unfold zMem, addr_of, loc_addr, sti, st. pose proof (ff_mem16 _ _ _ _ _ FFx) as M. pose proof (ff_stride16 _ _ _ _ _ FFx) as S.
  pose proof Hmem_pg as R. unfold pg_aligned in R. destruct (am_mem am) as [r o]. cbn [prid poff] in *.
  apply Z.mod_divide in M; [|lia]. apply Z.mod_divide in S; [|lia]. apply Z.mod_divide in R; [|lia].
  destruct M as [m Hm]. destruct S as [q Hq]. destruct R as [t Ht]. rewrite Hm, Hq, Ht.
  replace (t * 4096 + m * 16 + 16 + q * 16 * i + 16 * fr_off fr) with ((t * 256 + m + 1 + q * i + fr_off fr) * 16) by lia.
  apply Z_mod_mult.
Qed.

Lemma Hext : ltac2:(tb__ "0|0|
S3S0S129Vam;A1SeS8Z10S7cA2Z4A2A3").
Proof using . unfold group_extent, stl, st, UNIT, IB. reflexivity. Qed.

Lemma Hsti : ltac2:(tb__ "0|0|
S4S9Z0S74A2S4S9S8S74S71A2S7cA2S9Z10S71A2A2A2").
Proof using FFx.
  pose proof (ff_i _ _ _ _ _ FFx) as Hi. pose proof (ff_stride_pos _ _ _ _ _ FFx) as Hs. unfold sti, stl, st in *.
  split; [apply Z.mul_nonneg_nonneg; lia|]. split; [|lia].
  replace (stride_of am * (am_last am + 1)) with (stride_of am * am_last am + stride_of am) by lia.
  assert (stride_of am * i <= stride_of am * am_last am) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

Lemma Hstl : stl < 2 ^ 20.
Proof using FFx HQ. unfold stl, st. destruct (ff_ext _ _ _ _ _ FFx) as [H|H]; [exact H|]. exfalso. pose proof Hsc48 as H0. clear -H H0. lia. Qed.

Lemma Hfit : ltac2:(tb__ "0|0|
S3S0S8S8ScZ10ScbVfr;A1A2S6dA2S6eA2SeS71Z4A2A3").
Proof using . unfold n, rsv, reserved_of, st, UNIT, IB. lia. Qed.

Definition rw1 (j : positive) : word := ltac2:(tb__ "0|2|
S1dSb4Q40M0A1L_;M1SbdVj;P82A2Sb5G0S7bA2G1SbdVj;P83A2Sb5G0S73A2G1SbdVj;P84A2Sb5G0S79A2G1SbdVj;P85A2Sb5G0Sc2Vam;A1A2G1SbdVj;P86A2Sb5G0SbfVam;A1A2G1SbdVj;P87A2Sb5G0S78A2G1SbdVj;P88A2Sb5G0SdS130VL;A1SaZ2Z40A2A2A2G1SbdVj;P89A2Sb5G0S6eA2G1SbdVj;P8bA2S39Vrho;PfA2G1SbdVj;PdA2S39Vrho;P10A2S39Vrho;Vj;A2X1dx2X1dx2X1dx2X1dx2X1dx2X1dx2X1dx2X1dx2X1dx2X1dx2").

Definition rw1_changed (j : positive) : bool := ltac2:(tb__ "0|0|
S27S27S27S27S27S27S27S27S27SbdVj;P82A2SbdVj;P83A2A2SbdVj;P84A2A2SbdVj;P85A2A2SbdVj;P86A2A2SbdVj;P87A2A2SbdVj;P88A2A2SbdVj;P89A2A2SbdVj;P8bA2A2SbdVj;PdA2A2").

Lemma rw1_other : ltac2:(tb__ "0|0|
S1S3S1dS8eR1A1S20A3S3Sb4Q40A1S8aR2A1S39Vrho;R2A2A3F_;Fj;").
Proof using .
  intros j H. unfold rw1_changed in H. unfold rw1.
  repeat (apply Bool.orb_false_iff in H; destruct H as [H ?]).
  repeat match goal with
         | |- (if Pos.eqb j ?c then _ else _) = _ => replace (Pos.eqb j c) with false by (symmetry; assumption)
         end.
  reflexivity.
Qed.

Definition rl1 (l : positive) : list byte := ltac2:(tb__ "0|2|
S1dS21Sb4Q8M0A1M1A1L_;SbdVl;P1A2Sf1S0G1Sb5G0A1S153A4S4bVrho;Vl;A2X1dx2").

Definition rho1 (m : word -> option byte) : valuation := ltac2:(tb__ "0|0|
S5fS8aS8dVm;A3").

Definition zr1 : positive -> Z := zr_of (rho1 (fun _ => None)).
Definition zl1 : positive -> list Z := zl_of (rho1 (fun _ => None)).

Lemma zr1_zl1_any : ltac2:(tb__ "0|1|
Sb4Q40A1S1fSb4Q8A1A1F_;S31S3S0S96S9fS69R2A1M0A1S9eG0A1R1A3S96S67S68R1A3A3Fe;Fm;").
Proof using . intros. apply zeval_ext; intros; reflexivity. Qed.

Lemma u64 : ltac2:(tb__ "0|1|
S0S4S9Z0R1A2SbR1SaZ2Z40A2A2A2S3S0Sb6Q40M0Sb5G0R2A2A2R2A3F_;Fz;").
Proof using . intros. apply u64_of_sum. assumption. Qed.

Lemma ceiling_small : topL L < 2 ^ 47.
Proof using . pose proof (topL_range L). lia. Qed.

Lemma zr1_12 : zr1 12%positive = zP. Proof using HP12. unfold zr1, zr_of, rho1. cbn [rw rw1 Pos.eqb]. exact HP12. Qed.
Lemma zr1_130 : zr1 130%positive = h3. Proof using FFx HQ. unfold zr1, zr_of, rho1. cbn [rw rw1 Pos.eqb]. apply u64. pose proof Hh3_range. lia. Qed.
Lemma zr1_131 : zr1 131%positive = h16. Proof using FFx. unfold zr1, zr_of, rho1. cbn [rw rw1 Pos.eqb]. apply u64. pose proof (ff_h16 _ _ _ _ _ FFx). unfold h16. lia. Qed.
Lemma zr1_132 : zr1 132%positive = zG.
Proof using Harea HzA. unfold zr1, zr_of, rho1. cbn [rw rw1 Pos.eqb]. apply u64. pose proof HzG. pose proof HzA. pose proof ceiling_small. destruct Harea as (_ & Hk & _). unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia. Qed.
Lemma zr1_133 : ltac2:(tb__ "0|0|
S3S0S67P85A1Sc2Vam;A1A3"). Proof using FFx. unfold zr1, zr_of, rho1. cbn [rw rw1 Pos.eqb]. apply u64. pose proof (ff_avail_nn _ _ _ _ _ FFx). lia. Qed.
Lemma zr1_134 : ltac2:(tb__ "0|0|
S3S0S67P86A1SbfVam;A1A3"). Proof using FFx. unfold zr1, zr_of, rho1. cbn [rw rw1 Pos.eqb]. apply u64. pose proof (ff_freed_nn _ _ _ _ _ FFx). lia. Qed.
Lemma bits_range : 0 <= bits < 2 ^ 48.
Proof using FFx HQ Hmem_pg Hrgm.
  rewrite Hbits. pose proof Hlast1. pose proof Hsc48. pose proof (ff_maplen _ _ _ _ _ FFx).
  pose proof Hreg as (_ & _ & Hm).
  destruct (Z_lt_dec 0 (am_maplen am)) as [Hpos|Hz].
  - destruct (Hm Hpos) as [_ Hlen]. pose proof HzMem as (_ & _ & HC). pose proof ceiling_small. unfold PGSZ in *. lia.
  - lia.
Qed.
Lemma zr1_135 : zr1 135%positive = bits. Proof using FFx HQ Hmem_pg Hrgm. unfold zr1, zr_of, rho1. cbn [rw rw1 Pos.eqb]. apply u64. pose proof bits_range. lia. Qed.
Lemma zr1_136 : ltac2:(tb__ "0|0|
S3S0S67P88A1SdS130VL;A1SaZ2Z40A2A2A3"). Proof using . unfold zr1, zr_of, rho1. cbn [rw rw1 Pos.eqb]. apply u64. apply Z.mod_pos_bound. lia. Qed.
Lemma rsv_range : 0 <= rsv < 2 ^ 20.
Proof using FFx HQ.
  pose proof Hrsv_nn. unfold rsv, reserved_of in *. pose proof (ff_ext _ _ _ _ _ FFx) as [E|E]; [|pose proof Hsc48; lia].
  pose proof (ff_n _ _ _ _ _ FFx). pose proof (ff_off _ _ _ _ _ FFx). pose proof Hlast1. pose proof (ff_stride_pos _ _ _ _ _ FFx). unfold UNIT, IB in *. nia.
Qed.
Lemma zr1_137 : zr1 137%positive = rsv. Proof using FFx HQ. unfold zr1, zr_of, rho1. cbn [rw rw1 Pos.eqb]. apply u64. pose proof rsv_range. lia. Qed.
Lemma zl1_1 : ltac2:(tb__ "0|0|
S3S21S0A1S68Sa2A1S153A3"). Proof using . unfold zl1, zl_of, rho1, rl1, L_SIZECLASSES. cbn [rl Pos.eqb]. apply zl_table. Qed.

Lemma ze_var : ltac2:(tb__ "0|0|
S1S3S0S96S67S68S34R1A1A3SdS67R1A1SaZ2Z40A2A2A3Fj;"). Proof using . reflexivity. Qed.
Lemma ze_v : ltac2:(tb__ "0|0|
S1S3S0S96S67S68Sa0R1A1A3SdS67R1A1SaZ2Z40A2A2A3Fj;"). Proof using . reflexivity. Qed.
Lemma ze_lit : ltac2:(tb__ "0|0|
S0S3S0S96S67S68S2dR1A1A3SdR1SaZ2Z40A2A2A3Fz;"). Proof using . reflexivity. Qed.
Lemma ze_alu : ltac2:(tb__ "0|0|
S141S31S31S3S0S96S67S68S36R3R2R1A3A3S9bZ40R3S96S67S68R2A3S96S67S68R1A3A4A3Fy;Fx;Fop;"). Proof using . reflexivity. Qed.
Lemma ze_aluw : ltac2:(tb__ "0|2|
S141S31S31S3S0S96S67S68S3bR3R2R1A3A3S97S9bZ20M0R3SdS96S67S68R2A3SaZ2G0A2M1A2SdS96S67S68R1A3G1A2A4A1A3Fy;Fx;Fop;"). Proof using . reflexivity. Qed.
Lemma ze_mul : ltac2:(tb__ "0|0|
S31S31S3S0S96S67S68S50S144R2R1A3A3SdScS96S67S68R2A3S96S67S68R1A3A2SaZ2Z40A2A2A3Fy;Fx;"). Proof using . reflexivity. Qed.
Lemma ze_ext : ltac2:(tb__ "0|3|
S1dS2S31S3S0S96S67S68S3eR3R2R1A3A3S1dS0Lsg;R3SdS99S19R2A1M0S96S67S68R1A3M1A2SaZ2M2Z40A2A2SdG1SaG2G0A2A2X1dx2A3Fx;Fw;Fsg;"). Proof using . reflexivity. Qed.
Lemma ze_lbytes : ltac2:(tb__ "0|0|
S1S31S0S3S0S96S67S68S4fR3R2R1A3A3SdS9cS9dS96S67S68R2A3R1S68R3A1A3A1SaZ2Z40A2A2A3Fkk;Fix;Fl;"). Proof using . reflexivity. Qed.

Lemma m64 : ltac2:(tb__ "0|1|
S0S4S9Z0R1A2SbR1SaZ2Z40A2M0A2A2S3S0SdR2G0A2R2A3F_;Fz;").
Proof using . intros. apply Z.mod_small. assumption. Qed.

Lemma R_all : ltac2:(tb__ "0|10|
S4S4S9Z0M0Vi;A2S9Vi;Sc7Vam;A1M1A2A2S4S4S9Z1M2G1A2S9G1Z1fA2A2S4S4S9G0Sc9Vam;A1M3A2SbG3Z30A2A2S4S4S9G2S75A2S9S75Z1fffA2A2S4S3S0S71ScZ10M4S75A2A3S4S4S9G0ScbVfr;A1M5A2S9G5ZffA2A2S4S9G0S6dA2S4S3S0S8S8ScG4G5A2M6S6dA2S6eA2SeS71Z4M7A2A3S4S9G0S6eA2S4S4S9G0S73A2S9S73ZffffA2A2S4S3S0ScG4S73A2S8S74G6A2A3S4S9G0Sc5Vam;A1A2S4S4S9G0Sc2Vam;A1M8A2SbG8SaZ2M9Z20A2MaA2A2S4S4S9G0SbfVam;A1MbA2SbGbGaA2A2S4S9Z1000McS6cA2S4S9S8S8S6cS129Vam;A1MdA2G7A2S151VL;A1MeA2S4SbGeSaG9Z2fA2A2S4S3S0S6aS8S8S8S6cG4A2S74A2MfG6A2A3S4S3S0S6fSeS8GfS71A2G7A2A3S4S3S0GdSeS8G4S7cA2G7A2A3S4S9G0S74A2S4S9S8S74S71A2S7cA2S4SbS7cSaG9Z14A2A2S4S9GcS6bA2S4S9S8S6bGcA2GeA2S4S3S0S79S8S8S6bZ18A2ScZ28Vk;A2A2A3S4S9G0Vk;A2SbVk;Z65A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  pose proof (ff_i _ _ _ _ _ FFx). pose proof Hlast1. pose proof Hsc48. pose proof Hsz. pose proof Hst.
  pose proof (ff_off _ _ _ _ _ FFx). pose proof (ff_n _ _ _ _ _ FFx) as Hn. pose proof Hfit.
  pose proof Hrsv_nn. pose proof (ff_h16 _ _ _ _ _ FFx) as H16. pose proof Hh16.
  pose proof (ff_maplen _ _ _ _ _ FFx). pose proof (ff_avail_nn _ _ _ _ _ FFx). pose proof (ff_freed_nn _ _ _ _ _ FFx).
  pose proof HzMem as (M1 & M2 & _). pose proof ceiling_small. pose proof HzP. pose proof HzEnd. pose proof Hext.
  pose proof Hsti. pose proof Hstl.
  pose proof HzA as ZA. pose proof HzG as ZG.
  destruct Harea as (_ & Hk & _ & _).
  clear HQ HLok Hmem_pg Hrgm HzA HP12.
  unfold n, h16, PGSZ, IB, AREA_HDR, META_SIZE, METAS_PER_AREA in *.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Lemma m64_small : ltac2:(tb__ "0|1|
S0S9Z0R1A2SbR2SaZ2Z40A2M0A2S3S0SdR3G0A2R3A3F_;F_;Fz;").
Proof using . intros. apply Z.mod_small. lia. Qed.

Lemma ze12 : ltac2:(tb__ "0|0|
S3S0S96S67S68Sa0PcA1A3S6aA3").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm HzA. rewrite ze_v, zr1_12. pose proof R_all. apply m64_small; lia. Qed.
Lemma ze130 : ltac2:(tb__ "0|0|
S3S0S96S67S68Sa0P82A1A3S7bA3").
Proof using FFx HQ. rewrite ze_v, zr1_130. pose proof Hh3_range. apply m64_small; lia. Qed.
Lemma ze131 : ltac2:(tb__ "0|0|
S3S0S96S67S68Sa0P83A1A3S73A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA. rewrite ze_v, zr1_131. pose proof R_all. apply m64_small; lia. Qed.
Lemma ze132 : ltac2:(tb__ "0|0|
S3S0S96S67S68Sa0P84A1A3S79A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA. rewrite ze_v, zr1_132. pose proof R_all. apply m64_small; lia. Qed.
Lemma ze133 : ltac2:(tb__ "0|0|
S3S0S96S67S68Sa0P85A1A3Sc2Vam;A1A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA. rewrite ze_v, zr1_133. pose proof R_all. apply m64_small; lia. Qed.
Lemma ze134 : ltac2:(tb__ "0|0|
S3S0S96S67S68Sa0P86A1A3SbfVam;A1A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA. rewrite ze_v, zr1_134. pose proof R_all. apply m64_small; lia. Qed.
Lemma ze135 : ltac2:(tb__ "0|0|
S3S0S96S67S68Sa0P87A1A3S78A3").
Proof using FFx HQ Hmem_pg Hrgm. rewrite ze_v, zr1_135. pose proof bits_range. apply m64_small; lia. Qed.
Lemma ze137 : ltac2:(tb__ "0|0|
S3S0S96S67S68Sa0P89A1A3S6eA3").
Proof using FFx HQ. rewrite ze_v, zr1_137. pose proof rsv_range. apply m64_small; lia. Qed.

Lemma h3_div32 : ltac2:(tb__ "0|1|
S4S3S0S14S7bZ20M0A2S10S6eZ5A2A3S3S0SdS7bG0A2Vi;A3A2").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  pose proof R_all as R. rewrite Hh3.
  assert (Hi : 0 <= i < 32) by lia.
  set (m := Z.min rsv 5) in *.
  replace (i + 32 * m) with (i + m * 32) by lia. split.
  - rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
  - rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma ze_idx : ltac2:(tb__ "0|0|
S3S0S96S67S68SaeA3Vi;A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  unfold gm_idx. rewrite ze_alu, ze130, ze_lit. cbn [zalu]. change (31 mod 2 ^ 64) with 31.
  pose proof Hh3_range. rewrite (m64_small h3) by lia. rewrite land_31. apply h3_div32.
Qed.

Lemma ze_ffidx : ltac2:(tb__ "0|0|
S3S0S96S67S68S119A3Vi;A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA. exact ze_idx. Qed.

Lemma ze_code : ltac2:(tb__ "0|0|
S3S0S96S67S68S101A3S10S6eZ5A2A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  unfold ff_code. rewrite ze_alu, ze130, ze_lit. cbn [zalu]. change (5 mod 2 ^ 64 mod 64) with 5.
  pose proof Hh3_range. rewrite (m64_small h3) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. apply h3_div32.
Qed.

Lemma bits_mod32 : ltac2:(tb__ "0|4|
S4S3S0SdS78Z20M0A2Sc7Vam;A1A3S4S3S0S14S78Z1000M1A2Sc5Vam;A1M2A3S4S3S0S14SdS78G1A2Z40A2Sc9Vam;A1M3A3S3S0S14S78G0A2S8S8Z1ScZ2G3A2A2ScZ80G2A2A2A3A2A2A2").
Proof using FFx HQ.
  pose proof Hlast1. pose proof Hsc48. pose proof (ff_maplen _ _ _ _ _ FFx). clear HQ HLok Harea Hmem_pg HP12 Hrgm HzA.
  rewrite Hbits.
  set (l := am_last am) in *. set (c := am_sc am) in *. set (m := am_maplen am) in *.
  repeat split.
  - replace (l + 32 + 64 * c + 4096 * m) with (l + (1 + 2 * c + 128 * m) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - replace (l + 32 + 64 * c + 4096 * m) with ((l + 32 + 64 * c) + m * 4096) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
  - replace (l + 32 + 64 * c + 4096 * m) with ((l + 32 + 64 * c) + m * 4096) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace (l + 32 + 64 * c) with ((l + 32) + c * 64) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
  - replace (l + 32 + 64 * c + 4096 * m) with (l + (1 + 2 * c + 128 * m) * 32) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma ze_last : ltac2:(tb__ "0|0|
S3S0S96S67S68SafA3Sc7Vam;A1A3").
Proof using FFx HQ Hmem_pg Hrgm.
  unfold gm_last. rewrite ze_alu, ze135, ze_lit. cbn [zalu]. change (31 mod 2 ^ 64) with 31.
  pose proof bits_range. rewrite (m64_small bits) by lia. rewrite land_31. apply bits_mod32.
Qed.

Lemma ze_maplen : ltac2:(tb__ "0|0|
S3S0S96S67S68Sb0A3Sc5Vam;A1A3").
Proof using FFx HQ Hmem_pg Hrgm.
  unfold gm_maplen. rewrite ze_alu, ze135, ze_lit. cbn [zalu]. change (12 mod 2 ^ 64 mod 64) with 12.
  pose proof bits_range. rewrite (m64_small bits) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096. apply bits_mod32.
Qed.

Lemma ze_sc : ltac2:(tb__ "0|0|
S3S0S96S67S68Sb2A3Sc9Vam;A1A3").
Proof using FFx HQ Hmem_pg Hrgm.
  unfold gm_sc. rewrite ze_alu, ze_alu, ze135, !ze_lit. cbn [zalu].
  change (52 mod 2 ^ 64 mod 64) with 52. change (58 mod 2 ^ 64 mod 64) with 58.
  pose proof bits_range as B. pose proof bits_mod32 as (_ & _ & M & _).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite (Z.mod_small ((bits * 2 ^ 52) mod 2 ^ 64) (2 ^ 64)) by (apply Z.mod_pos_bound; lia).
  rewrite <- M.
  replace (2 ^ 64) with (2 ^ 12 * 2 ^ 52) by reflexivity.
  rewrite Z.mul_mod_distr_r by lia.
  replace (2 ^ 58) with (2 ^ 52 * 2 ^ 6) by reflexivity.
  rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma ze_scsize : ltac2:(tb__ "0|0|
S3S0S96S67S68Sb3A3S75A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  unfold gm_scsize. rewrite ze_ext. cbn [Z.of_N]. rewrite ze_lbytes, ze_alu, ze_sc, ze_lit. cbn [zalu].
  change (1 mod 2 ^ 64 mod 64) with 1. rewrite zl1_1.
  pose proof R_all as R. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  rewrite (Z.mod_small (am_sc am * 2)) by lia. rewrite (Z.mul_comm (am_sc am) 2).
  rewrite table_u16 by lia. fold sz. change (Z.of_N 16) with 16.
  rewrite (Z.mod_small sz (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma ze_S : ltac2:(tb__ "0|0|
S3S0S96S67S68S115A3S75A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  unfold ff_S. rewrite ze_ext. cbn [Z.of_N]. rewrite ze_lbytes, ze_alu, ze_alu, ze135, !ze_lit. cbn [zalu].
  change (5 mod 2 ^ 64 mod 64) with 5. change (126 mod 2 ^ 64) with 126. rewrite zl1_1.
  pose proof R_all as R. pose proof bits_range as B. pose proof bits_mod32 as (_ & _ & _ & M).
  rewrite (m64_small bits) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  rewrite (Z.mod_small (bits / 32)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite M. rewrite land_126_odd by lia.
  rewrite table_u16 by lia. fold sz.
  rewrite (Z.mod_small sz (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma ze_stride : ltac2:(tb__ "0|0|
S3S0S96S67S68S11cA3S71A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  unfold ff_stride. rewrite ze_alu, ze_S, ze_lit. cbn [zalu]. change (4 mod 2 ^ 64 mod 64) with 4.
  pose proof R_all as R. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ze_mem : ltac2:(tb__ "0|0|
S3S0S96S67S68Sa3A3S8S6cZ10A2A3").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm HzA.
  unfold gm_mem_sv. rewrite ze_alu, ze12, ze_alu, ze131, ze_lit. cbn [zalu]. change (4 mod 2 ^ 64 mod 64) with 4.
  pose proof R_all as R.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  rewrite (Z.mod_small (h16 * 16)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ze_memm16 : ltac2:(tb__ "0|0|
S3S0S96S67S68S36S13aSa3S2dN10A1A3A3S6cA3").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm HzA.
  rewrite ze_alu, ze_mem, ze_lit. cbn [zalu]. pose proof R_all as R.
  change ((-16) mod 2 ^ 64) with (2 ^ 64 - 16).
  replace (zMem + 16 + (2 ^ 64 - 16)) with (zMem + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma ze_end : ltac2:(tb__ "0|0|
S3S0S96S67S68SfaA3S6fA3").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm HzA.
  unfold ff_end. rewrite ze_alu, ze_alu, ze_alu, ze_memm16, ze_stride, ze_mul, ze_stride, ze_ffidx, !ze_lit. cbn [zalu].
  change (12 mod 2 ^ 64) with 12.
  pose proof R_all as R. fold sti.
  rewrite (Z.mod_small (zMem + st)) by lia.
  rewrite (Z.mod_small sti) by lia.
  rewrite (Z.mod_small (zMem + st + sti)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma ze_area : ltac2:(tb__ "0|0|
S3S0S96S67S68S36S13cSa0P84A1S2dSa4A1A3A3S6bA3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  rewrite ze_alu, ze132, ze_lit. cbn [zalu]. pose proof R_all as R.
  rewrite (Z.mod_small zG) by lia.
  match goal with |- Z.land zG ?m = _ => replace m with (2 ^ 64 - 2 ^ 12) by reflexivity end.
  rewrite (land_high_mask zG 12) by lia. change (2 ^ 12) with 4096.
  replace zG with (24 + 40 * k + zA) by lia.
  pose proof HzA_pg as HA. unfold pg_aligned in HA.
  rewrite <- Z.add_mod_idemp_r, HA, Z.add_0_r by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma pow2_i_range : ltac2:(tb__ "0|2|
S4S4S9Z1SaZ2M0Vi;A2M1A2SbG1SaG0Z20A2A2A2S9G1SaG0Z1fA2A2A2").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  pose proof R_all as R. split; [split|].
  - apply Z.le_trans with (2 ^ 0); [lia|]. apply Z.pow_le_mono_r; lia.
  - apply Z.pow_lt_mono_r; lia.
  - apply Z.pow_le_mono_r; lia.
Qed.

Lemma ze_bit : ltac2:(tb__ "0|0|
S3S0S96S67S68Sa9A3S97SaZ2Vi;A2A1A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  unfold gm_bit. rewrite ze_aluw, ze_idx, ze_lit. cbn [zalu]. pose proof R_all as R. pose proof pow2_i_range as P.
  change (1 mod 2 ^ 64 mod 2 ^ 32) with 1. rewrite (Z.mod_small i) by lia. rewrite (Z.mod_small i) by lia.
  rewrite Z.shiftl_1_l. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma ze_self : ltac2:(tb__ "0|0|
S3S0S96S67S68SfcA3S97SaZ2Vi;A2A1A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA. exact ze_bit. Qed.

Lemma ze_sx133 : ltac2:(tb__ "0|0|
S3S0S96S67S68S3eS23Q20Sa0P85A1A3A3S97Sc2Vam;A1A1A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA. rewrite ze_ext, ze133. reflexivity. Qed.
Lemma ze_sx134 : ltac2:(tb__ "0|0|
S3S0S96S67S68S3eS23Q20Sa0P86A1A3A3S97SbfVam;A1A1A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA. rewrite ze_ext, ze134. reflexivity. Qed.

Lemma ze_mask : ltac2:(tb__ "0|0|
S3S0S96S67S68SfeA3S97S12Sc2Vam;A1SbfVam;A1A2A1A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  unfold ff_mask. rewrite ze_alu, ze_sx133, ze_sx134. cbn [zalu]. pose proof R_all as R.
  pose proof (sx32_range (am_avail am) ltac:(lia)). pose proof (sx32_range (am_freed am) ltac:(lia)).
  rewrite !Z.mod_small by lia. apply sx32_lor; lia.
Qed.

Lemma lor_range : ltac2:(tb__ "0|1|
S4S9Z0S12Sc2Vam;A1SbfVam;A1A2M0A2SbG0SaZ2Z20A2A2A2").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA. pose proof R_all as R. apply lor_bound32; lia. Qed.

Lemma lor_bit_clear : ltac2:(tb__ "0|0|
S3S1dS1aS12Sc2Vam;A1SbfVam;A1A2Vi;A2S20A3").
Proof using FFx. rewrite Z.lor_spec, (ff_avail_i _ _ _ _ _ FFx), (ff_freed_i _ _ _ _ _ FFx). reflexivity. Qed.

Lemma lor_plus_bit : ltac2:(tb__ "0|1|
SbS8S12Sc2Vam;A1SbfVam;A1A2SaZ2M0Vi;A2A2SaG0Z20A2A2").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  pose proof R_all as R. pose proof lor_range as LR. pose proof pow2_i_range as P.
  rewrite (lor_add_disjoint_bit _ i) by (try lia; apply lor_bit_clear).
  apply (lor_bound32 _ _ LR). lia.
Qed.

Lemma ze_maskself : ltac2:(tb__ "0|0|
S3S0S96S67S68S3bS13aSfeSfcA3A3S97S8S12Sc2Vam;A1SbfVam;A1A2SaZ2Vi;A2A2A1A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  rewrite ze_aluw, ze_mask, ze_self. cbn [zalu]. pose proof lor_range. pose proof pow2_i_range. pose proof lor_plus_bit.
  rewrite !sx32_mod32 by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma freed_plus_bit : ltac2:(tb__ "0|1|
SbS8SbfVam;A1SaZ2M0Vi;A2A2SaG0Z20A2A2").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  pose proof R_all as R. pose proof pow2_i_range as P.
  rewrite (lor_add_disjoint_bit _ i) by (try lia; apply (ff_freed_i _ _ _ _ _ FFx)).
  apply lor_bound32; lia.
Qed.

Lemma ze_newfreed : ltac2:(tb__ "0|0|
S3S0S96S67S68S3bS13aS3eS23Q20Sa0P86A1A3SfcA3A3S97S8SbfVam;A1SaZ2Vi;A2A2A1A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  rewrite ze_aluw, ze_sx134, ze_self. cbn [zalu]. pose proof R_all as R. pose proof pow2_i_range. pose proof freed_plus_bit.
  rewrite !sx32_mod32 by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma ze_allmask : ltac2:(tb__ "0|2|
S3S0S96S67S68S3bS13aS3bS13eS2dZ2M0A1Sa0P87A1A3S2dZffffffffffffffffA1A3A3S97SeSaG0S8Sc7Vam;A1Z1M1A2A2G1A2A1A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  rewrite ze_aluw, ze_aluw, ze135, !ze_lit. cbn [zalu]. pose proof R_all as R. pose proof bits_range as B. pose proof bits_mod32 as (M & _).
  change (2 mod 2 ^ 64 mod 2 ^ 32) with 2. change (18446744073709551615 mod 2 ^ 64 mod 2 ^ 32) with (2 ^ 32 - 1).
  replace (bits mod 2 ^ 32 mod 32) with (bits mod 32).
  2:{ rewrite <- (Znumtheory.Zmod_div_mod 32 (2 ^ 32) bits); [reflexivity|lia|lia|exists (2 ^ 27); reflexivity]. }
  rewrite M.
  assert (P : 2 <= 2 ^ (am_last am + 1) <= 2 ^ 32).
  { split; [replace 2 with (2 ^ 1) at 1 by reflexivity|]; apply Z.pow_le_mono_r; lia. }
  rewrite Z.shiftl_mul_pow2 by lia. replace (2 * 2 ^ am_last am) with (2 ^ (am_last am + 1)) by (rewrite Z.pow_add_r by lia; lia).
  assert (E : (2 ^ (am_last am + 1)) mod 2 ^ 32 + (2 ^ 32 - 1) = (2 ^ (am_last am + 1) - 1) + 1 * 2 ^ 32 \/
              (2 ^ (am_last am + 1)) mod 2 ^ 32 + (2 ^ 32 - 1) = 2 ^ (am_last am + 1) - 1).
  { destruct (Z.eq_dec (2 ^ (am_last am + 1)) (2 ^ 32)) as [E|NE].
    - right. rewrite E, Z.mod_same by lia. lia.
    - left. rewrite Z.mod_small by lia. lia. }
  rewrite sx32_mod32.
  2:{ apply Z.mod_pos_bound. lia. }
  destruct E as [E|E]; rewrite E; [rewrite Z.mod_add by lia|]; rewrite Z.mod_small by lia; reflexivity.
Qed.

Hypothesis Hsp : ltac2:(tb__ "0|1|
S4S9Z1000Sb6Q40S39Vrho;PaA2A2M0A2S3S0SdG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S4S9S99Z40Sb6Q40S39Vrho;PfA2A2A2M0N1d0A2S9S13SaZ2Z28A2A1G0A2A2").

Definition kv : ff_kind := ltac2:(tb__ "0|0|
S1dSf7L_;SfSc5Vam;A1Z0A2S110S10fX1dx2").
Definition rvv : ff_rsv := ltac2:(tb__ "0|2|
S1dSf6L_;M0SfS6eZ0A2S111G0S15S6eZ5M1A2S112G0SfS6eG1A2S113S114X1dx2X1dx2X1dx2").

Ltac zfact := cbn [zholds zcond].

Lemma zr1_10 : ltac2:(tb__ "0|1|
S3S0S67PaM0A1Sb6Q40S39Vrho;G0A2A2A3"). Proof using . reflexivity. Qed.
Lemma zr1_139 : ltac2:(tb__ "0|0|
S3S0S67P8bA1Sb6Q40S39Vrho;PfA2A2A3"). Proof using . reflexivity. Qed.

Lemma ZF_common : ltac2:(tb__ "0|0|
Sf0S2eS98S67S68A2SaaA3").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm Hsp HzA.
  pose proof R_all as R. pose proof Hh3_range. unfold gm_facts_common.
  constructor. { zfact. rewrite zr1_12. split; [lia|]. rewrite (Z.mod_small zP (2 ^ 64)) by lia.
                 pose proof HzP16 as P. change (2 ^ 4) with 16. exact P. }
  constructor. { zfact. rewrite ze130, ze_lit. change (255 mod 2 ^ 64) with 255. lia. }
  constructor. { zfact. rewrite ze131, ze_lit. change (65535 mod 2 ^ 64) with 65535. lia. }
  constructor. { zfact. rewrite ze_last, ze_idx. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze_alu, ze_sx133, ze_bit, ze_lit. cbn [zalu]. pose proof pow2_i_range.
                 pose proof (sx32_range (am_avail am) ltac:(lia)). pose proof (sx32_range (2 ^ i) ltac:(lia)).
                 rewrite !Z.mod_small by lia. rewrite sx32_land by lia.
                 rewrite land_pow2_testbit, (ff_avail_i _ _ _ _ _ FFx) by lia. reflexivity. }
  constructor. { zfact. rewrite ze_alu, ze_sx134, ze_bit, ze_lit. cbn [zalu]. pose proof pow2_i_range.
                 pose proof (sx32_range (am_freed am) ltac:(lia)). pose proof (sx32_range (2 ^ i) ltac:(lia)).
                 rewrite !Z.mod_small by lia. rewrite sx32_land by lia.
                 rewrite land_pow2_testbit, (ff_freed_i _ _ _ _ _ FFx) by lia. reflexivity. }
  constructor.
Qed.

Lemma h16_bounds : ltac2:(tb__ "0|1|
S4S9ScS75Vi;A2M0S73A2SbS73S8G0S75A2A2A2").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  pose proof R_all as R. clear HQ HLok Harea Hmem_pg HP12 Hrgm HzA Hsp Hdepth.
  assert (E : sti = 16 * (sz * i)) by (unfold sti; lia).
  lia.
Qed.

Lemma szi_range : ltac2:(tb__ "0|1|
S4S9Z0ScS75Vi;A2M0A2SbS8G0S75A2SaZ2Z3eA2A2A2").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  pose proof R_all as R. clear HQ HLok Harea Hmem_pg HP12 Hrgm HzA Hsp Hdepth.
  assert (E : sti = 16 * (sz * i)) by (unfold sti; lia). lia.
Qed.

Lemma ZF_sized : ltac2:(tb__ "0|0|
Sf0S2eS98S67S68A2SadA3").
Proof using FFx HQ Harea Hmem_pg Hrgm Hsp HzA.
  pose proof R_all as R. pose proof h16_bounds. pose proof szi_range. unfold gm_facts_sized.
  constructor. { zfact. rewrite ze_lit, ze_sc. change (47 mod 2 ^ 64) with 47. rewrite Z.ltb_lt. lia. }
  constructor. { zfact. rewrite ze131, ze_mul, ze_scsize, ze_idx. rewrite Z.mod_small by lia.
                 apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze131, ze_mul, ze_alu, ze_idx, ze_lit, ze_scsize. cbn [zalu]. change (1 mod 2 ^ 64) with 1.
                 rewrite (Z.mod_small (i + 1)) by lia. rewrite Z.mod_small by nia.
                 rewrite Bool.negb_true_iff. intros E. apply Z.ltb_ge in E. nia. }
  constructor.
Qed.

Lemma ZF_nomap : ltac2:(tb__ "0|0|
S3S0Sc5Vam;A1Z0A3Sf0S2eS98S67S68A2SacA3F_;").
Proof using FFx HQ Hmem_pg Hrgm.
  intros Hm. unfold gm_facts_nomap. constructor; [|constructor].
  zfact. rewrite ze_maplen, ze_lit, Hm. reflexivity.
Qed.

Lemma maplen_h16 : ltac2:(tb__ "0|1|
SbZ0Sc5Vam;A1M0A2SbS8S73Z1A2ScG0Z100A2A2F_;").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA.
  intros Hm. pose proof Hreg as (Ho & He & HM). destruct (HM Hm) as [P0 L0].
  pose proof R_all as R. clear HQ HLok Harea Hmem_pg HP12 Hrgm HzA Hsp Hdepth HM.
  unfold PGSZ, IB in *. lia.
Qed.

Lemma ZF_map : ltac2:(tb__ "0|0|
SbZ0Sc5Vam;A1A2Sf0S2eS98S67S68A2SabA3F_;").
Proof using FFx HQ Harea Hmem_pg Hrgm Hsp HzA.
  intros Hm. pose proof (maplen_h16 Hm). pose proof R_all as R. pose proof bits_range. unfold gm_facts_map.
  constructor. { zfact. rewrite ze_maplen, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. lia. }
  constructor. { zfact. rewrite ze_alu, ze_alu, ze_maplen, !ze_lit, ze131. cbn [zalu].
                 change (8 mod 2 ^ 64 mod 64) with 8. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
                 rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
                 assert (B : am_maplen am * 256 < 2 ^ 60) by (rewrite Hbits in *; lia).
                 rewrite (Z.mod_small (am_maplen am * 256)) by lia.
                 replace (am_maplen am * 256 + (2 ^ 64 - 1)) with ((am_maplen am * 256 - 1) + 1 * 2 ^ 64) by lia.
                 rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
                 apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor.
Qed.

Lemma ZF_depth : ltac2:(tb__ "0|0|
Sf0S2eS98S67S68A2S117A3").
Proof using Hdepth.
  destruct Hdepth as [D1 D2]. unfold ff_facts_depth.
  constructor. { zfact. rewrite ze_lit, ze_v, zr1_139. rewrite (toS_mod 64 (bv_unsigned (rw rho 15%positive))) by lia.
                 replace (toS 64 ((-48) mod 2 ^ 64)) with (-48) by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze_lit, ze_v, zr1_139. rewrite (toS_mod 64 (bv_unsigned (rw rho 15%positive))) by lia.
                 replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor.
Qed.

Lemma ZF_kind : ltac2:(tb__ "0|0|
Sf0S2eS98S67S68A2S108S76A1A3").
Proof using FFx HP12 HQ Harea Hdepth Hmem_pg Hrgm Hsp HzA.
  unfold ff_facts_kind, kv. pose proof R_all as R.
  destruct (am_maplen am =? 0) eqn:E.
  - apply Z.eqb_eq in E. apply Forall_app. split; [|apply ZF_depth].
    unfold gm_facts. apply Forall_app. split; [apply ZF_common|]. apply Forall_app. split; [apply ZF_sized|apply ZF_nomap; exact E].
  - apply Z.eqb_neq in E. apply Forall_app. split; [|apply ZF_depth].
    apply Forall_app. split.
    + unfold gm_facts. apply Forall_app. split; [apply ZF_common|]. apply Forall_app. split; [apply ZF_sized|apply ZF_map; lia].
    + constructor; [|constructor]. zfact. rewrite ze_alu, ze135, !ze_lit. cbn [zalu]. change (31 mod 2 ^ 64) with 31. change (0 mod 2 ^ 64) with 0.
      pose proof bits_range. rewrite (Z.mod_small bits) by lia. rewrite land_31. rewrite (proj1 bits_mod32). rewrite Z.eqb_eq. lia.
Qed.

Lemma ze_end_minus_p : ltac2:(tb__ "0|0|
S3S0S96S67S68S36S13dSfaSa0PcA1A3A3S8S6dS6eA2A3").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm Hsp HzA.
  rewrite ze_alu, ze_end, ze12. cbn [zalu]. pose proof R_all as R. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ZF_rsv : ltac2:(tb__ "0|0|
Sf0S2eS98S67S68A2S109S70A1A3").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm Hsp HzA.
  pose proof R_all as R. pose proof Hh3 as H3. pose proof rsv_range. unfold ff_facts_rsv, rvv.
  destruct (rsv =? 0) eqn:E0; [|destruct (rsv <? 5) eqn:E5; [|destruct (rsv =? 5) eqn:E55]].
  - apply Z.eqb_eq in E0. rewrite E0 in H3. rewrite Z.min_l in H3 by lia.
    constructor. { zfact. rewrite ze130, ze_lit. change (31 mod 2 ^ 64) with 31. lia. }
    constructor. { zfact. rewrite ze_end_minus_p, ze_lit. change (0 mod 2 ^ 64) with 0. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
    constructor.
  - apply Z.eqb_neq in E0. apply Z.ltb_lt in E5. rewrite Z.min_l in H3 by lia.
    constructor. { zfact. rewrite ze130, ze_lit. change (160 mod 2 ^ 64) with 160. apply Z.ltb_lt. lia. }
    constructor. { zfact. rewrite ze_code, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.min_l by lia. rewrite Z.eqb_eq. lia. }
    constructor. { zfact. rewrite ze_end_minus_p, ze_code. rewrite Z.min_l by lia. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
    constructor.
  - apply Z.ltb_ge in E5. apply Z.eqb_eq in E55. rewrite Z.min_r in H3 by lia.
    constructor. { zfact. rewrite ze130, ze_lit. change (160 mod 2 ^ 64) with 160. rewrite Z.ltb_lt. lia. }
    constructor. { zfact. rewrite ze_code, ze_lit. change (5 mod 2 ^ 64) with 5. rewrite Z.min_r by lia. reflexivity. }
    constructor. { zfact. rewrite ze_end_minus_p, ze_lit. change (5 mod 2 ^ 64) with 5. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
    constructor.
  - apply Z.ltb_ge in E5. apply Z.eqb_neq in E55. rewrite Z.min_r in H3 by lia.
    constructor. { zfact. rewrite ze130, ze_lit. change (160 mod 2 ^ 64) with 160. rewrite Z.ltb_lt. lia. }
    constructor. { zfact. rewrite ze_code, ze_lit. change (5 mod 2 ^ 64) with 5. rewrite Z.min_r by lia. reflexivity. }
    constructor. { zfact. rewrite ze137, ze_lit. change (4294967295 mod 2 ^ 64) with 4294967295. lia. }
    constructor. { zfact. rewrite ze_lit, ze137. change (4 mod 2 ^ 64) with 4. apply Z.ltb_lt. lia. }
    constructor. { zfact. rewrite ze_end_minus_p, ze137. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
    constructor.
Qed.

Lemma ZF_quick : ltac2:(tb__ "0|0|
Sf0S2eS98S67S68A2S118A3").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm Hsp HzA.
  pose proof R_all as R. pose proof lor_range as LR. pose proof pow2_i_range as P2. pose proof lor_plus_bit as LP.
  destruct HQ as (_ & _ & _ & Hfz & Hall & _). destruct Hsp as [S1 S2].
  unfold ff_facts_quick.
  constructor. { zfact. rewrite ze_alu, ze_mask, ze_self, ze_lit. cbn [zalu]. change (0 mod 2 ^ 64) with 0.
                 pose proof (sx32_range _ LR). pose proof (sx32_range (2 ^ i) ltac:(lia)).
                 rewrite !Z.mod_small by lia. rewrite sx32_land by lia.
                 rewrite land_pow2_testbit, lor_bit_clear by lia. reflexivity. }
  constructor. { zfact. rewrite ze_sx134, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq.
                 intros E. apply Hfz. apply (sx32_zero_iff (am_freed am)); lia. }
  constructor. { zfact. rewrite ze_maskself, ze_allmask. rewrite Z.eqb_eq. intros E.
                 apply sx32_inj in E; [|lia|].
                 2:{ assert (2 ^ (am_last am + 1) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
                     assert (1 <= 2 ^ (am_last am + 1)) by (apply Z.le_trans with (2 ^ 0); [lia|apply Z.pow_le_mono_r; lia]). lia. }
                 apply Hall. unfold bit, ones. rewrite Z.lor_comm. exact E. }
  constructor. { zfact. rewrite ze_alu, ze_alu, ze135, !ze_lit. cbn [zalu].
                 change (5 mod 2 ^ 64 mod 64) with 5. change (126 mod 2 ^ 64) with 126. change (94 mod 2 ^ 64) with 94.
                 pose proof bits_range as B. pose proof bits_mod32 as (_ & _ & _ & M).
                 rewrite (Z.mod_small bits) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
                 rewrite (Z.mod_small (bits / 32)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
                 rewrite M, land_126_odd by lia. lia. }
  constructor. { zfact. rewrite zr1_10. split; [lia|]. rewrite (Z.mod_small (bv_unsigned (rw rho 10%positive)) (2 ^ 64)) by (pose proof (urange (rw rho 10%positive)); lia).
                 change (2 ^ 4) with 16. exact S2. }
  constructor. { zfact. rewrite ze_lit, ze_var, zr1_10. change (4096 mod 2 ^ 64) with 4096.
                 rewrite (Z.mod_small (bv_unsigned (rw rho 10%positive)) (2 ^ 64)) by (pose proof (urange (rw rho 10%positive)); lia). lia. }
  constructor. { zfact. rewrite ze12, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. lia. }
  constructor.
Qed.

Theorem ZF_all : ltac2:(tb__ "0|0|
Sf0S2eS98S67S68A2S43Sf9Sf8S76S70A3A1A3").
Proof using FFx HP12 HQ Harea Hdepth Hmem_pg Hrgm Hsp HzA.
  cbn [Pre_free_fast ss_facts]. apply Forall_app. split; [apply ZF_kind|]. apply Forall_app. split; [apply ZF_rsv|apply ZF_quick].
Qed.

Theorem facts_hold : ltac2:(tb__ "0|0|
Sb4Q40A1S1fSb4Q8A1A1F_;Sf0S2eS54S69R1A1A1S43Sf9Sf8S76S70A3A1A3Fm;").
Proof using FFx HP12 HQ Harea Hdepth Hmem_pg Hrgm Hsp HzA.
  intros m. apply Forall_holds_of_zholds.
  - unfold kv, rvv. destruct (am_maplen am =? 0), (rsv =? 0); [| destruct (rsv <? 5); [|destruct (rsv =? 5)] | | destruct (rsv <? 5); [|destruct (rsv =? 5)]]; vm_compute; reflexivity.
  - apply Forall_forall. intros f Hf. apply (proj1 (zholds_ext zr1 (zr_of (rho1 m)) zl1 (zl_of (rho1 m)) f ltac:(intros; reflexivity) ltac:(intros; reflexivity))).
    exact (proj1 (Forall_forall _ _) ZF_all f Hf).
Qed.

Let m0 : word -> option byte := rm rho.
Variable vm : VmMaps.
Hypothesis HMI : ltac2:(tb__ "0|0|
S184S154S183Vs;VL;A2S14cS8fVm0;A2S14dS8fVm0;A2Vvm;A5").
Variable m1 : word -> option byte.
Hypothesis Hm1 : ltac2:(tb__ "0|2|
Sb4Q40M0A1S7S4S9S6aSb6G0R1A2M1A2SbG1S8S6aS6dA2A2A2A1S3S1fSb4Q8A1A1Vm1;R2A1Vm0;R2A1A3F_;Fw;").
Hypothesis Hfr : ltac2:(tb__ "0|2|
S11dS22S22S22SbeSc0A2M0S0A2M1Sc1A2S1eG1Sc1S1eG0S0S1eSbeSc0Vg;Vam;A4Vi;A4Vfr;A4S12bVs;A1A3").
Hypothesis Hblock : ltac2:(tb__ "0|0|
S11dS22SbeS0A2S1eSbeS0S89S6dA4S131Vs;A1A3").

Let bv0 : byteview := ltac2:(tb__ "0|0|
S155S14cS8fVm0;A2S14dS8fVm0;A2A2").

Lemma HW : WF s. Proof using HMI. exact (proj1 HMI). Qed.
Lemma HreprP : ltac2:(tb__ "0|0|
S180VL;Vs;Vbv0;A3"). Proof using HMI. exact (proj1 (proj2 (proj2 (proj2 HMI)))). Qed.
Lemma Hstat : ltac2:(tb__ "0|0|
S157S154S155S14cS8fVm0;A2Sb4Q40A1S23L_;A2Vbv0;A3").
Proof using HMI. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HMI)))))). Qed.

Lemma m1_eq : ltac2:(tb__ "0|1|
S0S4S9Z0R1A2SbR1SaZ2Z40A2A2A2S7S4S9S6aR2A2SbR2S8S6aS6dA2A2A2A1S3S1fSb4Q8A1A1Vm1;Sb5Q40R3A2M0A1Vm0;G0A1A3F_;F_;Fx;").
Proof using Hm1. intros x Hx Hnb. apply Hm1. rewrite u64 by exact Hx. exact Hnb. Qed.

Lemma rd1_eq : ltac2:(tb__ "0|1|
S0S4S9Z0R1A2SbR1SaZ2Z40A2A2A2S7S4S9S6aR2A2SbR2S8S6aS6dA2A2A2A1S4S3S1fSb4Q8A1A1S14cS8fVm1;Sb5Q40R3A2M0A3S14cS8fVm0;G0A3A3S3S1dS14dS8fVm1;G0A3S14dS8fVm0;G0A3A3A2F_;F_;Fx;").
Proof using Hm1. intros x Hx Hnb. unfold Glue.rd_of, Glue.wok_of. rewrite (m1_eq x Hx Hnb). auto. Qed.

Lemma cell_bytes1 : ltac2:(tb__ "0|4|
S122S0S5S11dS122R2S126Vs;A1A3S11dS122R2S17eVs;A1A3A2S3S1fS0A1S192VL;R3A2S26S0R2A2A3S24S190R1S12aR5A1A2S4S4S9Z0S8S127VL;S12dR6A1A2S11R2A1A2M0A2SbG0SaZ2Z40A2A2A2S4S3S1dS14dS8fVm1;Sb5Q40G0A2M1A3S23A3S3S1fSb4Q8M2A1M3A1S14cS8fVm1;G1A3S26G3Sb5G2S137R5S12aR6A1R2A3A2A2A3A2A2F_;Fj;F_;F_;Fz;Fc;").
Proof using HLok HMI Hblock Hm1 Hsp bv0.
  intros c z Hc Hz j Hj.
  assert (CH : MallocInv.cell_holds L bv0 c).
  { destruct Hc as [Hc|Hc].
    - exact (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 HreprP))) c Hc).
    - exact (proj1 (Forall_forall _ _) (proj2 HreprP) c Hc). }
  destruct (cell_bytes L _ _ c z CH Hz j Hj) as (R & W & B).
  assert (D : MallocInv.ranges_disjoint (cell_range L c) (block_range L (p, n))).
  { destruct Hc as [Hc|Hc].
    - exact (image_outside_user_blocks s L c (p, n) HW HLok Hc Hblock).
    - exact (footer_outside_user_blocks s L c (p, n) HW HLok Hc Hblock). }
  unfold MallocInv.ranges_disjoint, cell_range, block_range in D. cbn [fst snd] in D. fold zP in D. unfold addr_of in D.
  change (loc_addr L (LMem p)) with zP in D.
  destruct (rd1_eq (loc_addr L (mc_loc c) + Z.of_nat j) R ltac:(lia)) as [E1 E2].
  rewrite E1, E2. auto.
Qed.

Lemma cell_rw1 : ltac2:(tb__ "0|3|
S122S0S0S0S24S5S11dS122R5S126Vs;A1A3S11dS122R5S17eVs;A1A3A2S3S1fS0A1S192VL;R6A2S26S0R5A2A3S3S24S12aR7A1R3A3S3S0S127VL;S12dR8A1A2S8R6R5A2A3S0S4S9S8R8R7A2M0R1A2SbR1S8G0S11R6A1A2A2A2S4S3S1dS14dS8fVm1;Sb5Q40M1R2A2A3S23A3S6Sb4Q8A1M2G2S3S1fG2A1S14cS8fVm1;Sb5G1R3A2A3S26G2R1A2A3Lbb;A2A2F_;Fx;F_;F_;F_;F_;Fkk;Foff;Fb;Fz;Fc;").
Proof using HLok HMI Hblock Hm1 Hsp bv0.
  intros c z b off kk Hc Hz Hw Ha x Hx.
  destruct (cell_bytes1 c z Hc Hz (Z.to_nat (x - (b + off))) ltac:(rewrite Hw; lia)) as (_ & W & R).
  rewrite Ha in W, R. rewrite Z2Nat.id in W, R by lia. replace (b + off + (x - (b + off))) with x in W, R by lia.
  split; [exact W | eexists; exact R].
Qed.

Lemma ev1 : ltac2:(tb__ "0|2|
Sb4Q40M0A1M1S1fSb4Q8A1A1F_;S31S3S1dS9aR1A1S23A3S3G1S44S69R3A1R2A2Sb5G0S96S67S68R2A3A2A3F_;Fe;Fm;").
Proof using .
  intros m e He. rewrite <- (zr1_zl1_any m). rewrite <- (eval_zeval (rho1 m) e He). symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma ev1u : ltac2:(tb__ "0|1|
Sb4Q40M0A1S1fSb4Q8A1A1F_;S31S3S1dS9aR1A1S23A3S3S0Sb6G0S44S69R3A1R2A2A2S96S67S68R2A3A3F_;Fe;Fm;").
Proof using . intros m e He. rewrite <- (zr1_zl1_any m). apply eval_zeval. exact He. Qed.

Definition Eg : loc * Z := ltac2:(tb__ "0|0|
S1eS124S0S125Sd8SccSc3Vam;A1A1Z0A2A1Sc6Vrgm;A1A4").
Definition Ea : loc * Z := ltac2:(tb__ "0|0|
S1eS124S0S125Va;A1Sc4A4").
Definition Ec : loc * Z := ltac2:(tb__ "0|0|
S1eS124S0S12eZ0A1S132A4").

Lemma Eg_in : In Eg (footprint s).
Proof using FFx Hrgm.
  destruct (ff_region _ _ _ _ _ FFx) as (rg & Hr & Hk & Hl & _). destruct Hrgm as [Hr' _]. rewrite Hr in Hr'. injection Hr' as ->.
  unfold Eg. apply footprint_region_In; assumption.
Qed.
Lemma Ea_in : In Ea (footprint s).
Proof using Harea Hdepth Hrgm Hsp HzA. unfold Ea, footprint. right. apply in_app_iff. left. apply in_map_iff. exists a. split; [reflexivity|]. tauto. Qed.
Lemma Ec_in : In Ec (footprint s).
Proof using . left. reflexivity. Qed.

Lemma Eg_addr : ltac2:(tb__ "0|0|
S4S3S0S127VL;S2aS124S0S88A3A2SeS6cSc8Sc3Vam;A1A1A2A3S3S0S2bS124S0S88A3Sc6Vrgm;A1A3A2").
Proof using Hmem_pg Hrgm rho. unfold Eg, zMem, addr_of, loc_addr. destruct (am_mem am) as [r o]. cbn [fst snd prid poff]. lia. Qed.
Lemma Ea_addr : ltac2:(tb__ "0|0|
S4S3S0S127VL;S2aS124S0S87A3A2S6bA3S3S0S2bS124S0S87A3Sc4A3A2").
Proof using . unfold Ea, zA, addr_of. cbn [fst snd]. auto. Qed.

Lemma cell_view1 : ltac2:(tb__ "0|4|
S122S0S0S0S24S31S5S11dS122R6S126Vs;A1A3S11dS122R6S17eVs;A1A3A2S3S1fS0A1S192VL;R7A2S26S0R6A2A3S3S24S12aR8A1R4A3S191R5U8A2S3S0S127VL;S12dRaA1A2S8R8R7A2A3S3Sb4Q40M0A1S44S69Vm1;A1M1R6A2Sb5G0RaA2A3S24S190R1R9A2S3S1fSb4Q8M2A1M3A1S14cS8fVm1;Sb5G0S8S8RcRbA2S11R2A1A2A2A3S26G3Sf2G3R2S5dRaS44G1R9A2A2Sb5G2Z0A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;Fe;Fkk;Foff;Fb;Fz;Fc;").
Proof using HLok HMI Hblock Hm1 Hsp.
  intros c z b off kk e Hc Hz Hw Hk Ha He j Hj.
  destruct (cell_bytes1 c z Hc Hz j ltac:(rewrite Hw; exact Hj)) as (_ & _ & R).
  rewrite Ha in R. rewrite R, He, Hw. rewrite nth_enc_bytes by assumption. reflexivity.
Qed.

Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.

Definition O_hdr : sobj := ltac2:(tb__ "0|3|
S32Sa0PcA1S2dN4A1M0S2dZ0A1M1S1bS30S33G0Z1M2G1A3S1bS30S33S2dN3A1G2Sa0P82A1A3S1bS30S33S2dN2A1Z2Sa0P83A1A3S1cS30A1A3A3A3S35A5").
Definition O_grp : sobj := ltac2:(tb__ "0|1|
S32Sa3S2dN10A1M0S2dN8A1S1bS30S33G0Z8Sa0P84A1A3S1cS30A1A3S35A5").
Definition O_meta : sobj := ltac2:(tb__ "0|3|
S32Sa0P84A1S2dZ10A1M0S2dZ28A1S1bS30S33G0Z8M1S36S13aSa3S2dN10A1A3A3S1bS30S33S2dZ18A1Z4M2Sa0P85A1A3S1bS30S33S2dZ1cA1G2Sa0P86A1A3S1bS30S33S2dZ20A1G1Sa0P87A1A3S1cS30A1A3A3A3A3S35A5").
Definition O_area : sobj := ltac2:(tb__ "0|2|
S32S36S13cSa0P84A1S2dSa4A1A3S2dZ0A1M0S2dZ8M1A1S1bS30S33G0G1Sa0P88A1A3S1cS30A1A3S35A5").
Definition O_ctx : sobj := ltac2:(tb__ "0|2|
S32S2dZ5a3d0A1S2dZ0A1M0S2dZ8M1A1S1bS30S33G0G1Sa0P88A1A3S1cS30A1A3S35A5").
Definition O_libc : sobj := ltac2:(tb__ "0|2|
S32S2dS8Z5a358Z3A2A1S2dZ0A1M0S2dZ1M1A1S1bS30S33G0G1G0A3S1cS30A1A3S35A5").
Definition O_lock : sobj := ltac2:(tb__ "0|2|
S32S2dZ5a3c8A1S2dZ0A1M0S2dZ4M1A1S1bS30S33G0G1G0A3S1cS30A1A3S35A5").
Definition O_sctab : sobj := ltac2:(tb__ "0|0|
S32S2dZ108ecA1S2dZ0A1S2dZ60A1S1cS30A1S4eSa2A1A5").

Lemma ff_objs_common_eq : ltac2:(tb__ "0|0|
S3S21S2fA1S11bSf8A1S1bS2fS32S34PaA1Sa0P8bA1S2dZ0A1S1cS30A1S35A5S1bS2fS7fS1bS2fS7aS1bS2fS82S1bS2fS7dS1bS2fS7eS1bS2fS80S1bS2fS81S1cS2fA1A3A3A3A3A3A3A3A3A3").
Proof using . reflexivity. Qed.

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.

Lemma hold_hdr : ltac2:(tb__ "0|0|
S3cS8fS69Vm1;A1S14aVms;Vm1;A2S7fA4").
Proof using FFx HLok HMI HP12 HQ Harea Hblock Hfr Hm1 Hmem_pg Hrgm Hrom Hsp HzA.
  pose proof R_all as R. pose proof Hreg as (Ho & He & _). pose proof Eg_addr as [GA GL].
  pose proof (quick_cells s g am i fr HW Hfr Hkind) as QC. cbn beta in QC.
  destruct QC as (C1 & C2 & C3 & _).
  change O_hdr with (carved (v 12) (-4) 0 [((-4), 1%nat, SLit 0); ((-3), 1%nat, v 130); ((-2), 2%nat, v 131)]).
  assert (B : bv_unsigned (eval (rho1 m1) (v 12)) = zP) by (rewrite ev1u by reflexivity; apply ze12).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros off Hoff.
    destruct (Z_lt_dec off (-3)) as [O1|O1]; [|destruct (Z_lt_dec off (-2)) as [O2|O2]].
    + apply (cell_rw1 _ 0 zP (-4) 1 (or_introl C1) eq_refl eq_refl); [|lia].
      cbn [mc_loc]. unfold zP, addr_of, loc_addr, p. destruct (frame_ptr am i fr) as [r o]; cbn [padd]; lia.
    + apply (cell_rw1 _ h3 zP (-3) 1 (or_introl C2) eq_refl eq_refl); [|lia].
      cbn [mc_loc]. unfold zP, addr_of, loc_addr, p. destruct (frame_ptr am i fr) as [r o]; cbn [padd]; lia.
    + apply (cell_rw1 _ h16 zP (-2) 2 (or_introl C3) eq_refl eq_refl); [|lia].
      cbn [mc_loc]. unfold zP, addr_of, loc_addr, p. destruct (frame_ptr am i fr) as [r o]; cbn [padd]; lia.
  - unfold cells_in_view. constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (cell_view1 _ 0 zP (-4) 1 (SLit 0) (or_introl C1) eq_refl eq_refl ltac:(lia)).
      * cbn [mc_loc]. unfold zP, addr_of, loc_addr, p. destruct (frame_ptr am i fr) as [r o]; cbn [padd]; lia.
      * reflexivity.
    + apply (cell_view1 _ h3 zP (-3) 1 (v 130) (or_introl C2) eq_refl eq_refl ltac:(lia)).
      * cbn [mc_loc]. unfold zP, addr_of, loc_addr, p. destruct (frame_ptr am i fr) as [r o]; cbn [padd]; lia.
      * rewrite ev1 by reflexivity. rewrite ze130. reflexivity.
    + apply (cell_view1 _ h16 zP (-2) 2 (v 131) (or_introl C3) eq_refl eq_refl ltac:(lia)).
      * cbn [mc_loc]. unfold zP, addr_of, loc_addr, p. destruct (frame_ptr am i fr) as [r o]; cbn [padd]; lia.
      * rewrite ev1 by reflexivity. rewrite ze131. reflexivity.
Qed.

Lemma Ea_Eg_disjoint : ltac2:(tb__ "0|1|
S5S9S8S6bSc4A2SeS6cSc8Sc3Vam;A1A1A2M0A2S9S8G0Sc6Vrgm;A1A2S6bA2A2").
Proof using FFx HLok HMI Harea Hdepth Hmem_pg Hrgm Hsp HzA.
  pose proof Eg_addr as [GA GL]. pose proof Ea_addr as [AA AL].
  assert (NE : Ea <> Eg).
  { unfold Ea, Eg. intros E. injection E as E1 E2.
    destruct Harea as (Ha & _). destruct (proj1 (proj2 (inv_areas HW)) a Ha) as (r & o & rga & Er & _ & _ & Hra & _ & _ & Hkind).
    destruct (ff_region _ _ _ _ _ FFx) as (rg & Hr & Hk & _).
    rewrite Er in E1. injection E1 as Er' Eo. subst r. rewrite Hr in Hra. injection Hra as <-. rewrite Hk in Hkind. exact Hkind. }
  destruct HLok as (_ & _ & PW & _).
  destruct (pairwise_map_In _ (crange L) (footprint s) Ea Eg PW Ea_in Eg_in NE) as [DD|DD];
    unfold MallocInv.ranges_disjoint, crange in DD; rewrite GA, AA in DD; cbn [fst snd] in DD; rewrite ?AL, ?GL in DD; lia.
Qed.

Lemma block_in_Eg : ltac2:(tb__ "0|1|
S4S9SeS6cSc8Sc3Vam;A1A1A2M0S6aA2S9S8S6aS6dA2S8G0Sc6Vrgm;A1A2A2A2").
Proof using FFx HQ Harea Hmem_pg Hrgm Hsp HzA. pose proof R_all as R. pose proof Hreg as (Ho & He & _). unfold IB in He. lia. Qed.

Lemma hold_grp : ltac2:(tb__ "0|0|
S3cS8fS69Vm1;A1S14aVms;Vm1;A2S7aA4").
Proof using FFx HLok HMI HP12 HQ Harea Hblock Hfr Hm1 Hmem_pg Hrgm Hrom Hsp HzA.
  pose proof R_all as R. pose proof Hreg as (Ho & He & _). pose proof Eg_addr as [GA GL].
  pose proof (quick_cells s g am i fr HW Hfr Hkind) as QC. cbn beta in QC.
  destruct QC as (_ & _ & _ & C4 & _).
  change O_grp with (carved gm_mem_sv (-16) (-8) [((-16), 8%nat, v 132)]).
  assert (B : bv_unsigned (eval (rho1 m1) gm_mem_sv) = zMem + 16) by (rewrite ev1u by reflexivity; apply ze_mem).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros off Hoff. apply (cell_rw1 _ zG (zMem + 16) (-16) 8 (or_introl C4) eq_refl eq_refl); [|lia].
    cbn [mc_loc]. unfold zMem, addr_of. lia.
  - unfold cells_in_view. constructor; [|constructor].
    apply (cell_view1 _ zG (zMem + 16) (-16) 8 (v 132) (or_introl C4) eq_refl eq_refl ltac:(lia)).
    + cbn [mc_loc]. unfold zMem, addr_of. lia.
    + rewrite ev1 by reflexivity. rewrite ze132. reflexivity.
Qed.

Lemma hold_meta : ltac2:(tb__ "0|0|
S3cS8fS69Vm1;A1S14aVms;Vm1;A2S82A4").
Proof using FFx HLok HMI HP12 HQ Harea Hblock Hdepth Hfr Hm1 Hmem_pg Hrgm Hrom Hsp HzA.
  pose proof R_all as R. pose proof Ea_addr as [AA AL]. pose proof Ea_Eg_disjoint as D. pose proof block_in_Eg as BE.
  pose proof (quick_cells s g am i fr HW Hfr Hkind) as QC. cbn beta in QC.
  destruct QC as (_ & _ & _ & _ & C5 & C6 & C7 & C8 & _).
  change O_meta with (carved (v 132) 16 40 [(16, 8%nat, SAlu ALU_ADD gm_mem_sv (SLit (-16))); (24, 4%nat, v 133); (28, 4%nat, v 134); (32, 8%nat, v 135)]).
  assert (B : bv_unsigned (eval (rho1 m1) (v 132)) = zG) by (rewrite ev1u by reflexivity; apply ze132).
  assert (AG : forall d, loc_addr L (LMem (padd g d)) = zG + d) by (intros d; unfold zG, addr_of, loc_addr; destruct g; cbn [padd]; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros off Hoff.
    destruct (Z_lt_dec off 24) as [O1|O1]; [|destruct (Z_lt_dec off 28) as [O2|O2]; [|destruct (Z_lt_dec off 32) as [O3|O3]]].
    + apply (cell_rw1 _ zMem zG 16 8 (or_introl C5) eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw1 _ (am_avail am) zG 24 4 (or_introl C6) eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw1 _ (am_freed am) zG 28 4 (or_introl C7) eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw1 _ bits zG 32 8 (or_introl C8) eq_refl eq_refl); [apply AG|lia].
  - unfold cells_in_view. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply (cell_view1 _ zMem zG 16 8 _ (or_introl C5) eq_refl eq_refl ltac:(lia)); [apply AG|].
      rewrite ev1 by reflexivity. rewrite ze_memm16. reflexivity.
    + apply (cell_view1 _ (am_avail am) zG 24 4 _ (or_introl C6) eq_refl eq_refl ltac:(lia)); [apply AG|].
      rewrite ev1 by reflexivity. rewrite ze133. reflexivity.
    + apply (cell_view1 _ (am_freed am) zG 28 4 _ (or_introl C7) eq_refl eq_refl ltac:(lia)); [apply AG|].
      rewrite ev1 by reflexivity. rewrite ze134. reflexivity.
    + apply (cell_view1 _ bits zG 32 8 _ (or_introl C8) eq_refl eq_refl ltac:(lia)); [apply AG|].
      rewrite ev1 by reflexivity. rewrite ze135. reflexivity.
Qed.

Lemma secret_cells : ltac2:(tb__ "0|2|
S4S11dS122S128S125Va;A1U8M0S12fA3S126Vs;A1M1A3S11dS122S128S12eS133A1G0S12fA3G1A3A2").
Proof using HMI HQ Harea Hfr Hsp.
  pose proof (quick_cells s g am i fr HW Hfr Hkind) as QC. cbn beta in QC.
  destruct QC as (_ & _ & _ & _ & _ & _ & _ & _ & (a' & k' & Ha' & Hk' & E' & Ca & Cc) & _).
  destruct Harea as (Ha & Hk & E & Hal & _).
  assert (Ea' : a' = a /\ k' = k).
  {
    rewrite E in E'. destruct a as [r o], a' as [r' o']. cbn [padd] in E'. injection E' as Er Eo. subst r'.
    unfold pg_aligned in Hal. cbn [poff] in Hal.
    destruct (proj1 (proj2 (inv_areas HW)) _ Ha') as (r2 & o2 & rga & Er2 & Hal' & _). injection Er2 as _ Eo2. subst o2.
    unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *.
    assert (o' = o) by lia. subst o'. split; [reflexivity|lia]. }
  destruct Ea' as [-> ->]. auto.
Qed.

Lemma hold_area : ltac2:(tb__ "0|0|
S3cS8fS69Vm1;A1S14aVms;Vm1;A2S7dA4").
Proof using FFx HLok HMI HQ Harea Hblock Hdepth Hfr Hm1 Hmem_pg Hrgm Hrom Hsp HzA.
  pose proof R_all as R. pose proof Ea_addr as [AA AL]. pose proof Ea_Eg_disjoint as D. pose proof block_in_Eg as BE.
  destruct secret_cells as [Ca _].
  change O_area with (carved (SAlu ALU_AND (v 132) (SLit MASK_PAGE)) 0 8 [(0, 8%nat, v 136)]).
  assert (B : bv_unsigned (eval (rho1 m1) (SAlu ALU_AND (v 132) (SLit MASK_PAGE))) = zA) by (rewrite ev1u by reflexivity; apply ze_area).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros off Hoff. apply (cell_rw1 _ (ly_sec L) zA 0 8 (or_introl Ca) eq_refl eq_refl); [unfold zA, addr_of; cbn [mc_loc]; lia|lia].
  - unfold cells_in_view. constructor; [|constructor].
    apply (cell_view1 _ (ly_sec L) zA 0 8 _ (or_introl Ca) eq_refl eq_refl ltac:(lia)); [unfold zA, addr_of; cbn [mc_loc]; lia|].
    cbn [eval rho1 rw rw1 Pos.eqb]. apply Z_to_bv64_mod.
Qed.

Hypothesis HEg_img : ltac2:(tb__ "0|1|
S5S9S8SeS6cSc8Sc3Vam;A1A1A2M0Sc6Vrgm;A1A2Z10000A2S9Z5b000G0A2A2").
Hypothesis HEa_img : ltac2:(tb__ "0|0|
S5S9S8S6bSc4A2Z10000A2S9Z5b000S6bA2A2").
Hypothesis Hm0_rom : ltac2:(tb__ "0|1|
S0S4S9Z0R1A2SbR1Z60A2A2S3S1fSb4Q8A1M0A1Vm0;Sb5Q40S8Z108ecR2A2A2A1S28G0A1A3F_;Fkk;").

Lemma HblockImg : ltac2:(tb__ "0|0|
S5S9S8S8S6aS6dA2SceA2Z10000A2S9S8Z5b000Sd9A2S6aA2A2").
Proof using FFx HEg_img HQ Harea Hmem_pg Hrgm Hsp HzA. pose proof block_in_Eg. pose proof R_all. pose proof Hreg as (Ho & He & _). unfold IB, UNIT in *. lia. Qed.

Lemma Hctx : ly_ctx L = 0x5a3d0.
Proof using HMI. exact (proj1 (proj2 (proj2 HMI))). Qed.

Lemma hold_ctx : ltac2:(tb__ "0|0|
S3cS8fS69Vm1;A1S14aVms;Vm1;A2S7eA4").
Proof using FFx HEg_img HLok HMI HQ Harea Hblock Hfr Hm1 Hmem_pg Hrgm Hrom Hsp HzA.
  pose proof R_all as R. destruct secret_cells as [_ Cc]. pose proof Hctx as HC. pose proof HblockImg as HBI. unfold IB, UNIT in HBI.
  change O_ctx with (carved (SLit 0x5a3d0) 0 8 [(0, 8%nat, v 136)]).
  assert (B : bv_unsigned (eval (rho1 m1) (SLit 0x5a3d0)) = 0x5a3d0) by (cbn [eval]; apply u64; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros off Hoff. apply (cell_rw1 _ (ly_sec L) 0x5a3d0 0 8 (or_introl Cc) eq_refl eq_refl); [cbn [mc_loc loc_addr]; rewrite HC; unfold CTX_secret; lia|lia].
  - unfold cells_in_view. constructor; [|constructor].
    apply (cell_view1 _ (ly_sec L) 0x5a3d0 0 8 _ (or_introl Cc) eq_refl eq_refl ltac:(lia)); [cbn [mc_loc loc_addr]; rewrite HC; unfold CTX_secret; lia|].
    cbn [eval rho1 rw rw1 Pos.eqb]. apply Z_to_bv64_mod.
Qed.

Lemma libc_byte0 : ltac2:(tb__ "0|2|
S3S1fSb4Q8M0A1M1A1S14cS8fVm0;Sb5Q40Z5a35bA2A3S26G1Sb5G0Z0A2A2A3").
Proof using HMI bv0.
  destruct Hstat as (NL & _). unfold holds, mc_need_locks in NL. cbn [mc_libc C_U] in NL.
  specialize (NL 0%nat ltac:(lia)). cbn [Z.of_nat] in NL. rewrite Z.add_0_r in NL.
  destruct (byteview_of_Some _ _ _ _ NL) as (_ & _ & b & Hb & E).
  change (369496 + 3) with 369499 in Hb. rewrite Hb. f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. reflexivity.
Qed.

Lemma lock_bytes0 : ltac2:(tb__ "0|3|
S24S190R1U4A2S4S3S1dS14dS8fVm0;Sb5Q40S8Z5a3c8S11R2A1A2A2M0A3S23A3S3S1fSb4Q8M1A1M2A1S14cS8fVm0;G0A3S26G2Sb5G1Z0A2A2A3A2F_;Fkk;").
Proof using HMI bv0.
  intros kk Hk. destruct Hstat as (_ & _ & _ & LK & _). unfold holds in LK. cbn [mc_lock C_U] in LK.
  specialize (LK kk Hk).
  destruct (byteview_of_Some _ _ _ _ LK) as (_ & W & b & Hb & E). split; [exact W|]. rewrite Hb. f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma hold_libc : ltac2:(tb__ "0|0|
S3cS8fS69Vm1;A1S14aVms;Vm1;A2S80A4").
Proof using FFx HEg_img HMI HQ Harea Hm1 Hmem_pg Hrgm Hrom Hsp HzA.
  pose proof R_all as R. pose proof HblockImg as HBI. unfold IB, UNIT in HBI.
  change O_libc with (carved (SLit (0x5a358 + 3)) 0 1 [(0, 1%nat, SLit 0)]).
  assert (B : bv_unsigned (eval (rho1 m1) (SLit (0x5a358 + 3))) = 0x5a35b) by (cbn [eval]; apply u64; lia).
  assert (RD : Glue.rd_of segsU m1 (Z_to_bv 64 0x5a35b) = Some (Z_to_bv 8 0)).
  { destruct (rd1_eq 0x5a35b ltac:(lia) ltac:(lia)) as [E1 _]. rewrite E1. apply libc_byte0. }
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros off Hoff. replace off with 0 by lia. rewrite Z.add_0_r. split; [|exists (Z_to_bv 8 0); exact RD].
    unfold Glue.wok_of. destruct (m1 (Z_to_bv 64 0x5a35b)); [reflexivity|]. vm_compute. reflexivity.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. replace j with 0%nat by lia.
    cbn [Z.of_nat]. rewrite !Z.add_0_r. exact RD.
Qed.

Lemma hold_lock : ltac2:(tb__ "0|0|
S3cS8fS69Vm1;A1S14aVms;Vm1;A2S81A4").
Proof using FFx HEg_img HMI HQ Harea Hm1 Hmem_pg Hrgm Hrom Hsp HzA.
  pose proof R_all as R. pose proof HblockImg as HBI. unfold IB, UNIT in HBI.
  change O_lock with (carved (SLit 0x5a3c8) 0 4 [(0, 4%nat, SLit 0)]).
  assert (B : bv_unsigned (eval (rho1 m1) (SLit 0x5a3c8)) = 0x5a3c8) by (cbn [eval]; apply u64; lia).
  assert (BY : forall kk, (kk < 4)%nat ->
            Glue.wok_of segsU m1 (Z_to_bv 64 (0x5a3c8 + Z.of_nat kk)) = true
            /\ Glue.rd_of segsU m1 (Z_to_bv 64 (0x5a3c8 + Z.of_nat kk)) = Some (Z_to_bv 8 0)).
  { intros kk Hk. destruct (rd1_eq (0x5a3c8 + Z.of_nat kk) ltac:(lia) ltac:(lia)) as [E1 E2].
    rewrite E1, E2. apply lock_bytes0. exact Hk. }
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros off Hoff. destruct (BY (Z.to_nat off) ltac:(lia)) as [W RD]. rewrite Z2Nat.id in W, RD by lia.
    split; [exact W | exists (Z_to_bv 8 0); exact RD].
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    destruct (BY j Hj) as [_ RD]. rewrite RD.
    do 4 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

Lemma rl1_len : ltac2:(tb__ "0|0|
S3S0S11S2cSb4Q8A1S4bS69Vm1;A1Sa2A2A2A1Z60A3").
Proof using . reflexivity. Qed.

Lemma sctab_image : ltac2:(tb__ "0|3|
S0S4S9Z0M0R1A2SbR1Z60A2A2S3S1fSb4Q8M1A1M2A1S5eS8fSb5Q40S8Z108ecR2A2A2A2S26G2Sf2G2S17R2A1S4bS69Vm1;A1Sa2A2Sb5G1G0A2A4A2A3F_;Fkk;").
Proof using .
  intros kk Hk.
  pose proof (forall_range_dec (fun kk => match image_byte segsU (Z_to_bv 64 (0x108ec + kk)) with
                                         | Some b => bv_eqb b (nth (Z.to_nat kk) (map (Z_to_bv 8) size_classes_bytes) (Z_to_bv 8 0))
                                         | None => false end) 0 96 ltac:(vm_compute; reflexivity) kk ltac:(lia)) as H.
  cbn beta in H. rewrite Z.add_0_l in H || idtac.
  replace (0 + kk) with kk in H by lia.
  cbn [rl rho1 rl1 L_SIZECLASSES Pos.eqb].
  destruct (image_byte segsU (Z_to_bv 64 (67820 + kk))) as [b|]; [|discriminate].
  f_equal. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Lemma hold_sctab : ltac2:(tb__ "0|0|
S3cS8fS69Vm1;A1S14aVms;Vm1;A2S86A4").
Proof using FFx HEg_img HQ Harea Hm0_rom Hm1 Hmem_pg Hrgm Hrom Hsp HzA.
  pose proof R_all as R. pose proof HblockImg as HBI. unfold IB, UNIT in HBI. unfold O_sctab.
  apply obj_holds_frame_rom; try exact Hrom; try lia.
  - exact rl1_len.
  - intros kk Hk. split.
    + rewrite (m1_eq (0x108ec + kk)) by lia. apply Hm0_rom. exact Hk.
    + apply sctab_image. exact Hk.
Qed.

Lemma ze_end_code : ltac2:(tb__ "0|0|
S3S0S96S67S68S36S13dSfaS101A3A3SeS6fS10S6eZ5A2A2A3").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm Hsp HzA.
  rewrite ze_alu, ze_end, ze_code. cbn [zalu]. pose proof R_all as R.
  pose proof (Z.le_min_l rsv 5). pose proof (Z.min_glb rsv 5 0 ltac:(lia) ltac:(lia)).
  apply Z.mod_small. lia.
Qed.

Lemma ze_end_rsv : ltac2:(tb__ "0|0|
S3S0S96S67S68S36S13dSfaSa0P89A1A3A3S8S6aS6dA2A3").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm Hsp HzA.
  rewrite ze_alu, ze_end, ze137. cbn [zalu]. pose proof R_all as R. rewrite Z.mod_small by lia. lia.
Qed.

Lemma hold_zero_byte : ltac2:(tb__ "0|8|
S31S0S3S1dS9aR2A1S23A3S3S0S96S67S68R3A3R2A3S5S4S5S11dS122S128S125S17fVam;Vi;A2A1U1M0S134Z0M1A1M2A3M3S126Vs;A1A3S11dS122G3S17eVs;A1M4A3A2S3S0R3S6fA3A2S4S11dS122S128S125Sd5S89S6dA2A1G0G2A3G4A3S3S0R3S8S6aS6dA2M5A3A2A2S9G5R4A2S9S8R5Z1M6A2S8S6fG6A2A2S3cS8fS69Vm1;A1S14aVms;Vm1;A2S32R7S2dG1A1M7S2dG6A1S1bS30S33G7G6G7A3S1cS30A1A3S35A5A4F_;F_;F_;F_;F_;Fx;Fbase;").
Proof using FFx HLok HMI HQ Harea Hblock Hm1 Hmem_pg Hrgm Hrom Hsp HzA.
  intros base x Hs Hx Hc Hlo Hhi. pose proof R_all as R. pose proof Hreg as (Ho & He & _). pose proof Eg_addr as [GA GL].
  change (mkObj base (SLit 0) (SLit 1) [mkCell (SLit 0) 1 (SLit 0)] DUnknown) with (carved base 0 1 [(0, 1%nat, SLit 0)]).
  assert (B : bv_unsigned (eval (rho1 m1) base) = x) by (rewrite ev1u by exact Hs; exact Hx).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros off Hoff. destruct Hc as [[Hc ->] | [Hc ->]].
    + apply (cell_rw1 _ 0 zEnd 0 1 Hc eq_refl eq_refl); [|lia]. cbn [mc_loc]. unfold zEnd, addr_of. lia.
    + apply (cell_rw1 _ 0 (zP + n) 0 1 (or_intror Hc) eq_refl eq_refl); [|lia].
      cbn [mc_loc]. unfold zP, addr_of, loc_addr. destruct p; cbn [padd]. lia.
  - unfold cells_in_view. constructor; [|constructor].
    destruct Hc as [[Hc ->] | [Hc ->]].
    + apply (cell_view1 _ 0 zEnd 0 1 (SLit 0) Hc eq_refl eq_refl ltac:(lia)); [|reflexivity].
      cbn [mc_loc]. unfold zEnd, addr_of. lia.
    + apply (cell_view1 _ 0 (zP + n) 0 1 (SLit 0) (or_intror Hc) eq_refl eq_refl ltac:(lia)); [|reflexivity].
      cbn [mc_loc]. unfold zP, addr_of, loc_addr. destruct p; cbn [padd]. lia.
Qed.

Lemma hold_rsv : ltac2:(tb__ "0|0|
Sf0S2fS3cS8fS69Vm1;A1S14aVms;Vm1;A2A3S104S70A1A3").
Proof using FFx HLok HMI HP12 HQ Harea Hblock Hfr Hm1 Hmem_pg Hrgm Hrom Hsp HzA.
  pose proof R_all as R. pose proof Hreg as (Ho & He & _). pose proof Eg_addr as [GA GL].
  pose proof (quick_cells s g am i fr HW Hfr Hkind) as QC. cbn beta in QC.
  destruct QC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Cend & Cpn & Cu32 & Ce5).
  fold p in Cpn. change (fr_n fr) with n in Cpn. fold rsv in Cpn, Cu32, Ce5.
  assert (AE : forall d, loc_addr L (LMem (padd (slot_end am i) d)) = zEnd + d)
    by (intros d; unfold zEnd, addr_of, loc_addr; destruct (slot_end am i); cbn [padd]; lia).
  unfold ff_objs_rsv, rvv.
  destruct (rsv =? 0) eqn:E0; [|destruct (rsv <? 5) eqn:E5; [|destruct (rsv =? 5) eqn:E55]].
  - apply Z.eqb_eq in E0. constructor; [|constructor].
    apply (hold_zero_byte ff_end zEnd eq_refl ze_end); [left; auto | lia | lia].
  - apply Z.eqb_neq in E0. apply Z.ltb_lt in E5. constructor; [|constructor; [|constructor]].
    + apply (hold_zero_byte (SAlu ALU_SUB ff_end ff_code) (zP + n) eq_refl); [rewrite ze_end_code, Z.min_l by lia; lia | right; split; [apply Cpn; lia|reflexivity] | lia | lia].
    + apply (hold_zero_byte ff_end zEnd eq_refl ze_end); [left; auto | lia | lia].
  - apply Z.eqb_eq in E55.
    constructor; [|constructor].
    change (mkObj ff_end (SLit (-5)) (SLit 1) [mkCell (SLit (-5)) 1 (SLit 0); mkCell (SLit (-4)) 4 (SLit 5); mkCell (SLit 0) 1 (SLit 0)] DUnknown)
      with (carved ff_end (-5) 1 [((-5), 1%nat, SLit 0); ((-4), 4%nat, SLit 5); (0, 1%nat, SLit 0)]).
    assert (B : bv_unsigned (eval (rho1 m1) ff_end) = zEnd) by (rewrite ev1u by reflexivity; apply ze_end).
    apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    + cells_inside_tac.
    + intros off Hoff.
      destruct (Z_lt_dec off (-4)) as [O1|O1]; [|destruct (Z_lt_dec off 0) as [O2|O2]].
      * apply (cell_rw1 _ 0 zEnd (-5) 1 (or_intror (Cpn ltac:(lia))) eq_refl eq_refl); [|lia].
        cbn [mc_loc]. transitivity (zP + n); [|lia]. unfold zP, addr_of, loc_addr. destruct p; cbn [padd]. lia.
      * apply (cell_rw1 _ rsv zEnd (-4) 4 (or_intror (Cu32 ltac:(lia))) eq_refl eq_refl); [apply AE|lia].
      * apply (cell_rw1 _ 0 zEnd 0 1 Cend eq_refl eq_refl); [|lia]. cbn [mc_loc]. unfold zEnd, addr_of. lia.
    + unfold cells_in_view. constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (cell_view1 _ 0 zEnd (-5) 1 (SLit 0) (or_intror (Cpn ltac:(lia))) eq_refl eq_refl ltac:(lia)); [|reflexivity].
        cbn [mc_loc]. transitivity (zP + n); [|lia]. unfold zP, addr_of, loc_addr. destruct p; cbn [padd]. lia.
      * apply (cell_view1 _ rsv zEnd (-4) 4 (SLit 5) (or_intror (Cu32 ltac:(lia))) eq_refl eq_refl ltac:(lia)); [apply AE|].
        rewrite E55. reflexivity.
      * apply (cell_view1 _ 0 zEnd 0 1 (SLit 0) Cend eq_refl eq_refl ltac:(lia)); [|reflexivity].
        cbn [mc_loc]. unfold zEnd, addr_of. lia.
  - apply Z.eqb_neq in E55. apply Z.ltb_ge in E5.
    constructor; [|constructor; [|constructor]].
    + change (mkObj ff_end (SLit (-5)) (SLit 1) [mkCell (SLit (-5)) 1 (SLit 0); mkCell (SLit (-4)) 4 (v 137); mkCell (SLit 0) 1 (SLit 0)] DUnknown)
        with (carved ff_end (-5) 1 [((-5), 1%nat, SLit 0); ((-4), 4%nat, v 137); (0, 1%nat, SLit 0)]).
      assert (B : bv_unsigned (eval (rho1 m1) ff_end) = zEnd) by (rewrite ev1u by reflexivity; apply ze_end).
      apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
      * cells_inside_tac.
      * intros off Hoff.
        destruct (Z_lt_dec off (-4)) as [O1|O1]; [|destruct (Z_lt_dec off 0) as [O2|O2]].
        -- apply (cell_rw1 _ 0 zEnd (-5) 1 (or_intror (Ce5 ltac:(lia))) eq_refl eq_refl); [apply AE|lia].
        -- apply (cell_rw1 _ rsv zEnd (-4) 4 (or_intror (Cu32 ltac:(lia))) eq_refl eq_refl); [apply AE|lia].
        -- apply (cell_rw1 _ 0 zEnd 0 1 Cend eq_refl eq_refl); [|lia]. cbn [mc_loc]. unfold zEnd, addr_of. lia.
      * unfold cells_in_view. constructor; [|constructor; [|constructor; [|constructor]]].
        -- apply (cell_view1 _ 0 zEnd (-5) 1 (SLit 0) (or_intror (Ce5 ltac:(lia))) eq_refl eq_refl ltac:(lia)); [apply AE|reflexivity].
        -- apply (cell_view1 _ rsv zEnd (-4) 4 (v 137) (or_intror (Cu32 ltac:(lia))) eq_refl eq_refl ltac:(lia)); [apply AE|].
           rewrite ev1 by reflexivity. rewrite ze137. reflexivity.
        -- apply (cell_view1 _ 0 zEnd 0 1 (SLit 0) Cend eq_refl eq_refl ltac:(lia)); [|reflexivity].
           cbn [mc_loc]. unfold zEnd, addr_of. lia.
    + apply (hold_zero_byte (SAlu ALU_SUB ff_end (v 137)) (zP + n) eq_refl ze_end_rsv); [right; split; [apply Cpn; lia|reflexivity] | lia | lia].
Qed.

Definition O_stk : sobj := ltac2:(tb__ "0|0|
S32S34PaA1Sa0P8bA1S2dZ0A1S1cS30A1S35A5").
Definition sp0 : Z := bv_unsigned (rw rho 10%positive).
Definition D0 : Z := ltac2:(tb__ "0|0|
S99Z40Sb6Q40S39Vrho;PfA2A2A2").

Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S9S151VL;A1S8S84S85A2A2").

Lemma soff1_lit : ltac2:(tb__ "0|1|
Sb4Q40A1S1fSb4Q8A1A1F_;S0S4S9S13SaZ2Z3eA2M0A1R1A2S9R1G0A2A2S3S0S65S69R3A1S2dR2A1A2R2A3F_;Fz;Fm;").
Proof using . intros. apply soff_lit_small. lia. Qed.

Lemma rng_lit : ltac2:(tb__ "0|3|
Sb4Q40M0A1S1fSb4Q8A1A1F_;S31S0S0S21S30A1S45S0S4S9S13SaZ2Z3eA2M1A1R5A2S9R5G1A2A2M2G2S3S0Sb6G0S44S69R9A1R8A2A2R3A3S3S22S0S0A2S38S69RaA1S32R9S2dR8A1S2dR7A1R6R5A5A2S1eS0S0S8R4R8A2S8R4R7A2A4A3F_;F_;F_;Fb;Fd;Fcs;Fhi;Flo;Fbase;Fm;").
Proof using .
  intros m base lo hi cs d b Hlo Hhi Hb. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite Hb, !soff1_lit by lia. reflexivity.
Qed.

Lemma rng_stk : ltac2:(tb__ "0|0|
S3S22S0S0A2S38S69Vm1;A1S83A2S1eS0S0S8S84S85A2S84A4A3").
Proof using .
  unfold obj_range, obj_lo_of, obj_hi_of, O_stk. cbn [ob_base ob_lo ob_hi]. cbn [eval rho1 rw rw1 Pos.eqb].
  rewrite soff1_lit by lia. unfold soff. cbn [eval rho1 rw rw1 v Pos.eqb]. rewrite bv_signed_toS by (cbn; lia). unfold sp0, D0. f_equal. lia.
Qed.

Lemma rng_hdr : ltac2:(tb__ "0|0|
S3S22S0S0A2S38S69Vm1;A1S7fA2S1eS0S0S8S6aN4A2S8S6aZ0A2A4A3").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm HzA. apply rng_lit; try lia. rewrite ev1u by reflexivity. apply ze12. Qed.
Lemma rng_grp : ltac2:(tb__ "0|1|
S3S22S0S0A2S38S69Vm1;A1S7aA2S1eS0S0S8S8S6cZ10A2M0N10A2S8G0N8A2A4A3").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm HzA. apply rng_lit; try lia. rewrite ev1u by reflexivity. apply ze_mem. Qed.
Lemma rng_meta : ltac2:(tb__ "0|0|
S3S22S0S0A2S38S69Vm1;A1S82A2S1eS0S0S8S79Z10A2S8S79Z28A2A4A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA. apply rng_lit; try lia. rewrite ev1u by reflexivity. apply ze132. Qed.
Lemma rng_area : ltac2:(tb__ "0|0|
S3S22S0S0A2S38S69Vm1;A1S7dA2S1eS0S0S8S6bZ0A2S8S6bZ8A2A4A3").
Proof using FFx HQ Harea Hmem_pg Hrgm HzA. apply rng_lit; try lia. rewrite ev1u by reflexivity. apply ze_area. Qed.
Lemma rng_ctx : ltac2:(tb__ "0|1|
S3S22S0S0A2S38S69Vm1;A1S7eA2S1eS0S0S8Z5a3d0M0Z0A2S8G0Z8A2A4A3").
Proof using . apply rng_lit; try lia. cbn [eval]. apply u64. lia. Qed.
Lemma rng_libc : ltac2:(tb__ "0|1|
S3S22S0S0A2S38S69Vm1;A1S80A2S1eS0S0S8Z5a35bM0Z0A2S8G0Z1A2A4A3").
Proof using . apply rng_lit; try lia. cbn [eval]. apply u64. lia. Qed.
Lemma rng_lock : ltac2:(tb__ "0|1|
S3S22S0S0A2S38S69Vm1;A1S81A2S1eS0S0S8Z5a3c8M0Z0A2S8G0Z4A2A4A3").
Proof using . apply rng_lit; try lia. cbn [eval]. apply u64. lia. Qed.
Lemma rng_sctab : ltac2:(tb__ "0|1|
S3S22S0S0A2S38S69Vm1;A1S86A2S1eS0S0S8Z108ecM0Z0A2S8G0Z60A2A4A3").
Proof using . apply rng_lit; try lia. cbn [eval]. apply u64. lia. Qed.

Lemma rng_end1 : ltac2:(tb__ "0|3|
S3S22S0S0A2S38S69Vm1;A1S32SfaS2dZ0M0A1M1S2dZ1M2A1S1bS30S33G1G2G1A3S1cS30A1A3S35A5A2S1eS0S0S8S6fG0A2S8S6fG2A2A4A3").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm HzA. apply rng_lit; try lia. rewrite ev1u by reflexivity. apply ze_end. Qed.
Lemma rng_end5 : ltac2:(tb__ "0|2|
S21S30A1S3S22S0S0A2S38S69Vm1;A1S32SfaS2dN5M0A1S2dZ1M1A1R1S35A5A2S1eS0S0S8S6fG0A2S8S6fG1A2A4A3Fcs;").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm HzA. intros. apply rng_lit; try lia. rewrite ev1u by reflexivity. apply ze_end. Qed.
Lemma rng_pn_code : ltac2:(tb__ "0|4|
S3S22S0S0A2S38S69Vm1;A1S32S36S13dSfaS101A3S2dZ0M0A1M1S2dZ1M2A1S1bS30S33G1G2G1A3S1cS30A1A3S35A5A2S1eS0S0S8SeS6fS10S6eZ5A2A2M3G0A2S8G3G2A2A4A3").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm Hsp HzA. apply rng_lit; try lia. rewrite ev1u by reflexivity. apply ze_end_code. Qed.
Lemma rng_pn_rsv : ltac2:(tb__ "0|4|
S3S22S0S0A2S38S69Vm1;A1S32S36S13dSfaSa0P89A1A3S2dZ0M0A1M1S2dZ1M2A1S1bS30S33G1G2G1A3S1cS30A1A3S35A5A2S1eS0S0S8S8S6aS6dA2M3G0A2S8G3G2A2A4A3").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm Hsp HzA. apply rng_lit; try lia. rewrite ev1u by reflexivity. apply ze_end_rsv. Qed.

Definition in_G_after_block (r : Z * Z) : Prop := ltac2:(tb__ "0|2|
S4S9S8S6aS6dA2S2aS0S0Vr;A3M0A2S4S9S2bS0S0Vr;A3M1S8S6fZ1A2A2S9G0G1A2A2A2").

Lemma rng_rsv : ltac2:(tb__ "0|2|
S4Sf0S2fS2fS8cS38S69Vm1;A1M0R1A2A1Lo;S104S70A1M1A3S56G0G1A2A2").
Proof using FFx HP12 HQ Harea Hmem_pg Hrgm Hsp HzA.
  pose proof R_all as R. pose proof (Z.le_min_l rsv 5) as M1. pose proof (Z.min_glb rsv 5 0 ltac:(lia) ltac:(lia)) as M2.
  unfold ff_objs_rsv, rvv, in_G_after_block.
  destruct (rsv =? 0) eqn:E0; [|destruct (rsv <? 5) eqn:E5; [|destruct (rsv =? 5) eqn:E55]].
  - apply Z.eqb_eq in E0. split.
    + constructor; [|constructor]. rewrite rng_end1. cbn [fst snd]. lia.
    + cbn. split; [constructor | exact I].
  - apply Z.eqb_neq in E0. apply Z.ltb_lt in E5. rewrite Z.min_l in M1, M2 by lia. split.
    + constructor; [|constructor; [|constructor]].
      * rewrite rng_pn_code. rewrite Z.min_l by lia. cbn [fst snd]. lia.
      * rewrite rng_end1. cbn [fst snd]. lia.
    + cbn [pairwise_disjoint]. split; [|split; [constructor|exact I]].
      constructor; [|constructor]. rewrite rng_pn_code, rng_end1. rewrite Z.min_l by lia. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
  - apply Z.eqb_eq in E55. split.
    + constructor; [|constructor]. rewrite rng_end5. cbn [fst snd]. lia.
    + cbn. split; [constructor | exact I].
  - apply Z.eqb_neq in E55. apply Z.ltb_ge in E5. split.
    + constructor; [|constructor; [|constructor]].
      * rewrite rng_end5. cbn [fst snd]. lia.
      * rewrite rng_pn_rsv. cbn [fst snd]. lia.
    + cbn [pairwise_disjoint]. split; [|split; [constructor|exact I]].
      constructor; [|constructor]. rewrite rng_end5, rng_pn_rsv. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
Qed.

Definition N_common : list sobj := ltac2:(tb__ "0|0|
S1bS2fS7fS1bS2fS7aS1bS2fS82S1bS2fS7dS1bS2fS7eS1bS2fS80S1bS2fS81S1cS2fA1A3A3A3A3A3A3A3").
Definition N_all : list sobj := ltac2:(tb__ "0|0|
S25S2fS8bS25S2fS104S70A1S1bS2fS86S1cS2fA1A3A3A3").

Lemma ff_objs_eq : ltac2:(tb__ "0|0|
S3S21S2fA1S10cSf8S76S70A3S25S2fS1bS2fS83S1cS2fA1A3S77A3A3").
Proof using . unfold ff_objs, N_all, N_common. rewrite ff_objs_common_eq. reflexivity. Qed.

Lemma Zones : ltac2:(tb__ "0|5|
SeS6cSc8Sc3Vam;A1A1A2M0S0S8G0Sc6Vrgm;A1A2S0S4S9R2S6cA2S4S9S8S6fZ4A2R1A2S4S9R1S151VL;A1M1A2S4S5S9S8S6bZ1000A2M2R2A2S9R1S6bA2A2S4S5S9R1Z10000M3A2S9Z5b000M4R2A2A2S4S5S9G2G3A2S9G4S6bA2A2S4S9G1S8S84S85A2A2S4S9G2G1A2S9S8G4Z10A2G1A2A2A2A2A2A2A2A2A2TgHi;TgLo;").
Proof using FFx HEa_img HEg_img HLok HMI HQ Harea Hdepth Hmem_pg Hrgm Hsp Hsp_high HzA.
  pose proof R_all as R. pose proof Hreg as (Ho & He & _). pose proof Ea_Eg_disjoint. pose proof HEg_img. pose proof HEa_img.
  pose proof Hsp_high. destruct Hrgm as (_ & G1 & G2). pose proof HzA.
  assert (AC : 0x5b000 + 16 <= topL L) by (top_ranges; lia).
  cbn zeta. unfold zMem, addr_of, loc_addr, PGSZ, IB in *. destruct (am_mem am) as [r o]. cbn [prid poff] in *.
  unfold zMem, addr_of, loc_addr in R. cbn [prid poff] in R.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Ltac zone := rewrite ?rng_hdr, ?rng_grp, ?rng_meta, ?rng_area, ?rng_ctx, ?rng_libc, ?rng_lock, ?rng_sctab, ?rng_stk; unfold SymState.ranges_disjoint, in_G_after_block in *; cbn [fst snd] in *; lia.

Lemma N_hold : ltac2:(tb__ "0|0|
Sf0S2fS3cS8fS69Vm1;A1S14aVms;Vm1;A2A3S77A3").
Proof using FFx HEg_img HLok HMI HP12 HQ Harea Hblock Hdepth Hfr Hm0_rom Hm1 Hmem_pg Hrgm Hrom Hsp HzA.
  unfold N_all, N_common. repeat (apply Forall_cons; [first [apply hold_hdr|apply hold_grp|apply hold_meta|apply hold_area|apply hold_ctx|apply hold_libc|apply hold_lock]|]).
  apply Forall_app. split; [apply hold_rsv|]. constructor; [apply hold_sctab|constructor].
Qed.

Lemma N_vs_stack : ltac2:(tb__ "0|1|
Sf0S2fS2fS62S38S69Vm1;A1M0S83A2S38G0R1A2A2Lo;S77A3").
Proof using FFx HEa_img HEg_img HLok HMI HP12 HQ Harea Hdepth Hmem_pg Hrgm Hsp Hsp_high HzA.
  pose proof R_all as R. pose proof Zones as ZZ. cbn zeta in ZZ. rewrite rng_stk.
  unfold N_all, N_common. destruct rng_rsv as [GR _].
  repeat (apply Forall_cons; [rewrite ?rng_hdr, ?rng_grp, ?rng_meta, ?rng_area, ?rng_ctx, ?rng_libc, ?rng_lock; zone|]).
  apply Forall_app. split.
  - apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) GR o Ho) as G. zone.
  - constructor; [|constructor]. rewrite rng_sctab. zone.
Qed.

Lemma N_pairwise : ltac2:(tb__ "0|0|
S56S69Vm1;A1S77A2").
Proof using FFx HEa_img HEg_img HLok HMI HP12 HQ Harea Hdepth Hmem_pg Hrgm Hsp Hsp_high HzA.
  pose proof R_all as R. pose proof Zones as ZZ. cbn zeta in ZZ. destruct rng_rsv as [GR GP].
  unfold N_all. apply pairwise_disjoint_app.
  - unfold N_common. cbn [pairwise_disjoint].
    repeat split; repeat (apply Forall_cons; [zone|]); apply Forall_nil.
  - apply pairwise_disjoint_app; [exact GP| cbn; split; [constructor|exact I] |].
    constructor; [|constructor]. apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) GR o Ho) as G.
    rewrite rng_sctab. zone.
  - apply Forall_forall. intros o Ho. apply in_app_iff in Ho.
    assert (G : in_G_after_block (obj_range (rho1 m1) o) \/ obj_range (rho1 m1) o = (0x108ec + 0, 0x108ec + 96)).
    { destruct Ho as [Ho|[<-|[]]]; [left; exact (proj1 (Forall_forall _ _) GR o Ho) | right; apply rng_sctab]. }
    unfold N_common. repeat (apply Forall_cons; [rewrite ?rng_hdr, ?rng_grp, ?rng_meta, ?rng_area, ?rng_ctx, ?rng_libc, ?rng_lock; destruct G as [G|G]; [|rewrite G]; zone|]).
    apply Forall_nil.
Qed.

Lemma N_all_low : ltac2:(tb__ "0|2|
Sf0S2fS2fS4S9S2bS0S0S38S69Vm1;A1R1A2M0A3M1S151VL;A1A2S9S2aS0S0G0A3G1A2A2Lo;S77A3").
Proof using FFx HEa_img HEg_img HLok HMI HP12 HQ Harea Hdepth Hmem_pg Hrgm Hsp Hsp_high HzA.
  pose proof R_all as R. pose proof Zones as ZZ. cbn zeta in ZZ. destruct rng_rsv as [GR _].
  unfold N_all, N_common.
  repeat (apply Forall_cons; [rewrite ?rng_hdr, ?rng_grp, ?rng_meta, ?rng_area, ?rng_ctx, ?rng_libc, ?rng_lock; cbn [fst snd]; lia|]).
  apply Forall_app. split.
  - apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) GR o Ho) as G. unfold in_G_after_block in G. lia.
  - constructor; [|constructor]. rewrite rng_sctab. cbn [fst snd]. lia.
Qed.

Lemma N_rest_covered : ltac2:(tb__ "0|3|
S3S1dS11eS2fS2fS45S1dLx;S55R1A1S29S187R1A1S11eS30S30S1fS0A1S1dLx;S186S52R1A1A1S0S29S15Z0S53R2A1M0A2S16G0Z8A2A2Lz;S20X1fx2Lc;M1S48R1A1A3A2M2G2G2S1S29S187R2A1S11eS30G1S48R2A1A3A2Ll;S1S23Ll;S0S31S21S22S0S0A2A1S21S5cA1S29S187R5A1S11eS30G1S48R5A1A3A2Ltmpl;Lflds;Lcnt;Lesz;X45x6Lo;S1bS2fS7aSf5S2fU3S77A3A3A3S23A3").
Proof using .
  unfold N_all, N_common, rvv. destruct (rsv =? 0); [|destruct (rsv <? 5); [|destruct (rsv =? 5)]]; vm_compute; reflexivity.
Qed.

Definition S2 : sstate := ltac2:(tb__ "0|0|
S40Z20570S93S92S42S28S31A1S1bS2fS83S1cS2fA1A3S43Sf9Sf8S76S70A3A1Sa1S20A9").

Lemma Pre_ff_eq : ltac2:(tb__ "0|0|
S3S3aSf9Sf8S76S70A3S40S47S72A1S49S72A1S58S72A1S57S72A1S5bS72A1S25S2fS5aS72A1S77A3S43S72A1Sa1S4dS72A1A9A3").
Proof using . unfold Pre_free_fast. rewrite ff_objs_eq. reflexivity. Qed.

Lemma swf_Pre_ff : ltac2:(tb__ "0|0|
S3S1dS66Sf9Sf8S76S70A3A1S23A3").
Proof using . unfold kv, rvv. destruct (am_maplen am =? 0), (rsv =? 0); [| destruct (rsv <? 5); [|destruct (rsv =? 5)] | | destruct (rsv <? 5); [|destruct (rsv =? 5)]]; vm_compute; reflexivity. Qed.

Theorem carve : ltac2:(tb__ "0|2|
S21S147A1M0S148S46S8fS69Vm1;A1M1S72S1eG0S17cR2S17dVms;R1A2A4A4S46S8fG1Sf9Sf8S76S70A3S1eG0S17cR3S17dVms;R2A2A4A4F_;Fmd;Ftr;").
Proof using FFx HEa_img HEg_img HLok HMI HP12 HQ Harea Hblock Hdepth Hfr Hm0_rom Hm1 Hmem_pg Hrgm Hrom Hsp Hsp_high HzA.
  intros tr md Hsm. rewrite Pre_ff_eq. apply smatch_extend_objs.
  - exact Hsm.
  - rewrite <- Pre_ff_eq. apply swf_Pre_ff.
  - cbn [ss_objs S2]. change (rm (rho1 m1)) with m1. apply N_hold.
  - cbn [ss_objs S2]. apply Forall_forall. intros o Ho. constructor; [|constructor].
    exact (proj1 (Forall_forall _ _) N_vs_stack o Ho).
  - apply N_pairwise.
Qed.

End Inst.

Definition S1 : sstate := ltac2:(tb__ "0|1|
S40Z20570S94S93S1bS22S24S31A2M0S1eS24S31UbS34S175A1A4S1cG0A1A3A2S92S42S28S31A1S1bS2fS177S150A1S1bS2fS32S34PcA1S2dZ0A1S34PdA1S1cS30A1S35A5S1cS2fA1A3A3S25S2eS1bS2eS171S1bS2eS172S150A1S1cS2eA1A3A3S170S150A1A3S91S20A9").

Lemma S1_is_Pre_free_jumped : ltac2:(tb__ "0|1|
S3S3aS189S40Z20570S49S16fS178A1M0A1S58G0A1S57G0A1S5bG0A1S5aG0A1S43G0A1S91S20A9A3").
Proof. reflexivity. Qed.

Definition S1r : sstate := ltac2:(tb__ "0|1|
S40Z20570S94S93S1bS22S24S31A2M0S1eS24S31UbS34S175A1A4S1cG0A1A3A2S92S42S28S31A1S1bS2fS177S150A1S1cS2fA1A3S25S2eS1bS2eS171S1bS2eS172S150A1S1cS2eA1A3A3S170S150A1A3S91S20A9").

Lemma frame_user_block : ltac2:(tb__ "0|2|
SdaSbeSc0S0Sc1S11dS22S22S22SbeSc0A2M0S0A2M1Sc1A2S1eG1Sc1S1eG0S0S1eSbeSc0R4R3A4R2A4R1A4S12bR5A1A3S3ScfSd0R2A1ScdA3S11dS22SbeS0A2S1eSbeS0S123R5R4R3A3ScaR3A1A4S131R7A1A3F_;F_;Ffr;Fi;Fam;Fg;Fs;").
Proof.
  intros s g am i fr Hfr Hk. destruct (in_frames_inv s g am i fr Hfr) as (Hg & Hi & Hsl).
  unfold user_blocks. apply in_flat_map. exists (g, am). split; [exact Hg|]. cbn [snd].
  apply in_flat_map. exists i. split; [apply In_zseq; lia|]. rewrite Hsl, Hk. left. reflexivity.
Qed.

Lemma ro_sctab : ltac2:(tb__ "0|0|
S0S4S9Z0R1A2SbR1Z60A2A2S3S1dS64S8fSb5Q40S8Z108ecR2A2A2A2S23A3F_;Fkk;").
Proof.
  intros kk Hk. exact (forall_range_dec (fun kk => ro_addr segsU (Z_to_bv 64 (0x108ec + kk))) 0 96 ltac:(vm_compute; reflexivity) kk ltac:(lia)).
Qed.

Section Instantiate.
Variables (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame).
Variables (rho : valuation) (tr : list event) (ms : machine_state) (md : Model).

Hypothesis Hsm : ltac2:(tb__ "0|0|
S46S8fVrho;S189S1eS21S147A1S17cVtr;S17dVms;Vmd;A2A4A4").
Hypothesis HMI0 : ltac2:(tb__ "0|1|
S184S154S183Vs;VL;A2S179S8fS4cVrho;A1M0A2S17bS8fG0A2S149Vmd;A1A5").
Hypothesis HQ : ltac2:(tb__ "0|0|
S15cVs;S123Vam;Vi;Vfr;A3Vg;Vam;Vi;Vfr;A6").
Hypothesis HP12 : ltac2:(tb__ "0|0|
S3S0S152VL;S123Vam;Vi;Vfr;A3A2Sb6Q40S39Vrho;PcA2A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S3S0ScaVfr;A1Sb6Q40S39Vrho;PdA2A2A3").

Hypothesis Htop : ltac2:(tb__ "0|0|
S17aS183Vs;VL;A2Vrho;A2").

Let p : ltac2:(tb__ "0|0|
Sbe") := ltac2:(tb__ "0|0|
S123Vam;Vi;Vfr;A3").
Let zp := addr_of L p.
Let nn := fr_n fr.

Lemma I_frames : ltac2:(tb__ "0|2|
S11dS22S22S22SbeSc0A2M0S0A2M1Sc1A2S1eG1Sc1S1eG0S0S1eSbeSc0Vg;Vam;A4Vi;A4Vfr;A4S12bVs;A1A3"). Proof using HQ. exact (proj1 HQ). Qed.
Lemma I_kind : ltac2:(tb__ "0|0|
S3ScfSd0Vfr;A1ScdA3"). Proof using HQ. exact (proj1 (proj2 HQ)). Qed.
Lemma I_MI : ltac2:(tb__ "0|1|
S184S154S183Vs;VL;A2S14cS8fS4cVrho;A1M0A2S14dS8fG0A2S149Vmd;A1A5").
Proof using HMI0. exact HMI0. Qed.
Lemma I_WF : WF s. Proof using HMI0. exact (proj1 I_MI). Qed.
Lemma I_FF : ltac2:(tb__ "0|0|
S195Vs;Vg;Vam;Vi;Vfr;A5"). Proof using HMI0 HQ. exact (frame_facts_of s g am i fr I_WF I_frames). Qed.
Lemma I_Lok : layout_ok L s. Proof using HMI0. exact (proj1 (proj1 (proj1 (proj2 (proj2 (proj2 I_MI)))))). Qed.
Lemma I_vm : ltac2:(tb__ "0|0|
S158VL;Vs;S149Vmd;A1A3"). Proof using HMI0. exact (proj1 (proj2 (proj2 (proj2 (proj2 I_MI))))). Qed.
Lemma I_ledger : ltac2:(tb__ "0|0|
S156S154S149Vmd;A1A2"). Proof using HMI0. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 I_MI)))))))). Qed.

Lemma I_facts : ltac2:(tb__ "0|0|
Sf0S2eS54Vrho;A1S25S2eS1bS2eS171S1bS2eS172S150A1S1cS2eA1A3A3S170S150A1A3A3").
Proof using Hsm. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))). Qed.

Let u10 := bv_unsigned (rw rho 10%positive).
Let u15 := bv_unsigned (rw rho 15%positive).

Lemma I_depth : ltac2:(tb__ "0|1|
S4S9S99Z40Vu15;A2M0N1d0A2S9S13SaZ2Z28A2A1G0A2A2").
Proof using Hsm nn u10 zp.
  pose proof I_facts as F.
  assert (H1 : SymState.holds rho (SPBranch BC_GE (SLit (- free_stack)) (SVar V_DEPTH))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  assert (H2 : SymState.holds rho (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40)))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  rewrite (holds_zholds rho) in H1 by reflexivity. rewrite (holds_zholds rho) in H2 by reflexivity.
  cbn [zholds zcond zeval] in H1, H2. unfold V_DEPTH, zr_of in H1, H2. fold u15 in H1, H2.
  rewrite (toS_mod 64 u15) in H1, H2 by lia.
  replace (toS 64 ((- free_stack) mod 2 ^ 64)) with (-464) in H1 by reflexivity.
  replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) in H2 by reflexivity.
  apply Bool.negb_true_iff in H1. apply Z.ltb_ge in H1. apply Bool.negb_true_iff in H2. apply Z.ltb_ge in H2. lia.
Qed.

Lemma I_align : u10 mod 16 = 0.
Proof using Hsm.
  pose proof (proj1 (Forall_forall _ _) I_facts F_sp_aligned ltac:(left; reflexivity)) as H. cbn in H. exact (proj2 H).
Qed.

Lemma I_stack_lo : ltac2:(tb__ "0|0|
S9Z0S8Vu10;S99Z40Vu15;A2A2A2").
Proof using Hsm nn zp.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [ss_objs S1] in Hall.
  pose proof (proj1 (Forall_forall _ _) Hall (stack_win free_stack) ltac:(left; reflexivity)) as ((Hb & _) & _).
  unfold obj_lo_of, stack_win in Hb. cbn [ob_base ob_lo eval] in Hb. unfold soff in Hb. cbn [eval] in Hb.
  rewrite bv_signed_toS in Hb by (cbn; lia). change (Z.of_N 64) with 64 in Hb. unfold V_DEPTH in Hb. fold u10 u15 in Hb. lia.
Qed.

Lemma I_sp_high : ltac2:(tb__ "0|0|
S9S151VL;A1S8Vu10;S99Z40Vu15;A2A2A2").
Proof using Htop nn zp. pose proof Htop as H. unfold top_high, V_DEPTH in H. cbn [ma_L] in H. exact H. Qed.

Lemma I_sp : ltac2:(tb__ "0|0|
S4S9Z1000Vu10;A2S3S0SdVu10;Z10A2Z0A3A2").
Proof using Hsm Htop nn u15 zp. pose proof I_sp_high. pose proof I_depth. pose proof I_align. top_ranges. lia. Qed.

Lemma I_n_small : 0 <= nn < 2 ^ 20.
Proof using HMI0 HQ u10 u15 zp.
  pose proof (ff_n _ _ _ _ _ I_FF). pose proof (ff_fit _ _ _ _ _ I_FF). pose proof (ff_off _ _ _ _ _ I_FF).
  destruct (ff_ext _ _ _ _ _ I_FF) as [E|E].
  - pose proof (ff_last _ _ _ _ _ I_FF). pose proof (ff_stride_pos _ _ _ _ _ I_FF). unfold nn, UNIT, IB in *. nia.
  - destruct HQ as (_ & _ & _ & _ & _ & Hsc & _). lia.
Qed.

Lemma I_block_range : ltac2:(tb__ "0|0|
S3S22S0S0A2S38Vrho;S32S34PcA1S2dZ0A1S34PdA1S1cS30A1S35A5A2S1eS0S0Vzp;S8Vzp;Vnn;A2A4A3").
Proof using HMI0 HP12 HP13 HQ p.
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval]. rewrite soff_lit_small by lia.
  unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64.
  pose proof I_n_small as NS. unfold nn in NS. unfold zp, p, nn. rewrite HP12. rewrite <- HP13.
  unfold toS. rewrite Z.mod_small by lia. change (2 ^ (64 - 1)) with (2 ^ 63).
  replace (fr_n fr <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). f_equal. lia.
Qed.

Definition f_keep (j : positive) : bool := negb (rw1_changed j).

Lemma S1r_vars : ltac2:(tb__ "0|0|
S3S1dS15bS1a0S18aA2S23A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma S1r_nolist : state_nolist S1r = true. Proof using . vm_compute. reflexivity. Qed.

Lemma sd_S1r_S2 : ltac2:(tb__ "0|5|
S6S21S2eA1M0G0S4S3S1fS22S21S22S31S31A2M1A1M2G0A2M3A1S14bS18aS18bVam;Vfr;A2M4A2S26G3S1eG2G0S1bG1S1eS31S31S34P10A1S34PdA1A4S1bG1S1eS31S31S34PfA1S34P8bA1A4S1cG1A1A3A3R1A4A2A3S121S2eR1S43G4A1A3A2Lnf;A2").
Proof using .
  unfold S2. generalize (ss_facts (Pre_free_fast FF_P (kv am) (rvv am fr))). intros facts.
  eexists. split; [|apply incl_filter].
  unfold state_diff. cbn -[List.filter]. reflexivity.
Qed.

Lemma I_block_img : ltac2:(tb__ "0|0|
S5S9S8S8Vzp;Vnn;A2Z4A2Z10000A2S9S8Z5b000Z10A2Vzp;A2A2").
Proof using HMI0 HQ p.
  assert (HB : In (zp, nn) (ma_blocks (mkMA s L))).
  { unfold ma_blocks, blocks. cbn [ma_s ma_L]. apply in_map_iff. exists (p, nn). split; [reflexivity|].
    apply (frame_user_block s g am i fr I_frames I_kind). }
  pose proof (minv_block_geom C_U (mkMA s L) _ _ _ zp nn I_MI HB) as (_ & _ & _ & _ & G).
  cbn [mc_img_lo mc_img_hi C_U] in G. unfold IB, UNIT in G. exact G.
Qed.

Record InstH (m1 : word -> option byte) : Type := mkInstH {
  ih_a : sptr; ih_k : Z; ih_rgm : region;
  ih_FF : frame_facts s g am i fr;
  ih_Lok : layout_ok L s;
  ih_area : In ih_a (st_areas s) /\ 0 <= ih_k < METAS_PER_AREA /\ g = padd ih_a (AREA_HDR + META_SIZE * ih_k)
            /\ pg_aligned (poff ih_a) /\ pg_aligned (ly_reg L (prid ih_a));
  ih_mem_pg : pg_aligned (ly_reg L (prid (am_mem am)));
  ih_P12 : bv_unsigned (rw rho 12%positive) = zP L am i fr;
  ih_rgmH : region_of s (prid (am_mem am)) = Some ih_rgm /\ PGSZ <= ly_reg L (prid (am_mem am)) /\ ly_reg L (prid (am_mem am)) + rg_len ih_rgm <= topL L;
  ih_zA : PGSZ <= zA L ih_a /\ zA L ih_a + PGSZ <= topL L;
  ih_sp : 4096 <= bv_unsigned (rw rho 10%positive) /\ bv_unsigned (rw rho 10%positive) mod 16 = 0;
  ih_depth : toS 64 (bv_unsigned (rw rho 15%positive)) <= -464 /\ - 2 ^ 40 <= toS 64 (bv_unsigned (rw rho 15%positive));
  ih_m1 : forall w : word, ~ (zP L am i fr <= bv_unsigned w < zP L am i fr + n fr) -> m1 w = rm rho w;
  ih_Eg_img : zMem L am - poff (am_mem am) + rg_len ih_rgm <= 0x10000 \/ 0x5b000 <= zMem L am - poff (am_mem am);
  ih_Ea_img : zA L ih_a + PGSZ <= 0x10000 \/ 0x5b000 <= zA L ih_a;
  ih_m0_rom : forall kk, 0 <= kk < 96 -> rm rho (Z_to_bv 64 (0x108ec + kk)) = None;
  ih_sp_high : topL L <= sp0 rho + D0 rho
}.

Theorem free_quick_instantiate : ltac2:(tb__ "0|a|
S6Sb4Q40M0A1M1S1fSb4Q8A1M2A1M3F_;M4G4S6S19fR1A1M5G5S4G1S7S4S9Vzp;Sb6G0R1A2M6A2SbG6S8Vzp;Vnn;A2M7A2A2M8A1S3G3R4R2A1M9S4cVrho;R2A2A3F_;Fw;S4G1G8S3G3G9S193Vms;R2A2A3F_;Fw;S4S0S4S9Vzp;R1A2SbR1G7A2A2S4S7S3G3S194S8fS193Vms;A1Sb5G0R2A2A3S28G2A1A3A1S6G2G2S3G3S63Vms;Sb5G0R3A2A2S26G2R1A2A3Lb;A2A2F_;Fx;S46S8fS18eVL;Vg;Vam;Vi;Vfr;Vrho;R2A7Sf9Sf8S18dVam;A1S18fVam;Vfr;A2A3S1eS21S147A1S17cVtr;S17dVms;Vmd;A2A4A4A2A2A2LIH;A2Lm1;A2").
Proof using HMI0 HP12 HP13 HQ Hsm Htop.

  destruct (smatch_release_obj segsU rho S1 (tr, mkCfg ms md) [stack_win free_stack] (mkObj (SVar 12) (SLit 0) (SVar 13) [] DUnknown) NF
              Hsm eq_refl ltac:(vm_compute; reflexivity)) as (m1 & Hsm1 & Hout & Hin & Hblk & Hrom).
  rewrite I_block_range in Hout, Hin. unfold in_rng in Hout, Hin. cbn [fst snd] in Hout, Hin.
  cbn [cfg_ms w_cfg snd] in Hin, Hblk, Hrom.
  exists m1.
  assert (HBLK : forall x, zp <= x < zp + nn -> wview segsU (ms_mem ms) (Z_to_bv 64 x) <> None /\ exists b, rd ms (Z_to_bv 64 x) = Some b).
  { intros x Hx. destruct Hblk as (Bb & Bw & _ & Bd & _). unfold obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt eval] in *.
    pose proof I_block_range as BR. unfold obj_range, obj_lo_of, obj_hi_of in BR. cbn [ob_base ob_lo ob_hi eval] in BR.
    injection BR as BR1 BR2. rewrite soff_lit_small in BR1, Bb, Bd, Bw by lia.
    assert (E : bv_unsigned (rw rho 12%positive) + (x - zp) = x) by lia.
    split.
    - specialize (Bw (x - zp) ltac:(lia) eq_refl). rewrite E in Bw. exact Bw.
    - specialize (Bd (x - zp) ltac:(lia) ltac:(intros C; inversion C)). cbn [dflt_holds] in Bd. rewrite E in Bd. exact Bd. }
  change (mkSS (ss_pc S1) (ss_regs S1) (ss_fregs S1) (ss_fcsr S1) (ss_resv S1) [stack_win free_stack] (ss_facts S1) NF (ss_lenient S1)) with S1r in Hsm1.

  pose proof I_FF as FFx. pose proof I_WF as HW. pose proof I_Lok as HLok.
  destruct (ff_area _ _ _ _ _ FFx) as (a & k & Ha & Hk & Eg & Hapg & Hapg2 & rga & Hra & Hla & Hfit & Hkind).
  destruct (ff_region _ _ _ _ _ FFx) as (rgm & Hrm & Hkm & Hlm & Hom & Hem & _).
  pose proof HLok as (_ & HAL & _ & _).

  set (rhoB := mkVal (rw1 L g am i fr rho) (rl rho) m1).
  assert (Hsm2 : smatch segsU rhoB S1r (tr, mkCfg ms md)).
  { assert (RW : forall v, f_keep v = true -> rw (set_rm rho m1) v = rw rhoB v).
    { intros v Hv. unfold f_keep in Hv. cbn [rw set_rm rhoB]. symmetry. apply rw1_other. destruct (rw1_changed v); [discriminate|reflexivity]. }
    exact (smatch_agree_vars segsU f_keep (set_rm rho m1) rhoB S1r _ RW ltac:(intros; reflexivity) eq_refl S1r_vars Hsm1). }
  assert (Hsm3 : smatch segsU (rho1 L g am i fr rho m1) S1r (tr, mkCfg ms md)).
  { change (rho1 L g am i fr rho m1) with (set_rl rhoB (rl1 rho)). apply smatch_set_rl; [apply S1r_nolist | exact Hsm2]. }

  assert (Harea' : In a (st_areas s) /\ 0 <= k < METAS_PER_AREA /\ g = padd a (AREA_HDR + META_SIZE * k)
                   /\ pg_aligned (poff a) /\ pg_aligned (ly_reg L (prid a))).
  { repeat (split; [assumption|]). exact (HAL _ _ Hra Hla). }
  assert (Hmem_pg : pg_aligned (ly_reg L (prid (am_mem am)))) by exact (HAL _ _ Hrm Hlm).
  assert (HEg : In (LMem (SP (prid (am_mem am)) 0), rg_len rgm) (footprint s)) by (apply footprint_region_In; assumption).
  assert (HEa : In (LMem a, PGSZ) (footprint s)).
  { unfold footprint. right. apply in_app_iff. left. apply in_map_iff. exists a. auto. }
  assert (LEN : 0 <= rg_len rgm).
  { pose proof (Hsti s g am i fr FFx) as ST. pose proof (Hext am) as EX. unfold IB in Hem. lia. }
  pose proof (footprint_mem_range C_U L s (m_vmmaps md) _ _ I_vm I_ledger HEg LEN) as Gm.
  pose proof (footprint_mem_range C_U L s (m_vmmaps md) _ _ I_vm I_ledger HEa ltac:(unfold PGSZ; lia)) as Ga.
  unfold addr_of, loc_addr in Gm. cbn [prid poff mc_img_lo mc_img_hi C_U] in Gm. rewrite Z.add_0_r in Gm.
  cbn [mc_img_lo mc_img_hi C_U] in Ga.
  assert (Hrgm : region_of s (prid (am_mem am)) = Some rgm /\ PGSZ <= ly_reg L (prid (am_mem am)) /\ ly_reg L (prid (am_mem am)) + rg_len rgm <= topL L) by (split; [exact Hrm|lia]).
  assert (HzA : PGSZ <= zA L a /\ zA L a + PGSZ <= topL L) by (unfold zA; lia).

  destruct sd_S1r_S2 as (nf & Hsd & Hnf).
  assert (Hsm4 : smatch segsU (rho1 L g am i fr rho m1) (S2 am fr) (tr, mkCfg ms md)).
  { apply (smatch_restate segsU _ S1r (S2 am fr) _ [(SVar 16, SVar 13); (SVar 15, SVar 139)] nf Hsm3).
    - unfold S2. pose proof (swf_Pre_ff am fr) as W. unfold Pre_free_fast in W.
      unfold kv, rvv in *. destruct (am_maplen am =? 0), (rsv am fr =? 0); [| destruct (rsv am fr <? 5); [|destruct (rsv am fr =? 5)] | | destruct (rsv am fr <? 5); [|destruct (rsv am fr =? 5)]]; vm_compute; reflexivity.
    - exact Hsd.
    - unfold diffs_ok. constructor; [|constructor; [|constructor]]; cbn [fst snd eval rho1 rw rw1 Pos.eqb]; reflexivity.
    - apply (Forall_incl _ _ _ Hnf) || (eapply incl_Forall; [exact Hnf|]).
      apply (facts_hold s L g am i fr a k rho FFx HQ Harea' Hmem_pg (eq_sym HP12) rgm Hrgm HzA I_sp I_depth). }

  assert (Hm1' : forall w : word, ~ (zP L am i fr <= bv_unsigned w < zP L am i fr + n fr) -> m1 w = rm rho w).
  { intros w Hw. apply Hout. unfold zp, p, nn in *. unfold zP, n in Hw. exact Hw. }
  assert (HEgI : zMem L am - poff (am_mem am) + rg_len rgm <= 0x10000 \/ 0x5b000 <= zMem L am - poff (am_mem am)).
  { unfold zMem, addr_of, loc_addr. destruct (am_mem am) as [r o]; cbn [prid poff] in *. lia. }
  assert (HEaI : zA L a + PGSZ <= 0x10000 \/ 0x5b000 <= zA L a) by (unfold zA; lia).
  assert (HROM : forall kk, 0 <= kk < 96 -> rm rho (Z_to_bv 64 (0x108ec + kk)) = None).
  { intros kk Hkk.
    destruct Hsm as (_ & _ & _ & _ & _ & Hro & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hro, Hfr.
    rewrite <- Hfr.
    + apply Hro. apply ro_sctab. exact Hkk.
    + cbn [ss_objs S1]. constructor; [|constructor; [|constructor]].
      *   unfold obj_range, obj_lo_of, stack_win. cbn [ob_base ob_lo ob_hi eval fst snd].
        pose proof I_sp_high as SH. pose proof I_stack_lo. unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia).
        change (Z.of_N 64) with 64. unfold V_DEPTH. rewrite u64 by lia. top_ranges. unfold u10, u15 in *. lia.
      * rewrite I_block_range. cbn [fst snd]. rewrite u64 by lia. pose proof I_block_img. lia. }
  exists (mkInstH m1 a k rgm FFx HLok Harea' Hmem_pg (eq_sym HP12) Hrgm HzA I_sp I_depth Hm1' HEgI HEaI HROM I_sp_high).
  split; [exact Hout|]. split; [exact Hin|]. split; [exact HBLK|].
  apply (carve s L g am i fr a k rho FFx HQ HLok Harea' Hmem_pg (eq_sym HP12) rgm Hrgm HzA I_sp I_depth
               (m_vmmaps md) I_MI m1 Hm1' I_frames (frame_user_block s g am i fr I_frames I_kind) ms Hrom HEgI HEaI HROM I_sp_high).
  exact Hsm4.
Qed.

End Instantiate.
End Mal_free_quick.
