(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "Zpos"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "sub"; "mul"; "pow"; "opp"; "ltb"; "eqb"; "land"; "leb"; "lor"; "modulo"; "shiftr"; "of_nat"; "to_nat"; "div"; "lxor"; "ones"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "option"; "pair"; "list"; "prod"; "Some"; "andb"; "None"; "false"; "nil"; "fst"; "snd"; "app"; "nat"; "negb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "SAlu"; "obj_range"; "sprop"; "cell"; "rm"; "SVar"; "rw"; "eval"; "ob_base"; "soff"; "obj_holds"; "valuation"; "DUnknown"; "c_off"; "mkCell"; "mkObj"; "SPBranch"; "c_width"; "ob_cells"; "rd"; "smatch"; "ss_objs"; "sstate"; "FcsrFrm0"; "SPNot"; "c_val"; "ss_facts"; "SAluW"; "mkSS"; "ss_pc"; "swf"; "SExt"; "holds"; "ob_dflt"; "ob_hi"; "ob_lo"; "odefault"; "outside_all"; "reg_sv"; "rl"; "sprop_eqb"; "ss_fregs"; "sv_eqb"; "covered"; "enc_bytes"; "mkVal"; "ro_addr"; "rom_ok"; "sfcsr"; "ss_fcsr"; "ss_next"; "ss_regs"; "ss_resv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "callee_saved"; "pre_fregs"; "pre_reg"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "MR_P"; "vkind"; "vrsv"; "voff"; "RZ"; "F7"; "sh"; "C0"; "E_p0"; "E_stride"; "F_all"; "O_act"; "O_act0"; "O_ctr"; "O_ctz"; "O_lock"; "O_nl"; "O_sct"; "O_usg0"; "O_usg1"; "VM1"; "reg"; "NX"; "O0"; "O1"; "O_stk"; "R14"; "R5"; "RG"; "mr_ret"; "E_X0"; "E_X1"; "E_p"; "E_sll"; "VL"; "VM0"; "mr_cutB"; "mr_fold"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "below200"; "agrees"; "in_vars"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI"; "zl1"; "zr1"; "kd"; "zSt"; "stv"; "slack"; "j164"; "off"; "sc"; "zG"; "D0"; "N_all"; "sp0"; "rho1"; "Q_stk"; "S2"; "off0"; "rw1"; "zE"; "Q_act"; "Q_act0"; "Q_ctr"; "Q_lock"; "Q_meta"; "Q_nl"; "Q_slot"; "Q_usg0"; "Q_usg1"; "idx"; "rl1"; "sz"; "zMem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "zsupported"; "psupported"; "toS"; "zholds"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "stop_reason"; "lf_state"; "RsCut"; "lf_reason"; "RsFuel"; "RsMem"; "RsSymJump"; "mkLeaf"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "incl"; "filter"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sv_vars_all"; "sprop_vars_all"; "state_vars_all"; "agree_vals"; "obj_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastG.Reab"; "NL"; "m'"; "oStk"; "oMeta"; "oSlot"; "Lf"; "rw'"; "rho'"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD.InstD"; "vr"; "rsv"; "vo"; "fold_m3"; "SLACK_T"; "FOLD_T"; "M3_T"; "OFF1_T"; "SLACK5_T"; "bfact"; "osrc"; "FINAL"; "M1_T"; "M2_T"; "d7_of"; "hasf"; "l7_cls"; "l7_sd"; "pair_eqb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem";
"machine_state"; "wview"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SUB"; "ALU_SLL"; "ALU_SRL"; "BC_GEU"; "ALU_OR"; "ALU_SLTU"; "ALU_XOR"; "BC_EQ"; "aluop"; "mulop"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "in_ranges_dec"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "wz"; "malloc_stack"; "topL"; "C_U"; "byteview_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs.RP"; "LF"; "L7"; "C7"; "L8s"; "C8"; "C7base"; "D88"; "L8"; "L9"; "L9s"; "d0"; "l8_stop"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_vmmaps"; "VmMaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "Pre_malloc"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "top_high"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "MInv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD"; "vo"; "vr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastG"; "slot_cells"; "stk_cells"; "meta_cells'"; "AVAIL_T"; "instH"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Init.Specif"; "sumbool"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost"; "loop_case"; "in_zone"; "mf_idx"; "in_av"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC"; "POST"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "fold_off"; "le_byte"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "am_maplen"; "ameta"; "nth_slot"; "ss_hdr"; "am_last"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "ltb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "cell_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "reprO"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastG.Instantiate"; "f_keep"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_malloc_fastD.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fast_enum OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Section InstD.

Variables (s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta).
Variable rho : valuation.
Variables (b3 b16 : Z).
Hypothesis HW : WF s.
Hypothesis HC : ltac2:(tb__ "0|0|
S12eVs;Vn;Vg;Vam;A4").
Hypothesis HLok : layout_ok L s.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S6S6dQ40S37Vrho;PcA2A2Vn;A3").
Hypothesis Hb3 : 0 <= b3 < 256.
Hypothesis Hb16 : 0 <= b16 < 65536.
Hypothesis Hhdr : ltac2:(tb__ "0|1|
S6S6S0S20S23S6S6A2M0A1S139S138Vam;S130Vam;A1A2A1S24G0S21S6S6R2R1A4A2A3S1S0S6Vb3;R3A3S0S6Vb16;R2A3A2F_;Fh16;Fh3;").
Local Abbreviation stv := (@U.Mal_malloc__G2.Mal_malloc_fastI.stv am).
Local Abbreviation sz := (@U.Mal_malloc__G2.Mal_malloc_fastI.sz am).
Local Abbreviation zSt := (@U.Mal_malloc__G2.Mal_malloc_fastI.zSt L am).
Local Abbreviation off0 := (@U.Mal_malloc__G2.Mal_malloc_fastI.off0 s b3 b16).
Local Abbreviation slack := (@U.Mal_malloc__G2.Mal_malloc_fastI.slack n am).
Local Abbreviation off := (@U.Mal_malloc__G2.Mal_malloc_fastI.off s n am b3 b16).
Local Abbreviation kd := (@U.Mal_malloc__G2.Mal_malloc_fastI.kd am).
Local Abbreviation Hmaplen := (@U.Mal_malloc__G2.Mal_malloc_fastI.Hmaplen s n g am HW HC).
Local Abbreviation Hstv := (@U.Mal_malloc__G2.Mal_malloc_fastI.Hstv am).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S122S100S121Vs;VL;A2Vrd0;Vwok0;Vvm;A5").
Local Abbreviation Hoff0 := (@U.Mal_malloc__G2.Mal_malloc_fastI.Hoff0 s b3 b16 Hb3 Hb16).
Local Abbreviation Hoff := (@U.Mal_malloc__G2.Mal_malloc_fastI.Hoff s n g am b3 b16 HW HC Hb3 Hb16).
Local Notation "§1§ h__" := (h__ s L n g am rho b3 b16) (at level 10, h__ global).
Local Abbreviation rw1 := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.rw1).
Local Abbreviation rho1 := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.rho1).
Local Abbreviation zr1 := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.zr1).
Local Abbreviation zl1 := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.zl1).
Local Abbreviation R_all := (@U.Mal_malloc__G2.Mal_malloc_fastI.R_all s L n g am b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI).
Local Abbreviation ze_var := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_var).
Local Abbreviation ze_lit := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_lit).
Local Abbreviation ze_alu := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_alu).
Local Abbreviation ze_aluw := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_aluw).
Local Abbreviation ze_mul := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_mul).
Local Abbreviation ze_ext := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_ext).
Local Abbreviation ze_lbytes := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_lbytes).
Local Notation "§2§ h__" := (h__ s L n g am rho b3 b16 HW HC HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation ze12 := (§2§ U.Mal_malloc__G2.Mal_malloc_fastI.ze12).
Local Notation "§3§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation ze158 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze158).
Local Abbreviation ze_stride := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_stride).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1SbZ1000S6dQ40S37Vrho;PaA2A2M0A2S0S6S16G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1SbSbcZ40S6dQ40S37Vrho;PfA2A2A2M0S10SfeA1A2SbS10SfZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
SbSffVL;A1SaS6dQ40M0S37Vrho;PaA2A2SbcZ40S6dG0S37Vrho;PfA2A2A2A2A2").
Variable m0 : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0S6bQ40A1S20S6bQ8A1A1F_;Vrd0;S97S66Vm0;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0S6bQ40A1S1dF_;Vwok0;S98S66Vm0;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm0_sct : ltac2:(tb__ "0|1|
S6S1SbZ0R1A2ScR1Z60A2A2S0S20S6bQ8A1M0A1Vm0;S6cQ40SaZ108ecR2A2A2A1S26G0A1A3F_;Fkk;").
Hypothesis Hm0_ctz : ltac2:(tb__ "0|1|
S6S1SbZ0R1A2ScR1Z20A2A2S0S20S6bQ8A1M0A1Vm0;S6cQ40SaZ108ccR2A2A2A1S26G0A1A3F_;Fkk;").
Hypothesis Hm3 : ltac2:(tb__ "0|2|
S0S20S6bQ8M0A1M1A1S97S66Vm0;S6cQ40SdS9cVL;Vam;A2Z3A2A2A3S24G1S6cG0Vb3;A2A2A3").
Hypothesis Hm16 : ltac2:(tb__ "0|3|
S2cS12aR1U2M0A2S0S20S6bQ8M1A1M2A1S97S66Vm0;S6cQ40SaSdS9cVL;Vam;A2Z2A2S18R2A1A2A2A3S24G2S6cG1S135Vb16;G0R2A3A2A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S101S97S66Vm0;A2S98S66Vm0;A2A2").
Local Notation "§4§ h__" := (h__ s L n g am rho b3 b16 HW HC HLok Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hsp_high) (at level 10, h__ global).
Local Abbreviation Zones := (§4§ U.Mal_malloc__G2.Mal_malloc_fastI.Zones).
Variable ok : world -> Prop.
Variable K : ltac2:(tb__ "0|0|
S22S10eA1S10fOF_;F_;").
Hypothesis HK : ltac2:(tb__ "0|0|
S120S66Vok;VK;A3").
Variable mW : word -> option byte.
Let rhoW : valuation := rho1 mW.
Local Notation "§5§ h__" := (h__ s L n g am rho b3 b16 mW) (at level 10, h__ global).
Local Abbreviation EV := (§5§ U.Mal_malloc__G2.Mal_malloc_fastC.EV).
Local Abbreviation HOLDS := (§5§ U.Mal_malloc__G2.Mal_malloc_fastC.HOLDS).
Local Abbreviation rw_agrees := (§5§ U.Mal_malloc__G2.Mal_malloc_fastC.rw_agrees).
Local Abbreviation seg_run := (@U.Mal_malloc__G2.Mal_malloc_fastC.seg_run s L n g am rho b3 b16 Hb3 Hb16 ok K HK mW).
Local Notation "§6§ h__" := (h__ s L n g am rho b3 b16 K mW) (at level 10, h__ global).
Local Abbreviation POST := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.POST).
Local Abbreviation leaf_fact := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.leaf_fact).
Local Abbreviation setp := (@U.Mal_malloc__G2.Mal_malloc_fastC.setp).
Local Abbreviation setp_get := (@U.Mal_malloc__G2.Mal_malloc_fastC.setp_get).
Local Abbreviation linkp := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.linkp).
Local Abbreviation Zv12 := (§2§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv12).
Local Abbreviation Zv142 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv142).
Local Abbreviation Zv143 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv143).
Local Abbreviation Zv149 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv149).
Local Abbreviation Zv150 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv150).
Local Abbreviation Zv151 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv151).
Local Abbreviation Zv152 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv152).
Local Abbreviation Zv153 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv153).
Local Abbreviation Zv154 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv154).
Local Abbreviation Zv155 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv155).
Local Abbreviation Zv156 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv156).
Local Abbreviation Zv157 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv157).
Local Abbreviation Zv158 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv158).
Local Abbreviation Zv164 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv164).
Local Abbreviation Zv165 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv165).
Local Abbreviation ZE_S := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_S).
Local Abbreviation ZE_strideT := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_strideT).
Local Notation "§7§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp) (at level 10, h__ global).
Local Abbreviation ZE_and155 := (§7§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_and155).
Local Abbreviation ZE_strideM := (§3§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_strideM).
Local Abbreviation ZE_sll := (§7§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_sll).
Local Notation "§8§ h__" := (h__ rho b3 b16 Hb3 Hb16) (at level 10, h__ global).
Local Abbreviation land_255 := (§8§ U.Mal_malloc__G2.Mal_malloc_fastC.land_255).
Local Abbreviation land_31' := (§8§ U.Mal_malloc__G2.Mal_malloc_fastC.land_31').
Local Notation "§9§ h__" := (h__ s L n g am rho b3 b16 HW HC HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth Hsp_high mW) (at level 10, h__ global).
Local Abbreviation F_all_hold := (§9§ U.Mal_malloc__G2.Mal_malloc_fastC.F_all_hold).
Local Abbreviation ZF_holds := (§5§ U.Mal_malloc__G2.Mal_malloc_fastC.ZF_holds).
Local Abbreviation in_facts_b := (@U.Mal_malloc__G2.Mal_malloc_fastC.in_facts_b).
Local Abbreviation from_POST := (@U.Mal_malloc__G2.Mal_malloc_fastC.from_POST s L n g am rho b3 b16 ok K mW).
Local Abbreviation lnx_C6 := (@U.Mal_malloc__G2.Mal_malloc_fastC.lnx_C6).
Local Abbreviation lnx_C7 := (@U.Mal_malloc__G2.Mal_malloc_fastC.lnx_C7).
Local Abbreviation lnx_C8 := (@U.Mal_malloc__G2.Mal_malloc_fastC.lnx_C8).
Local Notation "§10§ h__" := (h__ s L n g am rho b3 b16 HW HC HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth ok K HK mW) (at level 10, h__ global).
Local Abbreviation pro_C6 := (§10§ U.Mal_malloc__G2.Mal_malloc_fastC.pro_C6).

Local Ltac hfact Hag :=
  match goal with |- SymState.holds ?r ?p => apply (proj2 (HOLDS r p Hag eq_refl eq_refl)); cbn [zholds zcond] end.
Local Ltac by_kind kd0 := destruct kd0; vm_compute; reflexivity.
Local Ltac zlits :=
  repeat match goal with
  | |- context [ (?x mod ?y) ] =>
      lazymatch x with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      lazymatch y with Zpos _ => idtac | Z.pow (Zpos _) (Zpos _) => idtac end;
      let vv := eval vm_compute in (x mod y) in change (x mod y) with vv
  end.
Local Ltac mlia := Z.to_euclidean_division_equations; lia.
Local Ltac zev :=
  rewrite ?ZE_strideT, ?ZE_sll;
  try rewrite ZE_strideM by lia; try rewrite ZE_and155 by lia;
  cbn [zeval zholds zcond zalu Z.of_N];
  zlits;
  rewrite ?Zv12, ?Zv142, ?Zv143, ?Zv149, ?Zv150, ?Zv151, ?Zv152, ?Zv153, ?Zv154, ?Zv155, ?Zv156, ?Zv157, ?Zv158, ?Zv164, ?Zv165;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  rewrite ?land_255, ?land_31'.
Local Ltac scratch_pair Hag HagS :=
  lazymatch goal with |- eval (setp ?r0 ?l) ?e = eval (setp ?r0 ?l) (SVar ?j) =>
    change (eval (setp r0 l) (SVar j)) with (rw (setp r0 l) j);
    rewrite (setp_get r0 l j e eq_refl) by (cbn; tauto);
    rewrite (eval_agrees rhoW (setp r0 l) e HagS) by reflexivity;
    rewrite (eval_agrees rhoW r0 e Hag) by reflexivity; reflexivity
  end.
Local Ltac sem_pair HagS :=
  rewrite !(EV _ _ HagS) by reflexivity; f_equal.
Local Ltac sd_tac v := intros [| |]; vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some v)).
Local Ltac by_kinds := intros [| |]; vm_cast_no_check (@eq_refl bool true).
Local Ltac lnx_tac := split; reflexivity.

Definition SLACK_T (S : sv) : sv := ltac2:(tb__ "0|0|
S31Sf3S31SefS31Sf1VS;S36PcA1A3S30N4A1A3S30Z4A1A3").
Definition SLACK5_T (S : sv) : sv := ltac2:(tb__ "0|0|
S31Sf3S31SefS31Sf1VS;S36PcA1A3S30N4A1A3S30Z5A1A3").
Definition M1_T (S : sv) : sv := ltac2:(tb__ "0|0|
S31Sf5SddVS;A1Se1VS;A1A3").
Definition M2_T (S : sv) : sv := ltac2:(tb__ "0|1|
S31Sf5S31Sf3Se5VS;A1M0S30Z2A1A3G0A3").
Definition M3_T (S : sv) : sv := ltac2:(tb__ "0|1|
S31Sf5S31Sf3Se6VS;A1M0S30Z4A1A3G0A3").
Definition OFF1_T (S O : sv) : sv := ltac2:(tb__ "0|0|
S31Sf0VO;SdfVS;A1A3").
Definition FOLD_T (S O : sv) : sv := ltac2:(tb__ "0|2|
S4cSefS31Sf0S31Sf1S30Z0A1S31Sf6SddVS;A1M0Se0VS;VO;A2M1A3A3S31Sf7G0S30ZffffffffffffffffA1A3A3G1A3").
Definition CTR8_T : sv := ltac2:(tb__ "0|0|
S31Sf0S50S1eQ20S36P99A1A3S30ZffA1A3").
Definition B16P1_T : sv := ltac2:(tb__ "0|0|
S31Sf0S31SefS36P8fA1S30Z1A1A3S30ZffA1A3").
Definition osrc (bz : bool) : sv := if bz then CTR8_T else B16P1_T.
Definition bfact (bz : bool) : sprop := ltac2:(tb__ "0|1|
S1dS33Lbz;Vbz;S41Sf8S36P8eA1S30Z0A1A3M0S49G0A1X1dx2").
Definition hasf (p : sprop) (S : sstate) : bool := ltac2:(tb__ "0|0|
Sc9S33S59Vp;A1S4bVS;A1A3").

Definition fold_m3 (sl : Z) : Z := ltac2:(tb__ "0|0|
S15Vsl;S17Vsl;Z1A2A2S6S15R1S17R1Z2A2A2S6S15R1S17R1Z4A2A2Tm2;Tm1;").
Lemma fold_off_eq : ltac2:(tb__ "0|2|
S6S6S0S6S134R2R1A2S1dS6L_;M0S11R2R1A2G0S11R2S13R1SdcR2A1A2M1A2SdG1SaR2Z1A2A2G1X1dx2R1X1dx2A3Fo0;Fsl;").
Proof using . intros. reflexivity. Qed.

Lemma lxor_ones : ltac2:(tb__ "0|2|
S6S6SbZ0M0R1A2S1SbG0R3A2ScR3SfZ2R2A2A2A2S0S6S1bR4S1cR3A1M1A2SdG1R4A2A3F_;F_;Fk;Fa;").
Proof using Hb16 Hb3 rho.
  intros a k Hk Ha.
  assert (E : Z.ones k - a = Z.ldiff (Z.ones k) a).
  { apply Z.sub_nocarry_ldiff. rewrite Z.ldiff_ones_r by lia.
    replace (Z.shiftr a k) with 0; [rewrite Z.shiftl_0_l; reflexivity|]. symmetry. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. }
  rewrite E. apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.ldiff_spec.
  destruct (Z_lt_dec i k).
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit a i); reflexivity.
  - rewrite Z.ones_spec_high by lia.
    assert (Ta : Z.testbit a i = false).
    { destruct (Z.eq_dec a 0) as [->|Hz]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
      apply (Z.lt_le_trans _ (2 ^ k)); [lia|]. apply Z.pow_le_mono_r; lia. }
    rewrite Ta. reflexivity.
Qed.

Lemma slack_val : ltac2:(tb__ "0|0|
S0S6S9eVn;Vam;A2S1aSdSdS9dVam;A1Z4A2Vn;A2Z10A2A3").
Proof using . unfold U.Mal_malloc__G2.Mal_malloc_fastI.slack, mf_slack, U.Mal_malloc__G2.Mal_malloc_fastI.stv, IB, UNIT. reflexivity. Qed.
Lemma slack_range : 0 <= slack < 2 ^ 16.
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp. rewrite slack_val. pose proof R_all as R. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma fold_m3_range : ltac2:(tb__ "0|1|
S1SbZ0SdcS9eVn;Vam;A2A1M0A2ScG0SfZ2Z20A2A2A2").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp.
  pose proof slack_range as SR. unfold fold_m3.
  assert (B1 : 0 <= Z.lor slack (Z.shiftr slack 1) < 2 ^ 32).
  { apply lor_bound32; [lia|]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  set (m1 := Z.lor slack (Z.shiftr slack 1)) in *.
  assert (B2 : 0 <= Z.lor m1 (Z.shiftr m1 2) < 2 ^ 32).
  { apply lor_bound32; [lia|]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  set (m2 := Z.lor m1 (Z.shiftr m1 2)) in *.
  apply lor_bound32; [lia|]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Section Fold.
  Variables (S O : sv) (zo : Z).
  Hypothesis HS : ltac2:(tb__ "0|0|
S0S6Sb9S9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8VS;A3S9dVam;A1A3").
  Hypothesis HO : ltac2:(tb__ "0|0|
S0S6Sb9S9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8VO;A3Vzo;A3").
  Hypothesis Hzo : 0 <= zo < 256.

  Lemma zv_SLACK : ltac2:(tb__ "0|0|
S0S6Sb9S9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8SddVS;A1A3S9eVn;Vam;A2A3").
  Proof using HC HMI HP12 HS HW Hb16 Hb3 Hhdr.
    clear HO Hzo. unfold SLACK_T. cbn [zeval zalu]. rewrite HS. zlits. rewrite Zv12. rewrite Z.shiftr_div_pow2 by lia.
    rewrite slack_val. pose proof R_all as R. mlia.
  Qed.
  Lemma zv_SLACK5 : ltac2:(tb__ "0|0|
S0S6Sb9S9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Se1VS;A1A3S17S9eVn;Vam;A2Z1A2A3").
  Proof using HC HMI HP12 HS HW Hb16 Hb3 Hhdr.
    clear HO Hzo. unfold SLACK5_T. cbn [zeval zalu]. rewrite HS. zlits. rewrite Zv12. rewrite !Z.shiftr_div_pow2 by lia.
    rewrite slack_val. pose proof R_all as R. mlia.
  Qed.
  Lemma zv_M3 : ltac2:(tb__ "0|0|
S0S6Sb9S9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8SdfVS;A1A3SdcS9eVn;Vam;A2A1A3").
  Proof using HC HMI HP12 HS HW Hb16 Hb3 Hhdr Hsp.
    clear HO Hzo. pose proof slack_range as SR.
    assert (E1 : zeval zr1 zl1 (M1_T S) = Z.lor slack (Z.shiftr slack 1)).
    { unfold M1_T. rewrite ze_alu, zv_SLACK, zv_SLACK5. cbn [zalu].
      rewrite !Z.mod_small; [reflexivity | |lia]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    assert (B1 : 0 <= Z.lor slack (Z.shiftr slack 1) < 2 ^ 32).
    { apply lor_bound32; [lia|]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    set (m1 := Z.lor slack (Z.shiftr slack 1)) in *.
    assert (E2 : zeval zr1 zl1 (M2_T S) = Z.lor m1 (Z.shiftr m1 2)).
    { unfold M2_T. rewrite ze_alu, (ze_alu ALU_SRL), E1, ze_lit. cbn [zalu]. zlits.
      rewrite !(Z.mod_small m1) by lia.
      rewrite (Z.mod_small (Z.shiftr m1 2)); [apply Z.lor_comm|].
      rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    assert (B2 : 0 <= Z.lor m1 (Z.shiftr m1 2) < 2 ^ 32).
    { apply lor_bound32; [lia|]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    set (m2 := Z.lor m1 (Z.shiftr m1 2)) in *.
    unfold M3_T. rewrite ze_alu, (ze_alu ALU_SRL), E2, ze_lit. cbn [zalu]. zlits.
    rewrite !(Z.mod_small m2) by lia.
    rewrite (Z.mod_small (Z.shiftr m2 4)).
    - unfold fold_m3. apply Z.lor_comm.
    - rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma zv_OFF1 : ltac2:(tb__ "0|0|
S0S6Sb9S9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Se0VS;VO;A2A3S13Vzo;SdcS9eVn;Vam;A2A1A2A3").
  Proof using HC HMI HO HP12 HS HW Hb16 Hb3 Hhdr Hsp Hzo.
    unfold OFF1_T. rewrite ze_alu, HO, zv_M3. cbn [zalu]. pose proof fold_m3_range.
    rewrite !Z.mod_small by lia. reflexivity.
  Qed.
  Lemma off1_range : ltac2:(tb__ "0|1|
S1SbZ0S13Vzo;SdcS9eVn;Vam;A2A1A2M0A2SbG0Vzo;A2A2").
  Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp Hzo. clear HS HO. pose proof fold_m3_range. split; [apply Z.land_nonneg; lia | apply land_le_l; lia]. Qed.

  Lemma zv_FOLD : ltac2:(tb__ "0|2|
S0S6Sb9S9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8SdeVS;VO;A2A3S1dS6L_;S11S9eVn;Vam;A2M0S13Vzo;SdcG0A1A2M1A2SdG1SaG0Z1A2A2G1X1dx2A3").
  Proof using HC HMI HO HP12 HS HW Hb16 Hb3 Hhdr Hsp Hzo.
    pose proof slack_range as SR. pose proof off1_range as OR1.
    unfold FOLD_T. rewrite ze_aluw. rewrite (ze_alu ALU_AND), (ze_alu ALU_SUB), (ze_alu ALU_SLTU), (ze_alu ALU_XOR), !zv_SLACK, !zv_OFF1, !ze_lit.
    set (o1 := Z.land zo (fold_m3 slack)) in *.
    cbn [zalu]. zlits.
    rewrite !(Z.mod_small slack (2 ^ 64)) by lia. rewrite !(Z.mod_small o1 (2 ^ 64)) by lia.
    change 18446744073709551615 with (Z.ones 64). rewrite lxor_ones by lia. change (Z.ones 64) with (2 ^ 64 - 1).
    destruct (slack <? o1) eqn:C.
    - apply Z.ltb_lt in C.
      match goal with |- context [Z.land ?a ?b] => replace (Z.land a b) with (2 ^ 64 - 1 - slack) end.
      2:{ rewrite (Z.mod_small (2 ^ 64 - 1 - slack)) by lia.
          match goal with |- context [Z.land ?a _] => replace a with (Z.ones 64) by reflexivity end.
          rewrite Z.land_comm, Z.land_ones by lia. symmetry. apply Z.mod_small. lia. }
      rewrite sx32_small by mlia. mlia.
    - apply Z.ltb_ge in C.
      match goal with |- context [Z.land ?a ?b] => replace (Z.land a b) with 0 by (replace a with 0 by reflexivity; rewrite Z.land_0_l; reflexivity) end.
      rewrite sx32_small by mlia. mlia.
  Qed.
End Fold.

Lemma zv_osrc : ltac2:(tb__ "0|0|
S1dS5S0S1dR1S1eA3S0S6Vb3;Z0A3A2S0S6Sb9S9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Se3R2A1A3Sa9Vs;Vb3;Vb16;A3A3F_;Fbz;").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  intros bz Hbz. pose proof R_all as R. unfold U.Mal_malloc__G2.Mal_malloc_fastI.off0.
  destruct bz; cbn [osrc]; unfold CTR8_T, B16P1_T; cbn [zeval zalu Z.of_N]; zlits.
  - rewrite (proj2 (Z.eqb_eq b3 0) (proj1 Hbz eq_refl)). rewrite Zv153. rewrite !land_255.
    unfold toS. destruct (_ <? _) eqn:E; [apply Z.ltb_lt in E|apply Z.ltb_ge in E]; mlia.
  - destruct (b3 =? 0) eqn:E; [exfalso; pose proof (proj2 Hbz (proj1 (Z.eqb_eq _ _) E)); discriminate|].
    rewrite Zv143, !land_255. mlia.
Qed.

Lemma off_fold : ltac2:(tb__ "0|0|
S0S6Sa0Vs;Vn;Vam;Vb3;Vb16;A5S134S9eVn;Vam;A2Sa9Vs;Vb3;Vb16;A3A2A3").
Proof using . reflexivity. Qed.

Definition rsv : Z := ltac2:(tb__ "0|0|
SdSdSdS9dVam;A1SeZ10Sa0Vs;Vn;Vam;Vb3;Vb16;A5A2A2Vn;A2Z4A2").
Definition vo : voff := ltac2:(tb__ "0|0|
S1dS71L_;S12Sa0Vs;Vn;Vam;Vb3;Vb16;A5Z0A2S85S86X1dx2").
Definition vr : vrsv := ltac2:(tb__ "0|1|
S1dS70L_;M0S12SdaZ0A2S72G0S14SdaZ4A2S88G0S12SdaZ5A2S89S8aX1dx2X1dx2X1dx2").
Lemma rsv_range : 0 <= rsv < 2 ^ 20.
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp. unfold rsv. pose proof R_all as R. lia. Qed.

Lemma ze_sll : ltac2:(tb__ "0|0|
S0S6Sb9S9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S8fA3SeZ10Sa0Vs;Vn;Vam;Vb3;Vb16;A5A2A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp. exact ZE_sll. Qed.
Lemma ze_X0 : ltac2:(tb__ "0|0|
S0S6Sb9S9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S8cS9bVam;A1A1A3SdSdS9dVam;A1Vn;A2Z4A2A3").
Proof using HC HMI HP12 HW Hb16 Hb3 Hhdr. unfold E_X0. rewrite !ze_alu, ze_stride, ze12, !ze_lit. cbn [zalu]. zlits. pose proof R_all as R. mlia. Qed.
Lemma ze_X1 : ltac2:(tb__ "0|0|
S0S6Sb9S9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S8dS9bVam;A1A1A3SdaA3").
Proof using HC HMI HP12 HW Hb16 Hb3 Hhdr Hsp. unfold E_X1, rsv. rewrite !ze_alu, ze_stride, ze_sll, ze12, !ze_lit. cbn [zalu]. zlits. pose proof R_all as R. mlia. Qed.

Theorem ZF7 : ltac2:(tb__ "0|0|
S119S33SbdS9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8A2S73S9bVam;A1SdbSd9A3A3").
Proof using HC HMI HP12 HW Hb16 Hb3 Hhdr Hsp.
  pose proof R_all as R. pose proof rsv_range as RR. pose proof Hoff as HO.
  unfold F7. apply Forall_app. split; [|apply Forall_app; split].
  - unfold vo. destruct (off =? 0) eqn:Eo; [apply Z.eqb_eq in Eo|apply Z.eqb_neq in Eo].
    + constructor; [|constructor]. cbn [zholds]. rewrite ze158, ze_lit. zlits. lia.
    + repeat constructor; cbn [zholds]; rewrite ?ze_alu, ?ze_sll, ?ze_stride, ?ze158, ?ze12, ?ze_lit; cbn [zalu]; zlits; try mlia.
  - assert (EX : zeval zr1 zl1 (E_X kd vo) = rsv).
    { unfold E_X, vo. destruct (off =? 0) eqn:Eo; [apply Z.eqb_eq in Eo; rewrite ze_X0; unfold rsv; lia | apply ze_X1]. }
    unfold vr. destruct (rsv =? 0) eqn:E0; [apply Z.eqb_eq in E0|apply Z.eqb_neq in E0].
    + repeat constructor. cbn [zholds]. rewrite EX, ze_lit. zlits. lia.
    + destruct (rsv <=? 4) eqn:E4; [apply Z.leb_le in E4|apply Z.leb_gt in E4].
      * repeat constructor; cbn [zholds]; rewrite EX, ze_lit; zlits; lia.
      * destruct (rsv =? 5) eqn:E5; [apply Z.eqb_eq in E5|apply Z.eqb_neq in E5];
          repeat constructor; cbn [zholds]; rewrite EX, ze_lit; zlits; lia.
  - unfold vo, vr.
    destruct (off =? 0) eqn:Eo; [apply Z.eqb_eq in Eo|apply Z.eqb_neq in Eo];
    (destruct (rsv =? 0) eqn:E0; [apply Z.eqb_eq in E0|apply Z.eqb_neq in E0]);
    (destruct (rsv <=? 4) eqn:E4; [apply Z.leb_le in E4|apply Z.leb_gt in E4]);
    (destruct (rsv =? 5) eqn:E5; [apply Z.eqb_eq in E5|apply Z.eqb_neq in E5]);
    repeat constructor; cbn [zholds]; rewrite ?ze_alu, ?ze_sll, ?ze_stride, ?ze12, ?ze_lit; cbn [zalu]; zlits; unfold rsv in *; mlia.
Qed.

Lemma F7_supported : ltac2:(tb__ "0|1|
S6fS71S70S1S0S1dSc8S33ScdS94A1S73R3R2R1A3M0A3S1eA3S0S1dSc8S33SbbG0A3S1eA3A2Fr;Fo;Fkd0;").
Proof using . intros [| |] [|] [| | |]; split; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma F7_hold : ltac2:(tb__ "0|0|
S3cS95VrhoW;R1A2S119S33S51R2A1S73S9bVam;A1SdbSd9A3A3F_;Frho';").
Proof using HC HMI HP12 HW Hb16 Hb3 Hhdr Hsp mW.
  intros rho' Hag. destruct (F7_supported kd vo vr) as [Hv Hs]. exact (ZF_holds rho' _ Hag Hv Hs ZF7).
Qed.

Definition l7_cls (kd0 : vkind) (L : leaf) : bool :=
  let S := E_stride kd0 in let st := lf_state L in
  existsb (fun bz : bool =>
    hasf (bfact bz) st &&
    match lf_reason L with
    | RsCut => (ss_pc st =? mr_cutB MR_P) && l7_same kd0 L
               && state_vars_all (fun u => negb (in_vars [204%positive; 205%positive] u)) st
               && sv_vars_all below200 (reg st 5) && sv_vars_all below200 (reg st 13)
               && ( (sv_eqb (reg st 17) (osrc bz) && hasf (SPBranch BC_GEU (SLACK_T S) (osrc bz)) st)
                  || (sv_eqb (reg st 17) (FOLD_T S (osrc bz)) && hasf (SPNot (SPBranch BC_GEU (SLACK_T S) (osrc bz))) st
                      && hasf (SPBranch BC_GEU (SLACK_T S) (FOLD_T S (osrc bz))) st) )
    | RsMem => hasf (SPNot (SPBranch BC_GEU (SLACK_T S) (osrc bz))) st
               && hasf (SPNot (SPBranch BC_GEU (SLACK_T S) (FOLD_T S (osrc bz)))) st
    | _ => false
    end)%bool [true; false].
Lemma L7_cls : ltac2:(tb__ "0|0|
S6fS0S1dSc8SbeSe9R1A1S103R1A1A3S1eA3Fkd0;"). Proof using . by_kinds. Qed.

Definition d7_of (st : sstate) : list (sv * sv) := ltac2:(tb__ "0|1|
S1fS23S2eS2eA2M0S21S2eS2eS83Vst;U5A2S36PccA1A4S1fG0S21S2eS2eS83Vst;UdA2S36PcdA1A4S1fG0S21S2eS2eS83Vst;U11A2S36P9eA1A4S28G0A1A3A3A3").
Definition pair_eqb (p q : sv * sv) : bool := ltac2:(tb__ "0|0|
S25S5bS29S2eS2eVp;A3S29S2eS2eVq;A3A2S5bS2aS2eS2eVp;A3S2aS2eS2eVq;A3A2A2").
Lemma pair_eqb_sound : ltac2:(tb__ "0|1|
S23S2eS2eA2M0G0S0S1dSebR2R1A2S1eA3S0G0R3R2A3F_;Fq;Fp;").
Proof using . intros [a b] [c d] H. unfold pair_eqb in H. cbn in H. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. subst a b. reflexivity. Qed.
Definition l7_sd (kd0 : vkind) (L : leaf) : bool :=
  match lf_reason L with
  | RsCut => match state_diff (lf_state L) (C7 kd0 O0 RZ) with
             | Some (d, _) => leqb pair_eqb d (d7_of (lf_state L))
             | None => false
             end
  | _ => true
  end.
Lemma L7_sd : ltac2:(tb__ "0|0|
S6fS0S1dSc8SbeSeaR1A1S103R1A1A3S1eA3Fkd0;"). Proof using . by_kinds. Qed.

Lemma swf_C7 : ltac2:(tb__ "0|0|
S6fS71S70S0S1dS4fS104R3R2R1A3A1S1eA3Fr;Fo;Fkd0;").
Proof using . intros [| |] [|] [| | |]; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma state_diff_refacts : ltac2:(tb__ "0|6|
S47S6S22S2eA1M0G0S22S2fA1S22S33A1M1G1S7S22S23S2eS2eA2A1M2G1S0S20S23G2G1A2M3A1M4S11eRaS4dR9R8R7S48S26S2eA1M5R6R5R3S27A9A2S24G3S21G2G1R2R1A4A2A3S0G4S11eRbS4dRaR9R8S48G5R7R5R4S27A9A2S24G3S21G2G1R3ScbS33S33S2dSc9S33S59R1A1S4bRcA1A3A1Lp;R5A3A4A2A3F_;Fnf;Fd;Fnx;Ff2;Ff1;Fob;Ffr;Frg;Fpc;FS0;").
Proof using .
  intros S0 pc rg fr ob f1 f2 nx d nf H. unfold state_diff in *. cbn [ss_pc ss_fcsr ss_resv ss_regs ss_fregs ss_objs ss_facts] in *.
  destruct (ss_pc S0 =? pc); [|discriminate].
  destruct (sfcsr_diff (ss_fcsr S0) FcsrFrm0); [|discriminate].
  destruct (osv_diff (ss_resv S0) None); [|discriminate].
  destruct (svs_diff (ss_regs S0) rg); [|discriminate].
  destruct (svs_diff (ss_fregs S0) fr); [|discriminate].
  destruct (objs_diff (ss_objs S0) ob); [|discriminate].
  injection H as <- _. reflexivity.
Qed.

Lemma C7_eq : ltac2:(tb__ "0|1|
S6fS71S70S0S47S104R3R2R1A3S4dS4eS107R3A1M0A1S64G0A1S5aG0A1S48S26S2eA1S46G0A1S2bS33S4bG0A1S73R3R2R1A3A3S84S27A9A3Fr;Fo;Fkd0;").
Proof using . intros. reflexivity. Qed.
Lemma C7base_facts : ltac2:(tb__ "0|0|
S6fS0S22S33A1S4bS107R1A1A1S78R1A1A3Fkd0;").
Proof using . intros [| |]; reflexivity. Qed.

Lemma sd_7 : ltac2:(tb__ "0|4|
S6fSbeS71S70Sc7SbeR3S103R4A1A3S0SbfSc2R4A1Sc1A3S4S22S33A1M0G0S1S0S20S23S22S23S2eS2eA2A1M1G0A2M2A1S11eSc0R6A1M3S104R7R5R4A3A2S24G2S21G1G0Se7G3A1R1A4A2A3ScaS33R1S2bS33S78R7A1S73R7R5R4A3A3A3A2Lnf;A2F_;F_;Fr;Fo;FLf;Fkd0;").
Proof using .
  intros kd0 Lf o r Hin HR.
  pose proof (proj1 (forallb_forall _ _) (L7_sd kd0) Lf Hin) as SD. unfold l7_sd in SD. rewrite HR in SD.
  rewrite C7_eq in SD. destruct (state_diff (lf_state Lf) _) as [[d nf0]|] eqn:E; [|discriminate].
  apply (leqb_sound pair_eqb pair_eqb_sound) in SD. subst d.
  eexists. split.
  - rewrite C7_eq. exact (state_diff_refacts _ _ _ _ _ _ _ _ _ _ E).
  - rewrite C7base_facts. apply incl_filter.
Qed.

Lemma L7_cut_or_mem : ltac2:(tb__ "0|2|
S6fSbeSc7SbeR1S103R2A1A3S2S1S0SbfSc2R2A1M0Sc1A3S0S6S4eSc0R2A1A1M1S92S6eA1A3A2S1S0SbfG0Sc4A3S0S6G1S93S6eA1A3A2A2F_;FLf;Fkd0;").
Proof using .
  intros kd0 Lf Hin. pose proof (proj1 (forallb_forall _ _) (L7_shape kd0) Lf Hin) as H. unfold l7_ok in H.
  destruct (lf_reason Lf); try discriminate; apply Z.eqb_eq in H; auto.
Qed.

Lemma zh_geu : ltac2:(tb__ "0|2|
S2eS2eS5SbdS9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8M0S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8M1S41Sf4R2R1A3A3SbSb9G0G1R1A3Sb9G0G1R2A3A2A2Fb;Fa;").
Proof using Hb16 Hb3 Hdepth Hsp. intros a b. cbn [zholds zcond]. rewrite Bool.negb_true_iff, Z.ltb_ge. tauto. Qed.
Lemma zh_ngeu : ltac2:(tb__ "0|2|
S2eS2eS5SbdS9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8M0S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8M1S49S41Sf4R2R1A3A1A3ScSb9G0G1R2A3Sb9G0G1R1A3A2A2Fb;Fa;").
Proof using Hb16 Hb3. intros a b. cbn [zholds zcond]. rewrite Bool.negb_true_iff, Z.ltb_ge. lia. Qed.
Lemma zh_bfact : ltac2:(tb__ "0|0|
S1dSbdS9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8Se2R1A1A3S5S0S1dR2S1eA3S0S6Vb3;Z0A3A2F_;Fbz;").
Proof using HC HMI HW Hb16 Hb3 Hdepth Hhdr Hsp.
  intros bz H. destruct bz; cbn [bfact zholds zcond zeval] in H; rewrite Zv142 in H; change (0 mod 2 ^ 64) with 0 in H.
  - apply Z.eqb_eq in H. tauto.
  - rewrite Z.eqb_eq in H. split; [discriminate | intros E; exfalso; exact (H E)].
Qed.

Lemma hasf_zholds : ltac2:(tb__ "0|0|
S3cS47S12cS33S95VrhoW;R4A2S11fS66VK;R4R5R3A5S0S1dSe8R3R5A2S1eA3S0S1dScdS94R4A2S1eA3S0S1dSbbR5A1S1eA3SbdS9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8R6A3F_;F_;F_;F_;F_;Fp;Fw;FS;Frho';").
Proof using mW. intros rho' S w p Hag HSP Hh Hv Hs. apply (leaf_fact rho' S w p Hag HSP); [apply in_facts_b; exact Hh | exact Hv | exact Hs]. Qed.

Lemma tmpl_supported : ltac2:(tb__ "0|5|
S6fS1dS77R2A1S2eSe3R2A1S2eS0S1dS25S25S25S25S25S25S25S25S25ScdS94Se2R3A1M0A2SbbG0A1A2ScdS94S41Sf4SddR2A1M1R1A3M2A2A2SbbG2A1A2ScdS94S41Sf4G1SdeR2R1A2M3A3M4A2A2SbbG4A1A2SccS94R1A2A2SbaR1A1A2SccS94G3A2A2SbaG3A1A2S1eA3TO;TS;Fbz;Fkd0;").
Proof using . intros [| |] [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma vars_not : ltac2:(tb__ "0|0|
S33S0S1dScdS94S49R1A1A2ScdS94R1A2A3Fp;").
Proof using . intros. reflexivity. Qed.
Lemma psup_not : ltac2:(tb__ "0|0|
S33S0S1dSbbS49R1A1A1SbbR1A1A3Fp;").
Proof using . intros. reflexivity. Qed.

Theorem link_7 : ltac2:(tb__ "0|1|
SbeS3cS12cSc7SbeR3S103S9bVam;A1M0A1A3S95VrhoW;R3A2S11fS66VK;Sc0R5A1R4R3A5S132Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;VK;VmW;S104G0SdbSd9A3R4AcF_;F_;F_;Fw;Frho';FLf;").
Proof using HC HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high.
  intros Lf rho' w Hin Hag HSP. pose proof R_all as R. pose proof Hoff0 as HO0. pose proof slack_range as SR.
  pose proof (proj1 (forallb_forall _ _) (L7_cls kd) Lf Hin) as CL. unfold l7_cls in CL.
  apply existsb_exists in CL as (bz & _ & CL). apply andb_prop in CL as [Hbf CL].
  pose proof (tmpl_supported kd bz) as TS. cbn beta iota zeta in TS.
  repeat (apply andb_prop in TS; destruct TS as [TS ?]).
  rename H into ZsF. rename H0 into VF. rename H1 into ZsO. rename H2 into VO.
  rename H3 into PsGF. rename H4 into VGF. rename H5 into PsG. rename H6 into VG. rename H7 into PsB.
  pose proof (zh_bfact bz (hasf_zholds rho' _ w _ Hag HSP Hbf TS PsB)) as Hbz.
  pose proof (zv_osrc bz Hbz) as EO.
  pose proof (zv_SLACK (E_stride kd) ze_stride) as ESL.
  pose proof (zv_FOLD (E_stride kd) (osrc bz) off0 ze_stride EO HO0) as EF.
  pose proof (off1_range off0 HO0) as OR1.
  set (o1 := Z.land off0 (fold_m3 slack)) in *.
  destruct (L7_cut_or_mem kd Lf Hin) as [[HR Hpc]|[HR Hpc]]; rewrite HR in CL.
  -
    apply andb_prop in CL as [CL Halt]. apply andb_prop in CL as [CL V13]. apply andb_prop in CL as [CL V5].
    apply andb_prop in CL as [CL Vst]. apply andb_prop in CL as [_ Hsame].

    assert (E17 : zeval zr1 zl1 (reg (lf_state Lf) 17) = off /\ sv_vars_all below200 (reg (lf_state Lf) 17) = true /\ zsupported (reg (lf_state Lf) 17) = true).
    { apply Bool.orb_prop in Halt. destruct Halt as [Hd|Hf].
      - apply andb_prop in Hd as [E Hge]. apply sv_eqb_sound in E. rewrite E.
        pose proof (proj1 (zh_geu _ _) (hasf_zholds rho' _ w _ Hag HSP Hge VG PsG)) as GE. rewrite ESL, EO in GE.
        split; [|split; assumption]. rewrite EO, off_fold, fold_off_eq. destruct (slack <? off0) eqn:C; [apply Z.ltb_lt in C; lia|reflexivity].
      - apply andb_prop in Hf as [Hf Hge2]. apply andb_prop in Hf as [E Hlt]. apply sv_eqb_sound in E. rewrite E.
        rewrite <- vars_not in VG. rewrite <- psup_not in PsG.
        pose proof (proj1 (zh_ngeu _ _) (hasf_zholds rho' _ w _ Hag HSP Hlt VG PsG)) as LT. rewrite ESL, EO in LT.
        split; [|split; assumption]. rewrite EF, off_fold, fold_off_eq. fold o1.
        destruct (slack <? off0) eqn:C; [reflexivity|apply Z.ltb_ge in C; lia]. }
    destruct E17 as (E17 & V17 & Zs17).
    destruct (sd_7 kd Lf vo vr Hin HR) as (nf & Hsd & Hnf).
    set (sets := [(204%positive, reg (lf_state Lf) 5); (205%positive, reg (lf_state Lf) 13)]).
    eapply (linkp (lf_state Lf) (C7 kd vo vr) sets _ nf rho' w);
      [exact Vst | reflexivity | apply swf_C7 | exact Hsd | exact Hag | | exact HSP].
    intros HagS _. split.
    + unfold diffs_ok, d7_of.
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
      * change (eval ?r (SVar 204)) with (rw r 204%positive).
        rewrite (setp_get rho' sets 204%positive (reg (lf_state Lf) 5) eq_refl) by (subst sets; cbn; tauto).
        rewrite (eval_agrees rhoW _ _ HagS V5), (eval_agrees rhoW _ _ Hag V5). reflexivity.
      * change (eval ?r (SVar 205)) with (rw r 205%positive).
        rewrite (setp_get rho' sets 205%positive (reg (lf_state Lf) 13) eq_refl) by (subst sets; cbn; tauto).
        rewrite (eval_agrees rhoW _ _ HagS V13), (eval_agrees rhoW _ _ Hag V13). reflexivity.
      * rewrite (EV _ _ HagS V17 Zs17). change (eval ?r (SVar 158)) with (rw r 158%positive).
        rewrite (rw_agrees _ 158%positive HagS eq_refl). rewrite E17. unfold U.Mal_malloc__G2.Mal_malloc_fastI.rw1. cbn [Pos.eqb]. reflexivity.
    + eapply incl_Forall; [exact Hnf|]. apply Forall_app. split; [apply F_all_hold; exact HagS | apply F7_hold; exact HagS].
  -
    exfalso. apply andb_prop in CL as [Hlt Hnge].
    rewrite <- vars_not in VG, VGF. rewrite <- psup_not in PsG, PsGF.
    pose proof (proj1 (zh_ngeu _ _) (hasf_zholds rho' _ w _ Hag HSP Hlt VG PsG)) as LT. rewrite ESL, EO in LT.
    pose proof (proj1 (zh_ngeu _ _) (hasf_zholds rho' _ w _ Hag HSP Hnge VGF PsGF)) as LT2. rewrite ESL, EF in LT2.
    pose proof (fold_off_ok slack off0 ltac:(lia) HO0) as FO. rewrite fold_off_eq in FO. fold o1 in FO.
    rewrite (proj2 (Z.ltb_lt slack off0) LT) in FO. destruct (slack <? o1); lia.
Qed.

Ltac zpeel :=
  repeat (first
    [ rewrite ZE_strideT | rewrite ZE_strideM by lia | rewrite ZE_and155 by lia | rewrite ZE_sll | rewrite ZE_S
    | rewrite ze_alu | rewrite ze_aluw | rewrite ze_mul | rewrite ze_ext | rewrite ze_lbytes | rewrite ze_var | rewrite ze_lit ]).
Ltac zev2 :=
  cbn [E_pn E_p E_p0 E_stride E_strideT E_strideM E_S E_sll E_X E_X0 E_X1 E_lowbit v];
  zpeel; cbn [zalu Z.of_N]; zlits;
  rewrite ?Zv12, ?Zv142, ?Zv143, ?Zv149, ?Zv150, ?Zv151, ?Zv152, ?Zv153, ?Zv154, ?Zv155, ?Zv156, ?Zv157, ?Zv158, ?Zv164, ?Zv165;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  rewrite ?land_255, ?land_31'.

Lemma single_leaf : ltac2:(tb__ "0|1|
S22SbeA1S23S6SbfA2M0SbeS0S22G0A1S11bSbeG0S74R3A4S1fG0R2S28G0A1A3A3Sc7SbeR2R4A3S1S0SbeR3S11aSbeU0R5Sc6S10cSc3A2A4A3S0G0S74R3A1R4A3A2F_;F_;FLf;Fst;Fl;").
Proof using .
  intros [|x [|y t]] st Lf Hm Hin; cbn in Hm; try discriminate.
  injection Hm as Hm. destruct Hin as [<-|[]]. cbn. auto.
Qed.

Lemma L8_single : ltac2:(tb__ "0|0|
S6fS71S70SbeSc7SbeR1S109R4R3R2A3A3S1S0S47Sc0R2A1S105R5R4R3A3A3S0S23S6SbfA2S74R2A1S10dR3A1A3A2F_;FLf;Fr;Fo;Fkd0;").
Proof using .
  intros kd0 o r Lf Hin. destruct (single_leaf _ _ _ (L8_shape kd0 o r) Hin) as [E Hs]. split; [|exact Hs].
  rewrite E. reflexivity.
Qed.
Lemma L9_single : ltac2:(tb__ "0|0|
S6fS71S70SbeS3S0S70R2S72A3A1Sc7SbeR2S10aR5R4R3A3A3S1S0S47Sc0R3A1S10bR6R5R4A3A3S0S23S6SbfA2S74R3A1S21S6SbfS8bS6eA1Sc5A4A3A2F_;F_;FLf;Fr;Fo;Fkd0;").
Proof using .
  intros kd0 o r Lf Hr Hin. destruct (single_leaf _ _ _ (L9_shape kd0 o r Hr) Hin) as [E Hs]. split; [|exact Hs].
  rewrite E. reflexivity.
Qed.

Lemma sd_88 : ltac2:(tb__ "0|4|
S6fS71S70S3S0S70R1S72A3A1S0S20S23S22S23S2eS2eA2A1M0S22S33A1M1A2M2A1S11eS105R4R3R2A3S106R4R3R2A3A2S24G2S21G0G1S29G0G1S108R4R3R2A3M3A3S2aG0G1G3A3A4A2A3F_;Fr;Fo;Fkd0;").
Proof using .
  intros kd0 o r Hr; destruct kd0, o, r; try (exfalso; exact (Hr eq_refl));
  match goal with |- _ = Some (fst ?d, _) => let dv := eval vm_compute in d in
    vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dv)) end.
Qed.
Lemma swf_C8 : ltac2:(tb__ "0|0|
S6fS71S70S3S0S70R1S72A3A1S0S1dS4fS106R4R3R2A3A1S1eA3F_;Fr;Fo;Fkd0;").
Proof using . intros kd0 o r Hr; destruct kd0, o, r; try (exfalso; exact (Hr eq_refl)); vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars_L8s : ltac2:(tb__ "0|1|
S6fS71S70S3S0S70R1S72A3A1S0S1dSceS7S2dS96S11bS23S7S2eA2M0S7S29S7S2eA2S28G0A1A4R1A2A1Lu;S105R4R3R2A3A2S1eA3F_;Fr;Fo;Fkd0;").
Proof using . intros kd0 o r Hr; destruct kd0, o, r; try (exfalso; exact (Hr eq_refl)); vm_cast_no_check (@eq_refl bool true). Qed.

Lemma kd_cases : ltac2:(tb__ "0|4|
S2S1S0S6fS9bVam;A1M0S90A3S3S0S6S13aVam;A1Z0M1A3M2A1A2S2S1S0S6fG0S91A3S1G2S0S6S136Vam;A1M3G1A3A2A2S1S0S6fG0S82A3S1G2ScG1G3A2A2A2A2A2").
Proof using HC HW Hb16 Hb3 Hsp.
  unfold U.Mal_malloc__G2.Mal_malloc_fastI.kd, kind_of. pose proof Hmaplen.
  destruct (am_last am =? 0) eqn:EL; [apply Z.eqb_eq in EL|apply Z.eqb_neq in EL].
  - destruct (am_maplen am =? 0) eqn:EM; [apply Z.eqb_eq in EM|apply Z.eqb_neq in EM]; [right; left|right; right]; repeat split; lia.
  - left. split; [reflexivity|exact EL].
Qed.
Lemma vo_cases : ltac2:(tb__ "0|1|
S2S1S0S71SdbS85A3S0S6Sa0Vs;Vn;Vam;Vb3;Vb16;A5M0Z0A3A2S1S0S71SdbS86A3S1SbZ1G0A2SbG0ZffA2A2A2A2").
Proof using HC HW Hb16 Hb3 rho. unfold vo. pose proof Hoff. destruct (off =? 0) eqn:E; [apply Z.eqb_eq in E; left | apply Z.eqb_neq in E; right]; split; auto; lia. Qed.
Lemma vr_cases : ltac2:(tb__ "0|0|
S2S1S0S70Sd9S72A3S0S6SdaZ0A3A2S2S1S0S70Sd9S88A3S1SbZ1SdaA2SbSdaZ4A2A2A2S2S1S0S70Sd9S89A3S0S6SdaZ5A3A2S1S0S70Sd9S8aA3SbZ6SdaA2A2A2A2A2").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp.
  unfold vr. pose proof rsv_range.
  destruct (rsv =? 0) eqn:E0; [apply Z.eqb_eq in E0; left; auto|apply Z.eqb_neq in E0].
  destruct (rsv <=? 4) eqn:E4; [apply Z.leb_le in E4; right; left; split; auto; lia|apply Z.leb_gt in E4].
  destruct (rsv =? 5) eqn:E5; [apply Z.eqb_eq in E5; right; right; left; auto|apply Z.eqb_neq in E5].
  right; right; right. split; auto; lia.
Qed.

Lemma stv_VM1 : ltac2:(tb__ "0|0|
S0S6fS9bVam;A1S82A3S0S6S9dVam;A1SdSeS136Vam;A1Z1000A2Z10A2A3F_;").
Proof using HC HW Hb16 Hb3 Hsp. intros E. rewrite Hstv. destruct kd_cases as [[Kk ?]|[[Kk ?]|[Kk [HL HM]]]]; rewrite Kk in E; try discriminate.
  rewrite HL. cbn [Z.eqb andb]. destruct (am_maplen am =? 0) eqn:EM; [apply Z.eqb_eq in EM; lia|]. cbn. unfold UNIT. lia. Qed.
Lemma stv_T : ltac2:(tb__ "0|0|
S3S0S6fS9bVam;A1S82A3A1S0S6S9dVam;A1SeZ10Sb7Vam;A1A2A3F_;").
Proof using HC HW Hb16 Hb3 Hsp. intros E. rewrite Hstv. destruct kd_cases as [[Kk HL]|[[Kk [HL HM]]|[Kk ?]]]; [| |exfalso; exact (E Kk)].
  - apply Z.eqb_neq in HL. rewrite HL. reflexivity.
  - rewrite HL, HM. reflexivity. Qed.

Lemma link_8 : ltac2:(tb__ "0|1|
S3cS12cS3S0S70Sd9S72A3A1S95VrhoW;R3A2S11fS66VK;S105S9bVam;A1M0SdbSd9A3R4R3A5S132Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;VK;VmW;S106G0SdbSd9A3R4AcF_;F_;F_;Fw;Frho';").
Proof using HC HMI HP12 HW Hb16 Hb3 Hhdr Hsp.
  intros rho' w Hr Hag HSP. pose proof R_all as R. pose proof rsv_range as RR. pose proof Hoff as HO.
  eapply (linkp (L8s kd vo vr) (C8 kd vo vr) [] _ _ rho' w); [apply vars_L8s; exact Hr | reflexivity | apply swf_C8; exact Hr | apply sd_88; exact Hr | exact Hag | | exact HSP].
  intros HagS _.
  pose proof stv_VM1 as SM. pose proof stv_T as ST.
  destruct kd_cases as [[Kk KF]|[[Kk KF]|[Kk KF]]]; rewrite Kk in *;
  destruct vo_cases as [[Ko OF]|[Ko OF]]; rewrite Ko in *;
  destruct vr_cases as [[Kr RF]|[[Kr RF]|[[Kr RF]|[Kr RF]]]]; rewrite Kr in *; try (exfalso; exact (Hr eq_refl));
  cbn [D88 fst snd]; (split; [|constructor]); unfold diffs_ok;
  (apply Forall_cons; [cbn [fst snd] | apply Forall_nil]); sem_pair HagS; zev2;
  unfold rsv in *; first [specialize (SM eq_refl) | specialize (ST ltac:(discriminate))]; mlia.
Qed.

Definition FINAL : assn := ltac2:(tb__ "0|0|
S132Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;VK;VmW;S102S9bVam;A1SdbSd9A3Ab").

Theorem chain : ltac2:(tb__ "0|0|
S12dS66Vok;S11fS66VK;S75S6eS9bVam;A1A2VrhoW;A4Se4A4").
Proof using HC HK HMI HP12 HW Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high.
  eapply triple_seq; [apply pro_C6|].
  apply from_POST. intros r6 Hag6.
  eapply triple_seq.
  { apply (seg_run 200 (C6 kd) (L7 kd) (POST (C7 kd vo vr)) r6); [apply (proj1 (lnx_C6 kd)) | apply (proj2 (lnx_C6 kd)) | apply run7 | exact Hag6 |].
    intros Lf rho'' w Hin Hag HSP. exact (link_7 Lf rho'' w Hin Hag HSP). }
  apply from_POST. intros r7 Hag7.
  destruct vr_cases as [[Kr _]|Hnz].
  -
    apply (seg_run 200 (C7 kd vo vr) (L8 kd vo vr) FINAL r7); [apply (proj1 (lnx_C7 kd vo vr)) | apply (proj2 (lnx_C7 kd vo vr)) | apply run8 | exact Hag7 |].
    intros Lf rho'' w Hin Hag HSP. destruct (L8_single kd vo vr Lf Hin) as [E _].
    exists rho''. split; [exact Hag|]. unfold LF. rewrite Kr in *. rewrite <- E. exact HSP.
  - assert (Hr : vr <> RZ) by (destruct Hnz as [[-> _]|[[-> _]|[-> _]]]; discriminate).
    eapply triple_seq.
    { apply (seg_run 200 (C7 kd vo vr) (L8 kd vo vr) (POST (C8 kd vo vr)) r7); [apply (proj1 (lnx_C7 kd vo vr)) | apply (proj2 (lnx_C7 kd vo vr)) | apply run8 | exact Hag7 |].
      intros Lf rho'' w Hin Hag HSP. destruct (L8_single kd vo vr Lf Hin) as [E _].
      apply (link_8 rho'' w Hr Hag). rewrite <- E. exact HSP. }
    apply from_POST. intros r8 Hag8.
    apply (seg_run 100 (C8 kd vo vr) (L9 kd vo vr) FINAL r8); [apply (proj1 (lnx_C8 kd vo vr)) | apply (proj2 (lnx_C8 kd vo vr)) | apply run9; exact Hr | exact Hag8 |].
    intros Lf rho'' w Hin Hag HSP. destruct (L9_single kd vo vr Lf Hr Hin) as [E _].
    exists rho''. split; [exact Hag|]. unfold LF. rewrite <- E. destruct Hnz as [[-> _]|[[-> _]|[-> _]]]; exact HSP.
Qed.

End InstD.
End Mal_malloc_fastD.

Module Mal_malloc_fastG.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageUpd OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fast_enum OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quick2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Lemma ro_tables : ltac2:(tb__ "0|0|
S6S1SbZ0R1A2ScR1Z80A2A2S0S1dS5fS66S6cQ40SaZ108ccR2A2A2A2S1eA3F_;Fkk;").
Proof.
  intros kk Hk. exact (forall_range_dec (fun kk => ro_addr segsU (Z_to_bv 64 (0x108cc + kk))) 0 128 ltac:(vm_compute; reflexivity) kk ltac:(lia)).
Qed.

Record instH (s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta) (rho : valuation) (md : Model) (ms : machine_state) (b3 b16 : Z) : Prop := mkInstH {
  ih_W : WF s;
  ih_C : loop_case s n g am;
  ih_L : layout_ok L s;
  ih_12 : bv_unsigned (rw rho 12%positive) = n;
  ih_b3 : 0 <= b3 < 256;
  ih_b16 : 0 <= b16 < 65536;
  ih_hdr : forall h3 h16, ss_hdr (nth_slot am (mf_idx am)) = Some (h3, h16) -> b3 = h3 /\ b16 = h16;
  ih_MI : MInv C_U (mkMA s L) (Glue.rd_of segsU (rm rho)) (Glue.wok_of segsU (rm rho)) (m_vmmaps md);
  ih_sp : 4096 <= bv_unsigned (rw rho 10%positive) /\ bv_unsigned (rw rho 10%positive) mod 16 = 0;
  ih_depth : toS 64 (bv_unsigned (rw rho 15%positive)) <= - malloc_stack /\ - 2 ^ 40 <= toS 64 (bv_unsigned (rw rho 15%positive));
  ih_high : topL L <= bv_unsigned (rw rho 10%positive) + toS 64 (bv_unsigned (rw rho 15%positive));
  ih_rom : rom_ok segsU ms;
  ih_sct : forall kk, 0 <= kk < 96 -> rm rho (Z_to_bv 64 (0x108ec + kk)) = None;
  ih_ctz : forall kk, 0 <= kk < 32 -> rm rho (Z_to_bv 64 (0x108cc + kk)) = None;
  ih_m3 : Glue.rd_of segsU (rm rho) (Z_to_bv 64 (zSt L am - 3)) = Some (Z_to_bv 8 b3);
  ih_m16 : forall j, (j < 2)%nat -> Glue.rd_of segsU (rm rho) (Z_to_bv 64 (zSt L am - 2 + Z.of_nat j)) = Some (Z_to_bv 8 (le_byte b16 2 j))
}.

Section Instantiate.
Variables (s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta).
Variables (rho : valuation) (tr : list event) (ms : machine_state) (md : Model).

Hypothesis Hsm : ltac2:(tb__ "0|0|
S45S66Vrho;S114S113A1S21S22S10eA1S11cVtr;S11dVms;Vmd;A2A4A4").
Hypothesis HMI0 : ltac2:(tb__ "0|1|
S122S100S121Vs;VL;A2S97S66S35Vrho;A1M0A2S98S66G0A2S110Vmd;A1A5").
Hypothesis HC : ltac2:(tb__ "0|0|
S12eVs;Vn;Vg;Vam;A4").
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S6S6dQ40S37Vrho;PcA2A2Vn;A3").

Hypothesis Htop : ltac2:(tb__ "0|0|
S118S121Vs;VL;A2Vrho;A2").

Lemma I_WF : WF s. Proof using HMI0. exact (proj1 HMI0). Qed.
Lemma I_Lok : layout_ok L s. Proof using HMI0. exact (proj1 (proj1 (proj1 (proj2 (proj2 (proj2 HMI0)))))). Qed.
Lemma I_reprO : ltac2:(tb__ "0|1|
S13eVL;Vs;S101S97S66S35Vrho;A1M0A2S98S66G0A2A2A3").
Proof using HMI0. exact (proj1 (proj2 (proj2 (proj2 HMI0)))). Qed.

Lemma I_facts : ltac2:(tb__ "0|0|
S119S33S51Vrho;A1S2bS33S1fS33S116S1fS33S117SfeA1S28S33A1A3A3S115SfeA1A3A3").
Proof using Hsm.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))) as HF. cbn [ss_facts Pre_malloc] in HF.
  apply Forall_app in HF as [HF1 HF2]. apply Forall_app in HF2 as [HF2 _]. apply Forall_app. split; [exact HF1 | exact HF2].
Qed.

Let u10 := bv_unsigned (rw rho 10%positive).
Let u15 := bv_unsigned (rw rho 15%positive).

Lemma I_depth : ltac2:(tb__ "0|1|
S1SbSbcZ40Vu15;A2M0S10SfeA1A2SbS10SfZ2Z28A2A1G0A2A2").
Proof using Hsm u10.
  pose proof I_facts as F.
  assert (H1 : SymState.holds rho (SPBranch BC_GE (SLit (- malloc_stack)) (SVar V_DEPTH))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  assert (H2 : SymState.holds rho (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40)))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  rewrite (holds_zholds rho) in H1 by reflexivity. rewrite (holds_zholds rho) in H2 by reflexivity.
  cbn [zholds zcond zeval] in H1, H2. unfold V_DEPTH, zr_of in H1, H2. fold u15 in H1, H2.
  rewrite (toS_mod 64 u15) in H1, H2 by lia.
  replace (toS 64 ((- malloc_stack) mod 2 ^ 64)) with (- malloc_stack) in H1 by reflexivity.
  replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) in H2 by reflexivity.
  apply Bool.negb_true_iff in H1. apply Z.ltb_ge in H1. apply Bool.negb_true_iff in H2. apply Z.ltb_ge in H2. lia.
Qed.

Lemma I_align : u10 mod 16 = 0.
Proof using Hsm.
  pose proof (proj1 (Forall_forall _ _) I_facts F_sp_aligned ltac:(left; reflexivity)) as H. cbn in H. exact (proj2 H).
Qed.

Lemma I_stack_lo : ltac2:(tb__ "0|0|
SbZ0SaVu10;SbcZ40Vu15;A2A2A2").
Proof using Hsm.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [ss_objs Pre_malloc] in Hall.
  pose proof (proj1 (Forall_forall _ _) Hall (stack_win malloc_stack) ltac:(left; reflexivity)) as ((Hb & _) & _).
  unfold obj_lo_of, stack_win in Hb. cbn [ob_base ob_lo eval] in Hb. unfold soff in Hb. cbn [eval] in Hb.
  rewrite bv_signed_toS in Hb by (cbn; lia). change (Z.of_N 64) with 64 in Hb. unfold V_DEPTH in Hb. fold u10 u15 in Hb. lia.
Qed.

Lemma I_sp_high : ltac2:(tb__ "0|0|
SbSffVL;A1SaVu10;SbcZ40Vu15;A2A2A2").
Proof using Htop. pose proof Htop as H. unfold top_high, V_DEPTH in H. cbn [ma_L] in H. exact H. Qed.

Lemma I_sp : ltac2:(tb__ "0|0|
S1SbZ1000Vu10;A2S0S6S16Vu10;Z10A2Z0A3A2").
Proof using Hsm Htop u15. pose proof I_sp_high. pose proof I_depth. pose proof I_align. unfold malloc_stack in *. top_ranges. lia. Qed.

Lemma I_rom_clear : ltac2:(tb__ "0|1|
S6S1SbZ0R1A2ScR1Z80A2A2S0S20S6bQ8A1M0A1S35Vrho;S6cQ40SaZ108ccR2A2A2A2S26G0A1A3F_;Fkk;").
Proof using Hsm Htop.
  intros kk Hkk.
  destruct Hsm as (_ & _ & _ & _ & _ & Hro & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hro, Hfr.
  rewrite <- Hfr.
  - apply Hro. apply ro_tables. exact Hkk.
  - cbn [ss_objs Pre_malloc]. constructor; [|constructor].
    unfold obj_range, obj_lo_of, stack_win. cbn [ob_base ob_lo ob_hi eval fst snd].
    pose proof I_sp_high as SH. pose proof I_stack_lo. unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia).
    change (Z.of_N 64) with 64. unfold V_DEPTH. rewrite u64 by lia. top_ranges. unfold u10, u15 in *. lia.
Qed.

Lemma I_zone_byte : ltac2:(tb__ "0|1|
S6S1SbSdS9cVL;Vam;A2Z4A2R1A2ScR1SabVL;Vam;A2A2A2S4S6bQ8A1M0G0S0S20G0A1S97S66S35Vrho;A1S6cQ40R3A2A3S24G0R1A2A3Lb;A2F_;Fx;").
Proof using HC HMI0.
  intros x Hx.
  pose proof (slot_owned C_U s L n g am 0 _ _ (m_vmmaps md) HMI0 HC ltac:(lia) x) as OW.
  unfold f_st, f_e, f_idx in OW. change (addr_of L (slot_start am (mf_idx am))) with (zSt L am) in OW.
  change (addr_of L (slot_end am (mf_idx am))) with (zE L am) in OW. specialize (OW Hx).
  pose proof (proj2 (proj2 (proj1 I_reprO)) x OW) as M.
  destruct (byteview_of (Glue.rd_of segsU (rm rho)) (Glue.wok_of segsU (rm rho)) x) as [vv|] eqn:E; [|exfalso; exact (M eq_refl)].
  destruct (byteview_of_Some _ _ _ _ E) as (_ & _ & bb & Hb & _). exists bb. exact Hb.
Qed.

Lemma I_bytes : ltac2:(tb__ "0|5|
S4S6bQ8A1M0G0S4G0G0S4G0G0S1S0S20G0A1M1S97S66S35Vrho;A1M2S6cQ40M3SdS9cVL;Vam;A2M4Z3A2A2A3S24G0R3A2A3S1S0G1S97S66G2S6cG3SdG4Z2A2A2A3S24G0R2A2A3S0G1S97S66G2S6cG3SdG4Z1A2A2A3S24G0R1A2A3A2A2Lqhi;A2Lqlo;A2Lq3;A2").
Proof using HC HMI0.
  pose proof (F_geom C_U s L n g am 0 _ _ (m_vmmaps md) HMI0 HC ltac:(lia)) as (Sp & E1 & E2 & E3 & _).
  unfold f_st, f_e, f_idx, IB, UNIT in *.
  change (addr_of L (slot_start am (mf_idx am))) with (zSt L am) in *. change (addr_of L (slot_end am (mf_idx am))) with (zE L am) in *.
  destruct (I_zone_byte (zSt L am - 3) ltac:(lia)) as [q3 H3].
  destruct (I_zone_byte (zSt L am - 2) ltac:(lia)) as [qlo Hlo].
  destruct (I_zone_byte (zSt L am - 1) ltac:(lia)) as [qhi Hhi].
  exists q3, qlo, qhi. auto.
Qed.

Definition f_keep (j : positive) : bool := negb (rw1_changed j).
Lemma Pre_vars : ltac2:(tb__ "0|0|
S0S1dSceS13fS114S113A1A2S1eA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma Pre_nolist1 : ltac2:(tb__ "0|0|
S0S1dS133P1S114S113A1A2S27A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma Pre_nolist4 : ltac2:(tb__ "0|0|
S0S1dS133P4S114S113A1A2S27A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_S2 : ltac2:(tb__ "0|0|
S137S0S1dS4fSa8R1A1A1S1eA3Fam';").
Proof using . intros am'. unfold S2, kd, kind_of. destruct (am_last am' =? 0); [destruct (am_maplen am' =? 0)|]; vm_compute; reflexivity. Qed.
Lemma sd_Pre_S2 : ltac2:(tb__ "0|4|
S137S4S22S33A1M0G0S1S0S20S23S22S23S2eS2eA2M1A1M2G0A2M3A1S11eS114S113A1Sa8R2A1A2S24G3S21G2G0S28G1A1R1A4A2A3ScaS33R1S78S9bR2A1A1A3A2Lnf;A2Fam';").
Proof using .
  intros am'. unfold S2. generalize (F_all (kd am')). intros facts.
  eexists. split; [|apply incl_filter]. unfold state_diff. cbn -[List.filter]. reflexivity.
Qed.

Theorem instantiate : ltac2:(tb__ "0|0|
S4S6S6S4S6S6S1S129Vs;VL;Vn;Vg;Vam;Vrho;Vmd;Vms;R2R1AaS45S66Sa6Vs;VL;Vn;Vg;Vam;Vrho;R2R1S35Vrho;A1A9S75S6eS9bVam;A1A2S21S22S10eA1S11cVtr;S11dVms;Vmd;A2A4A4A2Lb16;A2Lb3;A2").
Proof using HC HMI0 HP12 Hsm Htop.
  destruct I_bytes as (q3 & qlo & qhi & H3 & Hlo & Hhi).
  set (b3 := bv_unsigned q3). set (b16 := bv_unsigned qlo + 256 * bv_unsigned qhi).
  pose proof (urange_n 8 q3) as R3. pose proof (urange_n 8 qlo) as Rlo. pose proof (urange_n 8 qhi) as Rhi. change (2 ^ Z.of_N 8) with 256 in R3, Rlo, Rhi.
  assert (Hb3 : 0 <= b3 < 256) by (subst b3; lia).
  assert (Hb16 : 0 <= b16 < 65536) by (subst b16; lia).
  assert (Hm3 : Glue.rd_of segsU (rm rho) (Z_to_bv 64 (zSt L am - 3)) = Some (Z_to_bv 8 b3)).
  { rewrite H3. f_equal. subst b3. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (Hm16 : forall j, (j < 2)%nat -> Glue.rd_of segsU (rm rho) (Z_to_bv 64 (zSt L am - 2 + Z.of_nat j)) = Some (Z_to_bv 8 (le_byte b16 2 j))).
  { intros [|[|j]] Hj; [| | lia]; cbn [Z.of_nat].
    - rewrite Z.add_0_r, Hlo. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 qlo) at 1. apply Z_to_bv8_eq || f_equal.
      unfold le_byte. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
      rewrite (Z.mod_small b16) by lia. rewrite Z.mod_mod by lia. subst b16. rewrite Z.mul_comm, Z.mod_add by lia. rewrite !Z.mod_small; lia.
    - replace (zSt L am - 2 + Z.of_nat 1) with (zSt L am - 1) by lia. rewrite Hhi. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 qhi) at 1. f_equal.
      unfold le_byte. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (8 * Z.of_nat 1) with 8. rewrite (Z.mod_small b16) by lia.
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. subst b16.
      rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. rewrite !Z.mod_small; lia. }

  assert (Hhdr : forall h3 h16, ss_hdr (nth_slot am (mf_idx am)) = Some (h3, h16) -> b3 = h3 /\ b16 = h16).
  { intros h3 h16 Eh.
    pose proof (F_idx C_U s L n g am _ _ (m_vmmaps md) HMI0 HC) as (Hi & _).
    pose proof (slot_start_cells s g am (mf_idx am) I_WF (Hum s n g am I_WF HC) Hi) as [_ SC]. rewrite Eh in SC. destruct SC as [C3 C16].
    pose proof (inv_groups I_WF g am (Hu s n g am HC)) as (_ & _ & Gsl & _). pose proof (Gsl _ Hi) as (_ & Hr & _).
    destruct (Hr h3 h16 Eh) as [R3' R16'].
    assert (AS : forall d, loc_addr L (LMem (padd (slot_start am (mf_idx am)) d)) = zSt L am + d).
    { intros d. unfold zSt, idx, addr_of, loc_addr. destruct (slot_start am (mf_idx am)); cbn [padd]. lia. }
    pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 I_reprO))) _ C3) as CH3.
    pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 I_reprO))) _ C16) as CH16.
    destruct (cell_bytes L _ _ _ h3 CH3 eq_refl 0%nat ltac:(cbn; lia)) as (_ & _ & B3). cbn [mc_loc mc_w Z.of_nat] in B3. rewrite AS, Z.add_0_r in B3.
    replace (zSt L am + -3) with (zSt L am - 3) in B3 by lia. rewrite Hm3 in B3.
    destruct (cell_bytes L _ _ _ h16 CH16 eq_refl 0%nat ltac:(cbn; lia)) as (_ & _ & B16a). cbn [mc_loc mc_w Z.of_nat] in B16a. rewrite AS, Z.add_0_r in B16a.
    destruct (cell_bytes L _ _ _ h16 CH16 eq_refl 1%nat ltac:(cbn; lia)) as (_ & _ & B16b). cbn [mc_loc mc_w Z.of_nat] in B16b. rewrite AS in B16b.
    replace (zSt L am + -2) with (zSt L am - 2 + Z.of_nat 0) in B16a by lia. rewrite (Hm16 0%nat ltac:(lia)) in B16a.
    replace (zSt L am + -2 + Z.of_nat 1) with (zSt L am - 2 + Z.of_nat 1) in B16b by lia. rewrite (Hm16 1%nat ltac:(lia)) in B16b.
    apply (f_equal (fun o => match o with Some b => bv_unsigned b | None => 0 end)) in B3.
    apply (f_equal (fun o => match o with Some b => bv_unsigned b | None => 0 end)) in B16a.
    apply (f_equal (fun o => match o with Some b => bv_unsigned b | None => 0 end)) in B16b.
    cbn beta iota in B3, B16a, B16b.
    rewrite !Z_to_bv_unsigned in B3, B16a, B16b.
    assert (M8 : forall z, bv_wrap 8 z = z mod 256) by (intros; reflexivity). rewrite !M8 in B3, B16a, B16b.
    unfold le_byte in *. change (2 ^ (8 * Z.of_nat 1)) with 256 in *. change (2 ^ (8 * Z.of_nat 2)) with 65536 in *.
    change (8 * Z.of_nat 0) with 0 in *. change (8 * Z.of_nat 1) with 8 in *. rewrite !Z.shiftr_0_r in *.
    rewrite !Z.shiftr_div_pow2 in * by lia. change (2 ^ 8) with 256 in *.
    split.
    - rewrite (Z.mod_small b3), (Z.mod_small h3), Z.mod_mod in B3 by lia. rewrite Z.mod_small in B3 by lia. exact B3.
    - rewrite (Z.mod_small b16 65536), (Z.mod_small h16 65536) in * by lia. rewrite !Z.mod_mod in * by lia.
      pose proof (Z.div_mod b16 256 ltac:(lia)). pose proof (Z.div_mod h16 256 ltac:(lia)).
      rewrite (Z.mod_small (b16 / 256) 256), (Z.mod_small (h16 / 256) 256) in B16b by lia. lia. }
  exists b3, b16.
  assert (IH : instH s L n g am rho md ms b3 b16).
  { refine (mkInstH _ _ _ _ _ _ _ _ _ _ I_WF HC I_Lok HP12 Hb3 Hb16 Hhdr HMI0 I_sp I_depth I_sp_high _ _ _ Hm3 Hm16).
    - exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
    - intros kk Hkk. replace (0x108ec + kk) with (0x108cc + (32 + kk)) by lia. apply I_rom_clear. lia.
    - intros kk Hkk. apply I_rom_clear. lia. }
  split; [exact IH|].

  set (rhoW := rho1 s L n g am rho b3 b16 (rm rho)).
  assert (Hsm1 : smatch segsU (mkVal (rw rhoW) (rl rho) (rm rho)) (Pre_malloc EC_U) (tr, mkCfg ms md)).
  { apply (smatch_agree_vars segsU f_keep rho); [| intros; reflexivity | reflexivity | apply Pre_vars | exact Hsm].
    intros v Hv. cbn [rw]. unfold rhoW, rho1. cbn [rw]. symmetry. apply rw1_other. unfold f_keep in Hv. destruct (rw1_changed v); [discriminate|reflexivity]. }
  assert (Hsm2 : smatch segsU rhoW (Pre_malloc EC_U) (tr, mkCfg ms md)).
  { replace rhoW with (rho_set_rl (rho_set_rl (mkVal (rw rhoW) (rl rho) (rm rho)) 4 (map (Z_to_bv 8) ctz_tab_bytes)) 1 (map (Z_to_bv 8) size_classes_bytes)).
    - apply SymCall.smatch_set_rl; [apply Pre_nolist1|]. apply SymCall.smatch_set_rl; [apply Pre_nolist4|]. exact Hsm1.
    - unfold rhoW, rho1, rho_set_rl. cbn [rw rl rm]. f_equal. }
  destruct (sd_Pre_S2 am) as (nf & Hsd & Hnf).
  assert (Hsm3 : smatch segsU rhoW (S2 am) (tr, mkCfg ms md)).
  { apply (smatch_restate segsU _ (Pre_malloc EC_U) (S2 am) _ [] nf Hsm2); [apply swf_S2 | exact Hsd | constructor |].
    eapply incl_Forall; [exact Hnf|]. unfold rhoW.
    exact (facts_hold s L n g am rho b3 b16 I_WF HC HP12 Hb3 Hb16 Hhdr _ _ _ HMI0 I_sp I_depth I_sp_high (rm rho)). }
  unfold rhoW.
  exact (carve s L n g am rho b3 b16 I_WF HC I_Lok Hb3 Hb16 Hhdr _ _ _ HMI0 I_sp I_depth I_sp_high (rm rho) eq_refl eq_refl ms
           (ih_rom _ _ _ _ _ _ _ _ _ _ IH) (ih_sct _ _ _ _ _ _ _ _ _ _ IH) (ih_ctz _ _ _ _ _ _ _ _ _ _ IH) Hm3 Hm16 tr md Hsm3).
Qed.

End Instantiate.

Lemma cell_bytes_sym : ltac2:(tb__ "0|3|
S3cSedS2fS34S2cS3bS66R5R4R3A4Sc7S34R3S43R4A1A3S12aR3S19S42R4A1A1A2S0S20S6bQ8M0A1M1A1S44R7S6cQ40M2SaSaS6dG2S38R8S39R6A1A2A2S3aR8S3eR5A1A2A2S18R4A1A2A2A2S24G1S11aG1R4S5dS19S42R5A1A1S38R8S4aR5A1A2A2S6cG0Z0A2A4A2A3F_;F_;F_;Fj;Fc;Fo;FmsX;FrhoX;").
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
S3cS22S34A1S6S12bS5cR3R2R1A3M0S3G0A1A2Foff;Fcs;FrhoX;").
Proof. intros rhoX cs off. unfold covered. apply Exists_dec. intros c. apply in_cell_dec. Qed.

Lemma dunk_byte : ltac2:(tb__ "0|4|
S3cSedS2fS6S3bS66R4R3R2A4S0S55S52R3A1S3dA3S1SbS29S6S6S32R6R4A2M0A3R3A2ScR3S2aS6S6G0A3A2A2S1S4S6bQ8A1M1G1S0S20G1A1M2S44R7S6cQ40M3R5A2A2S24G1R1A2A3Lb;A2S3S0G2SeeS66SecR6A1S6cG3R4A2A3S26G1A1A3A1A2F_;F_;F_;Fx;Fo;FmsX;FrhoX;").
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
S6bQ40A1M0S20S6bQ8A1A1M1F_;SedG0S60S66R2A2S0G1R4R2A1SecR3R2A2A3S0G1S97S66R5R3A3S44R4R3A2A3F_;F_;Fa;FmsX;Fm;").
Proof. intros. apply rd_of_eq_rd; assumption. Qed.
Lemma wok_of_at : ltac2:(tb__ "0|3|
S6bQ40A1M0S20S6bQ8A1M1A1M2F_;SedG0S0G2R3R1A1SecR2R1A2A3S3S0G2SeeS66SecR3A1R2A3S26G1A1A3A1S0S1dS98S66R5R3A3S1eA3F_;F_;Fa;FmsX;Fm;").
Proof. intros m msX a E W. rewrite (wok_of_mem m (ms_mem msX) a E). apply wok_of_wview. exact W. Qed.

Lemma shape_range : ltac2:(tb__ "0|0|
S3cS2fS2fS0S2eS39R2A1S39R1A1A3S0S2eS54R3A1S54R2A1A3S0S2eS53R4A1S53R3A1A3S0S23S6S6A2S32R6R5A2S32R6R4A2A3F_;F_;F_;Fb;Fa;FrhoX;").
Proof. intros rhoX a b E1 E2 E3. unfold obj_range, obj_lo_of, obj_hi_of. rewrite E1, E2, E3. reflexivity. Qed.

Lemma lor_low5 : ltac2:(tb__ "0|3|
S6S6SbZ0M0R2A2M1S1G1ScR2Z20M2A2A2S0S6S16R4G2A2G0A3S0S6S15R5R4A2SaR5R4A2A3F_;F_;F_;Fb;Fa;").
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

Definition AVAIL_T : sv := ltac2:(tb__ "0|1|
S4cSf1S50S1eQ20S36P98A1A3M0S31Sf0G0S4cSf1S30Z0A1G0A3A3A3").
Definition meta_cells' : list cell := ltac2:(tb__ "0|2|
S1fS34S3fS30Z18A1Z4M0S128A3S1fS34S3fS30Z10A1Z8M1S36P9cA1A3S1fS34S3fS30Z1cA1G0S36P9aA1A3S1fS34S3fS30Z20A1G1S36P9bA1A3S28S34A1A3A3A3A3").
Definition stk_cells (kd0 : vkind) (o : voff) (r : vrsv) : list cell := ltac2:(tb__ "0|0|
S43S11aS2fU0S46S102Vkd0;Vo;Vr;A3A1S87A4A1").
Definition slot_cells (kd0 : vkind) (o : voff) (r : vrsv) : list cell := ltac2:(tb__ "0|0|
S43S11aS2fU8S46S102Vkd0;Vo;Vr;A3A1S87A4A1").

Lemma LF_objs : ltac2:(tb__ "0|1|
S6fS71S70S0S22S2fA1S46S102R3R2R1A3A1S1fS2fS40S36PaA1S36PfA1S30Z0A1S126R3R2R1A3S3dA5S1fS2fS7eS6eA1S1fS2fS7dS6eA1S1fS2fS7bS6eA1S1fS2fS79S6eA1S1fS2fS7fS6eA1S1fS2fS7cS6eA1S1fS2fS40S112P97A1S30Z10A1S30Z28A1S127S3dA5S1fS2fS40S76R3A1S30N4A1M0S31SefS77R3A1G0A3S125R3R2R1A3S3dA5S1fS2fS7aS6eA1S1fS2fS80S6eA1S1fS2fS81S6eA1S28S2fA1A3A3A3A3A3A3A3A3A3A3A3A3A3Fr;Fo;Fkd0;").
Proof. intros [| |] [|] [| | |]; match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (list sobj) l) end. Qed.

Lemma LF_misc : ltac2:(tb__ "0|1|
S6fS71S70S1S0S6S4eS102R3R2R1A3M0A1S8bS6eA1A3S1S0S7S63G0A1S84A3S1S0S22S2eA1S5aG0A1S69A3S1S0S61S62G0A1S48A3S0S20S2eA1S65G0A1S26S2eA1A3A2A2A2A2Fr;Fo;Fkd0;").
Proof. intros [| |] [|] [| | |]; repeat split; match goal with |- ?l = _ => vm_cast_no_check (eq_refl l) end. Qed.

Lemma LF_regs : ltac2:(tb__ "0|3|
S6fS71S70S6S1SbZ1R1A2SbR1Z1fA2A2S0S2eS57S102R5R4R3A3R2A2M0S1dS2eL_;M1S68S19R2A1M2A1S6aG2A1G1S12R2ZaA2S8eR5R4A2G0X1dx2X1dx2A3F_;Fz;Fr;Fo;Fkd0;").
Proof.
  intros kd0 o r z Hz.
  pose proof (forall_range_dec (fun z => sv_eqb (reg_sv (LF kd0 o r) z)
     (if callee_saved (Z.to_nat z) then pre_reg (Z.to_nat z) else if z =? 10 then E_p kd0 o else reg_sv (LF kd0 o r) z)) 1 31
     ltac:(destruct kd0, o, r; vm_cast_no_check (@eq_refl bool true)) z ltac:(lia)) as H.
  apply sv_eqb_sound in H. exact H.
Qed.

Lemma LF_slot_cells_ok : ltac2:(tb__ "0|b|
S6fS71S70S1S0S1dSc8S34S34S25S25S25S25S25SccS94S3eR1A1M0A2SbaG0A1A2SccS94S4aR1A1M1A2A2SbaG1A1A2S11Z0M2S42R1A1M3A2A2S14G3Z8A2A2Lc;S125R3R2R1A3M4A3S1eA3S1S0S1dSc9S34S13dS3fS30N4A1Z1S30G2A1A3A1G4A3S1eA3S0S1dSc8S34S34S25S2eS1dLx;M5G1S6S27Lz;S7S13cR1P64A2Lj;Sf9S2eS2eS27Lb;La;M6Lop;M7G7SfaG6Lop;M8G8S1dS8S2eS27La;Lw;Lsgn;M9S7S2eS6S27Lk;Li;Ll;MaX2ex8G5G0S6S25S14S10SfZ2Z3eA2A1R1A2S11R1G2A2A2Lz;S7S27Li;G7G7G8G8G9GaX2ex8A2Lc;S126R3R2R1A3A3S1eA3A2A2Fr;Fo;Fkd0;").
Proof. intros kd0 o r; repeat split; destruct kd0, o, r; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma C4_in : ltac2:(tb__ "0|0|
S6fS71S70Sc7S34S3fS30N4A1Z1S30Z0A1A3S125R3R2R1A3A3Fr;Fo;Fkd0;").
Proof.
  intros kd0 o r. destruct (LF_slot_cells_ok kd0 o r) as (_ & H & _).
  apply existsb_exists in H as (c & Hc & E). apply cell_eqb_sound in E. subst c. exact Hc.
Qed.

Section Reab.

Variables (s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta).
Variable rho : valuation.
Variables (b3 b16 : Z).
Hypothesis HW : WF s.
Hypothesis HC : ltac2:(tb__ "0|0|
S12eVs;Vn;Vg;Vam;A4").
Hypothesis HLok : layout_ok L s.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S6S6dQ40S37Vrho;PcA2A2Vn;A3").
Hypothesis Hb3 : 0 <= b3 < 256.
Hypothesis Hb16 : 0 <= b16 < 65536.
Hypothesis Hhdr : ltac2:(tb__ "0|1|
S6S6S0S20S23S6S6A2M0A1S139S138Vam;S130Vam;A1A2A1S24G0S21S6S6R2R1A4A2A3S1S0S6Vb3;R3A3S0S6Vb16;R2A3A2F_;Fh16;Fh3;").
Local Abbreviation sc := (@U.Mal_malloc__G2.Mal_malloc_fastI.sc am).
Local Abbreviation idx := (@U.Mal_malloc__G2.Mal_malloc_fastI.idx am).
Local Abbreviation stv := (@U.Mal_malloc__G2.Mal_malloc_fastI.stv am).
Local Abbreviation zG := (@U.Mal_malloc__G2.Mal_malloc_fastI.zG L g).
Local Notation "§11§ h__" := (h__ L am) (at level 10, h__ global).
Local Abbreviation zMem := (§11§ U.Mal_malloc__G2.Mal_malloc_fastI.zMem).
Local Abbreviation zSt := (§11§ U.Mal_malloc__G2.Mal_malloc_fastI.zSt).
Local Abbreviation zE := (§11§ U.Mal_malloc__G2.Mal_malloc_fastI.zE).
Local Notation "§12§ h__" := (h__ s n am b3 b16) (at level 10, h__ global).
Local Abbreviation off := (§12§ U.Mal_malloc__G2.Mal_malloc_fastI.off).
Local Abbreviation kd := (@U.Mal_malloc__G2.Mal_malloc_fastI.kd am).
Local Abbreviation Hu := (@U.Mal_malloc__G2.Mal_malloc_fastI.Hu s n g am HC).
Local Abbreviation Hum := (@U.Mal_malloc__G2.Mal_malloc_fastI.Hum s n g am HW HC).
Local Abbreviation j164 := (@U.Mal_malloc__G2.Mal_malloc_fastI.j164 s n am).
Local Abbreviation Hj164 := (@U.Mal_malloc__G2.Mal_malloc_fastI.Hj164 s n g am b3 b16 HW HC Hb3 Hb16).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S122S100S121Vs;VL;A2Vrd0;Vwok0;Vvm;A5").
Local Notation "§13§ h__" := (h__ s L n g am rho b3 b16) (at level 10, h__ global).
Local Abbreviation rw1 := (§13§ U.Mal_malloc__G2.Mal_malloc_fastI.rw1).
Local Abbreviation rw1_changed := (@U.Mal_malloc__G2.Mal_malloc_fastI.rw1_changed).
Local Abbreviation rw1_other := (§13§ U.Mal_malloc__G2.Mal_malloc_fastI.rw1_other).
Local Abbreviation rl1 := (@U.Mal_malloc__G2.Mal_malloc_fastI.rl1 rho).
Local Abbreviation rho1 := (§13§ U.Mal_malloc__G2.Mal_malloc_fastI.rho1).
Local Abbreviation zr1 := (§13§ U.Mal_malloc__G2.Mal_malloc_fastI.zr1).
Local Abbreviation zl1 := (§13§ U.Mal_malloc__G2.Mal_malloc_fastI.zl1).
Local Abbreviation R_all := (@U.Mal_malloc__G2.Mal_malloc_fastI.R_all s L n g am b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI).
Local Abbreviation ze_var := (§13§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_var).
Local Abbreviation ze_lit := (§13§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_lit).
Local Abbreviation ze_alu := (§13§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_alu).
Local Abbreviation ze_aluw := (§13§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_aluw).
Local Abbreviation ze_mul := (§13§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_mul).
Local Abbreviation ze_ext := (§13§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_ext).
Local Abbreviation ze_lbytes := (§13§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_lbytes).
Local Notation "§14§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation ze151 := (§14§ U.Mal_malloc__G2.Mal_malloc_fastI.ze151).
Local Abbreviation ze_p0 := (§14§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_p0).
Local Abbreviation ze_actoff := (§14§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_actoff).
Local Abbreviation ze_act0off := (§14§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_act0off).
Local Abbreviation ze_usg0off := (§14§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_usg0off).
Local Abbreviation ze_usg1off := (§14§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_usg1off).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1SbZ1000S6dQ40S37Vrho;PaA2A2M0A2S0S6S16G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1SbSbcZ40S6dQ40S37Vrho;PfA2A2A2M0S10SfeA1A2SbS10SfZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
SbSffVL;A1SaS6dQ40M0S37Vrho;PaA2A2SbcZ40S6dG0S37Vrho;PfA2A2A2A2A2").
Local Notation "§15§ h__" := (h__ s L n g am rho b3 b16 HW HC HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation facts_hold := (§15§ U.Mal_malloc__G2.Mal_malloc_fastI.facts_hold).
Variable m0 : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0S6bQ40A1S20S6bQ8A1A1F_;Vrd0;S97S66Vm0;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0S6bQ40A1S1dF_;Vwok0;S98S66Vm0;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm0_sct : ltac2:(tb__ "0|1|
S6S1SbZ0R1A2ScR1Z60A2A2S0S20S6bQ8A1M0A1Vm0;S6cQ40SaZ108ecR2A2A2A1S26G0A1A3F_;Fkk;").
Hypothesis Hm0_ctz : ltac2:(tb__ "0|1|
S6S1SbZ0R1A2ScR1Z20A2A2S0S20S6bQ8A1M0A1Vm0;S6cQ40SaZ108ccR2A2A2A1S26G0A1A3F_;Fkk;").
Hypothesis Hm3 : ltac2:(tb__ "0|2|
S0S20S6bQ8M0A1M1A1S97S66Vm0;S6cQ40SdS9cVL;Vam;A2Z3A2A2A3S24G1S6cG0Vb3;A2A2A3").
Hypothesis Hm16 : ltac2:(tb__ "0|3|
S2cS12aR1U2M0A2S0S20S6bQ8M1A1M2A1S97S66Vm0;S6cQ40SaSdS9cVL;Vam;A2Z2A2S18R2A1A2A2A3S24G2S6cG1S135Vb16;G0R2A3A2A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S101S97S66Vm0;A2S98S66Vm0;A2A2").
Local Abbreviation HMI0 := (@U.Mal_malloc__G2.Mal_malloc_fastI.HMI0 s L rd0 wok0 vm HMI m0 Erd Ewok).
Local Abbreviation ev1 := (§13§ U.Mal_malloc__G2.Mal_malloc_fastI.ev1).
Local Abbreviation Q_nl := (@U.Mal_malloc__G2.Mal_malloc_fastI.Q_nl).
Local Abbreviation Q_lock := (@U.Mal_malloc__G2.Mal_malloc_fastI.Q_lock).
Local Abbreviation Q_ctr := (@U.Mal_malloc__G2.Mal_malloc_fastI.Q_ctr).
Local Abbreviation Q_act := (@U.Mal_malloc__G2.Mal_malloc_fastI.Q_act).
Local Abbreviation Q_sct := (@U.Mal_malloc__G2.Mal_malloc_fastI.Q_sct).
Local Abbreviation Q_ctz := (@U.Mal_malloc__G2.Mal_malloc_fastI.Q_ctz).
Local Abbreviation Q_meta := (@U.Mal_malloc__G2.Mal_malloc_fastI.Q_meta).
Local Abbreviation Q_slot := (@U.Mal_malloc__G2.Mal_malloc_fastI.Q_slot am).
Local Abbreviation Q_act0 := (@U.Mal_malloc__G2.Mal_malloc_fastI.Q_act0).
Local Abbreviation Q_usg0 := (@U.Mal_malloc__G2.Mal_malloc_fastI.Q_usg0).
Local Abbreviation Q_usg1 := (@U.Mal_malloc__G2.Mal_malloc_fastI.Q_usg1).
Local Abbreviation Q_stk := (@U.Mal_malloc__G2.Mal_malloc_fastI.Q_stk).
Local Notation "§16§ h__" := (h__ s L n g am rho b3 b16 Hb3 Hb16 m0) (at level 10, h__ global).
Local Abbreviation soff_of_ev := (§16§ U.Mal_malloc__G2.Mal_malloc_fastI.soff_of_ev).
Local Abbreviation sp0 := (@U.Mal_malloc__G2.Mal_malloc_fastI.sp0 rho).
Local Abbreviation D0 := (@U.Mal_malloc__G2.Mal_malloc_fastI.D0 rho).
Local Abbreviation rng_stk := (§16§ U.Mal_malloc__G2.Mal_malloc_fastI.rng_stk).
Local Abbreviation rng_nl := (§16§ U.Mal_malloc__G2.Mal_malloc_fastI.rng_nl).
Local Abbreviation rng_lock := (§16§ U.Mal_malloc__G2.Mal_malloc_fastI.rng_lock).
Local Abbreviation rng_ctr := (§16§ U.Mal_malloc__G2.Mal_malloc_fastI.rng_ctr).
Local Notation "§17§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp m0) (at level 10, h__ global).
Local Abbreviation rng_act := (§17§ U.Mal_malloc__G2.Mal_malloc_fastI.rng_act).
Local Abbreviation rng_act0 := (§17§ U.Mal_malloc__G2.Mal_malloc_fastI.rng_act0).
Local Abbreviation rng_usg0 := (§17§ U.Mal_malloc__G2.Mal_malloc_fastI.rng_usg0).
Local Abbreviation rng_usg1 := (§17§ U.Mal_malloc__G2.Mal_malloc_fastI.rng_usg1).
Local Abbreviation rng_sct := (§16§ U.Mal_malloc__G2.Mal_malloc_fastI.rng_sct).
Local Abbreviation rng_ctz := (§16§ U.Mal_malloc__G2.Mal_malloc_fastI.rng_ctz).
Local Notation "§18§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI m0) (at level 10, h__ global).
Local Abbreviation rng_meta := (§18§ U.Mal_malloc__G2.Mal_malloc_fastI.rng_meta).
Local Abbreviation rng_slot := (§18§ U.Mal_malloc__G2.Mal_malloc_fastI.rng_slot).
Local Notation "§19§ h__" := (h__ s L n g am rho b3 b16 HW HC HLok Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hsp_high) (at level 10, h__ global).
Local Abbreviation Zones := (§19§ U.Mal_malloc__G2.Mal_malloc_fastI.Zones).
Local Abbreviation N_all := (@U.Mal_malloc__G2.Mal_malloc_fastI.N_all am).
Local Abbreviation OBJS_eq := (@U.Mal_malloc__G2.Mal_malloc_fastI.OBJS_eq am).
Local Abbreviation S2 := (@U.Mal_malloc__G2.Mal_malloc_fastI.S2 am).
Local Notation "§20§ h__" := (h__ s L n g am rho b3 b16 HW HC HLok Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hdepth Hsp_high m0 Erd Ewok ms Hrom Hm0_sct Hm0_ctz Hm3 Hm16) (at level 10, h__ global).
Local Abbreviation carve := (§20§ U.Mal_malloc__G2.Mal_malloc_fastI.carve).
Variable ok : world -> Prop.
Variable K : ltac2:(tb__ "0|0|
S22S10eA1S10fOF_;F_;").
Hypothesis HK : ltac2:(tb__ "0|0|
S120S66Vok;VK;A3").
Variable mW : word -> option byte.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EV := (@U.Mal_malloc__G2.Mal_malloc_fastC.EV s L n g am rho b3 b16 mW).
Local Abbreviation Zv12 := (@U.Mal_malloc__G2.Mal_malloc_fastC.Zv12 s L n g am rho b3 b16 HW HC HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI).
Local Abbreviation Zv142 := (§14§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv142).
Local Abbreviation Zv143 := (§14§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv143).
Local Abbreviation Zv149 := (§14§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv149).
Local Abbreviation Zv150 := (§14§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv150).
Local Abbreviation Zv151 := (§14§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv151).
Local Abbreviation Zv152 := (§14§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv152).
Local Abbreviation Zv153 := (§14§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv153).
Local Abbreviation Zv154 := (§14§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv154).
Local Abbreviation Zv155 := (§14§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv155).
Local Abbreviation Zv156 := (§14§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv156).
Local Abbreviation Zv157 := (§14§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv157).
Local Abbreviation Zv158 := (§14§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv158).
Local Abbreviation ZE_S := (§14§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_S).
Local Abbreviation ZE_strideT := (§14§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_strideT).
Local Notation "§21§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp) (at level 10, h__ global).
Local Abbreviation ZE_and155 := (§21§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_and155).
Local Abbreviation ZE_strideM := (§14§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_strideM).
Local Abbreviation ZE_sll := (§21§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_sll).
Local Notation "§22§ h__" := (h__ rho b3 b16 Hb3 Hb16) (at level 10, h__ global).
Local Abbreviation land_255 := (§22§ U.Mal_malloc__G2.Mal_malloc_fastC.land_255).
Local Abbreviation land_31' := (§22§ U.Mal_malloc__G2.Mal_malloc_fastC.land_31').
Local Abbreviation vo := (§12§ U.Mal_malloc__G3.Mal_malloc_fastD.vo).
Local Abbreviation vr := (§12§ U.Mal_malloc__G3.Mal_malloc_fastD.vr).
Local Abbreviation kd_cases := (@U.Mal_malloc__G3.Mal_malloc_fastD.kd_cases s n g am rho b3 b16 HW HC Hb3 Hb16 Hsp).

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
  rewrite ?Zv12, ?Zv142, ?Zv143, ?Zv149, ?Zv150, ?Zv151, ?Zv152, ?Zv153, ?Zv154, ?Zv155, ?Zv156, ?Zv157, ?Zv158;
  flat_mods; zlits;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by (clear; lia);
  rewrite ?land_255, ?land_31'.

Variables (tr : list event) (md : Model) (ms' : machine_state) (rhoF : valuation).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0S6bQ40A1S20S6bQ8A1A1F_;VmW;S35Vrho;A1A3").
Hypothesis Em0 : ltac2:(tb__ "0|0|
S0S6bQ40A1S20S6bQ8A1A1F_;Vm0;S35Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0S111Vvm;S110Vmd;A1A3").
Hypothesis Hsm : ltac2:(tb__ "0|0|
S45S66Vrho;S114S113A1S21S22S10eA1S11cVtr;S11dVms;Vmd;A2A4A4").
Hypothesis Hsm0 : ltac2:(tb__ "0|0|
S45S66VrhoW;S75S6eS9bVam;A1A2S21S22S10eA1S11cVtr;S11dVms;Vmd;A2A4A4").
Hypothesis HagF : agrees rhoW rhoF.
Hypothesis HsmF : ltac2:(tb__ "0|0|
S45S66VrhoF;S102S9bVam;A1S123Vs;Vn;Vam;Vb3;Vb16;A5S124Vs;Vn;Vam;Vb3;Vb16;A5A3S21S22S10eA1S11cVtr;S11dVms';Vmd;A2A4A4").

Definition Lf : sstate := ltac2:(tb__ "0|0|
S102S9bVam;A1S123Vs;Vn;Vam;Vb3;Vb16;A5S124Vs;Vn;Vam;Vb3;Vb16;A5A3").
Definition oStk : sobj := ltac2:(tb__ "0|0|
S40S36PaA1S36PfA1S30Z0A1S126S9bVam;A1S123Vs;Vn;Vam;Vb3;Vb16;A5S124Vs;Vn;Vam;Vb3;Vb16;A5A3S3dA5").
Definition oMeta : sobj := ltac2:(tb__ "0|0|
S40S112P97A1S30Z10A1S30Z28A1S127S3dA5").
Definition oSlot : sobj := ltac2:(tb__ "0|2|
S40S76S9bVam;A1M0A1S30N4A1M1S31SefS77G0A1G1A3S125G0S123Vs;Vn;Vam;Vb3;Vb16;A5S124Vs;Vn;Vam;Vb3;Vb16;A5A3S3dA5").
Definition NL : list sobj := ltac2:(tb__ "0|0|
S1fS2fS7eS6eA1S1fS2fS7dS6eA1S1fS2fS7bS6eA1S1fS2fS79S6eA1S1fS2fS7fS6eA1S1fS2fS7cS6eA1S1fS2fSd4S1fS2fSd5S1fS2fS7aS6eA1S1fS2fS80S6eA1S1fS2fS81S6eA1S28S2fA1A3A3A3A3A3A3A3A3A3A3A3").
Definition m' : word -> option byte := ltac2:(tb__ "0|2|
S6bQ40A1S12bSfbVrhoF;Sd1R1A3M0S3G0A1M1A2S20S6bQ8A1A1L_;SfcVrhoF;Sd1R1A3G0SecVms';R2A2L_;G1S35Vrho;R2A2L_;X12bx2La;").
Definition rw' (j : positive) : word := ltac2:(tb__ "0|2|
S1dS6bQ40A1L_;S25S14Z64M0S9Vj;A1M1A2S11G1Z84A2A2S38VrhoF;S57Sd6SdG1G0A2A2A2S37Vrho;Vj;A2X1dx2").
Definition rho' : valuation := ltac2:(tb__ "0|0|
S5eSd7S58Vrho;A1Sd2A3").

Lemma Lf_objs : ltac2:(tb__ "0|0|
S0S22S2fA1S46Sd6A1S1fS2fSd3Sd1A3A3").
Proof using . unfold Lf, NL, oStk, oMeta, oSlot. rewrite LF_objs. reflexivity. Qed.

Lemma rwF : ltac2:(tb__ "0|0|
S7S0S1dS94R1A1S1eA3S0S6bQ40A1S37VrhoF;R2A2SaaVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;R2A9A3F_;Fj;").
Proof using HagF. intros j Hj. destruct HagF as (A & _ & _). rewrite (A j Hj). reflexivity. Qed.
Lemma rmF : ltac2:(tb__ "0|0|
S6bQ40A1S0S20S6bQ8A1A1S35VrhoF;R1A2S35Vrho;R1A2A3Fa;").
Proof using EmW HagF. intros a. destruct HagF as (_ & _ & C). rewrite C. unfold rhoW. cbn [rm U.Mal_malloc__G2.Mal_malloc_fastI.rho1]. rewrite EmW. reflexivity. Qed.
Lemma rlF : ltac2:(tb__ "0|0|
S7S0S22S6bQ8A1A1S58VrhoF;R1A2Sb6Vrho;R1A2A3Fl;").
Proof using HagF. intros l. destruct HagF as (_ & B & _). rewrite (B l). reflexivity. Qed.
Lemma rw1_low : ltac2:(tb__ "0|0|
S7S13bR1P64A2S0S6bQ40A1SaaVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;R2A9S37Vrho;R2A2A3F_;Fj;").
Proof using Hb16 Hb3 Hsp.
  intros j Hj. apply rw1_other. unfold U.Mal_malloc__G2.Mal_malloc_fastI.rw1_changed.
  repeat (rewrite (proj2 (Pos.eqb_neq j _)) by lia). reflexivity.
Qed.
Lemma rw'_low : ltac2:(tb__ "0|0|
S7S13bR1P64A2S0S6bQ40A1Sd7R2A1S37Vrho;R2A2A3F_;Fj;").
Proof using Hb16 Hb3.
  intros j Hj. unfold rw'.
  replace ((100 <=? Z.pos j) && (Z.pos j <? 132))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
  reflexivity.
Qed.
Lemma agree_vals_rho' : ltac2:(tb__ "0|0|
ScfS67Vrho;Sd8A3").
Proof using Hb16 Hb3. split; [|reflexivity]. intros j Hj. cbn [rw rho']. symmetry. apply rw'_low. exact Hj. Qed.

Lemma evF : ltac2:(tb__ "0|1|
S2eS0S1dSccS94R1A2S1eA3S0S1dSbaR2A1S1eA3S0S6bQ40M0A1S38VrhoF;R3A2S6cG0Sb9S9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8R3A3A2A3F_;F_;Fe;").
Proof using HagF. intros e Hv Hs. exact (EV rhoF e HagF Hv Hs). Qed.
Lemma evFu : ltac2:(tb__ "0|0|
S2eS0S1dSccS94R1A2S1eA3S0S1dSbaR2A1S1eA3S0S6S6dQ40S38VrhoF;R3A2A2Sb9S9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8R3A3A3F_;F_;Fe;").
Proof using HagF. intros e Hv Hs. rewrite (evF e Hv Hs). apply u64. apply zeval_range. exact Hs. Qed.
Lemma evW : ltac2:(tb__ "0|1|
S2eS0S1dSbaR1A1S1eA3S0S6bQ40M0A1S38VrhoW;R2A2S6cG0Sb9S9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8R2A3A2A3F_;Fe;").
Proof using mW. intros e Hs. unfold rhoW. apply ev1. exact Hs. Qed.

Lemma rhoW_m0 : ltac2:(tb__ "0|0|
S0S3cVrhoW;Sa6Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;Vm0;A9A3").
Proof using Em0 EmW. unfold rhoW. rewrite EmW, Em0. reflexivity. Qed.

Lemma rngF : ltac2:(tb__ "0|0|
S2fS0S1dSd0S94R1A2S1eA3S0S23S6S6A2S32VrhoF;R2A2S32Sa6Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;Vm0;A9R2A2A3F_;Fo;").
Proof using Em0 EmW HagF.
  intros o Ho. rewrite <- rhoW_m0. apply (obj_range_agree_vars below200 rhoW rhoF o); [| |exact Ho].
  - intros j Hj. symmetry. apply rwF. exact Hj.
  - intros l. symmetry. apply rlF.
Qed.

Lemma RF : ltac2:(tb__ "0|13|
S1S0S23S6S6A2M0S32VrhoF;S7eS6eA1A2S21S6S6SaZ5a35bM1Z0M2A2SaG1Z1A2A4A3S1S0G0S32VrhoF;S7dS6eA1A2S21S6S6SaZ5a3c8M3G2A2SaG3Z4M4A2A4A3S1S0G0S32VrhoF;S7bS6eA1A2S21S6S6SaG3Z14A2SaG3Z18A2A4A3S1S0G0S32VrhoF;S79S6eA1A2S21S6S6SaG3SaSeZ8M5Sa1Vam;A1A2M6Z58M7A2A2SaG3SaG6Z60M8A2A2A4A3S1S0G0S32VrhoF;S7fS6eA1A2S21S6S6SaZ108ecM9G2A2SaG9G8A2A4A3S1S0G0S32VrhoF;S7cS6eA1A2S21S6S6SaZ108ccMaG2A2SaGaZ20A2A4A3S1S0G0S32VrhoF;Sd4A2S21S6S6SaSa2VL;Vg;A2MbZ10A2SaGbZ28A2A4A3S1S0G0S32VrhoF;Sd5A2S21S6S6SaS9cVL;Vam;A2McN4A2SaGcSdS9dVam;A1G4A2A2A4A3S1S0G0S32VrhoF;Sd3A2S21S6S6SaSa5Vrho;A1MdSa3Vrho;A1A2GdA4A3S1S0G0S32VrhoF;S7aS6eA1A2S21S6S6SaG3SaSeG5S9fVs;Vn;Vam;A3A2MeG7A2MfA2SaG3SaGfG5A2A2A4A3S1S0G0S32VrhoF;S80S6eA1A2S21S6S6SaG3SaGeZ1d8M10A2M11A2SaG3SaG11G5A2A2A4A3S0G0S32VrhoF;S81S6eA1A2S21S6S6SaG3SaG6G10A2M12A2SaG3SaG12G5A2A2A4A3A2A2A2A2A2A2A2A2A2A2A2").
Proof using Em0 EmW HC HMI HW HagF Hb16 Hb3 Hdepth Hhdr Hsp.
  assert (V : forall kd0, forallb (obj_vars_all below200) (OBJS MR_P kd0) = true) by (intros [| |]; vm_cast_no_check (@eq_refl bool true)).
  pose proof (proj1 (forallb_forall _ _) (V kd)) as V'. rewrite OBJS_eq in V'. unfold N_all in V'.
  assert (X : forall o o', In o' (Q_stk :: [Q_nl; Q_lock; Q_ctr; Q_act; Q_sct; Q_ctz; Q_meta; Q_slot; Q_act0; Q_usg0; Q_usg1]) ->
              ob_base o = ob_base o' -> ob_lo o = ob_lo o' -> ob_hi o = ob_hi o' -> obj_range rhoF o = obj_range (rho1 m0) o').
  { intros o o' Hin E1 E2 E3. rewrite (shape_range rhoF o o' E1 E2 E3). apply rngF. apply V'. exact Hin. }
  repeat match goal with |- _ /\ _ => split end.
  - rewrite (X _ Q_nl); [apply rng_nl | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_lock); [apply rng_lock | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_ctr); [apply rng_ctr | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_act); [apply rng_act | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_sct); [apply rng_sct | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_ctz); [apply rng_ctz | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_meta); [apply rng_meta | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_slot); [apply rng_slot | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_stk); [apply rng_stk | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_act0); [apply rng_act0 | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_usg0); [apply rng_usg0 | cbn; tauto | reflexivity ..].
  - rewrite (X _ Q_usg1); [apply rng_usg1 | cbn; tauto | reflexivity ..].
Qed.

Lemma RZ : ltac2:(tb__ "0|10|
S1SbZ0M0Vn;A2S1S1SbG0Sa0Vs;Vn;Vam;Vb3;Vb16;A5M1A2SbG1ZffA2A2S1SbSaSaSeZ10M2G1A2Vn;A2Z4M3A2S9dVam;A1M4A2S1SbG2G4A2S1ScG4SfZ2M5Z14A2A2S1SbZ1000M6Sb8VL;Vam;A2M7A2S1S0S6S9cVL;Vam;A2M8SaSaG7G2A2SeG4Sb5Vam;A1A2M9A2A3S1S0S6SabVL;Vam;A2MaSdSaG8G4A2G3A2A3S1SbG0G9A2S1SbSaGaG3A2SffVL;A1MbA2S1ScGbSfG5Z2fA2A2S1SbG6Sa2VL;Vg;A2McA2S1SbSaGcZ28A2GbA2S1SbGbSaSa5Vrho;A1Sa3Vrho;A1A2A2S1SbSaZ5b000G2A2GbA2S1S1SbG0Sa1Vam;A1MdA2ScGdZ30MeA2A2S1S1SbG0S9fVs;Vn;Vam;A3MfA2ScGfGeA2A2S3S0S6GfGdA3A1A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using HC HLok HMI HW Hb16 Hb3 Hhdr Hsp Hsp_high.
  pose proof R_all as R. pose proof Zones as (_ & SH & AC). pose proof Hj164. repeat match goal with |- _ /\ _ => split end; try lia.
Qed.

Lemma HO0 : ltac2:(tb__ "0|0|
S119S2fS3bS66VrhoW;Vms;A3S1fS2fSa7Sa4Vam;A1A3A3").
Proof using Hsm0.
  pose proof Hsm0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
  rewrite <- OBJS_eq. exact Hall.
Qed.
Lemma HOF : ltac2:(tb__ "0|0|
S119S2fS3bS66VrhoF;Vms';A3S1fS2fSd3Sd1A3A3").
Proof using HsmF.
  pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
  fold Lf in Hall. rewrite Lf_objs in Hall. exact Hall.
Qed.
Lemma Hfr0 : ltac2:(tb__ "0|0|
S6bQ40A1S56VrhoW;S1fS2fSa7Sa4Vam;A1A3R1A3S0S20S6bQ8A1A1SecVms;R2A2S35Vrho;R2A2A3F_;Fa;").
Proof using EmW Hsm0.
  pose proof Hsm0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr.
  intros a Ha. rewrite <- OBJS_eq in Ha. rewrite (Hfr a Ha). unfold rhoW. cbn [rm U.Mal_malloc__G2.Mal_malloc_fastI.rho1]. exact (f_equal (fun f => f a) EmW).
Qed.
Lemma HfrF : ltac2:(tb__ "0|0|
S6bQ40A1S56VrhoF;S1fS2fSd3Sd1A3R1A3S0S20S6bQ8A1A1SecVms';R2A2S35Vrho;R2A2A3F_;Fa;").
Proof using EmW HagF HsmF.
  pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr.
  intros a Ha. fold Lf in Hfr. rewrite Lf_objs in Hfr. rewrite (Hfr a Ha). apply rmF.
Qed.

Lemma Hfr00 : ltac2:(tb__ "0|1|
S6bQ40M0A1ScS6dG0R1A2SaSa5Vrho;A1Sa3Vrho;A1A2A2S0S20S6bQ8A1A1SecVms;R2A2S35Vrho;R2A2A3F_;Fa;").
Proof using Hb16 Hb3 Hsm.
  intros a Ha. pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr.
  apply Hfr. cbn [ss_objs Pre_malloc]. constructor; [|constructor].
  unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi eval fst snd]. unfold soff. cbn [eval].
  rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. unfold V_DEPTH. change (toS 64 (bv_unsigned (rw rho 15%positive))) with D0. fold sp0. lia.
Qed.

Lemma Hrom0 : rom_ok segsU ms. Proof using Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). Qed.
Lemma HromF : rom_ok segsU ms'. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.
Lemma HroF : ro_clear segsU ms'. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmF)))))). Qed.
Lemma Hro0 : ro_clear segsU ms. Proof using Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm)))))). Qed.

Lemma m'_in : ltac2:(tb__ "0|0|
S6bQ40A1SfbVrhoF;Sd1R1A3S0S20S6bQ8A1A1Sd2R2A1SecVms';R2A2A3F_;Fa;").
Proof using . intros a Ha. unfold m'. destruct (in_ranges_dec rhoF NL a) as [|N]; [reflexivity|]. exfalso. exact (N Ha). Qed.
Lemma m'_out : ltac2:(tb__ "0|0|
S6bQ40A1S3SfbVrhoF;Sd1R1A3A1S0S20S6bQ8A1A1Sd2R2A1S35Vrho;R2A2A3F_;Fa;").
Proof using . intros a Ha. unfold m'. destruct (in_ranges_dec rhoF NL a) as [Y|]; [|reflexivity]. exfalso. exact (Ha Y). Qed.

Lemma NL_cases : ltac2:(tb__ "0|f|
S6bQ40M0A1SfbVrhoF;Sd1R1A3S6dG0R2A2S6S2S1SbZ5a35bM1R1A2ScR1SaG1Z1A2A2A2S2S1SbZ5a3c8M2R1A2ScR1SaG2Z4M3A2A2A2S2S1SbSaG2Z14A2R1A2ScR1SaG2Z18A2A2A2S2S1SbSaG2SaSeZ8M4Sa1Vam;A1A2M5Z58M6A2A2R1A2ScR1SaG2SaG5Z60M7A2A2A2A2S2S1SbZ108ecM8R1A2ScR1SaG8G7A2A2A2S2S1SbZ108ccM9R1A2ScR1SaG9Z20A2A2A2S2S1SbSaSa2VL;Vg;A2MaZ10A2R1A2ScR1SaGaZ28A2A2A2S2S1SbSdS9cVL;Vam;A2MbG3A2R1A2ScR1SdSaGbS9dVam;A1A2G3A2A2A2S2S1SbSaG2SaSeG4S9fVs;Vn;Vam;A3A2McG6A2A2R1A2ScR1SaG2SaGcG7A2A2A2A2S2S1SbSaG2SaGcZ1d8MdA2A2R1A2ScR1SaG2SaGcZ1e0MeA2A2A2A2S1SbSaG2SaG5GdA2A2R1A2ScR1SaG2SaG5GeA2A2A2A2A2A2A2A2A2A2A2A2A2A2Tx;F_;Fa;").
Proof using Em0 EmW HC HMI HW HagF Hb16 Hb3 Hdepth Hhdr Hsp.
  intros a (o & Ho & R) x. pose proof RF as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
  unfold NL in Ho. cbn [In] in Ho.
  destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]];
    rewrite ?R1, ?R2, ?R3, ?R4, ?R5, ?R6, ?R7, ?R8, ?R10, ?R11, ?R12 in R; cbn [fst snd] in R; subst x; lia.
Qed.

Lemma NL_below_stack : ltac2:(tb__ "0|1|
S6bQ40M0A1SfbVrhoF;Sd1R1A3ScS6dG0R2A2SaSa5Vrho;A1Sa3Vrho;A1A2A2F_;Fa;").
Proof using Em0 EmW HC HLok HMI HW HagF Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high. intros a Ha. pose proof RZ as Z0. pose proof (NL_cases a Ha) as C. cbn zeta in C. top_ranges. lia. Qed.

Lemma HoSlotF : ltac2:(tb__ "0|0|
S3bS66VrhoF;Vms';Sd5A4").
Proof using Hb16 Hb3 Hdepth HsmF Hsp. apply (proj1 (Forall_forall _ _) HOF). right. unfold NL. cbn. tauto. Qed.
Lemma HoMetaF : ltac2:(tb__ "0|0|
S3bS66VrhoF;Vms';Sd4A4").
Proof using Hb16 Hb3 Hdepth HsmF Hsp. apply (proj1 (Forall_forall _ _) HOF). right. unfold NL. cbn. tauto. Qed.

Lemma slot_in_NL : ltac2:(tb__ "0|2|
S6S1SbSdS9cVL;Vam;A2M0Z4M1A2R1A2ScR1SdSaG0S9dVam;A1A2G1A2A2A2SfbVrhoF;Sd1SfdR2A1A3F_;Fx;").
Proof using Em0 EmW HC HLok HMI HW HagF Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high.
  intros x Hx. pose proof RZ. exists oSlot. split; [unfold NL; cbn; tauto|].
  rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RF)))))))). cbn [fst snd]. unfold wz. rewrite u64 by (top_ranges; lia). lia.
Qed.
Lemma meta_in_NL : ltac2:(tb__ "0|1|
S6S1SbSaSa2VL;Vg;A2M0Z10A2R1A2ScR1SaG0Z28A2A2A2SfbVrhoF;Sd1SfdR2A1A3F_;Fx;").
Proof using Em0 EmW HC HLok HMI HW HagF Hb16 Hb3 Hdepth Hhdr Hsp Hsp_high.
  intros x Hx. pose proof RZ. exists oMeta. split; [unfold NL; cbn; tauto|].
  rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RF))))))). cbn [fst snd]. unfold wz. rewrite u64 by (top_ranges; lia). lia.
Qed.

Theorem V2 : ltac2:(tb__ "0|1|
S6S12fVL;Vam;R1A3S1S0S1dS98S66Sd2SfdR2A1A3S1eA3S4S6bQ8A1M0G0S0S20G0A1S97S66Sd2SfdR3A1A3S24G0R1A2A3Lb;A2A2F_;Fx;").
Proof using Em0 EmW HC HLok HMI HW HagF Hb16 Hb3 Hdepth Hhdr HsmF Hsp Hsp_high.
  intros x Hx. unfold in_zone, f_st, f_e, f_idx in Hx. change (addr_of L (slot_start am (mf_idx am))) with zSt in Hx. change (addr_of L (slot_end am (mf_idx am))) with zE in Hx.
  pose proof RZ as Z0.
  assert (R : zSt - 4 <= x < zSt + stv - 4) by lia.
  pose proof (m'_in (wz x) (slot_in_NL x R)) as E.
  destruct (dunk_byte rhoF ms' oSlot x HoSlotF eq_refl ltac:(rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RF)))))))); cbn [fst snd]; lia)) as [[b Hb] W].
  split; [apply (wok_of_at m' ms'); [exact E | exact W]|].
  exists b. rewrite (rd_of_at m' ms' (wz x) HromF E). exact Hb.
Qed.

Lemma evFW : ltac2:(tb__ "0|0|
S2eS0S1dSccS94R1A2S1eA3S0S6bQ40A1S38VrhoF;R2A2S38VrhoW;R2A2A3F_;Fe;").
Proof using HagF. intros e He. exact (eval_agrees rhoW rhoF e HagF He). Qed.
Lemma soffFW : ltac2:(tb__ "0|0|
S2eS0S1dSccS94R1A2S1eA3S0S6S3aVrhoF;R2A2S3aVrhoW;R2A2A3F_;Fe;").
Proof using HagF. intros e He. unfold soff. rewrite (evFW e He). reflexivity. Qed.

Lemma same_cell_bytes : ltac2:(tb__ "0|3|
S2fS2fS34S6S3bS66VrhoW;Vms;R4A4S3bS66VrhoF;Vms';R4A4Sc7S34R4S43R6A1M0A3Sc7S34R5G0A3S0S2eS39R8A1S39R7A1A3S0S1dSccS94S39R9A1A2S1eA3S0S1dSccS94S3eR8A1A2S1eA3S0S1dSccS94S4aR9A1A2S1eA3S1SbSaS6dQ40S38VrhoF;S39RbA1A2A2S3aVrhoF;S3eRaA1A2A2M1R9A2ScR9SaG1S42RaA1A2A2A2S0S20S6bQ8A1A1S44Vms';SfdRaA1M2A2S44Vms;G2A2A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fx;Fc;FoB;FoA;").
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

Lemma ro_tab : ltac2:(tb__ "0|7|
S6bQ40M0A1S2S1SbZ108ecM1S6dG0R1A2M2A2ScG2SaG1Z60A2A2A2S1SbZ108ccM3G2A2ScG2SaG3Z20A2A2A2A2S1S0S20S6bQ8A1M4A1M5SecVms';R2A2S26G4A1M6A3S0G5S35Vrho;R2A2G6A3A2F_;Fa;").
Proof using Em0 Hb16 Hb3 Hm0_ctz Hm0_sct HsmF.
  intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a). split.
  - apply HroF. replace (bv_unsigned a) with (0x108cc + (bv_unsigned a - 0x108cc)) by lia. apply ro_tables. lia.
  - rewrite <- Em0. destruct Ha as [Ha|Ha].
    + replace (bv_unsigned a) with (0x108ec + (bv_unsigned a - 0x108ec)) by lia. apply Hm0_sct. lia.
    + replace (bv_unsigned a) with (0x108cc + (bv_unsigned a - 0x108cc)) by lia. apply Hm0_ctz. lia.
Qed.

Lemma HoldA : ltac2:(tb__ "0|0|
S2fSc7S2fR1Sa4Vam;A1A3S3bS66VrhoW;Vms;R2A4F_;Fo;").
Proof using Hsm0. intros o Ho. apply (proj1 (Forall_forall _ _) HO0). right. exact Ho. Qed.
Lemma HoldB : ltac2:(tb__ "0|0|
S2fSc7S2fR1Sd1A3S3bS66VrhoF;Vms';R2A4F_;Fo;").
Proof using HsmF. intros o Ho. apply (proj1 (Forall_forall _ _) HOF). right. exact Ho. Qed.

Ltac inN := unfold N_all, NL; cbn; tauto.

Lemma V1_cell : ltac2:(tb__ "0|7|
S2fS2fS34S6Sc7S2fR4Sa4Vam;A1A3Sc7S2fR4Sd1A3S0S55S52R6A1S3dA3M0G0Sc7S34R6S43R8A1M1A3Sc7S34R7G1A3S0S2eS39RaA1S39R9A1A3S0S1dSccS94S39RbA1A2S1eA3S0S1dSccS94S3eRaA1A2S1eA3S0S1dSccS94S4aRbA1A2S1eA3S1SbSaS6dQ40S38VrhoF;S39RdA1A2A2S3aVrhoF;S3eRcA1A2A2M2RbA2ScRbSaG2S42RcA1A2A2A2S1SbS29S6S6S32VrhoF;ReA2M3A3RcA2ScRcS2aS6S6G3A3A2A2S1SbS29S6S6S32VrhoW;R10A2M4A3RdA2ScRdS2aS6S6G4A3A2A2SfbVrhoF;Sd1SfdReA1A3S1SbZ0RfA2ScRfSfZ2Z40A2A2A2S1S0S20S6bQ8A1A1S97S66Sd2SfdR10A1M5A3S97S66S35Vrho;A1M6G5A3A3S0S1dS98S66Sd2G5A3S98S66G6G5A3A3A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fx;Fc;FoB;FoA;").
Proof using Em0 EmW HC HLok HMI HW HagF Hb16 Hb3 Hdepth Hhdr Hsm Hsm0 HsmF Hsp Hsp_high.
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

Lemma RW : ltac2:(tb__ "0|f|
S1S0S23S6S6A2M0S32VrhoW;Sb1A2S21S6S6SaZ5a35bM1Z0M2A2SaG1Z1A2A4A3S1S0G0S32VrhoW;SafA2S21S6S6SaZ5a3c8M3G2A2SaG3Z4M4A2A4A3S1S0G0S32VrhoW;SaeA2S21S6S6SaG3Z14A2SaG3Z18A2A4A3S1S0G0S32VrhoW;SacA2S21S6S6SaG3SaSeZ8M5Sa1Vam;A1A2M6Z58M7A2A2SaG3SaG6Z60A2A2A4A3S1S0G0S32VrhoW;Sb0A2S21S6S6SaSa2VL;Vg;A2M8Z10A2SaG8Z28A2A4A3S1S0G0S32VrhoW;Sb2Vam;A1A2S21S6S6SaS9cVL;Vam;A2M9N4A2SaG9SdS9dVam;A1G4A2A2A4A3S1S0G0S32VrhoW;SadA2S21S6S6SaG3SaSeG5S9fVs;Vn;Vam;A3A2MaG7A2MbA2SaG3SaGbG5A2A2A4A3S1S0G0S32VrhoW;Sb3A2S21S6S6SaG3SaGaZ1d8McA2MdA2SaG3SaGdG5A2A2A4A3S0G0S32VrhoW;Sb4A2S21S6S6SaG3SaG6GcA2MeA2SaG3SaGeG5A2A2A4A3A2A2A2A2A2A2A2A2").
Proof using Em0 EmW HC HMI HW Hb16 Hb3 Hhdr Hsp. rewrite rhoW_m0. repeat match goal with |- _ /\ _ => split end; first [apply rng_nl|apply rng_lock|apply rng_ctr|apply rng_act|apply rng_meta|apply rng_slot|apply rng_act0|apply rng_usg0|apply rng_usg1]. Qed.

Lemma baseF_lit : ltac2:(tb__ "0|0|
S6S1SbZ0R1A2ScR1SfZ2Z40A2A2A2S0S6S6dQ40S38VrhoF;S30R2A1A2A2R2A3F_;Fz;").
Proof using . intros z Hz. cbn [eval]. apply u64. exact Hz. Qed.
Lemma baseF_151 : ltac2:(tb__ "0|0|
S0S6S6dQ40S38VrhoF;S112P97A1A2A2Sa2VL;Vg;A2A3").
Proof using HC HMI HW HagF Hb16 Hb3 Hhdr. rewrite (evFu (v 151)) by reflexivity. exact ze151. Qed.
Lemma baseF_p0 : ltac2:(tb__ "0|0|
S0S6S6dQ40S38VrhoF;S76S9bVam;A1A1A2A2S9cVL;Vam;A2A3").
Proof using HC HMI HW HagF Hb16 Hb3 Hhdr Hsp. rewrite evFu; [exact ze_p0 | destruct kd_cases as [[-> _]|[[-> _]|[-> _]]]; reflexivity ..]. Qed.
Lemma soffF_lit : ltac2:(tb__ "0|1|
S6S1SbS10SfZ2Z3eA2M0A1R1A2SbR1G0A2A2S0S6S3aVrhoF;S30R2A1A2R2A3F_;Fz;").
Proof using Hb16 Hb3 rho. intros. apply soff_lit_small. lia. Qed.
Lemma soffF_act : ltac2:(tb__ "0|1|
S0S6S3aVrhoF;S31SefS31Sf2S112P96A1S30Z3A1A3S30Z58M0A1A3A2SaSeZ8Sa1Vam;A1A2G0A2A3").
Proof using Em0 EmW HC HLok HMI HW HagF Hb16 Hb3 Hhdr Hsp Hsp_high.
  rewrite soffFW by reflexivity. rewrite rhoW_m0. apply (soff_of_ev (SAlu ALU_ADD (SAlu ALU_SLL (v 150) (SLit 3)) (SLit 88)) (8 * sc + 88) eq_refl ze_actoff). pose proof RZ. lia.
Qed.

Lemma soffF_ofZ : ltac2:(tb__ "0|0|
S2eS6S0S1dSbaR2A1S1eA3S0S6Sb9S9aVs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S99Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8R3A3R2A3S1SbZ0R3A2ScR3SfZ2Z3fA2A2A2S0S1dSccS94R5A2S1eA3S0S6S3aVrhoF;R6A2R5A3F_;F_;F_;F_;Fz;Fe;").
Proof using Em0 EmW HagF Hb16 Hb3. intros e z Hs Hz Hr Hv. rewrite soffFW by exact Hv. rewrite rhoW_m0. apply (soff_of_ev e z Hs Hz Hr). Qed.
Lemma soffF_act0 : ltac2:(tb__ "0|1|
S0S6S3aVrhoF;S31SefS31Sf2S112Pa4A1S30Z3A1A3S30Z58M0A1A3A2SaSeZ8S9fVs;Vn;Vam;A3A2G0A2A3").
Proof using Em0 EmW HC HLok HMI HW HagF Hb16 Hb3 Hhdr Hsp Hsp_high. pose proof RZ. exact (soffF_ofZ (SAlu ALU_ADD (SAlu ALU_SLL (v 164) (SLit 3)) (SLit 88)) _ eq_refl ze_act0off ltac:(lia) eq_refl). Qed.
Lemma soffF_usg0 : ltac2:(tb__ "0|1|
S0S6S3aVrhoF;S31SefS31Sf2S112Pa4A1S30Z3A1A3S30Z1d8M0A1A3A2SaSeZ8S9fVs;Vn;Vam;A3A2G0A2A3").
Proof using Em0 EmW HC HLok HMI HW HagF Hb16 Hb3 Hhdr Hsp Hsp_high. pose proof RZ. exact (soffF_ofZ (SAlu ALU_ADD (SAlu ALU_SLL (v 164) (SLit 3)) (SLit 472)) _ eq_refl ze_usg0off ltac:(lia) eq_refl). Qed.
Lemma soffF_usg1 : ltac2:(tb__ "0|1|
S0S6S3aVrhoF;S31SefS31Sf2S112P96A1S30Z3A1A3S30Z1d8M0A1A3A2SaSeZ8Sa1Vam;A1A2G0A2A3").
Proof using Em0 EmW HC HLok HMI HW HagF Hb16 Hb3 Hhdr Hsp Hsp_high. pose proof RZ. exact (soffF_ofZ (SAlu ALU_ADD (SAlu ALU_SLL (v 150) (SLit 3)) (SLit 472)) _ eq_refl ze_usg1off ltac:(lia) eq_refl). Qed.

Theorem V1 : ltac2:(tb__ "0|2|
S6S1SbZ0R1A2ScR1SfZ2Z40A2A2A2S3S12fVL;Vam;R2A3A1S3S131VL;Vg;R3A3A1S1S0S20S6bQ8A1A1S97S66Sd2SfdR4A1M0A3S97S66S35Vrho;A1M1G0A3A3S0S1dS98S66Sd2G0A3S98S66G1G0A3A3A2F_;F_;F_;Fx;").
Proof using Em0 EmW HC HLok HMI HW HagF Hb16 Hb3 Hdepth Hhdr Hm0_ctz Hm0_sct Hsm Hsm0 HsmF Hsp Hsp_high.
  intros x Hx NZ NA.
  unfold in_zone, f_st, f_e, f_idx in NZ. change (addr_of L (slot_start am (mf_idx am))) with zSt in NZ. change (addr_of L (slot_end am (mf_idx am))) with zE in NZ.
  unfold in_av, f_zg in NA. change (addr_of L g) with zG in NA.
  pose proof RZ as Z0. pose proof RF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12). pose proof RW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9).
  destruct (in_ranges_dec rhoF NL (wz x)) as [IN|OUT].
  2:{ unfold Glue.rd_of, Glue.wok_of. rewrite (m'_out _ OUT). split; reflexivity. }
  pose proof IN as (o & Ho & R). unfold wz in R. rewrite u64 in R by lia.
  unfold NL in Ho. cbn [In] in Ho.
  destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]].
  -   rewrite F1 in R. cbn [fst snd] in R.
    apply (V1_cell Q_nl (U.Mal_malloc__G1.Mal_malloc_fast_runs.O_nl MR_P) (mkCell (SLit 0) 1 (SLit 0)) x); try inN; try reflexivity;
      rewrite ?F1, ?W1; cbn [fst snd ob_base U.Mal_malloc__G1.Mal_malloc_fast_runs.O_nl c_off c_width mr_nl MR_P]; rewrite ?baseF_lit, ?soffF_lit by lia; try lia; exact IN.
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
  -   rewrite F6 in R. cbn [fst snd] in R.
    destruct (ro_tab (wz x) ltac:(unfold wz; rewrite u64 by lia; lia)) as [M1 M2].
    rewrite <- M1, <- (m'_in _ IN) in M2. unfold Glue.rd_of, Glue.wok_of, Contract.rd_of, Contract.wok_of. rewrite <- M2. split; reflexivity.
  -   rewrite F7 in R. cbn [fst snd] in R.
    assert (KM : exists c, In c (ob_cells Q_meta) /\ In c meta_cells' /\ exists offc, c_off c = SLit offc /\ - 100 <= offc <= 100 /\ sv_vars_all below200 (c_val c) = true
                 /\ zG + offc <= x < zG + offc + c_width c).
    { destruct (Z_lt_dec x (zG + 24)) as [A|A].
      - exists (mkCell (SLit 16) 8 (v 156)). split; [cbn; tauto|]. split; [cbn; tauto|]. exists 16. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. cbn [c_width]. lia.
      - destruct (Z_lt_dec x (zG + 32)) as [B|B].
        + exists (mkCell (SLit 28) 4 (v 154)). split; [cbn; tauto|]. split; [cbn; tauto|]. exists 28. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. cbn [c_width]. lia.
        + exists (mkCell (SLit 32) 8 (v 155)). split; [cbn; tauto|]. split; [cbn; tauto|]. exists 32. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. cbn [c_width]. lia. }
    destruct KM as (c & C1 & C2 & offc & Eoff & Hoffc & Vc & Hxc).
    apply (V1_cell Q_meta oMeta c x); try inN; try reflexivity; try exact C1; try exact C2; try exact Vc;
      rewrite ?Eoff, ?F7, ?W5; cbn [fst snd ob_base oMeta]; rewrite ?baseF_151, ?soffF_lit by lia; try reflexivity; try lia; exact IN.
  -   rewrite F8 in R. cbn [fst snd] in R.
    assert (Ex : x = zSt - 4) by lia.
    apply (V1_cell Q_slot oSlot (mkCell (SLit (-4)) 1 (SLit 0)) x);
      [ inN | inN | reflexivity | reflexivity
      | unfold U.Mal_malloc__G2.Mal_malloc_fastI.Q_slot, U.Mal_malloc__G1.Mal_malloc_fast_runs.O_slot; cbn [ob_cells]; left; reflexivity
      | apply C4_in
      | reflexivity
      | unfold U.Mal_malloc__G2.Mal_malloc_fastI.Q_slot; cbn [ob_base U.Mal_malloc__G1.Mal_malloc_fast_runs.O_slot]; destruct kd_cases as [[Ek _]|[[Ek _]|[Ek _]]]; rewrite Ek; reflexivity
      | reflexivity | reflexivity
      | cbn [ob_base oSlot c_off c_width]; rewrite baseF_p0, soffF_lit by lia; lia
      | rewrite F8; cbn [fst snd]; lia
      | rewrite W6; cbn [fst snd]; lia
      | exact IN | lia ].
  -   rewrite F10 in R. cbn [fst snd] in R.
    apply (V1_cell Q_act0 (U.Mal_malloc__G1.Mal_malloc_fast_runs.O_act0 MR_P) (mkCell (SAlu ALU_ADD (SAlu ALU_SLL (v 164) (SLit 3)) (SLit 88)) 8 (v 166)) x); try inN; try reflexivity;
      rewrite ?F10, ?W7; cbn [fst snd ob_base U.Mal_malloc__G1.Mal_malloc_fast_runs.O_act0 c_off c_width mr_LK MR_P]; rewrite ?baseF_lit by lia;
      rewrite ?soffF_act0 by lia; try lia; exact IN.
  -   rewrite F11 in R. cbn [fst snd] in R.
    apply (V1_cell Q_usg0 (U.Mal_malloc__G1.Mal_malloc_fast_runs.O_usg0 MR_P) (mkCell (SAlu ALU_ADD (SAlu ALU_SLL (v 164) (SLit 3)) (SLit 472)) 8 (v 167)) x); try inN; try reflexivity;
      rewrite ?F11, ?W8; cbn [fst snd ob_base U.Mal_malloc__G1.Mal_malloc_fast_runs.O_usg0 c_off c_width mr_LK MR_P]; rewrite ?baseF_lit by lia;
      rewrite ?soffF_usg0 by lia; try lia; exact IN.
  -   rewrite F12 in R. cbn [fst snd] in R.
    apply (V1_cell Q_usg1 (U.Mal_malloc__G1.Mal_malloc_fast_runs.O_usg1 MR_P) (mkCell (SAlu ALU_ADD (SAlu ALU_SLL (v 150) (SLit 3)) (SLit 472)) 8 (v 165)) x); try inN; try reflexivity;
      rewrite ?F12, ?W9; cbn [fst snd ob_base U.Mal_malloc__G1.Mal_malloc_fast_runs.O_usg1 c_off c_width mr_LK MR_P]; rewrite ?baseF_lit by lia;
      rewrite ?soffF_usg1 by lia; try lia; exact IN.
Qed.

End Reab.
End Mal_malloc_fastG.
