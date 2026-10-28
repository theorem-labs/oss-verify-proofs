(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "false"; "bool"; "app"; "prod"; "pair"; "nat"; "true"; "list"; "None"; "option"; "Some"; "fst"; "negb"; "snd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SVar"; "sobj"; "SLit"; "cell"; "mkCell"; "SAlu"; "SPBranch"; "mkObj"; "DUnknown"; "mkSS"; "FcsrFrm0"; "SPUle"; "SPNot"; "SPAlign"; "obj_holds"; "eval"; "sstate"; "SExt"; "SAluW"; "rw"; "ss_facts"; "ss_pc"; "holds"; "ss_next"; "SMd"; "rl"; "ss_regs"; "DRom"; "SLBytes"; "obj_range"; "ranges_disjoint"; "rm"; "smatch"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_objs"; "ss_resv"; "image_byte"; "pairwise_disjoint"; "ro_addr"; "swf"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockView"; "rho1"; "zP"; "st"; "sti"; "sz"; "zMem"; "h16"; "h3"; "pS"; "xv"; "zA"; "zG"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "sub"; "eqb"; "mul"; "lor"; "min"; "of_nat"; "opp"; "testbit"; "leb"; "ltb"; "modulo"; "to_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "gm_facts"; "gm_facts_direct"; "gm_facts_map"; "gm_sc"; "gm_scsize"; "GM_A0"; "GM_A1"; "L_SIZECLASSES"; "MASK_PAGE"; "gm_facts_common"; "gm_facts_nomap"; "gm_facts_sized"; "gm_mem_sv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_I.Inst"; "rsv"; "zEnd"; "n"; "kindok"; "backed"; "cE"; "cPN"; "cR"; "cR5"; "endX"; "rsv_ok_j"; "rsv_ok_r"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zl_of"; "zr_of"; "zholds"; "zeval"; "sx32"; "zsupported"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_ADD"; "ALU_AND"; "BC_GEU"; "ALU_SUB"; "BC_GE"; "ALU_SLL"; "ALU_SRL"; "BC_LTU"; "M_MUL"; "ALU_OR"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "image"; "loc_addr"; "mc_loc"; "MCell"; "LMem"; "mc_w"; "VZ"; "CTX_SIZE"; "VSec"; "cell_holds"; "frames"; "CTX_secret"; "LCtx"; "U0"; "alloc_owned"; "frame_ptr"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_runs"; "fvar"; "km_kind"; "rcode"; "kc_kind"; "D_call"; "FS_NEXT"; "reg"; "FVC"; "FVM"; "F_win_facts"; "code_of"; "fs_cutsX"; "D_ret"; "C0"; "O_sct"; "hdr_obj"; "p_facts"; "strideM"; "F_tp_facts"; "O_area"; "O_grp"; "O_lock"; "O_meta"; "O_nl"; "O_sec"; "endM"; "kc_facts"; "km_facts"; "objs_rsv"; "objs_rsvM"; "rsvM_facts"; "C1"; "C2"; "C3"; "C4"; "C5E"; "C5G"; "KC_A0"; "KC_A1"; "KM_A1"; "KM_B"; "d0"; "idx_of"; "lf0"; "memsv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "am_last"; "am_maplen"; "am_freed"; "am_sc"; "sptr"; "am_avail"; "frame"; "ameta"; "padd"; "FUser"; "fkind"; "fr_kind"; "bit"; "ones"; "AREA_HDR"; "METAS_PER_AREA"; "META_SIZE"; "fr_n"; "fr_off"; "nth_slot"; "ss_fr"; "st_areas"; "@Stdlib.Lists.List"; "In"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_slow"; "fs_why"; "WF0"; "fs_facts_why"; "fs_ff"; "fs_ret_call"; "WALL"; "fs_ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast";
"ff_rsv"; "ff_entry"; "ff_mask"; "R0"; "ff_end"; "ff_self"; "ff_code"; "ff_facts_rsv"; "R5E"; "R5G"; "ff_ctx"; "ff_libc"; "ff_lockword"; "ff_ret"; "ff_sctab"; "R14"; "ff_S"; "ff_idx"; "ff_nontrivial_free"; "ff_stride"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "sym_run"; "RsCut"; "RsSymJump"; "lf_state"; "RsEcall"; "lf_reason"; "stop_reason"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_runs.RP"; "c"; "E_mu"; "segs"; "X_ret"; "X_ret2"; "D_after"; "X_nt"; "e"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "pre_regs"; "NF"; "cut_regs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "slot_end"; "reserved_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "free_stack"; "topL"; "mc_ctx"; "mc_need_locks"; "mc_size_classes"; "byteview_of"; "mc_img_hi"; "mc_lock"; "mc_tp"; "size_classes_bytes"; "addr_of"; "mc_replaced"; "owned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "V_FREE_A1"; "stack_win"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "V_DEPTH"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_runs.States"; "endM"; "objs_rsv"; "FS_NEXT"; "F_tp_facts"; "F_win_facts"; "p_facts"; "strideM"; "O_lock"; "memsv"; "objs_common"; "F_frame_cells"; "F_stk"; "F_stkF"; "O_area"; "O_errnoF"; "O_grp"; "O_meta"; "O_nl"; "O_sct"; "O_sec"; "hdr_obj"; "kc_facts"; "km_facts"; "objs_rsvM"; "ret_regs"; "rsvM_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "carved"; "cells_inside"; "wseg_addr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_I"; "why_w"; "rsv_j"; "rsv_r"; "xof"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_I.States"; "has_sct"; "Dmid"; "mid_objs"; "fixed7"; "h3_of"; "pwZ"; "wins"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_runs.Chain"; "leafXG"; "runXG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface"; "L_SIZECLASSES"; "carvable"; "d_range"; "bv_facts"; "bv_ram"; "d_pairwise"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "MInv"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT"; "ne_ret"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel"; "frame_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require Stdlib.Logic.FunctionalExtensionality.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockView.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeRelease.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_fslow_runs.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_slow.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Inductive kc_kind := KC_A0 | KC_A1.
Inductive km_kind := KM_A1 | KM_B.
Inductive rcode := C0 | C1 | C2 | C3 | C4 | C5E | C5G.
Inductive fvar := FVC (k : kc_kind) (r : ff_rsv) (w : fs_why) | FVM (k : km_kind) (j : rcode).
Definition code_of (j : rcode) : Z := ltac2:(tb__ "0|1|
Sa0S41Lj;Vj;Z0Z1Z2Z3Z4Z5M0G0Xa0x7").

Section States.
Variables (c : fs_consts) (e : ntentry_consts).
Let f : ff_consts := fs_ff c.

Definition F_stk : sobj := stack_win free_stack.
Definition F_win_facts : list sprop := ltac2:(tb__ "0|0|
S4S10S0S10S12aS0S10S12bS11aA1S1S10A1A3A3S129S11aA1A3").
Definition F_tp_facts : list sprop := ltac2:(tb__ "0|1|
S0S10S1dS14Z1000A1S12P18M0A1A2S0S10S1fG0Z2A2S1S10A1A3A3").

Definition strideM : sv := ltac2:(tb__ "0|0|
S17S80S17S81S5fP87A1S14Zfffffffffffff000A1A3S14N10A1A3").
Definition memsv : sv := SAlu ALU_ADD gm_mem_sv (SLit (-16)).
Definition endM : sv := ltac2:(tb__ "0|0|
S17S80S17S80S135S133A3S14ZcA1A3").

Definition hdr_obj (h3 : sv) : sobj := ltac2:(tb__ "0|3|
S19S5fPcA1S14N4A1M0S14Z0A1M1S0S15S16G0Z1M2G1A3S0S15S16S14N3A1G2Vh3;A3S0S15S16S14N2A1Z2S5fP83A1A3S1S15A1A3A3A3S1aA5").
Definition O_grp : sobj := ltac2:(tb__ "0|1|
S19S6cS14N10A1M0S14N8A1S0S15S16G0Z8S5fP84A1A3S1S15A1A3S1aA5").
Definition O_meta : sobj := ltac2:(tb__ "0|3|
S19S5fP84A1S14Z10A1M0S14Z28A1S0S15S16G0Z8M1S135A3S0S15S16S14Z18A1Z4M2S5fP85A1A3S0S15S16S14Z1cA1G2S5fP86A1A3S0S15S16S14Z20A1G1S5fP87A1A3S1S15A1A3A3A3A3S1aA5").
Definition O_area : sobj := ltac2:(tb__ "0|2|
S19S17S81S5fP84A1S14S68A1A3S14Z0A1M0S14Z8M1A1S0S15S16G0G1S5fP88A1A3S1S15A1A3S1aA5").
Definition O_sec : sobj := ltac2:(tb__ "0|2|
S19S14Sf3Vf;A1A1S14Z0A1M0S14Z8M1A1S0S15S16G0G1S5fP88A1A3S1S15A1A3S1aA5").
Definition O_nl : sobj := ltac2:(tb__ "0|2|
S19S14S50Sf4Vf;A1Z3A2A1S14Z0A1M0S14Z1M1A1S0S15S16G0G1G0A3S1S15A1A3S1aA5").
Definition O_lock : sobj := ltac2:(tb__ "0|2|
S19S14Sf5Vf;A1A1S14Z0A1M0S14Z4M1A1S0S15S16G0G1G0A3S1S15A1A3S1aA5").
Definition O_sct : sobj := ltac2:(tb__ "0|0|
S19S14Sf7Vf;A1A1S14Z0A1S14Z60A1S1S15A1S2dS67A1A5").
Definition objs_common (h3 : sv) : list sobj := ltac2:(tb__ "0|0|
S0S13S138S0S13S141Vh3;A1S0S13S13cS0S13S13dS0S13S13aS0S13S140S0S13S13eS0S13S134S1S13A1A3A3A3A3A3A3A3A3").

Definition objs_rsv (en : sv) (r : ff_rsv) : list sobj := ltac2:(tb__ "0|b|
Se9S9S13A1Lr;Vr;S0S13S19Ven;S14Z0A1M0S14Z1M1A1M2S0S15S16G0G1G0A3S1S15A1A3M3S1aA5S1S13A1M4A3M5S0S13S19S17S83Ven;SefA3G0G2G3S1aA5G5A3S0S13S19Ven;S14N5A1M6G2S0S15S16G6G1G0A3M7S0S15S16S14N4A1M8Z4M9S14Z5A1A3G3A3A3S1aA5G4A3S0S13S19Ven;G6G2S0S15G7S0S15S16G8G9S5fP89A1MaA3G3A3A3S1aA5S0S13S19S17S83Ven;GaA3G0G2G3S1aA5G4A3A3Xe9x4").

Definition objs_rsvM (j : rcode) : list sobj := ltac2:(tb__ "0|6|
Sa0S9S13A1Lj;Vj;S12eS12dSecA2S0S13S19S12dS14S59Sa8Vj;A1A1M0A1M1S14S50G0Z1M2A2A1S0S15S16G1G2S14Z0A1M3A3S1S15A1M4A3S1aA5S0S13S19S12dG3S14G2A1S0S15S16G3G2G3A3G4A3S1aA5S1S13A1A3A3M5G5G5G5S12eS12dSf1A2S12eS12dSf2A2Xa0x7").

Definition kc_facts (k : kc_kind) : list sprop := ltac2:(tb__ "0|3|
S4S10Sa1S9S10A1Lk;Vk;S60S65A1S4S10S60S66A1S0S10S1eS18S7fS17S81S5fP87A1M0S14Z1fA1A3S14Z0A1M1A3A1S1S10A1M2A3A3Xa1x2S0S10S1dS17S81S17S86G0S14Z5A1A3S14Z7eA1A3S14Z5eA1A2S0S10S18S7fS17S81SebSeeA3G1A3G2A3A3A3").

Definition km_facts (k : km_kind) : list sprop := ltac2:(tb__ "0|5|
S4S10S0S10S1fPcZ4A2S0S10S1dS5fP83A1M0S14ZffffA1A2S0S10S18S7fS17S81S5fP87A1S14Z1fA1A3S14Z0A1M1A3S0S10S18S7fS17S81S23S8Q20M2S5fP85A1A3S14Z1A1M3A3G1A3S0S10S18S7fS17S81S23S8G2S5fP86A1A3G3A3G1A3S0S10S18S7fS17S81SebG3A3G1A3S0S10S1dS14Z20A1S133A2S0S10S1dS133S14S52Z2Z3fA2A1A2S1S10A1M4A3A3A3A3A3A3A3A3S4S10S62S9fS9S10A1Lk;Vk;S0S10S1eS18S87S14Z2fA1S63A3A1S0S10S1eS18S82G0S64A3A1G4A3A3S61X9fx2A3A3").
Definition rsvM_facts (j : rcode) : list sprop := ltac2:(tb__ "0|4|
Sa0S9S10A1Lj;Vj;S0S10S18S82S17S83S12dS5fPcA1A3M0S14Sa8Vj;A1A1A3S1S10A1M1A3M2G2G2G2G2G2S0S10S1dS5fP89A1M3S14ZffffffffA1A2S0S10S18S87S14Z4A1G3A3S0S10S18S82G0G3A3G1A3A3A3Xa0x7").
Definition p_facts : list sprop := ltac2:(tb__ "0|1|
S0S10S1eS18S7fS5fPcA1M0S14Z0A1A3A1S0S10S1dS14Z1000A1G0A2S1S10A1A3A3").

Definition FS_NEXT : positive := 300%positive.
Definition D_call (x : fvar) : sstate := ltac2:(tb__ "0|6|
S9eS22Lx;Vx;Sa1Se9Se2S1bSeaVf;A1M0S113S114S0S5S7S11A2M1S6S7S11UbS12S127A1A4S1G1A1A3A2M2S112S1cSaS11A1M3S4S13S136S5fP82A1A1S4S13S12eSedR2A2S0S13S13fS1S13A1M4A3M5A3A3S4S10S131S4S10S130S4S10S132S4S10S142R3A1S4S10Sf0R2A1Se4R1A1A3A3A3A3A3S12fS2A9Lw;Lr;Lk;S9fSa0S1bG0G2S112S1cG3S4S13S136S14S55Z20Sa8R1A1A2A1A1S4S13S144R1A1S9fS9S13A1Lk;R2G5G4X9fx2A3A3S4S10S131S4S10S130S4S10S132S4S10S143R2A1S4S10S146R1A1Se4Se3A1A3A3A3A3A3S12fS2A9Lj;Lk;X9ex2").
Definition idx_of (x : fvar) : sv := ltac2:(tb__ "0|0|
S9eS11Lx;Vx;Sa1Se9Se2S17S81S5fP82A1S14Z1fA1A3Lw;Lr;Lk;S9fSa0S14Z0A1Lj;Lk;X9ex2").

Definition F_frame_cells : list cell := ltac2:(tb__ "0|1|
S0S15S16S14N28A1Z8M0S12P27A1A3S0S15S16S14N20A1G0S12P26A1A3S0S15S16S14N18A1G0S12P1dA1A3S0S15S16S14N10A1G0S12P1cA1A3S0S15S16S14N8A1G0S12PbA1A3S1S15A1A3A3A3A3A3").
Definition F_stkF : sobj := ltac2:(tb__ "0|0|
S19S12PaA1S12S12cA1S14Z0A1S137S1aA5").
Definition O_errnoF : sobj := ltac2:(tb__ "0|1|
S19S12P18A1S14Na4A1M0S14Na0A1S0S15S16G0Z4S5fPb6A1A3S1S15A1A3S1aA5").
Definition ret_regs : list sv := ltac2:(tb__ "0|1|
S113S116Pc8A1S0S5S7S11A2M0S6S7S11U1S14Se6Vc;A1A1A4S0G0S6S7S11U2S17S80S12PaA1S14N30A1A3A4S0G0S6S7S11U8S12Pd0A1A4S0G0S6S7S11U9S5fPcA1A4S0G0S6S7S11UaS5fPb4A1A4S0G0S6S7S11UbS5fPb5A1A4S1G0A1A3A3A3A3A3A3A2").
Definition D_ret (len0 : bool) : sstate := ltac2:(tb__ "0|3|
S1bS166Ve;A1S145S112S1cSaS11A1S4S13S0S13S139S0S13S134S1S13A1M0A3A3S3S9S13A1Llen0;Vlen0;G0S0S13S13bG0A3X3x2A3S4S10S131S4S10S130S4S10S132S3S9S10A1Llen0;Vlen0;S0S10S18S7fS5fPb5A1S14Z0A1A3M1S1S10A1M2A3S0S10S1eG1A1S0S10S1dS5fPb6A1S14ZffffffffA1A2G2A3A3X3x2A3A3A3S12fS2A9").

Definition fs_cutsX : list Z := fs_cuts c.
End States.

Definition d0 : sstate := ltac2:(tb__ "0|1|
S1bZ0S1S11A1M0G0S1cSaS11A1S1S13A1S1S10A1P1S2A9").
Definition reg (S : sstate) (r : nat) : sv := ltac2:(tb__ "0|0|
S9dS11Vr;S2cVS;A1S14Z0A1A4").
Definition lf0 (l : list leaf) (i : nat) (d : sstate) : sstate := ltac2:(tb__ "0|0|
S102S9dSfdVi;Vl;SfeVd;S100A2A4A1").
Definition sh (L : leaf) : Z * stop_reason := ltac2:(tb__ "0|0|
S6S41S105S27S102VL;A1A1S104VL;A1A4").

Section Chain.
Variables (segs : list Segment) (c : fs_consts) (e : ntentry_consts).
Definition runXG (fuel : nat) (S : sstate) : list leaf := ltac2:(tb__ "0|1|
SbS9SfdA1M0A1G0Lx;SffVsegs;Vfuel;Sa9Vc;A1VS;S8A5G0R1Ll;S1SfdA1Xbx2").
Definition leafXG (fuel : nat) (S : sstate) : sstate := ltac2:(tb__ "0|0|
Sc9S158Vfuel;VS;A2U0Sc7A3").
Definition X_ntG (x : fvar) : sstate := ltac2:(tb__ "0|0|
S157U190Sa2Vc;Vx;A2A2").
Definition X_retG : sstate := ltac2:(tb__ "0|0|
S157Uc8SaaVc;Ve;S8A3A2").
Definition E_muG : sstate := ltac2:(tb__ "0|0|
S157U12cSaaVc;Ve;S2A3A2").
Definition D_afterG : sstate := S_ret_lit E_muG 0.
Definition X_ret2G : sstate := leafXG 200 D_afterG.
End Chain.

Module RP.
Definition segs := segsU. Definition c := FS_P. Definition e := NTE_U.
Local Notation cuts := (fs_cutsX c) (only parsing).
Ltac cert := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast.
Ltac certb := vm_cast_no_check (@eq_refl bool true).

Definition X_nt (x : fvar) : sstate := ltac2:(tb__ "0|b3|
S9eS9eS22Lc;R1Sa1Se9Se2Sa1S22Lc;R3Se9S22Lc;M0R2Se2S22Lc;M1R1S1bZ2084cM2S0S11S12P14A1M3S0S11S14Z206e4A1M4S0S11S17S80S12PaM5A1M6S14N30A1A3M7S0S11S12P17A1M8S0S11S12P18M9A1MaS0S11S12P19A1MbS0S11S12P1aA1McS0S11S12P1bA1MdS0S11S17S81S12P82A1MeS14Z1fA1MfA3M10S0S11S12PcM11A1M12S0S11S12P84A1M13S0S11G10S0S11S24S85S14Z1M14A1M15G10A3M16S0S11S24S80S24S85S14Z2M17A1M18S12P87A1M19A3S14ZffffffffffffffffA1M1aA3M1bS0S11S14Z5a670A1M1cS0S11S23S8Q20M1dS12P86A1M1eA3M1fS0S11S17S89S23S8G1dS12P85A1M20A3M21G1fA3M22S0S11S14Z0A1M23S0S11S12P26A1M24S0S11S12P27A1M25S0S11S12P28A1S0S11S12P29A1S0S11S12P2aA1S0S11S12P2bA1S0S11S12P2cA1S0S11S12P2dA1S0S11S12P2eA1S0S11S12P2fA1S0S11S12P30A1S0S11S12P31A1S0S11S12P32A1S0S11S12P33A1S1S11A1M26A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M27A3A3A3A3M28A3A3A3A3A3A3A3A3A3A3A3A3A3M29S0S11S12P3cA1S0S11S12P3dA1S0S11S12P3eA1S0S11S12P3fA1S0S11S12P40A1S0S11S12P41A1S0S11S12P42A1S0S11S12P43A1S0S11S12P44A1S0S11S12P45A1S0S11S12P46A1S0S11S12P47A1S0S11S12P48A1S0S11S12P49A1S0S11S12P4aA1S0S11S12P4bA1S0S11S12P4cA1S0S11S12P4dA1S0S11S12P4eA1S0S11S12P4fA1S0S11S12P50A1S0S11S12P51A1S0S11S12P52A1S0S11S12P53A1S0S11S12P54A1S0S11S12P55A1S0S11S12P56A1S0S11S12P57A1S0S11S12P58A1S0S11S12P59A1S0S11S12P5aA1S0S11S12P5bA1G26A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M2aS1cSaS11A1M2bS0S13S19G6S12PfA1M2cG23S0S15S16S14N28A1Z8M2dG25A3S0S15S16S14N20A1G2dG24A3S0S15S16S14N18A1G2dS12P1dA1A3S0S15S16S14N10A1M2eG2dS12P1cA1A3S0S15S16S14N8A1M2fG2dS12PbA1A3S1S15A1M30A3A3A3A3A3S1aA5M31S0S13S19G12S14N4A1M32G23S0S15S16S14N2A1M33G17G23A3S0S15S16S14N3A1M34G14G1aA3S0S15S16G32G14G23A3G30A3M35A3A3S1aA5M36S0S13S19S17S83G12S17S85S12P83A1M37S14Z4M38A1M39A3A3M3aG2eG2fS0S15S16G2eG2dG13A3G30A3S1aA5M3bS0S13S19G13S14Z10A1M3cS14Z28A1S0S15S16G3cG2dS17S80G3aG2eA3M3dA3S0S15S16S14Z18A1G38G20A3S0S15S16S14Z1cA1G38G1eA3S0S15S16S14Z20A1M3eG2dG19A3G30A3A3A3A3S1aA5M3fS0S13S19S17S81G13S14Zfffffffffffff000A1M40A3G23S14G2dA1M41S0S15S16G23G2dS12P88A1A3G30A3M42S1aA5M43S0S13S19S14Z5a3d0A1G23G41G42S1aA5M44S0S13S19S14Z5a35bA1G23G15S0S15S16G23G14G23A3G30A3M45S1aA5M46S0S13S19S14Z5a3c8A1G23G39S0S15S16G23G38G23A3G30A3S1aA5M47S0S13S19S17S80S17S80S17S80G3dS17S85S23S2Q10M48S2eP1M49S17S81S17S86G19S14Z5A1M4aA3S14Z7eA1A3M4bG17A3A3G39A3M4cA3S2aS88G4cG10A3A3S14ZcA1M4dA3M4eG23G15G45S1aA5S0S13S19S14Z108ecA1G23S14Z60A1G30S2dG49A1A5S1S13A1M4fA3M50A3M51A3A3A3A3A3A3A3A3M52S0S10S1fG5G38A2M53S0S10S1dS14Z7fff7f800000A1S17S80G6G2cA3A2M54S0S10S18S84S14N1d0A1G2cA3M55S0S10S18S84G2cS14N10000000000A1A3M56S0S10S1dS14Z1000A1M57GaA2M58S0S10S1fG9G17A2M59S0S10S1eS18S7fG12G23A3A1M5aS0S10S1dG57G12A2M5bS0S10S1fG11G38A2M5cS0S10S1dGeS14ZffA1A2M5dS0S10S1dG37S14ZffffA1A2M5eS0S10S18S82S17S81G19GfA3M5fG10A3M60S0S10S18S7fS17S81G21G16A3G23A3M61S0S10S18S7fS17S81G1fG16A3G23A3M62S0S10S1eS18S87S14Z2fA1S17S86S17S85G19S14Z34A1A3S14Z3aA1A3M63A3M64A1M65S0S10S18S82G37S2aS88S23S2G48S2eG49S17S85G63G15A3G17A3A3M66G10A3A3M67S0S10S1eS18S82G37S2aS88S17S80G10G15A3G66A3A3A1M68S0S10S18S7fS17S86G19G4dA3M69G23A3M6aS0S10S1dG4bS14Z5eA1A2M6bS0S10S18S7fS17S81G22G16A3G23A3M6cS0S10S1dGe
GfA2M6dS0S10S18S82S17S83G4eG12A3M6eG23A3M6fS0S10S18S7fG1fG23A3M70S1S10A1M71A3M72A3A3A3A3M73A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cM74S2A9S1bG2S0S11G3S0S11G4S0S11G7S0S11G8S0S11GaS0S11GbS0S11GcS0S11GdS0S11G10S0S11G12S0S11G13S0S11G10S0S11G16S0S11G1bS0S11G1cS0S11G1fS0S11S24S80G22G16A3M75G27A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3M76G2aS1cG2bG52S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5dS0S10G5eS0S10G60S0S10G61S0S10G62S0S10G65S0S10G67S0S10G68S0S10G6aS0S10G6bS0S10G6cS0S10G6dS0S10G6fS0S10S1eG70A1S0S10S18S7fG75G1bA3G71A3A3M77A3A3A3A3M78A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9Xe2x2G1R1S1bG2G29G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13S19S17S83G4eS17S86GeG4aA3M79A3G23G15G45S1aA5G51A3A3A3A3A3A3A3A3A3M7aS0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5dS0S10G5eS0S10G60S0S10G61S0S10G62S0S10G65S0S10G67S0S10G68S0S10G6aS0S10G6bS0S10G6cS0S10S18S87GeS14Za0A1A3M7bS0S10S1eS18S7fG79G23A3A1M7cS0S10S18S82G6eG79A3M7dG72A3A3A3A3A3M7eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G76G2aS1cG2bG7aS0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5dS0S10G5eS0S10G60S0S10G61S0S10G62S0S10G65S0S10G67S0S10G68S0S10G6aS0S10G6bS0S10G6cS0S10G7bS0S10G7cS0S10G7dG77A3A3A3A3A3M7fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9Xe2x2G1R1S1bG2G29G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13S19G4eS14N5A1M80G15S0S15S16G80G14G23A3M81S0S15S16G32G38G4aA3G45A3A3M82S1aA5G50A3A3A3A3A3A3A3A3A3M83S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5dS0S10G5eS0S10G60S0S10G61S0S10G62S0S10G65S0S10G67S0S10G68S0S10G6aS0S10G6bS0S10G6cS0S10S1eG7bA1M84S0S10S18S7fG79G4aA3M85S0S10S18S82G6eG4aA3M86G72A3A3A3A3A3M87A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G76G2aS1cG2bG83S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5dS0S10G5eS0S10G60S0S10G61S0S10G62S0S10G65S0S10G67S0S10G68S0S10G6aS0S10G6bS0S10G6cS0S10G84S0S10G85S0S10G86G77A3A3A3A3A3M88A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9Xe2x2G1R1S1bG2G29G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13S19G4eG80G15S0S15G81S0S15S16G32G38S12P89A1M89A3G45A3A3M8aS1aA5S0S13S19S17S83G4eG89A3G23G15G45S1aA5G50A3A3A3A3A3A3A3A3A3A3M8bS0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5dS0S10G5eS0S10G60S0S10G61S0S10G62S0S10G65S0S10G67S0S10G68S0S10G6aS0S10G6bS0S10G6cS0S10G84S0S10G85S0S10S1dG89S14ZffffffffA1A2M8cS0S10S18S87G39G89A3M8dS0S10S18S82G6eG89A3M8eG72A3A3A3A3A3A3A3M8fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G76G2aS1cG2bG8bS0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5dS0S10G5eS0S10G60S0S10G61S0S10G62S0S10G65S0S10G67S0S10G68S0S10G6aS0S10G6bS0S10G6cS0S10G84S0S10G85S0S10G8cS0S10G8dS0S10G8eG77A3A3A3A3A3A3A3M90A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9Xe2x2Xe9x4G0R2G1R1S1bG2G29G2aS1cG2bG52S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5dS0
S10G5eS0S10G60S0S10G61S0S10G62S0S10G65S0S10G67S0S10G68S0S10S1eG6aA1M91S0S10S18S82S17S80S17S85G69G41A3S14N1A1M92A3G37A3M93S0S10S1eS18S7fG5fG23A3M94A1M95G73A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G76G2aS1cG2bG52S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5dS0S10G5eS0S10G60S0S10G61S0S10G62S0S10G65S0S10G67S0S10G68S0S10G91S0S10G93S0S10G95G78A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9Xe2x2G1R1S1bG2G29G2aS1cG2bG7aS0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5dS0S10G5eS0S10G60S0S10G61S0S10G62S0S10G65S0S10G67S0S10G68S0S10G91S0S10G93S0S10G95G7eA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G76G2aS1cG2bG7aS0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5dS0S10G5eS0S10G60S0S10G61S0S10G62S0S10G65S0S10G67S0S10G68S0S10G91S0S10G93S0S10G95G7fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9Xe2x2G1R1S1bG2G29G2aS1cG2bG83S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5dS0S10G5eS0S10G60S0S10G61S0S10G62S0S10G65S0S10G67S0S10G68S0S10G91S0S10G93S0S10G95G87A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G76G2aS1cG2bG83S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5dS0S10G5eS0S10G60S0S10G61S0S10G62S0S10G65S0S10G67S0S10G68S0S10G91S0S10G93S0S10G95G88A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9Xe2x2G1R1S1bG2G29G2aS1cG2bG8bS0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5dS0S10G5eS0S10G60S0S10G61S0S10G62S0S10G65S0S10G67S0S10G68S0S10G91S0S10G93S0S10G95G8fA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G76G2aS1cG2bG8bS0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5dS0S10G5eS0S10G60S0S10G61S0S10G62S0S10G65S0S10G67S0S10G68S0S10G91S0S10G93S0S10G95G90A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9Xe2x2Xe9x4Xa1x2Lw;Lr;Lk;S9fSa0S9fS22Lc;R2Sa0S22Lc;M96R1S1bG2S0S11G3S0S11G4S0S11G7S0S11G8S0S11GaS0S11GbS0S11GcS0S11GdS0S11G23S0S11G12S0S11G13S0S11G23S0S11G15G28A3A3A3A3A3A3A3A3A3A3A3A3A3M97G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13S19S17S80S17S80G3dS17S80S17S81G19G40A3G2eA3M98A3G4dA3M99G23G15G45S1aA5M9aG50A3M9bA3A3A3A3A3A3A3A3S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5eS0S10G94S0S10S18S7fS17S81G21G15A3G23A3M9cS0S10S18S7fS17S81G1fG15A3G23A3M9dS0S10S18S7fS17S81G22G15A3G23A3M9eS0S10S1dG3eG98A2M9fS0S10S1dG98S14Z8000000000000000A1A2Ma0S0S10G91S0S10G93S0S10G65S0S10S1eS18S82G37G66A3A1Ma1S0S10S18S82S17S83G99G12A3Ma2G23A3G72A3Ma3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G97G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13S19G99G92G23S0S15S16G92G14G23A3G30A3S1aA5Ma4G9bA3A3A3A3A3A3A3A3A3S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5eS0S10G94S0S10G9cS0S10G9dS0S10G9eS0S10G9fS0S10Ga0S0S10G91S0S10G93S0S10G65S0S10Ga1S0S10S18S82Ga2G15A3G72A3Ma5A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G97G2aS1cG2bS0S13G31S0S13
G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13S19G99G33G92S0S15S16G33G14G23A3G30A3S1aA5Ma6G9bA3A3A3A3A3A3A3A3A3S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5eS0S10G94S0S10G9cS0S10G9dS0S10G9eS0S10G9fS0S10Ga0S0S10G91S0S10G93S0S10G65S0S10Ga1S0S10S18S82Ga2G18A3G72A3Ma7A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G97G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13S19G99G34G33S0S15S16G34G14G23A3G30A3S1aA5Ma8G9bA3A3A3A3A3A3A3A3A3S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5eS0S10G94S0S10G9cS0S10G9dS0S10G9eS0S10G9fS0S10Ga0S0S10G91S0S10G93S0S10G65S0S10Ga1S0S10S18S82Ga2S14Z3A1A3G72A3Ma9A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G97G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13S19G99G32G34G35S1aA5MaaG9bA3A3A3A3A3A3A3A3A3S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5eS0S10G94S0S10G9cS0S10G9dS0S10G9eS0S10G9fS0S10Ga0S0S10G91S0S10G93S0S10G65S0S10Ga1S0S10S18S82Ga2G39A3G72A3MabA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G97G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13S19G99G80G15G82S1aA5MacG50A3A3A3A3A3A3A3A3A3S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5eS0S10G94S0S10G9cS0S10G9dS0S10G9eS0S10G9fS0S10Ga0S0S10G91S0S10G93S0S10G65S0S10Ga1S0S10S18S82Ga2G4aA3G72A3MadA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G97G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13S19G99G80G15G8aS1aA5MaeS0S13S19S17S83G99G89A3G23G15G45S1aA5MafG50A3A3A3A3A3A3A3A3A3A3S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5eS0S10G94S0S10G9cS0S10G9dS0S10G9eS0S10G9fS0S10Ga0S0S10G91S0S10G93S0S10G65S0S10Ga1S0S10G8cS0S10G8dS0S10S18S82Ga2G89A3G72A3A3A3Mb0A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9Xa0x7G96R1S1bG2G97G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13G9aG4fA3Mb1A3A3A3A3A3A3A3A3S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5eS0S10G94S0S10G9cS0S10G9dS0S10G9eS0S10G9fS0S10Ga0S0S10G91S0S10G93S0S10G64S0S10S18S7fG63S14Z3fA1A3Mb2Ga3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G97G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13Ga4Gb1A3A3A3A3A3A3A3A3A3S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5eS0S10G94S0S10G9cS0S10G9dS0S10G9eS0S10G9fS0S10Ga0S0S10G91S0S10G93S0S10G64S0S10Gb2Ga5A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G97G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13Ga6Gb1A3A3A3A3A3A3A3A3A3S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5eS0S10G94S0S10G9cS0S10G9dS0S10G9eS0S10G9fS0S10Ga0S0S10G91S0S10G93S0S10G64S0S10Gb2Ga7A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G97G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13Ga8Gb1A3A3A3A3A3A3A3A3A3
S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5eS0S10G94S0S10G9cS0S10G9dS0S10G9eS0S10G9fS0S10Ga0S0S10G91S0S10G93S0S10G64S0S10Gb2Ga9A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G97G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13GaaGb1A3A3A3A3A3A3A3A3A3S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5eS0S10G94S0S10G9cS0S10G9dS0S10G9eS0S10G9fS0S10Ga0S0S10G91S0S10G93S0S10G64S0S10Gb2GabA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G97G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13GacG4fA3A3A3A3A3A3A3A3A3S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5eS0S10G94S0S10G9cS0S10G9dS0S10G9eS0S10G9fS0S10Ga0S0S10G91S0S10G93S0S10G64S0S10Gb2GadA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9S1bG2G97G2aS1cG2bS0S13G31S0S13G36S0S13G3bS0S13G3fS0S13G43S0S13G44S0S13G46S0S13G47S0S13GaeS0S13GafG4fA3A3A3A3A3A3A3A3A3A3S0S10G53S0S10G54S0S10G55S0S10G56S0S10G58S0S10G59S0S10G5aS0S10G5bS0S10G5cS0S10G5eS0S10G94S0S10G9cS0S10G9dS0S10G9eS0S10G9fS0S10Ga0S0S10G91S0S10G93S0S10G64S0S10Gb2Gb0A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3G74S2A9Xa0x7X9fx2Lj;Lk;X9ex2Lx;Vx;A1").
Definition X_ret : sstate := ltac:(let v := eval vm_compute in (X_retG segs c e) in exact v).
Definition E_mu : sstate := ltac:(let v := eval vm_compute in (E_muG segs c e) in exact v).
Definition D_after : sstate := ltac:(let v := eval vm_compute in (D_afterG segs c e) in exact v).
Definition X_ret2 : sstate := ltac:(let v := eval vm_compute in (X_ret2G segs c e) in exact v).

Lemma run_call : ltac2:(tb__ "0|1|
S9eS3cSbS9SfdA1M0A1SffS10cU190Sa9S10aA1Sa2S10aR1A2S8A5ScG0S0SfdSfeS110R1A1S100A2S1SfdA1A3A2A3Fx;").
Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.
Lemma X_nt_shape : ltac2:(tb__ "0|1|
S9eS3dS3cS41S27S110R1A1M0A1SfbSe5S10aA1A1A3S3dS3cS11Sa4G0U1A2S14Se6S10aA1A1A3S3dS3cS11Sa4G0U2A2S17S80S12PaA1S14N30A1A3A3S3dS3cS11Sa4G0UaA2S5fP84A1A3S3dS3cS11Sa4G0UbA2Sc8R1A1A3S3cS42S29G0A1Sa3A3A2A2A2A2A2Fx;").
Proof. intros x; destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; repeat split; reflexivity. Qed.
Ltac certr := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast.
Lemma run_ret0 : ltac2:(tb__ "0|1|
S3cSbS9SfdA1M0A1SffS10cUc8Sa9S10aA1SaaS10aS111S8A3S8A5ScG0S0SfdSfeS10dS101A2S1SfdA1A3A2A3"). Proof. certr. Qed.
Lemma X_ret_pc : ltac2:(tb__ "0|0|
S3dS3cS41S27S10dA1Sf6Se5S10aA1A1A3S3cS42S29S10dA1Sa3A3A2"). Proof. split; reflexivity. Qed.
Lemma run_unmap : ltac2:(tb__ "0|1|
S3cSbS9SfdA1M0A1SffS10cU12cSa9S10aA1SaaS10aS111S2A3S8A5ScG0S0SfdSfeS10bS103A2S1SfdA1A3A2A3"). Proof. certr. Qed.
Lemma E_mu_shape : ltac2:(tb__ "0|0|
S3dS3cS41S27S10bA1Se8S10aA1A3S3dS3cS11Sa4S10bU11A2S14Zd7A1A3S3dS3cS11Sa4S10bUaA2S5fPb4A1A3S3dS3cS11Sa4S10bUbA2S5fPb5A1A3S3cS42S29S10bA1Sa3A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma D_after_eq : ltac2:(tb__ "0|0|
S3cS22S10fS165S10bZ0A2A3"). Proof. cert. Qed.
Lemma run_after : ltac2:(tb__ "0|1|
S3cSbS9SfdA1M0A1SffS10cUc8Sa9S10aA1S10fS8A5ScG0S0SfdSfeS10eS101A2S1SfdA1A3A2A3"). Proof. certr. Qed.
Lemma X_ret2_pc : ltac2:(tb__ "0|0|
S3dS3cS41S27S10eA1Sf6Se5S10aA1A1A3S3cS42S29S10eA1Sa3A3A2"). Proof. split; reflexivity. Qed.
End RP.
End Mal_fslow_runs.

Module Mal_fslow_I.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockView OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeRelease OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_slow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Local Notation SP := SymSoundR.SP.
Definition C : mconsts := C_U.
Definition E : entry_consts := EC_U.
Definition NTE : ntentry_consts := NTE_U.

Definition rsv_r (r : Z) : ff_rsv := ltac2:(tb__ "0|1|
S3Se9L_;M0S54Vr;Z0A2SecG0S5bVr;Z4A2Sf8G0S54Vr;Z5A2Sf1Sf2X3x2X3x2X3x2").
Definition rsv_j (r : Z) : rcode := ltac2:(tb__ "0|1|
S3Sa0L_;M0S54Vr;Z0A2SabG0S54Vr;Z1A2SbdG0S54Vr;Z2A2SbeG0S54Vr;Z3A2SbfG0S54Vr;Z4A2Sc0G0S54Vr;Z5A2Sc1Sc2X3x2X3x2X3x2X3x2X3x2X3x2").
Definition why_w (freed : Z) : fs_why := ltac2:(tb__ "0|0|
S3Se2L_;S54Vfreed;Z0A2Se3Se7X3x2").
Definition xof (am : ameta) (fr : frame) : fvar := ltac2:(tb__ "0|5|
S119Vam;Vfr;A2S41S3S9eL_;M0S54SccVam;A1Z0M1A2Sa5Sc3S14eR1A1M2S14cScdVam;A1A1M3A3G0SeS54ScbVam;A1G1A2A1Sa5Sc4G2G3A3G0S5cSceVam;A1Z30A2Sa6Sc5S14dR1A1M4A2Sa6Sc6G4A2X3x2X3x2X3x2Tr;").

Definition slow_case (s : astate) (g : sptr) (am : ameta) (i : Z) (fr : frame) : Prop := ltac2:(tb__ "0|3|
S3dSe1S5S5S5ScfSd2A2M0S41A2M1Sd1A2S6G1Sd1S6G0S41S6ScfSd2Vg;Vam;A4Vi;A4Vfr;A4S95Vs;A1A3S3dS3cSd5Sd6Vfr;A1Sd4A3S3eS3cS41ScdVam;A1M2Z0A3S3cS41S50S56G2Sd0Vam;A1A2Sd7Vi;A1A2Sd8ScbVam;A1A1A3A2A2A2").

Section States.
Variables (c : fs_consts).
Let f : ff_consts := fs_ff c.

Definition S1 : sstate := ltac2:(tb__ "0|1|
S1bSeaVf;A1S113S114S0S5S7S11A2M0S6S7S11UbS12S127A1A4S1G0A1A3A2S112S1cSaS11A1S0S13S128S11aA1S0S13S19S12PcA1S14Z0A1S12PdA1S1S15A1S1aA5S1S13A1A3A3Sa7S115S2A9").

Definition S1r : sstate := ltac2:(tb__ "0|1|
S1bSeaVf;A1S113S114S0S5S7S11A2M0S6S7S11UbS12S127A1A4S1G0A1A3A2S112S1cSaS11A1S0S13S128S11aA1S1S13A1A3Sa7S115S2A9").

Definition D0 (x : fvar) : sstate := ltac2:(tb__ "0|1|
S1bSeaVf;A1S113S114S0S5S7S11A2M0S6S7S11UbS12S127A1A4S1G0A1A3A2S112S1cSaS11A1S0S13S128S11aA1S1S13A1A3S26Sa2Vc;Vx;A2A1Sa3S2A9").

Definition fixed7 (h3 : sv) : list sobj := ltac2:(tb__ "0|0|
S0S13SadVh3;A1S0S13Sb2S0S13Sb4S0S13Sb1S0S13Sb6Vc;A1S0S13Sb5Vc;A1S0S13Sb3Vc;A1S1S13A1A3A3A3A3A3A3A3").
Definition wins (x : fvar) : list sobj := ltac2:(tb__ "0|0|
S9eS9S13A1Lx;Vx;Sa1Se9Se2SbaSedR2A2Lw;Lr;Lk;S9fSa0SbbR1A1Lj;Lk;X9ex2").
Definition h3_of (x : fvar) : sv := ltac2:(tb__ "0|0|
S9eS11Lx;Vx;Sa1Se9Se2S5fP82A1Lw;Lr;Lk;S9fSa0S14S55Z20Sa8R1A1A2A1Lj;Lk;X9ex2").
Definition mid_objs (x : fvar) : list sobj := ltac2:(tb__ "0|0|
S4S13S153S154Vx;A1A1S156Vx;A1A3").
Definition has_sct (x : fvar) : bool := ltac2:(tb__ "0|0|
S9eS3Lx;Vx;Sa1Se9Se2S8Lw;Lr;Lk;S9fSa0S9fS3Lk;R2S8S2X9fx2Lj;Lk;X9ex2").
Definition Dmid (x : fvar) : sstate := ltac2:(tb__ "0|1|
S1bSeaVf;A1S113S114S0S5S7S11A2M0S6S7S11UbS12S127A1A4S1G0A1A3A2S112S1cSaS11A1S0S13S128S11aA1S152Vx;A1A3S26Sa2Vc;Vx;A2A1Sa3S2A9").
Lemma D_call_eq x : ltac2:(tb__ "0|3|
S3cS22Sa2Vc;Vx;A2M0S1bSeaVf;A1S113S114S0S5S7S11A2M1S6S7S11UbS12S127A1A4S1G1A1A3A2S112S1cSaS11A1S4S13S0S13S128S11aA1S152Vx;A1A3S3S9S13A1L_;S150Vx;A1S0S13SacVc;A1S1S13A1M2A3G2X3x2A3S26G0A1Sa3S2A9A3").
Proof using . destruct x as [kx r w | [|] j]; reflexivity. Qed.
Lemma Dmid_sct x : ltac2:(tb__ "0|1|
S3cS3S150Vx;A1S8A3S3cS22Sa2Vc;Vx;A2S1bS27S151Vx;A1M0A1S2cG0A1S34G0A1S33G0A1S37G0A1S4S13S36G0A1S0S13SacVc;A1S1S13A1A3A3S26G0A1Sa3S35G0A1A9A3F_;").
Proof using . intros H. rewrite D_call_eq, H. reflexivity. Qed.
Lemma Dmid_nosct x : ltac2:(tb__ "0|0|
S3cS3S150Vx;A1S2A3S3cS22Sa2Vc;Vx;A2S151Vx;A1A3F_;").
Proof using . intros H. rewrite D_call_eq, H, app_nil_r. reflexivity. Qed.

Fixpoint pwZ (l : list (Z * Z)) : Prop :=
  match l with [] => True | r :: t => Forall (fun r' => SymState.ranges_disjoint r r') t /\ pwZ t end.
Lemma pw_of_ranges rho l : ltac2:(tb__ "0|0|
S155S9cS13S5S41S41A2S2fVrho;A1Vl;A4A1S39Vrho;Vl;A2F_;").
Proof using .
  induction l as [|o t IH]; cbn; intros H; [exact I|]. destruct H as [Hf Ht]. split; [|apply IH; exact Ht].
  apply Forall_forall. intros o' Ho'. apply (proj1 (Forall_forall _ _) Hf). apply in_map. exact Ho'.
Qed.
End States.

Section Inst.
Variables (segs : list Segment) (C : mconsts) (c : fs_consts).
Hypothesis HSI : statics_in_image C.
Hypothesis Hrc : ltac2:(tb__ "0|2|
S3eS4fS50S11cVC;A1M0S92A2S125VC;A1M1A2S4fS50G1Z4A2G0A2A2").

Hypothesis HCc : ltac2:(tb__ "0|1|
S3dS3cS41Sf3Se5Vc;A1M0A1S11cVC;A1A3S3dS3cS41S50Sf4G0A1Z3A2S11dVC;A1A3S3dS3cS41Sf5G0A1S121VC;A1A3S3cS41Sf7G0A1S11eVC;A1A3A2A2A2").

Hypothesis NLW : ltac2:(tb__ "0|0|
S3cS3S14bVsegs;S106Q40S11dVC;A1A2A2S8A3").
Hypothesis SCT : ltac2:(tb__ "0|4|
S41S3dS4fZ0M0R1A2S51R1Z60A2A2S3dS3cS3S3aVsegs;S106Q40S50S11eVC;A1R2A2A2M1A2S8A3S3cSbS107Q8M2A1M3A1S38Vsegs;G1A2ScG3S9dG3S5eR2A1S9cS41G3S106G2A1S123A4S106G2G0A2A4A2A3A2F_;Fkk;").

Variables (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame).
Variables (vm : VmMaps) (m : word -> option byte) (rhoC : valuation).
Hypothesis HMI : ltac2:(tb__ "0|0|
S160VC;S15fVs;VL;A2S147Vsegs;Vm;A2S148Vsegs;Vm;A2Vvm;A5").
Hypothesis Hfr : ltac2:(tb__ "0|2|
Se1S5S5S5ScfSd2A2M0S41A2M1Sd1A2S6G1Sd1S6G0S41S6ScfSd2Vg;Vam;A4Vi;A4Vfr;A4S95Vs;A1A3").
Hypothesis Hkind : ltac2:(tb__ "0|0|
S3cSd5Sd6Vfr;A1Sd4A3").
Definition n : Z := fr_n fr.
Definition rsv : Z := reserved_of am fr.
Let pv : positive := 12%positive.

Let rho : valuation := ltac2:(tb__ "0|0|
S164VrhoC;P89S106Q40S6dA2A3").
Hypothesis HpC : ltac2:(tb__ "0|0|
S3cS41S108Q40S25VrhoC;PcA2A2S44VL;Vam;Vi;Vfr;A4A3").
Hypothesis HnC : ltac2:(tb__ "0|0|
S3cS41S108Q40S25VrhoC;PdA2A2S6fA3").
Lemma Hp : ltac2:(tb__ "0|0|
S3cS41S108Q40S25Vrho;Vpv;A2A2S44VL;Vam;Vi;Vfr;A4A3").
Proof using HpC. unfold rho, pv. rewrite rho_set_rw_other by discriminate. exact HpC. Qed.
Lemma Hpv : (pv < 130)%positive. Proof using . reflexivity. Qed.
Variables (a : sptr) (k : Z).
Hypothesis Harea : ltac2:(tb__ "0|2|
S3dSe1ScfVa;Se0Vs;A1A3S3dS3dS4fZ0Vk;A2S51Vk;SdaA2A2S3dS3cScfVg;Sd3Va;S50Sd9S55SdbVk;A2A2A2A3S3dSe1S8aS8eS8fVa;A1U8M0S93A3S8bVs;A1M1A3Se1S8aS8eS97S96A1G0S93A3G1A3A2A2A2A2").

Local Notation "§1§ h__" := (h__ am i fr) (at level 10, h__ global).
Local Abbreviation B_p := (§1§ BlockView.p).
Local Abbreviation B_zP := (@BlockView.zP L am i fr).
Local Notation "§2§ h__" := (h__ segs C Hrc s L vm m HMI) (at level 10, h__ global).
Local Abbreviation B_HW := (§2§ BlockView.HW).
Local Abbreviation B_HC := (§2§ BlockView.HC).
Local Abbreviation B_HLok := (§2§ BlockView.HLok).
Local Abbreviation B_HI := (§2§ BlockView.HI).
Local Abbreviation B_HO := (§2§ BlockView.HO).
Local Abbreviation B_HV := (§2§ BlockView.HV).
Local Abbreviation B_HLG := (§2§ BlockView.HLG).
Local Notation "§3§ h__" := (h__ segs C Hrc s L g am i fr vm m HMI Hfr) (at level 10, h__ global).
Local Abbreviation B_FFx := (§3§ BlockView.FFx).
Local Abbreviation B_zMem := (@BlockView.zMem L am).
Local Abbreviation B_zG := (@BlockView.zG L g).
Local Abbreviation B_h3 := (§1§ BlockView.h3).
Local Abbreviation B_h16 := (§1§ BlockView.h16).
Local Abbreviation B_bits := (@BlockView.bits am).
Local Abbreviation B_sec := (@BlockView.sec L).
Local Abbreviation B_zA := (@BlockView.zA L a).
Local Abbreviation B_GM := (§3§ BlockView.GM).
Local Abbreviation B_Hareg := (@BlockView.Hareg segs C Hrc s L g vm m HMI a k Harea).
Local Abbreviation B_HzA := (@BlockView.HzA segs C Hrc s L g vm m pv HMI a k Harea).
Local Abbreviation B_G0 := (@BlockView.G0 L am).
Local Abbreviation B_Hgrp := (@BlockView.Hgrp segs C Hrc s L g am i fr vm m pv HMI Hfr Hpv).
Local Abbreviation B_Hctx := (@BlockView.Hctx C HSI L pv).
Local Abbreviation B_st := (@BlockView.st am).
Local Abbreviation B_sti := (@BlockView.sti am i).
Local Abbreviation B_n := (@BlockView.n fr).
Local Abbreviation B_R_all := (@BlockView.R_all segs C Hrc s L g am i fr vm m pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_HzP16 := (@BlockView.HzP16 segs C Hrc s L g am i fr vm m pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_vals := (@BlockView.vals L g am i fr).
Local Notation "§4§ h__" := (h__ L g am i fr rho) (at level 10, h__ global).
Local Abbreviation B_rho1 := (§4§ BlockView.rho1).
Local Notation "§5§ h__" := (h__ L g am i fr rho pv) (at level 10, h__ global).
Local Abbreviation B_u64 := (§5§ BlockView.u64).
Local Abbreviation B_zr1_pv := (@BlockView.zr1_pv L g am i fr rho pv Hp Hpv).
Local Abbreviation B_zr1_vals := (@BlockView.zr1_vals segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_zl1_1 := (§4§ BlockView.zl1_1).
Local Abbreviation B_pS := (@BlockView.pS pv).
Local Abbreviation B_ze_var := (§4§ BlockView.ze_var).
Local Abbreviation B_ze_lit := (§4§ BlockView.ze_lit).
Local Abbreviation B_ze_alu := (§4§ BlockView.ze_alu).
Local Abbreviation B_ze_aluw := (§4§ BlockView.ze_aluw).
Local Abbreviation B_ze_mul := (§4§ BlockView.ze_mul).
Local Abbreviation B_ze_ext := (§4§ BlockView.ze_ext).
Local Abbreviation B_ze_lbytes := (§4§ BlockView.ze_lbytes).
Local Abbreviation B_m64_small := (§5§ BlockView.m64_small).
Local Abbreviation B_bits_range := (@BlockView.bits_range segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_p := (@BlockView.ze_p segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_ze130 := (@BlockView.ze130 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze131 := (@BlockView.ze131 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze132 := (@BlockView.ze132 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze133 := (@BlockView.ze133 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze134 := (@BlockView.ze134 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze135 := (@BlockView.ze135 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze136 := (@BlockView.ze136 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_idx := (@BlockView.ze_idx segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_bits_decomp := (@BlockView.bits_decomp segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_last := (@BlockView.ze_last segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_maplen := (@BlockView.ze_maplen segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_sc := (@BlockView.ze_sc segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_land3072_mod := (§5§ BlockView.land3072_mod).
Local Abbreviation B_ze_bits3072 := (@BlockView.ze_bits3072 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_land3072_lo := (§5§ BlockView.land3072_lo).
Local Abbreviation B_land3072_hi := (§5§ BlockView.land3072_hi).
Local Abbreviation B_sz := (@BlockView.sz am).
Local Abbreviation B_ze_scsize := (@BlockView.ze_scsize segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Notation "§6§ h__" := (h__ segs C Hrc s L g am i fr vm m rho pv HMI Hfr) (at level 10, h__ global).
Local Abbreviation B_asserts_unpack := (§6§ BlockView.asserts_unpack).
Local Abbreviation B_pow2_i_range := (@BlockView.pow2_i_range segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_bit := (@BlockView.ze_bit segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_sx133 := (@BlockView.ze_sx133 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_sx134 := (@BlockView.ze_sx134 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ze_mem := (@BlockView.ze_mem segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_ze_memm16 := (@BlockView.ze_memm16 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_ze_area := (@BlockView.ze_area segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ZF_common := (@BlockView.ZF_common segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ZF_sized := (@BlockView.ZF_sized segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_ZF_direct := (@BlockView.ZF_direct segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ZF_nomap := (@BlockView.ZF_nomap segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ZF_map := (@BlockView.ZF_map segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_xv := (@BlockView.xv am).
Local Abbreviation B_ZF_all := (@BlockView.ZF_all segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_facts_hold := (@BlockView.facts_hold segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_addr_padd := (§5§ BlockView.addr_padd).
Local Abbreviation B_ZONES := (@BlockView.ZONES segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_own_win := (§2§ BlockView.own_win).
Local Abbreviation B_cell_own := (§2§ BlockView.cell_own).
Local Abbreviation B_cell_view := (@BlockView.cell_view segs C Hrc s L g am i fr vm m rho HMI).
Local Abbreviation B_ev1 := (§4§ BlockView.ev1).
Local Abbreviation B_ev1u := (§4§ BlockView.ev1u).
Local Abbreviation B_Z_to_bv64_mod := (§5§ BlockView.Z_to_bv64_mod).
Local Abbreviation B_ev_130 := (§4§ BlockView.ev_130).
Local Abbreviation B_ev_131 := (§4§ BlockView.ev_131).
Local Abbreviation B_ev_132 := (§4§ BlockView.ev_132).
Local Abbreviation B_ev_133 := (§4§ BlockView.ev_133).
Local Abbreviation B_ev_134 := (§4§ BlockView.ev_134).
Local Abbreviation B_ev_135 := (§4§ BlockView.ev_135).
Local Abbreviation B_ev_136 := (§5§ BlockView.ev_136).
Local Abbreviation B_ev_memm16 := (@BlockView.ev_memm16 segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_b_hdr := (@BlockView.b_hdr segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_b_grp := (@BlockView.b_grp segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_b_meta := (@BlockView.b_meta segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_b_area := (@BlockView.b_area segs C Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_b_ctx := (@BlockView.b_ctx segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_cov_hdr := (§6§ BlockView.cov_hdr).
Local Abbreviation B_cov_grp := (§6§ BlockView.cov_grp).
Local Abbreviation B_g_addrs := (§5§ BlockView.g_addrs).
Local Abbreviation B_cov_meta := (§6§ BlockView.cov_meta).
Local Notation "§7§ h__" := (h__ segs C Hrc s L g am i fr vm m rho pv HMI a k Harea) (at level 10, h__ global).
Local Abbreviation B_cov_area := (§7§ BlockView.cov_area).
Local Abbreviation B_cov_ctx := (§7§ BlockView.cov_ctx).
Local Abbreviation B_carv_hdr := (@BlockView.carv_hdr segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_carv_grp := (@BlockView.carv_grp segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_carv_meta := (@BlockView.carv_meta segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_carv_area := (@BlockView.carv_area segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_carv_ctx := (@BlockView.carv_ctx segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hpv a k Harea).
Local Abbreviation B_ranges := (@BlockView.ranges segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_blk_all := (@BlockView.blk_all segs C HSI Hrc s L g am i fr vm m rho pv HMI Hfr Hkind Hp Hpv a k Harea).
Local Abbreviation B_block_view := (@BlockView.block_view segs C HSI Hrc).

Local Notation rhoF := B_rho1.
Local Notation zr1 := (zr_of rhoF).
Local Notation zl1 := (zl_of rhoF).
Lemma rhoF_rm : ltac2:(tb__ "0|0|
S3cS107Q40A1SbS107Q8A1A1F_;S31S43VL;Vg;Vam;Vi;Vfr;Vrho;A6A1S31VrhoC;A1A3").
Proof using . unfold BlockView.rho1. rewrite bv_val_rm. unfold rho. apply rho_set_rw_rm. Qed.
Lemma rhoF_rl1 : ltac2:(tb__ "0|2|
S3cS9S107Q8M0A1M1A1S2bS43VL;Vg;Vam;Vi;Vfr;Vrho;A6S159A2S9cS41G1S106G0A1S123A4A3").
Proof using rhoC. unfold BlockView.rho1. apply bv_val_rl_1. Qed.
Lemma rhoF_rl_other : ltac2:(tb__ "0|0|
S42S40S3cS42R1S159A3A1S3cS9S107Q8A1A1S2bS43VL;Vg;Vam;Vi;Vfr;Vrho;A6R2A2S2bVrhoC;R2A2A3F_;Fl;").
Proof using . intros l Hl. unfold BlockView.rho1. rewrite bv_val_rl_other by exact Hl. unfold rho. rewrite rho_set_rw_rl. reflexivity. Qed.
Lemma rhoF_rw_low : ltac2:(tb__ "0|0|
S42S16aR1P82A2S3cS107Q40A1S25S43VL;Vg;Vam;Vi;Vfr;Vrho;A6R2A2S25VrhoC;R2A2A3F_;Fj;").
Proof using .
  intros j Hj. unfold BlockView.rho1. rewrite bv_val_rw_other; [| reflexivity | left; exact Hj].
  unfold rho. rewrite rho_set_rw_other by (intros ->; lia). reflexivity.
Qed.
Lemma rhoF_137 : ltac2:(tb__ "0|1|
S3cS107Q40M0A1S25S43VL;Vg;Vam;Vi;Vfr;Vrho;A6P89A2S106G0S6dA2A3").
Proof using rhoC. unfold BlockView.rho1. rewrite bv_val_rw_other; [| reflexivity | right; reflexivity]. unfold rho. apply rho_set_rw_at. Qed.

Lemma FFx : ltac2:(tb__ "0|0|
S167Vs;Vg;Vam;Vi;Vfr;A5"). Proof using HMI Hfr Hrc. exact B_FFx. Qed.
Lemma HMII : ltac2:(tb__ "0|0|
S168VC;S1ScfA1SaS5ScfS41A2A1S98S15fVs;VL;A2S147Vsegs;Vm;A2S148Vsegs;Vm;A2Vvm;A8"). Proof using HMI. exact (proj1 (proj1 (MInv_MInvI _ _ _ _ _) HMI)). Qed.
Definition zEnd : Z := ltac2:(tb__ "0|0|
S124VL;S118Vam;Vi;A2A2").
Lemma NUMS : ltac2:(tb__ "0|12|
S3dS4fZ0M0S6dA2S3dS3cS41S50S50S44VL;Vam;Vi;Vfr;A4M1S6fA2S6dA2S6eA3S3dS3cS41S6eS53S50S50S50S48VL;Vam;A2M2Z10M3A2S46Vam;Vi;A2M4A2M5S45Vam;A1M6A2Z4M7A2A3S3dS4fG3G6A2S3dS4fG0G4A2S3dS3dS4fG0SddVfr;A1M8A2S4fG8ZffM9A2A2S3dS3cS41S55G3S49Vam;Vi;Vfr;A3A2S50G4S55G3G8A2MaA2A3S3dS4fG0S6fA2S3dS3cS41G1S50G5GaA2A3S3dS3dS4fG0Vi;A2S4fVi;ScbVam;A1A2A2S3dS4fZ1000MbG2A2S3dS4fS50S6eG7A2S11bVL;A1McA2S3dS51GcS52Z2Z2fA2A2S3dS3cS41S4aVam;Vi;Vfr;A3MdS50Vi;S55Z20S57S6dZ5A2A2A2A3S3dS3dS4fG0GdA2S4fGdG9A2A2S3dS3dS4fGbS4eVL;Vg;A2MeA2S4fS50GeZ28A2GcA2A2S3dS3dS4fGbS4dVL;Va;A2MfA2S4fS50GfGbA2GcA2A2S3dS4fGbS11cVC;A1M10A2S3dS4fS50G10S92A2S120VC;A1M11A2S4fS50G11G3A2GcA2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using HMI HSI Harea Hfr Hkind Hrc rho.
  pose proof B_R_all as R. cbn zeta in R.
  destruct R as (Ri & Rl & Ro & Rn & Rfit & Rh16 & Rh16e & Rst & Rsti & Rml & Rav & Rfr & Rsc & RzP & Rrest).
  pose proof B_Hgrp as (rgm & _ & _ & _ & G1 & G2 & G3 & G4 & _). pose proof B_HzA as (A1 & A2 & _). pose proof B_Hctx as (X1 & X2 & X3 & X4).
  pose proof (ff_h16 _ _ _ _ _ FFx) as H16r. pose proof B_bits_range as BR.
  assert (E3 : B_h3 = i + 32 * Z.min rsv 5).
  { unfold BlockView.h3, hdr_byte3. rewrite Hkind. unfold rsv_code, rsv, reserved_of. destruct (5 <=? _) eqn:E5; [apply Z.leb_le in E5 | apply Z.leb_gt in E5]; lia. }
  assert (EE : zEnd = B_zMem + 16 + B_sti + B_st - 4).
  { unfold zEnd, BlockView.zMem, BlockView.sti, BlockView.st, addr_of, loc_addr, slot_end, slot_start. destruct (am_mem am); cbn [padd]. unfold UNIT, IB. lia. }
  top_ranges. unfold rsv, reserved_of, n, BlockView.n, BlockView.st, UNIT, IB, PGSZ, CTX_SIZE in *.
  repeat (split; [lia|]). lia.
Qed.

Variable ms : machine_state.
Hypothesis Hrom : rom_ok segs ms.

Lemma BV : ltac2:(tb__ "0|6|
S3dS9bS5S5S5S11S41A2S41A2S9S5S5S41S7A2S11A2A1A2M0S15aVsegs;S11bVL;A1S43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1Vm;A4S15dVC;S4bVpv;A1M2A2M3A3S3dS15eG1G3A2S3dS9bG0G0S30S15bG1R1A2S6S41S41S44VL;Vam;Vi;Vfr;A4M4S50G4S6fA2A4A2Ld;G3A3S3dS9bS10S28G1A1S15cG2S4cVam;A1A2A3S9bG0G0S41S3dS4fSdS41S41S15bG1R2A2M5A3R1A2S51R1SfS41S41G5A3A2A2S126VC;VL;Vs;R2A4F_;Fx;Ld;G3A3A2A2A2A2").
Proof using HMI HSI Harea Hfr Hkind HpC Hrc.
  pose proof B_blk_all as (_ & X1 & X2 & X3 & X4 & X5 & _). rewrite Hp in X3. change (BlockView.n fr) with n in X3.
  split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4 | exact X5].
Qed.

Lemma hold_of_carvable base lo hi cs : ltac2:(tb__ "0|3|
S4fS59S52Z2Z3eA2M0A1Vlo;A2S51Vhi;G0A2S15aVsegs;S11bVL;A1S43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1Vm;S6S5S5S11S41A2M2S41A2S9S5S5S41S7A2S11A2A1S6G2S41S6S11S41Vbase;Vlo;A4Vhi;A4Vcs;A4A5S20Vsegs;G1S109Vms;Vm;A2S149Vbase;Vlo;Vhi;Vcs;A4A4F_;F_;F_;").
Proof using Hrom rhoC.
  intros Hlo Hhi (H1 & H2 & H3 & H4 & H5 & Hins & Hview & Hcells).
  apply (obj_holds_frame_lit segs rhoF ms m base lo hi cs Hrom Hlo H2 Hhi H4); [|exact Hins | exact Hview | exact Hcells].
  top_ranges. lia.
Qed.

Lemma In5 {A0} (x1 x2 x3 x4 x5 : A0) P : ltac2:(tb__ "0|0|
S9bVA0;VP;S0VA0;Vx1;S0VA0;Vx2;S0VA0;Vx3;S0VA0;Vx4;S0VA0;Vx5;S1VA0;A1A3A3A3A3A3A3S3dVP;Vx1;A1S3dVP;Vx2;A1S3dVP;Vx3;A1S3dVP;Vx4;A1VP;Vx5;A1A2A2A2A2F_;").
Proof using HCc Harea Hrc. intros H. repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [? H] end. tauto. Qed.

Lemma hold_hdr : ltac2:(tb__ "0|0|
S20Vsegs;S43VL;Vg;Vam;Vi;Vfr;Vrho;A6S109Vms;Vm;A2SadS5fP82A1A1A4").
Proof using HCc HMI HSI Harea Hfr Hkind HpC Hrc Hrom.
  destruct (In5 _ _ _ _ _ _ (proj1 BV)) as (X & _).
  change (hdr_obj (v 130)) with (carved (SVar 12) (-4) 0 [(-4, 1%nat, SLit 0); (-3, 1%nat, SVar 130); (-2, 2%nat, SVar 131)]).
  apply hold_of_carvable; [lia | lia | exact X].
Qed.
Lemma hold_grp : ltac2:(tb__ "0|0|
S20Vsegs;S43VL;Vg;Vam;Vi;Vfr;Vrho;A6S109Vms;Vm;A2Sb2A4").
Proof using HCc HMI HSI Harea Hfr Hkind HpC Hrc Hrom.
  destruct (In5 _ _ _ _ _ _ (proj1 BV)) as (_ & X & _).
  change O_grp with (carved gm_mem_sv (-16) (-8) [(-16, 8%nat, SVar 132)]).
  apply hold_of_carvable; [lia | lia | exact X].
Qed.
Lemma hold_meta : ltac2:(tb__ "0|0|
S20Vsegs;S43VL;Vg;Vam;Vi;Vfr;Vrho;A6S109Vms;Vm;A2Sb4A4").
Proof using HCc HMI HSI Harea Hfr Hkind HpC Hrc Hrom.
  destruct (In5 _ _ _ _ _ _ (proj1 BV)) as (_ & _ & X & _).
  change O_meta with (carved (SVar 132) 16 40 [(16, 8%nat, memsv); (24, 4%nat, SVar 133); (28, 4%nat, SVar 134); (32, 8%nat, SVar 135)]).
  apply hold_of_carvable; [lia | lia | exact X].
Qed.
Lemma hold_area : ltac2:(tb__ "0|0|
S20Vsegs;S43VL;Vg;Vam;Vi;Vfr;Vrho;A6S109Vms;Vm;A2Sb1A4").
Proof using HCc HMI HSI Harea Hfr Hkind HpC Hrc Hrom.
  destruct (In5 _ _ _ _ _ _ (proj1 BV)) as (_ & _ & _ & X & _).
  change O_area with (carved (SAlu ALU_AND (SVar 132) (SLit MASK_PAGE)) 0 8 [(0, 8%nat, SVar 136)]).
  apply hold_of_carvable; [lia | lia | ]. unfold bv_area, bv_g, BlockViewIface.MASK_PAGE in X. unfold MASK_PAGE. exact X.
Qed.
Lemma hold_sec : ltac2:(tb__ "0|0|
S20Vsegs;S43VL;Vg;Vam;Vi;Vfr;Vrho;A6S109Vms;Vm;A2Sb6Vc;A1A4").
Proof using HCc HMI HSI Harea Hfr Hkind HpC Hrc Hrom.
  destruct (In5 _ _ _ _ _ _ (proj1 BV)) as (_ & _ & _ & _ & X).
  change (O_sec c) with (carved (SLit (ff_ctx (fs_ff c))) 0 8 [(0, 8%nat, SVar 136)]). rewrite (proj1 HCc).
  apply hold_of_carvable; [lia | lia | exact X].
Qed.

Lemma st_nums : ltac2:(tb__ "0|5|
S3dS4fZ1000M0S11dVC;A1M1A2S3dS4fS50G1Z1A2S120VC;A1M2A2S3dS4fG0S121VC;A1M3A2S3dS4fS50G3Z4A2G2A2S3dS4fS50G2Z10A2M4S11bVL;A1A2S4fG4Z7fff7f800000A2A2A2A2A2A2").
Proof using HSI.
  pose proof HSI as X. unfold statics_in_image in X. cbn beta zeta in X. unfold CTX_SIZE, PGSZ, UNIT, mc_need_locks in *.
  top_ranges. lia.
Qed.
Lemma hold_nl : ltac2:(tb__ "0|0|
S20Vsegs;S43VL;Vg;Vam;Vi;Vfr;Vrho;A6S109Vms;Vm;A2Sb5Vc;A1A4").
Proof using HCc HMI HSI Hrom NLW rhoC.
  pose proof st_nums as (N1 & N2 & N3 & N4 & N5 & N6).
  destruct (mig_statics HMII) as (NL & _). unfold MallocLayout.holds in NL. specialize (NL 0%nat ltac:(lia)). cbn [Z.of_nat] in NL. rewrite Z.add_0_r in NL.
  destruct (byteview_of_Some _ _ _ _ NL) as (_ & _ & b & Hb & Eb).
  change (O_nl c) with (carved (SLit (ff_libc (fs_ff c) + 3)) 0 1 [(0, 1%nat, SLit 0)]). rewrite (proj1 (proj2 HCc)).
  apply (obj_holds_frame_lit segs rhoF ms m (SLit (mc_need_locks C)) 0 1 [(0, 1%nat, SLit 0)] Hrom); cbn [eval]; rewrite ?u64_of_sum by lia; try lia.
  - constructor; [|constructor]. cbn. lia.
  - intros off Hoff. replace (mc_need_locks C + off) with (mc_need_locks C) by lia. split; [|eexists; exact Hb].
    unfold wok_of. destruct (m (Z_to_bv 64 (mc_need_locks C))); [reflexivity | exact NLW].
  - constructor; [|constructor]. intros j Hj. replace (mc_need_locks C + 0 + Z.of_nat j) with (mc_need_locks C) by lia. rewrite Hb.
    destruct j; [|lia]. cbn [nth enc_bytes]. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 b), <- Eb. reflexivity.
Qed.
Lemma hold_lock : ltac2:(tb__ "0|0|
S20Vsegs;S43VL;Vg;Vam;Vi;Vfr;Vrho;A6S109Vms;Vm;A2Sb3Vc;A1A4").
Proof using HCc HMI HSI Hrom rhoC.
  pose proof st_nums as (N1 & N2 & N3 & N4 & N5 & N6).
  destruct (mig_statics HMII) as (_ & _ & _ & LK & _). unfold MallocLayout.holds in LK.
  change (O_lock c) with (carved (SLit (ff_lockword (fs_ff c))) 0 4 [(0, 4%nat, SLit 0)]). rewrite (proj1 (proj2 (proj2 HCc))).
  apply (obj_holds_frame_lit segs rhoF ms m (SLit (mc_lock C)) 0 4 [(0, 4%nat, SLit 0)] Hrom); cbn [eval]; rewrite ?u64_of_sum by lia; try lia.
  - constructor; [|constructor]. cbn. lia.
  - intros off Hoff. replace off with (Z.of_nat (Z.to_nat off)) by lia.
    destruct (byteview_of_Some _ _ _ _ (LK (Z.to_nat off) ltac:(lia))) as (_ & W & b & Hb & _). split; [exact W | eexists; exact Hb].
  - constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    destruct (byteview_of_Some _ _ _ _ (LK j Hj)) as (_ & _ & b & Hb & Eb). rewrite Hb. f_equal. cbn [eval].
    rewrite nth_enc_bytes by lia. rewrite <- (Z_to_bv_bv_unsigned 8 b), <- Eb. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Ltac mlia := Z.to_euclidean_division_equations; lia.
Lemma zr1_137 : zr1 137%positive = rsv.
Proof using HMI HSI Harea Hfr Hkind Hrc rhoC. unfold zr_of. rewrite rhoF_137. pose proof NUMS as N. top_ranges. apply B_u64. lia. Qed.
Lemma ze137 : ltac2:(tb__ "0|1|
S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1S5fP89A1A3S6dA3").
Proof using HMI HSI Harea Hfr Hkind Hrc rhoC. unfold Mal_get_meta.v. rewrite B_ze_var, zr1_137. apply Z.mod_small. pose proof NUMS. top_ranges. lia. Qed.
Lemma ze12 : ltac2:(tb__ "0|1|
S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1S5fPcA1A3S44VL;Vam;Vi;Vfr;A4A3"). Proof using HMI Harea Hfr Hkind HpC Hrc. exact B_ze_p. Qed.
Lemma ze_ffidx : ltac2:(tb__ "0|1|
S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1SfaA3Vi;A3"). Proof using HMI Harea Hfr Hkind Hrc rhoC. exact B_ze_idx. Qed.
Lemma ze_code : ltac2:(tb__ "0|1|
S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1SefA3S57S6dZ5A2A3").
Proof using HMI HSI Harea Hfr Hkind Hrc rhoC.
  unfold ff_code, Mal_get_meta.v. rewrite B_ze_alu, B_ze130, B_ze_lit. cbn [zalu]. change (5 mod 2 ^ 64 mod 64) with 5.
  pose proof NUMS as (N0 & _ & _ & _ & _ & _ & _ & _ & _ & Ni & _ & _ & _ & E3 & R3 & _). rewrite E3.
  pose proof B_R_all as R. cbn zeta in R. destruct R as (_ & Rl & _).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. rewrite Z.mod_small by lia.
  destruct (Z_le_dec rsv 5); [rewrite Z.min_l by lia | rewrite Z.min_r by lia]; mlia.
Qed.
Lemma ze_mem16 : ltac2:(tb__ "0|1|
S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1ScaA3S48VL;Vam;A2A3"). Proof using HMI Harea Hfr Hkind HpC Hrc. exact B_ze_memm16. Qed.

Lemma st_class : ltac2:(tb__ "0|2|
S3eS3cS41SccVam;A1Z0M0A3S40S3cS41ScbVam;A1G0A3A1A2S3dS3dS4fG0SceVam;A1M1A2S51G1Z30A2A2S3cS41S45Vam;A1S55Z10S47Vam;A1A2A3A2F_;").
Proof using HMI Harea Hfr Hkind Hrc.
  intros Hk. pose proof B_R_all as R. cbn zeta in R. destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rsc & _).
  assert (Hsc : 0 <= am_sc am < 48) by (destruct Rsc as [H|(H1 & H2 & H3)]; [exact H | exfalso; lia]).
  split; [exact Hsc|]. unfold BlockView.st, stride_of, BlockView.sz, class_size, UNIT.
  destruct Hk as [E|NE]; [rewrite E; rewrite andb_false_r | replace (am_last am =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE)]; reflexivity.
Qed.
Lemma ze_S : ltac2:(tb__ "0|2|
S3eS3cS41SccVam;A1Z0M0A3S40S3cS41ScbVam;A1G0A3A1A2S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1A1S79G1A1Sf9A3S47Vam;A1A3F_;").
Proof using HMI Harea Hfr Hkind Hrc rhoC.
  intros Hk. destruct (st_class Hk) as [Hsc _].
  unfold ff_S, Mal_get_meta.v. rewrite B_ze_ext. cbn [Z.of_N]. rewrite B_ze_lbytes, B_ze_alu, B_ze_alu, B_ze135, !B_ze_lit. cbn [zalu].
  change (5 mod 2 ^ 64 mod 64) with 5. change (126 mod 2 ^ 64) with 126. change (Mal_get_meta.L_SIZECLASSES) with BlockViewIface.L_SIZECLASSES. rewrite B_zl1_1.
  pose proof B_bits_range as BR. pose proof B_bits_decomp as (M1 & M2 & M3 & _).
  rewrite (B_m64_small B_bits) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  rewrite (Z.mod_small (B_bits / 32)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  replace (B_bits / 32) with (1 + 2 * am_sc am + 128 * am_maplen am) by (unfold BlockView.bits, meta_bits; pose proof B_R_all as R; cbn zeta in R; mlia).
  rewrite land_126_odd by (pose proof B_R_all as R; cbn zeta in R; lia).
  rewrite table_u16 by lia. fold (BlockView.sz am). pose proof (znth_size_classes_range (am_sc am) Hsc).
  change (Z.of_N 16) with 16. unfold BlockView.sz in *. rewrite (Z.mod_small _ (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.
Lemma ze_stride : ltac2:(tb__ "0|2|
S3eS3cS41SccVam;A1Z0M0A3S40S3cS41ScbVam;A1G0A3A1A2S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1A1S79G1A1SfcA3S45Vam;A1A3F_;").
Proof using HMI Harea Hfr Hkind Hrc rhoC.
  intros Hk. destruct (st_class Hk) as [Hsc Est]. pose proof (znth_size_classes_range (am_sc am) Hsc). unfold BlockView.sz in *.
  unfold ff_stride. rewrite B_ze_alu, (ze_S Hk), B_ze_lit. cbn [zalu]. change (4 mod 2 ^ 64 mod 64) with 4.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. unfold BlockView.sz in *. rewrite Z.mod_small by lia. lia.
Qed.
Lemma ze_end : ltac2:(tb__ "0|2|
S3eS3cS41SccVam;A1Z0M0A3S40S3cS41ScbVam;A1G0A3A1A2S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1A1S79G1A1SedA3S6eA3F_;").
Proof using HMI HSI Harea Hfr Hkind HnC HpC Hrc.
  intros Hk. unfold ff_end. change (SAlu ALU_ADD gm_mem_sv (SLit (-16))) with memsv. rewrite !B_ze_alu.
  rewrite ze_mem16, (ze_stride Hk), B_ze_mul, (ze_stride Hk), ze_ffidx, B_ze_lit. cbn [zalu]. change (12 mod 2 ^ 64) with 12.
  pose proof NUMS as N. top_ranges. unfold BlockView.sti in *.
  rewrite (Z.mod_small (B_zMem + B_st)) by lia. rewrite (Z.mod_small (B_st * i)) by nia.
  rewrite (Z.mod_small (B_zMem + B_st + B_st * i)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma st_map : ltac2:(tb__ "0|2|
S3cS41ScbVam;A1Z0M0A3S51G0SccVam;A1M1A2S3dS3cS41S45Vam;A1S53S55G1Z1000A2Z10A2A3S3dS3cS41Vi;G0A3S3cS41S46Vam;Vi;A2G0A3A2A2F_;F_;").
Proof using HMI HSI Harea Hfr Hkind Hrc rho.
  intros Hl Hm. pose proof NUMS as N. assert (Ei : i = 0) by lia.
  unfold BlockView.sti, BlockView.st, stride_of. rewrite Hl, Ei.
  replace (am_maplen am =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Z.eqb andb negb]. unfold UNIT. split; [reflexivity|]. split; [reflexivity|]. lia.
Qed.
Lemma ze_strideM : ltac2:(tb__ "0|2|
S3cS41ScbVam;A1Z0M0A3S51G0SccVam;A1A2S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1A1S79G1A1SafA3S45Vam;A1A3F_;F_;").
Proof using HMI HSI Harea Hfr Hkind Hrc rhoC.
  intros Hl Hm. destruct (st_map Hl Hm) as (Est & _). pose proof B_bits_range as BR. pose proof NUMS as N.
  unfold strideM, Mal_get_meta.v. rewrite !B_ze_alu, B_ze135, !B_ze_lit. cbn [zalu].
  rewrite (Z.mod_small B_bits) by lia. replace ((18446744073709547520 mod 2 ^ 64) mod 2 ^ 64) with (2 ^ 64 - 2 ^ 12) by reflexivity.
  rewrite land_high_mask by lia. change (2 ^ 12) with 4096.
  assert (EB : B_bits - B_bits mod 4096 = am_maplen am * 4096).
  { unfold BlockView.bits, meta_bits. pose proof B_R_all as R. cbn zeta in R. mlia. }
  rewrite EB. change ((-16) mod 2 ^ 64) with (2 ^ 64 - 16). top_ranges. mlia.
Qed.
Lemma ze_endM : ltac2:(tb__ "0|2|
S3cS41ScbVam;A1Z0M0A3S51G0SccVam;A1A2S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1A1S79G1A1Sb7A3S6eA3F_;F_;").
Proof using HMI HSI Harea Hfr Hkind HpC Hrc.
  intros Hl Hm. destruct (st_map Hl Hm) as (Est & Ei & Esti). pose proof NUMS as N. top_ranges.
  unfold endM. rewrite !B_ze_alu, ze_mem16, (ze_strideM Hl Hm), B_ze_lit. cbn [zalu]. change (12 mod 2 ^ 64) with 12.
  rewrite (Z.mod_small (B_zMem + B_st)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition endX (x : fvar) : sv := ltac2:(tb__ "0|0|
S9eS11Lx;Vx;Sa1Se9Se2SedLw;Lr;Lk0;S9fSa0Sb7Lj;Lk0;X9ex2").
Definition kindok (x : fvar) : Prop := ltac2:(tb__ "0|5|
S9eOLx;Vx;Sa1Se9Se2Sa1OLk0;R3S3cS41SccVam;A1M0Z0M1A3S3dS51G1G0A2M2S40S3cS41ScbVam;A1G1A3M3A1A2Xa1x2Lw;Lr;Lk0;S9fSa0S9fOLk0;R2S3dG2S3dG3S51SceVam;A1M4Z30A2A2A2S3dG2S3dG3S3cS41G4Z3fA3A2A2X9fx2Lj;Lk0;X9ex2").
Lemma ze_endX x : ltac2:(tb__ "0|1|
S70Vx;A1S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1S76Vx;A1A3S6eA3F_;").
Proof using HMI HSI Harea Hfr Hkind HnC HpC Hrc. destruct x as [[|] r w | [|] j]; cbn [kindok endX]; intros K; [apply ze_end; left | apply ze_end; right | apply ze_endM | apply ze_endM]; lia. Qed.

Lemma HIF : ltac2:(tb__ "0|1|
S3dS9bS8aS94VL;S11fS147Vsegs;Vm;A2S148Vsegs;Vm;A2A2A2M0S8bVs;A1A3S9bS8aG0S117Vs;A1A3A2").
Proof using HMI. pose proof HMI as X. unfold MInv, reprO in X. cbn zeta in X. destruct X as (_ & _ & _ & ((_ & HI & _) & HF) & _). split; [exact HI | exact HF]. Qed.
Lemma cellIF cl : ltac2:(tb__ "0|0|
S3eSe1S8aVcl;S8bVs;A1A3Se1S8aVcl;S117Vs;A1A3A2S94VL;S11fS147Vsegs;Vm;A2S148Vsegs;Vm;A2A2Vcl;A3F_;").
Proof using HMI. intros [H|H]; [exact (proj1 (Forall_forall _ _) (proj1 HIF) cl H) | exact (proj1 (Forall_forall _ _) (proj2 HIF) cl H)]. Qed.
Lemma ownIF cl : ltac2:(tb__ "0|3|
S3eSe1S8aVcl;S8bVs;A1A3Se1S8aVcl;S117Vs;A1A3A2S41S3dS4fS8cVL;S8dVcl;A1A2M0R1A2S51R1S50G0S58S90Vcl;A1A1A2A2A2S3dS3cS3S148Vsegs;Vm;S106Q40M1R2A2A3S8A3S3fS107Q8A1M2G2S3cSbG2A1S147Vsegs;Vm;S106G1R3A2A3ScG2R1A2A3Lb;A2A2F_;Fx;F_;").
Proof using HMI Hrc. intros Hc x Hx. apply B_own_win. exact (cell_bytes_owned s L B_HW B_HLok cl Hc x Hx). Qed.

Definition cE : mcell := ltac2:(tb__ "0|0|
S8eS8fS118Vam;Vi;A2A1U1S91Z0A1A3").
Definition cPN : mcell := ltac2:(tb__ "0|0|
S8eS8fSd3S9aVam;Vi;Vfr;A3SdcVfr;A1A2A1U1S91Z0A1A3").
Definition cR : mcell := ltac2:(tb__ "0|0|
S8eS8fSd3S118Vam;Vi;A2N4A2A1U4S91S6dA1A3").
Definition cR5 : mcell := ltac2:(tb__ "0|0|
S8eS8fSd3S118Vam;Vi;A2N5A2A1U1S91Z0A1A3").
Lemma QC : ltac2:(tb__ "0|2|
S3dS3eSe1S8aS72S8bVs;A1A3Se1S8aS72S117Vs;A1M0A3A2S3dS51Z0S6dA2Se1S8aS73G0A3F_;S3dS4fZ5M1S6dA2Se1S8aS74G0A3F_;S51G1S6dA2Se1S8aS75G0A3F_;A2A2A2").
Proof using HMI Hfr Hkind Hrc.
  pose proof (quick_cells s g am i fr B_HW Hfr Hkind) as Q. cbn zeta in Q.
  destruct Q as (_ & _ & _ & _ & _ & _ & _ & _ & _ & QE & QP & QR & Q5). unfold cE, cPN, cR, cR5, rsv. auto.
Qed.
Lemma addr_cE : ltac2:(tb__ "0|0|
S3cS41S8cVL;S8dS72A1A2S6eA3"). Proof using . reflexivity. Qed.
Lemma addr_cPN : ltac2:(tb__ "0|0|
S3cS41S8cVL;S8dS73A1A2S53S6eS6dA2A3").
Proof using HMI HSI Harea Hfr Hkind Hrc rho. pose proof NUMS as (_ & E & _). cbn [cPN mc_loc]. fold (addr_of L (padd (frame_ptr am i fr) (fr_n fr))). rewrite B_addr_padd. fold (BlockView.p am i fr). fold B_zP. unfold n in E. lia. Qed.
Lemma addr_cR : ltac2:(tb__ "0|0|
S3cS41S8cVL;S8dS74A1A2S53S6eZ4A2A3").
Proof using g rho. cbn [cR mc_loc]. fold (addr_of L (padd (slot_end am i) (-4))). rewrite B_addr_padd. fold zEnd. lia. Qed.
Lemma addr_cR5 : ltac2:(tb__ "0|0|
S3cS41S8cVL;S8dS75A1A2S53S6eZ5A2A3").
Proof using g rho. cbn [cR5 mc_loc]. fold (addr_of L (padd (slot_end am i) (-5))). rewrite B_addr_padd. fold zEnd. lia. Qed.

Definition backed (off : Z) (w : nat) (val : sv) : Prop := ltac2:(tb__ "0|1|
S3fS8aS8aS3fS41S41S3dS3eSe1S8aR2S8bVs;A1A3Se1S8aR2S117Vs;A1A3A2S3dS3cSbS41A1S169VL;R2A2ScS41R1A2A3S3dS3cS7S90R2A1Vw;A3S3dS3cS41S8cVL;S8dR2A1A2Voff;A3S3cS107Q40M0A1S21S43VL;Vg;Vam;Vi;Vfr;Vrho;A6Vval;A2S106G0R1A2A3A2A2A2A2Lz;A2Lcl;A2").
Lemma G_Hng : ltac2:(tb__ "0|0|
Sd1S3cSbSd1A1SdfSdeVam;Vi;A2A1ScSd1R1A2A3S3cSd5Sd6R2A1Sd4A3F_;Ff;").
Proof using HMI Hfr Hkind Hrc. intros f Hf. rewrite (ff_slot _ _ _ _ _ FFx) in Hf. injection Hf as <-. exact Hkind. Qed.

Lemma tail_owned x : ltac2:(tb__ "0|0|
S3dS4fS50S44VL;Vam;Vi;Vfr;A4S6fA2Vx;A2S51Vx;S50S6eZ1A2A2A2S99VL;Vs;Vx;A3F_;").
Proof using HMI HSI Harea Hfr Hkind Hrc rho.
  intros Hx. pose proof NUMS as N.
  destruct (Z.eq_dec x zEnd) as [->|NE].
  { apply (cell_bytes_owned s L B_HW B_HLok cE (proj1 QC)). rewrite addr_cE. change (Z.of_nat (mc_w cE)) with 1. lia. }
  destruct (Zones.zone_in_footprint s L g am i B_HW (ff_used _ _ _ _ _ FFx) (ff_i _ _ _ _ _ FFx)) as (rg & Hrg & [I1 I2]).
  unfold zone_range, crange in I1, I2. cbn [fst snd] in I1, I2.
  change (loc_addr L (LMem (am_mem am))) with B_zMem in I1, I2. change (stride_of am) with B_st in I1, I2.
  unfold BlockView.sti, n in *. remember (B_st * i) as STI eqn:ESTI.
  split.
  - exists rg. split; [exact Hrg|]. unfold UNIT, IB in *. lia.
  - intros ([q k0] & Hb & Hxb). cbn [fst snd] in Hxb.
    destruct (zone_block_addr s L g am i B_HW B_HLok (ff_used _ _ _ _ _ FFx) (ff_i _ _ _ _ _ FFx) G_Hng q k0 Hb) as [(f & Hf & -> & ->) | D].
    + rewrite (ff_slot _ _ _ _ _ FFx) in Hf. injection Hf as <-. change (loc_addr L (LMem (frame_ptr am i fr))) with B_zP in Hxb. lia.
    + unfold ranges_disjoint, block_range, zone_range in D. cbn [fst snd] in D.
      change (loc_addr L (LMem (am_mem am))) with B_zMem in D. change (stride_of am) with B_st in D. rewrite <- ESTI in D. unfold UNIT, IB in *. lia.
Qed.

Lemma hold_win (e : sv) (d0 lo hi : Z) (cs : list (Z * nat * sv)) : ltac2:(tb__ "0|4|
S3cS41S108Q40S21S43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0Ve;A2A2S50S6eVd0;A2M1A3S4fS50S44VL;Vam;Vi;Vfr;A4S6fA2S50G1Vlo;A2A2S4fS50G1Vhi;A2S50S6eZ1A2A2S4fN8Vlo;A2S4fVlo;Vhi;A2S4fVhi;Z8A2S14aVlo;Vhi;Vcs;A3S9bS5S5S41S7A2M2S11A2M3G3G3OLt;R1G2S11G2OLp;R2S41S7S71S50G1R2A2R1R3A3Lw;Loff;X5x1Lval;Lp;X5x1Lt;Vcs;A3S20Vsegs;G0S109Vms;Vm;A2S149Ve;Vlo;Vhi;Vcs;A4A4F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using HMI HSI Harea Hfr Hkind Hrc Hrom.
  intros He Hd0 Hd1 Hlo Hlh Hhi Hins Hcells. pose proof NUMS as N. top_ranges.
  apply (obj_holds_frame_lit segs rhoF ms m e lo hi cs Hrom); rewrite ?He; [lia|lia|lia|lia|lia|exact Hins| |].
  - intros off Hoff. apply B_own_win. apply tail_owned. lia.
  - unfold cells_in_view. apply Forall_forall. intros [[off w] val] Hin.
    pose proof (proj1 (Forall_forall _ _) Hcells _ Hin) as (cl & z & Hc & Hz & Hw & Ha & Hv). cbn beta in *.
    pose proof (proj1 (Forall_forall _ _) Hins _ Hin) as (_ & _ & Hw8). cbn beta in Hw8.
    intros j Hj. exact (cell_in_view_of_image L (rd_of segs m) (wok_of segs m) cl z rhoF (zEnd + d0) off w val (cellIF cl Hc) Hz Hw ltac:(lia) ltac:(lia) Hv j Hj).
Qed.

Lemma ev0 : ltac2:(tb__ "0|2|
S3cS107Q40M0A1S21S43VL;Vg;Vam;Vi;Vfr;Vrho;A6S14Z0M1A1A2S106G0G1A2A3"). Proof using rhoC. reflexivity. Qed.
Lemma ev137 : ltac2:(tb__ "0|1|
S3cS107Q40M0A1S21S43VL;Vg;Vam;Vi;Vfr;Vrho;A6S5fP89A1A2S106G0S6dA2A3"). Proof using rhoC. exact rhoF_137. Qed.
Lemma ev5 : ltac2:(tb__ "0|2|
S3cS41S6dZ5M0A3S3cS107Q40M1A1S21S43VL;Vg;Vam;Vi;Vfr;Vrho;A6S14G0A1A2S106G1S6dA2A3F_;"). Proof using rhoC. intros ->. reflexivity. Qed.
Lemma bE : backed zEnd 1%nat (SLit 0).
Proof using HMI Hfr Hkind Hrc. exists cE, 0. pose proof QC as (Q & _). split; [exact Q|]. repeat split; reflexivity. Qed.
Lemma bPN : ltac2:(tb__ "0|1|
S51Z0M0S6dA2S71S53S6eS6dA2U1S14G0A1A3F_;").
Proof using HMI HSI Harea Hfr Hkind Hrc. intros H. exists cPN, 0. pose proof QC as (_ & Q & _). split; [right; exact (Q H)|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact addr_cPN | reflexivity]. Qed.
Lemma bR v : ltac2:(tb__ "0|1|
S4fZ5S6dA2S3cS107Q40M0A1S21S43VL;Vg;Vam;Vi;Vfr;Vrho;A6Vv;A2S106G0S6dA2A3S71S53S6eZ4A2U4Vv;A3F_;F_;").
Proof using HMI Hfr Hkind Hrc. intros H Hv. exists cR, rsv. pose proof QC as (_ & _ & Q & _). split; [right; exact (Q H)|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact addr_cR | exact Hv]. Qed.
Lemma bR5 : ltac2:(tb__ "0|1|
S4fZ5M0S6dA2S71S53S6eG0A2U1S14Z0A1A3F_;").
Proof using HMI HSI Harea Hfr Hkind Hrc.
  intros H. destruct (Z.eq_dec rsv 5) as [E|NE].
  - exists cPN, 0. pose proof QC as (_ & Q & _). split; [right; apply Q; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [rewrite addr_cPN; lia | reflexivity].
  - exists cR5, 0. pose proof QC as (_ & _ & _ & Q). split; [right; apply Q; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact addr_cR5 | reflexivity].
Qed.

Lemma covE x : ltac2:(tb__ "0|1|
S3cS41Vx;S6eA3S3fS8aS8aS3dS3eSe1S8aR1S8bVs;A1A3Se1S8aR1S117Vs;A1A3A2S3dS4fS8cVL;S8dR1A1A2M0Vx;A2S51Vx;S50G0S58S90R1A1A1A2A2A2A2Lcl;A2F_;").
Proof using HMI Hfr Hkind Hrc. intros ->. exists cE. pose proof QC as (Q & _). split; [exact Q|]. change (Z.of_nat (mc_w cE)) with 1. rewrite addr_cE. lia. Qed.
Lemma covPN x : ltac2:(tb__ "0|1|
S51Z0S6dA2S3cS41Vx;S53S6eS6dA2A3S3fS8aS8aS3dS3eSe1S8aR1S8bVs;A1A3Se1S8aR1S117Vs;A1A3A2S3dS4fS8cVL;S8dR1A1A2M0Vx;A2S51Vx;S50G0S58S90R1A1A1A2A2A2A2Lcl;A2F_;F_;").
Proof using HMI HSI Harea Hfr Hkind Hrc rho. intros H ->. exists cPN. pose proof QC as (_ & Q & _). split; [right; exact (Q H)|]. change (Z.of_nat (mc_w cPN)) with 1. rewrite addr_cPN. lia. Qed.
Lemma covR x : ltac2:(tb__ "0|2|
S4fZ5M0S6dA2S3dS4fS53S6eG0A2Vx;A2S51Vx;S6eA2A2S3fS8aS8aS3dS3eSe1S8aR1S8bVs;A1A3Se1S8aR1S117Vs;A1A3A2S3dS4fS8cVL;S8dR1A1A2M1Vx;A2S51Vx;S50G1S58S90R1A1A1A2A2A2A2Lcl;A2F_;F_;").
Proof using HMI HSI Harea Hfr Hkind Hrc rho.
  intros H Hx. destruct (Z.eq_dec x (zEnd - 5)) as [->|NE].
  - destruct (bR5 H) as (cl & z & Hc & _ & Hw & Ha & _). exists cl. split; [exact Hc|]. rewrite Ha, Hw. change (Z.of_nat 1) with 1. lia.
  - exists cR. pose proof QC as (_ & _ & Q & _). split; [right; exact (Q H)|]. change (Z.of_nat (mc_w cR)) with 4. rewrite addr_cR. lia.
Qed.

Definition rsv_ok_r (r : ff_rsv) : Prop := ltac2:(tb__ "0|0|
Se9OLr;Vr;S3cS41S6dZ0A3S3dS4fZ1S6dA2S4fS6dZ4A2A2S3cS41S6dZ5A3S4fZ6S6dA2Xe9x4").
Definition rsv_ok_j (j : rcode) : Prop := ltac2:(tb__ "0|1|
Sa0OLj;Vj;S3cS41S6dSa8Vj;A1A3M0G0G0G0G0S3cS41S6dZ5A3S4fZ6S6dA2Xa0x7").

Ltac cins := unfold cells_inside; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.
Ltac bcells := repeat (apply Forall_cons; [cbn beta iota|]); [..|apply Forall_nil].

Lemma ze_sub_code e : ltac2:(tb__ "0|2|
S3cS41S108Q40M0S21S43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1Ve;A2A2S6eA3S3cS3S7eVe;A1S8A3S3cS41S108G0S21G1S17S83Ve;SefA3A2A2S53S6eS57S6dZ5A2A2A3F_;F_;").
Proof using HMI HSI Harea Hfr Hkind Hrc rhoC.
  intros He Hs. pose proof NUMS as N. top_ranges. rewrite B_ev1u by (cbn; rewrite Hs; reflexivity). rewrite B_ze_alu, ze_code. rewrite <- (B_ev1u e Hs), He. cbn [zalu]. mlia.
Qed.
Lemma ze_sub_137 e : ltac2:(tb__ "0|2|
S3cS41S108Q40M0S21S43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1Ve;A2A2S6eA3S3cS3S7eVe;A1S8A3S3cS41S108G0S21G1S17S83Ve;S5fP89A1A3A2A2S53S6eS6dA2A3F_;F_;").
Proof using HMI HSI Harea Hfr Hkind Hrc rhoC.
  intros He Hs. pose proof NUMS as N. top_ranges. rewrite B_ev1u by (cbn; rewrite Hs; reflexivity). rewrite B_ze_alu, ze137. rewrite <- (B_ev1u e Hs), He. cbn [zalu]. mlia.
Qed.

Lemma hold_rsv (e : sv) (r : ff_rsv) : ltac2:(tb__ "0|1|
S3cS41S108Q40S21S43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0Ve;A2A2S6eA3S3cS3S7eVe;A1S8A3S78Vr;A1S9bS13S20Vsegs;G0S109Vms;Vm;A2A3SbaVe;Vr;A2A3F_;F_;F_;").
Proof using HMI HSI Harea Hfr Hkind Hrc Hrom rhoC.
  intros He Hs Hr. pose proof NUMS as N. destruct r; cbn [objs_rsv rsv_ok_r] in *.
  - apply Forall_cons; [|apply Forall_nil]. change (mkObj e (SLit 0) (SLit 1) [mkCell (SLit 0) 1 (SLit 0)] DUnknown) with (carved e 0 1 [(0, 1%nat, SLit 0)]).
    apply (hold_win e 0); [lia|lia|lia|lia|lia|lia|cins| bcells; rewrite Z.add_0_r, Z.add_0_r; exact bE].
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + change (mkObj (SAlu ALU_SUB e ff_code) (SLit 0) (SLit 1) [mkCell (SLit 0) 1 (SLit 0)] DUnknown) with (carved (SAlu ALU_SUB e ff_code) 0 1 [(0, 1%nat, SLit 0)]).
      apply (hold_win _ (- rsv)); [rewrite (ze_sub_code e He Hs); lia|lia|lia|lia|lia|lia|cins| bcells; replace (zEnd + - rsv + 0) with (zEnd - rsv) by lia; apply bPN; lia].
    + change (mkObj e (SLit 0) (SLit 1) [mkCell (SLit 0) 1 (SLit 0)] DUnknown) with (carved e 0 1 [(0, 1%nat, SLit 0)]).
      apply (hold_win e 0); [lia|lia|lia|lia|lia|lia|cins| bcells; rewrite Z.add_0_r, Z.add_0_r; exact bE].
  - apply Forall_cons; [|apply Forall_nil].
    change (mkObj e (SLit (-5)) (SLit 1) [mkCell (SLit (-5)) 1 (SLit 0); mkCell (SLit (-4)) 4 (SLit 5); mkCell (SLit 0) 1 (SLit 0)] DUnknown)
      with (carved e (-5) 1 [(-5, 1%nat, SLit 0); (-4, 4%nat, SLit 5); (0, 1%nat, SLit 0)]).
    apply (hold_win e 0); [lia|lia|lia|lia|lia|lia|cins|].
    bcells; rewrite Z.add_0_r; [replace (zEnd + -5) with (zEnd - 5) by lia; apply bR5; lia | replace (zEnd + -4) with (zEnd - 4) by lia; apply bR; [lia | apply ev5; exact Hr] | rewrite Z.add_0_r; exact bE].
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + change (mkObj e (SLit (-5)) (SLit 1) [mkCell (SLit (-5)) 1 (SLit 0); mkCell (SLit (-4)) 4 (v 137); mkCell (SLit 0) 1 (SLit 0)] DUnknown)
        with (carved e (-5) 1 [(-5, 1%nat, SLit 0); (-4, 4%nat, v 137); (0, 1%nat, SLit 0)]).
      apply (hold_win e 0); [lia|lia|lia|lia|lia|lia|cins|].
      bcells; rewrite Z.add_0_r; [replace (zEnd + -5) with (zEnd - 5) by lia; apply bR5; lia | replace (zEnd + -4) with (zEnd - 4) by lia; apply bR; [lia | exact ev137] | rewrite Z.add_0_r; exact bE].
    + change (mkObj (SAlu ALU_SUB e (v 137)) (SLit 0) (SLit 1) [mkCell (SLit 0) 1 (SLit 0)] DUnknown) with (carved (SAlu ALU_SUB e (v 137)) 0 1 [(0, 1%nat, SLit 0)]).
      apply (hold_win _ (- rsv)); [rewrite (ze_sub_137 e He Hs); lia|lia|lia|lia|lia|lia|cins| bcells; replace (zEnd + - rsv + 0) with (zEnd - rsv) by lia; apply bPN; lia].
Qed.
Lemma hold_rsvM (j : rcode) : ltac2:(tb__ "0|1|
S3cS41ScbVam;A1Z0M0A3S51G0SccVam;A1A2S77Vj;A1S9bS13S20Vsegs;S43VL;Vg;Vam;Vi;Vfr;Vrho;A6S109Vms;Vm;A2A3SbbVj;A1A3F_;F_;F_;").
Proof using HMI HSI Harea Hfr Hkind HpC Hrc Hrom.
  intros Hl Hm Hj. pose proof NUMS as N. pose proof (ze_endM Hl Hm) as ZE.
  assert (He : bv_unsigned (eval rhoF endM) = zEnd) by (rewrite B_ev1u by reflexivity; exact ZE).
  destruct j; cbn [objs_rsvM rsv_ok_j code_of] in *;
    first [ apply (hold_rsv endM R0 He eq_refl); cbn; lia
          | apply (hold_rsv endM R5E He eq_refl); cbn; lia
          | apply (hold_rsv endM R5G He eq_refl); cbn; lia
          | idtac ].
  all: apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  all: match goal with |- obj_holds _ _ _ (mkObj _ (SLit ?lo) (SLit ?hi) [mkCell _ _ _] _) =>
         change (obj_holds segs rhoF (with_mem ms m) (carved endM lo hi [(lo, 1%nat, SLit 0)])) end.
  all: apply (hold_win endM 0); [lia|lia|lia|lia|lia|lia|cins|].
  all: bcells; rewrite ?Z.add_0_r; first [exact bE | replace (zEnd + _) with (zEnd - rsv) by lia; apply bPN; lia].
Qed.

Lemma hold_hdrM : ltac2:(tb__ "0|0|
S3cS41ScbVam;A1Z0A3S20Vsegs;S43VL;Vg;Vam;Vi;Vfr;Vrho;A6S109Vms;Vm;A2SadS14S55Z20S57S6dZ5A2A2A1A1A4F_;").
Proof using HCc HMI HSI Harea Hfr Hkind HpC Hrc Hrom.
  intros Hl. pose proof NUMS as N. destruct (In5 _ _ _ _ _ _ (proj1 BV)) as (X & _).
  change (hdr_obj (SLit (32 * Z.min rsv 5))) with (carved (SVar 12) (-4) 0 [(-4, 1%nat, SLit 0); (-3, 1%nat, SLit (32 * Z.min rsv 5)); (-2, 2%nat, SVar 131)]).
  destruct X as (H1 & H2 & H3 & H4 & H5 & Hins & Hview & Hcells). unfold pv, pS in H4, H5, Hview, Hcells.
  apply (obj_holds_frame_lit segs rhoF ms m (SVar 12) (-4) 0 _ Hrom); [lia | lia | lia | exact H4 | lia | | exact Hview |].
  - unfold cells_inside. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
  - unfold cells_in_view in Hcells |- *.
    apply Forall_cons_iff in Hcells as [C1 Hcells]. apply Forall_cons_iff in Hcells as [C2 Hcells]. apply Forall_cons_iff in Hcells as [C3 _].
    apply Forall_cons; [exact C1|]. apply Forall_cons; [|apply Forall_cons; [exact C3 | apply Forall_nil]].
    cbn beta iota in C2 |- *. intros jj Hjj. rewrite (C2 jj Hjj). f_equal. f_equal. unfold bv_idxb. rewrite B_ev_130. cbn [eval]. f_equal.
    destruct N as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ni & _ & _ & _ & E3 & _). rewrite E3. replace (i + 32 * Z.min rsv 5) with (32 * Z.min rsv 5) by lia. reflexivity.
Qed.

Lemma carve_sct S tr md nx : ltac2:(tb__ "0|5|
S32Vsegs;S43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0VS;S6S9S163A1S161Vtr;S162Vms;Vmd;A2A4M1A4S3cS3S3bS1bS27VS;A1S2cVS;A1S34VS;A1S33VS;A1S37VS;A1S4S13S36VS;A1M2S0S13SacVc;A1S1S13A1A3A3S26VS;A1Vnx;S35VS;A1A9M3A1S8A3S9bS13S13S30S2fG0R1A2S6S41S41S11eVC;A1M4S50G4Z60A2A4A2Lo';G2A3S32Vsegs;G0G3G1A4F_;F_;F_;").
Proof using HCc HSI SCT rhoC.
  intros Hsm Hwf Hdisj. pose proof HSI as X. unfold statics_in_image in X. cbn beta zeta in X. unfold CTX_SIZE, PGSZ, UNIT in X. top_ranges.
  unfold O_sct in Hwf |- *. rewrite (proj2 (proj2 (proj2 HCc))) in Hwf |- *.
  apply (smatch_carve_rom segs rhoF S _ (mc_size_classes C) 96 Mal_get_meta.L_SIZECLASSES nx Hsm Hwf); [lia | lia | lia | | | exact Hdisj].
  - change Mal_get_meta.L_SIZECLASSES with BlockViewIface.L_SIZECLASSES. rewrite rhoF_rl1, length_map, size_classes_bytes_length. reflexivity.
  - intros kk Hk. change Mal_get_meta.L_SIZECLASSES with BlockViewIface.L_SIZECLASSES. rewrite rhoF_rl1. exact (SCT kk Hk).
Qed.

Ltac zfact := cbn [zholds zcond].

Hypothesis Hrsv32 : ltac2:(tb__ "0|0|
S3cS41SceVam;A1Z3fA3S51S6dS52Z2Z20A2A2F_;").
Lemma rsv_small : rsv < 2 ^ 32.
Proof using HMI HSI Harea Hfr Hkind Hrc Hrsv32 rho.
  pose proof (ff_ext _ _ _ _ _ FFx) as [X|X]; [|exact (Hrsv32 X)].
  pose proof NUMS as N. pose proof B_R_all as R. cbn zeta in R. clear HpC HnC. unfold rsv, reserved_of, BlockView.st, UNIT, IB in *. nia.
Qed.

Hypothesis HWIN : ltac2:(tb__ "0|0|
S9bS10S28VrhoC;A1Sa7A3").
Hypothesis HTP : ltac2:(tb__ "0|1|
S3dS4fZ1000S122VC;A1M0A2S3dS3cS41S5dG0Z4A2Z0A3S51G0S52Z2Z40A2A2A2A2").
Hypothesis Htp : ltac2:(tb__ "0|0|
S3cS41S108Q40S25VrhoC;P18A2A2S122VC;A1A3").
Lemma win_factsF : ltac2:(tb__ "0|0|
S9bS10S28S43VL;Vg;Vam;Vi;Vfr;Vrho;A6A1Sa7A3").
Proof using HWIN.
  pose proof HWIN as W. unfold F_win_facts, F_sp_aligned, F_sp_high, F_depth in W |- *. cbn [app] in W |- *.
  apply Forall_cons_iff in W as [W1 W]. apply Forall_cons_iff in W as [W2 W]. apply Forall_cons_iff in W as [W3 W]. apply Forall_cons_iff in W as [W4 _].
  cbn [SymState.holds eval] in W1, W2, W3, W4.
  constructor; [cbn [SymState.holds eval]; rewrite !rhoF_rw_low by reflexivity; exact W1|].
  constructor; [cbn [SymState.holds eval]; rewrite !rhoF_rw_low by reflexivity; exact W2|].
  constructor; [cbn [SymState.holds eval]; rewrite !rhoF_rw_low by reflexivity; exact W3|].
  constructor; [cbn [SymState.holds eval]; rewrite !rhoF_rw_low by reflexivity; exact W4|].
  constructor.
Qed.
Lemma tp_factsF : ltac2:(tb__ "0|0|
S9bS10S28S43VL;Vg;Vam;Vi;Vfr;Vrho;A6A1Sb0A3").
Proof using HTP Htp.
  pose proof HTP as (T1 & T2 & T3). unfold F_tp_facts.
  constructor; [cbn [SymState.holds eval]; rewrite rhoF_rw_low by reflexivity; rewrite Htp, (B_u64 4096) by lia; exact T1|].
  constructor; [cbn [SymState.holds eval]; rewrite rhoF_rw_low by reflexivity; rewrite Htp; split; [lia|]; change (2 ^ 2) with 4; exact T2|].
  constructor.
Qed.

Lemma ZF_p : ltac2:(tb__ "0|1|
S9bS10S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1A2SaeA3").
Proof using HMI HSI HTP Harea Hfr Hkind HpC Hrc.
  pose proof NUMS as N. unfold p_facts.
  constructor. { zfact. rewrite ze12, B_ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. lia. }
  constructor. { zfact. rewrite ze12, B_ze_lit. change (4096 mod 2 ^ 64) with 4096. lia. }
  constructor.
Qed.

Lemma ZF_align12 : ltac2:(tb__ "0|1|
S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1S1fPcZ4A2A3").
Proof using HMI HSI HTP Harea Hfr Hkind HpC Hrc.
  zfact. split; [lia|]. unfold zr_of. rewrite rhoF_rw_low by reflexivity. rewrite HpC.
  pose proof NUMS as N. rewrite (Z.mod_small B_zP (2 ^ 64)) by lia. change (2 ^ 4) with 16. exact B_HzP16.
Qed.
Lemma ZF_gm_common : ltac2:(tb__ "0|1|
S9bS10S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1A2S69A3").
Proof using HMI HSI HTP Harea Hfr Hkind HpC Hrc. constructor; [exact ZF_align12 | exact B_ZF_common]. Qed.
Lemma ZF_gm_sized : ltac2:(tb__ "0|2|
S3dS4fZ0SceVam;A1M0A2S51G0Z30A2A2S9bS10S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1A1S79G1A1A2S6bA3F_;").
Proof using HMI Harea Hfr Hkind HpC Hrc.
  intros Hsc. pose proof (B_ZF_sized Hsc) as X.
  apply Forall_cons_iff in X as [X1 X]. apply Forall_cons_iff in X as [_ X]. apply Forall_cons_iff in X as [X3 X]. apply Forall_cons_iff in X as [X4 _].
  constructor; [exact X1|]. constructor; [exact X3|]. constructor; [exact X4|]. constructor.
Qed.
Lemma ZF_gm_direct : ltac2:(tb__ "0|1|
S4fZ30SceVam;A1A2S9bS10S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1A2S61A3F_;").
Proof using HMI Harea Hfr Hkind Hrc rhoC.
  intros Hsc. pose proof (B_ZF_direct Hsc) as X.
  apply Forall_cons_iff in X as [X1 X]. apply Forall_cons_iff in X as [X2 _].
  constructor; [exact X1|]. constructor; [exact X2|]. constructor.
Qed.
Lemma ZF_gm_nomap : ltac2:(tb__ "0|1|
S3cS41SccVam;A1Z0A3S9bS10S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1A2S6aA3F_;").
Proof using HMI Harea Hfr Hkind Hrc rhoC. intros Hm. exact (B_ZF_nomap Hm). Qed.
Lemma ZF_gm_map : ltac2:(tb__ "0|1|
S51Z0SccVam;A1A2S9bS10S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1A2S62A3F_;").
Proof using HMI Harea Hfr Hkind Hrc rhoC. intros Hm. exact (B_ZF_map Hm). Qed.

Lemma ZF_idx94 : ltac2:(tb__ "0|2|
S3dS4fZ0SceVam;A1M0A2S51G0Z30A2A2S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1A1S79G1A1S1dS17S81S17S86S5fP87A1S14Z5A1A3S14Z7eA1A3S14Z5eA1A2A3F_;").
Proof using HMI HTP Harea Hfr Hkind Hrc rhoC.
  intros Hsc. zfact. unfold Mal_get_meta.v. rewrite B_ze_alu, B_ze_alu, B_ze135, !B_ze_lit. cbn [zalu].
  change (5 mod 2 ^ 64 mod 64) with 5. change (126 mod 2 ^ 64) with 126. change (94 mod 2 ^ 64) with 94.
  pose proof B_bits_range as BR. rewrite (B_m64_small B_bits) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  rewrite (Z.mod_small (B_bits / 32)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  replace (B_bits / 32) with (1 + 2 * am_sc am + 128 * am_maplen am) by (unfold BlockView.bits, meta_bits; pose proof B_R_all as R; cbn zeta in R; mlia).
  rewrite land_126_odd by (pose proof B_R_all as R; cbn zeta in R; lia). lia.
Qed.
Lemma lor_range : ltac2:(tb__ "0|1|
S3dS4fZ0S56Sd0Vam;A1ScdVam;A1A2M0A2S51G0S52Z2Z20A2A2A2").
Proof using HMI Harea Hfr Hkind Hrc. pose proof B_R_all as R. cbn zeta in R. apply lor_bound32; lia. Qed.
Lemma lor_bit_clear : ltac2:(tb__ "0|0|
S3cS3S5aS56Sd0Vam;A1ScdVam;A1A2Vi;A2S2A3").
Proof using HMI Hfr Hrc. rewrite Z.lor_spec, (ff_avail_i _ _ _ _ _ FFx), (ff_freed_i _ _ _ _ _ FFx). reflexivity. Qed.
Lemma lor_plus_bit : ltac2:(tb__ "0|1|
S51S50S56Sd0Vam;A1ScdVam;A1A2S52Z2M0Vi;A2A2S52G0Z20A2A2").
Proof using HMI Harea Hfr Hkind Hrc rho.
  pose proof B_R_all as R. cbn zeta in R. pose proof lor_range as LR. pose proof B_pow2_i_range as P.
  rewrite (lor_add_disjoint_bit _ i) by (try lia; apply lor_bit_clear).
  apply (lor_bound32 _ _ LR). lia.
Qed.
Lemma ze_mask : ltac2:(tb__ "0|1|
S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1SebA3S7dS56Sd0Vam;A1ScdVam;A1A2A1A3").
Proof using HMI Harea Hfr Hkind Hrc rhoC.
  unfold ff_mask, Mal_get_meta.v. rewrite B_ze_alu, B_ze_sx133, B_ze_sx134. cbn [zalu]. pose proof B_R_all as R. cbn zeta in R.
  pose proof (ZBits.sx32_range (am_avail am) ltac:(lia)). pose proof (ZBits.sx32_range (am_freed am) ltac:(lia)).
  rewrite !Z.mod_small by lia. apply sx32_lor; lia.
Qed.
Lemma ze_self : ltac2:(tb__ "0|1|
S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1SeeA3S7dS52Z2Vi;A2A1A3").
Proof using HMI Harea Hfr Hkind Hrc rhoC. exact B_ze_bit. Qed.
Lemma ZF_maskself : ltac2:(tb__ "0|1|
S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1S18S7fS17S81SebSeeA3S14Z0A1A3A3").
Proof using HMI HSI Harea Hfr Hkind Hrc rhoC.
  zfact. rewrite B_ze_alu, ze_mask, ze_self, B_ze_lit. cbn [zalu]. change (0 mod 2 ^ 64) with 0.
  pose proof lor_range as LR. pose proof B_pow2_i_range as P. pose proof NUMS as N.
  pose proof (ZBits.sx32_range _ LR). pose proof (ZBits.sx32_range (2 ^ i) ltac:(lia)).
  rewrite !Z.mod_small by lia. rewrite sx32_land by lia. rewrite land_pow2_testbit, lor_bit_clear by lia. reflexivity.
Qed.

Lemma sx32_1 : ltac2:(tb__ "0|0|
S3cS41Vi;Z0A3S3cS41Z1S7dS52Z2Vi;A2A1A3F_;").
Proof using Hfr HpC. intros ->. reflexivity. Qed.
Lemma ZF_and1 (e : sv) (x : Z) : ltac2:(tb__ "0|4|
S3cS41Vi;Z0M0A3S3dS4fG0Vx;A2S51Vx;S52Z2Z20A2A2A2S3cS3S5aVx;Vi;A2S2A3S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1A1M2S79G1A1M3Ve;A3S7dVx;A1A3S7bG2G3S18S7fS17S81Ve;S14Z1A1A3S14G0A1A3A3F_;F_;F_;F_;").
Proof using HMI HTP Harea Hfr Hkind HpC Hrc.
  intros Ei Hx Hb He. zfact. rewrite B_ze_alu, He, !B_ze_lit. cbn [zalu]. change (0 mod 2 ^ 64) with 0. change (1 mod 2 ^ 64) with 1.
  pose proof (ZBits.sx32_range _ Hx). pose proof B_pow2_i_range as P. pose proof (ZBits.sx32_range (2 ^ i) ltac:(lia)).
  rewrite (sx32_1 Ei). rewrite !Z.mod_small by lia. rewrite sx32_land by lia. rewrite land_pow2_testbit, Hb by lia. reflexivity.
Qed.
Lemma ZF_last0 : ltac2:(tb__ "0|2|
S3cS41ScbVam;A1Z0M0A3S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1A1S79G1A1S18S7fS17S81S5fP87A1S14Z1fA1A3S14G0A1A3A3F_;").
Proof using HMI Harea Hfr Hkind Hrc rhoC. intros Hl. zfact. change (SAlu ALU_AND (v 135) (SLit 31)) with bv_last. rewrite B_ze_last, B_ze_lit, Hl. reflexivity. Qed.
Lemma ZF_lastnz : ltac2:(tb__ "0|2|
S40S3cS41ScbVam;A1Z0M0A3A1S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1A1S79G1A1S1eS18S7fS17S81S5fP87A1S14Z1fA1A3S14G0A1A3A1A3F_;").
Proof using HMI Harea Hfr Hkind Hrc rhoC.
  intros Hl. zfact. change (SAlu ALU_AND (v 135) (SLit 31)) with bv_last. rewrite B_ze_last, B_ze_lit. change (0 mod 2 ^ 64) with 0.
  rewrite Z.eqb_eq. exact Hl.
Qed.
Lemma ZF_strideM : ltac2:(tb__ "0|4|
S3cS41ScbVam;A1Z0M0A3S51G0SccVam;A1A2S3dS7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1A1M2S79G1A1M3S1dS14Z20A1SafA2A3S7bG2G3S1dSafS14S52Z2Z3fA2A1A2A3A2F_;F_;").
Proof using HMI HSI HTP Harea Hfr Hkind Hrc rhoC.
  intros Hl Hm. destruct (st_map Hl Hm) as (Est & _). pose proof NUMS as N. top_ranges.
  split; zfact; rewrite (ze_strideM Hl Hm), B_ze_lit; [change (32 mod 2 ^ 64) with 32 | change (2 ^ 63 mod 2 ^ 64) with (2 ^ 63)]; lia.
Qed.
Lemma ZF_kmA1 : ltac2:(tb__ "0|2|
S3cS41ScbVam;A1Z0M0A3S51G0SccVam;A1A2S51SceVam;A1Z30A2S9bS10S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1A1S79G1A1A2S0S10S1eS18S87S14Z2fA1S63A3A1S0S10S1eS18S82S5fP83A1S64A3A1S1S10A1A3A3A3F_;F_;F_;").
Proof using HMI HSI HTP Harea Hfr Hkind Hrc Hrsv32 rhoC.
  intros Hl Hm Hsc. pose proof B_R_all as R. cbn zeta in R. assert (Hsc' : 0 <= am_sc am < 48) by lia.
  pose proof (proj1 B_asserts_unpack) as AU. destruct (am_sc am <? 48) eqn:E; [|apply Z.ltb_ge in E; lia]. destruct AU as [_ A2].
  destruct (st_map Hl Hm) as (_ & Ei & _). replace (B_sz * (i + 1)) with B_sz in A2 by (rewrite Ei; lia).
  constructor. { zfact. change gm_sc with bv_sc. rewrite B_ze_sc, B_ze_lit. change (47 mod 2 ^ 64) with 47. rewrite Z.ltb_lt. lia. }
  constructor. { zfact. change gm_scsize with bv_scsize. change (v 131) with (SVar 131). rewrite B_ze131, (B_ze_scsize Hsc').
                 rewrite Bool.negb_true_iff. intros X. apply Z.ltb_ge in X. unfold BlockView.sz in *. lia. }
  constructor.
Qed.

Lemma ZF_kc kx : ltac2:(tb__ "0|1|
S70Sa5Vkx;SecSe3A3A1S9bS10S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1A2Sb8Vkx;A1A3F_;").
Proof using HMI HSI HTP Harea Hfr Hkind HpC Hrc.
  intros K. pose proof B_R_all as R. cbn zeta in R.
  assert (Hk : am_maplen am = 0 \/ am_last am <> 0) by (destruct kx; cbn [kindok] in K; lia). destruct (st_class Hk) as [Hsc _].
  unfold kc_facts. apply Forall_app. split.
  - destruct kx; cbn [kindok] in K.
    + unfold gm_facts. apply Forall_app. split; [apply ZF_gm_common|]. apply Forall_app. split; [apply ZF_gm_sized; exact Hsc | apply ZF_gm_nomap; exact K].
    + apply Forall_app. split.
      * unfold gm_facts. apply Forall_app. split; [apply ZF_gm_common|]. apply Forall_app. split; [apply ZF_gm_sized; exact Hsc | apply ZF_gm_map; lia].
      * constructor; [apply ZF_lastnz; lia | constructor].
  - constructor; [apply ZF_idx94; exact Hsc|]. constructor; [apply ZF_maskself|]. constructor.
Qed.
Lemma ZF_km kx : ltac2:(tb__ "0|1|
S70Sa6Vkx;SabA2A1S9bS10S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1A2Sb9Vkx;A1A3F_;").
Proof using HMI HSI HTP Harea Hfr Hkind HpC Hrc Hrsv32.
  intros K. pose proof B_R_all as R. cbn zeta in R. pose proof NUMS as N.
  assert (Hl : am_last am = 0) by (destruct kx; cbn [kindok] in K; lia). assert (Hm : 0 < am_maplen am) by (destruct kx; cbn [kindok] in K; lia).
  destruct (st_map Hl Hm) as (Est & Ei & Esti). destruct (ZF_strideM Hl Hm) as [S1 S2].
  unfold km_facts. apply Forall_app. split; [|apply Forall_app; split; [apply ZF_gm_map; exact Hm|]].
  - constructor; [exact ZF_align12|].
    constructor. { zfact. change (v 131) with (SVar 131). rewrite B_ze131, B_ze_lit. change (65535 mod 2 ^ 64) with 65535. lia. }
    constructor; [apply ZF_last0; exact Hl|].
    constructor. { change (v 133) with (SVar 133). apply (ZF_and1 _ (am_avail am) Ei); [lia | exact (ff_avail_i _ _ _ _ _ FFx) | exact B_ze_sx133]. }
    constructor. { change (v 134) with (SVar 134). apply (ZF_and1 _ (am_freed am) Ei); [lia | exact (ff_freed_i _ _ _ _ _ FFx) | exact B_ze_sx134]. }
    constructor. { apply (ZF_and1 _ _ Ei lor_range lor_bit_clear ze_mask). }
    constructor; [exact S1|]. constructor; [exact S2|]. constructor.
  - destruct kx; cbn [kindok] in K; [apply ZF_kmA1; lia | apply ZF_gm_direct; lia].
Qed.

Lemma ze_en_minus_p (en : sv) : ltac2:(tb__ "0|3|
S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1M1S79G0A1M2Ven;A3S6eA3S3cS41S7cG1G2S17S83Ven;S5fPcA1A3A3S50S6fS6dA2A3F_;").
Proof using HMI HSI HTP Harea Hfr Hkind HpC Hrc. intros He. rewrite B_ze_alu, He, ze12. cbn [zalu]. pose proof NUMS as N. top_ranges. rewrite Z.mod_small by lia. lia. Qed.
Lemma rsv20 : ltac2:(tb__ "0|0|
S51SceVam;A1Z30A2S51S6dS52Z2Z14A2A2F_;").
Proof using HMI HSI HTP Harea Hfr Hkind Hrc Hrsv32 rho.
  intros Hsc. pose proof (ff_ext _ _ _ _ _ FFx) as [X|X]; [|lia].
  pose proof NUMS as N. pose proof B_R_all as R. cbn zeta in R. unfold rsv, reserved_of, BlockView.st, UNIT, IB in *. nia.
Qed.
Lemma ZF_rsv : ltac2:(tb__ "0|2|
S3eS3cS41SccVam;A1Z0M0A3S40S3cS41ScbVam;A1G0A3A1A2S9bS10S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1A1S79G1A1A2Sf0S14eS6dA1A1A3F_;").
Proof using HMI HSI HTP Harea Hfr Hkind HnC HpC Hrc Hrsv32.
  intros Hk. pose proof NUMS as N. pose proof NUMS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3 & _). pose proof B_R_all as R. cbn zeta in R.
  pose proof (ze_en_minus_p ff_end (ze_end Hk)) as EM. pose proof rsv_small as RS.
  unfold ff_facts_rsv, rsv_r. change (v 130) with (SVar 130).
  destruct (rsv =? 0) eqn:E0; [|destruct (rsv <=? 4) eqn:E5; [|destruct (rsv =? 5) eqn:E55]].
  - apply Z.eqb_eq in E0. rewrite E0 in E3. rewrite Z.min_l in E3 by lia.
    constructor. { zfact. rewrite B_ze130, B_ze_lit. change (31 mod 2 ^ 64) with 31. lia. }
    constructor. { zfact. rewrite EM, B_ze_lit. change (0 mod 2 ^ 64) with 0. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
    constructor.
  - apply Z.eqb_neq in E0. apply Z.leb_le in E5. rewrite Z.min_l in E3 by lia.
    constructor. { zfact. rewrite B_ze130, B_ze_lit. change (160 mod 2 ^ 64) with 160. apply Z.ltb_lt. lia. }
    constructor. { zfact. rewrite ze_code, B_ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.min_l by lia. rewrite Z.eqb_eq. lia. }
    constructor. { zfact. rewrite EM, ze_code. rewrite Z.min_l by lia. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
    constructor.
  - apply Z.leb_gt in E5. apply Z.eqb_eq in E55. rewrite Z.min_r in E3 by lia.
    constructor. { zfact. rewrite B_ze130, B_ze_lit. change (160 mod 2 ^ 64) with 160. rewrite Z.ltb_lt. lia. }
    constructor. { zfact. rewrite ze_code, B_ze_lit. change (5 mod 2 ^ 64) with 5. rewrite Z.min_r by lia. reflexivity. }
    constructor. { zfact. rewrite EM, B_ze_lit. change (5 mod 2 ^ 64) with 5. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
    constructor.
  - apply Z.leb_gt in E5. apply Z.eqb_neq in E55. rewrite Z.min_r in E3 by lia.
    constructor. { zfact. rewrite B_ze130, B_ze_lit. change (160 mod 2 ^ 64) with 160. rewrite Z.ltb_lt. lia. }
    constructor. { zfact. rewrite ze_code, B_ze_lit. change (5 mod 2 ^ 64) with 5. rewrite Z.min_r by lia. reflexivity. }
    constructor. { zfact. rewrite ze137, B_ze_lit. change (4294967295 mod 2 ^ 64) with 4294967295. lia. }
    constructor. { zfact. rewrite B_ze_lit, ze137. change (4 mod 2 ^ 64) with 4. apply Z.ltb_lt. lia. }
    constructor. { zfact. rewrite EM, ze137. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
    constructor.
Qed.
Lemma ZF_rsvM : ltac2:(tb__ "0|2|
S3cS41ScbVam;A1Z0M0A3S51G0SccVam;A1A2S9bS10S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M1A1S79G1A1A2SbcS14dS6dA1A1A3F_;F_;").
Proof using HMI HSI HTP Harea Hfr Hkind HpC Hrc Hrsv32.
  intros Hl Hm. pose proof NUMS as N. pose proof (ze_en_minus_p endM (ze_endM Hl Hm)) as EM. pose proof rsv_small as RS.
  unfold rsvM_facts, rsv_j.
  assert (GE : forall cz, 0 <= cz <= rsv -> zholds zr1 zl1 (SPBranch BC_GEU (SAlu ALU_SUB endM (v 12)) (SLit cz))).
  { intros cz Hcz. zfact. rewrite EM, B_ze_lit. rewrite Z.mod_small by lia. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  destruct (rsv =? 0) eqn:E0; [apply Z.eqb_eq in E0; constructor; [apply GE; cbn; lia | constructor]|]. apply Z.eqb_neq in E0.
  destruct (rsv =? 1) eqn:E1; [apply Z.eqb_eq in E1; constructor; [apply GE; cbn; lia | constructor]|]. apply Z.eqb_neq in E1.
  destruct (rsv =? 2) eqn:E2; [apply Z.eqb_eq in E2; constructor; [apply GE; cbn; lia | constructor]|]. apply Z.eqb_neq in E2.
  destruct (rsv =? 3) eqn:E3; [apply Z.eqb_eq in E3; constructor; [apply GE; cbn; lia | constructor]|]. apply Z.eqb_neq in E3.
  destruct (rsv =? 4) eqn:E4; [apply Z.eqb_eq in E4; constructor; [apply GE; cbn; lia | constructor]|]. apply Z.eqb_neq in E4.
  destruct (rsv =? 5) eqn:E5; [apply Z.eqb_eq in E5; constructor; [apply GE; cbn; lia | constructor]|]. apply Z.eqb_neq in E5.
  cbn [code_of].
  constructor. { zfact. rewrite ze137, B_ze_lit. change (4294967295 mod 2 ^ 64) with 4294967295. lia. }
  constructor. { zfact. rewrite B_ze_lit, ze137. change (4 mod 2 ^ 64) with 4. apply Z.ltb_lt. lia. }
  constructor. { zfact. rewrite EM, ze137. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor.
Qed.

Hypothesis Hslow : ltac2:(tb__ "0|1|
S3eS3cS41ScdVam;A1M0Z0A3S3cS41S50S56G0Sd0Vam;A1A2Sd7Vi;A1A2Sd8ScbVam;A1A1A3A2").
Lemma ze_maskself : ltac2:(tb__ "0|1|
S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1S24S80SebSeeA3A3S7dS50S56Sd0Vam;A1ScdVam;A1A2S52Z2Vi;A2A2A1A3").
Proof using HMI HTP Harea Hfr Hkind Hrc rhoC.
  rewrite B_ze_aluw, ze_mask, ze_self. cbn [zalu]. pose proof lor_range. pose proof B_pow2_i_range. pose proof lor_plus_bit.
  rewrite !sx32_mod32 by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ze_allmask : ltac2:(tb__ "0|3|
S3cS41S7cS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1S24S80S24S85S14Z2M1A1S5fP87A1A3S14ZffffffffffffffffA1A3A3S7dS53S52G1S50ScbVam;A1Z1M2A2A2G2A2A1A3").
Proof using HMI Harea Hfr Hkind Hrc rhoC.
  unfold Mal_get_meta.v. rewrite B_ze_aluw, B_ze_aluw, B_ze135, !B_ze_lit. cbn [zalu]. pose proof B_R_all as R. cbn zeta in R.
  pose proof B_bits_range as BR. pose proof B_bits_decomp as (M & _).
  change (2 mod 2 ^ 64 mod 2 ^ 32) with 2. change (18446744073709551615 mod 2 ^ 64 mod 2 ^ 32) with (2 ^ 32 - 1).
  replace (B_bits mod 2 ^ 32 mod 32) with (B_bits mod 32).
  2:{ rewrite <- (Znumtheory.Zmod_div_mod 32 (2 ^ 32) B_bits); [reflexivity|lia|lia|exists (2 ^ 27); reflexivity]. }
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
Lemma ZF_why : ltac2:(tb__ "0|1|
S9bS10S7bS7aS43VL;Vg;Vam;Vi;Vfr;Vrho;A6M0A1S79G0A1A2Se4S14cScdVam;A1A1A1A3").
Proof using HMI HTP Harea Hfr Hkind Hrc Hslow rhoC.
  pose proof B_R_all as R. cbn zeta in R. unfold fs_facts_why, why_w. change (v 134) with (SVar 134).
  destruct (am_freed am =? 0) eqn:E.
  - apply Z.eqb_eq in E. constructor; [|constructor]. zfact. rewrite B_ze_sx134, B_ze_lit, E. reflexivity.
  - apply Z.eqb_neq in E. destruct Hslow as [H0|Hall]; [lia|].
    constructor. { zfact. rewrite B_ze_sx134, B_ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. intros X. apply E. apply (sx32_zero_iff (am_freed am)); lia. }
    constructor. { zfact. rewrite ze_maskself, ze_allmask. rewrite Z.eqb_eq. f_equal. unfold bit, ones in Hall. rewrite Z.lor_comm. lia. }
    constructor.
Qed.
Lemma why_map : ltac2:(tb__ "0|0|
S3cS41ScbVam;A1Z0A3S3cSe2S14cScdVam;A1A1Se3A3F_;").
Proof using HMI HSI HTP Harea Hfr Hkind Hrc Hslow rho.
  intros Hl. unfold why_w. destruct Hslow as [H0|Hall]; [rewrite H0; reflexivity|].
  pose proof NUMS as N. assert (Ei : i = 0) by lia. rewrite Hl, Ei in Hall. unfold bit, ones in Hall. cbn in Hall.
  pose proof lor_range. rewrite Z.lor_comm in Hall. pose proof (Z.lor_nonneg (am_avail am) (am_freed am)).
  assert (Z : Z.lor (am_avail am) (am_freed am) = 0) by lia. apply Z.lor_eq_0_iff in Z as [_ Z]. rewrite Z. reflexivity.
Qed.

Lemma xof_cases : ltac2:(tb__ "0|1|
S3eS3fSa1Sa1S3dS3cS9eS14fVam;Vfr;A2M0Sa5R1S14eS6dA1S14cScdVam;A1A1A3A3S70Sa5R1SecSe3A3A1A2Lkx;A2S3fS9fS9fS3dS3cS9eG0Sa6R1S14dS6dA1A2A3S70Sa6R1SabA2A1A2Lkx;A2A2").
Proof using HMI HTP Harea Hfr Hkind Hrc.
  pose proof B_R_all as R. cbn zeta in R. unfold xof. change (reserved_of am fr) with rsv. cbn zeta.
  destruct (am_maplen am =? 0) eqn:Em; [apply Z.eqb_eq in Em; left; exists KC_A0; split; [reflexivity | exact Em]|apply Z.eqb_neq in Em].
  destruct (am_last am =? 0) eqn:El; [apply Z.eqb_eq in El|apply Z.eqb_neq in El]; cbn [negb].
  - right. destruct (am_sc am <? 48) eqn:Es; [apply Z.ltb_lt in Es; exists KM_A1 | apply Z.ltb_ge in Es; exists KM_B]; (split; [reflexivity | cbn [kindok]; lia]).
  - left. exists KC_A1. split; [reflexivity | cbn [kindok]; lia].
Qed.
Lemma psupp_facts x : forallb psupported (match x with FVC kx r w => p_facts ++ kc_facts kx ++ ff_facts_rsv r ++ fs_facts_why w
                                                    | FVM kx j => p_facts ++ km_facts kx ++ rsvM_facts j ++ fs_facts_why WF0 end) = true.
Proof using . destruct x as [[|] [| | |] [|] | [|] [| | | | | |]]; vm_compute; reflexivity. Qed.
Lemma D_call_facts_eq x : ltac2:(tb__ "0|1|
S3cS9S10A1M0S26Sa2Vc;Vx;A2A1S4S10Sa7S4S10Sb0S9eG0Lx;Vx;Sa1Se9Se2S4S10SaeS4S10Sb8R3A1S4S10Sf0R2A1Se4R1A1A3A3A3Lw;Lr;Lkx;S9fSa0S4S10SaeS4S10Sb9R2A1S4S10SbcR1A1Se4Se3A1A3A3A3Lj;Lkx;X9ex2A3A3A3").
Proof using . destruct x; reflexivity. Qed.
Theorem facts_D_call : ltac2:(tb__ "0|0|
S9bS10S28S43VL;Vg;Vam;Vi;Vfr;Vrho;A6A1S26Sa2Vc;S14fVam;Vfr;A2A2A1A3").
Proof using HMI HSI HTP HWIN Harea Hfr Hkind HnC HpC Hrc Hrsv32 Hslow Htp.
  destruct xof_cases as [(kx & EX & K)|(kx & EX & K)]; rewrite EX; rewrite D_call_facts_eq;
    (apply Forall_app; split; [apply win_factsF|]); (apply Forall_app; split; [apply tp_factsF|]).
  - apply Forall_holds_of_zholds; [exact (psupp_facts (FVC kx (rsv_r rsv) (why_w (am_freed am))))|].
    assert (Hk : am_maplen am = 0 \/ am_last am <> 0) by (destruct kx; cbn [kindok] in K; lia).
    apply Forall_app. split; [apply ZF_p|]. apply Forall_app. split; [exact (ZF_kc kx K)|]. apply Forall_app. split; [apply ZF_rsv; exact Hk | apply ZF_why].
  - apply Forall_holds_of_zholds; [exact (psupp_facts (FVM kx (rsv_j rsv)))|].
    assert (Hl : am_last am = 0 /\ 0 < am_maplen am) by (destruct kx; cbn [kindok] in K; lia).
    apply Forall_app. split; [apply ZF_p|]. apply Forall_app. split; [exact (ZF_km kx K)|]. apply Forall_app. split; [apply ZF_rsvM; lia|].
    rewrite <- (why_map (proj1 Hl)). apply ZF_why.
Qed.
End Inst.
End Mal_fslow_I.
