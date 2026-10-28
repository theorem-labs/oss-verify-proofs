(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "Zpos"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "True"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "eqb"; "modulo"; "mul"; "of_nat"; "sub"; "opp"; "testbit"; "to_nat"; "div"; "leb"; "lor"; "ltb"; "of_N"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "am_maplen"; "am_avail"; "am_freed"; "mslot"; "am_next"; "am_prev"; "ameta"; "am_mem"; "am_last"; "am_sc"; "st_free_meta_head"; "padd"; "MFree"; "frame"; "st_unmap_seq"; "stride_of"; "MUsed"; "ones"; "IB"; "bit"; "nth_slot"; "ss_fr"; "znth"; "FGroup"; "slot_start"; "st_bounces"; "st_seq"; "UNIT"; "am_aidx"; "class_size"; "find_frame_in"; "fkind"; "fr_kind"; "fr_n"; "fr_off"; "links_of"; "mkFrame"; "size_classes"; "ss_hdr"; "st_areas"; "st_metas"; "usage_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "cell"; "mkCell"; "rw"; "DUnknown"; "mkObj"; "obj_holds"; "SAlu"; "SPBranch"; "sprop"; "SPNot"; "eval"; "enc_bytes"; "SExt"; "SPAlign"; "SVar"; "SAluW"; "SPUle"; "rl"; "ro_addr"; "soff"; "DRom"; "c_off"; "c_val"; "c_width"; "image_byte"; "mkVal"; "ob_base"; "ob_cells"; "ob_dflt"; "obj_range"; "odefault"; "sobj"; "ss_facts"; "valuation"; "@Corelib.Init.Datatypes"; "Some"; "bool"; "option"; "pair"; "nat"; "cons"; "true"; "prod"; "nil"; "None"; "list"; "andb"; "false"; "length"; "snd"; "fst"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "zholds"; "zsupported"; "sx32"; "toS"; "zalu"; "zl_of"; "zr_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I.Inst"; "zr1"; "zl1"; "amPar"; "sc"; "iPar"; "ahQ"; "atQ"; "anQ"; "apQ"; "mask"; "zOff"; "useq_dw"; "zM"; "fmem"; "gPar"; "bits"; "zHb"; "frPar"; "tQ"; "zQ"; "fmQ"; "zH"; "zHp"; "zNm"; "zNx"; "zPv"; "zQm"; "ftQ"; "zF"; "zFn"; "zFp"; "zG"; "zHm"; "zHn"; "zNn"; "zNp"; "zPm"; "zPn"; "zPp"; "zQa"; "zTTn"; "zTTp"; "zTm"; "zTn"; "zTp"; "fmL"; "rho1"; "rw1"; "zS"; "flinks0"; "ftL"; "nQ"; "pQ"; "zA8"; "zB"; "zSec"; "zSeq"; "zU"; "e_parbase"; "e_parea"; "e_pmem"; "hQ"; "pm_idx"; "pm_last"; "pm_maplen"; "pm_sc"; "rl1"; "rw1v"; "useq_bytes"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "@Stdlib.Lists.List"; "In"; "forallb"; "last"; "existsb"; "nth_error"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "topL"; "addr_of"; "C_U"; "byteview_of"; "holds"; "mc_chk_guard"; "size_classes_bytes"; "statics_ok"; "vm_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "usedX"; "meta_bits"; "image"; "MCell"; "MT"; "LMem"; "active_hd"; "VZ"; "keys"; "le_byte"; "LCtx"; "loc_addr"; "mc_w"; "mc_loc"; "ring_ok"; "flinks"; "VP"; "memb"; "VSec"; "alinks"; "alloc_owned"; "allocated"; "optr"; "CTX_SIZE"; "CTX_bounces"; "CTX_free_meta_head"; "CTX_secret"; "CTX_seq"; "CTX_unmap_seq"; "CTX_usage"; "Inv"; "META_avail"; "META_bits"; "META_freed"; "META_mem"; "MTX"; "cell_holds"; "ctx_cells";
"group_cells"; "group_extent"; "group_ok"; "hdr_byte3"; "hdr_off16"; "layout"; "ly_ctx"; "ly_sec"; "meta_slot_cells"; "zseq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I"; "optrA"; "zl1"; "zr1"; "rho1"; "sc"; "udw"; "ubytes"; "zG"; "zA8"; "zNm"; "e_pmem"; "zB"; "zF"; "zH"; "zM"; "zQ"; "zQa"; "zQm"; "zU"; "ahQ"; "amPar"; "anQ"; "apQ"; "atQ"; "e_parbase"; "e_parea"; "fmQ"; "fmem"; "ftQ"; "gPar"; "hQ"; "nQ"; "pQ"; "tQ"; "useq_dw"; "zFp"; "zHp"; "zNx"; "zPv"; "zSec"; "zSeq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "wseg_addr"; "carved"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D.Inst"; "mkey"; "fkey"; "od"; "DS"; "flo"; "klo"; "dlo"; "dsxb"; "fcond"; "fptr"; "kbitsv"; "kmemv"; "kptr"; "krec"; "od_svs"; "sv_sem"; "dcells"; "dcond"; "dhi"; "fbase"; "kbase"; "useq_okb"; "FG"; "ds_checkb"; "dsz"; "kcond"; "obj_of"; "@Corelib.Lists.ListDef"; "nth"; "map"; "Forall"; "seq"; "repeat"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_ADD"; "ALU_SLL"; "ALU_SRL"; "BC_LTU"; "ALU_AND"; "aluop"; "ALU_SUB"; "BC_NE"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs"; "nt_sc"; "nt_maplen"; "nt_mask"; "nt_self"; "F_all"; "F_base"; "F_freeable"; "F_mask0"; "F_maskN0"; "F_notall"; "F_notall0"; "F_sc48"; "S_or"; "nt_all"; "nt_last"; "nt_sc8"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D"; "DS"; "dcells"; "dlo"; "obj_of"; "dhi"; "drom"; "od"; "OD_useqL"; "fcond"; "fkey"; "fptr"; "kcond"; "kptr"; "krec"; "mkey"; "sv_sem"; "useq_okb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@Corelib.Init.Nat"; "add"; "mul"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sv_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts"; "inring"; "mrec"; "mnext"; "mprev"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "below200"; "agrees"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib.Inst"; "e_actlo"; "O_metaK"; "e_acthi"; "O_act"; "O_fmh"; "O_got"; "O_guard"; "O_sct"; "O_seq"; "O_useq"; "free_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic.Inst"; "e_bnlo"; "e_uslo"; "e_bnhi"; "e_ushi"; "O_bnc"; "O_bptr"; "O_grp"; "O_parea"; "O_pbase"; "O_pmeta"; "O_secret"; "O_shdr"; "O_usage"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT"; "magree"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib"; "O_freeK"; "O_act"; "O_fmh"; "O_got"; "O_guard"; "O_metaK"; "O_sct"; "O_seq"; "O_useq"; "free_cells"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "reprO"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db.Inst"; "od_ok"; "od_ok_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic"; "O_bnc"; "O_bptr"; "O_grp"; "O_parea"; "O_pbase"; "O_pmeta"; "O_secret";
"O_shdr"; "O_usage"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_nt_I.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma size_classes_bytes_range : ltac2:(tb__ "0|0|
S156S0S0S5SaZ0R1A2ScR1Z100A2A2Lb;Sd7A3").
Proof.
  apply Forall_forall. intros b Hb.
  assert (H : forallb (fun b => (0 <=? b) && (b <? 256))%bool size_classes_bytes = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) H b Hb) as Hb'. apply andb_prop in Hb' as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma u64 : ltac2:(tb__ "0|1|
S0S5SaZ0R1A2ScR1SdZ2Z40A2A2A2S4S0Sd0Q40M0ScfG0R2A2A2R2A3F_;Fz;").
Proof. intros. apply u64_of_sum. assumption. Qed.

Lemma ceiling_small : ltac2:(tb__ "0|0|
S106ScSd1R1A1SdZ2Z2fA2A2FL0;").
Proof. intros L0. pose proof (topL_range L0). lia. Qed.

Lemma m64_small : ltac2:(tb__ "0|1|
S0SaZ0R1A2ScR2SdZ2Z40A2M0A2S4S0SfR3G0A2R3A3F_;F_;Fz;").
Proof. intros. apply Z.mod_small. lia. Qed.

Lemma ro_sct_P : ltac2:(tb__ "0|0|
S0S5SaZ0R1A2ScR1Z60A2A2S4S6bS5aSc8ScfQ40SbZ108ecR2A2A2A2S70A3F_;Fkk;").
Proof.
  intros kk Hk. exact (forall_range_dec (fun kk => ro_addr segsU (Z_to_bv 64 (0x108ec + kk))) 0 96 ltac:(vm_compute; reflexivity) kk ltac:(lia)).
Qed.

Definition ubytes (l : list Z) (j : nat) : list byte := ltac2:(tb__ "0|2|
S155S6eSceQ8M0A1S6eScfG0S154S0S188S189U8M1Vj;A2R1A2Vl;Z0A4A2Lk;S157U0G1A2A4").
Definition udw (l : list Z) (j : nat) : Z := bytes_le_to_Z (ubytes l j).
Lemma ubytes_len l j : ltac2:(tb__ "0|0|
S4S6eS77SceQ8A1S111Vl;Vj;A2A2U8A3"). Proof. unfold ubytes. rewrite length_map, length_seq. reflexivity. Qed.
Lemma udw_range l j : ltac2:(tb__ "0|1|
S5SaZ0S110Vl;Vj;A2M0A2ScG0SdZ2Z40A2A2A2").
Proof. unfold udw. pose proof (bytes_le_to_Z_bound (ubytes l j)) as B. rewrite ubytes_len in B. exact B. Qed.
Lemma udw_enc l j : ltac2:(tb__ "0|0|
S4S74SceQ8A1A1S53U8ScfQ40S110Vl;Vj;A2A2A2S111Vl;Vj;A2A3").
Proof. unfold udw. change (Z_to_bv 64 (bytes_le_to_Z (ubytes l j))) with (le_bytes_to_word (ubytes l j)). apply enc_bytes_le_word; [apply ubytes_len | lia]. Qed.
Lemma ubytes_zero j : ltac2:(tb__ "0|3|
S4S74SceQ8M0A1M1A1S111S158S0Z0M2U20A3Vj;A2S158G1ScfG0G2A2U8A3A3").
Proof.
  unfold ubytes. cbn [seq map]. rewrite !(nth_repeat 0). reflexivity.
Qed.
Lemma udw_zero j : udw (repeat 0 32) j = 0.
Proof. unfold udw. rewrite ubytes_zero. reflexivity. Qed.
Lemma le_byte_range z w k : ltac2:(tb__ "0|1|
S5SaZ0Se4Vz;Vw;Vk;A3M0A2ScG0Z100A2A2").
Proof. unfold le_byte. apply Z.mod_pos_bound. lia. Qed.
Lemma udw_byte l j t : ltac2:(tb__ "0|3|
S162Vt;U8M0A2S5SaZ0M1S154S0S188S189G0Vj;A2Vt;A2Vl;G1A4M2A2ScG2Z100A2A2S4S0Se4S110Vl;Vj;A2G0Vt;A3G2A3F_;F_;").
Proof.
  intros Ht Hb.
  pose proof (nth_enc_bytes 8 t (udw l j) Ht ltac:(lia)) as E. rewrite udw_enc in E. unfold ubytes in E.
  assert (E2 : nth t (map (fun k => Z_to_bv 8 (nth (8 * j + k) l 0)) (seq 0 8)) (Z_to_bv 8 0) = Z_to_bv 8 (nth (8 * j + t) l 0)).
  { destruct t as [|[|[|[|[|[|[|[|]]]]]]]]; try lia; cbn [map seq nth]; rewrite ?Nat.add_0_r; reflexivity. }
  rewrite E2 in E. pose proof (le_byte_range (udw l j) 8 t).
  apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 8) with 256 in E.
  rewrite !Z.mod_small in E by lia. symmetry. exact E.
Qed.

Definition optrA (L : layout) (o : option sptr) : Z := ltac2:(tb__ "0|0|
S6cS1bA1S0Lo;Vo;S1bSd2VL;R1A2Lq;Z0X6cx2").

Section Inst.
Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).

Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
S186Sd3VX;S6aS71S1bS0A2S6dS1bS0Vg;Vi;A4A2VU;S185Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Lemma HXr : xraw X s. Proof using HXz. exact (xzomb_xraw X s HXz). Qed.
Hypothesis Hu : ltac2:(tb__ "0|0|
SdbVX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Lemma HI : ltac2:(tb__ "0|0|
Sf9VX;S6aS71S1bS0A2S6dS1bS0Vg;Vi;A4A2VU;Vs;A4"). Proof using HMI. exact (mig_I HMI). Qed.
Lemma HL : layout_ok L s. Proof using HMI. exact (mig_layout HMI). Qed.
Lemma HV : ltac2:(tb__ "0|0|
Sd9VL;Vs;Vvm;A3"). Proof using HMI. exact (mig_vm HMI). Qed.
Lemma HLG : ledger_ok C_U vm. Proof using HMI. exact (mig_ledger HMI). Qed.
Lemma Hctx : ly_ctx L = 0x5a3d0. Proof using HMI. exact (mig_ctx HMI). Qed.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S4S0Sd0Q40S4aVrho;PcA2A2Sd2VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S4S0Sd0Q40S4aVrho;PdA2A2Vi;A3").

Definition zG : Z := addr_of L g.
Definition zM : Z := ltac2:(tb__ "0|0|
Sd2VL;S23Vam;A1A2").
Definition zPv : Z := ltac2:(tb__ "0|0|
S10bVL;S21Vam;A1A2").
Definition zNx : Z := ltac2:(tb__ "0|0|
S10bVL;S20Vam;A1A2").
Definition bits : Z := meta_bits am.
Definition mask : Z := ltac2:(tb__ "0|0|
S18S1dVam;A1S1eVam;A1A2").

Lemma G : ltac2:(tb__ "0|0|
S103VX;S6aS71S1bS0A2S6dS1bS0Vg;Vi;A4A2Vs;Vg;Vam;A5").
Proof using HMI Hu. exact (inv_groups HI g am Hu). Qed.
Lemma HMg_inst : ltac2:(tb__ "0|0|
S4S6cS1fA1SdfVs;Vg;A2S6aS1fS2cVam;A1A2A3").
Proof using Hu. exact (proj1 (usedX_MT _ _ _ _ Hu)). Qed.
Lemma g_key : In g (keys s).
Proof using Hu. eapply MT_Some_In_keys. exact HMg_inst. Qed.

Lemma Hres : ltac2:(tb__ "0|0|
S5S5SaZ0Vi;A2SaVi;S24Vam;A1A2A2S5S4S6cS29A1S31S30Vam;Vi;A2A1S73S29A1A3S4S6bSf0Vam;Vi;A2S70A3A2A2").
Proof using HMI Hu.
  destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & Hfr & Hal).
  pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->. auto.
Qed.

Lemma R_all : ltac2:(tb__ "0|d|
S5S5SaZ0M0Vi;A2SaVi;S24Vam;A1M1A2A2S5S5SaG0G1A2SaG1Z1fA2A2S5S5SaG0S38Vam;A1M2A2SaG2G1A2A2S5SaG0S1cVam;A1A2S5S5SaG0S1dVam;A1M3A2ScG3SdZ2M4Z20M5A2M6A2A2S5S5SaG0S1eVam;A1M7A2ScG7G6A2A2S5SaZ1000M8Sa1A2S5SaSbSa1Z28A2Sd1VL;A1M9A2S5S4S0SfSa1Z8A2G0A3S5SaG8S8eA2S5SaSbSbS8eZ10MaA2S10S2bVam;A1MbSbG1Z1A2A2A2G9A2S5S4S0SfS8eGaA2G0A3S5ScG9SdG4Z2fA2A2S5S9S4S0S25Vam;A1McZ3fA3S5SaG0GcA2ScGcZ30A2A2A2S5SaGaGbA2SaSbS8eG5A2G9A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using HMI Hgd Hu.
  pose proof Hres as (Ri & _ & _).
  pose proof (used_ranges X (Some (g, i)) U s HI g am Hu) as (A1 & A2 & A3 & A4 & A5).
  pose proof (used_addrs X (Some (g, i)) U s HI C_U L vm HL HV HLG g am Hu) as (B1 & B2 & B3 & _ & B5 & B6 & B7 & _).
  pose proof (ceiling_small L). pose proof (stride_pos _ _ _ _ _ G) as SP.
  assert (SC : am_sc am = 63 \/ 0 <= am_sc am < 48).
  { pose proof G as (_ & _ & _ & Gcl & _). destruct Gcl as [(C & _) | (C & _)]; [left | right]; exact C. }
  assert (PR : 16 <= stride_of am * (am_last am + 1)) by nia.
  unfold zG, zM, PGSZ, META_SIZE, UNIT in *. repeat match goal with |- _ /\ _ => split end; try lia.
Qed.

Lemma Hbits : ltac2:(tb__ "0|0|
S4S0S91SbSbSbS24Vam;A1Z20A2S10Z40S25Vam;A1A2A2S10Z1000S1cVam;A1A2A2A3").
Proof using . reflexivity. Qed.

Definition zS : Z := ltac2:(tb__ "0|0|
Sd2VL;S34Vam;Vi;A2A2").
Lemma zS_eq : ltac2:(tb__ "0|0|
S4S0Sb2SbSbS8eZ10A2S10S2bVam;A1Vi;A2A2A3").
Proof using Hgd. unfold zS, zM, slot_start, addr_of, loc_addr. destruct (am_mem am); cbn [padd]. unfold UNIT. lia. Qed.
Lemma zS_range : ltac2:(tb__ "0|1|
S5SaSbS8eZ10A2Sb2A2S5SaS12SbSb2S2bVam;A1M0A2S2eA2SbSbS8eS102Vam;A1A2S2eA2A2SaZ0S10G0Vi;A2A2A2A2").
Proof using HMI Hgd Hu.
  rewrite zS_eq. pose proof R_all as R. assert (0 <= stride_of am * i) by nia.
  assert (stride_of am * (i + 1) <= stride_of am * (am_last am + 1)) by nia. unfold group_extent, UNIT, IB. lia.
Qed.

Lemma maplen_range : ltac2:(tb__ "0|1|
S5SaZ0S1cVam;A1M0A2ScG0SdZ2Z23A2A2A2").
Proof using HMI Hgd Hu.
  pose proof R_all as R. pose proof G as (_ & _ & _ & _ & Gmp & _).
  destruct (Z_lt_dec 0 (am_maplen am)) as [Hpos|]; [|lia].
  destruct (Gmp Hpos) as (r & rg & Em & Hr & Hk & Hl & Hlen & Hfit & _).
  pose proof (footprint_region_In s _ _ Hr Hk Hl) as InR.
  pose proof (fp_mem_range C_U L s vm _ _ HV HLG InR ltac:(unfold PGSZ in *; lia)) as (M1 & M2 & _).
  unfold PGSZ in *. lia.
Qed.

Lemma bits_range : 0 <= bits < 2 ^ 48.
Proof using HMI Hgd Hu. rewrite Hbits. pose proof R_all. pose proof maplen_range. lia. Qed.

Lemma optr_range : ltac2:(tb__ "0|2|
S6cS1bA1M0S1bS4G0R2S6aS1bR1A2A3S6S22S22SdbVX;Vs;R3R1A4La';A2F_;Fq;S5SaZ0S10bVL;R2A2M1A2SaSbG1Z28A2Sd1VL;A1A2A2F_;Fo;").
Proof using HMI Hgd.
  intros [q|] Hq; cbn [optrA]; [|pose proof (ceiling_small L); top_ranges; lia].
  destruct (Hq q eq_refl) as (a' & Hu'). pose proof (used_addrs X (Some (g, i)) U s HI C_U L vm HL HV HLG q a' Hu') as (B1 & B2 & _).
  unfold PGSZ, META_SIZE in *. lia.
Qed.

Lemma linked_ring : ltac2:(tb__ "0|5|
S9S7S4S6cS1bA1M0S21Vam;A1S73S1bA1M1A3A1S7S4G0S20Vam;A1G1A3A1A2S6S0S0S6S1bS1bS6S74S1bA1M2G2S5S5SaZ0R3A2ScR3Z30A2A2S5S4S0S25Vam;A1R3A3S5S4G0Se1Vs;R3A2S6aS1bR2A2M3A3S5Se9SeeVX;Vs;R3A3G3S6fS1bR2R1A3M4A3Sc9S1bVg;G4A3A2A2A2A2Lrest;A2Lm0;A2Lsc;A2F_;").
Proof using HMI Hgd Hu.
  intros Hl. pose proof R_all as R. destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
  destruct (inv_rings HI) as (_ & A & D).
  destruct SC as [H63 | Hsc].
  - exfalso. destruct (D g am Hu H63) as [P N]. destruct Hl as [Hl|Hl]; [exact (Hl P) | exact (Hl N)].
  - destruct (A (am_sc am) Hsc) as (ms & Rg & Mem & _).
    assert (Hin : In g ms).
    { apply (Mem g am Hu eq_refl). destruct (am_prev am), (am_next am); try discriminate. destruct Hl as [Hl|Hl]; exfalso; apply Hl; reflexivity. }
    destruct ms as [|m0 rest]; [destruct Hin|].
    exists (am_sc am), m0, rest. pose proof Rg as [_ Hhd]. cbn in Hhd.
    split; [exact Hsc|]. split; [reflexivity|]. split; [exact Hhd|]. split; [rewrite <- Hhd; exact Rg | exact Hin].
Qed.

Lemma prev_used : ltac2:(tb__ "0|0|
S1bS4S6cS1bA1S21Vam;A1S6aS1bR1A2A3S6S22S22SdbVX;Vs;R3R1A4La';A2F_;Fq;").
Proof using HMI Hgd Hu.
  intros q Hq. destruct (linked_ring ltac:(left; rewrite Hq; discriminate)) as (sc & m0 & rest & Hsc & Esc & Hhd & Rg & Hin).
  pose proof (ring_step X s sc m0 rest g Rg Hin) as (_ & _ & Hp).
  unfold mprev, mrec in Hp. rewrite (proj1 (usedX_MT _ _ _ _ Hu)), Hq in Hp.
  destruct (ring_members_used _ _ _ _ _ _ Rg Hp) as (a' & Hu' & _). exists a'. exact Hu'.
Qed.

Lemma next_used : ltac2:(tb__ "0|0|
S1bS4S6cS1bA1S20Vam;A1S6aS1bR1A2A3S6S22S22SdbVX;Vs;R3R1A4La';A2F_;Fq;").
Proof using HMI Hgd Hu.
  intros q Hq. destruct (linked_ring ltac:(right; rewrite Hq; discriminate)) as (sc & m0 & rest & Hsc & Esc & Hhd & Rg & Hin).
  pose proof (ring_step X s sc m0 rest g Rg Hin) as (_ & Hn & _).
  unfold mnext, mrec in Hn. rewrite (proj1 (usedX_MT _ _ _ _ Hu)), Hq in Hn.
  destruct (ring_members_used _ _ _ _ _ _ Rg Hn) as (a' & Hu' & _). exists a'. exact Hu'.
Qed.

Lemma zPv_range : ltac2:(tb__ "0|0|
S5SaZ0S9bA2SaSbS9bZ28A2Sd1VL;A1A2A2").
Proof using HMI Hgd Hu. unfold zPv. apply optr_range. exact prev_used. Qed.
Lemma zNx_range : ltac2:(tb__ "0|0|
S5SaZ0S9aA2SaSbS9aZ28A2Sd1VL;A1A2A2").
Proof using HMI Hgd Hu. unfold zNx. apply optr_range. exact next_used. Qed.

Definition sc : Z := am_sc am.
Definition hQ : sptr := ltac2:(tb__ "0|0|
S6cS1bA1S1bLx;Se1Vs;S85A2S1bR1Lh;Vg;X6cx2").
Definition ahQ : ameta := mrec s hQ.
Definition tQ : sptr := mprev s hQ.
Definition atQ : ameta := mrec s tQ.
Definition zH : Z := ltac2:(tb__ "0|0|
S10bVL;Se1Vs;S85A2A2").
Definition zHp : Z := ltac2:(tb__ "0|0|
S10bVL;S21S87A1A2").
Definition zHn : Z := ltac2:(tb__ "0|0|
S10bVL;S20S87A1A2").
Definition zTp : Z := ltac2:(tb__ "0|0|
S10bVL;S21S88A1A2").
Definition zTn : Z := ltac2:(tb__ "0|0|
S10bVL;S20S88A1A2").
Definition zHm : Z := ltac2:(tb__ "0|0|
Sd2VL;S23S87A1A2").
Definition zTm : Z := ltac2:(tb__ "0|0|
Sd2VL;S23S88A1A2").

Section QueueRing.
  Hypothesis Hsc : 0 <= sc < 48.
  Variable h : sptr.
  Hypothesis Hhd : ltac2:(tb__ "0|0|
S4S6cS1bA1Se1Vs;S85A2S6aS1bVh;A2A3").
  Lemma hQ_eq : hQ = h. Proof using Hhd. unfold hQ. rewrite Hhd. reflexivity. Qed.
  Lemma h_inring : ltac2:(tb__ "0|0|
S18bVX;Vs;S85Vh;Vh;A5"). Proof using . apply inring_m0. Qed.
  Lemma h_used : ltac2:(tb__ "0|0|
S5SdbVX;Vs;Vh;S87A4S5S4S0S25S87A1S85A3S4S6cS1fA1SdfVs;Vh;A2S6aS1fS2cS87A1A2A3A2A2").
  Proof using HMI Hhd Hsc. destruct (inring_used X (Some (g, i)) U s sc h HI Hsc Hhd h h_inring) as (a & Hu' & Hs & M & Er). unfold ahQ. rewrite hQ_eq, Er. auto. Qed.
  Lemma t_inring : ltac2:(tb__ "0|0|
S18bVX;Vs;S85Vh;S94A5"). Proof using Hhd. unfold tQ. rewrite hQ_eq. apply (inring_prev X s sc h). apply inring_m0. Qed.
  Lemma t_used : ltac2:(tb__ "0|0|
S5SdbVX;Vs;S94S88A4S5S4S0S25S88A1S85A3S4S6cS1fA1SdfVs;S94A2S6aS1fS2cS88A1A2A3A2A2").
  Proof using HMI Hhd Hsc. destruct (inring_used X (Some (g, i)) U s sc h HI Hsc Hhd tQ t_inring) as (a & Hu' & Hs & M & Er). unfold atQ. rewrite Er. auto. Qed.

  Lemma h_prev : ltac2:(tb__ "0|0|
S4S6cS1bA1S21S87A1S6aS1bS94A2A3").
  Proof using HMI Hhd Hsc.
    destruct (ring_ex X (Some (g, i)) U s sc h HI Hsc Hhd) as [rest Rg].
    destruct (ring_head_links X s sc h ahQ (h :: rest) Rg (proj1 h_used)) as (rest' & E & Hp & Hn).
    unfold tQ, mprev. rewrite hQ_eq. unfold ahQ in Hp |- *. rewrite hQ_eq in Hp |- *. rewrite Hp. reflexivity.
  Qed.
  Lemma zH_eq : ltac2:(tb__ "0|0|
S4S0S97Sd2VL;Vh;A2A3"). Proof using Hhd. unfold zH. rewrite Hhd. reflexivity. Qed.
  Lemma zHp_eq : ltac2:(tb__ "0|0|
S4S0S98Sd2VL;S94A2A3"). Proof using HMI Hhd Hsc. unfold zHp. rewrite h_prev. reflexivity. Qed.

  Hypothesis Hp0 : am_prev am = None.
  Hypothesis Hn0 : am_next am = None.
  Lemma g_not_inring q : ltac2:(tb__ "0|0|
S18bVX;Vs;S85Vh;Vq;A5S7S4S1bVq;Vg;A3A1F_;").
  Proof using HMI Hhd Hn0 Hp0 Hsc Hu.
    intros Hq ->. destruct (inv_rings HI) as (_ & A & _). destruct (A sc Hsc) as (ms & Rg & Mem & _).
    rewrite Hhd in Rg. destruct (ring_head_In _ _ _ Rg) as [_ [rest ->]].
    pose proof (Hq rest Rg) as Hin. apply (proj1 (Mem g am Hu eq_refl)) in Hin. apply Hin. rewrite Hp0, Hn0. reflexivity.
  Qed.
  Lemma h_ne_g : h <> g. Proof using HMI Hhd Hn0 Hp0 Hsc Hu. exact (g_not_inring h h_inring). Qed.
  Lemma t_ne_g : tQ <> g. Proof using HMI Hhd Hn0 Hp0 Hsc Hu. exact (g_not_inring tQ t_inring). Qed.
End QueueRing.

Lemma zH_range : ltac2:(tb__ "0|0|
S5SaZ0S97A2SaSbS97Z28A2Sd1VL;A1A2A2").
Proof using HMI Hgd Hu.
  unfold zH. destruct (active_hd s sc) as [h|] eqn:E; cbn [optrA]; [|pose proof (ceiling_small L); top_ranges; lia].
  pose proof R_all as R. destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
  destruct (Z_lt_dec sc 48).
  - destruct (h_used ltac:(unfold sc in *; lia) h E) as (Hu' & _). pose proof (used_addrs X (Some (g, i)) U s HI C_U L vm HL HV HLG h _ Hu') as (B1 & B2 & _). unfold PGSZ, META_SIZE in *. lia.
  - exfalso. pose proof (proj1 (inv_ctx HI)) as Hlen. unfold active_hd in E. rewrite nth_overflow in E; [discriminate|]. rewrite Hlen. unfold sc in *. lia.
Qed.
Lemma optr_used_range o : ltac2:(tb__ "0|1|
S1bS4S6cS1bA1Vo;S6aS1bR1A2A3S6S22S22SdbVX;Vs;R3R1A4La';A2F_;Fq;S5SaZ0S10bVL;Vo;A2M0A2SaSbG0Z28A2Sd1VL;A1A2A2F_;").
Proof using HMI Hgd. exact (optr_range o). Qed.

Definition flinks0 (x : option mslot) : option sptr * option sptr := ltac2:(tb__ "0|4|
S6cS1fA1S71S6cS1bA1M0G0A2M1Lx;Vx;S1fS1fG1Lm;R1G0G0S6dG0G0R2R1A4Lnx;Lpr;S6dG0G0S73S1bA1M2G2A4M3S22G3Lm0;X1fx3Lm;G3X6cx2").
Definition fmQ : sptr := ltac2:(tb__ "0|0|
S6cS1bA1S1bLx;S26Vs;A1S1bR1Lf;Vg;X6cx2").
Definition fmL : option sptr * option sptr := ltac2:(tb__ "0|0|
Sb3SdfVs;S96A2A1").
Definition ftQ : sptr := ltac2:(tb__ "0|1|
S6cS1bA1M0S1bLx;S79G0G0SafA3S1bR1Lt;S96X6cx2").
Definition ftL : option sptr * option sptr := ltac2:(tb__ "0|0|
Sb3SdfVs;S9dA2A1").
Definition zF : Z := ltac2:(tb__ "0|0|
S10bVL;S26Vs;A1A2").
Definition zFp : Z := optrA L (fst fmL).
Definition zFn : Z := optrA L (snd fmL).
Definition zTTp : Z := optrA L (fst ftL).
Definition zTTn : Z := optrA L (snd ftL).

Definition zSeq : Z := st_seq s.

Lemma Hctx_ok : ctx_ok s. Proof using HMI. exact (inv_ctx HI). Qed.
Lemma seq_range : 0 <= zSeq <= 255. Proof using HMI. pose proof Hctx_ok as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma useq_len : length (st_unmap_seq s) = 32%nat. Proof using HMI. exact (proj1 (proj2 (proj2 Hctx_ok))). Qed.
Lemma useq_byte k : ltac2:(tb__ "0|2|
S5SaZ0M0S154S0Vk;S2aVs;A1G0A4M1A2SaG1ZffA2A2").
Proof using HMI Hgd.
  pose proof Hctx_ok as (_ & _ & _ & _ & _ & H & _).
  destruct (Nat.lt_ge_cases k (length (st_unmap_seq s))) as [Hk|Hk]; [apply H; apply nth_In; exact Hk|]. rewrite nth_overflow by exact Hk. lia.
Qed.

Lemma free_ring : ltac2:(tb__ "0|2|
S6S74S1bA1M0G0S5Se9SeaVX;Vs;A2S26Vs;A1R1A3S1bS6cS1bA1M1G1S4S6cS1fA1SfeVX;Vs;R3A3S6aS1fS28R2R1A2A2A3Sc9S1bR4R5A3F_;Fnx;Fpr;Fq;A2Lms;A2").
Proof using HMI. exact (proj1 (inv_rings HI)). Qed.
Lemma flinks_MT q pr nx : ltac2:(tb__ "0|2|
S4S6cS71S6cS1bA1M0G0A2M1A1SeaVX;Vs;Vq;A3S6aG1S6dG0G0Vpr;Vnx;A4A2A3S5S4S6cS1fA1SdfVs;Vq;A2S6aS1fS28Vpr;Vnx;A2A2A3S4S6bSecVq;VX;A2S76A3A2F_;").
Proof using .
  unfold flinks, MTX. intros H. destruct (memb q X) eqn:Em; [discriminate|]. destruct (MT s q) as [[p n| |a]|]; try discriminate.
  injection H as -> ->. auto.
Qed.

Lemma last_in_cons {A} (l : list A) (d : A) : ltac2:(tb__ "0|0|
Sc9VA;ScbVA;Vl;Vd;A3S6fVA;Vd;Vl;A3A3").
Proof using .
  revert d. induction l as [|x t IH]; intros d; [left; reflexivity|].
  destruct t as [|y t']; [right; left; reflexivity|].
  change (last (x :: y :: t') d) with (last (y :: t') d). pose proof (IH d) as H. destruct H as [H|H]; [left; exact H | right; right; exact H].
Qed.
Lemma last_hd_in {A} (m0 : A) rest : ltac2:(tb__ "0|1|
Sc9VA;ScbVA;S6fVA;Vm0;Vrest;A3M0Vm0;A3G0A3").
Proof using . destruct rest as [|x t]; [left; reflexivity|]. change (last (m0 :: x :: t) m0) with (last (x :: t) m0). apply last_in_cons. Qed.
Lemma fring_member ms q : ltac2:(tb__ "0|0|
Se9SeaVX;Vs;A2S26Vs;A1Vms;A3Sc9S1bVq;Vms;A3S6S1bS1bS6S1bS1bS5S4S6cS1fA1SdfVs;Vq;A2S6aS1fS28S6aS1bR2A2S6aS1bR1A2A2A2A3S5Sc9S1bR2Vms;A3S5Sc9S1bR1Vms;A3S5Sc9S1bVq;Se3Vs;A1A3S5S7S4S1bVq;Vg;A3A1S4S6bSecVq;VX;A2S76A3A2A2A2A2A2Lnx;A2Lpr;A2F_;F_;").
Proof using Hu.
  intros Rg Hin. destruct (ring_links _ _ _ _ Rg Hin) as (pr & nx & HLk).
  pose proof Rg as [[Hnd Hch] Hhd]. destruct ms as [|m0 rest] eqn:Ems; [destruct Hin|]. cbn [cycle_ok] in Hch.
  destruct (chain_next _ _ _ _ _ _ _ Hch Hin HLk) as (l1 & l2 & El & Enx & Epr). injection Enx as ->. injection Epr as ->.
  destruct (flinks_MT q _ _ HLk) as [M Em]. exists (last l1 (last (m0 :: rest) m0)), (hd m0 l2). split; [exact M|].
  split.
  { pose proof (last_in_cons l1 (last (m0 :: rest) m0)) as H1. destruct H1 as [H1|H1].
    - rewrite <- H1. apply last_hd_in.
    - assert (HH : forall y, In y l1 -> In y (m0 :: rest)) by (intros y Hy; rewrite El; apply in_app_iff; left; exact Hy). apply HH. exact H1. }
  split.
  { destruct l2 as [|y t]; [left; reflexivity|]. rewrite El. apply in_app_iff. right. right. left. reflexivity. }
  split; [eapply MT_Some_In_keys; exact M|]. split; [intros ->; rewrite HMg_inst in M; discriminate | exact Em].
Qed.

Definition fmem (q : sptr) : Prop := ltac2:(tb__ "0|1|
S6S74S1bA1M0G0S5Se9SeaVX;Vs;A2S26Vs;A1R1A3Sc9S1bVq;R1A3A2Lms;A2").
Lemma fmem_facts q : ltac2:(tb__ "0|0|
S8fVq;A1S6S1bS1bS6S1bS1bS5S4S6cS1fA1SdfVs;Vq;A2S6aS1fS28S6aS1bR2A2S6aS1bR1A2A2A2A3S5S8fR2A1S5S8fR1A1S5Sc9S1bVq;Se3Vs;A1A3S5S7S4S1bVq;Vg;A3A1S4S6bSecVq;VX;A2S76A3A2A2A2A2A2Lnx;A2Lpr;A2F_;").
Proof using Hu.
  intros (ms & Rg & Hin). destruct (fring_member ms q Rg Hin) as (pr & nx & M & Hp & Hn & K & NE & Em).
  exists pr, nx. split; [exact M|]. split; [exists ms; auto|]. split; [exists ms; auto|]. auto.
Qed.
Lemma fmem_head fm : ltac2:(tb__ "0|0|
S4S6cS1bA1S26Vs;A1S6aS1bVfm;A2A3S8fVfm;A1F_;").
Proof using HMI.
  intros Hfh. destruct free_ring as (ms & Rg & _). exists ms. split; [exact Rg|]. rewrite Hfh in Rg. exact (proj1 (ring_head_In _ _ _ Rg)).
Qed.

Lemma fmL_cases : ltac2:(tb__ "0|c|
S9S5S4S6cS1bA1M0S26Vs;A1M1S73S1bA1M2A3S5S4S1bS96Vg;A3S5S4S71G0G0A2M3SafS6dG0G0G2G2A4M4A3S5S4S1bS9dVg;A3S4G3Sb4G4A3A2A2A2A2S6S1bS1bS6S1bS1bS6S1bS1bS5S4G0G1S6aS1bR3A2A3S5S4S1bS96R3A3S5S8fR3A1S5S4S6cS1fA1M5SdfVs;R3A2S6aS1fS28S6aS1bR2A2M6S6aS1bR1A2M7A2A2M8A3S5S4G3SafS6dG0G0G6G7A4M9A3S5S8fR2A1MaS5S8fR1A1MbS5S4S1bS9dR2A3S6S1bS1bS6S1bS1bS5S4G5SdfVs;R4A2G8A3S5S4G3Sb4G9A3S5GaGbA2A2A2Lnx2;A2Lpr2;A2A2A2A2A2A2A2A2A2Lnx;A2Lpr;A2Lfm;A2A2").
Proof using HMI Hu.
  unfold ftL, ftQ, fmL, fmQ. destruct (st_free_meta_head s) as [fm|] eqn:Efh.
  - right. pose proof (fmem_head fm Efh) as Hfm. destruct (fmem_facts fm Hfm) as (pr & nx & M & Hpr & Hnx & _).
    destruct (fmem_facts pr Hpr) as (pr2 & nx2 & M2 & Hpr2 & Hnx2 & _).
    exists fm, pr, nx. rewrite M. cbn [flinks0 fst]. rewrite M2. cbn [flinks0].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hfm|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact Hpr|]. split; [exact Hnx|]. split; [reflexivity|]. exists pr2, nx2. auto.
  - left. rewrite HMg_inst. cbn [flinks0 fst]. rewrite HMg_inst. cbn [flinks0]. auto.
Qed.
Lemma key_range40 q : ltac2:(tb__ "0|1|
Sc9S1bVq;Se3Vs;A1A3S5SaZ1000Sd2VL;Vq;A2M0A2SaSbG0Z28A2Sd1VL;A1A2A2F_;").
Proof using HMI Hgd.
  intros Hq. pose proof (key_range X (Some (g, i)) U s L HI HL C_U vm q Hq HV HLG) as (K1 & K2 & _). unfold META_SIZE, PGSZ in *. lia.
Qed.
Lemma fmem_range q : ltac2:(tb__ "0|1|
S8fVq;A1S5SaZ1000Sd2VL;Vq;A2M0A2SaSbG0Z28A2Sd1VL;A1A2A2F_;").
Proof using HMI Hgd Hu. intros Hq. destruct (fmem_facts q Hq) as (_ & _ & _ & _ & _ & K & _). apply key_range40. exact K. Qed.
Lemma optr_fmem_range o : ltac2:(tb__ "0|1|
S1bS4S6cS1bA1Vo;S6aS1bR1A2A3S8fR2A1F_;Fq;S5SaZ0S10bVL;Vo;A2M0A2SaSbG0Z28A2Sd1VL;A1A2A2F_;").
Proof using HMI Hgd Hu.
  intros Ho. destruct o as [q|]; cbn [optrA].
  - pose proof (fmem_range q (Ho q eq_refl)). lia.
  - pose proof (ceiling_small L). top_ranges; lia.
Qed.
Lemma zF_range : ltac2:(tb__ "0|0|
S5SaZ0S9eA2SaSbS9eZ28A2Sd1VL;A1A2A2").
Proof using HMI Hgd Hu. unfold zF. apply optr_fmem_range. intros q Hq. exact (fmem_head q Hq). Qed.
Lemma zFp_range : ltac2:(tb__ "0|0|
S5SaZ0Sa0A2SaSbSa0Z28A2Sd1VL;A1A2A2").
Proof using HMI Hgd Hu.
  unfold zFp. apply optr_fmem_range. intros q Hq.
  destruct fmL_cases as [(_ & _ & E & _) | (fm & pr & nx & _ & _ & _ & _ & E & Hpr & _)]; rewrite E in Hq; cbn in Hq; [discriminate|]. injection Hq as <-. exact Hpr.
Qed.
Lemma zFn_range : ltac2:(tb__ "0|0|
S5SaZ0S9fA2SaSbS9fZ28A2Sd1VL;A1A2A2").
Proof using HMI Hgd Hu.
  unfold zFn. apply optr_fmem_range. intros q Hq.
  destruct fmL_cases as [(_ & _ & E & _) | (fm & pr & nx & _ & _ & _ & _ & E & _ & Hnx & _)]; rewrite E in Hq; cbn in Hq; [discriminate|]. injection Hq as <-. exact Hnx.
Qed.
Lemma zTTp_range : ltac2:(tb__ "0|0|
S5SaZ0SabA2SaSbSabZ28A2Sd1VL;A1A2A2").
Proof using HMI Hgd Hu.
  unfold zTTp. apply optr_fmem_range. intros q Hq.
  destruct fmL_cases as [(_ & _ & _ & _ & E) | (fm & pr & nx & _ & _ & _ & _ & _ & _ & _ & _ & pr2 & nx2 & _ & E & Hpr2 & _)]; rewrite E in Hq; cbn in Hq; [discriminate|]. injection Hq as <-. exact Hpr2.
Qed.
Lemma zTTn_range : ltac2:(tb__ "0|0|
S5SaZ0SaaA2SaSbSaaZ28A2Sd1VL;A1A2A2").
Proof using HMI Hgd Hu.
  unfold zTTn. apply optr_fmem_range. intros q Hq.
  destruct fmL_cases as [(_ & _ & _ & _ & E) | (fm & pr & nx & _ & _ & _ & _ & _ & _ & _ & _ & pr2 & nx2 & _ & E & _ & Hnx2)]; rewrite E in Hq; cbn in Hq; [discriminate|]. injection Hq as <-. exact Hnx2.
Qed.

Definition useq_bytes (j : nat) : list byte := ltac2:(tb__ "0|0|
S111S2aVs;A1Vj;A2").
Definition useq_dw (j : nat) : Z := ltac2:(tb__ "0|0|
S110S2aVs;A1Vj;A2").
Lemma useq_dw_range j : ltac2:(tb__ "0|1|
S5SaZ0S8dVj;A1M0A2ScG0SdZ2Z40A2A2A2"). Proof using . apply udw_range. Qed.
Lemma useq_dw_enc j : ltac2:(tb__ "0|0|
S4S74SceQ8A1A1S53U8ScfQ40S8dVj;A1A2A2Sc6Vj;A1A3"). Proof using . apply udw_enc. Qed.

Definition nQ : sptr := ltac2:(tb__ "0|0|
S6cS1bA1S1bLx;S20Vam;A1S1bR1Ln;Vg;X6cx2").
Definition pQ : sptr := ltac2:(tb__ "0|0|
S6cS1bA1S1bLx;S21Vam;A1S1bR1Lp;Vg;X6cx2").
Definition anQ : ameta := mrec s nQ.
Definition apQ : ameta := mrec s pQ.
Definition zNm : Z := ltac2:(tb__ "0|0|
Sd2VL;S23S89A1A2").
Definition zNn : Z := ltac2:(tb__ "0|0|
S10bVL;S20S89A1A2").
Definition zNp : Z := ltac2:(tb__ "0|0|
S10bVL;S21S89A1A2").
Definition zPn : Z := ltac2:(tb__ "0|0|
S10bVL;S20S8aA1A2").
Definition zPm : Z := ltac2:(tb__ "0|0|
Sd2VL;S23S8aA1A2").
Definition zPp : Z := ltac2:(tb__ "0|0|
S10bVL;S21S8aA1A2").

Definition zU : Z := usage_of s sc.
Definition zB : Z := ltac2:(tb__ "0|0|
S32S12S85Z7A2S35Vs;A1A2").

Definition zA8 : Z := ltac2:(tb__ "0|2|
S6cSceQ8M0A1M1A1S0Lx;Vrd0;ScfQ40SbS99Z8A2A2A1G1Sd0G0R1A2Lb;Z0X6cx2").

Definition parQ : sptr * Z := ltac2:(tb__ "0|1|
S6cS71S1bS0A2M0A1G0Lx;S3aS44Vs;A1S23Vam;A1A2G0R1Lx;S6dS1bS0Vg;Z0A4X6cx2").
Definition gPar : sptr := fst parQ.
Definition iPar : Z := snd parQ.
Definition amPar : ameta := mrec s gPar.
Definition frPar : frame := ltac2:(tb__ "0|1|
S6cS29A1S29Lx;S31S30S84S86A2A1S29R1Lfr;S40Z0M0G0S33A3X6cx2").
Definition zQ : Z := addr_of L gPar.
Definition zQm : Z := ltac2:(tb__ "0|0|
Sd2VL;S23S84A1A2").
Definition zQa : Z := zQ - zQ mod 4096.
Definition zHb : Z := ltac2:(tb__ "0|0|
S104S84S86S93A3").
Definition zOff : Z := ltac2:(tb__ "0|0|
S105S84S86S93A3").
Definition zSec : Z := ly_sec L mod 2 ^ 64.

Lemma par_spec : ltac2:(tb__ "0|5|
S4S0S1cVam;A1Z0M0A3S5SdbVX;Vs;S90S84A4S5S5SaG0S86A2SaS86S24S84A1A2A2S5S4S6cS29A1S31S30S84S86A2M1A1S6aS29S93A2A3S5S4S3bS3cS93A1S33A3S5S4S1bS23Vam;A1S34S84S86A2A3S5ScS85S25S84A1M2A2S5S7S4S0G2Z3fA3A1S5SaS12SbS37S10S39S85A1SbS24Vam;A1Z1A2A2A2S2eA2S3dS93A1M3A2S5S4S0S3eS93A1G0A3S5S4S0G3S12S2bS84A1S2eA2A3S5S4S6cS71S0S0A2M4A1S42G1A1S6aG4S6dS0S0S92S8cA4A2A3S5S4S6bSf0S84S86A2S70A3S7S4S1bS90Vg;A3A1A2A2A2A2A2A2A2A2A2A2A2A2F_;").
Proof using HMI Hgd Hu.
  intros Hml0. pose proof G as (_ & _ & _ & _ & _ & Gns).
  destruct (Gns Hml0) as (N63 & g' & am' & i' & fr' & U' & Hi' & F' & K' & Emem & Hsc' & N63' & Fit).
  pose proof (inv_groups HI g' am' U') as G'. pose proof G' as (_ & _ & Gsl' & _).
  pose proof (Gsl' i' Hi') as (_ & _ & S3'). rewrite F' in S3'. destruct S3' as (Hal' & _ & FOK & HDR).
  pose proof FOK as (_ & _ & _ & _ & FG). destruct (FG K') as [Hoff' Hn'].
  assert (EQ : parQ = (g', i')).
  { unfold parQ. replace (am_mem am) with (frame_ptr am' i' fr').
    - rewrite (find_frame_in_spec X (Some (g, i)) U s HI g' am' i' fr' U' Hi' F'). reflexivity.
    - unfold frame_ptr. rewrite Hoff', Z.mul_0_r. rewrite <- Emem. destruct (am_mem am) as [r o]; cbn [padd]; rewrite Z.add_0_r; reflexivity. }
  assert (Eg : gPar = g') by (unfold gPar; rewrite EQ; reflexivity).
  assert (Ei : iPar = i') by (unfold iPar; rewrite EQ; reflexivity).
  assert (Ea : amPar = am') by (unfold amPar; rewrite Eg; unfold mrec; rewrite (proj1 (usedX_MT _ _ _ _ U')); reflexivity).
  assert (Ef : frPar = fr') by (unfold frPar; rewrite Ea, Ei, F'; reflexivity).
  unfold zHb, zOff. rewrite Eg, Ei, Ea, Ef.
  split; [exact U'|]. split; [exact Hi'|]. split; [exact F'|]. split; [exact K'|]. split; [exact Emem|]. split; [unfold sc; exact Hsc'|].
  split; [exact N63'|]. split; [exact Fit|]. split; [exact Hoff'|]. split; [exact Hn'|]. split; [exact (HDR Hoff')|]. split; [exact Hal'|].
  intros E. pose proof (usedX_fun _ _ _ _ _ U' ltac:(rewrite E; exact Hu)) as E2. rewrite E2 in Hsc'. lia.
Qed.

Definition rw1v (j : positive) : option Z := ltac2:(tb__ "0|1|
S3Vj;A1S0S6bS6cS0A1L_;M0SeR1ZdA2S6aS0Vi;A2G0SeR1Z85A2S6aS0S1dVam;A1A2G0SeR1Z86A2S6aS0S1eVam;A1A2G0SeR1Z87A2S6aS0S91A2G0SeR1Z8cA2S6aS0S9bA2G0SeR1Z8dA2S6aS0S9aA2G0SeR1Z8eA2S6aS0S8eA2G0SeR1Z8fA2S6aS0Vgd;A2G0SeR1Z96A2S6aS0S97A2G0SeR1Za5A2S6aS0S98A2G0SeR1Za6A2S6aS0Sa3A2G0SeR1Za7A2S6aS0SaeA2G0SeR1Za8A2S6aS0SadA2G0SeR1ZafA2S6aS0Sa2A2G0SeR1Zb0A2S6aS0S1dS87A1A2G0SeR1Zb1A2S6aS0S1eS87A1A2G0SeR1Zb2A2S6aS0SdcS87A1A2G0SeR1Zb3A2S6aS0SacA2G0SeR1Zb6A2S6aS0S1dS88A1A2G0SeR1Zb7A2S6aS0S1eS88A1A2G0SeR1Zb8A2S6aS0SdcS88A1A2G0SeR1Z98A2S6aS0SbaA2G0SeR1Z74A2S6aS0S8dU0A1A2G0SeR1Z75A2S6aS0S8dU1A1A2G0SeR1Z76A2S6aS0S8dU2A1A2G0SeR1Z77A2S6aS0S8dU3A1A2G0SeR1Za0A2S6aS0S9eA2G0SeR1Za1A2S6aS0Sa0A2G0SeR1Za2A2S6aS0S9fA2G0SeR1Za3A2S6aS0SabA2G0SeR1Za4A2S6aS0SaaA2G0SeR1Z97A2S6aS0SbbA2G0SeR1Zb9A2S6aS0Sb8A2G0SeR1Z99A2S6aS0S1dS89A1A2G0SeR1Z9aA2S6aS0SdcS89A1A2G0SeR1Z9bA2S6aS0S1eS89A1A2G0SeR1Z9cA2S6aS0S99A2G0SeR1Z9dA2S6aS0Sa4A2G0SeR1Z9eA2S6aS0Sb7A2G0SeR1Z6fA2S6aS0Sa6A2G0SeR1Z70A2S6aS0S1dS8aA1A2G0SeR1Z71A2S6aS0S1eS8aA1A2G0SeR1Z72A2S6aS0SdcS8aA1A2G0SeR1Z9fA2S6aS0Sa8A2G0SeR1Z6eA2S6aS0Sa5A2G0SeR1Z73A2S6aS0Sa7A2G0SeR1ZaaA2S6aS0S92A2G0SeR1ZabA2S6aS0S8cA2G0SeR1ZacA2S6aS0S95A2G0SeR1ZadA2S6aS0S1dS84A1A2G0SeR1ZaeA2S6aS0S1eS84A1A2G0SeR1Za9A2S6aS0SdcS84A1A2G0SeR1Z88A2S6aS0Sb9A2S73S0A1X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2X6bx2Tz;").
Definition rw1 (j : positive) : word := ltac2:(tb__ "0|1|
S6cS0A1SceQ40M0A1Lx;Sc5Vj;A1S0ScfG0R1A2Lz;S4aVrho;Vj;A2X6cx2").
Definition rl1 (l : positive) : list byte := ltac2:(tb__ "0|2|
S6bS74SceQ8M0A1M1A1L_;S1c1Vl;P1A2S155S0G1ScfG0A1Sd7A4S59Vrho;Vl;A2X6bx2").
Definition rho1 (m : word -> option byte) : valuation := ltac2:(tb__ "0|0|
S61Sb1Sc4Vm;A3").

Lemma rw1_low : ltac2:(tb__ "0|0|
S1S1c2R1P64A2S7S4S1R2PdA3A1S4SceQ40A1Sb1R3A1S4aVrho;R3A2A3F_;F_;Fj;").
Proof using Hgd.
  intros j Hj H13. unfold rw1, rw1v.
  repeat match goal with |- context [if ?c then _ else _] => let e := fresh in destruct c eqn:e; [exfalso; apply Z.eqb_eq in e; lia|] end.
  reflexivity.
Qed.

Definition zr1 : positive -> Z := zr_of (rho1 (fun _ => None)).
Definition zl1 : positive -> list Z := zl_of (rho1 (fun _ => None)).
Lemma zr1_zl1_any : ltac2:(tb__ "0|1|
SceQ40A1S6cSceQ8A1A1F_;S46S4S0S7aS81Sb0R2A1M0A1S80G0A1R1A3S7aS82S83R1A3A3Fe;Fm;").
Proof using . intros m e. reflexivity. Qed.
Lemma zr1_any m j : ltac2:(tb__ "0|0|
S4S0S81Sb0Vm;A1Vj;A2S82Vj;A1A3"). Proof using . reflexivity. Qed.
Lemma zl1_any m l : ltac2:(tb__ "0|0|
S4S74S0A1S80Sb0Vm;A1Vl;A2S83Vl;A1A3"). Proof using . reflexivity. Qed.
Lemma zl1_1 : zl1 1%positive = size_classes_bytes.
Proof using Hgd.
  unfold zl1, zl_of, rho1. cbn [rl rl1 Pos.eqb].
  rewrite map_map. rewrite <- (map_id size_classes_bytes) at 2. apply map_ext_in.
  intros b Hb. pose proof (proj1 (Forall_forall _ _) size_classes_bytes_range b Hb) as R.
  cbn beta in R. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= b < 256). lia.
Qed.

Lemma zr1_v : ltac2:(tb__ "0|1|
S1S0S4SceQ40M0A1Sb1R2A1ScfG0R1A2A3S5SaZ0R2A2ScR2SdZ2Z40A2A2A2S4S0S82R4A1R3A3F_;F_;Fz;Fj;").
Proof using . intros j z E Hz. unfold zr1, zr_of, rho1. cbn [rw]. rewrite E. apply u64. exact Hz. Qed.
Lemma zr1_12 : zr1 12%positive = zG. Proof using HP12. unfold zr1, zr_of, rho1. cbn [rw rw1 rw1v Z.eqb Pos.eqb]. exact HP12. Qed.
Lemma zr1_10 : ltac2:(tb__ "0|1|
S4S0S82PaM0A1Sd0Q40S4aVrho;G0A2A2A3"). Proof using . reflexivity. Qed.
Lemma zr1_15 : ltac2:(tb__ "0|1|
S4S0S82PfM0A1Sd0Q40S4aVrho;G0A2A2A3"). Proof using . reflexivity. Qed.
Lemma zr1_13 : zr1 13%positive = i. Proof using HMI Hgd Hu. apply (zr1_v 13 i eq_refl). pose proof R_all. lia. Qed.
Lemma zr1_133 : ltac2:(tb__ "0|0|
S4S0S82P85A1S1dVam;A1A3"). Proof using HMI Hgd Hu. apply (zr1_v 133 _ eq_refl). pose proof R_all. lia. Qed.
Lemma zr1_134 : ltac2:(tb__ "0|0|
S4S0S82P86A1S1eVam;A1A3"). Proof using HMI Hgd Hu. apply (zr1_v 134 _ eq_refl). pose proof R_all. lia. Qed.
Lemma zr1_135 : zr1 135%positive = bits. Proof using HMI Hgd Hu. apply (zr1_v 135 _ eq_refl). pose proof bits_range. lia. Qed.
Lemma zr1_140 : zr1 140%positive = zPv. Proof using HMI Hgd Hu. apply (zr1_v 140 _ eq_refl). pose proof zPv_range. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_141 : zr1 141%positive = zNx. Proof using HMI Hgd Hu. apply (zr1_v 141 _ eq_refl). pose proof zNx_range. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_142 : zr1 142%positive = zM. Proof using HMI Hgd Hu. apply (zr1_v 142 _ eq_refl). pose proof R_all. lia. Qed.
Lemma zr1_143 : zr1 143%positive = gd. Proof using Hgd. apply (zr1_v 143 _ eq_refl). exact Hgd. Qed.

Lemma linked_ring_of q a : ltac2:(tb__ "0|5|
SdbVX;Vs;Vq;Va;A4S9S7S4S6cS1bA1M0S21Va;A1S73S1bA1M1A3A1S7S4G0S20Va;A1G1A3A1A2S6S0S0S6S1bS1bS6S74S1bA1M2G2S5S5SaZ0R3A2ScR3Z30A2A2S5S4S0S25Va;A1R3A3S5S4G0Se1Vs;R3A2S6aS1bR2A2M3A3S5Se9SeeVX;Vs;R3A3G3S6fS1bR2R1A3M4A3Sc9S1bVq;G4A3A2A2A2A2Lrest;A2Lm0;A2Lc;A2F_;F_;").
Proof using HMI.
  intros Hq Hl.
  pose proof (inv_groups HI q a Hq) as Gq. pose proof Gq as (_ & _ & _ & Gcl & _).
  assert (SC : am_sc a = 63 \/ 0 <= am_sc a < 48) by (destruct Gcl as [(C0 & _) | (C0 & _)]; [left | right]; exact C0).
  destruct (inv_rings HI) as (_ & A & D).
  destruct SC as [H63 | Hsc'].
  - exfalso. destruct (D q a Hq H63) as [P N]. destruct Hl as [Hl|Hl]; [exact (Hl P) | exact (Hl N)].
  - destruct (A (am_sc a) Hsc') as (ms & Rg & Mem & _).
    assert (Hin : In q ms).
    { apply (Mem q a Hq eq_refl). destruct (am_prev a), (am_next a); try discriminate. destruct Hl as [Hl|Hl]; exfalso; apply Hl; reflexivity. }
    destruct ms as [|m0 rest]; [destruct Hin|].
    exists (am_sc a), m0, rest. pose proof Rg as [_ Hhd']. cbn in Hhd'.
    split; [exact Hsc'|]. split; [reflexivity|]. split; [exact Hhd'|]. split; [rewrite <- Hhd'; exact Rg | exact Hin].
Qed.
Lemma prev_used_of q a p : ltac2:(tb__ "0|0|
SdbVX;Vs;Vq;Va;A4S4S6cS1bA1S21Va;A1S6aS1bVp;A2A3S6S22S22SdbVX;Vs;Vp;R1A4La';A2F_;F_;").
Proof using HMI.
  intros Hq Hp. destruct (linked_ring_of q a Hq ltac:(left; rewrite Hp; discriminate)) as (c & m0 & rest & Hc & Ec & Hhd' & Rg & Hin).
  pose proof (ring_step X s c m0 rest q Rg Hin) as (_ & _ & Hp').
  unfold mprev, mrec in Hp'. rewrite (proj1 (usedX_MT _ _ _ _ Hq)), Hp in Hp'.
  destruct (ring_members_used _ _ _ _ _ _ Rg Hp') as (a' & Hu' & _). exists a'. exact Hu'.
Qed.
Lemma next_used_of q a n : ltac2:(tb__ "0|0|
SdbVX;Vs;Vq;Va;A4S4S6cS1bA1S20Va;A1S6aS1bVn;A2A3S6S22S22SdbVX;Vs;Vn;R1A4La';A2F_;F_;").
Proof using HMI.
  intros Hq Hn. destruct (linked_ring_of q a Hq ltac:(right; rewrite Hn; discriminate)) as (c & m0 & rest & Hc & Ec & Hhd' & Rg & Hin).
  pose proof (ring_step X s c m0 rest q Rg Hin) as (_ & Hn' & _).
  unfold mnext, mrec in Hn'. rewrite (proj1 (usedX_MT _ _ _ _ Hq)), Hn in Hn'.
  destruct (ring_members_used _ _ _ _ _ _ Rg Hn') as (a' & Hu' & _). exists a'. exact Hu'.
Qed.
Lemma links_used_range' q a : ltac2:(tb__ "0|5|
SdbVX;Vs;Vq;Va;A4S5S5SaZ0M0S10bVL;S21Va;A1A2M1A2SaSbG1Z28M2A2Sd1VL;A1M3A2A2S5SaG0S10bVL;S20Va;A1A2M4A2SaSbG4G2A2G3A2A2A2F_;").
Proof using HMI Hgd. intros Hq. split; apply optr_range; intros q' Hq'; [exact (prev_used_of q a q' Hq Hq') | exact (next_used_of q a q' Hq Hq')]. Qed.

Lemma mrec_range q : ltac2:(tb__ "0|6|
S5S5SaZ0M0S10bVL;S21S18cVs;Vq;A2M1A1A2M2A2SaSbG2Z28M3A2Sd1VL;A1M4A2A2S5SaG0S10bVL;S20G1A1A2M5A2SaSbG5G3A2G4A2A2A2").
Proof using HMI HXz Hgd.
  pose proof (ceiling_small L) as CS. unfold mrec. destruct (MT s q) as [[pr nx| |a]|] eqn:E;
    try (cbn [am_prev am_next am_dummy optrA]; top_ranges; lia).
  destruct (memb q X) eqn:Em.
  - exfalso. unfold memb in Em. apply existsb_exists in Em as (q' & Hq' & Eq). apply sptr_eqb_eq in Eq. subst q'.
    destruct (HXr q Hq') as [R1|R1]; rewrite R1 in E; discriminate.
  - assert (Hq : usedX X s q a) by (unfold usedX, MTX; rewrite Em; exact E).
    split; apply optr_range; intros q' Hq'; [exact (prev_used_of q a q' Hq Hq') | exact (next_used_of q a q' Hq Hq')].
Qed.

Lemma mrec_used q : ltac2:(tb__ "0|0|
S6S22S22SdbVX;Vs;Vq;R1A4La;A2SdbVX;Vs;Vq;S18cVs;Vq;A2A4F_;").
Proof using . intros [a Ha]. unfold mrec. rewrite (proj1 (usedX_MT _ _ _ _ Ha)). exact Ha. Qed.
Lemma hQ_used : ltac2:(tb__ "0|0|
SdbVX;Vs;SbfS87A4").
Proof using HMI Hgd Hu.
  unfold ahQ. apply mrec_used. unfold hQ. destruct (active_hd s sc) as [h|] eqn:E; [|exists am; exact Hu].
  pose proof R_all as R. destruct (Z_lt_dec sc 48).
  - destruct (h_used ltac:(unfold sc in *; lia) h E) as (Hu' & _). eexists. exact Hu'.
  - exfalso. pose proof (proj1 (inv_ctx HI)) as Hlen. unfold active_hd in E. rewrite nth_overflow in E; [discriminate|]. rewrite Hlen. unfold sc in *. lia.
Qed.
Lemma tQ_used : ltac2:(tb__ "0|0|
SdbVX;Vs;S94S88A4").
Proof using HMI Hgd Hu.
  unfold atQ. apply mrec_used. unfold tQ, mprev. fold ahQ. destruct (am_prev ahQ) as [p|] eqn:E; [|exists ahQ; exact hQ_used].
  exact (prev_used_of hQ ahQ p hQ_used E).
Qed.
Lemma rec_ranges q a : ltac2:(tb__ "0|7|
SdbVX;Vs;Vq;Va;A4S5S5SaZ0M0S1dVa;A1M1A2ScG1SdZ2M2Z20A2M3A2A2S5S5SaG0S1eVa;A1M4A2ScG4G3A2A2S5S5SaG0SdcVa;A1M5A2ScG5SdG2Z30A2A2A2S5SaZ1000Sd2VL;S23Va;A1A2M6A2SaSbG6Z10A2Sd1VL;A1A2A2A2A2A2F_;").
Proof using HMI Hgd.
  intros Hq. pose proof (used_ranges X (Some (g, i)) U s HI q a Hq) as (A1 & A2 & A3 & A4 & A5). pose proof (ceiling_small L) as CS.
  pose proof (used_addrs X (Some (g, i)) U s HI C_U L vm HL HV HLG q a Hq) as (B1 & B2 & B3 & _ & B5 & B6 & _).
  pose proof (inv_groups HI q a Hq) as Gq. pose proof (stride_pos _ _ _ _ _ Gq) as SP.
  assert (SC : am_sc a = 63 \/ 0 <= am_sc a < 48) by (pose proof Gq as (_ & _ & _ & Gcl & _); destruct Gcl as [(C0 & _) | (C0 & _)]; [left | right]; exact C0).
  assert (ML : 0 <= am_maplen a < 2 ^ 35).
  { pose proof Gq as (_ & _ & _ & _ & Gmp & _). destruct (Z_lt_dec 0 (am_maplen a)) as [Hpos|]; [|lia].
    destruct (Gmp Hpos) as (r & rg & Em & Hr & Hk & Hl & Hlen & Hfit & _).
    pose proof (footprint_region_In s _ _ Hr Hk Hl) as InR.
    pose proof (fp_mem_range C_U L s vm _ _ HV HLG InR ltac:(unfold PGSZ in *; lia)) as (M1 & M2 & _). unfold PGSZ in *. lia. }
  assert (PR : 0 <= stride_of a * (am_last a + 1)) by nia.
  unfold meta_bits, PGSZ, UNIT in *. repeat split; try lia.
Qed.
Lemma zHp_range : ltac2:(tb__ "0|0|
S5SaZ0S98A2SaSbS98Z28A2Sd1VL;A1A2A2"). Proof using HMI HXz Hgd. exact (proj1 (mrec_range hQ)). Qed.
Lemma zHn_range : ltac2:(tb__ "0|0|
S5SaZ0Sa3A2SaSbSa3Z28A2Sd1VL;A1A2A2"). Proof using HMI HXz Hgd. exact (proj2 (mrec_range hQ)). Qed.
Lemma zTp_range : ltac2:(tb__ "0|0|
S5SaZ0SaeA2SaSbSaeZ28A2Sd1VL;A1A2A2"). Proof using HMI HXz Hgd. exact (proj1 (mrec_range tQ)). Qed.
Lemma zTn_range : ltac2:(tb__ "0|0|
S5SaZ0SadA2SaSbSadZ28A2Sd1VL;A1A2A2"). Proof using HMI HXz Hgd. exact (proj2 (mrec_range tQ)). Qed.
Lemma nQ_used : ltac2:(tb__ "0|0|
SdbVX;Vs;Sb5S89A4").
Proof using HMI Hgd Hu. unfold anQ. apply mrec_used. unfold nQ. destruct (am_next am) as [n|] eqn:E; [exact (next_used n E) | exists am; exact Hu]. Qed.
Lemma pQ_used : ltac2:(tb__ "0|0|
SdbVX;Vs;Sb6S8aA4").
Proof using HMI Hgd Hu. unfold apQ. apply mrec_used. unfold pQ. destruct (am_prev am) as [p|] eqn:E; [exact (prev_used p E) | exists am; exact Hu]. Qed.
Lemma RN : ltac2:(tb__ "0|6|
S5S5SaZ0M0S1dS89A1M1A2ScG1SdZ2M2Z20A2M3A2A2S5S5SaG0S1eS89A1M4A2ScG4G3A2A2S5S5SaG0SdcS89A1M5A2ScG5SdG2Z30A2A2A2S5SaZ1000S99A2SaSbS99Z10A2Sd1VL;A1A2A2A2A2A2").
Proof using HMI Hgd Hu. exact (rec_ranges nQ anQ nQ_used). Qed.
Lemma RP : ltac2:(tb__ "0|6|
S5S5SaZ0M0S1dS8aA1M1A2ScG1SdZ2M2Z20A2M3A2A2S5S5SaG0S1eS8aA1M4A2ScG4G3A2A2S5S5SaG0SdcS8aA1M5A2ScG5SdG2Z30A2A2A2S5SaZ1000Sa6A2SaSbSa6Z10A2Sd1VL;A1A2A2A2A2A2").
Proof using HMI Hgd Hu. exact (rec_ranges pQ apQ pQ_used). Qed.
Lemma zNn_range : ltac2:(tb__ "0|0|
S5SaZ0Sa4A2SaSbSa4Z28A2Sd1VL;A1A2A2"). Proof using HMI HXz Hgd. exact (proj2 (mrec_range nQ)). Qed.
Lemma zPp_range : ltac2:(tb__ "0|0|
S5SaZ0Sa8A2SaSbSa8Z28A2Sd1VL;A1A2A2"). Proof using HMI HXz Hgd. exact (proj1 (mrec_range pQ)). Qed.
Lemma zNp_range : ltac2:(tb__ "0|0|
S5SaZ0Sa5A2SaSbSa5Z28A2Sd1VL;A1A2A2"). Proof using HMI HXz Hgd. exact (proj1 (mrec_range nQ)). Qed.
Lemma zPn_range : ltac2:(tb__ "0|0|
S5SaZ0Sa7A2SaSbSa7Z28A2Sd1VL;A1A2A2"). Proof using HMI HXz Hgd. exact (proj2 (mrec_range pQ)). Qed.
Lemma gPar_used : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3SdbVX;Vs;S90S84A4F_;"). Proof using HMI Hgd Hu. intros H. exact (proj1 (par_spec H)). Qed.
Lemma gPar_key : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3Sc9S1bS90Se3Vs;A1A3F_;").
Proof using HMI Hgd Hu. intros H. eapply MT_Some_In_keys. exact (proj1 (usedX_MT _ _ _ _ (gPar_used H))). Qed.
Lemma RQ : ltac2:(tb__ "0|6|
S4S0S1cVam;A1Z0M0A3S5S5SaG0S1dS84A1M1A2ScG1SdZ2M2Z20A2M3A2A2S5S5SaG0S1eS84A1M4A2ScG4G3A2A2S5S5SaG0SdcS84A1M5A2ScG5SdG2Z30A2A2A2S5SaZ1000S9cA2SaSbS9cZ10A2Sd1VL;A1A2A2A2A2A2F_;").
Proof using HMI Hgd Hu. intros H. exact (rec_ranges gPar amPar (gPar_used H)). Qed.
Lemma zQ_range : ltac2:(tb__ "0|1|
S4S0S1cVam;A1Z0M0A3S5SaZ1000S95A2S5SaSbS95Z28A2Sd1VL;A1A2S4S0SfS95Z8A2G0A3A2A2F_;").
Proof using HMI Hgd Hu.
  intros H. pose proof (used_addrs X (Some (g, i)) U s HI C_U L vm HL HV HLG gPar amPar (gPar_used H)) as (B1 & B2 & B3 & _).
  unfold zQ, PGSZ, META_SIZE in *. lia.
Qed.
Lemma par_last : ltac2:(tb__ "0|3|
S4S0S1cVam;A1Z0M0A3S5S5SaG0S86A2SaS86S24S84A1M1A2A2S5SaG1Z1fA2S5S5SaG0S25S84A1M2A2ScG2Z30A2A2SaZ10S2bS84A1A2A2A2A2F_;").
Proof using HMI Hgd Hu.
  intros H. pose proof (par_spec H) as (U' & Hi' & _ & _ & _ & _ & N63' & _).
  pose proof (inv_groups HI gPar amPar U') as G'. pose proof (stride_pos _ _ _ _ _ G') as SP.
  pose proof G' as ((Glast & _) & _ & _ & Gcl' & _).
  split; [exact Hi'|]. split; [lia|]. split; [|exact SP]. destruct Gcl' as [(C & _) | (C & _)]; [exfalso; exact (N63' C) | exact C].
Qed.
Lemma zHb_eq : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S92SbS86Zc0A2A3F_;").
Proof using HMI Hgd Hu. intros H. pose proof (par_spec H) as (_ & _ & _ & K & _). unfold zHb, hdr_byte3. rewrite K. reflexivity. Qed.
Lemma AGp (q : sptr) d : ltac2:(tb__ "0|0|
S4S0Sd2VL;S27Vq;Vd;A2A2SbSd2VL;Vq;A2Vd;A2A3").
Proof using Hgd. unfold addr_of, loc_addr. destruct q; cbn [padd]. lia. Qed.
Lemma zM_eq : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S8eSbSbS9cZ10A2S10S2bS84A1S86A2A2A3F_;").
Proof using HMI Hgd Hu. intros H. pose proof (par_spec H) as (_ & _ & _ & _ & Emem & _). unfold zM, zQm. rewrite Emem. unfold slot_start. rewrite AGp. unfold UNIT. lia. Qed.
Lemma zOff_eq : ltac2:(tb__ "0|1|
S4S0S1cVam;A1Z0M0A3S5S4S0S10S8cZ10A2S10S2bS84A1S86A2A3S5SaG0S8cA2SaS8cZffffA2A2A2F_;").
Proof using HMI Hgd Hu.
  intros H. pose proof (par_spec H) as (U' & Hi' & F' & K' & _ & _ & _ & _ & Hoff & _).
  pose proof (stride_mod16 X (Some (g, i)) U s gPar amPar HI U') as SM. pose proof (par_last H) as (_ & _ & _ & SP).
  pose proof (inv_groups HI gPar amPar U') as (_ & _ & Gsl' & _). pose proof (Gsl' iPar Hi') as (_ & _ & S3). rewrite F' in S3.
  destruct S3 as (_ & _ & FOK & _). pose proof FOK as (_ & _ & _ & H16 & _).
  unfold zOff, hdr_off16 in *. rewrite Hoff in *. unfold UNIT in *.
  assert (D : (stride_of amPar * iPar) mod 16 = 0) by (rewrite Z.mul_mod, SM by lia; reflexivity).
  pose proof (Z.div_mod (stride_of amPar * iPar) 16 ltac:(lia)). pose proof (Z.div_pos (stride_of amPar * iPar) 16 ltac:(nia) ltac:(lia)). lia.
Qed.
Lemma par_bits_clear : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S5S4S6bS14S1dS84A1S86A2S76A3S4S6bS14S1eS84A1S86A2S76A3A2F_;").
Proof using HMI Hgd Hu.
  intros H. pose proof (par_spec H) as (_ & Hi' & _ & _ & _ & _ & _ & _ & _ & _ & _ & AL & _).
  unfold allocated in AL. apply Bool.negb_true_iff in AL. rewrite Z.lor_spec in AL. apply Bool.orb_false_iff in AL. exact AL.
Qed.
Lemma par_off_chk : ltac2:(tb__ "0|2|
S4S0S1cVam;A1Z0A3S5SaS10S32S25S84A1S41A2M0S86A2S8cA2S5ScS8cS10G0SbS86Z1M1A2A2A2S5SaG1G0A2SaG0Z1fffA2A2A2A2F_;").
Proof using HMI Hgd Hu.
  intros H. pose proof (zOff_eq H) as [E R]. pose proof (par_last H) as (Hi & Hl & Hsc & SP).
  pose proof (znth_size_classes_range (am_sc amPar) Hsc) as CS.
  assert (ST : stride_of amPar = class_size (am_sc amPar) \/ (am_last amPar = 0 /\ iPar = 0)).
  { unfold stride_of. destruct (am_last amPar =? 0) eqn:E0; [apply Z.eqb_eq in E0; right; lia | left; reflexivity]. }
  unfold class_size, UNIT in ST. destruct ST as [ST | [HL0 HI0]]; [rewrite ST in E | rewrite HI0, Z.mul_0_r in E; rewrite HI0]; nia.
Qed.
Lemma par_map_chk : ltac2:(tb__ "0|2|
S4S0S1cVam;A1Z0M0A3S7S4S0S1cS84A1M1G0A3A1S5SaS8cS12S10G1Z100A2Z1A2A2S5ScG0G1A2ScG1SdZ2Z23A2A2A2A2F_;F_;").
Proof using HMI Hgd Hu.
  intros H Hml. pose proof (zOff_eq H) as [E R]. pose proof (par_last H) as (Hi & Hl & Hsc & SP). pose proof (gPar_used H) as U'.
  pose proof (used_ranges X (Some (g, i)) U s HI gPar amPar U') as (_ & _ & _ & _ & ML0).
  pose proof (inv_groups HI gPar amPar U') as (_ & _ & _ & _ & Gmp & _).
  destruct (Gmp ltac:(lia)) as (r & rg & Em & Hr & Hk & Hlv & Hlen & Hfit & _).
  pose proof (footprint_region_In s _ _ Hr Hk Hlv) as InR.
  pose proof (fp_mem_range C_U L s vm _ _ HV HLG InR ltac:(unfold PGSZ in *; lia)) as (M1 & M2 & _).
  assert (stride_of amPar * iPar <= stride_of amPar * am_last amPar) by nia.
  unfold UNIT, PGSZ in *. pose proof (ceiling_small L). split; [|lia]. nia.
Qed.
Lemma par_area : ltac2:(tb__ "0|1|
S4S0S1cVam;A1Z0A3S6S1bS1bS5Sc9S1bR1S43Vs;A1A3S5S4S0Sd2VL;R1A2Sa9A3S5SaZ1000M0Sa9A2S5SaSbSa9G0A2Sd1VL;A1A2Sc9SdaSdeSe0R1A1U8SedA3SddVs;A1A3A2A2A2A2La;A2F_;").
Proof using HMI Hgd Hu.
  intros H. pose proof (gPar_key H) as K. destruct (key_area X (Some (g, i)) U s HI gPar K) as (a & k & Ha & Hk & Eq).
  pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK a Ha) as (r & o & rg & Ea & Ho & Ho0 & Hr & Hl & Hfit & _).
  pose proof HL as (_ & ALG & _ & _). pose proof (ALG r rg Hr Hl) as RA.
  pose proof (e_area_In s a Ha) as FP. pose proof (fp_mem_range C_U L s vm _ _ HV HLG FP ltac:(unfold PGSZ; lia)) as (M1 & M2 & _).
  assert (EA : addr_of L a = ly_reg L r + o) by (rewrite Ea; reflexivity).
  assert (EQ : zQ = addr_of L a + (AREA_HDR + META_SIZE * k)) by (unfold zQ; rewrite Eq, AGp; reflexivity).
  assert (AM : addr_of L a mod 4096 = 0) by (rewrite EA; unfold PGSZ in *; rewrite Z.add_mod, RA, Ho by lia; reflexivity).
  exists a. split; [exact Ha|]. split.
  { unfold zQa. rewrite EQ. unfold AREA_HDR, META_SIZE, METAS_PER_AREA in *.
    rewrite Z.add_mod, AM, Z.add_0_l, Z.mod_mod, (Z.mod_small (24 + 40 * k)) by lia. lia. }
  unfold zQa. rewrite EQ. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *.
  rewrite Z.add_mod, AM, Z.add_0_l, Z.mod_mod, (Z.mod_small (24 + 40 * k)) by lia.
  split; [lia|]. split; [lia|].
  unfold image. apply in_app_iff. right. apply in_app_iff. left. apply (In_areas_cells_intro s _ a); [exact Ha|]. intros next. left. reflexivity.
Qed.
Lemma init_trueI : st_init_done s = true.
Proof using HMI Hu.
  destruct (st_init_done s) eqn:E; [reflexivity|]. exfalso.
  pose proof (proj1 HI) as CX. unfold ctx_ok in CX.
  destruct CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _). destruct (Hf E) as (M & _).
  pose proof g_key as KK. unfold keys in KK. rewrite M in KK. destruct KK.
Qed.
Lemma secret_cell : ltac2:(tb__ "0|0|
Sc9SdaSdeSe5Sf5A1U8SedA3SddVs;A1A3").
Proof using HMI Hu. unfold image. apply in_app_iff. left. unfold ctx_cells. rewrite init_trueI. left. reflexivity. Qed.
Lemma group_cell_image q a c : ltac2:(tb__ "0|0|
SdbVX;Vs;Vq;Va;A4Sc9SdaVc;S101Vq;Va;A2A3Sc9SdaVc;SddVs;A1A3F_;F_;").
Proof using HMI HXz.
  intros Hq Hc. unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map.
  exists (q, a). split; [apply (used_iff X (Some (g, i)) U s HI HXr); exact Hq | exact Hc].
Qed.
Lemma hdr_cells : ltac2:(tb__ "0|4|
S4S0S1cVam;A1Z0M0A3S5Sc9SdaSdeSe0S27S23Vam;A1M1N4A2A1U1M2Se2G0A1A3SddVs;A1M3A3S5Sc9SdaSdeSe0S27G1N3A2A1G2Se2S92A1A3G3A3S5Sc9SdaSdeSe0S27G1N2A2A1U2Se2S8cA1A3G3A3Sc9SdaSdeSe0G1A1U8SebVg;A1A3G3A3A2A2A2F_;").
Proof using HMI HXz Hgd Hu.
  intros H. pose proof (par_spec H) as (U' & Hi' & F' & _ & Emem & _ & _ & _ & Hoff & _ & HDR & _).
  assert (SC : forall c, In c (slot_cells amPar iPar) -> In c (image s)).
  { intros c Hc. apply (group_cell_image gPar amPar c U'). unfold group_cells. right. right. apply in_flat_map. exists iPar. split; [apply zseq_In; lia | exact Hc]. }
  unfold slot_cells in SC. rewrite <- Emem, HDR, F', Hoff, Z.eqb_refl in SC.
  split; [apply SC; cbn; tauto|]. split; [apply SC; cbn; tauto|]. split; [apply SC; cbn; tauto|].
  apply (group_cell_image g am _ Hu). left. reflexivity.
Qed.
Lemma pbase_cell : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3Sc9SdaSdeSe0S23S84A1A1U8SebS90A1A3SddVs;A1A3F_;").
Proof using HMI HXz Hgd Hu. intros H. apply (group_cell_image gPar amPar _ (gPar_used H)). left. reflexivity. Qed.
Lemma pmeta_cells : ltac2:(tb__ "0|3|
S4S0S1cVam;A1Z0A3S5Sc9SdaSdeSe0S27S90SfdA2A1U8M0SebS23S84A1A1A3SddVs;A1M1A3S5Sc9SdaSdeSe0S27S90SfaA2A1U4M2Se2S1dS84A1A1A3G1A3S5Sc9SdaSdeSe0S27S90SfcA2A1G2Se2S1eS84A1A1A3G1A3Sc9SdaSdeSe0S27S90SfbA2A1G0Se2SdcS84A1A1A3G1A3A2A2A2F_;").
Proof using HMI Hgd Hu.
  intros H. pose proof (gPar_key H) as K. pose proof (proj1 (usedX_MT _ _ _ _ (gPar_used H))) as M.
  pose proof (fun c Hc => meta_cells_in_imageI X (Some (g, i)) U s HI gPar c K Hc) as MI. rewrite M in MI. cbn [meta_slot_cells] in MI.
  repeat split; apply MI; cbn; tauto.
Qed.

Lemma zU_range : 0 <= zU < 2 ^ 48.
Proof using HMI. pose proof (mig_bounded HMI) as (B1 & _). exact (B1 sc). Qed.
Lemma zB_range : 0 <= zB <= 255.
Proof using HMI Hgd.
  unfold zB, znth. pose proof (inv_ctx HI) as (_ & _ & _ & LenB & _ & _ & UB & _).
  destruct (Nat.lt_ge_cases (Z.to_nat (sc - 7)) (length (st_bounces s))) as [Hk|Hk]; [apply UB; apply nth_In; exact Hk|]. rewrite nth_overflow by exact Hk. lia.
Qed.
Lemma zA8_range : 0 <= zA8 < 256.
Proof using Hgd. unfold zA8. destruct (rd0 _) as [b|]; [pose proof (urange_n 8 b) as UR; cbn in UR; lia | lia]. Qed.
Lemma zr1_150 : zr1 150%positive = zH. Proof using HMI Hgd Hu. apply (zr1_v 150 _ eq_refl). pose proof zH_range. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_165 : zr1 165%positive = zHp. Proof using HMI HXz Hgd. apply (zr1_v 165 _ eq_refl). pose proof zHp_range. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_166 : zr1 166%positive = zHn. Proof using HMI HXz Hgd. apply (zr1_v 166 _ eq_refl). pose proof zHn_range. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_167 : zr1 167%positive = zTp. Proof using HMI HXz Hgd. apply (zr1_v 167 _ eq_refl). pose proof zTp_range. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_168 : zr1 168%positive = zTn. Proof using HMI HXz Hgd. apply (zr1_v 168 _ eq_refl). pose proof zTn_range. pose proof (ceiling_small L). lia. Qed.
Lemma RH : ltac2:(tb__ "0|6|
S5S5SaZ0M0S1dS87A1M1A2ScG1SdZ2M2Z20A2M3A2A2S5S5SaG0S1eS87A1M4A2ScG4G3A2A2S5S5SaG0SdcS87A1M5A2ScG5SdG2Z30A2A2A2S5SaZ1000Sa2A2SaSbSa2Z10A2Sd1VL;A1A2A2A2A2A2").
Proof using HMI Hgd Hu. exact (rec_ranges hQ ahQ hQ_used). Qed.
Lemma RT : ltac2:(tb__ "0|6|
S5S5SaZ0M0S1dS88A1M1A2ScG1SdZ2M2Z20A2M3A2A2S5S5SaG0S1eS88A1M4A2ScG4G3A2A2S5S5SaG0SdcS88A1M5A2ScG5SdG2Z30A2A2A2S5SaZ1000SacA2SaSbSacZ10A2Sd1VL;A1A2A2A2A2A2").
Proof using HMI Hgd Hu. exact (rec_ranges tQ atQ tQ_used). Qed.
Lemma zr1_175 : zr1 175%positive = zHm. Proof using HMI Hgd Hu. apply (zr1_v 175 _ eq_refl). pose proof RH. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_176 : zr1 176%positive = am_avail ahQ. Proof using HMI Hgd Hu. apply (zr1_v 176 _ eq_refl). pose proof RH. lia. Qed.
Lemma zr1_177 : zr1 177%positive = am_freed ahQ. Proof using HMI Hgd Hu. apply (zr1_v 177 _ eq_refl). pose proof RH. lia. Qed.
Lemma zr1_178 : zr1 178%positive = meta_bits ahQ. Proof using HMI Hgd Hu. apply (zr1_v 178 _ eq_refl). pose proof RH. lia. Qed.
Lemma zr1_179 : zr1 179%positive = zTm. Proof using HMI Hgd Hu. apply (zr1_v 179 _ eq_refl). pose proof RT. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_182 : zr1 182%positive = am_avail atQ. Proof using HMI Hgd Hu. apply (zr1_v 182 _ eq_refl). pose proof RT. lia. Qed.
Lemma zr1_183 : zr1 183%positive = am_freed atQ. Proof using HMI Hgd Hu. apply (zr1_v 183 _ eq_refl). pose proof RT. lia. Qed.
Lemma zr1_184 : zr1 184%positive = meta_bits atQ. Proof using HMI Hgd Hu. apply (zr1_v 184 _ eq_refl). pose proof RT. lia. Qed.
Lemma zr1_152 : zr1 152%positive = zSeq. Proof using HMI Hgd. apply (zr1_v 152 _ eq_refl). pose proof seq_range. lia. Qed.
Lemma zr1_116 : zr1 116%positive = useq_dw 0. Proof using . apply (zr1_v 116 _ eq_refl). apply useq_dw_range. Qed.
Lemma zr1_117 : zr1 117%positive = useq_dw 1. Proof using . apply (zr1_v 117 _ eq_refl). apply useq_dw_range. Qed.
Lemma zr1_118 : zr1 118%positive = useq_dw 2. Proof using . apply (zr1_v 118 _ eq_refl). apply useq_dw_range. Qed.
Lemma zr1_119 : zr1 119%positive = useq_dw 3. Proof using . apply (zr1_v 119 _ eq_refl). apply useq_dw_range. Qed.
Lemma zr1_160 : zr1 160%positive = zF. Proof using HMI Hgd Hu. apply (zr1_v 160 _ eq_refl). pose proof zF_range. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_161 : zr1 161%positive = zFp. Proof using HMI Hgd Hu. apply (zr1_v 161 _ eq_refl). pose proof zFp_range. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_162 : zr1 162%positive = zFn. Proof using HMI Hgd Hu. apply (zr1_v 162 _ eq_refl). pose proof zFn_range. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_163 : zr1 163%positive = zTTp. Proof using HMI Hgd Hu. apply (zr1_v 163 _ eq_refl). pose proof zTTp_range. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_164 : zr1 164%positive = zTTn. Proof using HMI Hgd Hu. apply (zr1_v 164 _ eq_refl). pose proof zTTn_range. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_151 : zr1 151%positive = zU. Proof using HMI Hgd. apply (zr1_v 151 _ eq_refl). pose proof zU_range. lia. Qed.
Lemma zr1_185 : zr1 185%positive = zB. Proof using HMI Hgd. apply (zr1_v 185 _ eq_refl). pose proof zB_range. lia. Qed.

Lemma zSec_range : 0 <= zSec < 2 ^ 64. Proof using Hgd. unfold zSec. apply Z.mod_pos_bound. lia. Qed.
Lemma zr1_136 : zr1 136%positive = zSec. Proof using Hgd. apply (zr1_v 136 _ eq_refl). exact zSec_range. Qed.
Lemma zHb_range : ltac2:(tb__ "0|1|
S4S0S1cVam;A1Z0M0A3S5SaG0S92A2SaS92ZffA2A2F_;"). Proof using HMI Hgd Hu. intros H. rewrite (zHb_eq H). pose proof (par_last H). lia. Qed.
Lemma zr1_170 : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S82PaaA1S92A3F_;"). Proof using HMI Hgd Hu. intros H. apply (zr1_v 170 _ eq_refl). pose proof (zHb_range H). lia. Qed.
Lemma zr1_171 : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S82PabA1S8cA3F_;"). Proof using HMI Hgd Hu. intros H. apply (zr1_v 171 _ eq_refl). pose proof (zOff_eq H). lia. Qed.
Lemma zr1_172 : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S82PacA1S95A3F_;"). Proof using HMI Hgd Hu. intros H. apply (zr1_v 172 _ eq_refl). pose proof (zQ_range H). pose proof (ceiling_small L). lia. Qed.
Lemma zr1_173 : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S82PadA1S1dS84A1A3F_;"). Proof using HMI Hgd Hu. intros H. apply (zr1_v 173 _ eq_refl). pose proof (RQ H). lia. Qed.
Lemma zr1_174 : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S82PaeA1S1eS84A1A3F_;"). Proof using HMI Hgd Hu. intros H. apply (zr1_v 174 _ eq_refl). pose proof (RQ H). lia. Qed.
Lemma zr1_169 : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S82Pa9A1SdcS84A1A3F_;"). Proof using HMI Hgd Hu. intros H. apply (zr1_v 169 _ eq_refl). pose proof (RQ H). lia. Qed.
Lemma zr1_153 : zr1 153%positive = am_avail anQ. Proof using HMI Hgd Hu. apply (zr1_v 153 _ eq_refl). pose proof RN. lia. Qed.
Lemma zr1_154 : zr1 154%positive = meta_bits anQ. Proof using HMI Hgd Hu. apply (zr1_v 154 _ eq_refl). pose proof RN. lia. Qed.
Lemma zr1_155 : zr1 155%positive = am_freed anQ. Proof using HMI Hgd Hu. apply (zr1_v 155 _ eq_refl). pose proof RN. lia. Qed.
Lemma zr1_156 : zr1 156%positive = zNm. Proof using HMI Hgd Hu. apply (zr1_v 156 _ eq_refl). pose proof RN. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_157 : zr1 157%positive = zNn. Proof using HMI HXz Hgd. apply (zr1_v 157 _ eq_refl). pose proof zNn_range. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_158 : zr1 158%positive = zA8. Proof using Hgd. apply (zr1_v 158 _ eq_refl). pose proof zA8_range. lia. Qed.
Lemma zr1_111 : zr1 111%positive = zPm. Proof using HMI Hgd Hu. apply (zr1_v 111 _ eq_refl). pose proof RP. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_112 : zr1 112%positive = am_avail apQ. Proof using HMI Hgd Hu. apply (zr1_v 112 _ eq_refl). pose proof RP. lia. Qed.
Lemma zr1_113 : zr1 113%positive = am_freed apQ. Proof using HMI Hgd Hu. apply (zr1_v 113 _ eq_refl). pose proof RP. lia. Qed.
Lemma zr1_114 : zr1 114%positive = meta_bits apQ. Proof using HMI Hgd Hu. apply (zr1_v 114 _ eq_refl). pose proof RP. lia. Qed.
Lemma zr1_159 : zr1 159%positive = zPp. Proof using HMI HXz Hgd. apply (zr1_v 159 _ eq_refl). pose proof zPp_range. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_110 : zr1 110%positive = zNp. Proof using HMI HXz Hgd. apply (zr1_v 110 _ eq_refl). pose proof zNp_range. pose proof (ceiling_small L). lia. Qed.
Lemma zr1_115 : zr1 115%positive = zPn. Proof using HMI HXz Hgd. apply (zr1_v 115 _ eq_refl). pose proof zPn_range. pose proof (ceiling_small L). lia. Qed.

Lemma ze_var : ltac2:(tb__ "0|0|
S1S4S0S7aS82S83S56R1A1A3SfS82R1A1SdZ2Z40A2A2A3Fj;"). Proof using . reflexivity. Qed.
Lemma ze_v : ltac2:(tb__ "0|0|
S1S4S0S7aS82S83Sc7R1A1A3SfS82R1A1SdZ2Z40A2A2A3Fj;"). Proof using . reflexivity. Qed.
Lemma ze_lit : ltac2:(tb__ "0|0|
S0S4S0S7aS82S83S47R1A1A3SfR1SdZ2Z40A2A2A3Fz;"). Proof using . reflexivity. Qed.
Lemma ze_alu : ltac2:(tb__ "0|0|
S15fS46S46S4S0S7aS82S83S4eR3R2R1A3A3S7fZ40R3S7aS82S83R2A3S7aS82S83R1A3A4A3Fy;Fx;Fop;"). Proof using . reflexivity. Qed.
Lemma ze_aluw : ltac2:(tb__ "0|2|
S15fS46S46S4S0S7aS82S83S57R3R2R1A3A3S7dS7fZ20M0R3SfS7aS82S83R2A3SdZ2G0A2M1A2SfS7aS82S83R1A3G1A2A4A1A3Fy;Fx;Fop;"). Proof using . reflexivity. Qed.
Lemma ze_ext : ltac2:(tb__ "0|3|
S6bS2S46S4S0S7aS82S83S54R3R2R1A3A3S6bS0Lsg;R3SfS7eS1aR2A1M0S7aS82S83R1A3M1A2SdZ2M2Z40A2A2SfG1SdG2G0A2A2X6bx2A3Fx;Fw;Fsg;"). Proof using . reflexivity. Qed.

Lemma ze12 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7PcA1A3Sa1A3"). Proof using HMI HP12 Hgd Hu. rewrite ze_v, zr1_12. pose proof R_all. apply m64_small; lia. Qed.
Lemma ze13 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7PdA1A3Vi;A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_13. pose proof R_all. apply m64_small; lia. Qed.
Lemma ze133 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P85A1A3S1dVam;A1A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_133. pose proof R_all. apply m64_small; lia. Qed.
Lemma ze134 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P86A1A3S1eVam;A1A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_134. pose proof R_all. apply m64_small; lia. Qed.
Lemma ze135 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P87A1A3S91A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_135. pose proof bits_range. apply m64_small; lia. Qed.
Lemma ze140 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P8cA1A3S9bA3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_140. pose proof zPv_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze141 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P8dA1A3S9aA3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_141. pose proof zNx_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze142 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P8eA1A3S8eA3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_142. pose proof R_all. apply m64_small; lia. Qed.
Lemma ze143 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P8fA1A3Vgd;A3"). Proof using Hgd. rewrite ze_v, zr1_143. apply m64_small; lia. Qed.
Lemma ze150 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P96A1A3S97A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_150. pose proof zH_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze165 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pa5A1A3S98A3"). Proof using HMI HXz Hgd. rewrite ze_v, zr1_165. pose proof zHp_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze166 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pa6A1A3Sa3A3"). Proof using HMI HXz Hgd. rewrite ze_v, zr1_166. pose proof zHn_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze167 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pa7A1A3SaeA3"). Proof using HMI HXz Hgd. rewrite ze_v, zr1_167. pose proof zTp_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze168 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pa8A1A3SadA3"). Proof using HMI HXz Hgd. rewrite ze_v, zr1_168. pose proof zTn_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze175 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7PafA1A3Sa2A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_175. pose proof RH. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze176 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pb0A1A3S1dS87A1A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_176. pose proof RH. apply m64_small; lia. Qed.
Lemma ze177 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pb1A1A3S1eS87A1A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_177. pose proof RH. apply m64_small; lia. Qed.
Lemma ze178 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pb2A1A3SdcS87A1A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_178. pose proof RH. apply m64_small; lia. Qed.
Lemma ze179 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pb3A1A3SacA3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_179. pose proof RT. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze182 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pb6A1A3S1dS88A1A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_182. pose proof RT. apply m64_small; lia. Qed.
Lemma ze183 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pb7A1A3S1eS88A1A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_183. pose proof RT. apply m64_small; lia. Qed.
Lemma ze184 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pb8A1A3SdcS88A1A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_184. pose proof RT. apply m64_small; lia. Qed.
Lemma ze152 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P98A1A3SbaA3"). Proof using HMI Hgd. rewrite ze_v, zr1_152. pose proof seq_range. apply m64_small; lia. Qed.
Lemma ze116 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P74A1A3S8dU0A1A3"). Proof using Hgd. rewrite ze_v, zr1_116. pose proof (useq_dw_range 0). apply m64_small; lia. Qed.
Lemma ze117 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P75A1A3S8dU1A1A3"). Proof using Hgd. rewrite ze_v, zr1_117. pose proof (useq_dw_range 1). apply m64_small; lia. Qed.
Lemma ze118 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P76A1A3S8dU2A1A3"). Proof using Hgd. rewrite ze_v, zr1_118. pose proof (useq_dw_range 2). apply m64_small; lia. Qed.
Lemma ze119 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P77A1A3S8dU3A1A3"). Proof using Hgd. rewrite ze_v, zr1_119. pose proof (useq_dw_range 3). apply m64_small; lia. Qed.
Lemma ze160 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pa0A1A3S9eA3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_160. pose proof zF_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze161 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pa1A1A3Sa0A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_161. pose proof zFp_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze162 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pa2A1A3S9fA3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_162. pose proof zFn_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze163 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pa3A1A3SabA3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_163. pose proof zTTp_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze164 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pa4A1A3SaaA3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_164. pose proof zTTn_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze151 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P97A1A3SbbA3"). Proof using HMI Hgd. rewrite ze_v, zr1_151. pose proof zU_range. apply m64_small; lia. Qed.
Lemma ze185 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7Pb9A1A3Sb8A3"). Proof using HMI Hgd. rewrite ze_v, zr1_185. pose proof zB_range. apply m64_small; lia. Qed.
Lemma ze153 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P99A1A3S1dS89A1A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_153. pose proof RN. apply m64_small; lia. Qed.
Lemma ze154 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P9aA1A3SdcS89A1A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_154. pose proof RN. apply m64_small; lia. Qed.
Lemma ze155 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P9bA1A3S1eS89A1A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_155. pose proof RN. apply m64_small; lia. Qed.
Lemma ze156 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P9cA1A3S99A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_156. pose proof RN. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze157 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P9dA1A3Sa4A3"). Proof using HMI HXz Hgd. rewrite ze_v, zr1_157. pose proof zNn_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze158 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P9eA1A3Sb7A3"). Proof using Hgd. rewrite ze_v, zr1_158. pose proof zA8_range. apply m64_small; lia. Qed.
Lemma ze111 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P6fA1A3Sa6A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_111. pose proof RP. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze112 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P70A1A3S1dS8aA1A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_112. pose proof RP. apply m64_small; lia. Qed.
Lemma ze113 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P71A1A3S1eS8aA1A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_113. pose proof RP. apply m64_small; lia. Qed.
Lemma ze114 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P72A1A3SdcS8aA1A3"). Proof using HMI Hgd Hu. rewrite ze_v, zr1_114. pose proof RP. apply m64_small; lia. Qed.
Lemma ze159 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P9fA1A3Sa8A3"). Proof using HMI HXz Hgd. rewrite ze_v, zr1_159. pose proof zPp_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze110 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P6eA1A3Sa5A3"). Proof using HMI HXz Hgd. rewrite ze_v, zr1_110. pose proof zNp_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze115 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P73A1A3Sa7A3"). Proof using HMI HXz Hgd. rewrite ze_v, zr1_115. pose proof zPn_range. pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze136 : ltac2:(tb__ "0|0|
S4S0S7aS82S83Sc7P88A1A3Sb9A3"). Proof using Hgd. rewrite ze_v, zr1_136. pose proof zSec_range. apply Z.mod_small; lia. Qed.
Lemma ze170 : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S7aS82S83Sc7PaaA1A3S92A3F_;"). Proof using HMI Hgd Hu. intros H. rewrite ze_v, (zr1_170 H). pose proof (zHb_range H). apply m64_small; lia. Qed.
Lemma ze171 : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S7aS82S83Sc7PabA1A3S8cA3F_;"). Proof using HMI Hgd Hu. intros H. rewrite ze_v, (zr1_171 H). pose proof (zOff_eq H). apply m64_small; lia. Qed.
Lemma ze172 : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S7aS82S83Sc7PacA1A3S95A3F_;"). Proof using HMI Hgd Hu. intros H. rewrite ze_v, (zr1_172 H). pose proof (zQ_range H). pose proof (ceiling_small L). apply m64_small; lia. Qed.
Lemma ze173 : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S7aS82S83Sc7PadA1A3S1dS84A1A3F_;"). Proof using HMI Hgd Hu. intros H. rewrite ze_v, (zr1_173 H). pose proof (RQ H). apply m64_small; lia. Qed.
Lemma ze174 : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S7aS82S83Sc7PaeA1A3S1eS84A1A3F_;"). Proof using HMI Hgd Hu. intros H. rewrite ze_v, (zr1_174 H). pose proof (RQ H). apply m64_small; lia. Qed.
Lemma ze169 : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S7aS82S83Sc7Pa9A1A3SdcS84A1A3F_;"). Proof using HMI Hgd Hu. intros H. rewrite ze_v, (zr1_169 H). pose proof (RQ H). apply m64_small; lia. Qed.

Definition e_parbase : sv := ltac2:(tb__ "0|0|
S4eS160Sc7P8eA1S4eS15bSc7PabA1S47Z4A1A3A3").
Definition e_pmem : sv := SAlu ALU_ADD e_parbase (SLit (-16)).
Definition e_parea : sv := SAlu ALU_AND (v 172) (SLit 18446744073709547520).
Lemma ze_parbase : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S7aS82S83SbcA3SbS9cZ10A2A3F_;").
Proof using HMI Hgd Hu.
  intros H. unfold e_parbase. rewrite ze_alu, ze142, ze_alu, (ze171 H), ze_lit. cbn [zalu]. change (4 mod 2 ^ 64 mod 64) with 4.
  pose proof (zOff_eq H) as [E R]. pose proof (zM_eq H) as EM. pose proof (RQ H). pose proof R_all. pose proof (ceiling_small L).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite (Z.mod_small (zOff * 16)) by lia.
  replace (zM - zOff * 16) with (zQm + 16) by lia. apply Z.mod_small. lia.
Qed.
Lemma ze_pmem : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S7aS82S83SbeA3S9cA3F_;").
Proof using HMI Hgd Hu.
  intros H. unfold e_pmem. rewrite ze_alu, (ze_parbase H), ze_lit. cbn [zalu]. pose proof (RQ H). pose proof (ceiling_small L).
  change ((-16) mod 2 ^ 64) with (2 ^ 64 - 16). replace (zQm + 16 + (2 ^ 64 - 16)) with (zQm + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma ze_parea : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S7aS82S83SbdA3Sa9A3F_;").
Proof using HMI Hgd Hu.
  intros H. unfold e_parea. rewrite ze_alu, (ze172 H), ze_lit. cbn [zalu]. pose proof (zQ_range H) as ZR. pose proof (ceiling_small L).
  rewrite (Z.mod_small zQ) by lia.
  match goal with |- Z.land zQ ?mm = _ => replace mm with (2 ^ 64 - 2 ^ 12) by reflexivity end.
  rewrite (land_high_mask zQ 12) by lia. unfold zQa. change (2 ^ 12) with 4096. reflexivity.
Qed.

Definition pm_idx : sv := SAlu ALU_AND (v 170) (SLit 31).
Definition pm_last : sv := SAlu ALU_AND (v 169) (SLit 31).
Definition pm_sc : sv := ltac2:(tb__ "0|0|
S4eS15cS4eS15bSc7Pa9A1S47Z34A1A3S47Z3aA1A3").
Definition pm_maplen : sv := SAlu ALU_SRL (v 169) (SLit 12).
Lemma ze_pm_idx : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S7aS82S83Sc0A3S86A3F_;").
Proof using HMI Hgd Hu.
  intros H. unfold pm_idx. rewrite ze_alu, (ze170 H), ze_lit, (zHb_eq H). cbn [zalu]. change ((31 mod 2 ^ 64) mod 2 ^ 64) with (Z.ones 5). pose proof (par_last H).
  rewrite (Z.mod_small (iPar + 192)) by lia.
  rewrite Z.land_ones by lia. change (2 ^ 5) with 32. replace (iPar + 192) with (iPar + 6 * 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma pbits_decomp : ltac2:(tb__ "0|4|
S4S0S1cVam;A1Z0M0A3S5S4S0SdcS84A1SbSbSbS24S84A1M1Z20A2S10Z40S25S84A1M2A2A2S10Z1000S1cS84A1M3A2A2A3S5SaG0G3A2S5S5SaG0G1A2SaG1Z1fA2A2S5SaG0G2A2ScG2Z30A2A2A2A2A2F_;").
Proof using HMI Hgd Hu. intros H. pose proof (par_last H). pose proof (used_ranges X (Some (g, i)) U s HI gPar amPar (gPar_used H)). unfold meta_bits. lia. Qed.
Lemma ze_pm_last : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S7aS82S83Sc1A3S24S84A1A3F_;").
Proof using HMI Hgd Hu.
  intros H. unfold pm_last. rewrite ze_alu, (ze169 H), ze_lit. cbn [zalu]. change ((31 mod 2 ^ 64) mod 2 ^ 64) with (Z.ones 5). pose proof (pbits_decomp H) as (E & M & La & C).
  pose proof (RQ H) as (_ & _ & B & _). rewrite (Z.mod_small (meta_bits amPar)) by lia.
  rewrite Z.land_ones by lia. change (2 ^ 5) with 32. rewrite E.
  replace (am_last amPar + 32 + 64 * am_sc amPar + 4096 * am_maplen amPar) with (am_last amPar + (1 + 2 * am_sc amPar + 128 * am_maplen amPar) * 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma ze_pm_sc : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S7aS82S83Sc3A3S25S84A1A3F_;").
Proof using HMI Hgd Hu.
  intros H. unfold pm_sc. rewrite ze_alu, ze_alu, (ze169 H), !ze_lit. cbn [zalu].
  change (52 mod 2 ^ 64 mod 64) with 52. change (58 mod 2 ^ 64 mod 64) with 58.
  pose proof (pbits_decomp H) as (E & M & La & C). pose proof (RQ H) as (_ & _ & B & _).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite (Z.mod_small ((meta_bits amPar * 2 ^ 52) mod 2 ^ 64) (2 ^ 64)) by (apply Z.mod_pos_bound; lia).
  replace (2 ^ 64) with (2 ^ 12 * 2 ^ 52) by reflexivity. rewrite Z.mul_mod_distr_r by lia.
  replace (2 ^ 58) with (2 ^ 52 * 2 ^ 6) by reflexivity. rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia.
  rewrite E. change (2 ^ 12) with 4096. change (2 ^ 6) with 64.
  replace (am_last amPar + 32 + 64 * am_sc amPar + 4096 * am_maplen amPar) with ((am_last amPar + 32 + 64 * am_sc amPar) + am_maplen amPar * 4096) by lia.
  rewrite Z.mod_add, Z.mod_small by lia.
  replace (am_last amPar + 32 + 64 * am_sc amPar) with (am_sc amPar * 64 + (am_last amPar + 32)) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma ze_pm_maplen : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S0S7aS82S83Sc2A3S1cS84A1A3F_;").
Proof using HMI Hgd Hu.
  intros H. unfold pm_maplen. rewrite ze_alu, (ze169 H), ze_lit. cbn [zalu]. change (12 mod 2 ^ 64 mod 64) with 12.
  pose proof (pbits_decomp H) as (E & M & La & C). pose proof (RQ H) as (_ & _ & B & _). rewrite (Z.mod_small (meta_bits amPar)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096. rewrite E.
  replace (am_last amPar + 32 + 64 * am_sc amPar + 4096 * am_maplen amPar) with (am_maplen amPar * 4096 + (am_last amPar + 32 + 64 * am_sc amPar)) by lia.
  rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma bits_mod32 : ltac2:(tb__ "0|4|
S5S4S0SfS91Z20M0A2S24Vam;A1A3S5S4S0S16S91Z1000M1A2S1cVam;A1M2A3S5S4S0S16SfS91G1A2Z40A2S25Vam;A1M3A3S5S4S0S16S91G0A2SbSbZ1S10Z2G3A2A2S10Z80G2A2A2A3S4S6bS14S91Z5A2S70A3A2A2A2A2").
Proof using HMI Hgd Hu.
  pose proof R_all as R. pose proof maplen_range as Mr. rewrite Hbits.
  set (l := am_last am) in *. set (c := am_sc am) in *. set (m := am_maplen am) in *.
  assert (Hc : 0 <= c <= 63) by lia.
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
  - rewrite Z.testbit_true by lia. change (2 ^ 5) with 32.
    replace (l + 32 + 64 * c + 4096 * m) with (l + (1 + 2 * c + 128 * m) * 32) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l.
    replace (1 + 2 * c + 128 * m) with (1 + (c + 64 * m) * 2) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma ze_sc : ltac2:(tb__ "0|0|
S4S0S7aS82S83S164A3S25Vam;A1A3").
Proof using HMI Hgd Hu.
  unfold nt_sc. rewrite ze_alu, ze_alu, ze135, !ze_lit. cbn [zalu].
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
Lemma ze_last : ltac2:(tb__ "0|0|
S4S0S7aS82S83S172A3S24Vam;A1A3").
Proof using HMI Hgd Hu.
  unfold nt_last. rewrite ze_alu, ze135, ze_lit. cbn [zalu]. change (31 mod 2 ^ 64) with 31.
  pose proof bits_range. rewrite (m64_small bits) by lia. rewrite land_31. apply bits_mod32.
Qed.
Lemma ze_maplen : ltac2:(tb__ "0|0|
S4S0S7aS82S83S165A3S1cVam;A1A3").
Proof using HMI Hgd Hu.
  unfold nt_maplen. rewrite ze_alu, ze135, ze_lit. cbn [zalu]. change (12 mod 2 ^ 64 mod 64) with 12.
  pose proof bits_range. rewrite (m64_small bits) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096. apply bits_mod32.
Qed.

Lemma pow2_i_range : ltac2:(tb__ "0|2|
S5S5SaZ1SdZ2M0Vi;A2M1A2ScG1SdG0Z20A2A2A2SaG1SdG0Z1fA2A2A2").
Proof using HMI Hgd Hu.
  pose proof R_all as R. split; [split|].
  - apply Z.le_trans with (2 ^ 0); [lia|]. apply Z.pow_le_mono_r; lia.
  - apply Z.pow_lt_mono_r; lia.
  - apply Z.pow_le_mono_r; lia.
Qed.
Lemma ze_self : ltac2:(tb__ "0|0|
S4S0S7aS82S83S167A3S7dSdZ2Vi;A2A1A3").
Proof using HMI Hgd Hu.
  unfold nt_self. rewrite ze_aluw, ze13, ze_lit. cbn [zalu]. pose proof R_all as R. pose proof pow2_i_range as P.
  change (1 mod 2 ^ 64 mod 2 ^ 32) with 1. rewrite (Z.mod_small i) by lia. rewrite (Z.mod_small i) by lia.
  rewrite Z.shiftl_1_l. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ze_sx133 : ltac2:(tb__ "0|0|
S4S0S7aS82S83S54S70Q20Sc7P85A1A3A3S7dS1dVam;A1A1A3").
Proof using HMI Hgd Hu. rewrite ze_ext, ze133. reflexivity. Qed.
Lemma ze_sx134 : ltac2:(tb__ "0|0|
S4S0S7aS82S83S54S70Q20Sc7P86A1A3A3S7dS1eVam;A1A1A3").
Proof using HMI Hgd Hu. rewrite ze_ext, ze134. reflexivity. Qed.
Lemma mask_range : 0 <= mask < 2 ^ 32.
Proof using HMI Hgd Hu. unfold mask. pose proof R_all as R. apply lor_bound32; lia. Qed.
Lemma ze_mask : ltac2:(tb__ "0|0|
S4S0S7aS82S83S166A3S7dS8bA1A3").
Proof using HMI Hgd Hu.
  unfold nt_mask, mask. rewrite ze_alu, ze_sx133, ze_sx134. cbn [zalu]. pose proof R_all as R.
  pose proof (sx32_range (am_avail am)). pose proof (sx32_range (am_freed am)).
  rewrite !Z.mod_small by lia. apply sx32_lor; lia.
Qed.
Lemma mask_bit_clear : ltac2:(tb__ "0|0|
S4S6bS14S8bVi;A2S76A3").
Proof using HMI Hu. pose proof Hres as (_ & _ & Hal). unfold allocated in Hal. unfold mask. destruct (Z.testbit _ i); [discriminate|reflexivity]. Qed.
Lemma mask_plus_bit : ltac2:(tb__ "0|1|
ScSbS8bSdZ2M0Vi;A2A2SdG0Z20A2A2").
Proof using HMI Hgd Hu.
  pose proof R_all as R. pose proof mask_range as LR. pose proof pow2_i_range as P.
  rewrite (lor_add_disjoint_bit _ i) by (try lia; apply mask_bit_clear).
  apply (lor_bound32 _ _ LR). lia.
Qed.
Lemma ze_maskself : ltac2:(tb__ "0|0|
S4S0S7aS82S83S57S15aS166S167A3A3S7dSbS8bSdZ2Vi;A2A2A1A3").
Proof using HMI Hgd Hu.
  rewrite ze_aluw, ze_mask, ze_self. cbn [zalu]. pose proof mask_range. pose proof pow2_i_range. pose proof mask_plus_bit.
  rewrite !sx32_mod32 by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ze_all : ltac2:(tb__ "0|1|
S4S0S7aS82S83S171A3S7dS12SdZ2SbS24Vam;A1Z1M0A2A2G0A2A1A3").
Proof using HMI Hgd Hu.
  unfold nt_all. rewrite ze_aluw, ze_aluw, ze135, !ze_lit. cbn [zalu]. pose proof R_all as R. pose proof bits_range as B. pose proof bits_mod32 as (M & _).
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
Lemma ones_eq' : ltac2:(tb__ "0|2|
S4S0S2dS24Vam;A1M0A1S12SdZ2SbG0Z1M1A2A2G1A2A3").
Proof using . reflexivity. Qed.

Hypothesis Hsp : ltac2:(tb__ "0|1|
S5SaZ1000Sd0Q40S4aVrho;PaA2A2M0A2S4S0SfG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S5SaS7eZ40Sd0Q40S4aVrho;PfA2A2A2M0N60A2SaS13SdZ2Z28A2A1G0A2A2").

Ltac zfact := cbn [zholds zcond].

Lemma sx32_inj_small a b : ltac2:(tb__ "0|2|
S5SaZ0M0Va;A2ScVa;SdZ2Z20A2M1A2A2S5SaG0Vb;A2ScVb;G1A2A2S4S0S7dVa;A1S7dVb;A1A3S4S0Va;Vb;A3F_;F_;F_;").
Proof using Hgd rho. intros Ha Hb E. rewrite <- (sx32_mod32 a), <- (sx32_mod32 b) by lia. rewrite E. reflexivity. Qed.

Lemma ZF_base : ltac2:(tb__ "0|0|
S156S50S7bS82S83A2S169A3").
Proof using HMI HP12 Hdepth Hgd Hsp Hu.
  pose proof R_all as R. pose proof Hsp as [S1 S2]. pose proof Hdepth as [D1 D2]. unfold F_base.
  constructor. { zfact. rewrite zr1_10. split; [lia|]. change (2 ^ 4) with 16. pose proof (urange (rw rho 10)). rewrite (Z.mod_small _ (2 ^ 64)) by lia. exact S2. }
  constructor. { zfact. rewrite ze_lit, ze_var, zr1_10. change (4096 mod 2 ^ 64) with 4096. pose proof (urange (rw rho 10)). rewrite Z.mod_small by lia. lia. }
  constructor. { zfact. rewrite ze13, ze_lit. change (31 mod 2 ^ 64) with 31. lia. }
  constructor. { zfact. rewrite zr1_12. split; [lia|]. change (2 ^ 3) with 8. rewrite (Z.mod_small _ (2 ^ 64)) by lia. lia. }
  constructor. { zfact. rewrite ze_lit, ze12. change (0 mod 2 ^ 64) with 0. rewrite (proj2 (Z.eqb_neq 0 zG)) by lia. discriminate. }
  constructor. { zfact. rewrite ze12, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite (proj2 (Z.eqb_neq zG 0)) by lia. discriminate. }
  constructor. { zfact. rewrite ze_lit, ze_var, zr1_15. rewrite (toS_mod 64 (bv_unsigned (rw rho 15%positive))) by lia.
                 replace (toS 64 ((-96) mod 2 ^ 64)) with (-96) by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze_lit, ze_var, zr1_15. rewrite (toS_mod 64 (bv_unsigned (rw rho 15%positive))) by lia.
                 replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor.
Qed.

Lemma ZF_freeable : ltac2:(tb__ "0|0|
S7bS82S83S16aA3").
Proof using HMI Hgd Hu.
  unfold F_freeable. zfact. rewrite ze_alu, ze135, !ze_lit. cbn [zalu]. change (32 mod 2 ^ 64) with 32. change (0 mod 2 ^ 64) with 0.
  pose proof bits_range. rewrite (m64_small bits) by lia.
  pose proof bits_mod32 as (_ & _ & _ & _ & T5).
  assert (NZ : Z.land bits 32 <> 0).
  { intros E. assert (B : Z.testbit (Z.land bits 32) 5 = false) by (rewrite E; reflexivity).
    rewrite Z.land_spec, T5 in B. cbn in B. discriminate. }
  change (32 mod 2 ^ 64) with 32. rewrite (proj2 (Z.eqb_neq _ _) NZ). discriminate.
Qed.

Lemma ZF_notall : ltac2:(tb__ "0|0|
S7S4S0SbS8bS2fVi;A1A2S2dS24Vam;A1A1A3A1S7bS82S83S16dA3F_;").
Proof using HMI Hgd Hsp Hu.
  intros Hna. unfold F_notall. zfact. rewrite ze_maskself, ze_all. pose proof R_all as R. pose proof mask_range. pose proof mask_plus_bit. pose proof pow2_i_range.
  rewrite <- ones_eq'. unfold bit in Hna. pose proof (ones_u32 (am_last am) ltac:(lia)).
  apply Bool.negb_true_iff. apply Z.eqb_neq. intros E. apply Hna. apply (sx32_inj_small (mask + 2 ^ i) (ones (am_last am))); [lia | lia | exact E].
Qed.

Lemma ZF_maskN0 : ltac2:(tb__ "0|0|
S7S4S0S8bZ0A3A1S7bS82S83S16cA3F_;").
Proof using HMI Hgd Hu.
  intros Hm. unfold F_maskN0. zfact. rewrite ze_mask, ze_lit. change (0 mod 2 ^ 64) with 0. pose proof mask_range.
  apply Bool.negb_true_iff. apply Z.eqb_neq. intros E. apply Hm. apply (sx32_inj_small mask 0); [lia | lia | rewrite E; reflexivity].
Qed.

Lemma ZF_or : ltac2:(tb__ "0|0|
S7S4S0S8bZ0A3A1S7S4S0SbS8bS2fVi;A1A2S2dS24Vam;A1A1A3A1S156S50S7bS82S83A2S68S170A1A3F_;F_;").
Proof using HMI HP12 Hdepth Hgd Hsp Hu.
  intros Hm Hna. change (ss_facts S_or) with ([F_freeable; F_notall; F_maskN0] ++ F_base).
  constructor; [apply ZF_freeable|]. constructor; [apply (ZF_notall Hna)|]. constructor; [apply (ZF_maskN0 Hm)|]. apply ZF_base.
Qed.

Lemma ZF_mask0 : ltac2:(tb__ "0|0|
S4S0S8bZ0A3S7bS82S83S16bA3F_;").
Proof using HMI Hgd Hu.
  intros Hm. unfold F_mask0. zfact. rewrite ze_mask, ze_lit, Hm. change (0 mod 2 ^ 64) with 0. change (sx32 0) with 0. cbn. discriminate.
Qed.
Lemma ZF_notall0 : ltac2:(tb__ "0|0|
S4S0S8bZ0A3S7S4S0SbS8bS2fVi;A1A2S2dS24Vam;A1A1A3A1S7bS82S83S16eA3F_;F_;").
Proof using HMI Hgd Hu.
  intros Hm Hna. unfold F_notall0. zfact. rewrite ze_self, ze_all. pose proof R_all as R. pose proof pow2_i_range.
  rewrite <- ones_eq'. unfold bit in Hna. rewrite Hm, Z.add_0_l in Hna. pose proof (ones_u32 (am_last am) ltac:(lia)).
  apply Bool.negb_true_iff. apply Z.eqb_neq. intros E. apply Hna. apply (sx32_inj_small (2 ^ i) (ones (am_last am))); [lia | lia | exact E].
Qed.
Lemma ze_tabidx : ltac2:(tb__ "0|0|
S5SaZ0S85A2ScS85Z30A2A2S4S0S7aS82S83S4eS15eS4eS15cSc7P87A1S47Z5A1A3S47Z7eA1A3A3S10Z2S85A2A3F_;").
Proof using HMI Hgd Hsp Hu.
  intros Hsc'. unfold sc in *. rewrite !ze_alu, ze135, !ze_lit. cbn [zalu]. pose proof bits_range as B. pose proof bits_mod32 as (_ & _ & _ & M4 & _). pose proof maplen_range.
  change ((5 mod 2 ^ 64) mod 64) with 5. change ((126 mod 2 ^ 64) mod 2 ^ 64) with 126. change (126 mod 2 ^ 64) with 126.
  rewrite (Z.mod_small bits) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. rewrite M4.
  rewrite (Z.mod_small (1 + 2 * am_sc am + 128 * am_maplen am)) by lia.
  apply land_126_odd; lia.
Qed.
Lemma size_class_table_facts : ltac2:(tb__ "0|1|
S5SaZ0S85A2ScS85Z30A2A2S5S7bS82S83S58S4eS15eS4eS15cSc7P87A1S47Z5A1A3S47Z7eA1A3S47Z5eA1M0A2A3S7bS82S83S58S4eS15bS164S47Z1A1A3G0A2A3A2F_;").
Proof using HMI Hgd Hsp Hu.
  intros Hsc'. pose proof (ze_tabidx Hsc') as T. unfold sc in *. split; zfact.
  - rewrite T, ze_lit. change (94 mod 2 ^ 64) with 94. lia.
  - rewrite ze_alu, ze_sc, !ze_lit. cbn [zalu]. change (1 mod 2 ^ 64 mod 64) with 1. change (94 mod 2 ^ 64) with 94.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small; lia.
Qed.
Lemma ZF_sc48 : ltac2:(tb__ "0|0|
S5SaZ0S85A2ScS85Z30A2A2S156S50S7bS82S83A2S16fA3F_;").
Proof using HMI Hgd Hsp Hu.
  intros Hsc'. destruct (size_class_table_facts Hsc') as [T1 T2]. unfold F_sc48. pose proof Hsc' as Hsc''. unfold sc in Hsc''.
  constructor. { zfact. rewrite ze_lit, ze_sc. change (47 mod 2 ^ 64) with 47. intros E. apply Z.ltb_lt in E. lia. }
  constructor. { zfact. rewrite ze_sc, ze_lit. change (48 mod 2 ^ 64) with 48. apply Z.ltb_lt. lia. }
  constructor; [exact T1|]. constructor; [exact T2|]. constructor.
Qed.
Lemma ZF_q_links0 : ltac2:(tb__ "0|3|
S4S6cS1bA1M0S21Vam;A1S73S1bA1M1A3S4G0S20Vam;A1G1A3S156S50S7bS82S83A2S6fS50S4fS159Sc7P8dA1S47Z0A1M2A3S6fS50S4fS159Sc7P8cA1G2A3S72S50A1A3A3A3F_;F_;").
Proof using HMI Hgd Hu.
  intros Hp Hn. constructor; [|constructor; [|constructor]]; zfact.
  - rewrite ze141, ze_lit. unfold zNx. rewrite Hn. reflexivity.
  - rewrite ze140, ze_lit. unfold zPv. rewrite Hp. reflexivity.
Qed.
Lemma ZF_h_facts h : ltac2:(tb__ "0|4|
S5SaZ0M0S85A2ScS85Z30A2A2S4S6cS1bA1M1Se1Vs;S85A2S6aS1bVh;A2A3S4G1S21Vam;A1S73S1bA1M2A3S4G1S20Vam;A1G2A3S156S50S7bS82S83A2S6fS50S51S4fS159Sc7P96A1M3Sc7PcA1A3A1S6fS50S51S4fS159G3S47G0A1A3A1S72S50A1A3A3A3F_;F_;F_;F_;").
Proof using HMI HP12 Hgd Hsp Hu.
  intros Hsc' Hhd Hp Hn. pose proof (zH_eq h Hhd) as EH. destruct (h_used Hsc' h Hhd) as (Huh & _).
  pose proof (used_addrs X (Some (g, i)) U s HI C_U L vm HL HV HLG h _ Huh) as (B1 & _).
  pose proof (h_ne_g Hsc' h Hhd Hp Hn) as NE.
  constructor; [|constructor; [|constructor]]; zfact.
  - rewrite ze150, ze12, EH. unfold zG. intros E. apply Z.eqb_eq in E.
    pose proof (meta_ranges_disjoint X (Some (g, i)) U s L HI HL h g (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ Huh))) g_key NE). unfold META_SIZE in *. lia.
  - rewrite ze150, ze_lit, EH. change (0 mod 2 ^ 64) with 0. unfold PGSZ in B1. intros E. apply Z.eqb_eq in E. lia.
Qed.

Lemma ZF_all : ltac2:(tb__ "0|0|
S4S0SbS8bS2fVi;A1A2S2dS24Vam;A1A1A3S7bS82S83S168A3F_;").
Proof using HMI Hgd Hu.
  intros Hall. unfold F_all. zfact. rewrite ze_maskself, ze_all. rewrite <- ones_eq'. unfold bit in Hall. rewrite Hall.
  rewrite Z.eqb_refl. cbn. discriminate.
Qed.
Lemma ZF_sc63 : ltac2:(tb__ "0|0|
S4S0S25Vam;A1Z3fA3S7bS82S83S4fS15dS47Z2fA1S164A3A3F_;").
Proof using HMI Hgd Hu. intros H63. zfact. rewrite ze_lit, ze_sc, H63. reflexivity. Qed.
Lemma ZF_maplenN0 : ltac2:(tb__ "0|1|
S7S4S0S1cVam;A1Z0M0A3A1S7bS82S83S51S4fS159S165S47G0A1A3A1A3F_;").
Proof using HMI Hgd Hu.
  intros Hml. zfact. rewrite ze_maplen, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite (proj2 (Z.eqb_neq _ _) Hml). discriminate.
Qed.
Lemma ZF_next0 : ltac2:(tb__ "0|0|
S4S6cS1bA1S20Vam;A1S73S1bA1A3S7bS82S83S4fS159Sc7P8dA1S47Z0A1A3A3F_;").
Proof using HMI Hgd Hu. intros Hn. zfact. rewrite ze141, ze_lit. unfold zNx. rewrite Hn. reflexivity. Qed.
Lemma ZF_fmN0 : ltac2:(tb__ "0|0|
S7S4S6cS1bA1S26Vs;A1S73S1bA1A3A1S7bS82S83S51S4fS159Sc7Pa0A1S47Z0A1A3A1A3F_;").
Proof using HMI Hgd Hu.
  intros Hfh. zfact. rewrite ze160, ze_lit. change (0 mod 2 ^ 64) with 0. unfold zF.
  destruct (st_free_meta_head s) as [fm|] eqn:E; [|exfalso; exact (Hfh eq_refl)]. cbn [optrA].
  pose proof (fmem_range fm (fmem_head fm E)). rewrite (proj2 (Z.eqb_neq _ _)) by lia. discriminate.
Qed.
Lemma ZF_fm_ne_ft : ltac2:(tb__ "0|0|
S7S4S6cS1bA1S26Vs;A1S73S1bA1A3A1S7S4S1bS9dS96A3A1S7bS82S83S51S4fS159Sc7Pa0A1Sc7Pa1A1A3A1A3F_;F_;").
Proof using HMI Hgd Hsp Hu.
  intros Hfh Hne. zfact. rewrite ze160, ze161. unfold zF, zFp.
  destruct fmL_cases as [(E & _) | (fm & pr & nx & E & Efm & Hfm & M & EL & Hpr & _ & Eft & _)]; [exfalso; exact (Hfh E)|].
  rewrite E, EL. cbn [optrA fst]. rewrite Eft, Efm in Hne.
  destruct (fmem_facts fm Hfm) as (_ & _ & _ & _ & _ & Kfm & _). destruct (fmem_facts pr Hpr) as (_ & _ & _ & _ & _ & Kpr & _).
  pose proof (meta_ranges_disjoint X (Some (g, i)) U s L HI HL fm pr Kfm Kpr ltac:(intros EE; apply Hne; symmetry; exact EE)) as D.
  unfold META_SIZE in D. rewrite (proj2 (Z.eqb_neq _ _)) by lia. discriminate.
Qed.

Lemma mnext_mprev_g : ltac2:(tb__ "0|2|
S9S7S4S6cS1bA1M0S21Vam;A1S73S1bA1M1A3A1S7S4G0S20Vam;A1G1A3A1A2S4S1bS18dVs;S18eVs;Vg;A2A2Vg;A3F_;").
Proof using HMI Hgd Hu rho.
  intros Hl. destruct (linked_ring Hl) as (c & m0 & rest & Hc & Ec & Hhd & Rg & Hin).
  destruct (In_nth _ _ m0 Hin) as (k & Hk & Ek).
  destruct (ring_pos X s c m0 Hc rest Rg k Hk) as [N P]. rewrite Ek in N, P. rewrite P.
  destruct k as [|j].
  - rewrite (ring_next_last X s c m0 Hc rest Rg). cbn in Ek. exact Ek.
  - destruct (ring_pos X s c m0 Hc rest Rg j ltac:(cbn [length] in Hk |- *; lia)) as [N2 _]. rewrite N2. exact Ek.
Qed.
Lemma links_both : ltac2:(tb__ "0|4|
S9S7S4S6cS1bA1M0S21Vam;A1M1S73S1bA1M2A3A1S7S4G0S20Vam;A1M3G2A3A1A2S6S1bS1bS6S1bS1bS5S4G0G1S6aS1bR2A2A3S4G0G3S6aS1bR1A2A3A2Ln;A2Lp;A2F_;").
Proof using HMI Hgd Hu.
  intros Hl. destruct (linked_ring Hl) as (c & m0 & rest & Hc & Ec & Hhd & Rg & Hin).
  destruct (ring_links _ _ _ _ Rg Hin) as (pr & nx & HLk). unfold alinks, MTX in HLk.
  destruct (memb g X); [discriminate|]. rewrite HMg_inst in HLk.
  destruct (am_sc am =? c); [|discriminate]. injection HLk as E1 E2. exists pr, nx. auto.
Qed.
Lemma prev_ne_g n : ltac2:(tb__ "0|1|
S4S6cS1bA1M0S20Vam;A1S6aS1bVn;A2A3S7S4S1bVn;Vg;A3A1S6S1bS1bS5S4G0S21Vam;A1S6aS1bR1A2A3S7S4S1bR1Vg;A3A1A2Lp;A2F_;F_;").
Proof using HMI Hgd Hu rho.
  intros En Hng. destruct (links_both ltac:(right; rewrite En; discriminate)) as (p & n' & Ep & En').
  exists p. split; [exact Ep|]. intros ->.
  pose proof (mnext_mprev_g ltac:(right; rewrite En; discriminate)) as M. unfold mprev, mrec in M. rewrite HMg_inst, Ep in M.
  unfold mnext, mrec in M. rewrite HMg_inst, En in M. exact (Hng M).
Qed.

Lemma nonhead_avail0 q a : ltac2:(tb__ "0|1|
SdbVX;Vs;Vq;Va;A4S4S0S25Va;A1S85A3S5SaZ0M0S85A2ScS85Z30A2A2S7S4S6cS1bA1Se1Vs;S85A2S6aS1bVq;A2A3A1S4S0S1dVa;A1G0A3F_;F_;F_;F_;").
Proof using HMI.
  intros Hq Hs Hsc' Hnh. destruct (inv_rings HI) as (_ & A & _). destruct (A sc Hsc') as (ms & Rg & Mem & Off & R1 & _).
  destruct (Z.eq_dec (am_avail a) 0) as [E|NE]; [exact E|]. exfalso. apply Hnh. exact (R1 q a Hq Hs NE).
Qed.

Lemma ZF_hd_g : ltac2:(tb__ "0|0|
S4S6cS1bA1Se1Vs;S85A2S6aS1bVg;A2A3S7bS82S83S4fS159Sc7P96A1Sc7PcA1A3A3F_;").
Proof using HMI HP12 Hgd Hu. intros Hhd. zfact. rewrite ze150, ze12. unfold zH. rewrite Hhd. cbn [optrA]. unfold zG. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma ZF_hd_ng : ltac2:(tb__ "0|0|
S5SaZ0S85A2ScS85Z30A2A2S7S4S6cS1bA1Se1Vs;S85A2S6aS1bVg;A2A3A1S7bS82S83S51S4fS159Sc7P96A1Sc7PcA1A3A1A3F_;F_;").
Proof using HMI HP12 Hgd Hsp Hu.
  intros Hsc' Hhd. zfact. rewrite ze150, ze12. pose proof R_all as R. unfold zH, zG in *.
  destruct (active_hd s sc) as [h|] eqn:E; cbn [optrA].
  - destruct (h_used Hsc' h E) as (Huh & _).
    assert (NE : h <> g) by (intros ->; apply Hhd; reflexivity).
    pose proof (meta_ranges_disjoint X (Some (g, i)) U s L HI HL h g (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ Huh))) g_key NE). unfold META_SIZE in *.
    rewrite (proj2 (Z.eqb_neq _ _)) by lia. discriminate.
  - rewrite (proj2 (Z.eqb_neq _ _)) by lia. discriminate.
Qed.
Lemma nQ_eq n : ltac2:(tb__ "0|0|
S4S6cS1bA1S20Vam;A1S6aS1bVn;A2A3S4S1bSb5Vn;A3F_;"). Proof using . intros E. unfold nQ. rewrite E. reflexivity. Qed.
Lemma pQ_eq p : ltac2:(tb__ "0|0|
S4S6cS1bA1S21Vam;A1S6aS1bVp;A2A3S4S1bSb6Vp;A3F_;"). Proof using . intros E. unfold pQ. rewrite E. reflexivity. Qed.
Lemma zNx_eq n : ltac2:(tb__ "0|0|
S4S6cS1bA1S20Vam;A1S6aS1bVn;A2A3S4S0S9aSd2VL;Vn;A2A3F_;"). Proof using . intros E. unfold zNx. rewrite E. reflexivity. Qed.
Lemma zPv_eq p : ltac2:(tb__ "0|0|
S4S6cS1bA1S21Vam;A1S6aS1bVp;A2A3S4S0S9bSd2VL;Vp;A2A3F_;"). Proof using . intros E. unfold zPv. rewrite E. reflexivity. Qed.
Lemma ZF_n_ne_g n : ltac2:(tb__ "0|0|
S4S6cS1bA1S20Vam;A1S6aS1bVn;A2A3S7S4S1bVn;Vg;A3A1S7bS82S83S4fS161Sc7P8dA1Sc7PcA1A3A3F_;F_;").
Proof using HMI HP12 Hgd Hsp Hu.
  intros En Hng. zfact. rewrite ze141, ze12, (zNx_eq n En). unfold zG in *.
  pose proof nQ_used as Un. rewrite (nQ_eq n En) in Un.
  pose proof (meta_ranges_disjoint X (Some (g, i)) U s L HI HL n g (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ Un))) g_key Hng). unfold META_SIZE in *.
  apply Bool.negb_true_iff. apply Z.eqb_neq. lia.
Qed.
Lemma ZF_n_nz n : ltac2:(tb__ "0|0|
S4S6cS1bA1S20Vam;A1S6aS1bVn;A2A3S7bS82S83S51S4fS159Sc7P8dA1S47Z0A1A3A1A3F_;").
Proof using HMI Hgd Hu.
  intros En. zfact. rewrite ze141, ze_lit, (zNx_eq n En). change (0 mod 2 ^ 64) with 0.
  pose proof nQ_used as Un. rewrite (nQ_eq n En) in Un. pose proof (used_addrs X (Some (g, i)) U s HI C_U L vm HL HV HLG n _ Un) as (B1 & _). unfold PGSZ in B1.
  rewrite (proj2 (Z.eqb_neq _ _)) by lia. discriminate.
Qed.
Lemma ZF_align141 n : ltac2:(tb__ "0|0|
S4S6cS1bA1S20Vam;A1S6aS1bVn;A2A3S7bS82S83S55P8dZ3A2A3F_;").
Proof using HMI Hgd Hsp Hu.
  intros En. zfact. rewrite zr1_141, (zNx_eq n En). pose proof nQ_used as Un. rewrite (nQ_eq n En) in Un.
  pose proof (used_addrs X (Some (g, i)) U s HI C_U L vm HL HV HLG n _ Un) as (B1 & B2 & B3 & _). pose proof (ceiling_small L).
  split; [lia|]. change (2 ^ 3) with 8. rewrite (Z.mod_small _ (2 ^ 64)) by (unfold PGSZ, META_SIZE in *; lia). exact B3.
Qed.
Lemma ZF_align140 p : ltac2:(tb__ "0|0|
S4S6cS1bA1S21Vam;A1S6aS1bVp;A2A3S7bS82S83S55P8cZ3A2A3F_;").
Proof using HMI Hgd Hsp Hu.
  intros Ep. zfact. rewrite zr1_140, (zPv_eq p Ep). pose proof pQ_used as Upp. rewrite (pQ_eq p Ep) in Upp.
  pose proof (used_addrs X (Some (g, i)) U s HI C_U L vm HL HV HLG p _ Upp) as (B1 & B2 & B3 & _). pose proof (ceiling_small L).
  split; [lia|]. change (2 ^ 3) with 8. rewrite (Z.mod_small _ (2 ^ 64)) by (unfold PGSZ, META_SIZE in *; lia). exact B3.
Qed.
Lemma ZF_align156 : ltac2:(tb__ "0|0|
S7bS82S83S55P9cZ4A2A3").
Proof using HMI Hgd Hsp Hu.
  zfact. rewrite zr1_156. unfold zNm. pose proof (used_addrs X (Some (g, i)) U s HI C_U L vm HL HV HLG nQ _ nQ_used) as (_ & _ & _ & _ & B5 & B6 & B7 & _). pose proof (ceiling_small L).
  pose proof RN as R'. unfold zNm in R'.
  split; [lia|]. change (2 ^ 4) with 16. rewrite (Z.mod_small _ (2 ^ 64)) by lia. exact B7.
Qed.
Lemma ZF_p_ne_n p n : ltac2:(tb__ "0|1|
S4S6cS1bA1M0S21Vam;A1S6aS1bVp;A2A3S4G0S20Vam;A1S6aS1bVn;A2A3S7S4S1bVp;Vn;A3A1S7bS82S83S51S4fS159Sc7P8cA1Sc7P8dA1A3A1A3F_;F_;F_;").
Proof using HMI Hgd Hsp Hu.
  intros Ep En Hpn. zfact. rewrite ze140, ze141, (zPv_eq p Ep), (zNx_eq n En).
  pose proof nQ_used as Un. rewrite (nQ_eq n En) in Un. pose proof pQ_used as Up. rewrite (pQ_eq p Ep) in Up.
  pose proof (meta_ranges_disjoint X (Some (g, i)) U s L HI HL p n (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ Up))) (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ Un))) Hpn). unfold META_SIZE in *.
  rewrite (proj2 (Z.eqb_neq _ _)) by lia. discriminate.
Qed.
Lemma ze_scm7 : ltac2:(tb__ "0|0|
S4S0S7aS82S83S4eS15aS164S47N7A1A3A3SfS12S85Z7A2SdZ2Z40A2A2A3").
Proof using HMI Hgd Hu.
  rewrite ze_alu, ze_sc, ze_lit. cbn [zalu]. unfold sc. pose proof R_all.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma ZF_notbnc : ltac2:(tb__ "0|0|
S9ScS85Z7A2SaZ27S85A2A2S5SaZ0S85A2ScS85Z30A2A2S7bS82S83S4fS15dS47Z1fA1S4eS15aS164S47N7A1A3A3A3F_;F_;").
Proof using HMI Hgd Hu.
  intros Hr Hsc'. zfact. rewrite ze_lit, ze_scm7. change (31 mod 2 ^ 64) with 31. apply Z.ltb_lt.
  destruct Hr as [Hr|Hr]; [|rewrite Z.mod_small by lia; lia].
  replace ((sc - 7) mod 2 ^ 64) with (2 ^ 64 + (sc - 7)) by (symmetry; rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small by lia; lia). lia.
Qed.
Lemma ZF_bncrng : ltac2:(tb__ "0|0|
S5SaZ7S85A2ScS85Z27A2A2S7bS82S83S51S4fS15dS47Z1fA1S4eS15aS164S47N7A1A3A3A1A3F_;").
Proof using HMI Hgd Hu.
  intros Hr. zfact. rewrite ze_lit, ze_scm7. change (31 mod 2 ^ 64) with 31. rewrite Z.mod_small by lia.
  intros E. apply Z.ltb_lt in E. lia.
Qed.

End Inst.
End Mal_nt_I.

Module Mal_nt_Ib.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Inst.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
S186Sd3VX;S6aS71S1bS0A2S6dS1bS0Vg;Vi;A4A2VU;S185Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Local Abbreviation HXr := (@U.Mal_nt__G1.Mal_nt_I.HXr s X HXz).
Hypothesis Hu : ltac2:(tb__ "0|0|
SdbVX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Notation "§1§ h__" := (h__ s L X U g i vm rd0 wok0 HMI) (at level 10, h__ global).
Local Abbreviation HI := (§1§ U.Mal_nt__G1.Mal_nt_I.HI).
Local Abbreviation HL := (§1§ U.Mal_nt__G1.Mal_nt_I.HL).
Local Abbreviation HV := (§1§ U.Mal_nt__G1.Mal_nt_I.HV).
Local Abbreviation HLG := (§1§ U.Mal_nt__G1.Mal_nt_I.HLG).
Local Abbreviation Hctx := (§1§ U.Mal_nt__G1.Mal_nt_I.Hctx).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S4S0Sd0Q40S4aVrho;PcA2A2Sd2VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S4S0Sd0Q40S4aVrho;PdA2A2Vi;A3").
Local Abbreviation g_key := (@U.Mal_nt__G1.Mal_nt_I.g_key s X g am Hu).
Local Notation "§2§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation R_all := (§2§ U.Mal_nt__G1.Mal_nt_I.R_all).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Abbreviation zH := (@U.Mal_nt__G1.Mal_nt_I.zH s L am).
Local Abbreviation zH_range := (§2§ U.Mal_nt__G1.Mal_nt_I.zH_range).
Local Abbreviation zF := (@U.Mal_nt__G1.Mal_nt_I.zF s L).
Local Abbreviation zSeq := (@U.Mal_nt__G1.Mal_nt_I.zSeq s).
Local Notation "§3§ h__" := (h__ s L X U g i gd vm rd0 wok0 HMI Hgd) (at level 10, h__ global).
Local Abbreviation useq_byte := (§3§ U.Mal_nt__G1.Mal_nt_I.useq_byte).
Local Abbreviation useq_bytes := (@U.Mal_nt__G1.Mal_nt_I.useq_bytes s).
Local Abbreviation useq_dw := (@U.Mal_nt__G1.Mal_nt_I.useq_dw s).
Local Abbreviation useq_dw_enc := (@U.Mal_nt__G1.Mal_nt_I.useq_dw_enc s).
Local Abbreviation rl1 := (@U.Mal_nt__G1.Mal_nt_I.rl1 rho).
Local Notation "§4§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§4§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation zr1 := (§4§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§4§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation zr1_zl1_any := (§4§ U.Mal_nt__G1.Mal_nt_I.zr1_zl1_any).
Local Abbreviation links_used_range' := (§3§ U.Mal_nt__G1.Mal_nt_I.links_used_range').
Local Abbreviation rec_ranges := (§3§ U.Mal_nt__G1.Mal_nt_I.rec_ranges).
Local Abbreviation ze_lit := (§4§ U.Mal_nt__G1.Mal_nt_I.ze_lit).
Local Abbreviation ze_alu := (§4§ U.Mal_nt__G1.Mal_nt_I.ze_alu).
Local Abbreviation ze143 := (@U.Mal_nt__G1.Mal_nt_I.ze143 s L g am i rho gd rd0 Hgd).
Local Abbreviation ze_sc := (@U.Mal_nt__G1.Mal_nt_I.ze_sc s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S5SaZ1000Sd0Q40S4aVrho;PaA2A2M0A2S4S0SfG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S5SaS7eZ40Sd0Q40S4aVrho;PfA2A2A2M0N60A2SaS13SdZ2Z28A2A1G0A2A2").

Ltac zfact := cbn [zholds zcond].

Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S4SceQ40A1S6cSceQ8A1A1F_;Vrd0;S135Sc8VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S4SceQ40A1S6bF_;Vwok0;S136Sc8VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S0S5SaZ0R1A2ScR1Z60A2A2S4S6cSceQ8A1M0A1VmV;ScfQ40SbZ108ecR2A2A2A1S73G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
Sd5Sd4Vrd0;SceQ40A1S70L_;A2Sd6Sd3A1U8Vgd;A4").

Let bv0 : byteview := ltac2:(tb__ "0|0|
Sd4S135Sc8VmV;A2S136Sc8VmV;A2A2").
Lemma HMI0 : ltac2:(tb__ "0|0|
S186Sd3VX;S6aS71S1bS0A2S6dS1bS0Vg;Vi;A4A2VU;S185Vs;VL;A2S135Sc8VmV;A2S136Sc8VmV;A2Vvm;A8").
Proof using Erd Ewok HMI. rewrite <- Erd, <- Ewok. exact HMI. Qed.
Lemma HreprO : ltac2:(tb__ "0|0|
S1b5VL;Vs;Vbv0;A3"). Proof using Erd Ewok HMI. exact (mig_reprO HMI0). Qed.
Lemma Hstat : ltac2:(tb__ "0|0|
Sd8Sd3Sd4S135Sc8VmV;A2SceQ40A1S70L_;A2Vbv0;A3").
Proof using Erd Ewok HMI. exact (mig_statics HMI0). Qed.

Lemma cell_bytes0 : ltac2:(tb__ "0|4|
SdaS0Sc9SdaR2SddVs;A1A3S4S6cS0A1S187VL;R3A2S6aS0R2A2A3S6eS162R1Se7R5A1A2S5S5SaZ0SbSe6VL;Se8R6A1A2S11R2A1A2M0A2ScG0SdZ2Z40A2A2A2S5S4S6bS136Sc8VmV;ScfQ40G0A2M1A3S70A3S4S6cSceQ8M2A1M3A1S135Sc8VmV;G1A3S6aG3ScfG2Se4R5Se7R6A1R2A3A2A2A3A2A2F_;Fj;F_;F_;Fz;Fc;").
Proof using Erd Ewok HMI.
  intros c z Hc Hz j Hj.
  assert (CH : MallocInv.cell_holds L bv0 c) by exact (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 HreprO))) c Hc).
  exact (cell_bytes L _ _ c z CH Hz j Hj).
Qed.
Lemma cell_rw0 : ltac2:(tb__ "0|3|
SdaS0S0S0S6eSc9SdaR5SddVs;A1A3S4S6cS0A1S187VL;R6A2S6aS0R5A2A3S4S6eSe7R7A1R3A3S4S0Se6VL;Se8R8A1A2SbR6R5A2A3S0S5SaSbR8R7A2M0R1A2ScR1SbG0S11R6A1A2A2A2S5S4S6bS136Sc8VmV;ScfQ40M1R2A2A3S70A3S6SceQ8A1M2G2S4S6cG2A1S135Sc8VmV;ScfG1R3A2A3S6aG2R1A2A3Lbb;A2A2F_;Fx;F_;F_;F_;F_;Fkk;Foffs;Fb;Fz;Fc;").
Proof using Erd Ewok HMI Hgd Hsp.
  intros c z b offs kk Hc Hz Hw Ha x Hx.
  destruct (cell_bytes0 c z Hc Hz (Z.to_nat (x - (b + offs))) ltac:(rewrite Hw; lia)) as (_ & W & R).
  rewrite Ha in W, R. rewrite Z2Nat.id in W, R by lia. replace (b + offs + (x - (b + offs))) with x in W, R by lia.
  split; [exact W | eexists; exact R].
Qed.
Lemma ev1 : ltac2:(tb__ "0|2|
SceQ40M0A1M1S6cSceQ8A1A1F_;S46S4S6bS7cR1A1S70A3S4G1S52S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R3A9R2A2ScfG0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R2A3A2A3F_;Fe;Fm;").
Proof using .
  intros m e He. rewrite <- (zr1_zl1_any m). rewrite <- (eval_zeval (rho1 m) e He). symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma ev1u : ltac2:(tb__ "0|1|
SceQ40M0A1S6cSceQ8A1A1F_;S46S4S6bS7cR1A1S70A3S4S0Sd0G0S52S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R3A9R2A2A2S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R2A3A3F_;Fe;Fm;").
Proof using . intros m e He. rewrite <- (zr1_zl1_any m). apply eval_zeval. exact He. Qed.
Lemma cell_view0 : ltac2:(tb__ "0|4|
SdaS0S0S0S6eS46Sc9SdaR6SddVs;A1A3S4S6cS0A1S187VL;R7A2S6aS0R6A2A3S4S6eSe7R8A1R4A3S163R5U8A2S4S0Se6VL;Se8RaA1A2SbR8R7A2A3S4SceQ40M0A1S52S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9M1R6A2ScfG0RaA2A3S6eS162R1R9A2S4S6cSceQ8M2A1M3A1S135Sc8VmV;ScfG0SbSbRcRbA2S11R2A1A2A2A3S6aG3S154G3R2S53RaS52G1R9A2A2ScfG2Z0A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;Fe;Fkk;Foffs;Fb;Fz;Fc;").
Proof using Erd Ewok HMI.
  intros c z b offs kk e Hc Hz Hw Hk Ha He j Hj.
  destruct (cell_bytes0 c z Hc Hz j ltac:(rewrite Hw; exact Hj)) as (_ & _ & R).
  rewrite Ha in R. rewrite R, He, Hw. rewrite nth_enc_bytes by assumption. reflexivity.
Qed.

Lemma cell_view0m : ltac2:(tb__ "0|3|
SdaS0S0S0S6eS46Sc9SdaR6SddVs;A1A3S4S6cS0A1S187VL;R7A2S6aS0R6A2A3S4S6eSe7R8A1R4A3S163R5U8A2S4S0Se6VL;Se8RaA1A2SbR8R7A2A3S4S6bS7cR6A1S70A3S4S0SfS7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R7A3SdZ2S10Z8S11R8A1A2A2M0A2SfRbG0A2A3S6eS162R1RaA2S4S6cSceQ8M1A1M2A1S135Sc8VmV;ScfQ40SbSbRdRcA2S11R2A1A2A2A3S6aG2S154G2R2S53RbS52S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9RaA2A2ScfG1Z0A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;F_;Fe;Fkk;Foffs;Fb;Fz;Fc;").
Proof using Erd Ewok HMI.
  intros c z b offs kk e Hc Hz Hw Hk Ha He Em j Hj.
  destruct (cell_bytes0 c z Hc Hz j ltac:(rewrite Hw; exact Hj)) as (_ & _ & R).
  rewrite Ha in R. rewrite R, Hw. rewrite (ev1 mV e He). rewrite nth_enc_bytes by assumption. unfold le_byte. rewrite Em. reflexivity.
Qed.
Lemma owned_rw : ltac2:(tb__ "0|2|
S0SefVL;Vs;R1A3S5S4S6bS136Sc8VmV;ScfQ40M0R2A2A3S70A3S6SceQ8A1M1G1S4S6cG1A1S135Sc8VmV;ScfG0R3A2A3S6aG1R1A2A3Lbb;A2A2F_;Fx;").
Proof using Erd Ewok HMI.
  intros x OW. pose proof (proj2 (proj2 (proj1 HreprO)) x OW) as M. unfold bv0 in M.
  destruct (byteview_of (Glue.rd_of segsU mV) (Glue.wok_of segsU mV) x) as [vv|] eqn:E; [|exfalso; exact (M eq_refl)].
  destruct (byteview_of_Some _ _ _ _ E) as (_ & W & bb & Hb & _). split; [exact W | exists bb; exact Hb].
Qed.
Lemma soff_of_ev : ltac2:(tb__ "0|0|
S46S0S4S6bS7cR2A1S70A3S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R3A3R2A3S5SaZ0R3A2ScR3SdZ2Z3fA2A2A2S4S0S5bS10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9R5A2R4A3F_;F_;F_;Fz;Fe;").
Proof using Hgd.
  intros e z Hs Hz Hr. unfold soff. rewrite (ev1 mV e Hs), Hz. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64.
  rewrite u64 by lia. unfold toS. rewrite Z.mod_small by lia. change (2 ^ (64 - 1)) with (2 ^ 63).
  replace (z <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.

Lemma rv_byte a vv : ltac2:(tb__ "0|3|
S4S6cS0A1Sd4S135Sc8VmV;A2SceQ40M0A1S70L_;Va;A3S6aS0Vvv;A2A3S4S6cSceQ8M1A1M2A1S135Sc8VmV;ScfG0Va;A2A3S6aG2ScfG1Vvv;A2A2A3F_;").
Proof using .
  intros H. destruct (byteview_of_Some _ _ _ _ H) as (_ & _ & b & Hb & E). rewrite Hb. f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. reflexivity.
Qed.

Definition O_stk : sobj := ltac2:(tb__ "0|0|
S4cS56PaA1S56PfA1S47Z0A1S72S48A1S4bA5").
Definition O_got : sobj := ltac2:(tb__ "0|2|
S4cS47Z28d50A1S47Z0A1M0S47Z8M1A1S6fS48S49G0G1S47Z5a338A1A3S72S48A1A3S4bA5").
Definition O_guard : sobj := ltac2:(tb__ "0|2|
S4cS47Z5a338A1S47Z0A1M0S47Z8M1A1S6fS48S49G0G1Sc7P8fA1A3S72S48A1A3S4bA5").
Definition O_sct : sobj := ltac2:(tb__ "0|0|
S4cS47Z108ecA1S47Z0A1S47Z60A1S72S48A1S5cP1A1A5").
Definition O_metaK (bv pv nv mv av fv bvv : sv) : sobj := ltac2:(tb__ "0|3|
S4cVbv;S47Z0A1M0S47Z28A1S6fS48S49G0Z8M1Vpv;A3S6fS48S49S47G1A1G1Vnv;A3S6fS48S49S47Z10A1G1Vmv;A3S6fS48S49S47Z18A1Z4M2Vav;A3S6fS48S49S47Z1cA1G2Vfv;A3S6fS48S49S47Z20A1G1Vbvv;A3S72S48A1A3A3A3A3A3A3S4bA5").
Definition O_meta (pv nv av fv : sv) : sobj := ltac2:(tb__ "0|0|
S192Sc7PcA1Vpv;Vnv;Sc7P8eA1Vav;Vfv;Sc7P87A1A7").
Definition O_links (bv pv nv : sv) : sobj := ltac2:(tb__ "0|2|
S4cVbv;S47Z0A1M0S47Z10A1S6fS48S49G0Z8M1Vpv;A3S6fS48S49S47G1A1G1Vnv;A3S72S48A1A3A3S4bA5").

Lemma got_wseg : ltac2:(tb__ "0|0|
S4S6bScaS0S0S137Sc8ScfQ40R1A2A2Lx;S155S6eS0S6eSbZ28d50S11R1A1A2Lk;S157U0U8A2A4A3S70A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma guard_wseg : ltac2:(tb__ "0|0|
S4S6bScaS0S0S137Sc8ScfQ40R1A2A2Lx;S155S6eS0S6eSbZ5a338S11R1A1A2Lk;S157U0U8A2A4A3S70A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma wseg_range lo (n : nat) a : ltac2:(tb__ "0|1|
S4S6bScaS0S0S137Sc8ScfQ40M0R1A2A2Lx;S155S6eS0S6eSbVlo;S11R1A1A2Lk;S157U0Vn;A2A4A3S70A3S5SaVlo;Va;A2ScVa;SbVlo;S11Vn;A1A2A2A2S4S6bS136Sc8VmV;ScfG0Va;A2A3S70A3F_;F_;").
Proof using .
  intros H Ha. unfold Glue.wok_of. destruct (mV (Z_to_bv 64 a)); [reflexivity|].
  exact (forall_range_dec _ lo n H a Ha).
Qed.

Lemma hold_got : ltac2:(tb__ "0|0|
S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S196A4").
Proof using Erd Ewok HMI Hgd Hrom Hsp.
  change O_got with (carved (SLit 0x28d50) 0 8 [(0, 8%nat, SLit 0x5a338)]).
  assert (B : bv_unsigned (eval (rho1 mV) (SLit 0x28d50)) = 0x28d50) by (cbn [eval]; apply u64; lia).
  destruct Hstat as (_ & _ & _ & _ & _ & _ & _ & _ & (gd' & T9 & T10)).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. split; [apply (wseg_range 0x28d50 8); [apply got_wseg | cbn; lia]|].
    pose proof (T9 (Z.to_nat o) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. cbn [mc_chk_guard_got C_U] in E.
    eexists. exact (rv_byte _ _ E).
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    pose proof (T9 j Hj) as E. cbn [mc_chk_guard_got C_U] in E. rewrite (rv_byte _ _ E).
    cbn [eval]. rewrite nth_enc_bytes by lia. reflexivity.
Qed.

Lemma hold_guard : ltac2:(tb__ "0|0|
S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S197A4").
Proof using Erd Hgd Hgd_holds Hrom Hsp.
  change O_guard with (carved (SLit 0x5a338) 0 8 [(0, 8%nat, v 143)]).
  assert (B : bv_unsigned (eval (rho1 mV) (SLit 0x5a338)) = 0x5a338) by (cbn [eval]; apply u64; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. split; [apply (wseg_range 0x5a338 8); [apply guard_wseg | cbn; lia]|].
    pose proof (Hgd_holds (Z.to_nat o) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. rewrite Erd in E. cbn [mc_chk_guard C_U] in E.
    eexists. exact (rv_byte _ _ E).
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    pose proof (Hgd_holds j Hj) as E. rewrite Erd in E. cbn [mc_chk_guard C_U] in E. rewrite (rv_byte _ _ E).
    rewrite (ev1 mV (v 143) eq_refl), ze143, nth_enc_bytes by lia. reflexivity.
Qed.

Lemma sctab_image : ltac2:(tb__ "0|3|
S0S5SaZ0M0R1A2ScR1Z60A2A2S4S6cSceQ8M1A1M2A1S60Sc8ScfQ40SbZ108ecR2A2A2A2S6aG2S154G2S15R2A1S59S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9P1A2ScfG1G0A2A4A2A3F_;Fkk;").
Proof using Hgd.
  intros kk Hk.
  pose proof (forall_range_dec (fun kk => match image_byte segsU (Z_to_bv 64 (0x108ec + kk)) with
                                         | Some b => bv_eqb b (nth (Z.to_nat kk) (map (Z_to_bv 8) size_classes_bytes) (Z_to_bv 8 0))
                                         | None => false end) 0 96 ltac:(vm_compute; reflexivity) kk ltac:(lia)) as H.
  cbn beta in H. cbn [rl rho1 rl1 Pos.eqb].
  destruct (image_byte segsU (Z_to_bv 64 (67820 + kk))) as [b|]; [|discriminate].
  f_equal. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.
Lemma hold_sct : ltac2:(tb__ "0|0|
S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S198A4").
Proof using Hgd Hm_sct Hrom.
  unfold O_sct. apply obj_holds_frame_rom; try exact Hrom; try lia.
  - reflexivity.
  - intros kk Hk. split; [apply Hm_sct; exact Hk | apply sctab_image; exact Hk].
Qed.

Lemma ctx_owned off : ltac2:(tb__ "0|0|
S5SaZ0Voff;A2ScVoff;Sf2A2A2SefVL;Vs;SbS107VL;A1Voff;A2A3F_;").
Proof using HMI HXz Hgd Hsp.
  intros Ho. split.
  - exists (LCtx 0, CTX_SIZE). split; [left; reflexivity|]. cbn [fst snd loc_addr]. lia.
  - intros (b & Hb & Hx). cbn [fst snd] in Hx.
    destruct (user_block_in_group X (Some (g, i)) U s L HI HXr b Hb) as (g' & am' & i' & fr & Hg & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
    destruct (group_range X (Some (g, i)) U s L HI HL C_U vm g' am' Hg HV HLG) as (_ & _ & _ & D).
    pose proof (stride_pos _ _ _ _ _ (inv_groups HI g' am' Hg)) as Sp. assert (0 <= stride_of am' * i') by nia.
    rewrite Eb in Hx, B1, B2. cbn [fst snd] in Hx, B1, B2. unfold addr_of in *. unfold UNIT, IB, CTX_SIZE in *. lia.
Qed.

Lemma meta_cell_In c : ltac2:(tb__ "0|0|
Sc9SdaVc;S109Vg;S6aS1fS2cVam;A1A2A2A3Sc9SdaVc;SddVs;A1A3F_;").
Proof using HMI Hu. intros Hc. apply (meta_cells_in_imageI X (Some (g, i)) U s HI g c g_key). rewrite (proj1 (usedX_MT _ _ _ _ Hu)). exact Hc. Qed.

Lemma cellZ_optr o lc w : ltac2:(tb__ "0|0|
S4S6cS0A1S187VL;SdeVlc;Vw;Sf1Vo;A1A3A2S6aS0S10bVL;Vo;A2A2A3").
Proof using . destruct o; reflexivity. Qed.

Lemma hold_metaK (q : sptr) (a : ameta) (bv pv nv mv av fv bvv : sv) : ltac2:(tb__ "0|3|
SdbVX;Vs;Vq;Va;A4S4S6bS7cVbv;A1S70A3S4S6bS7cVpv;A1S70A3S4S6bS7cVnv;A1S70A3S4S6bS7cVmv;A1S70A3S4S6bS7cVav;A1S70A3S4S6bS7cVfv;A1S70A3S4S6bS7cVbvv;A1S70A3S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M0S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M1Vbv;A3Sd2VL;Vq;A2A3S4S0S7aG0G1Vpv;A3S10bVL;S21Va;A1A2A3S4S0S7aG0G1Vnv;A3S10bVL;S20Va;A1A2A3S4S0S7aG0G1Vmv;A3Sd2VL;S23Va;A1A2A3S4S0SfS7aG0G1Vav;A3SdZ2Z20A2M2A2S1dVa;A1A3S4S0SfS7aG0G1Vfv;A3G2A2S1eVa;A1A3S4S0S7aG0G1Vbvv;A3SdcVa;A1A3S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S192Vbv;Vpv;Vnv;Vmv;Vav;Vfv;Vbvv;A7A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using Erd Ewok HMI Hdepth Hgd Hrom Hsp.
  intros Hq Sb Sp Sn Sm Sa Sf Sbb Eb Ep En Em Ea Ef Ebb. pose proof (rec_ranges q a Hq) as (R1 & R2 & R3 & R4 & R5). pose proof (ceiling_small L) as CS.
  pose proof (used_addrs X (Some (g, i)) U s HI C_U L vm HL HV HLG q a Hq) as (B1 & B2 & _).
  destruct (links_used_range' q a Hq) as [[P1 P2] [N1 N2]].
  change (O_metaK bv pv nv mv av fv bvv) with (carved bv 0 40 [(0, 8%nat, pv); (8, 8%nat, nv); (16, 8%nat, mv); (24, 4%nat, av); (28, 4%nat, fv); (32, 8%nat, bvv)]).
  assert (B : bv_unsigned (eval (rho1 mV) bv) = addr_of L q) by (rewrite ev1u by exact Sb; exact Eb).
  assert (AG : forall d, loc_addr L (LMem (padd q d)) = addr_of L q + d) by (intros d; unfold addr_of, loc_addr; destruct q; cbn [padd]; lia).
  pose proof (proj1 (usedX_MT _ _ _ _ Hq)) as Mq. pose proof (MT_Some_In_keys _ _ _ Mq) as Kq.
  pose proof (fun c Hc => meta_cells_in_imageI X (Some (g, i)) U s HI q c Kq Hc) as MI. rewrite Mq in MI. cbn [meta_slot_cells] in MI.
  assert (C0 : In (MCell (LMem (padd q META_prev)) 8 (MallocInv.optr (am_prev a))) (image s)) by (apply MI; cbn; tauto).
  assert (C1 : In (MCell (LMem (padd q META_next)) 8 (MallocInv.optr (am_next a))) (image s)) by (apply MI; cbn; tauto).
  assert (C2 : In (MCell (LMem (padd q META_mem)) 8 (VP (am_mem a))) (image s)) by (apply MI; cbn; tauto).
  assert (C3 : In (MCell (LMem (padd q META_avail)) 4 (VZ (am_avail a))) (image s)) by (apply MI; cbn; tauto).
  assert (C4 : In (MCell (LMem (padd q META_freed)) 4 (VZ (am_freed a))) (image s)) by (apply MI; cbn; tauto).
  assert (C5 : In (MCell (LMem (padd q META_bits)) 8 (VZ (meta_bits a))) (image s)) by (apply MI; cbn; tauto).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try (unfold META_SIZE, PGSZ in *; lia).
  - cells_inside_tac.
  - intros o Ho.
    destruct (Z_lt_dec o 8) as [O0|O0]; [|destruct (Z_lt_dec o 16) as [O1|O1]; [|destruct (Z_lt_dec o 24) as [O2|O2]; [|destruct (Z_lt_dec o 28) as [O3|O3]; [|destruct (Z_lt_dec o 32) as [O4|O4]]]]].
    + apply (cell_rw0 _ _ (addr_of L q) 0 8 C0 (cellZ_optr _ _ _) eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ _ (addr_of L q) 8 8 C1 (cellZ_optr _ _ _) eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ (addr_of L (am_mem a)) (addr_of L q) 16 8 C2 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ (am_avail a) (addr_of L q) 24 4 C3 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ (am_freed a) (addr_of L q) 28 4 C4 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ (meta_bits a) (addr_of L q) 32 8 C5 eq_refl eq_refl); [apply AG|lia].
  - unfold cells_in_view. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]].
    + apply (cell_view0 _ _ (addr_of L q) 0 8 _ C0 (cellZ_optr _ _ _) eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by exact Sp. rewrite Ep. reflexivity.
    + apply (cell_view0 _ _ (addr_of L q) 8 8 _ C1 (cellZ_optr _ _ _) eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by exact Sn. rewrite En. reflexivity.
    + apply (cell_view0 _ _ (addr_of L q) 16 8 _ C2 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by exact Sm. rewrite Em. reflexivity.
    + apply (cell_view0m _ (am_avail a) (addr_of L q) 24 4 _ C3 eq_refl eq_refl ltac:(lia)); [apply AG | exact Sa |]. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Ea. rewrite Z.mod_small; lia.
    + apply (cell_view0m _ (am_freed a) (addr_of L q) 28 4 _ C4 eq_refl eq_refl ltac:(lia)); [apply AG | exact Sf |]. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Ef. rewrite Z.mod_small; lia.
    + apply (cell_view0 _ _ (addr_of L q) 32 8 _ C5 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by exact Sbb. rewrite Ebb. reflexivity.
Qed.

Lemma hold_links (q : sptr) (x : mslot) (bv pv nv : sv) : ltac2:(tb__ "0|6|
Sc9S1bVq;Se3Vs;A1A3S4S6cS1fA1SdfVs;Vq;A2S6aS1fVx;A2A3S4S6bS7cVbv;A1S70A3S4S6bS7cVpv;A1S70A3S4S6bS7cVnv;A1S70A3S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M0S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M1Vbv;A3Sd2VL;Vq;A2A3S4S0S7aG0G1Vpv;A3S10bVL;S79S6cS1bA1M2G2S3fVx;A1M3A3A2A3S4S0S7aG0G1Vnv;A3S10bVL;S78G2G2G3A3A2A3S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S4cVbv;S47Z0A1M4S47Z10A1S6fS48S49G4Z8M5Vpv;A3S6fS48S49S47G5A1G5Vnv;A3S72S48A1A3A3S4bA5A4F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using Erd Ewok HMI Hdepth Hgd Hrom Hsp.
  intros Hq Mq Sb Sp Sn Eb Ep En.
  pose proof (key_range X (Some (g, i)) U s L HI HL C_U vm q Hq HV HLG) as (K1 & K2 & K3 & K4). pose proof (ceiling_small L) as CS.
  change (mkObj bv (SLit 0) (SLit 16) [mkCell (SLit 0) 8 pv; mkCell (SLit 8) 8 nv] DUnknown) with (carved bv 0 16 [(0, 8%nat, pv); (8, 8%nat, nv)]).
  assert (B : bv_unsigned (eval (rho1 mV) bv) = addr_of L q) by (rewrite ev1u by exact Sb; exact Eb).
  assert (AG : forall d, loc_addr L (LMem (padd q d)) = addr_of L q + d) by (intros d; unfold addr_of, loc_addr; destruct q; cbn [padd]; lia).

  assert (CC : exists vp vn, In (MCell (LMem (padd q META_prev)) 8 vp) (image s) /\ In (MCell (LMem (padd q META_next)) 8 vn) (image s)
               /\ cellZ L (MCell (LMem (padd q META_prev)) 8 vp) = Some (optrA L (fst (links_of x)))
               /\ cellZ L (MCell (LMem (padd q META_next)) 8 vn) = Some (optrA L (snd (links_of x)))).
  { pose proof (fun c Hc => meta_cells_in_imageI X (Some (g, i)) U s HI q c Hq Hc) as MI. rewrite Mq in MI.
    destruct x as [pr nx| |a]; cbn [meta_slot_cells links_of fst snd] in MI |- *.
    - exists (MallocInv.optr pr), (MallocInv.optr nx). split; [apply MI; cbn; tauto|]. split; [apply MI; cbn; tauto|]. split; apply cellZ_optr.
    - exists (VZ 0), (VZ 0). split; [apply MI; cbn; tauto|]. split; [apply MI; cbn; tauto|]. split; reflexivity.
    - exists (MallocInv.optr (am_prev a)), (MallocInv.optr (am_next a)). split; [apply MI; cbn; tauto|]. split; [apply MI; cbn; tauto|]. split; apply cellZ_optr. }
  destruct CC as (vp & vn & C0 & C1 & Z0 & Z1).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try (unfold META_SIZE, PGSZ in *; lia).
  - cells_inside_tac.
  - intros o Ho. destruct (Z_lt_dec o 8).
    + apply (cell_rw0 _ _ (addr_of L q) 0 8 C0 Z0 eq_refl); [apply AG | lia].
    + apply (cell_rw0 _ _ (addr_of L q) 8 8 C1 Z1 eq_refl); [apply AG | lia].
  - unfold cells_in_view. constructor; [|constructor; [|constructor]].
    + apply (cell_view0 _ _ (addr_of L q) 0 8 _ C0 Z0 eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by exact Sp. rewrite Ep. reflexivity.
    + apply (cell_view0 _ _ (addr_of L q) 8 8 _ C1 Z1 eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by exact Sn. rewrite En. reflexivity.
Qed.

Definition e_actlo : sv := SAlu ALU_ADD nt_sc8 (SLit 80).
Definition e_acthi : sv := SAlu ALU_ADD nt_sc8 (SLit 88).
Lemma ze_sc8 : ltac2:(tb__ "0|0|
S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S173A3S10Z8S10fVam;A1A2A3").
Proof using HMI Hgd Hsp Hu.
  unfold nt_sc8. rewrite ze_alu, ze_sc, ze_lit. cbn [zalu]. change (3 mod 2 ^ 64 mod 64) with 3.
  pose proof R_all as R. unfold sc. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small; lia.
Qed.
Lemma ze_actlo : ltac2:(tb__ "0|0|
S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S191A3SbS10Z8S10fVam;A1A2Z50A2A3").
Proof using HMI Hgd Hsp Hu. unfold e_actlo. rewrite ze_alu, ze_sc8, ze_lit. cbn [zalu]. change (80 mod 2 ^ 64) with 80. pose proof R_all as R. unfold sc in *. rewrite Z.mod_small; lia. Qed.
Lemma ze_acthi : ltac2:(tb__ "0|0|
S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S193A3SbS10Z8S10fVam;A1A2Z58A2A3").
Proof using HMI Hgd Hsp Hu. unfold e_acthi. rewrite ze_alu, ze_sc8, ze_lit. cbn [zalu]. change (88 mod 2 ^ 64) with 88. pose proof R_all as R. unfold sc in *. rewrite Z.mod_small; lia. Qed.

Definition O_act (hv : sv) : sobj := ltac2:(tb__ "0|0|
S4cS47Z5a3d0A1S191S193S6fS48S49S191Z8Vhv;A3S72S48A1A3S4bA5").

Lemma hold_act (hv : sv) : ltac2:(tb__ "0|1|
S5SaZ0S10fVam;A1M0A2ScG0Z30A2A2S4S6bS7cVhv;A1S70A3S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Vhv;A3S118Vs;VL;Vam;A3A3S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S194Vhv;A1A4F_;F_;F_;").
Proof using Erd Ewok HMI Hgd Hrom Hsp Hu.
  intros Hsc' Shv Ehv. pose proof Hctx as HCX. pose proof zH_range as ZR. pose proof (ceiling_small L) as CS.
  assert (B : bv_unsigned (eval (rho1 mV) (SLit 0x5a3d0)) = 0x5a3d0) by (cbn [eval]; apply u64; lia).
  assert (CI : In (MCell (LCtx (CTX_active + 8 * Z.of_nat (Z.to_nat sc))) 8 (MallocInv.optr (nth (Z.to_nat sc) (st_active s) None))) (image s)).
  { unfold image. apply in_app_iff. left. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. left.
    apply in_map_iff. exists (Z.to_nat sc). split; [reflexivity|]. apply in_seq. lia. }
  rewrite Z2Nat.id in CI by lia. change (nth (Z.to_nat sc) (st_active s) None) with (active_hd s sc) in CI.
  assert (AD : loc_addr L (LMem (padd g 0)) = loc_addr L (LMem (padd g 0))) by reflexivity.
  assert (AG : loc_addr L (mc_loc (MCell (LCtx (CTX_active + 8 * sc)) 8 (MallocInv.optr (active_hd s sc)))) = 0x5a3d0 + (8 * sc + 80)).
  { cbn [mc_loc loc_addr]. rewrite HCX. unfold CTX_active. lia. }
  apply (obj_holds_sem segsU (rho1 mV) (with_mem ms mV) (carved (SLit 0x5a3d0) (8 * sc + 80) (8 * sc + 88) [(8 * sc + 80, 8%nat, hv)])).
  - reflexivity.
  - cbn [ob_lo carved O_act]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_actlo | lia].
  - cbn [ob_hi carved O_act]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_acthi | lia].
  - reflexivity.
  - cbn [ob_cells carved O_act map]. constructor; [|constructor].
    split; [|split; reflexivity]. cbn [c_off]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_actlo | lia].
  - apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    + cells_inside_tac.
    + intros o Ho. apply (cell_rw0 _ zH 0x5a3d0 (8 * sc + 80) 8 CI (cellZ_optr _ _ _) eq_refl AG). lia.
    + unfold cells_in_view. constructor; [|constructor]. intros j Hj.
      apply (cell_view0 _ zH 0x5a3d0 (8 * sc + 80) 8 hv CI (cellZ_optr _ _ _) eq_refl ltac:(lia) AG); [|exact Hj].
      rewrite (ev1 mV) by exact Shv. rewrite Ehv. reflexivity.
Qed.

Definition O_seq (x : sv) : sobj := ltac2:(tb__ "0|1|
S4cS47Z5a3d0A1S47Z390A1M0S47Z391A1S6fS48S49G0Z1Vx;A3S72S48A1A3S4bA5").
Lemma ctx_cell_In c : ltac2:(tb__ "0|0|
Sc9SdaVc;S100Vs;A1A3Sc9SdaVc;SddVs;A1A3F_;").
Proof using . intros Hc. unfold image. apply in_app_iff. left. exact Hc. Qed.
Lemma seq_cell_In : ltac2:(tb__ "0|0|
Sc9SdaSdeSe5Sf6A1U1Se2S36Vs;A1A1A3SddVs;A1A3").
Proof using Hdepth Hgd Hsp. apply ctx_cell_In. unfold ctx_cells. apply in_app_iff. left. cbn. tauto. Qed.
Lemma hold_seq (x : sv) : ltac2:(tb__ "0|1|
S4S6bS7cVx;A1S70A3S4S0SfS7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Vx;A3SdZ2Z8A2M0A2SfS133Vs;A1G0A2A3S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S199Vx;A1A4F_;F_;").
Proof using Erd Ewok HMI Hdepth Hgd Hrom Hsp.
  intros Sx Ex. pose proof Hctx as HCX. pose proof seq_cell_In as CI.
  change (O_seq x) with (carved (SLit 0x5a3d0) 912 913 [(912, 1%nat, x)]).
  assert (B : bv_unsigned (eval (rho1 mV) (SLit 0x5a3d0)) = 0x5a3d0) by (cbn [eval]; apply u64; lia).
  assert (AG : loc_addr L (mc_loc (MCell (LCtx CTX_seq) 1 (VZ (st_seq s)))) = 0x5a3d0 + 912) by (cbn [mc_loc loc_addr]; rewrite HCX; reflexivity).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. apply (cell_rw0 _ (st_seq s) 0x5a3d0 912 1 CI eq_refl eq_refl AG). lia.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj.
    apply (cell_view0m _ (st_seq s) 0x5a3d0 912 1 x CI eq_refl eq_refl ltac:(lia) AG Sx); [|exact Hj].
    change (8 * Z.of_nat 1) with 8. exact Ex.
Qed.

Definition O_fmh (x : sv) : sobj := ltac2:(tb__ "0|1|
S4cS47Z5a3d0A1S47Z10A1M0S47Z18A1S6fS48S49G0Z8Vx;A3S72S48A1A3S4bA5").
Lemma fmh_cell_In : ltac2:(tb__ "0|0|
Sc9SdaSdeSe5Sf4A1U8Sf1S26Vs;A1A1A3SddVs;A1A3").
Proof using Hdepth Hgd Hsp. apply ctx_cell_In. unfold ctx_cells. apply in_app_iff. left. cbn. tauto. Qed.
Lemma hold_fmh (x : sv) : ltac2:(tb__ "0|0|
S4S6bS7cVx;A1S70A3S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Vx;A3S117Vs;VL;A2A3S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S195Vx;A1A4F_;F_;").
Proof using Erd Ewok HMI Hdepth Hgd Hrom Hsp.
  intros Sx Ex. pose proof Hctx as HCX. pose proof fmh_cell_In as CI.
  change (O_fmh x) with (carved (SLit 0x5a3d0) 16 24 [(16, 8%nat, x)]).
  assert (B : bv_unsigned (eval (rho1 mV) (SLit 0x5a3d0)) = 0x5a3d0) by (cbn [eval]; apply u64; lia).
  assert (AG : loc_addr L (mc_loc (MCell (LCtx CTX_free_meta_head) 8 (MallocInv.optr (st_free_meta_head s)))) = 0x5a3d0 + 16) by (cbn [mc_loc loc_addr]; rewrite HCX; reflexivity).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. apply (cell_rw0 _ zF 0x5a3d0 16 8 CI (cellZ_optr _ _ _) eq_refl AG). lia.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj.
    apply (cell_view0 _ zF 0x5a3d0 16 8 x CI (cellZ_optr _ _ _) eq_refl ltac:(lia) AG); [|exact Hj].
    rewrite (ev1 mV) by exact Sx. rewrite Ex. reflexivity.
Qed.

Definition O_useq (a b c d : sv) : sobj := ltac2:(tb__ "0|2|
S4cS47Z5a3d0A1S47Z350A1M0S47Z370A1S6fS48S49G0Z8M1Va;A3S6fS48S49S47Z358A1G1Vb;A3S6fS48S49S47Z360A1G1Vc;A3S6fS48S49S47Z368A1G1Vd;A3S72S48A1A3A3A3A3S4bA5").
Lemma useq_cell_In k : ltac2:(tb__ "0|0|
S162Vk;U20A2Sc9SdaSdeSe5SbSf7S11Vk;A1A2A1U1Se2S154S0Vk;S2aVs;A1Z0A4A1A3SddVs;A1A3F_;").
Proof using Hgd rho.
  intros Hk. apply ctx_cell_In. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia].
Qed.
Lemma useq_byte_rd k : ltac2:(tb__ "0|3|
S162Vk;U20A2S5S4S6bS136Sc8VmV;ScfQ40SbSbZ5a3d0Z350A2S11Vk;A1A2A2M0A3S70A3S4S6cSceQ8M1A1M2A1S135Sc8VmV;G0A3S6aG2ScfG1S154S0Vk;S2aVs;A1Z0A4A2A2A3A2F_;").
Proof using Erd Ewok HMI Hgd rho.
  intros Hk. pose proof Hctx as HCX.
  destruct (cell_bytes0 _ (nth k (st_unmap_seq s) 0) (useq_cell_In k Hk) eq_refl 0 ltac:(cbn; lia)) as (_ & W & R).
  cbn [mc_loc loc_addr mc_w] in W, R. rewrite HCX in W, R. unfold CTX_unmap_seq in W, R. rewrite Z.add_0_r in W, R.
  replace (369616 + (848 + Z.of_nat k)) with (369616 + 848 + Z.of_nat k) in W, R by lia.
  split; [exact W|]. rewrite R. f_equal. f_equal. unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, Z.mod_mod by lia. pose proof (useq_byte k). apply Z.mod_small. lia.
Qed.
Lemma hold_useq (es : list sv) : ltac2:(tb__ "0|1|
S4S6eS77S46Ves;A2U4A3S6eS46S4S6cS46A1ScdS46Ves;R2A3S6aS46R1A2A3S5S4S6bS7cR2A1S70A3S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R2A3S12dVs;R3A2A3A2F_;Fe;Fj;S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S19aS154S46U0Ves;S47Z0A1M0A4S154S46U1Ves;G0A4S154S46U2Ves;G0A4S154S46U3Ves;G0A4A4A4F_;F_;").
Proof using Erd Ewok HMI Hgd Hrom Hsp.
  intros Hlen Hes. destruct es as [|a [|b [|c [|d [|]]]]]; try discriminate. cbn [nth].
  change (O_useq a b c d) with (carved (SLit 0x5a3d0) 848 880 [(848, 8%nat, a); (856, 8%nat, b); (864, 8%nat, c); (872, 8%nat, d)]).
  assert (B : bv_unsigned (eval (rho1 mV) (SLit 0x5a3d0)) = 0x5a3d0) by (cbn [eval]; apply u64; lia).
  assert (CV : forall (j : nat) e, nth_error [a; b; c; d] j = Some e -> forall t, (t < 8)%nat ->
             Glue.rd_of segsU mV (Z_to_bv 64 (0x5a3d0 + (848 + 8 * Z.of_nat j) + Z.of_nat t)) = Some (nth t (enc_bytes 8 (eval (rho1 mV) e)) (Z_to_bv 8 0))).
  { intros j e He t Ht. destruct (Hes j e He) as [Se Ee]. rewrite (ev1 mV e Se), Ee, useq_dw_enc.
    assert (Hj : (j < 4)%nat) by (destruct j as [|[|[|[|j]]]]; cbn in He; try lia; destruct j; discriminate).
    replace (0x5a3d0 + (848 + 8 * Z.of_nat j) + Z.of_nat t) with (0x5a3d0 + 848 + Z.of_nat (8 * j + t)) by lia.
    rewrite (proj2 (useq_byte_rd (8 * j + t) ltac:(lia))). unfold useq_bytes, ubytes. f_equal.
    destruct t as [|[|[|[|[|[|[|[|]]]]]]]]; try lia; cbn [map seq nth]; rewrite ?Nat.add_0_r; reflexivity. }
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. replace (0x5a3d0 + o) with (0x5a3d0 + 848 + Z.of_nat (Z.to_nat (o - 848))) by lia.
    destruct (useq_byte_rd (Z.to_nat (o - 848)) ltac:(lia)) as [W R]. split; [exact W | eexists; exact R].
  - unfold cells_in_view.
    constructor; [intros t Ht; apply (CV 0%nat a eq_refl t Ht)|].
    constructor; [intros t Ht; apply (CV 1%nat b eq_refl t Ht)|].
    constructor; [intros t Ht; apply (CV 2%nat c eq_refl t Ht)|].
    constructor; [intros t Ht; apply (CV 3%nat d eq_refl t Ht)|]. constructor.
Qed.

Definition free_cells (five : bool) (pv nv : sv) : list (Z * nat * sv) := ltac2:(tb__ "0|b|
S6bS74S71S71S0S6eA2M0S46A2M1A1Lfive;Vfive;S6fG1S6dG0S46S6dS0S6eZ0M2U8M3A4Vpv;A4M4S6fG1S6dG0S46S6dS0S6eZ8G3A4Vnv;A4M5S6fG1S6dG0S46S6dS0S6eZ10G3A4S47G2A1M6A4M7S6fG1S6dG0S46S6dS0S6eZ18M8G3A4G6A4S6fG1S6dG0S46S6dS0S6eZ20G3A4G6A4S72G1A1A3M9A3A3A3A3S6fG1G4S6fG1G5S6fG1G7S6fG1S6dG0S46S6dS0S6eG8U4MaA4G6A4S6fG1S6dG0S46S6dS0S6eZ1cGaA4G6A4G9A3A3A3A3A3X6bx2").
Definition O_freeK (bv : sv) (five : bool) (pv nv : sv) : sobj := ltac2:(tb__ "0|0|
S138Vbv;Z0Z28S19bVfive;Vpv;Vnv;A3A4").

End Inst.
End Mal_nt_Ib.

Module Mal_nt_Ic.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Inst.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
S186Sd3VX;S6aS71S1bS0A2S6dS1bS0Vg;Vi;A4A2VU;S185Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Local Abbreviation HXr := (@U.Mal_nt__G1.Mal_nt_I.HXr s X HXz).
Hypothesis Hu : ltac2:(tb__ "0|0|
SdbVX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Notation "§5§ h__" := (h__ s L X U g i vm rd0 wok0 HMI) (at level 10, h__ global).
Local Abbreviation HI := (§5§ U.Mal_nt__G1.Mal_nt_I.HI).
Local Abbreviation Hctx := (§5§ U.Mal_nt__G1.Mal_nt_I.Hctx).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S4S0Sd0Q40S4aVrho;PcA2A2Sd2VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S4S0Sd0Q40S4aVrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Abbreviation zM := (@U.Mal_nt__G1.Mal_nt_I.zM L am).
Local Notation "§6§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation R_all := (§6§ U.Mal_nt__G1.Mal_nt_I.R_all).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Abbreviation key_range40 := (@U.Mal_nt__G1.Mal_nt_I.key_range40 s L X U g i gd vm rd0 wok0 HMI Hgd).
Local Abbreviation nQ := (@U.Mal_nt__G1.Mal_nt_I.nQ g am).
Local Notation "§7§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation anQ := (§7§ U.Mal_nt__G1.Mal_nt_I.anQ).
Local Notation "§8§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation zNm := (§8§ U.Mal_nt__G1.Mal_nt_I.zNm).
Local Abbreviation zU := (@U.Mal_nt__G1.Mal_nt_I.zU s am).
Local Abbreviation zB := (@U.Mal_nt__G1.Mal_nt_I.zB s am).
Local Abbreviation zA8 := (@U.Mal_nt__G1.Mal_nt_I.zA8 s L g am rd0).
Local Abbreviation gPar := (§7§ U.Mal_nt__G1.Mal_nt_I.gPar).
Local Abbreviation amPar := (§7§ U.Mal_nt__G1.Mal_nt_I.amPar).
Local Abbreviation zQ := (§8§ U.Mal_nt__G1.Mal_nt_I.zQ).
Local Abbreviation zQm := (§8§ U.Mal_nt__G1.Mal_nt_I.zQm).
Local Abbreviation zQa := (§8§ U.Mal_nt__G1.Mal_nt_I.zQa).
Local Abbreviation zHb := (§7§ U.Mal_nt__G1.Mal_nt_I.zHb).
Local Abbreviation zOff := (§7§ U.Mal_nt__G1.Mal_nt_I.zOff).
Local Abbreviation zSec := (@U.Mal_nt__G1.Mal_nt_I.zSec L).
Local Notation "§9§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§9§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation zr1 := (§9§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§9§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation nQ_used := (§6§ U.Mal_nt__G1.Mal_nt_I.nQ_used).
Local Abbreviation RN := (§6§ U.Mal_nt__G1.Mal_nt_I.RN).
Local Abbreviation RQ := (§6§ U.Mal_nt__G1.Mal_nt_I.RQ).
Local Abbreviation zQ_range := (§6§ U.Mal_nt__G1.Mal_nt_I.zQ_range).
Local Abbreviation zOff_eq := (§6§ U.Mal_nt__G1.Mal_nt_I.zOff_eq).
Local Abbreviation par_area := (§6§ U.Mal_nt__G1.Mal_nt_I.par_area).
Local Abbreviation secret_cell := (@U.Mal_nt__G1.Mal_nt_I.secret_cell s L X U g am i vm rd0 wok0 HMI Hu).
Local Notation "§10§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI HXz Hu Hgd) (at level 10, h__ global).
Local Abbreviation hdr_cells := (§10§ U.Mal_nt__G1.Mal_nt_I.hdr_cells).
Local Abbreviation pbase_cell := (§10§ U.Mal_nt__G1.Mal_nt_I.pbase_cell).
Local Abbreviation pmeta_cells := (§6§ U.Mal_nt__G1.Mal_nt_I.pmeta_cells).
Local Abbreviation zU_range := (@U.Mal_nt__G1.Mal_nt_I.zU_range s L X U g am i vm rd0 wok0 HMI).
Local Abbreviation zB_range := (@U.Mal_nt__G1.Mal_nt_I.zB_range s L X U g am i gd vm rd0 wok0 HMI Hgd).
Local Abbreviation zA8_range := (@U.Mal_nt__G1.Mal_nt_I.zA8_range s L g am gd rd0 Hgd).
Local Abbreviation zSec_range := (@U.Mal_nt__G1.Mal_nt_I.zSec_range L gd Hgd).
Local Abbreviation zHb_range := (§6§ U.Mal_nt__G1.Mal_nt_I.zHb_range).
Local Abbreviation ze_lit := (§9§ U.Mal_nt__G1.Mal_nt_I.ze_lit).
Local Abbreviation ze_alu := (§9§ U.Mal_nt__G1.Mal_nt_I.ze_alu).
Local Notation "§11§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation ze142 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze142).
Local Abbreviation ze156 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze156).
Local Abbreviation ze136 := (@U.Mal_nt__G1.Mal_nt_I.ze136 s L g am i rho gd rd0 Hgd).
Local Abbreviation ze170 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze170).
Local Abbreviation ze171 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze171).
Local Abbreviation ze172 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze172).
Local Abbreviation ze173 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze173).
Local Abbreviation ze174 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze174).
Local Abbreviation ze169 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze169).
Local Abbreviation e_parbase := (@U.Mal_nt__G1.Mal_nt_I.e_parbase).
Local Abbreviation e_pmem := (@U.Mal_nt__G1.Mal_nt_I.e_pmem).
Local Abbreviation e_parea := (@U.Mal_nt__G1.Mal_nt_I.e_parea).
Local Abbreviation ze_parbase := (§11§ U.Mal_nt__G1.Mal_nt_I.ze_parbase).
Local Abbreviation ze_pmem := (§11§ U.Mal_nt__G1.Mal_nt_I.ze_pmem).
Local Abbreviation ze_parea := (§11§ U.Mal_nt__G1.Mal_nt_I.ze_parea).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S5SaZ1000Sd0Q40S4aVrho;PaA2A2M0A2S4S0SfG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S5SaS7eZ40Sd0Q40S4aVrho;PfA2A2A2M0N60A2SaS13SdZ2Z28A2A1G0A2A2").
Local Abbreviation ze_scm7 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze_scm7).
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S4SceQ40A1S6cSceQ8A1A1F_;Vrd0;S135Sc8VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S4SceQ40A1S6bF_;Vwok0;S136Sc8VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S0S5SaZ0R1A2ScR1Z60A2A2S4S6cSceQ8A1M0A1VmV;ScfQ40SbZ108ecR2A2A2A1S73G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
Sd5Sd4Vrd0;SceQ40A1S70L_;A2Sd6Sd3A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
Sd4S135Sc8VmV;A2S136Sc8VmV;A2A2").
Local Notation "§12§ h__" := (h__ s L X U g i vm rd0 wok0 HMI mV Erd Ewok) (at level 10, h__ global).
Local Abbreviation HreprO := (§12§ U.Mal_nt__G1.Mal_nt_Ib.HreprO).
Local Abbreviation cell_bytes0 := (§12§ U.Mal_nt__G1.Mal_nt_Ib.cell_bytes0).
Local Abbreviation cell_rw0 := (@U.Mal_nt__G1.Mal_nt_Ib.cell_rw0 s L X U g i rho gd vm rd0 wok0 HMI Hgd Hsp mV Erd Ewok).
Local Abbreviation ev1 := (§9§ U.Mal_nt__G1.Mal_nt_Ib.ev1).
Local Abbreviation ev1u := (§9§ U.Mal_nt__G1.Mal_nt_Ib.ev1u).
Local Notation "§13§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI mV Erd Ewok) (at level 10, h__ global).
Local Abbreviation cell_view0 := (§13§ U.Mal_nt__G1.Mal_nt_Ib.cell_view0).
Local Abbreviation cell_view0m := (§13§ U.Mal_nt__G1.Mal_nt_Ib.cell_view0m).
Local Abbreviation soff_of_ev := (@U.Mal_nt__G1.Mal_nt_Ib.soff_of_ev s L g am i rho gd rd0 Hgd mV).
Local Abbreviation cellZ_optr := (@U.Mal_nt__G1.Mal_nt_Ib.cellZ_optr L).
Local Abbreviation ze_sc8 := (@U.Mal_nt__G1.Mal_nt_Ib.ze_sc8 s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp).
Local Abbreviation ctx_cell_In := (@U.Mal_nt__G1.Mal_nt_Ib.ctx_cell_In s).
Local Abbreviation free_cells := (@U.Mal_nt__G1.Mal_nt_Ib.free_cells).
Local Abbreviation O_freeK := (@U.Mal_nt__G1.Mal_nt_Ib.O_freeK).

Ltac zfact := cbn [zholds zcond].
Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.

Lemma hold_freeK (q : sptr) pr nx (bv : sv) five (pv nv : sv) : ltac2:(tb__ "0|6|
S4S6cS1fA1SdfVs;Vq;A2S6aS1fS28Vpr;Vnx;A2A2A3Sc9S1bVq;Se3Vs;A1M0A3S1bS4S6cS1bA1M1Vpr;S6aS1bR1A2M2A3Sc9S1bR2G0A3M3F_;Fp;S1bS4G1Vnx;G2A3G3F_;Fp;S4S6bS7cVbv;A1S70A3S4S6bS7cVpv;A1S70A3S4S6bS7cVnv;A1S70A3S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M4S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M5Vbv;A3Sd2VL;Vq;A2A3S4S0S7aG4G5Vpv;A3S10bVL;Vpr;A2A3S4S0S7aG4G5Vnv;A3S10bVL;Vnx;A2A3S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S1aaVbv;Vfive;Vpv;Vnv;A4A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using Erd Ewok HMI Hdepth Hgd Hrom Hsp.
  intros Mq Kq Kpr Knx Sb Sp Sn Eb Ep En. pose proof (ceiling_small L) as CS. pose proof (key_range40 q Kq) as (B1 & B2).
  assert (P12 : 0 <= optrA L pr /\ optrA L pr + 40 <= topL L).
  { destruct pr as [p|]; cbn [optrA]; [pose proof (key_range40 p (Kpr p eq_refl)); lia | top_ranges; lia]. }
  assert (N12 : 0 <= optrA L nx /\ optrA L nx + 40 <= topL L).
  { destruct nx as [p|]; cbn [optrA]; [pose proof (key_range40 p (Knx p eq_refl)); lia | top_ranges; lia]. }
  assert (B : bv_unsigned (eval (rho1 mV) bv) = addr_of L q) by (rewrite ev1u by exact Sb; exact Eb).
  assert (AG : forall d, loc_addr L (LMem (padd q d)) = addr_of L q + d) by (intros d; unfold addr_of, loc_addr; destruct q; cbn [padd]; lia).
  pose proof (fun c Hc => meta_cells_in_imageI X (Some (g, i)) U s HI q c Kq Hc) as MI. rewrite Mq in MI. cbn [meta_slot_cells] in MI.
  unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in MI.
  assert (C0 : In (MCell (LMem (padd q 0)) 8 (MallocInv.optr pr)) (image s)) by (apply MI; cbn; tauto).
  assert (C1 : In (MCell (LMem (padd q 8)) 8 (MallocInv.optr nx)) (image s)) by (apply MI; cbn; tauto).
  assert (C2 : In (MCell (LMem (padd q 16)) 8 (VZ 0)) (image s)) by (apply MI; cbn; tauto).
  assert (C3 : In (MCell (LMem (padd q 24)) 4 (VZ 0)) (image s)) by (apply MI; cbn; tauto).
  assert (C4 : In (MCell (LMem (padd q 28)) 4 (VZ 0)) (image s)) by (apply MI; cbn; tauto).
  assert (C5 : In (MCell (LMem (padd q 32)) 8 (VZ 0)) (image s)) by (apply MI; cbn; tauto).
  assert (RW : forall o, 0 <= o < 40 -> Glue.wok_of segsU mV (Z_to_bv 64 (addr_of L q + o)) = true /\ exists x, Glue.rd_of segsU mV (Z_to_bv 64 (addr_of L q + o)) = Some x).
  { intros o Ho.
    destruct (Z_lt_dec o 8); [apply (cell_rw0 _ _ (addr_of L q) 0 8 C0 (cellZ_optr _ _ _) eq_refl); [apply AG | lia]|].
    destruct (Z_lt_dec o 16); [apply (cell_rw0 _ _ (addr_of L q) 8 8 C1 (cellZ_optr _ _ _) eq_refl); [apply AG | lia]|].
    destruct (Z_lt_dec o 24); [apply (cell_rw0 _ 0 (addr_of L q) 16 8 C2 eq_refl eq_refl); [apply AG | lia]|].
    destruct (Z_lt_dec o 28); [apply (cell_rw0 _ 0 (addr_of L q) 24 4 C3 eq_refl eq_refl); [apply AG | lia]|].
    destruct (Z_lt_dec o 32); [apply (cell_rw0 _ 0 (addr_of L q) 28 4 C4 eq_refl eq_refl); [apply AG | lia]|].
    apply (cell_rw0 _ 0 (addr_of L q) 32 8 C5 eq_refl eq_refl); [apply AG | lia]. }

  assert (ZB : forall off (w : nat) c, In c (image s) -> cellZ L c = Some 0 -> mc_w c = w -> loc_addr L (mc_loc c) = addr_of L q + off ->
               forall t, (t < w)%nat -> Glue.rd_of segsU mV (Z_to_bv 64 (addr_of L q + off + Z.of_nat t)) = Some (Z_to_bv 8 0)).
  { intros off w c Hc Hz Hw Ha t Ht. destruct (cell_bytes0 c 0 Hc Hz t ltac:(rewrite Hw; exact Ht)) as (_ & _ & R). rewrite Ha in R. rewrite R.
    f_equal. f_equal. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. }
  pose proof (ZB 16 8%nat _ C2 eq_refl eq_refl (AG 16)) as Z16.
  pose proof (ZB 24 4%nat _ C3 eq_refl eq_refl (AG 24)) as Z24.
  pose proof (ZB 28 4%nat _ C4 eq_refl eq_refl (AG 28)) as Z28.
  pose proof (ZB 32 8%nat _ C5 eq_refl eq_refl (AG 32)) as Z32.
  assert (ZERO : forall (k t : nat), (t < k)%nat -> (k <= 8)%nat -> nth t (enc_bytes k (eval (rho1 mV) (SLit 0))) (Z_to_bv 8 0) = Z_to_bv 8 0).
  { intros k t Ht Hk. cbn [eval]. rewrite nth_enc_bytes by lia. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity. }
  unfold O_freeK. destruct five; cbn [free_cells];
    (apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try (unfold PGSZ in *; lia); [cells_inside_tac | intros o Ho; apply RW; lia |]);
    unfold cells_in_view.
  - constructor; [intros t Ht; apply (cell_view0 _ _ (addr_of L q) 0 8 _ C0 (cellZ_optr _ _ _) eq_refl ltac:(lia) (AG 0)); [rewrite ev1 by exact Sp; rewrite Ep; reflexivity | exact Ht]|].
    constructor; [intros t Ht; apply (cell_view0 _ _ (addr_of L q) 8 8 _ C1 (cellZ_optr _ _ _) eq_refl ltac:(lia) (AG 8)); [rewrite ev1 by exact Sn; rewrite En; reflexivity | exact Ht]|].
    constructor; [intros t Ht; rewrite (ZERO 8%nat t Ht ltac:(lia)); apply Z16; exact Ht|].
    constructor.
    { intros t Ht. rewrite (ZERO 8%nat t Ht ltac:(lia)). destruct (Nat.lt_ge_cases t 4) as [T|T].
      - apply Z24. exact T.
      - replace (addr_of L q + 24 + Z.of_nat t) with (addr_of L q + 28 + Z.of_nat (t - 4)) by lia. apply Z28. lia. }
    constructor; [intros t Ht; rewrite (ZERO 8%nat t Ht ltac:(lia)); apply Z32; exact Ht|]. constructor.
  - constructor; [intros t Ht; apply (cell_view0 _ _ (addr_of L q) 0 8 _ C0 (cellZ_optr _ _ _) eq_refl ltac:(lia) (AG 0)); [rewrite ev1 by exact Sp; rewrite Ep; reflexivity | exact Ht]|].
    constructor; [intros t Ht; apply (cell_view0 _ _ (addr_of L q) 8 8 _ C1 (cellZ_optr _ _ _) eq_refl ltac:(lia) (AG 8)); [rewrite ev1 by exact Sn; rewrite En; reflexivity | exact Ht]|].
    constructor; [intros t Ht; rewrite (ZERO 8%nat t Ht ltac:(lia)); apply Z16; exact Ht|].
    constructor; [intros t Ht; rewrite (ZERO 4%nat t Ht ltac:(lia)); apply Z24; exact Ht|].
    constructor; [intros t Ht; rewrite (ZERO 4%nat t Ht ltac:(lia)); apply Z28; exact Ht|].
    constructor; [intros t Ht; rewrite (ZERO 8%nat t Ht ltac:(lia)); apply Z32; exact Ht|]. constructor.
Qed.

Definition e_uslo : sv := SAlu ALU_ADD nt_sc8 (SLit 464).
Definition e_ushi : sv := SAlu ALU_ADD nt_sc8 (SLit 472).
Lemma ze_uslo : ltac2:(tb__ "0|0|
S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S19dA3SbS10Z8S10fVam;A1A2Z1d0A2A3").
Proof using HMI Hgd Hsp Hu. unfold e_uslo. rewrite ze_alu, ze_sc8, ze_lit. cbn [zalu]. change (464 mod 2 ^ 64) with 464. pose proof R_all as R. unfold sc in *. rewrite Z.mod_small; lia. Qed.
Lemma ze_ushi : ltac2:(tb__ "0|0|
S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S19fA3SbS10Z8S10fVam;A1A2Z1d8A2A3").
Proof using HMI Hgd Hsp Hu. unfold e_ushi. rewrite ze_alu, ze_sc8, ze_lit. cbn [zalu]. change (472 mod 2 ^ 64) with 472. pose proof R_all as R. unfold sc in *. rewrite Z.mod_small; lia. Qed.
Definition O_usage (x : sv) : sobj := ltac2:(tb__ "0|0|
S4cS47Z5a3d0A1S19dS19fS6fS48S49S19dZ8Vx;A3S72S48A1A3S4bA5").
Lemma usage_cell_In' : ltac2:(tb__ "0|1|
S5SaZ0S10fVam;A1M0A2ScG0Z30A2A2Sc9SdaSdeSe5SbSf8S10Z8G0A2A2A1U8Se2S11dVs;Vam;A2A1A3SddVs;A1A3F_;").
Proof using Hgd Hsp.
  intros Hsc'. apply ctx_cell_In. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_map_iff. exists (Z.to_nat sc). rewrite Z2Nat.id by lia. split; [|apply in_seq; lia]. unfold zU, usage_of, znth. reflexivity.
Qed.
Lemma hold_usage (x : sv) : ltac2:(tb__ "0|1|
S5SaZ0S10fVam;A1M0A2ScG0Z30A2A2S4S6bS7cVx;A1S70A3S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Vx;A3S11dVs;Vam;A2A3S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S1a8Vx;A1A4F_;F_;F_;").
Proof using Erd Ewok HMI Hgd Hrom Hsp Hu.
  intros Hsc' Sx Ex. pose proof Hctx as HCX. pose proof zU_range as ZR. pose proof (ceiling_small L) as CS.
  assert (B : bv_unsigned (eval (rho1 mV) (SLit 0x5a3d0)) = 0x5a3d0) by (cbn [eval]; apply u64; lia).
  pose proof (usage_cell_In' Hsc') as CI.
  assert (AG : loc_addr L (mc_loc (MCell (LCtx (CTX_usage + 8 * sc)) 8 (VZ zU))) = 0x5a3d0 + (8 * sc + 464)) by (cbn [mc_loc loc_addr]; rewrite HCX; unfold CTX_usage; lia).
  apply (obj_holds_sem segsU (rho1 mV) (with_mem ms mV) (carved (SLit 0x5a3d0) (8 * sc + 464) (8 * sc + 472) [(8 * sc + 464, 8%nat, x)])).
  - reflexivity.
  - cbn [ob_lo carved O_usage]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_uslo | lia].
  - cbn [ob_hi carved O_usage]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_ushi | lia].
  - reflexivity.
  - cbn [ob_cells carved O_usage map]. constructor; [|constructor].
    split; [|split; reflexivity]. cbn [c_off]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_uslo | lia].
  - apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    + cells_inside_tac.
    + intros o Ho. apply (cell_rw0 _ zU 0x5a3d0 (8 * sc + 464) 8 CI eq_refl eq_refl AG). lia.
    + unfold cells_in_view. constructor; [|constructor]. intros j Hj.
      apply (cell_view0 _ zU 0x5a3d0 (8 * sc + 464) 8 x CI eq_refl eq_refl ltac:(lia) AG); [|exact Hj].
      rewrite (ev1 mV) by exact Sx. rewrite Ex. reflexivity.
Qed.

Definition e_bnlo : sv := ltac2:(tb__ "0|0|
S4eS15aS4eS15aS164S47N7A1A3S47Z370A1A3").
Definition e_bnhi : sv := ltac2:(tb__ "0|0|
S4eS15aS4eS15aS164S47N7A1A3S47Z371A1A3").
Lemma ze_bnlo : ltac2:(tb__ "0|2|
S5SaZ7M0S10fVam;A1M1A2ScG1Z27A2A2S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S19cA3SbS12G1G0A2Z370A2A3F_;").
Proof using HMI Hgd Hu. intros Hr. unfold e_bnlo. rewrite ze_alu, ze_scm7, ze_lit. cbn [zalu]. change (880 mod 2 ^ 64) with 880. rewrite (Z.mod_small (sc - 7)) by lia. rewrite Z.mod_small; lia. Qed.
Lemma ze_bnhi : ltac2:(tb__ "0|2|
S5SaZ7M0S10fVam;A1M1A2ScG1Z27A2A2S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S19eA3SbS12G1G0A2Z371A2A3F_;").
Proof using HMI Hgd Hu. intros Hr. unfold e_bnhi. rewrite ze_alu, ze_scm7, ze_lit. cbn [zalu]. change (881 mod 2 ^ 64) with 881. rewrite (Z.mod_small (sc - 7)) by lia. rewrite Z.mod_small; lia. Qed.
Definition O_bnc (x : sv) : sobj := ltac2:(tb__ "0|0|
S4cS47Z5a3d0A1S19cS19eS6fS48S49S19cZ1Vx;A3S72S48A1A3S4bA5").
Lemma bnc_cell_In : ltac2:(tb__ "0|2|
S5SaZ7M0S10fVam;A1M1A2ScG1Z27A2A2Sc9SdaSdeSe5SbSf3S12G1G0A2A2A1U1Se2S116Vs;Vam;A2A1A3SddVs;A1A3F_;").
Proof using Hgd Hsp.
  intros Hr. apply ctx_cell_In. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right.
  apply in_map_iff. exists (Z.to_nat (sc - 7)). rewrite Z2Nat.id by lia. split; [|apply in_seq; lia]. unfold zB, znth. reflexivity.
Qed.
Lemma hold_bnc (x : sv) : ltac2:(tb__ "0|2|
S5SaZ7S10fVam;A1M0A2ScG0Z27A2A2S4S6bS7cVx;A1S70A3S4S0SfS7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Vx;A3SdZ2Z8A2M1A2SfS116Vs;Vam;A2G1A2A3S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S1a0Vx;A1A4F_;F_;F_;").
Proof using Erd Ewok HMI Hgd Hrom Hsp Hu.
  intros Hr Sx Ex. pose proof Hctx as HCX. pose proof zB_range as ZR. pose proof (ceiling_small L) as CS.
  assert (B : bv_unsigned (eval (rho1 mV) (SLit 0x5a3d0)) = 0x5a3d0) by (cbn [eval]; apply u64; lia).
  pose proof (bnc_cell_In Hr) as CI.
  assert (AG : loc_addr L (mc_loc (MCell (LCtx (CTX_bounces + (sc - 7))) 1 (VZ zB))) = 0x5a3d0 + (sc - 7 + 880)) by (cbn [mc_loc loc_addr]; rewrite HCX; unfold CTX_bounces; lia).
  apply (obj_holds_sem segsU (rho1 mV) (with_mem ms mV) (carved (SLit 0x5a3d0) (sc - 7 + 880) (sc - 7 + 881) [(sc - 7 + 880, 1%nat, x)])).
  - reflexivity.
  - cbn [ob_lo carved O_bnc]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply (ze_bnlo Hr) | lia].
  - cbn [ob_hi carved O_bnc]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply (ze_bnhi Hr) | lia].
  - reflexivity.
  - cbn [ob_cells carved O_bnc map]. constructor; [|constructor].
    split; [|split; reflexivity]. cbn [c_off]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply (ze_bnlo Hr) | lia].
  - apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    + cells_inside_tac.
    + intros o Ho. apply (cell_rw0 _ zB 0x5a3d0 (sc - 7 + 880) 1 CI eq_refl eq_refl AG). lia.
    + unfold cells_in_view. constructor; [|constructor]. intros j Hj.
      apply (cell_view0m _ zB 0x5a3d0 (sc - 7 + 880) 1 x CI eq_refl eq_refl ltac:(lia) AG Sx); [|exact Hj].
      change (8 * Z.of_nat 1) with 8. exact Ex.
Qed.

Definition O_grp (x : sv) : sobj := ltac2:(tb__ "0|1|
S4cSc7P9cA1S47Z8A1M0S47Z9A1S6fS48S49G0Z1Vx;A3S72S48A1A3S4bA5").
Lemma grp_byte : ltac2:(tb__ "0|0|
S6SdaSdaS5Sc9SdaR1SddVs;A1A3S5S4S0Se6VL;Se8R1A1A2SbS114Vs;VL;Vg;Vam;A4Z8A2A3S5S163U1Se7R1A1A2SffVL;Vbv0;R1A3A2A2A2Lc;A2").
Proof using Erd Ewok HMI HXz Hgd Hu rho.
  pose proof (aidx_cell_In X (Some (g, i)) U s HI HXr nQ anQ nQ_used) as CI.
  exists (Zones2.aidx_cell anQ). split; [exact CI|].
  assert (CH : MallocInv.cell_holds L bv0 (Zones2.aidx_cell anQ)) by exact (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 HreprO))) _ CI).
  unfold Zones2.aidx_cell in *. unfold zNm, addr_of, loc_addr. destruct (am_maplen anQ =? 0); cbn [mc_loc mc_w]; destruct (am_mem anQ); cbn [padd]; (split; [lia|]); (split; [lia | exact CH]).
Qed.
Lemma grp_byte_rd : ltac2:(tb__ "0|3|
S5S4S6bS136Sc8VmV;ScfQ40SbS114Vs;VL;Vg;Vam;A4Z8A2A2M0A3S70A3S4S6cSceQ8M1A1M2A1S135Sc8VmV;G0A3S6aG2ScfG1S113Vs;VL;Vg;Vam;Vrd0;A5A2A2A3A2").
Proof using Erd Ewok HMI HXz Hgd Hu rho.
  destruct grp_byte as (c & CI & AD & Wc & CH). pose proof RN as R'. pose proof (ceiling_small L) as CS.
  assert (BY : exists vv, bv0 (zNm + 8) = Some vv).
  { unfold MallocInv.cell_holds in CH. destruct c as [lc w val]. cbn [mc_loc mc_w mc_val] in *.
    destruct val as [z|p|z|]; try (specialize (CH 0%nat ltac:(lia)); rewrite AD, Z.add_0_r in CH; eexists; exact CH).
    all: destruct CH as (b & Hb & _); rewrite AD in Hb; eexists; exact Hb. }
  destruct BY as (vv & Hvv). unfold bv0 in Hvv. destruct (byteview_of_Some _ _ _ _ Hvv) as (_ & W & b & Hb & E).
  split; [exact W|]. rewrite Hb. f_equal. unfold zA8. rewrite Erd, Hb.
  symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma hold_grp (x : sv) : ltac2:(tb__ "0|0|
S4S6bS7cVx;A1S70A3S4S0SfS7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Vx;A3SdZ2Z8A2A2S113Vs;VL;Vg;Vam;Vrd0;A5A3S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S1a2Vx;A1A4F_;F_;").
Proof using Erd Ewok HMI HXz Hgd Hrom Hsp Hu.
  intros Sx Ex. pose proof RN as R'. pose proof (ceiling_small L) as CS. pose proof zA8_range as A8.
  change (O_grp x) with (carved (v 156) 8 9 [(8, 1%nat, x)]).
  assert (B : bv_unsigned (eval (rho1 mV) (v 156)) = zNm) by (rewrite ev1u by reflexivity; apply ze156).
  destruct grp_byte_rd as [W R].
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. replace (zNm + o) with (zNm + 8) by lia. split; [exact W | eexists; exact R].
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. assert (j = 0%nat) as -> by lia. rewrite Z.add_0_r, R.
    rewrite (ev1 mV x Sx). rewrite nth_enc_bytes by lia. f_equal. f_equal. unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8). change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r, Ex. symmetry. apply Z.mod_small. lia.
Qed.

Definition O_shdr : sobj := ltac2:(tb__ "0|3|
S4cSc7P8eA1S47N4A1M0S47Z0A1M1S6fS48S49G0Z1M2G1A3S6fS48S49S47N3A1G2Sc7PaaA1A3S6fS48S49S47N2A1Z2Sc7PabA1A3S72S48A1A3A3A3S4bA5").
Definition O_bptr (c0 : sv) : sobj := ltac2:(tb__ "0|2|
S4cSc7P8eA1S47Z0A1M0S47Z8M1A1S6fS48S49G0G1Vc0;A3S72S48A1A3S4bA5").
Definition O_pbase : sobj := ltac2:(tb__ "0|1|
S4cS123S47N10A1M0S47N8A1S6fS48S49G0Z8Sc7PacA1A3S72S48A1A3S4bA5").
Definition O_pmeta : sobj := ltac2:(tb__ "0|3|
S4cSc7PacA1S47Z10A1M0S47Z28A1S6fS48S49G0Z8M1S115A3S6fS48S49S47Z18A1Z4M2Sc7PadA1A3S6fS48S49S47Z1cA1G2Sc7PaeA1A3S6fS48S49S47Z20A1G1Sc7Pa9A1A3S72S48A1A3A3A3A3S4bA5").
Definition O_parea : sobj := ltac2:(tb__ "0|2|
S4cS124S47Z0A1M0S47Z8M1A1S6fS48S49G0G1Sc7P88A1A3S72S48A1A3S4bA5").
Definition O_secret : sobj := ltac2:(tb__ "0|2|
S4cS47Z5a3d0A1S47Z0A1M0S47Z8M1A1S6fS48S49G0G1Sc7P88A1A3S72S48A1A3S4bA5").

Lemma AGq (q : sptr) d : ltac2:(tb__ "0|0|
S4S0Se6VL;Se0S27Vq;Vd;A2A1A2SbSd2VL;Vq;A2Vd;A2A3").
Proof using Hgd rho. unfold addr_of, loc_addr. destruct q; cbn [padd]. lia. Qed.

Lemma hold_shdr : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S1a7A4F_;").
Proof using Erd Ewok HMI HXz Hgd Hrom Hsp Hu.
  intros H. pose proof (hdr_cells H) as (C4 & C3 & C2 & _). pose proof R_all as R. pose proof (ceiling_small L) as CS.
  pose proof (zHb_range H). pose proof (zOff_eq H).
  change O_shdr with (carved (v 142) (-4) 0 [(-4, 1%nat, SLit 0); (-3, 1%nat, v 170); (-2, 2%nat, v 171)]).
  assert (B : bv_unsigned (eval (rho1 mV) (v 142)) = zM) by (rewrite ev1u by reflexivity; exact ze142).
  assert (AG : forall d, loc_addr L (LMem (padd (am_mem am) d)) = zM + d) by (intros d; unfold zM; apply AGq).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. destruct (Z_lt_dec o (-3)) as [O0|O0]; [|destruct (Z_lt_dec o (-2)) as [O1|O1]].
    + apply (cell_rw0 _ 0 zM (-4) 1 C4 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ zHb zM (-3) 1 C3 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ zOff zM (-2) 2 C2 eq_refl eq_refl); [apply AG|lia].
  - unfold cells_in_view. constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (cell_view0 _ _ zM (-4) 1 _ C4 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by reflexivity. rewrite ze_lit. reflexivity.
    + apply (cell_view0 _ _ zM (-3) 1 _ C3 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by reflexivity. rewrite (ze170 H). reflexivity.
    + apply (cell_view0 _ _ zM (-2) 2 _ C2 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by reflexivity. rewrite (ze171 H). reflexivity.
Qed.
Lemma hold_bptr (c0 : sv) : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4S6bS7cVc0;A1S70A3S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Vc0;A3S112VL;Vg;A2A3S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S1a1Vc0;A1A4F_;F_;F_;").
Proof using Erd Ewok HMI HXz Hgd Hrom Hsp Hu.
  intros H S0 E0. pose proof (hdr_cells H) as (_ & _ & _ & C0). pose proof R_all as R. pose proof (ceiling_small L) as CS.
  change (O_bptr c0) with (carved (v 142) 0 8 [(0, 8%nat, c0)]).
  assert (B : bv_unsigned (eval (rho1 mV) (v 142)) = zM) by (rewrite ev1u by reflexivity; exact ze142).
  assert (AG : loc_addr L (LMem (am_mem am)) = zM + 0) by (unfold zM, addr_of; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. apply (cell_rw0 _ zG zM 0 8 C0 eq_refl eq_refl); [exact AG|lia].
  - unfold cells_in_view. constructor; [|constructor].
    apply (cell_view0 _ _ zM 0 8 _ C0 eq_refl eq_refl ltac:(lia)); [exact AG|]. rewrite ev1 by exact S0. rewrite E0. reflexivity.
Qed.
Lemma hold_pbase : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S1a4A4F_;").
Proof using Erd Ewok HMI HXz Hgd Hrom Hsp Hu.
  intros H. pose proof (pbase_cell H) as C0. pose proof (RQ H) as R. pose proof (ceiling_small L) as CS. pose proof (zQ_range H).
  change O_pbase with (carved e_parbase (-16) (-8) [(-16, 8%nat, v 172)]).
  assert (B : bv_unsigned (eval (rho1 mV) e_parbase) = zQm + 16) by (rewrite ev1u by reflexivity; exact (ze_parbase H)).
  assert (AG : loc_addr L (LMem (am_mem amPar)) = zQm + 16 + (-16)) by (unfold zQm, addr_of; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. apply (cell_rw0 _ zQ (zQm + 16) (-16) 8 C0 eq_refl eq_refl); [exact AG|lia].
  - unfold cells_in_view. constructor; [|constructor].
    apply (cell_view0 _ _ (zQm + 16) (-16) 8 _ C0 eq_refl eq_refl ltac:(lia)); [exact AG|]. rewrite ev1 by reflexivity. rewrite (ze172 H). reflexivity.
Qed.
Lemma hold_pmeta : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S1a5A4F_;").
Proof using Erd Ewok HMI Hgd Hrom Hsp Hu.
  intros H. pose proof (pmeta_cells H) as (C2 & C3 & C4 & C5). pose proof (RQ H) as R. pose proof (ceiling_small L) as CS. pose proof (zQ_range H) as ZQ.
  change O_pmeta with (carved (v 172) 16 40 [(16, 8%nat, e_pmem); (24, 4%nat, v 173); (28, 4%nat, v 174); (32, 8%nat, v 169)]).
  assert (B : bv_unsigned (eval (rho1 mV) (v 172)) = zQ) by (rewrite ev1u by reflexivity; exact (ze172 H)).
  assert (AG : forall d, loc_addr L (LMem (padd gPar d)) = zQ + d) by (intros d; unfold zQ; apply AGq).
  unfold META_mem, META_avail, META_freed, META_bits in C2, C3, C4, C5.
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try (unfold META_SIZE, PGSZ in *; lia).
  - cells_inside_tac.
  - intros o Ho. destruct (Z_lt_dec o 24) as [O2|O2]; [|destruct (Z_lt_dec o 28) as [O3|O3]; [|destruct (Z_lt_dec o 32) as [O4|O4]]].
    + apply (cell_rw0 _ zQm zQ 16 8 C2 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ (am_avail amPar) zQ 24 4 C3 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ (am_freed amPar) zQ 28 4 C4 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ (meta_bits amPar) zQ 32 8 C5 eq_refl eq_refl); [apply AG|lia].
  - unfold cells_in_view. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply (cell_view0 _ _ zQ 16 8 _ C2 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by reflexivity. rewrite (ze_pmem H). reflexivity.
    + apply (cell_view0m _ (am_avail amPar) zQ 24 4 _ C3 eq_refl eq_refl ltac:(lia)); [apply AG | reflexivity |]. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (ze173 H). rewrite Z.mod_small; lia.
    + apply (cell_view0m _ (am_freed amPar) zQ 28 4 _ C4 eq_refl eq_refl ltac:(lia)); [apply AG | reflexivity |]. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (ze174 H). rewrite Z.mod_small; lia.
    + apply (cell_view0 _ _ zQ 32 8 _ C5 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by reflexivity. rewrite (ze169 H). reflexivity.
Qed.

Lemma sec_byte j : ltac2:(tb__ "0|1|
S162Vj;U8M0A2S4S0Se4S108VL;A1G0Vj;A3Se4S132VL;A1G0Vj;A3A3F_;").
Proof using Hgd rho.
  intros Hj. unfold le_byte, zSec. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma hold_parea : ltac2:(tb__ "0|0|
S4S0S1cVam;A1Z0A3S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S1a3A4F_;").
Proof using Erd Ewok HMI Hgd Hrom Hsp Hu.
  intros H. destruct (par_area H) as (a & Ha & Ea & Z1 & Z2 & Ca). pose proof (ceiling_small L) as CS. pose proof zSec_range.
  change O_parea with (carved e_parea 0 8 [(0, 8%nat, v 136)]).
  assert (B : bv_unsigned (eval (rho1 mV) e_parea) = zQa) by (rewrite ev1u by reflexivity; exact (ze_parea H)).
  assert (AG : loc_addr L (LMem a) = zQa + 0) by (unfold addr_of in Ea; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. apply (cell_rw0 _ (ly_sec L) zQa 0 8 Ca eq_refl eq_refl); [exact AG|lia].
  - unfold cells_in_view. constructor; [|constructor].
    intros j Hj. destruct (cell_bytes0 _ (ly_sec L) Ca eq_refl j Hj) as (_ & _ & R). cbn [mc_loc mc_w] in R. rewrite AG in R. rewrite R.
    rewrite (ev1 mV (v 136) eq_refl), ze136, nth_enc_bytes by lia. cbn [mc_w]. rewrite sec_byte by exact Hj. reflexivity.
Qed.
Lemma hold_secret : ltac2:(tb__ "0|0|
S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S1a6A4").
Proof using Erd Ewok HMI Hgd Hrom Hsp Hu.
  pose proof secret_cell as Cs. pose proof (ceiling_small L) as CS. pose proof zSec_range. pose proof Hctx as HCX.
  change O_secret with (carved (SLit 0x5a3d0) 0 8 [(0, 8%nat, v 136)]).
  assert (B : bv_unsigned (eval (rho1 mV) (SLit 0x5a3d0)) = 0x5a3d0) by (cbn [eval]; apply u64; lia).
  assert (AG : loc_addr L (LCtx CTX_secret) = 0x5a3d0 + 0) by (cbn [loc_addr]; rewrite HCX; unfold CTX_secret; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. apply (cell_rw0 _ (ly_sec L) 0x5a3d0 0 8 Cs eq_refl eq_refl); [exact AG|lia].
  - unfold cells_in_view. constructor; [|constructor].
    intros j Hj. destruct (cell_bytes0 _ (ly_sec L) Cs eq_refl j Hj) as (_ & _ & R). cbn [mc_loc mc_w] in R. rewrite AG in R. rewrite R.
    rewrite (ev1 mV (v 136) eq_refl), ze136, nth_enc_bytes by lia. cbn [mc_w]. rewrite sec_byte by exact Hj. reflexivity.
Qed.
End Inst.
End Mal_nt_Ic.

Module Mal_nt_D.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Inst.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
S186Sd3VX;S6aS71S1bS0A2S6dS1bS0Vg;Vi;A4A2VU;S185Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Hypothesis Hu : ltac2:(tb__ "0|0|
SdbVX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Notation "§14§ h__" := (h__ s L X U g i vm rd0 wok0 HMI) (at level 10, h__ global).
Local Abbreviation HI := (§14§ U.Mal_nt__G1.Mal_nt_I.HI).
Local Abbreviation HL := (§14§ U.Mal_nt__G1.Mal_nt_I.HL).
Local Abbreviation HV := (§14§ U.Mal_nt__G1.Mal_nt_I.HV).
Local Abbreviation HLG := (§14§ U.Mal_nt__G1.Mal_nt_I.HLG).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S4S0Sd0Q40S4aVrho;PcA2A2Sd2VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S4S0Sd0Q40S4aVrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Abbreviation zM := (@U.Mal_nt__G1.Mal_nt_I.zM L am).
Local Abbreviation zPv := (@U.Mal_nt__G1.Mal_nt_I.zPv L am).
Local Abbreviation zNx := (@U.Mal_nt__G1.Mal_nt_I.zNx L am).
Local Notation "§15§ h__" := (h__ s X g am Hu) (at level 10, h__ global).
Local Abbreviation g_key := (§15§ U.Mal_nt__G1.Mal_nt_I.g_key).
Local Notation "§16§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation R_all := (§16§ U.Mal_nt__G1.Mal_nt_I.R_all).
Local Abbreviation zPv_range := (§16§ U.Mal_nt__G1.Mal_nt_I.zPv_range).
Local Abbreviation zNx_range := (§16§ U.Mal_nt__G1.Mal_nt_I.zNx_range).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Notation "§17§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation hQ := (§17§ U.Mal_nt__G1.Mal_nt_I.hQ).
Local Abbreviation ahQ := (§17§ U.Mal_nt__G1.Mal_nt_I.ahQ).
Local Abbreviation tQ := (§17§ U.Mal_nt__G1.Mal_nt_I.tQ).
Local Abbreviation atQ := (§17§ U.Mal_nt__G1.Mal_nt_I.atQ).
Local Abbreviation zH := (@U.Mal_nt__G1.Mal_nt_I.zH s L am).
Local Notation "§18§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation zHp := (§18§ U.Mal_nt__G1.Mal_nt_I.zHp).
Local Abbreviation zHp_eq := (@U.Mal_nt__G1.Mal_nt_I.zHp_eq s L X U g am i vm rd0 wok0 HMI).
Local Abbreviation zH_range := (§16§ U.Mal_nt__G1.Mal_nt_I.zH_range).
Local Abbreviation fmQ := (@U.Mal_nt__G1.Mal_nt_I.fmQ s g).
Local Abbreviation ftQ := (@U.Mal_nt__G1.Mal_nt_I.ftQ s g).
Local Abbreviation zF := (@U.Mal_nt__G1.Mal_nt_I.zF s L).
Local Abbreviation zFp := (@U.Mal_nt__G1.Mal_nt_I.zFp s L g).
Local Abbreviation fmem := (@U.Mal_nt__G1.Mal_nt_I.fmem s X).
Local Abbreviation fmem_facts := (§15§ U.Mal_nt__G1.Mal_nt_I.fmem_facts).
Local Abbreviation fmL_cases := (@U.Mal_nt__G1.Mal_nt_I.fmL_cases s L X U g am i vm rd0 wok0 HMI Hu).
Local Abbreviation zF_range := (§16§ U.Mal_nt__G1.Mal_nt_I.zF_range).
Local Abbreviation zFp_range := (§16§ U.Mal_nt__G1.Mal_nt_I.zFp_range).
Local Abbreviation nQ := (@U.Mal_nt__G1.Mal_nt_I.nQ g am).
Local Abbreviation pQ := (@U.Mal_nt__G1.Mal_nt_I.pQ g am).
Local Abbreviation anQ := (§17§ U.Mal_nt__G1.Mal_nt_I.anQ).
Local Abbreviation apQ := (§17§ U.Mal_nt__G1.Mal_nt_I.apQ).
Local Abbreviation zNm := (§18§ U.Mal_nt__G1.Mal_nt_I.zNm).
Local Abbreviation gPar := (§17§ U.Mal_nt__G1.Mal_nt_I.gPar).
Local Abbreviation iPar := (§17§ U.Mal_nt__G1.Mal_nt_I.iPar).
Local Abbreviation amPar := (§17§ U.Mal_nt__G1.Mal_nt_I.amPar).
Local Abbreviation zQ := (§18§ U.Mal_nt__G1.Mal_nt_I.zQ).
Local Abbreviation zQm := (§18§ U.Mal_nt__G1.Mal_nt_I.zQm).
Local Abbreviation zQa := (§18§ U.Mal_nt__G1.Mal_nt_I.zQa).
Local Notation "§19§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§19§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation zr1 := (§19§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§19§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation zr1_any := (§19§ U.Mal_nt__G1.Mal_nt_I.zr1_any).
Local Abbreviation zl1_any := (§19§ U.Mal_nt__G1.Mal_nt_I.zl1_any).
Local Abbreviation hQ_used := (§16§ U.Mal_nt__G1.Mal_nt_I.hQ_used).
Local Abbreviation tQ_used := (§16§ U.Mal_nt__G1.Mal_nt_I.tQ_used).
Local Abbreviation zHp_range := (@U.Mal_nt__G1.Mal_nt_I.zHp_range s L X U g am i gd vm rd0 wok0 HMI HXz Hgd).
Local Abbreviation nQ_used := (§16§ U.Mal_nt__G1.Mal_nt_I.nQ_used).
Local Abbreviation pQ_used := (§16§ U.Mal_nt__G1.Mal_nt_I.pQ_used).
Local Abbreviation RN := (§16§ U.Mal_nt__G1.Mal_nt_I.RN).
Local Abbreviation gPar_used := (§16§ U.Mal_nt__G1.Mal_nt_I.gPar_used).
Local Abbreviation RQ := (§16§ U.Mal_nt__G1.Mal_nt_I.RQ).
Local Abbreviation zQ_range := (§16§ U.Mal_nt__G1.Mal_nt_I.zQ_range).
Local Abbreviation par_last := (§16§ U.Mal_nt__G1.Mal_nt_I.par_last).
Local Abbreviation zM_eq := (§16§ U.Mal_nt__G1.Mal_nt_I.zM_eq).
Local Abbreviation par_area := (§16§ U.Mal_nt__G1.Mal_nt_I.par_area).
Local Abbreviation ze12 := (@U.Mal_nt__G1.Mal_nt_I.ze12 s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12).
Local Notation "§20§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation ze135 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze135).
Local Abbreviation ze140 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze140).
Local Abbreviation ze141 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze141).
Local Abbreviation ze142 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze142).
Local Abbreviation ze150 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze150).
Local Abbreviation ze165 := (@U.Mal_nt__G1.Mal_nt_I.ze165 s L X U g am i rho gd vm rd0 wok0 HMI HXz Hgd).
Local Abbreviation ze175 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze175).
Local Abbreviation ze178 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze178).
Local Abbreviation ze179 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze179).
Local Abbreviation ze184 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze184).
Local Abbreviation ze160 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze160).
Local Abbreviation ze161 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze161).
Local Abbreviation ze154 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze154).
Local Abbreviation ze156 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze156).
Local Abbreviation ze111 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze111).
Local Abbreviation ze114 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze114).
Local Abbreviation ze172 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze172).
Local Abbreviation e_parbase := (@U.Mal_nt__G1.Mal_nt_I.e_parbase).
Local Abbreviation e_pmem := (@U.Mal_nt__G1.Mal_nt_I.e_pmem).
Local Abbreviation e_parea := (@U.Mal_nt__G1.Mal_nt_I.e_parea).
Local Abbreviation ze_parbase := (§20§ U.Mal_nt__G1.Mal_nt_I.ze_parbase).
Local Abbreviation ze_parea := (§20§ U.Mal_nt__G1.Mal_nt_I.ze_parea).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S5SaZ1000Sd0Q40S4aVrho;PaA2A2M0A2S4S0SfG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S5SaS7eZ40Sd0Q40S4aVrho;PfA2A2A2M0N60A2SaS13SdZ2Z28A2A1G0A2A2").
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S4SceQ40A1S6cSceQ8A1A1F_;Vrd0;S135Sc8VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S4SceQ40A1S6bF_;Vwok0;S136Sc8VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S0S5SaZ0R1A2ScR1Z60A2A2S4S6cSceQ8A1M0A1VmV;ScfQ40SbZ108ecR2A2A2A1S73G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
Sd5Sd4Vrd0;SceQ40A1S70L_;A2Sd6Sd3A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
Sd4S135Sc8VmV;A2S136Sc8VmV;A2A2").
Local Abbreviation O_got := (@U.Mal_nt__G1.Mal_nt_Ib.O_got).
Local Abbreviation O_guard := (@U.Mal_nt__G1.Mal_nt_Ib.O_guard).
Local Abbreviation O_sct := (@U.Mal_nt__G1.Mal_nt_Ib.O_sct).
Local Abbreviation O_metaK := (@U.Mal_nt__G1.Mal_nt_Ib.O_metaK).
Local Abbreviation e_actlo := (@U.Mal_nt__G1.Mal_nt_Ib.e_actlo).
Local Abbreviation e_acthi := (@U.Mal_nt__G1.Mal_nt_Ib.e_acthi).
Local Notation "§21§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_actlo := (§21§ U.Mal_nt__G1.Mal_nt_Ib.ze_actlo).
Local Abbreviation ze_acthi := (§21§ U.Mal_nt__G1.Mal_nt_Ib.ze_acthi).
Local Abbreviation O_act := (@U.Mal_nt__G1.Mal_nt_Ib.O_act).
Local Abbreviation O_seq := (@U.Mal_nt__G1.Mal_nt_Ib.O_seq).
Local Abbreviation O_fmh := (@U.Mal_nt__G1.Mal_nt_Ib.O_fmh).
Local Abbreviation O_useq := (@U.Mal_nt__G1.Mal_nt_Ib.O_useq).
Local Abbreviation free_cells := (@U.Mal_nt__G1.Mal_nt_Ib.free_cells).
Local Abbreviation O_freeK := (@U.Mal_nt__G1.Mal_nt_Ib.O_freeK).
Local Abbreviation e_uslo := (@U.Mal_nt__G1.Mal_nt_Ic.e_uslo).
Local Abbreviation e_ushi := (@U.Mal_nt__G1.Mal_nt_Ic.e_ushi).
Local Abbreviation ze_uslo := (§21§ U.Mal_nt__G1.Mal_nt_Ic.ze_uslo).
Local Abbreviation ze_ushi := (§21§ U.Mal_nt__G1.Mal_nt_Ic.ze_ushi).
Local Abbreviation O_usage := (@U.Mal_nt__G1.Mal_nt_Ic.O_usage).
Local Abbreviation e_bnlo := (@U.Mal_nt__G1.Mal_nt_Ic.e_bnlo).
Local Abbreviation e_bnhi := (@U.Mal_nt__G1.Mal_nt_Ic.e_bnhi).
Local Abbreviation ze_bnlo := (§20§ U.Mal_nt__G1.Mal_nt_Ic.ze_bnlo).
Local Abbreviation ze_bnhi := (§20§ U.Mal_nt__G1.Mal_nt_Ic.ze_bnhi).
Local Abbreviation O_bnc := (@U.Mal_nt__G1.Mal_nt_Ic.O_bnc).
Local Abbreviation O_grp := (@U.Mal_nt__G1.Mal_nt_Ic.O_grp).
Local Abbreviation O_shdr := (@U.Mal_nt__G1.Mal_nt_Ic.O_shdr).
Local Abbreviation O_bptr := (@U.Mal_nt__G1.Mal_nt_Ic.O_bptr).
Local Abbreviation O_pbase := (@U.Mal_nt__G1.Mal_nt_Ic.O_pbase).
Local Abbreviation O_pmeta := (@U.Mal_nt__G1.Mal_nt_Ic.O_pmeta).
Local Abbreviation O_parea := (@U.Mal_nt__G1.Mal_nt_Ic.O_parea).
Local Abbreviation O_secret := (@U.Mal_nt__G1.Mal_nt_Ic.O_secret).

Inductive mkey := KG | KH | KT | KN | KP.
Definition kbase (k : mkey) : sv := ltac2:(tb__ "0|0|
S139S46Lk;Vk;Sc7PcA1Sc7P96A1Sc7Pa5A1Sc7P8dA1Sc7P8cA1X139x5").
Definition kmemv (k : mkey) : sv := ltac2:(tb__ "0|0|
S139S46Lk;Vk;Sc7P8eA1Sc7PafA1Sc7Pb3A1Sc7P9cA1Sc7P6fA1X139x5").
Definition kbitsv (k : mkey) : sv := ltac2:(tb__ "0|0|
S139S46Lk;Vk;Sc7P87A1Sc7Pb2A1Sc7Pb8A1Sc7P9aA1Sc7P72A1X139x5").
Definition kptr (k : mkey) : sptr := ltac2:(tb__ "0|0|
S139S1bLk;Vk;Vg;S129Vs;Vg;Vam;A3S12cVs;Vg;Vam;A3S12aVg;Vam;A2S12bVg;Vam;A2X139x5").
Definition krec (k : mkey) : ameta := ltac2:(tb__ "0|0|
S139S22Lk;Vk;Vam;S11eVs;Vg;Vam;A3S122Vs;Vg;Vam;A3S120Vs;Vg;Vam;A3S121Vs;Vg;Vam;A3X139x5").
Definition klo (k : mkey) : Z := ltac2:(tb__ "0|0|
S139S0Lk;Vk;S112VL;Vg;A2S118Vs;VL;Vam;A3S12fVs;VL;Vg;Vam;A4S130VL;Vam;A2S131VL;Vam;A2X139x5").

Definition kcond (k : mkey) : Prop := ltac2:(tb__ "0|4|
S139OLk;Vk;S8S5S7S4S6cS1bA1M0Se1Vs;S10fVam;A1M1A2S73S1bA1M2A3A1S5SaZ0G1A2ScG1Z30A2A2A2M3G3S7S4G0S20Vam;A1G2A3A1S7S4G0S21Vam;A1G2A3A1X139x5").

Inductive fkey := FG | FM | FT.
Definition fbase (k : fkey) : sv := ltac2:(tb__ "0|0|
S13aS46Lk;Vk;Sc7PcA1Sc7Pa0A1Sc7Pa1A1X13ax3").
Definition fptr (k : fkey) : sptr := ltac2:(tb__ "0|0|
S13aS1bLk;Vk;Vg;S125Vs;Vg;A2S127Vs;Vg;A2X13ax3").
Definition flo (k : fkey) : Z := ltac2:(tb__ "0|0|
S13aS0Lk;Vk;S112VL;Vg;A2S117Vs;VL;A2S12eVs;VL;Vg;A3X13ax3").
Definition fcond (k : fkey) : Prop := ltac2:(tb__ "0|1|
S13aOLk;Vk;S8S7S4S6cS1bA1S26Vs;A1S73S1bA1A3A1M0G0X13ax3").

Inductive od :=
  | OD_got | OD_guard | OD_sct
  | OD_meta (k : mkey) (pv nv av fv : sv)
  | OD_act (hv : sv)
  | OD_seq (x : sv)
  | OD_useq (a b c d : sv)
  | OD_fmh (x : sv)
  | OD_free (k : fkey) (five : bool) (pv nv : sv)
  | OD_usage (x : sv)
  | OD_bnc (x : sv)
  | OD_grp (x : sv)

  | OD_shdr
  | OD_bptr (c0 : sv)
  | OD_pbase
  | OD_pmeta
  | OD_parea
  | OD_secret
  | OD_useqL (cs : list (Z * nat * sv)).

Definition obj_of (d : od) : sobj := ltac2:(tb__ "0|3|
S13bS67Ld;Vd;S1adS1aeS1b0S139S46S46S46S46S1afS14dR5A1R4R3S144R5A1R2R1S143R5A1A7Lfv;Lav;Lnv;Lpv;Lk;S46S1abR1A1Lhv;S46S1b1R1A1Lx;S46S46S46S46S1b2R4R3R2R1A4Ld;Lc;Lb;La;S46S1acR1A1Lx;S13aS6bS46S46S1aaS14cR4A1R3R2R1A4Lnv;Lpv;Lfive;Lk;S46S1c0R1A1Lx;S46S1b8R1A1Lx;S46S1baR1A1Lx;S1bfS46S1b9R1A1Lc0;S1bcS1bdS1bbS1beS74S71S71S0S6eA2M0S46A2M1A1S4cS47Z5a3d0A1S47Z350M2A1S47Z370A1S155G1S48G1G1S48Lc;R1G0S46G0S48Lp;R2S0S6eS49S47SbG2R2A2A1S11R1A1R3A3Lw;Loff;X71x1Le;Lp;X71x1Lc;R1A4S4bA5Lcs;X13bx13").
Definition dlo (d : od) : Z := ltac2:(tb__ "0|7|
S13bS0Ld;Vd;Z28d50Z5a338Z108ecS139S46S46S46S46S13eR5A1Lfv;Lav;Lnv;Lpv;Lk;S46SbZ5a3d0M0SbS10Z8M1S10fVam;A1M2A2M3Z50A2A2Lhv;S46SbG0Z390A2Lx;S46S46S46S46SbG0Z350A2M4Ld0;Lc;Lb;La;S46SbG0Z10M5A2Lx;S13aS6bS46S46S13dR4A1Lnv;Lpv;Lfive;Lk;S46SbG0SbG3Z1d0A2A2Lx;S46SbG0SbS12G2Z7A2Z370A2A2Lx;S46SbS114Vs;VL;Vg;Vam;A4G1A2Lx;S12S119VL;Vam;A2M6Z4A2S46G6Lc0;S11cVs;VL;Vg;Vam;A4SbS11aVs;VL;Vg;Vam;A4G5A2S11bVs;VL;Vg;Vam;A4SbG0Z0A2S74S71S71S0S6eA2S46A2A1G4Lcs;X13bx13").
Definition dsz (d : od) : Z := ltac2:(tb__ "0|5|
S13bS0Ld;Vd;Z8M0G0Z60S139S46S46S46S46Z28M1Lfv;Lav;Lnv;Lpv;Lk;S46G0Lhv;S46Z1Lx;M2S46S46S46S46Z20M3Ld0;Lc;Lb;La;S46G0Lx;M4S13aS6bS46S46G1Lnv;Lpv;Lfive;Lk;G4G2G2Z4S46G0Lc0;G0Z18G0G0S74S71S71S0S6eA2S46A2A1G3Lcs;X13bx13").
Definition dhi (d : od) : Z := ltac2:(tb__ "0|0|
SbS13fVd;A1S151Vd;A1A2").
Definition dcells (d : od) : list (Z * nat * sv) := ltac2:(tb__ "0|13|
S13bS74S71S71S0S6eA2M0S46A2M1A1M2Ld;Vd;S6fG1S6dG0S46S6dS0S6eZ0M3U8M4A4M5S47Z5a338A1A4S72G1A1M6A3S6fG1S6dG0S46G5Sc7P8fA1A4G6A3G6S139S46S46S46S46S6fG1S6dG0S46G5R4A4M7S6fG1S6dG0S46S6dS0S6eZ8M8G4A4R3A4M9S6fG1S6dG0S46S6dS0S6eZ10G4A4MaS144R5A1A4S6fG1S6dG0S46S6dS0S6eZ18MbU4McA4R2A4S6fG1S6dG0S46S6dS0S6eZ1cGcA4R1A4S6fG1S6dG0S46S6dS0S6eZ20G4A4S143R5A1A4G6A3A3A3A3A3A3Lfv;Lav;Lnv;Lpv;Lk;S46S6fG1S6dG0S46G5R1A4G6A3MdLhv;S46S6fG1S6dG0S46S6dS0S6eG3U1MeA4MfR1A4G6A3Lx;M10S46S46S46S46S6fG1G7S6fG1G9S6fG1S6dG0S46GaR2A4S6fG1S6dG0S46S6dS0S6eGbG4A4R1A4G6A3A3A3A3Ld;Lc;Lb;La;S46GdLx;M11S13aS6bS46S46S1b3R3R2R1A3Lnv;Lpv;Lfive;Lk;G11G10G10S6fG1S6dG0S46GfS47G3A1A4S6fG1S6dG0S46S6dS0S6eZ1GeA4Sc7PaaA1A4S6fG1S6dG0S46S6dS0S6eZ2U2A4Sc7PabA1A4G6A3A3A3S46GdLc0;S6fG1S6dG0S46G5Sc7PacA1A4G6A3S6fG1S6dG0S46G5S115A4S6fG1S6dG0S46S6dS0S6eG8GcA4Sc7PadA1A4S6fG1S6dG0S46S6dS0S6eZcGcA4Sc7PaeA1A4S6fG1S6dG0S46GaSc7Pa9A1A4G6A3A3A3A3S6fG1S6dG0S46G5Sc7P88A1A4G6A3M12G12G2R1Lcs;X13bx13").
Definition drom (d : od) : option positive := match d with OD_sct => Some 1%positive | _ => None end.
Definition od_svs (d : od) : list sv := ltac2:(tb__ "0|2|
S155S71S71S0S6eA2M0S46A2M1S46G1S78G0S46R1A3Lc;S149Vd;A1A4").
Definition sv_sem (e : sv) : bool := ltac2:(tb__ "0|0|
S75S18aS18fVe;A2S7cVe;A1A2").

Definition useq_okb (cs : list (Z * nat * sv)) : bool := ltac2:(tb__ "0|7|
S75ScaS71S71S0S6eA2M0S46A2M1G1G1S6bLc;M2R1G0S46G0S6bLp;M3R2S0S6eS75S75S75S17Z0M4R2A2S17SbR2S11R1A1A2M5Z20M6A2A2S1b4U1R1A2A2S1b4R1U8A2A2Lw;Loff;X71x1Ls0;Lp;X71x1Lc;Vcs;A3ScaS0S0SccG1G1G2R1G0S46G3R2S0S6eS75S17R2R6A2S19R6G5A2A2Lw;Loff;X71x1Ls0;Lp;X71x1Lc;Vcs;A3Lx;S10aG4G6A2A3A2").
Definition dsxb (d : od) : bool := match d with OD_useqL cs => useq_okb cs | _ => true end.
Definition ds_checkb (d : od) : bool := ltac2:(tb__ "0|0|
S75ScaS46S148S147Vd;A1A3S140Vd;A1A2").

Definition dcond (d : od) : Prop := ltac2:(tb__ "0|4|
S13bOLd;Vd;S8S8S8S139S46S46S46S46S8Lfv;Lav;Lnv;Lpv;Lk;S46S8Lhv;S46S8Lx;M0S46S46S46S46S8Ld0;Lc;Lb;La;G0S13aS6bS46S46S8Lnv;Lpv;Lfive;Lk;S46S5SaZ0M1S10fVam;A1M2A2ScG2Z30A2A2Lx;S46S5SaZ7G2A2ScG2Z27A2A2Lx;G0S4S0S1cVam;A1G1A3M3S46G3Lc0;G3G3G3S8S74S71S71S0S6eA2S46A2A1S8Lcs;X13bx13").

Definition DS (d : od) : Prop := ltac2:(tb__ "0|0|
S5S4S6bS150Vd;A1S70A3S14aVd;A1A2").
Lemma DS_svs d : ltac2:(tb__ "0|0|
S13cVd;A1S4S6bScaS46S148S147Vd;A1A3S70A3F_;").
Proof using . intros [H _]. unfold ds_checkb in H. apply andb_prop in H as [H _]. exact H. Qed.
Lemma DS_x d : ltac2:(tb__ "0|0|
S13cVd;A1S4S6bS140Vd;A1S70A3F_;").
Proof using . intros [H _]. unfold ds_checkb in H. apply andb_prop in H as [_ H]. exact H. Qed.
Lemma DS_intro d : ltac2:(tb__ "0|0|
S4S6bScaS46S148S147Vd;A1A3S70A3S4S6bS140Vd;A1S70A3S14aVd;A1S13cVd;A1F_;F_;F_;").
Proof using . intros A B C. split; [|exact C]. unfold ds_checkb. rewrite A, B. reflexivity. Qed.

Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S1a9VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Ltac in_list := cbn; repeat (first [left; reflexivity | right]).

Lemma par_ranges : ltac2:(tb__ "0|7|
S4S0S1cVam;A1Z0A3S5SaSbZ1000M0Z10M1A2S119VL;Vam;A2M2A2S5SaSbG2Z8A2Sd1VL;A1M3A2S5SaG0S11cVs;VL;Vg;Vam;A4M4A2S5SaSbG4G1A2G2A2S5SaG0S11aVs;VL;Vg;Vam;A4M5A2S5SaSbG5Z28A2G3A2S5SaG0S11bVs;VL;Vg;Vam;A4M6A2SaSbG6G0A2G3A2A2A2A2A2A2A2A2F_;").
Proof using HMI Hgd Hsp Hu.
  intros H. pose proof (zQ_range H). destruct (par_area H) as (a & _ & _ & A1 & A2 & _). pose proof (RQ H) as (_ & _ & _ & Q1 & Q2).
  pose proof (zM_eq H) as EM. pose proof (par_last H) as (Hi & Hl & Hsc & SP).
  destruct (group_range X (Some (g, i)) U s L HI HL C_U vm gPar amPar (gPar_used H) HV HLG) as (G1 & G2 & _).
  assert (0 <= stride_of amPar * iPar) by nia. assert (stride_of amPar * (iPar + 1) <= stride_of amPar * (am_last amPar + 1)) by nia.
  unfold group_extent, zQm, UNIT, IB, PGSZ in *. lia.
Qed.
Lemma sv_sem_of d off w e : ltac2:(tb__ "0|1|
S13cVd;A1Sc9S71S71S0S6eA2M0S46A2S6dG0S46S6dS0S6eVoff;Vw;A4Ve;A4S149Vd;A1A3S5S4S6bS18aS18fVe;A2S70A3S4S6bS7cVe;A1S70A3A2F_;F_;").
Proof using .
  intros Hd0 Hin. pose proof (DS_svs d Hd0) as Hd. unfold od_svs in Hd. pose proof (proj1 (forallb_forall _ _) Hd e ltac:(apply in_map_iff; exists (off, w, e); auto)) as S0.
  unfold sv_sem in S0. apply andb_prop in S0 as [S1 S2]. auto.
Qed.

Lemma ze_kbase k : ltac2:(tb__ "0|0|
S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S14dVk;A1A3S13eVk;A1A3").
Proof using HMI HP12 HXz Hgd Hu. destruct k; cbn [kbase klo]; [apply ze12 | apply ze150 | apply ze165 | apply ze141 | apply ze140]. Qed.
Lemma klo_range k : ltac2:(tb__ "0|1|
S5SaZ0S13eVk;A1M0A2SaSbG0Z28A2Sd1VL;A1A2A2").
Proof using HMI HXz Hgd Hu rho. pose proof R_all as R. pose proof zH_range. pose proof zHp_range. pose proof zNx_range. pose proof zPv_range. destruct k; cbn [klo]; lia. Qed.
Lemma klo_ptr k : ltac2:(tb__ "0|0|
S152Vk;A1S4S0S13eVk;A1Sd2VL;S145Vk;A1A2A3F_;").
Proof using HMI.
  destruct k; cbn [kcond klo kptr]; intros Hc; [reflexivity| | | |].
  - destruct Hc as [Hnz _]. unfold zH, hQ. destruct (active_hd s sc); [reflexivity | exfalso; exact (Hnz eq_refl)].
  - destruct Hc as [Hnz Hsc']. destruct (active_hd s sc) as [h|] eqn:E; [exact (zHp_eq Hsc' h E) | exfalso; exact (Hnz eq_refl)].
  - unfold zNx, nQ. destruct (am_next am); [reflexivity | exfalso; exact (Hc eq_refl)].
  - unfold zPv, pQ. destruct (am_prev am); [reflexivity | exfalso; exact (Hc eq_refl)].
Qed.
Lemma kptr_used k : ltac2:(tb__ "0|0|
SdbVX;Vs;S145Vk;A1S146Vk;A1A4").
Proof using HMI Hgd Hu. destruct k; cbn [kptr krec]; [exact Hu | exact hQ_used | exact tQ_used | exact nQ_used | exact pQ_used]. Qed.
Lemma kptr_key k : ltac2:(tb__ "0|0|
Sc9S1bS145Vk;A1Se3Vs;A1A3").
Proof using HMI Hgd Hu. eapply MT_Some_In_keys. exact (proj1 (usedX_MT _ _ _ _ (kptr_used k))). Qed.
Lemma ze_kmemv k : ltac2:(tb__ "0|0|
S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S144Vk;A1A3Sd2VL;S23S146Vk;A1A1A2A3").
Proof using HMI Hgd Hu. destruct k; cbn [kmemv krec]; [apply ze142 | apply ze175 | apply ze179 | apply ze156 | apply ze111]. Qed.
Lemma ze_kbitsv k : ltac2:(tb__ "0|0|
S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S143Vk;A1A3SdcS146Vk;A1A1A3").
Proof using HMI Hgd Hu. destruct k; cbn [kbitsv krec]; [apply ze135 | apply ze178 | apply ze184 | apply ze154 | apply ze114]. Qed.

Lemma ze_fbase k : ltac2:(tb__ "0|0|
S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S14cVk;A1A3S13dVk;A1A3").
Proof using HMI HP12 Hgd Hu. destruct k; cbn [fbase flo]; [apply ze12 | apply ze160 | apply ze161]. Qed.
Lemma flo_range k : ltac2:(tb__ "0|1|
S5SaZ0S13dVk;A1M0A2SaSbG0Z28A2Sd1VL;A1A2A2").
Proof using HMI Hgd Hu rho. pose proof R_all as R. pose proof zF_range. pose proof zFp_range. destruct k; cbn [flo]; lia. Qed.
Lemma fptr_facts k : ltac2:(tb__ "0|1|
S141Vk;A1S5S4S0S13dVk;A1Sd2VL;S142Vk;A1M0A2A3S5Sc9S1bG0Se3Vs;A1A3S7S4S13aVk;S14fA3A1S126Vs;VX;G0A3F_;A2A2F_;").
Proof using HMI Hu.
  destruct k; cbn [fcond flo fptr]; intros Hc.
  - split; [reflexivity|]. split; [exact g_key|]. intros NE. exfalso. exact (NE eq_refl).
  - unfold zF. destruct fmL_cases as [(E & _) | (fm & pr & nx & E & Efm & Hfm & _)]; [exfalso; exact (Hc E)|].
    rewrite E, Efm. cbn [optrA]. destruct (fmem_facts fm Hfm) as (_ & _ & _ & _ & _ & K & _). split; [reflexivity|]. split; [exact K|]. intros _. exact Hfm.
  - unfold zFp. destruct fmL_cases as [(E & _) | (fm & pr & nx & E & Efm & Hfm & M & EL & Hpr & Hnx & Eft & _)]; [exfalso; exact (Hc E)|].
    rewrite EL, Eft. cbn [optrA fst]. destruct (fmem_facts pr Hpr) as (_ & _ & _ & _ & _ & K & _). split; [reflexivity|]. split; [exact K|]. intros _. exact Hpr.
Qed.
Lemma flo_ptr k : ltac2:(tb__ "0|0|
S141Vk;A1S4S0S13dVk;A1Sd2VL;S142Vk;A1A2A3F_;").
Proof using HMI Hu. intros Hc. exact (proj1 (fptr_facts k Hc)). Qed.
Lemma fptr_key k : ltac2:(tb__ "0|0|
S141Vk;A1Sc9S1bS142Vk;A1Se3Vs;A1A3F_;").
Proof using HMI Hu. intros Hc. exact (proj1 (proj2 (fptr_facts k Hc))). Qed.

Lemma rngD d rhoX : ltac2:(tb__ "0|0|
S13cVd;A1S190VrhoW;VrhoX;A2S4S71S0S0A2S65VrhoX;S153Vd;A1A2S6dS0S0S13fVd;A1S14bVd;A1A4A3F_;F_;").
Proof using HMI HP12 HXz Hgd Hsp Hu mW.
  intros Hd Hag. pose proof (proj2 Hd) as HC. unfold dhi. pose proof R_all as R. pose proof (ceiling_small L). pose proof RN as R2.
  assert (EVX : forall e z, sv_vars_all below200 e = true -> zsupported e = true -> zeval zr1 zl1 e = z -> 0 <= z < 2 ^ 64 -> bv_unsigned (eval rhoX e) = z).
  { intros e z Hv Hs Ez Hz. rewrite (EVu rhoW zr1 zl1 (zr1_any mW) (zl1_any mW) rhoX e Hag Hv Hs). exact Ez. }
  destruct d; cbn [obj_of dlo dsz dcond] in HC |- *; unfold O_got, O_guard, O_sct, O_metaK, O_act, O_seq, O_useq, O_fmh, O_freeK, O_usage, O_bnc, O_grp, O_shdr, O_bptr, O_pbase, O_pmeta, O_parea, O_secret, carved, obj_range, obj_lo_of, obj_hi_of; cbn [ob_base ob_lo ob_hi];
    rewrite ?soff_lit_small by lia; try (pose proof (par_ranges HC) as PR).
  - cbn [eval]. rewrite u64 by lia. f_equal; lia.
  - cbn [eval]. rewrite u64 by lia. f_equal; lia.
  - cbn [eval]. rewrite u64 by lia. f_equal; lia.
  - pose proof (klo_range k). rewrite (EVX (kbase k) (klo k) ltac:(destruct k; reflexivity) ltac:(destruct k; reflexivity) (ze_kbase k)) by lia. f_equal; lia.
  - cbn [eval]. rewrite u64 by lia. unfold sc in *.
    rewrite (soff_semX rhoW zr1 zl1 (zr1_any mW) (zl1_any mW) rhoX e_actlo (8 * am_sc am + 80) Hag eq_refl eq_refl ze_actlo) by lia.
    rewrite (soff_semX rhoW zr1 zl1 (zr1_any mW) (zl1_any mW) rhoX e_acthi (8 * am_sc am + 88) Hag eq_refl eq_refl ze_acthi) by lia.
    f_equal; lia.
  - cbn [eval]. rewrite u64 by lia. f_equal; lia.
  - cbn [eval]. rewrite u64 by lia. f_equal; lia.
  - cbn [eval]. rewrite u64 by lia. f_equal; lia.
  - pose proof (flo_range k). rewrite (EVX (fbase k) (flo k) ltac:(destruct k; reflexivity) ltac:(destruct k; reflexivity) (ze_fbase k)) by lia. f_equal; lia.
  - cbn [eval]. rewrite u64 by lia. unfold sc in *.
    rewrite (soff_semX rhoW zr1 zl1 (zr1_any mW) (zl1_any mW) rhoX e_uslo (8 * am_sc am + 464) Hag eq_refl eq_refl ze_uslo) by lia.
    rewrite (soff_semX rhoW zr1 zl1 (zr1_any mW) (zl1_any mW) rhoX e_ushi (8 * am_sc am + 472) Hag eq_refl eq_refl ze_ushi) by lia.
    f_equal; lia.
  - cbn [eval]. rewrite u64 by lia. unfold sc in *.
    rewrite (soff_semX rhoW zr1 zl1 (zr1_any mW) (zl1_any mW) rhoX e_bnlo (am_sc am - 7 + 880) Hag eq_refl eq_refl (ze_bnlo HC)) by lia.
    rewrite (soff_semX rhoW zr1 zl1 (zr1_any mW) (zl1_any mW) rhoX e_bnhi (am_sc am - 7 + 881) Hag eq_refl eq_refl (ze_bnhi HC)) by lia.
    f_equal; lia.
  - rewrite (EVX (v 156) zNm eq_refl eq_refl ze156) by lia. f_equal; lia.
  - rewrite (EVX (v 142) zM eq_refl eq_refl ze142) by lia. f_equal; lia.
  - rewrite (EVX (v 142) zM eq_refl eq_refl ze142) by lia. f_equal; lia.
  - rewrite (EVX e_parbase (zQm + 16) eq_refl eq_refl (ze_parbase HC)) by lia. f_equal; lia.
  - rewrite (EVX (v 172) zQ eq_refl eq_refl (ze172 HC)) by lia. f_equal; lia.
  - rewrite (EVX e_parea zQa eq_refl eq_refl (ze_parea HC)) by lia. f_equal; lia.
  - cbn [eval]. rewrite u64 by lia. f_equal; lia.
  - cbn [eval]. rewrite u64 by lia. f_equal; lia.
Qed.

Lemma klo_range' k : ltac2:(tb__ "0|1|
S5SaZ0S13eVk;A1M0A2SaSbG0Z28A2Sd1VL;A1A2A2"). Proof using HMI HXz Hgd Hu rho. apply klo_range. Qed.

Lemma range64D d : ltac2:(tb__ "0|0|
S13cVd;A1S5SaZ0S13fVd;A1A2ScS14bVd;A1SdZ2Z3fA2A2A2F_;").
Proof using HMI HXz Hgd Hsp Hu.
  intros Hd. pose proof (proj2 Hd) as HC. unfold dhi. pose proof R_all as R. pose proof (ceiling_small L). pose proof RN.
  destruct d; cbn [dcond] in HC; cbn [dlo dsz]; try (pose proof (klo_range' k)); try (pose proof (flo_range k)); try (pose proof (par_ranges HC)); unfold sc; top_ranges; lia.
Qed.

Lemma useq_okb_cell cs off w e : ltac2:(tb__ "0|1|
S4S6bS14eVcs;A1S70A3Sc9S71S71S0S6eA2M0S46A2S6dG0S46S6dS0S6eVoff;Vw;A4Ve;A4Vcs;A3S5SaZ0Voff;A2S5SaSbVoff;S11Vw;A1A2Z20A2S5S163U1Vw;A2S163Vw;U8A2A2A2A2F_;F_;").
Proof using Hgd rho.
  intros H Hin. unfold useq_okb in H. apply andb_prop in H as [H _].
  pose proof (proj1 (forallb_forall _ _) H (off, w, e) Hin) as Y. cbn beta in Y.
  apply andb_prop in Y as [Y Y4]. apply andb_prop in Y as [Y Y3]. apply andb_prop in Y as [Y1 Y2].
  apply Z.leb_le in Y1. apply Z.leb_le in Y2. apply Nat.leb_le in Y3. apply Nat.leb_le in Y4. lia.
Qed.
Lemma useq_okb_cover cs x : ltac2:(tb__ "0|1|
S4S6bS14eVcs;A1S70A3S5SaZ0Vx;A2ScVx;Z20A2A2S6S0S0S6S6eS6eS6S46S46S5Sc9S71S71S0S6eA2M0S46A2S6dG0S46S6dS0S6eR3R2A4R1A4Vcs;A3S5SaR3Vx;A2ScVx;SbR3S11R2A1A2A2A2A2Le;A2Lw;A2Loff;A2F_;F_;").
Proof using Hgd rho.
  intros H Hx. unfold useq_okb in H. apply andb_prop in H as [_ H].
  pose proof (proj1 (forallb_forall _ _) H x ltac:(apply zseq_In; lia)) as Y. apply existsb_exists in Y as ([[off w] e] & Hin & Y).
  apply andb_prop in Y as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.ltb_lt in Y2. exists off, w, e. auto.
Qed.

End Inst.
End Mal_nt_D.

Module Mal_nt_Db.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Inst.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
S186Sd3VX;S6aS71S1bS0A2S6dS1bS0Vg;Vi;A4A2VU;S185Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Hypothesis Hu : ltac2:(tb__ "0|0|
SdbVX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S4S0Sd0Q40S4aVrho;PcA2A2Sd2VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S4S0Sd0Q40S4aVrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Abbreviation zM := (@U.Mal_nt__G1.Mal_nt_I.zM L am).
Local Notation "§22§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation R_all := (§22§ U.Mal_nt__G1.Mal_nt_I.R_all).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Notation "§23§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation zNm := (§23§ U.Mal_nt__G1.Mal_nt_I.zNm).
Local Abbreviation zA8 := (@U.Mal_nt__G1.Mal_nt_I.zA8 s L g am rd0).
Local Notation "§24§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation gPar := (§24§ U.Mal_nt__G1.Mal_nt_I.gPar).
Local Abbreviation amPar := (§24§ U.Mal_nt__G1.Mal_nt_I.amPar).
Local Abbreviation zQ := (§23§ U.Mal_nt__G1.Mal_nt_I.zQ).
Local Abbreviation zQm := (§23§ U.Mal_nt__G1.Mal_nt_I.zQm).
Local Abbreviation zQa := (§23§ U.Mal_nt__G1.Mal_nt_I.zQa).
Local Notation "§25§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§25§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation zr1 := (§25§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§25§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation zr1_any := (§25§ U.Mal_nt__G1.Mal_nt_I.zr1_any).
Local Abbreviation zl1_any := (§25§ U.Mal_nt__G1.Mal_nt_I.zl1_any).
Local Abbreviation RN := (§22§ U.Mal_nt__G1.Mal_nt_I.RN).
Local Notation "§26§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation ze142 := (§26§ U.Mal_nt__G1.Mal_nt_I.ze142).
Local Abbreviation ze156 := (§26§ U.Mal_nt__G1.Mal_nt_I.ze156).
Local Abbreviation ze172 := (§26§ U.Mal_nt__G1.Mal_nt_I.ze172).
Local Abbreviation e_parbase := (@U.Mal_nt__G1.Mal_nt_I.e_parbase).
Local Abbreviation e_pmem := (@U.Mal_nt__G1.Mal_nt_I.e_pmem).
Local Abbreviation e_parea := (@U.Mal_nt__G1.Mal_nt_I.e_parea).
Local Abbreviation ze_parbase := (§26§ U.Mal_nt__G1.Mal_nt_I.ze_parbase).
Local Abbreviation ze_parea := (§26§ U.Mal_nt__G1.Mal_nt_I.ze_parea).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S5SaZ1000Sd0Q40S4aVrho;PaA2A2M0A2S4S0SfG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S5SaS7eZ40Sd0Q40S4aVrho;PfA2A2A2M0N60A2SaS13SdZ2Z28A2A1G0A2A2").
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S4SceQ40A1S6cSceQ8A1A1F_;Vrd0;S135Sc8VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S4SceQ40A1S6bF_;Vwok0;S136Sc8VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S0S5SaZ0R1A2ScR1Z60A2A2S4S6cSceQ8A1M0A1VmV;ScfQ40SbZ108ecR2A2A2A1S73G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
Sd5Sd4Vrd0;SceQ40A1S70L_;A2Sd6Sd3A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
Sd4S135Sc8VmV;A2S136Sc8VmV;A2A2").
Local Abbreviation ev1 := (§25§ U.Mal_nt__G1.Mal_nt_Ib.ev1).
Local Abbreviation O_got := (@U.Mal_nt__G1.Mal_nt_Ib.O_got).
Local Abbreviation O_guard := (@U.Mal_nt__G1.Mal_nt_Ib.O_guard).
Local Abbreviation O_metaK := (@U.Mal_nt__G1.Mal_nt_Ib.O_metaK).
Local Notation "§27§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hgd Hsp mV Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_got := (§27§ U.Mal_nt__G1.Mal_nt_Ib.hold_got).
Local Abbreviation hold_guard := (@U.Mal_nt__G1.Mal_nt_Ib.hold_guard s L g am i rho gd rd0 Hgd Hsp mV Erd ms Hrom Hgd_holds).
Local Abbreviation hold_sct := (@U.Mal_nt__G1.Mal_nt_Ib.hold_sct s L g am i rho gd rd0 Hgd mV ms Hrom Hm_sct).
Local Notation "§28§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hgd Hsp Hdepth mV Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_metaK := (§28§ U.Mal_nt__G1.Mal_nt_Ib.hold_metaK).
Local Abbreviation e_actlo := (@U.Mal_nt__G1.Mal_nt_Ib.e_actlo).
Local Notation "§29§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_actlo := (§29§ U.Mal_nt__G1.Mal_nt_Ib.ze_actlo).
Local Abbreviation O_act := (@U.Mal_nt__G1.Mal_nt_Ib.O_act).
Local Notation "§30§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp mV Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_act := (§30§ U.Mal_nt__G1.Mal_nt_Ib.hold_act).
Local Abbreviation O_seq := (@U.Mal_nt__G1.Mal_nt_Ib.O_seq).
Local Abbreviation hold_seq := (§28§ U.Mal_nt__G1.Mal_nt_Ib.hold_seq).
Local Abbreviation O_fmh := (@U.Mal_nt__G1.Mal_nt_Ib.O_fmh).
Local Abbreviation hold_fmh := (§28§ U.Mal_nt__G1.Mal_nt_Ib.hold_fmh).
Local Abbreviation O_useq := (@U.Mal_nt__G1.Mal_nt_Ib.O_useq).
Local Abbreviation useq_byte_rd := (@U.Mal_nt__G1.Mal_nt_Ib.useq_byte_rd s L X U g i rho gd vm rd0 wok0 HMI Hgd mV Erd Ewok).
Local Abbreviation hold_useq := (§27§ U.Mal_nt__G1.Mal_nt_Ib.hold_useq).
Local Abbreviation free_cells := (@U.Mal_nt__G1.Mal_nt_Ib.free_cells).
Local Abbreviation O_freeK := (@U.Mal_nt__G1.Mal_nt_Ib.O_freeK).
Local Abbreviation hold_freeK := (§28§ U.Mal_nt__G1.Mal_nt_Ic.hold_freeK).
Local Abbreviation e_uslo := (@U.Mal_nt__G1.Mal_nt_Ic.e_uslo).
Local Abbreviation ze_uslo := (§29§ U.Mal_nt__G1.Mal_nt_Ic.ze_uslo).
Local Abbreviation O_usage := (@U.Mal_nt__G1.Mal_nt_Ic.O_usage).
Local Abbreviation hold_usage := (§30§ U.Mal_nt__G1.Mal_nt_Ic.hold_usage).
Local Abbreviation e_bnlo := (@U.Mal_nt__G1.Mal_nt_Ic.e_bnlo).
Local Abbreviation ze_bnlo := (§26§ U.Mal_nt__G1.Mal_nt_Ic.ze_bnlo).
Local Abbreviation O_bnc := (@U.Mal_nt__G1.Mal_nt_Ic.O_bnc).
Local Abbreviation hold_bnc := (§30§ U.Mal_nt__G1.Mal_nt_Ic.hold_bnc).
Local Abbreviation O_grp := (@U.Mal_nt__G1.Mal_nt_Ic.O_grp).
Local Notation "§31§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd Hsp mV Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_grp := (§31§ U.Mal_nt__G1.Mal_nt_Ic.hold_grp).
Local Abbreviation O_shdr := (@U.Mal_nt__G1.Mal_nt_Ic.O_shdr).
Local Abbreviation O_bptr := (@U.Mal_nt__G1.Mal_nt_Ic.O_bptr).
Local Abbreviation O_pbase := (@U.Mal_nt__G1.Mal_nt_Ic.O_pbase).
Local Abbreviation O_pmeta := (@U.Mal_nt__G1.Mal_nt_Ic.O_pmeta).
Local Abbreviation O_parea := (@U.Mal_nt__G1.Mal_nt_Ic.O_parea).
Local Abbreviation O_secret := (@U.Mal_nt__G1.Mal_nt_Ic.O_secret).
Local Abbreviation hold_shdr := (§31§ U.Mal_nt__G1.Mal_nt_Ic.hold_shdr).
Local Abbreviation hold_bptr := (§31§ U.Mal_nt__G1.Mal_nt_Ic.hold_bptr).
Local Abbreviation hold_pbase := (§31§ U.Mal_nt__G1.Mal_nt_Ic.hold_pbase).
Local Abbreviation hold_pmeta := (§30§ U.Mal_nt__G1.Mal_nt_Ic.hold_pmeta).
Local Abbreviation hold_parea := (§30§ U.Mal_nt__G1.Mal_nt_Ic.hold_parea).
Local Abbreviation hold_secret := (§30§ U.Mal_nt__G1.Mal_nt_Ic.hold_secret).
Local Abbreviation kbase := (@U.Mal_nt__G1.Mal_nt_D.kbase).
Local Abbreviation kmemv := (@U.Mal_nt__G1.Mal_nt_D.kmemv).
Local Abbreviation kbitsv := (@U.Mal_nt__G1.Mal_nt_D.kbitsv).
Local Abbreviation kptr := (§24§ U.Mal_nt__G1.Mal_nt_D.kptr).
Local Abbreviation krec := (§24§ U.Mal_nt__G1.Mal_nt_D.krec).
Local Abbreviation klo := (§23§ U.Mal_nt__G1.Mal_nt_D.klo).
Local Abbreviation kcond := (@U.Mal_nt__G1.Mal_nt_D.kcond s am).
Local Abbreviation fbase := (@U.Mal_nt__G1.Mal_nt_D.fbase).
Local Abbreviation fptr := (@U.Mal_nt__G1.Mal_nt_D.fptr s g).
Local Abbreviation flo := (@U.Mal_nt__G1.Mal_nt_D.flo s L g).
Local Abbreviation fcond := (@U.Mal_nt__G1.Mal_nt_D.fcond s).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Abbreviation obj_of := (@U.Mal_nt__G1.Mal_nt_D.obj_of).
Local Abbreviation dlo := (§23§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§23§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation dcells := (@U.Mal_nt__G1.Mal_nt_D.dcells).
Local Abbreviation drom := (@U.Mal_nt__G1.Mal_nt_D.drom).
Local Abbreviation od_svs := (@U.Mal_nt__G1.Mal_nt_D.od_svs).
Local Abbreviation sv_sem := (@U.Mal_nt__G1.Mal_nt_D.sv_sem).
Local Abbreviation useq_okb := (@U.Mal_nt__G1.Mal_nt_D.useq_okb).
Local Abbreviation dsxb := (@U.Mal_nt__G1.Mal_nt_D.dsxb).
Local Abbreviation dcond := (@U.Mal_nt__G1.Mal_nt_D.dcond am).
Local Abbreviation DS := (@U.Mal_nt__G1.Mal_nt_D.DS am).
Local Abbreviation DS_svs := (@U.Mal_nt__G1.Mal_nt_D.DS_svs am).
Local Abbreviation DS_x := (@U.Mal_nt__G1.Mal_nt_D.DS_x am).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S1a9VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Abbreviation par_ranges := (§29§ U.Mal_nt__G1.Mal_nt_D.par_ranges).
Local Abbreviation sv_sem_of := (@U.Mal_nt__G1.Mal_nt_D.sv_sem_of am).
Local Abbreviation ze_kbase := (@U.Mal_nt__G1.Mal_nt_D.ze_kbase s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12).
Local Abbreviation klo_ptr := (@U.Mal_nt__G1.Mal_nt_D.klo_ptr s L X U g am i vm rd0 wok0 HMI).
Local Abbreviation kptr_used := (§22§ U.Mal_nt__G1.Mal_nt_D.kptr_used).
Local Abbreviation ze_kmemv := (§26§ U.Mal_nt__G1.Mal_nt_D.ze_kmemv).
Local Abbreviation ze_kbitsv := (§26§ U.Mal_nt__G1.Mal_nt_D.ze_kbitsv).
Local Abbreviation ze_fbase := (@U.Mal_nt__G1.Mal_nt_D.ze_fbase s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12).
Local Abbreviation flo_range := (§26§ U.Mal_nt__G1.Mal_nt_D.flo_range).
Local Notation "§32§ h__" := (h__ s L X U g am i vm rd0 wok0 HMI Hu) (at level 10, h__ global).
Local Abbreviation flo_ptr := (§32§ U.Mal_nt__G1.Mal_nt_D.flo_ptr).
Local Abbreviation fptr_key := (§32§ U.Mal_nt__G1.Mal_nt_D.fptr_key).
Local Abbreviation klo_range' := (@U.Mal_nt__G1.Mal_nt_D.klo_range' s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd).
Local Abbreviation useq_okb_cell := (@U.Mal_nt__G1.Mal_nt_D.useq_okb_cell rho gd Hgd).
Local Abbreviation useq_okb_cover := (@U.Mal_nt__G1.Mal_nt_D.useq_okb_cover rho gd Hgd).

Ltac in_list := cbn; repeat (first [left; reflexivity | right]).

Lemma cellsD d off w e : ltac2:(tb__ "0|2|
S174Vam;Vd;A2Sc9S71S71S0S6eA2M0S46A2S6dG0S46S6dS0S6eVoff;Vw;A4Ve;A4S175Vd;A1A3S6S48S48S5Sc9S48R1S63S177Vd;A1M1A1A3S5S4S46S5eR1A1Ve;A3S5S4S6eS15S5fR1A1A1Vw;A3S69S190VrhoW;R1A2S4S0SbSd0Q40S52R2S62G1A1A2A2S5bR2S5dR3A1A2A2SbS176Vs;VL;Vg;Vam;Vd;A5Voff;A2A3F_;FrhoX;A2A2A2Lc;A2F_;F_;").
Proof using HMI HP12 HXz Hgd Hsp Hu mW.
  intros Hd Hin. pose proof (proj2 Hd) as HC. pose proof (DS_x d Hd) as HX. pose proof R_all as R. pose proof (ceiling_small L). pose proof RN.
  assert (EVX : forall rhoX e z, agrees rhoW rhoX -> sv_vars_all below200 e = true -> zsupported e = true -> zeval zr1 zl1 e = z -> 0 <= z < 2 ^ 64 -> bv_unsigned (eval rhoX e) = z).
  { intros rhoX e0 z Hag Hv Hs Ez Hz. rewrite (EVu rhoW zr1 zl1 (zr1_any mW) (zl1_any mW) rhoX e0 Hag Hv Hs). exact Ez. }

  assert (GEN : forall (cbase : Z) (cells : list cell) (base : sv) (bz tgt : Z),
            In (mkCell (SLit (cbase + off)) (Z.of_nat w) e) cells ->
            (forall rhoX, agrees rhoW rhoX -> bv_unsigned (eval rhoX base) = bz) ->
            - 2 ^ 62 <= cbase + off < 2 ^ 62 -> tgt = bz + cbase + off ->
            exists c, In c cells /\ c_val c = e /\ Z.to_nat (c_width c) = w /\
              forall rhoX, agrees rhoW rhoX -> bv_unsigned (eval rhoX base) + soff rhoX (c_off c) = tgt).
  { intros cbase cells base bz tgt Hc Hb Hr ->. exists (mkCell (SLit (cbase + off)) (Z.of_nat w) e). split; [exact Hc|]. split; [reflexivity|]. split; [cbn; lia|].
    intros rhoX Hag. cbn [c_off]. rewrite soff_lit_small by lia. rewrite (Hb rhoX Hag). lia. }

  assert (SYM : forall (lo : sv) (zlo : Z) (e0 : sv), zeval zr1 zl1 lo = zlo -> 0 <= zlo < 2 ^ 62 -> sv_vars_all below200 lo = true -> zsupported lo = true ->
            exists c, In c [mkCell lo (Z.of_nat w) e0] /\ c_val c = e0 /\ Z.to_nat (c_width c) = w /\
              forall rhoX, agrees rhoW rhoX -> bv_unsigned (eval rhoX (SLit 0x5a3d0)) + soff rhoX (c_off c) = 0x5a3d0 + zlo + 0).
  { intros lo zlo e0 Ez Hz Hv Hs. exists (mkCell lo (Z.of_nat w) e0). split; [left; reflexivity|]. split; [reflexivity|]. split; [cbn; lia|].
    intros rhoX Hag. cbn [c_off eval]. rewrite u64 by lia. rewrite (soff_semX rhoW zr1 zl1 (zr1_any mW) (zl1_any mW) rhoX lo zlo Hag Hv Hs Ez) by lia. lia. }
  destruct d; try destruct five; cbn [dcond] in HC; cbn [dsxb] in HX; cbn in Hin;
    try (repeat match type of Hin with
         | _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-|]
         | False => destruct Hin
         end); cbn [obj_of ob_cells ob_base O_got O_guard O_metaK O_act O_seq O_useq O_fmh O_freeK O_usage O_bnc O_grp O_shdr O_bptr O_pbase O_pmeta O_parea O_secret carved lit_cells map free_cells]; unfold dlo; try (pose proof (par_ranges HC) as PR).

  1-2: eapply (GEN 0); [in_list | intros rhoX Hag; cbn [eval]; apply u64; lia | lia | lia].

  1-6: pose proof (klo_range' k);
       eapply (GEN 0); [in_list | intros rhoX Hag; apply (EVX rhoX (kbase k) (klo k) Hag ltac:(destruct k; reflexivity) ltac:(destruct k; reflexivity) (ze_kbase k)); lia | lia | lia].

  1: replace (369616 + (8 * sc + 80) + 0) with (369616 + (8 * sc + 80) + 0) by lia; apply (SYM e_actlo (8 * sc + 80)); [apply ze_actlo | unfold sc; lia | reflexivity | reflexivity].

  1: eapply (GEN 912); [in_list | intros rhoX Hag; cbn [eval]; apply u64; lia | lia | lia].

  1-4: eapply (GEN 848); [in_list | intros rhoX Hag; cbn [eval]; apply u64; lia | lia | lia].

  1: eapply (GEN 16); [in_list | intros rhoX Hag; cbn [eval]; apply u64; lia | lia | lia].

  1-11: pose proof (flo_range k);
       eapply (GEN 0); [in_list | intros rhoX Hag; apply (EVX rhoX (fbase k) (flo k) Hag ltac:(destruct k; reflexivity) ltac:(destruct k; reflexivity) (ze_fbase k)); lia | lia | lia].

  1: apply (SYM e_uslo (8 * sc + 464)); [apply ze_uslo | unfold sc; lia | reflexivity | reflexivity].
  1: apply (SYM e_bnlo (sc - 7 + 880)); [apply (ze_bnlo HC) | unfold sc; lia | reflexivity | reflexivity].

  1: eapply (GEN 8); [in_list | intros rhoX Hag; apply (EVX rhoX (v 156) zNm Hag eq_refl eq_refl ze156); lia | lia | lia].

  1-3: eapply (GEN (-4)); [in_list | intros rhoX Hag; apply (EVX rhoX (v 142) zM Hag eq_refl eq_refl ze142); lia | lia | lia].
  1: eapply (GEN 0); [in_list | intros rhoX Hag; apply (EVX rhoX (v 142) zM Hag eq_refl eq_refl ze142); lia | lia | lia].
  1: eapply (GEN (-16)); [in_list | intros rhoX Hag; apply (EVX rhoX e_parbase (zQm + 16) Hag eq_refl eq_refl (ze_parbase HC)); lia | lia | lia].
  1-4: eapply (GEN 16); [in_list | intros rhoX Hag; apply (EVX rhoX (v 172) zQ Hag eq_refl eq_refl (ze172 HC)); lia | lia | lia].
  1: eapply (GEN 0); [in_list | intros rhoX Hag; apply (EVX rhoX e_parea zQa Hag eq_refl eq_refl (ze_parea HC)); lia | lia | lia].
  1: eapply (GEN 0); [in_list | intros rhoX Hag; cbn [eval]; apply u64; lia | lia | lia].

  destruct (useq_okb_cell cs off w e HX Hin) as (C1 & C2 & C3).
  eapply (GEN 848); [| intros rhoX Hag; cbn [eval]; apply u64; lia | lia | lia].
  apply in_map_iff. exists (off, w, e). split; [reflexivity | exact Hin].
Qed.

Lemma cellsInD d off w e : ltac2:(tb__ "0|1|
S174Vam;Vd;A2Sc9S71S71S0S6eA2M0S46A2S6dG0S46S6dS0S6eVoff;Vw;A4Ve;A4S175Vd;A1A3S5SaZ0Voff;A2S5SaSbVoff;S11Vw;A1A2S12S178Vs;VL;Vg;Vam;Vd;A5S176Vs;VL;Vg;Vam;Vd;A5A2A2S163Vw;U8A2A2A2F_;F_;").
Proof using Hgd rho.
  intros Hd Hin. pose proof (DS_x d Hd) as HX. unfold dhi. destruct d; try destruct five; cbn [dsxb] in HX; cbn in Hin; cbn [dsz];
  try (repeat match type of Hin with
  | _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]
  | False => destruct Hin
  end).
  destruct (useq_okb_cell cs off w e HX Hin) as (C1 & C2 & C3). lia.
Qed.

Lemma semD d off w e : ltac2:(tb__ "0|1|
S174Vam;Vd;A2Sc9S71S71S0S6eA2M0S46A2S6dG0S46S6dS0S6eVoff;Vw;A4Ve;A4S175Vd;A1A3S5S4S6bS18aS18fVe;A2S70A3S4S6bS7cVe;A1S70A3A2F_;F_;").
Proof using . exact (sv_sem_of d off w e). Qed.

Lemma coverD d x : ltac2:(tb__ "0|3|
S174Vam;Vd;A2S4S6cS1A1S179Vd;A1S73S1A1A3S5SaS176Vs;VL;Vg;Vam;Vd;A5M0Vx;A2ScVx;S178Vs;VL;Vg;Vam;Vd;A5A2A2S6S0S0S6S6eS6eS6S46S46S5Sc9S71S71S0S6eA2M1S46A2S6dG1S46S6dS0S6eR3R2A4R1A4S175Vd;A1A3S5SaR3S12Vx;G0A2M2A2ScG2SbR3S11R2A1A2A2A2A2Le;A2Lw;A2Loff;A2F_;F_;F_;").
Proof using Hgd rho.
  intros Hd Hr Hx. pose proof (DS_x d Hd) as HX. unfold dhi in Hx. destruct d; cbn [drom] in Hr; try discriminate; cbn [dsz dlo] in Hx; cbn [dcells dlo]; cbn [dsxb] in HX;
    cbv [Z.of_nat Pos.of_succ_nat Pos.succ].
  - exists 0, 8%nat, (SLit 0x5a338). split; [left; reflexivity | lia].
  - exists 0, 8%nat, (v 143). split; [left; reflexivity | lia].
  - destruct (Z_lt_dec (x - klo k) 8); [exists 0, 8%nat, pv; split; [in_list | lia]|].
    destruct (Z_lt_dec (x - klo k) 16); [exists 8, 8%nat, nv; split; [in_list | lia]|].
    destruct (Z_lt_dec (x - klo k) 24); [exists 16, 8%nat, (kmemv k); split; [in_list | lia]|].
    destruct (Z_lt_dec (x - klo k) 28); [exists 24, 4%nat, av; split; [in_list | lia]|].
    destruct (Z_lt_dec (x - klo k) 32); [exists 28, 4%nat, fv; split; [in_list | lia]|].
    exists 32, 8%nat, (kbitsv k); split; [in_list | lia].
  - exists 0, 8%nat, hv. split; [left; reflexivity | unfold sc in *; lia].
  - exists 0, 1%nat, x0. split; [left; reflexivity | lia].
  - destruct (Z_lt_dec (x - (369616 + 848)) 8); [exists 0, 8%nat, a; split; [in_list | lia]|].
    destruct (Z_lt_dec (x - (369616 + 848)) 16); [exists 8, 8%nat, b; split; [in_list | lia]|].
    destruct (Z_lt_dec (x - (369616 + 848)) 24); [exists 16, 8%nat, c; split; [in_list | lia]|].
    exists 24, 8%nat, d; split; [in_list | lia].
  - exists 0, 8%nat, x0. split; [left; reflexivity | lia].
  - destruct (Z_lt_dec (x - flo k) 8); [exists 0, 8%nat, pv; split; [destruct five; in_list | lia]|].
    destruct (Z_lt_dec (x - flo k) 16); [exists 8, 8%nat, nv; split; [destruct five; in_list | lia]|].
    destruct (Z_lt_dec (x - flo k) 24); [exists 16, 8%nat, (SLit 0); split; [destruct five; in_list | lia]|].
    destruct five.
    + destruct (Z_lt_dec (x - flo k) 32); [exists 24, 8%nat, (SLit 0); split; [in_list | lia]|].
      exists 32, 8%nat, (SLit 0); split; [in_list | lia].
    + destruct (Z_lt_dec (x - flo k) 28); [exists 24, 4%nat, (SLit 0); split; [in_list | lia]|].
      destruct (Z_lt_dec (x - flo k) 32); [exists 28, 4%nat, (SLit 0); split; [in_list | lia]|].
      exists 32, 8%nat, (SLit 0); split; [in_list | lia].
  - exists 0, 8%nat, x0. split; [left; reflexivity | unfold sc in *; lia].
  - exists 0, 1%nat, x0. split; [left; reflexivity | unfold sc in *; lia].
  - exists 0, 1%nat, x0. split; [left; reflexivity | lia].
  - destruct (Z_lt_dec (x - (zM - 4)) 1); [exists 0, 1%nat, (SLit 0); split; [in_list | lia]|].
    destruct (Z_lt_dec (x - (zM - 4)) 2); [exists 1, 1%nat, (v 170); split; [in_list | lia]|].
    exists 2, 2%nat, (v 171); split; [in_list | lia].
  - exists 0, 8%nat, c0. split; [left; reflexivity | lia].
  - exists 0, 8%nat, (v 172). split; [left; reflexivity | lia].
  - destruct (Z_lt_dec (x - (zQ + 16)) 8); [exists 0, 8%nat, e_pmem; split; [in_list | lia]|].
    destruct (Z_lt_dec (x - (zQ + 16)) 12); [exists 8, 4%nat, (v 173); split; [in_list | lia]|].
    destruct (Z_lt_dec (x - (zQ + 16)) 16); [exists 12, 4%nat, (v 174); split; [in_list | lia]|].
    exists 16, 8%nat, (v 169); split; [in_list | lia].
  - exists 0, 8%nat, (v 136). split; [left; reflexivity | lia].
  - exists 0, 8%nat, (v 136). split; [left; reflexivity | lia].
  - destruct (useq_okb_cover cs (x - (369616 + 848)) HX ltac:(lia)) as (off & w & e & Hin & R). exists off, w, e. auto.
Qed.

Lemma dunkD d : ltac2:(tb__ "0|0|
S174Vam;Vd;A2S4S6cS1A1S179Vd;A1S73S1A1A3S4S66S64S177Vd;A1A1S4bA3F_;F_;").
Proof using . intros _ H. destruct d; cbn in H |- *; first [reflexivity | discriminate | unfold O_freeK, carved; reflexivity | unfold O_shdr, O_bptr, O_pbase, O_pmeta, O_parea, O_secret; reflexivity]. Qed.

Lemma romD d l x : ltac2:(tb__ "0|2|
S174Vam;Vd;A2S4S6cS1A1S179Vd;A1S6aS1Vl;A2A3S5SaS176Vs;VL;Vg;Vam;Vd;A5Vx;A2ScVx;S178Vs;VL;Vg;Vam;Vd;A5A2A2S5S4S6bS5aSc8ScfQ40Vx;A2M0A2S70A3S4S6cSceQ8A1M1A1VmW;G0A1S73G1A1A3A2F_;F_;F_;").
Proof using HZ Hgd Hm_sct rho.
  intros _ H Hx. unfold dhi in Hx. destruct d; cbn in H; try discriminate. cbn [dlo dsz] in Hx.
  split.
  - replace x with (0x108ec + (x - 0x108ec)) by lia. apply ro_sct_P. lia.
  - replace x with (0x108ec + (x - 0x108ec)) by lia. apply (proj1 (proj2 HZ _)). apply Hm_sct. lia.
Qed.

Definition od_ok_at (t : astate) (d : od) : Prop := ltac2:(tb__ "0|1c|
S17aOLd;Vd;S8S8S8S182S46S46S46S46S5S17fVs;Vam;R5A3S6S22S22S5S4S6cS1fA1M0SdfVt;S180Vs;Vg;Vam;R6A4A2S6aS1fS2cR1A1A2M1A3S5S4S1bS23R1A1M2S23S181Vs;Vg;Vam;R6A4M3A1A3S5S4S0SdcR1A1M4SdcG3A1A3S5S4S0S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M5S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M6R5A3S10bVL;S21R1A1A2A3S5S4S0S7aG5G6R4A3M7S10bVL;S20R1A1A2A3S5S4S0SfS7aG5G6R3A3M8SdZ2M9Z20A2MaA2S1dR1A1MbA3S4S0SfS7aG5G6R2A3McGaA2S1eR1A1MdA3A2A2A2A2A2A2La;A2A2Lfv;Lav;Lnv;Lpv;Lk;S46S5S5SaZ0MeS10fVam;A1MfA2ScGfZ30A2A2M10S4S0S7aG5G6R1A3M11S10bVL;Se1Vt;GfA2A2A3A2Lhv;S46S4S0SfG11SdG9Z8A2M12A2M13SfS36Vt;A1G12A2A3Lx;S46S46S46S46S5S4S0G7S110S2aVt;A1M14U0A2A3S5S4S0G8S110G14U1A2A3S5S4S0GcS110G14U2A2A3S4S0G11S110G14U3A2A3A2A2A2Ld;Lc;Lb;La;S46S4S0G11S10bVL;S26Vt;A1A2A3Lx;S17dS6bS46S46S5S17cVs;R4A2S6S6cS1bA1M15G15S6G15G15S5S4G0SdfVt;S17eVs;Vg;R6A3A2S6aS1fS28R2R1A2A2A3S5S1bS4G15R3S6aS1bR1A2M16A3Sc9S1bR2Se3Vs;A1A3M17F_;Fp;S5S1bS4G15R2G16A3G17F_;Fp;S5S4S0G7S10bVL;R2A2A3S4S0G8S10bVL;R1A2A3A2A2A2A2Lnx;A2Lpr;A2A2Lnv;Lpv;Lfive;Lk;S46S5G10S4S0G11S45Vt;GfA2A3A2Lx;S46S5S5SaZ7M18GfA2ScGfZ27A2A2S4S0G13SfS32S12GfG18A2S35Vt;A1A2G12A2A3A2Lx;S46S4S0G13S113Vs;VL;Vg;Vam;Vrd0;A5A3Lx;S8S46S4S0G11S112VL;Vg;A2A3Lc0;S8S6S22S22S5S4G0SdfVt;S128Vs;Vg;Vam;A3A2G1A3S5S4S1bG2S23S11fVs;Vg;Vam;A3M19A1A3S5S4S0GbS1dG19A1A3S5S4S0GdS1eG19A1A3S4S0G4SdcG19A1A3A2A2A2A2La;A2S8S8S74S71S71S0S6eA2M1aS46A2M1bA1S5S5S4S6eS77S0G14A2U20A3S0Sc9S0R1G14A3S5SaGeR2A2SaR2ZffA2A2F_;Fu;A2S0S6eS46Sc9G1bS6dG1aS46S6dS0S6eR3R2A4R1A4R4A3S6eS162R1R4A2S4S0Se4G7R5R2A3S154S0S188S15R6A1R2A2G14GeA4A3F_;Fj;F_;Fe;Fw;Foff;A2Lcs;X17ax13").
Definition od_ok (d : od) : Prop := ltac2:(tb__ "0|0|
S5S174Vam;Vd;A2S1b7Vs;Vd;A2A2").

Lemma hold_useqL cs : ltac2:(tb__ "0|2|
S4S6bS184Vcs;A1S70A3S4S6bScaS46S183S155S71S71S0S6eA2M0S46A2M1S46G1S78G0S46R1A3Lc;Vcs;A4A3S70A3S0S6eS46Sc9G1S6dG0S46S6dS0S6eR3R2A4R1A4Vcs;A3S6eS162R1R4A2S4S0Se4S7aS10dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S10cVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R4A3R5R2A3S154S0S188S15R6A1R2A2S2aVs;A1Z0A4A3F_;Fj;F_;Fe;Fw;Foff;S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S177S17bVcs;A1A1A4F_;F_;F_;").
Proof using Erd Ewok HMI Hgd Hrom Hsp.
  intros HX HS Hcs. cbn [obj_of].
  assert (LC : forall l : list (Z * nat * sv), lit_cells (map (fun c : Z * nat * sv => let '(off, w, e) := c in (848 + off, w, e)) l) = map (fun c : Z * nat * sv => let '(off, w, e) := c in mkCell (SLit (848 + off)) (Z.of_nat w) e) l).
  { induction l as [|[[o w] e] t IH]; [reflexivity|]. cbn [map lit_cells]. rewrite IH. reflexivity. }
  replace (mkObj (SLit 369616) (SLit 848) (SLit 880) (map (fun c : Z * nat * sv => let '(off, w, e) := c in mkCell (SLit (848 + off)) (Z.of_nat w) e) cs) DUnknown)
    with (carved (SLit 0x5a3d0) 848 880 (map (fun c : Z * nat * sv => let '(off, w, e) := c in (848 + off, w, e)) cs)) by (unfold carved; rewrite LC; reflexivity).
  assert (B : bv_unsigned (eval (rho1 mV) (SLit 0x5a3d0)) = 0x5a3d0) by (cbn [eval]; apply u64; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - unfold cells_inside. apply Forall_forall. intros [[o w] e] Hin. apply in_map_iff in Hin as ([[o' w'] e'] & E & Hin). injection E as <- <- <-.
    destruct (useq_okb_cell cs o' w' e' HX Hin) as (C1 & C2 & C3). lia.
  - intros o Ho. replace (0x5a3d0 + o) with (0x5a3d0 + 848 + Z.of_nat (Z.to_nat (o - 848))) by lia.
    destruct (useq_byte_rd (Z.to_nat (o - 848)) ltac:(lia)) as [W R]. split; [exact W | eexists; exact R].
  - unfold cells_in_view. apply Forall_forall. intros [[o w] e] Hin. apply in_map_iff in Hin as ([[o' w'] e'] & E & Hin). injection E as <- <- <-.
    destruct (useq_okb_cell cs o' w' e' HX Hin) as (C1 & C2 & C3).
    pose proof (proj1 (forallb_forall _ _) HS e' ltac:(apply in_map_iff; exists (o', w', e'); auto)) as Se. unfold sv_sem in Se. apply andb_prop in Se as [_ Se].
    intros t Ht. replace (0x5a3d0 + (848 + o') + Z.of_nat t) with (0x5a3d0 + 848 + Z.of_nat (Z.to_nat o' + t)) by lia.
    rewrite (proj2 (useq_byte_rd (Z.to_nat o' + t) ltac:(lia))). rewrite (ev1 mV e' Se), nth_enc_bytes by lia. f_equal. f_equal.
    symmetry. apply Hcs; [exact Hin | exact Ht].
Qed.

Lemma od_hold d : ltac2:(tb__ "0|0|
S1b6Vd;A1S4dSc8S10eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmV;A9S134Vms;VmV;A2S177Vd;A1A4F_;").
Proof using Erd Ewok HMI HP12 HXz Hdepth Hgd Hgd_holds Hm_sct Hrom Hsp Hu.
  intros [Hs Hok]. pose proof (DS_svs d Hs) as Hs'. pose proof (DS_x d Hs) as HX. unfold od_svs in Hs'.
  destruct d; cbn [dcells free_cells map snd forallb] in Hs'; cbn [od_ok_at] in Hok; cbn [dsxb] in HX.
  - apply hold_got.
  - apply hold_guard.
  - apply hold_sct.
  - apply andb_prop in Hs' as [S1 Hs']. apply andb_prop in Hs' as [S2 Hs']. apply andb_prop in Hs' as [S3 Hs']. apply andb_prop in Hs' as [S4 Hs']. apply andb_prop in Hs' as [S5 Hs']. apply andb_prop in Hs' as [S6 _].
    unfold sv_sem in *. apply andb_prop in S1 as [_ S1]. apply andb_prop in S2 as [_ S2]. apply andb_prop in S3 as [_ S3]. apply andb_prop in S4 as [_ S4]. apply andb_prop in S5 as [_ S5]. apply andb_prop in S6 as [_ S6].
    destruct Hok as (Hc & a & Ma & Em & Eb & E1 & E2 & E3 & E4).
    pose proof (kptr_used k) as Ku. rewrite (proj1 (usedX_MT _ _ _ _ Ku)) in Ma. injection Ma as <-.
    apply (hold_metaK (kptr k) (krec k)); try assumption.
    + destruct k; reflexivity.
    + rewrite ze_kbase. apply klo_ptr. exact Hc.
    + apply ze_kmemv.
    + apply ze_kbitsv.
  - apply andb_prop in Hs' as [S1 _]. unfold sv_sem in S1. apply andb_prop in S1 as [_ S1]. destruct Hok as [Hsc' E]. apply hold_act; [exact Hsc' | exact S1 | exact E].
  - apply andb_prop in Hs' as [S1 _]. unfold sv_sem in S1. apply andb_prop in S1 as [_ S1]. apply hold_seq; [exact S1|]. exact Hok.
  - apply andb_prop in Hs' as [S1 Hs']. apply andb_prop in Hs' as [S2 Hs']. apply andb_prop in Hs' as [S3 Hs']. apply andb_prop in Hs' as [S4 _].
    unfold sv_sem in *. apply andb_prop in S1 as [_ S1]. apply andb_prop in S2 as [_ S2]. apply andb_prop in S3 as [_ S3]. apply andb_prop in S4 as [_ S4].
    destruct Hok as (E1 & E2 & E3 & E4).
    apply (hold_useq [a; b; c; d] eq_refl). intros j e He.
    destruct j as [|[|[|[|j]]]]; cbn in He; try (destruct j; discriminate); injection He as <-; auto.
  - apply andb_prop in Hs' as [S1 _]. unfold sv_sem in S1. apply andb_prop in S1 as [_ S1]. apply hold_fmh; [exact S1 | exact Hok].
  - destruct Hok as (Hc & pr & nx & M & Kp & Kn & Ep & En).
    assert (SP : zsupported pv = true /\ zsupported nv = true).
    { destruct five; cbn [dcells free_cells map snd forallb] in Hs'; apply andb_prop in Hs' as [S1 Hs']; apply andb_prop in Hs' as [S2 _];
        unfold sv_sem in *; apply andb_prop in S1 as [_ S1]; apply andb_prop in S2 as [_ S2]; auto. }
    destruct SP as [Sp Sn].
    apply (hold_freeK (fptr k) pr nx); try assumption.
    + apply fptr_key. exact Hc.
    + destruct k; reflexivity.
    + rewrite ze_fbase. apply flo_ptr. exact Hc.
  - apply andb_prop in Hs' as [S1 _]. unfold sv_sem in S1. apply andb_prop in S1 as [_ S1]. destruct Hok as [Hsc' E]. apply hold_usage; [exact Hsc' | exact S1 | exact E].
  - apply andb_prop in Hs' as [S1 _]. unfold sv_sem in S1. apply andb_prop in S1 as [_ S1]. destruct Hok as [Hr E]. apply hold_bnc; [exact Hr | exact S1 | exact E].
  - apply andb_prop in Hs' as [S1 _]. unfold sv_sem in S1. apply andb_prop in S1 as [_ S1]. apply hold_grp; [exact S1 | exact Hok].
  - apply (hold_shdr (proj2 Hs)).
  - apply andb_prop in Hs' as [S1 _]. unfold sv_sem in S1. apply andb_prop in S1 as [_ S1].
    apply (hold_bptr c0 (proj2 Hs) S1 Hok).
  - apply (hold_pbase (proj2 Hs)).
  - apply (hold_pmeta (proj2 Hs)).
  - apply (hold_parea (proj2 Hs)).
  - apply hold_secret.
  - apply (hold_useqL cs HX Hs'). exact (proj2 Hok).
Qed.

End Inst.
End Mal_nt_Db.
