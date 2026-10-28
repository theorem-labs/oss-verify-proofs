(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "bool"; "nil"; "app"; "Some"; "list"; "option"; "true"; "prod"; "None"; "false"; "andb"; "negb"; "length"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "cell"; "sobj"; "mkCell"; "SPUle"; "SAlu"; "mkObj"; "DUnknown"; "obj_holds"; "mkSS"; "eval"; "FcsrFrm0"; "SPBranch"; "soff"; "SPAlign"; "rw"; "ss_objs"; "obj_range"; "SPNot"; "smatch"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "DRom"; "odefault"; "pairwise_disjoint"; "ranges_disjoint"; "ss_next"; "swf"; "SExt"; "SLBytes"; "SMd"; "c_off"; "c_val"; "c_width"; "cell_holds"; "covered"; "enc_bytes"; "image_byte"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "rl"; "DZero"; "SAluW"; "holds"; "mkVal"; "ro_addr"; "sprop_eqb"; "valuation"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "Zpos"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "or"; "ex"; "not"; "iff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "eqb"; "pow"; "lt"; "mul"; "modulo"; "of_nat"; "sub"; "ltb"; "opp"; "leb"; "to_nat"; "even"; "land"; "of_N"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I.InstA"; "zr2"; "zl2"; "rho2"; "usg"; "udw"; "usg2"; "bnc"; "icnt0"; "ctr"; "seqv"; "iaidx"; "icnt"; "iszc"; "zA"; "ineeded"; "isize"; "useq"; "iu"; "rw2"; "icnt1"; "ij"; "inos"; "iqdiv"; "itotal"; "live"; "rl2"; "rw2v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "pre_fregs"; "setregs"; "pre_regs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "zholds"; "toS"; "zsupported"; "zalu"; "psupported"; "sx32"; "zl_of"; "zle"; "zr_of"; "zsublist"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_GE"; "BC_EQ"; "ALU_AND"; "ALU_SRL"; "M_MUL"; "aluop"; "BC_LTU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "od2"; "ubytes2"; "cells_sem_eq"; "ia_Rz"; "od2_disj"; "od2_rangeP"; "udw2"; "od2_kind"; "od2_wfP"; "ia_L"; "ia_R"; "ia_U"; "ia_X"; "ia_erv"; "ia_gd"; "ia_m"; "ia_mW"; "ia_req"; "ia_rho"; "ia_s"; "ia_sc"; "ia_vm"; "mkInstA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "LK"; "F_G"; "F_M"; "F_CTX"; "NXA"; "e_cx"; "F_SZ"; "O_got"; "O_guard"; "O_sct"; "m1v"; "F_M1"; "O_m"; "objsCs"; "O_ctrv"; "O_med"; "O_pgs"; "O_s2c"; "O_small"; "O_stk"; "S_useqv"; "O_ctr"; "O_errnov"; "SCT"; "S_usg2"; "regsM1"; "O_errno"; "O_seqv"; "S_act0"; "S_act0v"; "S_bncv"; "S_usg"; "S_usg2v"; "S_usgv"; "Z_act0"; "Z_usg"; "objsC"; "useq_cells"; "F_N"; "O_mv"; "O_seq"; "STKC"; "S_bnc"; "S_useq0"; "S_useqB"; "Z_usg2"; "factsA"; "mkst"; "objsM1"; "regsA"; "regsN2"; "regs_base"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "seq"; "repeat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "image"; "MCell"; "LCtx"; "VZ"; "loc_addr"; "mc_w"; "mc_loc";
"CTX_SIZE"; "alloc_owned"; "CTX_active"; "CTX_bounces"; "CTX_unmap_seq"; "CTX_usage"; "LMem"; "VP"; "ctx_cells"; "le_byte"; "ly_ctx"; "meta_slot_cells"; "@Stdlib.Lists.List"; "In"; "forallb"; "Forall2"; "existsb"; "filter"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "wseg_addr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I.InstA.Live"; "obj_of2"; "od2_pairwise"; "od2_wf"; "od2_entry"; "od2_range"; "sp0"; "D0"; "O_act0"; "O_bnc"; "O_usg"; "O_usg2"; "Z_useqD"; "od2_pairwiseb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "mc_chk_guard"; "mc_tp"; "addr_of"; "holds"; "mc_errno"; "med_cnt_tab_bytes"; "size_classes_bytes"; "small_cnt_tab_bytes"; "vm_ok"; "ctz_tab_bytes"; "statics_ok"; "topL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "st_unmap_seq"; "usage_of"; "znth"; "class_size"; "st_bounces"; "PGSZ"; "IB"; "UNIT"; "sptr"; "st_mmap_counter"; "st_seq"; "MRaw"; "halve_while_big"; "halve_while_even"; "is_bouncing"; "mmap_plan"; "mslot"; "padd"; "page_round"; "size_classes"; "size_to_class"; "small_cnt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2"; "regsM23"; "objsM23"; "F_A"; "F_B"; "F_J"; "F_T"; "O_map"; "objsM23z"; "regsJ3"; "regsJA"; "regsJB"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3"; "nj"; "F_NT"; "NXN"; "O_gmeta"; "e_cj"; "e_pslot"; "S_actj"; "S_pslot"; "Z_actj"; "Z_pslot"; "factsN3"; "factsN3s"; "nstride"; "ntotal"; "objsN3"; "objsN3s"; "regsN3"; "regsN3s"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@Corelib.Init.Nat"; "add"; "mul"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "bytes_le_to_Z"; "@LinuxProcessSemantics.Riscv.Prelude"; "bv_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "obj_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "reprO"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "below200"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_agrp_St.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.

Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.

Definition NXA : positive := 300%positive.
Definition LK : Z := 0x5a3c8.
Definition SCT : Z := 0x108ec.

Definition STKC : list cell := ltac2:(tb__ "0|1|
S0S14S16S11N60A1Z8M0S12PaeA1A3S0S14S16S11N58A1G0S12P2dA1A3S0S14S16S11N50A1G0S12P2cA1A3S0S14S16S11N48A1G0S12P2bA1A3S0S14S16S11N40A1G0S12P2aA1A3S0S14S16S11N38A1G0S12P29A1A3S0S14S16S11N30A1G0S12P28A1A3S0S14S16S11N28A1G0S12P27A1A3S0S14S16S11N20A1G0S12P26A1A3S0S14S16S11N18A1G0S12P1dA1A3S0S14S16S11N10A1G0S12P1cA1A3S0S14S16S11N8A1G0S12PbA1A3S4S14A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition O_stk : sobj := ltac2:(tb__ "0|0|
S19S12PaA1S12PfA1S11Z0A1SdfS1aA5").
Definition O_got : sobj := ltac2:(tb__ "0|2|
S19S11Z28d50A1S11Z0A1M0S11Z8M1A1S0S14S16G0G1S57PadA1A3S4S14A1A3S1aA5").
Definition O_guard : sobj := ltac2:(tb__ "0|2|
S19S57PadA1S11Z0A1M0S11Z8M1A1S0S14S16G0G1S57PaeA1A3S4S14A1A3S1aA5").
Definition O_m : sobj := ltac2:(tb__ "0|3|
S19S57PbeA1S11Z0A1M0S11Z28A1S0S14S16G0Z8M1G0A3S0S14S16S11G1A1G1G0A3S0S14S16S11Z10A1G1G0A3S0S14S16S11Z18A1Z4M2G0A3S0S14S16S11Z1cA1G2G0A3S0S14S16S11Z20A1G1G0A3S4S14A1A3A3A3A3A3A3S1aA5").
Definition O_pgs : sobj := ltac2:(tb__ "0|2|
S19S11Z5a388A1S11Z0A1M0S11Z8M1A1S0S14S16G0G1S11Z1000A1A3S4S14A1A3S1aA5").
Definition O_ctr : sobj := ltac2:(tb__ "0|1|
S19S11Z5a3c8A1S11Z14A1M0S11Z18A1S0S14S16G0Z4S57Pc5A1A3S4S14A1A3S1aA5").
Definition O_sct : sobj := ltac2:(tb__ "0|0|
S19S11Z108ecA1S11Z0A1S11Z60A1S4S14A1S2fP1A1A5").
Definition O_small : sobj := ltac2:(tb__ "0|0|
S19S11Z1094cA1S11Z0A1S11Z1bA1S4S14A1S2fP2A1A5").
Definition O_med : sobj := ltac2:(tb__ "0|0|
S19S11Z10967A1S11Z0A1S11Z4A1S4S14A1S2fP3A1A5").
Definition O_s2c : sobj := ltac2:(tb__ "0|0|
S19S11Z108ccA1S11Z0A1S11Z20A1S4S14A1S2fP4A1A5").
Definition O_seq : sobj := ltac2:(tb__ "0|1|
S19S11Z5a3c8A1S11Z398A1M0S11Z399A1S0S14S16G0Z1S57Pc3A1A3S4S14A1A3S1aA5").
Definition O_errno : sobj := ltac2:(tb__ "0|1|
S19S12P18A1S11Na4A1M0S11Na0A1S0S14S16G0Z4S57Pb6A1A3S4S14A1A3S1aA5").

Definition Z_act0 (sc : Z) : sobj := ltac2:(tb__ "0|3|
S19S11Z5a3c8A1S11S58Z58S5dZ8M0Vsc;A2M1A2A1M2S11S58Z60G1A2A1S0S14S16G2G0S11Z0A1A3S4S14A1A3S1aA5").
Definition Z_usg (sc : Z) : sobj := ltac2:(tb__ "0|3|
S19S11Z5a3c8A1S11S58Z1d8S5dZ8M0Vsc;A2M1A2A1M2S11S58Z1e0G1A2A1S0S14S16G2G0S57Pc0A1A3S4S14A1A3S1aA5").
Definition Z_usg2 (sc : Z) : sobj := ltac2:(tb__ "0|3|
S19S11Z5a3c8A1S11S58Z1e0S5dZ8M0Vsc;A2M1A2A1M2S11S58Z1e8G1A2A1S0S14S16G2G0S57Pc4A1A3S4S14A1A3S1aA5").
Definition Z_bnc (sc : Z) : sobj := ltac2:(tb__ "0|1|
S19S11Z5a3c8A1S11S58Z371Vsc;A2A1M0S11S58Z372Vsc;A2A1S0S14S16G0Z1S57Pc1A1A3S4S14A1A3S1aA5").
Definition Z_useq (sc : Z) : sobj := ltac2:(tb__ "0|1|
S19S11Z5a3c8A1S11Z358A1S11Z378A1S3S7S14A1L_;SdS63Z7Vsc;A2S63Vsc;Z26A2A2S0S14S16S11S58Z351Vsc;A2A1Z1S57Pc2A1A3S4S14A1M0A3G0X3x2S1aA5").

Definition F_G : list sprop := ltac2:(tb__ "0|5|
S0S13S21PaM0Z4A2S0S13S17S11Z7fff7f800000A1S18S95S12G0A1S12PfA1M1A3A2S0S13S1fS97S11N120A1G1A3S0S13S1fS97G1S11S62S5bZ2M2Z28A2A1A1A3S0S13S17S11Z1000A1S12P18M3A1M4A2S0S13S17G4S11S5bG2Z2fA2A1A2S0S13S21G3Z3A2S4S13A1A3A3A3A3A3A3A3").
Definition F_M : list sprop := ltac2:(tb__ "0|2|
S0S13S25S1fS98S57PbeM0A1M1S11Z0A1A3A1S0S13S21G0Z3A2S0S13S17S11Z1000A1G1A2S0S13S17S18S95G1S11Z28A1A3S11Z7fffff800000A1A2S4S13A1A3A3A3A3").
Definition F_CTX : list sprop := ltac2:(tb__ "0|2|
S0S13S17S57Pc0A1S11S5bZ2Z30A2A1M0A2S0S13S17S57Pc4A1G0A2S0S13S17S57Pc1A1S11ZffA1M1A2S0S13S17S57Pc2A1G1A2S0S13S17S57Pc3A1G1A2S0S13S17S57Pc5A1S11ZffffffffA1A2S0S13S17S57Pc6A1S11Z1A1A2S4S13A1A3A3A3A3A3A3A3").

Definition regs_base (sc : Z) : list (nat * sv) := ltac2:(tb__ "0|2|
S0SaS2S10A2M0S1S2S10U1S12PdcA1A4S0G0S1S2S10U2S18S95S12PaA1S11N90A1A3A4S0G0S1S2S10U5S12PddA1A4S0G0S1S2S10U6S12PdeA1A4S0G0S1S2S10U7S12PdfA1A4S0G0S1S2S10U8S11Vsc;A1A4S0G0S1S2S10U9S57PbeA1A4S0G0S1S2S10UbS12Pe0A1A4S0G0S1S2S10UcS12Pe1A1A4S0G0S1S2S10UdS12Pe2A1A4S0G0S1S2S10UeS12Pe3A1A4S0G0S1S2S10UfS12Pe4A1A4S0G0S1S2S10U10S12Pe5A1A4S0G0S1S2S10U11S12Pe6A1A4S0G0S1S2S10U12S12PdA1A4S0G0S1S2S10U14S12PadA1A4S0G0S1S2S10U15S11S58S58Sb6Z58A2S5dZ8Vsc;A2M1A2A1A4S0G0S1S2S10U16S11Sb6A1A4S0G0S1S2S10U17S11S58Sb6G1A2A1A4S0G0S1S2S10U18S11S129Vsc;A1A1A4S0G0S1S2S10U19S11ScdA1A4S0G0S1S2S10U1cS12Pe7A1A4S0G0S1S2S10U1dS12Pe8A1A4S0G0S1S2S10U1eS12Pe9A1A4S0G0S1S2S10U1fS12PeaA1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition mkst (pc sc : Z) (over : list (nat * sv)) (objs : list sobj) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S1cVpc;S85S86S5SaS2S10A2Se9Vsc;A1Vover;A3A2S84S1eSbS10A1Vobjs;Vfacts;SbaScA9").

Definition e_cx (k : Z) : sv := ltac2:(tb__ "0|0|
S18S95S18S96S12PcA1S11Z3A1A3S11Vk;A1A3").
Definition S_act0v (hv : sv) : sobj := ltac2:(tb__ "0|1|
S19S11Sb6A1SbbZ58A1M0SbbZ60A1S0S14S16G0Z8Vhv;A3S4S14A1A3S1aA5").
Definition S_usgv (uv : sv) : sobj := ltac2:(tb__ "0|1|
S19S11Sb6A1SbbZ1d8A1M0SbbZ1e0A1S0S14S16G0Z8Vuv;A3S4S14A1A3S1aA5").
Definition S_usg2v (uv : sv) : sobj := ltac2:(tb__ "0|1|
S19S11Sb6A1SbbZ1e0A1M0SbbZ1e8A1S0S14S16G0Z8Vuv;A3S4S14A1A3S1aA5").
Definition S_bncv (bv : sv) : sobj := ltac2:(tb__ "0|2|
S19S11Sb6A1S18S95S12PcA1M0S11Z371A1A3M1S18S95G0S11Z372A1A3S0S14S16G1Z1Vbv;A3S4S14A1A3S1aA5").

Definition useq_cells (d0 d1 d2 d3 : sv) : list cell := ltac2:(tb__ "0|1|
S0S14S16S11Z358A1Z8M0Vd0;A3S0S14S16S11Z360A1G0Vd1;A3S0S14S16S11Z368A1G0Vd2;A3S0S14S16S11Z370A1G0Vd3;A3S4S14A1A3A3A3A3").
Definition S_useqv (d0 d1 d2 d3 : sv) (ob : option sv) : sobj := ltac2:(tb__ "0|1|
S19S11Sb6A1S11Z358A1S11Z378A1S5S14SdbVd0;Vd1;Vd2;Vd3;A4S8S10A1S7S14A1Lob;Vob;S10S0S14S16S18S95S12PcA1S11Z351A1A3Z1R1A3S4S14A1M0A3Lbv;G0X8x2A3S1aA5").
Definition O_seqv (qv : sv) : sobj := ltac2:(tb__ "0|1|
S19S11Sb6A1S11Z398A1M0S11Z399A1S0S14S16G0Z1Vqv;A3S4S14A1A3S1aA5").
Definition O_ctrv (cv : sv) : sobj := ltac2:(tb__ "0|1|
S19S11Sb6A1S11Z14A1M0S11Z18A1S0S14S16G0Z4Vcv;A3S4S14A1A3S1aA5").
Definition O_errnov (ev : sv) : sobj := ltac2:(tb__ "0|1|
S19S12P18A1S11Na4A1M0S11Na0A1S0S14S16G0Z4Vev;A3S4S14A1A3S1aA5").
Definition O_mv (c0 c1 c2 c3 c4 c5 : sv) : sobj := ltac2:(tb__ "0|3|
S19S57PbeA1S11Z0A1M0S11Z28A1S0S14S16G0Z8M1Vc0;A3S0S14S16S11G1A1G1Vc1;A3S0S14S16S11Z10A1G1Vc2;A3S0S14S16S11Z18A1Z4M2Vc3;A3S0S14S16S11Z1cA1G2Vc4;A3S0S14S16S11Z20A1G1Vc5;A3S4S14A1A3A3A3A3A3A3S1aA5").
Definition S_act0 : sobj := S_act0v (SLit 0).
Definition S_usg : sobj := S_usgv (v 192).
Definition S_usg2 : sobj := S_usg2v (v 196).
Definition S_bnc : sobj := S_bncv (v 193).
Definition S_useqB : sobj := ltac2:(tb__ "0|0|
ScaS57Pa4A1S57Pa5A1S57Pa6A1S57Pa7A1S6S10S57Pc2A1A2A5").
Definition S_useq0 : sobj := ltac2:(tb__ "0|0|
ScaS57Pa4A1S57Pa5A1S57Pa6A1S57Pa7A1SbS10A1A5").
Definition objsCs : list sobj := ltac2:(tb__ "0|0|
S0S15Sc9S0S15Sc2S0S15SbfS0S15SbdS0S15SbeS0S15Sd2S0S15Sc6S0S15Sd5S0S15Sc8S0S15Sc5S0S15Sc7S4S15A1A3A3A3A3A3A3A3A3A3A3A3").

Definition objsC (sc : Z) : list sobj := ltac2:(tb__ "0|0|
S0S15Sc9S0S15Sc2S0S15SbfS0S15SbdS0S15SbeS0S15Sd8Vsc;A1S0S15Sc6S0S15Sd9Vsc;A1S0S15Sc8S0S15Sc5S0S15Sc7S4S15A1A3A3A3A3A3A3A3A3A3A3A3").

Definition regsA : list sv := ltac2:(tb__ "0|4|
S0S10S12P14A1S0S10S11Z21464A1S0S10S18S95S12PaA1S11N90A1A3S0S10S12P17A1S0S10S12P18A1S0S10S12P131A1S0S10S12P132A1S0S10S12P133A1S0S10S12PcA1M0S0S10S12P1dA1S0S10S57PbeA1S0S10S12P137A1S0S10S12P138A1S0S10S12P139A1S0S10S12P13aA1S0S10S12P13bA1S0S10S12P13cA1S0S10S12P13dA1S0S10S12PdA1S0S10S18S96G0S11Z1A1A3M1S0S10S12PadA1S0S10S18S95S18S96G0S11Z3A1A3M2S11Z5a420A1A3S0S10S11Z5a3c8A1M3S0S10S18S95G2G3A3S0S10S35ScQ10S36P1G1Z2A3A3S0S10S11Z108ecA1S0S10S12P2eA1S0S10S12P2fA1S0S10S12P148A1S0S10S12P149A1S0S10S12P14aA1S0S10S12P14bA1S4S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition factsA : list sprop := ltac2:(tb__ "0|a|
S0S13S21PaM0Z4A2S0S13S17S11Z7fff7f800000A1M1S18S95S12G0A1M2S12PfA1M3A3A2S0S13S1fS97S11N120A1G3A3S0S13S1fS97G3S11N10000000000A1M4A3S0S13S17S12PcA1S11Z2fA1A2S0S13S17S11Z1000A1M5G2A2S0S13S21P136M6Z3A2S0S13S25S1fS98S12G6A1M7S11Z0A1A3A1S0S13S17G5G7A2S0S13S17S18S95G7S11Z28A1A3S11Z7fffff800000A1A2S0S13S17G1S18S95S18S95G2S11N90A1M8A3S18S95G3S11Z90A1A3M9A3A2S0S13S1fS97G8G9A3S0S13S1fS97G9G4A3S4S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition SCsym : sstate := ltac2:(tb__ "0|0|
S1cZ20ec8Se7S84S1eSbS10A1Sc3Se4P154ScA9").

Definition SCz (sc : Z) : sstate := ltac2:(tb__ "0|1|
Se5Z20ec8Vsc;S0SaS2S10A2M0S1S2S10U1S11Z21464A1A4S0G0S1S2S10U9S12P1dA1A4S0G0S1S2S10UaS57PbeA1A4S0G0S1S2S10U13S11S5dZ2Vsc;A2A1A4S0G0S1S2S10U18S11S128Vsc;S139A2A1A4S4G0A1A3A3A3A3A3SdaVsc;A1S5S13Sb7S5S13Sb8Sb9A3A3A5").

Definition regsM1 : list sv := ltac2:(tb__ "0|6|
S0S10S12P14A1S0S10S11Z21464A1S0S10S18S95S12PaA1S11N90A1A3S0S10S12P17A1S0S10S12P18A1S0S10S12PddA1S0S10S12PdeA1S0S10S12PdfA1S0S10S12PcA1M0S0S10S57PbeA1S0S10S57Pc0A1S0S10S11Z1000A1S0S10S18S95S57PbfA1M1S11Z10A1M2A3S0S10S11Z800A1S0S10S57PacA1M3S0S10S18S95G3G2A3S0S10S12Pe5A1S0S10S12Pe6A1S0S10S12PdA1S0S10S57PafA1S0S10S12PadA1S0S10S18S95S18S96G0S11Z3A1A3M4S11S58Sb6Z58A2A1A3S0S10S11Sb6A1M5S0S10S18S95G4G5A3S0S10G1S0S10S11ScdA1S0S10S12P2eA1S0S10S12P2fA1S0S10S12Pe7A1S0S10S12Pe8A1S0S10S12Pe9A1S0S10S12PeaA1S4S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition F_SZ : list sprop := ltac2:(tb__ "0|2|
S0S13S17S57PafA1M0S11Z20A1A2S0S13S17S11Z1A1G0A2S0S13S17S57PacA1S11S5bZ2Z17A2A1A2S0S13S17S11Z10A1S57PbfA1M1A2S0S13S17G1S11Z1fff0A1A2S0S13S17S12PcA1S11Z2fA1A2S4S13A1A3A3A3A3A3A3").
Definition SM1pre : sstate := ltac2:(tb__ "0|0|
S1cZ21538ScfS84S1eSbS10A1Sc3S5S13Sb7S5S13Sb8S5S13Sb9SbcA3A3A3SbaScA9").

Definition regsN2 : list sv := ltac2:(tb__ "0|4|
S0S10S12P14A1S0S10S11Z2164cA1S0S10S18S95S12PaA1S11N90A1A3S0S10S12P17A1S0S10S12P18A1S0S10S12PddA1S0S10S12PdeA1S0S10S12PdfA1S0S10S12PcA1M0S0S10S57PbeA1S0S10S57Pa9A1M1S0S10S57Pa8A1S0S10S12Pe1A1S0S10S12Pe2A1S0S10S12Pe3A1S0S10S12Pe4A1S0S10S12Pe5A1S0S10S12Pe6A1S0S10G1S0S10S57PafA1S0S10S12PadA1S0S10S18S95S18S96G0S11Z3A1A3M2S11S58Sb6Z58A2A1A3S0S10S11Sb6A1M3S0S10S18S95G2G3A3S0S10S57PbfA1S0S10S11ScdA1S0S10S12P2eA1S0S10S12P2fA1S0S10S12Pe7A1S0S10S12Pe8A1S0S10S12Pe9A1S0S10S12PeaA1S4S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition F_N : list sprop := ltac2:(tb__ "0|0|
S0S13S17S57Pa9A1S11Z2fA1A2S0S13S17S57Pa8A1S11Z800A1A2S4S13A1A3A3").
Definition SN2pre : sstate := ltac2:(tb__ "0|0|
S1cZ2126cSe8S84S1eSbS10A1Sc3S5S13Sb7S5S13Sb8S5S13Sb9S5S13SbcSdcA3A3A3A3SbaScA9").

Inductive m1v := M1a | M1b | M1c | M1d.
Definition objsM1 (x : m1v) : list sobj := ltac2:(tb__ "0|5|
S5S15Sc3Sc0S7S15A1Lx;Vx;S0S15SceS0S15Sc4S57Pc5A1A1M0S0S15SccS57Pb6A1A1M1S0S15Se1S0S15Sd1S57Pc3A1A1S4S15A1A3M2A3A3A3M3A3M4S0S15SceS0S15G0S0S15G1S0S15Se0S0S15Se2G2A3A3A3A3A3G4G3Xc0x4A3").
Definition F_M1 (x : m1v) : list sprop := ltac2:(tb__ "0|2|
Sc0S7S13A1Lx;Vx;S0S13S17S12PcA1M0S11Z6A1A2S4S13A1M1A3S0S13S17S11Z7A1G0A2S0S13S17G0S11Z26A1A2G1A3A3S0S13S17S11Z27A1G0A2S0S13S17G0S11Z2eA1A2G1A3A3S0S13S17S11Z2fA1G0A2G1A3Xc0x4").
Definition SM1 (x : m1v) : sstate := ltac2:(tb__ "0|0|
S1cZ21538ScfS84S1eSbS10A1Se6Vx;A1S5S13Sb7S5S13Sb8S5S13Sb9S5S13SbcSc1Vx;A1A3A3A3A3SbaScA9").
End Mal_agrp_St.

Module Mal_agrp_St2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St.

Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.

Definition regsM23 : list sv := ltac2:(tb__ "0|1|
S85ScfS0SaS2S10A2M0S1S2S10U5S12PebA1A4S0G0S1S2S10U6S12PecA1A4S0G0S1S2S10UdS57Pc6A1A4S0G0S1S2S10UfS11Z1fA1A4S0G0S1S2S10U10S12PedA1A4S0G0S1S2S10U11S12PeeA1A4S4G0A1A3A3A3A3A3A3A2").

Definition objsM23 (x : m1v) : list sobj := ltac2:(tb__ "0|2|
S5S15Sc3S5S15S0S15Sc4S57Pc5A1A1S0S15SccS57Pb6A1A1S4S15A1M0A3A3Sc0S7S15A1Lx;Vx;S0S15SceG0A3M1G1G1G0Xc0x4A3A3").
Definition SM23 (x : m1v) : sstate := ltac2:(tb__ "0|0|
S1cZ21818S13eS84S1eSbS10A1S13fVx;A1S5S13Sb7S5S13Sb8S5S13Sb9S5S13SbcSc1Vx;A1A3A3A3A3SbaScA9").

Definition objsM23z (sc : Z) : list sobj := ltac2:(tb__ "0|1|
S5S15SdaVsc;A1S5S15S0S15ScbS0S15Sd0S4S15A1M0A3A3S3S7S15A1L_;S5aVsc;Z2fA2G0S0S15Se3Vsc;A1G0A3X3x2A3A3").
Definition SM23z (sc cnt0 : Z) : sstate := ltac2:(tb__ "0|2|
S129Vsc;A1S4cS1cZ21818S85S13eS0SaS2S10A2M0S1S2S10U8S11Vsc;A1A4S0G0S1S2S10U13S11Vcnt0;A1A4S0G0S1S2S10U18S11R1A1A4S0G0S1S2S10UeS11S5dR1Vcnt0;A2A1A4S0G0S1S2S10UcS11S58R1Z10A2A1A4S0G0S1S2S10U15S11S58S58Sb6Z58A2S5dZ8Vsc;A2M1A2A1A4S0G0S1S2S10U17S11S58Sb6G1A2A1A4S4G0A1A3A3A3A3A3A3A3A2S84S1eSbS10A1S145Vsc;A1S5S13Sb7S5S13Sb8Sb9A3A3SbaScA9Tsize;").

Definition regsJ3 : list sv := ltac2:(tb__ "0|1|
S85S13eS0SaS2S10A2M0S1S2S10U5S12PefA1A4S0G0S1S2S10U6S12Pf0A1A4S0G0S1S2S10U7S12Pf1A1A4S0G0S1S2S10UaS12Pf2A1A4S0G0S1S2S10UbS12Pf3A1A4S0G0S1S2S10UdS12Pf4A1A4S0G0S1S2S10UeS12Pf5A1A4S0G0S1S2S10UfS12Pf6A1A4S0G0S1S2S10U10S12Pf7A1A4S0G0S1S2S10U11S12Pf8A1A4S0G0S1S2S10U13S57Pb1A1A4S0G0S1S2S10U19S57Pb0A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A2").

Definition F_A : list sprop := ltac2:(tb__ "0|0|
S0S13S17S57Pc7A1S11S5bZ2Z31A2A1A2S4S13A1A3").
Definition F_B : list sprop := ltac2:(tb__ "0|1|
S0S13S17S11Z1A1S57Pa3A1M0A2S0S13S17G0S11Z20A1A2S4S13A1A3A3").
Definition regsJA : list sv := ltac2:(tb__ "0|1|
S85S13eS0SaS2S10A2M0S1S2S10UaS57Pc7A1A4S0G0S1S2S10UfS12Pf9A1A4S4G0A1A3A3A2").
Definition SJA (x : m1v) : sstate := ltac2:(tb__ "0|0|
S1cZ2182cS147S84S1eSbS10A1S13fVx;A1S5S13Sb7S5S13Sb8S5S13Sb9S5S13SbcS5S13Sc1Vx;A1S140A3A3A3A3A3SbaScA9").
Definition regsJB : list sv := ltac2:(tb__ "0|1|
S85S13eS0SaS2S10A2M0S1S2S10UaS57Pc7A1A4S0G0S1S2S10U19S57Pa3A1A4S0G0S1S2S10U5S12Pf9A1A4S0G0S1S2S10UfS12PfaA1A4S0G0S1S2S10U10S12PfbA1A4S0G0S1S2S10U11S12PfcA1A4S0G0S1S2S10U13S12PfdA1A4S4G0A1A3A3A3A3A3A3A3A2").
Definition SJB (x : m1v) : sstate := ltac2:(tb__ "0|0|
S1cZ218a0S148S84S1eSbS10A1S13fVx;A1S5S13Sb7S5S13Sb8S5S13Sb9S5S13SbcS5S13Sc1Vx;A1S5S13S140S141A3A3A3A3A3A3SbaScA9").
Definition F_J : list sprop := ltac2:(tb__ "0|3|
S0S13S17S11Z1A1S57Pb0A1M0A2S0S13S17G0S11Z20A1A2S0S13S17S11Z1000A1S57Pb1M1A1M2A2S0S13S17G2S11S5bZ2Z17A2A1A2S0S13S21G1ZcA2S4S13A1A3A3A3A3A3").

Definition SJ3 (x : m1v) : sstate := ltac2:(tb__ "0|0|
S1cZ218fcS146S84S1eSbS10A1S13fVx;A1S5S13Sb7S5S13Sb8S5S13Sb9S5S13SbcS5S13Sc1Vx;A1S142A3A3A3A3A3SbaScA9").

Definition O_map : sobj := ltac2:(tb__ "0|0|
S19S57PbbA1S11Z0A1S57Pb1A1S4S14A1S45A5").
Definition F_T : list sprop := ltac2:(tb__ "0|2|
S0S13S21PbbM0ZcA2S0S13S17S11Z1000A1S57G0A1M1A2S0S13S17S18S95G1S57Pb1A1A3S11Z7fffff800000A1A2S0S13S25S1fS98G1S11ZffffffffffffffffA1A3A1S4S13A1A3A3A3A3").
Definition mkSKT (E : sstate) : sstate := ltac2:(tb__ "0|0|
S1cS58S2bVE;A1Z4A2S161S10S2cVE;A1UaS57PbbA1A4S29VE;A1S28VE;A1S2dVE;A1S5S15S23VE;A1S0S15S144S4S15A1A3A3S5S13S27VE;A1S143A3S33VE;A1S2aVE;A1A9").
Definition mkSKF (E : sstate) : sstate := S_ret_lit E enomem_ret.

Definition mkSKV (E : sstate) : sstate := ltac2:(tb__ "0|0|
S1cS2bVE;A1S161S10S2cVE;A1UbS57Pa2A1A4S29VE;A1S28VE;A1S2dVE;A1S23VE;A1S27VE;A1S33VE;A1S2aVE;A1A9").

Definition mkSKW (E : sstate) : sstate := ltac2:(tb__ "0|1|
S1cS2bVE;A1S161S10S2cVE;A1UcS57Pa1A1A4S29VE;A1S28VE;A1S2dVE;A1S23VE;A1S107S13S13SeS106S13S4aR1A1S0S13S1fS9dS12Pb0A1S12Pa2A1A3M0S0S13S25G0A1S4S13A1A3A3A3A1Lp;S27VE;A1A3S33VE;A1S2aVE;A1A9").
End Mal_agrp_St2.

Module Mal_agrp_St3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St.

Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.

Definition nvars : list (Z * Z) := ltac2:(tb__ "0|11|
S0SaS4cS4cA2M0S1S4cS4cZ0Z1eA4S0G0S1S4cS4cZ1M1ZfM2A4S0G0S1S4cS4cG1Z1fM3A4S0G0S1S4cS4cZ2M4ZaM5A4S0G0S1S4cS4cG4Z14A4S0G0S1S4cS4cZ3M6Z7M7A4S0G0S1S4cS4cG6G2A4S0G0S1S4cS4cG6G3A4S0G0S1S4cS4cZ4M8Z6M9A4S0G0S1S4cS4cG8ZcMaA4S0G0S1S4cS4cG8Z19A4S0G0S1S4cS4cZ5MbGbA4S0G0S1S4cS4cGbG5A4S0G0S1S4cS4cGbZ15A4S0G0S1S4cS4cG9G8A4S0G0S1S4cS4cG9Z8McA4S0G0S1S4cS4cG9Z12A4S0G0S1S4cS4cG7G7A4S0G0S1S4cS4cG7G2A4S0G0S1S4cS4cGcG9A4S0G0S1S4cS4cGcZeMdA4S0G0S1S4cS4cZ9MeG6A4S0G0S1S4cS4cGeG9A4S0G0S1S4cS4cGeGaA4S0G0S1S4cS4cG5GbA4S0G0S1S4cS4cG5G5A4S0G0S1S4cS4cZbMfG4A4S0G0S1S4cS4cGfG8A4S0G0S1S4cS4cGfGcA4S0G0S1S4cS4cGaG7A4S0G0S1S4cS4cZdM10G6A4S0G0S1S4cS4cG10G9A4S0G0S1S4cS4cGdGbA4S0G0S1S4cS4cG2G4A4S0G0S1S4cS4cG2G8A4S0G0S1S4cS4cZ11G6A4S0G0S1S4cS4cZ13G4A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition ntotal (sc cnt0 : Z) : Z := ltac2:(tb__ "0|0|
S60S58S12dS5dVcnt0;S129Vsc;A1A2A2S12cA2").
Definition nj (sc cnt0 : Z) : Z := ltac2:(tb__ "0|0|
S13aS158Vsc;Vcnt0;A2A1").
Definition nstride (sc cnt0 : Z) : Z := ltac2:(tb__ "0|0|
S129S14bVsc;Vcnt0;A2A1").

Definition Z_actj (j : Z) : sobj := ltac2:(tb__ "0|3|
S19S11Sb6A1S11S58Z58S5dZ8M0Vj;A2M1A2A1M2S11S58Z60G1A2A1S0S14S16G2G0S57Pb3A1A3S4S14A1A3S1aA5").

Definition O_gmeta : sobj := ltac2:(tb__ "0|3|
S19S57Pb3A1S11Z10A1M0S11Z28A1S0S14S16G0Z8M1S57Pb4A1A3S0S14S16S11Z18A1Z4M2S57Pb8A1A3S0S14S16S11Z1cA1G2S57Pb9A1A3S0S14S16S11Z20A1G1S57PbaA1A3S4S14A1A3A3A3A3S1aA5").

Definition e_pslot (stride : sv) : sv := ltac2:(tb__ "0|0|
S18S95S18S95S57Pb4A1S37S9bVstride;S57Pb2A1A3A3S11Z10A1A3").
Definition Z_pslot (stride : Z) : sobj := ltac2:(tb__ "0|3|
S19S150S11Vstride;A1A1S11N4A1M0S11S60Vstride;Z3A2A1S0S14S16G0Z1M1S11Z0A1M2A3S0S14S16S11S60Vstride;Z4A2A1G1G2A3S4S14A1A3A3S1aA5").
Definition objsN3 (sc cnt0 : Z) : list sobj := ltac2:(tb__ "0|0|
S0S15Sc9S0S15Sc2S0S15SbfS0S15SbdS0S15SbeS0S15Sd8Vsc;A1S0S15Sd9Vsc;A1S0S15ScbS0S15S153S14bVsc;Vcnt0;A2A1S0S15S14eS0S15S154S157Vsc;Vcnt0;A2A1S4S15A1A3A3A3A3A3A3A3A3A3A3A3").

Definition e_cj (k : Z) : sv := ltac2:(tb__ "0|0|
S18S95S18S96S57PaaA1S11Z3A1A3S11Vk;A1A3").
Definition S_actj : sobj := ltac2:(tb__ "0|1|
S19S11Sb6A1S14fZ58A1M0S14fZ60A1S0S14S16G0Z8S57Pb3A1A3S4S14A1A3S1aA5").
Definition S_pslot : sobj := ltac2:(tb__ "0|4|
S19S150S57Pb5A1M0A1S11N4A1M1S18S95G0S11N3A1A3S0S14S16G1Z1M2S11Z0A1M3A3S0S14S16S18S95G0G1A3G2G3A3S4S14A1A3A3S1aA5").
Definition objsN3s : list sobj := ltac2:(tb__ "0|0|
S0S15Sc9S0S15Sc2S0S15SbfS0S15SbdS0S15SbeS0S15Sd2S0S15Sd5S0S15Sc4S57Pc5A1A1S0S15S151S0S15S14eS0S15S152S4S15A1A3A3A3A3A3A3A3A3A3A3A3").

Definition F_NT (j2 : sv) (bz : bool) : list sprop := ltac2:(tb__ "0|c|
S5S13S0S13S17S57Pc0A1S11S5bZ2M0Z30A2A1A2S0S13S17S57Pc5A1S11ZffffffffA1A2S0S13S17S57Pb2A1S11Z1fA1M1A2S0S13S25S1fS98S57Pb3M2A1M3S11Z0A1M4A3A1S0S13S21G2Z3A2S0S13S17S11Z1000A1M5G3A2S0S13S17S18S95G3S11Z28A1A3S11Z7fffff800000A1A2S0S13S21Pb4M6Z4A2S0S13S17G5S57G6A1M7A2S0S13S17G7S11S5bG0Z2fA2A1A2S0S13S17Vj2;S18S99S18S9aS57PbaA1M8S11Z5A1A3S11Z7eA1A3M9A2S0S13S17G9Vj2;A2S4S13A1MaA3A3A3A3A3A3A3A3A3A3A3A3S3S7S13A1Lbz;Vbz;S0S13S17S18S99G8G1A3MbG4A2S0S13S17S18S9aG8S11ZcA1A3G4A2GaA3A3S0S13S25S1fS98GbG4A3A1GaA3X3x2A3").
Definition factsN3 (j : Z) (bz : bool) : list sprop := ltac2:(tb__ "0|0|
S5S13Sb7S5S13Sb8S14cS11S5dZ2Vj;A2A1Vbz;A2A3A3").

Definition factsN3s (bz : bool) : list sprop := ltac2:(tb__ "0|3|
S5S13Sb7S5S13Sb8S5S13S14cS18S96S57PaaA1M0S11Z1A1A3Vbz;A2S0S13S17S11Z10A1S57Pb5A1M1A2S0S13S17G1S11Z920A1A2S0S13S17G0S11Z2fA1A2S0S13S17S11Z2A1S57PabA1M2A2S0S13S17G2S11Z20A1A2S4S13A1A3A3A3A3A3A3A3A3").

Definition regsN3s : list sv := ltac2:(tb__ "0|3|
S0S10S12P12dA1S0S10S11Z2164cA1S0S10S18S95S12PaA1S11N90A1A3S0S10S12P17A1S0S10S12P18A1S0S10S12P131A1S0S10S12P132A1S0S10S12P133A1S0S10S12PcA1M0S0S10S12PbeA1S0S10S57Pb2A1S0S10S12P137A1S0S10S12P138A1S0S10S12P139A1S0S10S12P13aA1S0S10S12P13bA1S0S10S12P13cA1S0S10S12P13dA1S0S10S57PaaA1S0S10S57PabA1S0S10S12PadA1S0S10S18S95S18S96G0S11Z3A1A3M1S11Z5a420A1A3S0S10S11Z5a3c8A1M2S0S10S18S95G1G2A3S0S10S12PbfA1S0S10S11Z108ecA1S0S10S12P2eA1S0S10S12P2fA1S0S10S12P148A1S0S10S12P149A1S0S10S12P14aA1S0S10S12P14bA1S4S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition regsN3 (sc cnt0 : Z) : list sv := ltac2:(tb__ "0|1|
S0S10S12P12dA1S0S10S11Z2164cA1S0S10S18S95S12PaA1S11N90A1A3S0S10S12P17A1S0S10S12P18A1S0S10S12P131A1S0S10S12P132A1S0S10S12P133A1S0S10S11Vsc;A1S0S10S12PbeA1S0S10S57Pb2A1S0S10S12P137A1S0S10S12P138A1S0S10S12P139A1S0S10S12P13aA1S0S10S12P13bA1S0S10S12P13cA1S0S10S12P13dA1S0S10S11S14bVsc;Vcnt0;A2A1S0S10S11Vcnt0;A1S0S10S12PadA1S0S10S11S58S58Sb6Z58A2S5dZ8Vsc;A2M0A2A1S0S10S11Sb6A1S0S10S11S58Sb6G0A2A1S0S10S11S129Vsc;A1A1S0S10S11Z108ecA1S0S10S12P2eA1S0S10S12P2fA1S0S10S12P148A1S0S10S12P149A1S0S10S12P14aA1S0S10S12P14bA1S4S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition NXN : positive := 340%positive.
Definition SN3s (bz : bool) : sstate := ltac2:(tb__ "0|0|
S1cZ21b08S15cS84S1eSbS10A1S15aS156Vbz;A1S14dScA9").
Definition SN3z (sc cnt0 : Z) (bz : bool) : sstate := ltac2:(tb__ "0|0|
S1cZ21b08S15bVsc;Vcnt0;A2S84S1eSbS10A1S159Vsc;Vcnt0;A2S155S14bVsc;Vcnt0;A2Vbz;A2S14dScA9").
End Mal_agrp_St3.

Module Mal_agrp_I.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Inductive od2 :=
  | D_got | D_guard | D_pgs | D_sct | D_small | D_med | D_s2c | D_errno (ev : sv)
  | D_act0 (hv : sv) | D_usg (uv : sv) | D_usg2 (uv : sv) | D_ctr (cv : sv)
  | D_bnc (bv : sv) | D_useq (d0 d1 d2 d3 : sv) (ob : option sv) | D_seq (qv : sv)
  | D_m (c0 c1 c2 c3 c4 c5 : sv).

Definition od2_rangeP (scp zm tp : Z) (d : od2) : Z * Z := ltac2:(tb__ "0|d|
S9eSaS4cS4cA2Ld;Vd;S1S4cS4cS58Z28d50M0Z0M1A2S58G0Z8M2A2A4S1S4cS4cS58Z5a338M3G1A2S58G3G2A2A4S1S4cS4cS58Z5a388M4G1A2S58G4G2A2A4S1S4cS4cS58Z108ecM5G1A2S58G5Z60M6A2A4S1S4cS4cS58Z1094cM7G1A2S58G7Z1bA2A4S1S4cS4cS58Z10967M8G1A2S58G8Z4A2A4S1S4cS4cS58Z108ccM9G1A2S58G9Z20A2A4S10S1S4cS4cS58Vtp;Na4A2S58Vtp;Na0A2A4Lev;S10S1S4cS4cS58Z5a3c8MaS58Z58S5dG2Vscp;A2MbA2A2S58GaS58G6GbA2A2A4Lhv;S10S1S4cS4cS58GaS58Z1d8GbA2A2S58GaS58Z1e0GbA2A2McA4Luv;S10S1S4cS4cGcS58GaS58Z1e8GbA2A2A4Luv;S10S1S4cS4cS58GaZ14A2S58GaZ18A2A4Lcv;S10S1S4cS4cS58GaS58Z371Vscp;A2A2S58GaS58Z372Vscp;A2A2A4Lbv;S10S10S10S10S8S10A1S1S4cS4cS58GaZ358A2S58GaZ378A2A4Lob;Ld3;Ld2;Ld1;Ld0;S10S1S4cS4cS58GaZ398A2S58GaZ399A2A4Lqv;S10S10S10S10S10S10S1S4cS4cS58Vzm;G1A2S58Vzm;Z28A2A4Lc5;Lc4;Lc3;Lc2;Lc1;Lc0;X9ex10").
Definition od2_wfP (scp : Z) (d : od2) : Prop := ltac2:(tb__ "0|0|
S9eOLd;Vd;S52S52S52S52S52S52S52S10S52Lev;S10S52Lhv;S10S52Luv;S10S5cS58Vscp;Z1A2Z30A2Luv;S10S52Lcv;S10S51S59Z7Vscp;A2S59Vscp;Z26A2A2Lbv;S10S10S10S10S8S10A1S52Lob;Ld3;Ld2;Ld1;Ld0;S10S52Lqv;S10S10S10S10S10S10S52Lc5;Lc4;Lc3;Lc2;Lc1;Lc0;X9ex10").
Definition od2_kind (d : od2) : nat := ltac2:(tb__ "0|0|
S9eS2Ld;Vd;U0U1U2U3U4U5U6S10U7Lev;S10U8Lhv;S10U9Luv;S10UaLuv;S10UbLcv;S10UcLbv;S10S10S10S10S8S10A1UdLob;Ld3;Ld2;Ld1;Ld0;S10UeLqv;S10S10S10S10S10S10UfLc5;Lc4;Lc3;Lc2;Lc1;Lc0;X9ex10").
Definition od2_disj (d1 d2 : od2) : Prop := ltac2:(tb__ "0|0|
S55S50S2Sa5Vd1;A1Sa5Vd2;A1A3A1").

Lemma od2_disjointP scp zm d1 d2 : ltac2:(tb__ "0|3|
S51S59Z0Vscp;A2S5cVscp;Z30A2A2S59Z1000Vzm;A2S53S59S58Vzm;Z28A2M0Z10000A2S59Z5b000Vzm;A2A2S53S59S58Z5a3d0M1Z3a0A2Vzm;A2S59G0G1A2A2Sa6Vscp;Vd1;A2Sa6Vscp;Vd2;A2Sa2Vd1;Vd2;A2S32Sa3Vscp;Vzm;Z3a0d0M2Vd1;A4Sa3Vscp;Vzm;G2Vd2;A4A2F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros SC M1 M2 M3. unfold SymState.ranges_disjoint, od2_disj.
  destruct d1; cbn [od2_kind od2_rangeP od2_wfP fst snd]; intros W1; (destruct d2; cbn [od2_kind od2_rangeP od2_wfP fst snd]; intros W2 Hd; [lia ..]).
Qed.

Lemma loc_addr_padd L p off : ltac2:(tb__ "0|0|
S50S4cSf4VL;SfdS137Vp;Voff;A2A1A2S58S11cVL;Vp;A2Voff;A2A3").
Proof. unfold addr_of, loc_addr. destruct p; cbn [padd prid poff]. lia. Qed.

Definition ubytes2 (l : list Z) (j : nat) : list byte := ltac2:(tb__ "0|2|
SeaS2S92Q8M0A1S2S93G0SecS4cS163S164U8M1Vj;A2R1A2Vl;Z0A4A2Lk;SedU0G1A2A4").
Definition udw2 (l : list Z) (j : nat) : Z := ltac2:(tb__ "0|0|
S165S9fVl;Vj;A2A1").
Lemma ubytes2_len l j : ltac2:(tb__ "0|0|
S50S2SfS92Q8A1S9fVl;Vj;A2A2U8A3"). Proof. unfold ubytes2. rewrite length_map, length_seq. reflexivity. Qed.
Lemma udw2_range l j : ltac2:(tb__ "0|1|
S51S59Z0Sa4Vl;Vj;A2M0A2S5cG0S5bZ2Z40A2A2A2").
Proof. unfold udw2. pose proof (bytes_le_to_Z_bound (ubytes2 l j)) as B. rewrite ubytes2_len in B. exact B. Qed.
Lemma udw2_enc l j : ltac2:(tb__ "0|0|
S50S7S92Q8A1A1S3dU8S93Q40Sa4Vl;Vj;A2A2A2S9fVl;Vj;A2A3").
Proof. unfold udw2. change (Z_to_bv 64 (bytes_le_to_Z (ubytes2 l j))) with (le_bytes_to_word (ubytes2 l j)). apply enc_bytes_le_word; [apply ubytes2_len | lia]. Qed.
Lemma ubytes2_zero j : ltac2:(tb__ "0|3|
S50S7S92Q8M0A1M1A1S9fSeeS4cZ0M2U20A3Vj;A2SeeG1S93G0G2A2U8A3A3").
Proof. unfold ubytes2. cbn [seq map]. rewrite !(nth_repeat 0). reflexivity. Qed.
Lemma udw2_zero j : udw2 (repeat 0 32) j = 0.
Proof. unfold udw2. rewrite ubytes2_zero. reflexivity. Qed.
Lemma ubytes2_nth l j t : ltac2:(tb__ "0|4|
S149Vt;U8M0A2S50S92Q8M1A1M2SecG2Vt;S9fVl;Vj;A2S93G1Z0M3A2A4S93G1SecS4cS163S164G0Vj;A2Vt;A2Vl;G3A4A2A3F_;").
Proof. intros Ht. unfold ubytes2. destruct t as [|[|[|[|[|[|[|[|]]]]]]]]; try lia; cbn [map seq nth]; rewrite ?Nat.add_0_r; reflexivity. Qed.

Definition cells_sem_eq (rho : valuation) (cs1 cs2 : list cell) : Prop := ltac2:(tb__ "0|0|
S105S14S14S14S14S51S50S4cS20Vrho;S38R2A1A2S20Vrho;S38R1A1A2A3S51S50S4cS3aR2A1S3aR1A1A3S50S92Q40A1S1dVrho;S39R2A1A2S1dVrho;S39R1A1A2A3A2A2Lc2;Lc1;Vcs1;Vcs2;A5").
Lemma covered_sem rho cs1 cs2 off : ltac2:(tb__ "0|0|
Sa0Vrho;Vcs1;Vcs2;A3S56S3cVrho;Vcs1;Voff;A3S3cVrho;Vcs2;Voff;A3A2F_;").
Proof.
  intros H. unfold covered. induction H as [|c1 c2 t1 t2 (E1 & E2 & E3) H IH]; [split; intros X; inversion X|].
  rewrite !Exists_cons, IH. unfold in_cell. rewrite E1, E2. tauto.
Qed.
Lemma cells_holds_sem rho b1 b2 lo hi ms cs1 cs2 : ltac2:(tb__ "0|0|
S50S92Q40A1S1dVrho;Vb1;A2S1dVrho;Vb2;A2A3Sa0Vrho;Vcs1;Vcs2;A3SebS14S3bVrho;Vb1;Vlo;Vhi;Vms;A5Vcs1;A3SebS14S3bVrho;Vb2;Vlo;Vhi;Vms;A5Vcs2;A3F_;F_;F_;").
Proof.
  intros Eb Ec. induction Ec as [|c1 c2 t1 t2 E Ec IH]; intros H; [constructor|]. apply Forall_cons_iff in H as [C1 Ht].
  destruct E as (E1 & E2 & E3). constructor; [|exact (IH Ht)]. unfold SymState.cell_holds, oaddr in *. rewrite <- Eb, <- E1, <- E2, <- E3. exact C1.
Qed.
Lemma obj_holds_sem rho ms o1 o2 : ltac2:(tb__ "0|0|
S50S92Q40A1S1dVrho;S3fVo1;A1A2S1dVrho;S3fVo2;A1A2A3S50S4cS20Vrho;S43Vo1;A1A2S20Vrho;S43Vo2;A1A2A3S50S4cS20Vrho;S42Vo1;A1A2S20Vrho;S42Vo2;A1A2A3S50S30S41Vo1;A1S41Vo2;A1A3Sa0Vrho;S40Vo1;A1S40Vo2;A1A3S1bS83Vrho;Vms;Vo1;A4S1bS83Vrho;Vms;Vo2;A4F_;F_;F_;F_;F_;F_;").
Proof.
  intros Eb Elo Ehi Ed Ec (H1 & H2 & H3 & H4 & H5). unfold obj_holds, obj_lo_of, obj_hi_of in *.
  rewrite <- Eb, <- Elo, <- Ehi, <- Ed. split; [exact H1|]. split; [exact H2|]. split; [exact (cells_holds_sem rho _ _ _ _ ms _ _ Eb Ec H3)|]. split; [|exact H5].
  intros off Ho Hc. apply H4; [exact Ho|]. intros C. apply Hc. exact (proj1 (covered_sem rho _ _ off Ec) C).
Qed.

Record instA := mkInstA {
  ia_s : astate; ia_L : layout; ia_X : list sptr; ia_R : option (sptr * Z); ia_U : Z -> Z;
  ia_sc : Z; ia_req : Z;
  ia_rho : valuation;
  ia_m : sptr;
  ia_gd : Z; ia_erv : Z;
  ia_vm : VmMaps;
  ia_mW : word -> option byte;
  ia_Rz : Z                      }.
Definition set_R (ia : instA) (a : Z) : instA := ltac2:(tb__ "0|0|
Sb4Sb1Via;A1Sa7Via;A1SaaVia;A1Sa8Via;A1Sa9Via;A1Sb2Via;A1SafVia;A1Sb0Via;A1SadVia;A1SacVia;A1SabVia;A1Sb3Via;A1SaeVia;A1Va;Ae").

Section InstA.
Variable ia : instA.
Let s : astate := ia_s ia. Let L : layout := ia_L ia. Let X : list sptr := ia_X ia. Let RR : option (sptr * Z) := ia_R ia. Let U : Z -> Z := ia_U ia.
Let sc : Z := ia_sc ia. Let req : Z := ia_req ia. Let rho : valuation := ia_rho ia. Let m : sptr := ia_m ia.
Let gd : Z := ia_gd ia. Let erv : Z := ia_erv ia. Let vm : VmMaps := ia_vm ia. Let mW : word -> option byte := ia_mW ia.
Let rd0 : word -> option byte := Glue.rd_of segsU mW. Let wok0 : word -> bool := Glue.wok_of segsU mW.

Record instA_ok : Prop := mkInstAok {
  iok_I : Inv (m :: X) RR U s;
  iok_Xr : xraw (m :: X) s;
  iok_sc : 0 <= sc < 48;
  iok_req : 0 <= req /\ req + IB <= class_size sc;
  iok_hd : active_hd s sc = None;
  iok_m_key : In m (keys s);
  iok_m_raw : MT s m = Some MRaw \/ MT s m = Some (MFree None None);
  iok_MI : MInvI C_U (m :: X) RR U (mkMA s L) rd0 wok0 vm;
  iok_gd : 0 <= gd < 2 ^ 64;
  iok_erv : 0 <= erv < 2 ^ 32;
  iok_sp : 4096 <= bv_unsigned (rw rho 10%positive) /\ bv_unsigned (rw rho 10%positive) mod 16 = 0;
  iok_depth : toS 64 (bv_unsigned (rw rho 15%positive)) <= - as_stack (Z.of_nat (ContractI.tier sc)) /\ - 2 ^ 40 <= toS 64 (bv_unsigned (rw rho 15%positive));
  iok_sp_high : topL L <= bv_unsigned (rw rho 10%positive) + toS 64 (bv_unsigned (rw rho 15%positive));
  iok_tp : bv_unsigned (rw rho 24%positive) = mc_tp C_U;
  iok_m_ro : forall kk, 0 <= kk < 160 -> mW (Z_to_bv 64 (0x108cc + kk)) = None;
  iok_gd_holds : holds (byteview_of rd0 (fun _ => true)) (mc_chk_guard C_U) 8 gd;
  iok_erv_holds : holds (byteview_of rd0 (fun _ => true)) (mc_errno C_U) 4 erv;
  iok_U0 : forall c, U c = 0                        }.
Hypothesis Hi : instA_ok.

Let HI : Inv (m :: X) RR U s := iok_I Hi.
Let HXr : xraw (m :: X) s := iok_Xr Hi.
Let Hsc : 0 <= sc < 48 := iok_sc Hi.
Let Hreq : 0 <= req /\ req + IB <= class_size sc := iok_req Hi.
Let Hhd : active_hd s sc = None := iok_hd Hi.
Let Hm_key : In m (keys s) := iok_m_key Hi.
Let Hm_raw : MT s m = Some MRaw \/ MT s m = Some (MFree None None) := iok_m_raw Hi.
Let HMI : MInvI C_U (m :: X) RR U (mkMA s L) rd0 wok0 vm := iok_MI Hi.
Let Hgd : 0 <= gd < 2 ^ 64 := iok_gd Hi.
Let Herv : 0 <= erv < 2 ^ 32 := iok_erv Hi.
Let Hsp : 4096 <= bv_unsigned (rw rho 10%positive) /\ bv_unsigned (rw rho 10%positive) mod 16 = 0 := iok_sp Hi.
Let Hdepth : toS 64 (bv_unsigned (rw rho 15%positive)) <= - as_stack (Z.of_nat (ContractI.tier sc)) /\ - 2 ^ 40 <= toS 64 (bv_unsigned (rw rho 15%positive)) := iok_depth Hi.
Let Hsp_high : topL L <= bv_unsigned (rw rho 10%positive) + toS 64 (bv_unsigned (rw rho 15%positive)) := iok_sp_high Hi.
Let Htp : bv_unsigned (rw rho 24%positive) = mc_tp C_U := iok_tp Hi.
Let Hm_ro : forall kk, 0 <= kk < 160 -> mW (Z_to_bv 64 (0x108cc + kk)) = None := iok_m_ro Hi.
Let Hgd_holds : holds (byteview_of rd0 (fun _ => true)) (mc_chk_guard C_U) 8 gd := iok_gd_holds Hi.
Let Herv_holds : holds (byteview_of rd0 (fun _ => true)) (mc_errno C_U) 4 erv := iok_erv_holds Hi.
Lemma HL : layout_ok L s. Proof using HMI. exact (mig_layout HMI). Qed.
Lemma HV : ltac2:(tb__ "0|0|
S122VL;Vs;Vvm;A3"). Proof using HMI. exact (mig_vm HMI). Qed.
Lemma HLG : ledger_ok C_U vm. Proof using HMI. exact (mig_ledger HMI). Qed.
Lemma Hctx : ly_ctx L = 0x5a3d0. Proof using HMI. exact (mig_ctx HMI). Qed.

Definition zA (q : sptr) : Z := addr_of L q.
Definition optrZ (o : option sptr) : Z := match o with Some p => zA p | None => 0 end.

Definition usg : Z := usage_of s sc.
Definition usg2 : Z := ltac2:(tb__ "0|0|
S127Vs;S58Vsc;Z1A2A2").
Definition bnc : Z := ltac2:(tb__ "0|0|
S128S60Vsc;Z7A2S12aVs;A1A2").
Definition useq : Z := ltac2:(tb__ "0|0|
S128S60Vsc;Z7A2S126Vs;A1A2").
Definition seqv : Z := st_seq s.
Definition ctr : Z := st_mmap_counter s.
Definition udw (j : nat) : Z := ltac2:(tb__ "0|0|
Sa4S126Vs;A1Vj;A2").

Lemma ctx_ranges : ltac2:(tb__ "0|2|
S51S59Z0M0S6bA2S51S59G0S6dA2S51S51S59G0S6eA2S59S6eZffM1A2A2S51S51S59G0S78A2S59S78G1A2A2S51S51S59G0S71A2S59S71G1A2A2S51S59G0S70A2S5cS70S5bZ2Z20A2A2A2A2A2A2A2A2").
Proof using HI Herv Hgd Hsc.
  pose proof (inv_ctx HI) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & _).
  unfold usg, usg2, bnc, useq, seqv, ctr, usage_of, znth.
  assert (U1 : forall k, 0 <= nth k (st_usage s) 0).
  { intros k. destruct (nth_in_or_default k (st_usage s) 0) as [Hin| ->]; [exact (C5 _ Hin) | lia]. }
  assert (U2 : forall k, 0 <= nth k (st_unmap_seq s) 0 <= 255).
  { intros k. destruct (nth_in_or_default k (st_unmap_seq s) 0) as [Hin| ->]; [exact (C6 _ Hin) | lia]. }
  assert (U3 : forall k, 0 <= nth k (st_bounces s) 0 <= 255).
  { intros k. destruct (nth_in_or_default k (st_bounces s) 0) as [Hin| ->]; [exact (C7 _ Hin) | lia]. }
  repeat split; try apply U1; try apply U2; try apply U3; lia.
Qed.

Lemma usg_bounds : ltac2:(tb__ "0|1|
S51S5cS6bS5bZ2Z30A2M0A2S5cS6dG0A2A2").
Proof using HMI Herv Hgd Hsc.
  pose proof (mig_bounded HMI) as B. destruct B as (B1 & _). cbn [ma_s] in B1.
  unfold usg, usg2. pose proof (B1 sc). pose proof (B1 (sc + 1)). lia.
Qed.

Definition isize : Z := class_size sc.
Definition icnt0 : Z := initial_cnt sc usg.
Definition iszc : Z := isize * icnt0.
Definition iplan : Z * Z := ltac2:(tb__ "0|0|
S135Vs;Vsc;Vreq;S6fS6bA5").
Definition icnt : Z := fst iplan.
Definition ineeded : Z := snd iplan.
Definition inos : Z := if is_bouncing s sc then 1 else 0.

Definition iu : Z := ltac2:(tb__ "0|0|
S3S4cL_;SdS65Vsc;A1S61Vsc;Z20A2A2S58S6bS6dA2S6bX3x2").
Definition icnt1 : Z := ltac2:(tb__ "0|7|
S3S4cL_;M0SdS61S79S5dZ4M1S6fA2A2SeS134Vs;Vsc;A2A1A2G0SdS5aS66Vsc;Z3M2A2M3Z1A2S61S5dZ8S12bA2S74A2M4A2Z2M5G0SdS5aG3G5A2S61S5dG1S12bA2S74A2A2G2G0SdS5aG3Z0A2M6G4A2G2G0SdG6S61S5dG5S12bA2S74A2A2Z5S6fX3x2X3x2X3x2X3x2S6fX3x2").
Definition itotal : Z := ltac2:(tb__ "0|0|
S60S58S12dS5dS6fS77A2A2S12cA2").

Definition iqdiv : Z := 4080 / isize.

Definition iaidx : Z := mm_aidx isize icnt.
Definition ij : Z := size_to_class itotal mod 2 ^ 64.

Lemma isize_range : 16 <= isize <= 131056.
Proof using Herv Hgd Hsc Hsp.
  unfold isize, class_size, znth, UNIT.
  assert (H : forall k, (k < 48)%nat -> 1 <= nth k size_classes 0 <= 8191).
  { intros k Hk. unfold size_classes. do 48 (destruct k as [|k]; [cbn [nth]; lia|]). lia. }
  pose proof (H (Z.to_nat sc) ltac:(lia)). lia.
Qed.
Lemma small_cnt_range u : ltac2:(tb__ "0|1|
S5cVsc;Z9A2S51S59Z4S13bVsc;Vu;A2M0A2S59G0Z1fA2A2F_;").
Proof using Herv Hgd Hsc Hsp.
  intros H9. unfold small_cnt.
  assert (T : forall k, (k < 9)%nat -> exists r0 r1 r2, nth k small_cnt_tab [] = [r0; r1; r2] /\ 4 <= r0 <= 31 /\ 4 <= r1 <= 31 /\ 4 <= r2 <= 31).
  { intros k Hk. unfold small_cnt_tab. do 9 (destruct k as [|k]; [cbn [nth]; eexists _, _, _; split; [reflexivity|]; lia|]). lia. }
  destruct (T (Z.to_nat sc) ltac:(lia)) as (r0 & r1 & r2 & E & R0 & R1 & R2). rewrite E.
  replace (znth 0 [r0; r1; r2]) with r0 by reflexivity. replace (znth 1 [r0; r1; r2]) with r1 by reflexivity. replace (znth 2 [r0; r1; r2]) with r2 by reflexivity.
  destruct (negb (u <? 4 * r0)); [lia|]. destruct (negb (u <? 4 * r1)); lia.
Qed.
Lemma hwe_range f c u : ltac2:(tb__ "0|2|
S59Z1M0Vc;A2S51S59G0S133Vf;Vc;Vu;A3M1A2S59G1Vc;A2A2F_;").
Proof using Herv Hgd Hsc Hsp.
  revert c. induction f as [|f IH]; intros c Hc; cbn [halve_while_even]; [lia|].
  destruct (Z.even c) eqn:E; cbn [andb]; [|lia]. destruct (u <? 4 * c); [|lia].
  pose proof (Zeven_div2 c ltac:(apply Zeven_bool_iff; exact E)) as D. rewrite Zdiv2_div in D.
  pose proof (IH (c / 2) ltac:(lia)). lia.
Qed.
Lemma hwb_range f c : ltac2:(tb__ "0|2|
S59Z1M0Vc;A2S51S59G0S132Vf;Vc;S77A3M1A2S59G1Vc;A2A2F_;").
Proof using Herv Hgd Hsc Hsp.
  pose proof isize_range as SR. revert c. induction f as [|f IH]; intros c Hc; cbn [halve_while_big]; [lia|].
  destruct (65536 * UNIT <=? isize * c) eqn:E; [|lia]. apply Z.leb_le in E. unfold UNIT in E.
  assert (2 <= c) by nia. pose proof (IH (c / 2) ltac:(Z.to_euclidean_division_equations; lia)). Z.to_euclidean_division_equations; lia.
Qed.
Lemma icnt0_range : 1 <= icnt0 <= 32.
Proof using Herv Hgd Hsc Hsp.
  unfold icnt0, initial_cnt. fold isize.
  assert (M : 20 <= znth (Z.land sc 3) med_cnt_tab <= 32).
  { unfold znth, med_cnt_tab.
    assert (HL : 0 <= Z.land sc 3 <= 3).
    { split; [apply Z.land_nonneg; lia |]. change 3 with (Z.ones 2) at 1. rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound sc (2 ^ 2)). lia. }
    destruct (Z.to_nat (Z.land sc 3)) as [|[|[|[|k]]]] eqn:E; cbn [nth]; lia. }
  set (c := if sc <? 9 then _ else _).
  assert (C : 1 <= c <= 32).
  { subst c. destruct (sc <? 9) eqn:E9.
    - apply Z.ltb_lt in E9. pose proof (small_cnt_range usg E9). lia.
    - pose proof (hwe_range 8 (znth (Z.land sc 3) med_cnt_tab) usg ltac:(lia)) as W.
      pose proof (hwb_range 8 (halve_while_even 8 (znth (Z.land sc 3) med_cnt_tab) usg) ltac:(lia)). lia. }
  clearbody c. destruct ((c =? 1) && _)%bool; lia.
Qed.
Lemma iszc_range : 0 <= iszc < 2 ^ 23.
Proof using Herv Hgd Hsc Hsp. unfold iszc. pose proof isize_range. pose proof icnt0_range. nia. Qed.
Lemma page_round_range x : ltac2:(tb__ "0|1|
S59Z0Vx;A2S51S59Vx;S138Vx;A1M0A2S5cG0S58Vx;Z1000A2A2A2F_;").
Proof using Herv Hgd Hsc Hsp. intros Hx. unfold page_round, PGSZ. Z.to_euclidean_division_equations; lia. Qed.
Lemma iplan_range : ltac2:(tb__ "0|0|
S51S51S59Z1S73A2S59S73Z20A2A2S51S59Z0S76A2S5cS76S5bZ2Z18A2A2A2A2").
Proof using Herv Hgd Hreq Hsc Hsp.
  unfold icnt, ineeded, iplan, mmap_plan. fold isize. pose proof isize_range as SR. pose proof icnt0_range as CR.
  unfold IB in Hreq. fold isize in Hreq.
  set (u := if (Z.even sc && _)%bool then _ else _). clearbody u.
  set (c := if ((u <? 4 * icnt0) && _)%bool then _ else _).
  assert (C : 1 <= c <= 32) by (subst c; repeat (destruct (_ && _)%bool); lia). clearbody c.
  pose proof (page_round_range (isize * c + UNIT) ltac:(unfold UNIT; nia)) as P1.
  pose proof (page_round_range (req + IB + UNIT) ltac:(unfold IB, UNIT; lia)) as P2.
  assert (isize * c <= 131056 * 32) by nia. unfold UNIT, IB in *.
  destruct (negb _ && _)%bool; [destruct (_ || _)%bool|]; cbn [fst snd]; lia.
Qed.
Lemma itotal_range : 0 <= itotal < 2 ^ 23.
Proof using Herv Hgd Hsc Hsp. unfold itotal. pose proof isize_range. pose proof icnt0_range. unfold UNIT, IB. nia. Qed.
Lemma ij_range : 0 <= ij < 2 ^ 64.
Proof using Herv Hgd Hsc. unfold ij. apply Z.mod_pos_bound. lia. Qed.

Definition rw2v (j : positive) : option Z := ltac2:(tb__ "0|1|
S4fVj;A1S4cS3S8S4cA1L_;M0S5aR1ZcA2S6S4cVsc;A2G0S5aR1ZdA2S6S4cVreq;A2G0S5aR1Za8A2S6S4cS7fA2G0S5aR1Za9A2S6S4cS7cA2G0S5aR1Za4A2S6S4cS6cU0A1A2G0S5aR1Za5A2S6S4cS6cU1A1A2G0S5aR1Za6A2S6S4cS6cU2A1A2G0S5aR1Za7A2S6S4cS6cU3A1A2G0S5aR1ZacA2S6S4cS74A2G0S5aR1ZadA2S6S4cS11aS118A1A2G0S5aR1ZaeA2S6S4cVgd;A2G0S5aR1ZafA2S6S4cS6fA2G0S5aR1Zb0A2S6S4cS73A2G0S5aR1Zb1A2S6S4cS76A2G0S5aR1Zb6A2S6S4cVerv;A2G0S5aR1ZbeA2S6S4cS75Vm;A1A2G0S5aR1ZbfA2S6S4cS77A2G0S5aR1Zc0A2S6S4cS6bA2G0S5aR1Zc1A2S6S4cS6eA2G0S5aR1Zc2A2S6S4cS78A2G0S5aR1Zc3A2S6S4cS71A2G0S5aR1Zc4A2S6S4cS6dA2G0S5aR1Zc5A2S6S4cS70A2G0S5aR1Zc6A2S6S4cS7dA2G0S5aR1Zc7A2S6S4cS79A2G0S5aR1Za3A2S6S4cS7bA2G0S5aR1Za2A2S6S4cS7eA2G0S5aR1Za1A2S6S4cS72A2G0S5aR1ZbbA2S6S4cS5eSa1Via;A1S5bZ2Z40A2A2A2SbS4cA1X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2X3x2Tz;").

Definition rw2 (j : positive) : word := ltac2:(tb__ "0|1|
S8S4cA1S92Q40M0A1Lx;S82Vj;A1S4cS93G0R1A2Lz;S22Vrho;Vj;A2X8x2").

Definition rl2 (l : positive) : list byte := ltac2:(tb__ "0|4|
S3S7S92Q8M0A1M1A1L_;M2S15dVl;P1A2SeaS4cG1S93G0A1M3S120A4G2S15dVl;P2A2SeaS4cG1G3S121A4G2S15dVl;P3A2SeaS4cG1G3S11fA4G2S15dVl;P4A2SeaS4cG1G3S123A4S44Vrho;Vl;A2X3x2X3x2X3x2X3x2").

Definition rho2 (mm : word -> option byte) : valuation := ltac2:(tb__ "0|0|
S48S7aS81Vmm;A3").

Lemma rw2_low : ltac2:(tb__ "0|0|
S4dS15eR1P64A2S55S50S4dR2PcA3A1S55S50S4dR3PdA3A1S50S92Q40A1S7aR4A1S22Vrho;R4A2A3F_;F_;F_;Fj;").
Proof using Herv Hgd Hsc Hsp.
  intros j Hj H12 H13. unfold rw2, rw2v.
  repeat match goal with |- context [if ?c then _ else _] => let e := fresh in destruct c eqn:e; [exfalso; apply Z.eqb_eq in e; lia|] end.
  reflexivity.
Qed.

Definition zr2 : positive -> Z := zr_of (rho2 (fun _ => None)).
Definition zl2 : positive -> list Z := zl_of (rho2 (fun _ => None)).

Lemma zr2_zl2_any : ltac2:(tb__ "0|1|
S92Q40A1S8S92Q8A1A1F_;S10S50S4cS87S90S6aR2A1M0A1S8eG0A1R1A3S87S68S69R1A3A3Fe;Fmm;").
Proof using . intros mm e. reflexivity. Qed.

Lemma size_classes_bytes_range : ltac2:(tb__ "0|0|
SebS4cS4cS51S59Z0R1A2S5cR1Z100A2A2Lb;S120A3").
Proof using Herv Hgd Hsc.
  assert (H : forallb (fun b => (0 <=? b) && (b <? 256))%bool size_classes_bytes = true) by (vm_compute; reflexivity).
  apply Forall_forall. intros b Hb. pose proof (proj1 (forallb_forall _ _) H b Hb) as XB. cbn beta in XB.
  apply andb_prop in XB as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia.
Qed.
Lemma small_cnt_tab_bytes_range : ltac2:(tb__ "0|0|
SebS4cS4cS51S59Z0R1A2S5cR1Z100A2A2Lb;S121A3").
Proof using Herv Hgd Hsc. unfold small_cnt_tab_bytes, small_cnt_tab. cbn. repeat constructor; lia. Qed.
Lemma med_cnt_tab_bytes_range : ltac2:(tb__ "0|0|
SebS4cS4cS51S59Z0R1A2S5cR1Z100A2A2Lb;S11fA3").
Proof using Herv Hgd Hsc. unfold med_cnt_tab_bytes, med_cnt_tab. repeat constructor; lia. Qed.

Lemma zl_of_bytes l : ltac2:(tb__ "0|2|
SebS4cS4cS51S59Z0R1A2S5cR1Z100A2A2Lb;Vl;A3S50S7S4cA1SeaS92Q8M0A1M1S4cG1S94G0R1A2Lb;SeaS4cG1S93G0A1Vl;A4A4Vl;A3F_;").
Proof using Herv Hgd Hsc.
  intros H. rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in.
  intros b Hb. pose proof (proj1 (Forall_forall _ _) H b Hb) as R. cbn beta in R.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= b < 256). lia.
Qed.
Lemma zl2_1 : zl2 1%positive = size_classes_bytes.
Proof using Herv Hgd Hsc. unfold zl2, zl_of, rho2. cbn [rl rl2 Pos.eqb]. apply zl_of_bytes. apply size_classes_bytes_range. Qed.
Lemma zl2_2 : zl2 2%positive = small_cnt_tab_bytes.
Proof using Herv Hgd Hsc. unfold zl2, zl_of, rho2. cbn [rl rl2 Pos.eqb]. apply zl_of_bytes. apply small_cnt_tab_bytes_range. Qed.
Lemma zl2_3 : zl2 3%positive = med_cnt_tab_bytes.
Proof using Herv Hgd Hsc. unfold zl2, zl_of, rho2. cbn [rl rl2 Pos.eqb]. apply zl_of_bytes. apply med_cnt_tab_bytes_range. Qed.
Lemma zl2_4 : zl2 4%positive = ctz_tab_bytes.
Proof using . unfold zl2, zl_of, rho2. cbn [rl rl2 Pos.eqb]. apply zl_ctz. Qed.

Lemma zr2_v : ltac2:(tb__ "0|1|
S4dS4cS50S92Q40M0A1S7aR2A1S93G0R1A2A3S51S59Z0R2A2S5cR2S5bZ2Z40A2A2A2S50S4cS68R4A1R3A3F_;F_;Fz;Fj;").
Proof using . intros j z E Hz. unfold zr2, zr_of, rho2. cbn [rw]. rewrite E. apply u64. exact Hz. Qed.

Lemma m_align : zA m mod 8 = 0.
Proof using HI HMI Herv Hgd Hm_key Hsc Hsp.
  destruct (key_area (m :: X) RR U s HI m Hm_key) as (a & k & Ha & Hk & Em).
  pose proof HL as (_ & Halign & _).
  pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK a Ha) as (r & o & rga & Ea & Hoo & _ & Hra & Hla & _).
  pose proof (Halign _ _ Hra Hla) as RA.
  unfold zA. rewrite Em. subst a. unfold addr_of, loc_addr. cbn [padd prid poff].
  unfold AREA_HDR, META_SIZE, PGSZ in *. Z.to_euclidean_division_equations; lia.
Qed.

Lemma m_R : ltac2:(tb__ "0|3|
S51S59Z1000S75Vm;A1M0A2S51S59S58G0Z28A2M1S125VL;A1A2S51S50S4cS5eG0Z8A2Z0A3S51S53S59G1Z10000A2S59Z5b000G0A2A2S53S59S58Z5a3d0M2Z3a0A2G0A2S59G1G2A2A2A2A2A2A2").
Proof using HI HMI Herv Hgd Hm_key Hsc Hsp.
  pose proof Hctx as HCX. pose proof m_align as MA.
  pose proof (key_range (m :: X) RR U s L HI HL C_U vm m Hm_key HV HLG) as (K1 & K2 & K3 & K4).
  rewrite HCX in K4. cbn [mc_img_lo mc_img_hi C_U] in K3. unfold zA, META_SIZE, PGSZ, CTX_SIZE in *. lia.
Qed.

Lemma zr2_12 : zr2 12%positive = sc. Proof using Herv Hgd Hsc Hsp. apply (zr2_v 12 sc eq_refl). lia. Qed.
Lemma zr2_13 : zr2 13%positive = req.
Proof using Herv Hgd Hreq Hsc Hsp. apply (zr2_v 13 req eq_refl). pose proof (class_size_bounds sc Hsc). unfold IB in Hreq. lia. Qed.
Lemma zr2_173 : ltac2:(tb__ "0|0|
S50S4cS68PadA1S11aS118A1A3"). Proof using Herv Hgd Hsc. apply (zr2_v 173 _ eq_refl). cbn. lia. Qed.
Lemma zr2_174 : zr2 174%positive = gd. Proof using Herv Hgd Hsc Hsp. apply (zr2_v 174 gd eq_refl). lia. Qed.
Lemma zr2_182 : zr2 182%positive = erv. Proof using Herv Hgd Hsc Hsp. apply (zr2_v 182 erv eq_refl). lia. Qed.
Lemma zr2_190 : ltac2:(tb__ "0|0|
S50S4cS68PbeA1S75Vm;A1A3"). Proof using HI HMI Herv Hgd Hm_key Hsc Hsp Hsp_high. apply (zr2_v 190 _ eq_refl). pose proof m_R. top_ranges. lia. Qed.
Lemma zr2_192 : zr2 192%positive = usg. Proof using HI HMI Herv Hgd Hsc. apply (zr2_v 192 _ eq_refl). pose proof ctx_ranges. pose proof usg_bounds. lia. Qed.
Lemma zr2_193 : zr2 193%positive = bnc. Proof using HI Herv Hgd Hsc. apply (zr2_v 193 _ eq_refl). pose proof ctx_ranges. lia. Qed.
Lemma zr2_194 : zr2 194%positive = useq. Proof using HI Herv Hgd Hsc. apply (zr2_v 194 _ eq_refl). pose proof ctx_ranges. lia. Qed.
Lemma zr2_195 : zr2 195%positive = seqv. Proof using HI Herv Hgd Hsc. apply (zr2_v 195 _ eq_refl). pose proof ctx_ranges. lia. Qed.
Lemma zr2_196 : zr2 196%positive = usg2. Proof using HI HMI Herv Hgd Hsc. apply (zr2_v 196 _ eq_refl). pose proof ctx_ranges. pose proof usg_bounds. lia. Qed.
Lemma zr2_197 : zr2 197%positive = ctr. Proof using HI Herv Hgd Hsc. apply (zr2_v 197 _ eq_refl). pose proof ctx_ranges. lia. Qed.
Lemma zr2_164 : zr2 164%positive = udw 0. Proof using . apply (zr2_v 164 _ eq_refl). apply udw2_range. Qed.
Lemma zr2_165 : zr2 165%positive = udw 1. Proof using . apply (zr2_v 165 _ eq_refl). apply udw2_range. Qed.
Lemma zr2_166 : zr2 166%positive = udw 2. Proof using . apply (zr2_v 166 _ eq_refl). apply udw2_range. Qed.
Lemma zr2_167 : zr2 167%positive = udw 3. Proof using . apply (zr2_v 167 _ eq_refl). apply udw2_range. Qed.
Lemma zr2_168 : zr2 168%positive = itotal. Proof using Herv Hgd Hsc Hsp. apply (zr2_v 168 _ eq_refl). pose proof itotal_range. lia. Qed.
Lemma zr2_169 : zr2 169%positive = ij. Proof using Herv Hgd Hsc. apply (zr2_v 169 _ eq_refl). apply ij_range. Qed.
Lemma zr2_172 : zr2 172%positive = iszc. Proof using Herv Hgd Hsc Hsp. apply (zr2_v 172 _ eq_refl). pose proof iszc_range. lia. Qed.
Lemma zr2_175 : zr2 175%positive = icnt0. Proof using Herv Hgd Hsc Hsp. apply (zr2_v 175 _ eq_refl). pose proof icnt0_range. lia. Qed.
Lemma zr2_176 : zr2 176%positive = icnt. Proof using Herv Hgd Hreq Hsc Hsp. apply (zr2_v 176 _ eq_refl). pose proof iplan_range. lia. Qed.
Lemma zr2_177 : zr2 177%positive = ineeded. Proof using Herv Hgd Hreq Hsc Hsp. apply (zr2_v 177 _ eq_refl). pose proof iplan_range. lia. Qed.
Lemma zr2_191 : zr2 191%positive = isize. Proof using Herv Hgd Hsc Hsp. apply (zr2_v 191 _ eq_refl). pose proof isize_range. lia. Qed.
Lemma zr2_198 : zr2 198%positive = inos. Proof using Herv Hgd Hsc. apply (zr2_v 198 _ eq_refl). unfold inos. destruct (is_bouncing s sc); lia. Qed.
Lemma iu_range : 0 <= iu < 2 ^ 49.
Proof using HI HMI Herv Hgd Hsc Hsp. unfold iu. pose proof ctx_ranges. pose proof usg_bounds. destruct (Z.even sc && (sc <? 32)); lia. Qed.
Lemma icnt1_range : 1 <= icnt1 <= 32.
Proof using Herv Hgd Hsc Hsp. unfold icnt1. pose proof icnt0_range. repeat (destruct (_ && _)%bool); lia. Qed.
Lemma zr2_199 : zr2 199%positive = iu. Proof using HI HMI Herv Hgd Hsc Hsp. apply (zr2_v 199 _ eq_refl). pose proof iu_range. lia. Qed.
Lemma zr2_163 : zr2 163%positive = icnt1. Proof using Herv Hgd Hsc Hsp. apply (zr2_v 163 _ eq_refl). pose proof icnt1_range. lia. Qed.
Lemma iqdiv_range : 0 <= iqdiv <= 255.
Proof using Herv Hgd Hsc Hsp. unfold iqdiv. pose proof isize_range. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia. Qed.
Lemma zr2_162 : zr2 162%positive = iqdiv. Proof using Herv Hgd Hsc Hsp. apply (zr2_v 162 _ eq_refl). pose proof iqdiv_range. lia. Qed.
Lemma iaidx_range : ltac2:(tb__ "0|0|
S51S51S59Z0S72A2S59S72S60S73Z1A2A2A2S59S72Z1fA2A2").
Proof using Herv Hgd Hreq Hsc Hsp. unfold iaidx, mm_aidx, UNIT. pose proof iplan_range as [R _]. set (a0 := (4096 - 16) / isize - 1). cbn zeta. destruct (Z.ltb_spec (icnt - 1) a0) as [H1|H1]; [destruct (Z.ltb_spec (icnt - 1) 0); lia | destruct (Z.ltb_spec a0 0); lia]. Qed.
Lemma zr2_161 : zr2 161%positive = iaidx. Proof using Herv Hgd Hreq Hsc Hsp. apply (zr2_v 161 _ eq_refl). pose proof iaidx_range. lia. Qed.
Lemma zr2_187 : ltac2:(tb__ "0|0|
S50S4cS68PbbA1S5eSa1Via;A1S5bZ2Z40A2A2A3"). Proof using Herv Hgd Hsc. apply (zr2_v 187 _ eq_refl). apply Z.mod_pos_bound. lia. Qed.

Lemma ze_var : ltac2:(tb__ "0|0|
S4dS50S4cS87S68S69S12R1A1A3S5eS68R1A1S5bZ2Z40A2A2A3Fj;"). Proof using . reflexivity. Qed.
Lemma ze_v : ltac2:(tb__ "0|0|
S4dS50S4cS87S68S69S57R1A1A3S5eS68R1A1S5bZ2Z40A2A2A3Fj;"). Proof using . reflexivity. Qed.
Lemma ze_lit : ltac2:(tb__ "0|0|
S4cS50S4cS87S68S69S11R1A1A3S5eR1S5bZ2Z40A2A2A3Fz;"). Proof using . reflexivity. Qed.
Lemma ze_alu : ltac2:(tb__ "0|0|
S9cS10S10S50S4cS87S68S69S18R3R2R1A3A3S8bZ40R3S87S68S69R2A3S87S68S69R1A3A4A3Fy;Fx;Fop;"). Proof using . reflexivity. Qed.
Lemma ze_aluw : ltac2:(tb__ "0|2|
S9cS10S10S50S4cS87S68S69S46R3R2R1A3A3S8dS8bZ20M0R3S5eS87S68S69R2A3S5bZ2G0A2M1A2S5eS87S68S69R1A3G1A2A4A1A3Fy;Fx;Fop;"). Proof using . reflexivity. Qed.
Lemma ze_mul : ltac2:(tb__ "0|0|
S10S10S50S4cS87S68S69S37S9bR2R1A3A3S5eS5dS87S68S69R2A3S87S68S69R1A3A2S5bZ2Z40A2A2A3Fy;Fx;"). Proof using . reflexivity. Qed.
Lemma ze_ext : ltac2:(tb__ "0|3|
S3S4eS10S50S4cS87S68S69S35R3R2R1A3A3S3S4cLsg;R3S5eS89S67R2A1M0S87S68S69R1A3M1A2S5bZ2M2Z40A2A2S5eG1S5bG2G0A2A2X3x2A3Fx;Fw;Fsg;"). Proof using . reflexivity. Qed.
Lemma ze_lbytes : ltac2:(tb__ "0|0|
S4dS10S4cS50S4cS87S68S69S36R3R2R1A3A3S5eS8fS91S87S68S69R2A3R1S69R3A1A3A1S5bZ2Z40A2A2A3Fkk;Fix;Fl;"). Proof using . reflexivity. Qed.

Lemma ze12 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57PcA1A3Vsc;A3"). Proof using Herv Hgd Hsc Hsp. rewrite ze_v, zr2_12. apply m64. lia. Qed.
Lemma ze13 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57PdA1A3Vreq;A3"). Proof using Herv Hgd Hreq Hsc Hsp. rewrite ze_v, zr2_13. apply m64. pose proof (class_size_bounds sc Hsc). unfold IB in Hreq. lia. Qed.
Lemma ze173 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57PadA1A3S11aS118A1A3"). Proof using Herv Hgd Hsc. rewrite ze_v, zr2_173. reflexivity. Qed.
Lemma ze174 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57PaeA1A3Vgd;A3"). Proof using Herv Hgd Hsc Hsp. rewrite ze_v, zr2_174. apply m64. lia. Qed.
Lemma ze182 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pb6A1A3Verv;A3"). Proof using Herv Hgd Hsc Hsp. rewrite ze_v, zr2_182. apply m64. lia. Qed.
Lemma ze190 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57PbeA1A3S75Vm;A1A3"). Proof using HI HMI Herv Hgd Hm_key Hsc Hsp Hsp_high. rewrite ze_v, zr2_190. apply m64. pose proof m_R. top_ranges. lia. Qed.
Lemma ze192 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pc0A1A3S6bA3"). Proof using HI HMI Herv Hgd Hsc. rewrite ze_v, zr2_192. apply m64. pose proof ctx_ranges. pose proof usg_bounds. lia. Qed.
Lemma ze193 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pc1A1A3S6eA3"). Proof using HI Herv Hgd Hsc. rewrite ze_v, zr2_193. apply m64. pose proof ctx_ranges. lia. Qed.
Lemma ze194 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pc2A1A3S78A3"). Proof using HI Herv Hgd Hsc. rewrite ze_v, zr2_194. apply m64. pose proof ctx_ranges. lia. Qed.
Lemma ze195 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pc3A1A3S71A3"). Proof using HI Herv Hgd Hsc. rewrite ze_v, zr2_195. apply m64. pose proof ctx_ranges. lia. Qed.
Lemma ze196 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pc4A1A3S6dA3"). Proof using HI HMI Herv Hgd Hsc. rewrite ze_v, zr2_196. apply m64. pose proof ctx_ranges. pose proof usg_bounds. lia. Qed.
Lemma ze197 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pc5A1A3S70A3"). Proof using HI Herv Hgd Hsc. rewrite ze_v, zr2_197. apply m64. pose proof ctx_ranges. lia. Qed.
Lemma ze164 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pa4A1A3S6cU0A1A3"). Proof using . rewrite ze_v, zr2_164. apply m64. apply udw2_range. Qed.
Lemma ze165 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pa5A1A3S6cU1A1A3"). Proof using . rewrite ze_v, zr2_165. apply m64. apply udw2_range. Qed.
Lemma ze166 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pa6A1A3S6cU2A1A3"). Proof using . rewrite ze_v, zr2_166. apply m64. apply udw2_range. Qed.
Lemma ze167 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pa7A1A3S6cU3A1A3"). Proof using . rewrite ze_v, zr2_167. apply m64. apply udw2_range. Qed.
Lemma ze168 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pa8A1A3S7fA3"). Proof using Herv Hgd Hsc Hsp. rewrite ze_v, zr2_168. apply m64. pose proof itotal_range. lia. Qed.
Lemma ze169 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pa9A1A3S7cA3"). Proof using Herv Hgd Hsc. rewrite ze_v, zr2_169. apply m64. apply ij_range. Qed.
Lemma ze172 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57PacA1A3S74A3"). Proof using Herv Hgd Hsc Hsp. rewrite ze_v, zr2_172. apply m64. pose proof iszc_range. lia. Qed.
Lemma ze175 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57PafA1A3S6fA3"). Proof using Herv Hgd Hsc Hsp. rewrite ze_v, zr2_175. apply m64. pose proof icnt0_range. lia. Qed.
Lemma ze176 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pb0A1A3S73A3"). Proof using Herv Hgd Hreq Hsc Hsp. rewrite ze_v, zr2_176. apply m64. pose proof iplan_range. lia. Qed.
Lemma ze177 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pb1A1A3S76A3"). Proof using Herv Hgd Hreq Hsc Hsp. rewrite ze_v, zr2_177. apply m64. pose proof iplan_range. lia. Qed.
Lemma ze191 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57PbfA1A3S77A3"). Proof using Herv Hgd Hsc Hsp. rewrite ze_v, zr2_191. apply m64. pose proof isize_range. lia. Qed.
Lemma ze198 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pc6A1A3S7dA3"). Proof using Herv Hgd Hsc. rewrite ze_v, zr2_198. apply m64. unfold inos. destruct (is_bouncing s sc); lia. Qed.
Lemma ze199 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pc7A1A3S79A3"). Proof using HI HMI Herv Hgd Hsc Hsp. rewrite ze_v, zr2_199. apply m64. pose proof iu_range. lia. Qed.
Lemma ze163 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pa3A1A3S7bA3"). Proof using Herv Hgd Hsc Hsp. rewrite ze_v, zr2_163. apply m64. pose proof icnt1_range. lia. Qed.
Lemma ze162 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pa2A1A3S7eA3"). Proof using Herv Hgd Hsc Hsp. rewrite ze_v, zr2_162. apply m64. pose proof iqdiv_range. lia. Qed.
Lemma ze161 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57Pa1A1A3S72A3"). Proof using Herv Hgd Hreq Hsc Hsp. rewrite ze_v, zr2_161. apply m64. pose proof iaidx_range. lia. Qed.
Lemma ze187 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S57PbbA1A3S5eSa1Via;A1S5bZ2Z40A2A2A3"). Proof using Herv Hgd Hsc. rewrite ze_v, zr2_187. apply m64. apply Z.mod_pos_bound. lia. Qed.

Lemma zr2_10 : ltac2:(tb__ "0|1|
S50S4cS68PaM0A1S94Q40S22Vrho;G0A2A2A3"). Proof using . reflexivity. Qed.
Lemma zr2_15 : ltac2:(tb__ "0|1|
S50S4cS68PfM0A1S94Q40S22Vrho;G0A2A2A3"). Proof using . reflexivity. Qed.
Lemma zr2_24 : ltac2:(tb__ "0|0|
S50S4cS68P18A1S11bS118A1A3"). Proof using Htp. unfold zr2, zr_of, rho2. cbn [rw]. change (rw2 24%positive) with (rw rho 24%positive). exact Htp. Qed.
Lemma ze24 : ltac2:(tb__ "0|0|
S50S4cS87S68S69S12P18A1A3S11bS118A1A3"). Proof using Htp. rewrite ze_var, zr2_24. reflexivity. Qed.

Theorem facts_hold : ltac2:(tb__ "0|0|
S92Q40A1S8S92Q8A1A1F_;S7S13A1S50S3S104S13S8cR1A3S9A3SebS13S88S68S69A2R2A3SebS13S47S6aR4A1A1R3A3F_;F_;FF;Fmm;").
Proof using .
  intros mm F HS HF. apply Forall_holds_of_zholds; [exact HS|].
  apply Forall_forall. intros p Hp. apply (zholds_ext zr2 (zr_of (rho2 mm)) zl2 (zl_of (rho2 mm))).
  - intros j. reflexivity.
  - intros l. reflexivity.
  - exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Ltac zfact := cbn [zholds zcond].

Lemma sp_sum : ltac2:(tb__ "0|4|
S50S4cS5eS58S94Q40M0S22Vrho;PaA2A2M1S94G0S22Vrho;PfA2A2M2A2S5bZ2Z40M3A2A2S58G1S89G3G2A2A2A3").
Proof using Hdepth Herv Hgd Hsc Hsp Hsp_high.
  pose proof Hdepth as [D1 D2]. pose proof Hsp_high as SH. pose proof (urange (rw rho 10%positive)) as U10. pose proof (urange (rw rho 15%positive)) as U15.
  unfold as_stack in D1.
  unfold toS in *. rewrite (Z.mod_small (bv_unsigned (rw rho 15%positive)) (2 ^ 64)) in * by lia.
  change (2 ^ (64 - 1)) with (2 ^ 63) in *.
  destruct (bv_unsigned (rw rho 15%positive) <? 2 ^ 63) eqn:E; [apply Z.ltb_lt in E; lia|apply Z.ltb_ge in E].
  top_ranges.
  replace (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho 15%positive))
    with ((bv_unsigned (rw rho 10%positive) + (bv_unsigned (rw rho 15%positive) - 2 ^ 64)) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
Qed.

Theorem ZF_G : ltac2:(tb__ "0|0|
SebS13S88S68S69A2Sb7A3").
Proof using Hdepth Herv Hgd Hsc Hsp Hsp_high Htp.
  pose proof Hsp as [S1 S2]. pose proof Hdepth as [D1 D2]. pose proof Hsp_high as SH. unfold as_stack in D1.
  assert (ET : mc_tp C_U = 0x3a0d0) by reflexivity.
  unfold F_G.
  constructor. { zfact. rewrite zr2_10. split; [lia|]. rewrite (Z.mod_small _ (2 ^ 64)) by (pose proof (urange (rw rho 10%positive)); lia).
                 change (2 ^ 4) with 16. exact S2. }
  constructor. { zfact. rewrite ze_lit, ze_alu, !ze_var, zr2_10, zr2_15. cbn [zalu].
                 pose proof (urange (rw rho 10%positive)) as U10. pose proof (urange (rw rho 15%positive)) as U15.
                 rewrite !(Z.mod_small (bv_unsigned _) (2 ^ 64)) by lia. rewrite sp_sum. top_ranges.
                 change (140735332483072 mod 2 ^ 64) with 140735332483072. lia. }
  constructor. { zfact. rewrite ze_lit, ze_var, zr2_15. rewrite (toS_mod 64 (bv_unsigned (rw rho 15%positive))) by lia.
                 replace (toS 64 ((-288) mod 2 ^ 64)) with (-288) by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze_lit, ze_var, zr2_15. rewrite (toS_mod 64 (bv_unsigned (rw rho 15%positive))) by lia.
                 replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze_lit, ze24, ET. change (4096 mod 2 ^ 64) with 4096. lia. }
  constructor. { zfact. rewrite ze_lit, ze24, ET. change ((2 ^ 47) mod 2 ^ 64) with (2 ^ 47). lia. }
  constructor. { zfact. rewrite zr2_24, ET. split; [lia | reflexivity]. }
  constructor.
Qed.

Theorem ZF_M : ltac2:(tb__ "0|0|
SebS13S88S68S69A2Sb8A3").
Proof using HI HMI Herv Hgd Hm_key Hsc Hsp Hsp_high.
  pose proof m_R as MR. top_ranges. unfold F_M.
  constructor. { zfact. rewrite ze190, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. lia. }
  constructor. { zfact. split; [lia|]. rewrite zr2_190. rewrite (Z.mod_small _ (2 ^ 64)) by lia. change (2 ^ 3) with 8. lia. }
  constructor. { zfact. rewrite ze_lit, ze190. change (4096 mod 2 ^ 64) with 4096. lia. }
  constructor. { zfact. rewrite ze_lit, ze_alu, ze190, ze_lit. cbn [zalu]. change (40 mod 2 ^ 64) with 40. top_ranges.
                 change (140737479966720 mod 2 ^ 64) with 140737479966720. rewrite Z.mod_small; lia. }
  constructor.
Qed.

Theorem ZF_CTX : ltac2:(tb__ "0|0|
SebS13S88S68S69A2Sb9A3").
Proof using HI HMI Herv Hgd Hsc.
  pose proof ctx_ranges as CR. pose proof usg_bounds as UB. unfold F_CTX.
  constructor. { zfact. rewrite ze192, ze_lit. change ((2 ^ 48) mod 2 ^ 64) with (2 ^ 48). lia. }
  constructor. { zfact. rewrite ze196, ze_lit. change ((2 ^ 48) mod 2 ^ 64) with (2 ^ 48). lia. }
  constructor. { zfact. rewrite ze193, ze_lit. change (255 mod 2 ^ 64) with 255. lia. }
  constructor. { zfact. rewrite ze194, ze_lit. change (255 mod 2 ^ 64) with 255. lia. }
  constructor. { zfact. rewrite ze195, ze_lit. change (255 mod 2 ^ 64) with 255. lia. }
  constructor. { zfact. rewrite ze197, ze_lit. change (4294967295 mod 2 ^ 64) with 4294967295. lia. }
  constructor. { zfact. rewrite ze198, ze_lit. change (1 mod 2 ^ 64) with 1. unfold inos. destruct (is_bouncing s sc); lia. }
  constructor.
Qed.

Section Live.
Variables (cur : astate) (Lc : layout) (mWc : word -> option byte) (vmc : VmMaps).
Record live : Prop := mkLive {
  lv_MI : MInvI C_U (m :: X) RR U (mkMA cur Lc) (Glue.rd_of segsU mWc) (Glue.wok_of segsU mWc) vmc;
  lv_Xr : xraw (m :: X) cur;
  lv_hd : active_hd cur sc = None;
  lv_key : In m (keys cur);
  lv_raw : MT cur m = Some MRaw \/ MT cur m = Some (MFree None None);
  lv_ro : forall kk, 0 <= kk < 160 -> mWc (Z_to_bv 64 (0x108cc + kk)) = None;
  lv_gd : holds (byteview_of (Glue.rd_of segsU mWc) (fun _ => true)) (mc_chk_guard C_U) 8 gd;
  lv_m_addr : addr_of Lc m = zA m;

  lv_kept : mem_kept segsU C_U (mkMA s L) (mkMA cur Lc) mW mWc;
  lv_blocks : blocks Lc cur = blocks L s;

  lv_top : topL Lc = topL L }.
Hypothesis HLV : live.
Let LMI := lv_MI HLV.
Let LI : Inv (m :: X) RR U cur := mig_I LMI.
Let LXr := lv_Xr HLV.
Let Lhd := lv_hd HLV.
Let Lkey := lv_key HLV.
Let Lraw := lv_raw HLV.
Let Lro := lv_ro HLV.
Let Lgd := lv_gd HLV.
Lemma LL : layout_ok Lc cur. Proof using LMI. exact (mig_layout LMI). Qed.
Lemma LV : ltac2:(tb__ "0|0|
S122VLc;Vcur;Vvmc;A3"). Proof using LMI. exact (mig_vm LMI). Qed.
Lemma LLG : ledger_ok C_U vmc. Proof using LMI. exact (mig_ledger LMI). Qed.
Lemma Lctx : ly_ctx Lc = 0x5a3d0. Proof using LMI. exact (mig_ctx LMI). Qed.

Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.

Let bv0 : byteview := ltac2:(tb__ "0|0|
S119S108S83VmWc;A2S109S83VmWc;A2A2").
Lemma LreprO : ltac2:(tb__ "0|0|
S168VLc;Vcur;Vbv0;A3"). Proof using LMI. exact (mig_reprO LMI). Qed.
Lemma Lstat : ltac2:(tb__ "0|0|
S124S118S119S108S83VmWc;A2S92Q40A1S9L_;A2Vbv0;A3").
Proof using LMI. exact (mig_statics LMI). Qed.

Lemma cell_bytes0 : ltac2:(tb__ "0|4|
SefS4cS103SefR2Sf0Vcur;A1A3S50S8S4cA1S162VLc;R3A2S6S4cR2A2A3S2S149R1Sf5R5A1A2S51S51S59Z0S58Sf4VLc;Sf6R6A1A2S5fR2A1A2M0A2S5cG0S5bZ2Z40A2A2A2S51S50S3S109S83VmWc;S93Q40G0A2M1A3S9A3S50S8S92Q8M2A1M3A1S108S83VmWc;G1A3S6G3S93G2S100R5Sf5R6A1R2A3A2A2A3A2A2F_;Fj;F_;F_;Fz;Fc;").
Proof using LMI.
  intros c z Hc Hz j Hj.
  assert (CH : MallocInv.cell_holds Lc bv0 c) by exact (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 LreprO))) c Hc).
  exact (cell_bytes Lc _ _ c z CH Hz j Hj).
Qed.

Lemma cell_rw0 : ltac2:(tb__ "0|3|
SefS4cS4cS4cS2S103SefR5Sf0Vcur;A1A3S50S8S4cA1S162VLc;R6A2S6S4cR5A2A3S50S2Sf5R7A1R3A3S50S4cSf4VLc;Sf6R8A1A2S58R6R5A2A3S4cS51S59S58R8R7A2M0R1A2S5cR1S58G0S5fR6A1A2A2A2S51S50S3S109S83VmWc;S93Q40M1R2A2A3S9A3S54S92Q8A1M2G2S50S8G2A1S108S83VmWc;S93G1R3A2A3S6G2R1A2A3Lbb;A2A2F_;Fx;F_;F_;F_;F_;Fkk;Foffs;Fb;Fz;Fc;").
Proof using Herv Hgd Hsc Hsp LMI.
  intros c z b offs kk Hc Hz Hw Ha x Hx.
  destruct (cell_bytes0 c z Hc Hz (Z.to_nat (x - (b + offs))) ltac:(rewrite Hw; lia)) as (_ & W & R).
  rewrite Ha in W, R. rewrite Z2Nat.id in W, R by lia. replace (b + offs + (x - (b + offs))) with x in W, R by lia.
  split; [exact W | eexists; exact R].
Qed.

Lemma ev2 : ltac2:(tb__ "0|2|
S92Q40M0A1M1S8S92Q8A1A1F_;S10S50S3S8aR1A1S9A3S50G1S1dS6aR3A1R2A2S93G0S87S68S69R2A3A2A3F_;Fe;Fmm;").
Proof using .
  intros mm e He. rewrite <- (zr2_zl2_any mm). rewrite <- (eval_zeval (rho2 mm) e He). symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma ev2u : ltac2:(tb__ "0|1|
S92Q40M0A1S8S92Q8A1A1F_;S10S50S3S8aR1A1S9A3S50S4cS94G0S1dS6aR3A1R2A2A2S87S68S69R2A3A3F_;Fe;Fmm;").
Proof using . intros mm e He. rewrite <- (zr2_zl2_any mm). apply eval_zeval. exact He. Qed.

Lemma cell_view0 : ltac2:(tb__ "0|4|
SefS4cS4cS4cS2S10S103SefR6Sf0Vcur;A1A3S50S8S4cA1S162VLc;R7A2S6S4cR6A2A3S50S2Sf5R8A1R4A3S14aR5U8A2S50S4cSf4VLc;Sf6RaA1A2S58R8R7A2A3S50S92Q40M0A1S1dS6aVmWc;A1M1R6A2S93G0RaA2A3S2S149R1R9A2S50S8S92Q8M2A1M3A1S108S83VmWc;S93G0S58S58RcRbA2S5fR2A1A2A2A3S6G3SecG3R2S3dRaS1dG1R9A2A2S93G2Z0A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;Fe;Fkk;Foffs;Fb;Fz;Fc;").
Proof using LMI.
  intros c z b offs kk e Hc Hz Hw Hk Ha He j Hj.
  destruct (cell_bytes0 c z Hc Hz j ltac:(rewrite Hw; exact Hj)) as (_ & _ & R).
  rewrite Ha in R. rewrite R, He, Hw. rewrite nth_enc_bytes by assumption. reflexivity.
Qed.

Lemma owned_rw : ltac2:(tb__ "0|2|
S4cSf8VLc;Vcur;R1A3S51S50S3S109S83VmWc;S93Q40M0R2A2A3S9A3S54S92Q8A1M1G1S50S8G1A1S108S83VmWc;S93G0R3A2A3S6G1R1A2A3Lbb;A2A2F_;Fx;").
Proof using LMI.
  intros x OW. pose proof (proj2 (proj2 (proj1 LreprO)) x OW) as M. unfold bv0 in M.
  destruct (byteview_of (Glue.rd_of segsU mWc) (Glue.wok_of segsU mWc) x) as [vv|] eqn:E; [|exfalso; exact (M eq_refl)].
  destruct (byteview_of_Some _ _ _ _ E) as (_ & W & bb & Hb & _). split; [exact W | exists bb; exact Hb].
Qed.

Lemma ctx_owned off : ltac2:(tb__ "0|0|
S51S59Z0Voff;A2S5cVoff;Sf7A2A2Sf8VLc;Vcur;S58S101VLc;A1Voff;A2A3F_;").
Proof using Herv Hgd Hsc Hsp LI LXr.
  intros Ho. split.
  - exists (LCtx 0, CTX_SIZE). split; [left; reflexivity|]. cbn [fst snd loc_addr]. lia.
  - intros (b & Hb & Hx). cbn [fst snd] in Hx.
    destruct (user_block_in_group (m :: X) RR U cur Lc LI LXr b Hb) as (g & am & ii & fr & Hg & Hii & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
    destruct (group_range (m :: X) RR U cur Lc LI LL C_U vmc g am Hg LV LLG) as (_ & _ & _ & D).
    pose proof (stride_pos _ _ _ _ _ (inv_groups LI g am Hg)) as Sp. assert (0 <= stride_of am * ii) by nia.
    rewrite Eb in Hx, B1, B2. cbn [fst snd] in Hx, B1, B2. unfold addr_of in *. unfold UNIT, IB, CTX_SIZE in *. lia.
Qed.

Lemma rv_byte a vv : ltac2:(tb__ "0|3|
S50S8S4cA1S119S108S83VmWc;A2S92Q40M0A1S9L_;Va;A3S6S4cVvv;A2A3S50S8S92Q8M1A1M2A1S108S83VmWc;S93G0Va;A2A3S6G2S93G1Vvv;A2A2A3F_;").
Proof using .
  intros H. destruct (byteview_of_Some _ _ _ _ H) as (_ & _ & b & Hb & E). rewrite Hb. f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. reflexivity.
Qed.

Lemma wseg_range lo (n : nat) a : ltac2:(tb__ "0|1|
S50S3S104S4cS4cS10aS83S93Q40M0R1A2A2Lx;SeaS2S4cS2S58Vlo;S5fR1A1A2Lk;SedU0Vn;A2A4A3S9A3S51S59Vlo;Va;A2S5cVa;S58Vlo;S5fVn;A1A2A2A2S50S3S109S83VmWc;S93G0Va;A2A3S9A3F_;F_;").
Proof using .
  intros H Ha. unfold Glue.wok_of. destruct (mWc (Z_to_bv 64 a)); [reflexivity|].
  exact (forall_range_dec _ lo n H a Ha).
Qed.

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.

Definition O_act0 : sobj := Z_act0 sc.
Definition O_usg : sobj := Z_usg sc.
Definition O_usg2 : sobj := Z_usg2 sc.
Definition O_bnc : sobj := Z_bnc sc.
Definition O_useq : sobj := Z_useq sc.

Lemma got_wseg : ltac2:(tb__ "0|0|
S50S3S104S4cS4cS10aS83S93Q40R1A2A2Lx;SeaS2S4cS2S58Z28d50S5fR1A1A2Lk;SedU0U8A2A4A3S9A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma guard_wseg : ltac2:(tb__ "0|0|
S50S3S104S4cS4cS10aS83S93Q40R1A2A2Lx;SeaS2S4cS2S58Z5a338S5fR1A1A2Lk;SedU0U8A2A4A3S9A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma pgs_wseg : ltac2:(tb__ "0|0|
S50S3S104S4cS4cS10aS83S93Q40R1A2A2Lx;SeaS2S4cS2S58Z5a388S5fR1A1A2Lk;SedU0U8A2A4A3S9A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma errno_wseg : ltac2:(tb__ "0|0|
S50S3S104S4cS4cS10aS83S93Q40R1A2A2Lx;SeaS2S4cS2S58Z3a02cS5fR1A1A2Lk;SedU0U4A2A4A3S9A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma hold_got : ltac2:(tb__ "0|0|
S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2SbdA4").
Proof using Herv Hgd Hrom Hsc Hsp LMI.
  change O_got with (carved (SLit 0x28d50) 0 8 [(0, 8%nat, v 173)]).
  assert (B : bv_unsigned (eval (rho2 mWc) (SLit 0x28d50)) = 0x28d50) by (cbn [eval]; apply WalkArith.u64; lia).
  destruct Lstat as (_ & _ & _ & _ & _ & _ & _ & _ & (gd' & T9 & T10)).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. split; [apply (wseg_range 0x28d50 8); [apply got_wseg | cbn; lia]|].
    pose proof (T9 (Z.to_nat o) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. cbn [mc_chk_guard_got C_U] in E.
    eexists. exact (rv_byte _ _ E).
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    pose proof (T9 j Hj) as E. cbn [mc_chk_guard_got C_U] in E. rewrite (rv_byte _ _ E).
    rewrite (ev2 mWc (v 173) eq_refl), ze173, nth_enc_bytes by lia. reflexivity.
Qed.

Lemma hold_guard : ltac2:(tb__ "0|0|
S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2SbeA4").
Proof using Herv Hgd Hrom Hsc Hsp Lgd.
  change O_guard with (carved (v 173) 0 8 [(0, 8%nat, v 174)]).
  assert (B : bv_unsigned (eval (rho2 mWc) (v 173)) = 0x5a338) by (rewrite ev2u by reflexivity; rewrite ze173; reflexivity).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. split; [apply (wseg_range 0x5a338 8); [apply guard_wseg | cbn; lia]|].
    pose proof (Lgd (Z.to_nat o) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. cbn [mc_chk_guard C_U] in E.
    eexists. exact (rv_byte _ _ E).
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    pose proof (Lgd j Hj) as E. cbn [mc_chk_guard C_U] in E. rewrite (rv_byte _ _ E).
    rewrite (ev2 mWc (v 174) eq_refl), ze174, nth_enc_bytes by lia. reflexivity.
Qed.

Lemma hold_pgs : ltac2:(tb__ "0|0|
S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2Sc6A4").
Proof using Herv Hgd Hrom Hsc Hsp LMI.
  change O_pgs with (carved (SLit 0x5a388) 0 8 [(0, 8%nat, SLit 4096)]).
  assert (B : bv_unsigned (eval (rho2 mWc) (SLit 0x5a388)) = 0x5a388) by (cbn [eval]; apply WalkArith.u64; lia).
  destruct Lstat as (_ & T2 & _).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. split; [apply (wseg_range 0x5a388 8); [apply pgs_wseg | cbn; lia]|].
    pose proof (T2 (Z.to_nat o) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. replace (mc_page_size C_U) with 0x5a388 in E by reflexivity.
    eexists. exact (rv_byte _ _ E).
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    pose proof (T2 j Hj) as E. replace (mc_page_size C_U) with 0x5a388 in E by reflexivity. rewrite (rv_byte _ _ E).
    replace (eval (rho2 mWc) (SLit 4096)) with (Z_to_bv 64 4096) by reflexivity. rewrite nth_enc_bytes by lia. reflexivity.
Qed.

Lemma hold_errno : ltac2:(tb__ "0|0|
S11dS119S108S83VmWc;A2S92Q40A1S9L_;A2S11eS118A1U4Verv;A4S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2Sd0A4F_;").
Proof using Herv Hgd Hrom Hsc Hsp Htp.
  intros Lerv.
  change O_errno with (carved (SVar 24) (-164) (-160) [(-164, 4%nat, v 182)]).
  assert (B : bv_unsigned (eval (rho2 mWc) (SVar 24)) = mc_tp C_U) by (cbn [eval rho2 rw]; exact Htp).
  assert (ET : mc_tp C_U = 0x3a02c + 164) by reflexivity.
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia; try (rewrite ET; lia).
  - cells_inside_tac.
  - intros o Ho. rewrite ET. split; [apply (wseg_range 0x3a02c 4); [apply errno_wseg | cbn; lia]|].
    pose proof (Lerv (Z.to_nat (o + 164)) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. replace (mc_errno C_U) with 0x3a02c in E by reflexivity.
    replace (0x3a02c + 164 + o) with (0x3a02c + (o + 164)) by lia. eexists. exact (rv_byte _ _ E).
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite ET.
    pose proof (Lerv j Hj) as E. replace (mc_errno C_U) with 0x3a02c in E by reflexivity.
    replace (0x3a02c + 164 + -164 + Z.of_nat j) with (0x3a02c + Z.of_nat j) by lia. rewrite (rv_byte _ _ E).
    rewrite (ev2 mWc (v 182) eq_refl), ze182, nth_enc_bytes by lia. reflexivity.
Qed.

Lemma ro_tables2_P : ltac2:(tb__ "0|0|
S4cS51S59Z0R1A2S5cR1Za0A2A2S50S3S49S83S93Q40S58Z108ccR2A2A2A2S9A3F_;Fkk;").
Proof using Herv Hgd Hsc.
  intros kk Hk. exact (forall_range_dec (fun kk => ro_addr segsU (Z_to_bv 64 (0x108cc + kk))) 0 160 ltac:(vm_compute; reflexivity) kk ltac:(lia)).
Qed.

Lemma tab_image (base n : Z) (l : positive) (bytes : list Z) : ltac2:(tb__ "0|9|
S50S3S104S4cS4cS8S92Q8M0A1M1A1M2S3Lx;S3eS83S93Q40M3S58Vbase;R1A2A2A2G1S166G0R1SecG1S64R2A1M4SeaS4cG1S93G0A1Vbytes;A4M5S93G0Z0M6A2M7A4A3Lb;ScX8x2Lkk;SeaS2S4cS2S58G6S5fR1A1A2Lk;SedU0S64Vn;A1A2A4A3S9A3S50S7G1A1S44S6aVmWc;A1Vl;A2M8G5A3S4cS51S59G6R1A2S5cR1Vn;A2A2S50G2S3eS83S93G3S58Vbase;R2A2A2A2S6G1SecG1G4G8G7A4A2A3F_;Fkk;F_;F_;").
Proof using Herv Hgd Hsc Hsp.
  intros H El kk Hk.
  pose proof (forall_range_dec _ 0 (Z.to_nat n) H kk ltac:(lia)) as XB. cbn beta in XB. rewrite El.
  destruct (image_byte segsU (Z_to_bv 64 (base + kk))) as [b|]; [|discriminate].
  f_equal. unfold bv_eqb in XB. apply Z.eqb_eq in XB. apply bv_eq. exact XB.
Qed.

Lemma hold_sct : ltac2:(tb__ "0|0|
S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2SbfA4").
Proof using Herv Hgd Hrom Hsc Hsp Lro.
  unfold O_sct. apply obj_holds_frame_rom; try exact Hrom; try lia.
  - reflexivity.
  - intros kk Hk. split; [replace (0x108ec + kk) with (0x108cc + (32 + kk)) by lia; apply Lro; lia|].
    apply (tab_image 0x108ec 96 1 size_classes_bytes); [vm_cast_no_check (@eq_refl bool true) | reflexivity | exact Hk].
Qed.
Lemma hold_s2c : ltac2:(tb__ "0|0|
S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2Sc7A4").
Proof using Herv Hgd Hrom Hsc Hsp Lro.
  unfold O_s2c. apply obj_holds_frame_rom; try exact Hrom; try lia.
  - reflexivity.
  - intros kk Hk. split; [apply Lro; lia|].
    apply (tab_image 0x108cc 32 4 ctz_tab_bytes); [vm_cast_no_check (@eq_refl bool true) | reflexivity | exact Hk].
Qed.
Lemma hold_small : ltac2:(tb__ "0|0|
S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2Sc8A4").
Proof using Herv Hgd Hrom Hsc Hsp Lro.
  unfold O_small. apply obj_holds_frame_rom; try exact Hrom; try lia.
  - reflexivity.
  - intros kk Hk. split; [replace (0x1094c + kk) with (0x108cc + (128 + kk)) by lia; apply Lro; lia|].
    apply (tab_image 0x1094c 27 2 small_cnt_tab_bytes); [vm_cast_no_check (@eq_refl bool true) | reflexivity | exact Hk].
Qed.
Lemma hold_med : ltac2:(tb__ "0|0|
S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2Sc5A4").
Proof using Herv Hgd Hrom Hsc Hsp Lro.
  unfold O_med. apply obj_holds_frame_rom; try exact Hrom; try lia.
  - reflexivity.
  - intros kk Hk. split; [replace (0x10967 + kk) with (0x108cc + (155 + kk)) by lia; apply Lro; lia|].
    apply (tab_image 0x10967 4 3 med_cnt_tab_bytes); [vm_cast_no_check (@eq_refl bool true) | reflexivity | exact Hk].
Qed.

Lemma hold_ctx_cell (off : Z) (w : nat) (e : sv) (z : Z) : ltac2:(tb__ "0|6|
S53S103SefSf1Sf2S60Voff;Z8M0A2A1M1Vw;Sf3Vz;A1A3Sf0Vcur;A1M2A3S54S12eS12eS51S103SefSf1G1Vw;SfeR1A1A3G2A3S50S4cVz;S11cVLc;R1A2A3A2Lp;A2A2S14aVw;U8A2S14aU1Vw;A2S59G0Voff;A2S59S58Voff;S5fVw;A1M3A2M4S58G0Sf7A2A2S50S3S8aVe;A1S9A3S50S4cS87S68S69Ve;A3Vz;A3S51S59Z0Vz;A2S5cVz;S5bZ2Z40A2A2A2S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2S19S11Z5a3c8A1S11Voff;A1M5S11G4A1S0S14S16G5G3Ve;A3S4S14A1A3S1aA5A4F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using Herv Hgd Hrom Hsc Hsp LMI.
  intros Hc Hw Hw1 Ho1 Ho2 Se Ee Hz. pose proof Lctx as HCX.
  assert (B : bv_unsigned (eval (rho2 mWc) (SLit 0x5a3c8)) = 0x5a3c8) by (cbn [eval]; apply WalkArith.u64; lia).
  assert (HC : exists c, In c (image cur) /\ cellZ Lc c = Some z /\ mc_w c = w /\ loc_addr Lc (mc_loc c) = 0x5a3c8 + off).
  { destruct Hc as [Hc | (p & Hc & ->)].
    - eexists. split; [exact Hc|]. cbn [cellZ mc_w mc_loc loc_addr]. rewrite HCX. repeat split; try reflexivity. lia.
    - eexists. split; [exact Hc|]. cbn [cellZ mc_w mc_loc loc_addr]. rewrite HCX. repeat split; try reflexivity. lia. }
  destruct HC as (c & Hin & Hcz & Hcw & Had).
  change (mkObj (SLit 0x5a3c8) (SLit off) (SLit (off + Z.of_nat w)) [mkCell (SLit off) (Z.of_nat w) e] DUnknown) with (carved (SLit 0x5a3c8) off (off + Z.of_nat w) [(off, w, e)]).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try (unfold CTX_SIZE in *; lia).
  - unfold cells_inside. constructor; [repeat split; lia | constructor].
  - intros o Ho. apply (cell_rw0 c z 0x5a3c8 off w Hin Hcz Hcw Had). lia.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj.
    apply (cell_view0 c z 0x5a3c8 off w e Hin Hcz Hcw Hw Had); [|exact Hj].
    rewrite (ev2 mWc e Se), Ee. reflexivity.
Qed.

Lemma ctx_In_head c : ltac2:(tb__ "0|0|
S103SefVc;SffVcur;A1A3S103SefVc;Sf0Vcur;A1A3F_;").
Proof using . intros H. unfold image. apply in_app_iff. left. exact H. Qed.

Lemma Cact0 : ltac2:(tb__ "0|0|
S103SefSf1Sf2S58Sf9S5dZ8Vsc;A2A2A1U8Sf3Z0A1A3Sf0Vcur;A1A3").
Proof using Herv Hgd Hsc Hsp Lhd.
  apply ctx_In_head. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (Z.to_nat sc).
  rewrite Z2Nat.id by lia. split; [| apply in_seq; lia]. unfold active_hd in Lhd. rewrite Lhd. reflexivity.
Qed.
Lemma hold_act0 : ltac2:(tb__ "0|0|
S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2S112A4").
Proof using Herv Hgd Hrom Hsc Hsp LMI Lhd.
  unfold O_act0, Z_act0. replace (96 + 8 * sc) with ((88 + 8 * sc) + Z.of_nat 8) by lia.
  apply (hold_ctx_cell (88 + 8 * sc) 8 (SLit 0) 0); try reflexivity; try (unfold CTX_SIZE; lia).
  left. replace (88 + 8 * sc - 8) with (CTX_active + 8 * sc) by (unfold CTX_active; lia). exact Cact0.
Qed.

Lemma Cusg k : ltac2:(tb__ "0|0|
S51S59Z0Vk;A2S5cVk;Z30A2A2S103SefSf1Sf2S58SfcS5dZ8Vk;A2A2A1U8Sf3S127Vcur;Vk;A2A1A3Sf0Vcur;A1A3F_;").
Proof using Herv Hgd Hsc Hsp.
  intros Hk. apply ctx_In_head. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_map_iff. exists (Z.to_nat k). rewrite Z2Nat.id by lia. split; [| apply in_seq; lia]. unfold usage_of, znth. reflexivity.
Qed.
Lemma hold_usg : ltac2:(tb__ "0|0|
S50S4cS127Vcur;Vsc;A2S6bA3S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2S114A4F_;").
Proof using HI HMI Herv Hgd Hrom Hsc Hsp LMI.
  intros Eusg.
  unfold O_usg, Z_usg. replace (480 + 8 * sc) with ((472 + 8 * sc) + Z.of_nat 8) by lia.
  pose proof ctx_ranges. pose proof usg_bounds.
  apply (hold_ctx_cell (472 + 8 * sc) 8 (v 192) usg); try reflexivity; try (unfold CTX_SIZE; lia); [|apply ze192].
  left. replace (472 + 8 * sc - 8) with (CTX_usage + 8 * sc) by (unfold CTX_usage; lia). rewrite <- Eusg. exact (Cusg sc Hsc).
Qed.
Lemma hold_usg2 : ltac2:(tb__ "0|1|
S5cS58Vsc;Z1A2M0Z30A2S50S4cS127Vcur;G0A2S6dA3S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2S115A4F_;F_;").
Proof using HI HMI Herv Hgd Hrom Hsc Hsp LMI.
  intros H48 Eusg2. unfold O_usg2, Z_usg2. replace (488 + 8 * sc) with ((480 + 8 * sc) + Z.of_nat 8) by lia.
  pose proof ctx_ranges. pose proof usg_bounds.
  apply (hold_ctx_cell (480 + 8 * sc) 8 (v 196) usg2); try reflexivity; try (unfold CTX_SIZE; lia); [|apply ze196].
  left. replace (480 + 8 * sc - 8) with (CTX_usage + 8 * (sc + 1)) by (unfold CTX_usage; lia). rewrite <- Eusg2. exact (Cusg (sc + 1) ltac:(lia)).
Qed.
Lemma hold_ctr : ltac2:(tb__ "0|0|
S50S4cS12fVcur;A1S70A3S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2ScbA4F_;").
Proof using HI Hdepth Herv Hgd Hm_raw Hreq Hrom Hsc Hsp LMI Lraw.
  intros Ectr.
  unfold O_ctr. change (SLit 24) with (SLit (20 + Z.of_nat 4)). pose proof ctx_ranges.
  apply (hold_ctx_cell 20 4 (v 197) ctr); try reflexivity; try (unfold CTX_SIZE; lia); [|apply ze197].
  left. apply ctx_In_head. unfold ctx_cells. apply in_app_iff. left. rewrite <- Ectr. cbn. tauto.
Qed.
Lemma hold_seq : ltac2:(tb__ "0|0|
S50S4cS130Vcur;A1S71A3S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2SdeA4F_;").
Proof using HI Hdepth Herv Hgd Hm_raw Hreq Hrom Hsc Hsp LMI Lraw.
  intros Eseq.
  unfold O_seq. change (SLit 921) with (SLit (920 + Z.of_nat 1)). pose proof ctx_ranges.
  apply (hold_ctx_cell 920 1 (v 195) seqv); try reflexivity; try (unfold CTX_SIZE; lia); [|apply ze195].
  left. apply ctx_In_head. unfold ctx_cells. apply in_app_iff. left. rewrite <- Eseq. cbn. tauto.
Qed.
Lemma Cbnc : ltac2:(tb__ "0|2|
S51S59Z7M0Vsc;A2S59Vsc;Z26A2A2S103SefSf1Sf2S58SfaS60Vsc;G0A2M1A2A1U1Sf3S128G1S12aVcur;A1A2A1A3Sf0Vcur;A1A3F_;").
Proof using Herv Hgd Hsc Hsp.
  intros Hr. apply ctx_In_head. unfold ctx_cells. rewrite !in_app_iff. right; right; right; right.
  apply in_map_iff. exists (Z.to_nat (sc - 7)). rewrite Z2Nat.id by lia. split; [| apply in_seq; lia]. unfold znth. reflexivity.
Qed.
Lemma hold_bnc : ltac2:(tb__ "0|1|
S51S59Z7M0Vsc;A2S59Vsc;Z26A2A2S50S4cS128S60Vsc;G0A2S12aVcur;A1A2S6eA3S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2S113A4F_;F_;").
Proof using HI Herv Hgd Hrom Hsc Hsp LMI.
  intros Hr Ebnc. unfold O_bnc, Z_bnc. replace (882 + sc) with ((881 + sc) + Z.of_nat 1) by lia. pose proof ctx_ranges.
  apply (hold_ctx_cell (881 + sc) 1 (v 193) bnc); try reflexivity; try (unfold CTX_SIZE; lia); [|apply ze193].
  left. replace (881 + sc - 8) with (CTX_bounces + (sc - 7)) by (unfold CTX_bounces; lia). rewrite <- Ebnc. exact (Cbnc Hr).
Qed.

Definition Z_useqD (withb : bool) : sobj := ltac2:(tb__ "0|1|
S19S11Z5a3c8A1S11Z358A1S11Z378A1S5S14SdbS57Pa4A1S57Pa5A1S57Pa6A1S57Pa7A1A4S3S7S14A1Lwithb;Vwithb;S0S14S16S11S58Z351Vsc;A2A1Z1S57Pc2A1A3S4S14A1M0A3G0X3x2A3S1aA5").
Lemma Cuseq i : ltac2:(tb__ "0|0|
S149Vi;U20A2S103SefSf1Sf2S58SfbS5fVi;A1A2A1U1Sf3SecS4cVi;S126Vcur;A1Z0A4A1A3Sf0Vcur;A1A3F_;").
Proof using Herv Hgd Hsc.
  intros Hii. apply ctx_In_head. unfold ctx_cells. rewrite !in_app_iff. right; right; right; left.
  apply in_map_iff. exists i. split; [reflexivity | apply in_seq; lia].
Qed.
Lemma hold_useqD (withb : bool) : ltac2:(tb__ "0|0|
S50S7S4cA1S126Vcur;A1S126Vs;A1A3S50S3Vwithb;S9A3S51S59Z7Vsc;A2S59Vsc;Z26A2A2F_;S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2S116Vwithb;A1A4F_;F_;").
Proof using HI Herv Hgd Hrom Hsc Hsp LI LXr.
  intros Eus Hb. unfold Z_useqD. pose proof Lctx as HCX. pose proof ctx_ranges as CR.
  assert (B : bv_unsigned (eval (rho2 mWc) (SLit 0x5a3c8)) = 0x5a3c8) by (cbn [eval]; apply WalkArith.u64; lia).
  assert (DW : forall (jj : nat) (e : sv), (jj < 4)%nat -> eval (rho2 mWc) e = Z_to_bv 64 (udw jj) ->
              forall j, (j < 8)%nat -> Glue.rd_of segsU mWc (Z_to_bv 64 (0x5a3c8 + (856 + 8 * Z.of_nat jj) + Z.of_nat j)) = Some (nth j (enc_bytes 8 (eval (rho2 mWc) e)) (Z_to_bv 8 0))).
  { intros jj e Hjj He j Hj. rewrite He. unfold udw. rewrite udw2_enc, ubytes2_nth by exact Hj. rewrite <- Eus.
    pose proof (Cuseq (8 * jj + j) ltac:(lia)) as C.
    destruct (cell_bytes0 _ (nth (8 * jj + j) (st_unmap_seq cur) 0) C eq_refl 0%nat ltac:(cbn; lia)) as (_ & _ & R).
    cbn [mc_loc loc_addr mc_w] in R. rewrite HCX in R. unfold CTX_unmap_seq in R.
    replace (369616 + (848 + Z.of_nat (8 * jj + j)) + Z.of_nat 0) with (369608 + (856 + 8 * Z.of_nat jj) + Z.of_nat j) in R by lia.
    rewrite R. f_equal. f_equal.
    assert (RB : 0 <= nth (8 * jj + j) (st_unmap_seq cur) 0 <= 255).
    { pose proof (inv_ctx LI) as (_ & _ & _ & _ & _ & C6 & _). destruct (nth_in_or_default (8 * jj + j) (st_unmap_seq cur) 0) as [Hin| ->]; [exact (C6 _ Hin) | lia]. }
    unfold le_byte. rewrite Z.mul_0_r, Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite !Z.mod_small by lia. reflexivity. }
  assert (TAIL : forall cs, cells_inside 856 888 cs ->
            cells_in_view (rho2 mWc) (Glue.rd_of segsU mWc) 0x5a3c8 cs ->
            obj_holds segsU (rho2 mWc) (with_mem ms mWc) (carved (SLit 0x5a3c8) 856 888 ([(856, 8%nat, v 164); (864, 8%nat, v 165); (872, 8%nat, v 166); (880, 8%nat, v 167)] ++ cs))).
  { intros cs Hci Hcv. apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    - unfold cells_inside. apply Forall_app. split; [repeat constructor; cbn; lia | exact Hci].
    - intros o Ho. replace (0x5a3c8 + o) with (ly_ctx Lc + (o - 8)) by (rewrite HCX; lia). apply owned_rw. apply ctx_owned. unfold CTX_SIZE. lia.
    - unfold cells_in_view. apply Forall_app. split; [|exact Hcv].
      constructor. { intros j Hj. exact (DW 0%nat (v 164) ltac:(lia) ltac:(rewrite (ev2 mWc (v 164) eq_refl), ze164; reflexivity) j Hj). }
      constructor. { intros j Hj. exact (DW 1%nat (v 165) ltac:(lia) ltac:(rewrite (ev2 mWc (v 165) eq_refl), ze165; reflexivity) j Hj). }
      constructor. { intros j Hj. exact (DW 2%nat (v 166) ltac:(lia) ltac:(rewrite (ev2 mWc (v 166) eq_refl), ze166; reflexivity) j Hj). }
      constructor. { intros j Hj. exact (DW 3%nat (v 167) ltac:(lia) ltac:(rewrite (ev2 mWc (v 167) eq_refl), ze167; reflexivity) j Hj). }
      constructor. }
  destruct withb.
  - specialize (Hb eq_refl).
    change (mkObj (SLit 0x5a3c8) (SLit 856) (SLit 888) (useq_cells (v 164) (v 165) (v 166) (v 167) ++ [mkCell (SLit (849 + sc)) 1 (v 194)]) DUnknown)
      with (carved (SLit 0x5a3c8) 856 888 ([(856, 8%nat, v 164); (864, 8%nat, v 165); (872, 8%nat, v 166); (880, 8%nat, v 167)] ++ [(849 + sc, 1%nat, v 194)])).
    apply TAIL.
    + unfold cells_inside. repeat constructor; cbn; lia.
    + unfold cells_in_view. constructor; [|constructor]. intros j Hj.
      assert (Cin : In (MCell (LCtx (CTX_unmap_seq + (sc - 7))) 1 (VZ useq)) (image cur)).
      { unfold useq. rewrite <- Eus. unfold znth. replace (sc - 7) with (Z.of_nat (Z.to_nat (sc - 7))) at 1 by lia. apply Cuseq. lia. }
      apply (cell_view0 _ useq 0x5a3c8 (849 + sc) 1 (v 194) Cin eq_refl eq_refl ltac:(lia)); [cbn [mc_loc loc_addr]; rewrite HCX; unfold CTX_unmap_seq; lia| |exact Hj].
      rewrite (ev2 mWc (v 194) eq_refl), ze194. reflexivity.
  - change (mkObj (SLit 0x5a3c8) (SLit 856) (SLit 888) (useq_cells (v 164) (v 165) (v 166) (v 167) ++ []) DUnknown)
      with (carved (SLit 0x5a3c8) 856 888 ([(856, 8%nat, v 164); (864, 8%nat, v 165); (872, 8%nat, v 166); (880, 8%nat, v 167)] ++ [])).
    apply TAIL; constructor.
Qed.

Lemma m_cells_In c : ltac2:(tb__ "0|0|
S103SefVc;S102Vm;S6S136S131A2A2A3S103SefVc;Sf0Vcur;A1A3F_;").
Proof using LI Lkey Lraw.
  intros Hc. apply (meta_cells_in_imageI (m :: X) RR U cur LI m c Lkey).
  destruct Lraw as [E|E]; rewrite E; [exact Hc | exact Hc].
Qed.

Lemma hold_m : ltac2:(tb__ "0|0|
S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2Sc2A4").
Proof using HI HMI Hdepth Herv Hgd Hm_key Hm_raw Hreq Hrom Hsc Hsp Hsp_high LI Lkey Lraw.
  pose proof m_R as MR.
  assert (B : bv_unsigned (eval (rho2 mWc) (v 190)) = zA m) by (rewrite ev2u by reflexivity; apply ze190).
  change O_m with (carved (v 190) 0 40 [(0, 8%nat, SLit 0); (8, 8%nat, SLit 0); (16, 8%nat, SLit 0); (24, 4%nat, SLit 0); (28, 4%nat, SLit 0); (32, 8%nat, SLit 0)]).
  assert (C : forall off (w : nat), In (MCell (LMem (padd m off)) w (VZ 0)) (meta_slot_cells m (Some MRaw)) ->
             In (MCell (LMem (padd m off)) w (VZ 0)) (image cur) /\ loc_addr Lc (mc_loc (MCell (LMem (padd m off)) w (VZ 0))) = zA m + off).
  { intros off w Hin. split; [exact (m_cells_In _ Hin)|]. cbn [mc_loc]. rewrite loc_addr_padd, (lv_m_addr HLV). reflexivity. }
  cbn [meta_slot_cells] in C. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in C.
  destruct (C 0 8%nat ltac:(cbn; tauto)) as [I0 A0]. destruct (C 8 8%nat ltac:(cbn; tauto)) as [I1 A1].
  destruct (C 16 8%nat ltac:(cbn; tauto)) as [I2 A2]. destruct (C 24 4%nat ltac:(cbn; tauto)) as [I3 A3].
  destruct (C 28 4%nat ltac:(cbn; tauto)) as [I4 A4]. destruct (C 32 8%nat ltac:(cbn; tauto)) as [I5 A5].
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try (top_ranges; lia).
  - cells_inside_tac.
  - intros o Ho.
    destruct (Z_lt_dec o 8); [apply (cell_rw0 _ 0 (zA m) 0 8 I0 eq_refl eq_refl A0); lia|].
    destruct (Z_lt_dec o 16); [apply (cell_rw0 _ 0 (zA m) 8 8 I1 eq_refl eq_refl A1); lia|].
    destruct (Z_lt_dec o 24); [apply (cell_rw0 _ 0 (zA m) 16 8 I2 eq_refl eq_refl A2); lia|].
    destruct (Z_lt_dec o 28); [apply (cell_rw0 _ 0 (zA m) 24 4 I3 eq_refl eq_refl A3); lia|].
    destruct (Z_lt_dec o 32); [apply (cell_rw0 _ 0 (zA m) 28 4 I4 eq_refl eq_refl A4); lia|].
    apply (cell_rw0 _ 0 (zA m) 32 8 I5 eq_refl eq_refl A5); lia.
  - unfold cells_in_view.
    repeat (constructor; [intros j Hj;
      first [ apply (cell_view0 _ 0 (zA m) 0 8 (SLit 0) I0 eq_refl eq_refl ltac:(lia) A0 eq_refl j Hj)
            | apply (cell_view0 _ 0 (zA m) 8 8 (SLit 0) I1 eq_refl eq_refl ltac:(lia) A1 eq_refl j Hj)
            | apply (cell_view0 _ 0 (zA m) 16 8 (SLit 0) I2 eq_refl eq_refl ltac:(lia) A2 eq_refl j Hj)
            | apply (cell_view0 _ 0 (zA m) 24 4 (SLit 0) I3 eq_refl eq_refl ltac:(lia) A3 eq_refl j Hj)
            | apply (cell_view0 _ 0 (zA m) 28 4 (SLit 0) I4 eq_refl eq_refl ltac:(lia) A4 eq_refl j Hj)
            | apply (cell_view0 _ 0 (zA m) 32 8 (SLit 0) I5 eq_refl eq_refl ltac:(lia) A5 eq_refl j Hj) ] |]).
    constructor.
Qed.

Definition obj_of2 (d : od2) : sobj := ltac2:(tb__ "0|0|
S9eS15Ld;Vd;SbdSbeSc6SbfSc8Sc5Sc7S10SccR1A1Lev;S10Sd3R1A1Lhv;S10Sd7R1A1Luv;S10Sd6R1A1Luv;S10Sc4R1A1Lcv;S10Sd4R1A1Lbv;S10S10S10S10S8S10A1ScaR5R4R3R2R1A5Lob;Ld3;Ld2;Ld1;Ld0;S10Sd1R1A1Lqv;S10S10S10S10S10S10SddR6R5R4R3R2R1A6Lc5;Lc4;Lc3;Lc2;Lc1;Lc0;X9ex10").

Lemma soff2_lit : ltac2:(tb__ "0|1|
S92Q40A1S8S92Q8A1A1F_;S4cS51S59S62S5bZ2Z3eA2M0A1R1A2S59R1G0A2A2S50S4cS20S6aR3A1S11R2A1A2R2A3F_;Fz;Fmm;").
Proof using Herv Hgd Hsc. intros. apply soff_lit_small. lia. Qed.

Lemma ev_cx mm k : ltac2:(tb__ "0|1|
S51S59Z0Vk;A2S5cVk;S5bZ2Z20A2A2A2S50S92Q40M0A1S1dS6aVmm;A1SbbVk;A1A2S93G0S58S5dZ8Vsc;A2Vk;A2A2A3F_;").
Proof using Herv Hgd Hsc Hsp.
  intros Hk. rewrite (ev2 mm (e_cx k) eq_refl). f_equal. unfold e_cx. rewrite ze_alu, ze_alu, ze_var, zr2_12, !ze_lit. cbn [zalu].
  pose proof Hsc. change ((3 mod 2 ^ 64) mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. rewrite !Z.mod_small; lia.
Qed.
Lemma soff_cx mm k : ltac2:(tb__ "0|0|
S51S59Z0Vk;A2S5cVk;S5bZ2Z20A2A2A2S50S4cS20S6aVmm;A1SbbVk;A1A2S58S5dZ8Vsc;A2Vk;A2A3F_;").
Proof using Herv Hgd Hsc Hsp. intros Hk. unfold soff. rewrite (ev_cx mm k Hk). pose proof Hsc. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. rewrite u64 by lia. apply toS_small. lia. Qed.
Lemma ev_bx mm k : ltac2:(tb__ "0|1|
S51S59Z0Vk;A2S5cVk;S5bZ2Z20A2A2A2S50S92Q40M0A1S1dS6aVmm;A1S18S95S12PcA1S11Vk;A1A3A2S93G0S58Vsc;Vk;A2A2A3F_;").
Proof using Herv Hgd Hsc Hsp.
  intros Hk. rewrite (ev2 mm (SAlu ALU_ADD (SVar 12) (SLit k)) eq_refl). f_equal. rewrite ze_alu, ze_var, zr2_12, ze_lit. cbn [zalu]. pose proof Hsc. rewrite !Z.mod_small; lia.
Qed.
Lemma soff_bx mm k : ltac2:(tb__ "0|0|
S51S59Z0Vk;A2S5cVk;S5bZ2Z20A2A2A2S50S4cS20S6aVmm;A1S18S95S12PcA1S11Vk;A1A3A2S58Vsc;Vk;A2A3F_;").
Proof using Herv Hgd Hsc Hsp. intros Hk. unfold soff. rewrite (ev_bx mm k Hk). pose proof Hsc. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. rewrite u64 by lia. apply toS_small. lia. Qed.

Ltac soff_eq := cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]; rewrite ?soff_cx, ?soff_bx by lia; rewrite ?soff2_lit by lia; first [reflexivity | lia].
Ltac sem_obj := apply obj_holds_sem; [reflexivity | soff_eq | soff_eq | reflexivity |
  cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]; unfold cells_sem_eq; repeat (constructor; [cbn [c_off c_width c_val]; split; [soff_eq | split; reflexivity] |]); constructor].
Lemma hold_act0S : ltac2:(tb__ "0|0|
S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2Sd3S11Z0A1A1A4").
Proof using Herv Hgd Hrom Hsc Hsp LMI Lhd. pose proof Hsc. generalize hold_act0. unfold O_act0, Z_act0, S_act0v. sem_obj. Qed.
Lemma hold_usgS : ltac2:(tb__ "0|0|
S50S4cS127Vcur;Vsc;A2S6bA3S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2Sd7S57Pc0A1A1A4F_;").
Proof using HI HMI Herv Hgd Hrom Hsc Hsp LMI. intros E. pose proof Hsc. generalize (hold_usg E). unfold O_usg, Z_usg, S_usgv. sem_obj. Qed.
Lemma hold_usg2S : ltac2:(tb__ "0|1|
S5cS58Vsc;Z1A2M0Z30A2S50S4cS127Vcur;G0A2S6dA3S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2Sd6S57Pc4A1A1A4F_;F_;").
Proof using HI HMI Herv Hgd Hrom Hsc Hsp LMI. intros H48 E. pose proof Hsc. generalize (hold_usg2 H48 E). unfold O_usg2, Z_usg2, S_usg2v. sem_obj. Qed.
Lemma hold_bncS : ltac2:(tb__ "0|1|
S51S59Z7M0Vsc;A2S59Vsc;Z26A2A2S50S4cS128S60Vsc;G0A2S12aVcur;A1A2S6eA3S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2Sd4S57Pc1A1A1A4F_;F_;").
Proof using HI Herv Hgd Hrom Hsc Hsp LMI. intros Hr E. pose proof Hsc. generalize (hold_bnc Hr E). unfold O_bnc, Z_bnc, S_bncv. sem_obj. Qed.
Lemma hold_useqS (ob : option sv) : ltac2:(tb__ "0|0|
S50S7S4cA1S126Vcur;A1S126Vs;A1A3S8S10A1OLob;Vob;S10S51S50S10R1S57Pc2A1A3S51S59Z7Vsc;A2S59Vsc;Z26A2A2A2Lbv;S52X8x2S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2ScaS57Pa4A1S57Pa5A1S57Pa6A1S57Pa7A1Vob;A5A4F_;F_;").
Proof using HI Herv Hgd Hrom Hsc Hsp LI LXr.
  intros Eus Hob. pose proof Hsc. destruct ob as [bv|].
  - destruct Hob as [-> Hr]. generalize (hold_useqD true Eus ltac:(intros _; exact Hr)). unfold Z_useqD, S_useqv. cbn [useq_cells app]. sem_obj.
  - generalize (hold_useqD false Eus ltac:(intros XX; discriminate XX)). unfold Z_useqD, S_useqv. cbn [useq_cells app]. sem_obj.
Qed.

Definition od2_entry (d : od2) : Prop := ltac2:(tb__ "0|6|
S9eOLd;Vd;S52S52S52S52S52S52S52S10S51S50S10R1S57Pb6A1A3S11dS119S108S83VmWc;A2S92Q40A1S9L_;A2S11eS118A1U4Verv;A4A2Lev;S10S50S10R1S11Z0A1M0A3M1Lhv;S10S51S50S10R1S57Pc0A1A3S50S4cS127Vcur;Vsc;A2S6bA3A2Luv;S10S51S50S10R1S57Pc4A1A3S51S5cS58Vsc;Z1A2M2Z30A2S50S4cS127Vcur;G2A2S6dA3A2A2Luv;S10S51S50S10R1S57Pc5A1A3S50S4cS12fVcur;A1S70A3A2Lcv;S10S51S50S10R1S57Pc1A1A3S51S51S59Z7M3Vsc;A2S59Vsc;Z26A2A2M4S50S4cS128S60Vsc;G3A2S12aVcur;A1A2S6eA3A2A2Lbv;S10S10S10S10S8S10A1M5S51S50S10R5S57Pa4A1A3S51S50S10R4S57Pa5A1A3S51S50S10R3S57Pa6A1A3S51S50S10R2S57Pa7A1A3S51S50S7S4cA1S126Vcur;A1S126Vs;A1A3G5OLob;R1S10S51S50S10R1S57Pc2A1A3G4A2Lbv;S52X8x2A2A2A2A2A2Lob;Ld3;Ld2;Ld1;Ld0;S10S51S50S10R1S57Pc3A1A3S50S4cS130Vcur;A1S71A3A2Lqv;S10S10S10S10S10S10S51S50S10R6G0A3S51S50S10R5G0A3S51S50S10R4G0A3S51S50S10R3G0A3S51S50S10R2G0A3G1A2A2A2A2A2Lc5;Lc4;Lc3;Lc2;Lc1;Lc0;X9ex10").

Lemma od2_hold d : ltac2:(tb__ "0|0|
S10eVd;A1S1bS83S6aVmWc;A1Sb5Vms;VmWc;A2S10bVd;A1A4F_;").
Proof using HI HMI Hdepth Herv Hgd Hm_key Hm_raw Hreq Hrom Hsc Hsp Hsp_high Htp LI LXr Lgd Lhd Lkey Lraw Lro.
  destruct d; cbn [od2_entry obj_of2]; intros H.
  - apply hold_got. - apply hold_guard. - apply hold_pgs. - apply hold_sct. - apply hold_small. - apply hold_med. - apply hold_s2c.
  - destruct H as [E H1]. rewrite E. apply hold_errno. exact H1.
  - rewrite H. apply hold_act0S.
  - destruct H as [E H1]. rewrite E. apply hold_usgS. exact H1.
  - destruct H as (E & H48 & H1). rewrite E. apply hold_usg2S; assumption.
  - destruct H as [E H1]. rewrite E. apply hold_ctr. exact H1.
  - destruct H as (E & Hr & H1). rewrite E. apply hold_bncS; assumption.
  - destruct H as (E0 & E1 & E2 & E3 & Eus & Hob). rewrite E0, E1, E2, E3. apply hold_useqS; assumption.
  - destruct H as [E H1]. rewrite E. apply hold_seq. exact H1.
  - destruct H as (E0 & E1 & E2 & E3 & E4 & E5). rewrite E0, E1, E2, E3, E4, E5. apply hold_m.
Qed.

Definition od2_range (d : od2) : Z * Z := ltac2:(tb__ "0|0|
Sa3Vsc;S75Vm;A1S11bS118A1Vd;A4").

Lemma rng_lit2 : ltac2:(tb__ "0|3|
S10S4cS4cS7S14A1S30S4cS51S59S62S5bZ2Z3eA2M0A1R5A2S59R5G0A2A2M1G1S50S4cS94Q40S1dS6aVmWc;A1M2R8A2A2R3A3S50SaS4cS4cA2S24G2S19R9S11R8A1S11R7A1R6R5A5A2S1S4cS4cS58R4R8A2S58R4R7A2A4A3F_;F_;F_;Fb;Fd;Fcs;Fhi;Flo;Fbase;").
Proof using Herv Hgd Hsc.
  intros base lo hi cs d b Hlo Hhi Hb. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite Hb, !soff2_lit by lia. reflexivity.
Qed.

Lemma rng_sym : ltac2:(tb__ "0|3|
S10S10S7S14A1S30S4cS4cS50S4cS20S6aVmWc;A1M0R6A2R2A3M1G1S50SaS4cS4cA2S24G0S19S11Sb6A1R8R7R6R5A5A2S1S4cS4cS58Z5a3c8M2R4A2S58G2R3A2A4A3F_;F_;Fzhi;Fzlo;Fd;Fcs;Fhi;Flo;").
Proof using Herv Hgd Hsc.
  intros lo hi cs d zlo zhi Elo Ehi. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval].
  rewrite Elo, Ehi. unfold LK. rewrite WalkArith.u64 by lia. reflexivity.
Qed.
Lemma od2_rng d : ltac2:(tb__ "0|0|
S50SaS4cS4cA2S24S6aVmWc;A1S10bVd;A1A2S10fVd;A1A3").
Proof using HI HMI Herv Hgd Hm_key Hsc Hsp Hsp_high Htp.
  pose proof m_R as MR. pose proof Hsc.
  destruct d; cbn [obj_of2 od2_range od2_rangeP]; unfold O_got, O_guard, O_pgs, O_sct, O_small, O_med, O_s2c, O_errnov, S_act0v, S_usgv, S_usg2v, O_ctrv, S_bncv, S_useqv, O_seqv, O_mv, LK.
  - apply rng_lit2; [lia | lia |]. cbn [eval]; apply WalkArith.u64; lia.
  - apply rng_lit2; [lia | lia |]. rewrite ev2u by reflexivity; rewrite ze173; reflexivity.
  - apply rng_lit2; [lia | lia |]. cbn [eval]; apply WalkArith.u64; lia.
  - apply rng_lit2; [lia | lia |]. cbn [eval]; apply WalkArith.u64; lia.
  - apply rng_lit2; [lia | lia |]. cbn [eval]; apply WalkArith.u64; lia.
  - apply rng_lit2; [lia | lia |]. cbn [eval]; apply WalkArith.u64; lia.
  - apply rng_lit2; [lia | lia |]. cbn [eval]; apply WalkArith.u64; lia.
  - apply rng_lit2; [lia | lia |]. cbn [eval rho2 rw]. exact Htp.
  - fold LK. rewrite (rng_sym _ _ _ _ (8 * sc + 88) (8 * sc + 96)) by (apply soff_cx; lia). unfold LK. f_equal; lia.
  - fold LK. rewrite (rng_sym _ _ _ _ (8 * sc + 472) (8 * sc + 480)) by (apply soff_cx; lia). unfold LK. f_equal; lia.
  - fold LK. rewrite (rng_sym _ _ _ _ (8 * sc + 480) (8 * sc + 488)) by (apply soff_cx; lia). unfold LK. f_equal; lia.
  - apply rng_lit2; [lia | lia |]. cbn [eval]; apply WalkArith.u64; lia.
  - fold LK. rewrite (rng_sym _ _ _ _ (sc + 881) (sc + 882)) by (apply soff_bx; lia). unfold LK. f_equal; lia.
  - apply rng_lit2; [lia | lia |]. cbn [eval]; apply WalkArith.u64; lia.
  - apply rng_lit2; [lia | lia |]. cbn [eval]; apply WalkArith.u64; lia.
  - apply rng_lit2; [lia | lia |]. rewrite ev2u by reflexivity; apply ze190.
Qed.

Definition od2_wf (d : od2) : Prop := od2_wfP sc d.
Lemma od2_entry_wf d : ltac2:(tb__ "0|0|
S10eVd;A1S10dVd;A1F_;").
Proof using Hdepth Herv Hgd Hm_raw Hreq Hsc Hsp Lraw. destruct d; cbn; tauto. Qed.

Lemma od2_disjoint d1 d2 : ltac2:(tb__ "0|0|
S10dVd1;A1S10dVd2;A1Sa2Vd1;Vd2;A2S32S10fVd1;A1S10fVd2;A1A2F_;F_;F_;").
Proof using HI HMI Herv Hgd Hm_key Hsc Hsp.
  pose proof m_R as MR. unfold od2_range, od2_wf. replace (mc_tp C_U) with 0x3a0d0 by reflexivity.
  apply od2_disjointP; lia.
Qed.

Fixpoint od2_pairwise (l : list od2) : Prop :=
  match l with [] => True | d :: t => Forall (od2_disj d) t /\ od2_pairwise t end.

Lemma od2_pairwise_disjoint l : ltac2:(tb__ "0|0|
SebS9eS10dVl;A3S10cVl;A1S31S6aVmWc;A1SeaS9eS15S10bVl;A4A2F_;F_;").
Proof using HI HMI Herv Hgd Hm_key Hsc Hsp Hsp_high Htp.
  induction l as [|d t IH]; intros W H; cbn [od2_pairwise map pairwise_disjoint] in *; [exact I|].
  apply Forall_cons_iff in W as [Wd Wt].
  destruct H as [Hd Ht]. split; [|apply IH; [exact Wt | exact Ht]].
  apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d' & <- & Hd').
  rewrite !od2_rng. apply od2_disjoint; [exact Wd | exact (proj1 (Forall_forall _ _) Wt d' Hd') | exact (proj1 (Forall_forall _ _) Hd d' Hd')].
Qed.

Fixpoint od2_pairwiseb (l : list od2) : bool :=
  match l with [] => true | d :: t => forallb (fun d' => negb (Nat.eqb (od2_kind d) (od2_kind d'))) t && od2_pairwiseb t end.
Lemma od2_pairwiseb_ok l : ltac2:(tb__ "0|0|
S50S3S117Vl;A1S9A3S10cVl;A1F_;").
Proof using .
  induction l as [|d t IH]; cbn; intros H; [exact I|]. apply andb_prop in H as [H1 H2]. split; [|apply IH; exact H2].
  apply Forall_forall. intros d' Hd'. pose proof (proj1 (forallb_forall _ _) H1 d' Hd') as X1. cbn beta in X1.
  unfold od2_disj. intros E. rewrite E, Nat.eqb_refl in X1. discriminate X1.
Qed.

Definition sp0 : Z := bv_unsigned (rw rho 10%positive).
Definition D0 : Z := ltac2:(tb__ "0|0|
S89Z40S94Q40S22Vrho;PfA2A2A2").

Lemma ev_sp mm : ltac2:(tb__ "0|1|
S50S92Q40A1S1dS6aVmm;A1S12PaM0A1A2S22Vrho;G0A2A3").
Proof using Herv Hgd Hsc Hsp. cbn [eval rho2 rw]. apply rw2_low; lia. Qed.
Lemma ev_v15 mm : ltac2:(tb__ "0|1|
S50S92Q40A1S1dS6aVmm;A1S12PfM0A1A2S22Vrho;G0A2A3").
Proof using Herv Hgd Hsc Hsp. cbn [eval rho2 rw]. apply rw2_low; lia. Qed.

Lemma rng_stk cs : ltac2:(tb__ "0|0|
S50SaS4cS4cA2S24S6aVmWc;A1S19S12PaA1S12PfA1S11Z0A1Vcs;S1aA5A2S1S4cS4cS58S110S111A2S110A4A3").
Proof using Herv Hgd Hsc Hsp.
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite ev_sp.
  rewrite soff2_lit by lia. unfold soff. rewrite ev_v15. rewrite bv_signed_toS by (cbn; lia). unfold sp0, D0. f_equal. lia.
Qed.

Lemma od2_vs_stack cs d : ltac2:(tb__ "0|1|
S32S24S6aVmWc;A1M0S19S12PaA1S12PfA1S11Z0A1Vcs;S1aA5A2S24G0S10bVd;A1A2A2").
Proof using HI HMI Herv Hgd Hm_key Hsc Hsp Hsp_high Htp.
  rewrite rng_stk, od2_rng. pose proof Hsp_high as SH. pose proof m_R as MR. pose proof Hsc. unfold sp0, D0, SymState.ranges_disjoint.
  assert (ET : mc_tp C_U = 0x3a0d0) by reflexivity.
  destruct d; cbn [od2_range od2_rangeP fst snd]; rewrite ?ET; top_ranges; lia.
Qed.

Theorem carve2 : ltac2:(tb__ "0|2|
S2eS7S14A1S7S9eA1S4dS7S160A1M0S15fS50S7S15A1S23R6A1S0S15S19S12PaA1S12PfA1S11Z0A1R5S1aA5S4S15A1A3A3SebS9eS10eR5A3S10cR6A1S1cS2bR9A1S2cR9A1S29R9A1S28R9A1S2dR9A1S5S15S23R9A1SeaS9eS15S10bR7A4A3S27R9A1R6S2aR9A1A9S2eS50S3S34R1A1S9A3S26S83S6aVmWc;A1M1RbS1G0S13cR7S13dVms;R6A2A4A4S26S83G1R3S1G0S13cR8S13dVms;R7A2A4A4F_;F_;TS';F_;F_;F_;Fmd;Ftr;Fnx;Fds;Fcs;FS;").
Proof using HI HMI Hdepth Herv Hgd Hm_key Hm_raw Hreq Hrom Hsc Hsp Hsp_high Htp LI LXr Lgd Lhd Lkey Lraw Lro.
  intros S cs ds nx tr md HO Hok Hpw S' Hwf Hsm. apply smatch_extend_objs.
  - exact Hsm.
  - exact Hwf.
  - change (rm (rho2 mWc)) with mWc. apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd).
    apply od2_hold. exact (proj1 (Forall_forall _ _) Hok d Hd).
  - rewrite HO. apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd). constructor; [|constructor]. apply od2_vs_stack.
  - apply od2_pairwise_disjoint; [|exact Hpw]. apply Forall_forall. intros d Hd. apply od2_entry_wf. exact (proj1 (Forall_forall _ _) Hok d Hd).
Qed.

Lemma od2_pairwise_app ds0 ds : ltac2:(tb__ "0|0|
S10cS5S9eVds0;Vds;A3A1S51S10cVds;A1S9eS9eS103S9eR2Vds0;A3S103S9eR2Vds;A3Sa2R4R3A2F_;F_;Fd;Fd0;A2F_;").
Proof using .
  induction ds0 as [|d0 t IH]; cbn [od2_pairwise app]; intros H.
  - split; [exact H|]. intros d0 d [].
  - destruct H as [F P]. destruct (IH P) as [P1 P2]. split; [exact P1|].
    intros x d [<-|Hx] Hd.
    + apply (proj1 (Forall_forall _ _) F). apply in_app_iff. right. exact Hd.
    + exact (P2 x d Hx Hd).
Qed.

Theorem carve2p : ltac2:(tb__ "0|3|
S2eS7S14A1S7S9eA1M0G0S4dS7S160A1M1S15fS50S7S15A1S23R7A1S0S15S19S12PaA1S12PfA1S11Z0A1R6S1aA5SeaS9eS15S10bR5A4A3A3SebS9eS10dR6A3SebS9eS10eR6A3S10cS5S9eR8R7A3A1S1cS2bRbA1S2cRbA1S29RbA1S28RbA1S2dRbA1S5S15S23RbA1SeaS9eS15S10bR8A4A3S27RbA1R7S2aRbA1A9S2eS50S3S34R1A1S9A3S26S83S6aVmWc;A1M2RdS1G1S13cR8S13dVms;R7A2A4A4S26S83G2R3S1G1S13cR9S13dVms;R8A2A4A4F_;F_;TS';F_;F_;F_;F_;Fmd;Ftr;Fnx;Fds;Fds0;Fcs;FS;").
Proof using HI HMI Hdepth Herv Hgd Hm_key Hm_raw Hreq Hrom Hsc Hsp Hsp_high Htp LI LXr Lgd Lhd Lkey Lraw Lro.
  intros S cs ds0 ds nx tr md HO W0 Hok Hpw S' Hwf Hsm.
  destruct (od2_pairwise_app ds0 ds Hpw) as [Pw Cross].
  assert (Wd : Forall od2_wf ds) by (apply Forall_forall; intros d Hd; apply od2_entry_wf; exact (proj1 (Forall_forall _ _) Hok d Hd)).
  apply smatch_extend_objs.
  - exact Hsm.
  - exact Hwf.
  - change (rm (rho2 mWc)) with mWc. apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd).
    apply od2_hold. exact (proj1 (Forall_forall _ _) Hok d Hd).
  - rewrite HO. apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd). constructor; [apply od2_vs_stack|].
    apply Forall_forall. intros o' Ho'. apply in_map_iff in Ho' as (d0 & <- & Hd0).
    rewrite !od2_rng. apply od2_disjoint; [exact (proj1 (Forall_forall _ _) W0 d0 Hd0) | exact (proj1 (Forall_forall _ _) Wd d Hd) | exact (Cross d0 d Hd0 Hd)].
  - apply od2_pairwise_disjoint; [exact Wd | exact Pw].
Qed.

Lemma pairwise_disjoint_ext r1 r2 (l : list sobj) : ltac2:(tb__ "0|0|
S15S103S15R1Vl;A3S50SaS4cS4cA2S24Vr2;R2A2S24Vr1;R2A2A3F_;Fo;S31Vr1;Vl;A2S31Vr2;Vl;A2F_;F_;").
Proof using .
  induction l as [|o t IH]; cbn [pairwise_disjoint]; intros E H; [exact I|]. destruct H as [F P]. split.
  - apply Forall_forall. intros o' Ho'. rewrite (E o ltac:(left; reflexivity)), (E o' ltac:(right; exact Ho')). exact (proj1 (Forall_forall _ _) F o' Ho').
  - apply IH; [intros x Hx; apply E; right; exact Hx | exact P].
Qed.

Theorem carve2a : ltac2:(tb__ "0|2|
S4bS2eS7S14A1S7S9eA1M0G0S4dS7S160A1M1S15fS169S6aVmWc;A1R8A2S50S3S104S9eS9eS167S16aS10bR1A1A2Ld;S5S9eR6R5A3A3S9A3S50S7S15A1S23R9A1S0S15S19S12PaA1S12PfA1S11Z0A1R8S1aA5SeaS9eS15S10bR7A4A3A3SebS9eS10dR8A3SebS9eS10eR8A3S10cS5S9eRaR9A3A1S1cS2bRdA1S2cRdA1S29RdA1S28RdA1S2dRdA1S5S15S23RdA1SeaS9eS15S10bRaA4A3S27RdA1R9S2aRdA1A9S2eS50S3S34R1A1S9A3S26S83R10RfS1G1S13cRaS13dVms;R9A2A4A4S26S83R11R3S1G1S13cRbS13dVms;RaA2A4A4F_;F_;TS';F_;F_;F_;F_;F_;F_;Fmd;Ftr;Fnx;Fds;Fds0;Fcs;FS;FrhoB;").
Proof using HI HMI Hdepth Herv Hgd Hm_key Hm_raw Hreq Hrom Hsc Hsp Hsp_high Htp LI LXr Lgd Lhd Lkey Lraw Lro.
  intros rhoB S cs ds0 ds nx tr md Hag Hvars HO W0 Hok Hpw S' Hwf Hsm.
  destruct Hag as (AW & AL & AM).
  assert (HV : forall v, WalkLink.below200 v = true -> rw (rho2 mWc) v = rw rhoB v) by (intros v Hv; symmetry; exact (AW v Hv)).
  assert (HL' : forall l, rl (rho2 mWc) l = rl rhoB l) by (intros l; symmetry; exact (AL l)).
  assert (VARS : forall d, In d (ds0 ++ ds) -> obj_vars_all WalkLink.below200 (obj_of2 d) = true)
    by (intros d Hd; exact (proj1 (forallb_forall _ _) Hvars d Hd)).
  assert (RNG : forall d, In d (ds0 ++ ds) -> obj_range rhoB (obj_of2 d) = od2_range d).
  { intros d Hd. rewrite (obj_range_agree_vars WalkLink.below200 (rho2 mWc) rhoB (obj_of2 d) HV HL' (VARS d Hd)). apply od2_rng. }
  destruct (od2_pairwise_app ds0 ds Hpw) as [Pw Cross].
  assert (Wd : Forall od2_wf ds) by (apply Forall_forall; intros d Hd; apply od2_entry_wf; exact (proj1 (Forall_forall _ _) Hok d Hd)).
  apply smatch_extend_objs.
  - exact Hsm.
  - exact Hwf.
  - rewrite AM. change (rm (rho2 mWc)) with mWc. apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd).
    apply (obj_holds_agree_vars segsU WalkLink.below200 (rho2 mWc) rhoB _ _ HV HL' (VARS d ltac:(apply in_app_iff; right; exact Hd))).
    apply od2_hold. exact (proj1 (Forall_forall _ _) Hok d Hd).
  - rewrite HO. apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd). constructor.
    + unfold obj_range at 1. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval]. unfold soff. cbn [eval].
      rewrite (AW 10%positive eq_refl), (AW 15%positive eq_refl).
      rewrite (RNG d ltac:(apply in_app_iff; right; exact Hd)).
      pose proof (od2_vs_stack cs d) as D. rewrite od2_rng, rng_stk in D.
      change (rw (rho2 mWc) 10%positive) with (eval (rho2 mWc) (SVar 10)). change (rw (rho2 mWc) 15%positive) with (eval (rho2 mWc) (SVar 15)).
      rewrite ev_sp, ev_v15. rewrite !bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64.
      replace (toS 64 (bv_unsigned (Z_to_bv 64 0))) with 0 by reflexivity. rewrite Z.add_0_r. unfold sp0, D0 in D. exact D.
    + apply Forall_forall. intros o' Ho'. apply in_map_iff in Ho' as (d0 & <- & Hd0).
      rewrite (RNG d ltac:(apply in_app_iff; right; exact Hd)), (RNG d0 ltac:(apply in_app_iff; left; exact Hd0)).
      apply od2_disjoint; [exact (proj1 (Forall_forall _ _) W0 d0 Hd0) | exact (proj1 (Forall_forall _ _) Wd d Hd) | exact (Cross d0 d Hd0 Hd)].
  - apply (pairwise_disjoint_ext (rho2 mWc)).
    + intros o Ho. apply in_map_iff in Ho as (d & <- & Hd). rewrite (RNG d ltac:(apply in_app_iff; right; exact Hd)). symmetry. apply od2_rng.
    + apply od2_pairwise_disjoint; [exact Wd | exact Pw].
Qed.
End Live.

Lemma live_A : ltac2:(tb__ "0|0|
S80Vs;VL;VmW;Vvm;A4").
Proof using HMI HXr Hgd_holds Hhd Hm_key Hm_raw Hm_ro.
  constructor.
  - exact HMI. - exact HXr. - exact Hhd. - exact Hm_key. - exact Hm_raw. - exact Hm_ro.
  - exact Hgd_holds. - reflexivity.
  - intros a _ _ _ _ _. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
End InstA.
End Mal_agrp_I.
