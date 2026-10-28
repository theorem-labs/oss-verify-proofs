(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "true"; "nil"; "list"; "option"; "pair"; "bool"; "false"; "prod"; "None"; "Some"; "nat"; "length"; "andb"; "S"; "app"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "SLit"; "sv"; "cell"; "mkCell"; "sprop"; "SAlu"; "sobj"; "mkObj"; "SPBranch"; "DUnknown"; "SPNot"; "SPUle"; "SAluW"; "SExt"; "DRom"; "SPAlign"; "mkSS"; "FcsrFrm0"; "SMd"; "rw"; "obj_holds"; "eval"; "SLBytes"; "obj_range"; "rl"; "image_byte"; "ranges_disjoint"; "smatch"; "soff"; "ss_objs"; "sstate"; "enc_bytes"; "holds"; "mkVal"; "odefault"; "pairwise_disjoint"; "ro_addr"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "ALU_AND"; "ALU_SLL"; "BC_GE"; "ALU_SRL"; "ALU_SUB"; "M_MUL"; "BC_NE"; "ALU_OR"; "ALU_XOR"; "aluop"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "True"; "ex"; "False"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "Zpos"; "N"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "am_freed"; "am_aidx"; "am_mem"; "ones"; "am_avail"; "am_maplen"; "am_last"; "ameta"; "mslot"; "lowbit"; "MUsed"; "am_next"; "am_prev"; "am_sc"; "ctz32"; "st_bounces"; "znth"; "IB"; "class_size"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I.Inst"; "zr1"; "zl1"; "member"; "mam"; "zA"; "mptr"; "rho1"; "pM0"; "pA"; "od"; "pB"; "pC"; "pP"; "e_sx"; "vfreed"; "vbits"; "vbyte"; "e_onesw"; "member_val"; "vavail"; "mbase"; "mbyte"; "vptr"; "obj_of"; "od_ok"; "rcls"; "e_and"; "e_bncoff"; "e_dbidx"; "e_lowbit"; "vmem"; "MC"; "MP"; "O_stk"; "e_actoff"; "e_bncidx0"; "e_tabidx"; "od_range"; "optrZ"; "rw1"; "O_act"; "O_bnc"; "O_ctz"; "O_got"; "O_guard"; "O_mem"; "O_meta"; "O_sct"; "e_acthi"; "e_bncidx"; "od_pairwise"; "rw1v"; "sp0"; "D0"; "F_T"; "F_base5"; "MA_"; "MB"; "MM0"; "OD_bnc"; "OD_mem"; "OD_meta"; "e_ctz"; "od_disj"; "od_ok_at"; "rl1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "leaf"; "sym_run"; "RsCut"; "RsSymJump"; "RsFuel"; "RsMem"; "lf_state"; "mkLeaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR"; "CUTS"; "segs"; "NXA"; "SA_E"; "SA_H"; "SA_N"; "SA_R1nh"; "SA_R1ns"; "SA_R1sh"; "SA_R2nh"; "SA_R2nr"; "SA_R2sh"; "SA_R2sr"; "SA_R3nh"; "SA_R3nr"; "SA_R3sh"; "SA_R3sr"; "SA_R4nh"; "SA_R4nr"; "SA_R4sh"; "SA_R4sr"; "SA_R5nh"; "SA_R5nr"; "SA_R5sh"; "SA_R5sr"; "SL_R1ns"; "ST0_R1ns"; "ST2_R1ns"; "ST_R1nh"; "ST_R1sh"; "ST_R2nh"; "ST_R2nr"; "ST_R2sh"; "ST_R2sr"; "ST_R3nh"; "ST_R3nr"; "ST_R3sh"; "ST_R3sr"; "ST_R4nh"; "ST_R4nr"; "ST_R4sh"; "ST_R4sr"; "ST_R5nh"; "ST_R5nr"; "ST_R5sh"; "ST_R5sr"; "SX_R1ns"; "LA_E"; "LA_H"; "LA_N"; "LA_R1nh"; "LA_R1ns"; "LA_R1sh"; "LA_R2nh"; "LA_R2nr"; "LA_R2sh"; "LA_R2sr"; "LA_R3nh"; "LA_R3nr"; "LA_R3sh"; "LA_R3sr"; "LA_R4nh"; "LA_R4nr"; "LA_R4sh"; "LA_R4sr"; "LA_R5nh"; "LA_R5nr"; "LA_R5sh"; "LA_R5sr"; "LL_R1ns"; "LT0_R1ns"; "LT2_R1ns"; "LT_R1nh"; "LT_R1sh"; "LT_R2nh"; "LT_R2nr"; "LT_R2sh"; "LT_R2sr";
"LT_R3nh"; "LT_R3nr"; "LT_R3sh"; "LT_R3sr"; "LT_R4nh"; "LT_R4nr"; "LT_R4sh"; "LT_R4sr"; "LT_R5nh"; "LT_R5nr"; "LT_R5sh"; "LT_R5sr"; "LX_R1ns"; "RA_E"; "RA_H"; "RA_N"; "RA_R1nh"; "RA_R1ns"; "RA_R1sh"; "RA_R2nh"; "RA_R2nr"; "RA_R2sh"; "RA_R2sr"; "RA_R3nh"; "RA_R3nr"; "RA_R3sh"; "RA_R3sr"; "RA_R4nh"; "RA_R4nr"; "RA_R4sh"; "RA_R4sr"; "RA_R5nh"; "RA_R5nr"; "RA_R5sh"; "RA_R5sr"; "RL_R1ns"; "RT0_R1ns"; "RT2_R1ns"; "RT_R1nh"; "RT_R1sh"; "RT_R2nh"; "RT_R2nr"; "RT_R2sh"; "RT_R2sr"; "RT_R3nh"; "RT_R3nr"; "RT_R3sh"; "RT_R3sr"; "RT_R4nh"; "RT_R4nr"; "RT_R4sh"; "RT_R4sr"; "RT_R5nh"; "RT_R5nr"; "RT_R5sh"; "RT_R5sr"; "RX_R1ns"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "pow"; "lt"; "opp"; "modulo"; "eqb"; "leb"; "mul"; "land"; "sub"; "of_nat"; "to_pos"; "shiftr"; "to_nat"; "of_N"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "zholds"; "sx32"; "zsupported"; "toS"; "zalu"; "psupported"; "zl_of"; "zle"; "zr_of"; "zsublist"; "@Corelib.Lists.ListDef"; "map"; "nth"; "Forall"; "seq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "sh"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "pre_fregs"; "pre_regs"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts"; "mprev"; "mnext"; "inring"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "wseg_addr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sv_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "meta_bits"; "image"; "mc_w"; "MT"; "alloc_owned"; "loc_addr"; "mc_loc"; "active_hd"; "CTX_SIZE"; "CTX_active"; "Inv"; "LCtx"; "MCell"; "VP"; "alinks"; "keys"; "le_byte"; "ly_ctx"; "meta_slot_cells"; "ring_ok"; "usedX"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "below200"; "@Corelib.Init.Peano"; "le"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "mc_chk_guard"; "topL"; "ctz_tab_bytes"; "holds"; "size_classes_bytes"; "statics_ok"; "vm_ok"; "@Stdlib.Lists.List"; "In"; "forallb"; "last"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "as_stack"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "reprO"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_aslot_I.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma ro_tables_P : ltac2:(tb__ "0|0|
S52S4cS13dZ0R1A2S13fR1Z80A2A2S4bS6S35S15dS161Q40S13cZ108ccR2A2A2A2S1A3F_;Fkk;").
Proof.
  intros kk Hk. exact (forall_range_dec (fun kk => ro_addr segsU (Z_to_bv 64 (0x108cc + kk))) 0 128 ltac:(vm_compute; reflexivity) kk ltac:(lia)).
Qed.

Section Inst.
Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.

Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).

Hypothesis HI : ltac2:(tb__ "0|0|
S176VX;S9S8S56S52A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S4cS13dZ0Vreq;A2S13dS13cVreq;S68A2S69Vsc;A1A2A2").

Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S4bS4S56A1S173Vs;Vsc;A2SaS56Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S17fS17aVX;Vs;Vsc;A3SaS56Vm0;A2S0S56Vm0;Vrest;A3A3").

Local Notation mrec := (RingFacts.mrec s).
Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).
Definition pM0 : sptr := m0.
Definition pA : sptr := mnext pM0.
Definition pB : sptr := mnext pA.
Definition pC : sptr := mnext pB.
Definition pP : sptr := mprev pM0.

Inductive member := MM0 | MA_ | MB | MC | MP.
Definition member_eqb (x y : member) : bool := ltac2:(tb__ "0|1|
S6cS6Lx;Vx;S6cS6Ly;M0Vy;S1S7S7S7S7X6cx5G0Vy;S7S1S7S7S7X6cx5G0Vy;S7S7S1S7S7X6cx5G0Vy;S7S7S7S1S7X6cx5G0Vy;S7S7S7S7S1X6cx5X6cx5").
Definition mptr (x : member) : sptr := ltac2:(tb__ "0|0|
S6cS56Lx;Vx;S71S72S74S75S76X6cx5").
Definition mbase (x : member) : positive := ltac2:(tb__ "0|0|
S6cS53Lx;Vx;P78P82P8cP96Pa0X6cx5").
Definition mbyte (x : member) : Z := ltac2:(tb__ "0|0|
S6cS52Lx;Vx;VbyM0;VbyA;VbyB;VbyC;VbyP;X6cx5").
Definition mam (x : member) : ameta := mrec (mptr x).

Definition rcls : nat := Nat.min 5 (S (length rest)).

Local Notation rl0 := (m0 :: rest).
Lemma RP i : ltac2:(tb__ "0|2|
S183Vi;ScS56S0S56Vm0;Vrest;A3M0A2A2S4cS4bS56S164Vs;S158S56Vi;G0Vm0;A4M1A2S158S56SeVi;A1G0Vm0;A4A3S4bS56S163Vs;G1A2SbS56Li;Vi;S18fS56G0Vm0;A3SbS158S56R1G0Vm0;A4Lj;Xbx2A3A2F_;").
Proof using Hsc Rg. exact (ring_pos X s sc m0 Hsc rest Rg i). Qed.
Lemma RD i j : ltac2:(tb__ "0|2|
S183Vi;ScS56S0S56Vm0;Vrest;A3M0A2M1A2S183Vj;G1A2S4dS4bSbVi;Vj;A3A1S4dS4bS56S158S56Vi;G0Vm0;A4S158S56Vj;G0Vm0;A4A3A1F_;F_;F_;").
Proof using Rg. exact (ring_distinct X s sc m0 rest Rg i j). Qed.
Lemma RNL : ltac2:(tb__ "0|0|
S4bS56S164Vs;S18fS56S0S56Vm0;Vrest;A3Vm0;A3A2Vm0;A3").
Proof using Hsc Rg. exact (ring_next_last X s sc m0 Hsc rest Rg). Qed.

Local Notation nn := (length rl0).
Local Notation el := (fun i => nth i rl0 m0).

Lemma OVF i : ltac2:(tb__ "0|1|
S182ScS56S0S56Vm0;Vrest;A3M0A2Vi;A2S4bS56S158S56Vi;G0Vm0;A4Vm0;A3F_;").
Proof using . intros Hi. apply nth_overflow. exact Hi. Qed.
Lemma nn_pos : (1 <= nn)%nat. Proof using Hsc. cbn. lia. Qed.
Lemma E_A : ltac2:(tb__ "0|0|
S4bS56S72S158S56U1S0S56Vm0;Vrest;A3Vm0;A4A3").
Proof using Hsc Rg. unfold pA, pM0. destruct (RP 0 ltac:(cbn; lia)) as [N0 _]. exact N0. Qed.
Lemma E_P : ltac2:(tb__ "0|1|
S4bS56S76S158S56S197ScS56S0S56Vm0;Vrest;A3M0A2U1A2G0Vm0;A4A3").
Proof using Hsc Rg. unfold pP, pM0. destruct (RP 0 ltac:(cbn; lia)) as [_ P0]. rewrite <- last_nth. exact P0. Qed.
Lemma E_B : ltac2:(tb__ "0|2|
S182U2M0ScS56S0S56Vm0;Vrest;A3M1A2A2S4bS56S74S158S56G0G1Vm0;A4A3F_;").
Proof using Hsc Rg. intros H. unfold pB. rewrite E_A. destruct (RP 1 ltac:(lia)) as [N1 _]. exact N1. Qed.
Lemma E_C : ltac2:(tb__ "0|2|
S182U3M0ScS56S0S56Vm0;Vrest;A3M1A2A2S4bS56S75S158S56G0G1Vm0;A4A3F_;").
Proof using Hsc Rg. intros H. unfold pC. rewrite (E_B ltac:(lia)). destruct (RP 2 ltac:(lia)) as [N2 _]. exact N2. Qed.
Lemma PV_A : ltac2:(tb__ "0|0|
S182U2ScS56S0S56Vm0;Vrest;A3A2A2S4bS56S163Vs;S72A2S71A3F_;").
Proof using Hsc Rg. intros H. rewrite E_A. destruct (RP 1 ltac:(lia)) as [_ P1]. exact P1. Qed.
Lemma PV_B : ltac2:(tb__ "0|0|
S182U3ScS56S0S56Vm0;Vrest;A3A2A2S4bS56S163Vs;S74A2S72A3F_;").
Proof using Hsc Rg. intros H. rewrite (E_B ltac:(lia)), E_A. destruct (RP 2 ltac:(lia)) as [_ P2]. exact P2. Qed.
Lemma PV_C : ltac2:(tb__ "0|0|
S182U4ScS56S0S56Vm0;Vrest;A3A2A2S4bS56S163Vs;S75A2S74A3F_;").
Proof using Hsc Rg. intros H. rewrite (E_C ltac:(lia)), (E_B ltac:(lia)). destruct (RP 3 ltac:(lia)) as [_ P3]. exact P3. Qed.
Lemma NX_P : ltac2:(tb__ "0|0|
S4bS56S164Vs;S76A2S71A3").
Proof using Hsc Rg. rewrite E_P, <- last_nth. exact RNL. Qed.

Ltac rdist i j := let H := fresh in pose proof (RD i j ltac:(lia) ltac:(lia) ltac:(lia)) as H; cbn [nth] in H; exact H.

Lemma cls1 : ltac2:(tb__ "0|0|
S4bSbS83U1A3S4cS4bS56S72S71A3S4cS4bS56S74S71A3S4cS4bS56S75S71A3S4bS56S76S71A3A2A2A2F_;").
Proof using Hsc Rg.
  intros H. unfold rcls in H. assert (Hn : nn = 1%nat) by (cbn [length] in *; lia).
  assert (EA : pA = pM0) by (rewrite E_A; apply OVF; lia).
  assert (EB : pB = pM0) by (unfold pB; rewrite EA; exact EA).
  assert (EC : pC = pM0) by (unfold pC; rewrite EB; exact EA).
  assert (EP : pP = pM0) by (rewrite E_P, Hn; reflexivity).
  auto.
Qed.

Lemma cls2 : ltac2:(tb__ "0|0|
S4bSbS83U2A3S4cS4bS56S74S71A3S4cS4bS56S75S72A3S4cS4bS56S76S72A3S4cS4bS56S163Vs;S72A2S71A3S4dS4bS56S72S71A3A1A2A2A2A2F_;").
Proof using Hsc Rg.
  intros H. unfold rcls in H. assert (Hn : nn = 2%nat) by (cbn [length] in *; lia).
  assert (EB : pB = pM0) by (rewrite (E_B ltac:(lia)); apply OVF; lia).
  assert (EC : pC = pA) by (unfold pC; rewrite EB; reflexivity).
  assert (EP : pP = pA) by (rewrite E_P, E_A, Hn; reflexivity).
  repeat split; auto using PV_A with nocore.
  - apply PV_A. lia.
  - rewrite E_A. unfold pM0. rdist 1%nat 0%nat.
Qed.

Lemma cls3 : ltac2:(tb__ "0|0|
S4bSbS83U3A3S4cS4bS56S75S71A3S4cS4bS56S76S74A3S4cS4bS56S163Vs;S72A2S71A3S4cS4bS56S163Vs;S74A2S72A3S4cS4dS4bS56S72S71A3A1S4cS4dS4bS56S74S71A3A1S4dS4bS56S74S72A3A1A2A2A2A2A2A2F_;").
Proof using Hsc Rg.
  intros H. unfold rcls in H. assert (Hn : nn = 3%nat) by (cbn [length] in *; lia).
  assert (EC : pC = pM0) by (rewrite (E_C ltac:(lia)); apply OVF; lia).
  assert (EP : pP = pB) by (rewrite E_P, (E_B ltac:(lia)), Hn; reflexivity).
  split; [exact EC|]. split; [exact EP|]. split; [apply PV_A; lia|]. split; [apply PV_B; lia|].
  rewrite (E_B ltac:(lia)), E_A. unfold pM0.
  split; [rdist 1%nat 0%nat|]. split; [rdist 2%nat 0%nat|]. rdist 2%nat 1%nat.
Qed.

Lemma cls4 : ltac2:(tb__ "0|0|
S4bSbS83U4A3S4cS4bS56S76S75A3S4cS4bS56S164Vs;S75A2S71A3S4cS4bS56S163Vs;S72A2S71A3S4cS4bS56S163Vs;S74A2S72A3S4cS4bS56S163Vs;S75A2S74A3S4cS4dS4bS56S72S71A3A1S4cS4dS4bS56S74S71A3A1S4cS4dS4bS56S75S71A3A1S4cS4dS4bS56S74S72A3A1S4cS4dS4bS56S75S72A3A1S4dS4bS56S75S74A3A1A2A2A2A2A2A2A2A2A2A2F_;").
Proof using Hsc Rg.
  intros H. unfold rcls in H. assert (Hn : nn = 4%nat) by (cbn [length] in *; lia).
  assert (EP : pP = pC) by (rewrite E_P, (E_C ltac:(lia)), Hn; reflexivity).
  split; [exact EP|]. split; [rewrite <- EP; apply NX_P|].
  split; [apply PV_A; lia|]. split; [apply PV_B; lia|]. split; [apply PV_C; lia|].
  rewrite (E_C ltac:(lia)), (E_B ltac:(lia)), E_A. unfold pM0.
  split; [rdist 1%nat 0%nat|]. split; [rdist 2%nat 0%nat|]. split; [rdist 3%nat 0%nat|].
  split; [rdist 2%nat 1%nat|]. split; [rdist 3%nat 1%nat|]. rdist 3%nat 2%nat.
Qed.

Lemma cls5 : ltac2:(tb__ "0|0|
S4bSbS83U5A3S4cS4bS56S164Vs;S76A2S71A3S4cS4bS56S163Vs;S72A2S71A3S4cS4bS56S163Vs;S74A2S72A3S4cS4bS56S163Vs;S75A2S74A3S4cS4dS4bS56S72S71A3A1S4cS4dS4bS56S74S71A3A1S4cS4dS4bS56S75S71A3A1S4cS4dS4bS56S76S71A3A1S4cS4dS4bS56S74S72A3A1S4cS4dS4bS56S75S72A3A1S4cS4dS4bS56S76S72A3A1S4cS4dS4bS56S75S74A3A1S4cS4dS4bS56S76S74A3A1S4dS4bS56S76S75A3A1A2A2A2A2A2A2A2A2A2A2A2A2A2F_;").
Proof using Hsc Rg.
  intros H. unfold rcls in H. assert (Hn : (5 <= nn)%nat) by (cbn [length] in *; lia).
  split; [apply NX_P|]. split; [apply PV_A; lia|]. split; [apply PV_B; lia|]. split; [apply PV_C; lia|].
  rewrite E_P, (E_C ltac:(lia)), (E_B ltac:(lia)), E_A. unfold pM0.
  split; [rdist 1%nat 0%nat|]. split; [rdist 2%nat 0%nat|]. split; [rdist 3%nat 0%nat|]. split; [rdist (nn - 1)%nat 0%nat|].
  split; [rdist 2%nat 1%nat|]. split; [rdist 3%nat 1%nat|]. split; [rdist (nn - 1)%nat 1%nat|].
  split; [rdist 3%nat 2%nat|]. split; [rdist (nn - 1)%nat 2%nat|]. rdist (nn - 1)%nat 3%nat.
Qed.

Local Notation inring := (RingFacts.inring X s sc m0).

Lemma mem_inring : ltac2:(tb__ "0|0|
S6cS165VX;Vs;Vsc;Vm0;S6fR1A1A5Fx;").
Proof using .
  intros [| | | |]; cbn [mptr pM0 pA pB pC pP].
  - apply inring_m0.
  - apply inring_next; apply inring_m0.
  - do 2 apply inring_next; apply inring_m0.
  - do 3 apply inring_next; apply inring_m0.
  - apply inring_prev; apply inring_m0.
Qed.

Lemma mam_used : ltac2:(tb__ "0|2|
S6cS4cS180VX;Vs;S6fR1A1M0S6dR1A1M1A4S4cS4bS52S64G1A1Vsc;A3S4bS4S5fA1S16fVs;G0A2SaS5fS61G1A1A2A3A2A2Fx;").
Proof using HI Hhd Hsc.
  intros x. destruct (inring_used X None U s sc m0 HI Hsc Hhd (mptr x) (mem_inring x)) as (am & Hu & Hs & M & E).
  unfold mam. rewrite E. auto.
Qed.

Lemma mptr_key : ltac2:(tb__ "0|0|
S6cS18dS56S6fR1A1S17bVs;A1A3Fx;").
Proof using HI Hhd Hsc. intros x. destruct (mam_used x) as (_ & _ & M). exact (MT_Some_In_keys _ _ _ M). Qed.

Lemma mnext_used x : ltac2:(tb__ "0|0|
S4fS56S56S4cS4bS4S56A1S62S6dVx;A1A1SaS56R1A2A3S4bS56S164Vs;S6fVx;A1A2R1A3A2Ln;A2").
Proof using HI Hhd Hsc.
  destruct (ring_ex X None U s sc m0 HI Hsc Hhd) as [rest' Rg'].
  pose proof (mem_inring x rest' Rg') as Hin.
  destruct (ring_links _ _ _ _ Rg' Hin) as (pr & nx & Lk).
  destruct (lk_mnext_mprev X s sc (mptr x) _ _ Lk) as [E1 E2].
  destruct (alinks_used _ _ _ _ _ Lk) as (am & Hu & _ & El). injection El as Ep En.
  pose proof (usedX_fun _ _ _ _ _ Hu (proj1 (mam_used x))) as ->.
  exists nx. split; [symmetry; exact En | exact E1].
Qed.

Lemma mprev_used x : ltac2:(tb__ "0|0|
S4fS56S56S4cS4bS4S56A1S63S6dVx;A1A1SaS56R1A2A3S4bS56S163Vs;S6fVx;A1A2R1A3A2Lp;A2").
Proof using HI Hhd Hsc.
  destruct (ring_ex X None U s sc m0 HI Hsc Hhd) as [rest' Rg'].
  pose proof (mem_inring x rest' Rg') as Hin.
  destruct (ring_links _ _ _ _ Rg' Hin) as (pr & nx & Lk).
  destruct (lk_mnext_mprev X s sc (mptr x) _ _ Lk) as [E1 E2].
  destruct (alinks_used _ _ _ _ _ Lk) as (am & Hu & _ & El). injection El as Ep En.
  pose proof (usedX_fun _ _ _ _ _ Hu (proj1 (mam_used x))) as ->.
  exists pr. split; [symmetry; exact Ep | exact E2].
Qed.

Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S194S184VX;S9S8S56S52A2A1VU;S193Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Lemma HL : layout_ok L s. Proof using HMI. exact (mig_layout HMI). Qed.
Lemma HV : ltac2:(tb__ "0|0|
S18cVL;Vs;Vvm;A3"). Proof using HMI. exact (mig_vm HMI). Qed.
Lemma HLG : ledger_ok C_U vm. Proof using HMI. exact (mig_ledger HMI). Qed.
Lemma Hctx : ly_ctx L = 0x5a3d0. Proof using HMI. exact (mig_ctx HMI). Qed.

Hypothesis Hbytes : ltac2:(tb__ "0|3|
S6cS4cS4cS13dZ0M0S7fR1A1M1A2S13fG1Z100A2A2S4cS4bS52S141G1Z20A2S58S6dR1A1M2A1A3S4dS4bS52S5cG2A1G0A3A1S4bS52S7fR2A1S58S6dR2A1A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.

Hypothesis Hspanv : 0 <= spanv <= 300.

Definition zA (q : sptr) : Z := addr_of L q.

Lemma mem_R : ltac2:(tb__ "0|c|
S6cS4cS4cS13dZ0M0S5bS6dR1A1M1A1M2A2S13fG2S13eZ2Z20A2M3A2A2S4cS4cS13dG0S57G1A1M4A2S13fG4G3A2A2S4cS4cS13dG0S5dG1A1M5A2S13dG5Z1fA2A2S4cS4cS13dG0S58G1A1M6A2S13dG6G5A2A2S4cS13dG0S5cG1A1A2S4cS13dZ1000M7S6eS6fR1A1A1M8A2S4cS13dS13cG8Z28A2S187VL;A1M9A2S4cS4bS52S141G8Z8A2G0A3S4cS13dG7S6eS59G1A1A1MaA2S4cS13dS13cGaZ10MbA2G9A2S4bS52S141GaGbA2G0A3A2A2A2A2A2A2A2A2A2A2Fx;").
Proof using HI HMI Hbnc Hgd Hhd Hsc.
  intros x. destruct (mam_used x) as (Hu & Hs & M).
  pose proof (used_ranges X None U s HI (mptr x) (mam x) Hu) as (R1 & R2 & R3 & R4 & R5).
  pose proof (used_addrs X None U s HI C_U L vm HL HV HLG (mptr x) (mam x) Hu) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  pose proof (stride_pos _ _ _ _ _ (inv_groups HI _ _ Hu)) as SP.
  assert (E16 : 16 <= stride_of (mam x) * (am_last (mam x) + 1)) by nia.
  unfold zA, PGSZ, META_SIZE, UNIT in *.
  repeat split; lia.
Qed.

Lemma mem_bits : ltac2:(tb__ "0|3|
S6cS4cS4cS13dZ0S16cS6dR1A1M0A1M1A2S13fG1S13eZ2M2Z3bA2A2A2S4cS4bS52S64G0A1Vsc;A3S13fS144S5cG0A1Z1000A2S13eG2Z2fA2A2A2A2Fx;").
Proof using HI HMI Hbnc Hgd Hhd Hsc.
  intros x. destruct (mam_used x) as (Hu & Hs & M). pose proof (mem_R x) as (R1 & R2 & R3 & R4 & R5 & _).
  assert (ML : am_maplen (mam x) * 4096 < 2 ^ 47).
  { destruct (Z_lt_dec 0 (am_maplen (mam x))) as [Hp|Hz]; [|lia].
    pose proof (inv_groups HI _ _ Hu) as (_ & _ & _ & _ & Gmp & _).
    destruct (Gmp Hp) as (r & rg & Em & Hr & Hk & Hl & Len & _).
    pose proof (fp_mem_range C_U L s vm _ _ HV HLG (footprint_region_In s _ _ Hr Hk Hl) ltac:(rewrite Len; unfold PGSZ; lia)) as (M1 & M2 & _).
    top_ranges. unfold addr_of, loc_addr in M1, M2. cbn [prid poff] in M1, M2. rewrite Len in M2. unfold PGSZ in *. lia. }
  unfold meta_bits. rewrite Hs. pose proof Hsc. split; [|auto]. nia.
Qed.

Lemma bits_mod32 x : ltac2:(tb__ "0|2|
S4cS4bS52S141S16cS6dVx;A1M0A1M1Z20A2S5dG0A1A3S4bS52S149G1Z5A2S13cS13cZ1S144Z2Vsc;A2A2S144Z80S5cG0A1A2A2A3A2").
Proof using HI HMI Hbnc Hgd Hhd Hsc.
  pose proof (mem_R x) as (_ & _ & R3 & _ & R5 & _). pose proof (mem_bits x) as (_ & Hs & _). unfold meta_bits. rewrite Hs.
  split.
  - replace (am_last (mam x) + 32 + 64 * sc + 4096 * am_maplen (mam x)) with (am_last (mam x) + (1 + 2 * sc + 128 * am_maplen (mam x)) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. Z.to_euclidean_division_equations; lia.
Qed.

Lemma mptr_addr_ne x y : ltac2:(tb__ "0|5|
S4dS4bS56S6fVx;A1M0S6fVy;A1M1A3A1S51S13dS13cS6eG0A1M2Z28M3A2S6eG1A1M4A2S13dS13cG4G3A2G2A2A2F_;").
Proof using HI HMI Hhd Hsc. intros Hne. unfold zA. exact (meta_ranges_disjoint X None U s L HI HL (mptr x) (mptr y) (mptr_key x) (mptr_key y) Hne). Qed.

Lemma mmem_addr_ne x y : ltac2:(tb__ "0|0|
S4dS4bS56S6fVx;A1S6fVy;A1A3A1S4dS4bS52S6eS59S6dVx;A1A1A1S6eS59S6dVy;A1A1A1A3A1F_;").
Proof using HI HMI Hhd Hsc. intros Hne. unfold zA. exact (used_mem_addr_ne X None U s L HI HL _ _ _ _ (proj1 (mam_used x)) (proj1 (mam_used y)) Hne). Qed.

Definition member_val (x : member) (k : Z) : option Z := ltac2:(tb__ "0|1|
S6dVx;A1S5eS6S4S52A1L_;M0S142Vk;Z0A2SaS52S6eS6fVx;A1A1A2G0S142Vk;Z3A2SaS52S6eS59R1A1A1A2G0S142Vk;Z4A2SaS52S5bR1A1A2G0S142Vk;Z5A2SaS52S57R1A1A2G0S142Vk;Z6A2SaS52S16cR1A1A2G0S142Vk;Z7A2SaS52S7fVx;A1A2S9S52A1X6x2X6x2X6x2X6x2X6x2X6x2Tam;").

Definition rw1v (j : positive) : option Z := ltac2:(tb__ "0|6|
S54Vj;A1S52S6S4S52A1L_;M0S142R1ZcA2SaS52Vsc;A2G0S142R1ZdA2SaS52Vreq;A2G0SdS143Z78M1R1A2S143R1Z7fA2A2S7cSa4S146R1G1A2A2G0SdS143Z82M2R1A2S143R1Z89A2A2S7cSa2S146R1G2A2A2G0SdS143Z8cM3R1A2S143R1Z93A2A2S7cSa3S146R1G3A2A2G0SdS143Z96M4R1A2S143R1Z9dA2A2G0S142R1Z98A2SaS52S6eS164Vs;S75A2A1A2S7cS89S146R1G4A2A2X6x2G0SdS143Za0M5R1A2S143R1Za7A2A2G0S142R1Za1A2SaS52S6eS163Vs;S76A2A1A2S7cS8aS146R1G5A2A2X6x2G0S142R1ZaaA2SaS52Vbnc;A2G0S142R1ZabA2SaS52S14eVmaskv;A1A2G0S142R1ZacA2SaS52Vspanv;A2G0S142R1ZadA2SaS52S186S184A1A2G0S142R1ZaeA2SaS52Vgd;A2S9S52A1X6x2X6x2X6x2X6x2X6x2X6x2X6x2X6x2X6x2X6x2X6x2X6x2Tz;").

Definition rw1 (j : positive) : word := ltac2:(tb__ "0|1|
S4S52A1S160Q40M0A1Lx;S9dVj;A1S52S161G0R1A2Lz;S24Vrho;Vj;A2X4x2").

Definition rl1 (l : positive) : list byte := ltac2:(tb__ "0|4|
S6S3S160Q8M0A1M1A1L_;M2S195Vl;P1A2S157S52G1S161G0A1M3S18aA4G2S195Vl;P4A2S157S52G1G3S188A4S29Vrho;Vl;A2X6x2X6x2").

Definition rho1 (m : word -> option byte) : valuation := ltac2:(tb__ "0|0|
S32S91SabVm;A3").

Lemma rw1_low : ltac2:(tb__ "0|0|
S53S196R1P64A2S4dS4bS53R2PcA3A1S4dS4bS53R3PdA3A1S4bS160Q40A1S91R4A1S24Vrho;R4A2A3F_;F_;F_;Fj;").
Proof using Hbnc Hgd Hsc.
  intros j Hj H12 H13. unfold rw1, rw1v.
  repeat match goal with |- context [if ?c then _ else _] => let e := fresh in destruct c eqn:e; [exfalso; try apply Z.eqb_eq in e; try (apply andb_prop in e; destruct e as [e _]; apply Z.leb_le in e); lia|] end.
  reflexivity.
Qed.

Definition zr1 : positive -> Z := zr_of (rho1 (fun _ => None)).
Definition zl1 : positive -> list Z := zl_of (rho1 (fun _ => None)).

Lemma zr1_zl1_any : ltac2:(tb__ "0|1|
S160Q40A1S4S160Q8A1A1F_;S12S4bS52S14cS155S70R2A1M0A1S153G0A1R1A3S14cS6aS6bR1A3A3Fe;Fm;").
Proof using . intros m e. reflexivity. Qed.

Lemma zl1_1 : zl1 1%positive = size_classes_bytes.
Proof using Hbnc Hgd Hsc.
  unfold zl1, zl_of, rho1. cbn [rl rl1 Pos.eqb].
  rewrite map_map. rewrite <- (map_id size_classes_bytes) at 2. apply map_ext_in.
  intros b Hb. pose proof (proj1 (Forall_forall _ _) size_classes_bytes_range b Hb) as R.
  cbn beta in R. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= b < 256). lia.
Qed.
Lemma zl1_4 : zl1 4%positive = ctz_tab_bytes.
Proof using . unfold zl1, zl_of, rho1. cbn [rl rl1 Pos.eqb]. apply zl_ctz. Qed.

Lemma zr1_v : ltac2:(tb__ "0|1|
S53S52S4bS160Q40M0A1S91R2A1S161G0R1A2A3S4cS13dZ0R2A2S13fR2S13eZ2Z40A2A2A2S4bS52S6aR4A1R3A3F_;F_;Fz;Fj;").
Proof using . intros j z E Hz. unfold zr1, zr_of, rho1. cbn [rw]. rewrite E. apply u64. exact Hz. Qed.

Lemma next_prev_R : ltac2:(tb__ "0|5|
S4cS13dZ1000M0S6eS164Vs;S75A2A1M1A2S4cS13dS13cG1Z28M2A2S187VL;A1M3A2S4cS13dG0S6eS163Vs;S76A2A1M4A2S13dS13cG4G2A2G3A2A2A2A2").
Proof using HI HMI Hbnc Hgd Hhd Hsc.
  assert (K : forall q, inring q -> 4096 <= zA q /\ zA q + 40 <= topL L).
  { intros q Hq. destruct (inring_used X None U s sc m0 HI Hsc Hhd q Hq) as (am & Hu & _).
    pose proof (used_addrs X None U s HI C_U L vm HL HV HLG q am Hu) as (A1 & A2 & _). unfold zA, PGSZ, META_SIZE in *. lia. }
  destruct (K (mnext pC) ltac:(apply inring_next; exact (mem_inring MC))) as [A B].
  destruct (K (mprev pP) ltac:(apply inring_prev; exact (mem_inring MP))) as [C D]. auto.
Qed.

Lemma zr1_12 : zr1 12%positive = sc. Proof using Hbnc Hgd Hsc. apply (zr1_v 12 sc eq_refl). lia. Qed.
Lemma zr1_13 : zr1 13%positive = req.
Proof using Hbnc Hgd Hreq Hsc. apply (zr1_v 13 req eq_refl). pose proof (MallocWfArith.class_size_bounds sc ltac:(lia)). unfold IB in Hreq. lia. Qed.
Lemma zr1_170 : zr1 170%positive = bnc. Proof using Hbnc Hgd Hsc. apply (zr1_v 170 bnc eq_refl). lia. Qed.
Lemma zr1_171 : ltac2:(tb__ "0|0|
S4bS52S6aPabA1S14eVmaskv;A1A3"). Proof using . apply (zr1_v 171 (sx32 maskv) eq_refl). apply WalkArith.sx32_range. Qed.
Lemma zr1_173 : ltac2:(tb__ "0|0|
S4bS52S6aPadA1S186S184A1A3"). Proof using Hbnc Hgd Hsc. apply (zr1_v 173 _ eq_refl). cbn. lia. Qed.
Lemma zr1_174 : zr1 174%positive = gd. Proof using Hbnc Hgd Hsc. apply (zr1_v 174 gd eq_refl). lia. Qed.
Lemma zr1_152 : ltac2:(tb__ "0|0|
S4bS52S6aP98A1S6eS164Vs;S75A2A1A3").
Proof using HI HMI Hbnc Hgd Hhd Hsc. apply (zr1_v 152 _ eq_refl). pose proof next_prev_R. top_ranges. lia. Qed.
Lemma zr1_161 : ltac2:(tb__ "0|0|
S4bS52S6aPa1A1S6eS163Vs;S76A2A1A3").
Proof using HI HMI Hbnc Hgd Hhd Hsc. apply (zr1_v 161 _ eq_refl). pose proof next_prev_R. top_ranges. lia. Qed.

Lemma rw1v_member x k : ltac2:(tb__ "0|0|
S4cS13dZ0Vk;A2S13dVk;Z7A2A2S4bS6cVx;S89A3S4dS4bS52Vk;Z2A3A1F_;S4bS6cVx;S8aA3S4dS4bS52Vk;Z1A3A1F_;S4bS4S52A1S9dS148S13cS54S7eVx;A1A1Vk;A2A1A1S7cVx;Vk;A2A3F_;F_;F_;").
Proof using Hbnc Hgd Hsc.
  intros Hk HC HP. unfold rw1v.
  assert (E : Z.pos (Z.to_pos (Z.pos (mbase x) + k)) = Z.pos (mbase x) + k) by (rewrite Z2Pos.id; [reflexivity|]; destruct x; cbn; lia).
  rewrite E. destruct x; cbn [mbase] in *;
  repeat match goal with |- context [if ?c then _ else _] =>
    let e := fresh in destruct c eqn:e;
    [first [apply Z.eqb_eq in e | apply andb_prop in e; destruct e as [e e']; apply Z.leb_le in e; apply Z.leb_le in e']
    | first [apply Z.eqb_neq in e | apply Bool.andb_false_iff in e; destruct e as [e|e]; apply Z.leb_gt in e]]; try lia end;
  try reflexivity; try (f_equal; lia).
Qed.

Lemma member_val_range x k z : ltac2:(tb__ "0|0|
S4bS4S52A1S7cVx;Vk;A2SaS52Vz;A2A3S4cS13dZ0Vz;A2S13fVz;S13eZ2Z40A2A2A2F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc.
  unfold member_val. pose proof (mem_R x) as R. pose proof (mem_bits x) as B. pose proof (Hbytes x) as (Y1 & Y2 & Y3). top_ranges.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; intros E; try discriminate; injection E as <-; lia.
Qed.

Lemma zr1_member x k z : ltac2:(tb__ "0|0|
S4cS13dZ0Vk;A2S13dVk;Z7A2A2S4bS6cVx;S89A3S4dS4bS52Vk;Z2A3A1F_;S4bS6cVx;S8aA3S4dS4bS52Vk;Z1A3A1F_;S4bS4S52A1S7cVx;Vk;A2SaS52Vz;A2A3S4bS52S6aS148S13cS54S7eVx;A1A1Vk;A2A1A1Vz;A3F_;F_;F_;F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc.
  intros Hk HC HP E. apply zr1_v; [| exact (member_val_range x k z E)].
  unfold rw1. rewrite (rw1v_member x k Hk HC HP), E. reflexivity.
Qed.

Lemma ze_var : ltac2:(tb__ "0|0|
S53S4bS52S14cS6aS6bS10R1A1A3S141S6aR1A1S13eZ2Z40A2A2A3Fj;"). Proof using . reflexivity. Qed.
Lemma ze_v : ltac2:(tb__ "0|0|
S53S4bS52S14cS6aS6bS3eR1A1A3S141S6aR1A1S13eZ2Z40A2A2A3Fj;"). Proof using . reflexivity. Qed.
Lemma ze_lit : ltac2:(tb__ "0|0|
S52S4bS52S14cS6aS6bS11R1A1A3S141R1S13eZ2Z40A2A2A3Fz;"). Proof using . reflexivity. Qed.
Lemma ze_alu : ltac2:(tb__ "0|0|
S4aS12S12S4bS52S14cS6aS6bS16R3R2R1A3A3S151Z40R3S14cS6aS6bR2A3S14cS6aS6bR1A3A4A3Fy;Fx;Fop;"). Proof using . reflexivity. Qed.
Lemma ze_aluw : ltac2:(tb__ "0|2|
S4aS12S12S4bS52S14cS6aS6bS1dR3R2R1A3A3S14eS151Z20M0R3S141S14cS6aS6bR2A3S13eZ2G0A2M1A2S141S14cS6aS6bR1A3G1A2A4A1A3Fy;Fx;Fop;"). Proof using . reflexivity. Qed.
Lemma ze_mul : ltac2:(tb__ "0|0|
S12S12S4bS52S14cS6aS6bS23S46R2R1A3A3S141S144S14cS6aS6bR2A3S14cS6aS6bR1A3A2S13eZ2Z40A2A2A3Fy;Fx;"). Proof using . reflexivity. Qed.
Lemma ze_ext : ltac2:(tb__ "0|3|
S6S55S12S4bS52S14cS6aS6bS1eR3R2R1A3A3S6S52Lsg;R3S141S150S14bR2A1M0S14cS6aS6bR1A3M1A2S13eZ2M2Z40A2A2S141G1S13eG2G0A2A2X6x2A3Fx;Fw;Fsg;"). Proof using . reflexivity. Qed.
Lemma ze_lbytes : ltac2:(tb__ "0|0|
S53S12S52S4bS52S14cS6aS6bS27R3R2R1A3A3S141S154S156S14cS6aS6bR2A3R1S6bR3A1A3A1S13eZ2Z40A2A2A3Fkk;Fix;Fl;"). Proof using . reflexivity. Qed.

Definition vptr (x : member) : positive := mbase x.
Definition vmem (x : member) : positive := ltac2:(tb__ "0|0|
S148S13cS54S7eVx;A1A1Z3A2A1").
Definition vavail (x : member) : positive := ltac2:(tb__ "0|0|
S148S13cS54S7eVx;A1A1Z4A2A1").
Definition vfreed (x : member) : positive := ltac2:(tb__ "0|0|
S148S13cS54S7eVx;A1A1Z5A2A1").
Definition vbits (x : member) : positive := ltac2:(tb__ "0|0|
S148S13cS54S7eVx;A1A1Z6A2A1").
Definition vbyte (x : member) : positive := ltac2:(tb__ "0|0|
S148S13cS54S7eVx;A1A1Z7A2A1").

Lemma below_vptr x : ltac2:(tb__ "0|0|
S4bS6S16aS181S3eS80Vx;A1A1A2S1A3"). Proof using . destruct x; reflexivity. Qed.
Lemma below_vmem x : ltac2:(tb__ "0|0|
S4bS6S16aS181S3eS88Vx;A1A1A2S1A3"). Proof using . destruct x; reflexivity. Qed.
Lemma below_vavail x : ltac2:(tb__ "0|0|
S4bS6S16aS181S3eS7dVx;A1A1A2S1A3"). Proof using . destruct x; reflexivity. Qed.
Lemma below_vfreed x : ltac2:(tb__ "0|0|
S4bS6S16aS181S3eS78Vx;A1A1A2S1A3"). Proof using . destruct x; reflexivity. Qed.
Lemma below_vbits x : ltac2:(tb__ "0|0|
S4bS6S16aS181S3eS79Vx;A1A1A2S1A3"). Proof using . destruct x; reflexivity. Qed.
Lemma below_vbyte x : ltac2:(tb__ "0|0|
S4bS6S16aS181S3eS7aVx;A1A1A2S1A3"). Proof using . destruct x; reflexivity. Qed.

Lemma ze_ptr x : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS3eS80Vx;A1A1A3S6eS6fVx;A1A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc.
  unfold vptr. rewrite ze_v. replace (mbase x) with (Z.to_pos (Z.pos (mbase x) + 0)) by (destruct x; reflexivity).
  rewrite (zr1_member x 0 _ ltac:(lia) ltac:(intros; lia) ltac:(intros; lia) eq_refl). apply m64. pose proof (mem_R x). top_ranges. lia.
Qed.
Lemma ze_mem x : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS3eS88Vx;A1A1A3S6eS59S6dVx;A1A1A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. unfold vmem. rewrite ze_v, (zr1_member x 3 _ ltac:(lia) ltac:(intros; lia) ltac:(intros; lia) eq_refl). apply m64. pose proof (mem_R x). top_ranges. lia. Qed.
Lemma ze_avail x : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS3eS7dVx;A1A1A3S5bS6dVx;A1A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. unfold vavail. rewrite ze_v, (zr1_member x 4 _ ltac:(lia) ltac:(intros; lia) ltac:(intros; lia) eq_refl). apply m64. pose proof (mem_R x). lia. Qed.
Lemma ze_freed x : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS3eS78Vx;A1A1A3S57S6dVx;A1A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. unfold vfreed. rewrite ze_v, (zr1_member x 5 _ ltac:(lia) ltac:(intros; lia) ltac:(intros; lia) eq_refl). apply m64. pose proof (mem_R x). lia. Qed.
Lemma ze_bits x : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS3eS79Vx;A1A1A3S16cS6dVx;A1A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. unfold vbits. rewrite ze_v, (zr1_member x 6 _ ltac:(lia) ltac:(intros; lia) ltac:(intros; lia) eq_refl). apply m64. pose proof (mem_bits x). lia. Qed.
Lemma ze_byte x : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS3eS7aVx;A1A1A3S7fVx;A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. unfold vbyte. rewrite ze_v, (zr1_member x 7 _ ltac:(lia) ltac:(intros; lia) ltac:(intros; lia) eq_refl). apply m64. pose proof (Hbytes x). lia. Qed.

Lemma ze12 : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS3ePcA1A3Vsc;A3"). Proof using Hbnc Hgd Hsc. rewrite ze_v, zr1_12. apply m64. lia. Qed.
Lemma ze13 : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS3ePdA1A3Vreq;A3"). Proof using Hbnc Hgd Hreq Hsc. rewrite ze_v, zr1_13. apply m64. pose proof (MallocWfArith.class_size_bounds sc ltac:(lia)). unfold IB in Hreq. lia. Qed.
Lemma ze170 : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS3ePaaA1A3Vbnc;A3"). Proof using Hbnc Hgd Hsc. rewrite ze_v, zr1_170. apply m64. lia. Qed.
Lemma ze171 : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS3ePabA1A3S14eVmaskv;A1A3"). Proof using . rewrite ze_v, zr1_171. apply m64. apply WalkArith.sx32_range. Qed.
Lemma zr1_172 : zr1 172%positive = spanv. Proof using Hbnc Hgd Hsc Hspanv. apply (zr1_v 172 spanv eq_refl). lia. Qed.
Lemma ze172 : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS3ePacA1A3Vspanv;A3"). Proof using Hbnc Hgd Hsc Hspanv. rewrite ze_v, zr1_172. apply m64. lia. Qed.
Lemma ze173 : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS3ePadA1A3S186S184A1A3"). Proof using Hbnc Hgd Hsc. rewrite ze_v, zr1_173. reflexivity. Qed.
Lemma ze174 : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS3ePaeA1A3Vgd;A3"). Proof using Hbnc Hgd Hsc. rewrite ze_v, zr1_174. apply m64. lia. Qed.
Lemma ze152 : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS3eP98A1A3S6eS164Vs;S75A2A1A3"). Proof using HI HMI Hbnc Hgd Hhd Hsc. rewrite ze_v, zr1_152. apply m64. pose proof next_prev_R. top_ranges. lia. Qed.
Lemma ze161 : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS3ePa1A1A3S6eS163Vs;S76A2A1A3"). Proof using HI HMI Hbnc Hgd Hhd Hsc. rewrite ze_v, zr1_161. apply m64. pose proof next_prev_R. top_ranges. lia. Qed.

Definition e_sx (e : sv) : sv := SExt true 32 e.
Definition e_onesw (e : sv) : sv := ltac2:(tb__ "0|0|
S1dS3fS1dS42S11Z2A1Ve;A3S11ZffffffffffffffffA1A3").
Definition e_and (a b : sv) : sv := SAlu ALU_AND a b.
Definition e_lowbit (e : sv) : sv := ltac2:(tb__ "0|0|
S16S41Ve;S1dS45S11Z0A1Ve;A3A3").
Definition e_dbidx (e : sv) : sv := ltac2:(tb__ "0|0|
S1dS44S23S46S87Ve;A1S11Z77cb531A1A3S11Z1bA1A3").
Definition e_bncidx0 (x : member) : sv := ltac2:(tb__ "0|0|
S16S44S16S42S77S3eS79Vx;A1A1A1S11Z34A1A3S11Z3aA1A3").
Definition e_bncidx (x : member) : sv := ltac2:(tb__ "0|0|
S16S3fS8dVx;A1S11N7A1A3").

Definition e_bncoff (x : member) : sv := ltac2:(tb__ "0|0|
S16S3fS8dVx;A1S11Z371A1A3").
Definition e_actoff : sv := ltac2:(tb__ "0|0|
S16S3fS16S42S3ePcA1S11Z3A1A3S11Z58A1A3").
Definition e_acthi : sv := ltac2:(tb__ "0|0|
S16S3fS16S42S3ePcA1S11Z3A1A3S11Z60A1A3").
Definition e_tabidx (x : member) : sv := ltac2:(tb__ "0|0|
S16S41S16S44S3eS79Vx;A1A1S11Z5A1A3S11Z7eA1A3").

Lemma below_bncoff x : ltac2:(tb__ "0|0|
S4bS6S16aS181S85Vx;A1A2S1A3"). Proof using . destruct x; reflexivity. Qed.
Lemma below_bncidx x : ltac2:(tb__ "0|0|
S4bS6S16aS181S9bVx;A1A2S1A3"). Proof using . destruct x; reflexivity. Qed.
Lemma below_tabidx x : ltac2:(tb__ "0|0|
S4bS6S16aS181S8eVx;A1A2S1A3"). Proof using . destruct x; reflexivity. Qed.
Lemma zsup_bncoff x : ltac2:(tb__ "0|0|
S4bS6S14fS85Vx;A1A1S1A3"). Proof using . destruct x; reflexivity. Qed.

Lemma ze_sx_avail x : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS77S3eS7dVx;A1A1A1A3S14eS5bS6dVx;A1A1A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. unfold e_sx. rewrite ze_ext, ze_avail. reflexivity. Qed.
Lemma ze_sx_freed x : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS77S3eS78Vx;A1A1A1A3S14eS57S6dVx;A1A1A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. unfold e_sx. rewrite ze_ext, ze_freed. reflexivity. Qed.

Lemma ze_onesw_bits x : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS7bS3eS79Vx;A1A1A1A3S14eS5aS5dS6dVx;A1A1A1A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc.
  unfold e_onesw. rewrite ze_aluw, ze_aluw, !ze_lit, ze_bits. pose proof (mem_bits x) as (B & _).
  change ((2 mod 2 ^ 64) mod 2 ^ 32) with 2. change ((18446744073709551615 mod 2 ^ 64) mod 2 ^ 32) with (2 ^ 32 - 1).
  rewrite ones_w_val by lia. rewrite (proj1 (bits_mod32 x)). reflexivity.
Qed.
Lemma ze_onesw_byte x : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS7bS3eS7aVx;A1A1A1A3S14eS5aS58S6dVx;A1A1A1A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc.
  unfold e_onesw. rewrite ze_aluw, ze_aluw, !ze_lit, ze_byte. pose proof (Hbytes x) as (B & E & _).
  change ((2 mod 2 ^ 64) mod 2 ^ 32) with 2. change ((18446744073709551615 mod 2 ^ 64) mod 2 ^ 32) with (2 ^ 32 - 1).
  rewrite ones_w_val by lia. rewrite E. reflexivity.
Qed.

Lemma ze_actoff : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS8cA3S13cS144Z8Vsc;A2Z58A2A3").
Proof using Hbnc Hgd Hsc.
  unfold e_actoff. rewrite !ze_alu, ze12, !ze_lit. cbn [zalu]. change ((3 mod 2 ^ 64) mod 64) with 3.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. change (88 mod 2 ^ 64) with 88. rewrite !Z.mod_small; lia.
Qed.
Lemma ze_acthi : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS9aA3S13cS144Z8Vsc;A2Z60A2A3").
Proof using Hbnc Hgd Hsc.
  unfold e_acthi. rewrite !ze_alu, ze12, !ze_lit. cbn [zalu]. change ((3 mod 2 ^ 64) mod 64) with 3.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. change (96 mod 2 ^ 64) with 96. rewrite !Z.mod_small; lia.
Qed.

Lemma mod_mod_le a m n : ltac2:(tb__ "0|2|
S4cS13dZ0Vm;A2S13dVm;Vn;A2A2S4bS52S141S141Va;S13eZ2M0Vn;A2A2S13eG0Vm;A2M1A2S141Va;G1A2A3F_;").
Proof using Hbnc Hgd Hsc.
  intros Hmn. rewrite <- Znumtheory.Zmod_div_mod; [reflexivity| apply Z.pow_pos_nonneg; lia | apply Z.pow_pos_nonneg; lia |].
  exists (2 ^ (n - m)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma ze_bncidx0 x : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS8dVx;A1A3Vsc;A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc.
  unfold e_bncidx0, e_sx. rewrite !ze_alu, ze_ext, ze_bits, !ze_lit. cbn [zalu Z.of_N].
  pose proof (mem_bits x) as (B & Hs & ML). pose proof (mem_R x) as (_ & _ & R3 & _ & R5 & _).
  change ((52 mod 2 ^ 64) mod 64) with 52. change ((58 mod 2 ^ 64) mod 64) with 58.
  set (T := toS 32 (meta_bits (mam x)) mod 2 ^ 64).
  set (low := am_last (mam x) + 32 + 64 * sc).
  assert (Hlow : 0 <= low < 2 ^ 12) by (unfold low; lia).
  assert (LOW : T mod 2 ^ 12 = low).
  { unfold T. rewrite (mod_mod_le _ 12 64) by lia.
    rewrite <- (mod_mod_le (toS 32 (meta_bits (mam x))) 12 32) by lia. rewrite toS_mod_back by lia.
    rewrite (mod_mod_le _ 12 32) by lia.
    unfold meta_bits. rewrite Hs. fold low.
    replace (low + 4096 * am_maplen (mam x)) with (low + am_maplen (mam x) * 2 ^ 12) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (SHL : (T ≪ 52) mod 2 ^ 64 = low * 2 ^ 52).
  { rewrite Z.shiftl_mul_pow2 by lia. replace (2 ^ 64) with (2 ^ 12 * 2 ^ 52) by reflexivity.
    rewrite Z.mul_mod_distr_r by lia. rewrite LOW. reflexivity. }
  rewrite SHL. rewrite (Z.mod_small (low * 2 ^ 52)) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (low * 2 ^ 52 / 2 ^ 58) with sc.
  2:{ replace (2 ^ 58) with (2 ^ 52 * 2 ^ 6) by reflexivity. rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia.
      unfold low. change (2 ^ 6) with 64. Z.to_euclidean_division_equations; lia. }
  pose proof Hsc. lia.
Qed.

Lemma ze_bncidx x : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS9bVx;A1A3S141S146Vsc;Z7A2S13eZ2Z40A2A2A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc.
  unfold e_bncidx. rewrite ze_alu, ze_bncidx0, ze_lit. cbn [zalu]. change ((-7) mod 2 ^ 64) with (2 ^ 64 - 7).
  replace (sc + (2 ^ 64 - 7)) with ((sc - 7) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma ze_tabidx x : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS8eVx;A1A3S144Z2Vsc;A2A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc.
  unfold e_tabidx. rewrite !ze_alu, ze_bits, !ze_lit. cbn [zalu]. pose proof (mem_bits x) as (B & Hs & ML). pose proof (mem_R x) as (_ & _ & _ & _ & R5 & _).
  change ((5 mod 2 ^ 64) mod 64) with 5. change ((126 mod 2 ^ 64) mod 2 ^ 64) with 126.
  rewrite (Z.mod_small (meta_bits (mam x))) by lia.
  rewrite (proj2 (bits_mod32 x)).
  rewrite (Z.mod_small (1 + 2 * sc + 128 * am_maplen (mam x))) by lia.
  apply land_126_odd; lia.
Qed.

Lemma ze_lowbit_sx e z : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bVe;A3S14eVz;A1A3S4cS13fZ0Vz;A2S13fVz;S13eZ2Z20A2A2A2S4bS52S14cS6aS6bS87Ve;A1A3S14eS60Vz;A1A1A3F_;F_;").
Proof using Hbnc Hgd Hsc.
  intros E Hz. unfold e_lowbit. rewrite ze_alu, ze_aluw, E, !ze_lit. cbn [zalu].
  change ((0 mod 2 ^ 64) mod 2 ^ 32) with 0. rewrite sx32_mod32 by lia.
  pose proof (WalkArith.sx32_range z). pose proof (WalkArith.sx32_range ((0 - z) mod 2 ^ 32)).
  rewrite !(Z.mod_small (sx32 _) (2 ^ 64)) by lia.
  pose proof (Z.mod_pos_bound (0 - z) (2 ^ 32) ltac:(lia)) as M.
  rewrite sx32_land by lia.
  replace (0 - z) with (- z) by lia. rewrite land_neg_mod32 by lia. reflexivity.
Qed.

Lemma sx32_lowbit_nz z : ltac2:(tb__ "0|1|
S4cS13fZ0M0Vz;A2S13fVz;S13eZ2Z20A2A2A2S4dS4bS52S14eS60Vz;A1A1G0A3A1F_;").
Proof using Hbnc Hgd Hsc.
  intros Hz E. pose proof (lowbit_range z Hz) as LR.
  apply (proj1 (sx32_zero_iff (lowbit z) ltac:(lia))) in E. lia.
Qed.

Lemma ze_dbidx_sx e z : ltac2:(tb__ "0|4|
S4bS52S14cS6aS6bVe;A3S14eVz;A1A3S4cS13fZ0M0Vz;A2S13fVz;S13eZ2Z20M1A2M2A2A2S4cS4bS52S14cS6aS6bS86Ve;A1A3M3S149S141S144S60Vz;A1Z77cb531A2G2A2Z1bA2A3S4cS13dG0G3A2S13fG3G1A2A2A2F_;F_;").
Proof using Hbnc Hgd Hsc.
  intros E Hz. unfold e_dbidx. rewrite ze_aluw, ze_mul, (ze_lowbit_sx e z E Hz), !ze_lit. cbn [zalu].
  change (((27 mod 2 ^ 64) mod 2 ^ 32) mod 32) with 27. change (125613361 mod 2 ^ 64) with 125613361.
  pose proof (lowbit_range z Hz) as LR.
  rewrite (mod_mod_le _ 32 64) by lia. rewrite Z.mod_mod by lia.
  rewrite <- Z.mul_mod_idemp_l by lia. rewrite sx32_mod32 by lia.
  pose proof (dbidx_lt32 (lowbit z * 125613361)) as D.
  rewrite sx32_small by lia. split; [reflexivity | exact D].
Qed.

Hypothesis Hsp : ltac2:(tb__ "0|1|
S4cS13dZ1000S162Q40S24Vrho;PaA2A2M0A2S4bS52S141G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S4cS13dS150Z40S162Q40S24Vrho;PfA2A2A2M0S140S19aZ0A1A1A2S13dS140S13eZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S13dS187VL;A1S13cS162Q40M0S24Vrho;PaA2A2S150Z40S162G0S24Vrho;PfA2A2A2A2A2").
Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Ltac zfact := cbn [zholds zcond].

Lemma zr1_10 : ltac2:(tb__ "0|1|
S4bS52S6aPaM0A1S162Q40S24Vrho;G0A2A2A3"). Proof using . reflexivity. Qed.
Lemma zr1_15 : ltac2:(tb__ "0|1|
S4bS52S6aPfM0A1S162Q40S24Vrho;G0A2A2A3"). Proof using . reflexivity. Qed.

Lemma sp_sum : ltac2:(tb__ "0|4|
S4bS52S141S13cS162Q40M0S24Vrho;PaA2A2M1S162G0S24Vrho;PfA2A2M2A2S13eZ2Z40M3A2A2S13cG1S150G3G2A2A2A3").
Proof using Hbnc Hdepth Hgd Hsc Hsp Hsp_high.
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

Definition F_base5 : list sprop := ltac2:(tb__ "0|2|
S0S15S20PaM0Z4A2S0S15S1cS11Z7fff7f800000A1S16S3fS10G0A1S10PfA1M1A3A2S0S15S19S43S11N120A1G1A3S0S15S19S43G1S11S140S13eZ2Z28A2A1A1A3S0S15S1cS3ePcA1S11Z2fA1A2S2S15A1A3A3A3A3A3").

Theorem ZF_base5 : ltac2:(tb__ "0|0|
S159S15S14dS6aS6bA2Sa1A3").
Proof using Hbnc Hdepth Hgd Hsc Hsp Hsp_high.
  pose proof Hsp as [S1 S2]. pose proof Hdepth as [D1 D2]. pose proof Hsp_high as SH. unfold as_stack in D1.
  unfold F_base5.
  constructor. { zfact. rewrite zr1_10. split; [lia|]. rewrite (Z.mod_small _ (2 ^ 64)) by (pose proof (urange (rw rho 10%positive)); lia).
                 change (2 ^ 4) with 16. exact S2. }
  constructor. { zfact. rewrite ze_lit, ze_alu, !ze_var, zr1_10, zr1_15. cbn [zalu].
                 pose proof (urange (rw rho 10%positive)) as U10. pose proof (urange (rw rho 15%positive)) as U15.
                 rewrite !(Z.mod_small (bv_unsigned _) (2 ^ 64)) by lia. rewrite sp_sum. top_ranges.
                 change (140735332483072 mod 2 ^ 64) with 140735332483072. lia. }
  constructor. { zfact. rewrite ze_lit, ze_var, zr1_15. rewrite (toS_mod 64 (bv_unsigned (rw rho 15%positive))) by lia.
                 replace (toS 64 ((-288) mod 2 ^ 64)) with (-288) by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze_lit, ze_var, zr1_15. rewrite (toS_mod 64 (bv_unsigned (rw rho 15%positive))) by lia.
                 replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
  constructor. { zfact. rewrite ze12, ze_lit. change (47 mod 2 ^ 64) with 47. lia. }
  constructor.
Qed.

Lemma zf_ptr_ne0 x : ltac2:(tb__ "0|0|
S14dS6aS6bS1bS19S40S3eS80Vx;A1A1S11Z0A1A3A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp. zfact. rewrite ze_ptr, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. pose proof (mem_R x). lia. Qed.

Lemma zf_byte x : ltac2:(tb__ "0|0|
S14dS6aS6bS1cS3eS7aVx;A1A1S11ZffA1A2A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp. zfact. rewrite ze_byte, ze_lit. change (255 mod 2 ^ 64) with 255. pose proof (Hbytes x) as (Y1 & _). lia. Qed.

Lemma zf_align x : ltac2:(tb__ "0|0|
S14dS6aS6bS20S80Vx;A1Z3A2A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp.
  zfact. split; [lia|]. unfold vptr. pose proof (ze_ptr x) as E. rewrite ze_v in E. unfold vptr in E. rewrite E.
  change (2 ^ 3) with 8. pose proof (mem_R x). lia.
Qed.

Lemma zf_freeable x : ltac2:(tb__ "0|0|
S14dS6aS6bS1bS19S40S16S41S3eS79Vx;A1A1S11Z20A1A3S11Z0A1A3A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp.
  zfact. rewrite ze_alu, ze_bits, !ze_lit. cbn [zalu]. pose proof (mem_bits x) as (B0 & _).
  rewrite (Z.mod_small (meta_bits (mam x)) (2 ^ 64)) by lia.
  change ((32 mod 2 ^ 64) mod 2 ^ 64) with 32. change (0 mod 2 ^ 64) with 0.
  rewrite Z.eqb_eq. intros E.
  pose proof (member_freeable X None U s sc m0 HI Hsc Hhd (mptr x) (mam x) (mem_inring x) eq_refl) as B.
  assert (T : Z.testbit (Z.land (meta_bits (mam x)) 32) 5 = true).
  { rewrite Z.land_spec, B. reflexivity. }
  rewrite E in T. cbn in T. discriminate.
Qed.

Lemma zf_neq x y : ltac2:(tb__ "0|0|
S4dS4bS56S6fVx;A1S6fVy;A1A3A1S14dS6aS6bS1bS19S40S3eS80Vx;A1A1S3eS80Vy;A1A1A3A1A3F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. intros Hne. zfact. rewrite !ze_ptr. rewrite Z.eqb_eq. pose proof (mptr_addr_ne x y Hne). lia. Qed.

Lemma zf_avail_eq0 x : ltac2:(tb__ "0|1|
S4bS52S5bS6dVx;A1A1Z0M0A3S14dS6aS6bS19S40S77S3eS7dVx;A1A1A1S11G0A1A3A3F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp. intros E. zfact. rewrite ze_sx_avail, ze_lit, E. reflexivity. Qed.
Lemma zf_avail_ne0 x : ltac2:(tb__ "0|1|
S4dS4bS52S5bS6dVx;A1A1Z0M0A3A1S14dS6aS6bS1bS19S40S77S3eS7dVx;A1A1A1S11G0A1A3A1A3F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp.
  intros E. zfact. rewrite ze_sx_avail, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. intros Z0.
  apply E. pose proof (mem_R x) as (R1 & _). apply (proj1 (sx32_zero_iff (am_avail (mam x)) ltac:(lia))). exact Z0.
Qed.
Lemma zf_freed_eq0 x : ltac2:(tb__ "0|1|
S4bS52S57S6dVx;A1A1Z0M0A3S14dS6aS6bS19S40S77S3eS78Vx;A1A1A1S11G0A1A3A3F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp. intros E. zfact. rewrite ze_sx_freed, ze_lit, E. reflexivity. Qed.
Lemma zf_freed_ne0 x : ltac2:(tb__ "0|1|
S4dS4bS52S57S6dVx;A1A1Z0M0A3A1S14dS6aS6bS1bS19S40S77S3eS78Vx;A1A1A1S11G0A1A3A1A3F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp.
  intros E. zfact. rewrite ze_sx_freed, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. intros Z0.
  apply E. pose proof (mem_R x) as (_ & R2 & _). apply (proj1 (sx32_zero_iff (am_freed (mam x)) ltac:(lia))). exact Z0.
Qed.
Lemma zf_avail_le0 x : ltac2:(tb__ "0|1|
S4bS52S5bS6dVx;A1A1Z0M0A3S14dS6aS6bS1cS3eS7dVx;A1A1S11G0A1A2A3F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp. intros E. zfact. rewrite ze_avail, ze_lit, E. reflexivity. Qed.

Lemma zf_all_eq x : ltac2:(tb__ "0|1|
S4bS52S57S6dVx;A1M0A1S5aS5dG0A1A1A3S14dS6aS6bS19S40S77S3eS78Vx;A1A1A1S7bS3eS79Vx;A1A1A1A3A3F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp. intros E. zfact. rewrite ze_sx_freed, ze_onesw_bits, E. apply Z.eqb_refl. Qed.
Lemma zf_all_ne x : ltac2:(tb__ "0|1|
S4dS4bS52S57S6dVx;A1M0A1S5aS5dG0A1A1A3A1S14dS6aS6bS19S47S77S3eS78Vx;A1A1A1S7bS3eS79Vx;A1A1A1A3A3F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp.
  intros E. zfact. rewrite ze_sx_freed, ze_onesw_bits. apply Bool.negb_true_iff. apply Z.eqb_neq. intros EQ. apply E.
  pose proof (mem_R x) as (_ & R2 & R3 & _). pose proof (ones_u32 (am_last (mam x)) ltac:(lia)).
  exact (ZBits.sx32_inj (am_freed (mam x)) (ones (am_last (mam x))) ltac:(lia) ltac:(lia) EQ).
Qed.

Lemma land_act_freed x : ltac2:(tb__ "0|3|
S4bS52S145S14eS5aS58S6dVx;A1M0A1A1M1A1S14eS57G0A1M2A1A2S14eS145G2G1A2A1A3").
Proof using HI HMI Hbnc Hgd Hhd Hsc Hsp.
  pose proof (mem_R x) as (_ & R2 & R3 & R4 & _). pose proof (ones_u32 (am_aidx (mam x)) ltac:(lia)).
  rewrite sx32_land by lia. rewrite Z.land_comm. reflexivity.
Qed.
Lemma land_freed_act x : ltac2:(tb__ "0|3|
S4bS52S145S14eS57S6dVx;A1M0A1M1A1S14eS5aS58G0A1A1M2A1A2S14eS145G1G2A2A1A3").
Proof using HI HMI Hbnc Hgd Hhd Hsc Hsp.
  pose proof (mem_R x) as (_ & R2 & R3 & R4 & _). pose proof (ones_u32 (am_aidx (mam x)) ltac:(lia)).
  rewrite sx32_land by lia. reflexivity.
Qed.
Lemma land_fa_range x : ltac2:(tb__ "0|2|
S4cS13dZ0S145S57S6dVx;A1M0A1S5aS58G0A1A1A2M1A2S13fG1S13eZ2Z20A2A2A2").
Proof using HI HMI Hbnc Hgd Hhd Hsc Hsp.
  pose proof (mem_R x) as (_ & R2 & R3 & R4 & _). pose proof (ones_u32 (am_aidx (mam x)) ltac:(lia)).
  split; [apply Z.land_nonneg; lia|].
  pose proof (land_le_l (am_freed (mam x)) (ones (am_aidx (mam x))) ltac:(lia)). lia.
Qed.

Lemma zf_act_ne0_a x : ltac2:(tb__ "0|2|
S4dS4bS52S145S57S6dVx;A1M0A1S5aS58G0A1A1A2Z0M1A3A1S14dS6aS6bS1bS19S40S84S7bS3eS7aVx;A1A1A1S77S3eS78Vx;A1A1A1A2S11G1A1A3A1A3F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp.
  intros E. zfact. unfold e_and. rewrite ze_alu, ze_onesw_byte, ze_sx_freed, ze_lit. cbn [zalu]. rewrite !(Z.mod_small (sx32 _) (2 ^ 64)) by apply WalkArith.sx32_range. rewrite land_act_freed.
  change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. intros Z0. apply E. apply (proj1 (sx32_zero_iff _ (land_fa_range x))). exact Z0.
Qed.
Lemma zf_act_ne0_b x : ltac2:(tb__ "0|2|
S4dS4bS52S145S57S6dVx;A1M0A1S5aS58G0A1A1A2Z0M1A3A1S14dS6aS6bS1bS19S40S84S77S3eS78Vx;A1A1A1S7bS3eS7aVx;A1A1A1A2S11G1A1A3A1A3F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp.
  intros E. zfact. unfold e_and. rewrite ze_alu, ze_onesw_byte, ze_sx_freed, ze_lit. cbn [zalu]. rewrite !(Z.mod_small (sx32 _) (2 ^ 64)) by apply WalkArith.sx32_range. rewrite land_freed_act.
  change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. intros Z0. apply E. apply (proj1 (sx32_zero_iff _ (land_fa_range x))). exact Z0.
Qed.
Lemma zf_act_eq0_a x : ltac2:(tb__ "0|2|
S4bS52S145S57S6dVx;A1M0A1S5aS58G0A1A1A2Z0M1A3S14dS6aS6bS19S40S84S7bS3eS7aVx;A1A1A1S77S3eS78Vx;A1A1A1A2S11G1A1A3A3F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp.
  intros E. zfact. unfold e_and. rewrite ze_alu, ze_onesw_byte, ze_sx_freed, ze_lit. cbn [zalu]. rewrite !(Z.mod_small (sx32 _) (2 ^ 64)) by apply WalkArith.sx32_range. rewrite land_act_freed, E. reflexivity.
Qed.
Lemma zf_act_eq0_b x : ltac2:(tb__ "0|2|
S4bS52S145S57S6dVx;A1M0A1S5aS58G0A1A1A2Z0M1A3S14dS6aS6bS19S40S84S77S3eS78Vx;A1A1A1S7bS3eS7aVx;A1A1A1A2S11G1A1A3A3F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp.
  intros E. zfact. unfold e_and. rewrite ze_alu, ze_onesw_byte, ze_sx_freed, ze_lit. cbn [zalu]. rewrite !(Z.mod_small (sx32 _) (2 ^ 64)) by apply WalkArith.sx32_range. rewrite land_freed_act, E. reflexivity.
Qed.

Lemma zf_tabidx x : ltac2:(tb__ "0|0|
S14dS6aS6bS1cS8eVx;A1S11Z5eA1A2A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. zfact. rewrite ze_tabidx, ze_lit. change (94 mod 2 ^ 64) with 94. lia. Qed.

Lemma zf_hit x : ltac2:(tb__ "0|3|
S4dS4bS52S5bS6dVx;A1A1Z0M0A3A1S159S15S14dS6aS6bA2S0S15S1bS19S40S77S3eS7dVx;A1A1A1M1S11G0A1M2A3A1S0S15S1bS19S40S87G1A1G2A3A1S0S15S1cS86G1A1S11Z1fA1A2S2S15A1A3A3A3A3F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp.
  intros Hav. pose proof (mem_R x) as (R1 & _).
  pose proof (ze_lowbit_sx (e_sx (v (vavail x))) (am_avail (mam x)) (ze_sx_avail x) ltac:(lia)) as LB.
  constructor; [apply zf_avail_ne0; exact Hav|].
  constructor. { zfact. rewrite LB, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. apply sx32_lowbit_nz. lia. }
  constructor. { zfact. destruct (ze_dbidx_sx _ _ (ze_sx_avail x) ltac:(lia)) as [_ D]. rewrite ze_lit. change (31 mod 2 ^ 64) with 31. lia. }
  constructor.
Qed.

Definition F_T : list sprop := ltac2:(tb__ "0|2|
S0S15S1bS19S40S3ePabA1M0S11Z0A1M1A3A1S0S15S1bS19S40S87G0A1G1A3A1S0S15S1cS86G0A1S11Z1fA1A2S0S15S1cS3ePaaA1S11ZffA1A2S2S15A1A3A3A3A3").

Theorem ZF_T : ltac2:(tb__ "0|0|
S159S15S14dS6aS6bA2Sa0A3").
Proof using Hbnc Hgd Hmaskv Hsc Hsp.
  pose proof (ze_lowbit_sx (v 171) maskv ze171 Hmaskv) as LB.
  unfold F_T.
  constructor. { zfact. rewrite ze171, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. intros E. apply (proj1 (sx32_zero_iff maskv ltac:(lia))) in E. lia. }
  constructor. { zfact. rewrite LB, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite Z.eqb_eq. apply sx32_lowbit_nz. lia. }
  constructor. { zfact. destruct (ze_dbidx_sx _ _ ze171 Hmaskv) as [_ D]. rewrite ze_lit. change (31 mod 2 ^ 64) with 31. lia. }
  constructor. { zfact. rewrite ze170, ze_lit. change (255 mod 2 ^ 64) with 255. lia. }
  constructor.
Qed.

Theorem facts_hold : ltac2:(tb__ "0|0|
S160Q40A1S4S160Q8A1A1F_;S3S15A1S4bS6S18eS15S152R1A3S1A3S159S15S14dS6aS6bA2R2A3S159S15S31S70R4A1A1R3A3F_;F_;FF;Fm;").
Proof using . drop_sp.
  intros m F HS HF. apply Forall_holds_of_zholds; [exact HS|].
  apply Forall_forall. intros p Hp. apply (zholds_ext zr1 (zr_of (rho1 m)) zl1 (zl_of (rho1 m))).
  - intros j. reflexivity.
  - intros l. reflexivity.
  - exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S4bS160Q40A1S4S160Q8A1A1F_;Vrd0;S166S15dVmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S4bS160Q40A1S6F_;Vwok0;S167S15dVmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.

Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S52S4cS13dZ0R1A2S13fR1Z60A2A2S4bS4S160Q8A1M0A1VmW;S161Q40S13cZ108ecR2A2A2A1S9G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S52S4cS13dZ0R1A2S13fR1Z20A2A2S4bS4S160Q8A1M0A1VmW;S161Q40S13cZ108ccR2A2A2A1S9G0A1A3F_;Fkk;").

Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S6cS4bS4S160Q8M0A1M1A1S166S15dVmW;S161Q40S13cS6eS59S6dR1A1A1A1Z8A2A2A3SaG1S161G0S7fR1A1A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S4bS4S160Q8M0A1M1A1S166S15dVmW;S161Q40S13cS13cZ5a3d0Z369A2Vsc;A2A2A3SaG1S161G0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S189S185Vrd0;S160Q40A1S1L_;A2S186S184A1U8Vgd;A4").

Let bv0 : byteview := ltac2:(tb__ "0|0|
S185S166S15dVmW;A2S167S15dVmW;A2A2").

Lemma HMI0 : ltac2:(tb__ "0|0|
S194S184VX;S9S8S56S52A2A1VU;S193Vs;VL;A2S166S15dVmW;A2S167S15dVmW;A2Vvm;A8").
Proof using Erd Ewok HMI. drop_sp. rewrite <- Erd, <- Ewok. exact HMI. Qed.
Lemma HreprO : ltac2:(tb__ "0|0|
S19bVL;Vs;Vbv0;A3"). Proof using Erd Ewok HMI. exact (mig_reprO HMI0). Qed.
Lemma Hstat : ltac2:(tb__ "0|0|
S18bS184S185S166S15dVmW;A2S160Q40A1S1L_;A2Vbv0;A3").
Proof using Erd Ewok HMI. drop_sp. exact (mig_statics HMI0). Qed.

Lemma cell_bytes0 : ltac2:(tb__ "0|4|
S16bS52S18dS16bR2S16dVs;A1A3S4bS4S52A1S190VL;R3A2SaS52R2A2A3SbS183R1S16eR5A1A2S4cS4cS13dZ0S13cS171VL;S172R6A1A2S147R2A1A2M0A2S13fG0S13eZ2Z40A2A2A2S4cS4bS6S167S15dVmW;S161Q40G0A2M1A3S1A3S4bS4S160Q8M2A1M3A1S166S15dVmW;G1A3SaG3S161G2S17cR5S16eR6A1R2A3A2A2A3A2A2F_;Fj;F_;F_;Fz;Fc;").
Proof using Erd Ewok HMI. drop_sp.
  intros c z Hc Hz j Hj.
  assert (CH : MallocInv.cell_holds L bv0 c) by exact (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 HreprO))) c Hc).
  exact (cell_bytes L _ _ c z CH Hz j Hj).
Qed.

Lemma cell_rw0 : ltac2:(tb__ "0|3|
S16bS52S52S52SbS18dS16bR5S16dVs;A1A3S4bS4S52A1S190VL;R6A2SaS52R5A2A3S4bSbS16eR7A1R3A3S4bS52S171VL;S172R8A1A2S13cR6R5A2A3S52S4cS13dS13cR8R7A2M0R1A2S13fR1S13cG0S147R6A1A2A2A2S4cS4bS6S167S15dVmW;S161Q40M1R2A2A3S1A3S4fS160Q8A1M2G2S4bS4G2A1S166S15dVmW;S161G1R3A2A3SaG2R1A2A3Lbb;A2A2F_;Fx;F_;F_;F_;F_;Fkk;Foffs;Fb;Fz;Fc;").
Proof using Erd Ewok HMI Hbnc Hgd Hsc Hsp.
  intros c z b offs kk Hc Hz Hw Ha x Hx.
  destruct (cell_bytes0 c z Hc Hz (Z.to_nat (x - (b + offs))) ltac:(rewrite Hw; lia)) as (_ & W & R).
  rewrite Ha in W, R. rewrite Z2Nat.id in W, R by lia. replace (b + offs + (x - (b + offs))) with x in W, R by lia.
  split; [exact W | eexists; exact R].
Qed.

Lemma ev1 : ltac2:(tb__ "0|2|
S160Q40M0A1M1S4S160Q8A1A1F_;S12S4bS6S14fR1A1S1A3S4bG1S26S70R3A1R2A2S161G0S14cS6aS6bR2A3A2A3F_;Fe;Fm;").
Proof using . drop_sp.
  intros m e He. rewrite <- (zr1_zl1_any m). rewrite <- (eval_zeval (rho1 m) e He). symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma ev1u : ltac2:(tb__ "0|1|
S160Q40M0A1S4S160Q8A1A1F_;S12S4bS6S14fR1A1S1A3S4bS52S162G0S26S70R3A1R2A2A2S14cS6aS6bR2A3A3F_;Fe;Fm;").
Proof using . drop_sp. intros m e He. rewrite <- (zr1_zl1_any m). apply eval_zeval. exact He. Qed.

Lemma cell_view0 : ltac2:(tb__ "0|4|
S16bS52S52S52SbS12S18dS16bR6S16dVs;A1A3S4bS4S52A1S190VL;R7A2SaS52R6A2A3S4bSbS16eR8A1R4A3S182R5U8A2S4bS52S171VL;S172RaA1A2S13cR8R7A2A3S4bS160Q40M0A1S26S70VmW;A1M1R6A2S161G0RaA2A3SbS183R1R9A2S4bS4S160Q8M2A1M3A1S166S15dVmW;S161G0S13cS13cRcRbA2S147R2A1A2A2A3SaG3S158G3R2S30RaS26G1R9A2A2S161G2Z0A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;Fe;Fkk;Foffs;Fb;Fz;Fc;").
Proof using Erd Ewok HMI. drop_sp.
  intros c z b offs kk e Hc Hz Hw Hk Ha He j Hj.
  destruct (cell_bytes0 c z Hc Hz j ltac:(rewrite Hw; exact Hj)) as (_ & _ & R).
  rewrite Ha in R. rewrite R, He, Hw. rewrite nth_enc_bytes by assumption. reflexivity.
Qed.

Lemma owned_rw : ltac2:(tb__ "0|2|
S52S170VL;Vs;R1A3S4cS4bS6S167S15dVmW;S161Q40M0R2A2A3S1A3S4fS160Q8A1M1G1S4bS4G1A1S166S15dVmW;S161G0R3A2A3SaG1R1A2A3Lbb;A2A2F_;Fx;").
Proof using Erd Ewok HMI. drop_sp.
  intros x OW. pose proof (proj2 (proj2 (proj1 HreprO)) x OW) as M. unfold bv0 in M.
  destruct (byteview_of (Glue.rd_of segsU mW) (Glue.wok_of segsU mW) x) as [vv|] eqn:E; [|exfalso; exact (M eq_refl)].
  destruct (byteview_of_Some _ _ _ _ E) as (_ & W & bb & Hb & _). split; [exact W | exists bb; exact Hb].
Qed.

Lemma soff_of_ev : ltac2:(tb__ "0|0|
S12S52S4bS6S14fR2A1S1A3S4bS52S14cS6aS6bR3A3R2A3S4cS13dZ0R3A2S13fR3S13eZ2Z3fA2A2A2S4bS52S2dS70VmW;A1R5A2R4A3F_;F_;F_;Fz;Fe;").
Proof using Hbnc Hgd Hsc. drop_sp.
  intros e z Hs Hz Hr. unfold soff. rewrite (ev1 mW e Hs), Hz. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64.
  rewrite u64 by lia. unfold toS. rewrite Z.mod_small by lia. change (2 ^ (64 - 1)) with (2 ^ 63).
  replace (z <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.

Definition O_stk : sobj := ltac2:(tb__ "0|0|
S18S10PaA1S10PfA1S11Z0A1S2S13A1S1aA5").
Definition O_got : sobj := ltac2:(tb__ "0|2|
S18S11Z28d50A1S11Z0A1M0S11Z8M1A1S0S13S14G0G1S3ePadA1A3S2S13A1A3S1aA5").
Definition O_guard : sobj := ltac2:(tb__ "0|2|
S18S3ePadA1S11Z0A1M0S11Z8M1A1S0S13S14G0G1S3ePaeA1A3S2S13A1A3S1aA5").

Definition O_act (hv : sv) : sobj := ltac2:(tb__ "0|0|
S18S11Z5a3c8A1S8cS9aS0S13S14S8cZ8Vhv;A3S2S13A1A3S1aA5").
Definition O_meta (x : member) (pv nv mv av fv bv : sv) : sobj := ltac2:(tb__ "0|3|
S18S3eS80Vx;A1A1S11Z0A1M0S11Z28A1S0S13S14G0Z8M1Vpv;A3S0S13S14S11G1A1G1Vnv;A3S0S13S14S11Z10A1G1Vmv;A3S0S13S14S11Z18A1Z4M2Vav;A3S0S13S14S11Z1cA1G2Vfv;A3S0S13S14S11Z20A1G1Vbv;A3S2S13A1A3A3A3A3A3A3S1aA5").
Definition O_mem (x : member) (yv : sv) : sobj := ltac2:(tb__ "0|1|
S18S3eS88Vx;A1A1S11Z8A1M0S11Z9A1S0S13S14G0Z1Vyv;A3S2S13A1A3S1aA5").
Definition O_sct : sobj := ltac2:(tb__ "0|0|
S18S11Z108ecA1S11Z0A1S11Z60A1S2S13A1S1fP1A1A5").
Definition O_ctz : sobj := ltac2:(tb__ "0|0|
S18S11Z108ccA1S11Z0A1S11Z20A1S2S13A1S1fP4A1A5").
Definition O_bnc (x : member) (yv : sv) : sobj := ltac2:(tb__ "0|2|
S18S11Z5a3c8A1S85Vx;A1M0S16S3fG0S11Z1M1A1A3S0S13S14G0G1Vyv;A3S2S13A1A3S1aA5").

Definition optrZ (o : option sptr) : Z := match o with Some p => zA p | None => 0 end.

Lemma rv_byte a vv : ltac2:(tb__ "0|3|
S4bS4S52A1S185S166S15dVmW;A2S160Q40M0A1S1L_;Va;A3SaS52Vvv;A2A3S4bS4S160Q8M1A1M2A1S166S15dVmW;S161G0Va;A2A3SaG2S161G1Vvv;A2A2A3F_;").
Proof using . drop_sp.
  intros H. destruct (byteview_of_Some _ _ _ _ H) as (_ & _ & b & Hb & E). rewrite Hb. f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite <- E. reflexivity.
Qed.

Lemma wseg_range lo (n : nat) a : ltac2:(tb__ "0|1|
S4bS6S18eS52S52S168S15dS161Q40M0R1A2A2Lx;S157SbS52SbS13cVlo;S147R1A1A2Lk;S15aU0Vn;A2A4A3S1A3S4cS13dVlo;Va;A2S13fVa;S13cVlo;S147Vn;A1A2A2A2S4bS6S167S15dVmW;S161G0Va;A2A3S1A3F_;F_;").
Proof using . drop_sp.
  intros H Ha. unfold Glue.wok_of. destruct (mW (Z_to_bv 64 a)); [reflexivity|].
  exact (forall_range_dec _ lo n H a Ha).
Qed.

Lemma got_wseg : ltac2:(tb__ "0|0|
S4bS6S18eS52S52S168S15dS161Q40R1A2A2Lx;S157SbS52SbS13cZ28d50S147R1A1A2Lk;S15aU0U8A2A4A3S1A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma guard_wseg : ltac2:(tb__ "0|0|
S4bS6S18eS52S52S168S15dS161Q40R1A2A2Lx;S157SbS52SbS13cZ5a338S147R1A1A2Lk;S15aU0U8A2A4A3S1A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma hold_got : ltac2:(tb__ "0|0|
S25S15dS70VmW;A1S169Vms;VmW;A2S95A4").
Proof using Erd Ewok HMI Hbnc Hgd Hrom Hsc Hsp.
  change O_got with (carved (SLit 0x28d50) 0 8 [(0, 8%nat, v 173)]).
  assert (B : bv_unsigned (eval (rho1 mW) (SLit 0x28d50)) = 0x28d50) by (cbn [eval]; apply u64; lia).
  destruct Hstat as (_ & _ & _ & _ & _ & _ & _ & _ & (gd' & T9 & T10)).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. split; [apply (wseg_range 0x28d50 8); [apply got_wseg | cbn; lia]|].
    pose proof (T9 (Z.to_nat o) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. cbn [mc_chk_guard_got C_U] in E.
    eexists. exact (rv_byte _ _ E).
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    pose proof (T9 j Hj) as E. cbn [mc_chk_guard_got C_U] in E. rewrite (rv_byte _ _ E).
    rewrite (ev1 mW (v 173) eq_refl), ze173, nth_enc_bytes by lia. reflexivity.
Qed.

Lemma hold_guard : ltac2:(tb__ "0|0|
S25S15dS70VmW;A1S169Vms;VmW;A2S96A4").
Proof using Erd Hbnc Hgd Hgd_holds Hrom Hsc Hsp.
  change O_guard with (carved (v 173) 0 8 [(0, 8%nat, v 174)]).
  assert (B : bv_unsigned (eval (rho1 mW) (v 173)) = 0x5a338) by (rewrite ev1u by reflexivity; rewrite ze173; reflexivity).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. split; [apply (wseg_range 0x5a338 8); [apply guard_wseg | cbn; lia]|].
    pose proof (Hgd_holds (Z.to_nat o) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. rewrite Erd in E. cbn [mc_chk_guard C_U] in E.
    eexists. exact (rv_byte _ _ E).
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    pose proof (Hgd_holds j Hj) as E. rewrite Erd in E. cbn [mc_chk_guard C_U] in E. rewrite (rv_byte _ _ E).
    rewrite (ev1 mW (v 174) eq_refl), ze174, nth_enc_bytes by lia. reflexivity.
Qed.

Lemma sctab_image : ltac2:(tb__ "0|3|
S52S4cS13dZ0M0R1A2S13fR1Z60A2A2S4bS4S160Q8M1A1M2A1S2aS15dS161Q40S13cZ108ecR2A2A2A2SaG2S158G2S14aR2A1S29S70VmW;A1P1A2S161G1G0A2A4A2A3F_;Fkk;").
Proof using Hbnc Hgd Hsc. drop_sp.
  intros kk Hk.
  pose proof (forall_range_dec (fun kk => match image_byte segsU (Z_to_bv 64 (0x108ec + kk)) with
                                         | Some b => bv_eqb b (nth (Z.to_nat kk) (map (Z_to_bv 8) size_classes_bytes) (Z_to_bv 8 0))
                                         | None => false end) 0 96 ltac:(vm_compute; reflexivity) kk ltac:(lia)) as H.
  cbn beta in H. cbn [rl rho1 rl1 Pos.eqb].
  destruct (image_byte segsU (Z_to_bv 64 (67820 + kk))) as [b|]; [|discriminate].
  f_equal. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Lemma ctztab_image : ltac2:(tb__ "0|3|
S52S4cS13dZ0M0R1A2S13fR1Z20A2A2S4bS4S160Q8M1A1M2A1S2aS15dS161Q40S13cZ108ccR2A2A2A2SaG2S158G2S14aR2A1S29S70VmW;A1P4A2S161G1G0A2A4A2A3F_;Fkk;").
Proof using Hbnc Hgd Hsc. drop_sp.
  intros kk Hk.
  pose proof (forall_range_dec (fun kk => match image_byte segsU (Z_to_bv 64 (0x108cc + kk)) with
                                         | Some b => bv_eqb b (nth (Z.to_nat kk) (map (Z_to_bv 8) ctz_tab_bytes) (Z_to_bv 8 0))
                                         | None => false end) 0 32 ltac:(vm_compute; reflexivity) kk ltac:(lia)) as H.
  cbn beta in H. cbn [rl rho1 rl1 Pos.eqb].
  destruct (image_byte segsU (Z_to_bv 64 (67788 + kk))) as [b|]; [|discriminate].
  f_equal. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Lemma hold_sct : ltac2:(tb__ "0|0|
S25S15dS70VmW;A1S169Vms;VmW;A2S99A4").
Proof using Hbnc Hgd Hm_sct Hrom Hsc. drop_sp.
  unfold O_sct. apply obj_holds_frame_rom; try exact Hrom; try lia.
  - reflexivity.
  - intros kk Hk. split; [apply Hm_sct; exact Hk | apply sctab_image; exact Hk].
Qed.
Lemma hold_ctz : ltac2:(tb__ "0|0|
S25S15dS70VmW;A1S169Vms;VmW;A2S94A4").
Proof using Hbnc Hgd Hm_ctz Hrom Hsc. drop_sp.
  unfold O_ctz. apply obj_holds_frame_rom; try exact Hrom; try lia.
  - reflexivity.
  - intros kk Hk. split; [apply Hm_ctz; exact Hk | apply ctztab_image; exact Hk].
Qed.

Lemma Cact : ltac2:(tb__ "0|0|
S18dS16bS178S177S13cS175S144Z8Vsc;A2A2A1U8S179Vm0;A1A3S16dVs;A1A3").
Proof using Hbnc Hgd Hhd Hsc Hsp.
  unfold image. apply in_app_iff. left. unfold ctx_cells.
  apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (Z.to_nat sc).
  rewrite Z2Nat.id by lia. split; [| apply in_seq; lia].
  unfold active_hd in Hhd. rewrite Hhd. reflexivity.
Qed.

Lemma hold_act hv : ltac2:(tb__ "0|0|
S4bS6S14fVhv;A1S1A3S4bS52S14cS6aS6bVhv;A3S6eVm0;A1A3S25S15dS70VmW;A1S169Vms;VmW;A2S92Vhv;A1A4F_;F_;").
Proof using Erd Ewok HMI Hbnc Hgd Hhd Hrom Hsc Hsp.
  intros Shv Ehv. pose proof Hctx as HCX.
  assert (B : bv_unsigned (eval (rho1 mW) (SLit 0x5a3c8)) = 0x5a3c8) by (cbn [eval]; apply u64; lia).
  assert (AD : loc_addr L (mc_loc (MCell (LCtx (CTX_active + 8 * sc)) 8 (VP m0))) = 0x5a3c8 + (8 * sc + 88)).
  { cbn [mc_loc loc_addr]. rewrite HCX. unfold CTX_active. lia. }
  apply (obj_holds_sem segsU (rho1 mW) (with_mem ms mW) (carved (SLit 0x5a3c8) (8 * sc + 88) (8 * sc + 96) [(8 * sc + 88, 8%nat, hv)])).
  - reflexivity.
  - cbn [ob_lo carved O_act]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_actoff | lia].
  - cbn [ob_hi carved O_act]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_acthi | lia].
  - reflexivity.
  - cbn [ob_cells carved O_act map]. constructor; [|constructor].
    split; [|split; reflexivity]. cbn [c_off]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_actoff | lia].
  - apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    + cells_inside_tac.
    + intros o Ho. apply (cell_rw0 _ (zA m0) 0x5a3c8 (8 * sc + 88) 8 Cact eq_refl eq_refl AD). lia.
    + unfold cells_in_view. constructor; [|constructor]. intros j Hj.
      apply (cell_view0 _ (zA m0) 0x5a3c8 (8 * sc + 88) 8 hv Cact eq_refl eq_refl ltac:(lia) AD); [|exact Hj].
      rewrite (ev1 mW) by exact Shv. rewrite Ehv. reflexivity.
Qed.

Lemma ze_bncoff x : ltac2:(tb__ "0|0|
S4bS52S14cS6aS6bS85Vx;A1A3S13cZ371Vsc;A2A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp.
  unfold e_bncoff. rewrite ze_alu, ze_bncidx0, ze_lit. cbn [zalu]. change (881 mod 2 ^ 64) with 881.
  pose proof Hsc. rewrite Z.mod_small; lia.
Qed.

Lemma ctx_owned off : ltac2:(tb__ "0|0|
S4cS13dZ0Voff;A2S13fVoff;S174A2A2S170VL;Vs;S13cS17dVL;A1Voff;A2A3F_;").
Proof using HI HMI HXr Hbnc Hgd Hsc Hsp.
  intros Ho. split.
  - exists (LCtx 0, CTX_SIZE). split; [left; reflexivity|]. cbn [fst snd loc_addr]. lia.
  - intros (b & Hb & Hx). cbn [fst snd] in Hx.
    destruct (user_block_in_group X None U s L HI HXr b Hb) as (g & am & i & fr & Hg & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
    destruct (group_range X None U s L HI HL C_U vm g am Hg HV HLG) as (_ & _ & _ & D).
    pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hg)) as Sp. assert (0 <= stride_of am * i) by nia.
    rewrite Eb in Hx, B1, B2. cbn [fst snd] in Hx, B1, B2. unfold addr_of in *. unfold UNIT, IB, CTX_SIZE in *. lia.
Qed.

Lemma hold_bnc x yv : ltac2:(tb__ "0|0|
S4bS6S14fVyv;A1S1A3S4bS52S14cS6aS6bVyv;A3Vbnc;A3S25S15dS70VmW;A1S169Vms;VmW;A2S93Vx;Vyv;A2A4F_;F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbytes Hgd Hhd Hrom Hsc Hsp.
  intros Syv Eyv. pose proof Hctx as HCX.
  assert (B : bv_unsigned (eval (rho1 mW) (SLit 0x5a3c8)) = 0x5a3c8) by (cbn [eval]; apply u64; lia).
  apply (obj_holds_sem segsU (rho1 mW) (with_mem ms mW) (carved (SLit 0x5a3c8) (881 + sc) (882 + sc) [(881 + sc, 1%nat, yv)])).
  - reflexivity.
  - cbn [ob_lo carved O_bnc]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_bncoff | lia].
  - cbn [ob_hi carved O_bnc]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | | lia].
    rewrite ze_alu, ze_bncoff, ze_lit. cbn [zalu]. change (1 mod 2 ^ 64) with 1. rewrite Z.mod_small; lia.
  - reflexivity.
  - cbn [ob_cells carved O_bnc map]. constructor; [|constructor].
    split; [|split; reflexivity]. cbn [c_off]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_bncoff | lia].
  - apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    + cells_inside_tac.
    + intros o Ho. replace (0x5a3c8 + o) with (ly_ctx L + (873 + sc)) by (rewrite HCX; lia). apply owned_rw. apply ctx_owned. unfold CTX_SIZE. lia.
    + unfold cells_in_view. constructor; [|constructor]. intros j Hj. replace j with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
      replace (369608 + (881 + sc)) with (0x5a3d0 + 873 + sc) by lia. rewrite Hbnc_rd.
      rewrite (ev1 mW yv Syv), Eyv, nth_enc_bytes by lia.
      unfold le_byte. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.mod_mod, (Z.mod_small bnc 256) by lia. reflexivity.
Qed.

Lemma meta_cell_In x c : ltac2:(tb__ "0|0|
S18dS16bVc;S17eS6fVx;A1SaS5fS61S6dVx;A1A1A2A2A3S18dS16bVc;S16dVs;A1A3F_;").
Proof using HI Hhd Hsc. drop_sp.
  intros Hc. destruct (mam_used x) as (_ & _ & M). apply (meta_cells_in_imageI X None U s HI (mptr x) c (mptr_key x)). rewrite M. exact Hc.
Qed.

Lemma hold_meta x (pv nv mv av fv bv : sv) : ltac2:(tb__ "0|3|
S4bS6S14fVpv;A1S1A3S4bS6S14fVnv;A1S1A3S4bS6S14fVmv;A1S1A3S4bS6S14fVav;A1S1A3S4bS6S14fVfv;A1S1A3S4bS6S14fVbv;A1S1A3S4bS52S14cS6aS6bVpv;A3S6eS163Vs;S6fVx;A1M0A2A1A3S4bS52S14cS6aS6bVnv;A3S6eS164Vs;G0A2A1A3S4bS52S14cS6aS6bVmv;A3S6eS59S6dVx;A1M1A1A1A3S4bS52S141S14cS6aS6bVav;A3S13eZ2Z20A2M2A2S5bG1A1A3S4bS52S141S14cS6aS6bVfv;A3G2A2S57G1A1A3S4bS52S14cS6aS6bVbv;A3S16cG1A1A3S25S15dS70VmW;A1S169Vms;VmW;A2S98Vx;Vpv;Vnv;Vmv;Vav;Vfv;Vbv;A7A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using Erd Ewok HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hreq Hrom Hsc Hsp Hspanv.
  intros Spv Snv Smv Sav Sfv Sbv Epv Env Emv Eav Efv Ebv. pose proof (mem_R x) as R. pose proof (mem_bits x) as (BB & _). top_ranges.
  destruct (mprev_used x) as (p & Hp & Ep). destruct (mnext_used x) as (n & Hn & En).
  change (O_meta x pv nv mv av fv bv) with (carved (v (vptr x)) 0 40 [(0, 8%nat, pv); (8, 8%nat, nv); (16, 8%nat, mv); (24, 4%nat, av); (28, 4%nat, fv); (32, 8%nat, bv)]).
  assert (B : bv_unsigned (eval (rho1 mW) (v (vptr x))) = zA (mptr x)) by (rewrite ev1u by reflexivity; apply ze_ptr).
  assert (AG : forall d, loc_addr L (LMem (padd (mptr x) d)) = zA (mptr x) + d) by (intros d; unfold zA, addr_of, loc_addr; destruct (mptr x); cbn [padd]; lia).
  set (am := mam x) in *.
  assert (C0 : In (MCell (LMem (padd (mptr x) META_prev)) 8 (optr (am_prev am))) (image s)) by (apply (meta_cell_In x); cbn; tauto).
  assert (C1 : In (MCell (LMem (padd (mptr x) META_next)) 8 (optr (am_next am))) (image s)) by (apply (meta_cell_In x); cbn; tauto).
  assert (C2 : In (MCell (LMem (padd (mptr x) META_mem)) 8 (VP (am_mem am))) (image s)) by (apply (meta_cell_In x); cbn; tauto).
  assert (C3 : In (MCell (LMem (padd (mptr x) META_avail)) 4 (VZ (am_avail am))) (image s)) by (apply (meta_cell_In x); cbn; tauto).
  assert (C4 : In (MCell (LMem (padd (mptr x) META_freed)) 4 (VZ (am_freed am))) (image s)) by (apply (meta_cell_In x); cbn; tauto).
  assert (C5 : In (MCell (LMem (padd (mptr x) META_bits)) 8 (VZ (meta_bits am))) (image s)) by (apply (meta_cell_In x); cbn; tauto).
  rewrite Hp in C0. rewrite Hn in C1. cbn [optr] in C0, C1.

  assert (ENC4 : forall (e : sv) (z : Z) (j : nat), (j < 4)%nat -> zsupported e = true -> zeval zr1 zl1 e mod 2 ^ 32 = z ->
            nth j (enc_bytes 4 (eval (rho1 mW) e)) (Z_to_bv 8 0) = Z_to_bv 8 (le_byte z 4 j)).
  { intros e z j Hj Se Ez. rewrite (ev1 mW e Se). rewrite nth_enc_bytes by lia. f_equal.
    unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite <- Ez, Z.mod_mod by lia. reflexivity. }
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho.
    destruct (Z_lt_dec o 8) as [O0|O0]; [|destruct (Z_lt_dec o 16) as [O1|O1]; [|destruct (Z_lt_dec o 24) as [O2|O2]; [|destruct (Z_lt_dec o 28) as [O3|O3]; [|destruct (Z_lt_dec o 32) as [O4|O4]]]]].
    + apply (cell_rw0 _ (zA p) (zA (mptr x)) 0 8 C0 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ (zA n) (zA (mptr x)) 8 8 C1 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ (zA (am_mem am)) (zA (mptr x)) 16 8 C2 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ (am_avail am) (zA (mptr x)) 24 4 C3 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ (am_freed am) (zA (mptr x)) 28 4 C4 eq_refl eq_refl); [apply AG|lia].
    + apply (cell_rw0 _ (meta_bits am) (zA (mptr x)) 32 8 C5 eq_refl eq_refl); [apply AG|lia].
  - unfold cells_in_view. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]].
    + apply (cell_view0 _ (zA p) (zA (mptr x)) 0 8 _ C0 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by exact Spv. rewrite Epv, Ep. reflexivity.
    + apply (cell_view0 _ (zA n) (zA (mptr x)) 8 8 _ C1 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by exact Snv. rewrite Env, En. reflexivity.
    + apply (cell_view0 _ (zA (am_mem am)) (zA (mptr x)) 16 8 _ C2 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by exact Smv. rewrite Emv. reflexivity.
    + intros j Hj. destruct (cell_bytes0 _ (am_avail am) C3 eq_refl j Hj) as (_ & _ & RD). cbn [mc_loc mc_w] in RD. rewrite AG in RD. unfold META_avail in RD. rewrite RD.
      symmetry. f_equal. apply ENC4; [exact Hj | exact Sav | exact Eav].
    + intros j Hj. destruct (cell_bytes0 _ (am_freed am) C4 eq_refl j Hj) as (_ & _ & RD). cbn [mc_loc mc_w] in RD. rewrite AG in RD. unfold META_freed in RD. rewrite RD.
      symmetry. f_equal. apply ENC4; [exact Hj | exact Sfv | exact Efv].
    + apply (cell_view0 _ (meta_bits am) (zA (mptr x)) 32 8 _ C5 eq_refl eq_refl ltac:(lia)); [apply AG|]. rewrite ev1 by exact Sbv. rewrite Ebv. reflexivity.
Qed.

Lemma aidx_owned x : ltac2:(tb__ "0|0|
S170VL;Vs;S13cS6eS59S6dVx;A1A1A1Z8A2A3").
Proof using HI HMI HXr Hbnc Hgd Hhd Hsc rho. drop_sp.
  destruct (mam_used x) as (Hu & _).
  pose proof (aidx_cell_In X None U s HI HXr (mptr x) (mam x) Hu) as CI.
  pose proof (image_cell_owned X None U s L HI HXr HL _ CI 0%nat) as OW.
  assert (E : loc_addr L (mc_loc (aidx_cell (mam x))) + Z.of_nat 0 = zA (am_mem (mam x)) + 8).
  { unfold aidx_cell. destruct (am_maplen (mam x) =? 0); cbn [mc_loc]; unfold zA, addr_of, loc_addr; destruct (am_mem (mam x)); cbn [padd]; lia. }
  rewrite <- E. apply OW. unfold aidx_cell. destruct (am_maplen (mam x) =? 0); cbn; lia.
Qed.

Lemma hold_mem x yv : ltac2:(tb__ "0|0|
S4bS6S14fVyv;A1S1A3S4bS52S14cS6aS6bVyv;A3S7fVx;A1A3S25S15dS70VmW;A1S169Vms;VmW;A2S97Vx;Vyv;A2A4F_;F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbytes Hbytes_rd Hgd Hhd Hrom Hsc. drop_sp.
  intros Syv Eyv. pose proof (mem_R x) as R. top_ranges. pose proof (Hbytes x) as (HB & _).
  change (O_mem x yv) with (carved (v (vmem x)) 8 9 [(8, 1%nat, yv)]).
  assert (B : bv_unsigned (eval (rho1 mW) (v (vmem x))) = zA (am_mem (mam x))) by (rewrite ev1u by reflexivity; apply ze_mem).
  apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
  - cells_inside_tac.
  - intros o Ho. replace o with 8 by lia. apply owned_rw. apply aidx_owned.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. replace j with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
    rewrite Hbytes_rd. rewrite (ev1 mW yv Syv), Eyv, nth_enc_bytes by lia.
    unfold le_byte. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.mod_mod, (Z.mod_small (mbyte x) 256) by lia. reflexivity.
Qed.

Inductive od :=
  | OD_got | OD_guard | OD_sct | OD_ctz
  | OD_act (hv : sv)
  | OD_meta (x : member) (pv nv mv av fv bv : sv)
  | OD_mem (x : member) (yv : sv)
  | OD_bnc (x : member) (yv : sv).

Definition obj_of (d : od) : sobj := ltac2:(tb__ "0|0|
S73S17Ld;Vd;S95S96S99S94S12S92R1A1Lhv;S6cS12S12S12S12S12S12S98R7R6R5R4R3R2R1A7Lbv;Lfv;Lav;Lmv;Lnv;Lpv;Lx;S6cS12S97R2R1A2Lyv;Lx;S6cS12S93R2R1A2Lyv;Lx;X73x8").

Definition od_ok_at (t : astate) (d : od) : Prop := ltac2:(tb__ "0|e|
S73OLd;Vd;S4eS4eS4eS4eS12S4cS4bS6S14fR1A1S1A3M0S4bS52S14cS6aS6bR1A3M1S90S173Vt;Vsc;A2A1A3A2Lhv;S6cS12S12S12S12S12S12S4cS4bS6S14fR6A1S1A3S4cS4bS6S14fR5A1S1A3S4cS4bS6S14fR4A1S1A3S4cS4bS6S14fR3A1S1A3S4cS4bS6S14fR2A1S1A3S4cG0S4fS5eS5eS4cS4bS4S5fA1M2S16fVt;S6fR8A1A2SaS5fS61R1A1A2M3A3S4cS4bS52S14cS6aS6bR7A3S90S63R1A1A1A3S4cS4bS52S14cS6aS6bR6A3S90S62R1A1A1A3S4cS4bS52S14cS6aS6bR5A3S6eS59R1A1M4A1A3S4cS4bS52S141S14cS6aS6bR4A3S13eZ2Z20M5A2M6A2S5bR1A1A3S4cS4bS52S141S14cS6aS6bR3A3M7G6A2S57R1A1A3S4bS52S14cS6aS6bR2A3M8S16cR1A1A3A2A2A2A2A2A2Lam;A2A2A2A2A2A2A2Lbv;Lfv;Lav;Lmv;Lnv;Lpv;Lx;S6cS12S4cG0S4fS5eS5eS4cS4bG2S16fVt;S6fR3A1A2G3A3S4cS4cS13dZ0M9G8A2S13fG8Z100MaA2A2S4cS4bS52S141G8G5A2S58R1A1A3S4cS4bS56G4S59S6dR3A1MbA1A3S4cS4bS52S5cR1A1McS5cGbA1A3S4dS4bS52GcG9A3A1S4bS52G7S58R2A1A3F_;A2A2A2A2A2Lam;A2A2Lyv;Lx;S6cS12S4cG0S4cS4cS13dG9G1A2S13fG1GaA2A2S4cS13dZ7MdVsc;A2S13fVsc;Z27A2A2S4bS52G8S67S146Vsc;GdA2S66Vt;A1A2A3F_;A2A2Lyv;Lx;X73x8").

Definition od_ok (d : od) : Prop := ltac2:(tb__ "0|1|
S4cSaaVs;Vd;A2S73OLd;Vd;S4eS4eS4eS4eS12S4eLhv;S6cS12S12S12S12S12S12S4eLbv;Lfv;Lav;Lmv;Lnv;Lpv;Lx;S6cS12S4bS52S14cS6aS6bR1A3M0S7fR2A1A3Lyv;Lx;S6cS12S4bS52G0Vbnc;A3Lyv;Lx;X73x8A2").

Lemma od_hold d : ltac2:(tb__ "0|0|
S82Vd;A1S25S15dS70VmW;A1S169Vms;VmW;A2S81Vd;A1A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hreq Hrom Hsc Hsp Hspanv.
  destruct d; cbn [od_ok od_ok_at obj_of]; intros [H E].
  - apply hold_got. - apply hold_guard. - apply hold_sct. - apply hold_ctz.
  - destruct H as [S1 H1]. apply hold_act; [exact S1|]. rewrite H1, Hhd. reflexivity.
  - destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & am & M & E1 & E2 & E3 & E4 & E5 & E6).
    destruct (mam_used x) as (_ & _ & M'). rewrite M' in M. injection M as <-.
    destruct (mprev_used x) as (p & Hp & Ep). destruct (mnext_used x) as (n & Hn & En).
    apply hold_meta; try assumption.
    + rewrite E1, Hp, Ep. reflexivity.
    + rewrite E2, Hn, En. reflexivity.
  - destruct H as [S1 _]. apply hold_mem; assumption.
  - destruct H as [S1 _]. apply hold_bnc; assumption.
Qed.

Definition od_range (d : od) : Z * Z := ltac2:(tb__ "0|b|
S73S8S52S52A2Ld;Vd;S5S52S52S13cZ28d50M0Z0M1A2S13cG0Z8M2A2A4S5S52S52S13cZ5a338M3G1A2S13cG3G2A2A4S5S52S52S13cZ108ecM4G1A2S13cG4Z60M5A2A4S5S52S52S13cZ108ccM6G1A2S13cG6Z20A2A4S12S5S52S52S13cZ5a3c8M7S13cS144G2Vsc;A2M8Z58A2A2S13cG7S13cG8G5A2A2A4Lhv;S6cS12S12S12S12S12S12S5S52S52S13cS6eS6fR7A1A1M9G1A2S13cG9Z28A2A4Lbv;Lfv;Lav;Lmv;Lnv;Lpv;Lx;S6cS12S5S52S52S13cS6eS59S6dR2A1A1A1MaG2A2S13cGaZ9A2A4Lyv;Lx;S6cS12S5S52S52S13cG7S13cZ371Vsc;A2A2S13cG7S13cZ372Vsc;A2A2A4Lyv;Lx;X73x8").

Lemma soff1_lit : ltac2:(tb__ "0|1|
S160Q40A1S4S160Q8A1A1F_;S52S4cS13dS140S13eZ2Z3eA2M0A1R1A2S13dR1G0A2A2S4bS52S2dS70R3A1S11R2A1A2R2A3F_;Fz;Fm;").
Proof using Hbnc Hgd Hsc. drop_sp. intros. apply soff_lit_small. lia. Qed.

Lemma rng_lit : ltac2:(tb__ "0|3|
S12S52S52S3S13A1S33S52S4cS13dS140S13eZ2Z3eA2M0A1R5A2S13dR5G0A2A2M1G1S4bS52S162Q40S26S70VmW;A1M2R8A2A2R3A3S4bS8S52S52A2S28G2S18R9S11R8A1S11R7A1R6R5A5A2S5S52S52S13cR4R8A2S13cR4R7A2A4A3F_;F_;F_;Fb;Fd;Fcs;Fhi;Flo;Fbase;").
Proof using Hbnc Hgd Hsc. drop_sp.
  intros base lo hi cs d b Hlo Hhi Hb. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite Hb, !soff1_lit by lia. reflexivity.
Qed.

Lemma od_rng d : ltac2:(tb__ "0|0|
S4bS8S52S52A2S28S70VmW;A1S81Vd;A1A2S8fVd;A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp.
  pose proof (fun x => mem_R x) as R.
  destruct d; cbn [obj_of od_range]; unfold O_got, O_guard, O_meta, O_mem, O_sct, O_ctz.
  - apply rng_lit; [lia | lia | cbn [eval]; apply u64; lia].
  - apply rng_lit; [lia | lia | rewrite ev1u by reflexivity; rewrite ze173; reflexivity].
  - apply rng_lit; [lia | lia | cbn [eval]; apply u64; lia].
  - apply rng_lit; [lia | lia | cbn [eval]; apply u64; lia].
  - unfold obj_range, obj_lo_of, obj_hi_of, O_act. cbn [ob_base ob_lo ob_hi].
    rewrite (soff_of_ev e_actoff (8 * sc + 88) eq_refl ze_actoff) by lia. rewrite (soff_of_ev e_acthi (8 * sc + 96) eq_refl ze_acthi) by lia.
    cbn [eval]. rewrite u64 by lia. reflexivity.
  - apply rng_lit; [lia | lia |]. rewrite ev1u by reflexivity. apply ze_ptr.
  - apply rng_lit; [lia | lia |]. rewrite ev1u by reflexivity. apply ze_mem.
  - unfold obj_range, obj_lo_of, obj_hi_of, O_bnc. cbn [ob_base ob_lo ob_hi].
    rewrite (soff_of_ev (e_bncoff x) (881 + sc) eq_refl (ze_bncoff x)) by lia.
    rewrite (soff_of_ev (SAlu ALU_ADD (e_bncoff x) (SLit 1)) (882 + sc) eq_refl) by
      first [rewrite ze_alu, ze_bncoff, ze_lit; cbn [zalu]; change (1 mod 2 ^ 64) with 1; rewrite Z.mod_small; lia | lia].
    cbn [eval]. rewrite u64 by lia. reflexivity.
Qed.

Definition od_disj (d1 d2 : od) : Prop := ltac2:(tb__ "0|9|
S73OLd1;Vd1;S73OLd2;M0Vd2;S50S4eS4eS4eS12S4eLhv;M1S6cS12S12S12S12S12S12S4eLbv;Lfv;Lav;Lmv;Lnv;Lpv;M2Lx;M3S6cS12S4eLyv;M4Lx;M5G5X73x8G0Vd2;S4eS50S4eS4eG1G3G5G5X73x8G0Vd2;S4eS4eS50S4eG1G3G5G5X73x8G0Vd2;S4eS4eS4eS50G1G3G5G5X73x8S12G0Vd2;S4eS4eS4eS4eS12S50Lhv0;G3G5G5X73x8Lhv;S6cS12S12S12S12S12S12G0Vd2;S4eS4eS4eS4eG1S6cS12S12S12S12S12S12S4dS4bS56S6fReA1S6fR7A1A3A1Lbv1;Lfv0;Lav0;Lmv0;Lnv0;Lpv0;Ly;S6cG4Lx0;M6G6X73x8Lbv;Lfv;Lav;Lmv;Lnv;Lpv;Lx;S6cS12G0Vd2;S4eS4eS4eS4eG1S6cG2Lx0;M7S6cS12S4dS4bS56S6fR4A1S6fR2A1A3A1Lyv0;Ly;S6cS12S4eLyv0;Lx0;M8X73x8Lyv;Lx;S6cS12G0Vd2;S4eS4eS4eS4eG1G7G8S6cS12S50Lyv0;Lx0;X73x8Lyv;Lx;X73x8").

Lemma mem_zone x : ltac2:(tb__ "0|a|
S4cS13dZ1000M0S6eS6fVx;A1A1M1A2S4cS13dS13cG1Z28A2M2S187VL;A1M3A2S4cS51S13dG2Z10000M4A2S13dZ5b000M5G1A2A2S4cS51S13dS13cZ5a3d0M6Z3a0A2M7G1A2S13dG2G6A2A2S4cS13dG0S6eS59S6dVx;A1A1A1M8A2S4cS13dS13cG8Z9A2M9G3A2S4cS51S13dG9G4A2S13dG5G8A2A2S51S13dG7G8A2S13dG9G6A2A2A2A2A2A2A2A2A2").
Proof using HI HMI Hbnc Hgd Hhd Hsc Hsp.
  pose proof Hctx as HCX. destruct (mam_used x) as (Hu & _).
  pose proof (key_range X None U s L HI HL C_U vm (mptr x) (mptr_key x) HV HLG) as (K1 & K2 & K3 & K4).
  pose proof (group_range X None U s L HI HL C_U vm (mptr x) (mam x) Hu HV HLG) as (G1 & G2 & G3 & G4).
  pose proof (inv_groups HI _ _ Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as ((Glast & _) & _).
  assert (E28 : 28 <= group_extent (mam x)).
  { unfold group_extent. assert (stride_of (mam x) <= stride_of (mam x) * (am_last (mam x) + 1)) by nia. unfold UNIT, IB. lia. }
  rewrite HCX in K4, G4. cbn [mc_img_lo mc_img_hi C_U] in K3, G3. unfold zA, META_SIZE, PGSZ, CTX_SIZE, IB in *. lia.
Qed.

Lemma meta_vs_mem x y : ltac2:(tb__ "0|2|
S51S13dS13cS6eS6fVx;A1A1M0Z28A2S13cS6eS59S6dVy;A1A1A1Z8A2M1A2S13dS13cG1Z1A2G0A2A2").
Proof using HI HMI Hbnc Hgd Hhd Hsc Hsp.
  destruct (mam_used y) as (Hu & _). pose proof (inv_groups HI _ _ Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as ((Glast & _) & _).
  assert (E28 : 28 <= group_extent (mam y)).
  { unfold group_extent. assert (stride_of (mam y) <= stride_of (mam y) * (am_last (mam y) + 1)) by nia. unfold UNIT, IB. lia. }
  pose proof (meta_vs_group X None U s L HI HL (mptr x) (mptr y) (mam y) 8 (mptr_key x) Hu ltac:(unfold IB; lia)) as D.
  unfold zA, META_SIZE in *. lia.
Qed.

Lemma od_disjoint d1 d2 : ltac2:(tb__ "0|0|
Sa9Vd1;Vd2;A2S2bS8fVd1;A1S8fVd2;A1A2F_;").
Proof using HI HMI Hbnc Hgd Hhd Hsc Hsp Hsp_high.
  intros Hd. unfold SymState.ranges_disjoint.
  destruct d1 as [| | | |h1|x1 p1 n1 q1 a1 f1 b1|x1 y1|x1 y1]; destruct d2 as [| | | |h2|x2 p2 n2 q2 a2 f2 b2|x2 y2|x2 y2]; cbn [od_disj od_range fst snd] in *;
    try (exfalso; exact Hd);
    try (pose proof (mem_zone x1) as Z1); try (pose proof (mem_zone x2) as Z2);
    top_ranges; try lia.
  - pose proof (mptr_addr_ne x1 x2 Hd). lia.
  - pose proof (meta_vs_mem x1 x2). lia.
  - pose proof (meta_vs_mem x2 x1). lia.
  - pose proof (mmem_addr_ne x1 x2 Hd). lia.
Qed.

Fixpoint od_pairwise (l : list od) : Prop :=
  match l with [] => True | d :: t => Forall (od_disj d) t /\ od_pairwise t end.

Lemma od_pairwise_disjoint l : ltac2:(tb__ "0|0|
S9cVl;A1S34S70VmW;A1S157S73S17S81Vl;A4A2F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp Hsp_high.
  induction l as [|d t IH]; intros H; cbn [od_pairwise map pairwise_disjoint] in *; [exact I|].
  destruct H as [Hd Ht]. split; [|apply IH; exact Ht].
  apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d' & <- & Hd').
  rewrite !od_rng. apply od_disjoint. exact (proj1 (Forall_forall _ _) Hd d' Hd').
Qed.

Definition sp0 : Z := bv_unsigned (rw rho 10%positive).
Definition D0 : Z := toS 64 (bv_unsigned (rw rho 15%positive)).

Lemma ev_sp m : ltac2:(tb__ "0|1|
S4bS160Q40A1S26S70Vm;A1S10PaM0A1A2S24Vrho;G0A2A3").
Proof using Hbnc Hgd Hsc. drop_sp. cbn [eval rho1 rw]. apply rw1_low; lia. Qed.
Lemma ev_v15 m : ltac2:(tb__ "0|1|
S4bS160Q40A1S26S70Vm;A1S10PfM0A1A2S24Vrho;G0A2A3").
Proof using Hbnc Hgd Hsc. drop_sp. cbn [eval rho1 rw]. apply rw1_low; lia. Qed.

Lemma rng_stk : ltac2:(tb__ "0|0|
S4bS8S52S52A2S28S70VmW;A1S8bA2S5S52S52S13cS9eS9fA2S9eA4A3").
Proof using Hbnc Hgd Hsc. drop_sp.
  unfold obj_range, obj_lo_of, obj_hi_of, O_stk. cbn [ob_base ob_lo ob_hi]. rewrite ev_sp.
  rewrite soff1_lit by lia. unfold soff. rewrite ev_v15. rewrite bv_signed_toS by (cbn; lia). unfold sp0, D0. f_equal. lia.
Qed.

Lemma od_vs_stack d : ltac2:(tb__ "0|1|
S2bS28S70VmW;A1M0S8bA2S28G0S81Vd;A1A2A2").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp Hsp_high.
  rewrite rng_stk, od_rng. pose proof Hsp_high as SH. unfold sp0, D0, SymState.ranges_disjoint.
  destruct d as [| | | |h|x p n q a f b|x y|x y]; cbn [od_range fst snd]; try (pose proof (mem_zone x) as ZX); top_ranges; lia.
Qed.

Theorem carve : ltac2:(tb__ "0|2|
S2fS3S73A1S53S3S199A1M0S198S4bS3S17A1S2eR5A1S0S17S8bS2S17A1A3A3S159S73S82R5A3S9cR6A1S21S3aR8A1S3bR8A1S38R8A1S37R8A1S3cR8A1SfS17S2eR8A1S157S73S17S81R7A4A3S36R8A1R6S39R8A1A9S2fS4bS6S3dR1A1S1A3S2cS15dS70VmW;A1M1RaS5G0S191R7S192Vms;R6A2A4A4S2cS15dG1R3S5G0S191R8S192Vms;R7A2A4A4F_;F_;TS';F_;F_;F_;Fmd;Ftr;Fnx;Fds;FS;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hreq Hrom Hsc Hsp Hsp_high Hspanv.
  intros S ds nx tr md HO Hok Hpw S' Hwf Hsm. apply smatch_extend_objs.
  - exact Hsm.
  - exact Hwf.
  - change (rm (rho1 mW)) with mW. apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd).
    apply od_hold. exact (proj1 (Forall_forall _ _) Hok d Hd).
  - rewrite HO. apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd). constructor; [|constructor]. apply od_vs_stack.
  - apply od_pairwise_disjoint. exact Hpw.
Qed.

Definition e_ctz (e : sv) : sv := ltac2:(tb__ "0|0|
S1eS7Q8S27P4S86Ve;A1Z1A3A3").

Lemma lowbit_is_bit z : ltac2:(tb__ "0|1|
S13fZ0M0Vz;A2S4fS52S52S4cS13dG0R1A2S4cS4bS52S60Vz;A1S13eZ2R1A2A3S4bS52S65Vz;A1R1A3A2A2Lk;A2F_;").
Proof using . drop_sp.
  intros Hz. destruct (lowbit_spec z Hz) as (k & Hk & Hl & _). exists k. split; [exact Hk|].
  unfold bit in Hl. split; [exact Hl|]. unfold ctz32. rewrite Hl. apply Z.log2_pow2. exact Hk.
Qed.

Lemma ze_ctz e z : ltac2:(tb__ "0|2|
S4bS52S14cS6aS6bVe;A3S14eVz;A1A3S4cS13fZ0M0Vz;A2S13fVz;S13eZ2Z20A2A2A2S4cS4bS52S14cS6aS6bSa8Ve;A1A3S65Vz;A1M1A3S4cS13dG0G1A2S13dG1Z1fA2A2A2F_;F_;").
Proof using Hbnc Hgd Hsc Hsp.
  intros E Hz. destruct (lowbit_is_bit z ltac:(lia)) as (k & Hk & Hl & Hc). rewrite Hc.
  pose proof (lowbit_range z Hz) as LR.
  assert (Hk31 : k <= 31).
  { destruct (Z_le_dec k 31); [assumption|]. exfalso. assert (2 ^ 32 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). lia. }
  split; [|lia].
  unfold e_ctz. rewrite ze_ext. cbn [Z.of_N]. rewrite ze_lbytes, zl1_4.
  destruct (ze_dbidx_sx e z E Hz) as [ED _]. rewrite ED, Hl.
  set (j := Z.shiftr ((2 ^ k * 125613361) mod 2 ^ 32) 27).
  pose proof (dbidx_lt32 (2 ^ k * 125613361)) as D. fold j in D.
  pose proof (ctz_lookup k ltac:(lia)) as T. fold j in T.
  unfold zsublist. change (Z.to_nat 1) with 1%nat.
  assert (LEN : (Z.to_nat j < length ctz_tab_bytes)%nat) by (change (length ctz_tab_bytes) with 32%nat; lia).
  destruct (skipn (Z.to_nat j) ctz_tab_bytes) as [|b t] eqn:Es.
  - exfalso. pose proof (length_skipn (Z.to_nat j) ctz_tab_bytes) as SL. rewrite Es in SL. cbn in SL. lia.
  - assert (Eb : b = k).
    { rewrite <- T. rewrite <- (Nat.add_0_r (Z.to_nat j)). rewrite <- nth_skipn. rewrite Es. reflexivity. }
    subst b. cbn [firstn zle]. rewrite Z.mul_0_r, Z.add_0_r. rewrite (Z.mod_small k 256) by lia. rewrite !Z.mod_small; lia.
Qed.

Lemma od_ok_meta_entry x (pv nv : positive) : ltac2:(tb__ "0|3|
S4bS52S14cS6aS6bS3eVpv;A1M0A3S6eS163Vs;S6fVx;A1M1A2A1A3S4bS52S14cS6aS6bS3eVnv;A1M2A3S6eS164Vs;G1A2A1A3S82Sa7Vx;G0G2S3eS88Vx;A1A1S3eS7dVx;A1A1S3eS78Vx;A1A1S3eS79Vx;A1A1A7A1F_;F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp.
  intros Epv Env. destruct (mam_used x) as (_ & _ & M). destruct (mprev_used x) as (p & Hp & Ep). destruct (mnext_used x) as (n & Hn & En).
  pose proof (mem_R x) as R.
  split; [|exact I]. cbn [od_ok_at]. repeat (split; [reflexivity|]). exists (mam x). split; [exact M|].
  rewrite Epv, Env, Hp, Hn, <- Ep, <- En. cbn [optrZ]. rewrite ze_mem, ze_avail, ze_freed, ze_bits.
  repeat split; try reflexivity; apply Z.mod_small; lia.
Qed.
Lemma od_ok_act_entry : od_ok (OD_act (v 120)).
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp. split; [|exact I]. cbn [od_ok_at]. split; [reflexivity|]. rewrite Hhd. cbn [optrZ]. exact (ze_ptr MM0). Qed.
Lemma od_ok_mem_entry x : ltac2:(tb__ "0|0|
S82Sa6Vx;S3eS7aVx;A1A1A2A1").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp.
  pose proof (Hbytes x) as (B1 & B2 & B3). destruct (mam_used x) as (_ & _ & M).
  split; [|apply ze_byte]. cbn [od_ok_at]. split; [reflexivity|]. exists (mam x). rewrite ze_byte. repeat split; auto; lia.
Qed.
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S4cS13dZ7M0Vsc;A2S13fVsc;Z27A2A2S4bS52Vbnc;S67S146Vsc;G0A2S66Vs;A1A2A3F_;").
Lemma od_ok_bnc_entry x : ltac2:(tb__ "0|0|
S82Sa5Vx;S3ePaaA1A2A1").
Proof using Hbnc Hbnc_val Hgd Hsc Hsp. split; [|apply ze170]. cbn [od_ok_at]. rewrite ze170. split; [reflexivity|]. split; [lia|]. exact Hbnc_val. Qed.
Lemma od_ok_got : od_ok OD_got. Proof using . split; exact I. Qed.
Lemma od_ok_guard : od_ok OD_guard. Proof using . split; exact I. Qed.
Lemma od_ok_sct : od_ok OD_sct. Proof using . split; exact I. Qed.
Lemma od_ok_ctz : od_ok OD_ctz. Proof using . split; exact I. Qed.

End Inst.
End Mal_aslot_I.

Module Mal_aslot_runsR.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs.

Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.
Set Printing Width 300. Set Printing Depth 100000.
Definition segs := segsU.
Definition CUTS : list Z := ltac2:(tb__ "0|0|
S0S52Z20c24S0S52Z2126cS0S52Z21b10S0S52Z202a8S0S52Z21788S0S52Z2144cS0S52Z21ddcS0S52Z213e0S0S52Z2179cS2S52A1A3A3A3A3A3A3A3A3A3").
Definition NXA : positive := 300%positive.

Definition lfs (l : list leaf) (i : nat) (d : sstate) : sstate := ltac2:(tb__ "0|0|
Sb3S158SadVi;Vl;Sb4Vd;Sb1A2A4A1").
Definition unopt (o : option (list leaf)) : list leaf := match o with Some l => l | None => [] end.

Definition SA_N : sstate := ltac2:(tb__ "0|c|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1S16S3fS16S42S3ePcA1M8S11Z3A1A3M9S11Z58A1A3MaS16S3fG9S11Z60A1MbA3S0S13S14GaG5G3A3G4A3S1aA5S0S17S18S11Z108ecA1G3GbG4S1fP1A1A5S0S17S18S11Z108ccA1G3S11Z20A1G4S1fP4A1A5S2S17A1A3A3A3A3A3A3S0S15S20G0Z4A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2Z28A2A1A1A3S0S15S1cG8S11Z2fA1A2S2S15A1A3A3A3A3A3Sb7S7A9").

Definition RA_N__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5SbaS1A5").
Definition RA_N : option (list leaf) := ltac:(let x := eval vm_compute in RA_N__f in exact x).
Lemma runA_N : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5SbaS1A5S112A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) RA_N). Qed.
Definition LA_N : list leaf := ltac:(let x := eval vm_compute in (unopt RA_N) in exact x).
Lemma LA_N_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSe6A4S0G0S5S52SacZ2144cSafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_Ns : sstate := ltac:(let x := eval vm_compute in (lfs LA_N 0 SA_N) in exact x).

Definition SA_H : sstate := ltac2:(tb__ "0|13|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1S16S3fS16S42S3ePcA1M8S11Z3A1A3M9S11Z58A1A3MaS16S3fG9S11Z60A1MbA3S0S13S14GaG5S3eP78A1McA3G4A3S1aA5S0S17S18GcG3S11Z28MdA1S0S13S14G3G5S3ePa0A1A3S0S13S14G6G5S3eP82A1A3S0S13S14S11Z10A1G5S3eP7bA1A3S0S13S14S11Z18A1Z4MeS3eP7cA1MfA3S0S13S14S11Z1cA1GeS3eP7dA1A3S0S13S14S11Z20A1M10G5S3eP7eA1A3G4A3A3A3A3A3A3S1aA5S0S17S18S11Z108ecA1G3GbG4S1fP1A1A5S0S17S18S11Z108ccA1G3G10G4S1fP4A1A5S2S17A1A3A3A3A3A3A3A3S0S15S20G0GeA2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2GdA2A1A1A3S0S15S1cG8S11Z2fA1A2S0S15S1bS19S40GcG3A3A1S0S15S1bS19S40S1eS1Q20GfA3M11G3A3A1S0S15S1bS19S40S16S41G11S1dS45G3G11A3A3M12G3A3A1S0S15S1cS1dS44S23S46G12S11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S2S15A1A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_H__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sb9S1A5").
Definition RA_H : option (list leaf) := ltac:(let x := eval vm_compute in RA_H__f in exact x).
Lemma runA_H : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sb9S1A5S111A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_H__f. Qed.
Definition LA_H : list leaf := ltac:(let x := eval vm_compute in (unopt RA_H) in exact x).
Lemma LA_H_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSe5A4S0G0S5S52SacZ21b08Sb0A4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_Hs : sstate := ltac:(let x := eval vm_compute in (lfs LA_H 0 SA_H) in exact x).

Definition SA_E : sstate := ltac2:(tb__ "0|13|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1S16S3fS16S42S3ePcA1M8S11Z3A1A3M9S11Z58A1A3MaS16S3fG9S11Z60A1MbA3S0S13S14GaG5S3eP78A1McA3G4A3S1aA5S0S17S18GcG3S11Z28MdA1S0S13S14G3G5GcA3S0S13S14G6G5GcA3S0S13S14S11Z10A1G5S3eP7bA1A3S0S13S14S11Z18A1Z4MeS3eP7cA1MfA3S0S13S14S11Z1cA1GeS3eP7dA1M10A3S0S13S14S11Z20A1M11G5S3eP7eA1A3G4A3A3A3A3A3A3S1aA5S0S17S18S11Z108ecA1G3GbG4S1fP1A1A5S0S17S18S11Z108ccA1G3G11G4S1fP4A1A5S2S17A1A3A3A3A3A3A3A3S0S15S20G0GeA2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2GdA2A1A1A3S0S15S1cG8S11Z2fA1A2S0S15S1bS19S40GcG3A3A1S0S15S19S40S1eS1Q20M12GfA3G3A3S0S15S19S40S1eS1G12G10A3G3A3S2S15A1A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_E__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sb8S1A5").
Definition RA_E : option (list leaf) := ltac:(let x := eval vm_compute in RA_E__f in exact x).
Lemma runA_E : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sb8S1A5S110A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_E__f. Qed.
Definition LA_E : list leaf := ltac:(let x := eval vm_compute in (unopt RA_E) in exact x).
Lemma LA_E_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSe4A4S0G0S5S52SacZ2144cSafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_Es : sstate := ltac:(let x := eval vm_compute in (lfs LA_E 0 SA_E) in exact x).

Definition SA_R1nh : sstate := ltac2:(tb__ "0|22|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78MeA1MfA3G4A3S1aA5S0S17S18GfG3S11Z28M10A1S0S13S14G3G5GfA3S0S13S14G6G5GfA3S0S13S14S11Z10A1G5S3eP7bA1M11A3S0S13S14S11Z18A1Z4M12S3eP7cA1M13A3S0S13S14S11Z1cA1G12S3eP7dA1M14A3S0S13S14S11Z20A1M15G5S3eP7eA1M16A3G4A3A3A3A3A3A3S1aA5S0S17S18G11G6S11Z9A1S0S13S14G6Z1M17S3eP7fA1M18A3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G15G4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M19G16A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M1aS16S3fG1aS11G17A1A3S0S13S14G1aG17S3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3S0S15S20G0G12A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M1bG10A2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GfG3A3A1S0S15S1cG18S11ZffA1A2S0S15S20GeGaA2S0S15S1bS19S40S16S41G16G15A3G3A3A1S0S15S19S40S1eS1G19G13A3G3A3S0S15S1bS19S40S1eS1G19G14A3M1cG3A3A1S0S15S19S47G1cS1dS3fS1dS42S11G1bA1M1dG16A3S11ZffffffffffffffffA1M1eA3A3S0S15S1bS19S40S16S41S1dS3fS1dS42G1dG18A3G1eA3M1fG1cA3G3A3A1M20S0S15S1bS19S40S16S41G1cG1fA3G3A3A1M21S0S15S1cG13G3A2S0S15G21S0S15G20S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R1nh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5SbbS1A5").
Definition RA_R1nh : option (list leaf) := ltac:(let x := eval vm_compute in RA_R1nh__f in exact x).
Lemma runA_R1nh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5SbbS1A5S113A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R1nh__f. Qed.
Definition LA_R1nh : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R1nh) in exact x).
Lemma LA_R1nh_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSe7A4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R1nhs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R1nh 0 SA_R1nh) in exact x).
Definition ST_R1nh : sstate := ltac2:(tb__ "0|28|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P78M5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P7fA1MaA3MbA3McS0S12S1eS1Q20MdS10P7dA1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18G6G9S11Z28A1S0S13S14S11Z18A1Z4M1fS16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G1fGfA3S0S13S14G9G19G6A3S0S13S14G1cG19G6A3S0S13S14S11Z10A1G19S10P7bA1M20A3S0S13S14S11Z20A1M21G19S10P7eA1M22A3G1bA3A3A3A3A3A3S1aA5S0S17S18G20G1cS11Z9A1S0S13S14G1cZ1M23GaA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G21G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG22A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M24S16S3fG24S11G23A1A3S0S13S14G24G23S10PaaA1M25A3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3S0S15S20G1G1fA2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G6G9A3A1S0S15S1cGaS11ZffA1M26A2S0S15S20G5G12A2S0S15S1bS19S40S16S41G22G21A3G9A3A1S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M27G9A3A1S0S15S1cS1dS44S23S46G27S11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG25G26A2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R1nh : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R1nhs ST_R1nh) in exact x).
Definition RT_R1nh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sd1S1A5").
Definition RT_R1nh : option (list leaf) := ltac:(let x := eval vm_compute in RT_R1nh__f in exact x).
Lemma runT_R1nh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sd1S1A5S129A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R1nh__f. Qed.
Definition LT_R1nh : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R1nh) in exact x).
Lemma LT_R1nh_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cSfdA4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R1ns : sstate := ltac2:(tb__ "0|20|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78MeA1MfA3G4A3S1aA5S0S17S18GfG3S11Z28M10A1S0S13S14G3G5GfA3S0S13S14G6G5GfA3S0S13S14S11Z10A1G5S3eP7bA1M11A3S0S13S14S11Z18A1Z4M12S3eP7cA1M13A3S0S13S14S11Z1cA1G12S3eP7dA1M14A3S0S13S14S11Z20A1M15G5S3eP7eA1M16A3G4A3A3A3A3A3A3S1aA5S0S17S18G11G6S11Z9A1S0S13S14G6Z1M17S3eP7fA1M18A3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G15G4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M19G16A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M1aS16S3fG1aS11G17A1A3S0S13S14G1aG17S3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3S0S15S20G0G12A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M1bG10A2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GfG3A3A1S0S15S1cG18S11ZffA1A2S0S15S20GeGaA2S0S15S1bS19S40S16S41G16G15A3G3A3A1S0S15S19S40S1eS1G19G13A3G3A3S0S15S1bS19S40S1eS1G19G14A3M1cG3A3A1S0S15S19S47G1cS1dS3fS1dS42S11G1bA1M1dG16A3S11ZffffffffffffffffA1M1eA3A3S0S15S19S40S16S41S1dS3fS1dS42G1dG18A3G1eA3M1fG1cA3G3A3S0S15S19S40S16S41G1cG1fA3G3A3S0S15S1cS16S41S16S44G16S11Z5A1A3S11Z7eA1A3S11Z5eA1A2S0S15S1cG13G3A2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R1ns__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5SbcS1A5").
Definition RA_R1ns : option (list leaf) := ltac:(let x := eval vm_compute in RA_R1ns__f in exact x).
Lemma runA_R1ns : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5SbcS1A5S114A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R1ns__f. Qed.
Definition LA_R1ns : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R1ns) in exact x).
Lemma LA_R1ns_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSe8A4S0G0S5S52SacZ21788SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R1nss : sstate := ltac:(let x := eval vm_compute in (lfs LA_R1ns 0 SA_R1ns) in exact x).
Definition SL_R1ns : sstate := ltac:(let x := eval vm_compute in (restateF LA_R1nss 0x21788 [(5%nat, SVar 210); (16%nat, SVar 211); (14%nat, SVar 212); (6%nat, SVar 213)] (ss_facts SA_R1ns)) in exact x).
Definition DL_R1ns : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R1nss SL_R1ns) in exact x).
Definition RL_R1ns__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5SceS1A5").
Definition RL_R1ns : option (list leaf) := ltac:(let x := eval vm_compute in RL_R1ns__f in exact x).
Lemma runL_R1ns : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5SceS1A5S126A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RL_R1ns__f. Qed.
Definition LL_R1ns : list leaf := ltac:(let x := eval vm_compute in (unopt RL_R1ns) in exact x).
Lemma LL_R1ns_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSfaA4S0G0S5S52SacZ21788SafA4S0G0S5S52SacZ2179cSafA4S2G0A1A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition DLL_R1ns : list (sv * sv) * list sprop := ltac2:(tb__ "0|5|
S5S3S8S12S12A2M0A1S3S15A1S0G0S5S12S12S1dS3fS10Pd2A1M1S16S42S1eS7Q10S27P1S16S41S16S44S10P7eA1S11Z5A1A3S11Z7eA1A3Z2A3A3S11Z4A1A3M2A3G1A4S0G0S5S12S12S16S49S10Pd3A1M3G1A3S10Pd5A1A4S0G0S5S12S12S1dS3fS10Pd4A1M4S11Z1A1A3G4A4S0G0S5S12S12S1dS3fG3G2A3G3A4S2G0A1A3A3A3A3S2S15A1A4").
Definition SX_R1ns : sstate := ltac2:(tb__ "0|29|
S21Z2179cS0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10Pd6A1S0S12S10Pd8A1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P78M5A1M6S0S12S10P7bA1M7S0S12S10P7fA1M8S0S12S10P7eA1M9S0S12S10PacA1MaS0S12S16S42S1eS7Q10S27P1MbS16S41S16S44G9S11Z5A1A3S11Z7eA1A3McZ2MdA3A3S11Z4MeA1A3S0S12S10Pd7A1S0S12S10Pd9A1S0S12S10PdA1S0S12S10P27A1MfS0S12S10PadA1M10S0S12S16S3fS16S42G3S11Z3M11A1A3M12S11Z5a420A1A3S0S12S11Z5a3c8A1M13S0S12S16S3fG12G13A3S0S12S10P2cA1M14S0S12S10P2dA1M15S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M16A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G16A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M17S11Z0A1M18S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G15A3S0S13S14S11N50A1G19G14A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19GfA3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G18S11G19A1M1cS0S13S14G18G19G10A3G1bA3S1aA5S0S17S18G10G18G1cS0S13S14G18G19G1aA3G1bA3S1aA5S0S17S18G13S16S3fG12S11Z58A1A3M1dS16S3fG12S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18G6G18S11Z28A1S0S13S14G18G19G6A3S0S13S14G1cG19G6A3S0S13S14S11Z10A1G19G7A3S0S13S14S11Z18A1GeS10P7cA1M1fA3S0S13S14S11Z1cA1GeS10P7dA1M20A3S0S13S14S11Z20A1M21G19G9A3G1bA3A3A3A3A3A3S1aA5S0S17S18G7G1cS11Z9A1S0S13S14G1cZ1M22G8A3G1bA3S1aA5S0S17S18S11Z108ecA1G18G1eG1bS1fGbA1A5S0S17S18S11Z108ccA1G18G21G1bS1fP4A1A5S0S17S18G13S16S3fS16S44S16S42S1eS1Q20M23G9A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M24S16S3fG24S11G22A1A3S0S13S14G24G22S10PaaA1A3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3S0S15S20G1GeA2S0S15S1cS11Z7fff7f800000A1S16S3fG2G17A3A2S0S15S19S43S11N120A1G17A3S0S15S19S43G17S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G6G18A3A1S0S15S1cG8S11ZffA1A2S0S15S20G5G11A2S0S15S1bS19S40S16S41G9G21A3G18A3A1S0S15S19S40S1eS1G23G1fA3G18A3S0S15S1bS19S40S1eS1G23G20A3M25G18A3A1S0S15S19S47G25S1dS3fS1dS42S11GdA1M26G9A3S11ZffffffffffffffffA1M27A3A3S0S15S19S40S16S41S1dS3fS1dS42G26G8A3G27A3M28G25A3G18A3S0S15S19S40S16S41G25G28A3G18A3S0S15S1cGcS11Z5eA1A2S0S15S1cG1fG18A2S0S15S1cGaS11Z12cA1A2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DX_R1ns : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff (lfs LL_R1ns 1 SA_R1ns) SX_R1ns) in exact x).
Definition RX_R1ns__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Se3S1A5").
Definition RX_R1ns : option (list leaf) := ltac:(let x := eval vm_compute in RX_R1ns__f in exact x).
Lemma runX_R1ns : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Se3S1A5S13bA3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RX_R1ns__f. Qed.
Definition LX_R1ns : list leaf := ltac:(let x := eval vm_compute in (unopt RX_R1ns) in exact x).
Lemma LX_R1ns_shape : ltac2:(tb__ "0|3|
S4bS3S8S52SacA2M0A1S157SadG0S15cS10fA4S0G0S5S52SacZ213e0SafA4M1S0G0S5S52SacZ213dcSb2A4M2S0G0G1S0G0G2S2G0A1A3A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition ST0_R1ns : sstate := ltac2:(tb__ "0|2a|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10Pd6A1S0S12S10Pd8A1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P78M5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S16S48S16S41S16S3fS10PacA1S11N1A1A3S11Z1fA1MaA3S16S41S10P7fA1MbS11Ze0A1A3A3McA3MdA3MeS0S12S1eS1Q20MfS10P7dA1A3M10S0S12S16S41G10GeA3M11S0S12G10S0S12G9S0S12S10PdA1S0S12S10P27A1M12S0S12S10PadA1M13S0S12S16S3fS16S42G3S11Z3M14A1A3M15S11Z5a420A1A3S0S12S11Z5a3c8A1M16S0S12S16S3fG15G16A3S0S12S10P2cA1M17S0S12S10P2dA1M18S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M19A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G19A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M1aG9S0S13S14S11N60A1Z8M1bS10PaeA1M1cA3S0S13S14S11N58A1G1bG18A3S0S13S14S11N50A1G1bG17A3S0S13S14S11N48A1G1bS10P2bA1A3S0S13S14S11N40A1G1bS10P2aA1A3S0S13S14S11N38A1G1bS10P29A1A3S0S13S14S11N30A1G1bS10P28A1A3S0S13S14S11N28A1G1bG12A3S0S13S14S11N20A1G1bS10P26A1A3S0S13S14S11N18A1G1bG4A3S0S13S14S11N10A1G1bS10P1cA1A3S0S13S14S11N8A1G1bG0A3S2S13A1M1dA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G1bA1M1eS0S13S14G9G1bG13A3G1dA3S1aA5S0S17S18G13G9G1eS0S13S14G9G1bG1cA3G1dA3S1aA5S0S17S18G16S16S3fG15S11Z58A1A3M1fS16S3fG15S11Z60A1M20A3S0S13S14G1fG1bG6A3G1dA3S1aA5S0S17S18G6G9S11Z28A1S0S13S14S11Z18A1Z4M21S16S41G10S1dS3fGdS11ZffffffffffffffffA1A3A3A3S0S13S14G8G21G11A3S0S13S14G9G1bG6A3S0S13S14G1eG1bG6A3S0S13S14S11Z10A1G1bS10P7bA1M22A3S0S13S14S11Z20A1M23G1bS10P7eA1M24A3G1dA3A3A3A3A3A3S1aA5S0S17S18G22G1eS11Z9A1S0S13S14G1eZ1M25GcA3G1dA3S1aA5S0S17S18S11Z108ecA1G9G20G1dS1fP1A1A5S0S17S18S11Z108ccA1G9G23G1dS1fP4A1A5S0S17S18G16S16S3fS16S44S16S42S1eS1GfG24A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M26S16S3fG26S11G25A1A3S0S13S14G26G25S10PaaA1M27A3G1dA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3S0S15S20G1G21A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G1aA3A2S0S15S19S43S11N120A1G1aA3S0S15S19S43G1aS11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G6G9A3A1S0S15S1cGbS11ZffA1M28A2S0S15S20G5G14A2S0S15S1bS19S40S16S41G24G23A3G9A3A1S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M29G9A3A1S0S15S1cS1dS44S23S46G29S11Z77cb531A1A3S11Z1bA1A3GaA2S0S15S1cG27G28A2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT0_R1ns : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff (lfs LX_R1ns 0 SA_R1ns) ST0_R1ns) in exact x).
Definition RT0_R1ns__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5ScfS1A5").
Definition RT0_R1ns : option (list leaf) := ltac:(let x := eval vm_compute in RT0_R1ns__f in exact x).
Lemma runT0_R1ns : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5ScfS1A5S127A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT0_R1ns__f. Qed.
Definition LT0_R1ns : list leaf := ltac:(let x := eval vm_compute in (unopt RT0_R1ns) in exact x).
Lemma LT0_R1ns_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cSfbA4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition ST2_R1ns : sstate := ltac2:(tb__ "0|2a|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10Pd6A1S0S12S10Pd8A1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P78M5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S16S48S16S41S16S41S10P7eA1MaS11Z1fA1MbA3GbA3S16S41S10P7fA1McS11Ze0A1A3A3MdA3MeA3MfS0S12S1eS1Q20M10S10P7dA1A3M11S0S12S16S41G11GfA3M12S0S12G11S0S12G9S0S12S10PdA1S0S12S10P27A1M13S0S12S10PadA1M14S0S12S16S3fS16S42G3S11Z3M15A1A3M16S11Z5a420A1A3S0S12S11Z5a3c8A1M17S0S12S16S3fG16G17A3S0S12S10P2cA1M18S0S12S10P2dA1M19S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M1aA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G1aA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M1bG9S0S13S14S11N60A1Z8M1cS10PaeA1M1dA3S0S13S14S11N58A1G1cG19A3S0S13S14S11N50A1G1cG18A3S0S13S14S11N48A1G1cS10P2bA1A3S0S13S14S11N40A1G1cS10P2aA1A3S0S13S14S11N38A1G1cS10P29A1A3S0S13S14S11N30A1G1cS10P28A1A3S0S13S14S11N28A1G1cG13A3S0S13S14S11N20A1G1cS10P26A1A3S0S13S14S11N18A1G1cG4A3S0S13S14S11N10A1G1cS10P1cA1A3S0S13S14S11N8A1G1cG0A3S2S13A1M1eA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G1cA1M1fS0S13S14G9G1cG14A3G1eA3S1aA5S0S17S18G14G9G1fS0S13S14G9G1cG1dA3G1eA3S1aA5S0S17S18G17S16S3fG16S11Z58A1A3M20S16S3fG16S11Z60A1M21A3S0S13S14G20G1cG6A3G1eA3S1aA5S0S17S18G6G9S11Z28A1S0S13S14S11Z18A1Z4M22S16S41G11S1dS3fGeS11ZffffffffffffffffA1A3A3A3S0S13S14G8G22G12A3S0S13S14G9G1cG6A3S0S13S14G1fG1cG6A3S0S13S14S11Z10A1G1cS10P7bA1M23A3S0S13S14S11Z20A1M24G1cGaA3G1eA3A3A3A3A3A3S1aA5S0S17S18G23G1fS11Z9A1S0S13S14G1fZ1M25GdA3G1eA3S1aA5S0S17S18S11Z108ecA1G9G21G1eS1fP1A1A5S0S17S18S11Z108ccA1G9G24G1eS1fP4A1A5S0S17S18G17S16S3fS16S44S16S42S1eS1G10GaA3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M26S16S3fG26S11G25A1A3S0S13S14G26G25S10PaaA1M27A3G1eA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3S0S15S20G1G22A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G1bA3A2S0S15S19S43S11N120A1G1bA3S0S15S19S43G1bS11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G6G9A3A1S0S15S1cGcS11ZffA1M28A2S0S15S20G5G15A2S0S15S1bS19S40S16S41GaG24A3G9A3A1S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M29G9A3A1S0S15S1cS1dS44S23S46G29S11Z77cb531A1A3S11Z1bA1A3GbA2S0S15S1cG27G28A2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT2_R1ns : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff (lfs LX_R1ns 2 SA_R1ns) ST2_R1ns) in exact x).
Definition RT2_R1ns__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sd0S1A5").
Definition RT2_R1ns : option (list leaf) := ltac:(let x := eval vm_compute in RT2_R1ns__f in exact x).
Lemma runT2_R1ns : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sd0S1A5S128A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT2_R1ns__f. Qed.
Definition LT2_R1ns : list leaf := ltac:(let x := eval vm_compute in (unopt RT2_R1ns) in exact x).
Lemma LT2_R1ns_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cSfcA4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R1sh : sstate := ltac2:(tb__ "0|22|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78MeA1MfA3G4A3S1aA5S0S17S18GfG3S11Z28M10A1S0S13S14G3G5GfA3S0S13S14G6G5GfA3S0S13S14S11Z10A1G5S3eP7bA1M11A3S0S13S14S11Z18A1Z4M12S3eP7cA1M13A3S0S13S14S11Z1cA1G12S3eP7dA1M14A3S0S13S14S11Z20A1M15G5S3eP7eA1M16A3G4A3A3A3A3A3A3S1aA5S0S17S18G11G6S11Z9A1S0S13S14G6Z1M17S3eP7fA1M18A3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G15G4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M19G16A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M1aS16S3fG1aS11G17A1A3S0S13S14G1aG17S3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3S0S15S20G0G12A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M1bG10A2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GfG3A3A1S0S15S1cG18S11ZffA1A2S0S15S20GeGaA2S0S15S1bS19S40S16S41G16G15A3G3A3A1S0S15S19S40S1eS1G19G13A3G3A3S0S15S1bS19S40S1eS1G19G14A3M1cG3A3A1S0S15S19S40G1cS1dS3fS1dS42S11G1bA1M1dG16A3S11ZffffffffffffffffA1M1eA3A3S0S15S1bS19S40S16S41S1dS3fS1dS42G1dG18A3G1eA3M1fG1cA3G3A3A1M20S0S15S1bS19S40S16S41G1cG1fA3G3A3A1M21S0S15S1cG13G3A2S0S15G21S0S15G20S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R1sh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5SbdS1A5").
Definition RA_R1sh : option (list leaf) := ltac:(let x := eval vm_compute in RA_R1sh__f in exact x).
Lemma runA_R1sh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5SbdS1A5S115A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R1sh__f. Qed.
Definition LA_R1sh : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R1sh) in exact x).
Lemma LA_R1sh_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSe9A4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R1shs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R1sh 0 SA_R1sh) in exact x).
Definition ST_R1sh : sstate := ltac2:(tb__ "0|28|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P78M5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P7fA1MaA3MbA3McS0S12S1eS1Q20MdS10P7dA1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18G6G9S11Z28A1S0S13S14S11Z18A1Z4M1fS16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G1fGfA3S0S13S14G9G19G6A3S0S13S14G1cG19G6A3S0S13S14S11Z10A1G19S10P7bA1M20A3S0S13S14S11Z20A1M21G19S10P7eA1M22A3G1bA3A3A3A3A3A3S1aA5S0S17S18G20G1cS11Z9A1S0S13S14G1cZ1M23GaA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G21G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG22A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M24S16S3fG24S11G23A1A3S0S13S14G24G23S10PaaA1M25A3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3S0S15S20G1G1fA2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G6G9A3A1S0S15S1cGaS11ZffA1M26A2S0S15S20G5G12A2S0S15S1bS19S40S16S41G22G21A3G9A3A1S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M27G9A3A1S0S15S1cS1dS44S23S46G27S11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG25G26A2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R1sh : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R1shs ST_R1sh) in exact x).
Definition RT_R1sh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sd2S1A5").
Definition RT_R1sh : option (list leaf) := ltac:(let x := eval vm_compute in RT_R1sh__f in exact x).
Lemma runT_R1sh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sd2S1A5S12aA3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R1sh__f. Qed.
Definition LT_R1sh : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R1sh) in exact x).
Lemma LT_R1sh_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cSfeA4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R2nh : sstate := ltac2:(tb__ "0|29|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78A1MeA3G4A3S1aA5S0S17S18GeG3S11Z28MfA1M10S0S13S14G3G5S3eP82M11A1M12A3S0S13S14G6G5G12A3S0S13S14S11Z10A1M13G5S3eP7bA1A3S0S13S14S11Z18A1M14Z4M15S3eP7cA1M16A3S0S13S14S11Z1cA1M17G15S3eP7dA1M18A3S0S13S14S11Z20A1M19G5S3eP7eA1A3G4A3A3A3A3A3A3S1aA5S0S17S18G12G3G10S0S13S14G3G5GeA3S0S13S14G6G5GeA3S0S13S14G13G5S3eP85A1M1aA3S0S13S14G14G15S3eP86A1M1bA3S0S13S14G17G15S3eP87A1M1cA3S0S13S14G19G5S3eP88A1M1dA3G4A3A3A3A3A3A3S1aA5S0S17S18G1aG6S11Z9A1S0S13S14G6Z1M1eS3eP89A1M1fA3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G19G4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M20G1dA3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M21S16S3fG21S11G1eA1A3S0S13S14G21G1eS3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3S0S15S20G0G15A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M22GfA2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GeG3A3A1S0S15S1bS19S40G12G3A3A1S0S15S1cG1fS11ZffA1A2S0S15S20G11GaA2S0S15S1bS19S40S16S41G1dG19A3G3A3A1S0S15S19S40S1eS1G20G16A3G3A3S0S15S1bS19S40S1eS1G20G18A3G3A3A1S0S15S19S47S1eS1G20G1cA3M23S1dS3fS1dS42S11G22A1M24G1dA3S11ZffffffffffffffffA1M25A3A3S0S15S1bS19S40S16S41S1dS3fS1dS42G24G1fA3G25A3M26G23A3G3A3A1M27S0S15S1bS19S40S16S41G23G26A3G3A3A1M28S0S15S1cG1bG3A2S0S15G28S0S15G27S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R2nh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5SbeS1A5").
Definition RA_R2nh : option (list leaf) := ltac:(let x := eval vm_compute in RA_R2nh__f in exact x).
Lemma runA_R2nh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5SbeS1A5S116A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R2nh__f. Qed.
Definition LA_R2nh : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R2nh) in exact x).
Lemma LA_R2nh_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSeaA4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R2nhs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R2nh 0 SA_R2nh) in exact x).
Definition ST_R2nh : sstate := ltac2:(tb__ "0|2c|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P82M5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P89A1MaA3MbA3McS0S12S1eS1Q20MdS10P87A1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18S10P78A1M1fG9S11Z28A1M20S0S13S14G9G19G6A3S0S13S14G1cG19G6A3S0S13S14S11Z10A1M21G19S10P7bA1A3S0S13S14S11Z18A1M22Z4M23S10P7cA1A3S0S13S14G8G23S10P7dA1A3S0S13S14S11Z20A1M24G19S10P7eA1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G6G9G20S0S13S14G22G23S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G23GfA3S0S13S14G9G19G1fA3S0S13S14G1cG19G1fA3S0S13S14G21G19S10P85A1M25A3S0S13S14G24G19S10P88A1M26A3G1bA3A3A3A3A3A3S1aA5S0S17S18G25G1cS11Z9A1S0S13S14G1cZ1M27GaA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G24G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG26A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M28S16S3fG28S11G27A1A3S0S13S14G28G27S10PaaA1M29A3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3S0S15S20G1G23A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G1fG9A3A1S0S15S1bS19S40G6G9A3A1S0S15S1cGaS11ZffA1M2aA2S0S15S20G5G12A2S0S15S1bS19S40S16S41G26G24A3G9A3A1S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M2bG9A3A1S0S15S1cS1dS44S23S46G2bS11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG29G2aA2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R2nh : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R2nhs ST_R2nh) in exact x).
Definition RT_R2nh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sd3S1A5").
Definition RT_R2nh : option (list leaf) := ltac:(let x := eval vm_compute in RT_R2nh__f in exact x).
Lemma runT_R2nh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sd3S1A5S12bA3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R2nh__f. Qed.
Definition LT_R2nh : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R2nh) in exact x).
Lemma LT_R2nh_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cSffA4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R2nr : sstate := ltac2:(tb__ "0|2d|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78MeA1MfA3G4A3S1aA5S0S17S18GfG3S11Z28M10A1M11S0S13S14G3G5S3eP82A1M12A3S0S13S14G6G5G12A3S0S13S14S11Z10A1M13G5S3eP7bA1M14A3S0S13S14S11Z18A1M15Z4M16S3eP7cA1M17A3S0S13S14S11Z1cA1M18G16S3eP7dA1M19A3S0S13S14S11Z20A1M1aG5S3eP7eA1M1bA3G4A3A3A3A3A3A3S1aA5S0S17S18G14G6S11Z9A1M1cS0S13S14G6Z1M1dS3eP7fA1M1eA3G4A3S1aA5S0S17S18G12G3G11S0S13S14G3G5GfA3S0S13S14G6G5GfA3S0S13S14G13G5S3eP85A1M1fA3S0S13S14G15G16S3eP86A1A3S0S13S14G18G16S3eP87A1M20A3S0S13S14G1aG5S3eP88A1M21A3G4A3A3A3A3A3A3S1aA5S0S17S18G1fG6G1cS0S13S14G6G1dS3eP89A1M22A3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G1aG4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M23G1bA3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M24S16S3fG24S11G1dA1A3S0S13S14G24G1dS3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3S0S15S20G0G16A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M25G10A2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GfG3A3A1S0S15S1cG1eS11ZffA1M26A2S0S15S20GeGaA2S0S15S1bS19S40G12G3A3A1S0S15S1cG22G26A2S0S15S1bS19S40S16S41G21G1aA3G3A3A1S0S15S1bS19S40GfG12A3A1S0S15S1bS19S40G12GfA3A1S0S15S19S40S1eS1G23G17A3G3A3S0S15S1bS19S40S1eS1G23G19A3M27G3A3A1S0S15S19S47S1eS1G23G20A3M28S1dS3fS1dS42S11G25A1M29G21A3S11ZffffffffffffffffA1M2aA3A3S0S15S19S40S16S41S1dS3fS1dS42G29G22A3G2aA3M2bG28A3G3A3S0S15S19S40S16S41G28G2bA3G3A3S0S15S1cG17G3A2S0S15S1bS19S40S16S41G27S1dS3fS1dS42G29G1eA3G2aA3M2cA3G3A3A1S0S15S1bS19S40S16S41G2cG27A3G3A3A1S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R2nr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5SbfS1A5").
Definition RA_R2nr : option (list leaf) := ltac:(let x := eval vm_compute in RA_R2nr__f in exact x).
Lemma runA_R2nr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5SbfS1A5S117A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R2nr__f. Qed.
Definition LA_R2nr : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R2nr) in exact x).
Lemma LA_R2nr_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSebA4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R2nrs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R2nr 0 SA_R2nr) in exact x).
Definition ST_R2nr : sstate := ltac2:(tb__ "0|30|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P78M5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P7fA1MaA3MbA3McS0S12S1eS1Q20MdS10P7dA1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18G6G9S11Z28A1M1fS0S13S14S11Z18A1M20Z4M21S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G21GfA3S0S13S14G9G19S10P82A1M22A3S0S13S14G1cG19G22A3S0S13S14S11Z10A1M23G19S10P7bA1M24A3S0S13S14S11Z20A1M25G19S10P7eA1M26A3G1bA3A3A3A3A3A3S1aA5S0S17S18G24G1cS11Z9A1M27S0S13S14G1cZ1M28GaA3G1bA3S1aA5S0S17S18G22G9G1fS0S13S14G9G19G6A3S0S13S14G1cG19G6A3S0S13S14G23G19S10P85A1M29A3S0S13S14G20G21S10P86A1A3S0S13S14G8G21S10P87A1A3S0S13S14G25G19S10P88A1M2aA3G1bA3A3A3A3A3A3S1aA5S0S17S18G29G1cG27S0S13S14G1cG28S10P89A1M2bA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G25G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG26A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M2cS16S3fG2cS11G28A1A3S0S13S14G2cG28S10PaaA1M2dA3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3S0S15S20G1G21A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G6G9A3A1S0S15S1cGaS11ZffA1M2eA2S0S15S20G5G12A2S0S15S1bS19S40G22G9A3A1S0S15S1cG2bG2eA2S0S15S1bS19S40S16S41G2aG25A3G9A3A1S0S15S1bS19S40G6G22A3A1S0S15S1bS19S40G22G6A3A1S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M2fG9A3A1S0S15S1cS1dS44S23S46G2fS11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG2dG2eA2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R2nr : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R2nrs ST_R2nr) in exact x).
Definition RT_R2nr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sd4S1A5").
Definition RT_R2nr : option (list leaf) := ltac:(let x := eval vm_compute in RT_R2nr__f in exact x).
Lemma runT_R2nr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sd4S1A5S12cA3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R2nr__f. Qed.
Definition LT_R2nr : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R2nr) in exact x).
Lemma LT_R2nr_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cS100A4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R2sh : sstate := ltac2:(tb__ "0|29|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78MeA1MfA3G4A3S1aA5S0S17S18GfG3S11Z28M10A1M11S0S13S14G3G5S3eP82A1M12A3S0S13S14G6G5G12A3S0S13S14S11Z10A1M13G5S3eP7bA1M14A3S0S13S14S11Z18A1M15Z4M16S3eP7cA1M17A3S0S13S14S11Z1cA1M18G16S3eP7dA1M19A3S0S13S14S11Z20A1M1aG5S3eP7eA1M1bA3G4A3A3A3A3A3A3S1aA5S0S17S18G14G6S11Z9A1S0S13S14G6Z1M1cS3eP7fA1M1dA3G4A3S1aA5S0S17S18G12G3G11S0S13S14G3G5GfA3S0S13S14G6G5GfA3S0S13S14G13G5S3eP85A1A3S0S13S14G15G16S3eP86A1A3S0S13S14G18G16S3eP87A1M1eA3S0S13S14G1aG5S3eP88A1M1fA3G4A3A3A3A3A3A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G1aG4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M20G1bA3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M21S16S3fG21S11G1cA1A3S0S13S14G21G1cS3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3S0S15S20G0G16A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M22G10A2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GfG3A3A1S0S15S1cG1dS11ZffA1A2S0S15S20GeGaA2S0S15S1bS19S40G12G3A3A1S0S15S1bS19S40S16S41G1fG1aA3G3A3A1S0S15S19S40S1eS1G20G17A3G3A3S0S15S1bS19S40S1eS1G20G19A3M23G3A3A1S0S15S19S40S1eS1G20G1eA3S1dS3fS1dS42S11G22A1M24G1fA3S11ZffffffffffffffffA1M25A3A3S0S15S1bS19S40S16S41S1dS3fS1dS42G24G1dA3G25A3M26G23A3G3A3A1M27S0S15S1bS19S40S16S41G23G26A3G3A3A1M28S0S15S1cG17G3A2S0S15G28S0S15G27S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R2sh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sc0S1A5").
Definition RA_R2sh : option (list leaf) := ltac:(let x := eval vm_compute in RA_R2sh__f in exact x).
Lemma runA_R2sh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sc0S1A5S118A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R2sh__f. Qed.
Definition LA_R2sh : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R2sh) in exact x).
Lemma LA_R2sh_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSecA4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R2shs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R2sh 0 SA_R2sh) in exact x).
Definition ST_R2sh : sstate := ltac2:(tb__ "0|2d|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P78M5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P7fA1MaA3MbA3McS0S12S1eS1Q20MdS10P7dA1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18G6G9S11Z28A1M1fS0S13S14S11Z18A1M20Z4M21S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G21GfA3S0S13S14G9G19S10P82A1M22A3S0S13S14G1cG19G22A3S0S13S14S11Z10A1M23G19S10P7bA1M24A3S0S13S14S11Z20A1M25G19S10P7eA1M26A3G1bA3A3A3A3A3A3S1aA5S0S17S18G24G1cS11Z9A1S0S13S14G1cZ1M27GaA3G1bA3S1aA5S0S17S18G22G9G1fS0S13S14G9G19G6A3S0S13S14G1cG19G6A3S0S13S14G23G19S10P85A1A3S0S13S14G20G21S10P86A1A3S0S13S14G8G21S10P87A1A3S0S13S14G25G19S10P88A1M28A3G1bA3A3A3A3A3A3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G25G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG26A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M29S16S3fG29S11G27A1A3S0S13S14G29G27S10PaaA1M2aA3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3S0S15S20G1G21A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G6G9A3A1S0S15S1cGaS11ZffA1M2bA2S0S15S20G5G12A2S0S15S1bS19S40G22G9A3A1S0S15S1bS19S40S16S41G28G25A3G9A3A1S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M2cG9A3A1S0S15S1cS1dS44S23S46G2cS11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG2aG2bA2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R2sh : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R2shs ST_R2sh) in exact x).
Definition RT_R2sh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sd5S1A5").
Definition RT_R2sh : option (list leaf) := ltac:(let x := eval vm_compute in RT_R2sh__f in exact x).
Lemma runT_R2sh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sd5S1A5S12dA3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R2sh__f. Qed.
Definition LT_R2sh : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R2sh) in exact x).
Lemma LT_R2sh_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cS101A4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R2sr : sstate := ltac2:(tb__ "0|2d|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78A1MeA3G4A3S1aA5S0S17S18GeG3S11Z28MfA1M10S0S13S14G3G5S3eP82M11A1M12A3S0S13S14G6G5G12A3S0S13S14S11Z10A1M13G5S3eP7bA1M14A3S0S13S14S11Z18A1M15Z4M16S3eP7cA1M17A3S0S13S14S11Z1cA1M18G16S3eP7dA1M19A3S0S13S14S11Z20A1M1aG5S3eP7eA1A3G4A3A3A3A3A3A3S1aA5S0S17S18G14G6S11Z9A1M1bS0S13S14G6Z1M1cS3eP7fA1M1dA3G4A3S1aA5S0S17S18G12G3G10S0S13S14G3G5GeA3S0S13S14G6G5GeA3S0S13S14G13G5S3eP85A1M1eA3S0S13S14G15G16S3eP86A1M1fA3S0S13S14G18G16S3eP87A1M20A3S0S13S14G1aG5S3eP88A1M21A3G4A3A3A3A3A3A3S1aA5S0S17S18G1eG6G1bS0S13S14G6G1cS3eP89A1M22A3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G1aG4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M23G21A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M24S16S3fG24S11G1cA1A3S0S13S14G24G1cS3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3S0S15S20G0G16A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M25GfA2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GeG3A3A1S0S15S1cG1dS11ZffA1M26A2S0S15S1bS19S40G12G3A3A1S0S15S1cG22G26A2S0S15S20G11GaA2S0S15S1bS19S40S16S41G21G1aA3G3A3A1S0S15S1bS19S40G12GeA3A1S0S15S1bS19S40GeG12A3A1S0S15S19S40S1eS1G23G17A3G3A3S0S15S1bS19S40S1eS1G23G19A3M27G3A3A1S0S15S19S40S1eS1G23G20A3M28S1dS3fS1dS42S11G25A1M29G21A3S11ZffffffffffffffffA1M2aA3A3S0S15S19S40S16S41S1dS3fS1dS42G29G1dA3G2aA3M2bG27A3G3A3S0S15S19S40S16S41G27G2bA3G3A3S0S15S1cG1fG3A2S0S15S1bS19S40S16S41G28S1dS3fS1dS42G29G22A3G2aA3M2cA3G3A3A1S0S15S1bS19S40S16S41G2cG28A3G3A3A1S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R2sr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sc1S1A5").
Definition RA_R2sr : option (list leaf) := ltac:(let x := eval vm_compute in RA_R2sr__f in exact x).
Lemma runA_R2sr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sc1S1A5S119A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R2sr__f. Qed.
Definition LA_R2sr : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R2sr) in exact x).
Lemma LA_R2sr_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSedA4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R2srs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R2sr 0 SA_R2sr) in exact x).
Definition ST_R2sr : sstate := ltac2:(tb__ "0|2f|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P82M5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P89A1MaA3MbA3McS0S12S1eS1Q20MdS10P87A1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18S10P78A1M1fG9S11Z28A1M20S0S13S14G9G19G6A3S0S13S14G1cG19G6A3S0S13S14S11Z10A1M21G19S10P7bA1M22A3S0S13S14S11Z18A1M23Z4M24S10P7cA1A3S0S13S14G8G24S10P7dA1A3S0S13S14S11Z20A1M25G19S10P7eA1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G22G1cS11Z9A1M26S0S13S14G1cZ1M27S10P7fA1M28A3G1bA3S1aA5S0S17S18G6G9G20S0S13S14G23G24S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G24GfA3S0S13S14G9G19G1fA3S0S13S14G1cG19G1fA3S0S13S14G21G19S10P85A1M29A3S0S13S14G25G19S10P88A1M2aA3G1bA3A3A3A3A3A3S1aA5S0S17S18G29G1cG26S0S13S14G1cG27GaA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G25G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG2aA3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M2bS16S3fG2bS11G27A1A3S0S13S14G2bG27S10PaaA1M2cA3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3S0S15S20G1G24A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G1fG9A3A1S0S15S1cG28S11ZffA1M2dA2S0S15S1bS19S40G6G9A3A1S0S15S1cGaG2dA2S0S15S20G5G12A2S0S15S1bS19S40S16S41G2aG25A3G9A3A1S0S15S1bS19S40G6G1fA3A1S0S15S1bS19S40G1fG6A3A1S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M2eG9A3A1S0S15S1cS1dS44S23S46G2eS11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG2cG2dA2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R2sr : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R2srs ST_R2sr) in exact x).
Definition RT_R2sr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sd6S1A5").
Definition RT_R2sr : option (list leaf) := ltac:(let x := eval vm_compute in RT_R2sr__f in exact x).
Lemma runT_R2sr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sd6S1A5S12eA3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R2sr__f. Qed.
Definition LT_R2sr : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R2sr) in exact x).
Lemma LT_R2sr_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cS102A4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R3nh : sstate := ltac2:(tb__ "0|2a|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78A1MeA3G4A3S1aA5S0S17S18GeG3S11Z28MfA1M10S0S13S14G3G5S3eP8cA1M11A3S0S13S14G6G5S3eP82M12A1M13A3S0S13S14S11Z10A1M14G5S3eP7bA1A3S0S13S14S11Z18A1M15Z4M16S3eP7cA1M17A3S0S13S14S11Z1cA1M18G16S3eP7dA1M19A3S0S13S14S11Z20A1M1aG5S3eP7eA1A3G4A3A3A3A3A3A3S1aA5S0S17S18G13G3G10S0S13S14G3G5GeA3S0S13S14G6G5G11A3S0S13S14G14G5S3eP85A1M1bA3S0S13S14G15G16S3eP86A1M1cA3S0S13S14G18G16S3eP87A1M1dA3S0S13S14G1aG5S3eP88A1M1eA3G4A3A3A3A3A3A3S1aA5S0S17S18G1bG6S11Z9A1S0S13S14G6Z1M1fS3eP89A1M20A3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G1aG4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M21G1eA3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M22S16S3fG22S11G1fA1A3S0S13S14G22G1fS3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3S0S15S20G0G16A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M23GfA2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GeG3A3A1S0S15S1bS19S40G13G3A3A1S0S15S1cG20S11ZffA1A2S0S15S20G12GaA2S0S15S1bS19S40S16S41G1eG1aA3G3A3A1S0S15S19S40S1eS1G21G17A3G3A3S0S15S1bS19S40S1eS1G21G19A3G3A3A1S0S15S19S47S1eS1G21G1dA3M24S1dS3fS1dS42S11G23A1M25G1eA3S11ZffffffffffffffffA1M26A3A3S0S15S1bS19S40S16S41S1dS3fS1dS42G25G20A3G26A3M27G24A3G3A3A1M28S0S15S1bS19S40S16S41G24G27A3G3A3A1M29S0S15S1cG1cG3A2S0S15G29S0S15G28S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R3nh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sc2S1A5").
Definition RA_R3nh : option (list leaf) := ltac:(let x := eval vm_compute in RA_R3nh__f in exact x).
Lemma runA_R3nh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sc2S1A5S11aA3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R3nh__f. Qed.
Definition LA_R3nh : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R3nh) in exact x).
Lemma LA_R3nh_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSeeA4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R3nhs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R3nh 0 SA_R3nh) in exact x).
Definition ST_R3nh : sstate := ltac2:(tb__ "0|2d|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P82M5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P89A1MaA3MbA3McS0S12S1eS1Q20MdS10P87A1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18S10P78A1M1fG9S11Z28A1M20S0S13S14G9G19S10P8cA1M21A3S0S13S14G1cG19G6A3S0S13S14S11Z10A1M22G19S10P7bA1A3S0S13S14S11Z18A1M23Z4M24S10P7cA1A3S0S13S14G8G24S10P7dA1A3S0S13S14S11Z20A1M25G19S10P7eA1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G6G9G20S0S13S14G23G24S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G24GfA3S0S13S14G9G19G1fA3S0S13S14G1cG19G21A3S0S13S14G22G19S10P85A1M26A3S0S13S14G25G19S10P88A1M27A3G1bA3A3A3A3A3A3S1aA5S0S17S18G26G1cS11Z9A1S0S13S14G1cZ1M28GaA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G25G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG27A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M29S16S3fG29S11G28A1A3S0S13S14G29G28S10PaaA1M2aA3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3S0S15S20G1G24A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G1fG9A3A1S0S15S1bS19S40G6G9A3A1S0S15S1cGaS11ZffA1M2bA2S0S15S20G5G12A2S0S15S1bS19S40S16S41G27G25A3G9A3A1S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M2cG9A3A1S0S15S1cS1dS44S23S46G2cS11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG2aG2bA2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R3nh : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R3nhs ST_R3nh) in exact x).
Definition RT_R3nh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sd7S1A5").
Definition RT_R3nh : option (list leaf) := ltac:(let x := eval vm_compute in RT_R3nh__f in exact x).
Lemma runT_R3nh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sd7S1A5S12fA3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R3nh__f. Qed.
Definition LT_R3nh : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R3nh) in exact x).
Lemma LT_R3nh_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cS103A4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R3nr : sstate := ltac2:(tb__ "0|30|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78A1MeA3G4A3S1aA5S0S17S18GeG3S11Z28MfA1M10S0S13S14G3G5S3eP8cM11A1M12A3S0S13S14G6G5S3eP82A1M13A3S0S13S14S11Z10A1M14G5S3eP7bA1A3S0S13S14S11Z18A1M15Z4M16S3eP7cA1M17A3S0S13S14S11Z1cA1M18G16S3eP7dA1M19A3S0S13S14S11Z20A1M1aG5S3eP7eA1A3G4A3A3A3A3A3A3S1aA5S0S17S18G13G3G10S0S13S14G3G5GeA3S0S13S14G6G5G12A3S0S13S14G14G5S3eP85A1M1bA3S0S13S14G15G16S3eP86A1A3S0S13S14G18G16S3eP87A1M1cA3S0S13S14G1aG5S3eP88A1M1dA3G4A3A3A3A3A3A3S1aA5S0S17S18G1bG6S11Z9A1M1eS0S13S14G6Z1M1fS3eP89A1M20A3G4A3S1aA5S0S17S18G12G3G10S0S13S14G3G5G13A3S0S13S14G6G5GeA3S0S13S14G14G5S3eP8fA1M21A3S0S13S14G15G16S3eP90A1M22A3S0S13S14G18G16S3eP91A1M23A3S0S13S14G1aG5S3eP92A1M24A3G4A3A3A3A3A3A3S1aA5S0S17S18G21G6G1eS0S13S14G6G1fS3eP93A1M25A3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G1aG4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M26G24A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M27S16S3fG27S11G1fA1A3S0S13S14G27G1fS3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3A3S0S15S20G0G16A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M28GfA2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GeG3A3A1S0S15S1bS19S40G13G3A3A1S0S15S1cG20S11ZffA1M29A2S0S15S1bS19S40S16S41G1dG1aA3G3A3A1S0S15S1bS19S40G12G3A3A1S0S15S1cG25G29A2S0S15S20G11GaA2S0S15S1bS19S40G12G13A3A1S0S15S1bS19S40G13G12A3A1S0S15S19S40S1eS1G26G17A3G3A3S0S15S1bS19S40S1eS1G26G19A3G3A3A1S0S15S19S47S1eS1G26G1cA3M2aS1dS3fS1dS42S11G28A1M2bG1dA3S11ZffffffffffffffffA1M2cA3A3S0S15S19S40S16S41S1dS3fS1dS42G2bG20A3G2cA3M2dG2aA3G3A3S0S15S19S40S16S41G2aG2dA3G3A3S0S15S1cG22G3A2S0S15S1bS19S40S16S41S1eS1G26G23A3M2eS1dS3fS1dS42G2bG25A3G2cA3M2fA3G3A3A1S0S15S1bS19S40S16S41G2fG2eA3G3A3A1S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R3nr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sc3S1A5").
Definition RA_R3nr : option (list leaf) := ltac:(let x := eval vm_compute in RA_R3nr__f in exact x).
Lemma runA_R3nr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sc3S1A5S11bA3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R3nr__f. Qed.
Definition LA_R3nr : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R3nr) in exact x).
Lemma LA_R3nr_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSefA4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R3nrs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R3nr 0 SA_R3nr) in exact x).
Definition ST_R3nr : sstate := ltac2:(tb__ "0|31|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P8cM5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P93A1MaA3MbA3McS0S12S1eS1Q20MdS10P91A1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18S10P78A1M1fG9S11Z28A1M20S0S13S14G9G19G6A3S0S13S14G1cG19S10P82A1M21A3S0S13S14S11Z10A1M22G19S10P7bA1A3S0S13S14S11Z18A1M23Z4M24S10P7cA1A3S0S13S14G8G24S10P7dA1A3S0S13S14S11Z20A1M25G19S10P7eA1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G21G9G20S0S13S14G9G19G1fA3S0S13S14G1cG19G6A3S0S13S14G22G19S10P85A1M26A3S0S13S14G23G24S10P86A1A3S0S13S14G8G24S10P87A1A3S0S13S14G25G19S10P88A1M27A3G1bA3A3A3A3A3A3S1aA5S0S17S18G26G1cS11Z9A1M28S0S13S14G1cZ1M29S10P89A1M2aA3G1bA3S1aA5S0S17S18G6G9G20S0S13S14G23G24S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G24GfA3S0S13S14G9G19G21A3S0S13S14G1cG19G1fA3S0S13S14G22G19S10P8fA1M2bA3S0S13S14G25G19S10P92A1M2cA3G1bA3A3A3A3A3A3S1aA5S0S17S18G2bG1cG28S0S13S14G1cG29GaA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G25G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG2cA3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M2dS16S3fG2dS11G29A1A3S0S13S14G2dG29S10PaaA1M2eA3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3A3S0S15S20G1G24A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G1fG9A3A1S0S15S1bS19S40G21G9A3A1S0S15S1cG2aS11ZffA1M2fA2S0S15S1bS19S40S16S41G27G25A3G9A3A1S0S15S1bS19S40G6G9A3A1S0S15S1cGaG2fA2S0S15S20G5G12A2S0S15S1bS19S40G6G21A3A1S0S15S1bS19S40G21G6A3A1S0S15S1bS19S40G7G9A3A1
S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M30G9A3A1S0S15S1cS1dS44S23S46G30S11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG2eG2fA2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R3nr : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R3nrs ST_R3nr) in exact x).
Definition RT_R3nr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sd8S1A5").
Definition RT_R3nr : option (list leaf) := ltac:(let x := eval vm_compute in RT_R3nr__f in exact x).
Lemma runT_R3nr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sd8S1A5S130A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R3nr__f. Qed.
Definition LT_R3nr : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R3nr) in exact x).
Lemma LT_R3nr_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cS104A4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R3sh : sstate := ltac2:(tb__ "0|2c|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78A1MeA3G4A3S1aA5S0S17S18GeG3S11Z28MfA1M10S0S13S14G3G5S3eP8cM11A1M12A3S0S13S14G6G5S3eP82A1M13A3S0S13S14S11Z10A1M14G5S3eP7bA1A3S0S13S14S11Z18A1M15Z4M16S3eP7cA1M17A3S0S13S14S11Z1cA1M18G16S3eP7dA1M19A3S0S13S14S11Z20A1M1aG5S3eP7eA1A3G4A3A3A3A3A3A3S1aA5S0S17S18G13G3G10S0S13S14G3G5GeA3S0S13S14G6G5G12A3S0S13S14G14G5S3eP85A1A3S0S13S14G15G16S3eP86A1A3S0S13S14G18G16S3eP87A1M1bA3S0S13S14G1aG5S3eP88A1M1cA3G4A3A3A3A3A3A3S1aA5S0S17S18G12G3G10S0S13S14G3G5G13A3S0S13S14G6G5GeA3S0S13S14G14G5S3eP8fA1M1dA3S0S13S14G15G16S3eP90A1M1eA3S0S13S14G18G16S3eP91A1M1fA3S0S13S14G1aG5S3eP92A1M20A3G4A3A3A3A3A3A3S1aA5S0S17S18G1dG6S11Z9A1S0S13S14G6Z1M21S3eP93A1M22A3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G1aG4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M23G20A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M24S16S3fG24S11G21A1A3S0S13S14G24G21S3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3S0S15S20G0G16A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M25GfA2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GeG3A3A1S0S15S1bS19S40G13G3A3A1S0S15S1bS19S40S16S41G1cG1aA3G3A3A1S0S15S1bS19S40G12G3A3A1S0S15S1cG22S11ZffA1A2S0S15S20G11GaA2S0S15S19S40S1eS1G23G17A3G3A3S0S15S1bS19S40S1eS1G23G19A3G3A3A1S0S15S19S40S1eS1G23G1bA3S1dS3fS1dS42S11G25A1M26G1cA3S11ZffffffffffffffffA1M27A3A3S0S15S1bS19S40S16S41S1dS3fS1dS42G26G22A3G27A3M28S1eS1G23G1fA3M29A3G3A3A1M2aS0S15S1bS19S40S16S41G29G28A3G3A3A1M2bS0S15S1cG1eG3A2S0S15G2bS0S15G2aS2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R3sh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sc4S1A5").
Definition RA_R3sh : option (list leaf) := ltac:(let x := eval vm_compute in RA_R3sh__f in exact x).
Lemma runA_R3sh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sc4S1A5S11cA3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R3sh__f. Qed.
Definition LA_R3sh : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R3sh) in exact x).
Lemma LA_R3sh_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSf0A4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R3shs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R3sh 0 SA_R3sh) in exact x).
Definition ST_R3sh : sstate := ltac2:(tb__ "0|2e|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P8cM5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P93A1MaA3MbA3McS0S12S1eS1Q20MdS10P91A1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18S10P78A1M1fG9S11Z28A1M20S0S13S14G9G19G6A3S0S13S14G1cG19S10P82A1M21A3S0S13S14S11Z10A1M22G19S10P7bA1A3S0S13S14S11Z18A1M23Z4M24S10P7cA1A3S0S13S14G8G24S10P7dA1A3S0S13S14S11Z20A1M25G19S10P7eA1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G21G9G20S0S13S14G9G19G1fA3S0S13S14G1cG19G6A3S0S13S14G22G19S10P85A1A3S0S13S14G23G24S10P86A1A3S0S13S14G8G24S10P87A1A3S0S13S14G25G19S10P88A1M26A3G1bA3A3A3A3A3A3S1aA5S0S17S18G6G9G20S0S13S14G23G24S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G24GfA3S0S13S14G9G19G21A3S0S13S14G1cG19G1fA3S0S13S14G22G19S10P8fA1M27A3S0S13S14G25G19S10P92A1M28A3G1bA3A3A3A3A3A3S1aA5S0S17S18G27G1cS11Z9A1S0S13S14G1cZ1M29GaA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G25G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG28A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M2aS16S3fG2aS11G29A1A3S0S13S14G2aG29S10PaaA1M2bA3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3S0S15S20G1G24A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G1fG9A3A1S0S15S1bS19S40G21G9A3A1S0S15S1bS19S40S16S41G26G25A3G9A3A1S0S15S1bS19S40G6G9A3A1S0S15S1cGaS11ZffA1M2cA2S0S15S20G5G12A2S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M2dG9A3A1S0S15S1cS1dS44S23S46G2dS11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG2bG2cA2S2S15
A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R3sh : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R3shs ST_R3sh) in exact x).
Definition RT_R3sh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sd9S1A5").
Definition RT_R3sh : option (list leaf) := ltac:(let x := eval vm_compute in RT_R3sh__f in exact x).
Lemma runT_R3sh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sd9S1A5S131A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R3sh__f. Qed.
Definition LT_R3sh : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R3sh) in exact x).
Lemma LT_R3sh_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cS105A4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R3sr : sstate := ltac2:(tb__ "0|2f|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78MeA1MfA3G4A3S1aA5S0S17S18GfG3S11Z28M10A1M11S0S13S14G3G5S3eP8cA1M12A3S0S13S14G6G5S3eP82A1M13A3S0S13S14S11Z10A1M14G5S3eP7bA1M15A3S0S13S14S11Z18A1M16Z4M17S3eP7cA1M18A3S0S13S14S11Z1cA1M19G17S3eP7dA1M1aA3S0S13S14S11Z20A1M1bG5S3eP7eA1M1cA3G4A3A3A3A3A3A3S1aA5S0S17S18G15G6S11Z9A1M1dS0S13S14G6Z1M1eS3eP7fA1M1fA3G4A3S1aA5S0S17S18G13G3G11S0S13S14G3G5GfA3S0S13S14G6G5G12A3S0S13S14G14G5S3eP85A1A3S0S13S14G16G17S3eP86A1A3S0S13S14G19G17S3eP87A1M20A3S0S13S14G1bG5S3eP88A1M21A3G4A3A3A3A3A3A3S1aA5S0S17S18G12G3G11S0S13S14G3G5G13A3S0S13S14G6G5GfA3S0S13S14G14G5S3eP8fA1M22A3S0S13S14G16G17S3eP90A1A3S0S13S14G19G17S3eP91A1M23A3S0S13S14G1bG5S3eP92A1A3G4A3A3A3A3A3A3S1aA5S0S17S18G22G6G1dS0S13S14G6G1eS3eP93A1M24A3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G1bG4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M25G1cA3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M26S16S3fG26S11G1eA1A3S0S13S14G26G1eS3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3A3S0S15S20G0G17A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M27G10A2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GfG3A3A1S0S15S1cG1fS11ZffA1M28A2S0S15S20GeGaA2S0S15S1bS19S40G13G3A3A1S0S15S1bS19S40S16S41G21G1bA3G3A3A1S0S15S1bS19S40G12G3A3A1S0S15S1cG24G28A2S0S15S1bS19S40GfG12A3A1S0S15S1bS19S40G12GfA3A1S0S15S19S40S1eS1G25G18A3G3A3S0S15S1bS19S40S1eS1G25G1aA3M29G3A3A1S0S15S19S40S1eS1G25G20A3S1dS3fS1dS42S11G27A1M2aG21A3S11ZffffffffffffffffA1M2bA3A3S0S15S19S40S16S41S1dS3fS1dS42G2aG24A3G2bA3M2cS1eS1G25G23A3M2dA3G3A3S0S15S19S40S16S41G2dG2cA3G3A3S0S15S1cG18G3A2S0S15S1bS19S40S16S41G29S1dS3fS1dS42G2aG1fA3G2bA3M2eA3G3A3A1S0S15S1bS19S40S16S41G2eG29A3G3A3A1S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R3sr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sc5S1A5").
Definition RA_R3sr : option (list leaf) := ltac:(let x := eval vm_compute in RA_R3sr__f in exact x).
Lemma runA_R3sr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sc5S1A5S11dA3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R3sr__f. Qed.
Definition LA_R3sr : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R3sr) in exact x).
Lemma LA_R3sr_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSf1A4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R3srs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R3sr 0 SA_R3sr) in exact x).
Definition ST_R3sr : sstate := ltac2:(tb__ "0|31|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P78M5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P7fA1MaA3MbA3McS0S12S1eS1Q20MdS10P7dA1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18G6G9S11Z28A1M1fS0S13S14S11Z18A1M20Z4M21S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G21GfA3S0S13S14G9G19S10P8cA1M22A3S0S13S14G1cG19S10P82A1M23A3S0S13S14S11Z10A1M24G19S10P7bA1M25A3S0S13S14S11Z20A1M26G19S10P7eA1M27A3G1bA3A3A3A3A3A3S1aA5S0S17S18G25G1cS11Z9A1M28S0S13S14G1cZ1M29GaA3G1bA3S1aA5S0S17S18G23G9G1fS0S13S14G9G19G6A3S0S13S14G1cG19G22A3S0S13S14G24G19S10P85A1A3S0S13S14G20G21S10P86A1A3S0S13S14G8G21S10P87A1A3S0S13S14G26G19S10P88A1M2aA3G1bA3A3A3A3A3A3S1aA5S0S17S18G22G9G1fS0S13S14G9G19G23A3S0S13S14G1cG19G6A3S0S13S14G24G19S10P8fA1M2bA3S0S13S14G20G21S10P90A1A3S0S13S14G8G21S10P91A1A3S0S13S14G26G19S10P92A1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G2bG1cG28S0S13S14G1cG29S10P93A1M2cA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G26G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG27A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M2dS16S3fG2dS11G29A1A3S0S13S14G2dG29S10PaaA1M2eA3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3A3S0S15S20G1G21A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G6G9A3A1S0S15S1cGaS11ZffA1M2fA2S0S15S20G5G12A2S0S15S1bS19S40G23G9A3A1S0S15S1bS19S40S16S41G2aG26A3G9A3A1S0S15S1bS19S40G22G9A3A1S0S15S1cG2cG2fA2S0S15S1bS19S40G6G22A3A1S0S15S1bS19S40G22G6A3A1S0S15S1bS19S40G7G9A3A1
S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M30G9A3A1S0S15S1cS1dS44S23S46G30S11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG2eG2fA2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R3sr : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R3srs ST_R3sr) in exact x).
Definition RT_R3sr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5SdaS1A5").
Definition RT_R3sr : option (list leaf) := ltac:(let x := eval vm_compute in RT_R3sr__f in exact x).
Lemma runT_R3sr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5SdaS1A5S132A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R3sr__f. Qed.
Definition LT_R3sr : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R3sr) in exact x).
Lemma LT_R3sr_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cS106A4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R4nh : sstate := ltac2:(tb__ "0|29|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78A1MeA3G4A3S1aA5S0S17S18GeG3S11Z28MfA1M10S0S13S14G3G5S3eP96A1A3S0S13S14G6G5S3eP82M11A1M12A3S0S13S14S11Z10A1M13G5S3eP7bA1A3S0S13S14S11Z18A1M14Z4M15S3eP7cA1M16A3S0S13S14S11Z1cA1M17G15S3eP7dA1M18A3S0S13S14S11Z20A1M19G5S3eP7eA1A3G4A3A3A3A3A3A3S1aA5S0S17S18G12G3G10S0S13S14G3G5GeA3S0S13S14G6G5S3eP8cA1A3S0S13S14G13G5S3eP85A1M1aA3S0S13S14G14G15S3eP86A1M1bA3S0S13S14G17G15S3eP87A1M1cA3S0S13S14G19G5S3eP88A1M1dA3G4A3A3A3A3A3A3S1aA5S0S17S18G1aG6S11Z9A1S0S13S14G6Z1M1eS3eP89A1M1fA3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G19G4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M20G1dA3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M21S16S3fG21S11G1eA1A3S0S13S14G21G1eS3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3S0S15S20G0G15A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M22GfA2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GeG3A3A1S0S15S1bS19S40G12G3A3A1S0S15S1cG1fS11ZffA1A2S0S15S20G11GaA2S0S15S1bS19S40S16S41G1dG19A3G3A3A1S0S15S19S40S1eS1G20G16A3G3A3S0S15S1bS19S40S1eS1G20G18A3G3A3A1S0S15S19S47S1eS1G20G1cA3M23S1dS3fS1dS42S11G22A1M24G1dA3S11ZffffffffffffffffA1M25A3A3S0S15S1bS19S40S16S41S1dS3fS1dS42G24G1fA3G25A3M26G23A3G3A3A1M27S0S15S1bS19S40S16S41G23G26A3G3A3A1M28S0S15S1cG1bG3A2S0S15G28S0S15G27S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R4nh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sc6S1A5").
Definition RA_R4nh : option (list leaf) := ltac:(let x := eval vm_compute in RA_R4nh__f in exact x).
Lemma runA_R4nh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sc6S1A5S11eA3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R4nh__f. Qed.
Definition LA_R4nh : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R4nh) in exact x).
Lemma LA_R4nh_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSf2A4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R4nhs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R4nh 0 SA_R4nh) in exact x).
Definition ST_R4nh : sstate := ltac2:(tb__ "0|2c|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P82M5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P89A1MaA3MbA3McS0S12S1eS1Q20MdS10P87A1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18S10P78A1M1fG9S11Z28A1M20S0S13S14G9G19S10P96A1A3S0S13S14G1cG19G6A3S0S13S14S11Z10A1M21G19S10P7bA1A3S0S13S14S11Z18A1M22Z4M23S10P7cA1A3S0S13S14G8G23S10P7dA1A3S0S13S14S11Z20A1M24G19S10P7eA1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G6G9G20S0S13S14G22G23S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G23GfA3S0S13S14G9G19G1fA3S0S13S14G1cG19S10P8cA1A3S0S13S14G21G19S10P85A1M25A3S0S13S14G24G19S10P88A1M26A3G1bA3A3A3A3A3A3S1aA5S0S17S18G25G1cS11Z9A1S0S13S14G1cZ1M27GaA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G24G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG26A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M28S16S3fG28S11G27A1A3S0S13S14G28G27S10PaaA1M29A3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3S0S15S20G1G23A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G1fG9A3A1S0S15S1bS19S40G6G9A3A1S0S15S1cGaS11ZffA1M2aA2S0S15S20G5G12A2S0S15S1bS19S40S16S41G26G24A3G9A3A1S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M2bG9A3A1S0S15S1cS1dS44S23S46G2bS11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG29G2aA2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R4nh : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R4nhs ST_R4nh) in exact x).
Definition RT_R4nh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5SdbS1A5").
Definition RT_R4nh : option (list leaf) := ltac:(let x := eval vm_compute in RT_R4nh__f in exact x).
Lemma runT_R4nh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5SdbS1A5S133A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R4nh__f. Qed.
Definition LT_R4nh : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R4nh) in exact x).
Lemma LT_R4nh_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cS107A4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R4nr : sstate := ltac2:(tb__ "0|31|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78A1MeA3G4A3S1aA5S0S17S18GeG3S11Z28MfA1M10S0S13S14G3G5S3eP96A1M11A3S0S13S14G6G5S3eP82A1M12A3S0S13S14S11Z10A1M13G5S3eP7bA1A3S0S13S14S11Z18A1M14Z4M15S3eP7cA1M16A3S0S13S14S11Z1cA1M17G15S3eP7dA1M18A3S0S13S14S11Z20A1M19G5S3eP7eA1A3G4A3A3A3A3A3A3S1aA5S0S17S18G12G3G10S0S13S14G3G5GeA3S0S13S14G6G5S3eP8cM1aA1M1bA3S0S13S14G13G5S3eP85A1M1cA3S0S13S14G14G15S3eP86A1A3S0S13S14G17G15S3eP87A1M1dA3S0S13S14G19G5S3eP88A1M1eA3G4A3A3A3A3A3A3S1aA5S0S17S18G1cG6S11Z9A1M1fS0S13S14G6Z1M20S3eP89A1M21A3G4A3S1aA5S0S17S18G1bG3G10S0S13S14G3G5G12A3S0S13S14G6G5G11A3S0S13S14G13G5S3eP8fA1M22A3S0S13S14G14G15S3eP90A1M23A3S0S13S14G17G15S3eP91A1M24A3S0S13S14G19G5S3eP92A1M25A3G4A3A3A3A3A3A3S1aA5S0S17S18G22G6G1fS0S13S14G6G20S3eP93A1M26A3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G19G4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M27G25A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M28S16S3fG28S11G20A1A3S0S13S14G28G20S3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3A3S0S15S20G0G15A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M29GfA2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GeG3A3A1S0S15S1bS19S40G12G3A3A1S0S15S1cG21S11ZffA1M2aA2S0S15S1bS19S40S16S41G1eG19A3G3A3A1S0S15S1bS19S40G1bG3A3A1S0S15S1cG26G2aA2S0S15S20G1aGaA2S0S15S1bS19S40G1bG12A3A1S0S15S1bS19S40G12G1bA3A1S0S15S19S40S1eS1G27G16A3G3A3S0S15S1bS19S40S1eS1G27G18A3G3A3A1S0S15S19S47S1eS1G27G1dA3M2bS1dS3fS1dS42S11G29A1M2cG1eA3S11ZffffffffffffffffA1M2dA3A3S0S15S19S40S16S41S1dS3fS1dS42G2cG21A3G2dA3M2eG2bA3G3A3S0S15S19S40S16S41G2bG2eA3G3A3S0S15S1cG23G3A2S0S15S1bS19S40S16S41S1eS1G27G24A3M2fS1dS3fS1dS42G2cG26A3G2dA3M30A3G3A3A1S0S15S1bS19S40S16S41G30G2fA3G3A3A1S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R4nr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sc7S1A5").
Definition RA_R4nr : option (list leaf) := ltac:(let x := eval vm_compute in RA_R4nr__f in exact x).
Lemma runA_R4nr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sc7S1A5S11fA3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R4nr__f. Qed.
Definition LA_R4nr : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R4nr) in exact x).
Lemma LA_R4nr_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSf3A4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R4nrs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R4nr 0 SA_R4nr) in exact x).
Definition ST_R4nr : sstate := ltac2:(tb__ "0|32|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P8cM5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P93A1MaA3MbA3McS0S12S1eS1Q20MdS10P91A1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18S10P78A1M1fG9S11Z28A1M20S0S13S14G9G19S10P96A1M21A3S0S13S14G1cG19S10P82A1M22A3S0S13S14S11Z10A1M23G19S10P7bA1A3S0S13S14S11Z18A1M24Z4M25S10P7cA1A3S0S13S14G8G25S10P7dA1A3S0S13S14S11Z20A1M26G19S10P7eA1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G22G9G20S0S13S14G9G19G1fA3S0S13S14G1cG19G6A3S0S13S14G23G19S10P85A1M27A3S0S13S14G24G25S10P86A1A3S0S13S14G8G25S10P87A1A3S0S13S14G26G19S10P88A1M28A3G1bA3A3A3A3A3A3S1aA5S0S17S18G27G1cS11Z9A1M29S0S13S14G1cZ1M2aS10P89A1M2bA3G1bA3S1aA5S0S17S18G6G9G20S0S13S14G24G25S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G25GfA3S0S13S14G9G19G22A3S0S13S14G1cG19G21A3S0S13S14G23G19S10P8fA1M2cA3S0S13S14G26G19S10P92A1M2dA3G1bA3A3A3A3A3A3S1aA5S0S17S18G2cG1cG29S0S13S14G1cG2aGaA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G26G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG2dA3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M2eS16S3fG2eS11G2aA1A3S0S13S14G2eG2aS10PaaA1M2fA3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3A3S0S15S20G1G25A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G1fG9A3A1S0S15S1bS19S40G22G9A3A1S0S15S1cG2bS11ZffA1M30A2S0S15S1bS19S40S16S41G28G26A3G9A3A1S0S15S1bS19S40G6G9A3A1S0S15S1cGaG30A2S0S15S20G5G12A2S0S15S1bS19S40G6G22A3A1S0S15S1bS19S40G22G6A3A1S0S15S1bS19
S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M31G9A3A1S0S15S1cS1dS44S23S46G31S11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG2fG30A2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R4nr : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R4nrs ST_R4nr) in exact x).
Definition RT_R4nr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5SdcS1A5").
Definition RT_R4nr : option (list leaf) := ltac:(let x := eval vm_compute in RT_R4nr__f in exact x).
Lemma runT_R4nr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5SdcS1A5S134A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R4nr__f. Qed.
Definition LT_R4nr : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R4nr) in exact x).
Lemma LT_R4nr_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cS108A4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R4sh : sstate := ltac2:(tb__ "0|2d|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78A1MeA3G4A3S1aA5S0S17S18GeG3S11Z28MfA1M10S0S13S14G3G5S3eP96A1M11A3S0S13S14G6G5S3eP82A1M12A3S0S13S14S11Z10A1M13G5S3eP7bA1A3S0S13S14S11Z18A1M14Z4M15S3eP7cA1M16A3S0S13S14S11Z1cA1M17G15S3eP7dA1M18A3S0S13S14S11Z20A1M19G5S3eP7eA1A3G4A3A3A3A3A3A3S1aA5S0S17S18G12G3G10S0S13S14G3G5GeA3S0S13S14G6G5S3eP8cM1aA1M1bA3S0S13S14G13G5S3eP85A1A3S0S13S14G14G15S3eP86A1A3S0S13S14G17G15S3eP87A1M1cA3S0S13S14G19G5S3eP88A1M1dA3G4A3A3A3A3A3A3S1aA5S0S17S18G1bG3G10S0S13S14G3G5G12A3S0S13S14G6G5G11A3S0S13S14G13G5S3eP8fA1M1eA3S0S13S14G14G15S3eP90A1M1fA3S0S13S14G17G15S3eP91A1M20A3S0S13S14G19G5S3eP92A1M21A3G4A3A3A3A3A3A3S1aA5S0S17S18G1eG6S11Z9A1S0S13S14G6Z1M22S3eP93A1M23A3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G19G4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M24G21A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M25S16S3fG25S11G22A1A3S0S13S14G25G22S3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3S0S15S20G0G15A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M26GfA2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GeG3A3A1S0S15S1bS19S40G12G3A3A1S0S15S1bS19S40S16S41G1dG19A3G3A3A1S0S15S1bS19S40G1bG3A3A1S0S15S1cG23S11ZffA1A2S0S15S20G1aGaA2S0S15S19S40S1eS1G24G16A3G3A3S0S15S1bS19S40S1eS1G24G18A3G3A3A1S0S15S19S40S1eS1G24G1cA3S1dS3fS1dS42S11G26A1M27G1dA3S11ZffffffffffffffffA1M28A3A3S0S15S1bS19S40S16S41S1dS3fS1dS42G27G23A3G28A3M29S1eS1G24G20A3M2aA3G3A3A1M2bS0S15S1bS19S40S16S41G2aG29A3G3A3A1M2cS0S15S1cG1fG3A2S0S15G2cS0S15G2bS2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R4sh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sc8S1A5").
Definition RA_R4sh : option (list leaf) := ltac:(let x := eval vm_compute in RA_R4sh__f in exact x).
Lemma runA_R4sh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sc8S1A5S120A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R4sh__f. Qed.
Definition LA_R4sh : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R4sh) in exact x).
Lemma LA_R4sh_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSf4A4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R4shs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R4sh 0 SA_R4sh) in exact x).
Definition ST_R4sh : sstate := ltac2:(tb__ "0|2f|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P8cM5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P93A1MaA3MbA3McS0S12S1eS1Q20MdS10P91A1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18S10P78A1M1fG9S11Z28A1M20S0S13S14G9G19S10P96A1M21A3S0S13S14G1cG19S10P82A1M22A3S0S13S14S11Z10A1M23G19S10P7bA1A3S0S13S14S11Z18A1M24Z4M25S10P7cA1A3S0S13S14G8G25S10P7dA1A3S0S13S14S11Z20A1M26G19S10P7eA1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G22G9G20S0S13S14G9G19G1fA3S0S13S14G1cG19G6A3S0S13S14G23G19S10P85A1A3S0S13S14G24G25S10P86A1A3S0S13S14G8G25S10P87A1A3S0S13S14G26G19S10P88A1M27A3G1bA3A3A3A3A3A3S1aA5S0S17S18G6G9G20S0S13S14G24G25S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G25GfA3S0S13S14G9G19G22A3S0S13S14G1cG19G21A3S0S13S14G23G19S10P8fA1M28A3S0S13S14G26G19S10P92A1M29A3G1bA3A3A3A3A3A3S1aA5S0S17S18G28G1cS11Z9A1S0S13S14G1cZ1M2aGaA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G26G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG29A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M2bS16S3fG2bS11G2aA1A3S0S13S14G2bG2aS10PaaA1M2cA3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3S0S15S20G1G25A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G1fG9A3A1S0S15S1bS19S40G22G9A3A1S0S15S1bS19S40S16S41G27G26A3G9A3A1S0S15S1bS19S40G6G9A3A1S0S15S1cGaS11ZffA1M2dA2S0S15S20G5G12A2S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M2eG9A3A1S0S15S1cS1dS44S23S46G2eS11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG2c
G2dA2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R4sh : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R4shs ST_R4sh) in exact x).
Definition RT_R4sh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5SddS1A5").
Definition RT_R4sh : option (list leaf) := ltac:(let x := eval vm_compute in RT_R4sh__f in exact x).
Lemma runT_R4sh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5SddS1A5S135A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R4sh__f. Qed.
Definition LT_R4sh : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R4sh) in exact x).
Lemma LT_R4sh_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cS109A4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R4sr : sstate := ltac2:(tb__ "0|32|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78A1MeA3G4A3S1aA5S0S17S18GeG3S11Z28MfA1M10S0S13S14G3G5S3eP96M11A1M12A3S0S13S14G6G5S3eP82A1M13A3S0S13S14S11Z10A1M14G5S3eP7bA1A3S0S13S14S11Z18A1M15Z4M16S3eP7cA1M17A3S0S13S14S11Z1cA1M18G16S3eP7dA1M19A3S0S13S14S11Z20A1M1aG5S3eP7eA1A3G4A3A3A3A3A3A3S1aA5S0S17S18G13G3G10S0S13S14G3G5GeA3S0S13S14G6G5S3eP8cA1M1bA3S0S13S14G14G5S3eP85A1A3S0S13S14G15G16S3eP86A1A3S0S13S14G18G16S3eP87A1M1cA3S0S13S14G1aG5S3eP88A1M1dA3G4A3A3A3A3A3A3S1aA5S0S17S18G1bG3G10S0S13S14G3G5G13A3S0S13S14G6G5G12A3S0S13S14G14G5S3eP8fA1M1eA3S0S13S14G15G16S3eP90A1A3S0S13S14G18G16S3eP91A1M1fA3S0S13S14G1aG5S3eP92A1A3G4A3A3A3A3A3A3S1aA5S0S17S18G1eG6S11Z9A1M20S0S13S14G6Z1M21S3eP93A1M22A3G4A3S1aA5S0S17S18G12G3G10S0S13S14G3G5G1bA3S0S13S14G6G5GeA3S0S13S14G14G5S3eP99A1M23A3S0S13S14G15G16S3eP9aA1M24A3S0S13S14G18G16S3eP9bA1M25A3S0S13S14G1aG5S3eP9cA1M26A3G4A3A3A3A3A3A3S1aA5S0S17S18G23G6G20S0S13S14G6G21S3eP9dA1M27A3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G1aG4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M28G26A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M29S16S3fG29S11G21A1A3S0S13S14G29G21S3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3A3A3S0S15S20G0G16A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M2aGfA2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GeG3A3A1S0S15S1bS19S40G13G3A3A1S0S15S1bS19S40S16S41G1dG1aA3G3A3A1S0S15S1bS19S40G1bG3A3A1S0S15S1cG22S11ZffA1M2bA2S0S15S1bS19S40G12G3A3A1S0S15S1cG27G2bA2S0S15S20G11GaA2S0S15S1bS19S40G12G1bA3A1S0S15S1bS19S40G1bG12A3A1S0S15S19S40S1eS1G28G17A3G3A3S0S15S1bS19S40S1eS1G28G19A3G3A3A1S0S15S19S40S1eS1G28G1cA3S1dS3fS1dS42S11G2aA1M2cG1dA3S11ZffffffffffffffffA1M2dA3A3S0S15S19S40S16S41S1dS3fS1dS42G2cG22A3G2dA3M2eS1eS1G28G1fA3M2fA3G3A3S0S15S19S40S16S41G2fG2eA3G3A3S0S15S1cG24G3A2S0S15S1bS19S40S16S41S1eS1G28G25A3M30S1dS3fS1dS42G2cG27A3G2dA3M31A3G3A3A1S0S15S1bS19S40S16S41G31G30A3G3A3A1S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R4sr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Sc9S1A5").
Definition RA_R4sr : option (list leaf) := ltac:(let x := eval vm_compute in RA_R4sr__f in exact x).
Lemma runA_R4sr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Sc9S1A5S121A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R4sr__f. Qed.
Definition LA_R4sr : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R4sr) in exact x).
Lemma LA_R4sr_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSf5A4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R4srs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R4sr 0 SA_R4sr) in exact x).
Definition ST_R4sr : sstate := ltac2:(tb__ "0|32|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P96M5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P9dA1MaA3MbA3McS0S12S1eS1Q20MdS10P9bA1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18S10P78A1M1fG9S11Z28A1M20S0S13S14G9G19G6A3S0S13S14G1cG19S10P82A1M21A3S0S13S14S11Z10A1M22G19S10P7bA1A3S0S13S14S11Z18A1M23Z4M24S10P7cA1A3S0S13S14G8G24S10P7dA1A3S0S13S14S11Z20A1M25G19S10P7eA1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G21G9G20S0S13S14G9G19G1fA3S0S13S14G1cG19S10P8cA1M26A3S0S13S14G22G19S10P85A1A3S0S13S14G23G24S10P86A1A3S0S13S14G8G24S10P87A1A3S0S13S14G25G19S10P88A1M27A3G1bA3A3A3A3A3A3S1aA5S0S17S18G26G9G20S0S13S14G9G19G21A3S0S13S14G1cG19G6A3S0S13S14G22G19S10P8fA1M28A3S0S13S14G23G24S10P90A1A3S0S13S14G8G24S10P91A1A3S0S13S14G25G19S10P92A1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G28G1cS11Z9A1M29S0S13S14G1cZ1M2aS10P93A1M2bA3G1bA3S1aA5S0S17S18G6G9G20S0S13S14G23G24S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G24GfA3S0S13S14G9G19G26A3S0S13S14G1cG19G1fA3S0S13S14G22G19S10P99A1M2cA3S0S13S14G25G19S10P9cA1M2dA3G1bA3A3A3A3A3A3S1aA5S0S17S18G2cG1cG29S0S13S14G1cG2aGaA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G25G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG2dA3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M2eS16S3fG2eS11G2aA1A3S0S13S14G2eG2aS10PaaA1M2fA3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3A3A3S0S15S20G1G24A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G1fG9A3A1S0S15S1bS19S40G21G9A3A1
S0S15S1bS19S40S16S41G27G25A3G9A3A1S0S15S1bS19S40G26G9A3A1S0S15S1cG2bS11ZffA1M30A2S0S15S1bS19S40G6G9A3A1S0S15S1cGaG30A2S0S15S20G5G12A2S0S15S1bS19S40G6G26A3A1S0S15S1bS19S40G26G6A3A1S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M31G9A3A1S0S15S1cS1dS44S23S46G31S11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG2fG30A2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R4sr : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R4srs ST_R4sr) in exact x).
Definition RT_R4sr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5SdeS1A5").
Definition RT_R4sr : option (list leaf) := ltac:(let x := eval vm_compute in RT_R4sr__f in exact x).
Lemma runT_R4sr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5SdeS1A5S136A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R4sr__f. Qed.
Definition LT_R4sr : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R4sr) in exact x).
Lemma LT_R4sr_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cS10aA4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R5nh : sstate := ltac2:(tb__ "0|29|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78A1MeA3G4A3S1aA5S0S17S18GeG3S11Z28MfA1M10S0S13S14G3G5S3ePa0A1A3S0S13S14G6G5S3eP82M11A1M12A3S0S13S14S11Z10A1M13G5S3eP7bA1A3S0S13S14S11Z18A1M14Z4M15S3eP7cA1M16A3S0S13S14S11Z1cA1M17G15S3eP7dA1M18A3S0S13S14S11Z20A1M19G5S3eP7eA1A3G4A3A3A3A3A3A3S1aA5S0S17S18G12G3G10S0S13S14G3G5GeA3S0S13S14G6G5S3eP8cA1A3S0S13S14G13G5S3eP85A1M1aA3S0S13S14G14G15S3eP86A1M1bA3S0S13S14G17G15S3eP87A1M1cA3S0S13S14G19G5S3eP88A1M1dA3G4A3A3A3A3A3A3S1aA5S0S17S18G1aG6S11Z9A1S0S13S14G6Z1M1eS3eP89A1M1fA3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G19G4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M20G1dA3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M21S16S3fG21S11G1eA1A3S0S13S14G21G1eS3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3S0S15S20G0G15A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M22GfA2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GeG3A3A1S0S15S1bS19S40G12G3A3A1S0S15S1cG1fS11ZffA1A2S0S15S20G11GaA2S0S15S1bS19S40S16S41G1dG19A3G3A3A1S0S15S19S40S1eS1G20G16A3G3A3S0S15S1bS19S40S1eS1G20G18A3G3A3A1S0S15S19S47S1eS1G20G1cA3M23S1dS3fS1dS42S11G22A1M24G1dA3S11ZffffffffffffffffA1M25A3A3S0S15S1bS19S40S16S41S1dS3fS1dS42G24G1fA3G25A3M26G23A3G3A3A1M27S0S15S1bS19S40S16S41G23G26A3G3A3A1M28S0S15S1cG1bG3A2S0S15G28S0S15G27S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R5nh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5ScaS1A5").
Definition RA_R5nh : option (list leaf) := ltac:(let x := eval vm_compute in RA_R5nh__f in exact x).
Lemma runA_R5nh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5ScaS1A5S122A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R5nh__f. Qed.
Definition LA_R5nh : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R5nh) in exact x).
Lemma LA_R5nh_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSf6A4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R5nhs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R5nh 0 SA_R5nh) in exact x).
Definition ST_R5nh : sstate := ltac2:(tb__ "0|2c|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P82M5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P89A1MaA3MbA3McS0S12S1eS1Q20MdS10P87A1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18S10P78A1M1fG9S11Z28A1M20S0S13S14G9G19S10Pa0A1A3S0S13S14G1cG19G6A3S0S13S14S11Z10A1M21G19S10P7bA1A3S0S13S14S11Z18A1M22Z4M23S10P7cA1A3S0S13S14G8G23S10P7dA1A3S0S13S14S11Z20A1M24G19S10P7eA1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G6G9G20S0S13S14G22G23S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G23GfA3S0S13S14G9G19G1fA3S0S13S14G1cG19S10P8cA1A3S0S13S14G21G19S10P85A1M25A3S0S13S14G24G19S10P88A1M26A3G1bA3A3A3A3A3A3S1aA5S0S17S18G25G1cS11Z9A1S0S13S14G1cZ1M27GaA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G24G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG26A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M28S16S3fG28S11G27A1A3S0S13S14G28G27S10PaaA1M29A3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3S0S15S20G1G23A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G1fG9A3A1S0S15S1bS19S40G6G9A3A1S0S15S1cGaS11ZffA1M2aA2S0S15S20G5G12A2S0S15S1bS19S40S16S41G26G24A3G9A3A1S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M2bG9A3A1S0S15S1cS1dS44S23S46G2bS11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG29G2aA2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R5nh : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R5nhs ST_R5nh) in exact x).
Definition RT_R5nh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5SdfS1A5").
Definition RT_R5nh : option (list leaf) := ltac:(let x := eval vm_compute in RT_R5nh__f in exact x).
Lemma runT_R5nh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5SdfS1A5S137A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R5nh__f. Qed.
Definition LT_R5nh : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R5nh) in exact x).
Lemma LT_R5nh_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cS10bA4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R5nr : sstate := ltac2:(tb__ "0|30|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78A1MeA3G4A3S1aA5S0S17S18GeG3S11Z28MfA1M10S0S13S14G3G5S3ePa0A1A3S0S13S14G6G5S3eP82A1M11A3S0S13S14S11Z10A1M12G5S3eP7bA1A3S0S13S14S11Z18A1M13Z4M14S3eP7cA1M15A3S0S13S14S11Z1cA1M16G14S3eP7dA1M17A3S0S13S14S11Z20A1M18G5S3eP7eA1A3G4A3A3A3A3A3A3S1aA5S0S17S18G11G3G10S0S13S14G3G5GeA3S0S13S14G6G5S3eP8cM19A1M1aA3S0S13S14G12G5S3eP85A1M1bA3S0S13S14G13G14S3eP86A1A3S0S13S14G16G14S3eP87A1M1cA3S0S13S14G18G5S3eP88A1M1dA3G4A3A3A3A3A3A3S1aA5S0S17S18G1bG6S11Z9A1M1eS0S13S14G6Z1M1fS3eP89A1M20A3G4A3S1aA5S0S17S18G1aG3G10S0S13S14G3G5G11A3S0S13S14G6G5S3eP96A1A3S0S13S14G12G5S3eP8fA1M21A3S0S13S14G13G14S3eP90A1M22A3S0S13S14G16G14S3eP91A1M23A3S0S13S14G18G5S3eP92A1M24A3G4A3A3A3A3A3A3S1aA5S0S17S18G21G6G1eS0S13S14G6G1fS3eP93A1M25A3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G18G4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M26G24A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M27S16S3fG27S11G1fA1A3S0S13S14G27G1fS3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3A3S0S15S20G0G14A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M28GfA2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GeG3A3A1S0S15S1bS19S40G11G3A3A1S0S15S1cG20S11ZffA1M29A2S0S15S1bS19S40S16S41G1dG18A3G3A3A1S0S15S1bS19S40G1aG3A3A1S0S15S1cG25G29A2S0S15S20G19GaA2S0S15S1bS19S40G1aG11A3A1S0S15S1bS19S40G11G1aA3A1S0S15S19S40S1eS1G26G15A3G3A3S0S15S1bS19S40S1eS1G26G17A3G3A3A1S0S15S19S47S1eS1G26G1cA3M2aS1dS3fS1dS42S11G28A1M2bG1dA3S11ZffffffffffffffffA1M2cA3A3S0S15S19S40S16S41S1dS3fS1dS42G2bG20A3G2cA3M2dG2aA3G3A3S0S15S19S40S16S41G2aG2dA3G3A3S0S15S1cG22G3A2S0S15S1bS19S40S16S41S1eS1G26G23A3M2eS1dS3fS1dS42G2bG25A3G2cA3M2fA3G3A3A1S0S15S1bS19S40S16S41G2fG2eA3G3A3A1S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R5nr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5ScbS1A5").
Definition RA_R5nr : option (list leaf) := ltac:(let x := eval vm_compute in RA_R5nr__f in exact x).
Lemma runA_R5nr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5ScbS1A5S123A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R5nr__f. Qed.
Definition LA_R5nr : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R5nr) in exact x).
Lemma LA_R5nr_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSf7A4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R5nrs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R5nr 0 SA_R5nr) in exact x).
Definition ST_R5nr : sstate := ltac2:(tb__ "0|31|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P8cM5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P93A1MaA3MbA3McS0S12S1eS1Q20MdS10P91A1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18S10P78A1M1fG9S11Z28A1M20S0S13S14G9G19S10Pa0A1A3S0S13S14G1cG19S10P82A1M21A3S0S13S14S11Z10A1M22G19S10P7bA1A3S0S13S14S11Z18A1M23Z4M24S10P7cA1A3S0S13S14G8G24S10P7dA1A3S0S13S14S11Z20A1M25G19S10P7eA1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G21G9G20S0S13S14G9G19G1fA3S0S13S14G1cG19G6A3S0S13S14G22G19S10P85A1M26A3S0S13S14G23G24S10P86A1A3S0S13S14G8G24S10P87A1A3S0S13S14G25G19S10P88A1M27A3G1bA3A3A3A3A3A3S1aA5S0S17S18G26G1cS11Z9A1M28S0S13S14G1cZ1M29S10P89A1M2aA3G1bA3S1aA5S0S17S18G6G9G20S0S13S14G23G24S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G24GfA3S0S13S14G9G19G21A3S0S13S14G1cG19S10P96A1A3S0S13S14G22G19S10P8fA1M2bA3S0S13S14G25G19S10P92A1M2cA3G1bA3A3A3A3A3A3S1aA5S0S17S18G2bG1cG28S0S13S14G1cG29GaA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G25G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG2cA3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M2dS16S3fG2dS11G29A1A3S0S13S14G2dG29S10PaaA1M2eA3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3A3S0S15S20G1G24A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G1fG9A3A1S0S15S1bS19S40G21G9A3A1S0S15S1cG2aS11ZffA1M2fA2S0S15S1bS19S40S16S41G27G25A3G9A3A1S0S15S1bS19S40G6G9A3A1S0S15S1cGaG2fA2S0S15S20G5G12A2S0S15S1bS19S40G6G21A3A1S0S15S1bS19S40G21G6A3A1S0S15S1bS19
S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M30G9A3A1S0S15S1cS1dS44S23S46G30S11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG2eG2fA2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R5nr : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R5nrs ST_R5nr) in exact x).
Definition RT_R5nr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Se0S1A5").
Definition RT_R5nr : option (list leaf) := ltac:(let x := eval vm_compute in RT_R5nr__f in exact x).
Lemma runT_R5nr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Se0S1A5S138A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R5nr__f. Qed.
Definition LT_R5nr : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R5nr) in exact x).
Lemma LT_R5nr_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cS10cA4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R5sh : sstate := ltac2:(tb__ "0|2c|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78A1MeA3G4A3S1aA5S0S17S18GeG3S11Z28MfA1M10S0S13S14G3G5S3ePa0A1A3S0S13S14G6G5S3eP82A1M11A3S0S13S14S11Z10A1M12G5S3eP7bA1A3S0S13S14S11Z18A1M13Z4M14S3eP7cA1M15A3S0S13S14S11Z1cA1M16G14S3eP7dA1M17A3S0S13S14S11Z20A1M18G5S3eP7eA1A3G4A3A3A3A3A3A3S1aA5S0S17S18G11G3G10S0S13S14G3G5GeA3S0S13S14G6G5S3eP8cM19A1M1aA3S0S13S14G12G5S3eP85A1A3S0S13S14G13G14S3eP86A1A3S0S13S14G16G14S3eP87A1M1bA3S0S13S14G18G5S3eP88A1M1cA3G4A3A3A3A3A3A3S1aA5S0S17S18G1aG3G10S0S13S14G3G5G11A3S0S13S14G6G5S3eP96A1A3S0S13S14G12G5S3eP8fA1M1dA3S0S13S14G13G14S3eP90A1M1eA3S0S13S14G16G14S3eP91A1M1fA3S0S13S14G18G5S3eP92A1M20A3G4A3A3A3A3A3A3S1aA5S0S17S18G1dG6S11Z9A1S0S13S14G6Z1M21S3eP93A1M22A3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G18G4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M23G20A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M24S16S3fG24S11G21A1A3S0S13S14G24G21S3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3S0S15S20G0G14A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M25GfA2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GeG3A3A1S0S15S1bS19S40G11G3A3A1S0S15S1bS19S40S16S41G1cG18A3G3A3A1S0S15S1bS19S40G1aG3A3A1S0S15S1cG22S11ZffA1A2S0S15S20G19GaA2S0S15S19S40S1eS1G23G15A3G3A3S0S15S1bS19S40S1eS1G23G17A3G3A3A1S0S15S19S40S1eS1G23G1bA3S1dS3fS1dS42S11G25A1M26G1cA3S11ZffffffffffffffffA1M27A3A3S0S15S1bS19S40S16S41S1dS3fS1dS42G26G22A3G27A3M28S1eS1G23G1fA3M29A3G3A3A1M2aS0S15S1bS19S40S16S41G29G28A3G3A3A1M2bS0S15S1cG1eG3A2S0S15G2bS0S15G2aS2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R5sh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5SccS1A5").
Definition RA_R5sh : option (list leaf) := ltac:(let x := eval vm_compute in RA_R5sh__f in exact x).
Lemma runA_R5sh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5SccS1A5S124A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R5sh__f. Qed.
Definition LA_R5sh : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R5sh) in exact x).
Lemma LA_R5sh_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSf8A4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R5shs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R5sh 0 SA_R5sh) in exact x).
Definition ST_R5sh : sstate := ltac2:(tb__ "0|2e|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P8cM5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P93A1MaA3MbA3McS0S12S1eS1Q20MdS10P91A1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18S10P78A1M1fG9S11Z28A1M20S0S13S14G9G19S10Pa0A1A3S0S13S14G1cG19S10P82A1M21A3S0S13S14S11Z10A1M22G19S10P7bA1A3S0S13S14S11Z18A1M23Z4M24S10P7cA1A3S0S13S14G8G24S10P7dA1A3S0S13S14S11Z20A1M25G19S10P7eA1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G21G9G20S0S13S14G9G19G1fA3S0S13S14G1cG19G6A3S0S13S14G22G19S10P85A1A3S0S13S14G23G24S10P86A1A3S0S13S14G8G24S10P87A1A3S0S13S14G25G19S10P88A1M26A3G1bA3A3A3A3A3A3S1aA5S0S17S18G6G9G20S0S13S14G23G24S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G24GfA3S0S13S14G9G19G21A3S0S13S14G1cG19S10P96A1A3S0S13S14G22G19S10P8fA1M27A3S0S13S14G25G19S10P92A1M28A3G1bA3A3A3A3A3A3S1aA5S0S17S18G27G1cS11Z9A1S0S13S14G1cZ1M29GaA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G25G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG28A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M2aS16S3fG2aS11G29A1A3S0S13S14G2aG29S10PaaA1M2bA3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3S0S15S20G1G24A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G1fG9A3A1S0S15S1bS19S40G21G9A3A1S0S15S1bS19S40S16S41G26G25A3G9A3A1S0S15S1bS19S40G6G9A3A1S0S15S1cGaS11ZffA1M2cA2S0S15S20G5G12A2S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M2dG9A3A1S0S15S1cS1dS44S23S46G2dS11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1c
G2bG2cA2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R5sh : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R5shs ST_R5sh) in exact x).
Definition RT_R5sh__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Se1S1A5").
Definition RT_R5sh : option (list leaf) := ltac:(let x := eval vm_compute in RT_R5sh__f in exact x).
Lemma runT_R5sh : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Se1S1A5S139A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R5sh__f. Qed.
Definition LT_R5sh : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R5sh) in exact x).
Lemma LT_R5sh_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cS10dA4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.

Definition SA_R5sr : sstate := ltac2:(tb__ "0|32|
S21Z2126cS15fS15eS22S9S12A1S0S17S18S10PaM0A1M1S10PfA1M2S11Z0A1M3S2S13A1M4S1aA5S0S17S18S11Z28d50A1G3S11Z8M5A1M6S0S13S14G3G5S3ePadA1M7A3G4A3S1aA5S0S17S18G7G3G6S0S13S14G3G5S3ePaeA1A3G4A3S1aA5S0S17S18S11Z5a3c8A1M8S16S3fS16S42S3ePcA1M9S11Z3MaA1A3MbS11Z58A1A3McS16S3fGbS11Z60A1MdA3S0S13S14GcG5S3eP78A1MeA3G4A3S1aA5S0S17S18GeG3S11Z28MfA1M10S0S13S14G3G5S3ePa0A1A3S0S13S14G6G5S3eP82A1M11A3S0S13S14S11Z10A1M12G5S3eP7bA1A3S0S13S14S11Z18A1M13Z4M14S3eP7cA1M15A3S0S13S14S11Z1cA1M16G14S3eP7dA1M17A3S0S13S14S11Z20A1M18G5S3eP7eA1A3G4A3A3A3A3A3A3S1aA5S0S17S18G11G3G10S0S13S14G3G5GeA3S0S13S14G6G5S3eP8cA1M19A3S0S13S14G12G5S3eP85A1A3S0S13S14G13G14S3eP86A1A3S0S13S14G16G14S3eP87A1M1aA3S0S13S14G18G5S3eP88A1M1bA3G4A3A3A3A3A3A3S1aA5S0S17S18G19G3G10S0S13S14G3G5G11A3S0S13S14G6G5S3eP96M1cA1M1dA3S0S13S14G12G5S3eP8fA1M1eA3S0S13S14G13G14S3eP90A1A3S0S13S14G16G14S3eP91A1M1fA3S0S13S14G18G5S3eP92A1A3G4A3A3A3A3A3A3S1aA5S0S17S18G1eG6S11Z9A1M20S0S13S14G6Z1M21S3eP93A1M22A3G4A3S1aA5S0S17S18G1dG3G10S0S13S14G3G5G19A3S0S13S14G6G5S3eP98A1A3S0S13S14G12G5S3eP99A1M23A3S0S13S14G13G14S3eP9aA1M24A3S0S13S14G16G14S3eP9bA1M25A3S0S13S14G18G5S3eP9cA1M26A3G4A3A3A3A3A3A3S1aA5S0S17S18G23G6G20S0S13S14G6G21S3eP9dA1M27A3G4A3S1aA5S0S17S18S11Z108ecA1G3GdG4S1fP1A1A5S0S17S18S11Z108ccA1G3G18G4S1fP4A1A5S0S17S18G8S16S3fS16S44S16S42S1eS1Q20M28G26A3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M29S16S3fG29S11G21A1A3S0S13S14G29G21S3ePaaA1A3G4A3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3A3A3S0S15S20G0G14A2S0S15S1cS11Z7fff7f800000A1S16S3fG1G2A3A2S0S15S19S43S11N120A1G2A3S0S15S19S43G2S11S140S13eZ2M2aGfA2A1A1A3S0S15S1cG9S11Z2fA1A2S0S15S1bS19S40GeG3A3A1S0S15S1bS19S40G11G3A3A1S0S15S1bS19S40S16S41G1bG18A3G3A3A1S0S15S1bS19S40G19G3A3A1S0S15S1cG22S11ZffA1M2bA2S0S15S1bS19S40G1dG3A3A1S0S15S1cG27G2bA2S0S15S20G1cGaA2S0S15S1bS19S40G1dG19A3A1S0S15S1bS19S40G19G1dA3A1S0S15S19S40S1eS1G28G15A3G3A3S0S15S1bS19S40S1eS1G28G17A3G3A3A1S0S15S19S40S1eS1G28G1aA3S1dS3fS1dS42S11G2aA1M2cG1bA3S11ZffffffffffffffffA1M2dA3A3S0S15S19S40S16S41S1dS3fS1dS42G2cG22A3G2dA3M2eS1eS1G28G1fA3M2fA3G3A3S0S15S19S40S16S41G2fG2eA3G3A3S0S15S1cG24G3A2S0S15S1bS19S40S16S41S1eS1G28G25A3M30S1dS3fS1dS42G2cG27A3G2dA3M31A3G3A3A1S0S15S1bS19S40S16S41G31G30A3G3A3A1S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb7S7A9").

Definition RA_R5sr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5ScdS1A5").
Definition RA_R5sr : option (list leaf) := ltac:(let x := eval vm_compute in RA_R5sr__f in exact x).
Lemma runA_R5sr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5ScdS1A5S125A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RA_R5sr__f. Qed.
Definition LA_R5sr : list leaf := ltac:(let x := eval vm_compute in (unopt RA_R5sr) in exact x).
Lemma LA_R5sr_shape : ltac2:(tb__ "0|1|
S4bS3S8S52SacA2M0A1S157SadG0S15cSf9A4S0G0S5S52SacZ213e0SafA4S2G0A1A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition LA_R5srs : sstate := ltac:(let x := eval vm_compute in (lfs LA_R5sr 0 SA_R5sr) in exact x).
Definition ST_R5sr : sstate := ltac2:(tb__ "0|32|
S21Z213e0S0S12S10P14A1S0S12S10PbA1M0S0S12S16S3fS10PaM1A1M2S11N90A1A3S0S12S10P17A1S0S12S10P18A1S0S12S10P19A1S0S12S10P1aA1S0S12S10P1bA1S0S12S10PcA1M3S0S12S10P1dA1M4S0S12S10P96M5A1M6S0S12S10PabA1M7S0S12S16S3fG6S11Z1cA1M8A3S0S12S1dS45S11Z0A1M9S1dS42S11Z2A1S10P9dA1MaA3MbA3McS0S12S1eS1Q20MdS10P9bA1A3MeS0S12S16S41GeGcA3MfS0S12GeS0S12G9S0S12S10PdA1S0S12S10P27A1M10S0S12S10PadA1M11S0S12S16S3fS16S42G3S11Z3M12A1A3M13S11Z5a420A1A3S0S12S11Z5a3c8A1M14S0S12S16S3fG13G14A3S0S12S10P2cA1M15S0S12S10P2dA1M16S0S12S10P2eA1S0S12S10P2fA1S0S12S10P30A1S0S12S10P31A1S0S12S10P32A1S0S12S10P33A1S2S12A1M17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S12S10P3cA1S0S12S10P3dA1S0S12S10P3eA1S0S12S10P3fA1S0S12S10P40A1S0S12S10P41A1S0S12S10P42A1S0S12S10P43A1S0S12S10P44A1S0S12S10P45A1S0S12S10P46A1S0S12S10P47A1S0S12S10P48A1S0S12S10P49A1S0S12S10P4aA1S0S12S10P4bA1S0S12S10P4cA1S0S12S10P4dA1S0S12S10P4eA1S0S12S10P4fA1S0S12S10P50A1S0S12S10P51A1S0S12S10P52A1S0S12S10P53A1S0S12S10P54A1S0S12S10P55A1S0S12S10P56A1S0S12S10P57A1S0S12S10P58A1S0S12S10P59A1S0S12S10P5aA1S0S12S10P5bA1G17A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S22S9S12A1S0S17S18G2S10PfA1M18G9S0S13S14S11N60A1Z8M19S10PaeA1M1aA3S0S13S14S11N58A1G19G16A3S0S13S14S11N50A1G19G15A3S0S13S14S11N48A1G19S10P2bA1A3S0S13S14S11N40A1G19S10P2aA1A3S0S13S14S11N38A1G19S10P29A1A3S0S13S14S11N30A1G19S10P28A1A3S0S13S14S11N28A1G19G10A3S0S13S14S11N20A1G19S10P26A1A3S0S13S14S11N18A1G19G4A3S0S13S14S11N10A1G19S10P1cA1A3S0S13S14S11N8A1G19G0A3S2S13A1M1bA3A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S17S18S11Z28d50A1G9S11G19A1M1cS0S13S14G9G19G11A3G1bA3S1aA5S0S17S18G11G9G1cS0S13S14G9G19G1aA3G1bA3S1aA5S0S17S18G14S16S3fG13S11Z58A1A3M1dS16S3fG13S11Z60A1M1eA3S0S13S14G1dG19G6A3G1bA3S1aA5S0S17S18S10P78A1M1fG9S11Z28A1M20S0S13S14G9G19S10Pa0A1A3S0S13S14G1cG19S10P82A1M21A3S0S13S14S11Z10A1M22G19S10P7bA1A3S0S13S14S11Z18A1M23Z4M24S10P7cA1A3S0S13S14G8G24S10P7dA1A3S0S13S14S11Z20A1M25G19S10P7eA1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G21G9G20S0S13S14G9G19G1fA3S0S13S14G1cG19S10P8cA1M26A3S0S13S14G22G19S10P85A1A3S0S13S14G23G24S10P86A1A3S0S13S14G8G24S10P87A1A3S0S13S14G25G19S10P88A1M27A3G1bA3A3A3A3A3A3S1aA5S0S17S18G26G9G20S0S13S14G9G19G21A3S0S13S14G1cG19G6A3S0S13S14G22G19S10P8fA1M28A3S0S13S14G23G24S10P90A1A3S0S13S14G8G24S10P91A1A3S0S13S14G25G19S10P92A1A3G1bA3A3A3A3A3A3S1aA5S0S17S18G28G1cS11Z9A1M29S0S13S14G1cZ1M2aS10P93A1M2bA3G1bA3S1aA5S0S17S18G6G9G20S0S13S14G23G24S16S41GeS1dS3fGbS11ZffffffffffffffffA1A3A3A3S0S13S14G8G24GfA3S0S13S14G9G19G26A3S0S13S14G1cG19S10P98A1A3S0S13S14G22G19S10P99A1M2cA3S0S13S14G25G19S10P9cA1M2dA3G1bA3A3A3A3A3A3S1aA5S0S17S18G2cG1cG29S0S13S14G1cG2aGaA3G1bA3S1aA5S0S17S18S11Z108ecA1G9G1eG1bS1fP1A1A5S0S17S18S11Z108ccA1G9G25G1bS1fP4A1A5S0S17S18G14S16S3fS16S44S16S42S1eS1GdG2dA3S11Z34A1A3S11Z3aA1A3S11Z371A1A3M2eS16S3fG2eS11G2aA1A3S0S13S14G2eG2aS10PaaA1M2fA3G1bA3S1aA5S2S17A1A3A3A3A3A3A3A3A3A3A3A3A3A3S0S15S20G1G24A2S0S15S1cS11Z7fff7f800000A1S16S3fG2G18A3A2S0S15S19S43S11N120A1G18A3S0S15S19S43G18S11N10000000000A1A3S0S15S1cG3S11Z2fA1A2S0S15S1bS19S40G1fG9A3A1S0S15S1bS19
S40G21G9A3A1S0S15S1bS19S40S16S41G27G25A3G9A3A1S0S15S1bS19S40G26G9A3A1S0S15S1cG2bS11ZffA1M30A2S0S15S1bS19S40G6G9A3A1S0S15S1cGaG30A2S0S15S20G5G12A2S0S15S1bS19S40G6G26A3A1S0S15S1bS19S40G26G6A3A1S0S15S1bS19S40G7G9A3A1S0S15S1bS19S40S16S41G7S1dS45G9G7A3A3M31G9A3A1S0S15S1cS1dS44S23S46G31S11Z77cb531A1A3S11Z1bA1A3S11Z1fA1A2S0S15S1cG2fG30A2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P12cS7A9").
Definition DT_R5sr : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (sdiff LA_R5srs ST_R5sr) in exact x).
Definition RT_R5sr__f : option (list leaf) := ltac2:(tb__ "0|0|
S15bSb6U12cSb5Se2S1A5").
Definition RT_R5sr : option (list leaf) := ltac:(let x := eval vm_compute in RT_R5sr__f in exact x).
Lemma runT_R5sr : ltac2:(tb__ "0|0|
S4bS4S3SadA1A1SaeSb6U12cSb5Se2S1A5S13aA3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.direct_cast RT_R5sr__f. Qed.
Definition LT_R5sr : list leaf := ltac:(let x := eval vm_compute in (unopt RT_R5sr) in exact x).
Lemma LT_R5sr_shape : ltac2:(tb__ "0|2|
S4bS3S8S52SacA2M0A1S157SadG0S15cS10eA4S0G0S5S52SacZ21b08Sb0A4M1S0G0G1S0G0G1S2G0A1A3A3A3A3"). Proof. match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
End Mal_aslot_runsR.
