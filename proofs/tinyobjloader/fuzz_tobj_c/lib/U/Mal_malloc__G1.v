(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "false"; "true"; "option"; "bool"; "pair"; "Some"; "app"; "prod"; "nat"; "andb"; "None"; "orb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "SPUle"; "sv"; "cell"; "sobj"; "SAlu"; "mkCell"; "mkObj"; "DUnknown"; "SVar"; "SPBranch"; "mkSS"; "FcsrFrm0"; "SPNot"; "ss_next"; "ss_pc"; "SPAlign"; "ss_fregs"; "ss_objs"; "ss_regs"; "sstate"; "sv_eqb"; "valuation"; "SExt"; "ss_facts"; "ss_lenient"; "DRom"; "SAluW"; "SMd"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "DZero"; "SLBytes"; "SPTrue"; "SPUlt"; "ss_fcsr"; "ss_resv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "stop_reason"; "sym_run"; "RsCut"; "lf_state"; "lf_reason"; "RsSymJump"; "RsFuel"; "mkLeaf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "eqb"; "opp"; "sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "vkind"; "vrsv"; "CUTS"; "sh"; "voff"; "mr_LK"; "NX"; "leqb"; "mr_c5"; "mr_enframe"; "RZ"; "lf0"; "mr_c1"; "mr_c2"; "mr_c3"; "mr_c4"; "mr_ck"; "mr_cutB"; "mr_ori"; "mr_ret"; "mr_sb"; "reg"; "C0"; "F7"; "MRC"; "mr_alloc_slot"; "mr_ctz"; "mr_errno"; "mr_fold"; "mr_lock"; "mr_malloc"; "mr_mmap"; "mr_nl"; "mr_sct"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs.RP"; "c"; "segs"; "L7"; "L8"; "L9"; "L0"; "L1"; "L2"; "L3"; "L4"; "L5"; "L5q"; "L6"; "L6o"; "d0"; "C1"; "C2"; "C3"; "C4"; "C5"; "C5o"; "C5q"; "C6"; "C7"; "C7base"; "C8"; "Ck"; "L7s"; "L8s"; "L9s"; "Tidx"; "Tlhu1"; "Tlhu2"; "l7_ok"; "l7_same"; "l8_stop"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "ALU_AND"; "ALU_SLL"; "ALU_SRL"; "ALU_SUB"; "mulop"; "BC_GE"; "M_MUL"; "BC_NE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs"; "md_seg"; "MD_P"; "MD_U"; "Pre_md"; "MD_FUEL"; "seq_kind"; "md_ctx"; "MD_NEXT"; "Posts_md_P"; "Posts_md_U"; "md_cuts"; "Pre_call"; "md_after_am"; "md_alloc_meta"; "md_enframe"; "md_entry"; "md_leaf_ok"; "md_okb"; "run_md"; "ACEIL"; "M64"; "MDC"; "MMAP_THRESHOLD"; "Pre_am0"; "Pre_amg"; "Pre_ovf"; "SQ_step"; "add_facts"; "md_lockfn"; "md_mmap"; "md_munmap"; "md_nl"; "md_ret"; "md_s2c"; "page_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "segsU"; "pre_fregs"; "pre_regs"; "setregs"; "cut_regs"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "skipn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs.States"; "v"; "O_errno"; "O_stk"; "base_facts"; "O_ctr"; "O_lock"; "O_nl"; "n_facts"; "O_R"; "O_seq"; "after_regs"; "frame_cells"; "page_facts"; "O_g"; "O_useq"; "seq_facts"; "seq_objs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs.Objs"; "E_sll"; "E_stride"; "E_lowbit"; "E_p0"; "E_strideT"; "E_S"; "E_X"; "E_X0"; "E_X1"; "E_p"; "E_strideM"; "F_all"; "F_base"; "F_kind"; "OBJS"; "O_act"; "O_act0";
"O_ctr"; "O_ctz"; "O_lock"; "O_meta"; "O_nl"; "O_sct"; "O_slot"; "O_stk"; "O_usg0"; "O_usg1"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs.Chain"; "StRet"; "leaf1"; "md_stop"; "StCut"; "StEcall"; "md_cuts"; "md_leaf_ok"; "md_okb"; "reg_is_lit"; "Pre_md"; "md_expect"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "S_ret_fresh"; "enomem_ret"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "cell_eqb"; "odefault_eqb"; "@Stdlib.PArith.BinPos.Pos"; "eqb"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_malloc_direct_runs.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record md_consts := MDC {
  md_entry : Z; md_ret : Z;
  md_mmap : Z; md_munmap : Z;
  md_alloc_meta : Z; md_after_am : Z;
  md_enframe : Z;
  md_s2c : Z;
  md_lockfn : Z;
  md_ctx : Z; md_nl : Z }.
Definition MD_P : md_consts :=
  MDC 0x20efc 0x20f54 0x21ea0 0x21f38 0x20c24 0x21088 0x21b10 0x20fd8 0x278e0 0x5a3c8 0x5a35b.
Definition MD_U : md_consts := ltac2:(tb__ "0|1|
Sb4S49Z207bcZ740M0A2S49Z20814G0A2S49Z21760G0A2S49Z217f8G0A2S49Z204e4G0A2S49Z20948G0A2S49Z213d0G0A2S49Z20898G0A2S49Z271a0G0A2S49Z59c88G0A2S49Z59c1bG0A2Ab").

Inductive seq_kind := SQ_step | SQ_wrap.
Inductive md_seg :=
| MD_ovf | MD_call | MD_fail | MD_ok (s : seq_kind) | MD_am0 | MD_am0_after | MD_amg.

Definition MD_NEXT : positive := 300%positive.
Definition MD_FUEL : nat := 2000%nat.
Definition M64 : Z := 2 ^ 64 - 1.
Definition ACEIL : Z := 0x7fffff800000.
Definition MMAP_THRESHOLD : Z := 131052.

Section States.
Variable c : md_consts.
Definition v (n : positive) : sv := SVar n.

Definition O_stk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S17S19PaA1SfN80A1SfZ0A1Vcells;S18A5").
Definition O_errno : sobj := ltac2:(tb__ "0|1|
S17S19P18A1SfNa4A1M0SfNa0A1S0S13S16G0Z4SccPb6A1A3S1S13A1A3S18A5").
Definition O_nl : sobj := ltac2:(tb__ "0|2|
S17SfSbeVc;A1A1SfZ0A1M0SfZ1M1A1S0S13S16G0G1G0A3S1S13A1A3S18A5").
Definition O_lock : sobj := ltac2:(tb__ "0|2|
S17SfSa5Vc;A1A1SfZ0A1M0SfZ4M1A1S0S13S16G0G1G0A3S1S13A1A3S18A5").
Definition O_ctr : sobj := ltac2:(tb__ "0|1|
S17SfSa5Vc;A1A1SfZ14A1M0SfZ18A1S0S13S16G0Z4SccP99A1A3S1S13A1A3S18A5").
Definition O_seq (s : sv) : sobj := ltac2:(tb__ "0|1|
S17SfSa5Vc;A1A1SfZ398A1M0SfZ399A1S0S13S16G0Z1Vs;A3S1S13A1A3S18A5").
Definition O_useq : sobj := ltac2:(tb__ "0|0|
S17SfSa5Vc;A1A1SfZ358A1SfZ378A1S1S13A1S18A5").
Definition O_R : sobj := ltac2:(tb__ "0|0|
S17SccPd2A1SfZ0A1SfZ10A1S1S13A1S32A5").
Definition O_g : sobj := ltac2:(tb__ "0|0|
S17SccPd3A1SfZ10A1SfZ28A1S1S13A1S18A5").

Definition base_facts : list sprop := ltac2:(tb__ "0|4|
S0S10S20PaM0Z4A2S0S10S11SfZ10000A1S19G0A1M1A2S0S10S11G1SfS4aZ2M2Z2fA2A1A2S0S10S11SfZ1000A1S19P18M3A1A2S0S10S20G3G2A2S0S10S11SccP99A1SfS4dS4aG2Z20A2Z1A2A1A2S1S10A1A3A3A3A3A3A3").
Definition n_facts : list sprop := ltac2:(tb__ "0|1|
S0S10S11SfSb5A1SccPcA1M0A2S0S10S35G0SfS4aZ2Z3eA2A1A2S1S10A1A3A3").
Definition page_facts (p : positive) : list sprop := ltac2:(tb__ "0|1|
S0S10S11SfZ1000A1S19Vp;A1M0A2S0S10S11G0SfSb2A1A2S0S10S20Vp;ZcA2S1S10A1A3A3A3").
Definition seq_objs (s : seq_kind) : list sobj := ltac2:(tb__ "0|1|
Sa4S2S14A1Ls;Vs;S0S14Sd5SccPbcA1A1S1S14A1M0A3S0S14Sd5SfZffA1A1S0S14SdaG0A3A3Xa4x2").
Definition seq_facts (s : seq_kind) : list sprop := ltac2:(tb__ "0|1|
Sa4S2S10A1Ls;Vs;S0S10S11SccPbcA1SfZfeA1A2S1S10A1M0A3G0Xa4x2").

Definition Pre_ovf : sstate := ltac2:(tb__ "0|0|
S1bSaeVc;A1Sc5Sc4S1cSdS12A1S0S14SceS1S13A1A1S0S14ScdS1S14A1A3A3S9S10ScfS0S10S11SfZ7fffffffffffefffA1SccPcA1A2S1S10A1A3A3Sa6S3A9").
Definition Pre_call (s : seq_kind) : sstate := ltac2:(tb__ "0|0|
S1bSaeVc;A1Sc5Sc4S1cSdS12A1S9S14S0S14SceS1S13A1A1S0S14ScdS0S14Sd2S0S14Sd1S0S14Sd0S1S14A1A3A3A3A3A3SdcVs;A1A3S9S10ScfS9S10Sd3SdbVs;A1A3A3Sa6S3A9").

Definition frame_cells : list cell := ltac2:(tb__ "0|1|
S0S13S16SfN8A1Z8M0S19PbA1A3S0S13S16SfN10A1G0S19P1cA1A3S0S13S16SfN18A1G0S19P1dA1A3S0S13S16SfN20A1G0S19P26A1A3S0S13S16SfN28A1G0S19P27A1A3S0S13S16SfN30A1G0S19P28A1A3S1S13A1A3A3A3A3A3A3").
Definition after_regs (a0 : sv) : list sv := ltac2:(tb__ "0|2|
Sc6Sc7Pc8A1S0SaSbS12A2M0S7SbS12U2S15S94S19PaA1SfN30A1A3A4S0G0S7SbS12U8SccPcA1M1A4S0G0S7SbS12U9SfSa5Vc;A1A1A4S0G0S7SbS12U12SfSb3A1A4S0G0S7SbS12U13S15S94G1SfZ14A1A3A4S0G0S7SbS12U14SccPd2A1A4S0G0S7SbS12UaVa0;A4S1G0A1A3A3A3A3A3A3A3A2").
Definition Pre_am0 : sstate := ltac2:(tb__ "0|0|
S1bSabVc;A1Sd6SfZ0A1A1Sc4S1cSdS12A1S0S14SceSd7A1S0S14ScdS0S14Sd2S0S14Sd1S0S14Sd0S0S14Sd4S1S14A1A3A3A3A3A3A3S9S10ScfS9S10Sd3Sd8Pd2A1A3A3Sa6S3A9").
Definition Pre_amg : sstate := ltac2:(tb__ "0|2|
S1bSabVc;A1Sd6SccPd3M0A1M1A1Sc4S1cSdS12A1S0S14SceSd7A1S0S14ScdS0S14Sd2S0S14Sd1S0S14Sd0S0S14Sd4S0S14Sd9S1S14A1A3A3A3A3A3A3A3S9S10ScfS9S10Sd3S9S10Sd8Pd2A1S0S10S1dS1aS95G1SfZ0A1A3A1S0S10S20G0Z3A2S0S10S11G1SfS4aZ2Z2fA2A1A2S0S10S11SfZ1000A1G1A2S1S10A1A3A3A3A3A3A3A3Sa6S3A9").
End States.

Definition add_facts (S : sstate) (fs : list sprop) : sstate := ltac2:(tb__ "0|0|
S1bS1fVS;A1S23VS;A1S21VS;A1S36VS;A1S37VS;A1S22VS;A1S9S10S28VS;A1Vfs;A3S1eVS;A1S29VS;A1A9").

Section Chain.
Variable segs : list Segment.
Variable c : md_consts.

Definition md_cuts : list Z := ltac2:(tb__ "0|0|
S0S41SacVc;A1S0S41SadVc;A1S0S41Sc0Vc;A1S0S41SbbVc;A1S1S41A1A3A3A3A3").
Definition leaf1 (S : sstate) : sstate := ltac2:(tb__ "0|1|
S5S2S38A1M0A1S24Lx;S3aVsegs;Sa3S102VS;S4A5G0G0S24Ll;R1VS;S38G0G0S24Ll0;R1S3cR2A1S38G0VS;Ll2;Ll1;X2x2Ll0;LL;X2x2Ll;VS;X5x2").

Definition Pre_md (x : md_seg) : sstate := ltac2:(tb__ "0|2|
S9fS24Lx;Vx;Sb8Vc;A1SaaVc;Sb9A2M0S10eSfeG0A1S110A2Sa4SbaS10fSfeSaaVc;R1A2A1A1Sc1P12cA1A2Ls;Sb6Vc;A1M1S10eSfeG1A1Z0A2Sb7Vc;A1X9fx7").

Definition reg_is_lit (S : sstate) (r : nat) (z : Z) : bool := ltac2:(tb__ "0|3|
S5S12A1S6Lx;S10aS12S23VS;A1Vr;A3S12S12S6Ls;R1S41S4bR1Vz;A2Ln;S42S3Li;S96S12S12S3Lb;La;M0Lop;M1G1S9bG0Lop;M2G2S6S43S12S3La;Lw;Lsgn;S42S12S41S3Lk;Li;Ll;X12x8Ls;S3X5x2").

Inductive md_stop := StEcall (pc : Z) (no : Z) | StCut (pc : Z) | StRet.
Definition md_expect (x : md_seg) : md_stop := ltac2:(tb__ "0|0|
S9fSffLx;Vx;SfdS101SbcVc;A1ZdeA2SfdSa4S100SacVc;A1A1Ls;S101SbdVc;A1Zd7A2SfdS100SadVc;A1A1X9fx7").
Definition md_leaf_ok (x : md_seg) (L : leaf) : bool := ltac2:(tb__ "0|2|
S3cVL;A1S24SffS6Lx;S107Vx;A1S41S41S39S6Lx;M0S3dVL;A1M1ScS4bS1fR3A1R2A2S105R3U11R1A3A2S3S3S3S3S3S3X39x7Lno;Lpc;S41G0G1S3S4bS1fR2A1R1A2S3S3S3S3S3X39x7Lpc;G0G1S3S3S3S3ScS4bS1fR1A1SbfVc;A1A2S105R1UaZ0A3A2S3S3X39x7Xffx3TS;").

Definition md_okb (x : md_seg) (o : option (list leaf)) : bool := ltac2:(tb__ "0|1|
S5S2S38A1M0A1S6Lo;Vo;G0G0S6Ll;R1S3S38G0G0S6Ll0;R1S103Vx;R2A2S38G0S3Ll2;Ll1;X2x2Ll0;LL;X2x2Ll;S3X5x2").
Lemma md_okb_run : ltac2:(tb__ "0|2|
S9fS5S2S38A1M0A1M1S44S6S104R2R1A2S4A3S44G1R2S8G0G1G0Lo;R2G0R1Ll;S1S38A1X5x2A2A3F_;Fo;Fx;").
Proof using . intros x [l|]; simpl; [reflexivity|discriminate]. Qed.
Lemma md_okb_shape : ltac2:(tb__ "0|2|
S9fS5S2S38A1M0A1M1S44S6S104R2R1A2S4A3S46S38S38S45S44G1R3S8G0S0S38R1S1S38A1A3A2A3S44S6S103R4R1A2S4A3A2LL;A2F_;Fo;Fx;").
Proof using . intros x [[|L [|]]|]; simpl; try discriminate. intros H. exists L. auto. Qed.

Definition run_md (x : md_seg) : list leaf := ltac2:(tb__ "0|1|
S5S2S38A1M0A1G0Lx;S3aVsegs;Sa3S102S106Vx;A1S4A5G0R1Ll;S1S38A1X5x2").
End Chain.

Definition Posts_md_P (x : md_seg) : list leaf := ltac2:(tb__ "0|0|
Sb1Sc2Sa0Vx;A3").
Definition Posts_md_U (x : md_seg) : list leaf := ltac2:(tb__ "0|0|
Sb1Sc3Sa1Vx;A3").

Ltac md_cases x := destruct x as [ | | | [ | ] | | | ].

Lemma Pre_md_P_strict : ltac2:(tb__ "0|0|
S9fS44S6S29Sa2Sc2Sa0R1A3A1S3A3Fx;").
Proof. intros x. md_cases x; vm_compute; reflexivity. Qed.
Lemma md_ok_P : ltac2:(tb__ "0|0|
S9fS44S6Sb0Sa0R1S3aSc2Sa3Sa9Sa0A1Sa2Sc2Sa0R1A3S4A5A3S4A3Fx;").
Proof. intros x. md_cases x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_md_P : ltac2:(tb__ "0|1|
S9fS44S5S2S38A1M0A1S3aSc2Sa3Sa9Sa0A1Sa2Sc2Sa0R1A3S4A5S8G0Sa7R1A1A2A3Fx;").
Proof. intros x. exact (md_okb_run MD_P x _ (md_ok_P x)). Qed.
Lemma Posts_md_P_shape : ltac2:(tb__ "0|0|
S9fS46S38S38S45S44S2S38A1Sa7R2A1S0S38R1S1S38A1A3A3S44S6SafSa0R2R1A3S4A3A2LL;A2Fx;").
Proof.
  intros x. destruct (md_okb_shape MD_P x _ (md_ok_P x)) as (L & HL & Hs). exists L.
  split; [|exact Hs]. unfold Posts_md_P, run_md. rewrite HL. reflexivity.
Qed.

Theorem malloc_direct_run_P : ltac2:(tb__ "0|1|
S9fS10dOF_;S2Sf9A1Sf8OF_;F_;S26SfcSc2R3R2A3S10cSc2R4SfbSc2R3Sa2Sc2Sa0R5A3M0R2A4SfaSc2R3S1eG0A1R2Sa7R5A1A5A4F_;Frho;FK;Fok;Fx;").
Proof.
  intros x ok K rho Hok. apply triple1_triple.
  apply (sym_run_sound_strict segsU MD_FUEL (md_cuts MD_P) (Pre_md segsU MD_P x) (Posts_md_P x) ok K rho (Pre_md_P_strict x) (run_md_P x) Hok).
Qed.

Theorem malloc_direct_run_ex_P : ltac2:(tb__ "0|1|
S9fS2Sf9A1Sf8OF_;F_;S26S10bSc2SfbSc2R2Sa2Sc2Sa0R3A3M0R1A4SfaSc2R2S1eG0A1R1Sa7R3A1A5A3Frho;FK;Fx;").
Proof.
  intros x K rho. apply (sym_run_etriple segsU MD_FUEL (md_cuts MD_P) (Pre_md segsU MD_P x) (Posts_md_P x) K rho (Pre_md_P_strict x) (run_md_P x)).
Qed.

Lemma Pre_md_U_strict : ltac2:(tb__ "0|0|
S9fS44S6S29Sa2Sc3Sa1R1A3A1S3A3Fx;").
Proof. intros x. md_cases x; vm_compute; reflexivity. Qed.
Lemma md_ok_U : ltac2:(tb__ "0|0|
S9fS44S6Sb0Sa1R1S3aSc3Sa3Sa9Sa1A1Sa2Sc3Sa1R1A3S4A5A3S4A3Fx;").
Proof. intros x. md_cases x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma run_md_U : ltac2:(tb__ "0|1|
S9fS44S5S2S38A1M0A1S3aSc3Sa3Sa9Sa1A1Sa2Sc3Sa1R1A3S4A5S8G0Sa8R1A1A2A3Fx;").
Proof. intros x. exact (md_okb_run MD_U x _ (md_ok_U x)). Qed.
Lemma Posts_md_U_shape : ltac2:(tb__ "0|0|
S9fS46S38S38S45S44S2S38A1Sa8R2A1S0S38R1S1S38A1A3A3S44S6SafSa1R2R1A3S4A3A2LL;A2Fx;").
Proof.
  intros x. destruct (md_okb_shape MD_U x _ (md_ok_U x)) as (L & HL & Hs). exists L.
  split; [|exact Hs]. unfold Posts_md_U, run_md. rewrite HL. reflexivity.
Qed.

Theorem malloc_direct_run_U : ltac2:(tb__ "0|1|
S9fS10dOF_;S2Sf9A1Sf8OF_;F_;S26SfcSc3R3R2A3S10cSc3R4SfbSc3R3Sa2Sc3Sa1R5A3M0R2A4SfaSc3R3S1eG0A1R2Sa8R5A1A5A4F_;Frho;FK;Fok;Fx;").
Proof.
  intros x ok K rho Hok. apply triple1_triple.
  apply (sym_run_sound_strict segsU MD_FUEL (md_cuts MD_U) (Pre_md segsU MD_U x) (Posts_md_U x) ok K rho (Pre_md_U_strict x) (run_md_U x) Hok).
Qed.

Theorem malloc_direct_run_ex_U : ltac2:(tb__ "0|1|
S9fS2Sf9A1Sf8OF_;F_;S26S10bSc3SfbSc3R2Sa2Sc3Sa1R3A3M0R1A4SfaSc3R2S1eG0A1R1Sa8R3A1A5A3Frho;FK;Fx;").
Proof.
  intros x K rho. apply (sym_run_etriple segsU MD_FUEL (md_cuts MD_U) (Pre_md segsU MD_U x) (Posts_md_U x) K rho (Pre_md_U_strict x) (run_md_U x)).
Qed.
End Mal_malloc_direct_runs.

Module Mal_malloc_fast_runs.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record mr_consts := MRC {
  mr_malloc : Z;
  mr_ck : Z;
  mr_c1 : Z; mr_c2 : Z; mr_c3 : Z; mr_c4 : Z;
  mr_lhu1 : Z; mr_lhu2 : Z;
  mr_c5 : Z;
  mr_ori : Z;
  mr_enframe : Z; mr_cutB : Z; mr_sb : Z; mr_ret : Z;
  mr_errno : Z; mr_lock : Z; mr_alloc_slot : Z; mr_mmap : Z;
  mr_fold : Z;
  mr_LK : Z;
  mr_nl : Z;
  mr_sct : Z; mr_ctz : Z }.

Definition MR_P : mr_consts :=
  MRC 0x2056c 0x20ff0 0x21014 0x21024 0x21030 0x2104c 0x2106c 0x210e0 0x21108 0x21168 0x21b10 0x21bc8 0x21c24 0x21c5c
      0x202e8 0x278e0 0x2126c 0x21ddc 0x21bc4 0x5a3c8 0x5a35b 0x108ec 0x108cc.
Definition MR_U : mr_consts := ltac2:(tb__ "0|1|
S66S49Z1fe2cZ740M0A2S49Z208b0G0A2S49Z208d4G0A2S49Z208e4G0A2S49Z208f0G0A2S49Z2090cG0A2S49Z2092cG0A2S49Z209a0G0A2S49Z209c8G0A2S49Z20a28G0A2S49Z213d0G0A2S49Z21488G0A2S49Z214e4G0A2S49Z2151cG0A2S49Z1fba8G0A2S49Z271a0G0A2S49Z20b2cG0A2S49Z2169cG0A2S49Z21484G0A2Z5a3c8Z5a35bZ108ecZ108ccA17").

Definition NX : positive := 300%positive.

Inductive vkind := VL   | VM0   | VM1  .

Inductive voff := O0 | O1.
Inductive vrsv := RZ | R14 | R5 | RG.

Section Objs.
Variable c : mr_consts.

Definition E_S : sv := ltac2:(tb__ "0|0|
S27S3Q10S33P1S15S97S15S99S48P9bA1SfZ5A1A3SfZ7eA1A3Z2A3A3").
Definition E_strideT : sv := ltac2:(tb__ "0|0|
S15S98Se2SfZ4A1A3").
Definition E_strideM : sv := ltac2:(tb__ "0|0|
S15S94S15S97S48P9bA1SfZfffffffffffff000A1A3SfN10A1A3").
Definition E_stride (kd : vkind) : sv := ltac2:(tb__ "0|0|
S4eS12Lkd;Vkd;Se1Se1Se7X4ex3").
Definition E_p0 (kd : vkind) : sv := ltac2:(tb__ "0|0|
S15S94S15S94S48P9cA1S2cS9dSdeVkd;A1S48P9dA1A3A3SfZ10A1A3").
Definition E_lowbit : sv := ltac2:(tb__ "0|1|
S15S97S27S4Q20S48P98A1A3M0S2bS9aSfZ0A1G0A3A3").
Definition E_sll : sv := SAluW ALU_SLL (v 158) (SLit 4).

Definition E_p (kd : vkind) (o : voff) : sv := ltac2:(tb__ "0|1|
S52S12Lo;Vo;Se0Vkd;A1M0S15S94G0SddA3X52x2").
Definition E_pn (kd : vkind) (o : voff) : sv := ltac2:(tb__ "0|0|
S15S94Se6Vkd;Vo;A2S48PcA1A3").

Definition E_X0 (kd : vkind) : sv := ltac2:(tb__ "0|0|
S15S94S15S9aSdeVkd;A1S48PcA1A3SfN4A1A3").
Definition E_X1 (kd : vkind) : sv := ltac2:(tb__ "0|0|
S15S94S15S9aS15S9aSdeVkd;A1SddA3S48PcA1A3SfN4A1A3").
Definition E_X (kd : vkind) (o : voff) : sv := ltac2:(tb__ "0|0|
S52S12Lo;Vo;Se4Vkd;A1Se5Vkd;A1X52x2").

Definition O_stk : sobj := ltac2:(tb__ "0|0|
S17S19PaA1S19PfA1SfZ0A1S1S13A1S18A5").
Definition O_nl : sobj := ltac2:(tb__ "0|2|
S17SfS6eVc;A1A1SfZ0A1M0SfZ1M1A1S0S13S16G0G1G0A3S1S13A1A3S18A5").
Definition O_lock : sobj := ltac2:(tb__ "0|2|
S17SfS53Vc;A1A1SfZ0A1M0SfZ4M1A1S0S13S16G0G1G0A3S1S13A1A3S18A5").
Definition O_ctr : sobj := ltac2:(tb__ "0|1|
S17SfS53Vc;A1A1SfZ14A1M0SfZ18A1S0S13S16G0Z4S48P99A1A3S1S13A1A3S18A5").
Definition O_act : sobj := ltac2:(tb__ "0|2|
S17SfS53Vc;A1A1S15S94S15S98S48P96A1SfZ3A1A3M0SfZ58A1A3M1S15S94G0SfZ60A1A3S0S13S16G1Z8S48P97A1A3S1S13A1A3S18A5").
Definition O_sct : sobj := ltac2:(tb__ "0|0|
S17SfS6fVc;A1A1SfZ0A1SfZ60A1S1S13A1S2aP1A1A5").
Definition O_ctz : sobj := ltac2:(tb__ "0|0|
S17SfS68Vc;A1A1SfZ0A1SfZ20A1S1S13A1S2aP4A1A5").
Definition O_meta : sobj := ltac2:(tb__ "0|3|
S17S48P97A1SfZ10A1M0SfZ28A1S0S13S16G0Z8M1S48P9cA1A3S0S13S16SfZ18A1Z4M2S48P98A1A3S0S13S16SfZ1cA1G2S48P9aA1A3S0S13S16SfZ20A1G1S48P9bA1A3S1S13A1A3A3A3A3S18A5").
Definition O_slot (kd : vkind) : sobj := ltac2:(tb__ "0|2|
S17Se0Vkd;A1SfN4A1M0S15S94SdeVkd;A1G0A3S0S13S16G0Z1M1SfZ0A1A3S0S13S16SfN3A1G1S48P8eA1A3S0S13S16SfN2A1Z2S48P8fA1A3S1S13A1A3A3A3S18A5").

Definition O_act0 : sobj := ltac2:(tb__ "0|2|
S17SfS53Vc;A1A1S15S94S15S98S48Pa4A1SfZ3A1A3M0SfZ58A1A3M1S15S94G0SfZ60A1A3S0S13S16G1Z8S48Pa6A1A3S1S13A1A3S18A5").
Definition O_usg0 : sobj := ltac2:(tb__ "0|2|
S17SfS53Vc;A1A1S15S94S15S98S48Pa4A1SfZ3A1A3M0SfZ1d8A1A3M1S15S94G0SfZ1e0A1A3S0S13S16G1Z8S48Pa7A1A3S1S13A1A3S18A5").
Definition O_usg1 : sobj := ltac2:(tb__ "0|2|
S17SfS53Vc;A1A1S15S94S15S98S48P96A1SfZ3A1A3M0SfZ1d8A1A3M1S15S94G0SfZ1e0A1A3S0S13S16G1Z8S48Pa5A1A3S1S13A1A3S18A5").
Definition OBJS (kd : vkind) : list sobj := ltac2:(tb__ "0|0|
S0S14Sf5S0S14Sf2S0S14Sf0S0S14SeeS0S14SecS0S14Sf3S0S14SefS0S14Sf1S0S14Sf4Vkd;A1S0S14SedS0S14Sf6S0S14Sf7S1S14A1A3A3A3A3A3A3A3A3A3A3A3A3").

Definition F_base (kd : vkind) : list sprop := ltac2:(tb__ "0|e|
S0S10S20PaM0Z4M1A2S0S10S11SfZ7fff7f800000A1S15S94S19G0A1S19PfA1M2A3A2S0S10S1aS9cSfN2f0A1G2A3S0S10S1aS9cG2SfS4cS4aZ2M3Z28A2A1A1A3S0S10S11S48PcA1M4SfZ1ffebA1A2S0S10S11S48P96A1SfZ2fM5A1A2S0S10S1dS1aS95S48P97A1M6SfZ0A1M7A3A1S0S10S11S48P99A1SfZffffffffA1M8A2S0S10S11S48P98A1G8A2S0S10S11G6SfS4aG3G5A2A1M9A2S0S10S11SfZ1000A1MaG6A2S0S10S11S48P9cA1MbG9A2S0S10S11GaGbA2S0S10S11S48P9dA1SfZ1fA1McA2S0S10S11S48P8eA1SfZffA1A2S0S10S11S48P8fA1SfZffffA1A2S0S10S11S15S97S15S99S48P9bA1SfZ5A1A3SfZ7eA1A3SfZ5eA1A2S0S10S11SdeVkd;A1MdSfS4aG3Z14A2A1A2S0S10S11SfZ10A1GdA2S0S10S11S15S94G4SfG1A1A3GdA2S0S10S1dS1aS95SdfG7A3A1S0S10S11S2bS99S2cS9dSdfSfZ77cb531A1A3SfZ1bA1A3GcA2S1S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition F_kind (kd : vkind) : list sprop := ltac2:(tb__ "0|5|
S4eS2S10A1Lkd;Vkd;S0S10S1dS1aS95S15S97S48P9bA1M0SfZ1fA1A3SfZ0A1M1A3M2A1S1S10A1M3A3S0S10G2S0S10S1aS95S15S99G0SfZcA1A3G1A3M4G3A3A3S0S10G2S0S10S1dG4A1G3A3A3X4ex3").
Definition F_all (kd : vkind) : list sprop := ltac2:(tb__ "0|0|
S9S10Se9Vkd;A1SeaVkd;A1A3").

Definition F7 (kd : vkind) (o : voff) (r : vrsv) : list sprop := ltac2:(tb__ "0|f|
S9S10S52S2S10A1M0Lo;M1Vo;S0S10S11S48P9eA1M2SfZ0A1M3A2S1S10A1M4A3S0S10S11SfZ1A1M5G2A2S0S10S11G2SfZffA1A2S0S10S11SddSfZff0A1A2S0S10S11SfZ10A1SddA2S0S10S11S15S94S15S94SddS48PcA1M6A3M7SfZ4A1M8A3SdeVkd;A1M9A2G4A3A3A3A3A3X52x2S9S10S4fG0Lr;MaVr;S0S10S11Se3Vkd;Vo;A2MbG3A2G4A3S0S10S11G5GbA2S0S10S11GbG8A2G4A3A3S0S10S11SfZ5A1McGbA2S0S10S11GbGcA2G4A3A3S0S10S11SfZ6A1GbA2S0S10S11GbSfS4aZ2Z14A2A1A2G4A3A3X4fx4G1Vo;GaVr;G4G4G4S0S10S11S15S94G6SfZaA1MdA3G9A2G4A3X4fx4GaVr;G4S0S10S11S15S94SddGcA3G9A2G4A3S0S10S11S15S94SddSfZ9A1A3G9A2MeG4A3S0S10GeS0S10S11S15S94G7GdA3G9A2G4A3A3X4fx4X52x2A3A3").

Definition F5 : list sprop := ltac2:(tb__ "0|3|
S0S10S20Pa4M0Z1A2S0S10S11SfZ4A1S48G0A1M1A2S0S10S11G1SfZ1eA1A2S0S10S1dS1aS95G1SfZ6A1A3A1S0S10S11S48Pa6A1SfZ0A1M2A2S0S10S11S48Pa7A1G2A2S0S10S11S48Pa5A1SfZcA1A2S0S10S1aS9eS27S4Q20S48P98A1A3G2A3S1S10A1A3A3A3A3A3A3A3A3").

Definition CUTS : list Z := ltac2:(tb__ "0|0|
S0S41S5eVc;A1S0S41S5aVc;A1S0S41S5bVc;A1S0S41S5cVc;A1S0S41S5dVc;A1S0S41S56Vc;A1S0S41S60Vc;A1S0S41S57Vc;A1S0S41S5fVc;A1S0S41S62Vc;A1S0S41S69Vc;A1S0S41S6bVc;A1S0S41S67Vc;A1S0S41S6dVc;A1S1S41A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition C0 (kd : vkind) : sstate := ltac2:(tb__ "0|0|
S1bS6cVc;A1Sc5Sc4S1cSdS12A1SebVkd;A1Se8Vkd;A1S54S3A9").
End Objs.

Definition restate (S : sstate) (pc : Z) (rs : list (nat * sv)) (dropf : nat) (fs : list sprop) : sstate := ltac2:(tb__ "0|0|
S1bVpc;Sc6S23VS;A1Vrs;A2S21VS;A1S1cSdS12A1S22VS;A1S9S10ScbS10Vdropf;S28VS;A1A3Vfs;A3S54S3A9").

Definition restateF (S : sstate) (pc : Z) (rs : list (nat * sv)) (fs : list sprop) : sstate := ltac2:(tb__ "0|0|
S1bVpc;Sc6S23VS;A1Vrs;A2S21VS;A1S1cSdS12A1S22VS;A1Vfs;S54S3A9").

Definition runc (segs : list Segment) (c : mr_consts) (fuel : nat) (S : sstate) : list leaf := ltac2:(tb__ "0|1|
S5S2S38A1M0A1G0Lx;S3aVsegs;Vfuel;S50Vc;A1VS;S4A5G0R1Ll;S1S38A1X5x2").
Definition lf0 (l : list leaf) (i : nat) (d : sstate) : sstate := ltac2:(tb__ "0|0|
S3cSc9S38Vi;Vl;S40Vd;S3fA2A4A1").
Definition sh (L : leaf) : Z * stop_reason := ltac2:(tb__ "0|0|
S7S41S39S1fS3cVL;A1A1S3dVL;A1A4").
Definition reg (S : sstate) (r : nat) : sv := ltac2:(tb__ "0|0|
Sc9S12Vr;S23VS;A1SfZ0A1A4").
Definition strip_base (e : sv) : sv := match e with SAlu ALU_ADD a (SLit _) => a | _ => e end.
Definition sdiff (S S' : sstate) : list (sv * sv) * list sprop := ltac2:(tb__ "0|4|
S5SaS2SaS12S12A2M0A1M1S2S10A1M2A2M3A1G3Lx;S111VS;VS';A2G3R1Lp;S7G1G2S1G0A1S0S10S1dS34A1S1S10A1A3A4X5x2").

Fixpoint leqb {A} (f : A -> A -> bool) (l l' : list A) : bool :=
  match l, l' with
  | [], [] => true
  | x :: t, y :: t' => f x y && leqb f t t'
  | _, _ => false
  end.
Lemma leqb_sound {A} (f : A -> A -> bool) : ltac2:(tb__ "0|1|
VA;VA;S44S6Vf;R2R1A2S4A3S44VA;R3R2A3F_;Fy;Fx;S2VA;A1M0G0S44S6S55VA;Vf;R2R1A4S4A3S44G0R3R2A3F_;Fl';Fl;F_;").
Proof. intros Hf. induction l as [|x t IH]; intros [|y t'] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (Hf _ _ H1), (IH _ H2). reflexivity. Qed.

Module RP.
Definition c := MR_P. Definition segs := segsU.
Definition d0 : sstate := C0 c VL.

Definition L0 (kd : vkind) : list leaf := Eval vm_compute in match kd with VL => runc segs c 400 (C0 c VL) | VM0 => runc segs c 400 (C0 c VM0) | VM1 => runc segs c 400 (C0 c VM1) end.
Lemma run0 : ltac2:(tb__ "0|1|
S4eS44S5S2S38A1M0A1S3aS71U190S50S70A1S64S70R1A2S4A5S8G0S75R1A1A2A3Fkd;").
Proof. intros [| |]; OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.
Lemma L0_shape : ltac2:(tb__ "0|1|
S4eS44S2SaS41S39A2M0A1Sc8S38G0S51S75R1A1A4S0G0S7S41S39S56S70A1S3bA4S0G0S7S41S39S5eS70A1S3bA4S1G0A1A3A3A3Fkd;").
Proof. intros [| |]; match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition L0s (kd : vkind) : sstate := Eval vm_compute in match kd with VL => lf0 (L0 VL) 0 d0 | VM0 => lf0 (L0 VM0) 0 d0 | VM1 => lf0 (L0 VM1) 0 d0 end.
Definition L0k (kd : vkind) : sstate := Eval vm_compute in match kd with VL => lf0 (L0 VL) 1 d0 | VM0 => lf0 (L0 VM0) 1 d0 | VM1 => lf0 (L0 VM1) 1 d0 end.

Definition Ck (kd : vkind) : sstate := Eval vm_compute in match kd with VL => restate (L0k VL) (mr_ck c) [(20%nat, v 149)] 0 [SPUle (SLit 10) (v 149); SPUle (v 149) (SLit 8190)] | VM0 => restate (L0k VM0) (mr_ck c) [(20%nat, v 149)] 0 [SPUle (SLit 10) (v 149); SPUle (v 149) (SLit 8190)] | VM1 => restate (L0k VM1) (mr_ck c) [(20%nat, v 149)] 0 [SPUle (SLit 10) (v 149); SPUle (v 149) (SLit 8190)] end.
Definition D0k (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (L0k VL) (Ck VL) | VM0 => sdiff (L0k VM0) (Ck VM0) | VM1 => sdiff (L0k VM1) (Ck VM1) end.
Definition L1 (kd : vkind) : list leaf := Eval vm_compute in match kd with VL => runc segs c 100 (Ck VL) | VM0 => runc segs c 100 (Ck VM0) | VM1 => runc segs c 100 (Ck VM1) end.
Lemma run1 : ltac2:(tb__ "0|1|
S4eS44S5S2S38A1M0A1S3aS71U64S50S70A1S8aR1A1S4A5S8G0S76R1A1A2A3Fkd;").
Proof. intros [| |]; OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.
Lemma L1_shape : ltac2:(tb__ "0|1|
S4eS44S2SaS41S39A2M0A1Sc8S38G0S51S76R1A1A4S0G0S7S41S39S5aS70A1S3bA4S1G0A1A3A3Fkd;").
Proof. intros [| |]; match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition L1s (kd : vkind) : sstate := Eval vm_compute in match kd with VL => lf0 (L1 VL) 0 d0 | VM0 => lf0 (L1 VM0) 0 d0 | VM1 => lf0 (L1 VM1) 0 d0 end.
Definition T1 : sv := Eval vm_compute in reg (L1s VL) 10.

Definition C1 (kd : vkind) : sstate := Eval vm_compute in match kd with VL => restate (L1s VL) (mr_c1 c) [(10%nat, v 160)] 0 [] | VM0 => restate (L1s VM0) (mr_c1 c) [(10%nat, v 160)] 0 [] | VM1 => restate (L1s VM1) (mr_c1 c) [(10%nat, v 160)] 0 [] end.
Definition D11 (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (L1s VL) (C1 VL) | VM0 => sdiff (L1s VM0) (C1 VM0) | VM1 => sdiff (L1s VM1) (C1 VM1) end.
Definition L2 (kd : vkind) : list leaf := Eval vm_compute in match kd with VL => runc segs c 100 (C1 VL) | VM0 => runc segs c 100 (C1 VM0) | VM1 => runc segs c 100 (C1 VM1) end.
Lemma run2 : ltac2:(tb__ "0|1|
S4eS44S5S2S38A1M0A1S3aS71U64S50S70A1S7fR1A1S4A5S8G0S77R1A1A2A3Fkd;").
Proof. intros [| |]; OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.
Lemma L2_shape : ltac2:(tb__ "0|1|
S4eS44S2SaS41S39A2M0A1Sc8S38G0S51S77R1A1A4S0G0S7S41S39S5bS70A1S3bA4S1G0A1A3A3Fkd;").
Proof. intros [| |]; match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition L2s (kd : vkind) : sstate := Eval vm_compute in match kd with VL => lf0 (L2 VL) 0 d0 | VM0 => lf0 (L2 VM0) 0 d0 | VM1 => lf0 (L2 VM1) 0 d0 end.
Definition T2 : sv := Eval vm_compute in reg (L2s VL) 10.

Definition C2 (kd : vkind) : sstate := Eval vm_compute in match kd with VL => restate (L2s VL) (mr_c2 c) [(10%nat, v 161)] 0 [] | VM0 => restate (L2s VM0) (mr_c2 c) [(10%nat, v 161)] 0 [] | VM1 => restate (L2s VM1) (mr_c2 c) [(10%nat, v 161)] 0 [] end.
Definition D22 (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (L2s VL) (C2 VL) | VM0 => sdiff (L2s VM0) (C2 VM0) | VM1 => sdiff (L2s VM1) (C2 VM1) end.
Definition L3 (kd : vkind) : list leaf := Eval vm_compute in match kd with VL => runc segs c 100 (C2 VL) | VM0 => runc segs c 100 (C2 VM0) | VM1 => runc segs c 100 (C2 VM1) end.
Lemma run3 : ltac2:(tb__ "0|1|
S4eS44S5S2S38A1M0A1S3aS71U64S50S70A1S80R1A1S4A5S8G0S78R1A1A2A3Fkd;").
Proof. intros [| |]; OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.
Lemma L3_shape : ltac2:(tb__ "0|1|
S4eS44S2SaS41S39A2M0A1Sc8S38G0S51S78R1A1A4S0G0S7S41S39S5cS70A1S3bA4S1G0A1A3A3Fkd;").
Proof. intros [| |]; match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition L3s (kd : vkind) : sstate := Eval vm_compute in match kd with VL => lf0 (L3 VL) 0 d0 | VM0 => lf0 (L3 VM0) 0 d0 | VM1 => lf0 (L3 VM1) 0 d0 end.
Definition T3 : sv := Eval vm_compute in reg (L3s VL) 10.

Definition Tidx : sv := Eval vm_compute in
  strip_base (reg (lf0 (match sym_run segs 100 [0x21048; 0x21048 + 0x740] (restate (L3s VL) (mr_c3 c) [(10%nat, v 162)] 0 []) true with Some l => l | None => [] end) 0 d0) 10).
Definition F3 : list sprop := ltac2:(tb__ "0|0|
S0S10S11S8eSfZ1fA1A2S1S10A1A3").
Definition C3 (kd : vkind) : sstate := Eval vm_compute in match kd with VL => restate (L3s VL) (mr_c3 c) [(10%nat, v 162)] 0 F3 | VM0 => restate (L3s VM0) (mr_c3 c) [(10%nat, v 162)] 0 F3 | VM1 => restate (L3s VM1) (mr_c3 c) [(10%nat, v 162)] 0 F3 end.
Definition D33 (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (L3s VL) (C3 VL) | VM0 => sdiff (L3s VM0) (C3 VM0) | VM1 => sdiff (L3s VM1) (C3 VM1) end.
Definition L4 (kd : vkind) : list leaf := Eval vm_compute in match kd with VL => runc segs c 100 (C3 VL) | VM0 => runc segs c 100 (C3 VM0) | VM1 => runc segs c 100 (C3 VM1) end.
Lemma run4 : ltac2:(tb__ "0|1|
S4eS44S5S2S38A1M0A1S3aS71U64S50S70A1S81R1A1S4A5S8G0S79R1A1A2A3Fkd;").
Proof. intros [| |]; OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.
Lemma L4_shape : ltac2:(tb__ "0|1|
S4eS44S2SaS41S39A2M0A1Sc8S38G0S51S79R1A1A4S0G0S7S41S39S5dS70A1S3bA4S1G0A1A3A3Fkd;").
Proof. intros [| |]; match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition L4s (kd : vkind) : sstate := Eval vm_compute in match kd with VL => lf0 (L4 VL) 0 d0 | VM0 => lf0 (L4 VM0) 0 d0 | VM1 => lf0 (L4 VM1) 0 d0 end.
Definition T4 : sv := Eval vm_compute in reg (L4s VL) 10.

Definition Tlhu1 : sv := Eval vm_compute in
  strip_base (reg (lf0 (match sym_run segs 100 [mr_lhu1 c] (restate (L4s VL) (mr_c4 c) [(10%nat, v 163)] 0 []) true with Some l => l | None => [] end) 0 d0) 13).
Definition Tlhu2 : list sv := Eval vm_compute in
  map (fun L => strip_base (reg (lf_state L) 10))
      (List.filter (fun L => ss_pc (lf_state L) =? mr_lhu2 c)
         (match sym_run segs 100 [mr_lhu2 c; mr_c5 c] (restate (L4s VL) (mr_c4 c) [(10%nat, v 163)] 0 [SPUle Tlhu1 (SLit 94)]) true with Some l => l | None => [] end)).
Definition F4 : list sprop := ltac2:(tb__ "0|1|
S0S10S11S8fSfZ5eA1M0A2Sc8S12S10S12S11R1G0A2Le;S90A4A3").
Definition C4 (kd : vkind) : sstate := Eval vm_compute in match kd with VL => restate (L4s VL) (mr_c4 c) [(10%nat, v 163)] 0 F4 | VM0 => restate (L4s VM0) (mr_c4 c) [(10%nat, v 163)] 0 F4 | VM1 => restate (L4s VM1) (mr_c4 c) [(10%nat, v 163)] 0 F4 end.
Definition D44 (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (L4s VL) (C4 VL) | VM0 => sdiff (L4s VM0) (C4 VM0) | VM1 => sdiff (L4s VM1) (C4 VM1) end.
Definition L5 (kd : vkind) : list leaf := Eval vm_compute in match kd with VL => runc segs c 100 (C4 VL) | VM0 => runc segs c 100 (C4 VM0) | VM1 => runc segs c 100 (C4 VM1) end.
Lemma run5 : ltac2:(tb__ "0|1|
S4eS44S5S2S38A1M0A1S3aS71U64S50S70A1S82R1A1S4A5S8G0S7aR1A1A2A3Fkd;").
Proof. intros [| |]; OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.
Lemma L5_shape : ltac2:(tb__ "0|2|
S4eS44S2SaS41S39A2M0A1Sc8S38G0S51S7aR1A1A4S0G0S7S41S39S56S70A1S3bA4M1S0G0G1S1G0A1A3A3A3Fkd;").
Proof. intros [| |]; match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition L5a (kd : vkind) : sstate := Eval vm_compute in match kd with VL => lf0 (L5 VL) 0 d0 | VM0 => lf0 (L5 VM0) 0 d0 | VM1 => lf0 (L5 VM1) 0 d0 end.
Definition L5b (kd : vkind) : sstate := Eval vm_compute in match kd with VL => lf0 (L5 VL) 1 d0 | VM0 => lf0 (L5 VM0) 1 d0 | VM1 => lf0 (L5 VM1) 1 d0 end.
Definition T5a : sv := Eval vm_compute in reg (L5a VL) 20.
Definition T5b : sv := Eval vm_compute in reg (L5b VL) 20.
Definition P5a : list sprop := Eval vm_compute in firstn 1 (ss_facts (L5a VL)).
Definition P5b : list sprop := Eval vm_compute in firstn 1 (ss_facts (L5b VL)).

Definition C5 (kd : vkind) : sstate := Eval vm_compute in match kd with VL => restateF (L5a VL) (mr_c5 c) [(20%nat, v 150); (10%nat, SVar 200); (11%nat, SVar 201); (12%nat, SVar 202); (13%nat, SVar 203)] (F_all VL) | VM0 => restateF (L5a VM0) (mr_c5 c) [(20%nat, v 150); (10%nat, SVar 200); (11%nat, SVar 201); (12%nat, SVar 202); (13%nat, SVar 203)] (F_all VM0) | VM1 => restateF (L5a VM1) (mr_c5 c) [(20%nat, v 150); (10%nat, SVar 200); (11%nat, SVar 201); (12%nat, SVar 202); (13%nat, SVar 203)] (F_all VM1) end.

Definition D05 (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (L0s VL) (C5 VL) | VM0 => sdiff (L0s VM0) (C5 VM0) | VM1 => sdiff (L0s VM1) (C5 VM1) end.
Definition D5a (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (L5a VL) (C5 VL) | VM0 => sdiff (L5a VM0) (C5 VM0) | VM1 => sdiff (L5a VM1) (C5 VM1) end.
Definition D5b (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (L5b VL) (C5 VL) | VM0 => sdiff (L5b VM0) (C5 VM0) | VM1 => sdiff (L5b VM1) (C5 VM1) end.
Definition L6 (kd : vkind) : list leaf := Eval vm_compute in match kd with VL => runc segs c 400 (C5 VL) | VM0 => runc segs c 400 (C5 VM0) | VM1 => runc segs c 400 (C5 VM1) end.
Lemma run6 : ltac2:(tb__ "0|1|
S4eS44S5S2S38A1M0A1S3aS71U190S50S70A1S83R1A1S4A5S8G0S7cR1A1A2A3Fkd;").
Proof. intros [| |]; OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.
Lemma L6_shape : ltac2:(tb__ "0|1|
S4eS44S2SaS41S39A2M0A1Sc8S38G0S51S7cR1A1A4S0G0S7S41S39S57S70A1S3bA4S1G0A1A3A3Fkd;").
Proof. intros [| |]; match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition L6s (kd : vkind) : sstate := Eval vm_compute in match kd with VL => lf0 (L6 VL) 0 d0 | VM0 => lf0 (L6 VM0) 0 d0 | VM1 => lf0 (L6 VM1) 0 d0 end.
Definition T6 : sv := Eval vm_compute in reg (L6s VL) 11.

Definition C5q (kd : vkind) : sstate := Eval vm_compute in match kd with VL => restateF (L5a VL) (mr_c5 c) [(20%nat, v 164); (10%nat, SVar 200); (11%nat, SVar 201); (12%nat, SVar 202); (13%nat, SVar 203)] (F_all VL ++ F5) | VM0 => restateF (L5a VM0) (mr_c5 c) [(20%nat, v 164); (10%nat, SVar 200); (11%nat, SVar 201); (12%nat, SVar 202); (13%nat, SVar 203)] (F_all VM0 ++ F5) | VM1 => restateF (L5a VM1) (mr_c5 c) [(20%nat, v 164); (10%nat, SVar 200); (11%nat, SVar 201); (12%nat, SVar 202); (13%nat, SVar 203)] (F_all VM1 ++ F5) end.
Definition D05q (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (L0s VL) (C5q VL) | VM0 => sdiff (L0s VM0) (C5q VM0) | VM1 => sdiff (L0s VM1) (C5q VM1) end.
Definition D5aq (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (L5a VL) (C5q VL) | VM0 => sdiff (L5a VM0) (C5q VM0) | VM1 => sdiff (L5a VM1) (C5q VM1) end.
Definition D5bq (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (L5b VL) (C5q VL) | VM0 => sdiff (L5b VM0) (C5q VM0) | VM1 => sdiff (L5b VM1) (C5q VM1) end.
Definition L5q (kd : vkind) : list leaf := Eval vm_compute in match kd with VL => runc segs c 100 (C5q VL) | VM0 => runc segs c 100 (C5q VM0) | VM1 => runc segs c 100 (C5q VM1) end.
Lemma run5q : ltac2:(tb__ "0|1|
S4eS44S5S2S38A1M0A1S3aS71U64S50S70A1S85R1A1S4A5S8G0S7bR1A1A2A3Fkd;").
Proof. intros [| |]; OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.
Lemma L5q_shape : ltac2:(tb__ "0|1|
S4eS44S2SaS41S39A2M0A1Sc8S38G0S51S7bR1A1A4S0G0S7S41S39S60S70A1S3bA4S1G0A1A3A3Fkd;").
Proof. intros [| |]; match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition L5qs (kd : vkind) : sstate := Eval vm_compute in match kd with VL => lf0 (L5q VL) 0 d0 | VM0 => lf0 (L5q VM0) 0 d0 | VM1 => lf0 (L5q VM1) 0 d0 end.

Definition C5o (kd : vkind) : sstate := Eval vm_compute in match kd with VL => restate (L5qs VL) (mr_ori c) [(10%nat, v 150)] 0 [] | VM0 => restate (L5qs VM0) (mr_ori c) [(10%nat, v 150)] 0 [] | VM1 => restate (L5qs VM1) (mr_ori c) [(10%nat, v 150)] 0 [] end.
Definition D5o (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (L5qs VL) (C5o VL) | VM0 => sdiff (L5qs VM0) (C5o VM0) | VM1 => sdiff (L5qs VM1) (C5o VM1) end.
Definition L6o (kd : vkind) : list leaf := Eval vm_compute in match kd with VL => runc segs c 400 (C5o VL) | VM0 => runc segs c 400 (C5o VM0) | VM1 => runc segs c 400 (C5o VM1) end.
Lemma run6o : ltac2:(tb__ "0|1|
S4eS44S5S2S38A1M0A1S3aS71U190S50S70A1S84R1A1S4A5S8G0S7dR1A1A2A3Fkd;").
Proof. intros [| |]; OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.
Lemma L6o_shape : ltac2:(tb__ "0|1|
S4eS44S2SaS41S39A2M0A1Sc8S38G0S51S7dR1A1A4S0G0S7S41S39S57S70A1S3bA4S1G0A1A3A3Fkd;").
Proof. intros [| |]; match goal with |- ?L = _ => vm_cast_no_check (@eq_refl (list (Z * stop_reason)) L) end. Qed.
Definition L6os (kd : vkind) : sstate := Eval vm_compute in match kd with VL => lf0 (L6o VL) 0 d0 | VM0 => lf0 (L6o VM0) 0 d0 | VM1 => lf0 (L6o VM1) 0 d0 end.

Definition C6 (kd : vkind) : sstate := Eval vm_compute in match kd with VL => restateF (L6s VL) (mr_enframe c) [(11%nat, v 157)] (F_all VL) | VM0 => restateF (L6s VM0) (mr_enframe c) [(11%nat, v 157)] (F_all VM0) | VM1 => restateF (L6s VM1) (mr_enframe c) [(11%nat, v 157)] (F_all VM1) end.
Definition D66 (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (L6s VL) (C6 VL) | VM0 => sdiff (L6s VM0) (C6 VM0) | VM1 => sdiff (L6s VM1) (C6 VM1) end.
Definition D6o (kd : vkind) := Eval vm_compute in match kd with VL => sdiff (L6os VL) (C6 VL) | VM0 => sdiff (L6os VM0) (C6 VM0) | VM1 => sdiff (L6os VM1) (C6 VM1) end.
Definition L7 (kd : vkind) : list leaf := Eval vm_compute in match kd with VL => runc segs c 200 (C6 VL) | VM0 => runc segs c 200 (C6 VM0) | VM1 => runc segs c 200 (C6 VM1) end.
Lemma run7 : ltac2:(tb__ "0|1|
S4eS44S5S2S38A1M0A1S3aS71Uc8S50S70A1S86R1A1S4A5S8G0S72R1A1A2A3Fkd;").
Proof. intros [| |]; OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.

Definition l7_ok (L : leaf) : bool := ltac2:(tb__ "0|1|
S39S6Lx;S3dVL;A1S3S4bS1fS3cVL;A1A1M0S5fS70A1A2S3S3S3S4bG0S6aS70A1A2S3X39x7").
Lemma L7_shape : ltac2:(tb__ "0|0|
S4eS44S6S109S38S91S72R1A1A3S4A3Fkd;").
Proof. intros [| |]; vm_cast_no_check (@eq_refl bool true). Qed.
Definition L7s (kd : vkind) : sstate := Eval vm_compute in match kd with VL => lf0 (L7 VL) 0 d0 | VM0 => lf0 (L7 VM0) 0 d0 | VM1 => lf0 (L7 VM1) 0 d0 end.

Definition l7_same (kd : vkind) (L : leaf) : bool := ltac2:(tb__ "0|2|
S39S6Lx;S3dVL;A1S4ScScScS109SbSbSeSeSeS108R1U5A2S108R1UdA2A2S108R1U11A2A2S25S63S3cVL;A1M0R1A2S63S8bVkd;A1M1R1A2A2A2Li;ScaU0U20A2A3S55S12S25S21G0A1S21G1A1A4A2S55S14S14S14ScScScScS25S2dR2A1S2dR1A1A2S55S13S112S2eR2A1S2eR1A1A4A2S25S31R2A1S31R1A1A2A2S25S30R2A1S30R1A1A2A2S113S2fR2A1S2fR1A1A2A2Lo';Lo;S22G0A1S22G1A1A4A2S114S1eG0A1S1eG1A1A2A2S4S4S4S4S4X39x7").
Lemma L7_same : ltac2:(tb__ "0|0|
S4eS44S6S109S38S92R1A1S72R1A1A3S4A3Fkd;").
Proof. intros [| |]; vm_cast_no_check (@eq_refl bool true). Qed.

Definition C7base (kd : vkind) : sstate := Eval vm_compute in match kd with VL => restateF (L7s VL) (mr_cutB c) [(17%nat, v 158); (5%nat, SVar 204); (13%nat, SVar 205)] (F_all VL) | VM0 => restateF (L7s VM0) (mr_cutB c) [(17%nat, v 158); (5%nat, SVar 204); (13%nat, SVar 205)] (F_all VM0) | VM1 => restateF (L7s VM1) (mr_cutB c) [(17%nat, v 158); (5%nat, SVar 204); (13%nat, SVar 205)] (F_all VM1) end.
Definition C7 (kd : vkind) (o : voff) (r : vrsv) : sstate := ltac2:(tb__ "0|1|
S1bS1fS88Vkd;A1M0A1S23G0A1S21G0A1S1cSdS12A1S22G0A1S9S10S28G0A1S65Vkd;Vo;Vr;A3A3S54S3A9").
Definition L8 (kd : vkind) (o : voff) (r : vrsv) : list leaf := Eval vm_compute in
  match kd, o, r with | VL, O0, RZ => runc segs c 200 (C7 VL O0 RZ) | VL, O0, R14 => runc segs c 200 (C7 VL O0 R14) | VL, O0, R5 => runc segs c 200 (C7 VL O0 R5) | VL, O0, RG => runc segs c 200 (C7 VL O0 RG) | VL, O1, RZ => runc segs c 200 (C7 VL O1 RZ) | VL, O1, R14 => runc segs c 200 (C7 VL O1 R14) | VL, O1, R5 => runc segs c 200 (C7 VL O1 R5) | VL, O1, RG => runc segs c 200 (C7 VL O1 RG) | VM0, O0, RZ => runc segs c 200 (C7 VM0 O0 RZ) | VM0, O0, R14 => runc segs c 200 (C7 VM0 O0 R14) | VM0, O0, R5 => runc segs c 200 (C7 VM0 O0 R5) | VM0, O0, RG => runc segs c 200 (C7 VM0 O0 RG) | VM0, O1, RZ => runc segs c 200 (C7 VM0 O1 RZ) | VM0, O1, R14 => runc segs c 200 (C7 VM0 O1 R14) | VM0, O1, R5 => runc segs c 200 (C7 VM0 O1 R5) | VM0, O1, RG => runc segs c 200 (C7 VM0 O1 RG) | VM1, O0, RZ => runc segs c 200 (C7 VM1 O0 RZ) | VM1, O0, R14 => runc segs c 200 (C7 VM1 O0 R14) | VM1, O0, R5 => runc segs c 200 (C7 VM1 O0 R5) | VM1, O0, RG => runc segs c 200 (C7 VM1 O0 RG) | VM1, O1, RZ => runc segs c 200 (C7 VM1 O1 RZ) | VM1, O1, R14 => runc segs c 200 (C7 VM1 O1 R14) | VM1, O1, R5 => runc segs c 200 (C7 VM1 O1 R5) | VM1, O1, RG => runc segs c 200 (C7 VM1 O1 RG) end.
Lemma run8 : ltac2:(tb__ "0|1|
S4eS52S4fS44S5S2S38A1M0A1S3aS71Uc8S50S70A1S87R3R2R1A3S4A5S8G0S73R3R2R1A3A2A3Fr;Fo;Fkd;").
Proof. intros kd o r; destruct kd, o, r; OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.
Definition l8_stop (r : vrsv) : Z * stop_reason := ltac2:(tb__ "0|1|
S4fSaS41S39A2Lr;Vr;S7S41S39S61S70A1S3eA4S7S41S39S62S70A1S3bA4M0G0G0X4fx4").
Lemma L8_shape : ltac2:(tb__ "0|1|
S4eS52S4fS44S2SaS41S39A2M0A1Sc8S38G0S51S73R3R2R1A3A4S0G0S93R1A1S1G0A1A3A3Fr;Fo;Fkd;").
Proof. intros kd o r; destruct kd, o, r; match goal with |- ?L = ?R => let v := eval vm_compute in R in vm_cast_no_check (@eq_refl (list (Z * stop_reason)) v) end. Qed.
Definition L8s (kd : vkind) (o : voff) (r : vrsv) : sstate := ltac2:(tb__ "0|0|
S59S73Vkd;Vo;Vr;A3U0S7eA3").

Definition C8 (kd : vkind) (o : voff) (r : vrsv) : sstate := Eval vm_compute in
  match kd, o, r with | VL, O0, RZ => restate (L8s VL O0 RZ) (mr_sb c) [(12%nat, E_pn VL O0)] 0 [] | VL, O0, R14 => restate (L8s VL O0 R14) (mr_sb c) [(12%nat, E_pn VL O0)] 0 [] | VL, O0, R5 => restate (L8s VL O0 R5) (mr_sb c) [(12%nat, E_pn VL O0)] 0 [] | VL, O0, RG => restate (L8s VL O0 RG) (mr_sb c) [(12%nat, E_pn VL O0)] 0 [] | VL, O1, RZ => restate (L8s VL O1 RZ) (mr_sb c) [(12%nat, E_pn VL O1)] 0 [] | VL, O1, R14 => restate (L8s VL O1 R14) (mr_sb c) [(12%nat, E_pn VL O1)] 0 [] | VL, O1, R5 => restate (L8s VL O1 R5) (mr_sb c) [(12%nat, E_pn VL O1)] 0 [] | VL, O1, RG => restate (L8s VL O1 RG) (mr_sb c) [(12%nat, E_pn VL O1)] 0 [] | VM0, O0, RZ => restate (L8s VM0 O0 RZ) (mr_sb c) [(12%nat, E_pn VM0 O0)] 0 [] | VM0, O0, R14 => restate (L8s VM0 O0 R14) (mr_sb c) [(12%nat, E_pn VM0 O0)] 0 [] | VM0, O0, R5 => restate (L8s VM0 O0 R5) (mr_sb c) [(12%nat, E_pn VM0 O0)] 0 [] | VM0, O0, RG => restate (L8s VM0 O0 RG) (mr_sb c) [(12%nat, E_pn VM0 O0)] 0 [] | VM0, O1, RZ => restate (L8s VM0 O1 RZ) (mr_sb c) [(12%nat, E_pn VM0 O1)] 0 [] | VM0, O1, R14 => restate (L8s VM0 O1 R14) (mr_sb c) [(12%nat, E_pn VM0 O1)] 0 [] | VM0, O1, R5 => restate (L8s VM0 O1 R5) (mr_sb c) [(12%nat, E_pn VM0 O1)] 0 [] | VM0, O1, RG => restate (L8s VM0 O1 RG) (mr_sb c) [(12%nat, E_pn VM0 O1)] 0 [] | VM1, O0, RZ => restate (L8s VM1 O0 RZ) (mr_sb c) [(12%nat, E_pn VM1 O0)] 0 [] | VM1, O0, R14 => restate (L8s VM1 O0 R14) (mr_sb c) [(12%nat, E_pn VM1 O0)] 0 [] | VM1, O0, R5 => restate (L8s VM1 O0 R5) (mr_sb c) [(12%nat, E_pn VM1 O0)] 0 [] | VM1, O0, RG => restate (L8s VM1 O0 RG) (mr_sb c) [(12%nat, E_pn VM1 O0)] 0 [] | VM1, O1, RZ => restate (L8s VM1 O1 RZ) (mr_sb c) [(12%nat, E_pn VM1 O1)] 0 [] | VM1, O1, R14 => restate (L8s VM1 O1 R14) (mr_sb c) [(12%nat, E_pn VM1 O1)] 0 [] | VM1, O1, R5 => restate (L8s VM1 O1 R5) (mr_sb c) [(12%nat, E_pn VM1 O1)] 0 [] | VM1, O1, RG => restate (L8s VM1 O1 RG) (mr_sb c) [(12%nat, E_pn VM1 O1)] 0 [] end.
Definition D88 (kd : vkind) (o : voff) (r : vrsv) := Eval vm_compute in
  match kd, o, r with | VL, O0, RZ => sdiff (L8s VL O0 RZ) (C8 VL O0 RZ) | VL, O0, R14 => sdiff (L8s VL O0 R14) (C8 VL O0 R14) | VL, O0, R5 => sdiff (L8s VL O0 R5) (C8 VL O0 R5) | VL, O0, RG => sdiff (L8s VL O0 RG) (C8 VL O0 RG) | VL, O1, RZ => sdiff (L8s VL O1 RZ) (C8 VL O1 RZ) | VL, O1, R14 => sdiff (L8s VL O1 R14) (C8 VL O1 R14) | VL, O1, R5 => sdiff (L8s VL O1 R5) (C8 VL O1 R5) | VL, O1, RG => sdiff (L8s VL O1 RG) (C8 VL O1 RG) | VM0, O0, RZ => sdiff (L8s VM0 O0 RZ) (C8 VM0 O0 RZ) | VM0, O0, R14 => sdiff (L8s VM0 O0 R14) (C8 VM0 O0 R14) | VM0, O0, R5 => sdiff (L8s VM0 O0 R5) (C8 VM0 O0 R5) | VM0, O0, RG => sdiff (L8s VM0 O0 RG) (C8 VM0 O0 RG) | VM0, O1, RZ => sdiff (L8s VM0 O1 RZ) (C8 VM0 O1 RZ) | VM0, O1, R14 => sdiff (L8s VM0 O1 R14) (C8 VM0 O1 R14) | VM0, O1, R5 => sdiff (L8s VM0 O1 R5) (C8 VM0 O1 R5) | VM0, O1, RG => sdiff (L8s VM0 O1 RG) (C8 VM0 O1 RG) | VM1, O0, RZ => sdiff (L8s VM1 O0 RZ) (C8 VM1 O0 RZ) | VM1, O0, R14 => sdiff (L8s VM1 O0 R14) (C8 VM1 O0 R14) | VM1, O0, R5 => sdiff (L8s VM1 O0 R5) (C8 VM1 O0 R5) | VM1, O0, RG => sdiff (L8s VM1 O0 RG) (C8 VM1 O0 RG) | VM1, O1, RZ => sdiff (L8s VM1 O1 RZ) (C8 VM1 O1 RZ) | VM1, O1, R14 => sdiff (L8s VM1 O1 R14) (C8 VM1 O1 R14) | VM1, O1, R5 => sdiff (L8s VM1 O1 R5) (C8 VM1 O1 R5) | VM1, O1, RG => sdiff (L8s VM1 O1 RG) (C8 VM1 O1 RG) end.
Definition L9 (kd : vkind) (o : voff) (r : vrsv) : list leaf := Eval vm_compute in
  match kd, o, r with | VL, O0, RZ => [] | VL, O0, R14 => runc segs c 100 (C8 VL O0 R14) | VL, O0, R5 => runc segs c 100 (C8 VL O0 R5) | VL, O0, RG => runc segs c 100 (C8 VL O0 RG) | VL, O1, RZ => [] | VL, O1, R14 => runc segs c 100 (C8 VL O1 R14) | VL, O1, R5 => runc segs c 100 (C8 VL O1 R5) | VL, O1, RG => runc segs c 100 (C8 VL O1 RG) | VM0, O0, RZ => [] | VM0, O0, R14 => runc segs c 100 (C8 VM0 O0 R14) | VM0, O0, R5 => runc segs c 100 (C8 VM0 O0 R5) | VM0, O0, RG => runc segs c 100 (C8 VM0 O0 RG) | VM0, O1, RZ => [] | VM0, O1, R14 => runc segs c 100 (C8 VM0 O1 R14) | VM0, O1, R5 => runc segs c 100 (C8 VM0 O1 R5) | VM0, O1, RG => runc segs c 100 (C8 VM0 O1 RG) | VM1, O0, RZ => [] | VM1, O0, R14 => runc segs c 100 (C8 VM1 O0 R14) | VM1, O0, R5 => runc segs c 100 (C8 VM1 O0 R5) | VM1, O0, RG => runc segs c 100 (C8 VM1 O0 RG) | VM1, O1, RZ => [] | VM1, O1, R14 => runc segs c 100 (C8 VM1 O1 R14) | VM1, O1, R5 => runc segs c 100 (C8 VM1 O1 R5) | VM1, O1, RG => runc segs c 100 (C8 VM1 O1 RG) end.
Lemma run9 : ltac2:(tb__ "0|1|
S4eS52S4fS47S44S4fR1S58A3A1S44S5S2S38A1M0A1S3aS71U64S50S70A1S89R4R3R2A3S4A5S8G0S74R4R3R2A3A2A3F_;Fr;Fo;Fkd;").
Proof. intros kd o r Hr; destruct kd, o, r; try (exfalso; exact (Hr eq_refl)); OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.
Lemma L9_shape : ltac2:(tb__ "0|1|
S4eS52S4fS47S44S4fR1S58A3A1S44S2SaS41S39A2M0A1Sc8S38G0S51S74R4R3R2A3A4S0G0S7S41S39S61S70A1S3eA4S1G0A1A3A3F_;Fr;Fo;Fkd;").
Proof. intros kd o r Hr; destruct kd, o, r; try (exfalso; exact (Hr eq_refl)); vm_cast_no_check (@eq_refl (list (Z * stop_reason)) [(mr_ret c, RsSymJump)]). Qed.
Definition L9s (kd : vkind) (o : voff) (r : vrsv) : sstate := ltac2:(tb__ "0|0|
S59S74Vkd;Vo;Vr;A3U0S7eA3").

Definition LF (kd : vkind) (o : voff) (r : vrsv) : sstate := ltac2:(tb__ "0|1|
S4fS24Lr;Vr;S8cVkd;Vo;Vr;A3S8dVkd;Vo;Vr;A3M0G0G0X4fx4").
End RP.
End Mal_malloc_fast_runs.
