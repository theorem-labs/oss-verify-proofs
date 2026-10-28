(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "SAlu"; "SPUle"; "sobj"; "SPBranch"; "SPNot"; "ss_lenient"; "ss_objs"; "swf"; "mkSS"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "ss_next"; "sv_eqb"; "DUnknown"; "SPAlign"; "smatch"; "sprop_eqb"; "SExt"; "SLBytes"; "holds"; "mkObj"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "sstate"; "valuation"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "bool"; "list"; "app"; "true"; "prod"; "andb"; "nil"; "option"; "false"; "Some"; "None"; "negb"; "fst"; "length"; "snd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "od2"; "zl2"; "zr2"; "obj_of2"; "ia_mW"; "rho2"; "seqv"; "D_seq"; "D_useq"; "ia_erv"; "od2_entry"; "D_bnc"; "D_ctr"; "D_errno"; "D_usg2"; "bnc"; "ia_sc"; "icnt0"; "ij"; "inos"; "isize"; "iszc"; "live"; "od2_pairwise"; "D_act0"; "D_got"; "D_guard"; "D_m"; "D_med"; "D_pgs"; "D_s2c"; "D_sct"; "D_small"; "D_usg"; "ctr"; "od2_wf"; "useq"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "div"; "leb"; "mul"; "pow"; "eqb"; "ltb"; "modulo"; "opp"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_EQ"; "ALU_SUB"; "BC_LT"; "BC_LTU"; "BC_NE"; "ALU_SLTU"; "ALU_XOR"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "SM1pre"; "m1v"; "F_M1"; "F_CTX"; "F_G"; "F_M"; "F_SZ"; "SN2pre"; "O_stk"; "SCsym"; "SM1"; "NXA"; "objsCs"; "objsM1"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost"; "mm_pre"; "ab_post"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zholds"; "psupported"; "toS"; "zeval"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "firstn"; "repeat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg"; "POST"; "setp"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M.M"; "bAm"; "bBm"; "bRm"; "s_ab"; "locsM"; "s_mm"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M"; "m1_hi"; "m1_lo"; "dsCs"; "dsX"; "dsP"; "has_fact"; "dsM1"; "recarved"; "ods_eqb"; "stk_shape"; "with_facts"; "D_m0"; "dsC_exp"; "m1_leaf_chk"; "stk_only"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "rhoW"; "@stdpp.bitvector.definitions"; "bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "diffs_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "PGSZ"; "UNIT"; "astate"; "mslot"; "set_seq"; "st_bounces"; "st_seq"; "st_unmap_seq"; "usage_of"; "MFree"; "MRaw"; "bounce_idx"; "set_bounces"; "set_unmap_seq"; "st_mmap_counter"; "znth"; "zset"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup"; "ctx_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "below200"; "agrees"; "in_vars"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "tier";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "MT"; "CTX_bounces"; "Inv"; "LCtx"; "active_hd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2"; "SM23"; "objsM23"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "obj_vars_all"; "sprop_vars_all"; "state_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "holds"; "mc_errno"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "odefault_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage"; "seq_locs_b"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "delta"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab"; "objs_matchb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_c6"; "LC_6_0"; "LC_6_1"; "LC_6_2"; "dC_6"; "dL_6_0"; "dL_6_1"; "dL_6_2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC"; "SC_6"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R"; "changed2"; "dcond2b"; "fill2"; "od2_semb"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G7.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G9.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G12.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G13.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G5.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G6.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G8.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G10.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G11.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_agrp_c6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_6 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_6 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_6 : ltac2:(tb__ "0|1|
S5aS2dS2aS27S2aS0S0A2A1S27S3A1A2M0A1SaaS7dSe2A2S2fG0SdeA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_6)). Qed.
Definition setsC_6 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_6)) in exact x).
Definition LC_6_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_6 0 SC_6) in exact x).
Definition dL_6_0 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_6_0 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_6_0 : ltac2:(tb__ "0|1|
S5aS2dS2aS27S2aS0S0A2A1S27S3A1A2M0A1SaaSdbS7bA2S2fG0SdfA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_6_0)). Qed.
Definition setsL_6_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_6_0)) in exact x).
Definition LC_6_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_6 1 SC_6) in exact x).
Definition dL_6_1 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_6_1 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_6_1 : ltac2:(tb__ "0|1|
S5aS2dS2aS27S2aS0S0A2A1S27S3A1A2M0A1SaaSdcS7bA2S2fG0Se0A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_6_1)). Qed.
Definition setsL_6_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_6_1)) in exact x).
Definition LC_6_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_6 2 SC_6) in exact x).
Definition dL_6_2 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_6_2 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_6_2 : ltac2:(tb__ "0|1|
S5aS2dS2aS27S2aS0S0A2A1S27S3A1A2M0A1SaaSddS7bA2S2fG0Se1A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_6_2)). Qed.
Definition setsL_6_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_6_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
Sd4S73VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 6.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S60S62SadZ2A2S5fS4aVia;A1SaeA2A2VTR;VkB;S8fS73VK;Sa8Via;S39Via;A1A2S74A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S5eS5fS64S49Via;A1S46Via;A1A2SaeA2S62SadZ2A2A2Sd5Sc2S47Via;A1M0A1Sc2S45Via;A1A1A2S5bS5eZ0G0A2S60G0Z30A2A2VTR;VkB;S8fS73VK;Sa8Via;S39Via;A1A2S7bA4VQ;A3F_;F_;F_;").

Theorem cls_6 : ltac2:(tb__ "0|0|
VTR;VkB;S8fS73VK;Sa8Via;S39Via;A1A2S7dA4VQ;A3").
Proof using CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_6 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_6 (setp rhoB setsC_6))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_6 w setsC_6 (fst dC_6) (snd dC_6)); [reflexivity | reflexivity | exact sdC_6 | | | exact HSP].
    - cbn [fst dC_6]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_6) (snd dC_6) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_6 LC_6 (setp rhoB setsC_6) Q HkB (eq_trans runC_6 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 72 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 72)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 18).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 6 (usg ia) 18 8 4) by reflexivity.
      change (class_size 6) with 112. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 2028) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 23) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_6 0 SC_6) with LC_6_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_6_0 SN2pre setsL_6_0 (fst dL_6_0) (snd dL_6_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_6_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_6_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_6_0) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 23 2028 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_geu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 32)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 72 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 72))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 8).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 6 (usg ia) 18 8 4) by reflexivity.
      change (class_size 6) with 112. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 908) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 19) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_6 1 SC_6) with LC_6_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_6_1 SN2pre setsL_6_1 (fst dL_6_1) (snd dL_6_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_6_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_6_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_6_1) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 19 908 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 72 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 72))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 4).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 6 (usg ia) 18 8 4) by reflexivity.
      change (class_size 6) with 112. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 460) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 15) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_6 2 SC_6) with LC_6_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_6_2 SN2pre setsL_6_2 (fst dL_6_2) (snd dL_6_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_6_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_6_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_6_2) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 15 460 Hj Htot ltac:(lia) ltac:(lia))).
Qed.
End C.
End Mal_agrp_c6.

Module Mal_agrp_CD.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_c0 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_c1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G7.Mal_agrp_c2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G9.Mal_agrp_c3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G12.Mal_agrp_c4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G13.Mal_agrp_c5 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_c6 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G13.Mal_agrp_c7 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G13.Mal_agrp_c8 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G13.Mal_agrp_c9 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G5.Mal_agrp_c10 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G6.Mal_agrp_c11 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G5.Mal_agrp_c12 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G6.Mal_agrp_c13 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G5.Mal_agrp_c14 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G6.Mal_agrp_c15 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G5.Mal_agrp_c16 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G6.Mal_agrp_c17 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G5.Mal_agrp_c18 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G7.Mal_agrp_c19 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G6.Mal_agrp_c20 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G7.Mal_agrp_c21 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G7.Mal_agrp_c22 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G8.Mal_agrp_c23 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G7.Mal_agrp_c24 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G8.Mal_agrp_c25 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G8.Mal_agrp_c26 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G9.Mal_agrp_c27 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G8.Mal_agrp_c28 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G9.Mal_agrp_c29 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G8.Mal_agrp_c30 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G9.Mal_agrp_c31 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G9.Mal_agrp_c32 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G10.Mal_agrp_c33 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G10.Mal_agrp_c34 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G11.Mal_agrp_c35 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G10.Mal_agrp_c36 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G10.Mal_agrp_c37 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G10.Mal_agrp_c38 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G11.Mal_agrp_c39 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G11.Mal_agrp_c40 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G11.Mal_agrp_c41 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G11.Mal_agrp_c42 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G12.Mal_agrp_c43 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G12.Mal_agrp_c44 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G12.Mal_agrp_c45 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G12.Mal_agrp_c46 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G13.Mal_agrp_c47.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section CD.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
Sd4S73VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S60S62SadZ2A2S5fS4aVia;A1SaeA2A2VTR;VkB;S8fS73VK;Sa8Via;S39Via;A1A2S74A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S5eS5fS64S49Via;A1S46Via;A1A2SaeA2S62SadZ2A2A2Sd5Sc2S47Via;A1M0A1Sc2S45Via;A1A1A2S5bS5eZ0G0A2S60G0Z30A2A2VTR;VkB;S8fS73VK;Sa8Via;S39Via;A1A2S7bA4VQ;A3F_;F_;F_;").

Theorem cls_any : ltac2:(tb__ "0|0|
VTR;VkB;S8fS73VK;Sa8Via;S39Via;A1A2S7dA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB RR.
  pose proof (iok_sc ia Hi) as SC.
  destruct (Z.eq_dec (ia_sc ia) 0) as [E0|N0]; [first [exact (cls_0 Kc RF GF TR RR kB HkB ia Hi E0 Q CONT_M CONT_N) | exact (cls_0 Kc RF GF TR RR kB HkB ia Hi E0 Q CONT_N) | exact (cls_0 Kc RF GF TR RR kB HkB ia Hi E0 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 1) as [E1|N1]; [first [exact (cls_1 Kc RF GF TR RR kB HkB ia Hi E1 Q CONT_M CONT_N) | exact (cls_1 Kc RF GF TR RR kB HkB ia Hi E1 Q CONT_N) | exact (cls_1 Kc RF GF TR RR kB HkB ia Hi E1 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 2) as [E2|N2]; [first [exact (cls_2 Kc RF GF TR RR kB HkB ia Hi E2 Q CONT_M CONT_N) | exact (cls_2 Kc RF GF TR RR kB HkB ia Hi E2 Q CONT_N) | exact (cls_2 Kc RF GF TR RR kB HkB ia Hi E2 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 3) as [E3|N3]; [first [exact (cls_3 Kc RF GF TR RR kB HkB ia Hi E3 Q CONT_M CONT_N) | exact (cls_3 Kc RF GF TR RR kB HkB ia Hi E3 Q CONT_N) | exact (cls_3 Kc RF GF TR RR kB HkB ia Hi E3 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 4) as [E4|N4]; [first [exact (cls_4 Kc RF GF TR RR kB HkB ia Hi E4 Q CONT_M CONT_N) | exact (cls_4 Kc RF GF TR RR kB HkB ia Hi E4 Q CONT_N) | exact (cls_4 Kc RF GF TR RR kB HkB ia Hi E4 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 5) as [E5|N5]; [first [exact (cls_5 Kc RF GF TR RR kB HkB ia Hi E5 Q CONT_M CONT_N) | exact (cls_5 Kc RF GF TR RR kB HkB ia Hi E5 Q CONT_N) | exact (cls_5 Kc RF GF TR RR kB HkB ia Hi E5 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 6) as [E6|N6]; [first [exact (cls_6 Kc RF GF TR RR kB HkB ia Hi E6 Q CONT_M CONT_N) | exact (cls_6 Kc RF GF TR RR kB HkB ia Hi E6 Q CONT_N) | exact (cls_6 Kc RF GF TR RR kB HkB ia Hi E6 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 7) as [E7|N7]; [first [exact (cls_7 Kc RF GF TR RR kB HkB ia Hi E7 Q CONT_M CONT_N) | exact (cls_7 Kc RF GF TR RR kB HkB ia Hi E7 Q CONT_N) | exact (cls_7 Kc RF GF TR RR kB HkB ia Hi E7 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 8) as [E8|N8]; [first [exact (cls_8 Kc RF GF TR RR kB HkB ia Hi E8 Q CONT_M CONT_N) | exact (cls_8 Kc RF GF TR RR kB HkB ia Hi E8 Q CONT_N) | exact (cls_8 Kc RF GF TR RR kB HkB ia Hi E8 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 9) as [E9|N9]; [first [exact (cls_9 Kc RF GF TR RR kB HkB ia Hi E9 Q CONT_M CONT_N) | exact (cls_9 Kc RF GF TR RR kB HkB ia Hi E9 Q CONT_N) | exact (cls_9 Kc RF GF TR RR kB HkB ia Hi E9 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 10) as [E10|N10]; [first [exact (cls_10 Kc RF GF TR RR kB HkB ia Hi E10 Q CONT_M CONT_N) | exact (cls_10 Kc RF GF TR RR kB HkB ia Hi E10 Q CONT_N) | exact (cls_10 Kc RF GF TR RR kB HkB ia Hi E10 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 11) as [E11|N11]; [first [exact (cls_11 Kc RF GF TR RR kB HkB ia Hi E11 Q CONT_M CONT_N) | exact (cls_11 Kc RF GF TR RR kB HkB ia Hi E11 Q CONT_N) | exact (cls_11 Kc RF GF TR RR kB HkB ia Hi E11 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 12) as [E12|N12]; [first [exact (cls_12 Kc RF GF TR RR kB HkB ia Hi E12 Q CONT_M CONT_N) | exact (cls_12 Kc RF GF TR RR kB HkB ia Hi E12 Q CONT_N) | exact (cls_12 Kc RF GF TR RR kB HkB ia Hi E12 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 13) as [E13|N13]; [first [exact (cls_13 Kc RF GF TR RR kB HkB ia Hi E13 Q CONT_M CONT_N) | exact (cls_13 Kc RF GF TR RR kB HkB ia Hi E13 Q CONT_N) | exact (cls_13 Kc RF GF TR RR kB HkB ia Hi E13 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 14) as [E14|N14]; [first [exact (cls_14 Kc RF GF TR RR kB HkB ia Hi E14 Q CONT_M CONT_N) | exact (cls_14 Kc RF GF TR RR kB HkB ia Hi E14 Q CONT_N) | exact (cls_14 Kc RF GF TR RR kB HkB ia Hi E14 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 15) as [E15|N15]; [first [exact (cls_15 Kc RF GF TR RR kB HkB ia Hi E15 Q CONT_M CONT_N) | exact (cls_15 Kc RF GF TR RR kB HkB ia Hi E15 Q CONT_N) | exact (cls_15 Kc RF GF TR RR kB HkB ia Hi E15 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 16) as [E16|N16]; [first [exact (cls_16 Kc RF GF TR RR kB HkB ia Hi E16 Q CONT_M CONT_N) | exact (cls_16 Kc RF GF TR RR kB HkB ia Hi E16 Q CONT_N) | exact (cls_16 Kc RF GF TR RR kB HkB ia Hi E16 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 17) as [E17|N17]; [first [exact (cls_17 Kc RF GF TR RR kB HkB ia Hi E17 Q CONT_M CONT_N) | exact (cls_17 Kc RF GF TR RR kB HkB ia Hi E17 Q CONT_N) | exact (cls_17 Kc RF GF TR RR kB HkB ia Hi E17 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 18) as [E18|N18]; [first [exact (cls_18 Kc RF GF TR RR kB HkB ia Hi E18 Q CONT_M CONT_N) | exact (cls_18 Kc RF GF TR RR kB HkB ia Hi E18 Q CONT_N) | exact (cls_18 Kc RF GF TR RR kB HkB ia Hi E18 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 19) as [E19|N19]; [first [exact (cls_19 Kc RF GF TR RR kB HkB ia Hi E19 Q CONT_M CONT_N) | exact (cls_19 Kc RF GF TR RR kB HkB ia Hi E19 Q CONT_N) | exact (cls_19 Kc RF GF TR RR kB HkB ia Hi E19 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 20) as [E20|N20]; [first [exact (cls_20 Kc RF GF TR RR kB HkB ia Hi E20 Q CONT_M CONT_N) | exact (cls_20 Kc RF GF TR RR kB HkB ia Hi E20 Q CONT_N) | exact (cls_20 Kc RF GF TR RR kB HkB ia Hi E20 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 21) as [E21|N21]; [first [exact (cls_21 Kc RF GF TR RR kB HkB ia Hi E21 Q CONT_M CONT_N) | exact (cls_21 Kc RF GF TR RR kB HkB ia Hi E21 Q CONT_N) | exact (cls_21 Kc RF GF TR RR kB HkB ia Hi E21 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 22) as [E22|N22]; [first [exact (cls_22 Kc RF GF TR RR kB HkB ia Hi E22 Q CONT_M CONT_N) | exact (cls_22 Kc RF GF TR RR kB HkB ia Hi E22 Q CONT_N) | exact (cls_22 Kc RF GF TR RR kB HkB ia Hi E22 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 23) as [E23|N23]; [first [exact (cls_23 Kc RF GF TR RR kB HkB ia Hi E23 Q CONT_M CONT_N) | exact (cls_23 Kc RF GF TR RR kB HkB ia Hi E23 Q CONT_N) | exact (cls_23 Kc RF GF TR RR kB HkB ia Hi E23 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 24) as [E24|N24]; [first [exact (cls_24 Kc RF GF TR RR kB HkB ia Hi E24 Q CONT_M CONT_N) | exact (cls_24 Kc RF GF TR RR kB HkB ia Hi E24 Q CONT_N) | exact (cls_24 Kc RF GF TR RR kB HkB ia Hi E24 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 25) as [E25|N25]; [first [exact (cls_25 Kc RF GF TR RR kB HkB ia Hi E25 Q CONT_M CONT_N) | exact (cls_25 Kc RF GF TR RR kB HkB ia Hi E25 Q CONT_N) | exact (cls_25 Kc RF GF TR RR kB HkB ia Hi E25 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 26) as [E26|N26]; [first [exact (cls_26 Kc RF GF TR RR kB HkB ia Hi E26 Q CONT_M CONT_N) | exact (cls_26 Kc RF GF TR RR kB HkB ia Hi E26 Q CONT_N) | exact (cls_26 Kc RF GF TR RR kB HkB ia Hi E26 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 27) as [E27|N27]; [first [exact (cls_27 Kc RF GF TR RR kB HkB ia Hi E27 Q CONT_M CONT_N) | exact (cls_27 Kc RF GF TR RR kB HkB ia Hi E27 Q CONT_N) | exact (cls_27 Kc RF GF TR RR kB HkB ia Hi E27 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 28) as [E28|N28]; [first [exact (cls_28 Kc RF GF TR RR kB HkB ia Hi E28 Q CONT_M CONT_N) | exact (cls_28 Kc RF GF TR RR kB HkB ia Hi E28 Q CONT_N) | exact (cls_28 Kc RF GF TR RR kB HkB ia Hi E28 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 29) as [E29|N29]; [first [exact (cls_29 Kc RF GF TR RR kB HkB ia Hi E29 Q CONT_M CONT_N) | exact (cls_29 Kc RF GF TR RR kB HkB ia Hi E29 Q CONT_N) | exact (cls_29 Kc RF GF TR RR kB HkB ia Hi E29 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 30) as [E30|N30]; [first [exact (cls_30 Kc RF GF TR RR kB HkB ia Hi E30 Q CONT_M CONT_N) | exact (cls_30 Kc RF GF TR RR kB HkB ia Hi E30 Q CONT_N) | exact (cls_30 Kc RF GF TR RR kB HkB ia Hi E30 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 31) as [E31|N31]; [first [exact (cls_31 Kc RF GF TR RR kB HkB ia Hi E31 Q CONT_M CONT_N) | exact (cls_31 Kc RF GF TR RR kB HkB ia Hi E31 Q CONT_N) | exact (cls_31 Kc RF GF TR RR kB HkB ia Hi E31 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 32) as [E32|N32]; [first [exact (cls_32 Kc RF GF TR RR kB HkB ia Hi E32 Q CONT_M CONT_N) | exact (cls_32 Kc RF GF TR RR kB HkB ia Hi E32 Q CONT_N) | exact (cls_32 Kc RF GF TR RR kB HkB ia Hi E32 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 33) as [E33|N33]; [first [exact (cls_33 Kc RF GF TR RR kB HkB ia Hi E33 Q CONT_M CONT_N) | exact (cls_33 Kc RF GF TR RR kB HkB ia Hi E33 Q CONT_N) | exact (cls_33 Kc RF GF TR RR kB HkB ia Hi E33 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 34) as [E34|N34]; [first [exact (cls_34 Kc RF GF TR RR kB HkB ia Hi E34 Q CONT_M CONT_N) | exact (cls_34 Kc RF GF TR RR kB HkB ia Hi E34 Q CONT_N) | exact (cls_34 Kc RF GF TR RR kB HkB ia Hi E34 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 35) as [E35|N35]; [first [exact (cls_35 Kc RF GF TR RR kB HkB ia Hi E35 Q CONT_M CONT_N) | exact (cls_35 Kc RF GF TR RR kB HkB ia Hi E35 Q CONT_N) | exact (cls_35 Kc RF GF TR RR kB HkB ia Hi E35 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 36) as [E36|N36]; [first [exact (cls_36 Kc RF GF TR RR kB HkB ia Hi E36 Q CONT_M CONT_N) | exact (cls_36 Kc RF GF TR RR kB HkB ia Hi E36 Q CONT_N) | exact (cls_36 Kc RF GF TR RR kB HkB ia Hi E36 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 37) as [E37|N37]; [first [exact (cls_37 Kc RF GF TR RR kB HkB ia Hi E37 Q CONT_M CONT_N) | exact (cls_37 Kc RF GF TR RR kB HkB ia Hi E37 Q CONT_N) | exact (cls_37 Kc RF GF TR RR kB HkB ia Hi E37 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 38) as [E38|N38]; [first [exact (cls_38 Kc RF GF TR RR kB HkB ia Hi E38 Q CONT_M CONT_N) | exact (cls_38 Kc RF GF TR RR kB HkB ia Hi E38 Q CONT_N) | exact (cls_38 Kc RF GF TR RR kB HkB ia Hi E38 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 39) as [E39|N39]; [first [exact (cls_39 Kc RF GF TR RR kB HkB ia Hi E39 Q CONT_M CONT_N) | exact (cls_39 Kc RF GF TR RR kB HkB ia Hi E39 Q CONT_N) | exact (cls_39 Kc RF GF TR RR kB HkB ia Hi E39 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 40) as [E40|N40]; [first [exact (cls_40 Kc RF GF TR RR kB HkB ia Hi E40 Q CONT_M CONT_N) | exact (cls_40 Kc RF GF TR RR kB HkB ia Hi E40 Q CONT_N) | exact (cls_40 Kc RF GF TR RR kB HkB ia Hi E40 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 41) as [E41|N41]; [first [exact (cls_41 Kc RF GF TR RR kB HkB ia Hi E41 Q CONT_M CONT_N) | exact (cls_41 Kc RF GF TR RR kB HkB ia Hi E41 Q CONT_N) | exact (cls_41 Kc RF GF TR RR kB HkB ia Hi E41 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 42) as [E42|N42]; [first [exact (cls_42 Kc RF GF TR RR kB HkB ia Hi E42 Q CONT_M CONT_N) | exact (cls_42 Kc RF GF TR RR kB HkB ia Hi E42 Q CONT_N) | exact (cls_42 Kc RF GF TR RR kB HkB ia Hi E42 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 43) as [E43|N43]; [first [exact (cls_43 Kc RF GF TR RR kB HkB ia Hi E43 Q CONT_M CONT_N) | exact (cls_43 Kc RF GF TR RR kB HkB ia Hi E43 Q CONT_N) | exact (cls_43 Kc RF GF TR RR kB HkB ia Hi E43 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 44) as [E44|N44]; [first [exact (cls_44 Kc RF GF TR RR kB HkB ia Hi E44 Q CONT_M CONT_N) | exact (cls_44 Kc RF GF TR RR kB HkB ia Hi E44 Q CONT_N) | exact (cls_44 Kc RF GF TR RR kB HkB ia Hi E44 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 45) as [E45|N45]; [first [exact (cls_45 Kc RF GF TR RR kB HkB ia Hi E45 Q CONT_M CONT_N) | exact (cls_45 Kc RF GF TR RR kB HkB ia Hi E45 Q CONT_N) | exact (cls_45 Kc RF GF TR RR kB HkB ia Hi E45 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 46) as [E46|N46]; [first [exact (cls_46 Kc RF GF TR RR kB HkB ia Hi E46 Q CONT_M CONT_N) | exact (cls_46 Kc RF GF TR RR kB HkB ia Hi E46 Q CONT_N) | exact (cls_46 Kc RF GF TR RR kB HkB ia Hi E46 Q CONT_M)]|].
  destruct (Z.eq_dec (ia_sc ia) 47) as [E47|N47]; [first [exact (cls_47 Kc RF GF TR RR kB HkB ia Hi E47 Q CONT_M CONT_N) | exact (cls_47 Kc RF GF TR RR kB HkB ia Hi E47 Q CONT_N) | exact (cls_47 Kc RF GF TR RR kB HkB ia Hi E47 Q CONT_M)]|].
  exfalso. lia.
Qed.
End CD.
End Mal_agrp_CD.

Module Mal_agrp_M.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rM1.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition D_m0 : od2 := ltac2:(tb__ "0|1|
S50S1Z0A1M0G0G0G0G0G0A6").

Definition dsCs : list od2 := ltac2:(tb__ "0|0|
S24S35Sa4S24S35S54S24S35S4eS24S35S4fS24S35S4dS1Z0A1A1S24S35S52S24S35S56S86Pc0A1A1S24S35S55S24S35S51S24S35S53S2cS35A1A3A3A3A3A3A3A3A3A3A3").
Lemma objsCs_eq : ltac2:(tb__ "0|0|
S5aS27S6A1S80S24S6S7cS8bS35S6S38S9bA4A3A3"). Proof. reflexivity. Qed.

Definition dsX (x : m1v) : list od2 := ltac2:(tb__ "0|a|
S75S27S35A1Lx;Vx;S24S35S43S86Pc4A1A1M0S24S35S41S86Pc5A1A1M1S24S35S42S86Pb6A1A1M2S24S35S3dS86Pa4A1M3S86Pa5A1M4S86Pa6A1M5S86Pa7A1M6S30S0A1A5S24S35S3cS86Pc3A1A1S2cS35A1A3M7A3A3A3M8A3M9S24S35G0S24S35G1S24S35G2S24S35S40S86Pc1A1A1S24S35S3dG3G4G5G6S2fS0S86Pc2A1A2A5G7A3A3A3A3A3G9G8X75x4").
Definition dsM1 (x : m1v) : list od2 := ltac2:(tb__ "0|0|
S28S35S9bS9cVx;A1A3").
Lemma objsM1_eq x : ltac2:(tb__ "0|0|
S5aS27S6A1S81Vx;A1S24S6S7cS8bS35S6S38S9fVx;A1A4A3A3"). Proof. destruct x; reflexivity. Qed.

Definition dsP (x : m1v) : list od2 := ltac2:(tb__ "0|2|
S28S35S9bS28S35S24S35S41S86Pc5A1A1S24S35S42S86Pb6A1A1S2cS35A1M0A3A3S75S27S35A1Lx;Vx;S24S35S43S86Pc4A1A1G0A3M1G1G1G0X75x4A3A3").
Lemma objsM23_eq x : ltac2:(tb__ "0|0|
S5aS27S6A1ScaVx;A1S24S6S7cS8bS35S6S38S9dVx;A1A4A3A3"). Proof. destruct x; reflexivity. Qed.

Definition m1_lo (x : m1v) : Z := ltac2:(tb__ "0|0|
S75S82Lx;Vx;Z0Z7Z27Z2fX75x4").
Definition m1_hi (x : m1v) : Z := ltac2:(tb__ "0|0|
S75S82Lx;Vx;Z6Z26Z2eZ2fX75x4").

Definition dsC_exp (bA bB bR : bool) : list od2 := ltac2:(tb__ "0|4|
S28S35S26S27S35A1M0LbA;VbA;S24S35S40S26S0LbB;VbB;S4S6aS2Pc1A1S1Z1A1M1A3S1Z96A1X26x2A1S2cS35A1M2A3G2X26x2S26G0LbR;VbR;S24S35S3dS1Z0A1M3G3G3G3S30S0A1A5S24S35S3cG1A1G2A3A3S24S35S3cS4S6aS2Pc3A1G1A3A1G2A3X26x2A3").

Fixpoint ods_eqb (l l' : list od2) : bool :=
  match l, l' with [], [] => true | d :: t, d' :: t' => od2_eqb d d' && ods_eqb t t' | _, _ => false end.
Lemma ods_eqb_sound l l' : ltac2:(tb__ "0|0|
S5aS26Sa1Vl;Vl';A2S29A3S5aS27S35A1Vl;Vl';A3F_;").
Proof.
  revert l'. induction l as [|d t IH]; intros [|d' t'] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply od2_eqb_sound in H1. rewrite H1, (IH t' H2). reflexivity.
Qed.

Definition stk_only (Lf : sstate) : sstate := ltac2:(tb__ "0|0|
ScS10VLf;A1S11VLf;A1SfVLf;A1SeVLf;A1S12VLf;A1S8dS6U1SaVLf;A1A3SdVLf;A1S13VLf;A1S9VLf;A1A9").
Definition recarved (x : m1v) (Lf : sstate) : sstate := ltac2:(tb__ "0|0|
ScS10VLf;A1S11VLf;A1SfVLf;A1SeVLf;A1S12VLf;A1S28S6S8dS6U1SaVLf;A1A3S8bS35S6S38S9dVx;A1A4A3SdVLf;A1S13VLf;A1S9VLf;A1A9").

Definition stk_shape (o : sobj) : bool := ltac2:(tb__ "0|0|
S2bS2bS2bS14S1dVo;A1S2PaA1A2S14S21Vo;A1S2PfA1A2A2S14S20Vo;A1S1Z0A1A2A2Sd6S1fVo;A1S15A2A2").
Definition m1_leaf_chk (x : m1v) (Lf : sstate) (bA bB bR : bool) : bool := ltac2:(tb__ "0|4|
S27S6A1M0S26Lx;SaVLf;A1S2eS6G0Se5S9fVx;A1M1R1A2S27S35A1M2Se3G1R1A2G2S2bS2bS2bS2bS2bS2bS2bS2bS2bSa2R4A1Sd9R3S8bS35S6S38R2A4M3A2A2S91S6SccSbfA1G3A3A2S91S35Se6R2A3A2S91S35Se4S9aVx;A1S99Vx;A1A2R2A3A2Se7S33S6R3A2S33S35G1A2A2A2Sa1R1Sa5VbA;VbB;VbR;A3A2A2SbSa7VLf;A1A1A2SbSa0Vx;VLf;A2A1A2S31S9VLf;A1A1A2TdsC;TdsF;LobjsF;Lstk;X27x2").

Definition has_fact (Lf : sstate) (p : sprop) : bool := ltac2:(tb__ "0|0|
S92S3S18Vp;A1SdVLf;A1A3").
Definition leaf_bools (x : m1v) (Lf : sstate) : bool * bool * bool := ltac2:(tb__ "0|2|
S25S2aS26S26A2S26S25S26S26S75S26Lx;Vx;S2eS2bS9eVLf;S8S7S6cS2Pc2A1M0S1Z0A1A3A1A2S9eVLf;S8S7S6eS1Z9A1S4S6dS2Pc3A1M1G0A3A3A1A2A2S2eS2eX75x4S9eVLf;S7S6fS2Pc1A1S1Z63A1A3A2A4S9eVLf;S8S7S70G1S1ZffA1A3A1A2A4").

Definition with_facts (F : list sprop) (S : sstate) : sstate := ltac2:(tb__ "0|0|
ScS10VS;A1S11VS;A1SfVS;A1SeVS;A1S12VS;A1SaVS;A1VF;S13VS;A1S9VS;A1A9").
Lemma smatch_with_facts rho F S w : ltac2:(tb__ "0|1|
S17S73Vrho;VS;Vw;A4S8cS3S1bVrho;A1VF;A3S5aS26SbSa3VF;VS;A2M0A1S29A3S17S73Vrho;G0Vw;A4F_;F_;F_;").
Proof.
  destruct w as [tr [ms md]]. intros Hsm HF Hwf.
  pose proof Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  unfold smatch. cbn [fst snd cfg_ms cfg_model with_facts ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in *.
  split; [exact Hwf|]. repeat (split; [assumption|]). exact HF.
Qed.

Section M.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
Sd4S73VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Let s : astate := ia_s ia. Let L : layout := ia_L ia. Let X : list sptr := ia_X ia. Let RRg : option (sptr * Z) := ia_R ia. Let U : Z -> Z := ia_U ia.
Let sc : Z := ia_sc ia. Let m : sptr := ia_m ia. Let mW : word -> option byte := ia_mW ia. Let vm : VmMaps := ia_vm ia.
Let K := K_ia Kc ia.
Let HLA : live ia s L mW vm := live_A ia Hi.

Definition bAm : bool := ltac2:(tb__ "0|1|
S2bS2bS2bS63Z7Vsc;A2S63Vsc;Z26A2A2S31S66S59Via;A1M0Z0A2A1A2S67S61S3bVia;A1G0A2ZaA2A2").
Definition bBm : bool := bnc ia + 1 <? 100.
Definition bRm : bool := seqv ia =? 255.
Definition s_ab : astate := ltac2:(tb__ "0|0|
S26SafL_;S93Sb9SbdS61Vsc;Z7A2S26S82L_;S94S5fS44Via;A1Z1A2Z96X26x2Sb2Vs;A1A3Vs;A2Vs;X26x2").
Definition s_mm : astate := ltac2:(tb__ "0|1|
S26SafL_;S95Sb1Z1M0SbaS8eS82Z0U20A3S96A2A2Sb1S5fS3bVia;A1G0A2S96A2X26x2").

Lemma bounce_idx_eq : ltac2:(tb__ "0|2|
S5aS2dS82A1M0Sb8Vsc;A1S26G0L_;S2bS63Z7M1Vsc;A2S63Vsc;Z26A2A2S2fS82S61Vsc;G1A2A2S30S82A1X26x2A3").
Proof using Hi U.
  unfold bounce_idx. pose proof (iok_sc ia Hi) as SC. unfold sc in *.
  destruct (7 <=? ia_sc ia) eqn:E1; cbn [andb]; [|reflexivity].
  destruct (ia_sc ia <? 39) eqn:E2; destruct (ia_sc ia <=? 38) eqn:E3; try reflexivity; exfalso;
    first [apply Z.ltb_lt in E2; apply Z.leb_gt in E3 | apply Z.ltb_ge in E2; apply Z.leb_le in E3]; lia.
Qed.
Lemma ab_post_eq : ltac2:(tb__ "0|0|
S5aSafS85Vsc;Vs;A2S96A3").
Proof using Hi.
  unfold ab_post, s_ab, bAm, bBm. rewrite bounce_idx_eq. fold (useq ia) (bnc ia) (seqv ia).
  destruct ((7 <=? sc) && (sc <=? 38)); cbn [andb]; [|reflexivity].
  change (znth (sc - 7) (st_unmap_seq s)) with (useq ia). change (znth (sc - 7) (st_bounces s)) with (bnc ia). change (st_seq s) with (seqv ia).
  destruct (negb (useq ia =? 0) && (seqv ia - useq ia <? 10)); reflexivity.
Qed.
Lemma seq_ab : ltac2:(tb__ "0|0|
S5aS82Sb3S96A1S3bVia;A1A3"). Proof using . unfold s_ab. destruct bAm; reflexivity. Qed.
Lemma mm_pre_eq : ltac2:(tb__ "0|0|
S5aSafS84Vsc;Vs;A2S98A3").
Proof using Hi. unfold mm_pre. rewrite ab_post_eq. unfold seq_post, s_mm, bRm. rewrite seq_ab. reflexivity. Qed.

Lemma ctx_frame_trans a b c : ltac2:(tb__ "0|0|
SbeVa;Vb;A2SbeVb;Vc;A2SbeVa;Vc;A2F_;F_;").
Proof using . unfold ctx_frame. intros (A1&A2&A3&A4&A5&A6) (B1&B2&B3&B4&B5&B6). repeat split; congruence. Qed.

Lemma mm_inv : ltac2:(tb__ "0|1|
S5bSc6S24SacVm;VX;A3VRRg;VU;S84Vsc;Vs;A2M0A4SbeVs;G0A2A2").
Proof using Hi.
  pose proof (iok_I ia Hi) as HI.
  pose proof (account_bounce_spec (m :: X) RRg U s sc (fun r => Inv (m :: X) RRg U (snd r) /\ ctx_frame s (snd r)) HI ltac:(intros s' H F; exact (conj H F))) as A.
  rewrite account_bounce_eq in A. cbn [itok snd] in A. destruct A as [IA FA].
  pose proof (step_seq_spec (m :: X) RRg U (ab_post sc s) (fun r => Inv (m :: X) RRg U (snd r) /\ ctx_frame (ab_post sc s) (snd r)) IA ltac:(intros s' H F; exact (conj H F))) as B.
  rewrite step_seq_eq in B. cbn [itok snd] in B. destruct B as [IB FB].
  unfold mm_pre. split; [exact IB | exact (ctx_frame_trans _ _ _ FA FB)].
Qed.
Lemma mm_MT q : ltac2:(tb__ "0|0|
S5aS2dSb0A1Sc4S84Vsc;Vs;A2Vq;A2Sc4Vs;Vq;A2A3").
Proof using Hi RRg U X m. unfold MT. rewrite (proj1 (proj2 mm_inv)). reflexivity. Qed.
Lemma mm_xraw : ltac2:(tb__ "0|0|
SdaS24SacVm;VX;A3S84Vsc;Vs;A2A2").
Proof using Hi RRg U. intros g Hg. rewrite !mm_MT. exact (iok_Xr ia Hi g Hg). Qed.
Lemma mm_hd : ltac2:(tb__ "0|0|
S5aS2dSacA1Sc8S84Vsc;Vs;A2Vsc;A2S30SacA1A3").
Proof using Hi RRg U X m. unfold active_hd. rewrite (proj1 (proj2 (proj2 mm_inv))). exact (iok_hd ia Hi). Qed.
Lemma mm_raw : ltac2:(tb__ "0|3|
S5dS5aS2dSb0A1M0Sc4S84Vsc;Vs;A2Vm;A2M1S2fSb0Sb7A2A3S5aG0G1S2fSb0Sb6S30SacA1M2G2A2A2A3A2").
Proof using Hi RRg U X. rewrite mm_MT. exact (iok_m_raw ia Hi). Qed.
Lemma mm_usage k : ltac2:(tb__ "0|0|
S5aS82Sb5S84Vsc;Vs;A2Vk;A2Sb5Vs;Vk;A2A3").
Proof using Hi RRg U X m. unfold usage_of. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 mm_inv))))). reflexivity. Qed.
Lemma mm_ctr : ltac2:(tb__ "0|0|
S5aS82SbbS84Vsc;Vs;A2A1S57Via;A1A3").
Proof using Hi. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 mm_inv)))))). reflexivity. Qed.

Lemma bAm_range : ltac2:(tb__ "0|0|
S5aS26S93S29A3S5bS5eZ7Vsc;A2S5eVsc;Z26A2A2F_;").
Proof using . unfold bAm. intros H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia. Qed.

Definition locsM : list loc := ltac2:(tb__ "0|1|
S28Sc3S26S27Sc3A1L_;S93S24Sc3Sc7S5fSc5S61Vsc;Z7A2A2A1S2cSc3A1M0A3G0X26x2Sd7S96A1A3").
Lemma mm_delta : ltac2:(tb__ "0|0|
Sd8Vs;S84Vsc;Vs;A2S97A3").
Proof using Hi.
  unfold mm_pre, locsM. rewrite ab_post_eq. apply (delta_trans s s_ab (seq_post s_ab)); [|apply delta_seq_b].
  unfold s_ab. pose proof bAm_range as BR. destruct bAm; [apply delta_sb; specialize (BR eq_refl); lia | apply delta_refl].
Qed.

Lemma mm_bounces : ltac2:(tb__ "0|3|
S5bS5eZ7M0Vsc;A2S5eVsc;Z26A2A2S5aS82SbcS61Vsc;G0A2Sb2S84Vsc;Vs;A2A1A2S26S82L_;M1S93G1S94S5fS44Via;A1M2Z1A2Z96X26x2G2X26x2A3F_;").
Proof using Hi.
  intros Hr. rewrite mm_pre_eq. unfold s_mm, s_ab.
  pose proof (inv_ctx (iok_I ia Hi)) as (_ & _ & _ & LenB & _). unfold s in *.
  destruct bRm; destruct bAm; cbn [st_bounces set_seq set_unmap_seq set_bounces]; try reflexivity;
    rewrite znth_zset by lia; rewrite Z.eqb_refl, LenB; (replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia)); reflexivity.
Qed.
Lemma mm_seq : ltac2:(tb__ "0|1|
S5aS82Sb3S84Vsc;Vs;A2A1S26S82L_;S95Z1M0S5fS3bVia;A1G0A2X26x2A3").
Proof using Hi. rewrite mm_pre_eq. unfold s_mm. destruct bRm; reflexivity. Qed.
Lemma mm_useq : ltac2:(tb__ "0|1|
S5aS27S82A1M0Sb4S84Vsc;Vs;A2A1S26G0L_;S95S8eS82Z0U20A3Sb4Vs;A1X26x2A3").
Proof using Hi. rewrite mm_pre_eq. unfold s_mm, s_ab. destruct bRm; destruct bAm; reflexivity. Qed.

Lemma toS_signed_small x : ltac2:(tb__ "0|3|
S5bS5eS69S65Z2M0Z3fA2M1A1Vx;A2S60Vx;G1A2A2S5aS82S89Z40M2S68Vx;S65G0G2A2A2A2Vx;A3F_;").
Proof using U sc.
  intros Hx. rewrite toS_mod by lia. unfold toS.
  destruct (Z_lt_dec x 0).
  - replace (x mod 2 ^ 64) with (x + 2 ^ 64) by (Z.to_euclidean_division_equations; lia).
    replace (x + 2 ^ 64 <? 2 ^ (64 - 1)) with false by (symmetry; apply Z.ltb_ge; lia). lia.
  - rewrite Z.mod_small by lia. replace (x <? 2 ^ (64 - 1)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma factA_useq0 : ltac2:(tb__ "0|0|
S87S37Via;A1S36Via;A1S7S6cS2Pc2A1S1Z0A1A3A3S5aS26S93S2eA3F_;").
Proof using Hi.
  cbn [zholds zcond]. rewrite (zs194 ia Hi), (ze_lit ia). change (0 mod 2 ^ 64) with 0. intros E. apply Z.eqb_eq in E.
  unfold bAm. rewrite E. cbn [Z.eqb negb]. rewrite !andb_false_r. reflexivity.
Qed.
Lemma factA_gap : ltac2:(tb__ "0|0|
S87S37Via;A1S36Via;A1S7S6eS1Z9A1S4S6dS2Pc3A1S2Pc2A1A3A3A3S5aS26S93S2eA3F_;").
Proof using Hi.
  cbn [zholds zcond]. rewrite (ze_alu ia), (zs194 ia Hi), (zs195 ia Hi), (ze_lit ia). cbn [zalu]. pose proof (ctx_ranges ia Hi) as CR.
  rewrite (toS_signed_small (seqv ia - useq ia)) by lia. change (toS 64 (9 mod 2 ^ 64)) with 9. intros E. apply Z.ltb_lt in E.
  unfold bAm. replace (seqv ia - useq ia <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity.
Qed.
Lemma factA_bump : ltac2:(tb__ "0|3|
S5bS5eZ7Vsc;A2S5eVsc;Z26A2A2S87S37Via;A1M0S36Via;A1M1S8S7S6cS2Pc2A1M2S1Z0A1A3A1A3S87G0G1S8S7S6eS1Z9A1S4S6dS2Pc3A1G2A3A3A1A3S5aS26S93S29A3F_;F_;F_;").
Proof using Hi.
  cbn [zholds zcond]. rewrite (ze_alu ia), (zs194 ia Hi), (zs195 ia Hi), (ze_lit ia), (ze_lit ia). cbn [zalu]. pose proof (ctx_ranges ia Hi) as CR.
  rewrite (toS_signed_small (seqv ia - useq ia)) by lia. change (toS 64 (9 mod 2 ^ 64)) with 9. change (0 mod 2 ^ 64) with 0. intros Hr E1 E2.
  unfold bAm. replace (7 <=? sc) with true by (symmetry; apply Z.leb_le; lia). replace (sc <=? 38) with true by (symmetry; apply Z.leb_le; lia).
  destruct (useq ia =? 0); [exfalso; exact (E1 eq_refl)|]. cbn [negb andb].
  apply Z.ltb_lt. destruct (Z_lt_dec 9 (seqv ia - useq ia)) as [Hlt|]; [|lia]. exfalso. apply E2. apply Z.ltb_lt. exact Hlt.
Qed.
Lemma factA_range : ltac2:(tb__ "0|0|
S5cS5bS5eZ7Vsc;A2S5eVsc;Z26A2A2A1S5aS26S93S2eA3F_;").
Proof using .
  intros Hr. unfold bAm. destruct (7 <=? sc) eqn:E1; [|reflexivity]. destruct (sc <=? 38) eqn:E2; [|reflexivity].
  exfalso. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.
Lemma factB_t : ltac2:(tb__ "0|0|
S87S37Via;A1S36Via;A1S7S6fS2Pc1A1S1Z63A1A3A3S5aS26S94S29A3F_;").
Proof using Hi.
  cbn [zholds zcond]. rewrite (zs193 ia Hi), (ze_lit ia). change (99 mod 2 ^ 64) with 99. intros E. apply Z.ltb_lt in E.
  unfold bBm. apply Z.ltb_lt. lia.
Qed.
Lemma factB_f : ltac2:(tb__ "0|0|
S87S37Via;A1S36Via;A1S8S7S6fS2Pc1A1S1Z63A1A3A1A3S5aS26S94S2eA3F_;").
Proof using Hi.
  cbn [zholds zcond]. rewrite (zs193 ia Hi), (ze_lit ia). change (99 mod 2 ^ 64) with 99. intros E.
  unfold bBm. apply Z.ltb_ge. destruct (Z_lt_dec (bnc ia) 99) as [Hlt|]; [|lia]. exfalso. apply E. apply Z.ltb_lt. exact Hlt.
Qed.
Lemma factR_f : ltac2:(tb__ "0|0|
S87S37Via;A1S36Via;A1S7S70S2Pc3A1S1ZffA1A3A3S5aS26S95S2eA3F_;").
Proof using Hi.
  cbn [zholds zcond]. rewrite (zs195 ia Hi), (ze_lit ia). change (255 mod 2 ^ 64) with 255. intros E. unfold bRm.
  destruct (seqv ia =? 255); [discriminate E | reflexivity].
Qed.
Lemma factR_t : ltac2:(tb__ "0|0|
S87S37Via;A1S36Via;A1S8S7S70S2Pc3A1S1ZffA1A3A1A3S5aS26S95S29A3F_;").
Proof using Hi.
  cbn [zholds zcond]. rewrite (zs195 ia Hi), (ze_lit ia). change (255 mod 2 ^ 64) with 255. intros E. unfold bRm.
  destruct (seqv ia =? 255); [reflexivity | exfalso; exact (E eq_refl)].
Qed.

Lemma ze_nosmall : ltac2:(tb__ "0|0|
S5bS5eZ7Vsc;A2S5eVsc;Z26A2A2S5aS82S8aS37Via;A1S36Via;A1S4S72S4S71S2Pc1A1S1Z64A1A3S1Z1A1A3A3S48Via;A1A3F_;").
Proof using Hi.
  intros Hr. rewrite (ze_alu ia), (ze_alu ia), (zs193 ia Hi), !(ze_lit ia). cbn [zalu]. pose proof (ctx_ranges ia Hi) as CR.
  change (100 mod 2 ^ 64) with 100. change ((1 mod 2 ^ 64) mod 2 ^ 64) with 1. rewrite (Z.mod_small (bnc ia)) by lia. change (100 mod 2 ^ 64) with 100.
  unfold inos, is_bouncing. fold s sc. rewrite bounce_idx_eq.
  replace (7 <=? sc) with true by (symmetry; apply Z.leb_le; lia). replace (sc <=? 38) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
  change (znth (sc - 7) (st_bounces s)) with (bnc ia).
  destruct (bnc ia <? 100) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
    [replace (100 <=? bnc ia) with false by (symmetry; apply Z.leb_gt; lia) | replace (100 <=? bnc ia) with true by (symmetry; apply Z.leb_le; lia)]; reflexivity.
Qed.
Lemma inos_0 : ltac2:(tb__ "0|0|
S5cS5bS5eZ7Vsc;A2S5eVsc;Z26A2A2A1S5aS82S48Via;A1Z0A3F_;").
Proof using Hi.
  intros Hr. unfold inos, is_bouncing. fold s sc. rewrite bounce_idx_eq.
  destruct (7 <=? sc) eqn:E1; [|reflexivity]. destruct (sc <=? 38) eqn:E2; [|reflexivity]. exfalso. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

Lemma ZF_M1 x : ltac2:(tb__ "0|0|
S5bS5eS9aVx;A1Vsc;A2S5eVsc;S99Vx;A1A2A2S8cS3S87S37Via;A1S36Via;A1A2S76Vx;A1A3F_;").
Proof using Hi.
  intros Hx. pose proof (iok_sc ia Hi) as SC. unfold F_M1.
  destruct x; cbn [m1_lo m1_hi] in Hx; repeat constructor; cbn [zholds zcond]; rewrite ?(zs12 ia Hi), ?(ze_lit ia); unfold sc in *;
    rewrite ?Z.mod_small by lia; lia.
Qed.
Lemma ZF_allM1 x : ltac2:(tb__ "0|0|
S5bS5eS9aVx;A1Vsc;A2S5eVsc;S99Vx;A1A2A2S8cS3S87S37Via;A1S36Via;A1A2S28S3S78S28S3S79S28S3S77S28S3S7aS76Vx;A1A3A3A3A3A3F_;").
Proof using Hi.
  intros Hx. apply Forall_app. split; [exact (ZF_G ia Hi)|]. apply Forall_app. split; [exact (ZF_M ia Hi)|].
  apply Forall_app. split; [exact (ZF_CTX ia Hi)|]. apply Forall_app. split; [exact (ZF_SZ ia Hi) | exact (ZF_M1 x Hx)].
Qed.

Lemma dsM1_entry x : ltac2:(tb__ "0|0|
S5bS5eS9aVx;A1Vsc;A2S5eVsc;S99Vx;A1A2A2S8cS35S3fVia;Vs;VmW;A3S9fVx;A1A3F_;").
Proof using Hi.
  intros Hx. pose proof (iok_sc ia Hi) as SC. pose proof (iok_erv_holds ia Hi) as HE.
  unfold dsM1, dsCs, dsX, D_m0. destruct x; cbn [m1_lo m1_hi] in Hx;
    repeat (apply Forall_cons; [cbn [od2_entry]; repeat split; try reflexivity; try exact HE; unfold sc in *; try lia |]); apply Forall_nil.
Qed.

Lemma dsP_entry x cur mWc : ltac2:(tb__ "0|0|
S5bS5eS9aVx;A1Vsc;A2S5eVsc;S99Vx;A1A2A2SbeVs;Vcur;A2Sd2Sd1ScfS73VmWc;A2Sa9Q40A1S29L_;A2Sd3Sd0A1U4S3eVia;A1A4S8cS35S3fVia;Vcur;VmWc;A3S9dVx;A1A3F_;F_;F_;").
Proof using Hi.
  intros Hx (F1 & F2 & F3 & F4 & F5 & F6) HE. pose proof (iok_sc ia Hi) as SC.
  assert (U1 : usage_of cur sc = usg ia) by (unfold usage_of; rewrite F4; reflexivity).
  assert (U2 : usage_of cur (sc + 1) = usg2 ia) by (unfold usage_of; rewrite F4; reflexivity).
  assert (C1 : st_mmap_counter cur = ctr ia) by (rewrite F5; reflexivity).
  unfold dsP, dsCs, D_m0. destruct x; cbn [m1_lo m1_hi] in Hx; cbn [app];
    repeat (apply Forall_cons; [cbn [od2_entry]; repeat split; try reflexivity; try exact HE; try exact U1; try exact U2; try exact C1; unfold sc in *; try lia |]); apply Forall_nil.
Qed.

Lemma stk_shape_sound o : ltac2:(tb__ "0|0|
S5aS26Sa2Vo;A1S29A3S5aS6Vo;S1cS2PaA1S2PfA1S1Z0A1S1eVo;A1S15A5A3F_;").
Proof using .
  unfold stk_shape. intros H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3. apply odefault_eqb_sound in H4.
  destruct o; cbn in *; subst; reflexivity.
Qed.

Lemma FM1_vars x : ltac2:(tb__ "0|0|
S5aS26S91S3ScdSbfA1S28S3S78S28S3S79S28S3S77S28S3S7aS76Vx;A1A3A3A3A3A3S29A3"). Proof using . destruct x; reflexivity. Qed.
Lemma FM1_sup x : ltac2:(tb__ "0|0|
S5aS26S91S3S88S28S3S78S28S3S79S28S3S77S28S3S7aS76Vx;A1A3A3A3A3A3S29A3"). Proof using . destruct x; reflexivity. Qed.
Lemma SM23_swf x : ltac2:(tb__ "0|0|
S5aS26SbSc9Vx;A1A1S29A3"). Proof using . destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsP_pairwise x : ltac2:(tb__ "0|0|
S4cS28S35S2cS35A1S9dVx;A1A3A1"). Proof using . apply od2_pairwiseb_ok. destruct x; reflexivity. Qed.
Lemma dsP_vars x : ltac2:(tb__ "0|0|
S5aS26S91S35S35SccSbfS38R1A1A2Ld;S28S35S2cS35A1S9dVx;A1A3A3S29A3"). Proof using . destruct x; reflexivity. Qed.

Section Leaf.
Variable x : m1v.
Hypothesis Hx : ltac2:(tb__ "0|0|
S5bS5eS9aVx;A1Vsc;A2S5eVsc;S99Vx;A1A2A2").
Variable Q : assn.
Hypothesis CONT_M23 : ltac2:(tb__ "0|1|
Sa9Q40A1M0S2dSa9Q8A1A1F_;S4bVia;S84Vsc;Vs;A2VL;R1Vvm;A5Sd2Sd1ScfS73R2A2G0S29L_;A2Sd3Sd0A1U4S3eVia;A1A4VTR;VkB;S8fS73VK;S3aVia;R3A2Sc9Vx;A1A4VQ;A3F_;F_;FmW';").
Variables (Lf : sstate) (rho' : valuation).
Hypothesis HagL : ltac2:(tb__ "0|0|
Sc0S3aVia;VmW;A2Vrho';A2").
Variables (bA bB bR : bool).
Hypothesis CHK : ltac2:(tb__ "0|0|
S5aS26Sa6Vx;VLf;VbA;VbB;VbR;A5S29A3").
Hypothesis EA : bAm = bA.
Hypothesis EB : ltac2:(tb__ "0|0|
S5aS26VbA;S29A3S5aS26S94VbB;A3F_;").
Hypothesis ER : bRm = bR.

Variables (dL : list (sv * sv) * list sprop) (setsL : list (positive * sv)).
Hypothesis HsdL : ltac2:(tb__ "0|1|
S5aS2dS2aS27S2aS0S0A2A1S27S3A1A2M0A1SaaSa0Vx;VLf;A2Sc9Vx;A1A2S2fG0VdL;A2A3").
Hypothesis Hvars : ltac2:(tb__ "0|0|
S5aS26SceS83S31Sc1S8bS2aS83S0A2S83S32S83S0A2VsetsL;A4R1A2A1Lu;Sa0Vx;VLf;A2A2S29A3").
Hypothesis Hsets : ltac2:(tb__ "0|0|
S5aS26S91S83S83S31SbfR1A1A1Lj;S8bS2aS83S0A2S83S32S83S0A2VsetsL;A4A3S29A3").
Hypothesis Hnf : ltac2:(tb__ "0|0|
S5aS26S91S3S3S92S3S18R1A1S28S3S78S28S3S79S28S3S77S28S3S7aS76Vx;A1A3A3A3A3A3Lp;S34S27S2aS0S0A2A1S27S3A1VdL;A3A3S29A3").
Hypothesis Hpairs : ltac2:(tb__ "0|0|
Sa9Q40A1S2dSa9Q8A1A1F_;S23Sc0S3aVia;R2A2S90R1VsetsL;A2A2SabS90R2VsetsL;A2S32S27S2aS0S0A2A1S27S3A1VdL;A3A2F_;FrhoX;Fmm;").

Theorem m1_leaf : ltac2:(tb__ "0|0|
VTR;VkB;ScbS73VK;VLf;Vrho';A4VQ;A3").
Proof using CHK CONT_M23 EA EB ER HLA HagL HkB Hnf Hpairs HsdL Hsets Hvars Hx RR RRg U X m.
  pose proof (iok_sc ia Hi) as SC.
  (apply (trr_inhP RR); [lia|]). intros [tr [msF md]] [HsmL HKw]. cbn [w_tr w_cfg cfg_model fst snd] in HKw.

  unfold m1_leaf_chk in CHK. destruct (ss_objs Lf) as [|stk objsF] eqn:EO; [discriminate|].
  apply andb_prop in CHK as [CHK Clen']. apply andb_prop in CHK as [CHK Cswf2]. apply andb_prop in CHK as [CHK Cswf1].
  apply andb_prop in CHK as [CHK CdsC]. apply andb_prop in CHK as [CHK Clen]. apply andb_prop in CHK as [CHK Ccond].
  apply andb_prop in CHK as [CHK Csem]. apply andb_prop in CHK as [CHK Cvars]. apply andb_prop in CHK as [Cstk Cmatch].
  set (dsF := fill2 (dsM1 x) objsF) in *. set (dsC := changed2 (dsM1 x) dsF) in *.
  apply ods_eqb_sound in CdsC. apply Nat.eqb_eq in Clen.
  pose proof (stk_shape_sound stk Cstk) as Estk. set (stkc := ob_cells stk) in *.
  assert (HSF_objs : ss_objs Lf = oStkF stkc :: objsF) by (rewrite EO, Estk; reflexivity).

  pose proof mm_inv as [HI'' CF]. pose proof mm_xraw as HXr''. pose proof mm_delta as HD.
  assert (Hcond : forall d, In d dsF -> dcond2 (ia_sc ia) d).
  { intros d Hd. apply (dcond2b_sound (m1_lo x) (m1_hi x)); [exact Hx | exact (proj1 (forallb_forall _ _) Ccond d Hd)]. }
  assert (Hent : forall d, In d dsF -> od2_entry ia s mW d \/ In d dsC).
  { intros d Hd. apply (ent_changed2 (od2_entry ia s mW) (dsM1 x) dsF); [| exact (dsM1_entry x Hx) | exact Hd].
    unfold dsF. apply fill2_length. exact Clen. }
  assert (HdsC : forall d, In d dsC -> In d dsF /\ od2_at ia L (mm_pre sc s) d /\ od2_chg d).
  { intros d Hd. split; [exact (changed2_sub _ _ d Hd)|]. rewrite CdsC in Hd. unfold dsC_exp in Hd.
    pose proof (mm_bounces) as MB. pose proof mm_seq as MS. pose proof mm_useq as MU. rewrite EA in MB. rewrite ER in MS, MU.
    pose proof bAm_range as BR. rewrite EA in BR. pose proof (ctx_ranges ia Hi) as CR.
    apply in_app_iff in Hd as [Hd|Hd].
    - destruct bA; [|destruct Hd]. destruct Hd as [<-|[]]. specialize (BR eq_refl). specialize (MB BR). rewrite (EB eq_refl) in MB.
      split; [|exact I]. cbn [od2_at]. split; [unfold sc in *; lia|]. fold sc. rewrite MB.
      destruct bB; [rewrite (ze_alu ia), (zs193 ia Hi), (ze_lit ia); cbn [zalu] | rewrite (ze_lit ia)].
      + pose proof (EB eq_refl) as HB. unfold bBm in HB. apply Z.ltb_lt in HB. rewrite !Z.mod_small; lia.
      + reflexivity.
    - destruct bR.
      + destruct Hd as [<-|[<-|[]]]; (split; [|exact I]); cbn [od2_at].
        * fold sc. rewrite MU, !(ze_lit ia), !udw2_zero. repeat split; reflexivity.
        * rewrite MS, (ze_lit ia). reflexivity.
      + destruct Hd as [<-|[]]. split; [|exact I]. cbn [od2_at]. rewrite MS, (ze_alu ia), (zs195 ia Hi), (ze_lit ia). cbn [zalu].
        pose proof ER as HR. unfold bRm in HR. apply Z.eqb_neq in HR. rewrite !Z.mod_small; lia. }
  assert (Hlocs : forall l, In l locsM -> exists d, In d dsC /\ dlo2 ia d <= loc_addr L l < dhi2 ia d).
  { intros l Hl. pose proof (mig_ctx (iok_MI ia Hi)) as HCX. cbn [ma_L mc_ctx C_U] in HCX. fold L in HCX.
    rewrite CdsC. unfold locsM in Hl. pose proof bAm_range as BR. rewrite EA in Hl, BR.
    apply in_app_iff in Hl as [Hl|Hl].
    - destruct bA; [|destruct Hl]. destruct Hl as [<-|[]]. eexists. split; [apply in_app_iff; left; left; reflexivity|].
      unfold dlo2, dhi2, od2_range, od2_rangeP. cbn [fst snd loc_addr]. rewrite HCX. specialize (BR eq_refl). unfold CTX_bounces, sc in *. lia.
    - unfold seq_locs_b in Hl. rewrite seq_ab in Hl. fold bRm in Hl. rewrite ER in Hl. destruct bR.
      + unfold seq_locs in Hl. destruct Hl as [<-|Hl].
        * eexists. split; [apply in_app_iff; right; right; left; reflexivity|]. unfold dlo2, dhi2, od2_range, od2_rangeP. cbn [fst snd loc_addr]. rewrite HCX. unfold CTX_seq. lia.
        * apply in_map_iff in Hl as (k & <- & Hk). apply in_seq in Hk.
          eexists. split; [apply in_app_iff; right; left; reflexivity|]. unfold dlo2, dhi2, od2_range, od2_rangeP. cbn [fst snd loc_addr]. rewrite HCX. unfold CTX_unmap_seq. lia.
      + destruct Hl as [<-|[]]. eexists. split; [apply in_app_iff; right; left; reflexivity|]. unfold dlo2, dhi2, od2_range, od2_rangeP. cbn [fst snd loc_addr]. rewrite HCX. unfold CTX_seq. lia. }

  pose proof (live' ia Hi s L mW vm HLA tr md msF rho' HagL Lf stkc objsF dsF dsC HSF_objs Cmatch HsmL Cvars Csem Hcond Hent
                (mm_pre sc s) locsM HI'' HXr'' HD HdsC Hlocs mm_hd mm_raw) as HLV'.
  set (m1 := m' msF rho' dsF) in *.

  assert (Eswf1 : swf (SFr Lf stkc) = true) by (unfold SFr; rewrite <- Cswf1; unfold stk_only; rewrite EO, Estk; reflexivity).
  pose proof (smatch_released tr md msF rho' Lf stkc objsF dsF HSF_objs Cmatch HsmL Eswf1) as SM1. fold m1 in SM1.
  pose proof (agrees_released ia mW msF rho' HagL dsF) as AG1. fold m1 in AG1.
  set (rhoB := set_rm rho' m1) in *.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 HsmL))))) as HromF.
  assert (HE1 : holds (byteview_of (Glue.rd_of segsU m1) (fun _ => true)) (mc_errno C_U) 4 (ia_erv ia)).
  { intros j Hj. pose proof (iok_erv_holds ia Hi j Hj) as E0. rewrite errno_U in E0 |- *.
    destruct (V1' ia Hi s L mW vm HLA tr md msF rho' HagL Lf stkc objsF dsF dsC HSF_objs Cmatch HsmL Cvars Csem Hcond Hent (237612 + Z.of_nat j) ltac:(lia)) as [_ EV].
    - intros (d & HdC & R). destruct (HdsC d HdC) as (_ & _ & Hchg). rewrite CdsC in HdC. unfold dsC_exp in HdC.
      unfold dlo2, dhi2, od2_range, od2_rangeP in R.
      apply in_app_iff in HdC as [HdC|HdC]; [destruct bA; [destruct HdC as [<-|[]] | destruct HdC] | destruct bR; [destruct HdC as [<-|[<-|[]]] | destruct HdC as [<-|[]]]];
        cbn [fst snd] in R; unfold sc in *; lia.
    - fold m1 in EV. rewrite EV. exact E0. }
  exists (POST segsU K (rho2 ia m1) (SM23 x)). split; [| exact (CONT_M23 m1 HLV' HE1)].
  pose proof (carve2a ia Hi (mm_pre sc s) L m1 vm HLV' msF HromF rhoB (SFr Lf stkc) stkc [] (dsP x) (ss_next Lf) tr md AG1 (dsP_vars x) eq_refl
                (Forall_nil _) (dsP_entry x (mm_pre sc s) m1 Hx CF HE1) (dsP_pairwise x)) as SM2.
  cbn zeta in SM2. specialize (SM2 ltac:(unfold SFr; rewrite <- Cswf2; unfold recarved; rewrite EO, Estk; reflexivity) SM1).
  assert (SM2' : smatch segsU rhoB (recarved x Lf) (tr, mkCfg msF md)).
  { unfold recarved. rewrite EO, Estk. exact SM2. }
  apply (linkp segsU K (rho2 ia m1) (recarved x Lf) (SM23 x) setsL (fst dL) (snd dL) rhoB (tr, mkCfg msF md) Hvars Hsets (SM23_swf x)).
  - rewrite HsdL. destruct dL; reflexivity.
  - exact AG1.
  - intros HagS _. split; [exact (Hpairs m1 rhoB HagS)|].
    exact (nf_of_big ia m1 (setp rhoB setsL) (snd dL) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_M1 x) HagS Hnf (FM1_vars x) (FM1_sup x) (ZF_allM1 x Hx)).
  - split; [exact SM2' | exact HKw].
Qed.
End Leaf.

Section Gen.
Variable x : m1v.

Lemma SM1_eq : ltac2:(tb__ "0|0|
S5aS22S7eVx;A1Sa3S28S3S78S28S3S79S28S3S77S28S3S7aS76Vx;A1A3A3A3A3ScS10S74A1S11S74A1SfS74A1SeS74A1S12S74A1S28S6SaS74A1S8bS35S6S38S9cVx;A1A4A3SdS74A1S7fS9S74A1A9A2A3").
Proof using . destruct x; reflexivity. Qed.
Lemma SM1_swf : ltac2:(tb__ "0|0|
S5aS26SbS7eVx;A1A1S29A3"). Proof using . destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma SM1o_swf : ltac2:(tb__ "0|0|
S5aS26SbScS10S74A1S11S74A1SfS74A1SeS74A1S12S74A1S28S6SaS74A1S8bS35S6S38S9cVx;A1A4A3SdS74A1S7fS9S74A1A9A1S29A3").
Proof using . destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsM1_vars : ltac2:(tb__ "0|0|
S5aS26S91S35S35SccSbfS38R1A1A2Ld;S28S35S9bS9cVx;A1A3A3S29A3"). Proof using . destruct x; reflexivity. Qed.
Lemma dsM1_pairwise : ltac2:(tb__ "0|0|
S4cS28S35S9bS9cVx;A1A3A1"). Proof using . apply od2_pairwiseb_ok. destruct x; reflexivity. Qed.
Lemma dsCs_wf : ltac2:(tb__ "0|0|
S8cS35S58Via;A1S9bA3").
Proof using . unfold dsCs, D_m0. repeat (apply Forall_cons; [exact I|]). apply Forall_nil. Qed.
Hypothesis Hx : ltac2:(tb__ "0|0|
S5bS5eS9aVx;A1Vsc;A2S5eVsc;S99Vx;A1A2A2").
Lemma dsX_entry : ltac2:(tb__ "0|0|
S8cS35S3fVia;Vs;VmW;A3S9cVx;A1A3").
Proof using Hi Hx. pose proof (dsM1_entry x Hx) as H. unfold dsM1 in H. apply Forall_app in H as [_ H]. exact H. Qed.

Lemma enter rhoB w : ltac2:(tb__ "0|0|
Sc0S3aVia;VmW;A2VrhoB;A2ScbS73VK;S74VrhoB;Vw;A5ScbS73VK;S7eVx;A1VrhoB;Vw;A5F_;F_;").
Proof using HLA Hx Kc.
  intros Hag [Hsm HKw]. destruct w as [tr [ms md]]. split; [|exact HKw].
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))) as Hrom.
  rewrite SM1_eq. apply smatch_with_facts.
  - apply (carve2a ia Hi s L mW vm HLA ms Hrom rhoB SM1pre STKC dsCs (dsX x) NXA tr md Hag dsM1_vars objsCs_eq dsCs_wf dsX_entry dsM1_pairwise SM1o_swf Hsm).
  - exact (ZFw ia mW rhoB _ Hag (FM1_vars x) (FM1_sup x) (ZF_allM1 x Hx)).
  - rewrite <- SM1_eq. exact SM1_swf.
Qed.
End Gen.

Ltac leaf_fact_tac ia K rho' w HagL HSP :=
  eapply (leaf_factw ia _ K rho' _ w _ HagL HSP); [cbn; tauto | reflexivity | reflexivity].
Ltac tacEA ia K rho' w HagL HSP Hxn :=
  first [ apply factA_range; exact Hxn
        | apply factA_useq0; leaf_fact_tac ia K rho' w HagL HSP
        | apply factA_gap; leaf_fact_tac ia K rho' w HagL HSP
        | apply factA_bump; [cbn [m1_lo m1_hi] in Hxn; exact Hxn | leaf_fact_tac ia K rho' w HagL HSP | leaf_fact_tac ia K rho' w HagL HSP] ].
Ltac tacEB ia K rho' w HagL HSP :=
  first [ let E := fresh in intros E; discriminate E
        | intros _; apply factB_t; leaf_fact_tac ia K rho' w HagL HSP
        | intros _; apply factB_f; leaf_fact_tac ia K rho' w HagL HSP ].
Ltac tacER ia K rho' w HagL HSP :=
  first [ apply factR_t; leaf_fact_tac ia K rho' w HagL HSP
        | apply factR_f; leaf_fact_tac ia K rho' w HagL HSP ].

Section Run.
Variable Q : assn.

Ltac one_leaf x Hx Hxr CONT rho' HagL :=
  cbn [lf_state];
  lazymatch goal with |- _ (SymSoundR.SP _ _ ?Lf _) _ =>
    (apply (trr_inh RR); [lia|]); let w := fresh "w" in let HSP := fresh "HSP" in intros w HSP;
    let bs := eval vm_compute in (leaf_bools x Lf) in
    lazymatch bs with (?bA, ?bB, ?bR) =>
      let d := eval vm_compute in (match state_diff (recarved x Lf) (SM23 x) with Some d => d | None => ([], []) end) in
      let sets := eval vm_compute in (scratch_of (fst d)) in
      apply (m1_leaf x Hx Q CONT Lf rho' HagL bA bB bR) with (dL := d) (setsL := sets);
      [ vm_compute; reflexivity
      | tacEA ia K rho' w HagL HSP Hxr
      | tacEB ia K rho' w HagL HSP
      | tacER ia K rho' w HagL HSP
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | reflexivity
      | vm_compute; reflexivity
      | let mm := fresh "mm" in let rhoX := fresh "rhoX" in let HagS := fresh "HagS" in
        intros mm rhoX HagS; cbn [fst];
        solve_pairs ia Hi HagS ltac:(first [rewrite (ze_nosmall Hxr); reflexivity | rewrite (inos_0 Hxr); reflexivity | reflexivity]) ]
    end
  end.

Theorem gen_M1 x : ltac2:(tb__ "0|1|
S5bS5eS9aVx;A1Vsc;A2S5eVsc;S99Vx;A1A2A2Sa9Q40A1M0S2dSa9Q8A1A1F_;S4bVia;S84Vsc;Vs;A2VL;R1Vvm;A5Sd2Sd1ScfS73R2A2G0S29L_;A2Sd3Sd0A1U4S3eVia;A1A4VTR;VkB;S8fS73VK;S3aVia;R3A2Sc9Vx;A1A4VQ;A3F_;F_;FmW';VTR;VkB;S8fS73VK;Sa8Via;VmW;A2S74A4VQ;A3F_;F_;").
Proof using HLA HkB RR.
  intros Hx CONT. pose proof (iok_sc ia Hi) as SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  apply (trr_pre RR (SymSoundR.SP segsU K (SM1 x) rhoB)); [intros w [_ HSP0]; exact (enter x Hx rhoB w Hag HSP0)|].
  destruct x; cbn [m1_lo m1_hi] in Hx.
  - assert (Hxr : ~ (7 <= sc <= 38)) by lia. rewrite SM1_a_eq.
    apply ((trr_run RR) kB 500%nat CUTS_M1 K SM1_a LM1_a rhoB Q HkB (eq_trans runM1_a eq_refl) eq_refl (K_ia_impl Kc ia)).
    intros Lf rho' Hin Hab.
    assert (HagL : agrees (rho2 ia mW) rho') by (eapply agrees_below; [exact Hag | exact Hab | cbv; discriminate]).
    destruct Hin as [<-|[<-|[]]]; one_leaf M1a Hx Hxr CONT rho' HagL.
  - assert (Hxr : 7 <= sc <= 38) by lia. rewrite SM1_b_eq.
    apply ((trr_run RR) kB 500%nat CUTS_M1 K SM1_b LM1_b rhoB Q HkB (eq_trans runM1_b eq_refl) eq_refl (K_ia_impl Kc ia)).
    intros Lf rho' Hin Hab.
    assert (HagL : agrees (rho2 ia mW) rho') by (eapply agrees_below; [exact Hag | exact Hab | cbv; discriminate]).
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; one_leaf M1b Hx Hxr CONT rho' HagL.
  - assert (Hxr : ~ (7 <= sc <= 38)) by lia. rewrite SM1_c_eq.
    apply ((trr_run RR) kB 500%nat CUTS_M1 K SM1_c LM1_c rhoB Q HkB (eq_trans runM1_c eq_refl) eq_refl (K_ia_impl Kc ia)).
    intros Lf rho' Hin Hab.
    assert (HagL : agrees (rho2 ia mW) rho') by (eapply agrees_below; [exact Hag | exact Hab | cbv; discriminate]).
    destruct Hin as [<-|[<-|[]]]; one_leaf M1c Hx Hxr CONT rho' HagL.
  - assert (Hxr : ~ (7 <= sc <= 38)) by lia. rewrite SM1_d_eq.
    apply ((trr_run RR) kB 500%nat CUTS_M1 K SM1_d LM1_d rhoB Q HkB (eq_trans runM1_d eq_refl) eq_refl (K_ia_impl Kc ia)).
    intros Lf rho' Hin Hab.
    assert (HagL : agrees (rho2 ia mW) rho') by (eapply agrees_below; [exact Hag | exact Hab | cbv; discriminate]).
    destruct Hin as [<-|[<-|[]]]; one_leaf M1d Hx Hxr CONT rho' HagL.
Qed.
End Run.
End M.
End Mal_agrp_M.
