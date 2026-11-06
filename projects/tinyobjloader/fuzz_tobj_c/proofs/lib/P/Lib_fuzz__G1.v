(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "cons"; "list"; "nil"; "true"; "bool"; "app"; "fst"; "nat"; "snd"; "Some"; "option"; "andb"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "valuation"; "ss_next"; "sprop"; "sobj"; "SLit"; "SVar"; "holds"; "ss_facts"; "SAlu"; "ss_regs"; "obj_range"; "smatch"; "sv_eqb"; "FcsrFrm0"; "SPUle"; "eval"; "mkSS"; "ss_fregs"; "ss_objs"; "ss_pc"; "SPBranch"; "SPNot"; "ob_base"; "ob_hi"; "ob_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "ANone"; "ameas"; "JGA"; "JGA_pre"; "PostsCA"; "XA"; "ad_rank"; "aedesc"; "am_below"; "am_subst"; "AHead"; "amL_ok"; "am_eqb"; "client_callAT"; "ejcertA"; "free_callAT"; "new_objs_okA"; "open_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "topL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "eq_refl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FuzzOneIface"; "P0_fz"; "fuzz_one_sum_ex_stmt_P"; "fuzz_one_sum_stmt_P"; "FZ_P"; "Posts_fuzz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "Pre_free"; "MInvR"; "JL_free"; "J_free_pre"; "L_free"; "ok_sideK"; "ec_free"; "vm_insensitive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_fuzz__G1.Lib_fuzz_one"; "z0"; "tv_ok"; "am_L"; "tv00"; "X_P0"; "X_far0"; "PDA_lo"; "am_ok"; "X_P"; "E_fd"; "E_lo"; "VGp"; "X_far1"; "am0"; "pB"; "tv_L"; "E_FAR"; "L_ret"; "Posts_loF"; "Pre_fz"; "X_ms"; "cutsE"; "is_pay"; "pNn"; "E_lo3"; "FUEL_fz"; "T_ok"; "VGm"; "X_ret"; "X_rete"; "cutpcs_fz"; "exitsE"; "fz_pop"; "load_obj_ex_stmt"; "load_obj_stmt"; "s_lo"; "vG"; "C_1"; "C_L"; "T_err"; "T_far"; "T_fd"; "X_P01"; "X_Pf"; "X_ret2"; "X_rete2"; "fz_ms"; "lo_facts"; "pNX"; "run_of"; "spm"; "xARi"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "jpost"; "LQP"; "import_sub"; "J_ofP"; "call_checkP"; "call_linkP"; "import_okP"; "import_post"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs"; "NP"; "Pre_lo"; "P0_lo"; "P_ok"; "P_err"; "lo_entry"; "pH"; "xAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XRebase"; "XMerge"; "XSelect"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "eqb"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD";
"ALU_SUB"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "leaf"; "lf_state"; "sym_run"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "malloc_contracts"; "malloc_contracts_ex"; "fbin"; "tvin"; "FBx"; "JG"; "JG_pre"; "T_ok"; "call_checkT"; "malloc_laws"; "tnz"; "tv_below"; "tvd"; "tvv"; "tvz"; "T_after"; "T_afterN"; "caddr"; "import_tv"; "pclF"; "remove_nth"; "robjs_ok"; "robjs_okF"; "tvL_ok"; "tv_sub_eqb"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "emeasZ"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy"; "ghost_facts"; "pop_tv"; "popped"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAs"; "entAs_TR"; "entAs_check"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue"; "Posts_lo"; "@Stdlib.Bool.Bool"; "Is_true"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require Stdlib.Sorting.Permutation.
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ZeroObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CellTile.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAs.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FuzzOneIface.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_fuzz_one.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ZeroObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CellTile OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FuzzOneIface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition fz_ms : Z := 0x1a97c.
Definition fz_lo : Z := 0x1a9ac.
Definition fz_pop : Z := 0x1aa04.
Definition fz_fd : Z := 0x1aa24.
Definition fz_fa : Z := 0x1aa44.
Definition fz_retpc : Z := 0x1a9d0.
Definition FUEL_fz : nat := 600%nat.
Definition cutpcs_fz : list Z := ltac2:(tb__ "0|0|
S2S2cS86S2S2cSa1S2S2cS78S2S2cS56S4fA1S4S2cA1A3A3A3A3").

Definition Pre_fz : sstate := Pre_fuzz FZ_P.
Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
ScS3SbfA1M0A1S3S11A1Lx;Sc1S2bS71S76VS;S5A5G0Sb0SbfS11Sc0R1A4Lls;S4S11A1Xcx2").
Definition leaves_at (S : sstate) (pc : Z) : list sstate := ltac2:(tb__ "0|1|
SebS11S3S11A1SedS11A1S11Se9SabS25R1A1Vpc;A2M0A1Ll;S11SecG0A1Lx;S89VS;A1A6").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_fz end.

Definition X_ms : sstate := Eval vm_compute in nth 0 (leaves_at Pre_fz fz_ms) Pre_fz.
Definition X_ms1 : sstate := Eval vm_compute in optS (apply_xforms X_ms [XSplit 0 (SLit (-256))]).
Definition C_1 : sstate := Eval vm_compute in optS (zero_obj_at X_ms1 0).

Definition E_lo : sstate := Eval vm_compute in nth 0 (leaves_at C_1 P.Lib_load__G1.Lib_load_obj_defs.lo_entry) Pre_fz.
Definition spm : sv := SAlu ALU_ADD (SVar 10) (SLit (-400)).
Definition lo_facts : list sprop := ltac2:(tb__ "0|1|
S2S14S20S1aSbbS17P1eA1M0S16Z4000A1A3S8aA2S2S14S20G0S1aSbbS17PaA1S16N100A1A3A2S4S14A1A3A3").
Definition E_lof : sstate := add_facts lo_facts E_lo.
Definition E_lo1 : sstate := Eval vm_compute in optS (apply_xforms E_lof [XSplit 1 (SLit (-48)); XSplit 3 (SLit (-1904))]).
Definition E_loA : sstate := Eval vm_compute in optS (unbase_obj_at E_lo1 0 (-400)).
Definition E_loB : sstate := Eval vm_compute in optS (unbase_obj_at E_loA 1 (-256)).
Definition E_lo2 : sstate := Eval vm_compute in optS (unbase_obj_at E_loB 3 (-1904)).
Definition E_lo3 : sstate := Eval vm_compute in optS (recell_at E_lo2 0 0 4294967295).
Definition s_lo : wsub := ltac2:(tb__ "0|1|
S7S1S2dS10A2M0S2G0S0S2dS10P13S1aSbbS17PfA1S16Z770A1A3A4S4G0A1A3Sb2PaS70S9dA3A3").
Definition R_lo : list sobj := Eval vm_compute in optR (entails_fr E_lo3 P.Lib_load__G1.Lib_load_obj_defs.Pre_lo s_lo).
Definition PDA_lo : list (sstate * (list (sv * sv) * amode)) := ltac2:(tb__ "0|5|
S2S1S11S1S3S1S10S10A2M0A1M1S2eA2M2A2M3S0S11G2S9fS0G1S2eS2G0S0S10S10Sa3S16Z40A1A4S4G0A1M4A3S39Sa2A1A4A4S2G3S0S11G2Sa0S0G1S2eG4S2fA4A4S4G3A1A3A3").

Definition T_ok : sstate := Eval vm_compute in T_afterN P.Lib_load__G1.Lib_load_obj_defs.NP E_lo3 s_lo R_lo P.Lib_load__G1.Lib_load_obj_defs.P_ok.
Definition T_err : sstate := Eval vm_compute in T_afterN P.Lib_load__G1.Lib_load_obj_defs.NP E_lo3 s_lo R_lo P.Lib_load__G1.Lib_load_obj_defs.P_err.
Definition isub_ok : wsub := ltac2:(tb__ "0|0|
S95S7bS9cS9fS13S70A1A4").
Definition xARi : sv := Eval vm_compute in wsub_get isub_ok 100%positive.
Definition pHi : sv := Eval vm_compute in wsub_get isub_ok 101%positive.
Definition tv_ok : list (sv * sv) := ltac2:(tb__ "0|1|
S2S1S10S10A2M0S0S10S10S8bS16Z40A1A4S4G0A1A3").
Definition am_ok : amode := AHead pHi.

Definition pB : sv := SVar 400.  Definition pNn : positive := 401.  Definition pNX : sv := SVar 401.  Definition vG : sv := SVar 404.
Definition X_P0 : sstate := Eval vm_compute in nth 0 (leaves_at T_ok fz_pop) Pre_fz.
Definition X_far0 : sstate := Eval vm_compute in nth 0 (leaves_at T_ok (ec_free EC_P)) Pre_fz.
Definition X_rete : sstate := Eval vm_compute in nth 0 (leaves_at T_err fz_retpc) Pre_fz.
Definition C_L : sstate := ltac2:(tb__ "0|0|
S22S78SbeS10SbeS10SbeS10S1bS5cA1UbS66A4U14S17P195A1A4U1S17P196A1A4S23S5cA1S1fSeS10A1S7S15S24S5cA1S2S15Se5S66S6fA2S4S15A1A3A3S7S14S40S66S6fA2S7S14Se3P194A1S19S5cA1A3A3P197SfA9").

Definition is_pay (o : sobj) : bool := ltac2:(tb__ "0|0|
SdSdS1eS28Vo;A1S17PcA1A2S1eS2aVo;A1S16Z0A1A2A2S1eS29Vo;A1S17PdA1A2A2").
Definition tv_L : list (sv * sv) := ltac2:(tb__ "0|0|
Se4S66S6fS59A3").
Definition am_L : amode := AHeadN pNX vG.
Definition E_fd : sstate := Eval vm_compute in nth 0 (leaves_at C_L (ec_free EC_P)) Pre_fz.
Definition s_fd : wsub := ltac2:(tb__ "0|0|
Sb2PaS61S50S4fA1A3").
Definition R_fd : list sobj := Eval vm_compute in optR (entails_fr E_fd (Pre_free EC_P) s_fd).
Definition T_fd : sstate := Eval vm_compute in T_after E_fd s_fd R_fd (L_free EC_P).
Definition X_P : sstate := Eval vm_compute in nth 0 (leaves_at T_fd fz_pop) Pre_fz.
Definition X_far1 : sstate := Eval vm_compute in nth 0 (leaves_at T_fd (ec_free EC_P)) Pre_fz.

Definition E_FAR : sstate := ltac2:(tb__ "0|1|
S22S25S5dA1SbeS10S1bS5dA1U14S17S13S5dA1M0A1A4S23S5dA1S1fSeS10A1S24S5dA1S19S72A1SdfG0P1A2SfA9").
Definition am0 : amode := AHead (SLit 0).
Definition s_far1 : wsub := ltac2:(tb__ "0|0|
Sb2S45S64S68A3").
Definition s_fa : wsub := ltac2:(tb__ "0|0|
Sb2PaS68S50S4fA1A3").
Definition R_fa : list sobj := Eval vm_compute in optR (entails_fr E_FAR (Pre_free EC_P) s_fa).
Definition T_far : sstate := Eval vm_compute in T_after E_FAR s_fa R_fa (L_free EC_P).
Definition X_ret : sstate := Eval vm_compute in nth 0 (leaves_at T_far fz_retpc) Pre_fz.

Definition X_P01 : sstate := lenN_state X_P0.
Definition X_P02 : sstate := Eval vm_compute in pop_stateN X_P01 pHi (SVar (ss_next X_P0)).
Definition s_P0 : wsub := ltac2:(tb__ "0|1|
S2S1S2dS10A2M0S0S2dS10P194S17SdfS13S82A1P3A2A1A4S2G0S0S2dS10P195Sb1S10U14S1bS5cA1S16Z0A1A4A4S4G0A1A3A3").

Definition X_Pf : sstate := ltac2:(tb__ "0|0|
Sb3S2S14S27S26SbdS88S16Z0A1A3A1S4S14A1A3S60A2").
Definition X_P2 : sstate := Eval vm_compute in pop_stateN X_Pf pNX vG.
Definition s_P : wsub := ltac2:(tb__ "0|1|
S2S1S2dS10A2M0S0S2dS10P194S17SdfS13S83A1P3A2A1A4S2G0S0S2dS10P195Sb1S10U14S1bS60A1S16Z0A1A4A4S4G0A1A3A3").

Definition ret_xforms : list xform := ltac2:(tb__ "0|5|
S2Sa4Sa5U0M0A1S2Sa4Sa5U1M1A1S2Sa4Sa5U2M2A1S2Sa4Sa5U4M3A1S2Sa4Sa7S2S9G3S2S9G2S2S9U5S2S9G1S2S9G0S2S9U3S4S9A1A3A3A3A3A3A3A1S2Sa4Sa6G0A1M4S2Sa4G4S2Sa4Sa6G1A1S4Sa4A1A3A3A3A3A3A3A3A3").
Definition X_ret1 : sstate := Eval vm_compute in optS (apply_xforms X_ret ret_xforms).
Definition X_ret2 : sstate := Eval vm_compute in optS (unbase_obj_at X_ret1 1 (-400)).
Definition X_rete1 : sstate := Eval vm_compute in optS (apply_xforms X_rete ret_xforms).
Definition X_rete2 : sstate := Eval vm_compute in optS (unbase_obj_at X_rete1 1 (-400)).
Definition L_ret : sstate := L_fuzz FZ_P fz_retpc.
Definition s_ret : wsub := ltac2:(tb__ "0|0|
Sb2S45S84S69A3").
Definition s_rete : wsub := ltac2:(tb__ "0|0|
Sb2S45S85S69A3").

Definition z0 : sv := SLit 0.
Definition VGp (k : Z) : sv := ltac2:(tb__ "0|0|
S1aSbbS7cS16Vk;A1A3").
Definition VGm (k : Z) : sv := ltac2:(tb__ "0|0|
S1aSbcS7cS16Vk;A1A3").
Definition tv00 : list (sv * sv) := [].
Definition cutsE : list aedesc := ltac2:(tb__ "0|8|
S2S1S1S11S1S3S1S10S10A2A1M0S2eA2M1A2M2S1S2cS10A2M3A2M4S0G2G3S0S11G1S6bS0G0S2eS5bS2fA4M5A4S0S2cS10Z64S58A4A4S2G4S0G2G3S0S11G1S7dG5A4S0S2cS10Z5aS58A4A4S2G4S0G2G3S0S11G1S72S0G0S2eS59S5fA4A4S0S2cS10Z3cS58A4M6A4S2G4S0G2G3S0S11G1S7fG5A4G6A4S2G4S0G2G3S0S11G1S7eS0G0S2eS67S5aA4A4S0S2cS10Z28M7S63Z2A1A4A4S2G4S0G2G3S0S11G1S81S0G0S2eS59S5aA4A4S0S2cS10G7S63Z0A1A4A4S2G4S0G2G3S0S11G1S80S0G0S2eS5bS65A4A4S0S2cS10Z14S58A4A4S4G4A1A3A3A3A3A3A3A3").
Definition exitsE : list aedesc := ltac2:(tb__ "0|b|
S2S1S1S11S1S3S1S10S10A2A1M0S2eA2M1A2M2S1S2cS10A2M3A2M4S0G2G3S0S11G1S6cS0G0S2eS5bS2fA4M5A4S0S2cS10Z5fS58A4A4S2G4S0G2G3S0S11G1S62G5A4S0S2cS10Z50S58A4A4S2G4S0G2G3S0S11G1S75G5A4S0S2cS10ZaS58A4M6A4S2G4S0G2G3S0S11G1S5cS0G0S2eS59S5fA4M7A4S0S2cS10Z32S58A4A4S2G4S0G2G3S0S11G1S5dG7A4S0S2cS10Z37S58A4A4S2G4S0G2G3S0S11G1S61S0G0S2eS67S5aA4A4S0S2cS10Z28M8S63Z1M9A1A4A4S2G4S0G2G3S0S11G1S60S0G0S2eS59S5aA4MaA4S0S2cS10G8S73G9A1A4A4S2G4S0G2G3S0S11G1S64GaA4S0S2cS10Z1eS58A4A4S2G4S0G2G3S0S11G1S74S0G0S2eS5bS65A4A4G6A4S4G4A1A3A3A3A3A3A3A3A3A3").

Definition Posts_loF (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) := ltac2:(tb__ "0|0|
S33S2bS41VKc;S9eS5eVFB;A6").
Definition load_obj_stmt : Prop := ltac2:(tb__ "0|0|
S8fOF_;S3S8dA1S8cOF_;F_;S3S1S2cS2cA2A1S12S55S2bR4R3A3S91S2bR5S43S2bS32S2bS41R4S9eR3A1R3S4S1S10S10A2A1S2fA7S9dR2A4S94S2bS9cR2S6aR4R3A2A4A4F_;Frho0;FFB;FKc;Fok;").
Definition load_obj_ex_stmt : Prop := ltac2:(tb__ "0|0|
S3S8dA1S8cOF_;F_;S3S1S2cS2cA2A1S12S57R3A1S90S2bS43S2bS32S2bS41R4S9eR3A1R3S4S1S10S10A2A1S2fA7S9dR2A4S94S2bS9cR2S6aR4R3A2A4A3F_;Frho0;FFB;FKc;").

Goal call_checkP E_lo3 P.Lib_load__G1.Lib_load_obj_defs.Pre_lo s_lo R_lo (map fst PDA_lo) = true /\ call_checkP E_fd (Pre_free EC_P) s_fd R_fd [L_free EC_P] = true
     /\ call_checkP E_FAR (Pre_free EC_P) s_fa R_fa [L_free EC_P] = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Ltac find_idx F l := lazymatch l with | F :: _ => constr:(O) | _ :: ?t => let i := find_idx F t in constr:(S i) end.
Ltac have_fact HF F :=
  lazymatch type of HF with Forall _ ?l =>
    let l' := eval vm_compute in l in let F' := eval vm_compute in F in let i := find_idx F' l' in
    pose proof (Forall_pick _ _ i F HF eq_refl) end.

Lemma ameas_emeasZ : ltac2:(tb__ "0|2|
S11S3S1S10S10A2A1M0S2eS2cS10S12S46S2cS30S0S1S11S1G0S2eA2M1A2S1S2cS10A2S0S11G1R6S0G0S2eR5R4A4A4S0S2cS10R3R2A4A4R1A2SdeR3R2R1A3A3Frho;Fv;Fr;Fam;Ftv;FS;").
Proof. intros. reflexivity. Qed.

Lemma pay_range : ltac2:(tb__ "0|2|
S3S1S2cS2cA2M0A1S12S12S15S2cS4aR5R4A2S92S45R5R4A3S46S6S6eR4A1S5A3S47Sa8S8S2cS2cS1cR6R5A2M1A3R4A2Sa9R4SaS2cS2cG1A3A2A2S48S2cS2cS48S2cS2cS47SacG0S0S2cS2cR2R1A4RbA3S47Sa8R2R7A2Sa9R7SaaR2R1A2A2A2A2Ln;A2Lb;A2F_;F_;F_;F_;Fa;Fo;Frho;Frho0;FFB;").
Proof.
  intros FB rho0 rho o a HP0 Hav Ht Hr. unfold is_pay in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 12%positive ltac:(reflexivity)), <- (Hw 13%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  pose proof (bv_urange (rw rho0 13)) as R13.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 13))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.

Section Fz.
Variable Kc : ltac2:(tb__ "0|0|
S3S8dA1S8cOF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs C_P.

Let JGv (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S31S2bS41S45VKc;Vrho0;S4aVFB;A1VFB;Vtv;Vam;A9").
Let Q : assn := ltac2:(tb__ "0|0|
S94S2bS45Vrho0;S4eS2bS41S4dVKc;VFB;A5A4").

Lemma ejcert_ok : ltac2:(tb__ "0|0|
S46S6S3dS2bS45S71S76S45S6dS77A7S5A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma pay_pclF : ltac2:(tb__ "0|1|
S12S15S2cS3S15A1S3S14A1SacS15R4R2A3S46S6S6eR5A1S5A3S4aVFB;Vrho0;A2S92S45Vrho0;R8A3SafS14S18R9A1R5A3S47Sa8S8S2cS2cS1cRaR9A2M0A3R8A2Sa9R8SaS2cS2cG0A3A2A2Sd5S2bS41Vrho0;VFB;R9A5F_;F_;F_;F_;F_;F_;Ffacts;Fobjs;Fa;Fo;Frho;").
Proof using .
  intros rho o a objs facts _ Ht HP0 Hav _ Hr. destruct (pay_range FB rho0 rho o a HP0 Hav Ht Hr) as (b & n & Hin & Hbn).
  right; right. exists b, n. auto.
Qed.

Lemma pay_caddr_free : ltac2:(tb__ "0|2|
Sb9S12S12S8cS3S1S10S10A2M0A1G0S15S2cS51S2bS41R8R7R5A5Sc4VFB;R9A2Sc5VFB;RaR8R6A4SacG0R6R7A3SccRaR7A2S4aVFB;Vrho0;A2S92S45Vrho0;RcA3S46S6S6eR9A1S5A3S47Sa8S8S2cS2cS1cReRaA2M1A3R9A2Sa9R9SaS2cS2cG1A3A2A2Sd3S2bS41R11SbS2cS8S2cS2cScfRfRcA2A3A2RaA5F_;F_;F_;F_;F_;F_;F_;F_;F_;Fa;Fo;Ft;Ftv;Fmd;Frho;FrhoM;FAi;").
Proof using JGv.
  intros Ai rhoM rho md tv t o a HM HP HN Ht Hnz HP0 Hav Htx Hr.
  destruct (pay_range FB rho0 rho o a HP0 Hav Htx Hr) as (b & n & Hin & Hbn).
  right; right. exists b, n. split; [exact (HP _ Hin)|]. split; [|exact Hbn].
  intros Heq. injection Heq as Heq.
  destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (Tpos & Tin & Tfb).
  unfold tvv in Heq, Tpos, Tin, Tfb. cbn [fst snd] in Heq, Tpos, Tin, Tfb. rewrite Heq in Tin, Tfb.
  set (tn := bv_unsigned (eval rho (snd t))) in *.
  assert (Hne : (b, tn) <> (b, n)) by (intros E; apply Tfb; rewrite E; exact Hin).
  exact (blocks_bases_differ segs C_P Ai rhoM md b tn b n HM Tin (HP _ Hin) Hne Tpos ltac:(lia) eq_refl).
Qed.

Lemma SPJ_JGA_JG : ltac2:(tb__ "0|0|
S3S1S10S10A2A1S2eS11S12S8fS43S2bVJGv;R5R4A2R3R2R1A5S43S2bSc7S2bS41S45VKc;Vrho0;S4aVFB;A1VFB;R6A8R4R3R2A5F_;Fw;Frho;FS;Fam;Ftv;").
Proof using . intros tv am S rho w [Hs [Ai [HJ _]]]. split; [exact Hs|]. exists Ai. exact HJ. Qed.

Lemma lo_facts_ok : ltac2:(tb__ "0|0|
S12SafS14S18R1A1S19S62A1A3SafS14S18R2A1S87A3F_;Frho;").
Proof using .
  intros rho HF.
  have_fact HF (SPUle (SVar 30) (SAlu ALU_ADD spm (SVar 15))). have_fact HF (SPBranch BC_GE (SLit (- FZ_DEPTH)) (SVar 15)).
  have_fact HF (SPBranch BC_GE (SVar 15) (SLit (- 2 ^ 40))). have_fact HF (SPUle (SVar 10) (SLit (2 ^ 47))).
  have_fact HF (SPUle (SVar 30) (SVar 10)).
  have_fact HF (SPUle (SLit aceil_lo) (SVar V_TOP)). have_fact HF (SPUle (SVar V_TOP) (SLit aceil_hi)). clear HF.
  unfold lo_facts, spm, aceil, FZ_DEPTH, V_TOP in *. zfacts; lia.
Qed.

Lemma P0_lo_of_fz : ltac2:(tb__ "0|0|
S12S3S15A1Sb8S4aVFB;Vrho0;A2S92S45Vrho0;R4A3S9eSc6VFB;R5S4S1S10S10A2A1A3Sb5Sb4R5R4R3A3S7bA2A2F_;F_;Fms;FR;Frho;").
Proof using .
  intros rho R ms HP0 Hav. unfold P.Lib_load__G1.Lib_load_obj_defs.P0_lo. rewrite !rw_call'.
  change (wsub_get s_lo 14) with (SVar 13). change (wsub_get s_lo 13) with (SVar 12). cbn [eval].
  destruct Hav as [Hw _]. rewrite <- (Hw 12%positive ltac:(reflexivity)), <- (Hw 13%positive ltac:(reflexivity)).
  unfold FBx. cbn [List.filter map]. rewrite app_nil_r. exact HP0.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S44S11S12S8eSafS14S18R2A1S19R3A1A3VTR;S43S2bR5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S8eS8eS8eS8fR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS8eS8eR3VTR;R3R2A2F_;VTR;S8fS47R5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S44S44S11S11Sb6S3S15A1M0S3S1S11S93A2M1A1S8eS12S46ScG0A1SddR7R6R5A3SbG0R4A2A3S46S6S97R8R7R6R5Sb0G1S11S8S11S93A2R4A4A5S5A3S12VTR;S43S2bRbR9R1A4S94S2bS13R9A1R1R6A4A2Frho1;S3S8dA1M2Sb8S8cS1dS2bR7RdS0G2SdbR3SdcR2R1A2A4A4R10R8R4R2A3R10Sb5Sb4R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S11S93G2Sb8S8cS12G2Sb8S8cSacG1S0S11S93R9R8A4R10A3S1dS2bRfR15S0G2SdbR8SdcR7R6A2A4A4R18R10R9R7A3S92S13R16A1Sb5Sb4R11R14R9A3R15A2R7A3S1dS2bR8RdS0G2SdbR7SdcR6R5A2A4A4RdSb5Sb4R13R16RbA3R17A2R9R8R6A4S47S99R14RcR17R18R19RfRaA7S12S98R15RdR18R19R1aR1bR10R1RbA9VTR;S43S2bS96R10Sb5Sb4R16R19ReA3R1aA2RcA3S9aR1aS13R1bA1R11S13R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S43S2bReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CFREE : ltac2:(tb__ "0|1|
Sb9S12VTR;S43S2bS53S2bS41R2VKc;A4S50S4fA1R1A4S94S2bS45R1S2S1S11S93A2M0S0S11S93S54S4fA1S52S2bS41R2VKc;A4A4S4G0A1A3A4A2Frho1;FAi;").
Hypothesis CLO : ltac2:(tb__ "0|0|
S3S1S2cS2cA2A1S12VTR;S43S2bS32S2bS41VKc;S9eR2A1R2S4S1S10S10A2A1S2fA7S9dR1A4S94S2bS9cR1S33S2bS41VKc;S9eS5eR2A6A4A2Frho1;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|5|
S11S3S1S10S10A2A1M0S2eS1S2cS10A2M1S12S2cSacS1S1S11S1G0S2eA2M2A2M3G1A2S0G3G1S0S11G2R6S0G0S2eR5R4A4A4R3A4S6dA3S47Sa8Z0S30S0G3G1S0S11G2R7S0G0S2eR6R5A4A4R4A4R3A2M4A2Sa9G4R2A2A2VTR;S43S2bVJGv;R7R6A2R8R4A4VFAM;R3A1A2F_;F_;Fb;Frho;Frv;Fam;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S12S2cVTR;S43S2bSc7S2bS41S45VKc;Vrho0;S4aVFB;A1VFB;S4S1S10S10A2A1A8S69R2A4VFAM;R1A1A2Fb;Frho;").

Let FREE : ltac2:(tb__ "0|8|
S11Sb6S3S15A1M0S12S3S1S10S10A2M1A1S2eS9G1S8eSb9S12VTR;S43S2bS53S2bS41R2VKc;A4S50S4fA1M2R1A4S94S2bSe2R1S2S1S11S93A2M3S0S11S93S54S4fA1M4S52S2bS41R2VKc;A4A4S4G3A1A3A4A2Frho1;FAi;S46ScG0A1SddRaG2R9A3SbG0R8A2A3S46S6ScaS41S45RbG2RaR9S2S11G4S4S11A1A3A7S5A3S46S6Se0S45S13RcA1A2S5A3S46S6ScdS13RdA1R9A2S5A3S46S6S37S13ReA1R9A2S5A3S46ScG1A1SaeG1RbR9A3SbG1R8A2A3Sb9SafS14S18ReA1S19R11A1A3S4aVFB;Vrho0;A2S92S45Vrho0;R10A3Sc4VFB;R4A2Sc5VFB;R5R12R11A4SceR13R12A2Sd0R14R13A2S34VFB;R13R8R15R14A5S48S12S12S48S8cS8cS51S2bS41RbR2R1A5Lmd;A2LrhoM;A2Sc9R17S42SbaRaA1A1A2S47SccR18R14A2S47S46S1S2cS2cA2ScfR18R14A2S0S2cS2cSe1Q40M5S21R18Sb7R1aPcA2A2A2M6Se1G5S21R18Sb7R1aPdA2A2A2A4A3Sd7S2bS41RbSbS2cG6A2R18R19A6A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S12S92S13R12A1RfR1A3VTR;S43S2bS31S2bS41S45VKc;Vrho0;S4aVFB;A1M7VFB;Sd6G1RdRfA3ReA9Sd1R13R12R11G4A4R2A4RbA2F_;Frho';VTR;S43S2bS31S2bS41S45VKc;Vrho0;G7VFB;ReRdA9R12RfA4RaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ft;Fi;Fam;Ftv;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S3eS2bS41S4fS45VKc;Vrho0;S4aVFB;A1VFB;VML;VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;Ae").
Let ENTAS : ltac2:(tb__ "0|4|
Sb6S2dS11S11S3S1S10S10A2M0A1M1G1G1S2eS2eS10S2cS2cS10S12S12S8eS46S6Se7S45R10RfReRdRcRbR9R8R7R6R5R4AdS5A3SeaG0RcRbA3S92R11R5R4A3S12S47Sa8Z0SdeRaRbR1A3M2A2Sa9G2SdeR9R8R7A3A2A2VTR;S43S2bG1S2eS31S2bS41S45VKc;Vrho0;S4aVFB;A1VFB;R2R1A9Lam;Ltv;M3RfRdA2R12R2A4R6A2F_;Frho';VTR;S43S2bG3R10RdA2R12R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Famj;Fami;Ftvj';Ftvj;Ftvi;FA;FX;Fn;Fs0;") := ltac2:(tb__ "0|0|
Se6S2bS41S45VKc;Vrho0;S4aVFB;A1VFB;VML;VTR;VTR_pre;VTR_exw;VTR_pureh;Ac").
Let CALLLO : ltac2:(tb__ "0|e|
S11Sb6S3S15A1M0S12S3S1S10S10A2M1A1M2G2S2eS8eS46ScG0A1SddR8S9dR7A3SbG0R6A2A3S46S6ScaS41S45R9S9dR8R7Sb0S1S11S1G2S2eA2M3A2M4S11S8S11G3A2S5eA4A7S5A3S46S6S9bR9S9cA2S5A3S46S6Se0S45S13RbA1A2S5A3S46S6ScdS13RcA1S7G1R8R7A3A2S5A3S46S6S37S13RdA1R7A2S5A3S46S6SdaRdR9S4G1A1A3S5A3S46S6S3bS38ReS2fA2R9A2S5A3S46S6SadG4G4SdSdSd9S9cR10S13R11A1M5S8S11G3R1A3M6S8G2S2eSaS11G3R1A3M7A3M8A5S3aS9cR10G5G6SaG2S2eG7A3M9A5A2S3fS9dG6G8G9A4A2Ld;S5eA3S5A3Sb9Sb8SafS14S18R10A1S19R13A1A3S4aVFB;Vrho0;A2S92S45Vrho0;R12A3Sc4VFB;R5A2Sc5VFB;R6R14S7G1R13R12A3A4SceR15S7G1R14R13A3A2Sd0R16S7G1R15R14A3A2S34VFB;R14R9R17S7G1R16R15A3A5S48S12S12S48S8cS8cS51S2bS41RcR2R1A5Lmd;A2LrhoM;A2Sc9R19S42SbaRbA1A1A2S47Sd8S2bS41Vrho0;VFB;R1aR19R1bA7S9eSc6VFB;R1aR19A3Sb5Sb4R1aR1bRbA3R1cA2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;G4S12SacG4R2S5eA3S92S13R15A1R12R2A3VTR;S43S2bS31S2bS41S45VKc;Vrho0;S4aVFB;A1MaVFB;S7G1R12Sd4S95R15S9cS8S11G3R4A3MbS13R16A1A4McS8G2S2eSaS11G3R4A3MdA3A2A3S38GcSaG2S2eGdA3A2A9Sd2S9cR16R15R14GbA5R3A4RfA2F_;F_;Frho';Fd;VTR;S43S2bS31S2bS41S45VKc;Vrho0;GaVFB;S7G1RfReA3RdA9R13R10A4RcA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Fpassed;Fkept;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S3cS2bS41S45VKc;Vrho0;S4aVFB;A1VFB;VML;S9eS9dS4S1S10S10A2A1S2fS5eS9cS49S2dS13S9dA1A2VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;VCLO;A15").

Lemma reenter_rank : ltac2:(tb__ "0|4|
S11S3S1S10S10A2A1M0S2eS2cS10S36S12S12SacS1S1S11S1G0S2eA2M1A2M2S1S2cS10A2M3A2S0G2G3S0S11G1R8S0G0S2eR7R6A4A4S0S2cS10R5R4A4A4S6dA3Sa8Z0R6A2Sa8SaaR7Z1A2S35R5A1A2VTR;S43S2bVJGv;RaR9A2RbR4A4VFAM;S30R6R5A2A1A2F_;F_;F_;Frho;FrhoX;FX;FvT;FrT;Fam;Ftv;FT;").
Proof using REENTER.
  intros T tv am rT vT X rhoX rho Hin H0 Hr. apply (REENTER T tv am (rT, vT) rho); [exact Hin|].
  unfold ameas, ad_rank, ad_var in *. cbn [fst snd] in *.
  pose proof (urange (eval rho vT)). pose proof (urange (eval rhoX (snd (snd X)))). nia.
Qed.

Lemma X_ms_ok : ltac2:(tb__ "0|2|
S12VTR;S43S2bVJGv;S5bS2fA2S6cR1A4VFAM;S30S0S1S11S1S3S1S10S10A2A1M0S2eA2M1A2S1S2cS10A2S0S11G1S6cS0G0S2eS5bS2fA4A4S0S2cS10Z5fS58A4A4R1A2A1A2Frho;").
Proof using REENTER TR_pre.
  intros rho. apply (TR_pre (SPJ segs (JGv tv00 ANone) C_1 rho)).
  - intros w [Hs HJ]. split; [|exact HJ].
    apply (smatch_zero_obj segs rho X_ms1 0 C_1 w ltac:(vm_cast_no_check (@eq_refl (option sstate) (Some C_1)))).
    exact (smatch_xforms segs [XSplit 0 (SLit (-256))] rho X_ms X_ms1 w ltac:(vm_cast_no_check (@eq_refl (option sstate) (Some X_ms1))) Hs).
  - apply (reenter_rank C_1 tv00 ANone 90 z0 (X_ms, (tv00, ANone), (95, z0)) rho rho); [apply (nth_error_In cutsE 1); reflexivity | lia | cbn; lia].
Qed.

Lemma E_lo_ok : ltac2:(tb__ "0|2|
S12VTR;S43S2bVJGv;S5bS2fA2S62R1A4VFAM;S30S0S1S11S1S3S1S10S10A2A1M0S2eA2M1A2S1S2cS10A2S0S11G1S62S0G0S2eS5bS2fA4A4S0S2cS10Z50S58A4A4R1A2A1A2Frho;").
Proof using CALLLO REENTER.
  intros rho. apply (TR_pre (SPJ segs (JGv tv00 ANone) E_lo3 rho)).
  { intros w Hw.
    apply (SPJ_recell segs _ rho E_lo2 0 0 4294967295 E_lo3 w ltac:(vm_cast_no_check (@eq_refl (option sstate) (Some E_lo3)))).
    assert (Hw1 : SPJ segs (JGv tv00 ANone) E_lo1 rho w).
    { apply (SPJ_xforms segs _ [XSplit 1 (SLit (-48)); XSplit 3 (SLit (-1904))] rho E_lof E_lo1 w ltac:(vm_compute; reflexivity)).
      unfold E_lof. apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md _ HF. apply lo_facts_ok. exact HF. }
    apply (SPJ_unbase segs _ rho E_loB 3 (-1904) E_lo2 w ltac:(vm_cast_no_check (@eq_refl (option sstate) (Some E_lo2)))).
    apply (SPJ_unbase segs _ rho E_loA 1 (-256) E_loB w ltac:(vm_cast_no_check (@eq_refl (option sstate) (Some E_loB)))).
    apply (SPJ_unbase segs _ rho E_lo1 0 (-400) E_loA w ltac:(vm_cast_no_check (@eq_refl (option sstate) (Some E_loA)))). exact Hw1. }
  change (JGv tv00 ANone) with (JGv ([] ++ []) ANone).
  apply (CALLLO E_lo3 s_lo R_lo rho [] [] ANone).
  - vm_cast_no_check (@eq_refl (option (list sobj)) (Some R_lo)).
  - vm_cast_no_check (@eq_refl bool true).
  - vm_cast_no_check (@eq_refl bool true).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai ms HF HP0 Hav HP HN HD HZ HXA HM HT. split.
    + eapply (robjs_checkF_sound segs C_P rho0 FB rho (ss_facts E_lo3) [] is_pay R_lo HF (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT)); [exact HZ | vm_cast_no_check (@eq_refl bool true) |].
      intros o a Ho Hx Hr. apply pclF_FBx. exact (pay_pclF rho o a _ _ Ho Hx HP0 Hav HF Hr).
    + apply P0_lo_of_fz; [exact HP0 | exact Hav].
  - intros d rho' Hd Hag. destruct Hd as [<-|[<-|[]]]; cbn [fst snd].
    + match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv ?am) ?T _) _ =>
        replace tv with tv_ok by (vm_compute; reflexivity); replace am with am_ok by (vm_compute; reflexivity);
        replace T with T_ok by (vm_cast_no_check (@eq_refl sstate T_ok)) end.
      apply (reenter_rank T_ok tv_ok am_ok 60 z0 _ rho rho'); [apply (nth_error_In cutsE 2); reflexivity | lia | cbn; lia].
    + match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv ?am) ?T _) _ =>
        replace tv with tv00 by (vm_compute; reflexivity); replace am with ANone by (vm_compute; reflexivity);
        replace T with T_err by (vm_cast_no_check (@eq_refl sstate T_err)) end.
      apply (reenter_rank T_err tv00 ANone 60 z0 _ rho rho'); [apply (nth_error_In cutsE 3); reflexivity | lia | cbn; lia].
Qed.

Lemma X_P0_ok : ltac2:(tb__ "0|2|
S12VTR;S43S2bVJGv;S59S5fA2S5cR1A4VFAM;S30S0S1S11S1S3S1S10S10A2A1M0S2eA2M1A2S1S2cS10A2S0S11G1S5cS0G0S2eS59S5fA4A4S0S2cS10Z32S58A4A4R1A2A1A2Frho;").
Proof using ENTAS REENTER.
  intros rho.
  apply (TR_pre (fun w => exists rho2, agree_below (ss_next X_P0) rho rho2 /\
                   SPJ segs (JGv (pop_tv pHi (ss_next X_P01) tv_ok) (AHeadN (SVar (ss_next X_P01)) (SVar (ss_next X_P01 + 3)%positive))) X_P02 rho2 w)).
  { intros w Hw.
    destruct (JGA_lenN segs C_P NF Kc rho0 (P0_fz FB) FB ML tv_ok pHi X_P0 rho w eq_refl eq_refl eq_refl ltac:(vm_cast_no_check (@eq_refl bool true)) Hw) as (rho1 & Hag1 & Hw1).
    destruct (JGA_popN segs C_P NF Kc rho0 (P0_fz FB) FB ML (TobjJVA.NP_ok_intro NF eq_refl) tv_ok pHi (SVar (ss_next X_P0)) X_P01 is_pay rho1 w
                ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl eq_refl eq_refl eq_refl ltac:(vm_cast_no_check (@eq_refl bool true))
                ltac:(intros o a Ho Hx HP0 Hav HF Hr; exact (pay_pclF rho1 o a _ _ Ho Hx HP0 Hav HF Hr)) eq_refl Hw1) as (rho2 & Hag2 & Hw2 & _).
    exists rho2. split; [|exact Hw2].
    eapply agree_below_trans; [exact Hag1|]. eapply agree_below_le; [|exact Hag2]. apply Pos.leb_le. reflexivity. }
  apply TR_exw; intros rho2. apply TR_pureh; intros Hag.
  apply (ENTAS s_P0 (ss_next X_P0) X_P02 C_L _ tv_L tv_L _ am_L (VGp 2) 40 50 z0 rho rho2).
  - vm_cast_no_check (@eq_refl bool true).
  - apply Permutation_refl.
  - apply agree_below_vals. exact Hag.
  - intros rho' Hm. apply (REENTER C_L tv_L am_L (40, VGp 2) rho'); [apply (nth_error_In cutsE 4); reflexivity | rewrite ameas_emeasZ; exact Hm].
Qed.

Lemma X_P_ok : ltac2:(tb__ "0|2|
S12VTR;S43S2bVJGv;S59S5aA2S60R1A4VFAM;S30S0S1S11S1S3S1S10S10A2A1M0S2eA2M1A2S1S2cS10A2S0S11G1S60S0G0S2eS59S5aA4A4S0S2cS10Z28S73Z1A1A4A4R1A2A1A2Frho;").
Proof using ENTAS REENTER.
  intros rho.
  apply (TR_pre (fun w => exists rho1, agree_below (ss_next X_Pf) rho rho1 /\
                   SPJ segs (JGv (pop_tv pNX (ss_next X_Pf) tv_ok) (AHeadN (SVar (ss_next X_Pf)) (SVar (ss_next X_Pf + 3)%positive))) X_P2 rho1 w)).
  { intros w Hw.
    assert (Hwf : SPJ segs (JGv tv_ok am_L) X_Pf rho w).
    { unfold X_Pf. apply SPJ_refacts_J; [exact Hw | reflexivity |]. intros tr md _ HF.
      have_fact HF (SPBranch BC_NE pNX (SLit 0)). clear - H. constructor; [|constructor]. unfold pNX in *. zfacts; lia. }
    destruct (JGA_popN segs C_P NF Kc rho0 (P0_fz FB) FB ML (TobjJVA.NP_ok_intro NF eq_refl) tv_ok pNX vG X_Pf is_pay rho w
                ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl eq_refl eq_refl eq_refl ltac:(vm_cast_no_check (@eq_refl bool true))
                ltac:(intros o a Ho Hx HP0 Hav HF Hr; exact (pay_pclF rho o a _ _ Ho Hx HP0 Hav HF Hr)) eq_refl Hwf) as (rho1 & Hag1 & Hw1 & _).
    exists rho1. split; [exact Hag1 | exact Hw1]. }
  apply TR_exw; intros rho1. apply TR_pureh; intros Hag.
  apply (ENTAS s_P (ss_next X_Pf) X_P2 C_L _ tv_L tv_L _ am_L (VGp 2) 40 40 (VGm 1) rho rho1).
  - vm_cast_no_check (@eq_refl bool true).
  - apply Permutation_refl.
  - apply agree_below_vals. exact Hag.
  - intros rho' Hm. apply (REENTER C_L tv_L am_L (40, VGp 2) rho'); [apply (nth_error_In cutsE 4); reflexivity | rewrite ameas_emeasZ; exact Hm].
Qed.

Lemma E_fd_ok : ltac2:(tb__ "0|2|
S12VTR;S43S2bVJGv;S67S5aA2S61R1A4VFAM;S30S0S1S11S1S3S1S10S10A2A1M0S2eA2M1A2S1S2cS10A2S0S11G1S61S0G0S2eS67S5aA4A4S0S2cS10Z28S63Z1A1A4A4R1A2A1A2Frho;").
Proof using CFREE FREE REENTER.
  intros rho. apply TR_facts. intros HF0.
  apply (FREE E_fd s_fd R_fd rho tv_L am_L 0%nat (pB, blk_size pNn) _ CFREE).
  - vm_cast_no_check (@eq_refl (option (list sobj)) (Some R_fd)).
  - vm_cast_no_check (@eq_refl bool true).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HX HM HT.
    change (wsub_get s_fd 12) with pB. change (wsub_get s_fd 13) with (blk_size pNn).
    assert (Tnz : tnz rho (pB, blk_size pNn)).
    { apply tnz_of_fact. have_fact HF (SPUle (SLit 4096) pB). clear - H. intros Hz%holds_beq. unfold pB in *. zfacts; lia. }
    split; [exact Tnz|]. split; [reflexivity|].
    destruct HM as (rhoM & md & HM).
    eapply (robjs_check_sound segs C_P FB Ai rho (ss_facts E_fd) tv_L (Some 0%nat) is_pay R_fd _ rhoM md HM HT HF HN HD HZ).
    + vm_cast_no_check (@eq_refl bool true).
    + intros o a Ho Hx Hr. change (bv_unsigned (eval rho pB)) with (fst (tvv rho (pB, blk_size pNn))).
      exact (pay_caddr_free Ai rhoM rho md tv_L _ o a HM HP HN ltac:(left; reflexivity) Tnz HP0 Hav Hx Hr).
    + exists (pB, blk_size pNn). split; [reflexivity|]. split; [exact Tnz | reflexivity].
  - intros rho' Hag.
    replace (T_after E_fd s_fd R_fd (L_free EC_P)) with T_fd by (vm_cast_no_check (@eq_refl sstate T_fd)).
    change (remove_nth 0 tv_L) with tv_ok.
    apply (REENTER T_fd tv_ok am_L (40, VGp 0) rho'); [apply (nth_error_In cutsE 5); reflexivity|].
    have_fact HF0 (SPUle vG (SLit two52)). clear - H Hag.
    unfold ameas, ad_rank, ad_var. cbn [fst snd]. unfold VGp, vG, two52 in *.
    rewrite <- (eval_agree_vals (ss_next E_fd) rho rho' (SAlu ALU_ADD (SVar 404) (SLit 0)) Hag eq_refl).
    zfacts; lia.
Qed.

Lemma E_FAR_free : ltac2:(tb__ "0|0|
S12S12S36Sa8Z15S35R1A1A2VTR;S43S2bVJGv;S59S65A2S68R3A4VFAM;S30R2R4A2A1A2F_;FX;Frho;FrhoX;").
Proof using CFREE FREE REENTER.
  intros rhoX rho X HX.
  apply (FREE E_FAR s_fa R_fa rho tv_ok am0 0%nat (xARi, SLit 64) _ CFREE).
  - vm_cast_no_check (@eq_refl (option (list sobj)) (Some R_fa)).
  - vm_cast_no_check (@eq_refl bool true).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HX' HM HT.
    change (wsub_get s_fa 12) with xARi. change (wsub_get s_fa 13) with (SLit 64).
    assert (Tnz : tnz rho (xARi, SLit 64)).
    { apply tnz_of_fact. have_fact HF (SPUle (SLit 4096) xARi). clear - H. intros Hz%holds_beq. unfold xARi in *. zfacts; lia. }
    split; [exact Tnz|]. split; [reflexivity|].
    destruct HM as (rhoM & md & HM).
    eapply (robjs_check_sound segs C_P FB Ai rho (ss_facts E_FAR) tv_ok (Some 0%nat) is_pay R_fa _ rhoM md HM HT HF HN HD HZ).
    + vm_cast_no_check (@eq_refl bool true).
    + intros o a Ho Hx Hr. change (bv_unsigned (eval rho xARi)) with (fst (tvv rho (xARi, SLit 64))).
      exact (pay_caddr_free Ai rhoM rho md tv_ok _ o a HM HP HN ltac:(left; reflexivity) Tnz HP0 Hav Hx Hr).
    + exists (xARi, SLit 64). split; [reflexivity|]. split; [exact Tnz | reflexivity].
  - intros rho' Hag.
    replace (T_after E_FAR s_fa R_fa (L_free EC_P)) with T_far by (vm_cast_no_check (@eq_refl sstate T_far)).
    change (remove_nth 0 tv_ok) with tv00.
    apply (REENTER T_far tv00 am0 (20, z0) rho'); [apply (nth_error_In cutsE 6); reflexivity|].
    unfold ameas, ad_rank, ad_var in *. cbn [fst snd] in *. unfold z0. rewrite U_lit. unfold M64v. rewrite Z.mod_0_l by lia.
    pose proof (urange (eval rhoX (snd (snd X)))). nia.
Qed.

Lemma X_far0_ok : ltac2:(tb__ "0|2|
S12VTR;S43S2bVJGv;S59S5fA2S5dR1A4VFAM;S30S0S1S11S1S3S1S10S10A2A1M0S2eA2M1A2S1S2cS10A2S0S11G1S5dS0G0S2eS59S5fA4A4S0S2cS10Z37S58A4A4R1A2A1A2Frho;").
Proof using CFREE FREE REENTER.
  intros rho. apply (TR_pre (SPJ segs (JGv tv_ok am0) E_FAR (rho_sub rho (infer_sub NF X_far0 E_FAR)))); [|apply (E_FAR_free rho); cbn; lia].
  intros w Hw. apply (SPJ_entails_JGA segs C_P NF Kc rho0 (P0_fz FB) FB ML X_far0 E_FAR _ tv_ok tv_ok am0 am0 rho w);
    [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true) | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  eapply (SPJ_head0 segs C_P NF Kc rho0 (P0_fz FB) FB). exact Hw.
Qed.

Lemma X_far1_ok : ltac2:(tb__ "0|2|
S12VTR;S43S2bVJGv;S59S5aA2S64R1A4VFAM;S30S0S1S11S1S3S1S10S10A2A1M0S2eA2M1A2S1S2cS10A2S0S11G1S64S0G0S2eS59S5aA4A4S0S2cS10Z1eS58A4A4R1A2A1A2Frho;").
Proof using CFREE FREE REENTER.
  intros rho. apply (TR_pre (SPJ segs (JGv tv_ok am0) E_FAR (rho_sub rho s_far1))); [|apply (E_FAR_free rho); cbn; lia].
  intros w Hw. apply (SPJ_entails_JGA segs C_P NF Kc rho0 (P0_fz FB) FB ML X_far1 E_FAR s_far1 tv_ok tv_ok am0 am0 rho w);
    [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true) | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  eapply (SPJ_head0 segs C_P NF Kc rho0 (P0_fz FB) FB). exact Hw.
Qed.

Lemma X_ret_ok : ltac2:(tb__ "0|0|
S12S2cVTR;S43S2bVJGv;S5bS65A2S74R2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_pre.
  intros rho b. apply (TR_pre (SPJ segs (JG segs C_P NF Kc rho0 (P0_fz FB) FB []) L_ret (rho_sub rho s_ret))); [|apply POST].
  intros w Hw. apply (SPJ_JGA_JG tv00 am0).
  apply (SPJ_entails_JGA segs C_P NF Kc rho0 (P0_fz FB) FB ML X_ret2 L_ret s_ret tv00 tv00 am0 am0 rho w);
    [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true) | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  apply (SPJ_unbase segs _ rho X_ret1 1 (-400) X_ret2 w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ ret_xforms rho X_ret X_ret1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma X_rete_ok : ltac2:(tb__ "0|0|
S12S2cVTR;S43S2bVJGv;S5bS2fA2S75R2A4VFAM;R1A1A2Fb;Frho;").
Proof using ML POST TR_pre.
  intros rho b. apply (TR_pre (SPJ segs (JG segs C_P NF Kc rho0 (P0_fz FB) FB []) L_ret (rho_sub rho s_rete))); [|apply POST].
  intros w Hw. apply (SPJ_JGA_JG tv00 ANone).
  apply (SPJ_entails_JGA segs C_P NF Kc rho0 (P0_fz FB) FB ML X_rete2 L_ret s_rete tv00 tv00 ANone ANone rho w);
    [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true) | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  apply (SPJ_unbase segs _ rho X_rete1 1 (-400) X_rete2 w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ ret_xforms rho X_rete X_rete1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma exits_okT : ltac2:(tb__ "0|4|
S11S3S1S10S10A2A1M0S2eS1S2cS10A2M1S12SacS1S1S11S1G0S2eA2M2A2M3G1A2S0G3G1S0S11G2R5S0G0S2eR4R3A4A4R2A4S77A3VTR;S43S2bVJGv;R5R4A2R6R2A4VFAM;S30S0G3G1S0S11G2R6S0G0S2eR5R4A4A4R3A4R2A2A1A2F_;Frho;FrvX;FamX;FtvX;FX;").
Proof using CALLLO CFREE ENTAS FREE POST REENTER.
  intros X tvX amX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; injection H as <- <- <- <-.
  - apply X_ms_ok.
  - apply E_lo_ok.
  - apply X_rete_ok.
  - apply X_P0_ok.
  - apply X_far0_ok.
  - apply E_fd_ok.
  - apply X_P_ok.
  - apply X_far1_ok.
  - apply X_ret_ok.
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ltac2:(tb__ "0|0|
S55S2bVok;VKc;A3").
Hypothesis MC : ltac2:(tb__ "0|0|
Sc2S2bS41S4fA3").
Hypothesis LOAD : load_obj_stmt.

Theorem fuzz_one_triple : ltac2:(tb__ "0|0|
S91S2bVok;S43S2bSc8S2bS41VKc;S4aVFB;A1VFB;S4S1S10S10A2A1A6S6bVrho0;A4VQ;A4").
Proof using HS LOAD MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGAE segs C_P NF Kc rho0 (P0_fz FB) FB ML FUEL_fz cutpcs_fz NF cutsE exitsE ok Q (proj1 HS)
                (ejcertA_jcertA segs NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map (nodeA segs C_P NF Kc rho0 (P0_fz FB) FB) (map (@adrop) cutsE)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                (triple_pureh segs ok)
                (call_soundP segs ok)).
       - intros Ai rho1. apply (mc_free _ _ _ MC). exact HS.
       - intros FBc rho1. apply (LOAD ok Kc FBc rho1 HS).
       - intros T tv am rv rho b Hin _. exact (reenter_cutGAE segs C_P NF Kc rho0 (P0_fz FB) FB ok cutsE T tv am rv Q rho Hin).
       - intros rho b. apply (exit_postG segs C_P NF Kc (P0_fz FB) FB ok rho0 [] (Posts_fuzz segs C_P FZ_P Kc FB) L_ret). cbn. left. reflexivity. }
  intros w Hw. destruct (JG_pre_intro segs C_P NF Kc (P0_fz FB) FB rho0 [] Pre_fz w Hw) as [Hs HJ]. split; [exact Hs|]. apply (proj2 (JGA_none segs C_P NF Kc rho0 (P0_fz FB) FB [] _ _ _)). exact HJ.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
Sc3S2bS41S4fA3").
Hypothesis LOADX : load_obj_ex_stmt.

Theorem fuzz_one_etriple : ltac2:(tb__ "0|0|
S90S2bS43S2bSc8S2bS41VKc;S4aVFB;A1VFB;S4S1S10S10A2A1A6S6bVrho0;A4VQ;A3").
Proof using Hvi LOADX MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JGA segs C_P NF Kc rho0 (P0_fz FB) FB ML FUEL_fz cutpcs_fz NF cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeA segs C_P NF Kc rho0 (P0_fz FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                (etriple_pureh segs)
                (call_completeP segs)).
       - intros Ai rho1. apply (mcx_free _ _ _ MCX). exact Hvi.
       - intros FBc rho1. apply (LOADX Kc FBc rho1 Hvi).
       - intros T tv am rv rho b Hin Hm. exact (ereenter_cutAE segs C_P NF Kc rho0 (P0_fz FB) FB cutsE T tv am rv Q b rho Hin Hm).
       - intros rho b. apply (eexit_postG segs C_P NF Kc (P0_fz FB) FB rho0 [] (Posts_fuzz segs C_P FZ_P Kc FB) L_ret). cbn. left. reflexivity. }
  intros w Hw. destruct (JG_pre_intro segs C_P NF Kc (P0_fz FB) FB rho0 [] Pre_fz w Hw) as [Hs HJ]. split; [exact Hs|]. apply (proj2 (JGA_none segs C_P NF Kc rho0 (P0_fz FB) FB [] _ _ _)). exact HJ.
Qed.
End Existence.
End Fz.

Theorem fuzz_one_ok : ltac2:(tb__ "0|0|
ScbS2bS41A2Sc2S2bS41S4fA3S7aS4cF_;F_;F_;").
Proof. intros ML MC LOAD ok Kc FBc rho1 HS. exact (fuzz_one_triple Kc FBc rho1 ML ok HS MC LOAD). Qed.
Theorem fuzz_one_ex_ok : ltac2:(tb__ "0|0|
ScbS2bS41A2Sc3S2bS41S4fA3S79S4bF_;F_;F_;").
Proof. intros ML MCX LOADX Kc FBc rho1 Hvi. exact (fuzz_one_etriple Kc FBc rho1 ML Hvi MCX LOADX). Qed.
End Lib_fuzz_one.

Module Lib_fuzz_one_top.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FuzzOneIface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.

Import ListNotations.
Open Scope Z_scope.

Lemma Posts_lo_F : ltac2:(tb__ "0|0|
S3S8dA1S8cOF_;F_;S3S1S2cS2cA2A1S46S3S1S11S93A2A1Se8R2R1A2S6aR2R1A2A3FFB;FKc;").
Proof. reflexivity. Qed.

Lemma load_obj_ok : ltac2:(tb__ "0|0|
Sc2S2bS41S4fA3S7aF_;").
Proof.
  intros MC ok Kc FB rho0 HS. rewrite <- Posts_lo_F.
  exact (Lib_load_obj.load_obj_sum Kc FB rho0 malloc_laws_P ok HS MC P.Lib_load__G1.Lib_load_obj_des.arena_destroy_ok).
Qed.

Lemma load_obj_ex_ok : ltac2:(tb__ "0|0|
Sc3S2bS41S4fA3S79F_;").
Proof.
  intros MCX Kc FB rho0 Hvi. rewrite <- Posts_lo_F.
  exact (Lib_load_obj.load_obj_sum_ex Kc FB rho0 malloc_laws_P Hvi MCX P.Lib_load__G1.Lib_load_obj_des.arena_destroy_ex_ok).
Qed.

Theorem fuzz_one_P : ltac2:(tb__ "0|0|
Sc2S2bS41S4fA3S4cF_;").
Proof. intros MC. exact (P.Lib_fuzz__G1.Lib_fuzz_one.fuzz_one_ok malloc_laws_P MC (load_obj_ok MC)). Qed.

Theorem fuzz_one_ex_P : ltac2:(tb__ "0|0|
Sc3S2bS41S4fA3S4bF_;").
Proof. intros MCX. exact (P.Lib_fuzz__G1.Lib_fuzz_one.fuzz_one_ex_ok malloc_laws_P MCX (load_obj_ex_ok MCX)). Qed.
End Lib_fuzz_one_top.
