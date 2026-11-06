(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "prod"; "nat"; "nil"; "list"; "app"; "bool"; "true"; "fst"; "option"; "None"; "false"; "Some"; "snd"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "SLit"; "sprop"; "cell"; "SPUle"; "SVar"; "valuation"; "sobj"; "ss_next"; "DUnknown"; "SAlu"; "mkObj"; "SPAlign"; "ss_facts"; "FcsrFrm0"; "holds"; "mkSS"; "smatch"; "ss_pc"; "SMd"; "SPBranch"; "ss_regs"; "ss_objs"; "mkCell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "callee_saved"; "post_regs"; "pre_reg"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "topL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "eq_refl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XRebase"; "XMerge"; "XSelect"; "XSplit"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push1"; "c8"; "tvB"; "pC"; "P0_op"; "pK"; "pD"; "vVALS"; "z0"; "CM"; "HS"; "PD_vr"; "kb4"; "vDEF"; "P_ret"; "VB"; "tvP"; "vAL"; "vV"; "E_vr2d"; "E_vr2v"; "E_vrL"; "Pre_op"; "hx"; "op_facts"; "tv0"; "vec_facts"; "FUEL_op"; "O_D"; "O_F"; "O_al"; "O_dat"; "O_deflt"; "O_vals"; "O_vec4"; "TA_2"; "cutpcs_op"; "cutsE"; "exitsE"; "objs_of"; "op_J2"; "op_L"; "optS"; "ra2"; "raL"; "vPRES"; "vVIDX"; "C_J2"; "C_L"; "E_vrL2"; "F_saved"; "HNEXT"; "TA_L"; "TF_2"; "TF_L"; "body_regs"; "op_entry"; "op_ret"; "op_xregs"; "run_of"; "s_L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push3w"; "c8"; "tvB"; "pC"; "P0_op"; "pK"; "pD"; "vVALS"; "z0"; "CM"; "HS"; "PD_vr"; "kb4"; "P_ret"; "VB"; "tvP"; "vAL"; "vDEF"; "vV"; "E_vr2d"; "E_vr2v"; "E_vrL"; "Pre_op"; "hx"; "op_facts"; "tv0"; "vec_facts"; "FUEL_op"; "O_D"; "O_F"; "O_al"; "O_dat"; "O_vals"; "O_vec4"; "TA_2"; "cutpcs_op"; "cutsE"; "exitsE"; "objs_of"; "op_J2"; "op_L"; "optS"; "ra2"; "raL"; "vPRES"; "vVIDX"; "C_J2"; "C_L"; "E_vrL2"; "F_saved"; "HNEXT"; "TA_L"; "TF_2"; "TF_L"; "body_regs"; "op_entry"; "op_ret"; "op_xregs"; "run_of"; "s_L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "agree_vals"; "import_sub"; "J_ofP"; "call_checkP"; "call_linkP"; "import_okP"; "import_post"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve"; "Pre_vr"; "P0_vr"; "tv0"; "vDp"; "two47"; "vr_ret"; "spo"; "vD"; "vK"; "P_grown"; "tv_post"; "vC"; "P_fail"; "P_keep"; "vr_entry"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "M_MUL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "JG"; "emeas"; "JG_pre";
"JLG"; "PostsC"; "import_tv"; "pdesc"; "tvz"; "FBx"; "T_afterN"; "T_ok"; "call_checkT"; "client_callT"; "ejcert"; "fbin"; "malloc_contracts"; "malloc_contracts_ex"; "new_objs_tv"; "nodeI"; "robjs_okF"; "tvL_ok"; "tv_below"; "tv_sub_eqb"; "tvd"; "tvin"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "Forall"; "seq"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "mul"; "pow"; "sub"; "add"; "eqb"; "opp"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push1.Sum"; "Posts_op"; "PD_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push3w.Sum"; "Posts_op"; "PD_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "sym_run"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "emeasZ"; "contE_TR"; "contE_check"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "MInvR"; "ok_sideK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "jnode"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "@Stdlib.Bool.Bool"; "Is_true"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_opt_push1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition CM : Z := 1.

Definition op_entry : Z := 0x1bd98.
Definition op_L : Z := 0x1be70.
Definition op_cpL : Z := 0x1bebc.
Definition op_J2 : Z := 0x1bdfc.
Definition op_cp2 : Z := 0x1befc.
Definition op_ret : Z := 0x1be5c.
Definition raL : Z := 0x1be84.  Definition ra2 : Z := 0x1be18.
Definition FUEL_op : nat := 400%nat.

Definition vV : sv := SVar 12. Definition vVIDX : sv := SVar 14. Definition vVALS : sv := SVar 33. Definition vDEF : sv := SVar 34.
Definition vPRES : sv := SVar 35. Definition vAL : sv := SVar 36.
Definition kb4 (k : sv) : sv := SMd M_MUL (SLit 4) k.
Definition c8 (o : Z) (v : sv) : cell := mkCell (SLit o) 8 v.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1cS16PaA1S12N50A1S12Z0A1Vcells;S1aA5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S1cSccN50A1Sc9S12Z0A1S4S14A1S1aA5").
Definition O_vec4 (d c k : sv) : sobj := ltac2:(tb__ "0|1|
S1cS52S12Z0M0A1S12Z20A1S0S14S41G0Vd;A2S0S14S41Z8Vc;A2S0S14S41Z10Vk;A2S0S14S41Z18S12Z4A1A2S4S14A1A3A3A3A3S1aA5").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S1cS51S12Z0M0A1M1S12Z30A1S0S14S41G0S12Z13858A1A2S0S14S41Z8S12Z13864A1A2S0S14S41Z10G1A2S0S14S41Z18S12Z13878A1A2S0S14S41Z20G1A2S0S14S41Z28G1A2S4S14A1A3A3A3A3A3A3S1aA5").
Definition O_vals : sobj := ltac2:(tb__ "0|0|
S1cS47S12Z0A1S12S101Z4S49A2A1S4S14A1S1aA5").
Definition O_deflt : sobj := ltac2:(tb__ "0|0|
S1cS4dS12Z0A1S12S101Z4S49A2A1S4S14A1S1aA5").
Definition O_dat (d k : sv) : sobj := ltac2:(tb__ "0|0|
S1cVd;S12Z0A1S4cVk;A1S4S14A1S1aA5").

Definition vec_facts (d c k : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S0S13S15Vc;Vk;A2S0S13S15S4cVk;A1S12ScaA1M0A2S0S13S15Vk;G0A2S0S13S15Vd;G0A2S0S13S1dVdv;Z4A2S4S13A1A3A3A3A3A3").
Definition op_facts : list sprop := ltac2:(tb__ "0|6|
S6S13S0S13S1dPaM0Z4A2S0S13S25Sd8S12N360A1Sc9A3S0S13S25Sd8Sc9S12S106S102Z2M1Z28A2A1A1A3S0S13S15S16P1eA1M2S1bSd7SccN50A1Sc9A3A2S0S13S15S1bSd7G2S12Z50A1A3S16G0A1M3A2S0S13S15G3S12ScaA1M4A2S0S13S15G2S52A2S0S13S15S52G4A2S0S13S1dPcZ3M5A2S0S13S15G2S51A2S0S13S15S51G4A2S0S13S1dP24G5A2S0S13S15G2S47A2S0S13S15S47G4A2S0S13S1dP21G1A2S0S13S15G2S4dA2S0S13S15S4dG4A2S0S13S1dP22G1A2S0S13S15S6eG4A2S0S13S15S6dS12Z1A1A2S0S13S15S12Z7fff7f800000A1G2A2S0S13S15G2S12Z7fffff800000A1A2S4S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S5aScdSd1ScePfA4A3").
Definition objs_of (d c k : sv) : list sobj := ltac2:(tb__ "0|0|
S0S18S5dS4S14A1A1S0S18S5cS0S18S62Vd;Vc;Vk;A3S0S18S5eS0S18S61S0S18S60S0S18S5fVd;Vk;A2S4S18A1A3A3A3A3A3A3A3").
Definition Pre_op : sstate := ltac2:(tb__ "0|1|
S21S78S2eS32S0S2S3S10A2M0S1S3S10UbS12S49A1A4S4G0A1A3A2S2dS1fSbS10A1S67ScdSd1SceA3S58S2cScA9").
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S10S10A2M0S1S10S10ScdS4cSceA1A4S4G0A1A3").

Definition cutpcs_op : list Z := ltac2:(tb__ "0|0|
S0S2aSd4S0S2aS69S0S2aS68S4S2aA1A3A3A3").
Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
SaS5S10eA1M0A1S5S11A1Lx;S110S29S5bS64VS;S8A5G0SfbS10eS11S10fR1A4Lls;S4S11A1Xax2").
Definition leaves_at (S : sstate) (pc : Z) : list sstate := ltac2:(tb__ "0|1|
S11fS11S5S11A1S121S11A1S11S11cS105S23R1A1Vpc;A2M0A1Ll;S11S120G0A1Lx;S7bVS;A1A6").
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_op end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition show (l : sstate) : ltac2:(tb__ "0|0|
S2S2S2S2S2aS2bA2S5S10A1A2S5S18A1A2S5S13A1A2") := ltac2:(tb__ "0|4|
S1S2S2S2S2aS2bA2M0S5S10A1M1A2M2S5S18A1M3A2S5S13A1S1G2G3S1G0G1S1S2aS2bS23Vl;A1S19Vl;A1A4S26Vl;A1A4S27Vl;A1A4SfcS13U8S1eVl;A1A3A4").

Definition hx (r : nat) : sv := SVar (Pos.of_nat (200 + r)).
Definition op_xregs : list sv := ltac2:(tb__ "0|0|
SfbS3S10S3S7S10L_;S2fR1A1S31R1A1S57R1A1X7x2Lr;SfeU0U20A2A4").
Definition HNEXT : positive := 300.
Definition pD : sv := SVar 280. Definition pC : sv := SVar 281. Definition pK : sv := SVar 282. Definition pI : sv := SVar 283.
Definition F_saved : list cell := ltac2:(tb__ "0|0|
S0S14S41N8S16PbA1A2S0S14S41N10S16P1cA1A2S0S14S41N18S16P1dA1A2S0S14S41N20S16P26A1A2S0S14S41N28S16P27A1A2S0S14S41N30S16P28A1A2S0S14S41N38S16P29A1A2S0S14S41N40S16P2aA1A2S0S14S41N48S16P2bA1A2S0S14S41N50S16P2cA1A2S4S14A1A3A3A3A3A3A3A3A3A3A3").
Definition body_regs (s0 : sv) (s3 : sv) (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|2|
S2eS7aS6S2S3S10A2M0S0G0S1S3S10U1M1S57G1A1A4S0G0S1S3S10U2SccN50A1A4S0G0S1S3S10U8Vs0;A4S0G0S1S3S10U9S52A4S0G0S1S3S10U12S12S49A1A4S0G0S1S3S10U13Vs3;A4S0G0S1S3S10U14S51A4S0G0S1S3S10U15S4dA4S0G0S1S3S10U16S6dA4S0G0S1S3S10U17S6eA4S0G0S1S3S10U18S12S103S103S102Z2Z40A2Z1A2S49A2A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition HS (pc : Z) (s0 s3 : sv) (regs : list (nat * sv)) (d c k : sv) (dv : positive) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S21Vpc;S77Vs0;Vs3;Vregs;A3S2dS1fSbS10A1S0S18S5dS72A1S0S18S5cS0S18S62Vd;Vc;Vk;A3S0S18S5eS0S18S61S0S18S60S0S18S5fVd;Vk;A2S4S18A1A3A3A3A3A3A3A3S6S13Vfacts;S6S13S5aVd;Vc;Vk;Vdv;A4S58A3A3S73ScA9").

Definition C_L : sstate := ltac2:(tb__ "0|1|
S4aS69S12Z1A1S47S0S2S3S10A2M0S1S3S10UbS43A4S4G0A1A3S46S43S45P118S4S13A1A9").

Definition TA_L : sstate := ltac2:(tb__ "0|2|
S4aScbS12Z1A1M0S47S0S2S3S10A2M1S1S3S10U1S12S6cA1A4S0G1S1S3S10UaG0A4S4G1A1A3A3S46S43S45P118S0S13S15S1bSd7S43S12S49A1A3S45A2S4S13A1A3A9").
Definition TF_L : sstate := ltac2:(tb__ "0|1|
S4aScbS12Z1A1S47S0S2S3S10A2M0S1S3S10U1S12S6cA1A4S0G0S1S3S10UaS12Z0A1A4S4G0A1A3A3S46S43S45P118S4S13A1A9").

Definition C_J2 : sstate := ltac2:(tb__ "0|1|
S4aS68S12Z1A1S47S0S2S3S10A2M0S1S3S10UbS43A4S4G0A1A3S46S43S45P118S4S13A1A9").

Definition TA_2 (src : sv) : sstate := ltac2:(tb__ "0|2|
S4aScbS12Z1A1M0Vsrc;S0S2S3S10A2M1S1S3S10U1S12S6bA1A4S0G1S1S3S10UaG0A4S4G1A1A3A3S46S43S45P118S0S13S15S1bSd7S43S12S49A1A3S45A2S4S13A1A3A9").
Definition TF_2 : sstate := ltac2:(tb__ "0|1|
S4aScbS12Z1A1S57U13A1S0S2S3S10A2M0S1S3S10U1S12S6bA1A4S0G0S1S3S10UaS12Z0A1A4S4G0A1A3A3S46S43S45P118S4S13A1A9").

Definition P_ret : sstate := ltac2:(tb__ "0|6|
S21S79S2eS30S2cA1S0S2S3S10A2M0S1S3S10UaS16P8fA1M1A4S4G0A1A3A2S2dS1fSbS10A1S67S16P8cM2A1M3S16P8dA1M4S16P8eA1M5A3S6S13S0S13S15G1S12Z1A1A2S4S13A1A3S6S13S5aG3G4G5G2A4S58A3A3P90ScA9").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S10S10A2M0S1S10S10S16P8cA1S4cS16P8eA1A1A4S4G0A1A3").
Definition tvB : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S10S10A2M0S1S10S10S46S4cS45A1A4S4G0A1A3").

Definition E_vrL : sstate := Eval vm_compute in nth 0 (leaves_at C_L vr_entry) Pre_op.
Definition E_vr2 : list sstate := Eval vm_compute in leaves_at C_J2 vr_entry.
Definition E_vr2v : sstate := Eval vm_compute in nth 0 E_vr2 Pre_op.
Definition E_vr2d : sstate := Eval vm_compute in nth 1 E_vr2 Pre_op.
Definition showr (l : sstate) : ltac2:(tb__ "0|0|
S2S2S2aS5S10A1A2S5S13A1A2") := ltac2:(tb__ "0|1|
S1S2S2aS5S10A1M0A2S5S13A1S1S2aG0S23Vl;A1SfcS10U10S26Vl;A1A3A4SfcS13U4S1eVl;A1A3A4").

Definition VB (c : sv) (ph : sv) : sv := ltac2:(tb__ "0|0|
S1bSd7S24Sd9S12Z20A1S1bSdaS12S104ScaZ1000A2A1Vc;A3A3Vph;A3").
Definition z0 : sv := SLit 0.
Definition cutsE : list edesc := ltac2:(tb__ "0|6|
S0S2S2S11S5S2S10S10A2A1M0A2M1S2S2aS10A2M2A2M3S1G1G2S1S11G0S56S59A4S1S2aS10Z64S48A4A4S0G3S1G1G2S1S11G0S70S42A4S1S2aS10Z32M4S4fS43S12Z14A1A2A4A4S0G3S1G1G2S1S11G0S74S42A4S1S2aS10G4S4fS43S12Z12A1A2A4A4S0G3S1G1G2S1S11G0S76S42A4S1S2aS10Z2dS48A4A4S0G3S1G1G2S1S11G0S6fS42A4S1S2aS10Z28S48A4A4S0G3S1G1G2S1S11G0S63S47A1S42A4S1S2aS10Z1eS48A4M5A4S0G3S1G1G2S1S11G0S63S4dA1S42A4G5A4S0G3S1G1G2S1S11G0S75S42A4G5A4S4G3A1A3A3A3A3A3A3A3A3").
Definition exitsE : list edesc := ltac2:(tb__ "0|5|
S0S2S2S11S5S2S10S10A2A1M0A2M1S2S2aS10A2M2A2M3S1G1G2S1S11G0S55S42A4S1S2aS10Z32S4fS43S12Z13A1A2A4A4S0G3S1G1G2S1S11G0S54S42A4S1S2aS10Z23S48A4M4A4S0G3S1G1G2S1S11G0S53S42A4G4A4S0G3S1G1G2S1S11G0S4eS50A4S1S2aS10Z0S48A4A4S4G3A1A3A3A3A3").

Definition vr_view (E : sstate) : sstate := ltac2:(tb__ "0|2|
S6aS119S6aS40VE;S0S3bS3fU1M0S12N40M1A1A2S4S3bA1A3A2A1G0G1A3A1").
Definition vr_sub (E : sstate) : wsub := ltac2:(tb__ "0|1|
S6S2S2bS10A2M0S0G0S1S2bS10P13S1bSd7Sc9S12Z40A1A3A4S0G0S1S2bS10PfS46A4S0G0S1S2bS10P10S43A4S0G0S1S2bS10P11S45A4S0G0S1S2bS10P12S12Z4A1A4S4G0A1A3A3A3A3A3S117PaVE;Sc6A3A3").
Definition E_vrL1 : sstate := Eval vm_compute in optS (apply_xforms E_vrL [XSplit 1 (SLit (-64))]).
Definition E_vrL2 : sstate := Eval vm_compute in vr_view E_vrL.
Definition E_vr2v1 : sstate := Eval vm_compute in optS (apply_xforms E_vr2v [XSplit 1 (SLit (-64))]).
Definition E_vr2v2 : sstate := Eval vm_compute in vr_view E_vr2v.
Definition E_vr2d1 : sstate := Eval vm_compute in optS (apply_xforms E_vr2d [XSplit 1 (SLit (-64))]).
Definition E_vr2d2 : sstate := Eval vm_compute in vr_view E_vr2d.
Definition s_L : wsub := vr_sub E_vrL2.   Definition R_L : list sobj := Eval vm_compute in optR (entails_fr E_vrL2 Pre_vr s_L).
Definition s_2v : wsub := vr_sub E_vr2v2. Definition R_2v : list sobj := Eval vm_compute in optR (entails_fr E_vr2v2 Pre_vr s_2v).
Definition s_2d : wsub := vr_sub E_vr2d2. Definition R_2d : list sobj := Eval vm_compute in optR (entails_fr E_vr2d2 Pre_vr s_2d).
Definition PD_vr : list pdesc := ltac2:(tb__ "0|2|
S0S2S11S5S2S10S10A2A1M0A2M1S1S11G0Sd3Sc8A4S0G1S1S11G0Sd2Sc8A4S0G1S1S11G0ScfSd0A4S4G1A1A3A3A3").

Definition xs_keep : list xform := ltac2:(tb__ "0|2|
S0S3bS3cU0M0A1S0S3bS3cU1M1A1S0S3bS3eS0S3G1S0S3G0S0S3U2S0S3U3S0S3U4S0S3U5S0S3U6S0S3U7S4S3A1A3A3A3A3A3A3A3A3A1S0S3bS3dG0A1S4S3bA1A3A3A3A3").
Definition xs_grown : list xform := ltac2:(tb__ "0|2|
S0S3bS3cU0M0A1S0S3bS3cU2M1A1S0S3bS3eS0S3G0S0S3G1S0S3U1S0S3U3S0S3U4S0S3U5S0S3U6S0S3U7S4S3A1A3A3A3A3A3A3A3A3A1S0S3bS3dG0A1S4S3bA1A3A3A3A3").
Definition tvG : list (sv * sv) := ltac2:(tb__ "0|0|
Se5SbfS7cS2cScfS19S71A1A4Sd0A2").

Goal call_checkP E_vrL2 Pre_vr s_L R_L [P_keep; P_fail; P_grown] = true /\ length R_L = 3%nat
     /\ call_checkP E_vr2v2 Pre_vr s_2v R_2v [P_keep; P_fail; P_grown] = true /\ call_checkP E_vr2d2 Pre_vr s_2d R_2d [P_keep; P_fail; P_grown] = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition P0_op (FB : list (Z * Z)) (r : valuation) : Prop := True.

Lemma P0_vr_of_tvz : ltac2:(tb__ "0|3|
S17S2bS2bS2aS5S18A1SdfSddS37S10SdeR1P11A2S16R5A1A3S37S10SdeR2PfA2S16R7A1M0A3Se7R9S0S2S10S10A2M1S1S10S10S16R8A1M2S24Sd9S12R6A1G0A3A4S4G1A1A3A2S20RaS15G2S12ScaA1A2A2S38SffZ1R8A2SffR8Z1000A2A2Sc7SdcSdbRcR8R7A3R6A2A1F_;F_;F_;F_;F_;Fs;Fms;FR;Fe;Fk;Fd;Frho;").
Proof.
  intros rho d k e R ms s H17 H15 HZ Hf He. unfold P0_vr. rewrite !rw_call', H17, H15. cbn [eval].
  intros Hk Hd. apply Hk. inversion HZ as [|t l Ht X]; subst. unfold tnz, tvv in Ht. cbn [fst snd] in Ht.
  specialize (Ht ltac:(intros Y; exact (Y Hd))).
  rewrite U_mul, U_lit in Ht. cbn [eval] in Ht. cbn [holds] in Hf. rewrite U_lit in Hf. cbn [eval] in Hf. unfold M64v, two47 in *.
  pose proof (bv_urange (rw rho k)) as Rk.
  rewrite (Z.mod_small e) in Ht by lia. rewrite (Z.mod_small (2 ^ 47)) in Hf by lia.
  rewrite Z.mod_small in Ht by nia. nia.
Qed.

Section Sum.
Variable Kc : ltac2:(tb__ "0|0|
S5Sd6A1Sd5OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs C_P.

Definition Posts_op : list (sstate * jpost) := ltac2:(tb__ "0|1|
S0S2S11SbcA2M0S1S11SbcS4eSe3S29S33VKc;S44VFB;A1VFB;S50A6A4S4G0A1A3").
Definition PD_op : list pdesc := ltac2:(tb__ "0|2|
S0S2S11S5S2S10S10A2A1M0A2M1S1S11G0S4eS50A4S4G1A1A3").
Lemma Posts_op_PD : ltac2:(tb__ "0|0|
S37S5S2S11SbcA2A1S109Se4S29S33VKc;S44S10aVFB;A6A3").
Proof using . reflexivity. Qed.

Let nI : ltac2:(tb__ "0|0|
S2S11S5S2S10S10A2A1A2S118Fn;") := ltac2:(tb__ "0|0|
Sf2S29S33S2cVKc;Vrho0;S44VFB;A1VFB;A7").
Let JGv (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
Se0S29S33S2cVKc;Vrho0;S44VFB;A1VFB;Vtv;A8").
Let Q : assn := ltac2:(tb__ "0|0|
SbdS29S2cVrho0;S109A4").

Lemma ejcert_ok : ltac2:(tb__ "0|0|
S37S7SedS29S2cS5bS64P64S65S66A7S8A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S36S11S17Sb8SfdS13S20R2A1S1eR3A1A3VTR;S35S29R5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sb8Sb8Sb8Sb9R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OSb8Sb8R3VTR;R3R2A2F_;VTR;Sb9S38R5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S36S36S11S11SddS5S18A1M0S5S2S11SbcA2M1A1Sb8S17S37SaG0A1S10dR7R6R5A3SdG0R4A2A3S37S7Sc1R8R7R6R5SfbG1S11S9S11SbcA2R4A4A5S8A3S17VTR;S35S29RbR9R1A4SbdS29S19R9A1R1R6A4A2Frho1;S5Sd6A1M2SdfSd5S22S29R7RdS1G2S107R3S108R2R1A2A4A4R10R8R4R2A3R10SdcSdbR9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S11SbcG2SdfSd5S17G2SdfSd5Sf9G1S1S11SbcR9R8A4R10A3S22S29RfR15S1G2S107R8S108R7R6A2A4A4R18R10R9R7A3SbeS19R16A1SdcSdbR11R14R9A3R15A2R7A3S22S29R8RdS1G2S107R7S108R6R5A2A4A4RdSdcSdbR13R16RbA3R17A2R9R8R6A4S38Sc3R14RcR17R18R19RfRaA7S17Sc2R15RdR18R19R1aR1bR10R1RbA9VTR;S35S29Sc0R10SdcSdbR16R19ReA3R1aA2RcA3Sc4R1aS19R1bA1R11S19R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S35S29ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CVR : ltac2:(tb__ "0|1|
S5S2S2aS2aA2A1M0S17VTR;S35S29Se2S29S33VKc;Sc7R2Sc8A6Sc6R1A4SbdS29S2cR1Se4S29S33VKc;G0Sc7L_;S4bR2A6A4A2Frho1;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S11S5S2S10S10A2A1M0S2S2aS10A2M1S17S2aSf9S2S2S11G0A2M2G1A2S1G2G1S1S11G0R5R4A4R3A4S65A3S38SffZ0Se1S1G2G1S1S11G0R6R5A4R4A4R3A2M3A2S100G3R2A2A2VTR;S35S29VJGv;R6A1R7R4A4VFAM;R3A1A2F_;F_;Fb;Frho;Frv;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S11S5S2S10S10A2A1S17S2aSf9S2S11SbcA2S1S11SbcR4Se3S29S33VKc;S44VFB;A1VFB;R3A6A4S109A3VTR;S35S29VJGv;R4A1R5R3A4VFAM;R2A1A2F_;Fb;Frho;Ftv;FP;").

Let CLIENT : ltac2:(tb__ "0|8|
S11SddS5S18A1M0S17S5S2S10S10A2M1A1M2G2Sb8S37SaG0A1S10dR7Sc6R6A3SdG0R5A2A3S37S7SebS33S2cR8Sc6R7R6SfbS2S11G2A2M3S11S9S11G2A2S4bA4A7S8A3S37S7Sc5R8S2cA2S8A3S37S7S11dS2cS19RaA1A2S8A3S37S7Sf5S19RbA1S6G1R7R6A3A2S8A3S37S7Sf6RbR7Sc8A3S8A3S37S7SfaG3G3SfSf4S2cRdS19ReA1S9S11G2R1A3M4SeS11G2R1A3M5A5Sf1Sc6G4G5A3A2Ld;S4bA3S8A3S11aSdfSfdS13S20RdA1S1eR10A1A3S44VFB;Vrho0;A2SbeS2cVrho0;RfA3SeeVFB;R5A2Sf8VFB;R6R11S6G1R10RfA3A4Sf7R12S6G1R11R10A3A2Se7R13S6G1R12R11A3A2S39S17S17S39Sd5Sd5S115S29S33RbR2R1A5Lmd;A2LrhoM;A2SeaR15S34S11bRaA1A1A2S38Sf3S29S33Vrho0;VFB;R16R15R17A7S5S2S2aS2aA2A1Sc7L_;Se8VFB;R16R15A3SdcSdbR16R17RaA3R18A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;Se6S17Sf9Se6R2S4bA3SbeS19R12A1RfR2A3VTR;S35S29Se0S29S33S2cVKc;Vrho0;S44VFB;A1M6VFB;S6G1RfSe5SbfR12S2cS9S11G2R4A3M7S19R13A1A4SeS11G2R4A3A2A3A8Se9S2cR13R12R11G7A5R3A4RdA2F_;F_;Frho';Fd;VTR;S35S29Se0S29S33S2cVKc;Vrho0;G6VFB;S6G1RcRbA3A8R10RdA4RaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fpassed;Fkept;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
SecS29S33S2cVKc;Vrho0;S44VFB;A1VFB;VML;S5S2S2aS2aA2A1Sc7L_;Sc6Sc8S4bS2cS3aS2bS19Sc6A1A2VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;VCVR;A14").
Let CONT : ltac2:(tb__ "0|4|
S5S3bA1S3S2aS2bS11S11S5S2S10S10A2M0A1M1G1G1S10S2aS2aS10S17S17Sb8S37S7S113S2cR10RfReRdRcRbRaR9R7R6R5R4AdS8A3S11eG0RaR9A3SbeRfR5R4A3S17S38SffZ0S111RaRbR1A3M2A2S100G2S111R9R8R7A3A2A2VTR;S35S29Se0S29S33S2cVKc;Vrho0;S44VFB;A1M3VFB;RdA8R10R2A4R6A2F_;Frho';VTR;S35S29Se0S29S33S2cVKc;Vrho0;G3VFB;ReA8R10R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;FA;FT;Fn;Fc;Fi;Fxs;") := ltac2:(tb__ "0|0|
S112S29S33S2cVKc;Vrho0;S44VFB;A1VFB;VML;VTR;VTR_pre;VTR_exw;VTR_pureh;Ac").

Lemma X_P_ret : ltac2:(tb__ "0|0|
S17S2aVTR;S35S29VJGv;S50A1S4eR2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_E_vrL : ltac2:(tb__ "0|1|
S17VTR;S35S29VJGv;S42A1S55R1A4VFAM;Se1S1S2S11S5S2S10S10A2A1M0A2S2S2aS10A2S1S11G0S55S42A4S1S2aS10Z32S4fS43S12Z13A1A2A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho; eapply TR_pre.
  2: { change (JGv tvB) with (JGv ([] ++ tvB)).
       apply (CLIENT E_vrL2 s_L R_L rho [] tvB _).
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       -
         intros Ai ms HF X1 X2 X3 X4 X5 HZ X6 HT. split.
         + eapply robjs_checkF_sound with (extra := fun _ => false).
           * exact HF. * exact (TobjJVx.T_ok_T0_NF _ _ _ X2 HT). * constructor. * vm_compute; reflexivity. * intros o a _ X; discriminate X.
         + cbn beta. eapply (P0_vr_of_tvz _ 280 282 4); [reflexivity | reflexivity | exact HZ | | lia].
           eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto.
       -
         intros d rho' Hd Hag; destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app].
         + eapply (CONT xs_keep 0 (-80) (ss_next E_vrL2) _ TA_L _ tvB tvB (VB pC (SLit 18)) 50 50 (VB pC (SLit 19)) rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER TA_L tvB (50, (VB pC (SLit 18))) rho''); [apply (nth_error_In _ 2%nat); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_keep 0 (-80) (ss_next E_vrL2) _ TF_L _ tvB tvB z0 45 50 (VB pC (SLit 19)) rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER TF_L tvB (45, z0) rho''); [apply (nth_error_In _ 3%nat); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_grown 0 (-80) (ss_next E_vrL2) _ TA_L _ tvB tvB (VB pC (SLit 18)) 50 50 (VB pC (SLit 19)) rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER TA_L tvB (50, (VB pC (SLit 18))) rho''); [apply (nth_error_In _ 2%nat); reflexivity | rewrite emeas_emeasZ; exact Hm]. }
  intros w Hw.
  apply (SPJ_unbase segs _ rho E_vrL1 1 (-64) E_vrL2 w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ [XSplit 1 (SLit (-64))] rho E_vrL E_vrL1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma X_E_vr2v : ltac2:(tb__ "0|1|
S17VTR;S35S29VJGv;S42A1S54R1A4VFAM;Se1S1S2S11S5S2S10S10A2A1M0A2S2S2aS10A2S1S11G0S54S42A4S1S2aS10Z23S48A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho; eapply TR_pre.
  2: { change (JGv tvB) with (JGv ([] ++ tvB)).
       apply (CLIENT E_vr2v2 s_2v R_2v rho [] tvB _).
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       -
         intros Ai ms HF X1 X2 X3 X4 X5 HZ X6 HT. split.
         + eapply robjs_checkF_sound with (extra := fun _ => false).
           * exact HF. * exact (TobjJVx.T_ok_T0_NF _ _ _ X2 HT). * constructor. * vm_compute; reflexivity. * intros o a _ X; discriminate X.
         + cbn beta. eapply (P0_vr_of_tvz _ 280 282 4); [reflexivity | reflexivity | exact HZ | | lia].
           eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto.
       -
         intros d rho' Hd Hag; destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app].
         + eapply (CONT xs_keep 0 (-80) (ss_next E_vr2v2) _ (TA_2 vVALS) _ tvB tvB z0 30 35 z0 rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER (TA_2 vVALS) tvB (30, z0) rho''); [apply (nth_error_In _ 5%nat); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_keep 0 (-80) (ss_next E_vr2v2) _ TF_2 _ tvB tvB z0 30 35 z0 rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER TF_2 tvB (30, z0) rho''); [apply (nth_error_In _ 7%nat); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_grown 0 (-80) (ss_next E_vr2v2) _ (TA_2 vVALS) _ tvB tvB z0 30 35 z0 rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER (TA_2 vVALS) tvB (30, z0) rho''); [apply (nth_error_In _ 5%nat); reflexivity | rewrite emeas_emeasZ; exact Hm]. }
  intros w Hw.
  apply (SPJ_unbase segs _ rho E_vr2v1 1 (-64) E_vr2v2 w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ [XSplit 1 (SLit (-64))] rho E_vr2v E_vr2v1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma X_E_vr2d : ltac2:(tb__ "0|1|
S17VTR;S35S29VJGv;S42A1S53R1A4VFAM;Se1S1S2S11S5S2S10S10A2A1M0A2S2S2aS10A2S1S11G0S53S42A4S1S2aS10Z23S48A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho; eapply TR_pre.
  2: { change (JGv tvB) with (JGv ([] ++ tvB)).
       apply (CLIENT E_vr2d2 s_2d R_2d rho [] tvB _).
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       -
         intros Ai ms HF X1 X2 X3 X4 X5 HZ X6 HT. split.
         + eapply robjs_checkF_sound with (extra := fun _ => false).
           * exact HF. * exact (TobjJVx.T_ok_T0_NF _ _ _ X2 HT). * constructor. * vm_compute; reflexivity. * intros o a _ X; discriminate X.
         + cbn beta. eapply (P0_vr_of_tvz _ 280 282 4); [reflexivity | reflexivity | exact HZ | | lia].
           eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto.
       -
         intros d rho' Hd Hag; destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app].
         + eapply (CONT xs_keep 0 (-80) (ss_next E_vr2d2) _ (TA_2 vDEF) _ tvB tvB z0 30 35 z0 rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER (TA_2 vDEF) tvB (30, z0) rho''); [apply (nth_error_In _ 6%nat); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_keep 0 (-80) (ss_next E_vr2d2) _ TF_2 _ tvB tvB z0 30 35 z0 rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER TF_2 tvB (30, z0) rho''); [apply (nth_error_In _ 7%nat); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_grown 0 (-80) (ss_next E_vr2d2) _ (TA_2 vDEF) _ tvB tvB z0 30 35 z0 rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER (TA_2 vDEF) tvB (30, z0) rho''); [apply (nth_error_In _ 6%nat); reflexivity | rewrite emeas_emeasZ; exact Hm]. }
  intros w Hw.
  apply (SPJ_unbase segs _ rho E_vr2d1 1 (-64) E_vr2d2 w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ [XSplit 1 (SLit (-64))] rho E_vr2d E_vr2d1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S11S5S2S10S10A2A1M0S2S2aS10A2M1S17Sf9S2S2S11G0A2M2G1A2S1G2G1S1S11G0R4R3A4R2A4S66A3VTR;S35S29VJGv;R4A1R5R2A4VFAM;Se1S1G2G1S1S11G0R5R4A4R3A4R2A2A1A2F_;Frho;FrvX;FtvX;FX;").
Proof using CLIENT CONT POST REENTER nI.
  intros X tvX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[]]]]]; injection H as <- <- <-.
  - apply X_E_vrL.
  - apply X_E_vr2v.
  - apply X_E_vr2d.
  - apply X_P_ret.
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ltac2:(tb__ "0|0|
S116S29Vok;VKc;A3").
Hypothesis MC : ltac2:(tb__ "0|0|
SefS29S33S114A3").

Theorem opt_push1_sum : ltac2:(tb__ "0|0|
SbbS29Vok;S35S29Se2S29S33VKc;S44VFB;A1VFB;S59A6S56Vrho0;A4SbdS29S2cVrho0;S109A4A4").
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segs C_P NF Kc rho0 (P0_op FB) FB ML FUEL_op cutpcs_op 100 cutsE exitsE ok Q (proj1 HS)
                (ejcert_jcert segs NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nI (map (@edrop) cutsE)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                (triple_pureh segs ok)
                (call_soundP segs ok)).
       - intros FBc rho1. apply (vec_reserve_sum ok Kc FBc rho1 HS ML MC).
       - intros T tv rv rho b Hin _. exact (reenter_cutGE segs C_P NF Kc rho0 (P0_op FB) FB ok cutsE T tv rv Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segs C_P NF Kc (P0_op FB) FB ok rho0 tv Posts_op P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
Sf0S29S33S114A3").

Theorem opt_push1_sum_ex : ltac2:(tb__ "0|0|
SbaS29S35S29Se2S29S33VKc;S44VFB;A1VFB;S59A6S56Vrho0;A4SbdS29S2cVrho0;S109A4A3").
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segs C_P NF Kc rho0 (P0_op FB) FB ML FUEL_op cutpcs_op 100 cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeI segs C_P NF Kc rho0 (P0_op FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                (etriple_pureh segs)
                (call_completeP segs)).
       - intros FBc rho1. apply (vec_reserve_sum_ex Kc FBc rho1 ML Hvi MCX).
       - intros T tv rv rho b Hin Hm. exact (ereenter_cutE segs C_P NF Kc rho0 (P0_op FB) FB cutsE T tv rv Q b rho Hin Hm).
       - intros P tv rho b Hin. apply (eexit_postG segs C_P NF Kc (P0_op FB) FB rho0 tv Posts_op P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_opt_push1.

Module Lib_opt_push3w.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition CM : Z := 3.

Definition op_entry : Z := 0x1bd98.
Definition op_L : Z := 0x1be70.
Definition op_cpL : Z := 0x1bebc.
Definition op_J2 : Z := 0x1bdfc.
Definition op_cp2 : Z := 0x1befc.
Definition op_ret : Z := 0x1be5c.
Definition raL : Z := 0x1be84.  Definition ra2 : Z := 0x1be18.
Definition FUEL_op : nat := 400%nat.

Definition vV : sv := SVar 12. Definition vVIDX : sv := SVar 14. Definition vVALS : sv := SVar 33.
Definition WHITE : Z := 0x10808.
Definition vDEF : sv := SLit WHITE.
Definition vPRES : sv := SVar 35. Definition vAL : sv := SVar 36.
Definition kb4 (k : sv) : sv := SMd M_MUL (SLit 4) k.
Definition c8 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S28S12Vo;A1Z8Vv;A3").
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1cS16PaA1S12N50A1S12Z0A1Vcells;S1aA5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S1cSccN50A1Sc9S12Z0A1S4S14A1S1aA5").
Definition O_vec4 (d c k : sv) : sobj := ltac2:(tb__ "0|1|
S1cS8eS12Z0M0A1S12Z20A1S0S14S7dG0Vd;A2S0S14S7dZ8Vc;A2S0S14S7dZ10Vk;A2S0S14S7dZ18S12Z4A1A2S4S14A1A3A3A3A3S1aA5").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S1cS8cS12Z0M0A1M1S12Z30A1S0S14S7dG0S12Z13858A1A2S0S14S7dZ8S12Z13864A1A2S0S14S7dZ10G1A2S0S14S7dZ18S12Z13878A1A2S0S14S7dZ20G1A2S0S14S7dZ28G1A2S4S14A1A3A3A3A3A3A3S1aA5").
Definition O_vals : sobj := ltac2:(tb__ "0|0|
S1cS83S12Z0A1S12S101Z4S85A2A1S4S14A1S1aA5").
Definition O_deflt : sobj := ltac2:(tb__ "0|0|
S1cS8dS12Z0A1S12S101Z4S85A2A1S4S14A1S1aA5").
Definition O_dat (d k : sv) : sobj := ltac2:(tb__ "0|0|
S1cVd;S12Z0A1S88Vk;A1S4S14A1S1aA5").

Definition vec_facts (d c k : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S0S13S15Vc;Vk;A2S0S13S15S88Vk;A1S12ScaA1M0A2S0S13S15Vk;G0A2S0S13S15Vd;G0A2S0S13S1dVdv;Z4A2S4S13A1A3A3A3A3A3").
Definition op_facts : list sprop := ltac2:(tb__ "0|6|
S6S13S0S13S1dPaM0Z4A2S0S13S25Sd8S12N360A1Sc9A3S0S13S25Sd8Sc9S12S106S102Z2M1Z28A2A1A1A3S0S13S15S16P1eA1M2S1bSd7SccN50A1Sc9A3A2S0S13S15S1bSd7G2S12Z50A1A3S16G0A1M3A2S0S13S15G3S12ScaA1M4A2S0S13S15G2S8eA2S0S13S15S8eG4A2S0S13S1dPcZ3M5A2S0S13S15G2S8cA2S0S13S15S8cG4A2S0S13S1dP24G5A2S0S13S15G2S83A2S0S13S15S83G4A2S0S13S1dP21G1A2S0S13S15Sa9G4A2S0S13S15Sa8S12Z1A1A2S0S13S15S12Z7fff7f800000A1G2A2S0S13S15G2S12Z7fffff800000A1A2S4S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S96ScdSd1ScePfA4A3").
Definition objs_of (d c k : sv) : list sobj := ltac2:(tb__ "0|0|
S0S18S99S4S14A1A1S0S18S98S0S18S9dVd;Vc;Vk;A3S0S18S9aS0S18S9cS0S18S9bVd;Vk;A2S4S18A1A3A3A3A3A3A3").
Definition Pre_op : sstate := ltac2:(tb__ "0|1|
S21Sb3S2eS32S0S2S3S10A2M0S1S3S10UbS12S85A1A4S0G0S1S3S10UeS8dA4S4G0A1A3A3A2S2dS1fSbS10A1Sa2ScdSd1SceA3S94S2cScA9").
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S10S10A2M0S1S10S10ScdS88SceA1A4S4G0A1A3").

Definition cutpcs_op : list Z := ltac2:(tb__ "0|0|
S0S2aSd4S0S2aSa4S0S2aSa3S4S2aA1A3A3A3").
Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
SaS5S10eA1M0A1S5S11A1Lx;S110S29S97S9fVS;S8A5G0SfbS10eS11S10fR1A4Lls;S4S11A1Xax2").
Definition leaves_at (S : sstate) (pc : Z) : list sstate := ltac2:(tb__ "0|1|
S11fS11S5S11A1S121S11A1S11S11cS105S23R1A1Vpc;A2M0A1Ll;S11S120G0A1Lx;Sb6VS;A1A6").
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_op end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition show (l : sstate) : ltac2:(tb__ "0|0|
S2S2S2S2S2aS2bA2S5S10A1A2S5S18A1A2S5S13A1A2") := ltac2:(tb__ "0|4|
S1S2S2S2S2aS2bA2M0S5S10A1M1A2M2S5S18A1M3A2S5S13A1S1G2G3S1G0G1S1S2aS2bS23Vl;A1S19Vl;A1A4S26Vl;A1A4S27Vl;A1A4SfcS13U8S1eVl;A1A3A4").

Definition hx (r : nat) : sv := SVar (Pos.of_nat (200 + r)).
Definition op_xregs : list sv := ltac2:(tb__ "0|0|
SfbS3S10S3S7S10L_;S2fR1A1S31R1A1S93R1A1X7x2Lr;SfeU0U20A2A4").
Definition HNEXT : positive := 300.
Definition pD : sv := SVar 280. Definition pC : sv := SVar 281. Definition pK : sv := SVar 282. Definition pI : sv := SVar 283.
Definition F_saved : list cell := ltac2:(tb__ "0|0|
S0S14S7dN8S16PbA1A2S0S14S7dN10S16P1cA1A2S0S14S7dN18S16P1dA1A2S0S14S7dN20S16P26A1A2S0S14S7dN28S16P27A1A2S0S14S7dN30S16P28A1A2S0S14S7dN38S16P29A1A2S0S14S7dN40S16P2aA1A2S0S14S7dN48S16P2bA1A2S0S14S7dN50S16P2cA1A2S4S14A1A3A3A3A3A3A3A3A3A3A3").
Definition body_regs (s0 : sv) (s3 : sv) (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|2|
S2eSb5S6S2S3S10A2M0S0G0S1S3S10U1M1S93G1A1A4S0G0S1S3S10U2SccN50A1A4S0G0S1S3S10U8Vs0;A4S0G0S1S3S10U9S8eA4S0G0S1S3S10U12S12S85A1A4S0G0S1S3S10U13Vs3;A4S0G0S1S3S10U14S8cA4S0G0S1S3S10U15S8dA4S0G0S1S3S10U16Sa8A4S0G0S1S3S10U17Sa9A4S0G0S1S3S10U18S12S103S103S102Z2Z40A2Z1A2S85A2A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition HS (pc : Z) (s0 s3 : sv) (regs : list (nat * sv)) (d c k : sv) (dv : positive) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S21Vpc;Sb2Vs0;Vs3;Vregs;A3S2dS1fSbS10A1S0S18S99SadA1S0S18S98S0S18S9dVd;Vc;Vk;A3S0S18S9aS0S18S9cS0S18S9bVd;Vk;A2S4S18A1A3A3A3A3A3A3S6S13Vfacts;S6S13S96Vd;Vc;Vk;Vdv;A4S94A3A3SaeScA9").

Definition C_L : sstate := ltac2:(tb__ "0|1|
S86Sa4S12Z1A1S83S0S2S3S10A2M0S1S3S10UbS7fA4S4G0A1A3S82S7fS81P118S4S13A1A9").

Definition TA_L : sstate := ltac2:(tb__ "0|2|
S86ScbS12Z1A1M0S83S0S2S3S10A2M1S1S3S10U1S12Sa7A1A4S0G1S1S3S10UaG0A4S4G1A1A3A3S82S7fS81P118S0S13S15S1bSd7S7fS12S85A1A3S81A2S4S13A1A3A9").
Definition TF_L : sstate := ltac2:(tb__ "0|1|
S86ScbS12Z1A1S83S0S2S3S10A2M0S1S3S10U1S12Sa7A1A4S0G0S1S3S10UaS12Z0A1A4S4G0A1A3A3S82S7fS81P118S4S13A1A9").

Definition C_J2 : sstate := ltac2:(tb__ "0|1|
S86Sa3S12Z1A1S83S0S2S3S10A2M0S1S3S10UbS7fA4S4G0A1A3S82S7fS81P118S4S13A1A9").

Definition TA_2 (src : sv) : sstate := ltac2:(tb__ "0|2|
S86ScbS12Z1A1M0Vsrc;S0S2S3S10A2M1S1S3S10U1S12Sa6A1A4S0G1S1S3S10UaG0A4S4G1A1A3A3S82S7fS81P118S0S13S15S1bSd7S7fS12S85A1A3S81A2S4S13A1A3A9").
Definition TF_2 : sstate := ltac2:(tb__ "0|1|
S86ScbS12Z1A1S93U13A1S0S2S3S10A2M0S1S3S10U1S12Sa6A1A4S0G0S1S3S10UaS12Z0A1A4S4G0A1A3A3S82S7fS81P118S4S13A1A9").

Definition P_ret : sstate := ltac2:(tb__ "0|6|
S21Sb4S2eS30S2cA1S0S2S3S10A2M0S1S3S10UaS16P8fA1M1A4S4G0A1A3A2S2dS1fSbS10A1Sa2S16P8cM2A1M3S16P8dA1M4S16P8eA1M5A3S6S13S0S13S15G1S12Z1A1A2S4S13A1A3S6S13S96G3G4G5G2A4S94A3A3P90ScA9").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S10S10A2M0S1S10S10S16P8cA1S88S16P8eA1A1A4S4G0A1A3").
Definition tvB : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S10S10A2M0S1S10S10S82S88S81A1A4S4G0A1A3").

Definition E_vrL : sstate := Eval vm_compute in nth 0 (leaves_at C_L vr_entry) Pre_op.
Definition E_vr2 : list sstate := Eval vm_compute in leaves_at C_J2 vr_entry.
Definition E_vr2v : sstate := Eval vm_compute in nth 0 E_vr2 Pre_op.
Definition E_vr2d : sstate := Eval vm_compute in nth 1 E_vr2 Pre_op.
Definition showr (l : sstate) : ltac2:(tb__ "0|0|
S2S2S2aS5S10A1A2S5S13A1A2") := ltac2:(tb__ "0|1|
S1S2S2aS5S10A1M0A2S5S13A1S1S2aG0S23Vl;A1SfcS10U10S26Vl;A1A3A4SfcS13U4S1eVl;A1A3A4").

Definition VB (c : sv) (ph : sv) : sv := ltac2:(tb__ "0|0|
S1bSd7S24Sd9S12Z20A1S1bSdaS12S104ScaZ1000A2A1Vc;A3A3Vph;A3").
Definition z0 : sv := SLit 0.
Definition cutsE : list edesc := ltac2:(tb__ "0|6|
S0S2S2S11S5S2S10S10A2A1M0A2M1S2S2aS10A2M2A2M3S1G1G2S1S11G0S92S95A4S1S2aS10Z64S84A4A4S0G3S1G1G2S1S11G0SabS7eA4S1S2aS10Z32M4S8aS7fS12Z14A1A2A4A4S0G3S1G1G2S1S11G0SafS7eA4S1S2aS10G4S8aS7fS12Z12A1A2A4A4S0G3S1G1G2S1S11G0Sb1S7eA4S1S2aS10Z2dS84A4A4S0G3S1G1G2S1S11G0SaaS7eA4S1S2aS10Z28S84A4A4S0G3S1G1G2S1S11G0S9eS83A1S7eA4S1S2aS10Z1eS84A4M5A4S0G3S1G1G2S1S11G0S9eS8dA1S7eA4G5A4S0G3S1G1G2S1S11G0Sb0S7eA4G5A4S4G3A1A3A3A3A3A3A3A3A3").
Definition exitsE : list edesc := ltac2:(tb__ "0|5|
S0S2S2S11S5S2S10S10A2A1M0A2M1S2S2aS10A2M2A2M3S1G1G2S1S11G0S91S7eA4S1S2aS10Z32S8aS7fS12Z13A1A2A4A4S0G3S1G1G2S1S11G0S90S7eA4S1S2aS10Z23S84A4M4A4S0G3S1G1G2S1S11G0S8fS7eA4G4A4S0G3S1G1G2S1S11G0S89S8bA4S1S2aS10Z0S84A4A4S4G3A1A3A3A3A3").

Definition vr_view (E : sstate) : sstate := ltac2:(tb__ "0|2|
Sa5S119Sa5S40VE;S0S3bS3fU1M0S12N40M1A1A2S4S3bA1A3A2A1G0G1A3A1").
Definition vr_sub (E : sstate) : wsub := ltac2:(tb__ "0|1|
S6S2S2bS10A2M0S0G0S1S2bS10P13S1bSd7Sc9S12Z40A1A3A4S0G0S1S2bS10PfS82A4S0G0S1S2bS10P10S7fA4S0G0S1S2bS10P11S81A4S0G0S1S2bS10P12S12Z4A1A4S4G0A1A3A3A3A3A3S117PaVE;Sc6A3A3").
Definition E_vrL1 : sstate := Eval vm_compute in optS (apply_xforms E_vrL [XSplit 1 (SLit (-64))]).
Definition E_vrL2 : sstate := Eval vm_compute in vr_view E_vrL.
Definition E_vr2v1 : sstate := Eval vm_compute in optS (apply_xforms E_vr2v [XSplit 1 (SLit (-64))]).
Definition E_vr2v2 : sstate := Eval vm_compute in vr_view E_vr2v.
Definition E_vr2d1 : sstate := Eval vm_compute in optS (apply_xforms E_vr2d [XSplit 1 (SLit (-64))]).
Definition E_vr2d2 : sstate := Eval vm_compute in vr_view E_vr2d.
Definition s_L : wsub := vr_sub E_vrL2.   Definition R_L : list sobj := Eval vm_compute in optR (entails_fr E_vrL2 Pre_vr s_L).
Definition s_2v : wsub := vr_sub E_vr2v2. Definition R_2v : list sobj := Eval vm_compute in optR (entails_fr E_vr2v2 Pre_vr s_2v).
Definition s_2d : wsub := vr_sub E_vr2d2. Definition R_2d : list sobj := Eval vm_compute in optR (entails_fr E_vr2d2 Pre_vr s_2d).
Definition PD_vr : list pdesc := ltac2:(tb__ "0|2|
S0S2S11S5S2S10S10A2A1M0A2M1S1S11G0Sd3Sc8A4S0G1S1S11G0Sd2Sc8A4S0G1S1S11G0ScfSd0A4S4G1A1A3A3A3").

Definition xs_keep : list xform := ltac2:(tb__ "0|2|
S0S3bS3cU0M0A1S0S3bS3cU1M1A1S0S3bS3eS0S3G1S0S3G0S0S3U2S0S3U3S0S3U4S0S3U5S0S3U6S4S3A1A3A3A3A3A3A3A3A1S0S3bS3dG0A1S4S3bA1A3A3A3A3").
Definition xs_grown : list xform := ltac2:(tb__ "0|2|
S0S3bS3cU0M0A1S0S3bS3cU2M1A1S0S3bS3eS0S3G0S0S3G1S0S3U1S0S3U3S0S3U4S0S3U5S0S3U6S4S3A1A3A3A3A3A3A3A3A1S0S3bS3dG0A1S4S3bA1A3A3A3A3").
Definition tvG : list (sv * sv) := ltac2:(tb__ "0|0|
Se5SbfSb7S2cScfS19SacA1A4Sd0A2").

Goal call_checkP E_vrL2 Pre_vr s_L R_L [P_keep; P_fail; P_grown] = true /\ length R_L = 2%nat
     /\ call_checkP E_vr2v2 Pre_vr s_2v R_2v [P_keep; P_fail; P_grown] = true /\ call_checkP E_vr2d2 Pre_vr s_2d R_2d [P_keep; P_fail; P_grown] = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition P0_op (FB : list (Z * Z)) (r : valuation) : Prop := True.

Lemma P0_vr_of_tvz : ltac2:(tb__ "0|3|
S17S2bS2bS2aS5S18A1SdfSddS37S10SdeR1P11A2S16R5A1A3S37S10SdeR2PfA2S16R7A1M0A3Se7R9S0S2S10S10A2M1S1S10S10S16R8A1M2S24Sd9S12R6A1G0A3A4S4G1A1A3A2S20RaS15G2S12ScaA1A2A2S38SffZ1R8A2SffR8Z1000A2A2Sc7SdcSdbRcR8R7A3R6A2A1F_;F_;F_;F_;F_;Fs;Fms;FR;Fe;Fk;Fd;Frho;").
Proof.
  intros rho d k e R ms s H17 H15 HZ Hf He. unfold P0_vr. rewrite !rw_call', H17, H15. cbn [eval].
  intros Hk Hd. apply Hk. inversion HZ as [|t l Ht X]; subst. unfold tnz, tvv in Ht. cbn [fst snd] in Ht.
  specialize (Ht ltac:(intros Y; exact (Y Hd))).
  rewrite U_mul, U_lit in Ht. cbn [eval] in Ht. cbn [holds] in Hf. rewrite U_lit in Hf. cbn [eval] in Hf. unfold M64v, two47 in *.
  pose proof (bv_urange (rw rho k)) as Rk.
  rewrite (Z.mod_small e) in Ht by lia. rewrite (Z.mod_small (2 ^ 47)) in Hf by lia.
  rewrite Z.mod_small in Ht by nia. nia.
Qed.

Section Sum.
Variable Kc : ltac2:(tb__ "0|0|
S5Sd6A1Sd5OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs C_P.

Definition Posts_op : list (sstate * jpost) := ltac2:(tb__ "0|1|
S0S2S11SbcA2M0S1S11SbcS89Se3S29S33VKc;S80VFB;A1VFB;S8bA6A4S4G0A1A3").
Definition PD_op : list pdesc := ltac2:(tb__ "0|2|
S0S2S11S5S2S10S10A2A1M0A2M1S1S11G0S89S8bA4S4G1A1A3").
Lemma Posts_op_PD : ltac2:(tb__ "0|0|
S37S5S2S11SbcA2A1S10bSe4S29S33VKc;S80S10cVFB;A6A3").
Proof using . reflexivity. Qed.

Let nI : ltac2:(tb__ "0|0|
S2S11S5S2S10S10A2A1A2S118Fn;") := ltac2:(tb__ "0|0|
Sf2S29S33S2cVKc;Vrho0;S80VFB;A1VFB;A7").
Let JGv (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
Se0S29S33S2cVKc;Vrho0;S80VFB;A1VFB;Vtv;A8").
Let Q : assn := ltac2:(tb__ "0|0|
SbdS29S2cVrho0;S10bA4").

Lemma ejcert_ok : ltac2:(tb__ "0|0|
S37S7SedS29S2cS97S9fP64Sa0Sa1A7S8A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S36S11S17Sb8SfdS13S20R2A1S1eR3A1A3VTR;S35S29R5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sb8Sb8Sb8Sb9R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OSb8Sb8R3VTR;R3R2A2F_;VTR;Sb9S38R5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S36S36S11S11SddS5S18A1M0S5S2S11SbcA2M1A1Sb8S17S37SaG0A1S10dR7R6R5A3SdG0R4A2A3S37S7Sc1R8R7R6R5SfbG1S11S9S11SbcA2R4A4A5S8A3S17VTR;S35S29RbR9R1A4SbdS29S19R9A1R1R6A4A2Frho1;S5Sd6A1M2SdfSd5S22S29R7RdS1G2S107R3S108R2R1A2A4A4R10R8R4R2A3R10SdcSdbR9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S11SbcG2SdfSd5S17G2SdfSd5Sf9G1S1S11SbcR9R8A4R10A3S22S29RfR15S1G2S107R8S108R7R6A2A4A4R18R10R9R7A3SbeS19R16A1SdcSdbR11R14R9A3R15A2R7A3S22S29R8RdS1G2S107R7S108R6R5A2A4A4RdSdcSdbR13R16RbA3R17A2R9R8R6A4S38Sc3R14RcR17R18R19RfRaA7S17Sc2R15RdR18R19R1aR1bR10R1RbA9VTR;S35S29Sc0R10SdcSdbR16R19ReA3R1aA2RcA3Sc4R1aS19R1bA1R11S19R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S35S29ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CVR : ltac2:(tb__ "0|1|
S5S2S2aS2aA2A1M0S17VTR;S35S29Se2S29S33VKc;Sc7R2Sc8A6Sc6R1A4SbdS29S2cR1Se4S29S33VKc;G0Sc7L_;S87R2A6A4A2Frho1;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S11S5S2S10S10A2A1M0S2S2aS10A2M1S17S2aSf9S2S2S11G0A2M2G1A2S1G2G1S1S11G0R5R4A4R3A4Sa0A3S38SffZ0Se1S1G2G1S1S11G0R6R5A4R4A4R3A2M3A2S100G3R2A2A2VTR;S35S29VJGv;R6A1R7R4A4VFAM;R3A1A2F_;F_;Fb;Frho;Frv;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S11S5S2S10S10A2A1S17S2aSf9S2S11SbcA2S1S11SbcR4Se3S29S33VKc;S80VFB;A1VFB;R3A6A4S10bA3VTR;S35S29VJGv;R4A1R5R3A4VFAM;R2A1A2F_;Fb;Frho;Ftv;FP;").

Let CLIENT : ltac2:(tb__ "0|8|
S11SddS5S18A1M0S17S5S2S10S10A2M1A1M2G2Sb8S37SaG0A1S10dR7Sc6R6A3SdG0R5A2A3S37S7SebS33S2cR8Sc6R7R6SfbS2S11G2A2M3S11S9S11G2A2S87A4A7S8A3S37S7Sc5R8S2cA2S8A3S37S7S11dS2cS19RaA1A2S8A3S37S7Sf5S19RbA1S6G1R7R6A3A2S8A3S37S7Sf6RbR7Sc8A3S8A3S37S7SfaG3G3SfSf4S2cRdS19ReA1S9S11G2R1A3M4SeS11G2R1A3M5A5Sf1Sc6G4G5A3A2Ld;S87A3S8A3S11aSdfSfdS13S20RdA1S1eR10A1A3S80VFB;Vrho0;A2SbeS2cVrho0;RfA3SeeVFB;R5A2Sf8VFB;R6R11S6G1R10RfA3A4Sf7R12S6G1R11R10A3A2Se7R13S6G1R12R11A3A2S39S17S17S39Sd5Sd5S115S29S33RbR2R1A5Lmd;A2LrhoM;A2SeaR15S34S11bRaA1A1A2S38Sf3S29S33Vrho0;VFB;R16R15R17A7S5S2S2aS2aA2A1Sc7L_;Se8VFB;R16R15A3SdcSdbR16R17RaA3R18A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;Se6S17Sf9Se6R2S87A3SbeS19R12A1RfR2A3VTR;S35S29Se0S29S33S2cVKc;Vrho0;S80VFB;A1M6VFB;S6G1RfSe5SbfR12S2cS9S11G2R4A3M7S19R13A1A4SeS11G2R4A3A2A3A8Se9S2cR13R12R11G7A5R3A4RdA2F_;F_;Frho';Fd;VTR;S35S29Se0S29S33S2cVKc;Vrho0;G6VFB;S6G1RcRbA3A8R10RdA4RaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fpassed;Fkept;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
SecS29S33S2cVKc;Vrho0;S80VFB;A1VFB;VML;S5S2S2aS2aA2A1Sc7L_;Sc6Sc8S87S2cS3aS2bS19Sc6A1A2VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;VCVR;A14").
Let CONT : ltac2:(tb__ "0|4|
S5S3bA1S3S2aS2bS11S11S5S2S10S10A2M0A1M1G1G1S10S2aS2aS10S17S17Sb8S37S7S113S2cR10RfReRdRcRbRaR9R7R6R5R4AdS8A3S11eG0RaR9A3SbeRfR5R4A3S17S38SffZ0S111RaRbR1A3M2A2S100G2S111R9R8R7A3A2A2VTR;S35S29Se0S29S33S2cVKc;Vrho0;S80VFB;A1M3VFB;RdA8R10R2A4R6A2F_;Frho';VTR;S35S29Se0S29S33S2cVKc;Vrho0;G3VFB;ReA8R10R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;FA;FT;Fn;Fc;Fi;Fxs;") := ltac2:(tb__ "0|0|
S112S29S33S2cVKc;Vrho0;S80VFB;A1VFB;VML;VTR;VTR_pre;VTR_exw;VTR_pureh;Ac").

Lemma X_P_ret : ltac2:(tb__ "0|0|
S17S2aVTR;S35S29VJGv;S8bA1S89R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_E_vrL : ltac2:(tb__ "0|1|
S17VTR;S35S29VJGv;S7eA1S91R1A4VFAM;Se1S1S2S11S5S2S10S10A2A1M0A2S2S2aS10A2S1S11G0S91S7eA4S1S2aS10Z32S8aS7fS12Z13A1A2A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho; eapply TR_pre.
  2: { change (JGv tvB) with (JGv ([] ++ tvB)).
       apply (CLIENT E_vrL2 s_L R_L rho [] tvB _).
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       -
         intros Ai ms HF X1 X2 X3 X4 X5 HZ X6 HT. split.
         + eapply robjs_checkF_sound with (extra := fun _ => false).
           * exact HF. * exact (TobjJVx.T_ok_T0_NF _ _ _ X2 HT). * constructor. * vm_compute; reflexivity. * intros o a _ X; discriminate X.
         + cbn beta. eapply (P0_vr_of_tvz _ 280 282 4); [reflexivity | reflexivity | exact HZ | | lia].
           eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto.
       -
         intros d rho' Hd Hag; destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app].
         + eapply (CONT xs_keep 0 (-80) (ss_next E_vrL2) _ TA_L _ tvB tvB (VB pC (SLit 18)) 50 50 (VB pC (SLit 19)) rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER TA_L tvB (50, (VB pC (SLit 18))) rho''); [apply (nth_error_In _ 2%nat); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_keep 0 (-80) (ss_next E_vrL2) _ TF_L _ tvB tvB z0 45 50 (VB pC (SLit 19)) rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER TF_L tvB (45, z0) rho''); [apply (nth_error_In _ 3%nat); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_grown 0 (-80) (ss_next E_vrL2) _ TA_L _ tvB tvB (VB pC (SLit 18)) 50 50 (VB pC (SLit 19)) rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER TA_L tvB (50, (VB pC (SLit 18))) rho''); [apply (nth_error_In _ 2%nat); reflexivity | rewrite emeas_emeasZ; exact Hm]. }
  intros w Hw.
  apply (SPJ_unbase segs _ rho E_vrL1 1 (-64) E_vrL2 w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ [XSplit 1 (SLit (-64))] rho E_vrL E_vrL1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma X_E_vr2v : ltac2:(tb__ "0|1|
S17VTR;S35S29VJGv;S7eA1S90R1A4VFAM;Se1S1S2S11S5S2S10S10A2A1M0A2S2S2aS10A2S1S11G0S90S7eA4S1S2aS10Z23S84A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho; eapply TR_pre.
  2: { change (JGv tvB) with (JGv ([] ++ tvB)).
       apply (CLIENT E_vr2v2 s_2v R_2v rho [] tvB _).
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       -
         intros Ai ms HF X1 X2 X3 X4 X5 HZ X6 HT. split.
         + eapply robjs_checkF_sound with (extra := fun _ => false).
           * exact HF. * exact (TobjJVx.T_ok_T0_NF _ _ _ X2 HT). * constructor. * vm_compute; reflexivity. * intros o a _ X; discriminate X.
         + cbn beta. eapply (P0_vr_of_tvz _ 280 282 4); [reflexivity | reflexivity | exact HZ | | lia].
           eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto.
       -
         intros d rho' Hd Hag; destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app].
         + eapply (CONT xs_keep 0 (-80) (ss_next E_vr2v2) _ (TA_2 vVALS) _ tvB tvB z0 30 35 z0 rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER (TA_2 vVALS) tvB (30, z0) rho''); [apply (nth_error_In _ 5%nat); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_keep 0 (-80) (ss_next E_vr2v2) _ TF_2 _ tvB tvB z0 30 35 z0 rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER TF_2 tvB (30, z0) rho''); [apply (nth_error_In _ 7%nat); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_grown 0 (-80) (ss_next E_vr2v2) _ (TA_2 vVALS) _ tvB tvB z0 30 35 z0 rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER (TA_2 vVALS) tvB (30, z0) rho''); [apply (nth_error_In _ 5%nat); reflexivity | rewrite emeas_emeasZ; exact Hm]. }
  intros w Hw.
  apply (SPJ_unbase segs _ rho E_vr2v1 1 (-64) E_vr2v2 w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ [XSplit 1 (SLit (-64))] rho E_vr2v E_vr2v1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma X_E_vr2d : ltac2:(tb__ "0|1|
S17VTR;S35S29VJGv;S7eA1S8fR1A4VFAM;Se1S1S2S11S5S2S10S10A2A1M0A2S2S2aS10A2S1S11G0S8fS7eA4S1S2aS10Z23S84A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho; eapply TR_pre.
  2: { change (JGv tvB) with (JGv ([] ++ tvB)).
       apply (CLIENT E_vr2d2 s_2d R_2d rho [] tvB _).
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       -
         intros Ai ms HF X1 X2 X3 X4 X5 HZ X6 HT. split.
         + eapply robjs_checkF_sound with (extra := fun _ => false).
           * exact HF. * exact (TobjJVx.T_ok_T0_NF _ _ _ X2 HT). * constructor. * vm_compute; reflexivity. * intros o a _ X; discriminate X.
         + cbn beta. eapply (P0_vr_of_tvz _ 280 282 4); [reflexivity | reflexivity | exact HZ | | lia].
           eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto.
       -
         intros d rho' Hd Hag; destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app].
         + eapply (CONT xs_keep 0 (-80) (ss_next E_vr2d2) _ (TA_2 vDEF) _ tvB tvB z0 30 35 z0 rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER (TA_2 vDEF) tvB (30, z0) rho''); [apply (nth_error_In _ 6%nat); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_keep 0 (-80) (ss_next E_vr2d2) _ TF_2 _ tvB tvB z0 30 35 z0 rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER TF_2 tvB (30, z0) rho''); [apply (nth_error_In _ 7%nat); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_grown 0 (-80) (ss_next E_vr2d2) _ (TA_2 vDEF) _ tvB tvB z0 30 35 z0 rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER (TA_2 vDEF) tvB (30, z0) rho''); [apply (nth_error_In _ 6%nat); reflexivity | rewrite emeas_emeasZ; exact Hm]. }
  intros w Hw.
  apply (SPJ_unbase segs _ rho E_vr2d1 1 (-64) E_vr2d2 w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ [XSplit 1 (SLit (-64))] rho E_vr2d E_vr2d1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S11S5S2S10S10A2A1M0S2S2aS10A2M1S17Sf9S2S2S11G0A2M2G1A2S1G2G1S1S11G0R4R3A4R2A4Sa1A3VTR;S35S29VJGv;R4A1R5R2A4VFAM;Se1S1G2G1S1S11G0R5R4A4R3A4R2A2A1A2F_;Frho;FrvX;FtvX;FX;").
Proof using CLIENT CONT POST REENTER nI.
  intros X tvX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[]]]]]; injection H as <- <- <-.
  - apply X_E_vrL.
  - apply X_E_vr2v.
  - apply X_E_vr2d.
  - apply X_P_ret.
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ltac2:(tb__ "0|0|
S116S29Vok;VKc;A3").
Hypothesis MC : ltac2:(tb__ "0|0|
SefS29S33S114A3").

Theorem opt_push3_sum : ltac2:(tb__ "0|0|
SbbS29Vok;S35S29Se2S29S33VKc;S80VFB;A1VFB;S95A6S92Vrho0;A4SbdS29S2cVrho0;S10bA4A4").
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segs C_P NF Kc rho0 (P0_op FB) FB ML FUEL_op cutpcs_op 100 cutsE exitsE ok Q (proj1 HS)
                (ejcert_jcert segs NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nI (map (@edrop) cutsE)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                (triple_pureh segs ok)
                (call_soundP segs ok)).
       - intros FBc rho1. apply (vec_reserve_sum ok Kc FBc rho1 HS ML MC).
       - intros T tv rv rho b Hin _. exact (reenter_cutGE segs C_P NF Kc rho0 (P0_op FB) FB ok cutsE T tv rv Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segs C_P NF Kc (P0_op FB) FB ok rho0 tv Posts_op P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
Sf0S29S33S114A3").

Theorem opt_push3_sum_ex : ltac2:(tb__ "0|0|
SbaS29S35S29Se2S29S33VKc;S80VFB;A1VFB;S95A6S92Vrho0;A4SbdS29S2cVrho0;S10bA4A3").
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segs C_P NF Kc rho0 (P0_op FB) FB ML FUEL_op cutpcs_op 100 cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeI segs C_P NF Kc rho0 (P0_op FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                (etriple_pureh segs)
                (call_completeP segs)).
       - intros FBc rho1. apply (vec_reserve_sum_ex Kc FBc rho1 ML Hvi MCX).
       - intros T tv rv rho b Hin Hm. exact (ereenter_cutE segs C_P NF Kc rho0 (P0_op FB) FB cutsE T tv rv Q b rho Hin Hm).
       - intros P tv rho b Hin. apply (eexit_postG segs C_P NF Kc (P0_op FB) FB rho0 tv Posts_op P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_opt_push3w.
