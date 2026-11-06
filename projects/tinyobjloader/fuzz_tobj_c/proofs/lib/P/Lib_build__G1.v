(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "prod"; "nat"; "nil"; "list"; "app"; "bool"; "true"; "fst"; "false"; "option"; "None"; "snd"; "Some"; "andb"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "sprop"; "SLit"; "valuation"; "SPUle"; "cell"; "SVar"; "sobj"; "ss_next"; "SAlu"; "mkObj"; "DUnknown"; "holds"; "smatch"; "ss_facts"; "FcsrFrm0"; "mkSS"; "SPAlign"; "SPBranch"; "sv_eqb"; "SMd"; "ob_base"; "ob_hi"; "ob_lo"; "rw"; "ss_pc"; "tfact"; "DArr"; "SPUlt"; "TF2le"; "ob_cells"; "obj_range"; "ss_objs"; "ss_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "callee_saved"; "pre_reg"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "topL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "eq_refl"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index"; "P0_bli"; "c8"; "pJ"; "vLEN"; "pC"; "tvB"; "pK"; "pD"; "VL"; "ij_facts"; "tv0"; "tvP"; "Posts_bli_darr"; "kb16"; "ra_vr"; "vAL"; "vV"; "z0"; "FR"; "PD_vr"; "Pre_bli0"; "bli_facts"; "pI"; "vBUF"; "vec_facts"; "HS"; "P_ret"; "P_ret_darr"; "Pre_bli"; "hx"; "E_vr"; "FUEL_bli"; "bli_LI"; "cutpcs_bli"; "objs_of"; "F_saved"; "HNEXT"; "O_D"; "O_F"; "O_al"; "O_txt"; "O_vec16"; "bli_ret"; "body_regs"; "cutsE"; "exitsE"; "objs_of_darr"; "C_LI"; "E_vr2"; "K_fail"; "K_ok"; "O_dat"; "O_dat_darr"; "PD_bli_darr"; "bli_entry"; "bli_xregs"; "is_txt"; "lines_tmpl"; "run_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "agree_vals"; "J_ofP"; "call_checkP"; "call_linkP"; "import_okP"; "import_post"; "import_sub"; "wsub_dom_below"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XRebase"; "XMerge"; "XSelect"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "BC_LTU"; "M_MUL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "JG"; "JG_pre"; "emeas"; "JLG"; "PostsC"; "pdesc"; "FBx"; "malloc_contracts"; "malloc_contracts_ex"; "tvz"; "T_afterN"; "T_ok"; "call_checkT"; "client_callT"; "ejcert"; "fbin"; "import_tv"; "malloc_laws"; "new_objs_tv"; "nodeI"; "robjs_okF"; "tvL_ok"; "tv_below"; "tv_sub_eqb"; "tvd"; "tvin"; "pclF"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "opp"; "pow"; "add"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "firstn"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index_darr.VRD"; "Pre_vr"; "tv0"; "P0_vr"; "P_fail"; "P_grown"; "P_keep"; "tv_post";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve"; "Pre_vr"; "vDp"; "P0_vr"; "tv0"; "vr_ret"; "spo"; "two47"; "vC"; "vD"; "vK"; "vr_entry"; "P_fail"; "P_grown"; "P_keep"; "tv_post"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "ok_sideK"; "MInvR"; "vm_insensitive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.Sum"; "Posts_bli"; "PD_bli"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index_darr"; "PD_vrd"; "HSd"; "darr_inv"; "E_vrd"; "X_nulld"; "cutsEd"; "exitsEd"; "C_LId"; "E_vr2d"; "K_faild"; "K_okd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "emeasZ"; "contE_TR"; "contE_check"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "jnode"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "sym_run"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
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

Module Lib_build_line_index.

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

Definition bli_entry : Z := 0x15f3c.
Definition bli_LI : Z := 0x15fe4.
Definition bli_ret : Z := 0x160c0.
Definition ra_vr : Z := 0x16014.
Definition FUEL_bli : nat := 500%nat.
Definition FR : Z := 96.

Definition vBUF : sv := SVar 12. Definition vLEN : sv := SVar 13. Definition vV : sv := SVar 14. Definition vAL : sv := SVar 33.
Definition kb16 (k : sv) : sv := SMd M_MUL (SLit 16) k.
Definition c8 (o : Z) (v : sv) : cell := mkCell (SLit o) 8 v.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1cS18PaA1S14Sc0S5aA1A1S14Z0A1Vcells;S1dA5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S1cSd4Sc0S5aA1A1Sd0S14Z0A1S4S17A1S1dA5").
Definition O_vec16 (d c k : sv) : sobj := ltac2:(tb__ "0|2|
S1cS58S14Z0M0A1S14Z20A1S0S17S49G0Vd;A2S0S17S49Z8Vc;A2S0S17S49Z10M1Vk;A2S0S17S49Z18S14G1A1A2S4S17A1A3A3A3A3S1dA5").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S1cS57S14Z0M0A1M1S14Z30A1S0S17S49G0S14Z13858A1A2S0S17S49Z8S14Z13864A1A2S0S17S49Z10G1A2S0S17S49Z18S14Z13878A1A2S0S17S49Z20G1A2S0S17S49Z28G1A2S4S17A1A3A3A3A3A3A3S1dA5").
Definition O_txt : sobj := ltac2:(tb__ "0|0|
S1cS5fS14Z0A1S4bS4S17A1S1dA5").
Definition O_dat (d k : sv) : sobj := ltac2:(tb__ "0|0|
S1cVd;S14Z0A1S55Vk;A1S4S17A1S1dA5").

Definition vec_facts (d c k : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S0S13S16Vc;Vk;A2S0S13S16S55Vk;A1S14Sd5A1M0A2S0S13S16Vk;G0A2S0S13S16Vd;G0A2S0S13S23Vdv;Z4A2S4S13A1A3A3A3A3A3").
Definition bli_facts : list sprop := ltac2:(tb__ "0|6|
S6S13S0S13S23PaM0Z4A2S0S13S24S9eS14N360A1Sd0A3S0S13S24S9eSd0S14Sc0Sc1Z2M1Z28A2A1A1A3S0S13S16S18P1eA1M2S1bS9dSd4Sc0S5aA1A1Sd0A3A2S0S13S16S1bS9dG2S14S5aA1A3S18G0A1M3A2S0S13S16G3S14Sd5A1M4A2S0S13S16S4bS14Sc1G1Z1aA2A1A2S0S13S16S14Z1A1S5fA2S0S13S16S5fG4A2S0S13S16G2S58A2S0S13S16S58G4A2S0S13S23PeZ3M5A2S0S13S16G2S57A2S0S13S16S57G4A2S0S13S23P21G5A2S0S13S16S14Z7fff7f800000A1G2A2S0S13S16G2S14Z7fffff800000A1A2S4S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S60Sd7Sd6Sd8PfA4A3").
Definition objs_of (fcells : list cell) (d c k : sv) : list sobj := ltac2:(tb__ "0|0|
S0S19S6eVfcells;A1S0S19S6dS0S19S71Vd;Vc;Vk;A3S0S19S6fS0S19S70S0S19S7bVd;Vk;A2S4S19A1A3A3A3A3A3A3").
Definition Pre_bli : sstate := ltac2:(tb__ "0|0|
S22S7eS3dS38S21ScS11A1S6aS4S17A1Sd7Sd6Sd8A4S5dS37SaA9").
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S11S11A2M0S1S11S11Sd7S55Sd8A1A4S4G0A1A3").

Definition cutpcs_bli : list Z := ltac2:(tb__ "0|0|
S0S35Sd9S0S35S68S4S35A1A3A3").
Definition run_of (S : sstate) : list sstate := ltac2:(tb__ "0|1|
SbS5Sf8A1M0A1S5S12A1Lx;SfaS34S67S69VS;S8A5G0Sc4Sf8S12Sf9R1A4Lls;S4S12A1Xbx2").
Definition leaves_at (S : sstate) (pc : Z) : list sstate := ltac2:(tb__ "0|1|
S101S12S5S12A1S103S12A1S12S100Sc3S2bR1A1Vpc;A2M0A1Ll;S12S102G0A1Lx;S82VS;A1A6").
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_bli end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition showr (l : sstate) : ltac2:(tb__ "0|0|
S2S2S2S35S5S11A1A2S5S2S2S2S11S11A2S11A2S3A2A1A2S5S13A1A2") := ltac2:(tb__ "0|6|
S1S2S2S35S5S11A1M0A2M1S5S2S2S2S11S11A2M2S11A2M3S3A2M4A1M5A2S5S13A1S1G1G5S1S35G0S2bVl;A1Sc6S11U1cS33Vl;A1A3A4Sc4S19G4S19S1G3S3S1G2S11S1S11S11S27R1A1S29R1A1A4S28R1A1A4S10S17S30R1A1A2A4Lo;S32Vl;A1A4A4Sc6S13U6S20Vl;A1A3A4").

Definition hx (r : nat) : sv := SVar (Pos.of_nat (200 + r)).
Definition bli_xregs : list sv := ltac2:(tb__ "0|0|
Sc4S3S11S3S7S11L_;S3bR1A1S3cR1A1S65R1A1X7x2Lr;Sc7U0U20A2A4").
Definition HNEXT : positive := 300.
Definition pD : sv := SVar 280. Definition pC : sv := SVar 281. Definition pK : sv := SVar 282.
Definition pI : sv := SVar 283. Definition pJ : sv := SVar 284. Definition pRES : sv := SVar 285.
Definition F_saved : list cell := ltac2:(tb__ "0|0|
S0S17S49N8S18PbA1A2S0S17S49N10S18P1cA1A2S0S17S49N18S18P1dA1A2S0S17S49N20S18P26A1A2S0S17S49N28S18P27A1A2S0S17S49N30S18P28A1A2S0S17S49N38S18P29A1A2S0S17S49N40S18P2aA1A2S0S17S49N48S18P2bA1A2S0S17S49N50S18P2cA1A2S0S17S49N58S18P2dA1A2S0S17S49N60S18P2eA1A2S4S17A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition body_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|4|
S39S7fS6S2S3S11A2M0S0G0S1S3S11U1M1S65G1A1A4S0G0S1S3S11U2Sd4Sc0S5aA1A1A4S0G0S1S3S11U8S57A4S0G0S1S3S11U9S58A4S0G0S1S3S11U12S4bA4S0G0S1S3S11U13S5fA4S0G0S1S3S11U14S14Z1A1A4S0G0S1S3S11U15M2S65G2A1A4S0G0S1S3S11U16S14ZaA1A4S0G0S1S3S11U17S14ZdA1A4S0G0S1S3S11U18S4aA4S0G0S1S3S11U19S5eA4S0G0S1S3S11U1aM3S65G3A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition HS (pc : Z) (regs : list (nat * sv)) (d c k : sv) (dv : positive) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S22Vpc;S73Vregs;A1S38S21ScS11A1S6aS6bVd;Vc;Vk;A4S6S13Vfacts;S6S13S60Vd;Vc;Vk;Vdv;A4S5dA3A3S6cSaA9").
Definition ij_facts : list sprop := ltac2:(tb__ "0|1|
S0S13S16S5eS4aA2S0S13S16S5eS14Sc1Z2Z1aA2A1M0A2S0S13S16S4aG0A2S4S13A1A3A3A3").

Definition C_LI : sstate := ltac2:(tb__ "0|0|
S61S68S4S2S3S11A2A1S4fS4cS4eP118S6S13S0S13S2eS4aS4bA2S4S13A1A3S51A3A7").

Definition E_vr : sstate := ltac2:(tb__ "0|1|
S61Sd9S0S2S3S11A2M0S1S3S11U1S14S56A1A4S0G0S1S3S11UaS58A4S0G0S1S3S11UbS1bS9dS4cS14Z1A1A3A4S0G0S1S3S11UcS57A4S4G0A1A3A3A3A3S4fS4cS4eP118S6S13S0S13S16S4aS4bA2S4S13A1A3S51A3A7").
Definition K_ok : sstate := ltac2:(tb__ "0|2|
S61Sd3S0S2S3S11A2M0S1S3S11U1S14S56A1A4S0G0S1S3S11UaS14Z1A1M1A4S4G0A1A3A3S4fS4cS4eP118S6S13S0S13S16S1bS9dS4cG1A3S4eA2S0S13S16S4aS4bA2S4S13A1A3A3S51A3A7").
Definition K_fail : sstate := ltac2:(tb__ "0|1|
S61Sd3S0S2S3S11A2M0S1S3S11U1S14S56A1A4S0G0S1S3S11UaS14Z0A1A4S4G0A1A3A3S4fS4cS4eP118S6S13S0S13S16S4aS4bA2S4S13A1A3S51A3A7").

Definition P_ret : sstate := ltac2:(tb__ "0|6|
S22S72S39S3aS37A1S0S2S3S11A2M0S1S3S11UaS18P8fA1M1A4S4G0A1A3A2S38S21ScS11A1S6aS4S17A1S18P8cM2A1M3S18P8dA1M4S18P8eA1M5A4S6S13S0S13S16G1S14Z1A1A2S4S13A1A3S6S13S60G3G4G5G2A4S5dA3A3P90SaA9").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S11S11A2M0S1S11S11S18P8cA1S55S18P8eA1A1A4S4G0A1A3").
Definition tvB : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S11S11A2M0S1S11S11S4fS55S4eA1A4S4G0A1A3").

Definition E_vr1 : sstate := Eval vm_compute in optS (apply_xforms E_vr [XSplit 1 (SLit (-64))]).
Definition E_vr2 : sstate := Eval vm_compute in optS (unbase_obj_at E_vr1 1 (-64)).
Definition s_vr : wsub := ltac2:(tb__ "0|1|
S6S2S36S11A2M0S0G0S1S36S11P13S1bS9dSd0S14Z40A1A3A4S0G0S1S36S11PfS4fA4S0G0S1S36S11P10S4cA4S0G0S1S36S11P11S4eA4S0G0S1S36S11P12S14Z10A1A4S4G0A1A3A3A3A3A3Sf5PaS78ScfA3A3").
Definition R_vr : list sobj := Eval vm_compute in optR (entails_fr E_vr2 Pre_vr s_vr).
Definition PD_vr : list pdesc := ltac2:(tb__ "0|2|
S0S2S12S5S2S11S11A2A1M0A2M1S1S12G0SdcSd2A4S0G1S1S12G0SdaSd2A4S0G1S1S12G0SdbSddA4S4G1A1A3A3A3").

Definition xs_keep : list xform := ltac2:(tb__ "0|2|
S0S93S94U0M0A1S0S93S94U1M1A1S0S93S96S0S3G1S0S3G0S0S3U2S0S3U3S0S3U4S0S3U5S0S3U6S4S3A1A3A3A3A3A3A3A3A1S0S93S95G0A1S4S93A1A3A3A3A3").
Definition xs_grown : list xform := ltac2:(tb__ "0|2|
S0S93S94U0M0A1S0S93S94U2M1A1S0S93S96S0S3G0S0S3G1S0S3U1S0S3U3S0S3U4S0S3U5S0S3U6S4S3A1A3A3A3A3A3A3A3A1S0S93S95G0A1S4S93A1A3A3A3A3").

Definition VL (j : sv) (ph : Z) : sv := ltac2:(tb__ "0|0|
S1bS9dS26Sa0S14Z8A1S1bSa1S1bS9dS14Sc2Sc1Z2Z1aA2Z10A2A1S4bA3Vj;A3A3S14Vph;A1A3").
Definition z0 : sv := SLit 0.
Definition cutsE : list edesc := ltac2:(tb__ "0|5|
S0S2S2S12S5S2S11S11A2A1M0A2M1S2S35S11A2M2A2M3S1G1G2S1S12G0S64S52A4S1S35S11Z64S59A4A4S0G3S1G1G2S1S12G0S77S4dA4S1S35S11Z32M4S50S4aZ5A2A4A4S0G3S1G1G2S1S12G0S7aS4dA4S1S35S11G4S50S4aZ3A2A4A4S0G3S1G1G2S1S12G0S79S4dA4S1S35S11Z2dS59A4A4S4G3A1A3A3A3A3").
Definition exitsE : list edesc := ltac2:(tb__ "0|4|
S0S2S2S12S5S2S11S11A2A1M0A2M1S2S35S11A2M2A2M3S1G1G2S1S12G0S66S4dA4S1S35S11Z32S50S4aZ4A2A4A4S0G3S1G1G2S1S12G0S62S53A4S1S35S11Z0S59A4A4S4G3A1A3A3").

Goal call_checkP E_vr2 Pre_vr s_vr R_vr [P_keep; P_fail; P_grown] = true /\ length R_vr = 2%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition P0_bli (FB : list (Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|3|
S47S42S35SffQ40M0S2aVr;PdA2A2M1Z0A3S44S35S35S44S35S35S43S97S2S35S35A2S1S35S35R2R1A4VFB;A3S43SbeR2SffG0S2aVr;PcA2A2M2A2SbeSc2G2G1A2Sc2R2R1A2A2A2A2Ln;A2Lb;A2A2").
Definition is_txt (o : sobj) : bool := ltac2:(tb__ "0|0|
SfSfS25S27Vo;A1S5fA2S25S29Vo;A1S14Z0A1A2A2S25S28Vo;A1S4bA2A2").

Lemma P0_vr_of_tvz : ltac2:(tb__ "0|3|
S15S36S36S35S5S19A1SbdS9bS42S11S9cR1P11A2S18R5A1A3S42S11S9cR2PfA2S18R7A1M0A3SabR9S0S2S11S11A2M1S1S11S11S18R8A1M2S26Sa0S14R6A1G0A3A4S4G1A1A3A2S1eRaS16G2S14Sd5A1A2A2S43SbeZ1R8A2SbeR8Z1000A2A2Sd1S9aS99RcR8R7A3R6A2A1F_;F_;F_;F_;F_;Fs;Fms;FR;Fe;Fk;Fd;Frho;").
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
S5S92A1S91OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs C_P.

Definition Posts_bli : list (sstate * jpost) := ltac2:(tb__ "0|1|
S0S2S12S87A2M0S1S12S87S62Sa5S34S3eVKc;S48VFB;A1VFB;S53A6A4S4G0A1A3").
Definition PD_bli : list pdesc := ltac2:(tb__ "0|2|
S0S2S12S5S2S11S11A2A1M0A2M1S1S12G0S62S53A4S4G1A1A3").
Lemma Posts_bli_PD : ltac2:(tb__ "0|0|
S42S5S2S12S87A2A1Se4Sa6S34S3eVKc;S48Se5VFB;A6A3").
Proof using . reflexivity. Qed.

Let nI : ltac2:(tb__ "0|0|
S2S12S5S2S11S11A2A1A2Sf6Fn;") := ltac2:(tb__ "0|0|
Sb5S34S3eS37VKc;Vrho0;S48VFB;A1VFB;A7").
Let JGv (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
Sa2S34S3eS37VKc;Vrho0;S48VFB;A1VFB;Vtv;A8").
Let Q : assn := ltac2:(tb__ "0|0|
S88S34S37Vrho0;Se4A4").

Lemma ejcert_ok : ltac2:(tb__ "0|0|
S42S7Sb0S34S37S67S69P64S74S75A7S8A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma txt_extra_ok : ltac2:(tb__ "0|1|
S15S5S2S11S11A2A1S5S19A1S19S35S48VFB;Vrho0;A2S89S37Vrho0;R6A3S97S19R4R5A3S42S7S80R5A1S8A3S43SbeS9S35S35S31R9R6A2M0A3R5A2SbfR5SdS35S35G0A3A2A2SbcS34S3eVrho0;Sa8VFB;RaR9A3R6A5F_;F_;F_;F_;F_;Fa;Fo;FR;Fkept;Frho;").
Proof using JGv.
  intros rho kept R o a HP0 Hav Ho Ht Hr. unfold is_txt in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  unfold vBUF, vLEN in Hr. rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 12%positive ltac:(reflexivity)), <- (Hw 13%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  right; right.
  pose proof (bv_urange (rw rho0 13)) as R13.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [apply in_or_app; left; exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 13))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S41S12S15S83Sc5S13S1eR2A1S20R3A1A3VTR;S40S34R5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S83S83S83S84R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS83S83R3VTR;R3R2A2F_;VTR;S84S43R5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S41S41S12S12S9bS5S19A1M0S5S2S12S87A2M1A1S83S15S42SbG0A1Sf1R7R6R5A3SeG0R4A2A3S42S7S8bR8R7R6R5Sc4G1S12S9S12S87A2R4A4A5S8A3S15VTR;S40S34RbR9R1A4S88S34S1aR9A1R1R6A4A2Frho1;S5S92A1M2SbdS91S1fS34R7RdS1G2SdeR3SdfR2R1A2A4A4R10R8R4R2A3R10S9aS99R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S12S87G2SbdS91S15G2SbdS91S97G1S1S12S87R9R8A4R10A3S1fS34RfR15S1G2SdeR8SdfR7R6A2A4A4R18R10R9R7A3S89S1aR16A1S9aS99R11R14R9A3R15A2R7A3S1fS34R8RdS1G2SdeR7SdfR6R5A2A4A4RdS9aS99R13R16RbA3R17A2R9R8R6A4S43S8dR14RcR17R18R19RfRaA7S15S8cR15RdR18R19R1aR1bR10R1RbA9VTR;S40S34S8aR10S9aS99R16R19ReA3R1aA2RcA3S8eR1aS1aR1bA1R11S1aR1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S40S34ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CVR : ltac2:(tb__ "0|1|
S5S2S35S35A2A1M0S15VTR;S40S34Sa3S34S3eVKc;Sd1R2Sd2A6ScfR1A4S88S34S37R1Sa6S34S3eVKc;G0Sd1L_;S5bR2A6A4A2Frho1;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S12S5S2S11S11A2A1M0S2S35S11A2M1S15S35S97S2S2S12G0A2M2G1A2S1G2G1S1S12G0R5R4A4R3A4S74A3S43SbeZ0Sa4S1G2G1S1S12G0R6R5A4R4A4R3A2M3A2SbfG3R2A2A2VTR;S40S34VJGv;R6A1R7R4A4VFAM;R3A1A2F_;F_;Fb;Frho;Frv;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S12S5S2S11S11A2A1S15S35S97S2S12S87A2S1S12S87R4Sa5S34S3eVKc;S48VFB;A1VFB;R3A6A4Se4A3VTR;S40S34VJGv;R4A1R5R3A4VFAM;R2A1A2F_;Fb;Frho;Ftv;FP;").

Let CLIENT : ltac2:(tb__ "0|8|
S12S9bS5S19A1M0S15S5S2S11S11A2M1A1M2G2S83S42SbG0A1Sf1R7ScfR6A3SeG0R5A2A3S42S7SaeS3eS37R8ScfR7R6Sc4S2S12G2A2M3S12S9S12G2A2S5bA4A7S8A3S42S7S90R8S37A2S8A3S42S7SfdS37S1aRaA1A2S8A3S42S7Sb8S1aRbA1S6G1R7R6A3A2S8A3S42S7Sb9RbR7Sd2A3S8A3S42S7S98G3G3SfSb7S37RdS1aReA1S9S12G2R1A3M4SdS12G2R1A3M5A5Sb4ScfG4G5A3A2Ld;S5bA3S8A3SfbSbdSc5S13S1eRdA1S20R10A1A3S48VFB;Vrho0;A2S89S37Vrho0;RfA3Sb1VFB;R5A2SbbVFB;R6R11S6G1R10RfA3A4SbaR12S6G1R11R10A3A2SabR13S6G1R12R11A3A2S44S15S15S44S91S91Se2S34S3eRbR2R1A5Lmd;A2LrhoM;A2SadR15S3fSfcRaA1A1A2S43Sb6S34S3eVrho0;VFB;R16R15R17A7S5S2S35S35A2A1Sd1L_;Sa8VFB;R16R15A3S9aS99R16R17RaA3R18A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;Sa7S15S97Sa7R2S5bA3S89S1aR12A1RfR2A3VTR;S40S34Sa2S34S3eS37VKc;Vrho0;S48VFB;A1M6VFB;S6G1RfSb2S8fR12S37S9S12G2R4A3M7S1aR13A1A4SdS12G2R4A3A2A3A8SacS37R13R12R11G7A5R3A4RdA2F_;F_;Frho';Fd;VTR;S40S34Sa2S34S3eS37VKc;Vrho0;G6VFB;S6G1RcRbA3A8R10RdA4RaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fpassed;Fkept;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
SafS34S3eS37VKc;Vrho0;S48VFB;A1VFB;VML;S5S2S35S35A2A1Sd1L_;ScfSd2S5bS37S45S36S1aScfA1A2VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;VCVR;A14").
Let CONT : ltac2:(tb__ "0|4|
S5S93A1S3S35S36S12S12S5S2S11S11A2M0A1M1G1G1S11S35S35S11S15S15S83S42S7Sf4S37R10RfReRdRcRbRaR9R7R6R5R4AdS8A3SfeG0RaR9A3S89RfR5R4A3S15S43SbeZ0Sf2RaRbR1A3M2A2SbfG2Sf2R9R8R7A3A2A2VTR;S40S34Sa2S34S3eS37VKc;Vrho0;S48VFB;A1M3VFB;RdA8R10R2A4R6A2F_;Frho';VTR;S40S34Sa2S34S3eS37VKc;Vrho0;G3VFB;ReA8R10R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;FA;FT;Fn;Fc;Fi;Fxs;") := ltac2:(tb__ "0|0|
Sf3S34S3eS37VKc;Vrho0;S48VFB;A1VFB;VML;VTR;VTR_pre;VTR_exw;VTR_pureh;Ac").

Lemma X_P_ret : ltac2:(tb__ "0|0|
S15S35VTR;S40S34VJGv;S53A1S62R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_E_vr : ltac2:(tb__ "0|1|
S15VTR;S40S34VJGv;S4dA1S66R1A4VFAM;Sa4S1S2S12S5S2S11S11A2A1M0A2S2S35S11A2S1S12G0S66S4dA4S1S35S11Z32S50S4aZ4A2A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho; eapply TR_pre.
  2: { change (JGv tvB) with (JGv ([] ++ tvB)).
       apply (CLIENT E_vr2 s_vr R_vr rho [] tvB _).
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       -
         intros Ai ms HF HP0 Hav X3 X4 X5 HZ X6 HT. split.
         + eapply robjs_checkF_sound with (extra := is_txt).
           * exact HF. * exact (TobjJVx.T_ok_T0_NF _ _ _ Hav HT). * constructor. * vm_compute; reflexivity. * intros o a Ho Hx Hr; eapply txt_extra_ok; eauto.
         + cbn beta. eapply (P0_vr_of_tvz _ 280 282 16); [reflexivity | reflexivity | exact HZ | | lia].
           eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto.
       - intros d rho' Hd Hag; destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app].
         + eapply (CONT xs_keep 0 (- FR) (ss_next E_vr2) _ K_ok _ tvB tvB (VL pJ 3) 50 50 (VL pJ 4) rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER K_ok tvB (50, VL pJ 3) rho''); [apply (nth_error_In _ 2); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_keep 0 (- FR) (ss_next E_vr2) _ K_fail _ tvB tvB z0 45 50 (VL pJ 4) rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER K_fail tvB (45, z0) rho''); [apply (nth_error_In _ 3); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_grown 0 (- FR) (ss_next E_vr2) _ K_ok _ tvB tvB (VL pJ 3) 50 50 (VL pJ 4) rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER K_ok tvB (50, VL pJ 3) rho''); [apply (nth_error_In _ 2); reflexivity | rewrite emeas_emeasZ; exact Hm]. }
  intros w Hw.
  apply (SPJ_unbase segs _ rho E_vr1 1 (-64) E_vr2 w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ [XSplit 1 (SLit (-64))] rho E_vr E_vr1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S12S5S2S11S11A2A1M0S2S35S11A2M1S15S97S2S2S12G0A2M2G1A2S1G2G1S1S12G0R4R3A4R2A4S75A3VTR;S40S34VJGv;R4A1R5R2A4VFAM;Sa4S1G2G1S1S12G0R5R4A4R3A4R2A2A1A2F_;Frho;FrvX;FtvX;FX;").
Proof using CLIENT CONT POST REENTER nI.
  intros X tvX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[]]]; injection H as <- <- <-.
  - apply X_E_vr.
  - apply X_P_ret.
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ltac2:(tb__ "0|0|
Se1S34Vok;VKc;A3").
Hypothesis MC : ltac2:(tb__ "0|0|
Sa9S34S3eSe0A3").

Theorem build_line_index_sum : ltac2:(tb__ "0|0|
S86S34Vok;S40S34Sa3S34S3eVKc;S48VFB;A1VFB;S52A6S64Vrho0;A4S88S34S37Vrho0;Se4A4A4").
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segs C_P NF Kc rho0 (P0_bli FB) FB ML FUEL_bli cutpcs_bli 100 cutsE exitsE ok Q (proj1 HS)
                (ejcert_jcert segs NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nI (map (@edrop) cutsE)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                (triple_pureh segs ok)
                (call_soundP segs ok)).
       - intros FBc rho1. apply (vec_reserve_sum ok Kc FBc rho1 HS ML MC).
       - intros T tv rv rho b Hin _. exact (reenter_cutGE segs C_P NF Kc rho0 (P0_bli FB) FB ok cutsE T tv rv Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segs C_P NF Kc (P0_bli FB) FB ok rho0 tv Posts_bli P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
SaaS34S3eSe0A3").

Theorem build_line_index_sum_ex : ltac2:(tb__ "0|0|
S85S34S40S34Sa3S34S3eVKc;S48VFB;A1VFB;S52A6S64Vrho0;A4S88S34S37Vrho0;Se4A4A3").
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segs C_P NF Kc rho0 (P0_bli FB) FB ML FUEL_bli cutpcs_bli 100 cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeI segs C_P NF Kc rho0 (P0_bli FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                (etriple_pureh segs)
                (call_completeP segs)).
       - intros FBc rho1. apply (vec_reserve_sum_ex Kc FBc rho1 ML Hvi MCX).
       - intros T tv rv rho b Hin Hm. exact (ereenter_cutE segs C_P NF Kc rho0 (P0_bli FB) FB cutsE T tv rv Q b rho Hin Hm).
       - intros P tv rho b Hin. apply (eexit_postG segs C_P NF Kc (P0_bli FB) FB rho0 tv Posts_bli P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Definition lines_tmpl : list tfact := ltac2:(tb__ "0|0|
S0S2cS2fSaU0U1S4bA4S4S2cA1A3").
Definition O_dat_darr (d c k : sv) : sobj := ltac2:(tb__ "0|3|
S1cVd;S14Z0M0A1S55Vk;A1S4S17A1S2dZ10Vc;S0S2S35S35A2M1S1S35S35G0Z8M2A4S0G1S1S35S35G2G2A4S4G1A1A3A3S81A4A5").
Definition objs_of_darr (fcells : list cell) (d c k : sv) : list sobj := ltac2:(tb__ "0|0|
S0S19S6eVfcells;A1S0S19S6dS0S19S71Vd;Vc;Vk;A3S0S19S6fS0S19S70S0S19S7cVd;Vc;Vk;A3S4S19A1A3A3A3A3A3A3").
Definition P_ret_darr : sstate := ltac2:(tb__ "0|6|
S22S72S39S3aS37A1S0S2S3S11A2M0S1S3S11UaS18P8fA1M1A4S4G0A1A3A2S38S21ScS11A1S76S4S17A1S18P8cM2A1M3S18P8dA1M4S18P8eA1M5A4S6S13S0S13S16G1S14Z1A1A2S0S13S16G4S4bA2S4S13A1A3A3S6S13S60G3G4G5G2A4S5dA3A3P90SaA9").

Definition Pre_bli0 : sstate := ltac2:(tb__ "0|0|
Sf7S0S13S16Sd6S14Z0A1A2S4S13A1A3S64A2").
Definition Posts_bli_darr (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) := ltac2:(tb__ "0|1|
S0S2S12S87A2M0S1S12S87S63Sa5S34S3eVKc;S48VFB;A1VFB;S53A6A4S4G0A1A3").
Definition PD_bli_darr : list pdesc := ltac2:(tb__ "0|2|
S0S2S12S5S2S11S11A2A1M0A2M1S1S12G0S63S53A4S4G1A1A3").
Lemma Posts_bli_darr_PD : ltac2:(tb__ "0|0|
S5S92A1S91OF_;F_;S5S2S35S35A2A1S42S5S2S12S87A2A1S54R2R1A2Sa6S34S3eR2S48S7dR1A6A3FFB;FKc;").
Proof. reflexivity. Qed.
Definition bli_darr_stmt : Prop := ltac2:(tb__ "0|0|
S84OF_;S5S92A1S91OF_;F_;S5S2S35S35A2A1S15Se1S34R4R3A3Sb3S34S3eA2Sa9S34S3eSe0A3S86S34R7S40S34Sa3S34S3eR6S48R5A1R5S52A6S5cR4A4S88S34S37R4S54R6R5A2A4A4F_;F_;F_;Frho0;FFB;FKc;Fok;").
Definition bli_darr_ex_stmt : Prop := ltac2:(tb__ "0|0|
S5S92A1S91OF_;F_;S5S2S35S35A2A1S15Sb3S34S3eA2Se3R4A1SaaS34S3eSe0A3S85S34S40S34Sa3S34S3eR6S48R5A1R5S52A6S5cR4A4S88S34S37R4S54R6R5A2A4A3F_;F_;F_;Frho0;FFB;FKc;").
End Lib_build_line_index.

Module Lib_build_line_index_darr.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module VRD. Include P.Lib_vec__G1.Lib_vec_reserve_darr. End VRD.

Definition HSd (pc : Z) (regs : list (nat * sv)) (d c k : sv) (dv : positive) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S22Vpc;S73Vregs;A1S38S21ScS11A1S76S6bVd;Vc;Vk;A4S6S13Vfacts;S6S13S60Vd;Vc;Vk;Vdv;A4S5dA3A3S6cSaA9").
Definition darr_inv : list sprop := ltac2:(tb__ "0|0|
S0S13S16S4cS5eA2S0S13S24S9fS5eS4bA3S4S13A1A3A3").
Definition C_LId : sstate := ltac2:(tb__ "0|0|
Se7S68S4S2S3S11A2A1S4fS4cS4eP118S6S13S0S13S24S9fS4aS4bA3S4S13A1A3S6S13S51Se8A3A3A7").
Definition E_vrd : sstate := ltac2:(tb__ "0|1|
Se7Sd9S0S2S3S11A2M0S1S3S11U1S14S56A1A4S0G0S1S3S11UaS58A4S0G0S1S3S11UbS1bS9dS4cS14Z1A1A3A4S0G0S1S3S11UcS57A4S4G0A1A3A3A3A3S4fS4cS4eP118S6S13S0S13S16S4aS4bA2S4S13A1A3S6S13S51Se8A3A3A7").
Definition K_okd : sstate := ltac2:(tb__ "0|2|
Se7Sd3S0S2S3S11A2M0S1S3S11U1S14S56A1A4S0G0S1S3S11UaS14Z1A1M1A4S4G0A1A3A3S4fS4cS4eP118S6S13S0S13S16S1bS9dS4cG1A3S4eA2S0S13S16S4aS4bA2S4S13A1A3A3S6S13S51Se8A3A3A7").
Definition K_faild : sstate := ltac2:(tb__ "0|1|
Se7Sd3S0S2S3S11A2M0S1S3S11U1S14S56A1A4S0G0S1S3S11UaS14Z0A1A4S4G0A1A3A3S4fS4cS4eP118S6S13S0S13S16S4aS4bA2S4S13A1A3S6S13S51Se8A3A3A7").

Definition E_vr1d : sstate := Eval vm_compute in optS (apply_xforms E_vrd [XSplit 1 (SLit (-64))]).
Definition E_vr2d : sstate := Eval vm_compute in optS (unbase_obj_at E_vr1d 1 (-64)).
Definition s_vrd : wsub := ltac2:(tb__ "0|1|
S6S2S36S11A2M0S0G0S1S36S11P13S1bS9dSd0S14Z40A1A3A4S0G0S1S36S11PfS4fA4S0G0S1S36S11P10S4cA4S0G0S1S36S11P11S4eA4S0G0S1S36S11P34S4bA4S4G0A1A3A3A3A3A3Sf5PaSeeSc8A3A3").
Definition R_vrd : list sobj := Eval vm_compute in optR (entails_fr E_vr2d VRD.Pre_vr s_vrd).
Definition PD_vrd : list pdesc := ltac2:(tb__ "0|2|
S0S2S12S5S2S11S11A2A1M0A2M1S1S12G0ScdSc9A4S0G1S1S12G0ScbSc9A4S0G1S1S12G0SccSceA4S4G1A1A3A3A3").

Definition cutsEd : list edesc := ltac2:(tb__ "0|5|
S0S2S2S12S5S2S11S11A2A1M0A2M1S2S35S11A2M2A2M3S1G1G2S1S12G0S5cS52A4S1S35S11Z64S59A4A4S0G3S1G1G2S1S12G0SedS4dA4S1S35S11Z32M4S50S4aZ5A2A4A4S0G3S1G1G2S1S12G0Sf0S4dA4S1S35S11G4S50S4aZ3A2A4A4S0G3S1G1G2S1S12G0SefS4dA4S1S35S11Z2dS59A4A4S4G3A1A3A3A3A3").

Definition X_nulld : sstate := Eval vm_compute in nth 0 (leaves_at K_okd bli_ret) Pre_bli.
Definition exitsEd : list edesc := ltac2:(tb__ "0|5|
S0S2S2S12S5S2S11S11A2A1M0A2M1S2S35S11A2M2A2M3S1G1G2S1S12G0Se9S4dA4S1S35S11Z32S50S4aZ4A2A4A4S0G3S1G1G2S1S12G0S63S53A4S1S35S11Z0S59A4M4A4S0G3S1G1G2S1S12G0SeaS4dA4G4A4S4G3A1A3A3A3").

Ltac find_idx F l := lazymatch l with | F :: _ => constr:(O) | _ :: ?t => let i := find_idx F t in constr:(S i) end.
Ltac have_fact HF F :=
  lazymatch type of HF with Forall _ ?l =>
    let l' := eval vm_compute in l in let F' := eval vm_compute in F in let i := find_idx F' l' in
    pose proof (Forall_pick _ _ i F HF eq_refl) end.

Goal call_checkP E_vr2d VRD.Pre_vr s_vrd R_vrd [VRD.P_keep; VRD.P_fail; VRD.P_grown] = true /\ length R_vrd = 2%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section Sum.
Variable Kc : ltac2:(tb__ "0|0|
S5S92A1S91OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs C_P.

Let nI : ltac2:(tb__ "0|0|
S2S12S5S2S11S11A2A1A2Sf6Fn;") := ltac2:(tb__ "0|0|
Sb5S34S3eS37VKc;Vrho0;S48VFB;A1VFB;A7").
Let JGv (tv : list (sv * sv)) : jpred := ltac2:(tb__ "0|0|
Sa2S34S3eS37VKc;Vrho0;S48VFB;A1VFB;Vtv;A8").
Let Q : assn := ltac2:(tb__ "0|0|
S88S34S37Vrho0;S54VKc;VFB;A2A4").

Lemma ejcert_ok : ltac2:(tb__ "0|0|
S42S7Sb0S34S37S67S69P64SebSecA7S8A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S41S12S15S83Sc5S13S1eR2A1S20R3A1A3VTR;S40S34R5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S83S83S83S84R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS83S83R3VTR;R3R2A2F_;VTR;S84S43R5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").
Hypothesis TR_contra : ltac2:(tb__ "0|0|
S41S12S83S15S5S92A1S91R6R3R2R1A3Sc5S13S1eR4A1S20R6A1A3S46F_;F_;Fmd;Ftr;Frho;S15VTR;S40S34R5R4R1A4R3A2Frho;F_;FQ';FX;FJ;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S41S41S12S12S9bS5S19A1M0S5S2S12S87A2M1A1S83S15S42SbG0A1Sf1R7R6R5A3SeG0R4A2A3S42S7S8bR8R7R6R5Sc4G1S12S9S12S87A2R4A4A5S8A3S15VTR;S40S34RbR9R1A4S88S34S1aR9A1R1R6A4A2Frho1;S5S92A1M2SbdS91S1fS34R7RdS1G2SdeR3SdfR2R1A2A4A4R10R8R4R2A3R10S9aS99R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S12S87G2SbdS91S15G2SbdS91S97G1S1S12S87R9R8A4R10A3S1fS34RfR15S1G2SdeR8SdfR7R6A2A4A4R18R10R9R7A3S89S1aR16A1S9aS99R11R14R9A3R15A2R7A3S1fS34R8RdS1G2SdeR7SdfR6R5A2A4A4RdS9aS99R13R16RbA3R17A2R9R8R6A4S43S8dR14RcR17R18R19RfRaA7S15S8cR15RdR18R19R1aR1bR10R1RbA9VTR;S40S34S8aR10S9aS99R16R19ReA3R1aA2RcA3S8eR1aS1aR1bA1R11S1aR1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S40S34ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CVR : ltac2:(tb__ "0|1|
S5S2S35S35A2A1M0S15VTR;S40S34Sa3S34S3eVKc;ScaR2Sc9A6Sc8R1A4S88S34S37R1Sa6S34S3eVKc;G0ScaL_;Se6R2A6A4A2Frho1;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S12S5S2S11S11A2A1M0S2S35S11A2M1S15S35S97S2S2S12G0A2M2G1A2S1G2G1S1S12G0R5R4A4R3A4SebA3S43SbeZ0Sa4S1G2G1S1S12G0R6R5A4R4A4R3A2M3A2SbfG3R2A2A2VTR;S40S34VJGv;R6A1R7R4A4VFAM;R3A1A2F_;F_;Fb;Frho;Frv;Ftv;FT;").
Hypothesis POST : ltac2:(tb__ "0|0|
S12S5S2S11S11A2A1S15S35S97S2S12S87A2S1S12S87R4Sa5S34S3eVKc;S48VFB;A1VFB;R3A6A4S54VKc;VFB;A2A3VTR;S40S34VJGv;R4A1R5R3A4VFAM;R2A1A2F_;Fb;Frho;Ftv;FP;").

Let CLIENT : ltac2:(tb__ "0|8|
S12S9bS5S19A1M0S15S5S2S11S11A2M1A1M2G2S83S42SbG0A1Sf1R7Sc8R6A3SeG0R5A2A3S42S7SaeS3eS37R8Sc8R7R6Sc4S2S12G2A2M3S12S9S12G2A2Se6A4A7S8A3S42S7S90R8S37A2S8A3S42S7SfdS37S1aRaA1A2S8A3S42S7Sb8S1aRbA1S6G1R7R6A3A2S8A3S42S7Sb9RbR7Sc9A3S8A3S42S7S98G3G3SfSb7S37RdS1aReA1S9S12G2R1A3M4SdS12G2R1A3M5A5Sb4Sc8G4G5A3A2Ld;Se6A3S8A3SfbSbdSc5S13S1eRdA1S20R10A1A3S48VFB;Vrho0;A2S89S37Vrho0;RfA3Sb1VFB;R5A2SbbVFB;R6R11S6G1R10RfA3A4SbaR12S6G1R11R10A3A2SabR13S6G1R12R11A3A2S44S15S15S44S91S91Se2S34S3eRbR2R1A5Lmd;A2LrhoM;A2SadR15S3fSfcRaA1A1A2S43Sb6S34S3eVrho0;VFB;R16R15R17A7S5S2S35S35A2A1ScaL_;Sa8VFB;R16R15A3S9aS99R16R17RaA3R18A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;Sa7S15S97Sa7R2Se6A3S89S1aR12A1RfR2A3VTR;S40S34Sa2S34S3eS37VKc;Vrho0;S48VFB;A1M6VFB;S6G1RfSb2S8fR12S37S9S12G2R4A3M7S1aR13A1A4SdS12G2R4A3A2A3A8SacS37R13R12R11G7A5R3A4RdA2F_;F_;Frho';Fd;VTR;S40S34Sa2S34S3eS37VKc;Vrho0;G6VFB;S6G1RcRbA3A8R10RdA4RaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fpassed;Fkept;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
SafS34S3eS37VKc;Vrho0;S48VFB;A1VFB;VML;S5S2S35S35A2A1ScaL_;Sc8Sc9Se6S37S45S36S1aSc8A1A2VTR;VTR_facts;VTR_ex;VTR_pre;VTR_callP;VCVR;A14").
Let CONT : ltac2:(tb__ "0|4|
S5S93A1S3S35S36S12S12S5S2S11S11A2M0A1M1G1G1S11S35S35S11S15S15S83S42S7Sf4S37R10RfReRdRcRbRaR9R7R6R5R4AdS8A3SfeG0RaR9A3S89RfR5R4A3S15S43SbeZ0Sf2RaRbR1A3M2A2SbfG2Sf2R9R8R7A3A2A2VTR;S40S34Sa2S34S3eS37VKc;Vrho0;S48VFB;A1M3VFB;RdA8R10R2A4R6A2F_;Frho';VTR;S40S34Sa2S34S3eS37VKc;Vrho0;G3VFB;ReA8R10R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;FA;FT;Fn;Fc;Fi;Fxs;") := ltac2:(tb__ "0|0|
Sf3S34S3eS37VKc;Vrho0;S48VFB;A1VFB;VML;VTR;VTR_pre;VTR_exw;VTR_pureh;Ac").

Lemma X_P_ret : ltac2:(tb__ "0|0|
S15S35VTR;S40S34VJGv;S53A1S63R2A4VFAM;R1A1A2Fb;Frho;").
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_nulld_ok : ltac2:(tb__ "0|0|
S15S35VTR;S40S34VJGv;S4dA1SeaR2A4VFAM;R1A1A2Fb;Frho;").
Proof using FB Kc TR_contra rho0.
  intros rho b. apply TR_contra. intros r tr md (Ai & Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0) HF.
  have_fact HF (SPBranch BC_EQ pD (SLit 0)). have_fact HF (SPUle (SAlu ALU_ADD pC (SLit 1)) pK).
  have_fact HF (SPUle pK (SLit two47)). have_fact HF (SPUle pC pI). have_fact HF (SPUle pI (SLit (2 ^ 26))). clear HF.
  assert (Hz : bv_unsigned (eval r (kb16 pK)) = 0).
  { apply (proj1 (Forall_forall _ _) HZ (pD, kb16 pK) ltac:(left; reflexivity)).
    intros Hnz. apply Hnz. unfold pD in *. cbn [fst eval]. zfacts; lia. }
  unfold kb16, pK, pC, pD, pI, two47 in *. zfacts; nia.
Qed.

Lemma X_E_vr : ltac2:(tb__ "0|1|
S15VTR;S40S34VJGv;S4dA1Se9R1A4VFAM;Sa4S1S2S12S5S2S11S11A2A1M0A2S2S35S11A2S1S12G0Se9S4dA4S1S35S11Z32S50S4aZ4A2A4A4R1A2A1A2Frho;").
Proof using CLIENT CONT REENTER nI.
  intros rho; eapply TR_pre.
  2: { change (JGv tvB) with (JGv ([] ++ tvB)).
       apply (CLIENT E_vr2d s_vrd R_vrd rho [] tvB _).
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       -
         intros Ai ms HF HP0 Hav X3 X4 X5 HZ X6 HT. split.
         + eapply robjs_checkF_sound with (extra := is_txt).
           * exact HF. * exact (TobjJVx.T_ok_T0_NF _ _ _ Hav HT). * constructor. * vm_compute; reflexivity. * intros o a Ho Hx Hr; eapply txt_extra_ok; eauto.
         + cbn beta. change (VRD.P0_vr (rho_sub (rho_absorb rho R_vrd ms) s_vrd)) with (P0_vr (rho_sub (rho_absorb rho R_vrd ms) s_vrd)).
           eapply (P0_vr_of_tvz _ 280 282 16); [reflexivity | reflexivity | exact HZ | | lia].
           eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto.
       - intros d rho' Hd Hag; destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app].
         + eapply (CONT xs_keep 0 (- FR) (ss_next E_vr2d) _ K_okd _ tvB tvB (VL pJ 3) 50 50 (VL pJ 4) rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER K_okd tvB (50, VL pJ 3) rho''); [apply (nth_error_In _ 2); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_keep 0 (- FR) (ss_next E_vr2d) _ K_faild _ tvB tvB z0 45 50 (VL pJ 4) rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER K_faild tvB (45, z0) rho''); [apply (nth_error_In _ 3); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_grown 0 (- FR) (ss_next E_vr2d) _ K_okd _ tvB tvB (VL pJ 3) 50 50 (VL pJ 4) rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER K_okd tvB (50, VL pJ 3) rho''); [apply (nth_error_In _ 2); reflexivity | rewrite emeas_emeasZ; exact Hm]. }
  intros w Hw.
  apply (SPJ_unbase segs _ rho E_vr1d 1 (-64) E_vr2d w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segs _ [XSplit 1 (SLit (-64))] rho E_vrd E_vr1d w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S12S5S2S11S11A2A1M0S2S35S11A2M1S15S97S2S2S12G0A2M2G1A2S1G2G1S1S12G0R4R3A4R2A4SecA3VTR;S40S34VJGv;R4A1R5R2A4VFAM;Sa4S1G2G1S1S12G0R5R4A4R3A4R2A2A1A2F_;Frho;FrvX;FtvX;FX;").
Proof using CLIENT CONT POST REENTER TR_contra nI.
  intros X tvX rvX rho Hin. cbn [exitsEd In] in Hin.
  destruct Hin as [H|[H|[H|[]]]]; injection H as <- <- <-.
  - apply X_E_vr.
  - apply X_P_ret.
  - apply X_nulld_ok.
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ltac2:(tb__ "0|0|
Se1S34Vok;VKc;A3").
Hypothesis MC : ltac2:(tb__ "0|0|
Sa9S34S3eSe0A3").

Theorem build_line_index_darr_sum : ltac2:(tb__ "0|0|
S86S34Vok;S40S34Sa3S34S3eVKc;S48VFB;A1VFB;S52A6S5cVrho0;A4S88S34S37Vrho0;S54VKc;VFB;A2A4A4").
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segs C_P NF Kc rho0 (P0_bli FB) FB ML FUEL_bli cutpcs_bli 100 cutsEd exitsEd ok Q (proj1 HS)
                (ejcert_jcert segs NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nI (map (@edrop) cutsEd)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                (triple_pureh segs ok) (triple_contraJ segs ok)
                (call_soundP segs ok)).
       - intros FBc rho1. rewrite <- VRD.Posts_vr_PD. apply (VRD.vec_reserve_darr_sum ok Kc FBc rho1 HS ML MC).
       - intros T tv rv rho b Hin _. exact (reenter_cutGE segs C_P NF Kc rho0 (P0_bli FB) FB ok cutsEd T tv rv Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segs C_P NF Kc (P0_bli FB) FB ok rho0 tv (Posts_bli_darr Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
SaaS34S3eSe0A3").

Theorem build_line_index_darr_sum_ex : ltac2:(tb__ "0|0|
S85S34S40S34Sa3S34S3eVKc;S48VFB;A1VFB;S52A6S5cVrho0;A4S88S34S37Vrho0;S54VKc;VFB;A2A4A3").
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segs C_P NF Kc rho0 (P0_bli FB) FB ML FUEL_bli cutpcs_bli 100 cutsEd exitsEd Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeI segs C_P NF Kc rho0 (P0_bli FB) FB) cutsEd) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                (etriple_pureh segs) (etriple_contraJ segs)
                (call_completeP segs)).
       - intros FBc rho1. rewrite <- VRD.Posts_vr_PD. apply (VRD.vec_reserve_darr_sum_ex Kc FBc rho1 ML Hvi MCX).
       - intros T tv rv rho b Hin Hm. exact (ereenter_cutE segs C_P NF Kc rho0 (P0_bli FB) FB cutsEd T tv rv Q b rho Hin Hm).
       - intros P tv rho b Hin. apply (eexit_postG segs C_P NF Kc (P0_bli FB) FB rho0 tv (Posts_bli_darr Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem bli_darr_ok : bli_darr_stmt.
Proof. intros ok Kc FB rho0 HS ML MC. exact (build_line_index_darr_sum Kc FB rho0 ML ok HS MC). Qed.
Theorem bli_darr_ex_ok : bli_darr_ex_stmt.
Proof. intros Kc FB rho0 ML Hvi MCX. exact (build_line_index_darr_sum_ex Kc FB rho0 ML Hvi MCX). Qed.
End Lib_build_line_index_darr.
