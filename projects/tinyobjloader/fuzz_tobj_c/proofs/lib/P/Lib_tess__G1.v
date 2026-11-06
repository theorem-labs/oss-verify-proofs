(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "prod"; "app"; "None"; "false"; "true"; "bool"; "Some"; "list"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SVar"; "SAlu"; "cell"; "sstate"; "SPUle"; "mkCell"; "sobj"; "SPUlt"; "DUnknown"; "SPBranch"; "mkObj"; "SMd"; "SPEq"; "FcsrFrm0"; "mkSS"; "tfact"; "SPNot"; "SPAlign"; "TFle"; "DArr"; "valuation"; "DList"; "ss_facts"; "ss_fregs"; "ss_lenient"; "ss_regs"; "SExt"; "SMdW"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "M_MUL"; "BC_EQ"; "BC_NE"; "ALU_SRL"; "ALU_AND"; "BC_GE"; "BC_GEU"; "ALU_SLTU"; "BC_LTU"; "M_REMU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d"; "vN"; "cut"; "stk_cells"; "vPRV"; "vNXT"; "vP2D"; "outK"; "vOUT"; "vRFX"; "NXC"; "km_regs"; "ptr_facts"; "arrK"; "cut_fregs"; "km_facts"; "O_p2d"; "O_rfx"; "O_stk"; "O_w"; "R2_P"; "inv_r"; "objs0"; "r2_Lr"; "O_nxt"; "O_prv"; "V_DEPTH"; "base_facts"; "r2_Lfan"; "std_regs"; "two47"; "Pre_r2"; "cutpcs"; "cuts1"; "ptr_rng"; "r2_Lc"; "r2_Lf"; "r2_Lg"; "r2_Li"; "r2_Lm"; "r2_Lx"; "FUEL_r2"; "Posts_r2"; "exits1"; "r2_La"; "r2_Ls"; "r2_ret"; "two20"; "vW"; "Kfan_gen"; "Ks"; "O_out"; "P_ret"; "fcallee_saved"; "flds3"; "hint12"; "idx_tmpl"; "inv_s"; "r2_consts"; "r2_entry"; "r2_tab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs"; "pN"; "poutK"; "pSCR"; "PG_P"; "pOUT"; "pPTS"; "pobjs"; "pg_entry"; "pNXT"; "pPRV"; "pg_base_facts"; "pRFX"; "A16"; "FUEL_pg"; "pcuts"; "pexits"; "pg_Lbbp"; "pg_Lcm"; "pg_Lext"; "pg_Lfin"; "pg_Lnw"; "pg_Lproj"; "pg_cutpcs2"; "pg_ret"; "F_cap"; "F_scr"; "Kext"; "Klat"; "O_desc"; "O_pbelow"; "O_pnxt"; "O_pout"; "O_pp2d"; "O_pprv"; "O_prfx"; "O_pstk"; "O_pts"; "O_res"; "Pre_pg"; "pg_cutpcs"; "pg_run2d"; "pg_scale2d"; "ptmpl3"; "@Corelib.Numbers.BinNums"; "Z"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingCfg"; "rnode"; "mkRN"; "mkRG"; "rghost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vdir"; "Vdown"; "vnode"; "Vup"; "check_cfg"; "mkVN"; "check_cut"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "setregs"; "post_regs"; "cut_regs"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d_ex_defs"; "eobjs"; "NXT"; "PRV"; "RGm"; "lexM"; "noring"; "R182"; "mg_facts"; "k3"; "out3"; "eqs_c"; "R182m1"; "REM_prv"; "RGfull"; "cellN"; "cellP"; "EKa"; "EKs"; "EPre"; "E_ret"; "K_c"; "K_c2"; "K_f"; "K_f0"; "K_fan"; "K_g"; "K_g2"; "K_gb"; "K_i"; "K_m"; "K_r"; "K_x"; "LN"; "LP"; "O_outE"; "SEL_nxt"; "X_c2"; "X_g2"; "X_r"; "X_r0"; "X_rf"; "gf_c2"; "gf_f"; "gf_g"; "gf_g2"; "gf_i"; "gf_m"; "gf_x"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs.PS2"; "pcut"; "P"; "pobjs2"; "n3"; "pre2"; "xr3"; "pstk_cells"; "res0"; "out3_cells"; "w_cells"; "xr4"; "xr5"; "E_r2"; "E_sc3"; "E_sc4"; "K29c"; "K318"; "K34c"; "K3dc"; "K4a"; "K4b"; "Kbbp"; "Kcm"; "Kext"; "Kfin"; "Klat"; "Knw"; "Kproj"; "P_inv";
"P_ok"; "pfregs"; "pre1"; "pregs"; "psp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingBuf"; "IX4"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "sub"; "opp"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d.S2"; "std_regs"; "km_objs"; "km_facts"; "km_regs"; "hint12"; "outK"; "Ea"; "Er"; "Kc"; "Kf"; "Kfan"; "Kfan_gen"; "Kg"; "Ki"; "Km"; "Kx"; "O_out_post"; "flds3"; "inv_r"; "tmpl3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_scale2d"; "v121"; "vN"; "Pre_sc"; "v120"; "vP"; "O_pts"; "base_facts"; "C1"; "FUEL_sc"; "P_sc"; "Posts_sc"; "cutpcs_sc"; "cuts_sc"; "NXC"; "NXP"; "cut_fregs"; "exits_sc"; "fcallee_saved"; "post_fregs"; "sc_state"; "szb"; "two31"; "two47"; "vcuts_sc"; "vexits_sc"; "@Corelib.Init.Nat"; "add"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "mkLeaf"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d_ex_defs.E"; "kgb_facts"; "xr_regs"; "ecutsG"; "kc_facts"; "kr_regs"; "xc2_regs"; "xg2_regs"; "EKa"; "EKs"; "EPre"; "E_ret"; "K_c"; "K_c2"; "K_f"; "K_f0"; "K_fan"; "K_g"; "K_g2"; "K_gb"; "K_i"; "K_m"; "K_r"; "K_x"; "X_c2"; "X_g2"; "X_r"; "X_r0"; "X_rf"; "eexits"; "gf_c2"; "gf_f"; "gf_g"; "gf_g2"; "gf_i"; "gf_m"; "gf_x"; "kgb_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d.S"; "objs0"; "NXC"; "body_fregs"; "body_regs"; "cut"; "inv_s"; "rsp"; "stk_cells"; "@Stdlib.Lists.List"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue"; "check_ecfgI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "vTop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d_ex_defs.N"; "N_Eret"; "N_Ka"; "N_Kc"; "N_Kc2"; "N_Kf"; "N_Kf0"; "N_Kfan"; "N_Kg"; "N_Kg2"; "N_Kgb"; "N_Ki"; "N_Km"; "N_Kr"; "N_Ks"; "N_Kx"; "N_Pre"; "N_Xc2"; "N_Xg2"; "N_Xr"; "N_Xr0"; "N_Xrf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_scale2d.TessScale2dAddr"; "sc_L1"; "sc_entry"; "sc_ret"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingBuf.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.Ring.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingCfg.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_tess_run2d.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition fcallee_saved (r : nat) : bool :=
  match r with 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition cut_fregs : list sv := ltac2:(tb__ "0|0|
S13bS1SeS1S9SeL_;S6dR1A1S11S145S13aU3cR1A2A1A1S11S145S13aU8cR1A2A1A1X9x2Lr;S13cU0U20A2A4").

Record r2_consts := R2C { r2_entry : Z; r2_ret : Z;
  r2_Ls : Z;
  r2_La : Z;
  r2_Lr : Z;
  r2_Lf : Z;
  r2_Lm : Z;
  r2_Li : Z;
  r2_Lfan : Z;
  r2_Lc : Z;
  r2_Lg : Z;
  r2_Lx : Z;
  r2_tab : Z   }.
Definition R2_P := R2C 0x1e85c 0x1f1d8 0x1e918 0x1e9ac 0x1ea40 0x1eac4 0x1eba4 0x1ed88 0x1f158 0x1ec5c 0x1ee18 0x1f0f0 0x108e0.

Definition vW : sv := SVar 12.  Definition vN : sv := SVar 13.  Definition vOUT : sv := SVar 14.
Definition vP2D : sv := SVar 15. Definition vNXT : sv := SVar 16. Definition vPRV : sv := SVar 17. Definition vRFX : sv := SVar 18.
Definition V_DEPTH : positive := 19%positive.

Definition O_stk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1bS11PaA1S11S52A1SfZ0A1Vcells;S19A5").
Definition O_w : sobj := ltac2:(tb__ "0|2|
S1bS68SfZ0A1M0SfZ20A1S0S13S16G0Z8M1S3eA3S0S13S16SfG1A1G1S3dA3S0S13S16SfZ10A1G1S3cA3S0S13S16SfZ18A1G1S41A3S3S13A1A3A3A3A3S19A5").
Definition O_p2d : sobj := ltac2:(tb__ "0|0|
S1bS3eSfZ0A1S12S2eS39SfZ4A1A3S3S13A1S19A5").
Definition idx_tmpl : list tfact := ltac2:(tb__ "0|0|
S0S20S23S8U0S6S4S9Sa1A2A1S39A4S3S20A1A3").
Definition O_nxt (d : odefault) : sobj := ltac2:(tb__ "0|0|
S1bS3dSfZ0A1S12S2eS39SfZ2A1A3S3S13A1Vd;A5").
Definition O_prv (d : odefault) : sobj := ltac2:(tb__ "0|0|
S1bS3cSfZ0A1S12S2eS39SfZ2A1A3S3S13A1Vd;A5").
Definition arrK (k : sv) : odefault := ltac2:(tb__ "0|2|
S24Z4M0Vk;S0S4Sa0Sa0A2M1S2Sa0Sa0Z0G0A4S3G1A1A3S70A4").
Definition O_rfx : sobj := ltac2:(tb__ "0|0|
S1bS41SfZ0A1S12S32S12S2dS39SfZ7A1A3SfZ3A1A3S3S13A1S19A5").
Definition O_out (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1bS40SfZ0A1S1cS2fS12S2dS39SfN2A1A3SfZcA1A3Vcells;S19A5").

Definition two20 : Z := 2 ^ 20. Definition two47 : Z := 2 ^ 47.
Definition ptr_facts (i : positive) (al : Z) : list sprop := ltac2:(tb__ "0|1|
S0S10S15SfZ1000A1S11Vi;A1M0A2S0S10S15G0SfS56A1A2S0S10S22Vi;Val;A2S3S10A1A3A3A3").
Definition ptr_rng (i : positive) : list sprop := ltac2:(tb__ "0|1|
S0S10S15SfZ1000A1S11Vi;A1M0A2S0S10S15G0SfS56A1A2S3S10A1A3A3").
Definition base_facts : list sprop := ltac2:(tb__ "0|4|
S5S10S0S10S15SfZ5A1S39A2S0S10S15S39SfS67A1A2S0S10S1aS34SfN50A1S11S52A1M0A3S0S10S1aS34G0SfS10bS108Z2Z28A2A1A1A3S0S10S22PaM1Z4M2A2S0S10S15SfZ10000A1S11G1A1M3A2S0S10S15G3SfS56A1A2S3S10A1A3A3A3A3A3A3A3S5S10S44PcZ3A2S5S10S44PeG2A2S5S10S44PfG2A2S5S10S5aP10A1S5S10S5aP11A1S5aP12A1A3A3A3A3A3A3").

Section S. Variable c : r2_consts.
Definition objs0 (dn dp : odefault) (outc : list cell) (stkc : list cell) : list sobj := ltac2:(tb__ "0|0|
S0S17S4aVstkc;A1S0S17S4bS0S17S48S0S17S50Vdn;A1S0S17S51Vdp;A1S0S17S49S0S17S6bVoutc;A1S3S17A1A3A3A3A3A3A3A3").
Definition Pre_r2 : sstate := ltac2:(tb__ "0|2|
S1fS73Vc;A1SafSb3S0S4S1SeA2M0S2S1SeUdSfZ0A1A4S3G0A1A3A2Sb2S1eS6SeA1S16eS19S19S3S13A1M1G1A4S53SaeS7A9").

Definition stk_cells : list cell := ltac2:(tb__ "0|1|
S0S13S16SfN8A1Z8M0S11P1cA1A3S0S13S16SfN10A1G0S11P1dA1A3S0S13S16SfN18A1G0S11P26A1A3S0S13S16SfN20A1G0S11P27A1A3S0S13S16SfN28A1G0S11P28A1A3S0S13S16SfN30A1G0S11P29A1A3S0S13S16SfN38A1G0S11P2aA1A3S0S13S16SfN40A1G0S11P44A1A3S0S13S16SfN48A1G0S11P45A1A3S3S13A1A3A3A3A3A3A3A3A3A3").
Definition rsp : sv := SAlu ALU_ADD (SVar 10) (SLit (-80)).

Definition body_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
SafSb1SaeA1S5S4S1SeA2M0S0G0S2S1SeU2S174A4S0G0S2S1SeU8S11P84A1A4S0G0S2S1SeU9S11P85A1A4S0G0S2S1SeU12S11P86A1A4S0G0S2S1SeU13S11P87A1A4S0G0S2S1SeU14S11P88A1A4S0G0S2S1SeU15S11P89A1A4S0G0S2S1SeU16S11P8aA1A4S0G0S2S1SeUaS68A4S3G0A1A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition body_fregs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
SafSafS46S0S4S1SeA2M0S2S1SeU8S11PacA1A4S0G0S2S1SeU9S11PadA1A4S3G0A1A3A3A2Vl;A2").
Definition NXC : positive := 200%positive.
Definition cut (pc : Z) (regs : list (nat * sv)) (fregs : list (nat * sv)) (objs : list sobj) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S1fVpc;S171Vregs;A1S170Vfregs;A1S1eS6SeA1Vobjs;S5S10Vfacts;S53A3S16fS7A9").

Definition inv_s : list sprop := ltac2:(tb__ "0|5|
S0S10S15SfZ1M0A1M1S11P78A1M2A2S0S10S15G2S39A2S0S10S1dS12S2dS11P7aM3A1M4S12S2eG2G1A3A3S12S2eS39G1A3A2S0S10S22G3G0A2S0S10S15G4SfZ400000A1A2S3S10A1A3A3A3A3A3").
Definition Ks : sstate := ltac2:(tb__ "0|3|
S172S65Vc;A1S0S4S1SeA2M0S2S1SeUeS3eA4S0G0S2S1SeUdS39A4S0G0S2S1SeUbS39A4S0G0S2S1SeUcS40A4S0G0S2S1SeUfM1S12S2dSfZ1A1S11P7aA1A3A4S0G0S2S1SeU10S11P78A1A4S3G0A1M2A3A3A3A3A3A3S0G0S2S1SeG1SfZ0A1A4G2A3S16eS19S19S3S13A1S175A4S173A5").
Definition cutpcs : list Z := ltac2:(tb__ "0|0|
S0Sa0S65Vc;A1S0Sa0S64Vc;A1S0Sa0S4fVc;A1S0Sa0S5cVc;A1S0Sa0S5fVc;A1S0Sa0S5eVc;A1S0Sa0S54Vc;A1S0Sa0S5bVc;A1S0Sa0S5dVc;A1S0Sa0S60Vc;A1S3Sa0A1A3A3A3A3A3A3A3A3A3A3").
End S.

Section S2. Variable c : r2_consts.
Definition RB8 : sv := ltac2:(tb__ "0|0|
S12S32S12S2dS39SfZ7A1A3SfZ3A1A3").
Definition flds3 : list (Z * Z) := ltac2:(tb__ "0|2|
S0S4Sa0Sa0A2M0S2Sa0Sa0Z0Z4M1A4S0G0S2Sa0Sa0G1G1A4S0G0S2Sa0Sa0Z8G1A4S3G0A1A3A3A3").
Definition tmpl3 : list tfact := ltac2:(tb__ "0|1|
S0S20S23S8U0S6S4S9Sa1A2A1M0S39A4S0S20S23S8U1G0S39A4S0S20S23S8U2G0S39A4S3S20A1A3A3A3").
Definition outK (k : sv) : odefault := ltac2:(tb__ "0|0|
S24ZcVk;S11eS120A4").
Definition std_regs : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S1SeA2M0S2S1SeUdS39A4S0G0S2S1SeUbS39A4S0G0S2S1SeUcS40A4S3G0A1A3A3A3").

Definition Ka_gen (extra : list sprop) : sstate := ltac2:(tb__ "0|2|
S3aS64Vc;A1S5S4S1SeA2M0S10dS0G0S2S1SeUeS3eA4S0G0S2S1SeUfS12S2dSfZ1A1S11P7aA1A3A4S0G0S2S1SeU10S11P78A1A4S3G0A1M1A3A3A3A3G1S4eS19S19S3S13A1S3bA4S5S10Vextra;S71A3A5").
Definition Ea : sstate := Ka_gen [].

Definition inv_r : list sprop := ltac2:(tb__ "0|2|
S0S10S1dS12S2dS11P7cA1M0S11P7bA1M1A3S39A2S0S10S15SfZ1A1G0A2S0S10S15G0S39A2S0S10S18G1S39A2S3S10A1A3A3A3A3").
Definition Kr_gen (extra : list sprop) : sstate := ltac2:(tb__ "0|5|
S3aS4fVc;A1S5S4S1SeA2M0S10dS0G0S2S1SeUeS12S2dS3dS12S2eS11P7bA1M1SfZ2A1A3M2A3A4S0G0S2S1SeUfS12S2dS3cG2A3A4S0G0S2S1SeU10S12S2dS12S2dS39SfN1A1A3G1A3A4S0G0S2S1SeU11S12S2dSfZ1A1G1A3A4S0G0S2S1SeU5S11P7cA1A4S3G0A1M3A3A3A3A3A3A3G3S4eS45G1A1M4G4S3S13A1S3bA4S5S10Vextra;S11fA3A5").
Definition Er : sstate := Kr_gen [].

Definition Kf_gen (extra : list sprop) : sstate := ltac2:(tb__ "0|4|
S3aS5cVc;A1S5S4S1SeA2M0S10dS0G0S2S1SeU10S11P7dA1M1A4S0G0S2S1SeU11SfZ1A1A4S3G0A1M2A3A3A3G2S4eS45S39A1M3G3S3S13A1S3bA4S5S10Vextra;S0S10S18G1S39A2S3S10A1A3A3A5").
Definition Kf : sstate := Kf_gen [].

Definition hint12 (k : sv) : sprop := ltac2:(tb__ "0|1|
S1dS1cS2fVk;SfZcA1A3M0G0A2").
Definition Kfan_gen (extra : list sprop) : sstate := ltac2:(tb__ "0|5|
S3aS54Vc;A1S5S4S1SeA2M0S10dS0G0S2S1SeUaS12S2dSfZ2A1S11P7eA1M1A3A4S0G0S2S1SeUdS12S2dS12S2dS12S2eG1SfZ1A1M2A3G1A3G2A3A4S3G0A1M3A3A3A3G3S5S17S4eS45S39A1M4G4S3S13A1S3bA4S3S17A1A3S5S10Vextra;S0S10S111G1A1S0S10S15S12S2dSfZ3A1G1A3S39A2S0S10S15G1S39A2S3S10A1A3A3A3A3A5").
Definition Kfan : sstate := ltac2:(tb__ "0|2|
S1fS54Vc;A1S2aS118S3S10A1A1M0A1S28G0A1S1eS6SeA1S0S17S4aS3bA1S0S17S4bS0S17S48S0S17S50S45S39A1M1A1S0S17S51G1A1S0S17S49S0S17S1bS40SfZ0A1S1cS2fS12S2dS39SfN2A1A3SfZcA1A3S3S13A1S112S11P7eA1A1A5S3S17A1A3A3A3A3A3A3A3S27G0A1S42S7A9").

Definition km_regs : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S1SeA2M0S10dS0G0S2S1SeU5S11Pb4A1A4S0G0S2S1SeUeS11Pb5A1A4S0G0S2S1SeUbS11Pb6A1A4S0G0S2S1SeU8S11Pb7A1A4S0G0S2S1SeU1fS11Pb8A1A4S0G0S2S1SeUdS11Pb9A1A4S0G0S2S1SeUfSfS74Vc;A1A1A4S0G0S2S1SeU10SfZ1A1A4S0G0S2S1SeU11SfZ3A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3").
Definition km_facts : list sprop := ltac2:(tb__ "0|2|
S0S10S18S11Pb4A1S39A2S0S10S1dS12S2dS11Pb5A1M0S11Pb6A1M1A3S39A2S0S10S1aS37SfZ3A1G1A3S0S10S15G1S39A2S0S10S15G0S39A2S0S10S111G0A1S3S10A1A3A3A3A3A3A3").
Definition km_objs (k : sv) : list sobj := ltac2:(tb__ "0|1|
S0S17S4aS3bA1S0S17S4bS0S17S48S0S17S50S45S39A1M0A1S0S17S51G0A1S0S17S49S0S17S1bS40SfZ0A1S1cS2fS12S2dS39SfN2A1A3SfZcA1A3S3S13A1S112Vk;A1A5S3S17A1A3A3A3A3A3A3A3").
Definition Km : sstate := ltac2:(tb__ "0|0|
S3aS5fVc;A1S110S3S4S1SeA2A1S10eS11Pb5A1A1S10fA5").

Definition Kc : sstate := ltac2:(tb__ "0|4|
S3aS5bVc;A1S5S4S1SeA2M0S110S0G0S2S1SeU6S11PbaA1M1A4S0G0S2S1SeU9S11PbbA1M2A4S0G0S2S1SeU7S3eA4S0G0S2S1SeU12S41A4S0G0S2S1SeU1cS12S2eS12S2eG1SfZ1A1A3SfZ20A1A3A4S0G0S2S1SeU1dS3cA4S0G0S2S1SeU1eS3dA4S3G0A1M3A3A3A3A3A3A3A3A3G3S10eS11Pb5A1A1S5S10S10fS0S10S18G1S39A2S0S10S18G2S39A2S3S10A1A3A3A3A5").

Definition Kg : sstate := ltac2:(tb__ "0|3|
S3aS5dVc;A1S5S4S1SeA2M0S110S0G0S2S1SeU6S11PbaA1M1A4S0G0S2S1SeU7S3eA4S0G0S2S1SeU1dS3cA4S0G0S2S1SeU1eS3dA4S3G0A1M2A3A3A3A3A3G2S10eS11Pb5A1A1S5S10S10fS0S10S18G1S39A2S3S10A1A3A3A5").

Definition Ki : sstate := ltac2:(tb__ "0|5|
S3aS5eVc;A1S5S4S1SeA2M0S110S0G0S2S1SeU6S11PbaA1M1A4S0G0S2S1SeU9S11PbbA1M2A4S0G0S2S1SeU13G2A4S0G0S2S1SeU14S11PbcA1M3A4S0G0S2S1SeU12S41A4S0G0S2S1SeU7S3eA4S0G0S2S1SeU1dS3cA4S0G0S2S1SeU1eS3dA4S0G0S2S1SeU1cS12S2eS12S2eG1SfZ1A1A3SfZ20A1A3A4S3G0A1M4A3A3A3A3A3A3A3A3A3A3G4S10eS11Pb5A1A1S5S10S10fS0S10S18G1S39A2S0S10S18G2S39A2S0S10S18G3S39A2S3S10A1A3A3A3A3A5").

Definition Kx : sstate := ltac2:(tb__ "0|6|
S3aS60Vc;A1S5S4S1SeA2M0S10dS0G0S2S1SeU5S11Pb4A1M1A4S0G0S2S1SeUeS11Pb5A1M2A4S0G0S2S1SeUbS11Pb6A1M3A4S0G0S2S1SeUdS11Pb9A1A4S3G0A1M4A3A3A3A3A3G4S10eG2A1S0S10S18G1S39A2S0S10S1dS12S2dG2G3A3S39A2S0S10S15G3SfZ3A1M5A2S0S10S15G5G3A2S0S10S15G2S39A2S0S10S111G2A1S3S10A1A3A3A3A3A3A3A5").

Definition O_out_post : sobj := ltac2:(tb__ "0|1|
S1bS40SfZ0A1S1cS2fS12S2dS39SfN2A1A3M0SfZcA1A3S3S13A1S112G0A1A5").
Definition P_ret : sstate := ltac2:(tb__ "0|1|
S1fS66Vc;A1Sb0SaeA1S46S1eS6SeA1S0S17S4aS3S13A1A1S0S17S4bS0S17S48S0S17S50S45S39A1M0A1S0S17S51G0A1S0S17S49S0S17S11dS3S17A1A3A3A3A3A3A3A3S53S42S7A9").
Definition cuts1 : list sstate := ltac2:(tb__ "0|0|
S0S14S57Vc;A1S0S14S6aVc;A1S0S14S113S0S14S114S0S14S116S0S14S117S0S14S11bS0S14S11aS0S14S115S0S14S119S0S14S11cS3S14A1A3A3A3A3A3A3A3A3A3A3A3").
Definition exits1 : list sstate := [P_ret].
End S2.

Definition FUEL_r2 : nat := 500%nat.
Definition Posts_r2 (c : r2_consts) : list leaf := ltac2:(tb__ "0|0|
S0S142S144S6cVc;A1S143A2S3S142A1A3").

Lemma cuts1_strict : ltac2:(tb__ "0|0|
S72S10cS9S176S14S29S59R1A1A3S7A3Fc;").
Proof. reflexivity. Qed.

Section Summary.
  Variable c : r2_consts.
  Hypothesis check_r2 : ltac2:(tb__ "0|0|
S10cS9SaaSb4S61S58Vc;A1SaeS59Vc;A1S63Vc;A1A6S8A3").

  Theorem run2d_sum_gen : ltac2:(tb__ "0|0|
S147OF_;SbS13eA1S13dOF_;F_;S25S141Sb4R3R2A3S146Sb4R4S140Sb4R3S57Vc;A1R2A4S13fSb4R3SaeR2S62Vc;A1A5A4F_;Frho;FK;Fok;").
  Proof using check_r2.
    intros ok K rho Hok.
    apply (cfg_sound segs FUEL_r2 (cutpcs c) NF (cuts1 c) (exits1 c)
             (fun rho' => agree_below NF rho rho') ok K (LQ segs K NF rho (Posts_r2 c)) Hok).
    - rewrite cuts1_strict. intros; discriminate.
    - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
    - exact check_r2.
    - intros E rhoE HinE HagE. destruct HinE as [<-|[]].
      apply exit_post; [left; reflexivity | exact HagE].
    - left; reflexivity.
    - apply agree_below_refl.
  Qed.
End Summary.

Lemma check_r2_P : ltac2:(tb__ "0|0|
S10cS9SaaSb4S61S58S4cA1SaeS59S4cA1S63S4cA1A6S8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem run2d_sum : ltac2:(tb__ "0|0|
S147OF_;SbS13eA1S13dOF_;F_;S25S141Sb4R3R2A3S146Sb4R4S140Sb4R3S57S4cA1R2A4S13fSb4R3SaeR2S62S4cA1A5A4F_;Frho;FK;Fok;").
Proof. exact (run2d_sum_gen R2_P check_r2_P). Qed.
End Lib_tess_run2d.

Module Lib_tess_scale2d.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module TessScale2dAddr.
  Definition sc_entry : Z := 0x1e7ac.
  Definition sc_L1 : Z := 0x1e7d4.
  Definition sc_ret : Z := 0x1e858.
End TessScale2dAddr.
Import TessScale2dAddr.

Definition FUEL_sc : nat := 300%nat.

Definition fcallee_saved (r : nat) : bool :=
  match r with 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition cut_fregs : list sv := ltac2:(tb__ "0|0|
S13bS1SeS1S9SeL_;S132R1A1S11S145S13aU3cR1A2A1A1S11S145S13aU8cR1A2A1A1X9x2Lr;S13cU0U20A2A4").
Definition post_fregs : list sv := cut_fregs.
Definition NXC : positive := 175%positive.
Definition NXP : positive := 180%positive.

Definition vP : sv := SVar 12.
Definition vN : sv := SVar 13.
Definition szb : sv := ltac2:(tb__ "0|0|
S12S2eS122SfZ4A1A3").
Definition two31 : Z := 2 ^ 31.
Definition two47 : Z := 2 ^ 47.
Definition base_facts : list sprop := ltac2:(tb__ "0|1|
S0S10S15SfZ1A1M0S122A2S0S10S15S122SfS136A1A2S0S10S15G0S125A2S0S10S15S125SfS137A1A2S0S10S22PcZ3A2S3S10A1A3A3A3A3A3").
Definition O_pts : sobj := ltac2:(tb__ "0|0|
S1bS125SfZ0A1S135S3S13A1S19A5").

Definition Pre_sc : sstate := ltac2:(tb__ "0|0|
S1fS18fSb3Sb2S1eS6SeA1S0S17S126S3S17A1A3S127SaeS7A9").

Definition v120 : sv := SVar 120.
Definition v121 : sv := SVar 121.
Definition inv : list sprop := ltac2:(tb__ "0|1|
S0S10S15SfZ1A1M0S124A2S0S10S15S124S122A2S0S10S1dS12S2dS121S12S2eS124G0A3A3S12S2dS12S2eS122G0A3G0A3A2S0S10S15G0S121A2S0S10S15S121SfZffffffffA1A2S3S10A1A3A3A3A3A3").

Definition sc_state (pc : Z) (regs : list (nat * sv)) (fregs : list (nat * sv)) (facts : list sprop) : sstate := ltac2:(tb__ "0|1|
S1fVpc;SafSb1SaeA1S0S4S1SeA2M0S2S1SeUaS125A4Vregs;A3A2SafS130S0G0S2S1SeUfSfZ0A1A4Vfregs;A3A2S1eS6SeA1S0S17S126S3S17A1A3S5S10Vfacts;S127A3S12eS7A9").

Definition C1_0 : sstate := ltac2:(tb__ "0|2|
S134S18eS0S4S1SeA2M0S2S1SeUbS124A4S0G0S2S1SeUcS121A4S3G0A1M1A3A3G1S3S10A1A4").
Definition C1 : sstate := add_facts inv C1_0.

Definition P_sc : sstate := ltac2:(tb__ "0|0|
S1fS190Sb0SaeA1S133S1eS6SeA1S0S17S126S3S17A1A3S127S12fS7A9").
Definition Posts_sc : list leaf := ltac2:(tb__ "0|0|
S0S142S144S12aS143A2S3S142A1A3").

Definition cuts_sc : list sstate := ltac2:(tb__ "0|0|
S0S14S123S0S14S128S3S14A1A3A3").
Definition exits_sc : list sstate := [P_sc].
Definition cutpcs_sc : list Z := [sc_L1].

Lemma check_sc : ltac2:(tb__ "0|0|
S10cS9SaaSb4S129S12cSaeS12dS131A6S8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cuts_sc_strict : ltac2:(tb__ "0|0|
S10cS9S176S14S29S12dA3S7A3").
Proof. vm_compute. reflexivity. Qed.

Theorem scale2d_sum : ltac2:(tb__ "0|0|
S147OF_;SbS13eA1S13dOF_;F_;S25S141Sb4R3R2A3S146Sb4R4S140Sb4R3S123R2A4S13fSb4R3SaeR2S12bA5A4F_;Frho;FK;Fok;").
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segs FUEL_sc cutpcs_sc NF cuts_sc exits_sc
           (fun rho' => agree_below NF rho rho') ok K (LQ segs K NF rho Posts_sc) Hok).
  - rewrite cuts_sc_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_sc.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[]]; revert HagE. apply exit_post. in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition vcuts_sc : list vnode := ltac2:(tb__ "0|0|
S0Sa8SabS123Z1eSfZ0A1A3S0Sa8SabS128Z14S121A3S3Sa8A1A3A3").
Definition vexits_sc : list vnode := ltac2:(tb__ "0|0|
S0Sa8SabS12aZ1S178A3S3Sa8A1A3").

Lemma echeck_sc : ltac2:(tb__ "0|0|
S10cS9S177Sb4S129S12cSaeS138S139A6S8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem scale2d_sum_ex : ltac2:(tb__ "0|0|
SbS13eA1S13dOF_;F_;S25S148Sb4S140Sb4R2S123R1A4S13fSb4R2SaeR1S12bA5A3Frho;FK;").
Proof.
  intros K rho.
  change Pre_sc with (vn_state (mkVN Pre_sc 30 (SLit 0))).
  apply (cfg_complete_autoI segs FUEL_sc cutpcs_sc NF vcuts_sc vexits_sc
           (fun rho' => agree_below NF rho rho') K (LQ segs K NF rho Posts_sc)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_sc.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[]]; revert HgE.
    apply (eexit_post_I0 segs K NF rho vcuts_sc Posts_sc (mkVN P_sc 1 vTop)). in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
End Lib_tess_scale2d.

Module Lib_tess_polygon_defs.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record pg_consts := PGC { pg_entry : Z; pg_ret : Z;
  pg_Lfin : Z; pg_Lcm : Z; pg_Lnw : Z; pg_Lext : Z; pg_Lproj : Z; pg_Lbb : Z; pg_Lbbp : Z;
  pg_scale2d : Z; pg_run2d : Z }.
Definition PG_P := PGC 0x1dd28 0x1e784 0x1ddcc 0x1df18 0x1df64 0x1e0ac 0x1e338 0x1e1a4 0x1e1a4 0x1e7ac 0x1e85c.

Definition pN : sv := SVar 14. Definition pPTS : sv := SVar 15. Definition pOUT : sv := SVar 16. Definition pSCR : sv := SVar 17.
Definition A16 : sv := ltac2:(tb__ "0|0|
S12S33S12S2dS12S2eS75SfZ2A1A3SfZfA1A3SfZfffffffffffffff0A1A3").
Definition pNXT : sv := ltac2:(tb__ "0|0|
S12S2dS77S12S2eS75SfZ4A1A3A3").
Definition pPRV : sv := ltac2:(tb__ "0|0|
S12S2dS7dS81A3").
Definition pRFX : sv := ltac2:(tb__ "0|0|
S12S2dS7eS81A3").

Definition ptmpl3 : list tfact := ltac2:(tb__ "0|1|
S0S20S23S8U0S6S4S9Sa1A2A1M0S75A4S0S20S23S8U1G0S75A4S0S20S23S8U2G0S75A4S3S20A1A3A3A3").
Definition poutK (k : sv) : odefault := ltac2:(tb__ "0|0|
S24ZcVk;S6eS9fA4").
Definition O_desc : sobj := ltac2:(tb__ "0|3|
S1bS11PcA1SfZ0A1M0SfZ48A1S0S13S16G0Z8M1S7aA3S0S13S16SfG1A1Z4M2S75A3S0S13S16SfZ10A1G1G0A3S0S13S16SfZ18A1G2G0A3S0S13S16SfZ20A1G1S79A3S0S13S16SfZ28A1G2S11P14A1A3S0S13S16SfZ30A1G1S77A3S0S13S16SfZ38A1G1S11P12A1A3S0S13S16SfZ40A1G1G0A3S3S13A1A3A3A3A3A3A3A3A3A3S19A5").
Definition O_res (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1bS11PdA1SfZ0A1SfZ14A1Vcells;S19A5").

Definition O_pstk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1bS11PaA1SfN8c0A1SfZ0A1Vcells;S19A5").
Definition O_pbelow : sobj := ltac2:(tb__ "0|0|
S1bS12S2dS11PaA1SfN8c0A1A3S11S52A1SfZ0A1S3S13A1S19A5").
Definition O_pts : sobj := ltac2:(tb__ "0|0|
S1bS7aSfZ0A1S1cS2fS75SfZcA1A3S3S13A1S19A5").
Definition O_pout (d : odefault) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1bS79SfZ0A1S1cS2fS12S2dS75SfN2A1A3SfZcA1A3Vcells;Vd;A5").
Definition O_pp2d : sobj := ltac2:(tb__ "0|0|
S1bS77SfZ0A1S12S2eS75SfZ4A1A3S3S13A1S19A5").
Definition O_pnxt (d : odefault) : sobj := ltac2:(tb__ "0|0|
S1bS7dSfZ0A1S12S2eS75SfZ2A1A3S3S13A1Vd;A5").
Definition O_pprv (d : odefault) : sobj := ltac2:(tb__ "0|0|
S1bS7eSfZ0A1S12S2eS75SfZ2A1A3S3S13A1Vd;A5").
Definition O_prfx : sobj := ltac2:(tb__ "0|0|
S1bS80SfZ0A1S12S32S12S2dS75SfZ7A1A3SfZ3A1A3S3S13A1S19A5").

Definition F_cap : sprop := ltac2:(tb__ "0|1|
S1aS35S2bS8Q20S11P14A1A3S12S2dS12S2eS12S2dS75SfN2A1A3M0SfZ1A1A3G0A3A3").
Definition F_scr : sprop := ltac2:(tb__ "0|1|
S1aS35S11P12A1S12S2dS12S2dS12S33S12S2dS12S2eS75SfZ3A1M0A3SfZ1eA1A3SfZffffffffffffffe0A1A3S12S2eS75SfZ4A1A3A3S12S33S12S2dS12S32S12S2dS75SfZ7A1A3G0A3SfZfA1A3SfZfffffffffffffff0A1A3A3A3").
Definition pg_base_facts : list sprop := ltac2:(tb__ "0|d|
S5S10S0S10S15SfZ3M0A1S75A2S0S10S15S75SfS67A1A2S0S10S1aS34SfN50A1S11S52A1M1A3S0S10S1aS34G1SfS10bS108Z2M2Z28A2A1A1A3S0S10S22PaM3Z4M4A2S0S10S15SfZ20000A1S11G3A1M5A2S0S10S15G5SfS56A1M6A2S0S10S21S1aS30S7aSfZ0A1M7A3A1S0S10S21S1aS30S79G7A3A1S0S10S21S1aS30S77G7A3A1S0S10S8dS0S10S8eS3S10A1M8A3A3A3A3A3A3A3A3A3A3A3A3S5S10S44PcG0A2S5S10S44PdG0A2S5S10S44PfG2A2S5S10S44P10G4A2S5S10S0S10S15SfZ1000A1S11P11M9A1MaA2S0S10S15GaSfZ7fffff800000A1MbA2S0S10S15S11P12A1McSfS108G2Z1aA2A1A2S0S10S15S12S2dGaGcA3GbA2S0S10S22G9G4A2G8A3A3A3A3A3S0S10S15S7dG6A2S0S10S15S7eG6A2S0S10S15S80G6A2G8A3A3A3A3A3A3A3A3A3").

Definition pobjs (dout dn dp : odefault) (outc resc stkc : list cell) : list sobj := ltac2:(tb__ "0|0|
S0S17S98Vstkc;A1S0S17S92S0S17S91S0S17S9aVresc;A1S0S17S99S0S17S94Vdout;Voutc;A2S0S17S95S0S17S93Vdn;A1S0S17S96Vdp;A1S0S17S97S3S17A1A3A3A3A3A3A3A3A3A3A3").

Section PS. Variable c : pg_consts.

Definition Pre_pg (extra : list sprop) : sstate := ltac2:(tb__ "0|2|
S1fS7cVc;A1SafSb3S0S4S1SeA2M0S2S1SeUcS11P16A1A4S3G0A1A3A2Sb2S1eS6SeA1S7bS76SfZ0A1A1S19S19S3S13A1M1G1G1A6S5S10Vextra;S7fA3SaeS7A9").
Definition pg_cutpcs : list Z := ltac2:(tb__ "0|0|
S0Sa0S88Vc;A1S0Sa0S86Vc;A1S0Sa0S89Vc;A1S0Sa0S87Vc;A1S0Sa0S8aVc;A1S0Sa0S85Vc;A1S0Sa0S9eVc;A1S0Sa0S9dVc;A1S0Sa0Z1e3d4S3Sa0A1A3A3A3A3A3A3A3A3A3").
End PS.

Section PS2. Variable c : pg_consts.
Definition psp : sv := SAlu ALU_ADD (SVar 10) (SLit (-2240)).

Definition pstk_cells : list cell := ltac2:(tb__ "0|1|
S0S13S16SfN8A1Z8M0S11PbA1A3S0S13S16SfN10A1G0S11P1cA1A3S0S13S16SfN18A1G0S11P1dA1A3S0S13S16SfN20A1G0S11P26A1A3S0S13S16SfN28A1G0S11P27A1A3S0S13S16SfN30A1G0S11P28A1A3S0S13S16SfN38A1G0S11P29A1A3S0S13S16SfN40A1G0S11P2aA1A3S0S13S16SfN48A1G0S11P2bA1A3S0S13S16SfN50A1G0S11P2cA1A3S0S13S16SfN58A1G0S11P2dA1A3S0S13S16SfN60A1G0S11P2eA1A3S0S13S16SfN68A1G0S11P2fA1A3S0S13S16SfN70A1G0S11P44A1A3S0S13S16SfN78A1G0S11P45A1A3S0S13S16SfN80A1G0S11P4eA1A3S3S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition pregs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
SafSb1SaeA1S5S4S1SeA2M0S0G0S2S1SeU2S106A4S0G0S2S1SeUaS11PcA1A4S0G0S2S1SeUbS11PdA1A4S3G0A1A3A3A3Vl;A3A2").
Definition pfregs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
SafSafS46S0S4S1SeA2M0S2S1SeU8S11PacA1A4S0G0S2S1SeU9S11PadA1A4S0G0S2S1SeU12S11PaeA1A4S3G0A1A3A3A3A2Vl;A2").
Definition pcut (pc : Z) (regs : list (nat * sv)) (fregs : list (nat * sv)) (objs : list sobj) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S1fVpc;S105Vregs;A1S103Vfregs;A1S1eS6SeA1Vobjs;S5S10Vfacts;S7fA3S42S7A9").
Definition n3 : sv := ltac2:(tb__ "0|0|
S12S2dS12S2eS75SfZ1A1A3S75A3").

Definition pre1 : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S1SeA2M0S2S1SeU12S75A4S0G0S2S1SeU13SfZ2A1A4S0G0S2S1SeU17S75A4S0G0S2S1SeU18S12S2dS11PaA1SfN98A1A3A4S0G0S2S1SeU19Se8A4S3G0A1A3A3A3A3A3").

Definition Kfin : sstate := ltac2:(tb__ "0|9|
Se5S88Vc;A1S5S4S1SeA2M0S104S0G0S2S1SeUcS12S2dS7aS11P78A1M1A3A4S0G0S2S1SeUdS11P79A1M2A4S3G0A1M3A3A3A3G3S7bS76SfZ0A1M4A1S19S19S3S13A1M5S0S13S16G4Z8M6G4A3S0S13S16SfG6A1G6G4A3S0S13S16SfZ10A1Z4SfZ2M7A1M8A3G5A3A3A3SebA6S0S10S1dS12S2dG1S12S2eG2G8A3A3S1cS2fS75SfZcA1A3A2S0S10S15SfZ1A1G2A2S0S10S15G2Se8A2S0S10S15G1SfS108G7Z18A2A1A2S3S10A1A3A3A3A3A5").

Definition w_cells : list cell := ltac2:(tb__ "0|1|
S0S13S16SfN8b8A1Z8M0S77A3S0S13S16SfN8b0A1G0S7dA3S0S13S16SfN8a8A1G0S7eA3S0S13S16SfN8a0A1G0S80A3S3S13A1A3A3A3A3").
Definition res0 : list cell := ltac2:(tb__ "0|2|
S0S13S16SfZ0A1M0Z8M1G0A3S0S13S16SfG1A1G1G0A3S0S13S16SfZ10A1Z4SfZ2A1A3S3S13A1A3A3A3").

Definition pre2 : list (nat * sv) := ltac2:(tb__ "0|2|
S0S4S1SeA2M0S2S1SeU8S79A4S0G0S2S1SeU9S77A4S0G0S2S1SeU12S75A4S0G0S2S1SeU13S7aA4S0G0S2S1SeU14S12S2dS75SfN2A1A3A4S0G0S2S1SeU15SfZ0A1M1A4S0G0S2S1SeU16SfZ1A1A4S0G0S2S1SeU17S75A4S0G0S2S1SeU18S12S2dS11PaA1SfN98A1A3A4S0G0S2S1SeU19Se8A4S0G0S2S1SeUdG1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3").
Definition pobjs2 (dout : odefault) (outc : list cell) : list sobj := ltac2:(tb__ "0|0|
S7bVdout;S19S19Voutc;SecS5S13SeeSebA3A6").

Definition Kcm : sstate := ltac2:(tb__ "0|6|
Se5S86Vc;A1S5S4S1SeA2M0Se9S0G0S2S1SeUfS12S2dS7aS11P78M1A1M2A3A4S0G0S2S1SeUeS12S2dS7aS12S2eSe8SfZ2M3A1A3A3A4S0G0S2S1SeUcSfZ0A1M4A4S3G0A1M5A3A3A3A3G5Se7S76G4A1S3S13A1A2S0S10S18G2S1cS2fS75SfZcA1A3A2S0S10S22G1G3A2S0S10S15G2SfS108G3Z18A2A1A2S3S10A1A3A3A3A5").

Definition Knw : sstate := ltac2:(tb__ "0|4|
Se5S89Vc;A1S5S4S1SeA2M0Se9S0G0S2S1SeUcS11P7aA1M1A4S0G0S2S1SeUeS11P7bA1M2A4S3G0A1M3A3A3A3G3Se7S76SfZ0A1A1S3S13A1A2S0S10S1dS12S2dG1S1cS2fG2SfZ3A1A3A3Se8A2S0S10S15SfZ1A1G2A2S0S10S15G2S75A2S0S10S15G1SfS108Z2Z16A2A1A2S3S10A1A3A3A3A3A5").

Definition Kext : sstate := ltac2:(tb__ "0|6|
Se5S87Vc;A1S5S4S1SeA2M0Se9S0G0S2S1SeUcS11P7aA1M1A4S0G0S2S1SeUeS11P7bA1M2A4S3G0A1M3A3A3A3G3Se7S76SfZ0A1A1S3S13A1A2S0S10S1dS12S2dG1S1cS2fG2SfZ3A1A3A3S12S2dSe8SfZ2M4A1M5A3A2S0S10S15SfZ1A1G2A2S0S10S15G2S75A2S0S10S15G5G1A2S0S10S15G1SfS108G4Z16A2A1A2S3S10A1A3A3A3A3A3A5").

Definition Kproj : sstate := ltac2:(tb__ "0|b|
Se5S8aVc;A1S5S4S1SeA2M0Se9S0G0S2S1SeUeS11P7cA1M1A4S0G0S2S1SeUcS12S2dSfZ1M2A1M3S11P7eM4A1M5A3A4S0G0S2S1SeU17S11P7bA1M6A4S3G0A1M7A3A3A3A3G7Se7S76SfZ0A1A1S3S13A1A2S0S10S1dS12S2dG1S1cS2fG6SfZ3A1A3A3S12S2dSe8SfZ2M8A1M9A3A2S0S10S1dS12S2dG5S12S2eG6G3A3A3S12S2eS75G3A3A2S0S10S15G3G6A2S0S10S15G6S75A2S0S10S22G4G2A2S0S10S15G9G1A2S0S10S15G1SfS108G8Z16A2A1MaA2S0S10S15G5GaA2S3S10A1A3A3A3A3A3A3A3A3A5").

Definition Kbbp : sstate := ltac2:(tb__ "0|13|
Se5S85Vc;A1S5S4S1SeA2M0Se9S0G0S2S1SeUcS11P7aA1M1A4S0G0S2S1SeUeS11P7cA1M2A4S0G0S2S1SeUfS12S2dSfZ1M3A1M4S11P7eM5A1M6A3A4S0G0S2S1SeU17S11P7bA1M7A4S3G0A1M8A3A3A3A3A3G8Se7S76SfZ0A1A1S3S13A1A2S0S10S1dS12S2dG6S12S2eG7G4A3A3S12S2eS75G4A3M9A2S0S10S15S1cS2fG6SfZ3A1A3MaS12S2eG1G4A3MbA2S0S10S15GbS12S2dGaSfZ2McA1MdA3MeA2S0S10S15GeS12S2eG2G4A3MfA2S0S10S15GfS12S2dGaSfZ4A1A3A2S0S10S15S12S2dG6GdA3G9A2S0S10S15G4G7A2S0S10S15G7S75A2S0S10S22G5G3A2S0S10S15G6SfS108GcZ15A2A1A2S0S10S15S12S2dG1G7A3S12S2dS12S2dG6S75A3M10G4A3M11A2S0S10S15G1G11A2S0S10S15S12S2dG2G7A3S12S2dG10GdA3M12A2S0S10S15G2G12A2S3S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A5").

Definition K29c : sstate := ltac2:(tb__ "0|3|
Se5S109S10aS7cVc;A1Z1dd28A2Z1e3d4A2S5S4S1SeA2M0Se9S0G0S2S1SeU17S11P7fA1M1A4S3G0A1M2A3A3G2Se7S76SfZ0A1A1S3S13A1A2S0S10S15G1SfZ1A1A2S3S10A1A3A5").

Definition Klat : sstate := ltac2:(tb__ "0|6|
Se5S109S10aS7cVc;A1Z1dd28A2Z1e088A2S5S4S1SeA2M0Se9S0G0S2S1SeUcS11P7aA1M1A4S0G0S2S1SeUeS11P7bA1M2A4S3G0A1M3A3A3A3G3Se7S76SfZ0A1A1S3S13A1A2S0S10S1dS12S2dG1S1cS2fG2SfZ3A1A3A3S12S2dSe8SfZ2M4A1M5A3A2S0S10S15SfZ1A1G2A2S0S10S15G2S75A2S0S10S15G5G1A2S0S10S15G1SfS108G4Z16A2A1A2S3S10A1A3A3A3A3A3A5").
Definition pg_cutpcs2 : list Z := ltac2:(tb__ "0|0|
S5Sa0S9cVc;A1S0Sa0Z1e620S0Sa0Z1e6e8S0Sa0S109S10aS7cVc;A1Z1dd28A2Z1e088A2S3Sa0A1A3A3A3A3").
Definition P (off : Z) : Z := ltac2:(tb__ "0|0|
S109S10aS7cVc;A1Z1dd28A2Voff;A2").

Definition out3_cells : list cell := ltac2:(tb__ "0|2|
S0S13S16SfZ8A1Z4M0SfZ2A1A3S0S13S16SfG0A1G0SfZ1A1A3S0S13S16SfZ0A1M1G0G1A3S3S13A1A3A3A3").

Definition xr3 : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S1SeA2M0S2S1SeU8S79A4S0G0S2S1SeU9S77A4S0G0S2S1SeU12S11PcA1A4S0G0S2S1SeU13S7aA4S0G0S2S1SeU14S12S2dS75SfN2A1A3A4S0G0S2S1SeU15SfZ0A1A4S0G0S2S1SeU16SfZ1A1A4S0G0S2S1SeU17S11P7fA1A4S0G0S2S1SeU18S11PdA1A4S0G0S2S1SeU19Se8A4S3G0A1A3A3A3A3A3A3A3A3A3A3").
Definition E_sc3 : sstate := ltac2:(tb__ "0|3|
Se5Se6Z1e7acA1S5S4S1SeA2M0SeaS0G0S2S1SeU1SfSe6Z1e450A1A1A4S0G0S2S1SeUaS77A4S0G0S2S1SeUbSfZ3A1M1A4S3G0A1M2A3A3A3A3G2Se7S76SfZ0A1A1SedA2S0S10S21S1aS31S75G1A3A1S0S10S15S11P7fA1SfZ1A1A2S3S10A1A3A3A5").
Definition K318 : sstate := ltac2:(tb__ "0|2|
Se5Se6Z1e858A1S5S4S1SeA2M0SeaS0G0S2S1SeU1SfSe6Z1e450A1A1A4S0G0S2S1SeUaS11P6eA1A4S0G0S2S1SeUbS11P6fA1A4S3G0A1M1A3A3A3A3G1Se7S76SfZ0A1A1SedA2S0S10S21S1aS31S75SfZ3A1A3A1S0S10S15S11P7fA1SfZ1A1A2S3S10A1A3A3A5").

Definition E_sc4 : sstate := ltac2:(tb__ "0|3|
Se5Se6Z1e7acA1S5S4S1SeA2M0SeaS0G0S2S1SeU1SfSe6Z1e484A1A1A4S0G0S2S1SeUaS77A4S0G0S2S1SeUbSfZ4A1M1A4S0G0S2S1SeUcG1A4S3G0A1M2A3A3A3A3A3G2Se7S76SfZ0A1A1S3S13A1A2S0S10S1aS30S75G1A3S0S10S15S11P7fA1SfZ1A1A2S3S10A1A3A3A5").
Definition K34c : sstate := ltac2:(tb__ "0|2|
Se5Se6Z1e858A1S5S4S1SeA2M0SeaS0G0S2S1SeU1SfSe6Z1e484A1A1A4S0G0S2S1SeUaS11P6eA1A4S0G0S2S1SeUbS11P6fA1A4S3G0A1M1A3A3A3A3G1Se7S76SfZ0A1A1S3S13A1A2S0S10S1aS30S75SfZ4A1A3S0S10S15S11P7fA1SfZ1A1A2S3S10A1A3A3A5").

Definition xr5 : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S1SeA2M0S2S1SeU8S79A4S0G0S2S1SeU9S77A4S0G0S2S1SeU12S75A4S0G0S2S1SeU13S11PdA1A4S0G0S2S1SeU14S12S2dS75SfN2A1A3A4S0G0S2S1SeU15SfZ0A1A4S0G0S2S1SeU16SfZ1A1A4S0G0S2S1SeU17S11P7fA1A4S0G0S2S1SeU18S11PcA1A4S0G0S2S1SeU19Se8A4S3G0A1A3A3A3A3A3A3A3A3A3A3").
Definition E_r2 : sstate := ltac2:(tb__ "0|3|
Se5Se6Z1e85cA1S5S4S1SeA2M0Sf0S0G0S2S1SeU1SfSe6Z1e514A1A1A4S0G0S2S1SeUaS12S2dS11PaA1SfN8b8A1A3A4S0G0S2S1SeUbS75A4S0G0S2S1SeUcS79A4S0G0S2S1SeUdSfZ0A1M1A4S3G0A1M2A3A3A3A3A3A3G2Se7S76G1A1S3S13A1A2S0S10S1aS31S75SfZ3A1A3S0S10S21S1aS30S75SfZ4A1A3A1S0S10S15S11P7fA1SfZ1A1A2S3S10A1A3A3A3A5").
Definition K3dc : sstate := ltac2:(tb__ "0|5|
Se5Se6Z1f1d8A1S5S4S1SeA2M0Sf0S0G0S2S1SeU1SfSe6Z1e514A1A1A4S0G0S2S1SeUaS11P6eA1A4S0G0S2S1SeUbS11P6fA1A4S3G0A1M1A3A3A3A3G1S7bS76S12S2dS75SfN2A1A3A1S24Z4M2S75S0S4Sa0Sa0A2M3S2Sa0Sa0Z0G2A4S3G3A1A3S0S20S23S8U0S6S4S9Sa1A2A1S75A4S3S20A1A3A4M4G4S3S13A1SecS5S13SeeSebA3A6S0S10S1aS31S75SfZ3A1A3S0S10S21S1aS30S75SfG2A1A3A1S0S10S15S11P7fA1SfZ1A1A2S3S10A1A3A3A3A5").

Definition xr4 (a2 a3 a4 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S1SeA2M0SeaS0G0S2S1SeU1SfSe6Z1e484A1A1A4S0G0S2S1SeUaS11PcA1A4S0G0S2S1SeUbS11PdA1A4S0G0S2S1SeUcVa2;A4S0G0S2S1SeUdVa3;A4S0G0S2S1SeUeVa4;A4S3G0A1A3A3A3A3A3A3A3").
Definition K4a : sstate := ltac2:(tb__ "0|4|
Se5Se6Z1e620A1S5S4S1SeA2M0SefSfZ1A1M1SfZ2A1SfZ3A1A3S0G0S2S1SeU13S11PbcA1M2A4S3G0A1M3A3A3G3Se7S76G1A1S3S13A1A2S0S10S1aS30S75SfZ4A1A3S0S10S15S11P7fA1G1A2S0S10S15G2G1A2S3S10A1A3A3A3A5").
Definition K4b : sstate := ltac2:(tb__ "0|4|
Se5Se6Z1e6e8A1S5S4S1SeA2M0SefSfZ1A1M1SfZ3A1S11P72A1A3S0G0S2S1SeU13S11PbcA1M2A4S3G0A1M3A3A3G3Se7S76G1A1S3S13A1A2S0S10S1aS30S75SfZ4A1A3S0S10S15S11P7fA1G1A2S0S10S15G2G1A2S3S10A1A3A3A3A5").

Definition P_inv : sstate := ltac2:(tb__ "0|2|
S1fS8cVc;A1SafSb0SaeA1S0S4S1SeA2M0S2S1SeUaSfZ2A1A4S3G0A1A3A2S46S1eS6SeA1S7bS76SfZ0A1A1S19S19S3S13A1M1SecG1A6S7fS42S7A9").
Definition P_ok : sstate := ltac2:(tb__ "0|5|
S1fS8cVc;A1Sb0SaeA1S46S1eS6SeA1S7bS76S12S2dS75SfN2A1A3M0A1S19S19S3S13A1M1S0S13S16SfZ0A1M2Z8M3S79A3S0S13S16SfG3A1Z4M4G0A3S0S13S16SfZcA1G4G2A3S0S13S16SfZ10A1G4S11P6eA1A3G1A3A3A3A3G1A6S7fS42S7A9").
Definition pcuts : list sstate := ltac2:(tb__ "0|0|
S0S14S9bVc;S3S10A1A2S0S14SfdS0S14SfbS0S14SffS0S14SfcS0S14S100S0S14SfaS0S14Sf4S0S14Sf5S0S14Sf6S0S14Sf7S0S14Sf8S0S14Sf9S0S14SfeS3S14A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition pexits : list sstate := ltac2:(tb__ "0|0|
S0S14S101S0S14S102S0S14Sf2S0S14Sf3S0S14Sf1S3S14A1A3A3A3A3A3").
End PS2.

Definition FUEL_pg : nat := 500%nat.
End Lib_tess_polygon_defs.

Module Lib_tess_run2d_ex_defs.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingBuf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.Ring OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingCfg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d.

Import ListNotations. Open Scope Z_scope.

Definition LN : positive := 10%positive.  Definition LP : positive := 11%positive.
Definition NXT (e : sv) : sv := LD4 LN e.
Definition PRV (e : sv) : sv := LD4 LP e.
Definition O_outE (cells : list cell) (d : odefault) : sobj := ltac2:(tb__ "0|0|
S1bS40SfZ0A1S1cS2fS12S2dS39SfN2A1A3SfZcA1A3Vcells;Vd;A5").

Definition eobjs (cn cp : list cell) (outc : list cell) (outd : odefault) (stkc : list cell) : list sobj := ltac2:(tb__ "0|2|
S0S17S4aVstkc;A1S0S17S4bS0S17S48S0S17S1bS3dSfZ0A1M0S12S2eS39SfZ2A1A3M1Vcn;S26Sd5A1A5S0S17S1bS3cG0G1Vcp;S26Sd6A1A5S0S17S49S0S17Sd7Voutc;Voutd;A2S3S17A1A3A3A3A3A3A3A3").

Definition k3 (k : sv) : sv := ltac2:(tb__ "0|0|
S12S2dS12S2eVk;SfZ1A1A3Vk;A3").
Definition out3 (k a b d : sv) : list cell := ltac2:(tb__ "0|3|
S0S13S16S12S2eS12S2dSbdVk;A1M0SfZ2A1M1A3G1A3Z4M2Vd;A3S0S13S16S12S2eS12S2dG0SfZ1A1A3G1A3G2Vb;A3S0S13S16S12S2eG0G1A3G2Va;A3S3S13A1A3A3A3").
Definition SEL_nxt : sv := ltac2:(tb__ "0|2|
S12S33S12S2dS12S36S12S2dS11P7cA1SfN1A1M0A3SfZ1A1M1A3G0A3S12S2dS11P7bA1G1A3A3").
Definition REM_prv : sv := ltac2:(tb__ "0|1|
S2cS38S12S2dS12S2dS11PdA1M0SfN1A1A3S11P7bA1A3G0A3").
Definition cellN : cell := ltac2:(tb__ "0|0|
S16S107S11P7bA1A1Z4Sd8A3").
Definition cellP : cell := ltac2:(tb__ "0|0|
S16S107S11P7bA1A1Z4Sc1A3").
Definition mg_facts : list sprop := ltac2:(tb__ "0|0|
S0S10S15S11Pb8A1SfZ2A1A2S0S10S15S11Pb7A1S11Pb6A1A2S3S10A1A3A3").

Section E. Variable c : r2_consts.
Definition ecut (pc : Z) (regs : list (nat * sv)) (fregs : list (nat * sv)) (objs : list sobj) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S3aVpc;Vregs;Vfregs;Vobjs;Vfacts;A5").

Definition EPre := Pre_r2 c.
Definition EKs := Ks c.
Definition EKa := Ea c.
Definition kr_regs : list (nat * sv) := ltac2:(tb__ "0|3|
S5S4S1SeA2M0S55S0G0S2S1SeUeS12S2dS3dS12S2eS11P7bA1M1SfZ2A1A3M2A3A4S0G0S2S1SeUfS12S2dS3cG2A3A4S0G0S2S1SeU10S12S2dS12S2dS39SfN1A1A3G1A3A4S0G0S2S1SeU11S12S2dG1SfZ1A1A3A4S0G0S2S1SeU5S11P7cA1A4S3G0A1A3A3A3A3A3A3").
Definition X_r0 : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|0|
S3aS4fVc;A1S14dS3S4S1SeA2A1S4eS19S19S3S13A1S3bA4S0S10S1dS11P7bA1SfZ0A1A2S4dA3A5").
Definition K_r : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|1|
S3aS4fVc;A1S14dS3S4S1SeA2A1Sb5S3S13A1M0G0G0S19S3bA5S4dA5").
Definition xr_regs : list (nat * sv) := ltac2:(tb__ "0|6|
S5S4S1SeA2M0S55S0G0S2S1SeUeS12S2dS12S2dS3dS12S2eS11P7bA1M1SfZ2A1M2A3M3A3SfZ4A1M4A3A4S0G0S2S1SeUfS12S2dS12S2dS3cG3A3G4A3A4S0G0S2S1SeU10S12S2dS12S2dS12S2dS39SfN1A1M5A3G1A3SfZ1A1A3A4S0G0S2S1SeU11S12S2dG1G2A3A4S0G0S2S1SeU5S12S2dS11P7cA1G5A3A4S0G0S2S1SeU6Sc1A4S3G0A1A3A3A3A3A3A3A3").

Definition X_r : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|1|
S3aS4fVc;A1S14aS3S4S1SeA2A1Sb5S0S13Sc3S3S13A1M0A3S0S13Sc4G0A3G0S19S3bA5S0S10S1aS31S12S2dS11P7cA1SfN1A1A3SfZ0A1A3S4dA3A5").

Definition X_rf : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|1|
S3aZ1ea70S14aS3S4S1SeA2A1Sb5S0S13Sc3S3S13A1M0A3S0S13Sc4G0A3G0S19S3bA5S0S10S21S1aS31S12S2dS11P7cA1SfN1A1A3SfZ0A1A3A1S4dA3A5").
Definition K_f0 : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|1|
S3aZ1ea70S14aS3S4S1SeA2A1Sb5S3S13A1M0G0G0S19S3bA5S0S10S21S1aS31S12S2dS11P7cA1SfN1A1A3SfZ0A1A3A1S4dA3A5").
Definition K_f : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|4|
S3aS5cVc;A1S5S4S1SeA2M0S55S0G0S2S1SeU10S11P7dA1M1A4S0G0S2S1SeU11SfZ1A1A4S3G0A1M2A3A3A3G2Sb5S3S13A1M3G3G3S19S3bA5S0S10S18G1S39A2S3S10A1A3A5").
Definition gf_f : list sprop := ltac2:(tb__ "0|1|
S0S10S18Sb6S11P7dA1M0A1S39A2S0S10S18Sb7G0A1S39A2S3S10A1A3A3").
Definition K_fan : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|2|
S1fS54Vc;A1S2aS69Vc;S3S10A1A2M0A1S28G0A1S1eS6SeA1Sb5S3S13A1M1G1G1S3fS11P7eA1A1S3bA5S27G0A1S42S7A9").

Definition K_m : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|1|
S3aS5fVc;A1S43Vc;A1S3S4S1SeA2A1Sb5S3S13A1M0G0G0S3fS11Pb5A1A1S3bA5S5S10S47SbcA3A5").
Definition gf_m : list sprop := ltac2:(tb__ "0|2|
S0S10S18Sb6S11Pb4A1M0A1M1S39A2S0S10S18Sb7G0A1S39A2S0S10S18Sb6G1A1S39A2S0S10S18Sb7G1A1S39A2S3S10A1A3A3A3A3").
Definition K_c : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|5|
S3aS5bVc;A1S5S4S1SeA2M0S43Vc;A1S0G0S2S1SeU6S11PbaA1M1A4S0G0S2S1SeU9S11PbbA1M2A4S0G0S2S1SeU7S3eA4S0G0S2S1SeU12S41A4S0G0S2S1SeU1cS12S2eS12S2eG1SfZ1A1A3SfZ20A1A3A4S0G0S2S1SeU1dS3cA4S0G0S2S1SeU1eS3dA4S3G0A1M3A3A3A3A3A3A3A3A3G3Sb5S3S13A1M4G4G4S3fS11Pb5A1A1S3bA5S5S10S47S5S10SbcS0S10S18G1S39A2S0S10S18G2S39A2S3S10A1A3A3A3A3A5").
Definition xc2_regs : list (nat * sv) := ltac2:(tb__ "0|8|
S5S4S1SeA2M0S43Vc;A1S0G0S2S1SeU6S11PbaA1M1A4S0G0S2S1SeU7S3eA4S0G0S2S1SeU8S12S2dS40S12S2eS12S2dSbdS11Pb5A1A1M2SfZ2A1M3A3G3A3A3A4S0G0S2S1SeU9S11PbbA1M4A4S0G0S2S1SeU12S41A4S0G0S2S1SeU13S12S2dS40S12S2eG2G3A3A3A4S0G0S2S1SeU14S12S2dS3cS107G1A1M5A3A4S0G0S2S1SeU15S12S2dS40S12S2eS12S2dG2SfZ1A1M6A3G3A3A3A4S0G0S2S1SeU1cS12S2eS12S2eG1G6A3SfZ20A1A3A4S0G0S2S1SeU1dS12S2dS3cS107G4A1M7A3A4S0G0S2S1SeU1eS12S2dS3dG7A3A4S0G0S2S1SeU1fG5A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition kc_facts : list sprop := ltac2:(tb__ "0|0|
S5S10S47S5S10SbcS0S10S18S11PbaA1S39A2S0S10S18S11PbbA1S39A2S3S10A1A3A3A3A3").

Definition X_c2 : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|5|
S3aZ1ecb8S14eS3S4S1SeA2A1Sb5S0S13S16S107S11PbbA1M0A1Z4M1S11PbaA1M2A3S3S13A1M3A3S0S13S16S107G2A1G1G0A3G3A3SbeS11Pb5A1M4G0S11Pb4A1G2A4S3fG4A1S3bA5S14cA5").
Definition K_c2 : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|2|
S3aZ1ecb8S14eS3S4S1SeA2A1Sb5S3S13A1M0G0SbeS11Pb5A1M1S11PbbA1S11Pb4A1S11PbaA1A4S3fG1A1S3bA5S14cA5").
Definition gf_c2 : list sprop := ltac2:(tb__ "0|2|
S0S10S18Sb6S11PbbA1M0A1S39A2S0S10S18Sb7G0A1S39A2S0S10S18Sb6S11PbaA1M1A1S39A2S0S10S18Sb7G1A1S39A2S3S10A1A3A3A3A3").
Definition K_g : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|4|
S3aS5dVc;A1S5S4S1SeA2M0S43Vc;A1S0G0S2S1SeU6S11PbaA1M1A4S0G0S2S1SeU7S3eA4S0G0S2S1SeU1dS3cA4S0G0S2S1SeU1eS3dA4S3G0A1M2A3A3A3A3A3G2Sb5S3S13A1M3G3G3S3fS11Pb5A1A1S3bA5S5S10S47S5S10SbcS0S10S18G1S39A2S3S10A1A3A3A3A5").
Definition gf_g : list sprop := ltac2:(tb__ "0|1|
S0S10S18Sb6S11PbaA1M0A1S39A2S0S10S18Sb7G0A1S39A2S3S10A1A3A3").

Definition kgb_regs : list (nat * sv) := ltac2:(tb__ "0|2|
S5S4S1SeA2M0S43Vc;A1S0G0S2S1SeU5S11Pc5A1A4S0G0S2S1SeU6S11PbaA1M1A4S0G0S2S1SeU7S3eA4S0G0S2S1SeU8SbdS11Pb5A1A1A4S0G0S2S1SeUdS12S2dS3dS107G1A1A3A4S0G0S2S1SeU1cS41A4S0G0S2S1SeU1dS3cA4S0G0S2S1SeU1eS3dA4S0G0S2S1SeU1fS11Pc4A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3").
Definition kgb_facts : list sprop := ltac2:(tb__ "0|0|
S5S10S47S5S10SbcS0S10S18S11PbaA1S39A2S0S10S18S11Pc4A1S39A2S0S10S18S11Pc5A1S39A2S3S10A1A3A3A3A3A3").
Definition K_gb : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|1|
S3aZ1ef2cS16dS3S4S1SeA2A1Sb5S3S13A1M0G0G0S3fS11Pb5A1A1S3bA5S149A5").
Definition xg2_regs : list (nat * sv) := ltac2:(tb__ "0|7|
S5S4S1SeA2M0S43Vc;A1S0G0S2S1SeU5S11Pc5A1M1A4S0G0S2S1SeU6S107G1A1M2A4S0G0S2S1SeU7S3eA4S0G0S2S1SeU8S12S2dS40S12S2eS12S2dSbdS11Pb5A1A1M3SfZ2A1M4A3G4A3A3A4S0G0S2S1SeU9S12S2dS40S12S2eS12S2dG3SfZ1A1A3G4A3A3A4S0G0S2S1SeUdS12S2dS3cS107S11Pc4A1M5A1M6A3A4S0G0S2S1SeU1cS12S2dS41S12S32G5SfZ3A1A3A3A4S0G0S2S1SeU1dS12S2dS3cG2A3A4S0G0S2S1SeU1eS12S2dS3dG6A3A4S0G0S2S1SeU1fG5A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3").

Definition X_g2 : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|5|
S3aZ1ef88S14fS3S4S1SeA2A1Sb5S0S13S16S107S11Pc4A1M0A1Z4M1S11Pc5A1M2A3S3S13A1M3A3S0S13S16S107G2A1G1G0A3G3A3SbeS11Pb5A1M4G0S11PbaA1G2A4S3fG4A1S3bA5S149A5").
Definition K_g2 : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|2|
S3aZ1ef88S14fS3S4S1SeA2A1Sb5S3S13A1M0G0SbeS11Pb5A1M1S11Pc4A1S11PbaA1S11Pc5A1A4S3fG1A1S3bA5S149A5").
Definition gf_g2 : list sprop := ltac2:(tb__ "0|2|
S0S10S18Sb6S11Pc4A1M0A1S39A2S0S10S18Sb7G0A1S39A2S0S10S18Sb6S11Pc5A1M1A1S39A2S0S10S18Sb7G1A1S39A2S3S10A1A3A3A3A3").
Definition K_i : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|6|
S3aS5eVc;A1S5S4S1SeA2M0S43Vc;A1S0G0S2S1SeU6S11PbaA1M1A4S0G0S2S1SeU9S11PbbA1M2A4S0G0S2S1SeU13G2A4S0G0S2S1SeU14S11PbcA1M3A4S0G0S2S1SeU12S41A4S0G0S2S1SeU7S3eA4S0G0S2S1SeU1dS3cA4S0G0S2S1SeU1eS3dA4S0G0S2S1SeU1cS12S2eS12S2eG1SfZ1A1A3SfZ20A1A3A4S3G0A1M4A3A3A3A3A3A3A3A3A3A3G4Sb5S3S13A1M5G5G5S3fS11Pb5A1A1S3bA5S5S10S47S5S10SbcS0S10S18G1S39A2S0S10S18G2S39A2S0S10S18G3S39A2S0S10S21S1aS30G3G2A3A1S3S10A1A3A3A3A3A3A3A5").
Definition gf_i : list sprop := ltac2:(tb__ "0|0|
S0S10S18Sb6S11PbcA1A1S39A2S3S10A1A3").
Definition K_x : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|7|
S3aS60Vc;A1S5S4S1SeA2M0S55S0G0S2S1SeU5S11Pb4A1M1A4S0G0S2S1SeUeS11Pb5A1M2A4S0G0S2S1SeUbS11Pb6A1M3A4S0G0S2S1SeUdS11Pb9A1A4S3G0A1M4A3A3A3A3A3G4Sb5S3S13A1M5G5G5S3fG2A1S3bA5S0S10S18G1S39A2S0S10S1dS12S2dG2G3A3S39A2S0S10S15G3SfZ3A1M6A2S0S10S15G6G3A2S0S10S15G2S39A2S0S10S6fG2A1S3S10A1A3A3A3A3A3A3A5").
Definition gf_x : list sprop := ltac2:(tb__ "0|1|
S0S10S18Sb6S11Pb4A1A1M0S39A2S0S10S18Sb6G0A1S39A2S3S10A1A3A3").
Definition E_ret : ltac2:(tb__ "0|0|
S14") := ltac2:(tb__ "0|1|
S1fS66Vc;A1Sb0SaeA1S46S1eS6SeA1Sb5S3S13A1M0G0G0S3fS12S2dS39SfN2A1A3A1G0A5S53S42S7A9").

Definition ecutsG : list (sstate * list sprop) := ltac2:(tb__ "0|3|
S0S4S14SbS10A1M0A2M1S2S14G0S152S3S10A1M2A4S0G1S2S14G0S151G2A4S0G1S2S14G0S150G2A4S0G1S2S14G0S15eG2A4S0G1S2S14G0S157G2A4S0G1S2S14G0S156S167A4S0G1S2S14G0S158G2A4S0G1S2S14G0S15dS16bA4S0G1S2S14G0S154G2A4S0G1S2S14G0S155S166A4S0G1S2S14G0S159S168A4S0G1S2S14G0S15bG2A4S0G1S2S14G0S15aS169A4S0G1S2S14G0S15cS16aA4S0G1S2S14G0S15fS16cA4S3G1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition eexits : list sstate := ltac2:(tb__ "0|0|
S0S14S163S0S14S162S0S14S164S0S14S160S0S14S161S0S14S153S3S14A1A3A3A3A3A3A3").
Definition esources : list sstate := ltac2:(tb__ "0|2|
S13bS4S14SbS10A1M0A2M1S14G1SadSdS14G0R1A3ScS14G0R1A3A2Lp;S14bA4").
Definition etargets : list sstate := ltac2:(tb__ "0|1|
S5S14S13bS4S14SbS10A1M0A2S14ScS14G0A2S14bA4S165A3").
Definition ecutpcs : list Z := ltac2:(tb__ "0|0|
S5Sa0S58Vc;A1S0Sa0Z1ecb8S0Sa0Z1ef2cS0Sa0Z1ef88S0Sa0Z1ea70S3Sa0A1A3A3A3A3A3").
End E.

Definition VN : positive := 13%positive.
Definition noring : option rghost := None.
Definition RGfull (roots : list sv) : option rghost := ltac2:(tb__ "0|0|
SaSa5Sa4S39SfZ0A1Vroots;S3S4SeSeA2A1A4A2").
Definition RGm (R cur : sv) (roots : list sv) (eqs : list (sv * sv)) : option rghost := ltac2:(tb__ "0|0|
SaSa5Sa4VR;Vcur;Vroots;Veqs;A4A2").
Definition R182 : sv := SVar 182.
Definition R182m1 : sv := SAlu ALU_ADD (SVar 182) (SLit (-1)).
Definition lexM : list (vdir * sv) := ltac2:(tb__ "0|2|
S0S4Sa6SeA2M0S2Sa6SeSa7S7A1S11Pb6A1A4S0G0S2Sa6SeSa9S7A1M1S11Pb8A1A4S0G0S2Sa6SeG1S11Pb7A1A4S3G0A1A3A3A3").
Definition eqs_c : list (sv * sv) := ltac2:(tb__ "0|2|
S0S4SeSeA2M0S2SeSeS11PbaA1Sb6S11Pb4A1M1A1A4S0G0S2SeSeS11PbbA1Sb7G1A1A4S3G0A1A3A3").

Section N. Variable c : r2_consts.

Definition N_Pre  : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|0|
Sa3Sc7Vc;A1S3S10A1S7S6SeA1SbaZcS3S4Sa6SeA2A1Z0S6S4SeSeA2A1A9").
Definition N_Ks   : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|1|
Sa3Sc6Vc;A1S3S10A1S7S6SeA1SbaZbS0S4Sa6SeA2M0S2Sa6SeSa7S7A1S11P78A1A4S3G0A1A3Z0S6S4SeSeA2A1A9").
Definition N_Ka   : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|1|
Sa3Sc5Vc;A1S3S10A1S7S6SeA1SbaZaS0S4Sa6SeA2M0S2Sa6SeSa7S7A1S11P78A1A4S3G0A1A3Z0S6S4SeSeA2A1A9").
Definition N_Kr   : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|1|
Sa3Sd3Vc;A1S3S10A1S7SaSeS11P7bA1A2SbaZ8S0S4Sa6SeA2M0S2Sa6SeSa7S7A1S11P7cA1A4S3G0A1A3Z2S6S4SeSeA2A1A9").
Definition N_Kf0  : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|0|
Sa3SccS3S10A1S8S6SeA1Sc2S3SeA1A1Z7S3S4Sa6SeA2A1Z0S6S4SeSeA2A1A9").
Definition N_Kf   : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|2|
Sa3ScbVc;A1SdfS8S6SeA1Sc2S0SeS11P7dA1M0S3SeA1A3A1Z6S0S4Sa6SeA2M1S2Sa6SeSa9S7A1G0A4S3G1A1A3Z0S6S4SeSeA2A1A9").
Definition N_Kfan : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|1|
Sa3ScdVc;A1S3S10A1S8S6SeA1SbaZ5S0S4Sa6SeA2M0S2Sa6SeSa9S7A1S11P7eA1A4S3G0A1A3Z0S6S4SeSeA2A1A9").
Definition N_Km   : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|2|
Sa3Sd2Vc;A1Se3S8S6SeA1Sb8SbbS11Pb4A1M0S0SeG0S3SeA1A3S3S4SeSeA2M1A1A4Z5Sb9Z8S6G1A1A9").
Definition N_Kc   : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|2|
Sa3Sc9Vc;A1S3S10A1S8S6SeA1Sb8SbbS11Pb4A1M0S0SeG0S0SeS11PbaA1S0SeS11PbbA1S3SeA1A3A3A3SbfA4Z5M1Sb9G1S6S4SeSeA2A1A9").
Definition N_Kc2  : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|2|
Sa3ScaVc;A1SdeS8S6SeA1Sb8Sc0S11PbaA1M0S0SeG0S0SeS11PbbA1S3SeA1A3A3S3S4SeSeA2M1A1A4Z5Sb9Z3S6G1A1A9").
Definition N_Kg   : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|4|
Sa3SceVc;A1Se0S8S6SeA1Sb8SbbS11Pb4A1M0S0SeG0S0SeS11PbaA1M1S3SeA1A3A3S0S4SeSeA2M2S2SeSeG1Sb6G0A1A4S3G2A1A3A4Z5M3Sb9G3S6G2A1A9").
Definition N_Kgb  : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|4|
Sa3Sd0Vc;A1S3S10A1S8S6SeA1Sb8SbbS11PbaA1M0S0SeG0S0SeS11Pc4A1M1S0SeS11Pc5A1M2S3SeA1A3A3A3S0S4SeSeA2M3S2SeSeG1Sb7G0A1A4S0G3S2SeSeG2Sb6G0A1A4S3G3A1A3A3A4Z5Sb9Z4S6G3A1A9").
Definition N_Kg2  : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|2|
Sa3ScfVc;A1Se1S8S6SeA1Sb8Sc0S11Pc5A1M0S0SeG0S0SeS11Pc4A1S3SeA1A3A3S3S4SeSeA2M1A1A4Z5Sb9Z2S6G1A1A9").
Definition N_Ki   : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|3|
Sa3Sd1Vc;A1Se2S8S6SeA1Sb8SbbS11Pb4A1M0S0SeG0S0SeS11PbaA1S0SeS11PbbA1M1S0SeS11PbcA1M2S3SeA1A3A3A3A3SbfA4Z5Sb9Z6SaS4SeSeA2S2SeSeG2G1A4A2A9").
Definition N_Kx   : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|2|
Sa3Sd4Vc;A1Se4S8S6SeA1Sb8SbbS11Pb4A1M0S0SeG0S3SeA1A3S3S4SeSeA2M1A1A4Z2S3S4Sa6SeA2A1Z0S6G1A1A9").

Definition N_Xr0  : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|0|
Sa3SdcVc;A1S3S10A1S7SaSeS11P7bA1A2SbaZ9S3S4Sa6SeA2A1Z0S6S4SeSeA2A1A9").
Definition N_Xr   : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|1|
Sa3SdbVc;A1S3S10A1S7SaSeS11P7bA1A2SbaZ8S0S4Sa6SeA2M0S2Sa6SeSa7S7A1S11P7cA1A4S3G0A1A3Z1S6S4SeSeA2A1A9").
Definition N_Xrf  : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|1|
Sa3SddS3S10A1S7SaSeS11P7bA1A2SbaZ8S0S4Sa6SeA2M0S2Sa6SeSa7S7A1S11P7cA1A4S3G0A1A3Z1S6S4SeSeA2A1A9").
Definition N_Xc2  : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|1|
Sa3Sd9Vc;A1S3S10A1S8S6SeA1Sb8SbbS11Pb4A1M0S0SeG0S0SeS11PbaA1S0SeS11PbbA1S3SeA1A3A3A3SbfA4Z5Sb9Z4S6S4SeSeA2A1A9").
Definition N_Xg2  : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|4|
Sa3SdaVc;A1S3S10A1S8S6SeA1Sb8SbbS11PbaA1M0S0SeG0S0SeS11Pc4A1M1S0SeS11Pc5A1M2S3SeA1A3A3A3S0S4SeSeA2M3S2SeSeG1Sb7G0A1A4S0G3S2SeSeG2Sb6G0A1A4S3G3A1A3A3A4Z5Sb9Z3S6G3A1A9").
Definition N_Eret : ltac2:(tb__ "0|0|
Sa2") := ltac2:(tb__ "0|0|
Sa3Sc8Vc;A1S3S10A1S8S6SeA1SbaZ1S3S4Sa6SeA2A1Z0S6S4SeSeA2A1A9").
Definition rcuts : list rnode := ltac2:(tb__ "0|0|
S0Sa2S188S0Sa2S186S0Sa2S17aS0Sa2S185S0Sa2S17eS0Sa2S17dS0Sa2S17fS0Sa2S184S0Sa2S17bS0Sa2S17cS0Sa2S180S0Sa2S182S0Sa2S181S0Sa2S183S0Sa2S187S3Sa2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition rexits : list rnode := ltac2:(tb__ "0|0|
S0Sa2S18cS0Sa2S18bS0Sa2S18dS0Sa2S189S0Sa2S18aS0Sa2S179S3Sa2A1A3A3A3A3A3A3").
End N.
End Lib_tess_run2d_ex_defs.

Module Lib_tess_polygon_chk1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs.

Import ListNotations.
Close Scope bv_scope.

Lemma chk_pg_Kext : ltac2:(tb__ "0|0|
S10cS9SacSb4S82S8bS78A1SaeS5S14S83S78A1S84S78A1A3S8fS78A1A6S8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma chk_pg_Klat : ltac2:(tb__ "0|0|
S10cS9SacSb4S82S8bS78A1SaeS5S14S83S78A1S84S78A1A3S90S78A1A6S8A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_tess_polygon_chk1.
