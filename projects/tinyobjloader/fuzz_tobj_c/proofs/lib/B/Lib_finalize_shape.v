(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "true"; "fst"; "list"; "negb"; "false"; "snd"; "bool"; "option"; "None"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "cell"; "SPUle"; "sobj"; "SVar"; "SAlu"; "DUnknown"; "mkObj"; "sv_eqb"; "SPAlign"; "SPBranch"; "FcsrFrm0"; "mkSS"; "SExt"; "SMd"; "SPNot"; "mkCell"; "ss_regs"; "SPEq"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "sym_runA"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "AHead"; "NDA"; "ND"; "edescA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXSplit"; "AXMerge"; "AXSelect"; "AXRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape"; "vdesc"; "c8"; "z0"; "sh_c"; "kb"; "sh_k"; "vHq"; "fins"; "vAR"; "vB"; "vDp"; "sh_d"; "tv0"; "bd_push"; "qD"; "VD"; "X_fs0"; "cs0"; "ndTf"; "ndTok"; "piece"; "qK"; "spm"; "vAL"; "vERR"; "Xof"; "pi_c"; "vHP"; "vd_d"; "vd_el"; "bofs"; "dats0"; "ghZ"; "lc_c"; "ndTz"; "qHD"; "vHD"; "vd_k"; "CHfrom"; "li_c"; "vCN"; "vHa"; "vd_c"; "FUEL_fs"; "ndE"; "post_fs"; "qcs"; "sg_c"; "vSH"; "Dof"; "HNEXT"; "NP"; "Pre_fs"; "Vd"; "c1"; "canon"; "fs_facts"; "mm_c"; "ndPf"; "ndPg"; "ndPk"; "pG"; "qERR"; "shOf"; "two47"; "vHv"; "vKg"; "vLC"; "vLI"; "vPI"; "AMin1"; "B32"; "CS"; "F_cells"; "O_dat"; "V"; "c4"; "cutsC"; "fv_c"; "main_facts"; "nd1"; "nd2"; "nd3"; "nd4"; "nd5"; "nd6"; "nd7"; "nd8"; "nd_fail_f"; "vDg"; "vd_mesh"; "vec_facts"; "xSH"; "BIG"; "CHf"; "CHname"; "C_1"; "C_2"; "C_3"; "C_4"; "C_5"; "C_6"; "C_7"; "C_8"; "C_E"; "E_ad1"; "E_ad1_0"; "E_ad2"; "E_ad2_0"; "E_ad3"; "E_ad3_0"; "E_ad4"; "E_ad4_0"; "E_mg0"; "E_mk0"; "E_nm"; "E_nm_0"; "E_vf5_0"; "E_vf6_0"; "E_vf7_0"; "E_vp"; "E_vp0"; "FEb"; "FL_50"; "FL_51"; "FL_60"; "FL_61"; "FL_70"; "FL_71"; "FL_E0"; "FL_E1"; "FL_p0"; "FL_p1"; "KLG"; "O_D"; "O_F"; "O_al"; "O_ar"; "PHIe"; "P_alloc"; "P_caps"; "P_cur"; "P_fail"; "P_failz"; "P_ff"; "P_hdr"; "P_nop"; "P_ok"; "P_st"; "Pre_ad1"; "Pre_ad2"; "Pre_ad3"; "Pre_ad4"; "Pre_mc"; "Pre_nm"; "Pre_vf"; "Pre_vp"; "T1_fail"; "T1_ok"; "T2_fail"; "T2_ok"; "T3_fail"; "T3_ok"; "T4_fail"; "T4_ok"; "T5_f"; "T5_ok"; "T5_z"; "T5_z2"; "T5_z2G"; "T5_zG"; "T6_f"; "T6_ok"; "T6_z"; "T6_z2"; "T6_z2G"; "T6_zG"; "T7_f"; "T7_ok"; "T7_z"; "T7_z2"; "T7_z2G"; "T7_zG"; "T_mg"; "T_mk"; "T_pf"; "T_pg"; "T_pgF"; "T_pk"; "T_pkF"; "Tn_fail"; "Tn_ok"; "Vof"; "X_ok"; "bd0"; "builder"; "calls_fs"; "cs8"; "dats_ok"; "dst_obj"; "eC"; "fail_facts"; "fails_t"; "failz_facts"; "finK"; "finV"; "fmid_obj"; "fs_regs"; "fv_d"; "fv_k"; "g8"; "hse_fact"; "hx"; "lc_d"; "lc_k"; "leafC_at"; "li_d"; "li_k"; "mi_c"; "mi_d"; "mi_k"; "mid_obj"; "mm_d"; "mm_k"; "nd0"; "nd_nop"; "nd_ok"; "ok_facts"; "perm_fin"; "perm_m"; "perm_nm"; "perm_vf"; "perm_vfk"; "perm_vp"; "pi_d"; "pi_k"; "sg_d"; "sg_k"; "slotx"; "src_obj"; "top_factG"; "top_factK"; "tv_g"; "tv_ok"; "vCFG"; "vFV"; "vLINE"; "vMI"; "vMM"; "vNM"; "vSG"; "vUD";
"vd_dv"; "vd_off"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "ASv"; "BI"; "BIc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "BC_GE"; "M_MUL"; "BC_GEU"; "@Corelib.Lists.ListDef"; "seq"; "map"; "nth"; "skipn"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "opp"; "mul"; "sub"; "@Corelib.Init.Nat"; "sub"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.FSAddr"; "FR"; "fs_ret"; "fs_entry"; "memcpy_pc"; "@Stdlib.Lists.List"; "filter"; "combine"; "concat"; "flat_map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "SHB"; "leavesA_at"; "mkA"; "segs"; "A_globals"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.VFZ"; "nd0z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.AA"; "ar_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.AD1.ADAddr"; "ad_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.AD2.ADAddr"; "ad_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.AD3.ADAddr"; "ad_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.AD4.ADAddr"; "ad_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.NM.AAAddr"; "aa_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.RA.ReallocAddr"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.VF"; "P_fail"; "P_ok"; "P_zero"; "P_zero2"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.VF.VFAddr"; "vf_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.VP"; "P_push_fail"; "P_push_grown"; "P_push_keep"; "ndp0"; "ndpG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.VP.VPAddr"; "vp_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "tv0"; "vDn"; "vKn"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve Lib_vec_push Lib_vec_finalize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o2.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Lib_realloc. End RA.
Module AA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc. End AA.
Module AD1. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Lib_finalize_shape_dup1. End AD1. Module AD2. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup2. End AD2. Module AD3. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup3. End AD3. Module AD4. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup4. End AD4.
Module NM. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_finalize_shape_name. End NM.
Module VP. Include Lib_vec_push. End VP.
Module VF. Include Lib_vec_finalize. End VF.
Module VFZ. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o2.Lib_vec_finalizeZ. End VFZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import RA.ReallocAddr AA.AAAddr VP.VPAddr VF.VFAddr.

Module FSAddr.
  Definition fs_entry : Z := 0x903e4.
  Definition fs_ret : Z := 0x912ec.
  Definition memcpy_pc : Z := 0x5c9e0.
  Definition FR : Z := 256.
End FSAddr.
Import FSAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47. Definition two40 := RA.two40.
Definition B32 := Lib_vec_reserve.B32. Definition B_EW := Lib_vec_reserve.B_EW.
Definition c4 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S22S11Vo;A1Z4Vv;A3").
Definition c1 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S22S11Vo;A1Z1Vv;A3").

Definition NP : positive := 200%positive.
Definition vB : sv := SVar 12.   Definition vDp : sv := SVar 19.
Definition vAL : sv := SVar 100. Definition vAR : sv := SVar 101. Definition vHD : sv := SVar 102.
Definition vERR : sv := SVar 103. Definition vLINE : sv := SVar 104. Definition vCN : sv := SVar 105. Definition vHP : sv := SVar 106.
Definition vCFG : sv := SVar 107.

Definition sh_d := SVar 110. Definition sh_c := SVar 111. Definition sh_k := SVar 112.
Definition mi_d := SVar 113. Definition mi_c := SVar 114. Definition mi_k := SVar 115.
Definition fv_d := SVar 116. Definition fv_c := SVar 117. Definition fv_k := SVar 118.
Definition mm_d := SVar 119. Definition mm_c := SVar 120. Definition mm_k := SVar 121.
Definition sg_d := SVar 122. Definition sg_c := SVar 123. Definition sg_k := SVar 124.
Definition li_d := SVar 125. Definition li_c := SVar 126. Definition li_k := SVar 127.
Definition lc_d := SVar 128. Definition lc_c := SVar 129. Definition lc_k := SVar 130.
Definition pi_d := SVar 131. Definition pi_c := SVar 132. Definition pi_k := SVar 133.
Definition kb (e : Z) (k : sv) : sv := ltac2:(tb__ "0|0|
S20S13eS11Ve;A1Vk;A3").

Definition piece (lo hi : Z) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S41S11Vlo;A1S11Vhi;A1Vcells;S18A5").
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S16PaA1S11S146S14dA1A1S11Z0A1Vcells;S18A5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S19S4eS14dA1S42S11Z0A1S3S13A1S18A5").
Definition P_alloc : sobj := ltac2:(tb__ "0|1|
S4cZ0M0Z8S0S13S39G0S4fA2S3S13A1A3A3").
Definition P_hdr : sobj := ltac2:(tb__ "0|1|
S4cZ8M0Z20S0S13S39G0S40A2S0S13S39Z10S11Z0A1A2S0S13S39Z18S12cA2S3S13A1A3A3A3A3").
Definition BIG : Z := 288230376151711743.
Definition P_caps : sobj := ltac2:(tb__ "0|4|
S4cZ20M0Z60S0S13S39G0S11S95A1M1A2S0S13S39Z28G1A2S0S13S39Z30G1A2S0S13S39Z38S11S145Z2M2Z14A2A1A2S0S13S39Z40S11S145G2Z18A2A1M3A2S0S13S39Z48G3A2S0S13S39Z50G3A2S0S13S39Z58G1A2S3S13A1A3A3A3A3A3A3A3A3A3").
Definition P_st (err : sv) : sobj := ltac2:(tb__ "0|1|
S4cZ60M0Z78S0S13S84G0Verr;A2S0S13S39Z68S12eA2S0S13S6eZ70S11Z1A1A2S3S13A1A3A3A3A3").
Definition V (o : Z) (d c k : sv) (e : Z) : sobj := ltac2:(tb__ "0|0|
S4cVo;S144Vo;Z20A2S0S13S39Vo;Vd;A2S0S13S39S144Vo;Z8A2Vc;A2S0S13S39S144Vo;Z10A2Vk;A2S0S13S39S144Vo;Z18A2S11Ve;A1A2S3S13A1A3A3A3A3A3").
Definition P_cur (cn hp : sv) : sobj := ltac2:(tb__ "0|1|
S4cZ1e0M0Z1f0S0S13S39G0Vcn;A2S0S13S6eZ1e8Vhp;A2S3S13A1A3A3A3").
Definition P_ff : sobj := ltac2:(tb__ "0|1|
S4cZ370Z3a8S0S13S6eZ375S11Z0A1M0A2S0S13S84Z388G0A2S3S13A1A3A3A3").
Definition Vd (o e : Z) : sobj := ltac2:(tb__ "0|1|
S4cVo;S144Vo;Z20A2S0S13S39Vo;S11Z0A1M0A2S0S13S39S144Vo;Z8A2G0A2S0S13S39S144Vo;Z10A2G0A2S0S13S39S144Vo;Z18A2S11Ve;A1A2S3S13A1A3A3A3A3A3").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S19S4fS11Z0M0A1M1S11Z30A1S0S13S39G0S11S169A1A2S0S13S39Z8S11S16aA1A2S0S13S39Z10G1A2S0S13S39Z18S11S16bA1A2S0S13S39Z20G1A2S0S13S39Z28S133A2S3S13A1A3A3A3A3A3A3S18A5").
Definition O_ar (hd : sv) : sobj := ltac2:(tb__ "0|0|
S19S40S11Z0A1S11Z40A1S163Vhd;A1S18A5").
Definition O_dat (d : sv) (e : Z) (k : sv) : sobj := ltac2:(tb__ "0|0|
S19Vd;S11Z0A1S3cVe;Vk;A2S3S13A1S18A5").

Record vdesc := VD { vd_off : Z; vd_el : Z; vd_d : sv; vd_c : sv; vd_k : sv; vd_dv : positive }.
Definition vMI : ltac2:(tb__ "0|0|
S38") := ltac2:(tb__ "0|0|
S47Z1f0ZcS113S112S114P71A6"). Definition vFV : ltac2:(tb__ "0|0|
S38") := ltac2:(tb__ "0|0|
S47Z210Z4S108S86S109P74A6"). Definition vMM : ltac2:(tb__ "0|0|
S38") := ltac2:(tb__ "0|0|
S47Z230Z4S116S71S117P77A6").
Definition vSG : ltac2:(tb__ "0|0|
S38") := ltac2:(tb__ "0|0|
S47Z250Z4S124S67S125P7aA6"). Definition vLI : ltac2:(tb__ "0|0|
S38") := ltac2:(tb__ "0|0|
S47Z270ZcS110S5fS111P7dA6"). Definition vLC : ltac2:(tb__ "0|0|
S38") := ltac2:(tb__ "0|0|
S47Z290Z4S10dS59S10eP80A6").
Definition vPI : ltac2:(tb__ "0|0|
S38") := ltac2:(tb__ "0|0|
S47Z2b0ZcS122S52S123P83A6"). Definition vSH : ltac2:(tb__ "0|0|
S38") := ltac2:(tb__ "0|0|
S47Z1c0Z80S43S3bS3dP6eA6").
Definition fins : list vdesc := ltac2:(tb__ "0|0|
S0S38S12fS0S38S12dS0S38S130S0S38S132S0S38S7cS0S38S7bS0S38S7dS3S38A1A3A3A3A3A3A3A3").
Definition Vof (v : vdesc) (c : sv) : sobj := ltac2:(tb__ "0|0|
S83S135Vv;A1S54Vv;A1Vc;S5dVv;A1S55Vv;A1A5").
Definition Dof (v : vdesc) : sobj := ltac2:(tb__ "0|0|
S82S54Vv;A1S55Vv;A1S5dVv;A1A3").
Definition Xof (v : vdesc) : sv * sv := ltac2:(tb__ "0|0|
S1S10S10S54Vv;A1S3cS55Vv;A1S5dVv;A1A2A4").
Definition vec_facts (v : vdesc) : list sprop := ltac2:(tb__ "0|3|
S54Vv;A1S10S62Vv;A1S10S5dVv;A1S10S55Vv;A1S25S0S12S1bS134Vv;A1Z4A2S0S12S14R4S16P1eA1M0A2S0S12S14S17S13bR4S3cR1R2A2M1A3G0A2S0S12S14R4S11S78A1A2S0S12S14R3R2A2S0S12S14R2S11S7fA1M2A2S0S12S14G1G2A2S3S12A1A3A3A3A3A3A3A3Te;Tk;Tc;Td;").

Definition builder (err : sv) (shd shc shk : sv) (cn hp : sv) (cs : list sv) : list sobj := ltac2:(tb__ "0|3|
S5S15S0S15Sc3S0S15Sc9S0S15Sc4S0S15SccVerr;A1S0S15S83Z1c0Vshd;Vshc;Vshk;Z80M0A5S0S15Sc5Vcn;Vhp;A2S3S15A1M1A3A3A3A3A3A3S5S15S141S4S38S10A2M2S15G2Sf8S7S38S10R1A3SbS38S10R1A3A2Lvc;S152S38S10S3fVcs;A4A4S0S15Sc8S0S15S6dZ488Z38A2S0S15S6dZ4a8Z30A2S0S15S6dZ4c8G0A2G1A3A3A3A3A3A3").
Definition cs0 : list sv := map vd_c fins.
Definition dats0 : list sobj := ltac2:(tb__ "0|0|
S5S15S141S38S15S69S3fA4S0S15S69S68A1S3S15A1A3A3").
Definition canon (fcells : list cell) (err : sv) (shd shc shk : sv) (cn hp : sv) (cs : list sv) (hd : sv) (dats : list sobj) : list sobj := ltac2:(tb__ "0|1|
S5S15S0S15SbfVfcells;A1S0S15SbeS3S15A1M0A3A3S5S15SfbVerr;Vshd;Vshc;Vshk;Vcn;Vhp;Vcs;A7S5S15S0S15Sc0S0S15Sc1Vhd;A1G0A3A3S5S15Vdats;S15fA3A3A3A3").

Definition xSH : sv * sv := ltac2:(tb__ "0|0|
S1S10S10S4eZe8A1S11Z80A1A4").
Definition X_fs0 : list (sv * sv) := ltac2:(tb__ "0|2|
S5S4S10S10A2M0S0G0S1S10S10S41S11Z518A1A4S0G0S1S10S10S4fS11Z30A1A4S0G0S1S10S10S40S11Z40A1A4S3G0A1M1A3A3A3S5G0S141S38G0S51S3fA4S0G0S51S68A1S0G0S94G1A3A3A3A3").

Definition fs_facts : list sprop := ltac2:(tb__ "0|8|
S5S12S0S12S1bPaM0Z4M1A2S0S12S14S16G0A1M2S11S78A1M3A2S0S12S14S16P1eA1M4S17S13bS4eS14dA1M5S42A3A2S0S12S14G4S4eS144S14dZ10d0A2A1A2S0S12S14G4G5A2S0S12S14G4G2A2S0S12S1cS13dS11N10d0A1S42A3S0S12S1cS13dS42S11S146S145Z2Z26A2A1A1A3S0S12S1bPcG1A2S0S12S14S11S15aA1M6S41A2S0S12S14S17S13bS41S11Z518A1A3G4A2S0S12S14S41G3A2S0S12S1bP64Z3A2S0S12S14G6S4fA2S0S12S14S17S13bS4fS11Z30A1A3G4A2S0S12S14S4fG3A2S0S12S1bP65G1A2S0S12S14S11Z1000A1S40A2S0S12S14S17S13bS40S11Z40A1A3G4A2S0S12S14S40G3A2S0S12S14S5cG4A2S0S12S14S53S11Z1A1A2S0S12S14S60G3A2S0S12S14S11Z7fff7f800000A1M7G4A2S0S12S14G4S11Z7fffff800000A1A2S0S12S14G7G2A2S3S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S5S12S153S12S141S38S8S12A1S93S3fA4A2S93S68A1A3A3").

Definition Pre_fs_S : sstate := ltac2:(tb__ "0|0|
S1eS14fS159S156S1dSeS10A1S6fS3S13A1S50S43S3bS3dS60S53S49S5cS57AaS70S6bSaA9").
Definition Pre_fs : axst := mkA Pre_fs_S X_fs0.

Definition FUEL_fs : nat := 2000%nat.

Definition calls_fs : list Z := ltac2:(tb__ "0|0|
S0S25S168S0S25S164S0S25S165S0S25S166S0S25S167S0S25S172S0S25S178S0S25S150S0S25S14eS3S25A1A3A3A3A3A3A3A3A3A3").
Definition leafF_at (cuts : list Z) (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S142S27Vk;S15cS63Vcuts;VS;Vpc;A4S6cA4").
Definition show_run (cuts : list Z) (S : axst) : ltac2:(tb__ "0|0|
S8S4S25S162A2A1") := ltac2:(tb__ "0|2|
SdS8S2aA1M0A1S8S4S25S162A2M1A1Lx;S2bS15eS63Vcuts;VS;S6A5G0S141S2aG1S160R1A4Lls;S3G1A1Xdx2").

Definition hx (r : nat) : sv := SVar (Pos.of_nat (200 + r)).
Definition pG : sv := SVar 240.
Definition HNEXT : positive := 280%positive.
Definition g8 (g : sv) : sv := SAlu ALU_SLL g (SLit 3).
Definition FEb (g : sv) : list sprop := ltac2:(tb__ "0|1|
S0S12S24S10aVg;A1M0S41A2S0S12S14Vg;S11S148S145Z2Z3dA2Z1A2A1A2S0S12S14G0S41A2S0S12S14S41G0A2S3S12A1A3A3A3A3").
Definition shOf (g : sv) (k : Z) : sv := ltac2:(tb__ "0|0|
S17S13bVg;S11S144S15bVk;A2A1A3").
Definition bofs (k : Z) : sv := ltac2:(tb__ "0|0|
S17S13bS41S11Vk;A1A3").
Definition F_cells : list cell := ltac2:(tb__ "0|0|
S0S13S39N8S16PbA1A2S0S13S39N10S16P1cA1A2S0S13S39N18S16P1dA1A2S0S13S39N20S16P26A1A2S0S13S39N28S16P27A1A2S0S13S39N30S16P28A1A2S0S13S39N38S16P29A1A2S0S13S39N40S16P2aA1A2S0S13S39N48S16P2bA1A2S0S13S39N50S16P2cA1A2S0S13S39N58S16P2dA1A2S0S13S39N60S16P2eA1A2S0S13S39N68S16P2fA1A2S3S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition fs_regs (g : sv) (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
S157S141S2S10S10cS140U0U20A2A4S5S4S2S10A2M0S0G0S1S2S10U2S4eS14dA1A4S0G0S1S2S10U3S16P17A1A4S0G0S1S2S10U4S16P18A1A4S0G0S1S2S10U8S41A4S0G0S1S2S10U9S56Z1e8A1A4S0G0S1S2S10U13S56Z490A1A4S0G0S1S2S10U18S11S15bA1A4S0G0S1S2S10U19S77Vg;Z3dA2A4S0G0S1S2S10U1aS77Vg;Z92A2A4S3G0A1A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition CS (pc : Z) (g : sv) (regs : list (nat * sv)) (fcells : list cell) (err shd shc shk cn hp : sv) (cs : list sv) (hd : sv)
              (dats : list sobj) (facts : list sprop) (nx : positive) : sstate := ltac2:(tb__ "0|0|
S1eVpc;S107Vg;Vregs;A2S156S1dSeS10A1S6fVfcells;Verr;Vshd;Vshc;Vshk;Vcn;Vhp;Vcs;Vhd;Vdats;AaS5S12Vfacts;S0S12S14Vhd;S16P1eA1A2S5S12Sb2Vg;A1S70A3A3A3Vnx;SaA9").

Definition C_E_S : sstate := ltac2:(tb__ "0|1|
S80Z90560S75S0S4S2S10A2M0S1S2S10U1S16PbA1A4S3G0A1A3S81S50S43S3bS3dS60S53S49S5cS57S3S12A1S6aAf").
Definition C_E : axst := mkA C_E_S X_fs0.

Definition eC (v : vdesc) (c : sv) : sv := ltac2:(tb__ "0|0|
S20S13eS11S55Vv;A1A1Vc;A3").

Definition vd_mesh (v : vdesc) : bool := vd_off v <? 624.
Definition AMin1 (c : sv) : batom := AMin c 1 0 1.
Definition CHf (v : vdesc) (c : sv) : list bitem := ltac2:(tb__ "0|9|
ScS8S136A1L_;S92Vv;A1S0S136S139Z1M0Z0M1S0S4S25S137A2M2S1S25S137Z2S138S100Vv;Vc;A2A1M3A4M4S0G2S1S25S137Z60M5S7eVc;A1A4S3G2A1M6A3A3G1A4S0S136S139G1G0S0G2S1S25S137Z4G3A4S0G2S1S25S137Z40S138Vc;A1M7A4G6A3A3G1A4S3S136A1A3M8A3S0S136S139G0G1S0G2G4S0G2S1S25S137G5G7A4G6A3A3G1A4G8A3Xcx2").
Definition CHname : list bitem := ltac2:(tb__ "0|2|
S0S136S13aZ1M0Z0M1Z62A3S0S136S13aG1G0Z44A3S3S136A1A3A3").
Definition PHIe (e : Z) (w k : sv) : bitem := ltac2:(tb__ "0|2|
S139Z1Z0M0S0S4S25S137A2M1S1S25S137Z6S138S3cVe;Vw;A2A1A4S0G1S1S25S137N4S138S3cVe;Vk;A2A1A4S0G1S1S25S137Z20S138S11Ve;A1A1A4S3G1A1A3A3A3G0A4").
Definition KLG := Lib_vec_reserve.KLG.
Definition bd_push (c k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S136Sc2Z80S17S13bVc;S11Z1A1A3Vk;A3S0S136SbdVk;A1S3S136A1A3A3").

Definition finV (i : nat) : bitem := ltac2:(tb__ "0|7|
S139Z1Z0M0S154S38S4S25S137A2M1S38ScS8G1A1L_;S92R1A1S0G1S1S25S137S147Z2S55R1A1A2M2S138S62R1A1M3A1M4A4S0G1S1S25S137Z60M5S7eG3A1A4S3G1A1M6A3A3S0G1S1S25S137S144G2G5A2G4A4G6A3Xcx2Lv;S143S38Vi;S3fA3A4G0A4").
Definition finK (i : nat) : bitem := ltac2:(tb__ "0|1|
S139Z0M0Z1S141S38S4S25S137A2S38S1S25S137S144S147Z4S55R1A1A2Z40A2S138S62R1A1A1A4Lv;S143S38Vi;S3fA3A4G0A4").
Definition CHfrom (i : nat) (cs : list sv) : list bitem := ltac2:(tb__ "0|0|
S0S136S105Vi;A1S0S136S104Vi;A1S3S136A1A3A3").
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S5S4S10S10A2M0S141S38G0S51S3fA4S0G0S51S68A1S0G0S1S10S10S40S11Z40A1A4S3G0A1A3A3A3").
Definition bd0 : list bitem := ltac2:(tb__ "0|0|
S5S136S5eU0S49A2S5S136S97S45S3bS3dA2A3A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S2fS44S3S4S4S10S25A2S10A2A1SfaS2eS5cS6A2A4").
Definition ndE : ndesc := nd0.

Definition main_facts : list sprop := ltac2:(tb__ "0|0|
S0S12S21S1cS13fS3bS11S145Z2Z18A2A1A3A1S3S12A1A3").

Definition vNM : sv := SVar 241. Definition vHq : sv := SVar 242.
Definition regs1 : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2S10A2M0S1S2S10UaS131A4S0G0S1S2S10U14S56Z8A1A4S0G0S1S2S10U1bS56Z1c0A1A4S3G0A1A3A3A3").
Definition regsK : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2S10A2M0S1S2S10U14S56Z8A1A4S0G0S1S2S10U17S77S75Z1A2A4S0G0S1S2S10U1bS56Z1c0A1A4S3G0A1A3A3A3").
Definition CK (pc : Z) (regs : list (nat * sv)) (cs : list sv) : axst := ltac2:(tb__ "0|0|
S15dS80Vpc;S75Vregs;S81S50S43S3bS3dS60S53Vcs;S3eS57S87S6aAfS48A2").
Definition cs2 : list sv := ltac2:(tb__ "0|0|
S0S10S11Z0A1S0S10S86S0S10S71S0S10S67S0S10S5fS0S10S59S0S10S52S3S10A1A3A3A3A3A3A3A3").
Definition cs3 : list sv := ltac2:(tb__ "0|1|
S0S10S11Z0A1M0S0S10G0S0S10S71S0S10S67S0S10S5fS0S10S59S0S10S52S3S10A1A3A3A3A3A3A3A3").
Definition cs4 : list sv := ltac2:(tb__ "0|1|
S0S10S11Z0A1M0S0S10G0S0S10G0S0S10S67S0S10S5fS0S10S59S0S10S52S3S10A1A3A3A3A3A3A3A3").
Definition cs5 : list sv := ltac2:(tb__ "0|1|
S0S10S11Z0A1M0S0S10G0S0S10G0S0S10G0S0S10S5fS0S10S59S0S10S52S3S10A1A3A3A3A3A3A3A3").
Definition cs6 : list sv := ltac2:(tb__ "0|1|
S0S10S11Z0A1M0S0S10G0S0S10G0S0S10G0S0S10G0S0S10S59S0S10S52S3S10A1A3A3A3A3A3A3A3").
Definition cs7 : list sv := ltac2:(tb__ "0|1|
S0S10S11Z0A1M0S0S10G0S0S10G0S0S10G0S0S10G0S0S10G0S0S10S52S3S10A1A3A3A3A3A3A3A3").
Definition cs8 : list sv := ltac2:(tb__ "0|1|
S0S10S11Z0A1M0S0S10G0S0S10G0S0S10G0S0S10G0S0S10G0S0S10G0S3S10A1A3A3A3A3A3A3A3").
Definition C_1 : axst := CK 0x9060c regs1 cs0.
Definition C_2 : axst := CK 0x90818 regsK cs2.
Definition C_3 : axst := CK 0x90994 regsK cs3.
Definition C_4 : axst := CK 0x90b24 regsK cs4.
Definition C_5 : axst := CK 0x90cb4 regsK cs5.
Definition C_6 : axst := CK 0x90d40 regsK cs6.
Definition C_7 : axst := CK 0x90dcc regsK cs7.
Definition C_8 : axst := CK 0x90e58 regsK cs8.
Definition ndK (i : nat) : ndesc := ltac2:(tb__ "0|0|
S2fS44S3S4S4S10S25A2S10A2A1S5S136S5eVi;S49A2S45S3bS3dA2A3S2eS3eS6A2A4").
Definition nd1 : ndesc := ndK 0. Definition nd2 : ndesc := ndK 1. Definition nd3 : ndesc := ndK 2. Definition nd4 : ndesc := ndK 3.
Definition nd5 : ndesc := ndK 4. Definition nd6 : ndesc := ndK 5. Definition nd7 : ndesc := ndK 6.
Definition nd8 : ndesc := ltac2:(tb__ "0|0|
S2fS44S3S4S4S10S25A2S10A2A1S45S3bS3dA2S2eS3eS6A2A4").

Definition cutsC : list Z := ltac2:(tb__ "0|0|
S5S25S0S25Z90560S0S25Z9060cS0S25Z90818S0S25Z90994S0S25Z90b24S0S25Z90cb4S0S25Z90d40S0S25Z90dccS0S25Z90e58S3S25A1A3A3A3A3A3A3A3A3A3SfcA3").
Definition optA (x : option axst) : axst := match x with Some s => s | None => Pre_fs end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leafC_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S142S27Vk;S15cS63S85VS;Vpc;A4S6cA4").
Definition xf_call (F : Z) : list axform := ltac2:(tb__ "0|2|
S0S32S34U1M0S11S146VF;A1M1A1A2S0S32S33G0G1A2S3S32A1A3A3").
Definition nobj (A : axst) : nat := length (ss_objs (ax_S A)).
Definition runC (S : axst) : list axst := ltac2:(tb__ "0|1|
SdS8S2aA1M0A1S8S27A1Lx;S2bS15eS63S85VS;S6A5G0S141S2aS27S2cR1A4Lls;S3S27A1Xdx2").

Definition Pre_nm : axst := NM.Pre_aa.
Definition E_nm_0 : axst := Eval vm_compute in leafC_at C_E NM.AAAddr.aa_entry 0.
Definition E_nm : axst := Eval vm_compute in optA (apply_axforms E_nm_0 (xf_call 64)).
Definition s_nm : wsub := ltac2:(tb__ "0|0|
S0S4S26S10A2S1S26S10P13S17S13bS42S11Z40A1A3A4S14bPaS28SabA1S28Sd2A1A3A3").
Definition R_nm : list sobj := Eval vm_compute in optR (entails_frA E_nm Pre_nm s_nm).
Definition Xk_nm : list (sv * sv) := ltac2:(tb__ "0|1|
S151S4S10S10A2M0G0S9S1aS7S10S10R1A3S40A2A1Lr;S48A3").
Definition perm_nm : list nat := ltac2:(tb__ "0|1|
S5S2S0S2U5S0S2U1S0S2U0S3S2A1M0A3A3A3S5S2S140U6U11A2S5S2S0S2U17S0S2U2G0A3A3S5S2S140U18U8A2S0S2U3S0S2U4G0A3A3A3A3A3A3").
Definition xf_back_nm : list axform := ltac2:(tb__ "0|1|
S0S32S33U1M0Z40A2S0S32S36S11eA1S0S32S35G0A1S3S32A1A3A3A3").
Definition Tn_ok0 : axst := Eval vm_compute in T_afterA3 Pre_nm E_nm s_nm R_nm NM.P_ok Xk_nm.
Definition Tn_fail0 : axst := Eval vm_compute in T_afterA3 Pre_nm E_nm s_nm R_nm NM.P_fail Xk_nm.
Definition Tn_ok : axst := Eval vm_compute in optA (apply_axforms Tn_ok0 xf_back_nm).
Definition Tn_fail : axst := Eval vm_compute in optA (apply_axforms Tn_fail0 xf_back_nm).

Definition go_facts (v : vdesc) : list sprop := ltac2:(tb__ "0|0|
S0S12S14S11Z1000A1S54Vv;A1A2S0S12S14S11Z1A1S62Vv;A1A2S3S12A1A3A3").

Definition Xk_fin (v : vdesc) : list (sv * sv) := ltac2:(tb__ "0|2|
S151S4S10S10A2M0G0SfS9S1aS7S10S10R1A3M1S40A2A1S9S1aG1S54Vv;A1A2A1A2Lr;S48A3").

Definition perm_fin (j : nat) : list nat := ltac2:(tb__ "0|4|
S5S2S0S2U6S0S2U1M0S0S2U0S3S2A1M1A3A3A3S5S2S140U7U11A2S5S2S0S2U18S0S2U2G1A3A3S5S2S140U19M2S149Vj;G0A2M3A2S5S2S0S2U3G1A3S5S2S140S14aG2G3A2S149U8Vj;A2A2S0S2U4S0S2U5G1A3A3A3A3A3A3A3A3").
Definition xf_back_fin (j : nat) : list axform := ltac2:(tb__ "0|1|
S0S32S33U1M0Z40A2S0S32S36S11cVj;A1A1S0S32S35G0A1S3S32A1A3A3A3").

Definition Pre_ad1 : axst := AD1.Pre_ad.
Definition E_ad1_0 : axst := Eval vm_compute in leafC_at C_1 AD1.ADAddr.ad_entry 0.
Definition E_ad1 : axst := Eval vm_compute in optA (apply_axforms (ax_add_facts (go_facts vMI) E_ad1_0) (xf_call 64)).
Definition s_ad1 : wsub := ltac2:(tb__ "0|0|
S0S4S26S10A2S1S26S10P13S17S13bS42S11Z40A1A3A4S14bPaS28Sa1A1S28ScdA1A3A3").
Definition R_ad1 : list sobj := Eval vm_compute in optR (entails_frA E_ad1 Pre_ad1 s_ad1).
Definition T1_ok0 : axst := Eval vm_compute in T_afterA3 Pre_ad1 E_ad1 s_ad1 R_ad1 AD1.P_ok (Xk_fin vMI).
Definition T1_fail0 : axst := Eval vm_compute in T_afterA3 Pre_ad1 E_ad1 s_ad1 R_ad1 AD1.P_fail (Xk_fin vMI).
Definition T1_ok : axst := Eval vm_compute in optA (apply_axforms T1_ok0 (xf_back_fin 1)).
Definition T1_fail : axst := Eval vm_compute in optA (apply_axforms T1_fail0 (xf_back_fin 1)).

Definition Pre_ad2 : axst := AD2.Pre_ad.
Definition E_ad2_0 : axst := Eval vm_compute in leafC_at C_2 AD2.ADAddr.ad_entry 0.
Definition E_ad2 : axst := Eval vm_compute in optA (apply_axforms (ax_add_facts (go_facts vFV) E_ad2_0) (xf_call 64)).
Definition s_ad2 : wsub := ltac2:(tb__ "0|0|
S0S4S26S10A2S1S26S10P13S17S13bS42S11Z40A1A3A4S14bPaS28Sa3A1S28SceA1A3A3").
Definition R_ad2 : list sobj := Eval vm_compute in optR (entails_frA E_ad2 Pre_ad2 s_ad2).
Definition T2_ok0 : axst := Eval vm_compute in T_afterA3 Pre_ad2 E_ad2 s_ad2 R_ad2 AD2.P_ok (Xk_fin vFV).
Definition T2_fail0 : axst := Eval vm_compute in T_afterA3 Pre_ad2 E_ad2 s_ad2 R_ad2 AD2.P_fail (Xk_fin vFV).
Definition T2_ok : axst := Eval vm_compute in optA (apply_axforms T2_ok0 (xf_back_fin 2)).
Definition T2_fail : axst := Eval vm_compute in optA (apply_axforms T2_fail0 (xf_back_fin 2)).

Definition Pre_ad3 : axst := AD3.Pre_ad.
Definition E_ad3_0 : axst := Eval vm_compute in leafC_at C_3 AD3.ADAddr.ad_entry 0.
Definition E_ad3 : axst := Eval vm_compute in optA (apply_axforms (ax_add_facts (go_facts vMM) E_ad3_0) (xf_call 64)).
Definition s_ad3 : wsub := ltac2:(tb__ "0|0|
S0S4S26S10A2S1S26S10P13S17S13bS42S11Z40A1A3A4S14bPaS28Sa5A1S28ScfA1A3A3").
Definition R_ad3 : list sobj := Eval vm_compute in optR (entails_frA E_ad3 Pre_ad3 s_ad3).
Definition T3_ok0 : axst := Eval vm_compute in T_afterA3 Pre_ad3 E_ad3 s_ad3 R_ad3 AD3.P_ok (Xk_fin vMM).
Definition T3_fail0 : axst := Eval vm_compute in T_afterA3 Pre_ad3 E_ad3 s_ad3 R_ad3 AD3.P_fail (Xk_fin vMM).
Definition T3_ok : axst := Eval vm_compute in optA (apply_axforms T3_ok0 (xf_back_fin 3)).
Definition T3_fail : axst := Eval vm_compute in optA (apply_axforms T3_fail0 (xf_back_fin 3)).

Definition Pre_ad4 : axst := AD4.Pre_ad.
Definition E_ad4_0 : axst := Eval vm_compute in leafC_at C_4 AD4.ADAddr.ad_entry 0.
Definition E_ad4 : axst := Eval vm_compute in optA (apply_axforms (ax_add_facts (go_facts vSG) E_ad4_0) (xf_call 64)).
Definition s_ad4 : wsub := ltac2:(tb__ "0|0|
S0S4S26S10A2S1S26S10P13S17S13bS42S11Z40A1A3A4S14bPaS28Sa7A1S28Sd0A1A3A3").
Definition R_ad4 : list sobj := Eval vm_compute in optR (entails_frA E_ad4 Pre_ad4 s_ad4).
Definition T4_ok0 : axst := Eval vm_compute in T_afterA3 Pre_ad4 E_ad4 s_ad4 R_ad4 AD4.P_ok (Xk_fin vSG).
Definition T4_fail0 : axst := Eval vm_compute in T_afterA3 Pre_ad4 E_ad4 s_ad4 R_ad4 AD4.P_fail (Xk_fin vSG).
Definition T4_ok : axst := Eval vm_compute in optA (apply_axforms T4_ok0 (xf_back_fin 4)).
Definition T4_fail : axst := Eval vm_compute in optA (apply_axforms T4_fail0 (xf_back_fin 4)).

Definition Pre_vf : axst := VF.Pre_vf.
Definition xf_vfcall (vidx : nat) (off : Z) : list axform := ltac2:(tb__ "0|2|
S0S32S33Vvidx;Voff;A2S0S32S34U1M0S11N60M1A1A2S0S32S34U2S11N20A1A2S0S32S33G0G1A2S3S32A1A3A3A3A3").
Definition s_vf (E : axst) : wsub := ltac2:(tb__ "0|2|
S0S4S26S10A2M0S1S26S10PaM1S4eS144S14dZ20A2A1A4S0G0S1S26S10P13S17S13bS42S11Z60A1A3A4S14bG1S28VE;A1S28Sd3A1A3A3A3").

Definition perm_vf (pidx : nat) (j : nat) : list nat := ltac2:(tb__ "0|8|
S5S2S0S2U8M0S0S2U1M1S0S2U0S0S2U5S3S2A1M2A3A3A3A3S5S2S140U9M3S149Vpidx;U2M4A2M5A2S5S2S0S2G4G2A3S5S2S140S14aG3G5A2S149U11G5A2A2S5S2S0S2U3G2A3S5S2S140U1aM6S149Vj;G1A2M7A2S5S2S0S2U4G2A3S5S2S140S14aG6G7A2S149G0Vj;A2A2S0S2U6S0S2U7G2A3A3A3A3A3A3A3A3A3A3").
Definition xf_back_vf (pidx : nat) (j : nat) : list axform := ltac2:(tb__ "0|3|
S0S32S33U1M0Z60A2S0S32S33U0Z20M1A2S0S32S33U5G1A2S0S32S36S11fVpidx;Vj;A2A1S0S32S35G0A1M2S0S32G2S0S32S37Vpidx;A1S3S32A1A3A3A3A3A3A3A3").

Definition perm_vfk (pidx : nat) (j : nat) : list nat := ltac2:(tb__ "0|8|
S5S2S0S2U8M0S0S2U1M1S0S2U0S0S2U4S3S2A1M2A3A3A3A3S5S2S140U9M3S149Vpidx;U2M4A2M5A2S5S2S0S2U7G2A3S5S2S140S14aG3G5A2S149U11G5A2A2S5S2S0S2G4G2A3S5S2S140U1aM6S149Vj;G1A2M7A2S5S2S0S2U3G2A3S5S2S140S14aG6G7A2S149G0Vj;A2A2S0S2U5S0S2U6G2A3A3A3A3A3A3A3A3A3A3").
Definition xf_back_vfk (pidx : nat) (j : nat) : list axform := ltac2:(tb__ "0|3|
S0S32S33U1M0Z60A2S0S32S33U0Z20M1A2S0S32S33U4G1A2S0S32S36S120Vpidx;Vj;A2A1S0S32S35G0A1M2S0S32G2S0S32S37Vpidx;A1S3S32A1A3A3A3A3A3A3A3").
Definition PD_vf : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S4S27S2dA2M0S1S27S2dS16eS161A4S0G0S1S27S2dS16cS170A4S0G0S1S27S2dS16dS171A4S0G0S1S27S2dS16fS161A4S3G0A1A3A3A3A3").
Definition Xk_vf (v : vdesc) : list (sv * sv) := ltac2:(tb__ "0|2|
S151S4S10S10A2M0G0SfS9S1aS7S10S10R1A3M1S40A2A1S9S1aG1S54Vv;A1A2A1A2Lr;S48A3").

Definition E_vf5_0 : axst := Eval vm_compute in leafC_at C_5 vf_entry 0.
Definition E_vf5 : axst := Eval vm_compute in optA (apply_axforms E_vf5_0 (xf_vfcall 12 624)).
Definition s_vf5 : wsub := s_vf E_vf5.
Definition R_vf5 : list sobj := Eval vm_compute in optR (entails_frA E_vf5 Pre_vf s_vf5).
Definition T5_z : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf5 s_vf5 R_vf5 VF.P_zero (Xk_vf vLI)) (xf_back_vf 12 5)).
Definition T5_z2 : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf5 s_vf5 R_vf5 VF.P_zero2 (Xk_vf vLI)) (xf_back_vf 12 5)).
Definition T5_f : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf5 s_vf5 R_vf5 VF.P_fail (Xk_vf vLI)) (xf_back_vfk 12 5)).
Definition T5_ok : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf5 s_vf5 R_vf5 VF.P_ok (Xk_vf vLI)) (xf_back_vfk 12 5)).

Definition E_vf6_0 : axst := Eval vm_compute in leafC_at C_6 vf_entry 0.
Definition E_vf6 : axst := Eval vm_compute in optA (apply_axforms E_vf6_0 (xf_vfcall 13 656)).
Definition s_vf6 : wsub := s_vf E_vf6.
Definition R_vf6 : list sobj := Eval vm_compute in optR (entails_frA E_vf6 Pre_vf s_vf6).
Definition T6_z : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf6 s_vf6 R_vf6 VF.P_zero (Xk_vf vLC)) (xf_back_vf 13 6)).
Definition T6_z2 : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf6 s_vf6 R_vf6 VF.P_zero2 (Xk_vf vLC)) (xf_back_vf 13 6)).
Definition T6_f : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf6 s_vf6 R_vf6 VF.P_fail (Xk_vf vLC)) (xf_back_vfk 13 6)).
Definition T6_ok : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf6 s_vf6 R_vf6 VF.P_ok (Xk_vf vLC)) (xf_back_vfk 13 6)).

Definition E_vf7_0 : axst := Eval vm_compute in leafC_at C_7 vf_entry 0.
Definition E_vf7 : axst := Eval vm_compute in optA (apply_axforms E_vf7_0 (xf_vfcall 14 688)).
Definition s_vf7 : wsub := s_vf E_vf7.
Definition R_vf7 : list sobj := Eval vm_compute in optR (entails_frA E_vf7 Pre_vf s_vf7).
Definition T7_z : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf7 s_vf7 R_vf7 VF.P_zero (Xk_vf vPI)) (xf_back_vf 14 7)).
Definition T7_z2 : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf7 s_vf7 R_vf7 VF.P_zero2 (Xk_vf vPI)) (xf_back_vf 14 7)).
Definition T7_f : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf7 s_vf7 R_vf7 VF.P_fail (Xk_vf vPI)) (xf_back_vfk 14 7)).
Definition T7_ok : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf7 s_vf7 R_vf7 VF.P_ok (Xk_vf vPI)) (xf_back_vfk 14 7)).

Definition Pre_vp : axst := VP.Pre_vp.
Definition xf_vpcall : list axform := ltac2:(tb__ "0|2|
S0S32S33U6Z1c0A2S0S32S34U1M0S11N30M1A1A2S0S32S33G0G1A2S3S32A1A3A3A3").
Definition E_vp0 : axst := Eval vm_compute in leafC_at C_8 vp_entry 0.
Definition E_vp : axst := Eval vm_compute in optA (apply_axforms E_vp0 xf_vpcall).
Definition s_vp : wsub := ltac2:(tb__ "0|0|
S0S4S26S10A2S1S26S10P13S17S13bS42S11Z30A1A3A4S14bPaS28Sb0A1S28Sd4A1A3A3").
Definition R_vp : list sobj := Eval vm_compute in optR (entails_frA E_vp Pre_vp s_vp).
Definition PD_vp : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S4S27S2dA2M0S1S27S2dS175S176A4S0G0S1S27S2dS173S30S179S3S4S4S10S25A2S10A2A1S3S136A1A3A4S0G0S1S27S2dS174S177S17aS17bA2A4S3G0A1A3A3A3").
Definition Xk_vp : list (sv * sv) := ltac2:(tb__ "0|2|
S151S4S10S10A2M0G0SfS9S1aS7S10S10R1A3M1S4fA2A1S9S1aG1S43A2A1A2Lr;S48A3").

Definition perm_vp : list nat := ltac2:(tb__ "0|4|
S5S2S0S2U7M0S0S2U1S0S2U0S3S2A1M1A3A3A3S5S2S140U8U4M2A2S5S2S0S2U2G1A3S5S2S140UcM3G3A2S5S2S0S2U3S0S2U18G1A3A3S5S2S140U19G0A2S0S2G2S0S2U5S0S2U6G1A3A3A3A3A3A3A3A3A3").
Definition xf_back_vp : list axform := ltac2:(tb__ "0|1|
S0S32S33U1M0Z30A2S0S32S36S121A1S0S32S35G0A1S0S32S37U6A1S3S32A1A3A3A3A3").
Definition T_pk0 : axst := Eval vm_compute in T_afterA3 Pre_vp E_vp s_vp R_vp VP.P_push_keep Xk_vp.
Definition T_pf0 : axst := Eval vm_compute in T_afterA3 Pre_vp E_vp s_vp R_vp VP.P_push_fail Xk_vp.
Definition T_pg0 : axst := Eval vm_compute in T_afterA3 Pre_vp E_vp s_vp R_vp VP.P_push_grown Xk_vp.
Definition T_pk : axst := Eval vm_compute in optA (apply_axforms T_pk0 xf_back_vp).
Definition T_pf : axst := Eval vm_compute in optA (apply_axforms T_pf0 xf_back_vp).
Definition T_pg : axst := Eval vm_compute in optA (apply_axforms T_pg0 xf_back_vp).

Definition hse_fact : sprop := ltac2:(tb__ "0|0|
S14S11S15aA1S43A2").

Definition top_factK : sprop := ltac2:(tb__ "0|0|
S14S17S13bS43S3cZ80S3dA2A3S11Z7fffff800000A1A2").
Definition T_pkF : axst := ltac2:(tb__ "0|0|
S14cS0S12S10bS0S12S129S3S12A1A3A3Sf4A2").
Definition vDg : sv := SVar 320. Definition vKg : sv := SVar 321.
Definition top_factG : sprop := ltac2:(tb__ "0|0|
S14S17S13bS91S3cZ80S7aA2A3S11Z7fffff800000A1A2").
Definition T_pgF : axst := ltac2:(tb__ "0|0|
S14cS0S12S128S3S12A1A3Sf2A2").

Definition slotx (d : sv) : sv := ltac2:(tb__ "0|0|
S17S13bVd;S3cZ80S3bA2A3").
Definition dst_obj (d : sv) : sobj := ltac2:(tb__ "0|0|
S19S126Vd;A1S11Z0A1S11Z80A1S3S13A1S18A5").
Definition mid_obj (d : sv) : sobj := ltac2:(tb__ "0|2|
S19Vd;S3cZ80M0S3bA2M1S17S13bG1S11G0A1A3S3S13A1S18A5").
Definition src_obj : sobj := ltac2:(tb__ "0|0|
S19S4eZe8A1S11Z0A1S11Z80A1S3S13A1S18A5").
Definition fmid_obj : sobj := ltac2:(tb__ "0|0|
S19S16PaA1S11Ne8A1S11N68A1S3S13A1S18A5").
Definition xf_mcall : list axform := ltac2:(tb__ "0|2|
S0S32S34U1cS3cZ80M0S3bA2M1A2S0S32S34U1dS17S13bG1S11G0A1A3A2S0S32S34U0S11Ne8A1A2S0S32S34U1S11N68A1A2S3S32A1A3A3A3A3").
Definition Pre_mc : axst := Pre_memcpy memcpy_pc.
Definition L_mc : axst := L_memcpy (ae_ret_asan_memcpy AE_A).
Definition s_m (E : axst) (d k : sv) : wsub := ltac2:(tb__ "0|2|
S0S4S26S10A2M0S1S26S10P35Vd;A4S0G0S1S26S10P36S3cZ80M1Vk;A2A4S0G0S1S26S10P37S4eZe8A1A4S0G0S1S26S10P38S11G1A1A4S14bPaS28VE;A1S28Sd1A1A3A3A3A3A3").
Definition E_mk0 : axst := Eval vm_compute in leafC_at T_pkF memcpy_pc 0.
Definition E_mg0 : axst := Eval vm_compute in leafC_at T_pgF memcpy_pc 0.
Definition E_mk1 : axst := Eval vm_compute in optA (apply_axforms E_mk0 xf_mcall).
Definition E_mg1 : axst := Eval vm_compute in optA (apply_axforms E_mg0 xf_mcall).
Definition E_mc (E1 : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S29VE1;S155S28VE1;A1U1fSffVd;A1A3A2S27S29R1S155S28R1A1U1S127A3A2TE2;").
Definition E_mk : axst := Eval vm_compute in E_mc E_mk1 sh_d.
Definition E_mg : axst := Eval vm_compute in E_mc E_mg1 vDg.
Definition R_mk : list sobj := Eval vm_compute in optR (entails_frA E_mk Pre_mc (s_m E_mk sh_d sh_k)).
Definition R_mg : list sobj := Eval vm_compute in optR (entails_frA E_mg Pre_mc (s_m E_mg vDg vKg)).
Definition T_mk0 : axst := Eval vm_compute in T_afterA Pre_mc E_mk (s_m E_mk sh_d sh_k) R_mk L_mc.
Definition T_mg0 : axst := Eval vm_compute in T_afterA Pre_mc E_mg (s_m E_mg vDg vKg) R_mg L_mc.

Definition perm_m : list nat := ltac2:(tb__ "0|1|
S5S2S0S2U5S0S2U2S0S2U6S0S2U0S3S2A1M0A3A3A3A3S5S2S140U7U1aA2S0S2U21S0S2U1S0S2U22S0S2U3S0S2U4G0A3A3A3A3A3A3A3").
Definition xf_mback : list axform := ltac2:(tb__ "0|2|
S0S32S36S11dA1S0S32S35U0A1M0S0S32G0S0S32S35U1cA1M1S0S32G1S3S32A1A3A3A3A3A3").
Definition T_mc1 (T0 : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S29VT0;S155S28VT0;A1U1S115Vd;A1A3A2S27S29R1S155S28R1A1U2S106A3A2TT1;").
Definition T_mk1 : axst := T_mc1 T_mk0 sh_d.
Definition T_mg1 : axst := T_mc1 T_mg0 vDg.
Definition T_mk : axst := Eval vm_compute in optA (apply_axforms T_mk1 xf_mback).
Definition T_mg : axst := Eval vm_compute in optA (apply_axforms T_mg1 xf_mback).

Definition qD : sv := SVar 260. Definition qK : sv := SVar 261. Definition qHD : sv := SVar 262. Definition qERR : sv := SVar 263.
Definition qcs : list sv := ltac2:(tb__ "0|0|
S141S2S10S2S16S17cS14aU108R1A2A1A1Li;S140U0U7A2A4").
Definition post_fs (a0 : sv) (err shd shc shk hp : sv) (cs : list sv) (hd : sv) (dats : list sobj) (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|1|
S15dS1eS14eS157S158S6bA1S0S4S2S10A2M0S1S2S10UaVa0;A4S3G0A1A3A2S156S1dSeS10A1S6fS3S13A1Verr;Vshd;Vshc;Vshk;S60Vhp;Vcs;Vhd;Vdats;AaS5S12Vfacts;S0S12S14Vhd;S16P1eA1A2S70A3A3S6aSaA9VX;A2").

Definition P_nop : axst := ltac2:(tb__ "0|0|
S65S11Z1A1S50S43S3bS3dS53S49S5cS57S3S12A1S48Ab").
Definition nd_nop : ndesc := nd0.

Definition dats_ok : list sobj := ltac2:(tb__ "0|0|
S5S15S141S38S15S69S3fA4S0S15S82S46Z80S4dA3S3S15A1A3A3").
Definition X_ok : list (sv * sv) := ltac2:(tb__ "0|2|
S5S4S10S10A2M0S0G0S1S10S10S41S11Z518A1A4S0G0S1S10S10S4fS11Z30A1A4S0G0S1S10S10S40S11Z40A1A4S3G0A1M1A3A3A3S5G0S141S38G0S51S3fA4S0G0S1S10S10S46S3cZ80S4dA2A4S0G0S94G1A3A3A3A3").
Definition ok_facts : list sprop := ltac2:(tb__ "0|3|
S5S12S0S12S14S17S13bS3bS11Z1A1A3S4dA2S0S12S1bP104Z4A2S0S12S14S11Z1000A1S46A2S0S12S14S11S15aA1S46A2S0S12S14S46S16P1eA1M0A2S0S12S14S17S13bS46S3cZ80S4dA2M1A3G0A2S0S12S14S46S11S78A1A2S0S12S14S4dS11S7fA1M2A2S0S12S14G1G2A2S3S12A1A3A3A3A3A3A3A3A3A3S87A3").
Definition P_ok : axst := ltac2:(tb__ "0|1|
S65S11Z1A1M0S50S46S17S13bS3bG0A3S4dS11Z0A1SfdS5bSfeS11bSf9Ab").
Definition tv_ok : list (sv * sv) := ltac2:(tb__ "0|1|
S5S4S10S10A2M0S141S38G0S51S3fA4S0G0S1S10S10S46S3cZ80S4dA2A4S0G0S1S10S10S40S11Z40A1A4S3G0A1A3A3A3").
Definition nd_ok : ndesc := ltac2:(tb__ "0|0|
S2fS12bS3S4S4S10S25A2S10A2A1S45S3bS4dA2S2eS5bS6A2A4").

Definition fail_facts : list sprop := ltac2:(tb__ "0|1|
S0S12S21S1cS13cS1fS6Q20S50A3S11Z0A1A3A1S141S4S38S10A2M0S12G0S14SbS38S10R1A3S5dS7S38S10R1A3A1A2Lvc;S152S38S10S3fS66A4A4A3").
Definition P_fail : axst := ltac2:(tb__ "0|0|
S65S11Z0A1S50S43S3bS3dS53S66S5bS57S101S48Ab").
Definition nd_fail_t : ndesc := ltac2:(tb__ "0|0|
S2fS44S3S4S4S10S25A2S10A2A1S3S136A1S2eS5bS6A2A4").
Definition nd_fail_f : ndesc := ltac2:(tb__ "0|0|
S2fS44S3S4S4S10S25A2S10A2A1S3S136A1S2eS5bSaA2A4").

Definition failz_facts : list sprop := ltac2:(tb__ "0|1|
S5S12S0S12S1cS13cS1fS6Q20S50A3S11Z0A1A3S0S12S14S11Z2A1S76A2S0S12S14S76S11Z7A1A2S3S12A1A3A3A3S141S4S38S10A2M0S12G0S14SbS38S10R1A3S5dS7S38S10R1A3A1A2Lvc;S152S38S10S3fS66A4A4A3").
Definition P_failz : axst := ltac2:(tb__ "0|0|
S65S11Z0A1S76S43S3bS3dS53S66S5bS57S103S48Ab").

Definition vGH : sv := SVar 259.
Definition ghZ : sprop := SPEq vGH (SLit 0).
Definition T5_zG : axst := ltac2:(tb__ "0|0|
S14cS0S12S58S3S12A1A3SdfA2").   Definition T5_z2G : axst := ltac2:(tb__ "0|0|
S14cS0S12S58S3S12A1A3Se0A2").
Definition T6_zG : axst := ltac2:(tb__ "0|0|
S14cS0S12S58S3S12A1A3Se5A2").   Definition T6_z2G : axst := ltac2:(tb__ "0|0|
S14cS0S12S58S3S12A1A3Se6A2").
Definition T7_zG : axst := ltac2:(tb__ "0|0|
S14cS0S12S58S3S12A1A3SebA2").   Definition T7_z2G : axst := ltac2:(tb__ "0|0|
S14cS0S12S58S3S12A1A3SecA2").
Definition s_gh (T : axst) : wsub := ltac2:(tb__ "0|1|
S0S4S26S10A2S1S26S10P103S11Z0A1A4S14bS6bS28VT;A1M0G0A3A3").

Definition z0 : sv := SLit 0.

Definition ndTok (j : nat) (hq : sv) : ndesc := ltac2:(tb__ "0|0|
S2fS44S3S4S4S10S25A2S10A2A1S5S136S5eVj;S49A2S45S3bS3dA2A3S2eVhq;S6A2A4").
Definition ndTf (j : nat) (hq : sv) : ndesc := ltac2:(tb__ "0|0|
S2fS44S3S4S4S10S25A2S10A2A1S5S136S5eVj;S49A2S45S3bS3dA2A3S2eVhq;SaA2A4").

Definition ndTz (j : nat) (v : vdesc) : ndesc := ltac2:(tb__ "0|0|
S2fS44S3S4S4S10S25A2S10A2A1S5S136S96Vv;S62Vv;A1A2S5S136S5eVj;S49A2S45S3bS3dA2A3A3S2eS3eS6A2A4").
Definition vHa : sv := SVar 321.
Definition vHv : sv := SVar 322.
Definition ndPk : ndesc := ltac2:(tb__ "0|0|
S2fS44S3S4S4S10S25A2S10A2A1S45S3bS3dA2S2eS3eS6A2A4").
Definition tv_g : list (sv * sv) := ltac2:(tb__ "0|1|
S5S4S10S10A2M0S141S38G0S51S3fA4S0G0S1S10S10S91S3cZ80S7aA2A4S0G0S1S10S10S40S11Z40A1A4S3G0A1A3A3A3").
Definition ndPg : ndesc := ltac2:(tb__ "0|0|
S2fS12aS3S4S4S10S25A2S10A2A1S45S3bS7aA2S2eS3eS6A2A4").
Definition ndPf : ndesc := ltac2:(tb__ "0|0|
S2fS44S3S4S4S10S25A2S10A2A1S3S136A1S2eS3eS6A2A4").
Definition cutsE : list edescA := ltac2:(tb__ "0|18|
S0S4S4S27S2dA2M0S4S25S10A2M1A2M2S1G0G1S1S27S2dS6cS118A4S1S25S10Zc8S3aA4A4S0G2S1G0G1S1S27S2dSa0S64A4S1S25S10ZbeS3aA4A4S0G2S1G0G1S1S27S2dSf7S4bU0M3S61A2A4S1S25S10Zb4S3aA4M4A4S0G2S1G0G1S1S27S2dSf6S4aG3S5cA2A4G4A4S0G2S1G0G1S1S27S2dS98S88A4S1S25S10Z96S3aA4A4S0G2S1G0G1S1S27S2dSd6S4bU1M5S61A2A4S1S25S10Z91S3aA4M6A4S0G2S1G0G1S1S27S2dSd5S4aG5S3eA2A4G6A4S0G2S1G0G1S1S27S2dS99S89A4S1S25S10Z8cS3aA4A4S0G2S1G0G1S1S27S2dSd8S4bU2M7S61A2A4S1S25S10Z87S3aA4M8A4S0G2S1G0G1S1S27S2dSd7S4aG7S3eA2A4G8A4S0G2S1G0G1S1S27S2dS9aS8aA4S1S25S10Z82S3aA4A4S0G2S1G0G1S1S27S2dSdaS4bU3M9S61A2A4S1S25S10Z7dS3aA4MaA4S0G2S1G0G1S1S27S2dSd9S4aG9S3eA2A4GaA4S0G2S1G0G1S1S27S2dS9bS8bA4S1S25S10Z78S3aA4A4S0G2S1G0G1S1S27S2dSdcS4bU4MbS61A2A4S1S25S10Z73S3aA4McA4S0G2S1G0G1S1S27S2dSdbS4aGbS3eA2A4GcA4S0G2S1G0G1S1S27S2dS9cS8cA4S1S25S10Z6eS3aA4A4S0G2S1G0G1S1S27S2dSe2S5aU5MdS7cA2MeA4S1S25S10Z69S3aA4MfA4S0G2S1G0G1S1S27S2dSdeS4bGdS79A2A4GfA4S0G2S1G0G1S1S27S2dSddS4aGdS3eA2A4GfA4S0G2S1G0G1S1S27S2dSe1GeA4GfA4S0G2S1G0G1S1S27S2dS9dS8dA4S1S25S10Z64S3aA4A4S0G2S1G0G1S1S27S2dSe8S5aU6M10S7bA2M11A4S1S25S10Z5fS3aA4M12A4S0G2S1G0G1S1S27S2dSe4S4bG10S79A2A4G12A4S0G2S1G0G1S1S27S2dSe3S4aG10S3eA2A4G12A4S0G2S1G0G1S1S27S2dSe7G11A4G12A4S0G2S1G0G1S1S27S2dS9eS8eA4S1S25S10Z5aS3aA4A4S0G2S1G0G1S1S27S2dSeeS5aU7M13S7dA2M14A4S1S25S10Z55S3aA4M15A4S0G2S1G0G1S1S27S2dSeaS4bG13S79A2A4G15A4S0G2S1G0G1S1S27S2dSe9S4aG13S3eA2A4G15A4S0G2S1G0G1S1S27S2dSedG14A4G15A4S0G2S1G0G1S1S27S2dS9fS8fA4S1S25S10Z50S3aA4A4S0G2S1G0G1S1S27S2dSf5S74A4S1S25S10Z4bS3aA4M16A4S0G2S1G0G1S1S27S2dSf1S72A4G16A4S0G2S1G0G1S1S27S2dSf3S73A4G16A4S0G2S1G0G1S1S27S2dSf0S74A4S1S25S10Z41S3aA4M17A4S0G2S1G0G1S1S27S2dSefS73A4G17A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition retleaf (S : axst) (k : nat) : axst := ltac2:(tb__ "0|0|
S10fVS;S14eVk;A3").
Definition FL_E0 : axst := Eval vm_compute in retleaf C_E 0.   Definition FL_E1 : axst := Eval vm_compute in retleaf C_E 1.
Definition FL_50 : axst := Eval vm_compute in retleaf T5_zG 0.  Definition FL_51 : axst := Eval vm_compute in retleaf T5_zG 1.
Definition FL_60 : axst := Eval vm_compute in retleaf T6_zG 0.  Definition FL_61 : axst := Eval vm_compute in retleaf T6_zG 1.
Definition FL_70 : axst := Eval vm_compute in retleaf T7_zG 0.  Definition FL_71 : axst := Eval vm_compute in retleaf T7_zG 1.
Definition FL_p0 : axst := Eval vm_compute in retleaf T_pf 0.  Definition FL_p1 : axst := Eval vm_compute in retleaf T_pf 1.
Definition fails_t : list edescA := ltac2:(tb__ "0|7|
S0S4S4S27S2dA2M0S4S25S10A2M1A2M2S1G0G1S1S27S2dSb9S64A4S1S25S10Z5S3aA4M3A4S0G2S1G0G1S1S27S2dSbaS64A4G3A4S0G2S1G0G1S1S27S2dSb3S5aU5S7cA2M4A4G3A4S0G2S1G0G1S1S27S2dSb4G4A4G3A4S0G2S1G0G1S1S27S2dSb5S5aU6S7bA2M5A4G3A4S0G2S1G0G1S1S27S2dSb6G5A4G3A4S0G2S1G0G1S1S27S2dSb7S5aU7S7dA2M6A4G3A4S0G2S1G0G1S1S27S2dSb8G6A4G3A4S0G2S1G0G1S1S27S2dSbbS72A4G3A4S0G2S1G0G1S1S27S2dSbcS72A4G3A4S3G2A1A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|6|
S5S4S4S27S2dA2M0S4S25S10A2M1A2M2S0G2S1G0G1S1S27S2dSacS64A4S1S25S10Zb9S3aA4A4S0G2S1G0G1S1S27S2dSa2S88A4S1S25S10Z94S3aA4A4S0G2S1G0G1S1S27S2dSa4S89A4S1S25S10Z8aS3aA4A4S0G2S1G0G1S1S27S2dSa6S8aA4S1S25S10Z80S3aA4A4S0G2S1G0G1S1S27S2dSa8S8bA4S1S25S10Z76S3aA4A4S0G2S1G0G1S1S27S2dSadS8cA4S1S25S10Z6cS3aA4A4S0G2S1G0G1S1S27S2dSaeS8dA4S1S25S10Z62S3aA4A4S0G2S1G0G1S1S27S2dSafS8eA4S1S25S10Z58S3aA4A4S0G2S1G0G1S1S27S2dSb1S8fA4S1S25S10Z4eS3aA4A4S0G2S1G0G1S1S27S2dSaaS74A4S1S25S10Z46S3aA4M3A4S0G2S1G0G1S1S27S2dSa9S73A4G3A4S3G2A1M4A3A3A3A3A3A3A3A3A3A3A3S5S31S102S0G2S1G0G1S1S27S2dScaS119A4S1S25S10Z0S3aA4M5A4S0G2S1G0G1S1S27S2dScbS11aA4G5A4S0G2S1G0G1S1S27S2dSc6S90A4G5A4S0G2S1G0G1S1S27S2dSc7S90A4G5A4G4A3A3A3A3A3A3").

Definition rdiff (C : sstate) (A : axst) : list (nat * sv * sv) := ltac2:(tb__ "0|3|
S151S4S4S2S10A2M0S10A2M1G1S9S1aSbS2S10S7G0S10R1A3A3SbG0S10R1A3A2A1Lp;S141S2G1S2S1G0S10S1S2S10R1S142S10R1S23S28VA;A1A1S11Z0A1M2A4A4S142S10R1S23VC;A1G2A4A4Li;S140U0U20A2A4A3").
