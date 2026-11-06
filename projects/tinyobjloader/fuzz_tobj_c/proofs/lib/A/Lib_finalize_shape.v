(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_021.   (* [comment removed for export] *)
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "true"; "list"; "negb"; "fst"; "option"; "false"; "snd"; "bool"; "None"; "andb"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "cell"; "SPUle"; "SAlu"; "sobj"; "SVar"; "DUnknown"; "mkObj"; "sv_eqb"; "SPAlign"; "SPBranch"; "ss_objs"; "FcsrFrm0"; "SPEq"; "mkSS"; "SExt"; "SMd"; "SPNot"; "mkCell"; "ss_regs"; "ob_base"; "ob_cells"; "ss_facts"; "ss_pc"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "sym_runA"; "ax_setS"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "NDA"; "AHead"; "AOpen"; "ND"; "edescA"; "tv_factsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape"; "c8"; "vdesc"; "z0"; "sh_c"; "sh_k"; "vHq"; "pG"; "vHD"; "bofs"; "shOf"; "sh_d"; "tv0"; "vAR"; "cs0"; "vERR"; "bd_push"; "vHP"; "dats0"; "kb"; "vCN"; "vDp"; "fins"; "CHfrom"; "HNEXT"; "CS"; "main_facts"; "vB"; "qD"; "vCAPl"; "NP"; "VD"; "pi_c"; "piece"; "qK"; "vAL"; "vUo"; "X_fs0"; "Xof"; "lc_c"; "ndE"; "ndTf"; "ndTok"; "vd_d"; "vd_el"; "FUEL_fs"; "li_c"; "ndTz"; "pfit"; "qHD"; "vd_k"; "F_cells"; "Pre_vf"; "vd_c"; "Pre_ad"; "Pre_fs"; "nd_fail_f"; "pGA"; "pfit0"; "post_fs"; "qcs"; "sg_c"; "spm"; "two40"; "vHa"; "vNM"; "vSH"; "C_1"; "C_slow"; "Dof"; "Vd"; "am_np"; "c1"; "canon"; "fs_facts"; "g8"; "ghZ"; "mm_c"; "ndO"; "ndPf"; "ndPg"; "ndPk"; "qERR"; "two47"; "vDg"; "vHv"; "vKg"; "vLC"; "vLI"; "vPI"; "vU"; "vUg"; "AMin1"; "B32"; "C_nz"; "E_m"; "F2_cells"; "F3_cells"; "F4_cells"; "F5_cells"; "F6_cells"; "F7_cells"; "FEa"; "O_D"; "O_dat"; "P_fail"; "P_failz"; "T_mg0"; "T_mk0"; "V"; "X_N0"; "X_nohead"; "bd0"; "bd_m"; "bd_rest"; "c4"; "cs8"; "cutpcsN"; "cutsC"; "fv_c"; "leafC_at"; "mi_c"; "mid_obj"; "nd1"; "nd2"; "nd3"; "nd4"; "nd5"; "nd6"; "nd7"; "nd8"; "ndMok"; "ndS"; "ndZ"; "optA"; "pGH"; "pN"; "vCAP"; "vNXl"; "vd_mesh"; "vd_off"; "vec_facts"; "BIG"; "CHf"; "CHname"; "C_2"; "C_3"; "C_4"; "C_5"; "C_6"; "C_7"; "C_8"; "C_E"; "C_open"; "E_ad1"; "E_ad1_0"; "E_ad2"; "E_ad2_0"; "E_ad3"; "E_ad3_0"; "E_ad4"; "E_ad4_0"; "E_mg0"; "E_mk0"; "E_vf5"; "E_vf5_0"; "E_vf6"; "E_vf6_0"; "E_vf7"; "E_vf7_0"; "E_vp"; "E_vp0"; "F8_cells"; "FEb"; "FEh"; "FL_50"; "FL_51"; "FL_60"; "FL_61"; "FL_70"; "FL_71"; "FL_E0"; "FL_E1"; "FL_p0"; "FL_p1"; "KLG"; "O_F"; "O_al"; "O_ar"; "O_hdrN"; "O_slotN"; "PHIe"; "P_alloc"; "P_caps"; "P_cur"; "P_ff"; "P_hdr"; "P_nop"; "P_ok"; "P_st"; "Pre_m"; "Pre_ms"; "Pre_vp"; "T1_fail"; "T1_ok"; "T2_fail"; "T2_ok"; "T3_fail"; "T3_ok"; "T4_fail"; "T4_ok"; "T5_f"; "T5_ok"; "T5_z"; "T5_zG"; "T6_f"; "T6_ok"; "T6_z"; "T6_zG"; "T7_f"; "T7_ok"; "T7_z"; "T7_zG"; "T_mg"; "T_mk"; "T_mnull"; "T_mok"; "T_mok0"; "T_pf"; "T_pg"; "T_pgF"; "T_pk"; "T_pkF"; "V_XB"; "V_XL"; "Vof"; "X_fit"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nzret"; "X_nzret3"; "X_ok"; "X_open0"; "X_sret"; "X_sret3"; "am_nz"; "am_open"; "bd_nz"; "bd_open"; "blkN"; "builder"; "calls_fs"; "cs2"; "cs3"; "cs4"; "cs5"; "cs6";
"cs7"; "dats_ok"; "eC"; "fail_facts"; "fails_t"; "failz_facts"; "finK"; "finV"; "find_idxb"; "fs_regs"; "fv_d"; "fv_k"; "hse_fact"; "hx"; "lc_d"; "lc_k"; "li_d"; "li_k"; "mi_d"; "mi_k"; "mm_d"; "mm_k"; "nd0"; "ndM"; "nd_nop"; "nd_ok"; "nz_facts"; "ok_facts"; "optR"; "p1"; "p2"; "p3"; "p5"; "p6"; "perm_fin"; "perm_m"; "perm_vf"; "perm_vfk"; "perm_vp"; "pi_d"; "pi_k"; "rdiff"; "sg_d"; "sg_k"; "slotx"; "top_factG"; "top_factK"; "tv_g"; "tv_m"; "tv_ok"; "ug_facts"; "vCFG"; "vFV"; "vLINE"; "vMI"; "vMM"; "vNX"; "vSG"; "vUD"; "vd_dv"; "xf_vfcall"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "BC_GE"; "BC_GEU"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXSelect"; "AXSplit"; "AXMerge"; "AXRebase"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "batom"; "ASv"; "BI"; "BIc"; "KU"; "@Corelib.Lists.ListDef"; "seq"; "map"; "nth"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "sub"; "opp"; "mul"; "@Corelib.Init.Nat"; "sub"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape.FSAddr"; "FR"; "fs_ret"; "fs_entry"; "memset_pc"; "@Stdlib.Lists.List"; "filter"; "combine"; "concat"; "flat_map"; "removelast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "leavesA_at"; "segs"; "SHB"; "A_globals"; "mkA"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "POT"; "e32"; "drop_lastA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape.RA.ReallocAddr"; "malloc_pc"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape.VF.VFAddr"; "vf_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape.AA"; "ar_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape.AD.ADAddr"; "ad_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape.VF"; "P_fail"; "P_ok"; "P_zero"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape.VFZ"; "nd0z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape.VP"; "P_push_fail"; "P_push_grown"; "P_push_keep"; "ndp0"; "ndpG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape.VP.VPAddr"; "vp_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "tv0"; "vDn"; "vKn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "Pre_malloc"; "UStopLe"; "ulink"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR ResidualA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve Lib_vec_push Lib_vec_finalize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ei.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Lib_realloc. End RA.
Module AA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc. End AA.
Module AD. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup. End AD.
Module VP. Include Lib_vec_push. End VP.
Module VF. Include Lib_vec_finalize. End VF.
Module VFZ. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_vec_finalizeZ. End VFZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import RA.ReallocAddr AA.AAAddr AD.ADAddr VP.VPAddr VF.VFAddr.

Module FSAddr.
  Definition fs_entry : Z := 0x8f45c.
  Definition fs_ret : Z := 0x9037c.
  Definition fs_jalr : Z := 0x8f890.
  Definition memset_pc : Z := 0x5cce8.
  Definition memset_ret : Z := 0x5cda8.
  Definition FR : Z := 208.
End FSAddr.
Import FSAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47. Definition two40 := RA.two40.
Definition B32 := Lib_vec_reserve.B32. Definition B_EW := Lib_vec_reserve.B_EW.
Definition c4 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S25S12Vo;A1Z4Vv;A3").
Definition c1 (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S25S12Vo;A1Z1Vv;A3").

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
S23S17dS12Ve;A1Vk;A3").

Definition piece (lo hi : Z) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1aS55S12Vlo;A1S12Vhi;A1Vcells;S19A5").
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1aS18PaA1S12S194S199A1A1S12Z0A1Vcells;S19A5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S1aS78S199A1S4fS12Z0A1S3S14A1S19A5").
Definition P_alloc : sobj := ltac2:(tb__ "0|1|
S5bZ0M0Z8S0S14S3bG0S5dA2S3S14A1A3A3").
Definition P_hdr : sobj := ltac2:(tb__ "0|1|
S5bZ8M0Z20S0S14S3bG0S47A2S0S14S3bZ10S12Z0A1A2S0S14S3bZ18S16fA2S3S14A1A3A3A3A3").
Definition BIG : Z := 288230376151711743.
Definition P_caps : sobj := ltac2:(tb__ "0|4|
S5bZ20M0Z60S0S14S3bG0S12Sc8A1M1A2S0S14S3bZ28G1A2S0S14S3bZ30G1A2S0S14S3bZ38S12S192Z2M2Z14A2A1A2S0S14S3bZ40S12S192G2Z18A2A1M3A2S0S14S3bZ48G3A2S0S14S3bZ50G3A2S0S14S3bZ58G1A2S3S14A1A3A3A3A3A3A3A3A3A3").
Definition P_st (err : sv) : sobj := ltac2:(tb__ "0|1|
S5bZ60M0Z78S0S14SadG0Verr;A2S0S14S3bZ68S171A2S0S14S82Z70S12Z1A1A2S3S14A1A3A3A3A3").
Definition V (o : Z) (d c k : sv) (e : Z) : sobj := ltac2:(tb__ "0|0|
S5bVo;S191Vo;Z20A2S0S14S3bVo;Vd;A2S0S14S3bS191Vo;Z8A2Vc;A2S0S14S3bS191Vo;Z10A2Vk;A2S0S14S3bS191Vo;Z18A2S12Ve;A1A2S3S14A1A3A3A3A3A3").
Definition P_cur (cn hp : sv) : sobj := ltac2:(tb__ "0|1|
S5bZ1e0M0Z1f0S0S14S3bG0Vcn;A2S0S14S82Z1e8Vhp;A2S3S14A1A3A3A3").
Definition P_ff : sobj := ltac2:(tb__ "0|1|
S5bZ370Z3a8S0S14S82Z375S12Z0A1M0A2S0S14SadZ388G0A2S3S14A1A3A3A3").
Definition Vd (o e : Z) : sobj := ltac2:(tb__ "0|1|
S5bVo;S191Vo;Z20A2S0S14S3bVo;S12Z0A1M0A2S0S14S3bS191Vo;Z8A2G0A2S0S14S3bS191Vo;Z10A2G0A2S0S14S3bS191Vo;Z18A2S12Ve;A1A2S3S14A1A3A3A3A3A3").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S1aS5dS12Z0M0A1M1S12Z30A1S0S14S3bG0S12S1b1A1A2S0S14S3bZ8S12S1b2A1A2S0S14S3bZ10G1A2S0S14S3bZ18S12S1b3A1A2S0S14S3bZ20G1A2S0S14S3bZ28S176A2S3S14A1A3A3A3A3A3A3S19A5").
Definition O_ar (hd : sv) : sobj := ltac2:(tb__ "0|0|
S1aS47S12Z0A1S12Z40A1S1b8Vhd;A1S19A5").
Definition O_dat (d : sv) (e : Z) (k : sv) : sobj := ltac2:(tb__ "0|0|
S1aVd;S12Z0A1S4dVe;Vk;A2S3S14A1S19A5").

Record vdesc := VD { vd_off : Z; vd_el : Z; vd_d : sv; vd_c : sv; vd_k : sv; vd_dv : positive }.
Definition vMI : ltac2:(tb__ "0|0|
S3c") := ltac2:(tb__ "0|0|
S59Z1f0ZcS14eSb3S14fP71A6"). Definition vFV : ltac2:(tb__ "0|0|
S3c") := ltac2:(tb__ "0|0|
S59Z210Z4S146Sb1S147P74A6"). Definition vMM : ltac2:(tb__ "0|0|
S3c") := ltac2:(tb__ "0|0|
S59Z230Z4S150S87S151P77A6").
Definition vSG : ltac2:(tb__ "0|0|
S3c") := ltac2:(tb__ "0|0|
S59Z250Z4S166S77S167P7aA6"). Definition vLI : ltac2:(tb__ "0|0|
S3c") := ltac2:(tb__ "0|0|
S59Z270ZcS14cS68S14dP7dA6"). Definition vLC : ltac2:(tb__ "0|0|
S3c") := ltac2:(tb__ "0|0|
S59Z290Z4S14aS61S14bP80A6").
Definition vPI : ltac2:(tb__ "0|0|
S3c") := ltac2:(tb__ "0|0|
S59Z2b0ZcS163S5aS164P83A6"). Definition vSH : ltac2:(tb__ "0|0|
S3c") := ltac2:(tb__ "0|0|
S59Z1c0Z80S45S3eS3fP6eA6").
Definition fins : list vdesc := ltac2:(tb__ "0|0|
S0S3cS172S0S3cS170S0S3cS173S0S3cS175S0S3cS92S0S3cS91S0S3cS93S3S3cA1A3A3A3A3A3A3A3").
Definition Vof (v : vdesc) (c : sv) : sobj := ltac2:(tb__ "0|0|
Sa7Sc6Vv;A1S65Vv;A1Vc;S6cVv;A1S66Vv;A1A5").
Definition Dof (v : vdesc) : sobj := ltac2:(tb__ "0|0|
Sa2S65Vv;A1S66Vv;A1S6cVv;A1A3").
Definition Xof (v : vdesc) : sv * sv := ltac2:(tb__ "0|0|
S1S11S11S65Vv;A1S4dS66Vv;A1S6cVv;A1A2A4").
Definition vec_facts (v : vdesc) : list sprop := ltac2:(tb__ "0|3|
S65Vv;A1S11S6fVv;A1S11S6cVv;A1S11S66Vv;A1S2cS0S13S1cS177Vv;A1Z4A2S0S13S15R4S18P1eA1M0A2S0S13S15S16S179R4S4dR1R2A2M1A3G0A2S0S13S15R4S12S8dA1A2S0S13S15R3R2A2S0S13S15R2S12S97A1M2A2S0S13S15G1G2A2S3S13A1A3A3A3A3A3A3A3Te;Tk;Tc;Td;").

Definition builder (err : sv) (shd shc shk : sv) (cn hp : sv) (cs : list sv) : list sobj := ltac2:(tb__ "0|3|
S5S17S0S17SfaS0S17SfeS0S17SfbS0S17S101Verr;A1S0S17Sa7Z1c0Vshd;Vshc;Vshk;Z80M0A5S0S17SfcVcn;Vhp;A2S3S17A1M1A3A3A3A3A3A3S5S17S18cS4S3cS11A2M2S17G2S125S9S3cS11R1A3ScS3cS11R1A3A2Lvc;S19eS3cS11S50Vcs;A4A4S0S17SfdS0S17S80Z488Z38A2S0S17S80Z4a8Z30A2S0S17S80Z4c8G0A2G1A3A3A3A3A3A3").
Definition cs0 : list sv := map vd_c fins.
Definition dats0 : list sobj := ltac2:(tb__ "0|0|
S5S17S18cS3cS17S7fS50A4S0S17S7fS7cA1S3S17A1A3A3").
Definition canon (fcells : list cell) (err : sv) (shd shc shk : sv) (cn hp : sv) (cs : list sv) (hd : sv) (dats : list sobj) : list sobj := ltac2:(tb__ "0|1|
S5S17S0S17Sf4Vfcells;A1S0S17Sa1S3S17A1M0A3A3S5S17S135Verr;Vshd;Vshc;Vshk;Vcn;Vhp;Vcs;A7S5S17S0S17Sf5S0S17Sf6Vhd;A1G0A3A3S5S17Vdats;S1a5A3A3A3A3").
Definition X_fs0 : list (sv * sv) := ltac2:(tb__ "0|2|
S5S4S11S11A2M0S0G0S1S11S11S55S12Z518A1A4S0G0S1S11S11S5dS12Z30A1A4S0G0S1S11S11S47S12Z40A1A4S3G0A1M1A3A3A3S5G0S18cS3cG0S60S50A4S0G0S60S7cA1G1A3A3A3").

Definition fs_facts : list sprop := ltac2:(tb__ "0|8|
S5S13S0S13S1cPaM0Z4M1A2S0S13S15S18G0A1M2S12S8dA1M3A2S0S13S15S18P1eA1M4S16S179S78S199A1M5S4fA3A2S0S13S15G4S78S191S199Z10d0A2A1A2S0S13S15G4G5A2S0S13S15G4G2A2S0S13S1dS17bS12N10d0A1S4fA3S0S13S1dS17bS4fS12S194S192Z2Z26A2A1A1A3S0S13S1cPcG1A2S0S13S15S12S1afA1M6S55A2S0S13S15S16S179S55S12Z518A1A3G4A2S0S13S15S55G3A2S0S13S1cP64Z3A2S0S13S15G6S5dA2S0S13S15S16S179S5dS12Z30A1A3G4A2S0S13S15S5dG3A2S0S13S1cP65G1A2S0S13S15S12Z1000A1S47A2S0S13S15S16S179S47S12Z40A1A3G4A2S0S13S15S47G3A2S0S13S15S42G4A2S0S13S15S4bS12Z1A1A2S0S13S15S4eG3A2S0S13S15S12Z7fff7f800000A1M7G4A2S0S13S15G4S12Z7fffff800000A1A2S0S13S15G7G2A2S3S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S5S13S19fS13S18cS3cS7S13A1Sc7S50A4A2Sc7S7cA1A3A3").

Definition Pre_fs_S : sstate := ltac2:(tb__ "0|0|
S21S19bS1abS1a8S1fSeS11A1S83S3S14A1S49S45S3eS3fS4eS4bS48S42S4cAaS84S58SbA9").
Definition Pre_fs : axst := mkA Pre_fs_S X_fs0.

Definition FUEL_fs : nat := 2000%nat.
Definition calls_fs : list Z := ltac2:(tb__ "0|0|
S0S2cS1b9S0S2cS1b4S0S2cS1c5S0S2cS19cS0S2cS1b0S0S2cS19aS3S2cA1A3A3A3A3A3A3").
Definition leafF_at (cuts : list Z) (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S18dS2eVk;S1a2S67Vcuts;VS;Vpc;A4S71A4").
Definition show_run (cuts : list Z) (S : axst) : ltac2:(tb__ "0|0|
S7S4S2cS1b5A2A1") := ltac2:(tb__ "0|2|
SaS7S30A1M0A1S7S4S2cS1b5A2M1A1Lx;S31S1a3S67Vcuts;VS;S6A5G0S18cS30G1S1a7R1A4Lls;S3G1A1Xax2").

Definition hx (r : nat) : sv := SVar (Pos.of_nat (200 + r)).
Definition pG : sv := SVar 240.
Definition HNEXT : positive := 280%positive.
Definition g8 (g : sv) : sv := SAlu ALU_SLL g (SLit 3).
Definition FEb (g : sv) : list sprop := ltac2:(tb__ "0|1|
S0S13S20S85Vg;A1M0S55A2S0S13S15Vg;S12S193S192Z2Z3dA2Z1A2A1A2S0S13S15G0S55A2S0S13S15S55G0A2S3S13A1A3A3A3A3").
Definition shOf (g : sv) (k : Z) : sv := ltac2:(tb__ "0|0|
S16S179Vg;S12S191S1a4Vk;A2A1A3").
Definition bofs (k : Z) : sv := ltac2:(tb__ "0|0|
S16S179S55S12Vk;A1A3").
Definition F_cells : list cell := ltac2:(tb__ "0|0|
S0S14S3bN8S18PbA1A2S0S14S3bN10S18P1cA1A2S0S14S3bN18S18P1dA1A2S0S14S3bN20S18P26A1A2S0S14S3bN28S18P27A1A2S0S14S3bN30S18P28A1A2S0S14S3bN38S18P29A1A2S0S14S3bN40S18P2aA1A2S0S14S3bN48S18P2bA1A2S0S14S3bN50S18P2cA1A2S0S14S3bN58S18P2dA1A2S0S14S3bN60S18P2eA1A2S0S14S3bN68S18P2fA1A2S3S14A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition fs_regs (g : sv) (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|1|
S1a9S18cS2S11S149S18bU0U20A2A4S5S4S2S11A2M0S0G0S1S2S11U2S78S199A1A4S0G0S1S2S11U3S18P17A1A4S0G0S1S2S11U4S18P18A1A4S0G0S1S2S11U8S43Z1e8A1A4S0G0S1S2S11U9S55A4S0G0S1S2S11U12S43Z490A1A4S0G0S1S2S11U15S44Vg;Z92A2A4S0G0S1S2S11U1aS44Vg;Z3dA2A4S0G0S1S2S11U1bS12S1a4A1A4S3G0A1A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition CS (pc : Z) (g : sv) (regs : list (nat * sv)) (fcells : list cell) (err shd shc shk cn hp : sv) (cs : list sv) (hd : sv)
              (dats : list sobj) (facts : list sprop) (nx : positive) : sstate := ltac2:(tb__ "0|0|
S21Vpc;S145Vg;Vregs;A2S1a8S1fSeS11A1S83Vfcells;Verr;Vshd;Vshc;Vshk;Vcn;Vhp;Vcs;Vhd;Vdats;AaS5S13Vfacts;S0S13S15Vhd;S18P1eA1A2S5S13Se7Vg;A1S84A3A3A3Vnx;SbA9").

Definition C_E_S : sstate := ltac2:(tb__ "0|1|
S53Z8f5b8S41S0S4S2S11A2M0S1S2S11U1S18PbA1A4S3G0A1A3S6dS49S45S3eS3fS4eS4bS48S42S4cS3S13A1S52Af").
Definition C_E : axst := mkA C_E_S X_fs0.

Definition eC (v : vdesc) (c : sv) : sv := ltac2:(tb__ "0|0|
S23S17dS12S66Vv;A1A1Vc;A3").

Definition vd_mesh (v : vdesc) : bool := vd_off v <? 624.
Definition AMin1 (c : sv) : batom := AMin c 1 0 1.
Definition CHf (v : vdesc) (c : sv) : list bitem := ltac2:(tb__ "0|9|
SdS7S185A1L_;Sc5Vv;A1S0S185S188Z1M0Z0M1S0S4S2cS186A2M2S1S2cS186Z2S187S13eVv;Vc;A2A1M3A4M4S0G2S1S2cS186Z60M5S96Vc;A1A4S3G2A1M6A3A3G1A4S0S185S188G1G0S0G2S1S2cS186Z4G3A4S0G2S1S2cS186Z40S187Vc;A1M7A4G6A3A3G1A4S3S185A1A3M8A3S0S185S188G0G1S0G2G4S0G2S1S2cS186G5G7A4G6A3A3G1A4G8A3Xdx2").
Definition CHname : list bitem := ltac2:(tb__ "0|2|
S0S185S189Z1M0Z0M1Z62A3S0S185S189G1G0Z44A3S3S185A1A3A3").
Definition PHIe (e : Z) (w k : sv) : bitem := ltac2:(tb__ "0|2|
S188Z1Z0M0S0S4S2cS186A2M1S1S2cS186Z6S187S4dVe;Vw;A2A1A4S0G1S1S2cS186N4S187S4dVe;Vk;A2A1A4S0G1S1S2cS186Z20S187S12Ve;A1A1A4S3G1A1A3A3A3G0A4").
Definition KLG := Lib_vec_reserve.KLG.
Definition bd_push (c k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S185Sf9Z80S16S179Vc;S12Z1A1A3Vk;A3S0S185Sf3Vk;A1S3S185A1A3A3").

Definition finV (i : nat) : bitem := ltac2:(tb__ "0|7|
S188Z1Z0M0S1a0S3cS4S2cS186A2M1S3cSdS7G1A1L_;Sc5R1A1S0G1S1S2cS186S195Z2S66R1A1A2M2S187S6fR1A1M3A1M4A4S0G1S1S2cS186Z60M5S96G3A1A4S3G1A1M6A3A3S0G1S1S2cS186S191G2G5A2G4A4G6A3Xdx2Lv;S18fS3cVi;S50A3A4G0A4").
Definition finK (i : nat) : bitem := ltac2:(tb__ "0|1|
S188Z0M0Z1S18cS3cS4S2cS186A2S3cS1S2cS186S191S195Z4S66R1A1A2Z40A2S187S6fR1A1A1A4Lv;S18fS3cVi;S50A3A4G0A4").
Definition CHfrom (i : nat) (cs : list sv) : list bitem := ltac2:(tb__ "0|0|
S0S185S143Vi;A1S0S185S142Vi;A1S3S185A1A3A3").
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S5S4S11S11A2M0S18cS3cG0S60S50A4S0G0S60S7cA1S0G0S1S11S11S47S12Z40A1A4S3G0A1A3A3A3").
Definition bd0 : list bitem := ltac2:(tb__ "0|0|
S5S185S51U0S48A2S5S185ScaS4aS3eS3fA2A3A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1SaaS36S42S6A2A4").
Definition ndE : ndesc := nd0.

Definition main_facts : list sprop := ltac2:(tb__ "0|0|
S0S13S24S1dS17cS3eS12S192Z2Z18A2A1A3A1S3S13A1A3").

Definition vNM : sv := SVar 241. Definition vHq : sv := SVar 242.
Definition C_1_S : sstate := ltac2:(tb__ "0|1|
S53Z8f620S41S0S4S2S11A2M0S1S2S11U13S43Z8A1A4S0G0S1S2S11U16S43Z1f8A1A4S0G0S1S2S11U17S44S41Z3fA2A4S0G0S1S2S11U19S7bA4S3G0A1A3A3A3A3S6dS49S45S3eS3fS4eS4bS48S40S4cS54S52Af").
Definition C_1 : axst := mkA C_1_S X_fs0.
Definition nd1 : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S5S185S51U0S48A2S4aS3eS3fA2A3S36S40S6A2A4").

Definition cs2 : list sv := ltac2:(tb__ "0|0|
S0S11S12Z0A1S0S11Sb1S0S11S87S0S11S77S0S11S68S0S11S61S0S11S5aS3S11A1A3A3A3A3A3A3A3").
Definition F2_cells : list cell := ltac2:(tb__ "0|0|
S0S14S3bN70Sb3A2S6dA3").
Definition C_2_S : sstate := ltac2:(tb__ "0|1|
S53Z8f6dcS41S0S4S2S11A2M0S1S2S11U13S43Z8A1A4S0G0S1S2S11U14S44S41Z1A2A4S0G0S1S2S11U16S43Z1f8A1A4S0G0S1S2S11U17S44S41Z3fA2A4S0G0S1S2S11U19S7bA4S3G0A1A3A3A3A3A3S9aS49S45S3eS3fS4eS4bS137S40S4cS54S52Af").
Definition C_2 : axst := mkA C_2_S X_fs0.
Definition nd2 : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S5S185S51U1S48A2S4aS3eS3fA2A3S36S40S6A2A4").

Definition cutsC : list Z := ltac2:(tb__ "0|0|
S5S2cS0S2cZ8f5b8S0S2cZ8f620S0S2cZ8f784S0S2cZ8f6dcS0S2cZ8f978S0S2cZ8fabcS0S2cZ8fbdcS0S2cZ8fc70S0S2cZ8fcfcS0S2cZ8fd88S3S2cA1A3A3A3A3A3A3A3A3A3A3S136A3").
Definition optA (x : option axst) : axst := match x with Some s => s | None => Pre_fs end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leafC_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S18dS2eVk;S1a2S67Sb0VS;Vpc;A4S71A4").
Definition xf_call (F : Z) : list axform := ltac2:(tb__ "0|2|
S0S17eS181U1M0S12S194VF;A1M1A1A2S0S17eS17fG0G1A2S3S17eA1A3A3").
Definition nobj (A : axst) : nat := length (ss_objs (ax_S A)).

Definition Pre_ad : axst := AD.Pre_ad.

Definition go_facts (v : vdesc) : list sprop := ltac2:(tb__ "0|0|
S0S13S15S12Z1000A1S65Vv;A1A2S0S13S15S12Z1A1S6fVv;A1A2S3S13A1A3A3").
Definition E_ad1_0 : axst := Eval vm_compute in leafC_at C_1 ad_entry 0.
Definition E_ad1 : axst := Eval vm_compute in optA (apply_axforms (ax_add_facts (go_facts vMI) E_ad1_0) (xf_call 64)).
Definition s_ad1 : wsub := ltac2:(tb__ "0|0|
S0S4S2dS11A2S1S2dS11P13S16S179S4fS12Z40A1A3A4S190PaS2fSd4A1S2fS70A1A3A3").
Definition R_ad1 : list sobj := Eval vm_compute in optR (entails_frA E_ad1 Pre_ad s_ad1).

Definition Xk_fin (v : vdesc) : list (sv * sv) := ltac2:(tb__ "0|2|
S19dS4S11S11A2M0G0SfS8S1bS9S11S11R1A3M1S47A2A1S8S1bG1S65Vv;A1A2A1A2Lr;S5fA3").

Definition perm_fin (j : nat) : list nat := ltac2:(tb__ "0|4|
S5S2S0S2U6S0S2U1M0S0S2U0S3S2A1M1A3A3A3S5S2S18bU7U11A2S5S2S0S2U18S0S2U2G1A3A3S5S2S18bU19M2S196Vj;G0A2M3A2S5S2S0S2U3G1A3S5S2S18bS197G2G3A2S196U8Vj;A2A2S0S2U4S0S2U5G1A3A3A3A3A3A3A3A3").
Definition xf_back_fin (j : nat) : list axform := ltac2:(tb__ "0|1|
S0S17eS17fU1M0Z40A2S0S17eS180S15eVj;A1A1S0S17eS182G0A1S3S17eA1A3A3A3").
Definition T1_ok0 : axst := Eval vm_compute in T_afterA3 Pre_ad E_ad1 s_ad1 R_ad1 AD.P_ok (Xk_fin vMI).
Definition T1_fail0 : axst := Eval vm_compute in T_afterA3 Pre_ad E_ad1 s_ad1 R_ad1 AD.P_fail (Xk_fin vMI).
Definition T1_ok : axst := Eval vm_compute in optA (apply_axforms T1_ok0 (xf_back_fin 1)).
Definition T1_fail : axst := Eval vm_compute in optA (apply_axforms T1_fail0 (xf_back_fin 1)).

Definition cs3 : list sv := ltac2:(tb__ "0|1|
S0S11S12Z0A1M0S0S11G0S0S11S87S0S11S77S0S11S68S0S11S61S0S11S5aS3S11A1A3A3A3A3A3A3A3").
Definition F3_cells : list cell := ltac2:(tb__ "0|0|
S0S14S3bN78S7bA2S9aA3").
Definition C_3_S : sstate := ltac2:(tb__ "0|1|
S53Z8f978S41S0S4S2S11A2M0S1S2S11U13S43Z8A1A4S0G0S1S2S11U14S44S41Z1A2A4S0G0S1S2S11U17S43Z218A1A4S0G0S1S2S11U18S44S41Z43A2A4S0G0S1S2S11U19S7bA4S3G0A1A3A3A3A3A3S9bS49S45S3eS3fS4eS4bS138S40S4cS54S52Af").
Definition C_3 : axst := mkA C_3_S X_fs0.
Definition nd3 : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S5S185S51U2S48A2S4aS3eS3fA2A3S36S40S6A2A4").

Definition E_ad2_0 : axst := Eval vm_compute in leafC_at C_2 ad_entry 0.
Definition E_ad2 : axst := Eval vm_compute in optA (apply_axforms (ax_add_facts (go_facts vFV) E_ad2_0) (xf_call 64)).
Definition s_ad2 : wsub := ltac2:(tb__ "0|0|
S0S4S2dS11A2S1S2dS11P13S16S179S4fS12Z40A1A3A4S190PaS2fSd6A1S2fS70A1A3A3").
Definition R_ad2 : list sobj := Eval vm_compute in optR (entails_frA E_ad2 Pre_ad s_ad2).
Definition T2_ok0 : axst := Eval vm_compute in T_afterA3 Pre_ad E_ad2 s_ad2 R_ad2 AD.P_ok (Xk_fin vFV).
Definition T2_fail0 : axst := Eval vm_compute in T_afterA3 Pre_ad E_ad2 s_ad2 R_ad2 AD.P_fail (Xk_fin vFV).
Definition T2_ok : axst := Eval vm_compute in optA (apply_axforms T2_ok0 (xf_back_fin 2)).
Definition T2_fail : axst := Eval vm_compute in optA (apply_axforms T2_fail0 (xf_back_fin 2)).

Definition p2 : sv := SVar 250. Definition p3 : sv := SVar 251. Definition p4 : sv := SVar 252.
Definition cs4 : list sv := ltac2:(tb__ "0|1|
S0S11S12Z0A1M0S0S11G0S0S11G0S0S11S77S0S11S68S0S11S61S0S11S5aS3S11A1A3A3A3A3A3A3A3").
Definition F4_cells : list cell := ltac2:(tb__ "0|0|
S0S14S3bN80S15aA2S9bA3").
Definition C_4_S : sstate := ltac2:(tb__ "0|1|
S53Z8fabcS41S0S4S2S11A2M0S1S2S11U13S43Z8A1A4S0G0S1S2S11U14S44S41Z1A2A4S0G0S1S2S11U18S43Z238A1A4S0G0S1S2S11U19S44S41Z47A2A4S3G0A1A3A3A3A3S9cS49S45S3eS3fS4eS4bS139S40S4cS54S52Af").
Definition C_4 : axst := mkA C_4_S X_fs0.
Definition nd4 : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S5S185S51U3S48A2S4aS3eS3fA2A3S36S40S6A2A4").

Definition E_ad3_0 : axst := Eval vm_compute in leafC_at C_3 ad_entry 0.
Definition E_ad3 : axst := Eval vm_compute in optA (apply_axforms (ax_add_facts (go_facts vMM) E_ad3_0) (xf_call 64)).
Definition s_ad3 : wsub := ltac2:(tb__ "0|0|
S0S4S2dS11A2S1S2dS11P13S16S179S4fS12Z40A1A3A4S190PaS2fSd8A1S2fS70A1A3A3").
Definition R_ad3 : list sobj := Eval vm_compute in optR (entails_frA E_ad3 Pre_ad s_ad3).
Definition T3_ok0 : axst := Eval vm_compute in T_afterA3 Pre_ad E_ad3 s_ad3 R_ad3 AD.P_ok (Xk_fin vMM).
Definition T3_fail0 : axst := Eval vm_compute in T_afterA3 Pre_ad E_ad3 s_ad3 R_ad3 AD.P_fail (Xk_fin vMM).
Definition T3_ok : axst := Eval vm_compute in optA (apply_axforms T3_ok0 (xf_back_fin 3)).
Definition T3_fail : axst := Eval vm_compute in optA (apply_axforms T3_fail0 (xf_back_fin 3)).

Definition cs5 : list sv := ltac2:(tb__ "0|1|
S0S11S12Z0A1M0S0S11G0S0S11G0S0S11G0S0S11S68S0S11S61S0S11S5aS3S11A1A3A3A3A3A3A3A3").
Definition F5_cells : list cell := ltac2:(tb__ "0|0|
S0S14S3bN88S15bA2S9cA3").
Definition C_5_S : sstate := ltac2:(tb__ "0|1|
S53Z8fbdcS41S0S4S2S11A2M0S1S2S11U13S43Z8A1A4S0G0S1S2S11U14S44S41Z1A2A4S0G0S1S2S11U18S44S41Z4bA2A4S0G0S1S2S11U19S43Z258A1A4S3G0A1A3A3A3A3S9dS49S45S3eS3fS4eS4bS13aS40S4cS54S52Af").
Definition C_5 : axst := mkA C_5_S X_fs0.
Definition nd5 : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S5S185S51U4S48A2S4aS3eS3fA2A3S36S40S6A2A4").

Definition E_ad4_0 : axst := Eval vm_compute in leafC_at C_4 ad_entry 0.
Definition E_ad4 : axst := Eval vm_compute in optA (apply_axforms (ax_add_facts (go_facts vSG) E_ad4_0) (xf_call 64)).
Definition s_ad4 : wsub := ltac2:(tb__ "0|0|
S0S4S2dS11A2S1S2dS11P13S16S179S4fS12Z40A1A3A4S190PaS2fSdaA1S2fS70A1A3A3").
Definition R_ad4 : list sobj := Eval vm_compute in optR (entails_frA E_ad4 Pre_ad s_ad4).
Definition T4_ok0 : axst := Eval vm_compute in T_afterA3 Pre_ad E_ad4 s_ad4 R_ad4 AD.P_ok (Xk_fin vSG).
Definition T4_fail0 : axst := Eval vm_compute in T_afterA3 Pre_ad E_ad4 s_ad4 R_ad4 AD.P_fail (Xk_fin vSG).
Definition T4_ok : axst := Eval vm_compute in optA (apply_axforms T4_ok0 (xf_back_fin 4)).
Definition T4_fail : axst := Eval vm_compute in optA (apply_axforms T4_fail0 (xf_back_fin 4)).

Definition Pre_vf : axst := VF.Pre_vf.
Definition xf_vfcall (vidx : nat) (off : Z) : list axform := ltac2:(tb__ "0|2|
S0S17eS17fVvidx;Voff;A2S0S17eS181U1M0S12N40M1A1A2S0S17eS17fG0G1A2S3S17eA1A3A3A3").

Definition perm_vf (pidx : nat) (j : nat) : list nat := ltac2:(tb__ "0|7|
S5S2S0S2U7S0S2U1M0S0S2U0S3S2A1M1A3A3A3S5S2S18bU8M2S196Vpidx;U2M3A2M4A2S5S2S0S2G3G1A3S5S2S18bS197G2G4A2S196U11G4A2A2S5S2S0S2U3G1A3S5S2S18bU19M5S196Vj;G0A2M6A2S5S2S0S2U4G1A3S5S2S18bS197G5G6A2S196G2Vj;A2A2S0S2U5S0S2U6G1A3A3A3A3A3A3A3A3A3A3").
Definition xf_back_vf (pidx : nat) (j : nat) : list axform := ltac2:(tb__ "0|1|
S0S17eS17fU1M0Z40A2S0S17eS180S160Vpidx;Vj;A2A1S0S17eS182G0A1S0S17eS183Vpidx;A1S3S17eA1A3A3A3A3").

Definition perm_vfk (pidx : nat) (j : nat) : list nat := ltac2:(tb__ "0|7|
S5S2S0S2U7S0S2U1M0S0S2U0S3S2A1M1A3A3A3S5S2S18bU8M2S196Vpidx;U2M3A2M4A2S5S2S0S2U6G1A3S5S2S18bS197G2G4A2S196U11G4A2A2S5S2S0S2G3G1A3S5S2S18bU19M5S196Vj;G0A2M6A2S5S2S0S2U3G1A3S5S2S18bS197G5G6A2S196G2Vj;A2A2S0S2U4S0S2U5G1A3A3A3A3A3A3A3A3A3A3").
Definition xf_back_vfk (pidx : nat) (j : nat) : list axform := ltac2:(tb__ "0|1|
S0S17eS17fU1M0Z40A2S0S17eS180S161Vpidx;Vj;A2A1S0S17eS182G0A1S0S17eS183Vpidx;A1S3S17eA1A3A3A3A3").
Definition PD_vf : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S4S2eS34A2M0S1S2eS34S1bcS1bfA4S0G0S1S2eS34S1baS1bdA4S0G0S1S2eS34S1bbS1beA4S3G0A1A3A3A3").
Definition Xk_vf (v : vdesc) : list (sv * sv) := ltac2:(tb__ "0|2|
S19dS4S11S11A2M0G0SfS8S1bS9S11S11R1A3M1S47A2A1S8S1bG1S65Vv;A1A2A1A2Lr;S5fA3").

Definition E_vf5_0 : axst := Eval vm_compute in leafC_at C_5 vf_entry 0.
Definition E_vf5 : axst := Eval vm_compute in optA (apply_axforms E_vf5_0 (xf_vfcall 12 624)).
Definition s_vf5 : wsub := ltac2:(tb__ "0|0|
S0S4S2dS11A2S1S2dS11P13S16S179S4fS12Z40A1A3A4S190PaS2fSdeA1S2fS6eA1A3A3").
Definition R_vf5 : list sobj := Eval vm_compute in optR (entails_frA E_vf5 Pre_vf s_vf5).
Definition T5_z0 : axst := Eval vm_compute in T_afterA3 Pre_vf E_vf5 s_vf5 R_vf5 VF.P_zero (Xk_vf vLI).
Definition T5_f0 : axst := Eval vm_compute in T_afterA3 Pre_vf E_vf5 s_vf5 R_vf5 VF.P_fail (Xk_vf vLI).
Definition T5_ok0 : axst := Eval vm_compute in T_afterA3 Pre_vf E_vf5 s_vf5 R_vf5 VF.P_ok (Xk_vf vLI).
Definition T5_z : axst := Eval vm_compute in optA (apply_axforms T5_z0 (xf_back_vf 12 5)).
Definition T5_f : axst := Eval vm_compute in optA (apply_axforms T5_f0 (xf_back_vfk 12 5)).
Definition T5_ok : axst := Eval vm_compute in optA (apply_axforms T5_ok0 (xf_back_vfk 12 5)).

Definition p1 : sv := SVar 253.
Definition cs6 : list sv := ltac2:(tb__ "0|1|
S0S11S12Z0A1M0S0S11G0S0S11G0S0S11G0S0S11G0S0S11S61S0S11S5aS3S11A1A3A3A3A3A3A3A3").
Definition F6_cells : list cell := ltac2:(tb__ "0|0|
S0S14S3bN98S68A2S0S14S3bN90S159A2S9dA3A3").
Definition C_6_S : sstate := ltac2:(tb__ "0|1|
S53Z8fc70S41S0S4S2S11A2M0S1S2S11U13S43Z8A1A4S0G0S1S2S11U14S44S41Z1A2A4S0G0S1S2S11U18S44S41Z4fA2A4S0G0S1S2S11U19S43Z278A1A4S3G0A1A3A3A3A3S9eS49S45S3eS3fS4eS4bS13bS40S4cS54S52Af").
Definition C_6 : axst := mkA C_6_S X_fs0.
Definition nd6 : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S5S185S51U5S48A2S4aS3eS3fA2A3S36S40S6A2A4").

Definition vf_site (C : axst) (pidx : nat) (v : vdesc) (j : nat) : axst * wsub * list sobj := ltac2:(tb__ "0|2|
Sb2VC;S1b4U0A3S2eSc0S184R1S178Vpidx;Sc6Vv;A1A2A2A1S2eS0S4S2dS11A2M0S1S2dS11P13S16S179S4fS12Z40A1A3A4S190PaS2fR1A1S2fS6eA1A3A3S7G0A1M1S1S4S2eG1A2S7S17A1S1S2eG1R2R1A4S158S1c9R2S6eR1A3A1A4Ts;TE;TE0;").

Definition E_vf6_0 : axst := Eval vm_compute in leafC_at C_6 vf_entry 0.
Definition E_vf6 : axst := Eval vm_compute in optA (apply_axforms E_vf6_0 (xf_vfcall 13 656)).
Definition s_vf6 : wsub := ltac2:(tb__ "0|0|
S0S4S2dS11A2S1S2dS11P13S16S179S4fS12Z40A1A3A4S190PaS2fSe0A1S2fS6eA1A3A3").
Definition R_vf6 : list sobj := Eval vm_compute in optR (entails_frA E_vf6 Pre_vf s_vf6).
Definition T6_z : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf6 s_vf6 R_vf6 VF.P_zero (Xk_vf vLC)) (xf_back_vf 13 6)).
Definition T6_f : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf6 s_vf6 R_vf6 VF.P_fail (Xk_vf vLC)) (xf_back_vfk 13 6)).
Definition T6_ok : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf6 s_vf6 R_vf6 VF.P_ok (Xk_vf vLC)) (xf_back_vfk 13 6)).

Definition p5 : sv := SVar 254.
Definition cs7 : list sv := ltac2:(tb__ "0|1|
S0S11S12Z0A1M0S0S11G0S0S11G0S0S11G0S0S11G0S0S11G0S0S11S5aS3S11A1A3A3A3A3A3A3A3").
Definition F7_cells : list cell := ltac2:(tb__ "0|0|
S0S14S3bNa8S61A2S0S14S3bNa0S15cA2S9eA3A3").
Definition C_7_S : sstate := ltac2:(tb__ "0|1|
S53Z8fcfcS41S0S4S2S11A2M0S1S2S11U13S43Z8A1A4S0G0S1S2S11U14S44S41Z1A2A4S0G0S1S2S11U18S44S41Z53A2A4S0G0S1S2S11U19S43Z298A1A4S3G0A1A3A3A3A3S9fS49S45S3eS3fS4eS4bS13cS40S4cS54S52Af").
Definition C_7 : axst := mkA C_7_S X_fs0.
Definition nd7 : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S5S185S51U6S48A2S4aS3eS3fA2A3S36S40S6A2A4").

Definition E_vf7_0 : axst := Eval vm_compute in leafC_at C_7 vf_entry 0.
Definition E_vf7 : axst := Eval vm_compute in optA (apply_axforms E_vf7_0 (xf_vfcall 14 688)).
Definition s_vf7 : wsub := ltac2:(tb__ "0|0|
S0S4S2dS11A2S1S2dS11P13S16S179S4fS12Z40A1A3A4S190PaS2fSe2A1S2fS6eA1A3A3").
Definition R_vf7 : list sobj := Eval vm_compute in optR (entails_frA E_vf7 Pre_vf s_vf7).
Definition T7_z : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf7 s_vf7 R_vf7 VF.P_zero (Xk_vf vPI)) (xf_back_vf 14 7)).
Definition T7_f : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf7 s_vf7 R_vf7 VF.P_fail (Xk_vf vPI)) (xf_back_vfk 14 7)).
Definition T7_ok : axst := Eval vm_compute in optA (apply_axforms (T_afterA3 Pre_vf E_vf7 s_vf7 R_vf7 VF.P_ok (Xk_vf vPI)) (xf_back_vfk 14 7)).

Definition p6 : sv := SVar 255.
Definition cs8 : list sv := ltac2:(tb__ "0|1|
S0S11S12Z0A1M0S0S11G0S0S11G0S0S11G0S0S11G0S0S11G0S0S11G0S3S11A1A3A3A3A3A3A3A3").
Definition F8_cells : list cell := ltac2:(tb__ "0|0|
S0S14S3bNb8S5aA2S0S14S3bNb0S15dA2S9fA3A3").
Definition C_8_S : sstate := ltac2:(tb__ "0|1|
S53Z8fd88S41S0S4S2S11A2M0S1S2S11U13S43Z8A1A4S0G0S1S2S11U14S44S41Z1A2A4S0G0S1S2S11U18S44S41Z57A2A4S0G0S1S2S11U19S43Z2b8A1A4S3G0A1A3A3A3A3Se6S49S45S3eS3fS4eS4bSaeS40S4cS54S52Af").
Definition C_8 : axst := mkA C_8_S X_fs0.
Definition nd8 : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S4aS3eS3fA2S36S40S6A2A4").

Definition Pre_vp : axst := VP.Pre_vp.
Definition xf_vpcall : list axform := ltac2:(tb__ "0|2|
S0S17eS17fU6Z1c0A2S0S17eS181U1M0S12N30M1A1A2S0S17eS17fG0G1A2S3S17eA1A3A3A3").
Definition E_vp0 : axst := Eval vm_compute in leafC_at C_8 vp_entry 0.
Definition E_vp : axst := Eval vm_compute in optA (apply_axforms E_vp0 xf_vpcall).
Definition s_vp : wsub := ltac2:(tb__ "0|0|
S0S4S2dS11A2S1S2dS11P13S16S179S4fS12Z30A1A3A4S190PaS2fSe4A1S2fS104A1A3A3").
Definition R_vp : list sobj := Eval vm_compute in optR (entails_frA E_vp Pre_vp s_vp).
Definition PD_vp : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S4S2eS34A2M0S1S2eS34S1c2S1c3A4S0G0S1S2eS34S1c0S38S1c6S3S4S4S11S2cA2S11A2A1S3S185A1A3A4S0G0S1S2eS34S1c1S1c4S1c7S1c8A2A4S3G0A1A3A3A3").
Definition Xk_vp : list (sv * sv) := ltac2:(tb__ "0|2|
S19dS4S11S11A2M0G0SfS8S1bS9S11S11R1A3M1S5dA2A1S8S1bG1S45A2A1A2Lr;S5fA3").

Definition perm_vp : list nat := ltac2:(tb__ "0|4|
S5S2S0S2U7M0S0S2U1S0S2U0S3S2A1M1A3A3A3S5S2S18bU8U4M2A2S5S2S0S2U2G1A3S5S2S18bUcM3G3A2S5S2S0S2U3S0S2U18G1A3A3S5S2S18bU19G0A2S0S2G2S0S2U5S0S2U6G1A3A3A3A3A3A3A3A3A3").
Definition xf_back_vp : list axform := ltac2:(tb__ "0|1|
S0S17eS17fU1M0Z30A2S0S17eS180S162A1S0S17eS182G0A1S0S17eS183U6A1S3S17eA1A3A3A3A3").
Definition T_pk0 : axst := Eval vm_compute in T_afterA3 Pre_vp E_vp s_vp R_vp VP.P_push_keep Xk_vp.
Definition T_pf0 : axst := Eval vm_compute in T_afterA3 Pre_vp E_vp s_vp R_vp VP.P_push_fail Xk_vp.
Definition T_pg0 : axst := Eval vm_compute in T_afterA3 Pre_vp E_vp s_vp R_vp VP.P_push_grown Xk_vp.
Definition T_pk : axst := Eval vm_compute in optA (apply_axforms T_pk0 xf_back_vp).
Definition T_pf : axst := Eval vm_compute in optA (apply_axforms T_pf0 xf_back_vp).
Definition T_pg : axst := Eval vm_compute in optA (apply_axforms T_pg0 xf_back_vp).

Definition hse_fact : sprop := ltac2:(tb__ "0|0|
S15S12S1afA1S45A2").

Definition top_factK : sprop := ltac2:(tb__ "0|0|
S15S16S179S45S4dZ80S3fA2A3S12Z7fffff800000A1A2").
Definition T_pkF : axst := ltac2:(tb__ "0|0|
S198S0S13S148S0S13S16aS3S13A1A3A3S121A2").
Definition vDg : sv := SVar 320. Definition vKg : sv := SVar 321.
Definition top_factG : sprop := ltac2:(tb__ "0|0|
S15S16S179S8eS4dZ80S90A2A3S12Z7fffff800000A1A2").
Definition T_pgF : axst := ltac2:(tb__ "0|0|
S198S0S13S169S3S13A1A3S11fA2").

Definition slotx (d : sv) : sv := ltac2:(tb__ "0|0|
S16S179Vd;S4dZ80S3eA2A3").
Definition hole_obj (d : sv) : sobj := ltac2:(tb__ "0|0|
S1aS16S179S168Vd;A1S12Z38A1A3S12Z0A1S12Z10A1S3S14A1S19A5").
Definition mid_obj (d : sv) : sobj := ltac2:(tb__ "0|1|
S1aVd;S16S179S4dZ80S3eA2M0S12Z38A1A3S16S179G0S12Z48A1A3S3S14A1S19A5").
Definition xf_mcall : list axform := ltac2:(tb__ "0|1|
S0S17eS181U1cS16S179S4dZ80S3eA2M0S12Z38A1A3A2S0S17eS181U1dS16S179G0S12Z48A1A3A2S3S17eA1A3A3").
Definition Pre_ms : axst := Pre_memset memset_pc.
Definition L_ms : axst := L_memset memset_ret.
Definition V_XB : positive := 53%positive.
Definition V_XL : positive := 54%positive.
Definition s_m (E : axst) (d k : sv) : wsub := ltac2:(tb__ "0|1|
S0S4S2dS11A2M0S1S2dS11S123Vd;A4S0G0S1S2dS11S124S4dZ80Vk;A2A4S190PaS2fVE;A1S2fS103A1A3A3A3").
Definition E_mk0 : axst := Eval vm_compute in leafC_at T_pkF memset_pc 0.
Definition E_mg0 : axst := Eval vm_compute in leafC_at T_pgF memset_pc 0.
Definition E_mk1 : axst := Eval vm_compute in optA (apply_axforms E_mk0 xf_mcall).
Definition E_mg1 : axst := Eval vm_compute in optA (apply_axforms E_mg0 xf_mcall).
Definition E_mk : axst := Eval vm_compute in ax_setS E_mk1 (reshape_obj_at (ax_S E_mk1) 29 (hole_obj sh_d)).
Definition E_mg : axst := Eval vm_compute in ax_setS E_mg1 (reshape_obj_at (ax_S E_mg1) 29 (hole_obj vDg)).
Definition R_mk : list sobj := Eval vm_compute in optR (entails_frA E_mk Pre_ms (s_m E_mk sh_d sh_k)).
Definition R_mg : list sobj := Eval vm_compute in optR (entails_frA E_mg Pre_ms (s_m E_mg vDg vKg)).
Definition T_mk0 : axst := Eval vm_compute in T_afterA Pre_ms E_mk (s_m E_mk sh_d sh_k) R_mk L_ms.
Definition T_mg0 : axst := Eval vm_compute in T_afterA Pre_ms E_mg (s_m E_mg vDg vKg) R_mg L_ms.

Definition perm_m : list nat := ltac2:(tb__ "0|1|
S5S2S0S2U4S0S2U0S3S2A1M0A3A3S5S2S18bU5U1aA2S0S2U1fS0S2U1S0S2U20S0S2U2S0S2U3G0A3A3A3A3A3A3A3").
Definition xf_mback : list axform := ltac2:(tb__ "0|1|
S0S17eS180S15fA1S0S17eS182U1cA1M0S0S17eG0S3S17eA1A3A3A3").
Definition T_mk1 : axst := ltac2:(tb__ "0|0|
S32Sa6S1b7S2fSa6A1U1Sb4S45A1A3A2").
Definition T_mg1 : axst := ltac2:(tb__ "0|0|
S32Sa5S1b7S2fSa5A1U1Sb4S8eA1A3A2").
Definition T_mk : axst := Eval vm_compute in optA (apply_axforms T_mk1 xf_mback).
Definition T_mg : axst := Eval vm_compute in optA (apply_axforms T_mg1 xf_mback).

Definition qD : sv := SVar 260. Definition qK : sv := SVar 261. Definition qHD : sv := SVar 262. Definition qERR : sv := SVar 263.
Definition qcs : list sv := ltac2:(tb__ "0|0|
S18cS2S11S2S18S1cfS197U108R1A2A1A1Li;S18bU0U7A2A4").
Definition post_fs (a0 : sv) (err shd shc shk hp : sv) (cs : list sv) (hd : sv) (dats : list sobj) (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|1|
S1a6S21S19aS1a9S1aaS58A1S0S4S2S11A2M0S1S2S11UaVa0;A4S3G0A1A3A2S1a8S1fSeS11A1S83S3S14A1Verr;Vshd;Vshc;Vshk;S4eVhp;Vcs;Vhd;Vdats;AaS5S13Vfacts;S0S13S15Vhd;S18P1eA1A2S84A3A3S52SbA9VX;A2").

Definition P_nop : axst := ltac2:(tb__ "0|0|
S75S12Z1A1S49S45S3eS3fS4bS48S42S4cS3S13A1S5fAb").
Definition nd_nop : ndesc := nd0.

Definition dats_ok : list sobj := ltac2:(tb__ "0|0|
S5S17S18cS3cS17S7fS50A4S0S17Sa2S56Z80S5cA3S3S17A1A3A3").
Definition X_ok : list (sv * sv) := ltac2:(tb__ "0|2|
S5S4S11S11A2M0S0G0S1S11S11S55S12Z518A1A4S0G0S1S11S11S5dS12Z30A1A4S0G0S1S11S11S47S12Z40A1A4S3G0A1M1A3A3A3S5G0S18cS3cG0S60S50A4S0G0S1S11S11S56S4dZ80S5cA2A4G1A3A3A3").
Definition ok_facts : list sprop := ltac2:(tb__ "0|3|
S5S13S0S13S15S16S179S3eS12Z1A1A3S5cA2S0S13S1cP104Z4A2S0S13S15S12Z1000A1S56A2S0S13S15S12S1afA1S56A2S0S13S15S56S18P1eA1M0A2S0S13S15S16S179S56S4dZ80S5cA2M1A3G0A2S0S13S15S56S12S8dA1A2S0S13S15S5cS12S97A1M2A2S0S13S15G1G2A2S3S13A1A3A3A3A3A3A3A3A3A3S54A3").
Definition P_ok : axst := ltac2:(tb__ "0|1|
S75S12Z1A1M0S49S56S16S179S3eG0A3S5cS12Z0A1SaeS6bS13dS157S12cAb").
Definition tv_ok : list (sv * sv) := ltac2:(tb__ "0|1|
S5S4S11S11A2M0S18cS3cG0S60S50A4S0G0S1S11S11S56S4dZ80S5cA2A4S0G0S1S11S11S47S12Z40A1A4S3G0A1A3A3A3").
Definition nd_ok : ndesc := ltac2:(tb__ "0|0|
S35S16dS3S4S4S11S2cA2S11A2A1S4aS3eS5cA2S36S6bS6A2A4").

Definition fail_facts : list sprop := ltac2:(tb__ "0|1|
S0S13S24S1dS17aS22S6Q20S49A3S12Z0A1A3A1S18cS4S3cS11A2M0S13G0S15ScS3cS11R1A3S6cS9S3cS11R1A3A1A2Lvc;S19eS3cS11S50S76A4A4A3").
Definition P_fail : axst := ltac2:(tb__ "0|0|
S75S12Z0A1S49S45S3eS3fS4bS76S6bS4cS13fS5fAb").
Definition nd_fail_t : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S3S185A1S36S6bS6A2A4").
Definition nd_fail_f : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S3S185A1S36S6bSbA2A4").

Definition failz_facts : list sprop := ltac2:(tb__ "0|1|
S5S13S0S13S1dS17aS22S6Q20S49A3S12Z0A1A3S0S13S15S12Z2A1S8cA2S0S13S15S8cS12Z7A1A2S3S13A1A3A3A3S18cS4S3cS11A2M0S13G0S15ScS3cS11R1A3S6cS9S3cS11R1A3A1A2Lvc;S19eS3cS11S50S76A4A4A3").
Definition P_failz : axst := ltac2:(tb__ "0|0|
S75S12Z0A1S8cS45S3eS3fS4bS76S6bS4cS141S5fAb").

Definition vGH : sv := SVar 259.
Definition ghZ : sprop := SPEq vGH (SLit 0).
Definition T5_zG : axst := ltac2:(tb__ "0|0|
S198S0S13S86S3S13A1A3S10fA2").
Definition T6_zG : axst := ltac2:(tb__ "0|0|
S198S0S13S86S3S13A1A3S113A2").
Definition T7_zG : axst := ltac2:(tb__ "0|0|
S198S0S13S86S3S13A1A3S117A2").
Definition s_gh (T : axst) : wsub := ltac2:(tb__ "0|1|
S0S4S2dS11A2S1S2dS11P103S12Z0A1A4S190S58S2fVT;A1M0G0A3A3").

Definition X_N0 : axst := Eval vm_compute in leafC_at C_E 0x8f784 0.

Definition z0 : sv := SLit 0.

Definition ndTok (j : nat) (hq : sv) : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S5S185S51Vj;S48A2S4aS3eS3fA2A3S36Vhq;S6A2A4").
Definition ndTf (j : nat) (hq : sv) : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S5S185S51Vj;S48A2S4aS3eS3fA2A3S36Vhq;SbA2A4").

Definition ndTz (j : nat) (v : vdesc) : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S5S185Sc9Vv;S6fVv;A1A2S5S185S51Vj;S48A2S4aS3eS3fA2A3A3S36S40S6A2A4").
Definition vHa : sv := SVar 321.
Definition vHv : sv := SVar 322.
Definition ndPk : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S4aS3eS3fA2S36S40S6A2A4").
Definition tv_g : list (sv * sv) := ltac2:(tb__ "0|1|
S5S4S11S11A2M0S18cS3cG0S60S50A4S0G0S1S11S11S8eS4dZ80S90A2A4S0G0S1S11S11S47S12Z40A1A4S3G0A1A3A3A3").
Definition ndPg : ndesc := ltac2:(tb__ "0|0|
S35S16bS3S4S4S11S2cA2S11A2A1S4aS3eS90A2S36S40S6A2A4").
Definition ndPf : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S3S185A1S36S40S6A2A4").
Definition cutsE : list edescA := ltac2:(tb__ "0|13|
S0S4S4S2eS34A2M0S4S2cS11A2M1A2M2S1G0G1S1S2eS34S71S152A4S1S2cS11Zc8S3dA4A4S0G2S1G0G1S1S2eS34Sd2S62A4S1S2cS11ZbeS3dA4A4S0G2S1G0G1S1S2eS34S7dSb5A4S1S2cS11Z96S3dA4A4S0G2S1G0G1S1S2eS34S106S64U1M3S7aA2A4S1S2cS11Z91S3dA4M4A4S0G2S1G0G1S1S2eS34S105S63G3S40A2A4G4A4S0G2S1G0G1S1S2eS34ScbSb6A4S1S2cS11Z8cS3dA4A4S0G2S1G0G1S1S2eS34S108S64U2M5S7aA2A4S1S2cS11Z87S3dA4M6A4S0G2S1G0G1S1S2eS34S107S63G5S40A2A4G6A4S0G2S1G0G1S1S2eS34SccSb7A4S1S2cS11Z82S3dA4A4S0G2S1G0G1S1S2eS34S10aS64U3M7S7aA2A4S1S2cS11Z7dS3dA4M8A4S0G2S1G0G1S1S2eS34S109S63G7S40A2A4G8A4S0G2S1G0G1S1S2eS34ScdSb8A4S1S2cS11Z78S3dA4A4S0G2S1G0G1S1S2eS34S10cS64U4M9S7aA2A4S1S2cS11Z73S3dA4MaA4S0G2S1G0G1S1S2eS34S10bS63G9S40A2A4GaA4S0G2S1G0G1S1S2eS34SceSb9A4S1S2cS11Z6eS3dA4A4S0G2S1G0G1S1S2eS34S110S69U5MbS92A2A4S1S2cS11Z69S3dA4McA4S0G2S1G0G1S1S2eS34S10eS64GbS8fA2A4GcA4S0G2S1G0G1S1S2eS34S10dS63GbS40A2A4GcA4S0G2S1G0G1S1S2eS34ScfSbaA4S1S2cS11Z64S3dA4A4S0G2S1G0G1S1S2eS34S114S69U6MdS91A2A4S1S2cS11Z5fS3dA4MeA4S0G2S1G0G1S1S2eS34S112S64GdS8fA2A4GeA4S0G2S1G0G1S1S2eS34S111S63GdS40A2A4GeA4S0G2S1G0G1S1S2eS34Sd0SbbA4S1S2cS11Z5aS3dA4A4S0G2S1G0G1S1S2eS34S118S69U7MfS93A2A4S1S2cS11Z55S3dA4M10A4S0G2S1G0G1S1S2eS34S116S64GfS8fA2A4G10A4S0G2S1G0G1S1S2eS34S115S63GfS40A2A4G10A4S0G2S1G0G1S1S2eS34Sd1SbcA4S1S2cS11Z50S3dA4A4S0G2S1G0G1S1S2eS34S122S8bA4S1S2cS11Z4bS3dA4M11A4S0G2S1G0G1S1S2eS34S11eS89A4G11A4S0G2S1G0G1S1S2eS34S120S8aA4G11A4S0G2S1G0G1S1S2eS34S11aS8bA4S1S2cS11Z41S3dA4M12A4S0G2S1G0G1S1S2eS34S119S8aA4G12A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition retleaf (S : axst) (k : nat) : axst := ltac2:(tb__ "0|0|
Sb2VS;S19aVk;A3").
Definition FL_E0 : axst := Eval vm_compute in retleaf C_E 0.   Definition FL_E1 : axst := Eval vm_compute in retleaf C_E 1.
Definition FL_50 : axst := Eval vm_compute in retleaf T5_zG 0.  Definition FL_51 : axst := Eval vm_compute in retleaf T5_zG 1.
Definition FL_60 : axst := Eval vm_compute in retleaf T6_zG 0.  Definition FL_61 : axst := Eval vm_compute in retleaf T6_zG 1.
Definition FL_70 : axst := Eval vm_compute in retleaf T7_zG 0.  Definition FL_71 : axst := Eval vm_compute in retleaf T7_zG 1.
Definition FL_p0 : axst := Eval vm_compute in retleaf T_pf 0.  Definition FL_p1 : axst := Eval vm_compute in retleaf T_pf 1.
Definition fails_t : list edescA := ltac2:(tb__ "0|7|
S0S4S4S2eS34A2M0S4S2cS11A2M1A2M2S1G0G1S1S2eS34SefS62A4S1S2cS11Z5S3dA4M3A4S0G2S1G0G1S1S2eS34Sf0S62A4G3A4S0G2S1G0G1S1S2eS34Se9S69U5S92A2M4A4G3A4S0G2S1G0G1S1S2eS34SeaG4A4G3A4S0G2S1G0G1S1S2eS34SebS69U6S91A2M5A4G3A4S0G2S1G0G1S1S2eS34SecG5A4G3A4S0G2S1G0G1S1S2eS34SedS69U7S93A2M6A4G3A4S0G2S1G0G1S1S2eS34SeeG6A4G3A4S0G2S1G0G1S1S2eS34Sf1S89A4G3A4S0G2S1G0G1S1S2eS34Sf2S89A4G3A4S3G2A1A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|6|
S5S4S4S2eS34A2M0S4S2cS11A2M1A2M2S0G2S1G0G1S1S2eS34Sa8S62A4S1S2cS11Zb9S3dA4A4S0G2S1G0G1S1S2eS34Sd5Sb5A4S1S2cS11Z94S3dA4A4S0G2S1G0G1S1S2eS34Sd7Sb6A4S1S2cS11Z8aS3dA4A4S0G2S1G0G1S1S2eS34Sd9Sb7A4S1S2cS11Z80S3dA4A4S0G2S1G0G1S1S2eS34SdbSb8A4S1S2cS11Z76S3dA4A4S0G2S1G0G1S1S2eS34SdfSb9A4S1S2cS11Z6cS3dA4A4S0G2S1G0G1S1S2eS34Se1SbaA4S1S2cS11Z62S3dA4A4S0G2S1G0G1S1S2eS34Se3SbbA4S1S2cS11Z58S3dA4A4S0G2S1G0G1S1S2eS34Se5SbcA4S1S2cS11Z4eS3dA4A4S0G2S1G0G1S1S2eS34SddS8bA4S1S2cS11Z46S3dA4M3A4S0G2S1G0G1S1S2eS34SdcS8aA4G3A4S3G2A1M4A3A3A3A3A3A3A3A3A3A3A3S5S39S140S0G2S1G0G1S1S2eS34SffS154A4S1S2cS11Z0S3dA4M5A4S0G2S1G0G1S1S2eS34S100S155A4G5A4S0G2S1G0G1S1S2eS34Sa3S72A4G5A4S0G2S1G0G1S1S2eS34Sa4S72A4G5A4G4A3A3A3A3A3A3").

Definition cutpcsN : list Z := ltac2:(tb__ "0|0|
S0S2cZ8f7b4S0S2cZ8f7ecS0S2cZ8fa6cS0S2cZ8f620S0S2cS1b0S0S2cS19aS3S2cA1A3A3A3A3A3A3").
Definition leafN_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S18dS2eVk;S1a2S67SafVS;Vpc;A4S71A4").
Definition runN (S : axst) : list axst := ltac2:(tb__ "0|1|
SaS7S30A1M0A1S7S2eA1Lx;S31S1a3S67SafVS;S6A5G0S18cS30S2eS33R1A4Lls;S3S2eA1Xax2").

Definition X_open0 : axst := Eval vm_compute in leafN_at X_N0 0x8f7b4 0.
Definition nO : positive := Eval vm_compute in ss_next (ax_S X_open0).
Definition C_open : axst := Eval vm_compute in open_stateA X_open0 vHD.
Definition vNX : sv := Eval vm_compute in SVar nO.
Definition vCAP : sv := Eval vm_compute in SVar (nO + 1).
Definition vU : sv := Eval vm_compute in SVar (nO + 2).
Definition am_open : amode := ltac2:(tb__ "0|0|
S37S42S174Sc3S3S4S11S11A2A1A4").
Definition bd_open : list bitem := bd0 ++ POT vU.
Definition ndO : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S133S131A4").

Definition X_nohead : axst := Eval vm_compute in leafN_at X_N0 0x8f7ec 0.

Definition X_fit : axst := Eval vm_compute in leafN_at C_open 0x8fa6c 0.
Definition X_nofit : axst := Eval vm_compute in leafN_at C_open 0x8f7ec 0.

Definition pGA : sv := SVar 243.
Definition FEa (g : sv) : list sprop := ltac2:(tb__ "0|1|
S0S13S20S85Vg;A1M0S47A2S0S13S15Vg;S12S193S192Z2Z3dA2Z1A2A1A2S0S13S15G0S47A2S0S13S15S47G0A2S3S13A1A3A3A3A3").
Definition vUg : sv := SVar 258.
Definition ug_facts : list sprop := ltac2:(tb__ "0|0|
S0S13S15S12Z10000A1S95A2S0S13S15S95S12S79A1A2S3S13A1A3A3").
Definition C_slow_S : sstate := ltac2:(tb__ "0|1|
S53Z8f7ecS41S0S4S2S11A2M0S1S2S11UaS47A4S0G0S1S2S11U13S43Z8A1A4S0G0S1S2S11U14S16S179S47S12Z30A1A3A4S0G0S1S2S11U16S44S73Z6A2A4S3G0A1A3A3A3A3S6dS49S45S3eS3fS4eS4bS48S42S4cS5S13S54S5S13S16eSa0S73A1A3A3S52Af").
Definition C_slow : axst := mkA C_slow_S X_fs0.
Definition am_np : amode := AHead vHD false.
Definition ndS : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S5S185SaaS1acS95A1A3S81A4").

Definition E_m : axst := Eval vm_compute in leafN_at C_slow malloc_pc 0.
Definition Pre_m : axst := ltac2:(tb__ "0|0|
S1cbS1caS3S1cdA1S1ccA3").
Definition s_ma : wsub := ltac2:(tb__ "0|0|
S0S4S2dS11A2S1S2dS11PfS4fA4S190PaS2fS99A1S2fS102A1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_m Pre_m s_ma).
Definition pN : positive := Eval vm_compute in pos_add_nat (ss_next (ax_S E_m)) 10.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S1S11S11S18Sc2A1S12Z10020A1A4").
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_ma R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_ma R_m (L_malloc_ok AE_A [] UStopLe).
Definition T_mok : axst := ltac2:(tb__ "0|0|
S198S3aS134A1S11dA2").

Definition bd_rest : list bitem := ltac2:(tb__ "0|0|
S5S185S51U0S48A2S4aS3eS3fA2A3").
Definition bd_m : list bitem := ltac2:(tb__ "0|1|
S5S185S0S185S189Z0Z1M0S18aA3S3S185A1A3S5S185S1acS12G0A1A1SacA3A3").
Definition tv_m : list (sv * sv) := blkN :: tv0.
Definition ndM : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1SabS81A4").
Definition ndMok : ndesc := ltac2:(tb__ "0|0|
S35S16cS3S4S4S11S2cA2S11A2A1SabS81A4").

Definition vNXl : sv := SVar 244. Definition vCAPl : sv := SVar 245. Definition vUo : sv := SVar 246. Definition pGH : sv := SVar 247.
Definition FEh (g : sv) : list sprop := ltac2:(tb__ "0|1|
S0S13S20S85Vg;A1M0S42A2S0S13S15Vg;S12S193S192Z2Z3dA2Z1A2A1A2S0S13S15G0S42A2S0S13S15S42G0A2S3S13A1A3A3A3A3").
Definition pfit : sv := ltac2:(tb__ "0|0|
S16S179S16S179S42S5eA3S12Z20A1A3").
Definition O_hdrN (hd nx cap u : sv) : sobj := ltac2:(tb__ "0|1|
S1aVhd;S12Z0M0A1S12Z18A1S0S14S3bG0Vnx;A2S0S14S3bZ8Vcap;A2S0S14S3bZ10Vu;A2S3S14A1A3A3A3S19A5").
Definition O_slotN (p : sv) : sobj := ltac2:(tb__ "0|0|
S1aVp;S12Z0A1S12Z1A1S3S14A1S19A5").
Definition nz_facts : list sprop := ltac2:(tb__ "0|5|
S0S13S1dS17cS57S16S179S5eS12Z1A1M0A3A3S0S13S15S5eS57A2S0S13S15S12Z10000A1S57A2S0S13S15S57S12S193S79Z21A2A1A2S0S13S15S16S179S42S1adS57A1A3M1S18P1eA1M2A2S0S13S15S12Z1000A1M3S42A2S0S13S1cP66Z4A2S0S13S15S16S179S42S12Z20A1A3S6aA2S0S13S15S16S179S6aG0A3M4G1A2S0S13S15G3S6aA2S0S13S15G4G2A2S0S13S15S6aG2A2S0S13S15S5eS12S79A1A2S3S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition C_nz_S : sstate := ltac2:(tb__ "0|1|
S53Z8fa6cS41S0S4S2S11A2M0S1S2S11UaS47A4S0G0S1S2S11UbS16S179S42S12Z10A1A3A4S0G0S1S2S11UcS16S179S5eS12Z1A1A3A4S0G0S1S2S11UdS42A4S0G0S1S2S11UeS44Sc1Z2A2A4S0G0S1S2S11UfS5eA4S0G0S1S2S11U10S57A4S0G0S1S2S11U13S43Z8A1A4S0G0S1S2S11U14S16S179S47S12Z30A1A3A4S0G0S1S2S11U16S44S73Z6A2A4S3G0A1A3A3A3A3A3A3A3A3A3A3S6dS49S45S3eS3fS4eS4bS48S42S4cS5S13S54S5S13S156S5S13Se8Sc1A1Sa0S73A1A3A3A3S52AfS2bS1b6R1S5S17S1eR1A1S0S17Sf7S42Sc4S57S5eA4S0S17Sf8S6aA1S3S17A1A3A3A3A2TS;").
Definition X_nz : list (sv * sv) := ltac2:(tb__ "0|0|
S0S4S11S11A2S1S11S11S42S1adS57A1A4S5fA3").
Definition C_nz : axst := mkA C_nz_S X_nz.
Definition am_nz : amode := ltac2:(tb__ "0|1|
S37S42Sc4S57S0S4S11S11A2M0S1S11S11S6aS12Z1A1A4S3G0A1A3A4").
Definition bd_nz : list bitem := ltac2:(tb__ "0|0|
S5S185SacS1acS16S179S5eS12Z1A1A3A1A3").
Definition ndZ : ndesc := ltac2:(tb__ "0|0|
S35S46S3S4S4S11S2cA2S11A2A1S132S130A4").

Definition pfit0 : sv := ltac2:(tb__ "0|0|
S16S179S16S179S42S94A3S12Z20A1A3").
Definition fit_facts : list sprop := ltac2:(tb__ "0|2|
S0S13S15S12Z1000A1S74A2S0S13S15S74S18P1eA1M0A2S0S13S15S16S179S74S12Z1A1A3M1S16S179S42S1adSc3A1A3A2S0S13S15G1G0A2S0S13S15S16S179S42S12Z20A1A3S74A2S0S13S15S94S12S79A1A2S3S13A1A3A3A3A3A3A3").
Definition X_fit3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_fit pfit0 (SLit 1)) (fit_facts ++ ss_facts (ax_S X_fit)).
Definition s_fit : wsub := ltac2:(tb__ "0|0|
S190S58S2fS127A1S2fS98A1A3").

Definition nofit_fact : sprop := SPUle (SLit 65536) vU.
Definition X_nofit1 : axst := Eval vm_compute in drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit))).
Definition X_nofit2 : axst := Eval vm_compute in ax_with_facts X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1)).
Definition s_nofit : wsub := ltac2:(tb__ "0|0|
S0S4S2dS11A2S1S2dS11P102S94A4S190S58S2fS129A1S2fS7eA1A3A3").
Definition s_nohead : wsub := ltac2:(tb__ "0|0|
S0S4S2dS11A2S1S2dS11P102S12Z10000A1A4S190S58S2fSa9A1S2fS7eA1A3A3").

Definition X_nzret : axst := Eval vm_compute in leafN_at C_nz 0x8f620 0.
Definition X_nzret2 : axst := Eval vm_compute in drop_lastA X_nzret (removelast (ss_objs (ax_S X_nzret))).
Definition X_nzret3 : axst := Eval vm_compute in drop_lastA X_nzret2 (removelast (ss_objs (ax_S X_nzret2))).
Definition s_nzret : wsub := ltac2:(tb__ "0|0|
S190S58S2fS12bA1S2fS7dA1A3").

Fixpoint find_idxb {T} (f : T -> bool) (l : list T) (k : nat) : nat :=
  match l with [] => k | x :: r => if f x then k else find_idxb f r (S k) end.
Definition sret_pipe (X : axst) : axst * axst := ltac2:(tb__ "0|2|
S144S17S17S1bS27R1A1S18Sc2A1A2Lo;S1eS2fVX;A1A1M0U0M1A4S2S5S2S19dS2S2S8S1ceR1R2A2A1Lj;S18bG1S10S17G0A2A2A3S0S2R1S3S2A1A3A3S7S2A1Sc0S184VX;S0S17eS180R1A1S0S17eS181S196S10S2R1A2U1A2S12Z18A1A2S3S17eA1A3A3A2A1S2eS1aeR1S1a1S17S1eS2fR1A1A1A2A2S2eS1S2eS2eR2R1A4TX2;TX1;Tsel;TiN;").
Definition X_sret : axst := Eval vm_compute in leafN_at T_mok 0x8f620 0.
Definition X_sret1 : axst := Eval vm_compute in fst (sret_pipe X_sret).
Definition X_sret2 : axst := Eval vm_compute in snd (sret_pipe X_sret).
Definition X_sret3 : axst := Eval vm_compute in drop_lastA X_sret2 (removelast (ss_objs (ax_S X_sret2))).
Definition s_sret : wsub := ltac2:(tb__ "0|0|
S190S58S2fS12fA1S2fS7dA1A3").

Definition cutsN : list edescA := ltac2:(tb__ "0|4|
S0S4S4S2eS34A2M0S4S2cS11A2M1A2M2S1G0G1S1S2eS34Sa8S62A4S1S2cS11Z64S3dA4A4S0G2S1G0G1S1S2eS34Sd3S88A4S1S2cS11Z5aS3dA4A4S0G2S1G0G1S1S2eS34S7eSbeA4S1S2cS11Z50S3dA4A4S0G2S1G0G1S1S2eS34S11bS153A4S1S2cS11Z41S3dA4M3A4S0G2S1G0G1S1S2eS34S11cSbdA4G3A4S0G2S1G0G1S1S2eS34S98SbfA4S1S2cS11Z32S3dA4A4S3G2A1A3A3A3A3A3A3").
Definition exitsN : list edescA := ltac2:(tb__ "0|6|
S0S4S4S2eS34A2M0S4S2cS11A2M1A2M2S1G0G1S1S2eS34S12dS62A4S1S2cS11Z5fS3dA4M3A4S0G2S1G0G1S1S2eS34Sa9S62A4G3A4S0G2S1G0G1S1S2eS34S126S88A4S1S2cS11Z55S3dA4M4A4S0G2S1G0G1S1S2eS34S128S88A4G4A4S0G2S1G0G1S1S2eS34S99SbeA4S1S2cS11Z46S3dA4A4S0G2S1G0G1S1S2eS34S12eSbdA4S1S2cS11Z3cS3dA4A4S0G2S1G0G1S1S2eS34S12aSbfA4S1S2cS11Z28S3dA4A4S0G2S1G0G1S1S2eS34Sa3S72A4S1S2cS11Z0S3dA4M5A4S0G2S1G0G1S1S2eS34Sa4S72A4G5A4S3G2A1A3A3A3A3A3A3A3A3A3").

Definition rdiff (C : sstate) (A : axst) : list (nat * sv * sv) := ltac2:(tb__ "0|3|
S19dS4S4S2S11A2M0S11A2M1G1S8S1bScS2S11S9G0S11R1A3A3ScG0S11R1A3A2A1Lp;S18cS2G1S2S1G0S11S1S2S11R1S18dS11R1S26S2fVA;A1A1S12Z0A1M2A4A4S18dS11R1S26VC;A1G2A4A4Li;S18bU0U20A2A4A3").
Definition showL (C : sstate) (A : axst) : ltac2:(tb__ "0|0|
S4S4S4S2cS7S13A1A2S7S4S4S2S11A2S11A2A1A2S7S14A1A2") := ltac2:(tb__ "0|4|
S1S4S4S2cS7S13A1M0A2M1S7S4S4S2S11A2S11A2A1M2A2S7S14A1S1G1G2S1S2cG0S2aS2fVA;A1M3A1S18eS13U3S29G3A1A3A4S165VC;VA;A2A4S18eS14U5S28S18dS17U0S1eG3A1Sa1A4A1A3A4").
Definition runC (S : axst) : list axst := ltac2:(tb__ "0|1|
SaS7S30A1M0A1S7S2eA1Lx;S31S1a3S67Sb0VS;S6A5G0S18cS30S2eS33R1A4Lls;S3S2eA1Xax2").
