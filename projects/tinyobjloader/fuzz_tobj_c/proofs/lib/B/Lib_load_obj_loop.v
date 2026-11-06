(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "pair"; "app"; "nat"; "prod"; "bool"; "list"; "None"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "SPUle"; "cell"; "SAlu"; "SVar"; "mkObj"; "DUnknown"; "SPUlt"; "SPAlign"; "SMd"; "ss_objs"; "SPBranch"; "DZero"; "FcsrFrm0"; "SExt"; "SPNot"; "mkSS"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve_darr"; "c8"; "two47"; "B32"; "spm"; "two40"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pI"; "t_k"; "t_d"; "t_c"; "zt"; "O_dataA"; "t3"; "VA"; "xLC"; "VdA"; "vec_factsA"; "pPOS"; "pLNL"; "bpiece"; "k_v"; "xLD"; "txt"; "vsP"; "CST"; "pCN"; "pH"; "pHP"; "pT0"; "xCM"; "xLK"; "xSM"; "ent_facts"; "pQ"; "v_av"; "v_avt"; "O_ent"; "pE"; "pR"; "v_acol"; "v_avn"; "v_avtw"; "v_avw"; "v_fv"; "v_lc"; "v_li"; "v_mi"; "v_mm"; "v_pi"; "v_sg"; "v_sh"; "cA"; "k_ent"; "k_ld"; "k_lk"; "nx_facts"; "pERR"; "pNX"; "rate_factsLo"; "v_co"; "v_rp"; "v_tr"; "v_ts"; "vec_factsK"; "LIA"; "LSA"; "LSAb"; "LSAc"; "LSAx"; "VAd"; "add_datas"; "add_ents"; "alA"; "bA"; "fpc"; "txtE"; "NZ32e"; "VS"; "avt2"; "coreA"; "datasA"; "gFV"; "gLC"; "gLI"; "gMI"; "gMM"; "gPI"; "gSG"; "kL"; "kX"; "k_cn"; "k_hd"; "k_hp"; "k_lc"; "pE0"; "tv_vecs"; "BIG"; "HNEXT"; "O_alA"; "O_arA"; "O_f5fl"; "O_f5gap"; "O_f5hdr"; "O_f5loc"; "O_f5rz"; "O_lnhA"; "O_lnkS"; "O_midA"; "O_savA"; "O_spillA"; "P_allocA"; "P_capsA"; "P_csA"; "P_curA"; "P_ffA"; "P_hdrA"; "P_matA"; "P_stA"; "X_loopA"; "arena_factsLo"; "av3"; "av_factsA"; "builderA"; "cnt_factsLo"; "entA"; "fkeepA"; "frame_factsLo"; "gCO"; "gRP"; "gS"; "gTR"; "gTS"; "ghost_factsLo"; "gran_factsLo"; "hf"; "hx"; "ifactsA"; "iregsA"; "kB"; "kI"; "kLE"; "kX7"; "kXE"; "k_ce"; "k_cm"; "k_cp"; "k_err"; "k_line"; "k_loc"; "k_out"; "k_sm"; "lfregsA"; "lines_factsA"; "lnA"; "loop_factsA"; "lregsA"; "misc_factsA"; "rate2"; "spill_cells"; "vecs_factsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "aluop"; "mulop"; "ALU_SLL"; "ALU_SUB"; "ALU_XOR"; "BC_EQ"; "BC_NE"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "pc_latch"; "pc_body"; "pc_dp"; "pc_l2l"; "pc_tk"; "pc_ws"; "c_ad"; "c_bd"; "c_bw"; "c_da"; "c_fs"; "c_fu"; "c_hf"; "c_hff"; "c_hl"; "c_hm"; "c_hp"; "c_hvn"; "c_hvt"; "c_ir"; "c_mf"; "c_nt"; "c_op"; "c_sd"; "c_si"; "c_vf"; "c_vr"; "pc_after"; "pc_errx"; "pc_join"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "vARn"; "blkAR"; "pAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "c1"; "c4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vF"; "vLEN"; "g5"; "vFL"; "vOUT"; "O_Dlo"; "O_cfg"; "O_lnk"; "O_out"; "O_txtL"; "X_lo"; "cps_pro"; "lo_facts"; "vCFGp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface";
"al48_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "SHB"; "A_globals"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs.LOAddr"; "FR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@Stdlib.PArith.BinPos.Pos"; "add"; "of_nat"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro2"; "X_body1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "two26"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve_darr.RA.ReallocAddr"; "free_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "frame_factsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import DrvGlueC ObjEmptyA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_vec_reserve_darr Lib_build_line_index.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr VRAddr RA.ReallocAddr VRDAddr LOAddr.

Module LOLAddr.
  Definition pc_latch : Z := 0x8d674.
  Definition pc_body : Z := 0x8d67c.
  Definition pc_errx : Z := 0x8e7cc.
  Definition pc_l2l : Z := 0x8d670.
  Definition pc_ws : Z := 0x8d768.
  Definition pc_tk : Z := 0x8d7b0.
  Definition pc_dp : Z := 0x8d7fc.
  Definition pc_chain : Z := 0x8d984.
  Definition pc_join : Z := 0x8dc6c.
  Definition pc_after : Z := 0x8e4ac.

  Definition c_sd : Z := 0x9a4cc.  Definition c_ad : Z := 0xa6ab4.  Definition c_fs : Z := 0x903e4.  Definition c_da : Z := 0xa42b0.
  Definition c_vr : Z := 0x949d4.  Definition c_op : Z := 0xa3f44.  Definition c_hf : Z := 0x9c8d8.  Definition c_hl : Z := 0x9ee04.
  Definition c_hvn : Z := 0x9bf74. Definition c_hvt : Z := 0x9c3a0. Definition c_hm : Z := 0xa0420.  Definition c_ir : Z := 0x9b2bc.
  Definition c_hp : Z := 0x9f8e8.  Definition c_hff : Z := 0xa0b60. Definition c_nt : Z := 0x9a1f4.  Definition c_si : Z := 0xa014c.
  Definition c_vf : Z := 0x916a0.  Definition c_bw : Z := 0xa0394.
  Definition c_mf : Z := 0x9b4e0.  Definition c_bd : Z := 0x91de8.  Definition c_fu : Z := 0x917fc.
End LOLAddr.
Import LOLAddr.

Definition bA : sv := SAlu ALU_ADD vF (SLit 448).
Definition alA : sv := SAlu ALU_ADD vF (SLit 368).
Definition cA : sv := spm 136.
Definition lnA : sv := spm 328.
Definition txt (e : sv) : sv := SAlu ALU_ADD vBUF e.
Definition hx (r : nat) : sv := SVar (Pos.of_nat (500 + r)).
Definition hf (r : nat) : sv := SVar (Pos.of_nat (540 + r)).
Definition HNEXT : positive := 600%positive.
Definition BIG : Z := 288230376151711743.

Definition T3 : Type := ltac2:(tb__ "0|0|
S5S5SbSbA2SbA2").
Definition t3 (n : positive) : T3 := ltac2:(tb__ "0|0|
S2S5SbSbA2SbS2SbSbS12Vn;A1S12S10aVn;P1A2A1A4S12S10aVn;P2A2A1A4").
Definition t_d (t : T3) : sv := ltac2:(tb__ "0|1|
S5S5SbSbA2M0SbA2SbLt;Vt;G0SbG0SbLp;R2SbSbR2Ls0;Ld;X5x1Ls;Lp;X5x1").
Definition t_c (t : T3) : sv := ltac2:(tb__ "0|1|
S5S5SbSbA2M0SbA2SbLt;Vt;G0SbG0SbLp;R2SbSbR1Lc;Ls0;X5x1Ls;Lp;X5x1").
Definition t_k (t : T3) : sv := ltac2:(tb__ "0|1|
S5S5SbSbA2M0SbA2SbLt;Vt;G0SbG0SbLp;R2SbSbR3Ls0;Ls;X5x1Lk;Lp;X5x1").

Record vecs := VS { v_av : T3; v_avw : T3; v_avn : T3; v_avt : T3; v_avtw : T3; v_acol : T3; v_sh : T3;
                    v_mi : T3; v_fv : T3; v_mm : T3; v_sg : T3; v_li : T3; v_lc : T3; v_pi : T3;
                    v_co : T3; v_rp : T3; v_tr : T3; v_ts : T3 }.

Definition av3 (t : T3) : T3 := ltac2:(tb__ "0|0|
S2S5SbSbA2SbS2SbSbS29Vt;A1S17Sc3S2aVt;A1SeZ3A1A3A4S28Vt;A1A4").

Definition avt2 (t : T3) : T3 := ltac2:(tb__ "0|0|
S2S5SbSbA2SbS2SbSbS29Vt;A1S11Sc6S2aVt;A1SeZ1A1A3A4S28Vt;A1A4").

Definition vsP : vecs := ltac2:(tb__ "0|0|
S6eS2dP190A1S2dP193A1S2dP196A1S2dP199A1S2dP19cA1S2dP19fA1S2dP1a2A1S2dP1a5A1S2dP1a8A1S2dP1abA1S2dP1aeA1S2dP1b1A1S2dP1b4A1S2dP1b7A1S2dP1baA1S2dP1bdA1S2dP1c0A1S2S5SbSbA2SbS2SbSbS12P1c3A1SeZ0A1A4S12P1c5A1A4A12").
Definition zt : T3 := ltac2:(tb__ "0|1|
S2S5SbSbA2SbS2SbSbSeZ0A1M0G0A4G0A4").
Definition vs0 : vecs := ltac2:(tb__ "0|0|
S6eS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bA12").

Definition pI : sv := SVar 460.
Definition pERR : sv := SVar 461.  Definition pLINE : sv := SVar 462.
Definition pCN : sv := SVar 463.          Definition pHP : sv := SVar 464.
Definition pH : sv := SVar 465.
Definition xLD : sv := SVar 466. Definition xLC : sv := SVar 467. Definition xLK : sv := SVar 468.

Definition pR : sv := SVar 471. Definition pQ : sv := SVar 472. Definition pT0 : sv := SVar 473. Definition pTL : sv := SVar 474.
Definition pCH : sv := SVar 475. Definition pCP : sv := SVar 476.
Definition xCM : sv := SVar 477.       Definition xSM : sv := SVar 478.

Definition bpiece (lo hi : Z) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S13S6aSeVlo;A1SeVhi;A1Vcells;S14A5").
Definition P_allocA : sobj := ltac2:(tb__ "0|1|
S34Z0M0Z8S0S10S22G0S69A2S1S10A1A3A3").
Definition P_hdrA : sobj := ltac2:(tb__ "0|1|
S34Z8M0Z20S0S10S22G0SecA2S0S10S22Z10SeZ0A1A2S0S10S22Z18SfeA2S1S10A1A3A3A3A3").
Definition P_capsA : sobj := ltac2:(tb__ "0|4|
S34Z20M0Z60S0S10S22G0SeS81A1M1A2S0S10S22Z28G1A2S0S10S22Z30G1A2S0S10S22Z38SeSccZ2M2Z14A2A1A2S0S10S22Z40SeSccG2Z18A2A1M3A2S0S10S22Z48G3A2S0S10S22Z50G3A2S0S10S22Z58G1A2S1S10A1A3A3A3A3A3A3A3A3A3").
Definition P_stA (err line : sv) : sobj := ltac2:(tb__ "0|1|
S34Z60M0Z78S0S10Sf0G0Verr;A2S0S10S22Z68Vline;A2S0S10SefZ70SeZ1A1A2S1S10A1A3A3A3A3").
Definition VA (o : Z) (t : T3) (e : Z) : sobj := ltac2:(tb__ "0|0|
S34Vo;ScbVo;Z20A2S0S10S22Vo;S29Vt;A1A2S0S10S22ScbVo;Z8A2S2aVt;A1A2S0S10S22ScbVo;Z10A2S28Vt;A1A2S0S10S22ScbVo;Z18A2SeVe;A1A2S1S10A1A3A3A3A3A3").
Definition VdA (o : Z) (e : Z) : sobj := ltac2:(tb__ "0|0|
S2eVo;S2bVe;A3").
Definition VAd (o : Z) (t : T3) (e : Z) : sobj := ltac2:(tb__ "0|0|
S34Vo;ScbVo;Z20A2S0S10S22Vo;S29Vt;A1A2S0S10S22ScbVo;Z10A2S28Vt;A1A2S0S10S22ScbVo;Z18A2SeVe;A1A2S1S10A1A3A3A3A3").
Definition P_csA : sobj := bpiece 312 320 [].
Definition P_curA (cn hp : sv) : sobj := ltac2:(tb__ "0|1|
S34Z1e0M0Z1f0S0S10S22G0Vcn;A2S0S10SefZ1e8Vhp;A2S1S10A1A3A3A3").
Definition P_ffA : sobj := ltac2:(tb__ "0|1|
S34Z370Z3a8S0S10SefZ375SeZ0A1M0A2S0S10Sf0Z388G0A2S1S10A1A3A3A3").
Definition P_matA (cm sm : sv) : sobj := ltac2:(tb__ "0|1|
S34Z4e8M0Z518S0S10Sf0G0Vcm;A2S0S10Sf0Z4ecVsm;A2S0S10SefZ4f0SeZ0A1A2S1S10A1A3A3A3A3").
Definition builderA (err line cn hp cm sm : sv) (v : vecs) : list sobj := ltac2:(tb__ "0|3|
S0SdS8fS0SdS94S0SdS90S0SdS96Verr;Vline;A2S0SdS2eZ78S99S43Vv;A1A1Z4M0A3S0SdS2eZ98S4bVv;A1G0A3S0SdS2eZb8S49Vv;A1G0A3S0SdS2eZd8S6fS44Vv;A1A1G0A3S0SdS2eZf8S4aVv;A1G0A3S0SdS2eZ118S48Vv;A1G0A3S0SdS91S0SdS30Z140Z490A2S0SdS30Z160Z8A2S0SdS30Z180G0A2S0SdS30Z1a0Z18A2S0SdS2eZ1c0S53Vv;A1Z80M1A3S0SdS92Vcn;Vhp;A2S0SdS2eZ1f0S4fVv;A1ZcM2A3S0SdS2eZ210S4cVv;A1G0A3S0SdS2eZ230S50Vv;A1G0A3S0SdS2eZ250S52Vv;A1G0A3S0SdS2eZ270S4eVv;A1G2A3S0SdS2eZ290S4dVv;A1G0A3S0SdS2eZ2b0S51Vv;A1G2A3S0SdS66Z2d0S5cVv;A1G2A3S0SdS66Z2f0S5dVv;A1G0A3S0SdS66Z310S5eVv;A1G0A3S0SdS2eZ330S5fVv;A1Z1A3S0SdS30Z350G0A2S0SdS93S0SdS30Z3a8G0A2S0SdS30Z3c8G2A2S0SdS30Z3e8G0A2S0SdS30Z408G0A2S0SdS30Z428G2A2S0SdS30Z448G2A2S0SdS30Z468G2A2S0SdS30Z488Z38A2S0SdS30Z4a8Z30A2S0SdS30Z4c8G1A2S0SdS95Vcm;Vsm;A2S1SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition bbnds : list Z := ltac2:(tb__ "0|0|
S0S1fZ8S0S1fZ20S0S1fZ60S0S1fZ78S0S1fZ98S0S1fZb8S0S1fZd8S0S1fZf8S0S1fZ118S0S1fZ138S0S1fZ140S0S1fZ160S0S1fZ180S0S1fZ1a0S0S1fZ1c0S0S1fZ1e0S0S1fZ1f0S0S1fZ210S0S1fZ230S0S1fZ250S0S1fZ270S0S1fZ290S0S1fZ2b0S0S1fZ2d0S0S1fZ2f0S0S1fZ310S0S1fZ330S0S1fZ350S0S1fZ370S0S1fZ3a8S0S1fZ3c8S0S1fZ3e8S0S1fZ408S0S1fZ428S0S1fZ448S0S1fZ468S0S1fZ488S0S1fZ4a8S0S1fZ4c8S0S1fZ4e8S1S1fA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition fpc (lo hi : Z) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S13S12PaA1SeVlo;A1SeVhi;A1Vcells;S14A5").
Definition f5p (lo hi : Z) (cells : list cell) (d : odefault) : sobj := ltac2:(tb__ "0|0|
S13Sf1SeVlo;A1SeVhi;A1Vcells;Vd;A5").

Definition objK0 (i : nat) : sobj := ltac2:(tb__ "0|1|
S103SdVi;S18SffS10dA1A1S6bZ0M0G0S1S10A1A3A4").

Definition spill_cells : list cell := Eval vm_compute in List.filter (fun c => negb (sv_eqb (c_off c) (SLit (-488))) && negb (sv_eqb (c_off c) (SLit (-440)))) (ob_cells (objK0 19)).
Definition O_spillA : sobj := ltac2:(tb__ "0|0|
S6bScdS108A1N148SbfA3").
Definition O_lnhA (d c k : sv) : sobj := ltac2:(tb__ "0|2|
S13SbaSeZ0M0A1SeZ20A1S0S10S22G0Vd;A2S0S10S22Z8Vc;A2S0S10S22Z10M1Vk;A2S0S10S22Z18SeG1A1A2S1S10A1A3A3A3A3S14A5").
Definition O_midA : sobj := fpc (-296) (-136) [].
Definition O_cPA (p : sv) : sobj := ltac2:(tb__ "0|1|
S13S54SeZ0M0A1SeZ8A1S0S10S22G0S37Vp;A1A2S1S10A1A3S14A5").
Definition O_cEA (e : sv) : sobj := ltac2:(tb__ "0|1|
S13S54SeZ8M0A1SeZ10A1S0S10S22G0S37Ve;A1A2S1S10A1A3S14A5").
Definition save_cells : list cell := Eval vm_compute in ob_cells (objK0 20).
Definition O_savA : sobj := fpc (-120) (-16) save_cells.
Definition O_lnkS : sobj := ltac2:(tb__ "0|1|
S6bN10M0Z0S0S10S22G0S12P1cA1A2S0S10S22N8S12PbA1A2S1S10A1A3A3A3").

Definition f5hdr_cells : list cell := Eval vm_compute in ob_cells (objK0 13).
Definition O_f5hdr : sobj := f5p 0 32 f5hdr_cells DUnknown.
Definition O_f5loc (cells : list cell) : sobj := f5p 32 368 cells DUnknown.
Definition O_f5gap : sobj := f5p 416 448 [] DUnknown.
Definition O_f5rz : sobj := f5p 1752 2040 [] DUnknown.
Definition f5fl_cells : list cell := Eval vm_compute in ob_cells (objK0 16).
Definition O_f5fl : sobj := f5p 2040 2048 f5fl_cells DUnknown.
Definition O_alA : sobj := ltac2:(tb__ "0|0|
S13S69SeZ0A1SeZ30A1S104S14A5").

Definition O_arA (hd : sv) : sobj := ltac2:(tb__ "0|0|
S13SecSeZ0A1SeZ40A1S3S10S104S0S10S22Z30Vhd;A2S0S10S22Z38SeZ10000A1A2S1S10A1A3A3A3S14A5").
Definition O_dataA (t : T3) (e : Z) : sobj := ltac2:(tb__ "0|0|
S13S29Vt;A1SeZ0A1Sc1Ve;S28Vt;A1A2S1S10A1S14A5").

Definition pPOS : sv := SVar 480. Definition pLNL : sv := SVar 481.

Definition pNX : sv := SVar 490.
Definition entA (i : sv) : sv := ltac2:(tb__ "0|0|
S11Sc2S36S17Sc3SeZ10A1Vi;A3A3").
Definition O_ent (i pos len : sv) : sobj := ltac2:(tb__ "0|1|
S13S9dVi;A1SeZ0M0A1SeZ10A1S0S10S22G0Vpos;A2S0S10S22Z8Vlen;A2S1S10A1A3A3S14A5").
Definition datasA (v : vecs) : list sobj := ltac2:(tb__ "0|2|
S0SdS2cS43Vv;A1Z4M0A2S0SdS2cS4bVv;A1G0A2S0SdS2cS49Vv;A1G0A2S0SdS2cS44Vv;A1G0A2S0SdS2cS4aVv;A1G0A2S0SdS2cS48Vv;A1G0A2S0SdS2cS53Vv;A1Z80A2S0SdS2cS4fVv;A1ZcM1A2S0SdS2cS4cVv;A1G0A2S0SdS2cS50Vv;A1G0A2S0SdS2cS52Vv;A1G0A2S0SdS2cS4eVv;A1G1A2S0SdS2cS4dVv;A1G0A2S0SdS2cS51Vv;A1G1A2S0SdS2cS5cVv;A1G1A2S0SdS2cS5dVv;A1G0A2S0SdS2cS5eVv;A1G0A2S0SdS2cS5fVv;A1Z1A2S1SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Record cst := CST { k_ld : sv; k_lc : sv; k_lk : sv; k_err : sv; k_line : sv; k_cn : sv; k_hp : sv; k_cm : sv; k_sm : sv; k_v : vecs;
                    k_cp : list cell; k_ce : list cell; k_loc : list cell; k_out : list cell; k_hd : sv; k_ent : list sobj }.

Definition coreA (k : cst) : list sobj := ltac2:(tb__ "0|2|
S3SdS0SdS8eS0SdS8aS56Vk;A1S7eVk;A1S57Vk;A1A3S0SdS8cS0SdS13S54SeZ0A1SeZ8A1M0Sb2Vk;A1S14A5S0SdS13S54G0SeZ10A1Sb0Vk;A1S14A5S0SdS8dS0SdS8bS0SdSf6S0SdS87S0SdS88Sb5Vk;A1A1S0SdS83S0SdS86S1SdA1M1A3A3A3A3A3A3A3A3A3A3A3A3S3SdS9bSb3Vk;A1Sb4Vk;A1S7bVk;A1S7dVk;A1Sb1Vk;A1Sb7Vk;A1S35Vk;A1A7S3SdS0SdS89S0SdS85S0SdSf9Sb6Vk;A1S1aA2S0SdSfaS0SdSf7S0SdSf8S0SdS84S7cVk;A1A1G1A3A3A3A3A3A3A3S106A3A3A3").

Definition canonA (k : cst) : list sobj := ltac2:(tb__ "0|0|
S3SdS70Vk;A1S3SdS71S35Vk;A1A1S55Vk;A1A3A3").

Definition tv_vecs (v : vecs) : list (sv * sv) := ltac2:(tb__ "0|15|
S0S5SbSbA2M0S2SbSbS29S43Vv;A1M1A1Sc1Z4M2S28G1A1A2A4S0G0S2SbSbS29S4bVv;A1M3A1Sc1G2S28G3A1A2A4S0G0S2SbSbS29S49Vv;A1M4A1Sc1G2S28G4A1A2A4S0G0S2SbSbS29S44Vv;A1M5A1Sc1G2S28G5A1A2A4S0G0S2SbSbS29S4aVv;A1M6A1Sc1G2S28G6A1A2A4S0G0S2SbSbS29S48Vv;A1M7A1Sc1G2S28G7A1A2A4S0G0S2SbSbS29S53Vv;A1M8A1Sc1Z80S28G8A1A2A4S0G0S2SbSbS29S4fVv;A1M9A1Sc1ZcMaS28G9A1A2A4S0G0S2SbSbS29S4cVv;A1MbA1Sc1G2S28GbA1A2A4S0G0S2SbSbS29S50Vv;A1McA1Sc1G2S28GcA1A2A4S0G0S2SbSbS29S52Vv;A1MdA1Sc1G2S28GdA1A2A4S0G0S2SbSbS29S4eVv;A1MeA1Sc1GaS28GeA1A2A4S0G0S2SbSbS29S4dVv;A1MfA1Sc1G2S28GfA1A2A4S0G0S2SbSbS29S51Vv;A1M10A1Sc1GaS28G10A1A2A4S0G0S2SbSbS29S5cVv;A1M11A1Sc1GaS28G11A1A2A4S0G0S2SbSbS29S5dVv;A1M12A1Sc1G2S28G12A1A2A4S0G0S2SbSbS29S5eVv;A1M13A1Sc1G2S28G13A1A2A4S0G0S2SbSbS29S5fVv;A1M14A1Sc1Z1S28G14A1A2A4S1G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition tv_k (k : cst) : list (sv * sv) := ltac2:(tb__ "0|1|
S3S5SbSbA2M0S80S35Vk;A1A1S0G0S2SbSbS56Vk;A1Sc1Z10S57Vk;A1A2A4S0G0SedS1G0A1A3A3A3").

Definition X_loopA (k : cst) : list (sv * sv) := ltac2:(tb__ "0|2|
S3S5SbSbA2M0SfbS3G0S0G0S2SbSbS69SeZ30A1A4S0G0S2SbSbS6aSeZ518A1A4S0G0SedS1G0A1M1A3A3A3S3G0S80S35Vk;A1A1S0G0S2SbSbS56Vk;A1Sc1Z10S57Vk;A1A2A4G1A3A3A3A3").

Definition vec_factsK (t : T3) (e : Z) : list sprop := ltac2:(tb__ "0|9|
S3ScS0ScSfS29Vt;A1M0S12P1eA1M1A2S0ScSfS11Sc2G0Sc1Ve;S28Vt;A1M2A2M3A3G1A2S0ScSfG0SeS23A1A2S0ScSfG2SeS24A1M4A2S0ScSfG3G4A2S1ScA1M5A3A3A3A3A3SbS7ScA1Lx;G0S1fG5Lz;S20S0ScS16R1Z4A2G5A3Ldv;Sc4SbSbG5Lb;La;M6Lop;M7G7Sc5G6Lop;M8G8S6S21SbG5La;Lw;Lsgn;S20SbS1fG5Lk;Li;Ll;Xbx8A3").
Definition vec_factsA (t : T3) (e : Z) : list sprop := ltac2:(tb__ "0|0|
S0ScSfS2aVt;A1S28Vt;A1A2S60Vt;Ve;A2A3").
Definition av_factsA (t : T3) : list sprop := ltac2:(tb__ "0|b|
S3ScS0ScSfS17Sc3S2aVt;A1M0SeZ3A1A3S28Vt;A1M1A2S0ScSfG0SeS26A1A2S0ScSfS29Vt;A1M2S12P1eA1M3A2S0ScSfS11Sc2G2Sc1Z4M4G1A2M5A3G3A2S0ScSfG2SeS23A1A2S0ScSfG1SeS24A1M6A2S0ScSfG5G6A2S1ScA1M7A3A3A3A3A3A3A3SbS7ScA1Lx;G2S1fG7Lz;S20S0ScS16R1G4A2G7A3Ldv;Sc4SbSbG7Lb;La;M8Lop;M9G9Sc5G8Lop;MaGaS6S21SbG7La;Lw;Lsgn;S20SbS1fG7Lk;Li;Ll;Xbx8A3").
Definition vecs_factsA (v : vecs) : list sprop := ltac2:(tb__ "0|2|
S3ScS9aS43Vv;A1A1S3ScS31S4bVv;A1Z4M0A2S3ScS31S49Vv;A1G0A2S3ScS31S6fS44Vv;A1A1G0A2S3ScS31S4aVv;A1G0A2S3ScS31S48Vv;A1G0A2S3ScS31S53Vv;A1Z80A2S3ScS31S4fVv;A1ZcM1A2S3ScS31S4cVv;A1G0A2S3ScS31S50Vv;A1G0A2S3ScS31S52Vv;A1G0A2S3ScS31S4eVv;A1G1A2S3ScS31S4dVv;A1G0A2S3ScS31S51Vv;A1G1A2S3ScS60S5cVv;A1G1A2S3ScS60S5dVv;A1G0A2S3ScS60S5eVv;A1G0A2S31S5fVv;A1Z1A2A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition gMI : sv := SVar 580. Definition gFV : sv := SVar 581. Definition gMM : sv := SVar 582. Definition gSG : sv := SVar 583.
Definition gLI : sv := SVar 584. Definition gLC : sv := SVar 585. Definition gPI : sv := SVar 586.
Definition gCO : sv := SVar 587. Definition gRP : sv := SVar 588. Definition gTR : sv := SVar 589. Definition gTS : sv := SVar 590.
Definition ghost_factsLo (v : vecs) : list sprop := ltac2:(tb__ "0|0|
S0ScSfS2aS4fVv;A1A1S75A2S0ScSfS2aS4cVv;A1A1S72A2S0ScSfS2aS50Vv;A1A1S76A2S0ScSfS2aS52Vv;A1A1S78A2S0ScSfS2aS4eVv;A1A1S74A2S0ScSfS2aS4dVv;A1A1S73A2S0ScSfS2aS51Vv;A1A1S77A2S1ScA1A3A3A3A3A3A3A3").

Definition cnt_factsLo (v : vecs) : list sprop := ltac2:(tb__ "0|1|
S0ScSfS2aS4bVv;A1A1S2aS43Vv;A1A1M0A2S0ScSfS2aS48Vv;A1A1S11Sc2S17Sc3SeZ3A1G0A3SeZ2A1A3A2S0ScSfS2aS4aVv;A1A1S2aS44Vv;A1A1A2S1ScA1A3A3A3").

Definition rate_factsLo (x : sv) (v : vecs) : list sprop := ltac2:(tb__ "0|1|
S0ScSfS2aS43Vv;A1A1Vx;A2S0ScSfS2aS49Vv;A1A1Sc1Z3Vx;A2M0A2S0ScSfS2aS44Vv;A1A1Vx;A2S0ScSfS2aS53Vv;A1A1Vx;A2S0ScSfS75G0A2S0ScSfS72Vx;A2S0ScSfS76Vx;A2S0ScSfS78Vx;A2S0ScSfS74Vx;A2S0ScSfS73Vx;A2S0ScSfS77Vx;A2S0ScSfSa0Vx;A2S0ScSfSa1G0A2S0ScSfSa3G0A2S0ScSfSa4Sc1Z25Vx;A2A2S1ScA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition lines_factsA (d c k : sv) : list sprop := ltac2:(tb__ "0|7|
S3ScS0ScSfVc;Vk;A2S0ScSfVd;S12P1eA1M0A2S0ScSfS11Sc2Vd;Sc1Z10Vk;A2M1A3G0A2S0ScSfVd;SeS23A1A2S0ScSfVk;SeS24A1M2A2S0ScSfG1G2A2S0ScSfVc;Sf2A2S1ScA1M3A3A3A3A3A3A3A3SbS7ScA1Ld;Vd;S1fG3Lz;S20S0ScS16R1Z4A2G3A3Ldv;Sc4SbSbG3Lb;La;M4Lop;M5G5Sc5G4Lop;M6G6S6S21SbG3La;Lw;Lsgn;S20SbS1fG3Lk0;Li;Ll;Xbx8A3").
Definition misc_factsA (cn hp hd : sv) : list sprop := ltac2:(tb__ "0|0|
S0ScSfVhp;SeZ1A1A2S0ScSfVcn;SeS23A1A2S0ScSfVhd;SeZ7fffff800000A1A2S1ScA1A3A3A3").

Definition arena_factsLo (hd : sv) : list sprop := ltac2:(tb__ "0|1|
S0ScS16SeeZ4A2S0ScSfSeZ1000A1SecA2S0ScSfS11Sc2SecSeZ40A1A3S12P1eA1M0A2S0ScSfSecSeS23A1A2S0ScSfVhd;G0A2S1ScA1A3A3A3A3A3").

Definition frame_factsLo : list sprop := ltac2:(tb__ "0|2|
S3ScS0ScS16P6eM0Z5A2S0ScS1dS19Sc9Sf1SeZ0A1A3A1S0ScSfSeS112A1M1Sf1A2S0ScSfG1Sf4A2S0ScSfS11Sc2Sf4SeZ1A1A3SeZ7fffff800000A1A2S1ScA1A3A3A3A3A3S111Sf3G0Z800A3A3").

Definition gran_factsLo : list sprop := FE 303%positive vARn.
Definition loop_factsA (k : cst) : list sprop := ltac2:(tb__ "0|2|
S3ScSc0S35Vk;A1M0A1S3ScSa5G0A1S3ScS9cG0A1S3ScSb9S56Vk;A1S7eVk;A1S57Vk;A1A3S3ScSbdS7bVk;A1S7dVk;A1S7cVk;A1M1A3S3ScS98G1A1S3ScS9fS3ScSa6SfdA3A3A3A3A3A3A3A3").

Definition gS : sv := ltac2:(tb__ "0|0|
S11Sc2S12Sf3A1SeS105A1A3").
Definition lregsA (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|3|
S110S101S4SbSa8S102U0U20A2A4S3S5S4SbA2M0S0G0S2S4SbU2S25S108A1M1A4S0G0S2S4SbU3S12P17A1A4S0G0S2S4SbU4S12P18A1A4S0G0S2S4SbU8S12PaA1A4S0G0S2S4SbU9G1A4S0G0S2S4SbU5S6aA4S0G0S2S4SbU6SeZ23A1A4S0G0S2S4SbU7SeZ2A1A4S0G0S2S4SbU1cSeZ1A1M2A4S0G0S2S4SbU10G2A4S0G0S2S4SbU11SeZ7A1A4S0G0S2S4SbU12SeZ20A1A4S0G0S2S4SbU17SeZ9A1A4S0G0S2S4SbU13Sa2A4S0G0S2S4SbU14Sf5A4S0G0S2S4SbU15Sf1A4S0G0S2S4SbU19S11Sc8Sf5SeZffffffffffffffffA1A3A4S0G0S2S4SbU1aSeS105A1A4S1G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").

Definition fkeepA (r : nat) : bool := match r with 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition lfregsA : list sv := ltac2:(tb__ "0|1|
S101S4SbS4S6SbL_;M0S113R1U8A2SeZffffffff3f800000A1G0S9eR1A1S12S10bS10cU3cR1A2A1A1Sa7R1A1X6x2X6x2Lr;S102U0U20A2A4").

Definition kL (v : vecs) : cst := ltac2:(tb__ "0|1|
S39S36S2fS3fSeZ0A1S27S3aS3cS3eS40Vv;S1S10A1M0G0G0G0S3bS1SdA1A10").
Definition LSAc (pc : Z) (regs : list (nat * sv)) (k : cst) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S107S1eVpc;SbcVregs;A1Sb8S1bS8SbA1S70Vk;A1S3ScVfacts;SbbVk;A1A3S82S9A9S97Vk;A1A2").
Definition add_datas (A : axst) (v : vecs) : axst := ltac2:(tb__ "0|1|
S100VA;S109SffVA;A1M0S3SdS18G0A1S71Vv;A1A3A2A2").
Definition add_ents (A : axst) (es : list sobj) : axst := ltac2:(tb__ "0|1|
S100VA;S109SffVA;A1M0S3SdS18G0A1Ves;A3A2A2").
Definition LSA (pc : Z) (regs : list (nat * sv)) (k : cst) (facts : list sprop) : axst := ltac2:(tb__ "0|1|
S68S67S64Vpc;Vregs;Vk;S3ScVfacts;S5bS5aS35Vk;A1M0A2A3A4G0A2S55Vk;A1A2").

Definition pE0 : sv := SAlu ALU_ADD pPOS pLNL.
Definition LSAx (pc : Z) (regs : list (nat * sv)) (k : cst) (facts : list sprop) : axst := ltac2:(tb__ "0|1|
S68S67S64Vpc;Vregs;Vk;S3ScVfacts;S5bS11Sc2S7fSeZ1A1A3S35Vk;A1M0A2A3A4G0A2S55Vk;A1A2").

Definition rate2 (k : cst) : list sprop := ltac2:(tb__ "0|1|
S3ScS5bS5aS35Vk;A1M0A2S5bS11Sc2S7fSeZ1A1A3G0A2A3").
Definition LSAb (pc : Z) (regs : list (nat * sv)) (k : cst) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S68S67S64Vpc;Vregs;Vk;S3ScVfacts;SbeVk;A1A3A4S35Vk;A1A2S55Vk;A1A2").

Definition nx_facts : list sprop := ltac2:(tb__ "0|0|
S0ScSfS5aS11Sc2Sf2SeZ1A1A3A2S1ScA1A3").
Definition K_loop : axst := ltac2:(tb__ "0|1|
S62SceS0S5S4SbA2M0S2S4SbU16S27A4S1G0A1A3S79S38A1S0ScSfS27S2fA2S58A3A4").

Definition X_bodyN : axst := ltac2:(tb__ "0|1|
S62ScfS0S5S4SbA2M0S2S4SbU16S27A4S1G0A1A3S79S38A1S0ScS15S27S2fA2S58A3A4").

Definition kB : cst := ltac2:(tb__ "0|1|
S39S36S2fS3fSeZ0A1S27S3aS3cS3eS40S38S1S10A1M0G0G0G0S3bS0SdS45S27S32S33A3S1SdA1A3A10").
Definition ent_facts : list sprop := ltac2:(tb__ "0|1|
S3ScS0ScSfS11Sc2S32S33A3Sf2A2S0ScSfS32SeS10eA1M0A2S0ScSfS33G0A2S0ScSfS5aS32A2S0ScSfSeZ1000A1S36A2S1ScA1A3A3A3A3A3S58A3").
Definition K_body : axst := ltac2:(tb__ "0|1|
S63ScfS0S5S4SbA2M0S2S4SbU16S27A4S1G0A1A3SabS0ScS15S27S2fA2S41A3A4").

Definition pE : sv := SAlu ALU_ADD pPOS pLNL.
Definition txtE : sv := ltac2:(tb__ "0|0|
S11Sc2S33S37S32A1A3").

Definition iregsA (l : list (nat * sv)) : list (nat * sv) := ltac2:(tb__ "0|1|
S3S5S4SbA2M0S0G0S2S4SbU16S11Sc2S27SeZ1A1A3A4S1G0A1A3Vl;A3").
Definition kI (cp : list cell) : cst := ltac2:(tb__ "0|1|
S39S36S2fS3fSeZ0A1S11Sc2S27SeZ1A1A3S3aS3cS3eS40S38Vcp;S0S10S22Z8S6cA2S1S10A1M0A3G0G0S3bS0SdS45S27S32S33A3S1SdA1A3A10").
Definition ifactsA : list sprop := ltac2:(tb__ "0|0|
S3ScS0ScS15S27S2fA2S0ScSfS33SeSccZ2Z18A2A1A2S1ScA1A3A3S41A3").
Definition LIA (pc : Z) (regs : list (nat * sv)) (cp : list cell) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S63Vpc;SaaVregs;A1SacVcp;A1S3ScVfacts;Sa9A3A4").

Definition kX : cst := ltac2:(tb__ "0|1|
S39S36S2fS3fSeZ0A1S11Sc2S27SeZ1A1A3S3aS3cS3eS40S38S1S10A1M0G0G0G0S3bS0SdS45S27S32S33A3S1SdA1A3A10").
Definition X_latch : axst := ltac2:(tb__ "0|1|
S65SceS0S5S4SbA2M0S2S4SbU16S11Sc2S27SeZ1A1A3A4S1G0A1A3S7aS0ScS15S27S2fA2S41A3A4").

Definition K_l2l : axst := ltac2:(tb__ "0|1|
S63Sd1S0S5S4SbA2M0S2S4SbU16S11Sc2S27SeZ1A1A3A4S1G0A1A3S7aS0ScS15S27S2fA2S41A3A4").

Definition kX7 : cst := ltac2:(tb__ "0|1|
S39S36S2fS3fSeZ7A1S11Sc2S27SeZ1A1A3S3aS3cS3eS40S38S1S10A1M0G0G0G0S3bS0SdS45S27S32S33A3S1SdA1A3A10").
Definition X_latch7 : axst := ltac2:(tb__ "0|1|
S65SceS0S5S4SbA2M0S2S4SbU16S11Sc2S27SeZ1A1A3A4S1G0A1A3SaeS0ScS15S27S2fA2S41A3A4").

Definition NZ32e (e : sv) : sprop := ltac2:(tb__ "0|0|
S19ScaS1cSaQ20Ve;A3SeZ0A1A3").
Definition kXE : cst := ltac2:(tb__ "0|1|
S39S36S2fS3fS59S11Sc2S27SeZ1A1A3S3aS3cS3eS40S38S1S10A1M0G0G0G0S3bS0SdS45S27S32S33A3S1SdA1A3A10").
Definition X_latchE : axst := ltac2:(tb__ "0|1|
S65SceS0S5S4SbA2M0S2S4SbU16S11Sc2S27SeZ1A1A3A4S1G0A1A3SafS0ScS15S27S2fA2S0ScS6dS59A1S41A3A3A4").
Definition kLE : cst := ltac2:(tb__ "0|1|
S39S36S2fS3fS59S27S3aS3cS3eS40S38S1S10A1M0G0G0G0S3bS1SdA1A10").
Definition K_loopE : axst := ltac2:(tb__ "0|1|
S62SceS0S5S4SbA2M0S2S4SbU16S27A4S1G0A1A3SadS0ScSfS27S2fA2S0ScS6dS59A1S58A3A3A4").

Definition K_ws : axst := ltac2:(tb__ "0|2|
S61Sd3S0S5S4SbA2M0S2S4SbUaS47A4S0G0S2S4SbUcS37S11Sc7S46S47A3A1M1A4S0G0S2S4SbU18G1A4S0G0S2S4SbUbS6cA4S1G0A1A3A3A3A3S1S10A1S0ScSfSeZ1A1S47A2S0ScSfS47S46A2S0ScSfS47S33A2S1ScA1A3A3A3A4").

Definition K_tk : axst := ltac2:(tb__ "0|2|
S61Sd2S0S5S4SbA2M0S2S4SbUaS37S42A1M1A4S0G0S2S4SbUcG1A4S0G0S2S4SbU18S37S3dA1A4S0G0S2S4SbUbS6cA4S1G0A1A3A3A3A3S0S10S22Z0G1A2S1S10A1A3S0ScSfS3dS42A2S0ScS15S42S46A2S0ScSfS32S3dA2S1ScA1A3A3A3A4").

Definition K_dp : axst := ltac2:(tb__ "0|1|
S61Sd0S0S5S4SbA2M0S2S4SbU18S37S3dA1A4S1G0A1A3S0S10S22Z0S37S42A1A2S1S10A1A3S0ScS15S3dS46A2S0ScSfS42S46A2S0ScSfS3dS42A2S0ScSfS32S3dA2S1ScA1A3A3A3A3A4").

Definition cps_loop : list Z := ltac2:(tb__ "0|0|
S3S1fS0S1fSd3S0S1fSd2S0S1fSd0S0S1fSceS0S1fScfS0S1fSd1S0S1fSeaS0S1fSe9S0S1fSebS0S1fSe5S0S1fSd4S0S1fSd8S0S1fSd7S0S1fSe8S0S1fSe4S0S1fSdaS0S1fSdcS0S1fSdfS0S1fSe0S0S1fSddS0S1fSe1S0S1fSdeS0S1fSdbS0S1fSe3S0S1fSe6S0S1fSe2S0S1fSd5S0S1fSd9S0S1fSe7S0S1fSd6S0S1fS10fS1S1fA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3SfcA3").

Goal length (builderA pERR pLINE pCN pHP xCM xSM vsP) = 41%nat /\ length spill_cells = 33%nat /\ length save_cells = 12%nat /\ length f5hdr_cells = 3%nat
  /\ forallb (fun A => swf (ax_S A) && axwf A) [K_loop; X_bodyN; K_body; X_latch; K_l2l; K_ws; K_tk; K_dp] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
