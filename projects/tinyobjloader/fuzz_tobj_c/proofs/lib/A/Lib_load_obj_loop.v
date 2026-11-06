(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "nat"; "app"; "prod"; "bool"; "list"; "None"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "cell"; "SPUle"; "SAlu"; "SVar"; "mkObj"; "DUnknown"; "SPUlt"; "SPAlign"; "SMd"; "ss_objs"; "SPBranch"; "DZero"; "FcsrFrm0"; "SExt"; "SPNot"; "mkSS"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve_darr"; "c8"; "two47"; "B32"; "spm"; "two40"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pI"; "t_k"; "t_d"; "t_c"; "zt"; "O_dataA"; "t3"; "VA"; "xLC"; "VdA"; "vec_factsA"; "pLNL"; "pPOS"; "txt"; "bpiece"; "k_v"; "vsP"; "xLD"; "CST"; "pCN"; "pE"; "pH"; "pHP"; "pT0"; "xCM"; "xLK"; "xSM"; "ent_facts"; "pQ"; "v_av"; "v_avt"; "O_ent"; "pR"; "v_acol"; "v_avn"; "v_avtw"; "v_avw"; "v_fv"; "v_lc"; "v_li"; "v_mi"; "v_mm"; "v_pi"; "v_sg"; "v_sh"; "bA"; "cA"; "k_ent"; "k_ld"; "k_lk"; "nx_facts"; "pERR"; "pNX"; "rate_factsLo"; "v_co"; "v_rp"; "v_tr"; "v_ts"; "vec_factsK"; "LIA"; "LSA"; "LSAb"; "LSAc"; "LSAx"; "VAd"; "add_datas"; "add_ents"; "alA"; "entA"; "fpc"; "hx"; "NZ32e"; "VS"; "avt2"; "coreA"; "datasA"; "gFV"; "gLC"; "gLI"; "gMI"; "gMM"; "gPI"; "gSG"; "kL"; "kX"; "k_cn"; "k_hd"; "k_hp"; "k_lc"; "pE0"; "tv_vecs"; "BIG"; "HNEXT"; "O_alA"; "O_arA"; "O_f5fl"; "O_f5gap"; "O_f5hdr"; "O_f5loc"; "O_f5rz"; "O_lnhA"; "O_lnkS"; "O_midA"; "O_savA"; "O_spillA"; "P_allocA"; "P_capsA"; "P_csA"; "P_curA"; "P_ffA"; "P_hdrA"; "P_matA"; "P_stA"; "X_loopA"; "arena_factsLo"; "av3"; "av_factsA"; "builderA"; "cnt_factsLo"; "fkeepA"; "frame_factsLo"; "gCO"; "gRP"; "gS"; "gTR"; "gTS"; "ghost_factsLo"; "gran_factsLo"; "hf"; "ifactsA"; "iregsA"; "kB"; "kI"; "kLE"; "kX7"; "kXE"; "k_ce"; "k_cm"; "k_cp"; "k_err"; "k_line"; "k_loc"; "k_out"; "k_sm"; "lfregsA"; "lines_factsA"; "lnA"; "loop_factsA"; "lregsA"; "misc_factsA"; "rate2"; "spill_cells"; "vecs_factsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "aluop"; "mulop"; "ALU_SLL"; "ALU_SUB"; "BC_EQ"; "BC_NE"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "vF"; "vCFGp"; "vLEN"; "g5"; "vFL"; "O_Dlo"; "O_cfg"; "O_lnk"; "O_out"; "O_txtL"; "X_lo"; "cps_pro"; "lo_facts"; "vBUF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop.LOLAddr"; "pc_latch"; "pc_body"; "pc_dp"; "pc_l2l"; "pc_tk"; "pc_ws"; "c_ad"; "c_bd"; "c_da"; "c_fs"; "c_fu"; "c_hf"; "c_hff"; "c_hl"; "c_hm"; "c_hp"; "c_hvn"; "c_hvt"; "c_ir"; "c_mf"; "c_nt"; "c_op"; "c_sd"; "c_si"; "c_vr"; "pc_after"; "pc_errx"; "pc_join"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "vARn"; "blkAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "SHB"; "A_globals"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "c1"; "c4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "FE"; "ax_setS"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface"; "al48_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs.LOAddr"; "FR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@Stdlib.PArith.BinPos.Pos"; "add"; "of_nat"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2"; "X_body1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "two26"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve_darr.RA.ReallocAddr"; "free_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "frame_factsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require DrvGlueC ObjEmptyA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_vec_reserve_darr Lib_build_line_index.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr VRAddr RA.ReallocAddr VRDAddr LOAddr.

Module LOLAddr.
  Definition pc_latch : Z := 0x8d450.
  Definition pc_body : Z := 0x8d45c.
  Definition pc_errx : Z := 0x8e6bc.
  Definition pc_l2l : Z := 0x8d44c.
  Definition pc_ws : Z := 0x8d4f4.
  Definition pc_tk : Z := 0x8d530.
  Definition pc_dp : Z := 0x8d56c.
  Definition pc_chain : Z := 0x8d6d4.
  Definition pc_join : Z := 0x8e028.
  Definition pc_after : Z := 0x8e69c.

  Definition c_sd : Z := 0x9bf30.  Definition c_ad : Z := 0xa8000.  Definition c_fs : Z := 0x8f45c.  Definition c_da : Z := 0xa6088.
  Definition c_vr : Z := 0x9311c.  Definition c_op : Z := 0xa5d68.  Definition c_hf : Z := 0x9e888.  Definition c_hl : Z := 0xa07f0.
  Definition c_hvn : Z := 0x9e048. Definition c_hvt : Z := 0x9e3e4. Definition c_hm : Z := 0xa1a3c.  Definition c_ir : Z := 0x9cff8.
  Definition c_hp : Z := 0xa1190.  Definition c_hff : Z := 0xa2314. Definition c_nt : Z := 0x9bdb4.  Definition c_si : Z := 0xa1840.
  Definition c_mf : Z := 0x9d3bc.  Definition c_bd : Z := 0x90ef0.  Definition c_fu : Z := 0x90850.
End LOLAddr.
Import LOLAddr.

Definition bA : sv := SAlu ALU_ADD vF (SLit 544).
Definition alA : sv := SAlu ALU_ADD vF (SLit 464).
Definition cA : sv := spm 160.
Definition lnA : sv := spm 216.
Definition txt (e : sv) : sv := SAlu ALU_ADD vBUF e.
Definition hx (r : nat) : sv := SVar (Pos.of_nat (500 + r)).
Definition hf (r : nat) : sv := SVar (Pos.of_nat (540 + r)).
Definition HNEXT : positive := 600%positive.
Definition BIG : Z := 288230376151711743.

Definition T3 : Type := ltac2:(tb__ "0|0|
S5S5SbSbA2SbA2").
Definition t3 (n : positive) : T3 := ltac2:(tb__ "0|0|
S1S5SbSbA2SbS1SbSbS12Vn;A1S12S106Vn;P1A2A1A4S12S106Vn;P2A2A1A4").
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
S1S5SbSbA2SbS1SbSbS29Vt;A1S17Sc2S2aVt;A1SeZ3A1A3A4S28Vt;A1A4").

Definition avt2 (t : T3) : T3 := ltac2:(tb__ "0|0|
S1S5SbSbA2SbS1SbSbS29Vt;A1S11Sc5S2aVt;A1SeZ1A1A3A4S28Vt;A1A4").

Definition vsP : vecs := ltac2:(tb__ "0|0|
S6fS2dP190A1S2dP193A1S2dP196A1S2dP199A1S2dP19cA1S2dP19fA1S2dP1a2A1S2dP1a5A1S2dP1a8A1S2dP1abA1S2dP1aeA1S2dP1b1A1S2dP1b4A1S2dP1b7A1S2dP1baA1S2dP1bdA1S2dP1c0A1S1S5SbSbA2SbS1SbSbS12P1c3A1SeZ0A1A4S12P1c5A1A4A12").
Definition zt : T3 := ltac2:(tb__ "0|1|
S1S5SbSbA2SbS1SbSbSeZ0A1M0G0A4G0A4").
Definition vs0 : vecs := ltac2:(tb__ "0|0|
S6fS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bS2bA12").

Definition pI : sv := SVar 460.
Definition pERR : sv := SVar 461.  Definition pLINE : sv := SVar 462.
Definition pCN : sv := SVar 463.          Definition pHP : sv := SVar 464.
Definition pH : sv := SVar 465.
Definition xLD : sv := SVar 466. Definition xLC : sv := SVar 467. Definition xLK : sv := SVar 468.

Definition pR : sv := SVar 471. Definition pQ : sv := SVar 472. Definition pT0 : sv := SVar 473. Definition pTL : sv := SVar 474.
Definition pCH : sv := SVar 475. Definition pCP : sv := SVar 476.
Definition xCM : sv := SVar 477.       Definition xSM : sv := SVar 478.

Definition bpiece (lo hi : Z) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S13S54SeVlo;A1SeVhi;A1Vcells;S14A5").
Definition P_allocA : sobj := ltac2:(tb__ "0|1|
S35Z0M0Z8S0SfS22G0S6aA2S2SfA1A3A3").
Definition P_hdrA : sobj := ltac2:(tb__ "0|1|
S35Z8M0Z20S0SfS22G0Sf6A2S0SfS22Z10SeZ0A1A2S0SfS22Z18ScdA2S2SfA1A3A3A3A3").
Definition P_capsA : sobj := ltac2:(tb__ "0|4|
S35Z20M0Z60S0SfS22G0SeS82A1M1A2S0SfS22Z28G1A2S0SfS22Z30G1A2S0SfS22Z38SeScaZ2M2Z14A2A1A2S0SfS22Z40SeScaG2Z18A2A1M3A2S0SfS22Z48G3A2S0SfS22Z50G3A2S0SfS22Z58G1A2S2SfA1A3A3A3A3A3A3A3A3A3").
Definition P_stA (err line : sv) : sobj := ltac2:(tb__ "0|1|
S35Z60M0Z78S0SfSfcG0Verr;A2S0SfS22Z68Vline;A2S0SfSfbZ70SeZ1A1A2S2SfA1A3A3A3A3").
Definition VA (o : Z) (t : T3) (e : Z) : sobj := ltac2:(tb__ "0|0|
S35Vo;Sc9Vo;Z20A2S0SfS22Vo;S29Vt;A1A2S0SfS22Sc9Vo;Z8A2S2aVt;A1A2S0SfS22Sc9Vo;Z10A2S28Vt;A1A2S0SfS22Sc9Vo;Z18A2SeVe;A1A2S2SfA1A3A3A3A3A3").
Definition VdA (o : Z) (e : Z) : sobj := ltac2:(tb__ "0|0|
S2eVo;S2bVe;A3").
Definition VAd (o : Z) (t : T3) (e : Z) : sobj := ltac2:(tb__ "0|0|
S35Vo;Sc9Vo;Z20A2S0SfS22Vo;S29Vt;A1A2S0SfS22Sc9Vo;Z10A2S28Vt;A1A2S0SfS22Sc9Vo;Z18A2SeVe;A1A2S2SfA1A3A3A3A3").
Definition P_csA : sobj := bpiece 312 320 [].
Definition P_curA (cn hp : sv) : sobj := ltac2:(tb__ "0|1|
S35Z1e0M0Z1f0S0SfS22G0Vcn;A2S0SfSfbZ1e8Vhp;A2S2SfA1A3A3A3").
Definition P_ffA : sobj := ltac2:(tb__ "0|1|
S35Z370Z3a8S0SfSfbZ375SeZ0A1M0A2S0SfSfcZ388G0A2S2SfA1A3A3A3").
Definition P_matA (cm sm : sv) : sobj := ltac2:(tb__ "0|1|
S35Z4e8M0Z518S0SfSfcG0Vcm;A2S0SfSfcZ4ecVsm;A2S0SfSfbZ4f0SeZ0A1A2S2SfA1A3A3A3A3").
Definition builderA (err line cn hp cm sm : sv) (v : vecs) : list sobj := ltac2:(tb__ "0|3|
S0SdS90S0SdS95S0SdS91S0SdS97Verr;Vline;A2S0SdS2eZ78S9aS44Vv;A1A1Z4M0A3S0SdS2eZ98S4bVv;A1G0A3S0SdS2eZb8S49Vv;A1G0A3S0SdS2eZd8S70S45Vv;A1A1G0A3S0SdS2eZf8S4aVv;A1G0A3S0SdS2eZ118S48Vv;A1G0A3S0SdS92S0SdS30Z140Z490A2S0SdS30Z160Z8A2S0SdS30Z180G0A2S0SdS30Z1a0Z18A2S0SdS2eZ1c0S53Vv;A1Z80M1A3S0SdS93Vcn;Vhp;A2S0SdS2eZ1f0S4fVv;A1ZcM2A3S0SdS2eZ210S4cVv;A1G0A3S0SdS2eZ230S50Vv;A1G0A3S0SdS2eZ250S52Vv;A1G0A3S0SdS2eZ270S4eVv;A1G2A3S0SdS2eZ290S4dVv;A1G0A3S0SdS2eZ2b0S51Vv;A1G2A3S0SdS67Z2d0S5dVv;A1G2A3S0SdS67Z2f0S5eVv;A1G0A3S0SdS67Z310S5fVv;A1G0A3S0SdS2eZ330S60Vv;A1Z1A3S0SdS30Z350G0A2S0SdS94S0SdS30Z3a8G0A2S0SdS30Z3c8G2A2S0SdS30Z3e8G0A2S0SdS30Z408G0A2S0SdS30Z428G2A2S0SdS30Z448G2A2S0SdS30Z468G2A2S0SdS30Z488Z38A2S0SdS30Z4a8Z30A2S0SdS30Z4c8G1A2S0SdS96Vcm;Vsm;A2S2SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition bbnds : list Z := ltac2:(tb__ "0|0|
S0S1fZ8S0S1fZ20S0S1fZ60S0S1fZ78S0S1fZ98S0S1fZb8S0S1fZd8S0S1fZf8S0S1fZ118S0S1fZ138S0S1fZ140S0S1fZ160S0S1fZ180S0S1fZ1a0S0S1fZ1c0S0S1fZ1e0S0S1fZ1f0S0S1fZ210S0S1fZ230S0S1fZ250S0S1fZ270S0S1fZ290S0S1fZ2b0S0S1fZ2d0S0S1fZ2f0S0S1fZ310S0S1fZ330S0S1fZ350S0S1fZ370S0S1fZ3a8S0S1fZ3c8S0S1fZ3e8S0S1fZ408S0S1fZ428S0S1fZ448S0S1fZ468S0S1fZ488S0S1fZ4a8S0S1fZ4c8S0S1fZ4e8S2S1fA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition fpc (lo hi : Z) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S13S12PaA1SeVlo;A1SeVhi;A1Vcells;S14A5").
Definition f5p (lo hi : Z) (cells : list cell) (d : odefault) : sobj := ltac2:(tb__ "0|0|
S13SccSeVlo;A1SeVhi;A1Vcells;Vd;A5").

Definition objK0 (i : nat) : sobj := ltac2:(tb__ "0|1|
S102SdVi;S18SfdS109A1A1S6cZ0M0G0S2SfA1A3A4").

Definition spill_cells : list cell := Eval vm_compute in List.filter (fun c => negb (sv_eqb (c_off c) (SLit (-344)))) (ob_cells (objK0 18)).
Definition O_spillA : sobj := ltac2:(tb__ "0|0|
S6cScbS104A1Nd8SbeA3").
Definition O_lnhA (d c k : sv) : sobj := ltac2:(tb__ "0|2|
S13Sb9SeZ0M0A1SeZ20A1S0SfS22G0Vd;A2S0SfS22Z8Vc;A2S0SfS22Z10M1Vk;A2S0SfS22Z18SeG1A1A2S2SfA1A3A3A3A3S14A5").
Definition O_midA : sobj := fpc (-184) (-160) [].
Definition O_cPA (p : sv) : sobj := ltac2:(tb__ "0|1|
S13S55SeZ0M0A1SeZ8A1S0SfS22G0S34Vp;A1A2S2SfA1A3S14A5").
Definition O_cEA (e : sv) : sobj := ltac2:(tb__ "0|1|
S13S55SeZ8M0A1SeZ10A1S0SfS22G0S34Ve;A1A2S2SfA1A3S14A5").
Definition save_cells : list cell := Eval vm_compute in ob_cells (objK0 19).
Definition O_savA : sobj := fpc (-144) (-16) save_cells.
Definition O_lnkS : sobj := ltac2:(tb__ "0|1|
S6cN10M0Z0S0SfS22G0S12P1cA1A2S0SfS22N8S12PbA1A2S2SfA1A3A3A3").

Definition f5hdr_cells : list cell := Eval vm_compute in ob_cells (objK0 11).
Definition O_f5hdr : sobj := f5p 0 32 f5hdr_cells DUnknown.
Definition O_f5loc (cells : list cell) : sobj := f5p 32 464 cells DUnknown.
Definition O_f5gap : sobj := f5p 512 544 [] DUnknown.
Definition O_f5rz : sobj := f5p 1848 2040 [] DUnknown.
Definition f5fl_cells : list cell := Eval vm_compute in ob_cells (objK0 14).
Definition O_f5fl : sobj := f5p 2040 2048 f5fl_cells DUnknown.
Definition O_alA : sobj := ltac2:(tb__ "0|0|
S13S6aSeZ0A1SeZ30A1S103S14A5").

Definition O_arA (hd : sv) : sobj := ltac2:(tb__ "0|0|
S13Sf6SeZ0A1SeZ40A1S4SfS103S0SfS22Z30Vhd;A2S0SfS22Z38SeZ10000A1A2S2SfA1A3A3A3S14A5").
Definition O_dataA (t : T3) (e : Z) : sobj := ltac2:(tb__ "0|0|
S13S29Vt;A1SeZ0A1Sc0Ve;S28Vt;A1A2S2SfA1S14A5").

Definition pPOS : sv := SVar 480. Definition pLNL : sv := SVar 481.

Definition pNX : sv := SVar 490.
Definition entA (i : sv) : sv := ltac2:(tb__ "0|0|
S11Sc1S38S17Sc2SeZ10A1Vi;A3A3").
Definition O_ent (i pos len : sv) : sobj := ltac2:(tb__ "0|1|
S13S6bVi;A1SeZ0M0A1SeZ10A1S0SfS22G0Vpos;A2S0SfS22Z8Vlen;A2S2SfA1A3A3S14A5").
Definition datasA (v : vecs) : list sobj := ltac2:(tb__ "0|2|
S0SdS2cS44Vv;A1Z4M0A2S0SdS2cS4bVv;A1G0A2S0SdS2cS49Vv;A1G0A2S0SdS2cS45Vv;A1G0A2S0SdS2cS4aVv;A1G0A2S0SdS2cS48Vv;A1G0A2S0SdS2cS53Vv;A1Z80A2S0SdS2cS4fVv;A1ZcM1A2S0SdS2cS4cVv;A1G0A2S0SdS2cS50Vv;A1G0A2S0SdS2cS52Vv;A1G0A2S0SdS2cS4eVv;A1G1A2S0SdS2cS4dVv;A1G0A2S0SdS2cS51Vv;A1G1A2S0SdS2cS5dVv;A1G1A2S0SdS2cS5eVv;A1G0A2S0SdS2cS5fVv;A1G0A2S0SdS2cS60Vv;A1Z1A2S2SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Record cst := CST { k_ld : sv; k_lc : sv; k_lk : sv; k_err : sv; k_line : sv; k_cn : sv; k_hp : sv; k_cm : sv; k_sm : sv; k_v : vecs;
                    k_cp : list cell; k_ce : list cell; k_loc : list cell; k_out : list cell; k_hd : sv; k_ent : list sobj }.

Definition coreA (k : cst) : list sobj := ltac2:(tb__ "0|2|
S4SdS0SdS8fS0SdS8bS57Vk;A1S7fVk;A1S58Vk;A1A3S0SdS8dS0SdS13S55SeZ0A1SeZ8A1M0Sb1Vk;A1S14A5S0SdS13S55G0SeZ10A1SafVk;A1S14A5S0SdS8eS0SdS8cS0SdSd1S0SdS88S0SdS89Sb4Vk;A1A1S0SdS84S0SdS87S2SdA1M1A3A3A3A3A3A3A3A3A3A3A3A3S4SdS9cSb2Vk;A1Sb3Vk;A1S7cVk;A1S7eVk;A1Sb0Vk;A1Sb6Vk;A1S36Vk;A1A7S4SdS0SdS8aS0SdS86S0SdSd4Sb5Vk;A1S1aA2S0SdSd5S0SdSd2S0SdSd3S0SdS85S7dVk;A1A1G1A3A3A3A3A3A3A3Sf9A3A3A3").

Definition canonA (k : cst) : list sobj := ltac2:(tb__ "0|0|
S4SdS71Vk;A1S4SdS72S36Vk;A1A1S56Vk;A1A3A3").

Definition tv_vecs (v : vecs) : list (sv * sv) := ltac2:(tb__ "0|15|
S0S5SbSbA2M0S1SbSbS29S44Vv;A1M1A1Sc0Z4M2S28G1A1A2A4S0G0S1SbSbS29S4bVv;A1M3A1Sc0G2S28G3A1A2A4S0G0S1SbSbS29S49Vv;A1M4A1Sc0G2S28G4A1A2A4S0G0S1SbSbS29S45Vv;A1M5A1Sc0G2S28G5A1A2A4S0G0S1SbSbS29S4aVv;A1M6A1Sc0G2S28G6A1A2A4S0G0S1SbSbS29S48Vv;A1M7A1Sc0G2S28G7A1A2A4S0G0S1SbSbS29S53Vv;A1M8A1Sc0Z80S28G8A1A2A4S0G0S1SbSbS29S4fVv;A1M9A1Sc0ZcMaS28G9A1A2A4S0G0S1SbSbS29S4cVv;A1MbA1Sc0G2S28GbA1A2A4S0G0S1SbSbS29S50Vv;A1McA1Sc0G2S28GcA1A2A4S0G0S1SbSbS29S52Vv;A1MdA1Sc0G2S28GdA1A2A4S0G0S1SbSbS29S4eVv;A1MeA1Sc0GaS28GeA1A2A4S0G0S1SbSbS29S4dVv;A1MfA1Sc0G2S28GfA1A2A4S0G0S1SbSbS29S51Vv;A1M10A1Sc0GaS28G10A1A2A4S0G0S1SbSbS29S5dVv;A1M11A1Sc0GaS28G11A1A2A4S0G0S1SbSbS29S5eVv;A1M12A1Sc0G2S28G12A1A2A4S0G0S1SbSbS29S5fVv;A1M13A1Sc0G2S28G13A1A2A4S0G0S1SbSbS29S60Vv;A1M14A1Sc0Z1S28G14A1A2A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition tv_k (k : cst) : list (sv * sv) := ltac2:(tb__ "0|1|
S4S5SbSbA2M0S81S36Vk;A1A1S0G0S1SbSbS57Vk;A1Sc0Z10S58Vk;A1A2A4S0G0Sf7S2G0A1A3A3A3").

Definition X_loopA (k : cst) : list (sv * sv) := ltac2:(tb__ "0|2|
S4S5SbSbA2M0Sd6S4G0S0G0S1SbSbS6aSeZ30A1A4S0G0S1SbSbS54SeZ518A1A4S0G0Sf7S2G0A1M1A3A3A3S4G0S81S36Vk;A1A1S0G0S1SbSbS57Vk;A1Sc0Z10S58Vk;A1A2A4G1A3A3A3A3").

Definition vec_factsK (t : T3) (e : Z) : list sprop := ltac2:(tb__ "0|9|
S4ScS0ScS10S29Vt;A1M0S12P1eA1M1A2S0ScS10S11Sc1G0Sc0Ve;S28Vt;A1M2A2M3A3G1A2S0ScS10G0SeS23A1A2S0ScS10G2SeS24A1M4A2S0ScS10G3G4A2S2ScA1M5A3A3A3A3A3SbS7ScA1Lx;G0S1fG5Lz;S20S0ScS16R1Z4A2G5A3Ldv;Sc3SbSbG5Lb;La;M6Lop;M7G7Sc4G6Lop;M8G8S6S21SbG5La;Lw;Lsgn;S20SbS1fG5Lk;Li;Ll;Xbx8A3").
Definition vec_factsA (t : T3) (e : Z) : list sprop := ltac2:(tb__ "0|0|
S0ScS10S2aVt;A1S28Vt;A1A2S61Vt;Ve;A2A3").
Definition av_factsA (t : T3) : list sprop := ltac2:(tb__ "0|b|
S4ScS0ScS10S17Sc2S2aVt;A1M0SeZ3A1A3S28Vt;A1M1A2S0ScS10G0SeS26A1A2S0ScS10S29Vt;A1M2S12P1eA1M3A2S0ScS10S11Sc1G2Sc0Z4M4G1A2M5A3G3A2S0ScS10G2SeS23A1A2S0ScS10G1SeS24A1M6A2S0ScS10G5G6A2S2ScA1M7A3A3A3A3A3A3A3SbS7ScA1Lx;G2S1fG7Lz;S20S0ScS16R1G4A2G7A3Ldv;Sc3SbSbG7Lb;La;M8Lop;M9G9Sc4G8Lop;MaGaS6S21SbG7La;Lw;Lsgn;S20SbS1fG7Lk;Li;Ll;Xbx8A3").
Definition vecs_factsA (v : vecs) : list sprop := ltac2:(tb__ "0|2|
S4ScS9bS44Vv;A1A1S4ScS31S4bVv;A1Z4M0A2S4ScS31S49Vv;A1G0A2S4ScS31S70S45Vv;A1A1G0A2S4ScS31S4aVv;A1G0A2S4ScS31S48Vv;A1G0A2S4ScS31S53Vv;A1Z80A2S4ScS31S4fVv;A1ZcM1A2S4ScS31S4cVv;A1G0A2S4ScS31S50Vv;A1G0A2S4ScS31S52Vv;A1G0A2S4ScS31S4eVv;A1G1A2S4ScS31S4dVv;A1G0A2S4ScS31S51Vv;A1G1A2S4ScS61S5dVv;A1G1A2S4ScS61S5eVv;A1G0A2S4ScS61S5fVv;A1G0A2S31S60Vv;A1Z1A2A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition gMI : sv := SVar 580. Definition gFV : sv := SVar 581. Definition gMM : sv := SVar 582. Definition gSG : sv := SVar 583.
Definition gLI : sv := SVar 584. Definition gLC : sv := SVar 585. Definition gPI : sv := SVar 586.
Definition gCO : sv := SVar 587. Definition gRP : sv := SVar 588. Definition gTR : sv := SVar 589. Definition gTS : sv := SVar 590.
Definition ghost_factsLo (v : vecs) : list sprop := ltac2:(tb__ "0|0|
S0ScS10S2aS4fVv;A1A1S76A2S0ScS10S2aS4cVv;A1A1S73A2S0ScS10S2aS50Vv;A1A1S77A2S0ScS10S2aS52Vv;A1A1S79A2S0ScS10S2aS4eVv;A1A1S75A2S0ScS10S2aS4dVv;A1A1S74A2S0ScS10S2aS51Vv;A1A1S78A2S2ScA1A3A3A3A3A3A3A3").

Definition cnt_factsLo (v : vecs) : list sprop := ltac2:(tb__ "0|1|
S0ScS10S2aS4bVv;A1A1S2aS44Vv;A1A1M0A2S0ScS10S2aS48Vv;A1A1S11Sc1S17Sc2SeZ3A1G0A3SeZ2A1A3A2S0ScS10S2aS4aVv;A1A1S2aS45Vv;A1A1A2S2ScA1A3A3A3").

Definition rate_factsLo (x : sv) (v : vecs) : list sprop := ltac2:(tb__ "0|1|
S0ScS10S2aS44Vv;A1A1Vx;A2S0ScS10S2aS49Vv;A1A1Sc0Z3Vx;A2M0A2S0ScS10S2aS45Vv;A1A1Vx;A2S0ScS10S2aS53Vv;A1A1Vx;A2S0ScS10S76G0A2S0ScS10S73Vx;A2S0ScS10S77Vx;A2S0ScS10S79Vx;A2S0ScS10S75Vx;A2S0ScS10S74Vx;A2S0ScS10S78Vx;A2S0ScS10Sa0Vx;A2S0ScS10Sa1G0A2S0ScS10Sa3G0A2S0ScS10Sa4Sc0Z25Vx;A2A2S2ScA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition lines_factsA (d c k : sv) : list sprop := ltac2:(tb__ "0|7|
S4ScS0ScS10Vc;Vk;A2S0ScS10Vd;S12P1eA1M0A2S0ScS10S11Sc1Vd;Sc0Z10Vk;A2M1A3G0A2S0ScS10Vd;SeS23A1A2S0ScS10Vk;SeS24A1M2A2S0ScS10G1G2A2S0ScS10Vc;SceA2S2ScA1M3A3A3A3A3A3A3A3SbS7ScA1Ld;Vd;S1fG3Lz;S20S0ScS16R1Z4A2G3A3Ldv;Sc3SbSbG3Lb;La;M4Lop;M5G5Sc4G4Lop;M6G6S6S21SbG3La;Lw;Lsgn;S20SbS1fG3Lk0;Li;Ll;Xbx8A3").
Definition misc_factsA (cn hp hd : sv) : list sprop := ltac2:(tb__ "0|0|
S0ScS10Vhp;SeZ1A1A2S0ScS10Vcn;SeS23A1A2S0ScS10Vhd;SeZ7fffff800000A1A2S2ScA1A3A3A3").

Definition arena_factsLo (hd : sv) : list sprop := ltac2:(tb__ "0|1|
S0ScS16P110Z4A2S0ScS10SeZ1000A1Sf6A2S0ScS10S11Sc1Sf6SeZ40A1A3S12P1eA1M0A2S0ScS10Sf6SeS23A1A2S0ScS10Vhd;G0A2S2ScA1A3A3A3A3A3").

Definition frame_factsLo : list sprop := ltac2:(tb__ "0|2|
S4ScS0ScS16P6eM0Z5A2S0ScS1dS19Sc7SccSeZ0A1A3A1S0ScS10SeS10eA1M1SccA2S0ScS10G1Sd0A2S0ScS10S11Sc1Sd0SeZ1A1A3SeZ7fffff800000A1A2S2ScA1A3A3A3A3A3S10dScfG0Z800A3A3").

Definition gran_factsLo : list sprop := ltac2:(tb__ "0|0|
S4ScSfePddScdA2SfeP156Sf6A2A3").
Definition loop_factsA (k : cst) : list sprop := ltac2:(tb__ "0|2|
S4ScSbfS36Vk;A1M0A1S4ScSa5G0A1S4ScS9dG0A1S4ScSb8S57Vk;A1S7fVk;A1S58Vk;A1A3S4ScSbcS7cVk;A1S7eVk;A1S7dVk;A1M1A3S4ScS99G1A1S4ScS9fS4ScSa6Sd8A3A3A3A3A3A3A3A3").

Definition gS : sv := ltac2:(tb__ "0|0|
S11Sc1S12ScfA1SeSf8A1A3").
Definition lregsA (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|3|
S10cS100S3SbS6dS101U0U20A2A4S4S5S3SbA2M0S0G0S1S3SbU1SeZ7A1A4S0G0S1S3SbU2S25S104A1M1A4S0G0S1S3SbU3S12P17A1A4S0G0S1S3SbU4S12P18A1A4S0G0S1S3SbU8S12PaA1A4S0G0S1S3SbU9G1A4S0G0S1S3SbU12SccA4S0G0S1S3SbU13Sa2A4S0G0S1S3SbU14S11Sc1ScdSeZ32A1A3A4S0G0S1S3SbU15S11Sc1SccSeZ20A1M2A3A4S0G0S1S3SbU16S54A4S0G0S1S3SbU18G2A4S0G0S1S3SbU19SeZ9A1A4S0G0S1S3SbU1bS11Sc1SccSeZ360A1A3A4S0G0S1S3SbU1dSeZ23A1A4S0G0S1S3SbU1eS54A4S0G0S1S3SbU1fSd9A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").

Definition fkeepA (r : nat) : bool := match r with 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition lfregsA : list sv := ltac2:(tb__ "0|1|
S100S3SbS3S6SbL_;M0S10fR1U8A2SeZffffffff3f800000A1G0S9eR1A1S12S107S108U3cR1A2A1A1Sa7R1A1X6x2X6x2Lr;S101U0U20A2A4").

Definition kL (v : vecs) : cst := ltac2:(tb__ "0|1|
S39S38S2fS40SeZ0A1S27S3aS3dS3fS41Vv;S2SfA1M0G0G0G0S3cS2SdA1A10").
Definition LSAc (pc : Z) (regs : list (nat * sv)) (k : cst) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
SfaS1eVpc;SbbVregs;A1Sb7S1bS8SbA1S71Vk;A1S4ScVfacts;SbaVk;A1A3S83S9A9S98Vk;A1A2").
Definition add_datas (A : axst) (v : vecs) : axst := ltac2:(tb__ "0|1|
SffVA;S105SfdVA;A1M0S4SdS18G0A1S72Vv;A1A3A2A2").
Definition add_ents (A : axst) (es : list sobj) : axst := ltac2:(tb__ "0|1|
SffVA;S105SfdVA;A1M0S4SdS18G0A1Ves;A3A2A2").
Definition LSA (pc : Z) (regs : list (nat * sv)) (k : cst) (facts : list sprop) : axst := ltac2:(tb__ "0|1|
S69S68S65Vpc;Vregs;Vk;S4ScVfacts;S5cS5bS36Vk;A1M0A2A3A4G0A2S56Vk;A1A2").

Definition pE0 : sv := SAlu ALU_ADD pPOS pLNL.
Definition LSAx (pc : Z) (regs : list (nat * sv)) (k : cst) (facts : list sprop) : axst := ltac2:(tb__ "0|1|
S69S68S65Vpc;Vregs;Vk;S4ScVfacts;S5cS11Sc1S80SeZ1A1A3S36Vk;A1M0A2A3A4G0A2S56Vk;A1A2").

Definition rate2 (k : cst) : list sprop := ltac2:(tb__ "0|1|
S4ScS5cS5bS36Vk;A1M0A2S5cS11Sc1S80SeZ1A1A3G0A2A3").
Definition LSAb (pc : Z) (regs : list (nat * sv)) (k : cst) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S69S68S65Vpc;Vregs;Vk;S4ScVfacts;SbdVk;A1A3A4S36Vk;A1A2S56Vk;A1A2").

Definition nx_facts : list sprop := ltac2:(tb__ "0|0|
S0ScS10S5bS11Sc1SceSeZ1A1A3A2S2ScA1A3").
Definition K_loop : axst := ltac2:(tb__ "0|1|
S63SdaS0S5S3SbA2M0S1S3SbU17S27A4S2G0A1A3S7aS37A1S0ScS10S27S2fA2S59A3A4").

Definition X_bodyN : axst := ltac2:(tb__ "0|1|
S63SdbS0S5S3SbA2M0S1S3SbU17S27A4S2G0A1A3S7aS37A1S0ScS15S27S2fA2S59A3A4").

Definition kB : cst := ltac2:(tb__ "0|1|
S39S38S2fS40SeZ0A1S27S3aS3dS3fS41S37S2SfA1M0G0G0G0S3cS0SdS46S27S33S32A3S2SdA1A3A10").
Definition ent_facts : list sprop := ltac2:(tb__ "0|1|
S4ScS0ScS10S11Sc1S33S32A3SceA2S0ScS10S33SeS10aA1M0A2S0ScS10S32G0A2S0ScS10S5bS33A2S2ScA1A3A3A3A3S59A3").
Definition K_body : axst := ltac2:(tb__ "0|1|
S64SdbS0S5S3SbA2M0S1S3SbU17S27A4S2G0A1A3SaaS0ScS15S27S2fA2S42A3A4").

Definition pE : sv := SAlu ALU_ADD pPOS pLNL.

Definition iregsA (l : list (nat * sv)) : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S3SbA2M0S0G0S1S3SbU17S11Sc1S27SeZ1A1A3A4S0G0S1S3SbU1aSeSf8A1A4S0G0S1S3SbUdS34S3bA1A4S0G0S1S3SbU5S34S33A1A4S0G0S1S3SbU10S32A4S0G0S1S3SbU11S33A4S2G0A1A3A3A3A3A3A3Vl;A3").
Definition kI (cp : list cell) : cst := ltac2:(tb__ "0|1|
S39S38S2fS40SeZ0A1S11Sc1S27SeZ1A1A3S3aS3dS3fS41S37Vcp;S0SfS22Z8S34S3bA1A2S2SfA1M0A3G0G0S3cS0SdS46S27S33S32A3S2SdA1A3A10").
Definition ifactsA : list sprop := ltac2:(tb__ "0|0|
S4ScS0ScS15S27S2fA2S0ScS10S32SeScaZ2Z18A2A1A2S2ScA1A3A3S42A3").
Definition LIA (pc : Z) (regs : list (nat * sv)) (cp : list cell) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S64Vpc;Sa9Vregs;A1SabVcp;A1S4ScVfacts;Sa8A3A4").

Definition kX : cst := ltac2:(tb__ "0|1|
S39S38S2fS40SeZ0A1S11Sc1S27SeZ1A1A3S3aS3dS3fS41S37S2SfA1M0G0G0G0S3cS0SdS46S27S33S32A3S2SdA1A3A10").
Definition X_latch : axst := ltac2:(tb__ "0|1|
S66SdaS0S5S3SbA2M0S1S3SbU17S11Sc1S27SeZ1A1A3A4S2G0A1A3S7bS0ScS15S27S2fA2S42A3A4").

Definition K_l2l : axst := ltac2:(tb__ "0|2|
S64SddS0S5S3SbA2M0S1S3SbU17S11Sc1S27SeZ1A1A3A4S0G0S1S3SbU1aSeSf8A1A4S0G0S1S3SbU10S32A4S0G0S1S3SbUaS6bS27A1A4S0G0S1S3SbUbM1S6dG1A1A4S2G0A1A3A3A3A3A3S7bS0ScS15S27S2fA2S42A3A4").

Definition kX7 : cst := ltac2:(tb__ "0|1|
S39S38S2fS40SeZ7A1S11Sc1S27SeZ1A1A3S3aS3dS3fS41S37S2SfA1M0G0G0G0S3cS0SdS46S27S33S32A3S2SdA1A3A10").
Definition X_latch7 : axst := ltac2:(tb__ "0|2|
S66SdaS0S5S3SbA2M0S1S3SbU17S11Sc1S27SeZ1A1A3A4S0G0S1S3SbU1aSeSf8A1A4S0G0S1S3SbU10S32A4S0G0S1S3SbUaS6bS27A1A4S0G0S1S3SbUbM1S6dG1A1A4S2G0A1A3A3A3A3A3SadS0ScS15S27S2fA2S42A3A4").

Definition NZ32e (e : sv) : sprop := ltac2:(tb__ "0|0|
S19Sc8S1cSaQ20Ve;A3SeZ0A1A3").
Definition kXE : cst := ltac2:(tb__ "0|1|
S39S38S2fS40S5aS11Sc1S27SeZ1A1A3S3aS3dS3fS41S37S2SfA1M0G0G0G0S3cS0SdS46S27S33S32A3S2SdA1A3A10").
Definition X_latchE : axst := ltac2:(tb__ "0|1|
S66SdaS0S5S3SbA2M0S1S3SbU17S11Sc1S27SeZ1A1A3A4S2G0A1A3SaeS0ScS15S27S2fA2S0ScS6eS5aA1S42A3A3A4").
Definition kLE : cst := ltac2:(tb__ "0|1|
S39S38S2fS40S5aS27S3aS3dS3fS41S37S2SfA1M0G0G0G0S3cS2SdA1A10").
Definition K_loopE : axst := ltac2:(tb__ "0|1|
S63SdaS0S5S3SbA2M0S1S3SbU17S27A4S2G0A1A3SacS0ScS10S27S2fA2S0ScS6eS5aA1S59A3A3A4").

Definition K_ws : axst := ltac2:(tb__ "0|2|
S62SdfS0S5S3SbA2M0S1S3SbUaS34S11Sc6S3bS47A3A1M1A4S0G0S1S3SbUbG1A4S0G0S1S3SbUcS47A4S2G0A1A3A3A3S2SfA1S0ScS10SeZ1A1S47A2S0ScS10S47S3bA2S0ScS10S47S32A2S2ScA1A3A3A3A4").

Definition K_tk : axst := ltac2:(tb__ "0|2|
S62SdeS0S5S3SbA2M0S1S3SbUaS34S43A1M1A4S0G0S1S3SbUbS34S3eA1A4S0G0S1S3SbUcG1A4S2G0A1A3A3A3S0SfS22Z0G1A2S2SfA1A3S0ScS10S3eS43A2S0ScS15S43S3bA2S0ScS10S33S3eA2S2ScA1A3A3A3A4").

Definition K_dp : axst := ltac2:(tb__ "0|1|
S62SdcS0S5S3SbA2M0S1S3SbUbS34S3eA1A4S2G0A1A3S0SfS22Z0S34S43A1A2S2SfA1A3S0ScS15S3eS3bA2S0ScS10S43S3bA2S0ScS10S3eS43A2S0ScS10S33S3eA2S2ScA1A3A3A3A3A4").

Definition cps_loop : list Z := ltac2:(tb__ "0|0|
S4S1fS0S1fSdfS0S1fSdeS0S1fSdcS0S1fSdaS0S1fSdbS0S1fSddS0S1fSf4S0S1fSf3S0S1fSf5S0S1fSf0S0S1fSe0S0S1fSe3S0S1fSe2S0S1fSf2S0S1fSefS0S1fSe5S0S1fSe7S0S1fSeaS0S1fSebS0S1fSe8S0S1fSecS0S1fSe9S0S1fSe6S0S1fSeeS0S1fSf1S0S1fSedS0S1fSe1S0S1fSe4S0S1fS10bS2S1fA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sd7A3").

Goal length (builderA pERR pLINE pCN pHP xCM xSM vsP) = 41%nat /\ length spill_cells = 34%nat /\ length save_cells = 15%nat /\ length f5hdr_cells = 3%nat
  /\ forallb (fun A => swf (ax_S A) && axwf A) [K_loop; X_bodyN; K_body; X_latch; K_l2l; K_ws; K_tk; K_dp] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
