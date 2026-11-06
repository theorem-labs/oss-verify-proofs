(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "app"; "pair"; "nat"; "nil"; "prod"; "None"; "false"; "fst"; "negb"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "sobj"; "SLit"; "SPUle"; "cell"; "SAlu"; "DUnknown"; "SPBranch"; "SVar"; "FcsrFrm0"; "mkSS"; "SExt"; "SMd"; "mkObj"; "ss_regs"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "pDco"; "pA"; "pKco"; "mm_k"; "sg_k"; "mi_c"; "mm_d"; "rp_k"; "sg_d"; "tr_k"; "ts_k"; "rp_d"; "tr_d"; "ts_d"; "xbo"; "fv_d"; "fv_k"; "V496"; "cA"; "fv_c"; "shB"; "vec_facts0"; "V528"; "datasF"; "pHP"; "O_F"; "O_Wf"; "O_flag"; "O_frame"; "V560"; "V592"; "V720"; "builderF"; "fr_hf"; "hdr3"; "mi_d"; "mi_k"; "V752e"; "V784e"; "V816"; "body_facts"; "cVF"; "BCUT"; "NCO"; "X_body"; "X_hf"; "frame_factsF"; "hf_facts"; "lregsH"; "mi_n"; "mm_c"; "prog_factF"; "rp_n"; "sg_c"; "shF"; "tr_n"; "ts_n"; "tv_body"; "tv_hf"; "xfo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "pKmi"; "pDmi"; "pX"; "qA"; "pKfv"; "pDfv"; "qKco"; "X_face"; "co_live"; "qCUR"; "qKfv"; "qKmi"; "qKmm"; "qKrp"; "qKsg"; "qKtr"; "qKts"; "FCUT"; "coP"; "mmP"; "qDco"; "qDfv"; "qDmi"; "qDmm"; "qDrp"; "qDsg"; "qDtr"; "qDts"; "rpP"; "sgP"; "trP"; "tsP"; "face_facts"; "fvP"; "qCfv"; "qCmi"; "qCmm"; "qCsg"; "qERR"; "q_base"; "q_vfacts"; "F_main"; "arity_fact"; "datasMI"; "mi_facts"; "regsRW"; "EC"; "ECsh"; "NFV"; "NMI"; "NMM"; "NZ32"; "XQ"; "bd_face"; "datasFV"; "datasQ"; "fvcell"; "miP3"; "pR"; "q_acct"; "rawF"; "regsE"; "regsF2"; "tvQ"; "vr_ret_fv"; "vr_ret_mi"; "CFV"; "CMI"; "CMM"; "CSG"; "E_dg"; "E_fv"; "E_mi"; "E_mm"; "NRP"; "NSG"; "NTR"; "NTS"; "T_fvk"; "T_mif"; "T_mig"; "T_mik"; "XFV"; "datasP"; "fv_facts"; "lregsF"; "miP"; "ndA"; "objs_face"; "pairsA"; "sel_backV"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "BC_NE"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "bd_vec"; "hG"; "av_d"; "av_k"; "hF"; "vec_facts"; "HNEXT"; "O_cE"; "O_cP"; "h_fregs"; "h_xregs"; "tE"; "O_text"; "PROG"; "tI"; "tp"; "tB"; "tL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "spm"; "vDp"; "B32"; "B_EW"; "two48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shobj"; "shadow_reopen_stateA"; "xlocal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.HFAddr"; "FR"; "hf_EPI"; "hf_A"; "hf_RJ"; "hf_RW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.VRAddr"; "vr_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "A_globals"; "mkA"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "O_al"; "vERR"; "vb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.VN"; "Pre_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ANone"; "NDA"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "Pre_da"; "@Stdlib.Lists.List"; "filter"; "@Stdlib.ZArith.BinInt.Z"; "opp"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition NMI (a : sv) : sv := ltac2:(tb__ "0|0|
S11Sb3S4dSb7Z3Va;A2A3").
Definition NFV (a : sv) : sv := SAlu ALU_ADD fv_n a.
Definition NMM (a : sv) : sv := SAlu ALU_ADD mm_n a.
Definition NSG (a : sv) : sv := SAlu ALU_ADD sg_n a.
Definition NRP (a : sv) : sv := ltac2:(tb__ "0|0|
S11Sb3S50Sb7Z3Va;A2A3").
Definition NTR (a : sv) : sv := ltac2:(tb__ "0|0|
S11Sb3S53Sb7Z3Va;A2A3").
Definition NTS (a : sv) : sv := ltac2:(tb__ "0|0|
S11Sb3S54Sb7Z25Va;A2A3").
Definition pairsA (a cur kmi kfv kmm ksg kco krp ktr kts : sv) : list bitem := ltac2:(tb__ "0|2|
S1ScaSb8ZcM0S47Vcur;A1Vkco;A3S1ScaSb8G0S89Va;A1Vkmi;A3S1ScaSb8Z4M1S88Va;A1Vkfv;A3S1ScaSb8G1S8aVa;A1Vkmm;A3S1ScaSb8G1Sa3Va;A1Vksg;A3S1ScaSb8G1Sa2Va;A1Vkrp;A3S1ScaSb8G1Sa4Va;A1Vktr;A3Sb8Z1Sa5Va;A1Vkts;A3A3A3A3A3A3A3A3").
Definition bd_face (cur a kmi kfv kmm ksg kco krp ktr kts : sv) : list bitem := ltac2:(tb__ "0|0|
S1ScaS0ScaSc5S45Vcur;A2S4ScaA1A3Sb1Va;Vcur;Vkmi;Vkfv;Vkmm;Vksg;Vkco;Vkrp;Vktr;Vkts;AaA3").

Definition ndA (cur a dco kco : sv) : ndesc := ltac2:(tb__ "0|0|
SedS55Vdco;Vkco;A2S3dS8dVcur;Va;S40S2cS1fS20Vkco;S23S25S26AaSecA4").

Definition arity_fact (a : sv) : sprop := ltac2:(tb__ "0|0|
SfS11Sb3Va;Sc6A3Sc3A2").

Definition pX : sv := SVar 305.
Definition XA : axst := ltac2:(tb__ "0|2|
S46SdfS1S5S3ScA2M0S4cS0G0S2S3ScUbSc7Sc3A1A4S0G0S2S3ScU14Sc7S5aA1A4S4G0A1A3A3A3S5aS1cS1dS1eS2eS4S10A1M1G1S1SbS0SbS82S1dA1S4SbA1A3S44S5aS1dS5aS1cS1eP12fA6A3Aa").
Definition ndXA : ndesc := ltac2:(tb__ "0|0|
SafS5aS1dS1cS1eA4").
Goal map (fun L => leaf_matches1A NPH L XA) (leaves_at2 [H; L1] hf_A) = [true; true; true]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition X_conull : axst := Eval vm_compute in leaf_at XA hf_trap 0.
Goal lvs XA = [(hf_RW, RsCut); (hf_K1, RsCut); (hf_trap, RsUnsupported); (da_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_dg0 : axst := Eval vm_compute in leaf_at XA da_entry 0.
Definition E_dg : axst := Eval vm_compute in optAp (apply_axforms E_dg0 [AXSplit 0 (SLit (-96))]).
Definition s_dg : wsub := ltac2:(tb__ "0|0|
Se3PaScdS9eA1ScdSefA1A3").
Definition R_dg : list sobj := Eval vm_compute in optR (entails_frA E_dg Pre_da s_dg).
Goal entails_frA E_dg Pre_da s_dg = Some R_dg /\ call_checkA E_dg Pre_da s_dg R_dg (map la_state Posts_da) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_dg0 : axst := Eval vm_compute in T_pure Pre_da E_dg s_dg R_dg P_da.
Definition T_dg : axst := Eval vm_compute in ax_setX (optAp (apply_axforms T_dg0 [AXSelect sel_da; AXMerge 0])) (X_body pDco pKco).
Goal shape T_dg = shape XA /\ lvs T_dg = [(hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition F_main : list cell := Eval vm_compute in List.filter (fun c => negb (sv_eqb (c_off c) (SLit (-136)))) F_cells.
Definition objs_face (cur hp : sv) (co rp tr mi fv mm sg ts : sobj) (ofcells fcells txt : list cell) (datas : list sobj) (tail : list sobj) : list sobj := ltac2:(tb__ "0|1|
S1SdS0SdS36S0SdS38S1S10S3eVfcells;A3A1S0SdS37S4SdA1M0A3A3A3S1SdSe5S1SdS0SdS35S1S10S81Vofcells;A3A1G0A3S1SdS3cSe9Vhp;Vco;Vrp;Vtr;Vmi;Vfv;Vmm;Vsg;Vts;AaS1SdS0SdSe8S0SdSc0Vcur;A1S0SdSbfS0SdS19Sc8SeZ0A1Sc9Vtxt;S12A5G0A3A3A3A3S1SdVdatas;Vtail;A3A3A3A3A3A3").

Definition FCUT (pc : Z) (regs : list (nat * sv)) (cur : sv) (co rp tr mi fv mm sg ts : sobj) (ofcells fcells : list cell) (datas tail : list sobj)
                (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
Se6S16Vpc;Sc2Vregs;A1Sc1S15S6ScA1Sb0Vcur;S34Vco;Vrp;Vtr;Vmi;Vfv;Vmm;Vsg;Vts;Vofcells;Vfcells;S4S10A1Vdatas;Vtail;AfVfacts;SbeS7A9VX;A2").

Definition coP : sobj := ltac2:(tb__ "0|0|
S3bS1cS1dS1eA3").
Definition rpP : sobj := V752e rp_d rp_k. Definition trP : sobj := V784e tr_d tr_k. Definition tsP : sobj := V816 ts_d ts_k.
Definition miP : sobj := ltac2:(tb__ "0|0|
S2dS3fS21S40A3"). Definition fvP : sobj := ltac2:(tb__ "0|0|
S32S2bS2fS2cA3"). Definition mmP : sobj := ltac2:(tb__ "0|0|
S39S22S4eS1fA3"). Definition sgP : sobj := ltac2:(tb__ "0|0|
S3aS24S51S20A3").
Definition datasP : list sobj := ltac2:(tb__ "0|0|
S33SbaSbbS3fS40S2bS2cS22S1fS24S20S1cS1eS27S23S28S25S29S26A12").

Definition face_facts (cur : sv) : list sprop := ltac2:(tb__ "0|0|
S1SbS0SbS82S1dA1S4SbA1A3S44Vcur;S1dVcur;S1cS1eP12fA6A3").

Definition lregsF : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S3ScA2M0S2S3ScU2Sd0SddA1M1A4S0G0S2S3ScU8S14PaA1A4S0G0S2S3ScU9G1A4S0G0S2S3ScU12Se7A4S0G0S2S3ScU15SeaA4S4G0A1A3A3A3A3A3").
Definition RW : axst := ltac2:(tb__ "0|3|
S69Se1S1S5S3ScA2M0SadS0G0S2S3ScUbSeZ3A1M1A4S0G0S2S3ScUfS1cA4S0G0S2S3ScU13S1dA4S0G0S2S3ScU14S30Z43A1A4S0G0S2S3ScU18SbcA4S0G0S2S3ScU19S2aZ218A1A4S0G0S2S3ScU1aS2aZ210A1A4S4G0A1A3A3A3A3A3A3A3A3S5aS6aS74S76SaeS79S6bS75S77S1S10S2eS0S10ScfN88S1cA2S4S10A1M2A3A3G2SabS4SdA1S1SbS0SbS13Sb4S1dG1A3S4SbA1A3S78S5aA1A3S48S1cS1eA2A11").
Goal leaf_matches1A NPH (leaf_at XA hf_RW 0) RW = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs RW = [(vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition sel_backV (vi di : nat) : list nat :=
  let fix go (j : nat) (k : nat) (n : nat) : list nat :=
    match n with O => [] | S n' =>
      if Nat.eqb j 3 then 5%nat :: go (S j) k n' else if Nat.eqb j 4 then 6%nat :: go (S j) k n'
      else if Nat.eqb j vi then 2%nat :: go (S j) k n' else if Nat.eqb j 23 then 3%nat :: go (S j) k n'
      else if Nat.eqb j di then 4%nat :: go (S j) k n' else k :: go (S j) (S k) n' end
  in (1 :: 0 :: go 1 7 35)%nat.
Goal sel_backV 18 32 = sel_back. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition xf_backV (vi di : nat) (off : Z) : list axform := ltac2:(tb__ "0|0|
S0Sd5Sd6U1Z40A2S0Sd5Sd8Sb2Vvi;Vdi;A2A1S0Sd5Sd7U0A1S0Sd5Sd6Vvi;Sf1Voff;A1A2S4Sd5A1A3A3A3A3").
Definition E_mi0 : axst := Eval vm_compute in leaf_at RW vr_entry 0.

Definition vr_need (e : Z) (w n : sv) : list sprop := ltac2:(tb__ "0|3|
S0SbSfVw;Vn;A2S0SbSfSb7Ve;Vw;A2M0Sb7Ve;Vn;A2M1A2S0SbSfG1SeSd3A1M2A2S0SbSfG0G2A2S0SbSfVw;SeSd4A1A2S4SbA1A3A3A3A3A3").
Definition want_of (E : axst) : sv := ltac2:(tb__ "0|0|
SeeScUbS1aScdVE;A1A1SeZ0A1A4").

Definition E_mi : axst := Eval vm_compute in let E := optAp (apply_axforms E_mi0 (xf_vr 15 496)) in ax_add_facts (vr_need 12 (want_of E) (NMI pA)) E.
Definition s_mi : wsub := ltac2:(tb__ "0|1|
S0S5ScbScA2M0S2ScbScP3bS89S1dA1A4S0G0S2ScbScP13S11Sb3Sd1SeZ40A1A3A4Se3PaScdSa0A1ScdSebA1A3A3A3").
Definition R_mi : list sobj := Eval vm_compute in optR (entails_frA E_mi VN.Pre_vr s_mi).
Goal entails_frA E_mi VN.Pre_vr s_mi = Some R_mi /\ call_checkPA E_mi VN.Pre_vr s_mi R_mi (map fst PD_vn) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition X_face (dmi dfv dmm dsg dco drp dtr dts kmi kfv kmm ksg kco krp ktr kts : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S0S5ScScA2S2ScScSbcSeZ0A1A4S49SbaVdmi;Vdfv;Vdmm;Vdsg;Vdco;Vdrp;Vdtr;Vdts;SbbVkmi;Vkfv;Vkmm;Vksg;Vkco;Vkrp;Vktr;Vkts;A12A3").
Definition XkeepF (d : sv) (X : list (sv * sv)) : list (sv * sv) := ltac2:(tb__ "0|1|
Sf0S5ScScA2M0G0S9S1bS8ScScR1A3Vd;A2A1Lr;VX;A3").
Definition T_mik0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_mi s_mi R_mi VN.P_keep (XkeepF mi_d (X_body pDco pKco)).
Definition T_mif0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_mi s_mi R_mi VN.P_fail (XkeepF mi_d (X_body pDco pKco)).
Definition T_mig0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_mi s_mi R_mi VN.P_grown (XkeepF mi_d (X_body pDco pKco)).
Definition T_mik : axst := Eval vm_compute in optAp (apply_axforms T_mik0 (xf_backV 14 28 496)).
Definition T_mif : axst := Eval vm_compute in optAp (apply_axforms T_mif0 (xf_backV 14 28 496)).
Definition T_mig : axst := Eval vm_compute in optAp (apply_axforms T_mig0 (xf_backV 14 28 496)).
Goal shape T_mik = shape RW /\ shape T_mif = shape RW. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition pDmi : sv := SVar 307. Definition pKmi : sv := SVar 308.
Definition vr_ret_mi : Z := 0x9d3b0.
Definition regsRW (ra a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S3ScA2M0S2S3ScU2Sd0SddA1M1A4S0G0S2S3ScU8S14PaA1A4S0G0S2S3ScU9G1A4S0G0S2S3ScU1Vra;A4S0G0S2S3ScUaVa0;A4S0G0S2S3ScU12Se7A4S0G0S2S3ScU13S2aZ1f0A1A4S0G0S2S3ScU14S30Z43A1A4S0G0S2S3ScU15S2aZ1f8A1A4S0G0S2S3ScU16S30Z0A1A4S0G0S2S3ScU17S30Z3fA1A4S0G0S2S3ScU18SbcA4S0G0S2S3ScU19S2aZ218A1A4S0G0S2S3ScU1aS2aZ210A1A4S0G0S2S3ScU1bSeZ3A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition datasMI (dmi kmi : sv) : list sobj := ltac2:(tb__ "0|0|
S33SbaSbbVdmi;Vkmi;S2bS2cS22S1fS24S20S1cS1eS27S23S28S25S29S26A12").
Definition mi_facts (dmi kmi : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S1SbS0SbSfS11Sb3S21SeZ3A1A3Vkmi;A2S0SbSfSeSdcA1Vdmi;A2S0SbSfS11Sb3Sb7ZcM0S21A2SeZ24A1A3Sb7G0Vkmi;A2A2S4SbA1A3A3A3S31Vdmi;Vkmi;G0Vdv;A4A3").

Definition co_live : sprop := ltac2:(tb__ "0|0|
SfSeSdcA1S1cA2").
Definition JR_mi : axst := ltac2:(tb__ "0|1|
S69Se2S85SeS99A1SeZ1A1A2S5aS6aS74S76S2dS59S21S58A3S79S6bS75S77S1S10S2eS0S10ScfN88S1cA2S4S10A1M0A3A3G0S83S59S58A2S0SdSd9Sb9Z4Z5G0S12A5S4SdA1A3S1SbS0SbS13Sb4S1dSeZ3A1A3S0SbS60S4SbA1A3A3S1SbS84S59S58P133A3S78S5aA1A3A3S5fS59S2bS22S24S1cS27S28S29S58S2cS1fS20S1eS23S25S26A10A11").
Definition JF_mi : axst := ltac2:(tb__ "0|1|
S69Se2S85SeS99A1SeZ0A1A2S5aS6aS74S76S2dS59S21S58A3S79S6bS75S77S1S10S2eS0S10ScfN88S1cA2S4S10A1M0A3A3G0S83S59S58A2S4SdA1S1SbS0SbS13Sb4S1dSeZ3A1A3S0SbS60S0SbSfS21S58A2S4SbA1A3A3A3S1SbS31S59S58ZcP133A4S78S5aA1A3A3S5fS59S2bS22S24S1cS27S28S29S58S2cS1fS20S1eS23S25S26A10A11").
Definition T_miks : axst := ltac2:(tb__ "0|0|
Se4S0SbSfSeSdcA1S3fA2S0SbS60S4SbA1A3A3Sa9A2").
Definition T_migs : axst := ltac2:(tb__ "0|0|
Se4S0SbS60S4SbA1A3Sa8A2").
Definition T_mifs : axst := ltac2:(tb__ "0|0|
Se4S0SbS60S4SbA1A3Sa7A2").
Definition reopen45 (A : axst) : axst := ltac2:(tb__ "0|0|
SdaVA;SceVA;A1Sb9Z4Z5A5").
Goal map (fun L => leaf_matches1A NPH L JR_mi) [reopen45 T_miks; reopen45 T_migs] = [true; true] /\ leaf_matches1A NPH T_mifs JF_mi = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Goal lvs JR_mi = [(hf_C36, RsCut)] /\ lvs JF_mi = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition pR : sv := SVar 309.
Definition done36 : sv := SAlu ALU_SUB (SLit 36) pR.
Definition dstmi (dmi : sv) : sv := ltac2:(tb__ "0|0|
S11Sb3Vdmi;S18Sb6S21SeZcA1A3A3").
Definition c36_facts : list sprop := ltac2:(tb__ "0|1|
S0SbSfSeZ1A1S92A2S0SbSfS92SeZ24A1M0A2S0SbSfG0Sb7ZcS1eA2A2S4SbA1A3A3A3").
Definition L_C36 : axst := Eval vm_compute in leaf_at JR_mi hf_C36 0.
Definition C36 : axst := Eval vm_compute in bl_cut L_C36 14 (SLit 36) [10; 11; 17; 5]%nat [].
Goal leaf_matches1A NPH (leaf_at JR_mi hf_C36 0) C36 = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs C36 = [(hf_C36, RsCut); (hf_RJ, RsCut); (hf_C36, RsCut); (hf_RJ, RsCut)]
  /\ map (fun L => leaf_matches1A NPH L C36) (leavesA_at FUEL_hf cutpcs_hf C36 hf_C36) = [true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition RJ : axst := ltac2:(tb__ "0|1|
S69Se0S85S14P191A1S14P19aA1A2S5aS6aS74S76S2dS59S21S58A3S79S6bS75S77S1S10S2eS0S10ScfN88S1cA2S4S10A1M0A3A3G0S83S59S58A2S0SdSd9Sb9Z4Z5G0S12A5S4SdA1A3S1SbS0SbS13Sb4S1dSeZ3A1A3S0SbS60S4SbA1A3A3S1SbS84S59S58P133A3S78S5aA1A3A3S5fS59S2bS22S24S1cS27S28S29S58S2cS1fS20S1eS23S25S26A10A11").
Goal map (fun L => leaf_matches1A NPH L RJ) (leavesA_at FUEL_hf cutpcs_hf C36 hf_RJ) = [true; true]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs RJ = [(vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_fv0 : axst := Eval vm_compute in leaf_at RJ vr_entry 0.
Definition sh_fv : sobj := Eval vm_compute in last (ss_objs (ax_S E_fv0)) O_Wf.
Definition objs_fv0 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S E_fv0)).
Goal sh_fv = shobj hG 4 5 (ob_cells sh_fv) DUnknown /\ local_ok (ob_cells sh_fv) DUnknown 4 5 (32, 4) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E_fv1 : axst := Eval vm_compute in shadow_release_stateA E_fv0 objs_fv0 160 [(32, 4)].
Definition E_fv : axst := Eval vm_compute in let E := optAp (apply_axforms E_fv1 (xf_vr 16 528)) in ax_add_facts (vr_need 4 (want_of E) (NFV pA)) E.
Definition s_fv : wsub := ltac2:(tb__ "0|1|
S0S5ScbScA2M0S2ScbScP3bS88S1dA1A4S0G0S2ScbScP13S11Sb3Sd1SeZ40A1A3A4Se3PaScdS9fA1ScdSebA1A3A3A3").
Definition R_fv : list sobj := Eval vm_compute in optR (entails_frA E_fv VN.Pre_vr s_fv).
Goal entails_frA E_fv VN.Pre_vr s_fv = Some R_fv /\ call_checkPA E_fv VN.Pre_vr s_fv R_fv (map fst PD_vn) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition XF1 : list (sv * sv) := ltac2:(tb__ "0|0|
S0S5ScScA2SdbPa0S2SccSccZ20Z4A4A2S5fS59S2bS22S24S1cS27S28S29S58S2cS1fS20S1eS23S25S26A10A3").
Definition T_fvk0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_fv s_fv R_fv VN.P_keep (XkeepF fv_d XF1).
Definition T_fvf0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_fv s_fv R_fv VN.P_fail (XkeepF fv_d XF1).
Definition T_fvg0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_fv s_fv R_fv VN.P_grown (XkeepF fv_d XF1).
Definition T_fvk : axst := Eval vm_compute in optAp (apply_axforms T_fvk0 (xf_backV 15 29 528)).
Definition T_fvf : axst := Eval vm_compute in optAp (apply_axforms T_fvf0 (xf_backV 15 29 528)).
Definition T_fvg : axst := Eval vm_compute in optAp (apply_axforms T_fvg0 (xf_backV 15 29 528)).

Definition pDfv : sv := SVar 314. Definition pKfv : sv := SVar 315.
Definition vr_ret_fv : Z := 0x9e4c8.
Definition regsF2 (ra a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S3ScA2M0S2S3ScU2Sd0SddA1M1A4S0G0S2S3ScU8S14PaA1A4S0G0S2S3ScU9G1A4S0G0S2S3ScU1Vra;A4S0G0S2S3ScUaVa0;A4S0G0S2S3ScU12Se7A4S0G0S2S3ScU13S57Z20A1A4S0G0S2S3ScU14S30Z43A1A4S0G0S2S3ScU15S2aZ1f8A1A4S0G0S2S3ScU16S30Z0A1A4S0G0S2S3ScU17S30Z3fA1A4S0G0S2S3ScU18SbcA4S0G0S2S3ScU19S2aZ218A1A4S0G0S2S3ScU1aS2aZ210A1A4S0G0S2S3ScU1bSeZ3A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition miP3 : sobj := ltac2:(tb__ "0|0|
S2dS59S11Sb3S21SeZ3A1A3S58A3").
Definition fvcell : list cell := [c4 32 (SLit 3)].
Definition datasFV (dfv kfv : sv) : list sobj := ltac2:(tb__ "0|0|
S33SbaSbbS59S58Vdfv;Vkfv;S22S1fS24S20S1cS1eS27S23S28S25S29S26A12").
Definition XFV (dfv kfv : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S0S5ScScA2SdbPa0S2SccSccZ20Z4A4A2S5fS59Vdfv;S22S24S1cS27S28S29S58Vkfv;S1fS20S1eS23S25S26A10A3").
Definition fv_facts (dfv kfv : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S1SbS0SbSfS11Sb3S2fSeZ1A1A3Vkfv;A2S0SbSfSeSdcA1Vdfv;A2S0SbSfS11Sb3Sb7Z4M0S2fA2SeG0A1A3Sb7G0Vkfv;A2A2S4SbA1A3A3A3S31Vdfv;Vkfv;G0Vdv;A4A3").
Definition rawF : list sprop := ltac2:(tb__ "0|0|
S1SbS0SbS13Sb4S1dSeZ3A1A3S0SbS60S4SbA1A3A3S1SbS84S59S58P133A3S78S5aA1A3A3").
Definition JR_fv : axst := ltac2:(tb__ "0|0|
S69Se2S96SeS98A1SeZ1A1A2S5aS6aS74S76S91S32S5dS2fS5cA3S6bS75S77S1S10S2eS0S10ScfN88S1cA2S4S10A1A3A3S90S8eS5dS5cA2S4SdA1S1SbSacS5dS5cP13aA3S1SbS94S0SbSfS2fSeSd2A1A2S4SbA1A3A3A3SaaS5dS5cA2A11").

Definition JF_fv : axst := ltac2:(tb__ "0|2|
S69Se2S96SeS98A1SeZ0A1A2S5aS6aS74S76S91S32S5dS2fS5cA3S6bS75S77S1S10S2eS0S10ScfN88S1cA2S4S10A1M0A3A3S90S8eS5dS5cA2S0SdSd9Sb9Z4M1Z5G0S12A5S4SdA1A3S1SbS0SbSfS2fS5cA2S4SbA1A3S1SbS31S5dS5cG1P13aA4S94A3A3S5fS59S5dS22S24S1cS27S28S29S58S5cS1fS20S1eS23S25S26A10A11").
Definition reopen45X (A : axst) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
SdaVA;VX;Sb9Z4Z5A5").
Definition T_fvks : axst := ltac2:(tb__ "0|0|
Se4S0SbSfSeSdcA1S2bA2S4SbA1A3Sa6A2").
Goal map (fun L => leaf_matches1A NPH L JR_fv) [T_fvks; T_fvg] = [true; true]
  /\ leaf_matches1A NPH (reopen45X T_fvf (X_face pDmi fv_d mm_d sg_d pDco rp_d tr_d ts_d pKmi fv_k mm_k sg_k pKco rp_k tr_k ts_k)) JF_fv = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal lvs JR_fv = [(hf_MQ, RsCut)] /\ lvs JF_fv = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Pre_mc : axst := Pre_memcpy memcpy_pc.
Definition L_mc1 : axst := L_memcpy (ae_ret_asan_memcpy AE_A).

Definition T_mcq : axst := Eval vm_compute in bl_forget (bl_prune HNEXT (leaf_at JR_fv hf_MQ 0)) [29%nat].
Goal shape T_mcq = shape JR_fv /\ lvs T_mcq = [(vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_mm0 : axst := Eval vm_compute in leaf_at T_mcq vr_entry 0.
Definition E_mm : axst := Eval vm_compute in let E := optAp (apply_axforms E_mm0 (xf_vr 17 560)) in ax_add_facts (vr_need 4 (want_of E) (NMM pA)) E.
Definition s_mm : wsub := ltac2:(tb__ "0|1|
S0S5ScbScA2M0S2ScbScP3bS8aS1dA1A4S0G0S2ScbScP13S11Sb3Sd1SeZ40A1A3A4Se3PaScdSa1A1ScdSebA1A3A3A3").
Definition R_mm : list sobj := Eval vm_compute in optR (entails_frA E_mm VN.Pre_vr s_mm).
Goal entails_frA E_mm VN.Pre_vr s_mm = Some R_mm /\ call_checkPA E_mm VN.Pre_vr s_mm R_mm (map fst PD_vn) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_mmk0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_mm s_mm R_mm VN.P_keep (XkeepF mm_d (XFV pDfv pKfv)).
Definition T_mmf0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_mm s_mm R_mm VN.P_fail (XkeepF mm_d (XFV pDfv pKfv)).
Definition T_mmg0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_mm s_mm R_mm VN.P_grown (XkeepF mm_d (XFV pDfv pKfv)).
Definition T_mmk : axst := Eval vm_compute in optAp (apply_axforms T_mmk0 (xf_backV 16 30 560)).
Definition T_mmf : axst := Eval vm_compute in optAp (apply_axforms T_mmf0 (xf_backV 16 30 560)).
Definition T_mmg : axst := Eval vm_compute in optAp (apply_axforms T_mmg0 (xf_backV 16 30 560)).
Goal shape T_mmk = shape JR_fv. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition qCUR : sv := SVar 320.
Definition qDmi : sv := SVar 321. Definition qCmi : sv := SVar 322. Definition qKmi : sv := SVar 323.
Definition qDfv : sv := SVar 324. Definition qCfv : sv := SVar 325. Definition qKfv : sv := SVar 326.
Definition qDmm : sv := SVar 327. Definition qCmm : sv := SVar 328. Definition qKmm : sv := SVar 329.
Definition qDsg : sv := SVar 330. Definition qCsg : sv := SVar 331. Definition qKsg : sv := SVar 332.
Definition qDco : sv := SVar 333. Definition qA : sv := SVar 334. Definition qKco : sv := SVar 335.
Definition qDrp : sv := SVar 336. Definition qKrp : sv := SVar 337. Definition qDtr : sv := SVar 338. Definition qKtr : sv := SVar 339.
Definition qDts : sv := SVar 340. Definition qKts : sv := SVar 341. Definition qERR : sv := SVar 342.
Definition NZ32 (e : sv) : sprop := ltac2:(tb__ "0|0|
S13Sb5S17SaQ20Ve;A3SeZ0A1A3").
Definition datasQ : list sobj := ltac2:(tb__ "0|0|
S33SbaSbbS6eS63S6dS62S6fS64S71S66S6cS5eS70S65S72S67S73S68A12").
Definition XQ : list (sv * sv) := ltac2:(tb__ "0|0|
S5fS6eS6dS6fS71S6cS70S72S73S63S62S64S66S5eS65S67S68A10").
Definition q_vfacts : list sprop := ltac2:(tb__ "0|2|
S1SbSbdS6eS7bS63ZcM0P141A5S1SbSbdS6dS7aS62Z4M1P144A5S1SbSbdS6fS7cS64G1P147A5S1SbSbdS71S7dS66G1P14aA5S1SbS31S6cS5eG0P14dA4S1SbS0SbSfS5bS5eA2S4SbA1A3S1SbS31S70S65G1P150A4S1SbS31S72S67G1P152A4SbdS73SeZ0A1S68Z1P154A5A3A3A3A3A3A3A3A3").
Definition q_base : list sprop := ltac2:(tb__ "0|0|
S1SbS0SbSfS34SeZ1A1A2S0SbSfSc6S61A2S0SbSfS61Sc3A2S4SbA1A3A3A3S1SbS4aS4bA3A3").

Definition CMI (a : sv) : sv := ltac2:(tb__ "0|0|
S11Sb3S21Sb7Z3Va;A2A3").
Definition CFV (a : sv) : sv := SAlu ALU_ADD fv_c a.
Definition CMM (a : sv) : sv := SAlu ALU_ADD mm_c a.
Definition CSG (a : sv) : sv := SAlu ALU_ADD sg_c a.
Definition q_acct : list sprop := ltac2:(tb__ "0|0|
S0SbS82S5bA1S0SbS4fS5bS61A2S0SbSfS7bS9bS5bA1A2S0SbSfS7aS9aS5bA1A2S0SbSfS7cS9cS5bA1A2S0SbSfS7dS9dS5bA1A2S4SbA1A3A3A3A3A3A3").
Definition regsE : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S3ScA2M0S2S3ScU2Sd0SddA1M1A4S0G0S2S3ScU8S14PaA1A4S0G0S2S3ScU9G1A4S0G0S2S3ScU13S52A4S0G0S2S3ScU14SbcA4S0G0S2S3ScU18SbcA4S4G0A1A3A3A3A3A3A3").
Definition EC (err : sv) (facts : list sprop) : axst := ltac2:(tb__ "0|1|
Se6S16SdeSc2S95A1Sc1S15S6ScA1S1SdS0SdS36S0SdS38S3eA1S0SdS37S4SdA1M0A3A3A3S1SdSe5S1SdS0SdS35S81A1G0A3S1SdS3cVerr;S34S3bS6cS5bS5eA3S41S70S65A2S42S72S67A2S2dS6eS7bS63A3S32S6dS7aS62A3S39S6fS7cS64A3S3aS71S7dS66A3S43S73S68A2AaS1SdS0SdSe8S0SdSc0S61A1S0SdSbfS0SdSc4G0A3A3A3A3S8fA3A3A3A3A3Vfacts;SbeS7A9S8cA2").
Definition C_Eo : axst := ltac2:(tb__ "0|0|
S86Se9S1SbS93S1SbS80S7fA3A3A2").
Definition C_Ef : axst := ltac2:(tb__ "0|0|
S86S7eS1SbS0SbS8bS7eA1S4SbA1A3S1SbS80S7fA3A3A2").
Definition tvQ : list (sv * sv) := ltac2:(tb__ "0|0|
S56SbaSbbS6eS63S6dS62S6fS64S71S66S6cS5eS70S65S72S67S73S68A12").
Definition ndEo : ndesc := ltac2:(tb__ "0|0|
SedS97S3dS8dS61S5bS63S62S64S66S5eS65S67S68AaSecA4").
Definition ndEf : ndesc := ltac2:(tb__ "0|0|
SedS97S3dS0ScaSc5S45S61A2S4ScaA1A3SecA4").

Definition ECsh (err : sv) (facts : list sprop) (sh : list sobj) : axst := ltac2:(tb__ "0|1|
Se6S16SdeSc2S95A1Sc1S15S6ScA1S1SdS0SdS36S0SdS38S3eA1S0SdS37S4SdA1M0A3A3A3S1SdSe5S1SdS0SdS35S81A1G0A3S1SdS3cVerr;S34S3bS6cS5bS5eA3S41S70S65A2S42S72S67A2S2dS6eS7bS63A3S32S6dS7aS62A3S39S6fS7cS64A3S3aS71S7dS66A3S43S73S68A2AaS1SdS0SdSe8S0SdSc0S61A1S0SdSbfS0SdSc4G0A3A3A3A3S1SdS8fVsh;A3A3A3A3A3A3Vfacts;SbeS7A9S8cA2").
Definition XEo4 : axst := ltac2:(tb__ "0|0|
S87Se9S1SbS93S1SbS80S7fA3A3S0SdSd9Sb9Z4Z5S4S10A1S12A5S4SdA1A3A3").
Definition XEf4 : axst := ltac2:(tb__ "0|0|
S87S7eS1SbS0SbS8bS7eA1S4SbA1A3S1SbS80S7fA3A3S0SdSd9Sb9Z4Z5S4S10A1S12A5S4SdA1A3A3").
Goal map (fun L => leaf_matches1A NPH L C_Eo) (leaves_at2 [T_dg] hf_EPI) = [true]
  /\ map (fun L => leaf_matches1A NPH L C_Ef) (leaves_at2 [JF_co; K; JF_mi] hf_EPI) = [true; true; true; true; true; true]
  /\ map (fun L => leaf_matches1A NPH L XEf4) (leaves_at2 [JF_fv] hf_EPI) = [true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
