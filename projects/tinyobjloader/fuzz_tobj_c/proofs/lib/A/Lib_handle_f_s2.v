(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "app"; "pair"; "nil"; "prod"; "None"; "false"; "fst"; "negb"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "sobj"; "SLit"; "SPUle"; "cell"; "SAlu"; "DUnknown"; "SPBranch"; "SVar"; "FcsrFrm0"; "mkSS"; "SExt"; "SMd"; "mkObj"; "ss_regs"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "pDmi"; "pKmi"; "pX"; "pKfv"; "qA"; "pDfv"; "X_face"; "co_live"; "qKco"; "FCUT"; "coP"; "mmP"; "qCUR"; "qKfv"; "qKmi"; "qKmm"; "qKrp"; "qKsg"; "qKtr"; "qKts"; "rpP"; "sgP"; "trP"; "tsP"; "face_facts"; "qDco"; "qDfv"; "qDmi"; "qDmm"; "qDrp"; "qDsg"; "qDtr"; "qDts"; "fvP"; "datasMI"; "mi_facts"; "qCfv"; "qCmi"; "qCmm"; "qCsg"; "qERR"; "q_base"; "q_vfacts"; "regsRW"; "F_main"; "arity_fact"; "pR"; "EC"; "ECsh"; "NFV"; "NMI"; "NMM"; "NZ32"; "XQ"; "bd_face"; "datasFV"; "datasQ"; "done36"; "fvcell"; "miP3"; "q_acct"; "rawF"; "regsE"; "regsF2"; "tvQ"; "vr_ret_fv"; "vr_ret_mi"; "CFV"; "CMI"; "CMM"; "CSG"; "E_dg"; "E_fv"; "E_mc"; "E_mi"; "E_mm"; "NRP"; "NSG"; "NTR"; "NTS"; "Pre_mc"; "T_fvk"; "T_mif"; "T_mig"; "T_mik"; "XFV"; "c36_facts"; "datasP"; "dstmi"; "fv_facts"; "lregsF"; "miP"; "ndA"; "objs_face"; "pairsA"; "sel_backV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "pDco"; "pKco"; "pA"; "mm_k"; "sg_k"; "mi_c"; "mm_d"; "rp_k"; "sg_d"; "tr_k"; "ts_k"; "rp_d"; "tr_d"; "ts_d"; "xbo"; "fv_d"; "fv_k"; "V496"; "cA"; "fv_c"; "vec_facts0"; "shB"; "V528"; "datasF"; "pHP"; "O_F"; "O_Wf"; "O_flag"; "O_frame"; "V560"; "V592"; "V720"; "builderF"; "fr_hf"; "hdr3"; "mi_d"; "mi_k"; "V752e"; "V784e"; "V816"; "body_facts"; "cVF"; "xfo"; "BCUT"; "NCO"; "X_body"; "X_hf"; "frame_factsF"; "hf_facts"; "lregs0"; "lregsH"; "mi_n"; "mm_c"; "prog_factF"; "rp_n"; "sg_c"; "shC"; "tr_n"; "ts_n"; "tv_body"; "tv_hf"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "BC_NE"; "M_MUL"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "hF"; "bd_vec"; "hG"; "av_d"; "av_k"; "vec_facts"; "HNEXT"; "O_cE"; "O_cP"; "h_fregs"; "h_xregs"; "tE"; "tp"; "O_text"; "PROG"; "tI"; "tB"; "tL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "AXUnbase"; "AXMerge"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vb"; "O_al"; "vERR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "c8"; "vDp"; "spm"; "B_EW"; "two48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shobj"; "shadow_reopen_stateA"; "xlocal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.VRAddr"; "vr_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "A_globals"; "mkA"; "shb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.HFAddr"; "FR"; "hf_EPI"; "hf_A"; "hf_C36"; "hf_RJ"; "hf_RW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.VN"; "Pre_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ANone"; "NDA"; "@Corelib.Lists.ListDef"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@Stdlib.Lists.List"; "filter"; "@Stdlib.ZArith.BinInt.Z"; "opp"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition NMI (a : sv) : sv := ltac2:(tb__ "0|0|
S11Sb9SafSbfZ3Va;A2A3").
Definition NFV (a : sv) : sv := SAlu ALU_ADD fv_n a.
Definition NMM (a : sv) : sv := SAlu ALU_ADD mm_n a.
Definition NSG (a : sv) : sv := SAlu ALU_ADD sg_n a.
Definition NRP (a : sv) : sv := ltac2:(tb__ "0|0|
S11Sb9Sb2SbfZ3Va;A2A3").
Definition NTR (a : sv) : sv := ltac2:(tb__ "0|0|
S11Sb9Sb5SbfZ3Va;A2A3").
Definition NTS (a : sv) : sv := ltac2:(tb__ "0|0|
S11Sb9Sb6SbfZ25Va;A2A3").
Definition pairsA (a cur kmi kfv kmm ksg kco krp ktr kts : sv) : list bitem := ltac2:(tb__ "0|2|
S2Sd2Sc1ZcM0Sa8Vcur;A1Vkco;A3S2Sd2Sc1G0S4eVa;A1Vkmi;A3S2Sd2Sc1Z4M1S4dVa;A1Vkfv;A3S2Sd2Sc1G1S4fVa;A1Vkmm;A3S2Sd2Sc1G1S69Va;A1Vksg;A3S2Sd2Sc1G1S68Va;A1Vkrp;A3S2Sd2Sc1G1S6aVa;A1Vktr;A3Sc1Z1S6bVa;A1Vkts;A3A3A3A3A3A3A3A3").
Definition bd_face (cur a kmi kfv kmm ksg kco krp ktr kts : sv) : list bitem := ltac2:(tb__ "0|0|
S2Sd2S0Sd2SceSa5Vcur;A2S4Sd2A1A3S7aVa;Vcur;Vkmi;Vkfv;Vkmm;Vksg;Vkco;Vkrp;Vktr;Vkts;AaA3").

Definition ndA (cur a dco kco : sv) : ndesc := ltac2:(tb__ "0|0|
Sf4Sb7Vdco;Vkco;A2S9dS52Vcur;Va;Sa0S8cS7fS80Vkco;S83S85S86AaSf3A4").

Definition arity_fact (a : sv) : sprop := ltac2:(tb__ "0|0|
SfS11Sb9Va;ScfA3ScbA2").

Definition pX : sv := SVar 305.
Definition XA : axst := ltac2:(tb__ "0|2|
Sa7SeeS2S5S1ScA2M0SaeS0G0S3S1ScUbSb4Z0A1A4S0G0S3S1ScUcSccScbA1A4S0G0S3S1ScU15SccS1eA1A4S4G0A1A3A3A3A3S1eS7cS7eS7dS8eS4S10A1M1G1S2SbS0SbS49S7eA1S4SbA1A3Sa4S1eS7eS1eS7cS7dP12fA6A3Aa").
Definition ndXA : ndesc := ltac2:(tb__ "0|0|
S78S1eS7eS7cS7dA4").
Goal map (fun L => leaf_matches1A NPH L XA) (leaves_at2 [H; L1] hf_A) = [true; true; true]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs XA = [(hf_RW, RsCut); (hf_K1, RsCut); (da_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_dg0 : axst := Eval vm_compute in leaf_at XA da_entry 0.
Definition E_dg : axst := Eval vm_compute in optAp (apply_axforms E_dg0 [AXSplit 0 (SLit (-96))]).
Definition s_dg : wsub := ltac2:(tb__ "0|0|
Se5PaSd3S63A1Sd3Sf7A1A3").
Definition R_dg : list sobj := Eval vm_compute in optR (entails_frA E_dg Pre_da s_dg).
Goal entails_frA E_dg Pre_da s_dg = Some R_dg /\ call_checkA E_dg Pre_da s_dg R_dg (map la_state Posts_da) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_dg0 : axst := Eval vm_compute in T_pure Pre_da E_dg s_dg R_dg P_da.
Definition T_dg : axst := Eval vm_compute in ax_setX (optAp (apply_axforms T_dg0 [AXSelect sel_da; AXMerge 0])) (X_body pDco pKco).
Goal shape T_dg = shape XA /\ lvs T_dg = [(hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition F_main : list cell := Eval vm_compute in List.filter (fun c => negb (sv_eqb (c_off c) (SLit (-136)))) F_cells.
Definition objs_face (cur hp : sv) (co rp tr mi fv mm sg ts : sobj) (ofcells fcells txt : list cell) (datas : list sobj) (tail : list sobj) : list sobj := ltac2:(tb__ "0|1|
S2SdS0SdS96S0SdS98S2S10S9eVfcells;A3A1S0SdS97S4SdA1M0A3A3A3S2SdSe9S2SdS0SdS95S2S10S48Vofcells;A3A1G0A3S2SdS9cSdcVhp;Vco;Vrp;Vtr;Vmi;Vfv;Vmm;Vsg;Vts;AaS2SdS0SdSdbS0SdSc8Vcur;A1S0SdSc7S0SdS19Sd0SeZ0A1Sd1Vtxt;S12A5G0A3A3A3A3S2SdVdatas;Vtail;A3A3A3A3A3A3").

Definition FCUT (pc : Z) (regs : list (nat * sv)) (cur : sv) (co rp tr mi fv mm sg ts : sobj) (ofcells fcells : list cell) (datas tail : list sobj)
                (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
SeaS16Vpc;ScaVregs;A1Sc9S15S6ScA1S79Vcur;S94Vco;Vrp;Vtr;Vmi;Vfv;Vmm;Vsg;Vts;Vofcells;Vfcells;S4S10A1Vdatas;Vtail;AfVfacts;Sc6S7A9VX;A2").

Definition coP : sobj := ltac2:(tb__ "0|0|
S9bS7cS7eS7dA3").
Definition rpP : sobj := V752e rp_d rp_k. Definition trP : sobj := V784e tr_d tr_k. Definition tsP : sobj := V816 ts_d ts_k.
Definition miP : sobj := ltac2:(tb__ "0|0|
S8dS9fS81Sa0A3"). Definition fvP : sobj := ltac2:(tb__ "0|0|
S92S8bS8fS8cA3"). Definition mmP : sobj := ltac2:(tb__ "0|0|
S99S82Sb0S7fA3"). Definition sgP : sobj := ltac2:(tb__ "0|0|
S9aS84Sb3S80A3").
Definition datasP : list sobj := ltac2:(tb__ "0|0|
S93Sc3Sc4S9fSa0S8bS8cS82S7fS84S80S7cS7dS87S83S88S85S89S86A12").

Definition face_facts (cur : sv) : list sprop := ltac2:(tb__ "0|0|
S2SbS0SbS49S7eA1S4SbA1A3Sa4Vcur;S7eVcur;S7cS7dP12fA6A3").

Definition lregsF : list (nat * sv) := ltac2:(tb__ "0|1|
S2S5S1ScA2M0SadS0G0S3S1ScU5S8aZ2d0A1A4S0G0S3S1ScU6SebA4S0G0S3S1ScU7S8aZ38A1A4S4G0A1A3A3A3A3").
Definition RW : axst := ltac2:(tb__ "0|3|
S25Sf1S2S5S1ScA2M0S76S0G0S3S1ScUaS8aZ70A1A4S0G0S3S1ScUbSeZ3A1M1A4S0G0S3S1ScUcSdaA4S0G0S3S1ScU15SccS1eA1A4S0G0S3S1ScU16S7cA4S0G0S3S1ScU17Sc0A4S0G0S3S1ScU18Sc0A4S0G0S3S1ScU19S8aZ218A1A4S0G0S3S1ScU1aS91Z43A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3S1eS26S30S32S77S3dS27S31S33S2S10S8eS0S10SddN88SdaA2S4S10A1M2A3A3G2S73S4SdA1S2SbS0SbS13SbaS7eG1A3S4SbA1A3S34S1eA1A3Sa9S7cS7dA2A11").
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
S0Sd5Sd7U1Z40A2S0Sd5Sd9S7bVvi;Vdi;A2A1S0Sd5Sd8U0A1S0Sd5Sd7Vvi;SfaVoff;A1A2S4Sd5A1A3A3A3A3").
Definition E_mi0 : axst := Eval vm_compute in leaf_at RW vr_entry 0.

Definition vr_need (e : Z) (w n : sv) : list sprop := ltac2:(tb__ "0|3|
S0SbSfVw;Vn;A2S0SbSfSbfVe;Vw;A2M0SbfVe;Vn;A2M1A2S0SbSfG1SeSe0A1M2A2S0SbSfG0G2A2S0SbSfVw;SeSe1A1A2S4SbA1A3A3A3A3A3").
Definition want_of (E : axst) : sv := ltac2:(tb__ "0|0|
Sf5ScUbS1aSd3VE;A1A1SeZ0A1A4").

Definition E_mi : axst := Eval vm_compute in let E := optAp (apply_axforms E_mi0 (xf_vr 15 496)) in ax_add_facts (vr_need 12 (want_of E) (NMI pA)) E.
Definition s_mi : wsub := ltac2:(tb__ "0|1|
S0S5SbdScA2M0S3SbdScP3bS4eS7eA1A4S0G0S3SbdScP13S11Sb9SdeSeZ40A1A3A4Se5PaSd3S66A1Sd3Sf2A1A3A3A3").
Definition R_mi : list sobj := Eval vm_compute in optR (entails_frA E_mi VN.Pre_vr s_mi).
Goal entails_frA E_mi VN.Pre_vr s_mi = Some R_mi /\ call_checkPA E_mi VN.Pre_vr s_mi R_mi (map fst PD_vn) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition X_face (dmi dfv dmm dsg dco drp dtr dts kmi kfv kmm ksg kco krp ktr kts : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S0S5ScScA2S3ScScSc0SeZ0A1A4SaaSc3Vdmi;Vdfv;Vdmm;Vdsg;Vdco;Vdrp;Vdtr;Vdts;Sc4Vkmi;Vkfv;Vkmm;Vksg;Vkco;Vkrp;Vktr;Vkts;A12A3").
Definition XkeepF (d : sv) (X : list (sv * sv)) : list (sv * sv) := ltac2:(tb__ "0|1|
Sf9S5ScScA2M0G0S9S1bS8ScScR1A3Vd;A2A1Lr;VX;A3").
Definition T_mik0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_mi s_mi R_mi VN.P_keep (XkeepF mi_d (X_body pDco pKco)).
Definition T_mif0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_mi s_mi R_mi VN.P_fail (XkeepF mi_d (X_body pDco pKco)).
Definition T_mig0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_mi s_mi R_mi VN.P_grown (XkeepF mi_d (X_body pDco pKco)).
Definition T_mik : axst := Eval vm_compute in optAp (apply_axforms T_mik0 (xf_backV 14 28 496)).
Definition T_mif : axst := Eval vm_compute in optAp (apply_axforms T_mif0 (xf_backV 14 28 496)).
Definition T_mig : axst := Eval vm_compute in optAp (apply_axforms T_mig0 (xf_backV 14 28 496)).
Goal shape T_mik = shape RW /\ shape T_mif = shape RW. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition pDmi : sv := SVar 307. Definition pKmi : sv := SVar 308.
Definition vr_ret_mi : Z := 0x9f49c.
Definition regsRW (ra a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1ScA2M0S3S1ScU2SdfSecA1M1A4S0G0S3S1ScU8S14PaA1A4S0G0S3S1ScU9G1A4S0G0S3S1ScU1Vra;A4S0G0S3S1ScUaVa0;A4S0G0S3S1ScU12S8aZ1f8A1A4S0G0S3S1ScU13S91Z3fA1A4S0G0S3S1ScU14S91Z0A1A4S0G0S3S1ScU15S8aZ1f0A1A4S0G0S3S1ScU17Sc0A4S0G0S3S1ScU18Sc0A4S0G0S3S1ScU19S8aZ218A1A4S0G0S3S1ScU1aS91Z43A1A4S0G0S3S1ScU1bSeZ3A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition datasMI (dmi kmi : sv) : list sobj := ltac2:(tb__ "0|0|
S93Sc3Sc4Vdmi;Vkmi;S8bS8cS82S7fS84S80S7cS7dS87S83S88S85S89S86A12").
Definition mi_facts (dmi kmi : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S2SbS0SbSfS11Sb9S81SeZ3A1A3Vkmi;A2S0SbSfSeSe6A1Vdmi;A2S0SbSfS11Sb9SbfZcM0S81A2SeZ24A1A3SbfG0Vkmi;A2A2S4SbA1A3A3A3S90Vdmi;Vkmi;G0Vdv;A4A3").

Definition co_live : sprop := ltac2:(tb__ "0|0|
SfSeSe6A1S7cA2").
Definition JR_mi : axst := ltac2:(tb__ "0|2|
S25Se7S2S5S1ScA2M0S47SeS5eA1SeZ1A1A2S0G0S3S1ScU16S7cA4S4G0A1A3A3S1eS26S30S32S8dS1cS81S1dA3S3dS27S31S33S2S10S8eS0S10SddN88SdaA2S4S10A1M1A3A3G1S3eS1cS1dA2S0SdSe2Sc2Z4Z5G1S12A5S4SdA1A3S2SbS0SbS13SbaS7eSeZ3A1A3S0SbS23S4SbA1A3A3S2SbS3fS1cS1dP133A3S34S1eA1A3A3S22S1cS8bS82S84S7cS87S88S89S1dS8cS7fS80S7dS83S85S86A10A11").
Definition JF_mi : axst := ltac2:(tb__ "0|2|
S25Se7S2S5S1ScA2M0S47SeS5eA1SeZ0A1A2S0G0S3S1ScU16S7cA4S4G0A1A3A3S1eS26S30S32S8dS1cS81S1dA3S3dS27S31S33S2S10S8eS0S10SddN88SdaA2S4S10A1M1A3A3G1S3eS1cS1dA2S4SdA1S2SbS0SbS13SbaS7eSeZ3A1A3S0SbS23S0SbSfS81S1dA2S4SbA1A3A3A3S2SbS90S1cS1dZcP133A4S34S1eA1A3A3S22S1cS8bS82S84S7cS87S88S89S1dS8cS7fS80S7dS83S85S86A10A11").
Definition T_miks : axst := ltac2:(tb__ "0|0|
Se8S0SbSfSeSe6A1S9fA2S0SbS23S4SbA1A3A3S70A2").
Definition T_migs : axst := ltac2:(tb__ "0|0|
Se8S0SbS23S4SbA1A3S6fA2").
Definition T_mifs : axst := ltac2:(tb__ "0|0|
Se8S0SbS23S4SbA1A3S6eA2").
Definition reopen45 (A : axst) : axst := ltac2:(tb__ "0|0|
Se3VA;Sd4VA;A1Sc2Z4Z5A5").
Goal map (fun L => leaf_matches1A NPH L JR_mi) [reopen45 T_miks; reopen45 T_migs] = [true; true] /\ leaf_matches1A NPH T_mifs JF_mi = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Goal lvs JR_mi = [(hf_C36, RsCut)] /\ lvs JF_mi = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition pR : sv := SVar 309.
Definition done36 : sv := SAlu ALU_SUB (SLit 36) pR.
Definition dstmi (dmi : sv) : sv := ltac2:(tb__ "0|0|
S11Sb9Vdmi;S18SbcS81SeZcA1A3A3").
Definition c36_facts : list sprop := ltac2:(tb__ "0|1|
S0SbSfSeZ1A1S4aA2S0SbSfS4aSeZ24A1M0A2S0SbSfG0SbfZcS7dA2A2S4SbA1A3A3A3").
Definition C36 : axst := ltac2:(tb__ "0|4|
S25SefS2S5S1ScA2M0S47S14P191A1S11Sb9S55S74S1cA1A3M1A2S0G0S3S1ScU6SebA4S0G0S3S1ScUbS11Sb9S55S7cA3M2A4S0G0S3S1ScUcS4aA4S0G0S3S1ScUdG1A4S0G0S3S1ScU16G2A4S4G0A1A3A3A3A3A3A3S1eS26S30S32S8dS1cS81S1dA3S3dS27S31S33S2S10S8eS0S10SddN88SdaA2S4S10A1M3A3A3G3S3eS1cS1dA2S0SdSe2Sc2Z4Z5G3S12A5S4SdA1A3S2SbS0SbS13SbaS7eSeZ3A1A3S0SbS23S4SbA1A3A3S2SbS72S2SbS3fS1cS1dP133A3S34S1eA1A3A3A3S22S1cS8bS82S84S7cS87S88S89S1dS8cS7fS80S7dS83S85S86A10A11").
Goal leaf_matches1A NPH (leaf_at JR_mi hf_C36 0) C36 = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs C36 = [(hf_C36, RsCut); (hf_RJ, RsCut); (hf_C36, RsCut); (hf_RJ, RsCut)]
  /\ map (fun L => leaf_matches1A NPH L C36) (leavesA_at FUEL_hf cutpcs_hf C36 hf_C36) = [true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition RJ : axst := ltac2:(tb__ "0|2|
S25Sf0S2S5S1ScA2M0S47S14P191A1S14P19aA1A2S0G0S3S1ScU6SebA4S4G0A1A3A3S1eS26S30S32S8dS1cS81S1dA3S3dS27S31S33S2S10S8eS0S10SddN88SdaA2S4S10A1M1A3A3G1S3eS1cS1dA2S0SdSe2Sc2Z4Z5G1S12A5S4SdA1A3S2SbS0SbS13SbaS7eSeZ3A1A3S0SbS23S4SbA1A3A3S2SbS3fS1cS1dP133A3S34S1eA1A3A3S22S1cS8bS82S84S7cS87S88S89S1dS8cS7fS80S7dS83S85S86A10A11").
Goal map (fun L => leaf_matches1A NPH L RJ) (leavesA_at FUEL_hf cutpcs_hf C36 hf_RJ) = [true; true]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs RJ = [(vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_fv0 : axst := Eval vm_compute in leaf_at RJ vr_entry 0.
Definition sh_fv : sobj := Eval vm_compute in last (ss_objs (ax_S E_fv0)) O_Wf.
Definition objs_fv0 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S E_fv0)).
Goal sh_fv = shobj hG 4 5 (ob_cells sh_fv) DUnknown /\ local_ok (ob_cells sh_fv) DUnknown 4 5 (32, 4) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E_fv1 : axst := Eval vm_compute in shadow_release_stateA E_fv0 objs_fv0 160 [(32, 4)].
Definition E_fv : axst := Eval vm_compute in let E := optAp (apply_axforms E_fv1 (xf_vr 16 528)) in ax_add_facts (vr_need 4 (want_of E) (NFV pA)) E.
Definition s_fv : wsub := ltac2:(tb__ "0|1|
S0S5SbdScA2M0S3SbdScP3bS4dS7eA1A4S0G0S3SbdScP13S11Sb9SdeSeZ40A1A3A4Se5PaSd3S64A1Sd3Sf2A1A3A3A3").
Definition R_fv : list sobj := Eval vm_compute in optR (entails_frA E_fv VN.Pre_vr s_fv).
Goal entails_frA E_fv VN.Pre_vr s_fv = Some R_fv /\ call_checkPA E_fv VN.Pre_vr s_fv R_fv (map fst PD_vn) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition XF1 : list (sv * sv) := ltac2:(tb__ "0|0|
S0S5ScScA2Se4Pa0S3SbeSbeZ20Z4A4A2S22S1cS8bS82S84S7cS87S88S89S1dS8cS7fS80S7dS83S85S86A10A3").
Definition T_fvk0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_fv s_fv R_fv VN.P_keep (XkeepF fv_d XF1).
Definition T_fvf0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_fv s_fv R_fv VN.P_fail (XkeepF fv_d XF1).
Definition T_fvg0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_fv s_fv R_fv VN.P_grown (XkeepF fv_d XF1).
Definition T_fvk : axst := Eval vm_compute in optAp (apply_axforms T_fvk0 (xf_backV 15 29 528)).
Definition T_fvf : axst := Eval vm_compute in optAp (apply_axforms T_fvf0 (xf_backV 15 29 528)).
Definition T_fvg : axst := Eval vm_compute in optAp (apply_axforms T_fvg0 (xf_backV 15 29 528)).

Definition pDfv : sv := SVar 314. Definition pKfv : sv := SVar 315.
Definition vr_ret_fv : Z := 0xa0094.
Definition regsF2 (ra a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1ScA2M0S3S1ScU2SdfSecA1M1A4S0G0S3S1ScU8S14PaA1A4S0G0S3S1ScU9G1A4S0G0S3S1ScU1Vra;A4S0G0S3S1ScUaVa0;A4S0G0S3S1ScU12S8aZ210A1A4S0G0S3S1ScU13Sa6Z20A1A4S0G0S3S1ScU14S91Z0A1A4S0G0S3S1ScU15S8aZ1f0A1A4S0G0S3S1ScU17Sc0A4S0G0S3S1ScU18Sc0A4S0G0S3S1ScU19S8aZ218A1A4S0G0S3S1ScU1aS91Z43A1A4S0G0S3S1ScU1bSeZ3A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition miP3 : sobj := ltac2:(tb__ "0|0|
S8dS1cS11Sb9S81SeZ3A1A3S1dA3").
Definition fvcell : list cell := [c4 32 (SLit 3)].
Definition datasFV (dfv kfv : sv) : list sobj := ltac2:(tb__ "0|0|
S93Sc3Sc4S1cS1dVdfv;Vkfv;S82S7fS84S80S7cS7dS87S83S88S85S89S86A12").
Definition XFV (dfv kfv : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S0S5ScScA2Se4Pa0S3SbeSbeZ20Z4A4A2S22S1cVdfv;S82S84S7cS87S88S89S1dVkfv;S7fS80S7dS83S85S86A10A3").
Definition fv_facts (dfv kfv : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S2SbS0SbSfS11Sb9S8fSeZ1A1A3Vkfv;A2S0SbSfSeSe6A1Vdfv;A2S0SbSfS11Sb9SbfZ4M0S8fA2SeG0A1A3SbfG0Vkfv;A2A2S4SbA1A3A3A3S90Vdfv;Vkfv;G0Vdv;A4A3").
Definition rawF : list sprop := ltac2:(tb__ "0|0|
S2SbS0SbS13SbaS7eSeZ3A1A3S0SbS23S4SbA1A3A3S2SbS3fS1cS1dP133A3S34S1eA1A3A3").
Definition JR_fv : axst := ltac2:(tb__ "0|0|
S25Se7S5bSeS5dA1SeZ1A1A2S1eS26S30S32S57S92S21S8fS1fA3S27S31S33S2S10S8eS0S10SddN88SdaA2S4S10A1A3A3S56S53S21S1fA2S4SdA1S2SbS75S21S1fP13aA3S59A3S71S21S1fA2A11").

Definition JF_fv : axst := ltac2:(tb__ "0|2|
S25Se7S5bSeS5dA1SeZ0A1A2S1eS26S30S32S57S92S21S8fS1fA3S27S31S33S2S10S8eS0S10SddN88SdaA2S4S10A1M0A3A3S56S53S21S1fA2S0SdSe2Sc2Z4M1Z5G0S12A5S4SdA1A3S2SbS0SbSfS8fS1fA2S4SbA1A3S2SbS90S21S1fG1P13aA4S59A3A3S22S1cS21S82S84S7cS87S88S89S1dS1fS7fS80S7dS83S85S86A10A11").
Definition reopen45X (A : axst) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
Se3VA;VX;Sc2Z4Z5A5").
Definition T_fvks : axst := ltac2:(tb__ "0|0|
Se8S0SbSfSeSe6A1S8bA2S4SbA1A3S6dA2").
Goal map (fun L => leaf_matches1A NPH L JR_fv) [T_fvks; T_fvg] = [true; true]
  /\ leaf_matches1A NPH (reopen45X T_fvf (X_face pDmi fv_d mm_d sg_d pDco rp_d tr_d ts_d pKmi fv_k mm_k sg_k pKco rp_k tr_k ts_k)) JF_fv = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal lvs JR_fv = [(memcpy_pc, RsCut)] /\ lvs JF_fv = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_mc0 : axst := Eval vm_compute in leaf_at JR_fv memcpy_pc 0.
Definition a0_mc : sv := Eval vm_compute in nth 10 (ss_regs (ax_S E_mc0)) (SLit 0).
Definition xf_mcf : list axform := ltac2:(tb__ "0|4|
S0Sd5Sd6U1SeZ20M0A1A2S0Sd5Sd6U2M1SeZ24A1A2S0Sd5Sd7G1G0A2S0Sd5Sd6U1fSbfZ4M2S8fA2M3A2S0Sd5Sd6U20S11Sb9G3SeG2A1A3A2S4Sd5A1A3A3A3A3A3").
Definition E_mc1 : axst := Eval vm_compute in optAp (apply_axforms E_mc0 xf_mcf).
Definition E_mc : axst := Eval vm_compute in reshapeA E_mc1 32 (mkObj a0_mc (SLit 0) (SLit 4) [] DUnknown).
Definition Pre_mc : axst := Pre_memcpy memcpy_pc.
Definition L_mc1 : axst := L_memcpy (ae_ret_asan_memcpy AE_A).
Definition s_mcf : wsub := ltac2:(tb__ "0|2|
S0S5SbdScA2M0S3SbdScP35S21A4S0G0S3SbdScP36SbfZ4M1S1fA2A4S0G0S3SbdScP37Sa6Z20A1A4S0G0S3SbdScP38SeG1A1A4S0G0S3SbdScSf8SdeA4Se5PaSd3S65A1Sd3S6cA1A3A3A3A3A3A3").
Definition R_mcf : list sobj := Eval vm_compute in optR (entails_frA E_mc Pre_mc s_mcf).
Goal entails_frA E_mc Pre_mc s_mcf = Some R_mcf /\ call_checkPA E_mc Pre_mc s_mcf R_mcf [L_mc1; L_mc1] = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_mc0 : axst := Eval vm_compute in T_afterA Pre_mc E_mc s_mcf R_mcf L_mc1.

Definition sel_mcf : list nat := ltac2:(tb__ "0|1|
S2S1S0S1U0S0S1U5S0S1U2S0S1U6S0S1U7S0S1U3S0S1U4S0S1U8S4S1A1M0A3A3A3A3A3A3A3A3S2S1Sf6U9U11A2S0S1U1aS0S1U1bS0S1U1cS0S1U1dS0S1U1eS0S1U1fS0S1U20S0S1U1S0S1U21S0S1U22S0S1U23S0S1U24S0S1U25S0S1U26S0S1U27G0A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition T_mc1 : axst := Eval vm_compute in reshapeA T_mc0 1 (mkObj pDfv (kb 4 fv_c) (SAlu ALU_ADD (kb 4 fv_c) (SLit 4)) [] DUnknown).
Definition T_mcq : axst := Eval vm_compute in optAp (apply_axforms T_mc1 [AXRebase 2; AXSelect sel_mcf; AXMerge 1; AXMerge 1; AXMerge 29; AXMerge 29]).
Goal shape T_mcq = shape JR_fv /\ lvs T_mcq = [(vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_mm0 : axst := Eval vm_compute in leaf_at T_mcq vr_entry 0.
Definition E_mm : axst := Eval vm_compute in let E := optAp (apply_axforms E_mm0 (xf_vr 17 560)) in ax_add_facts (vr_need 4 (want_of E) (NMM pA)) E.
Definition s_mm : wsub := ltac2:(tb__ "0|1|
S0S5SbdScA2M0S3SbdScP3bS4fS7eA1A4S0G0S3SbdScP13S11Sb9SdeSeZ40A1A3A4Se5PaSd3S67A1Sd3Sf2A1A3A3A3").
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
S13SbbS17SaQ20Ve;A3SeZ0A1A3").
Definition datasQ : list sobj := ltac2:(tb__ "0|0|
S93Sc3Sc4S37S2aS36S29S38S2bS3aS2dS35S24S39S2cS3bS2eS3cS2fA12").
Definition XQ : list (sv * sv) := ltac2:(tb__ "0|0|
S22S37S36S38S3aS35S39S3bS3cS2aS29S2bS2dS24S2cS2eS2fA10").
Definition q_vfacts : list sprop := ltac2:(tb__ "0|2|
S2SbSc5S37S41S2aZcM0P141A5S2SbSc5S36S40S29Z4M1P144A5S2SbSc5S38S42S2bG1P147A5S2SbSc5S3aS43S2dG1P14aA5S2SbS90S35S24G0P14dA4S2SbS0SbSfS20S24A2S4SbA1A3S2SbS90S39S2cG1P150A4S2SbS90S3bS2eG1P152A4Sc5S3cSeZ0A1S2fZ1P154A5A3A3A3A3A3A3A3A3").
Definition q_base : list sprop := ltac2:(tb__ "0|0|
S2SbS0SbSfS94SeZ1A1A2S0SbSfScfS28A2S0SbSfS28ScbA2S4SbA1A3A3A3S2SbSabSacA3A3").

Definition CMI (a : sv) : sv := ltac2:(tb__ "0|0|
S11Sb9S81SbfZ3Va;A2A3").
Definition CFV (a : sv) : sv := SAlu ALU_ADD fv_c a.
Definition CMM (a : sv) : sv := SAlu ALU_ADD mm_c a.
Definition CSG (a : sv) : sv := SAlu ALU_ADD sg_c a.
Definition q_acct : list sprop := ltac2:(tb__ "0|0|
S0SbS49S20A1S0SbSb1S20S28A2S0SbSfS41S60S20A1A2S0SbSfS40S5fS20A1A2S0SbSfS42S61S20A1A2S0SbSfS43S62S20A1A2S4SbA1A3A3A3A3A3A3").
Definition regsE : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1ScA2M0S3S1ScU2SdfSecA1M1A4S0G0S3S1ScU8S14PaA1A4S0G0S3S1ScU9G1A4S0G0S3S1ScU17Sc0A4S0G0S3S1ScU18Sc0A4S4G0A1A3A3A3A3A3").
Definition EC (err : sv) (facts : list sprop) : axst := ltac2:(tb__ "0|1|
SeaS16SedScaS5aA1Sc9S15S6ScA1S2SdS0SdS96S0SdS98S9eA1S0SdS97S4SdA1M0A3A3A3S2SdSe9S2SdS0SdS95S48A1G0A3S2SdS9cVerr;S94S9bS35S20S24A3Sa1S39S2cA2Sa2S3bS2eA2S8dS37S41S2aA3S92S36S40S29A3S99S38S42S2bA3S9aS3aS43S2dA3Sa3S3cS2fA2AaS2SdS0SdSdbS0SdSc8S28A1S0SdSc7S0SdScdG0A3A3A3A3S54A3A3A3A3A3Vfacts;Sc6S7A9S51A2").
Definition C_Eo : axst := ltac2:(tb__ "0|0|
S4bSdcS2SbS58S2SbS46S45A3A3A2").
Definition C_Ef : axst := ltac2:(tb__ "0|0|
S4bS44S2SbS0SbS50S44A1S4SbA1A3S2SbS46S45A3A3A2").
Definition tvQ : list (sv * sv) := ltac2:(tb__ "0|0|
Sb8Sc3Sc4S37S2aS36S29S38S2bS3aS2dS35S24S39S2cS3bS2eS3cS2fA12").
Definition ndEo : ndesc := ltac2:(tb__ "0|0|
Sf4S5cS9dS52S28S20S2aS29S2bS2dS24S2cS2eS2fAaSf3A4").
Definition ndEf : ndesc := ltac2:(tb__ "0|0|
Sf4S5cS9dS0Sd2SceSa5S28A2S4Sd2A1A3Sf3A4").

Definition ECsh (err : sv) (facts : list sprop) (sh : list sobj) : axst := ltac2:(tb__ "0|1|
SeaS16SedScaS5aA1Sc9S15S6ScA1S2SdS0SdS96S0SdS98S9eA1S0SdS97S4SdA1M0A3A3A3S2SdSe9S2SdS0SdS95S48A1G0A3S2SdS9cVerr;S94S9bS35S20S24A3Sa1S39S2cA2Sa2S3bS2eA2S8dS37S41S2aA3S92S36S40S29A3S99S38S42S2bA3S9aS3aS43S2dA3Sa3S3cS2fA2AaS2SdS0SdSdbS0SdSc8S28A1S0SdSc7S0SdScdG0A3A3A3A3S2SdS54Vsh;A3A3A3A3A3A3Vfacts;Sc6S7A9S51A2").
Definition XEo4 : axst := ltac2:(tb__ "0|0|
S4cSdcS2SbS58S2SbS46S45A3A3S0SdSe2Sc2Z4Z5S4S10A1S12A5S4SdA1A3A3").
Definition XEf4 : axst := ltac2:(tb__ "0|0|
S4cS44S2SbS0SbS50S44A1S4SbA1A3S2SbS46S45A3A3S0SdSe2Sc2Z4Z5S4S10A1S12A5S4SdA1A3A3").
Goal map (fun L => leaf_matches1A NPH L C_Eo) (leaves_at2 [T_dg] hf_EPI) = [true]
  /\ map (fun L => leaf_matches1A NPH L C_Ef) (leaves_at2 [JF_co; K; JF_mi] hf_EPI) = [true; true; true; true; true; true]
  /\ map (fun L => leaf_matches1A NPH L XEf4) (leaves_at2 [JF_fv] hf_EPI) = [true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
