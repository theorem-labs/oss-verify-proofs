(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "true"; "bool"; "prod"; "Some"; "option"; "list"; "app"; "negb"; "S"; "fst"; "None"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "cell"; "mkObj"; "ss_objs"; "DUnknown"; "sprop"; "mkCell"; "obj_wf"; "ss_facts"; "sstate"; "DZero"; "SAlu"; "SVar"; "ob_base"; "ob_hi"; "ob_lo"; "mkSS"; "ob_dflt"; "sprop_below"; "ss_next"; "ss_pc"; "sv_eqb"; "FcsrFrm0"; "c_off"; "ob_cells"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "swf"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "apply_axforms"; "AXMerge"; "AXSelect"; "AXRebase"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "axwf"; "ax_X"; "leafA"; "has_facts"; "la_state"; "entailsA"; "sym_runA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one"; "nx"; "E_lo"; "vF"; "s_lo"; "E_sm0"; "T_sm1"; "s_sm"; "C3"; "C_al"; "C_body"; "C_ms1"; "E_lo2"; "Pre_sm"; "R_lo"; "T_err0"; "runF"; "shapes"; "showL"; "C0"; "C1"; "C_pro"; "C_pro0"; "E_lo1"; "E_ms"; "L_alF"; "R_sm"; "T_err"; "T_suc"; "Xk_lo"; "ax_tidy"; "body_shape"; "glob_shape"; "optL"; "BAD"; "C_ms"; "L_al"; "L_sm"; "T_err1"; "T_sm"; "T_suc0"; "X_al"; "X_rel"; "cells_rel"; "cfg_obj"; "gF"; "hp"; "lo_entry"; "objs_rel"; "objs_sm1"; "out_mid"; "pF"; "pc_al"; "pc_ms"; "s_al"; "sm2_pc"; "vCFG"; "vFL"; "C2"; "C4"; "E_lo0"; "FUEL_fz"; "Fx"; "cfg_cellsE"; "cfg_cellsR"; "cps_fz"; "fnodup"; "free_pc"; "junk_regs"; "mentions"; "nobj"; "oBack"; "oH"; "oM0"; "pAR"; "pc_L"; "pc_adA"; "pc_adB"; "pc_fa"; "pc_rel"; "pc_sx"; "sel_sm"; "xf_al1"; "xf_al2"; "xf_al3"; "xf_lo"; "xf_ms"; "xfb_err"; "xfb_ms"; "xfb_ok"; "xnodup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_glue"; "vH"; "WIN"; "vG10"; "vDN"; "DNt"; "G10t"; "al_facts"; "hS"; "recell_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one.LD"; "Pre_lo"; "NP"; "@Stdlib.Lists.List"; "filter"; "nth_error"; "existsb"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "add"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "seq"; "skipn"; "nth"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "ax_setX"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "of_nat"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "vDAT"; "vDp"; "vLEN"; "fz_facts"; "Pre_fz"; "X_lits"; "spm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "GOT_HI"; "GOT_LO"; "RTC_HI"; "RTC_LO"; "mkA"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.FZAddr"; "D_FZ"; "fz_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA";
"entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "T_afterA"; "@Corelib.Init.Nat"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one.LI"; "PD_lo"; "P_err"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sprop_vars_all"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjZeroFillB"; "zero_fill_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "frame_open_stateA"; "local_ok"; "shadow_release_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "fs_frame_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "flagbyte_obj"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_defs Lib_load_obj_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_fuzz_iface2 Lib_fuzz_one_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjZeroFillB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import FZAddr.
Module LD. Include Lib_load_obj_defs. End LD. Module LI. Include Lib_load_obj_iface. End LI.

Definition sm2_pc : Z := 0x47da0.
Definition pc_ms : Z := 0x9bd8c.
Definition lo_entry : Z := 0x8cc90.
Definition free_pc : Z := 0x5e1f0.
Definition pc_al : Z := 0x9bc1c.
Definition pc_sx : Z := 0x9bddc.
Definition pc_rel : Z := 0x9bf44.
Definition pc_adA : Z := 0x8cb34.
Definition pc_L : Z := 0x8cb50.
Definition pc_adB : Z := 0x8cb34.
Definition pc_fa : Z := 0x8cba4.
Definition cps_fz : list Z := ltac2:(tb__ "0|0|
S0S45S92S0S45S91S0S45S93S0S45S94S0S45S96S0S45S95S0S45S7aS0S45S7dS0S45S7bS0S45S75S0S45S89S0S45Sd2S3S45A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition FUEL_fz : nat := 4000%nat.
Definition BAD : axst := ltac2:(tb__ "0|1|
ScfS23Z0S3S11A1M0G0S29SeS11A1S3S13A1S3S18A1P1SfA9S3S6S11S11A2A1A2").
Definition optL (x : option axst) : axst := match x with Some s => s | None => BAD end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition runF (S : axst) : list leafA := ltac2:(tb__ "0|1|
S8S9S40A1M0A1G0Lx;S44Sd0S83S87VS;S4A5G0R1Lls;S3S40A1X8x2").
Definition showL (ls : list leafA) := map show_leafA ls.
Definition leafF (ls : list leafA) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
SbbS3bVk;Sb7S40S3bS42Sb0S40S40Sb6S27S3cS42R1A1A1A1Vpc;A2LL;Vls;A3A4S68A4").
Definition shapes (A : axst) : ltac2:(tb__ "0|0|
S9S6S6S11S11A2S11A2A1") := ltac2:(tb__ "0|1|
Sb7S13S6S6S11S11A2M0S11A2S13S2G0S11S2S11S11S20R1A1S22R1A1A4S21R1A1A4Lo;S16S3cVA;A1A1A4").
Definition nobj (A : axst) : nat := length (ss_objs (ax_S A)).
Definition Fx (A : axst) : list sprop := ss_facts (ax_S A).
Definition nx (A : axst) : positive := ss_next (ax_S A).
Definition hp (k : Z) : sv := ltac2:(tb__ "0|0|
S1eSbcSa1S12Vk;A1A3").
Definition dropX (b : sv) (A : axst) : axst := ltac2:(tb__ "0|1|
SbeVA;Sb0S6S11S11A2M0G0SbS28SdS11S11R1A3Vb;A2A1Lr;S3fVA;A1A3A2").
Definition mentions (v : positive) (f : sprop) : bool := ltac2:(tb__ "0|0|
SbSe1S46SbSc0R1Vv;A2A1Lw;Vf;A2A1").
Definition dropV (vs : list positive) (A : axst) : axst := ltac2:(tb__ "0|0|
SbdVA;Sb0S18S18SbSb2S46S46S8bR1R2A2Lv;Vvs;A3A1Lf;S1bS3cVA;A1A1A3A2").
Definition keep_below (n : positive) (A : axst) : axst := ltac2:(tb__ "0|0|
SbdVA;Sb0S18S25Vn;A1S1bS3cVA;A1A1A3A2").

Fixpoint junk_regs (l : list nat) (n : positive) (rs : list sv) : list sv :=
  match l with [] => rs | r :: l' => junk_regs l' (Pos.succ n) (list_set rs r (SVar n)) end.
Definition junkRN (l : list nat) (A : axst) : axst := ltac2:(tb__ "0|1|
S3cVA;A1S1cS3dVA;S23S27R1A1S8aVl;S26R1A1M0S2fR1A1A3S2dR1A1S2cR1A1S30R1A1S16R1A1S1bR1A1Sc1SdaSc2G0A1S10S1Vl;A2A2A1S2eR1A1A9A2TS;").
Definition upd_obj_at (A : axst) (i : nat) (f : sobj -> sobj) : axst := ltac2:(tb__ "0|2|
S3dVA;SacS3cVA;A1M0SaS13Sb8S13Vi;S16G0A1M1A3SaS13Sb7S13S13Vf;Sb8S13U1SbaS13Vi;G1A3A3A4SbaS13ScVi;A1G1A3A3A3A2A2").
Definition drop_cells_obj (offs : list Z) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S15S20Vo;A1S22Vo;A1S21Vo;A1Sb0S14S14SbSb2S45S45S28S2aR2A1S12R1A1A2Lz;Voffs;A3A1Lc;S2bVo;A1A3S24Vo;A1A5").
Definition nocells_obj (o : sobj) : sobj := ltac2:(tb__ "0|0|
S15S20Vo;A1S22Vo;A1S21Vo;A1S3S14A1S24Vo;A1A5").

Fixpoint xnodup (l : list (sv * sv)) : list (sv * sv) :=
  match l with [] => [] | x :: r => if existsb (fun y => sv_eqb (fst y) (fst x) && sv_eqb (snd y) (snd x)) r then xnodup r else x :: xnodup r end.
Fixpoint fnodup (l : list sprop) : list sprop :=
  match l with [] => [] | x :: r => if existsb (sprop_eqb x) r then fnodup r else x :: fnodup r end.
Definition ax_tidy (A : axst) : axst := ltac2:(tb__ "0|0|
SbdSbeVA;Sa0S3fVA;A1A1A2S88S1bS3cVA;A1A1A1A2").

Definition L_al : axst := Eval vm_compute in leafF (runF Pre_fz) pc_al 0.
Definition L_alF : axst := Eval vm_compute in ax_with_facts L_al (al_facts hS DNt G10t ++ ss_facts (ax_S L_al)).
Definition X_al : list (sv * sv) := ltac2:(tb__ "0|1|
SaS6S11S11A2M0S0G0S2S11S11Sc3Sc5A4S0G0S2S11S11Sc9Sd1A1S12Sd1A1A4S0G0S2S11S11S74Sb4Sa2A1A1S12Sb5Sa2Z120A2A1A4S3G0A1A3A3A3Sc8A3").
Definition C0 : axst := Eval vm_compute in
  let S := ax_S L_al in
  mkA (mkSS pc_al (setregs (ss_regs S) [(2%nat, vH)]) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S)
            (SPAlign 100 5 :: al_facts vH vDN vG10 ++ fz_facts) 103%positive false) X_al.
Definition s_al : wsub := ltac2:(tb__ "0|1|
S0S6S46S11A2M0S2S46S11P64Sa8A4S0G0S2S46S11P65Sa5A4S0G0S2S46S11P66Sa6A4S3G0A1A3A3A3").
Definition xf_al1 : list axform := ltac2:(tb__ "0|2|
S0S34S35U0M0S12N40A1A2S0S34S39U2M1A1S0S34S38S0S1G1S0S1G0S0S1U1S0S1U3S0S1U4S0S1U5S3S1A1A3A3A3A3A3A3A1S0S34S37G0A1S3S34A1A3A3A3A3").
Definition C1 : axst := Eval vm_compute in optL (apply_axforms C0 xf_al1).
Definition oM0 : sobj := ltac2:(tb__ "0|0|
S15S1fPaA1S1eSbcSc4S12N120A1A3S12N40A1S3S14A1S17A5").
Definition C2 : axst := Eval vm_compute in ax_setS C1 (reshape_obj_at (ax_S C1) 0 oM0).
Definition xf_al2 : list axform := ltac2:(tb__ "0|0|
S0S34S35U0Sa3A2S0S34S37U1A1S3S34A1A3A3").
Definition C3 : axst := Eval vm_compute in optL (apply_axforms C2 xf_al2).
Definition oBack : sobj := ltac2:(tb__ "0|0|
S15S1fPaA1S1eSbcSc4S12N120A1A3Sa3S3S14A1S17A5").
Definition oH : sobj := ltac2:(tb__ "0|0|
S15Sa1Sa4S12Ze0A1S3S14A1S17A5").
Definition C4 : axst := Eval vm_compute in ax_setS C3 (reshape_obj_at (ax_S C3) 0 oH).
Definition xf_al3 : list axform := ltac2:(tb__ "0|2|
S0S34S35U0M0S12Sb4Sa2A1A1A2S0S34S35U1M1S12Z0A1A2S0S34S38S0S1G1S0S1U2S0S1G0S0S1U3S0S1U4S0S1U5S0S1U6S3S1A1A3A3A3A3A3A3A3A1S3S34A1A3A3A3").
Definition C_al : axst := Eval vm_compute in optL (apply_axforms C4 xf_al3).

Lemma fz_checks_al : ltac2:(tb__ "0|e|
S33S32S9S6S45SaaA2M0A1S58S56Sc7A1A1S0G0S2S45SaaS7aSabA4S3G0A1A3A3S33S32S9S18A1S1bS3cS6aA1M1A1M2Sc6A3S33S32S3bSbdS6aSaS18Sa7Sa8Sa5Sa6A3G2A3M3A2S5fA3S33S32S5Sb3S18S25S26G1A1A1G3A3S4A3S33S32S5S3eS59A1S4A3S33S32S5S43S5fS59S7cA3S4A3S33S32S5Se0S7cSadA2S4A3S33S32S5SbfSadS47S5fA1A2S4A3S33S32S8S3bA1M4S36S59S98A2S7S3bS5aA2A3S33S32S8S13A1M5Sb1S13S16S3cS5aA1A1U0M6A3S7S13S15S1fPaA1M7S1eSbcSc4S12N120A1M8A3S12N40A1S0S14S19G8Z8S12Z0A1M9A3S3S14A1A3S17A5A2A3S33S32S5S1aS47S5aA1S8fA2S4A3S33S32G4S36S80S99A2S7S3bS4eA2A3S33S32G5Sb1S13S16S3cS4eA1A1G6A3S7S13S8dA2A3S33S32S5S1aS47S4eA1S8eA2S4A3S33S32S5S41Sc6S84S4eA1MaA2S4A3S33S32S5S41Sa7Sa1Sa4Sa3A3GaA2S4A3S33S32G4S36S81S9aA2S7S3bS4fA2A3S33S32S5S3eS4fA1S4A3S32S9S6S6S11S11A2MbS11A2McA1S57S4fA1S0GcS2GbS11S2S11S11Sa1S12Sb4Sa2A1A1MdA4G9A4S0GcS2GbS11S2S11S11Sa1G9A4S12Ze0A1A4S0GcS2GbS11S2S11S11Sa1Sa4A4GdA4S0GcS2GbS11S2S11S11G7Sa3A4G9A4S0GcS2GbS11S2S11S11Sc3G9A4Sc5A4S0GcS2GbS11S2S11S11G9S12SccA1A4S12ScbA1A4S0GcS2GbS11S2S11S11G9S12SceA1A4S12ScdA1A4S3GcA1A3A3A3A3A3A3A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition E_sm0 : axst := Eval vm_compute in leafF (runF C_al) sm2_pc 0.
Definition Pre_sm : axst := Pre_stack_malloc AE_A 2.
Definition L_sm : axst := L_stack_malloc AE_A 2.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S0S6S46S11A2S2S46S11Se9S12Sb4Sa2A1A1A4Sd3PaS3cS4bA1S3cS53A1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Definition T_sm : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.

Definition pF : positive := 113%positive.  Definition pFL : positive := 123%positive.  Definition gF : positive := 143%positive.
Definition vF : sv := SVar pF.  Definition vFL : sv := SVar pFL.
Definition fr_fz : list (sv * Z * sv) := ltac2:(tb__ "0|2|
S0S6S6S11S45A2M0S11A2M1S2G0S11S2S11S45S49Z2A4S7fA4S3G1A1A3").
Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
SaS1Sb9U0Vi;A2SaS1Sb9ScVi;A1M0SdbS8cVA;A1G0A2A2S0S1Vi;S3S1A1A3A3A3").
Definition sel_sm : list nat := Eval vm_compute in sel_last T_sm 3.
Definition T_sm1 : axst := Eval vm_compute in optL (apply_axforms T_sm [AXSelect sel_sm]).
Definition objs_sm1 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S T_sm1)).
Definition C_pro0 : axst := Eval vm_compute in frame_open_stateA T_sm1 objs_sm1 X_al pF 256.
Definition C_pro : axst := Eval vm_compute in ax_setX C_pro0 ((vF, SLit 0) :: ax_X C_pro0).

Definition X_rel : axst := Eval vm_compute in leafF (runF C_pro) pc_ms 0.
Definition cells_rel : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S X_rel)) oH).
Definition objs_rel : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_rel)).
Definition C_ms : axst := Eval vm_compute in shadow_release_stateA X_rel objs_rel pF [(32, 144)].

Lemma fz_checks_sm : ltac2:(tb__ "0|d|
S33S32S9S6S45SaaA2M0A1M1S58S56S4fA1A1S0G0S2S45SaaS7dSabA4S3G0A1M2A3A3S33S32S8S9S13A1M3A1Sd5S4bS53S4dA3S7G3S60A2A3S33S32S5Sd4S4bS53S4dS60S0S3bS6bS3S3bA1A3A5S4A3S33S32S5Sd8SadS4dA2S4A3S33S32S5SbfSadS47S4bA1A2S4A3S33S32S11SdfS4dPcA2S12Z100A1A3S33S32S3bSd9S53S4bS4dS60S6bA5S6dA3S33S32S8S3bA1S36S6dS0S34S38S97A1S3S34A1A3A2S7S3bS4cA2A3S33S32G3S16S3cS4cA1A1SaS13S77S0S13SeaS7fS0S14S19S12Z0M4A1M5Z1M6S12G6A1A3S3S14A1A3A2S3S13A1M7A3A3A3S33S32S9S6S11S11A2M8A1S3fS4cA1SaG8S6fS0G8S2S11S11S49S12Se8Z2A1M9A1A4S3G8A1A3A3A3S33S32S46S47S4cA1S73A3S33S32S3bSe4S4cS77S6fS79G9A5S5cA3S33S32S3bSbeS5cS0G8S2S11S11S49G5A4S3fS5cA1A3A2S5bA3S33S32S5S3eS5bA1S4A3S33S32G1S58S56S5bA1A1S0G0S2S45SaaS7bSabA4G2A3A3S33S32G3S16S3cS70A1A1SaS13S76S0S13Se7S73G4Z20MaS71S1dA5G7A3A3A3S33S32S5Sb3S6S45S45A2MbSe5S71S1dG4GaA4S0GbS2S45S45GaZ90A4S3GbA1A3McA3S4A3S32S3bSe6S70S76S79GcA4S69A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition vCFG : sv := SAlu ALU_ADD vF (SLit 32).
Definition cfg_obj (cells : list cell) (d : odefault) : sobj := ltac2:(tb__ "0|0|
S15S7eS12Z0A1S12Z90A1Vcells;Vd;A5").
Definition xf_ms : list axform := ltac2:(tb__ "0|0|
S0S34S35U1S12Z20A1A2S0S34S35U2S12Zb0A1A2S3S34A1A3A3").
Definition C_ms1 : axst := Eval vm_compute in optL (apply_axforms C_ms xf_ms).
Definition E_ms : axst := Eval vm_compute in ax_setS C_ms1 (reshape_obj_at (ax_S C_ms1) 2 (cfg_obj [] DUnknown)).

Definition xfb_ms : list axform := ltac2:(tb__ "0|0|
S0S34S38S0S1U0S0S1U7S0S1U8S0S1U9S0S1UaS0S1U2S0S1U1S0S1U3S0S1U4S0S1U5S0S1U6S3S1A1A3A3A3A3A3A3A3A3A3A3A3A1S3S34A1A3").
Definition C_body : axst := Eval vm_compute in ax_tidy (optL (apply_axforms E_ms xfb_ms)).
Definition body_shape : list (sv * sv * sv) := ltac2:(tb__ "0|5|
S0S6S6S11S11A2M0S11A2M1S2G0S11S2S11S11Sa1S12Sb4Sa2A1A1M2A4S12Z0A1M3A4S0G1S2G0S11S2S11S11Sa1G3A4S12Ze0A1A4S0G1S2G0S11S2S11S11Sa1Sa4A4G2A4S0G1S2G0S11S2S11S11S1fPaA1Sa3A4G3A4S0G1S2G0S11S2S11S11Sc3G3A4Sc5A4S0G1S2G0S11S2S11S11S7eG3A4S12Z90A1A4S0G1S2G0S11S2S11S11S49G3A4S12Z20A1A4S0G1S2G0S11S2S11S11S49S12Zb0A1A4S12Zf8A1M4A4S0G1S2G0S11S2S11S11S49G4A4S12Z100A1A4S3G1A1A3A3A3A3A3A3A3A3A3").
Definition glob_shape : list (sv * sv * sv) := ltac2:(tb__ "0|3|
S0S6S6S11S11A2M0S11A2M1S2G0S11S2S11S11S12Z0A1M2S12SccA1A4S12ScbA1A4S0G1S2G0S11S2S11S11G2S12SceA1A4S12ScdA1A4S3G1A1A3A3").

Lemma fz_checks_ms : ltac2:(tb__ "0|8|
S33S32S8S3bA1M0S36S69S9cA2S7S3bS51A2A3S33S32S8S13A1Sb1S13S16S3cS51A1M1A1U2M2A3S7S13S15S49S12Z20A1S12Zb0A1S3S14A1M3S17A5A2A3S33S32S5S1aS47S51A1S72G3S17A2M4A2S4A3S33S32S3bS3dS51ScaG1G2G4A3A2S5eA3S33S32S5SbfSadS47S5eA1A2S4A3S33S32S3bS64S67S36S5eS9eA2M5A1M6A1S50A3S33S32G0G5S7S3bG6A2A3S33S32S5S3eS50A1S4A3S32S9S6S6S11S11A2S11A2M7A1S57S50A1SaG7S65S66A3A3A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition E_lo0 : axst := Eval vm_compute in leafF (runF C_body) lo_entry 0.

Definition xf_lo : list axform := ltac2:(tb__ "0|3|
S0S34S35U0M0S12N280M1A1A2S0S34S3aG0G1A2S0S34S35U2S12Z10M2A1A2S0S34S3aU3G2A2S0S34S35U5S12N10A1A2S3S34A1A3A3A3A3A3").
Definition E_lo1 : axst := Eval vm_compute in optL (apply_axforms E_lo0 xf_lo).

Definition optS (A : axst) (x : option sstate) : axst := ltac2:(tb__ "0|0|
S8S1cA1S3bLx;Vx;S1cS3dVA;R1A2LS1;S68X8x2").
Definition E_lo2 : axst := Eval vm_compute in optS E_lo1 (zero_fill_at (ax_S E_lo1) 8).
Definition cfg_cellsE : list cell := ltac2:(tb__ "0|1|
S0S14S19S12Z38A1Z4M0S12ZffffffffffffffffA1A3S0S14S19S12Z30A1G0S12Z10101A1A3S3S14A1A3A3").
Definition cfg_cellsR : list cell := ltac2:(tb__ "0|1|
S0S14S19S12Z38A1Z4M0S12ZffffffffA1A3S0S14S19S12Z30A1G0S12Z10101A1A3S3S14A1A3A3").
Definition E_lo : axst := Eval vm_compute in ax_setS E_lo2 (reshape_obj_at (ax_S E_lo2) 8 (recell_obj (cfg_obj cfg_cellsE DZero) cfg_cellsR)).
Definition s_lo : wsub := ltac2:(tb__ "0|0|
Sd3PaS3cS48A1S3cSaeA1A3").
Definition R_lo : list sobj := Eval vm_compute in optR (entails_frA E_lo LD.Pre_lo s_lo).
Definition Xk_lo : list (sv * sv) := Eval vm_compute in ax_X E_lo.
Definition T_err0 : axst := Eval vm_compute in T_afterA3 LD.Pre_lo E_lo s_lo R_lo LI.P_err Xk_lo.
Definition T_suc0 : axst := Eval vm_compute in T_afterA3 LD.Pre_lo E_lo s_lo R_lo LI.P_ok Xk_lo.

Definition out_mid : sobj := ltac2:(tb__ "0|0|
S15Sa1S12Z10A1S12Ze0A1S3S14A1S17A5").
Definition T_err1 : axst := Eval vm_compute in ax_setS T_err0 (reshape_obj_at (ax_S T_err0) 2 out_mid).
Definition xfb_err : list axform := ltac2:(tb__ "0|3|
S0S34S39U1M0A1S0S34S38S0S1G0S0S1U0M1S0S1U8S0S1U2S0S1U9S0S1UaS0S1U5S0S1U3M2S0S1U4S0S1UbS0S1UcS0S1UdS0S1U6S0S1U7S3S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S34S37G1A1S0S34S37G0A1S0S34S37G2A1S3S34A1A3A3A3A3A3").
Definition T_err : axst := Eval vm_compute in ax_tidy (optL (apply_axforms T_err1 xfb_err)).
Definition xfb_ok : list axform := ltac2:(tb__ "0|4|
S0S34S39U1M0A1S0S34S39U2M1A1S0S34S38S0S1G0S0S1U0M2S0S1U9S0S1G1S0S1UaS0S1UbS0S1U5S0S1U3M3S0S1U4S0S1UcS0S1UdS0S1UeS0S1U6S0S1U7S0S1U8S3S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S34S37G2A1S0S34S37G0A1S0S34S37G3A1S3S34A1A3A3A3A3A3A3").
Definition T_suc : axst := Eval vm_compute in ax_tidy (optL (apply_axforms T_suc0 xfb_ok)).

Definition pRC : sv := SVar 224.  Definition pAR : sv := SVar 225.  Definition pH : sv := SVar 226.

Lemma fz_checks_lo : ltac2:(tb__ "0|13|
S33S32S9S6S45SaaA2M0A1S58S56S50A1A1S0G0S2S45SaaS75SabA4S3G0A1A3A3S33S32S8S3bA1M1S36S82S9bA2S7S3bS5dA2A3S33S32S8S13A1M2Sb1S13S16S3cS52A1M3A1U8M4A3S7S13S72S85S1dA2M5A2A3S33S32S5S1aS47S52A1Sa9G5S86A2M6A2S4A3S33S32S3bS3dS52ScaG3G4G6A3A2S48A3S33S32S5S3eS48A1S4A3S33S32S8S9S13A1M7A1Sd5S48SaeS4aA3S7G7S54A2A3S33S32S5Sd4S48SaeS4aS54Sb7S6S3bSd6A2S3bSdS3bSd6A2SdcA4A5S4A3S33S32S5Sd8SadS4aA2S4A3S33S32S5Se2S4aSafA2S4A3S33S32S5SbfSadS47S48A1M8A2S4A3S33S32S9S6S11S11A2M9A1S3fS48A1S63A3S33S32S46G8P90A3S33S32S8S1cA1Se3S3cS5dA1G4A2S7S1cG3A2A3S33S32S3bS3dS5dG3A2S52A3S33S32S5S31G3A1S4A3S33S32S3bSd7SaeS48S4aS54SddS63A6S55A3S33S32S3bSd7SaeS48S4aS54SdeS63A6S6eA3S33S32G2Sb1S13S16S3cS55A1MaA1U2MbA3S7S13S15S74Z10A1S12Z0A1McS12Zd0A1S3S14A1S1dA5A2A3S33S32S5S1aS47S55A1S78A2S4A3S33S32S3bS3dS55ScaGaGbS78A3A2S6cA3S33S32G1S36S6cS9dA2MdS7S3bS67GdA1MeA2A3S33S32S3bS64GeA1S61A3S33S32S5S3eS61A1S4A3S33S32G1S36S6eS9fA2MfS7S3bS67GfA1M10A2A3S33S32S3bS64G10A1S62A3S33S32S5S3eS62A1S4A3S33S32S9S6G9S11A2M11A1M12S57S61A1SaG11S65S66A3A3S32G12S57S62A1SaG11S65S0G11S2G9S11S2S11S11S90GcA4S12Z40A1A4S66A3A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
