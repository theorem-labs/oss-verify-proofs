(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "true"; "bool"; "prod"; "Some"; "list"; "app"; "option"; "negb"; "S"; "fst"; "None"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "cell"; "mkObj"; "ss_objs"; "mkCell"; "DUnknown"; "sprop"; "obj_wf"; "ss_facts"; "DZero"; "SAlu"; "SVar"; "ob_base"; "ob_hi"; "ob_lo"; "mkSS"; "ob_dflt"; "sprop_below"; "ss_next"; "ss_pc"; "sv_eqb"; "FcsrFrm0"; "c_off"; "ob_cells"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sstate"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "apply_axforms"; "AXMerge"; "AXSelect"; "AXRebase"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "ax_X"; "ax_setS"; "leafA"; "has_facts"; "la_state"; "entailsA"; "sym_runA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_one"; "nx"; "E_lo"; "vF"; "E_ms"; "s_lo"; "E_sm0"; "T_sm1"; "s_sm"; "C3"; "C_al"; "C_body"; "C_ms1"; "E_lo1"; "Pre_ms"; "Pre_sm"; "R_lo"; "T_err0"; "runF"; "s_ms"; "shapes"; "showL"; "C0"; "C1"; "C_pro"; "C_pro0"; "L_alF"; "R_ms"; "R_sm"; "T_err"; "T_suc"; "Xk_lo"; "ax_tidy"; "body_shape"; "glob_shape"; "optL"; "vCFG"; "C_ms"; "L_al"; "L_ms"; "L_sm"; "T_err1"; "T_ms0"; "T_sm"; "T_suc0"; "X_al"; "X_rel"; "cells_rel"; "cfg_obj"; "gF"; "hp"; "lo_entry"; "memset_pc"; "objs_rel"; "objs_sm1"; "out_mid"; "pF"; "pc_al"; "s_al"; "sm2_pc"; "vFL"; "BAD"; "C2"; "C4"; "E_lo0"; "FUEL_fz"; "Fx"; "cfg_cellsE"; "cfg_cellsR"; "cps_fz"; "fnodup"; "free_pc"; "junk_regs"; "mentions"; "nobj"; "oBack"; "oH"; "oM0"; "pAR"; "pc_L"; "pc_adA"; "pc_adB"; "pc_fa"; "pc_rel"; "pc_sx"; "sel_sm"; "xf_al1"; "xf_al2"; "xf_al3"; "xf_lo"; "xf_ms"; "xfb_err"; "xfb_ms"; "xfb_ok"; "xnodup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_fuzz_one_glue"; "vH"; "WIN"; "vG10"; "vDN"; "DNt"; "G10t"; "al_facts"; "hS"; "recell_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "set_objs"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "add"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_one.LD"; "Pre_lo"; "NP"; "@Stdlib.Lists.List"; "filter"; "nth_error"; "existsb"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "seq"; "skipn"; "nth"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "ax_setX"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "of_nat"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "vDAT"; "vDp"; "vLEN"; "fz_facts"; "Pre_fz"; "X_lits"; "spm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "GOT_HI";
"GOT_LO"; "RTC_HI"; "RTC_LO"; "mkA"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.FZAddr"; "D_FZ"; "fz_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "flagbyte_obj"; "@Corelib.Init.Nat"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_one.LI"; "PD_lo"; "P_err"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sprop_vars_all"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "frame_open_stateA"; "local_ok"; "shadow_release_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "fs_frame_size"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_fuzz_iface2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_fuzz_one_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import FZAddr.
Module LD. Include Lib_load_obj_defs. End LD. Module LI. Include Lib_load_obj_iface. End LI.

Definition sm2_pc : Z := 0x47c0c.
Definition memset_pc : Z := 0x5cce8.
Definition lo_entry : Z := 0x8c894.
Definition free_pc : Z := 0x5e05c.
Definition pc_al : Z := 0x9db7c.
Definition pc_sx : Z := 0x9dd30.
Definition pc_rel : Z := 0x9df98.
Definition pc_adA : Z := 0x9de60.
Definition pc_L : Z := 0x9dea4.
Definition pc_adB : Z := 0x9def0.
Definition pc_fa : Z := 0x9dfdc.
Definition cps_fz : list Z := ltac2:(tb__ "0|0|
S0S44S95S0S44S94S0S44S96S0S44S97S0S44S99S0S44S98S0S44S7eS0S44S80S0S44S79S0S44S78S0S44S8cS0S44SdaS3S44A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition FUEL_fz : nat := 600%nat.
Definition BAD : axst := ltac2:(tb__ "0|1|
Sd7S22Z0S3S11A1M0G0S28SeS11A1S3S13A1S3S19A1P1SfA9S3S6S11S11A2A1A2").
Definition optL (x : option axst) : axst := match x with Some s => s | None => BAD end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition runF (S : axst) : list leafA := ltac2:(tb__ "0|1|
SaS8S3fA1M0A1G0Lx;S43Sd8S86S8aVS;S4A5G0R1Lls;S3S3fA1Xax2").
Definition showL (ls : list leafA) := map show_leafA ls.
Definition leafF (ls : list leafA) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
SbeS3aVk;SbaS3fS3aS41Sb6S3fS3fSb3S26S3bS41R1A1A1A1Vpc;A2LL;Vls;A3A4S82A4").
Definition shapes (A : axst) : ltac2:(tb__ "0|0|
S8S6S6S11S11A2S11A2A1") := ltac2:(tb__ "0|1|
SbaS13S6S6S11S11A2M0S11A2S13S2G0S11S2S11S11S1fR1A1S21R1A1A4S20R1A1A4Lo;S16S3bVA;A1A1A4").
Definition nobj (A : axst) : nat := length (ss_objs (ax_S A)).
Definition Fx (A : axst) : list sprop := ss_facts (ax_S A).
Definition nx (A : axst) : positive := ss_next (ax_S A).
Definition hp (k : Z) : sv := ltac2:(tb__ "0|0|
S1dSbfSa4S12Vk;A1A3").
Definition dropX (b : sv) (A : axst) : axst := ltac2:(tb__ "0|1|
Sc1VA;Sb6S6S11S11A2M0G0SbS27SdS11S11R1A3Vb;A2A1Lr;S3dVA;A1A3A2").
Definition mentions (v : positive) (f : sprop) : bool := ltac2:(tb__ "0|0|
SbSe6S45SbSc3R1Vv;A2A1Lw;Vf;A2A1").
Definition dropV (vs : list positive) (A : axst) : axst := ltac2:(tb__ "0|0|
Sc0VA;Sb6S19S19SbSb8S45S45S8eR1R2A2Lv;Vvs;A3A1Lf;S1bS3bVA;A1A1A3A2").
Definition keep_below (n : positive) (A : axst) : axst := ltac2:(tb__ "0|0|
Sc0VA;Sb6S19S24Vn;A1S1bS3bVA;A1A1A3A2").

Fixpoint junk_regs (l : list nat) (n : positive) (rs : list sv) : list sv :=
  match l with [] => rs | r :: l' => junk_regs l' (Pos.succ n) (list_set rs r (SVar n)) end.
Definition junkRN (l : list nat) (A : axst) : axst := ltac2:(tb__ "0|1|
S3bVA;A1S30S3eVA;S22S26R1A1S8dVl;S25R1A1M0S2eR1A1A3S2cR1A1S2bR1A1S2fR1A1S16R1A1S1bR1A1Sc4SdfSc5G0A1S10S1Vl;A2A2A1S2dR1A1A9A2TS;").
Definition upd_obj_at (A : axst) (i : nat) (f : sobj -> sobj) : axst := ltac2:(tb__ "0|2|
S3eVA;Sb0S3bVA;A1M0S9S13SbbS13Vi;S16G0A1M1A3S9S13SbaS13S13Vf;SbbS13U1SbdS13Vi;G1A3A3A4SbdS13ScVi;A1G1A3A3A3A2A2").
Definition drop_cells_obj (offs : list Z) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S15S1fVo;A1S21Vo;A1S20Vo;A1Sb6S14S14SbSb8S44S44S27S29R2A1S12R1A1A2Lz;Voffs;A3A1Lc;S2aVo;A1A3S23Vo;A1A5").
Definition nocells_obj (o : sobj) : sobj := ltac2:(tb__ "0|0|
S15S1fVo;A1S21Vo;A1S20Vo;A1S3S14A1S23Vo;A1A5").

Fixpoint xnodup (l : list (sv * sv)) : list (sv * sv) :=
  match l with [] => [] | x :: r => if existsb (fun y => sv_eqb (fst y) (fst x) && sv_eqb (snd y) (snd x)) r then xnodup r else x :: xnodup r end.
Fixpoint fnodup (l : list sprop) : list sprop :=
  match l with [] => [] | x :: r => if existsb (sprop_eqb x) r then fnodup r else x :: fnodup r end.
Definition ax_tidy (A : axst) : axst := ltac2:(tb__ "0|0|
Sc0Sc1VA;Sa3S3dVA;A1A1A2S8bS1bS3bVA;A1A1A1A2").

Definition L_al : axst := Eval vm_compute in leafF (runF Pre_fz) pc_al 0.
Definition L_alF : axst := Eval vm_compute in ax_with_facts L_al (al_facts hS DNt G10t ++ ss_facts (ax_S L_al)).
Definition X_al : list (sv * sv) := ltac2:(tb__ "0|1|
S9S6S11S11A2M0S0G0S2S11S11Sc6Sc8A4S0G0S2S11S11SccSd9A1S12Sd9A1A4S0G0S2S11S11S77Sb1Sa5A1A1S12Sb2Sa5Z180A2A1A4S3G0A1A3A3A3ScbA3").
Definition C0 : axst := Eval vm_compute in
  let S := ax_S L_al in
  mkA (mkSS pc_al (setregs (ss_regs S) [(2%nat, vH)]) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S)
            (SPAlign 100 5 :: al_facts vH vDN vG10 ++ fz_facts) 103%positive false) X_al.
Definition s_al : wsub := ltac2:(tb__ "0|1|
S0S6S45S11A2M0S2S45S11P64SabA4S0G0S2S45S11P65Sa8A4S0G0S2S45S11P66Sa9A4S3G0A1A3A3A3").
Definition xf_al1 : list axform := ltac2:(tb__ "0|2|
S0S33S34U0M0S12N68A1A2S0S33S38U2M1A1S0S33S37S0S1G1S0S1G0S0S1U1S0S1U3S0S1U4S0S1U5S3S1A1A3A3A3A3A3A3A1S0S33S36G0A1S3S33A1A3A3A3A3").
Definition C1 : axst := Eval vm_compute in optL (apply_axforms C0 xf_al1).
Definition oM0 : sobj := ltac2:(tb__ "0|0|
S15S1ePaA1S1dSbfSc7S12N180A1A3S12N68A1S3S14A1S18A5").
Definition C2 : axst := Eval vm_compute in ax_setS C1 (reshape_obj_at (ax_S C1) 0 oM0).
Definition xf_al2 : list axform := ltac2:(tb__ "0|0|
S0S33S34U0Sa6A2S0S33S36U1A1S3S33A1A3A3").
Definition C3 : axst := Eval vm_compute in optL (apply_axforms C2 xf_al2).
Definition oBack : sobj := ltac2:(tb__ "0|0|
S15S1ePaA1S1dSbfSc7S12N180A1A3Sa6S3S14A1S18A5").
Definition oH : sobj := ltac2:(tb__ "0|0|
S15Sa4Sa7S12Z118A1S3S14A1S18A5").
Definition C4 : axst := Eval vm_compute in ax_setS C3 (reshape_obj_at (ax_S C3) 0 oH).
Definition xf_al3 : list axform := ltac2:(tb__ "0|2|
S0S33S34U0M0S12Sb1Sa5A1A1A2S0S33S34U1M1S12Z0A1A2S0S33S37S0S1G1S0S1U2S0S1G0S0S1U3S0S1U4S0S1U5S0S1U6S3S1A1A3A3A3A3A3A3A3A1S3S33A1A3A3A3").
Definition C_al : axst := Eval vm_compute in optL (apply_axforms C4 xf_al3).

Lemma fz_checks_al : ltac2:(tb__ "0|e|
S32S31S8S6S44SaeA2M0A1S5aS57ScaA1A1S0G0S2S44SaeS7eSafA4S3G0A1A3A3S32S31S8S19A1S1bS3bS6bA1M1A1M2Sc9A3S32S31S3aSc0S6bS9S19SaaSabSa8Sa9A3G2A3M3A2S5fA3S32S31S5Sb9S19S24S25G1A1A1G3A3S4A3S32S31S5S3cS5bA1S4A3S32S31S5S42S5fS5bS7fA3S4A3S32S31S5Se5S7fSadA2S4A3S32S31S5Sc2SadS46S5fA1A2S4A3S32S31SaS3aA1M4S35S5bS9bA2S7S3aS5cA2A3S32S31SaS13A1M5Sb7S13S16S3bS5cA1A1U0M6A3S7S13S15S1ePaA1M7S1dSbfSc7S12N180A1M8A3S12N68A1S0S14S17G8Z8S12Z0A1M9A3S3S14A1A3S18A5A2A3S32S31S5S1aS46S5cA1S92A2S4A3S32S31G4S35S83S9cA2S7S3aS4eA2A3S32S31G5Sb7S13S16S3bS4eA1A1G6A3S7S13S90A2A3S32S31S5S1aS46S4eA1S91A2S4A3S32S31S5S40Sc9S87S4eA1MaA2S4A3S32S31S5S40SaaSa4Sa7Sa6A3GaA2S4A3S32S31G4S35S84S9dA2S7S3aS4fA2A3S32S31S5S3cS4fA1S4A3S31S8S6S6S11S11A2MbS11A2McA1S59S4fA1S0GcS2GbS11S2S11S11Sa4S12Sb1Sa5A1A1MdA4G9A4S0GcS2GbS11S2S11S11Sa4G9A4S12Z118A1A4S0GcS2GbS11S2S11S11Sa4Sa7A4GdA4S0GcS2GbS11S2S11S11G7Sa6A4G9A4S0GcS2GbS11S2S11S11Sc6G9A4Sc8A4S0GcS2GbS11S2S11S11G9S12Sd4A1A4S12Sd3A1A4S0GcS2GbS11S2S11S11G9S12Sd6A1A4S12Sd5A1A4S3GcA1A3A3A3A3A3A3A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition E_sm0 : axst := Eval vm_compute in leafF (runF C_al) sm2_pc 0.
Definition Pre_sm : axst := Pre_stack_malloc AE_A 2.
Definition L_sm : axst := L_stack_malloc AE_A 2.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S0S6S45S11A2S2S45S11SddS12Sb1Sa5A1A1A4ScdPaS3bS4bA1S3bS54A1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Definition T_sm : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.

Definition pF : positive := 113%positive.  Definition pFL : positive := 123%positive.  Definition gF : positive := 143%positive.
Definition vF : sv := SVar pF.  Definition vFL : sv := SVar pFL.
Definition fr_fz : list (sv * Z * sv) := ltac2:(tb__ "0|2|
S0S6S6S11S44A2M0S11A2M1S2G0S11S2S11S44S48Z2A4S81A4S3G1A1A3").
Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
S9S1SbcU0Vi;A2S9S1SbcScVi;A1M0Se0S8fVA;A1G0A2A2S0S1Vi;S3S1A1A3A3A3").
Definition sel_sm : list nat := Eval vm_compute in sel_last T_sm 3.
Definition T_sm1 : axst := Eval vm_compute in optL (apply_axforms T_sm [AXSelect sel_sm]).
Definition objs_sm1 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S T_sm1)).
Definition C_pro0 : axst := Eval vm_compute in frame_open_stateA T_sm1 objs_sm1 X_al pF 256.
Definition C_pro : axst := Eval vm_compute in ax_setX C_pro0 ((vF, SLit 0) :: ax_X C_pro0).

Definition X_rel : axst := Eval vm_compute in leafF (runF C_pro) memset_pc 0.
Definition cells_rel : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S X_rel)) oH).
Definition objs_rel : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_rel)).
Definition C_ms : axst := Eval vm_compute in shadow_release_stateA X_rel objs_rel pF [(32, 144)].

Lemma fz_checks_sm : ltac2:(tb__ "0|d|
S32S31S8S6S44SaeA2M0A1M1S5aS57S4fA1A1S0G0S2S44SaeS80SafA4S3G0A1M2A3A3S32S31SaS8S13A1M3A1ScfS4bS54S4dA3S7G3S61A2A3S32S31S5SceS4bS54S4dS61S0S3aS6dS3S3aA1A3A5S4A3S32S31S5Sd1SadS4dA2S4A3S32S31S5Sc2SadS46S4bA1A2S4A3S32S31S11Se4S4dPcA2S12Z100A1A3S32S31S3aSd2S54S4bS4dS61S6dA5S70A3S32S31SaS3aA1S35S70S0S33S37S9aA1S3S33A1A3A2S7S3aS4cA2A3S32S31G3S16S3bS4cA1A1S9S13S7bS0S13SdeS81S0S14S17S12Z0M4A1M5Z1M6S12G6A1A3S3S14A1A3A2S3S13A1M7A3A3A3S32S31S8S6S11S11A2M8A1S3dS4cA1S9G8S72S0G8S2S11S11S48S12SecZ2A1M9A1A4S3G8A1A3A3A3S32S31S45S46S4cA1S76A3S32S31S3aSe8S4cS7bS72S7dG9A5S5eA3S32S31S3aSc1S5eS0G8S2S11S11S48G5A4S3dS5eA1A3A2S5dA3S32S31S5S3cS5dA1S4A3S32S31G1S5aS57S5dA1A1S0G0S2S44SaeS79SafA4G2A3A3S32S31G3S16S3bS73A1A1S9S13S7aS0S13SebS76G4Z20MaS74S1cA5G7A3A3A3S32S31S5Sb9S6S44S44A2MbSe9S74S1cG4GaA4S0GbS2S44S44GaZ90A4S3GbA1A3McA3S4A3S31S3aSeaS73S7aS7dGcA4S6aA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition vCFG : sv := SAlu ALU_ADD vF (SLit 32).
Definition cfg_obj (cells : list cell) (d : odefault) : sobj := ltac2:(tb__ "0|0|
S15S69S12Z0A1S12Z90A1Vcells;Vd;A5").
Definition xf_ms : list axform := ltac2:(tb__ "0|0|
S0S33S34U1S12Z20A1A2S0S33S34U2S12Zb0A1A2S3S33A1A3A3").
Definition C_ms1 : axst := Eval vm_compute in optL (apply_axforms C_ms xf_ms).
Definition E_ms : axst := Eval vm_compute in ax_setS C_ms1 (reshape_obj_at (ax_S C_ms1) 2 (cfg_obj [] DUnknown)).
Definition Pre_ms : axst := Pre_memset memset_pc.
Definition L_ms : axst := L_memset (ae_ret_asan_memset AE_A).
Definition s_ms : wsub := ltac2:(tb__ "0|1|
S0S6S45S11A2M0S2S45S11P35S69A4S0G0S2S45S11P36S12Z90A1A4S0G0S2S45S11SddS12Sb1Sa5A1A1A4ScdPaS3bS49A1S3bS53A1A3A3A3A3").
Definition R_ms : list sobj := Eval vm_compute in optR (entails_frA E_ms Pre_ms s_ms).
Definition T_ms0 : axst := Eval vm_compute in T_afterA Pre_ms E_ms s_ms R_ms L_ms.
Definition xfb_ms : list axform := ltac2:(tb__ "0|0|
S0S33S37S0S1U0S0S1U7S0S1U8S0S1U9S0S1UaS0S1U1S0S1U4S0S1U5S0S1U6S0S1U2S0S1U3S3S1A1A3A3A3A3A3A3A3A3A3A3A3A1S3S33A1A3").
Definition C_body : axst := Eval vm_compute in ax_tidy (optL (apply_axforms T_ms0 xfb_ms)).
Definition body_shape : list (sv * sv * sv) := ltac2:(tb__ "0|5|
S0S6S6S11S11A2M0S11A2M1S2G0S11S2S11S11Sa4S12Sb1Sa5A1A1M2A4S12Z0A1M3A4S0G1S2G0S11S2S11S11Sa4G3A4S12Z118A1A4S0G1S2G0S11S2S11S11Sa4Sa7A4G2A4S0G1S2G0S11S2S11S11S1ePaA1Sa6A4G3A4S0G1S2G0S11S2S11S11Sc6G3A4Sc8A4S0G1S2G0S11S2S11S11S69G3A4S12Z90A1A4S0G1S2G0S11S2S11S11S48G3A4S12Z20A1A4S0G1S2G0S11S2S11S11S48S12Zb0A1A4S12Zf8A1M4A4S0G1S2G0S11S2S11S11S48G4A4S12Z100A1A4S3G1A1A3A3A3A3A3A3A3A3A3").
Definition glob_shape : list (sv * sv * sv) := ltac2:(tb__ "0|3|
S0S6S6S11S11A2M0S11A2M1S2G0S11S2S11S11S12Z0A1M2S12Sd4A1A4S12Sd3A1A4S0G1S2G0S11S2S11S11G2S12Sd6A1A4S12Sd5A1A4S3G1A1A3A3").

Lemma fz_checks_ms : ltac2:(tb__ "0|9|
S32S31SaS3aA1M0S35S6aS9fA2S7S3aS51A2A3S32S31SaS13A1Sb7S13S16S3bS51A1M1A1U2M2A3S7S13S15S48S12Z20A1S12Zb0A1S3S14A1M3S18A5A2A3S32S31S5S1aS46S51A1S75G3S18A2M4A2S4A3S32S31S3aS3eS51Sd0G1G2G4A3A2S49A3S32S31SaS8S13A1M5A1ScfS49S53S58A3S7G5S60A2A3S32S31S5SceS49S53S58S60S0S3aS6cS3S3aA1A3A5S4A3S32S31S5Sd1SadS58A2S4A3S32S31S5Sc2SadS46S49A1A2S4A3S32S31S3aSd2S53S49S58S60S6cA5S6fA3S32S31S3aS65S68S35S6fSa1A2M6A1M7A1S50A3S32S31G0G6S7S3aG7A2A3S32S31S5S3cS50A1S4A3S31S8S6S6S11S11A2S11A2M8A1S59S50A1S9G8S66S67A3A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition E_lo0 : axst := Eval vm_compute in leafF (runF C_body) lo_entry 0.

Definition xf_lo : list axform := ltac2:(tb__ "0|3|
S0S33S34U0M0S12N200M1A1A2S0S33S39G0G1A2S0S33S34U2S12Z48M2A1A2S0S33S39U3G2A2S0S33S34U5S12N10A1A2S3S33A1A3A3A3A3A3").
Definition E_lo1 : axst := Eval vm_compute in optL (apply_axforms E_lo0 xf_lo).

Definition cfg_cellsE : list cell := ltac2:(tb__ "0|1|
S0S14S17S12Z38A1Z4S12ZffffffffffffffffA1A3S0S14S17S12Z32A1Z1M0S12G0A1A3S0S14S17S12Z30A1Z2S12Z101A1A3S3S14A1A3A3A3").
Definition cfg_cellsR : list cell := ltac2:(tb__ "0|1|
S0S14S17S12Z38A1Z4S12ZffffffffA1A3S0S14S17S12Z32A1Z1M0S12G0A1A3S0S14S17S12Z30A1Z2S12Z101A1A3S3S14A1A3A3A3").
Definition E_lo : axst := Eval vm_compute in ax_setS E_lo1 (reshape_obj_at (ax_S E_lo1) 8 (recell_obj (cfg_obj cfg_cellsE DZero) cfg_cellsR)).
Definition s_lo : wsub := ltac2:(tb__ "0|0|
ScdPaS3bS47A1S3bSb4A1A3").
Definition R_lo : list sobj := Eval vm_compute in optR (entails_frA E_lo LD.Pre_lo s_lo).
Definition Xk_lo : list (sv * sv) := Eval vm_compute in ax_X E_lo.
Definition T_err0 : axst := Eval vm_compute in T_afterA3 LD.Pre_lo E_lo s_lo R_lo LI.P_err Xk_lo.
Definition T_suc0 : axst := Eval vm_compute in T_afterA3 LD.Pre_lo E_lo s_lo R_lo LI.P_ok Xk_lo.

Definition out_mid : sobj := ltac2:(tb__ "0|0|
S15Sa4S12Z48A1S12Z118A1S3S14A1S18A5").
Definition T_err1 : axst := Eval vm_compute in ax_setS T_err0 (reshape_obj_at (ax_S T_err0) 2 out_mid).
Definition xfb_err : list axform := ltac2:(tb__ "0|3|
S0S33S38U1M0A1S0S33S37S0S1G0S0S1U0M1S0S1U8S0S1U2S0S1U9S0S1UaS0S1U5S0S1U3M2S0S1U4S0S1UbS0S1UcS0S1UdS0S1U6S0S1U7S3S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S33S36G1A1S0S33S36G0A1S0S33S36G2A1S3S33A1A3A3A3A3A3").
Definition T_err : axst := Eval vm_compute in ax_tidy (optL (apply_axforms T_err1 xfb_err)).
Definition xfb_ok : list axform := ltac2:(tb__ "0|4|
S0S33S38U1M0A1S0S33S38U2M1A1S0S33S37S0S1G0S0S1U0M2S0S1U9S0S1G1S0S1UaS0S1UbS0S1U5S0S1U3M3S0S1U4S0S1UcS0S1UdS0S1UeS0S1U6S0S1U7S0S1U8S3S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S33S36G2A1S0S33S36G0A1S0S33S36G3A1S3S33A1A3A3A3A3A3A3").
Definition T_suc : axst := Eval vm_compute in ax_tidy (optL (apply_axforms T_suc0 xfb_ok)).

Definition pRC : sv := SVar 264.  Definition pAR : sv := SVar 265.  Definition pH : sv := SVar 266.

Lemma fz_checks_lo : ltac2:(tb__ "0|13|
S32S31S8S6S44SaeA2M0A1S5aS57S50A1A1S0G0S2S44SaeS78SafA4S3G0A1A3A3S32S31SaS3aA1M1S35S85S9eA2S7S3aS52A2A3S32S31SaS13A1M2Sb7S13S16S3bS52A1M3A1U8M4A3S7S13S75S88S1cA2M5A2A3S32S31S5S1aS46S52A1SacG5S89A2M6A2S4A3S32S31S3aS3eS52Sd0G3G4G6A3A2S47A3S32S31S5S3cS47A1S4A3S32S31SaS8S13A1M7A1ScfS47Sb4S4aA3S7G7S55A2A3S32S31S5SceS47Sb4S4aS55SbaS6S3aSdbA2S3aSdS3aSdbA2Se1A4A5S4A3S32S31S5Sd1SadS4aA2S4A3S32S31S5Se7S4aSb5A2S4A3S32S31S5Sc2SadS46S47A1M8A2S4A3S32S31S8S6S11S11A2M9A1S3dS47A1S64A3S32S31S45G8Pb8A3S32S31S3aSdcSb4S47S4aS55Se2S64A6S56A3S32S31S3aSdcSb4S47S4aS55Se3S64A6S71A3S32S31G2Sb7S13S16S3bS56A1MaA1U2MbA3S7S13S15S77Z48A1S12Z0A1McS12Zd0A1S3S14A1S1cA5A2A3S32S31S5S1aS46S56A1S7cA2S4A3S32S31S3aS3eS56Sd0GaGbS7cA3A2S6eA3S32S31G1S35S6eSa0A2MdS7S3aS68GdA1MeA2A3S32S31S3aS65GeA1S62A3S32S31S5S3cS62A1S4A3S32S31G1S35S71Sa2A2MfS7S3aS68GfA1M10A2A3S32S31S3aS65G10A1S63A3S32S31S5S3cS63A1S4A3S32S31S8S6G9S11A2M11A1M12S59S62A1S9G11S66S67A3A3S31G12S59S63A1S9G11S66S0G11S2G9S11S2S11S11S93GcA4S12Z40A1A4S67A3A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
