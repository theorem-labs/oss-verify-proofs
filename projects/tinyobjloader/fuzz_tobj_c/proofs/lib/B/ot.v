(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.

(* [comment removed for export] *)
Module DrvTPres.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "not"; "@Corelib.Init.Datatypes"; "list"; "bool"; "nil"; "prod"; "true"; "None"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "sprop"; "valuation"; "holds"; "rw"; "sobj"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "spT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite"; "sp0_factsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa"; "SH0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "keptFA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "HB"; "PRES"; "@Stdlib.ZArith.BinInt.Z"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code DrvIfaceT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvTLXa.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma fz_site_PRES : ltac2:(tb__ "0|6|
S2S5S9S9A2M0A1M1G1ScScS2SfA1S15S1eS2SbA1S1aR6A1S20S11R7R6A3S21RaR9R8S4G0A1S4S5G0S9A2A1SaR8A1SaR7A1A7S12Q40M2A1S1bR9R8R1A3S26S23S13G2R2A2A2S1S0S8S12Q8A1M3A1S16R9R3A2S7G3A1A3A1F_;F_;Fa;S14SbSdR9A1R5A3S0S3S19R6A1S6A3S0S10S1fR8PaM4A2S18A3S0S3S22S11R9A2S6A3S25S17SaS1dS1cRdRcRbA3RaA2M5A1S13G2SeG5G4A2A2S24G5A1A4F_;F_;F_;F_;F_;F_;F_;F_;Ffacts;Fs;Fms;FR;Frho1;FrhoT;FXGL;FCST;").
Proof.
  intros CST XGL rhoT rho1 R ms s facts (_ & _ & HPZ) Hav HK HM HF Hsp0 E10 Htp.
  destruct (sp0_facts_sound rho1 facts HF Hsp0) as [Hsp E30].
  assert (EV : rw rho1 V_TOP = rw rhoT V_TOP) by (symmetry; apply (proj1 Hav); unfold V_TOP, NF; lia).
  destruct (STKP_kept segs CST XGL rhoT rho1 [] [] EV HK HPZ) as [H47 HP1].

  assert (E10c : bv_unsigned (rw (rho_sub (rho_absorb rho1 R ms) s) 10%positive) = bv_unsigned (rw rho1 1%positive) - 208).
  { rewrite rw_call', E10. unfold spT, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf.add, sp0. cbn [eval].
    unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia. }
  assert (ETc : HB (rho_sub (rho_absorb rho1 R ms) s) = HB rho1).
  { unfold HB. f_equal. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.T0_calleeA NF rhoT s rho1 R ms Hav Htp) as X. unfold T0 in X. change Contract.V_TOP with V_TOP in X.
    rewrite X. f_equal. symmetry. exact EV. }
  rewrite E10c, ETc. change (bv_unsigned (rw rho1 V_TOP)) with (bv_unsigned (rw rho1 30%positive)) in H47, HP1. unfold STK_LO in HP1.
  apply (PRES_sub segs _ (bv_unsigned (rw rho1 30%positive) + 7340032) (HB rho1)); [lia | lia |].
  apply PRES_callee_all; [exact HM | unfold IMG_HI; lia | | exact HP1].
  pose proof (HBz_le_47 _ H47) as X. unfold HB. change (bv_unsigned (rw rho1 V_TOP)) with (bv_unsigned (rw rho1 30%positive)). lia.
Qed.
End DrvTPres.

(* [comment removed for export] *)
Module DrvSiteEx.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "False"; "True"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "ss_facts"; "sobj"; "ss_next"; "sstate"; "SLit"; "ss_objs"; "sprop"; "holds"; "ss_lenient"; "sprop_eqb"; "DUnknown"; "SPUle"; "cell"; "mkObj"; "SPEq"; "agree_below"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "nil"; "option"; "Some"; "cons"; "pair"; "app"; "nat"; "false"; "length"; "fst"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_X"; "ax_base"; "sym_runA"; "mkAX"; "mkLeafA"; "ax_setS"; "la_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "ExitEv"; "FdChannel"; "WriteEv"; "fd_lookup"; "m_fds"; "m_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "w_tr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExit"; "ch1"; "supported"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface"; "FERR"; "PEND"; "Pre_exit"; "Pre_exitP"; "supportedP"; "@Stdlib.ZArith.BinInt.Z"; "add"; "sub"; "le"; "lt"; "opp"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_tv"; "ANone"; "NDA"; "nd_below"; "ndesc"; "tvinA"; "JA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "vB"; "vCap"; "PreF"; "s_fb"; "PostF"; "vTP"; "CUTS_X"; "DEEP"; "FUEL_X"; "N_ex"; "O_deepM"; "O_deepS"; "dropX"; "s_ex"; "spM"; "spT"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "cls_kept_freeA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite"; "sp0_factsb"; "drv_xrb"; "robjs_checkD"; "xrs_checkD"; "ex_pipe"; "fb_pipe"; "HKP_K"; "HKV_K"; "site_ok_drv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "img_cell_apply"; "img_cell_okb"; "@Stdlib.Lists.List"; "In"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa"; "BX0"; "KP_T"; "KV_T"; "CST_drv"; "HKVrng_T"; "SH0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "rho_absorb"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT.TAddr"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ"; "JAK"; "carve_okb"; "lcarve"; "JA_carve"; "lc_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep";
"RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tvz"; "tnz"; "tvd"; "tvv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "KU"; "bd_below"; "bitem"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "call_checkTA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "KcA"; "alloc_contractsA_ex"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform MuslWLA DrvGlueA DrvGlueB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import PFAddr TAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Section SITE.
Variable AInv : ltac2:(tb__ "0|0|
S71S7S21S46Q40A1A1S3bOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S2dS8fVCST;R1A2S1S55Z0R2A2S56R2SabA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S2dS8fVXGL;R1A2S1S55Z0R2A2S56R2SabA2A2F_;Fa;").
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S2dS8fS88R1A2S8fVCST;R2A2F_;Fz;").
Hypothesis HLPP : law_pp_stmt AInv CST.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sb3S2fSb1VAInv;VCST;VXGL;A5").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Hypothesis HP0SH : ltac2:(tb__ "0|0|
S7VP0f;R1A1S8aR2A1F_;Fr;").
Variable PA : AA -> Prop.
Hypothesis HPAf : ltac2:(tb__ "0|0|
S71S71VPA;R2A1S72R3R2A2VPA;R3A1F_;F_;FA';FA;").

Let JK (nd : ndesc) : jpredA := ltac2:(tb__ "0|1|
S5fVAInv;VCST;VXGL;S48VKc;Vrho0;VP0f;S23S22S2dS2dA2M0A1S23S22G0S2dA2A1S85VPA;Vnd;Ac").
Let carveK : ltac2:(tb__ "0|3|
Sb2S5dS31S7S21S46Q40A1A1S4aS21S94A1S2eS43S2fS92VAInv;VCST;VXGL;S48Vrho0;VP0f;S23S22S2dS2dA2M0A1M1S23S22G0S2dA2A1M2S85VPA;R8R7AcR6R5R4R3A6S30R7A1SbS18S1bR1A1S1cR1A1S1aR1A1S19R1A1S1dR1A1S28S9SdR1A1S73S94S9S96R4A4A3S8R1A1R3S10R1A1A9SbS0S1fS1eR1A1S20A3S0S1fS70SaR3A1R5A2S20A3S0S6S34RbA1ScSacA1A3S0S1fS93S8R5A1SdR5A1S33RcA1S87S86S59RdA1R8A7S20A3S43S2fS92VAInv;VCST;VXGL;S48Vrho0;VP0f;G1G2S85VPA;RfReAcS38RdR5A2RcRbRaA6F_;F_;F_;F_;TS';TS;F_;Fnx;FN;Fw;Ftp;Frho;FA;Fnd;FKc;") := ltac2:(tb__ "0|1|
S95VAInv;VCST;VXGL;VALA;S48Vrho0;VP0f;S23S22S2dS2dA2M0A1S23S22G0S2dA2A1S85VPA;S87S7cVAInv;VCST;VXGL;VALA;VHCSTdrv;VHLPP;VKc;Vrho0;VP0f;VHP0SH;VPA;VPA;AcS89S86S7bVAInv;VCST;VXGL;VHCSTdrv;VKc;Vrho0;VP0f;VHP0SH;VPA;VPA;AaA10").
Let site_ok_drv := site_ok_drv AInv CST XGL ALA HCSTdrv rho0 P0f.

Lemma JK_erun : ltac2:(tb__ "0|1|
S5dS29S21S2dA1S31S21S32A1M0S7S21S46Q40A1A1S4aOF_;S0S24G0A1S35S2fR7R6R5S20A5S25G0R4A2A3S0S1fS10S30R6A1A1S2aA3S0S1fS70S48SaS30R7A1A1A2S20A3S0S1fS5cSaS30R8A1A1RbA2S20A3S32S7S82S32R2RaA3S17SaS30RcA1A1RaR2A3S49S2fS43S2fVJK;R10A1S39R4A1R3RaA5R9A3F_;F_;Frho';FL;S49S2fS43S2fVJK;RdA1RaR8R7A5R6A3F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fleaves;FA;Fcuts;Ffuel;Fnd;").
Proof.
  intros nd fuel cuts A leaves rho tp Q Hrun Hlen Hnf Hnb H. apply Pos.leb_le in Hnf.
  exact (erunA_tr segs fuel cuts A leaves (JK nd) rho tp Q Hrun Hlen (JK_stable AInv CST XGL ALA Kc HKc rho0 P0f PA nd _ Hnf Hnb) H).
Qed.

Lemma final_callJ_ex : ltac2:(tb__ "0|4|
S5dS31S31S8cS21S9A1M0S7S21S46Q40A1A1M1S44S7G1S4aOF_;M2F_;F_;G2S7G1S49S2fS43S2fR5RaR2R1A5R4R2R1A2A3Ftp1;Frho1;S0S24G0A1S7eRaR9R8A3S25G0R7A2A3S21S3aA1M3S90S3bS45S2fRaR9ReS27G3SadR3SaeR2R1A2A4A5VJK;R10RbRaR4R2A5RaS8eS8dRcRdSb0R3RbR4A3A3ReA2RbR5R3A4F_;F_;Fmd;Fms;Ftr;S7S4aR7R2R9R1A3R7R2A1F_;Fw;Frho1;S49S2fS43S2fVJK;ReA1RdR9R8A5R5A3F_;F_;F_;F_;FQ;FQc;FJp;Ftp;Frho;FR;Fs;FPre;FCl;Fnd;").
Proof.
  intros nd Cl Pre s R rho tp Jp Qc Q Hsum He HIN HQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp _ (conj HsmPre (HIN tr ms md Hsm Hk))) as (w' & Hsteps & HQc).
  exists w'. split; [exact Hsteps | exact (HQ _ _ HQc)].
Qed.

Section ExitCallEx.
Variable ph : bool.
Variable ndX : ndesc.
Variables n c : Z.
Variable CX : axst.
Variable s : wsub.
Variable R : list sobj.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S1fS70S48SaS30VCX;A1A1A2S20A3").
Hypothesis Hnb : ltac2:(tb__ "0|0|
S0S1fS5cSaS30VCX;A1A1VndX;A2S20A3").
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0S24S21S9A1M0A1S7eVCX;S51Vph;Vn;Vc;A3Vs;A3S25G0VR;A2A3").
Hypothesis Hsupp : ltac2:(tb__ "0|0|
S82S22S2dS2dA2S27S2dS2dVn;Vc;A4S52Vph;A1A3").
Hypothesis HKfd1 : ltac2:(tb__ "0|0|
S21S3aA1S3bVKc;R2R1A2S0S24S3cA1S40S41R2A1S4cA2S25S3cS3eS4cA1A2A3F_;Fmd;Ftr;").

Variable Q : world -> Prop.
Hypothesis HQ : ltac2:(tb__ "0|1|
S4aS21S3aA1M0S3bVKc;R2R1A2S0G0S4bR4A1S28S3aR3S28S3aS73S46Q8A1S3aS3fS4cA1S4fVn;A1A4S26S3aS3dS47Q40Vc;A2S42R2A1A2S23S3aA1A3A3A3A3VQ;R5A1F_;F_;Fmd;Ftr;Fw;").

Lemma X_exit_call_ex : ltac2:(tb__ "0|0|
S7S21S46Q40A1A1S49S2fS43S2fVJK;VndX;A1VCX;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. pose proof Hnx as Hnx'. apply Pos.leb_le in Hnx'.
  set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) => JK ndX rho t tr md).
  assert (JpK : forall r t tr md, Jp r t tr md -> Kc tr md) by (intros r t tr md HJ; exact (JK_Kc AInv CST XGL Kc rho0 P0f PA ndX _ _ _ _ HJ)).
  apply (final_callJ_ex ndX CX (Pre_exitP ph n c) s R rho tp Jp
           (fun rho1 tp1 w' => exists tr md, Jp rho1 tp1 tr md /\ w_tr w' = tr ++ map (WriteEv ch1) (PEND n) ++ [ExitEv (Z_to_bv 64 c) (m_fs md)])).
  - intros rho1 tp1. apply (exit_sumP_ex Jp n c) with (ph := ph); [| | exact Hsupp].
    + intros r r' t tr md md' Hag Hme HJ. unfold Jp in HJ |- *.
      destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF Kc rho0 P0f [] [] BX0 PA HKc ALA (ss_next (ax_S CX)) ndX Ai kc rho rho t tr md md');
        [exact Hnx' | exact Hnb | apply agree_below_refl | exact Hme | exact HJi].
    + intros r t tr md HJ. apply (HKfd1 tr md). exact (JpK _ _ _ _ HJ).
  - exact Hfr.
  - intros tr ms md Hsm HJ. exact HJ.
  - intros rho1 w (tr & md & HJ & Hw). exact (HQ w tr md (JpK _ _ _ _ HJ) Hw).
Qed.
End ExitCallEx.

Section ExitHandoffEx.
Variable ndX : ndesc.
Variables n c : Z.
Variable E : axst.
Variables S1 S4 S5 S6 : sstate.
Variable idxs : list nat.
Variable R : list sobj.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S1fS70S48SaS30VE;A1A1A2S20A3").
Hypothesis Hnb : ltac2:(tb__ "0|0|
S0S1fS5cSaS30VE;A1A1VndX;A2S20A3").
Hypothesis HbE : ltac2:(tb__ "0|0|
S0S6S34VE;A1ScSacA1A3").
Variable iw : nat.
Hypothesis H1n : ltac2:(tb__ "0|0|
S0S24S9A1S84S9SdS30VE;A1A1Viw;A3S25S9S15S6eScS57S67A1A1ScZ0A1S23S14A1S12A5A2A3").
Variable S0 : sstate.
Hypothesis H1e : ltac2:(tb__ "0|0|
S0SbSa3S30VE;A1Viw;S6bA3VS0;A3").
Hypothesis H1s : ltac2:(tb__ "0|0|
S0S1fS97S30VE;A1VS0;A2S20A3").
Variable ie : nat.
Let S0a : ltac2:(tb__ "0|0|
Sb") := ltac2:(tb__ "0|0|
S80VS0;Vie;S53S4eZ8cA2Z4S54S58Z2Z20A2Z1A2A5").
Let S0b : ltac2:(tb__ "0|0|
Sb") := ltac2:(tb__ "0|0|
S80VS0a;Vie;S53S4eZ10A2Z8Z0A5").
Let S0c : ltac2:(tb__ "0|0|
Sb") := ltac2:(tb__ "0|1|
S80VS0b;Vie;S53S4eZ8M0A2G0Z0A5").
Let S0d : ltac2:(tb__ "0|0|
Sb") := ltac2:(tb__ "0|0|
S80VS0c;Vie;S53S4eZ38A2Z8Z0A5").
Hypothesis H1i : ltac2:(tb__ "0|2|
S1S0S1fS81S2fVS0;Vie;S53S4eZ8cA2Z4S54S58Z2Z20A2Z1A2A6S20A3S1S0S1fS81S2fVS0a;Vie;S53S4eZ10A2Z8M0Z0M1A6S20A3S1S0S1fS81S2fVS0b;Vie;S53S4eG0A2G0G1A6S20A3S1S0S1fS81S2fVS0c;Vie;S53S4eZ38A2G0G1A6S20A3S0S1fS81S2fVS0d;Vie;S53S4eZ28A2G0G1A6S20A3A2A2A2A2").
Hypothesis H1j : ltac2:(tb__ "0|0|
S0SbS80VS0d;Vie;S53S4eZ28A2Z8Z0A5VS1;A3").
Hypothesis H2 : ltac2:(tb__ "0|0|
S0S1fS9eS2bS9SdVS1;A1A2Vidxs;A2S20A3").
Hypothesis H3 : ltac2:(tb__ "0|0|
S0S24SbA1S9aS9dVS1;S99SdVS1;A1Vidxs;A2A2U0A2S25SbVS4;A2A3").
Hypothesis H4 : ltac2:(tb__ "0|0|
S0S24SbA1S9bVS4;U0ScN430A1A3S25SbVS5;A2A3").
Let S5c := ex_S5c E S5.
Hypothesis H5n : ltac2:(tb__ "0|0|
S0S2eSaVS5;A1SaS30VE;A1A1A3").
Hypothesis H5w : swf S5c = true.
Hypothesis H5c : ltac2:(tb__ "0|0|
S0S1fS93S8VS5;A1SdVS5;A1S23S22S6S6A2A1S87S86S59VndX;A1S69A7S20A3").
Hypothesis H6e : ex_S6 S5c = S6.
Hypothesis H6w : swf S6 = true.
Variable d6 : list (sv * sv).
Hypothesis H6d : ltac2:(tb__ "0|3|
S0S24S22S21S22S6S6A2A1M0S21SeA1M1A2M2A1S98VS5c;VS6;A2S25G2S27G0G1Vd6;S23SeA1A4A2A3").
Hypothesis H6v : ltac2:(tb__ "0|4|
S5S0S21S22S6S6A2M0A1M1Vd6;S26G0S27S6S6S65ScS91A1M2A4S23G0A1M3A3A3S0G1Vd6;S26G0S27S6S6G2S65A4G3A3A3A2").
Hypothesis H6f : ltac2:(tb__ "0|0|
S0S1fS83SeS11S16S65ScS91A1A2A1S8S30VE;A1A1A3S20A3").
Let CX : axst := ltac2:(tb__ "0|0|
S36VS6;S23S22S6S6A2A1S34VE;A1A3").
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0S24S21S9A1M0A1S7eVCX;S50Vn;Vc;A2S6dVCX;Vn;Vc;A3A3S25G0VR;A2A3").
Hypothesis Hsupp : ltac2:(tb__ "0|0|
S82S22S2dS2dA2S27S2dS2dVn;Vc;A4S4dA3").
Hypothesis HKfd1 : ltac2:(tb__ "0|0|
S21S3aA1S3bVKc;R2R1A2S0S24S3cA1S40S41R2A1S4cA2S25S3cS3eS4cA1A2A3F_;Fmd;Ftr;").
Hypothesis HspfE : ltac2:(tb__ "0|0|
S0S1fS75S8S30VE;A1A1A1S20A3").
Variable Q : world -> Prop.
Hypothesis HQ : ltac2:(tb__ "0|1|
S4aS21S3aA1M0S3bVKc;R2R1A2S0G0S4bR4A1S28S3aR3S28S3aS73S46Q8A1S3aS3fS4cA1S4fVn;A1A4S26S3aS3dS47Q40Vc;A2S42R2A1A2S23S3aA1A3A3A3A3VQ;R5A1F_;F_;Fmd;Ftr;Fw;").

Lemma exit_reshape : ltac2:(tb__ "0|1|
S7S21S46Q40A1A1S4aS74SeSfR3A1S8S30VE;A1A1A3S43S2fVJK;VndX;A1M0VE;R4R3R2A6S43S2fG0VCX;R5R4R3A6F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HF HS.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF | exact HspfE]. }
  assert (Htp : eval rho vTP = eval rho (SLit TP)).
  { pose proof (holds_mem _ _ _ HF H6f) as X. cbn [holds] in X. exact X. }
  assert (HS0 : SPA segs (JK ndX) (ax_setS E S0) rho tp w).
  { rewrite <- H1e. apply (SPA_reslice segs (JK ndX) rho E iw _ O_deepS tp w H1n); try reflexivity.
    - rewrite H1e. exact H1s.
    - unfold O_deepS, spM. rewrite !obj_range_lits by (unfold DEEP; lia). rewrite U_add_lit by lia. unfold DEEP. f_equal; lia.
    - unfold O_deepS, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP; lia). unfold DEEP; lia.
    - exact HS. }
  destruct H1i as (I1 & I2 & I3 & I4 & I5).
  assert (HS1 : SPA segs (JK ndX) (mkAX S1 (ax_X E) (ax_base E)) rho tp w).
  { rewrite <- H1j.
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0d (ax_X E) (ax_base E)) ie _ 8 0 tp w I5).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0c (ax_X E) (ax_base E)) ie _ 8 0 tp w I4).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0b (ax_X E) (ax_base E)) ie _ 8 0 tp w I3).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0a (ax_X E) (ax_base E)) ie _ 8 0 tp w I2).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0 (ax_X E) (ax_base E)) ie _ 4 _ tp w I1). exact HS0. }
  pose proof (AxXform.SPA_select segs (JK ndX) rho (mkAX S1 (ax_X E) (ax_base E)) idxs tp w H2 HS1) as HS2.
  pose proof (SPA_merge segs (JK ndX) rho (mkAX (set_objs S1 (select (ss_objs S1) idxs)) (ax_X E) (ax_base E)) 0 S4 tp w H3 HS2) as HS3.
  pose proof (SPA_split segs (JK ndX) rho (mkAX S4 (ax_X E) (ax_base E)) 0 (SLit (-1072)) S5 tp w H4 HS3) as HS4.
  apply (SPA_x_sub segs (JK ndX) rho (mkAX S5 (ax_X E) (ax_base E)) [] tp w ltac:(intros rr Hrr; destruct Hrr)) in HS4.
  change (ax_setX (mkAX S5 (ax_X E) (ax_base E)) []) with (mkAX S5 [] (ax_base E)) in HS4.
  assert (HS5 : SPA segs (JK ndX) (mkAX S5c [] (ax_base E)) rho tp w).
  { pose proof (carveK Kc ndX (mkAX S5 [] (ax_base E)) rho tp w N_ex (ss_next S5) HS4) as X.
    cbn zeta in X. cbn [ax_S ax_setS ax_X ax_base] in X. apply X.
    - exact H5w.
    - apply Pos.leb_refl.
    - exact HbE.
    - exact H5c. }
  assert (HS6 : SPA segs (JK ndX) (mkAX S6 [] (ax_base E)) rho tp w).
  { change (mkAX S6 [] (ax_base E)) with (ax_setS (mkAX S5c [] (ax_base E)) S6).
    apply (SPA_restate segs (JK ndX) rho (mkAX S5c [] (ax_base E)) S6 tp w d6 [] H6w H6d).
    - rewrite <- H6e. reflexivity.
    - unfold diffs_ok. destruct H6v as [-> | ->]; (constructor; [cbn [fst snd] | constructor]); [exact Htp | symmetry; exact Htp].
    - constructor.
    - exact HS5. }
  unfold CX. exact HS6.
Qed.

Lemma X_exit_ex : ltac2:(tb__ "0|0|
S7S21S46Q40A1A1S49S2fS43S2fVJK;VndX;A1VE;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. apply etriple_factsA. intros HF.
  assert (HnxC : ss_next (ax_S CX) = ss_next (ax_S E)).
  { unfold CX. cbn [ax_S]. rewrite <- H6e. cbn [ss_next ex_S6]. exact H5n. }
  eapply (etriple_conseq (P := SPA segs (JK ndX) CX rho tp)); [intros w HS; exact (exit_reshape rho tp w HF HS) | intros w' Hw'; exact Hw' |].
  apply (X_exit_call_ex true ndX n c CX (s_ex CX n c) R); [rewrite HnxC; exact Hnx | rewrite HnxC; exact Hnb | exact Hfr | exact Hsupp | exact HKfd1 | exact HQ].
Qed.
End ExitHandoffEx.

Lemma X_exit_pipe_ex : ltac2:(tb__ "0|4|
S5dS2dS2dS31S21S9A1M0S4aOF_;S0S24G0A1S79R6R3R5R4A4S25G0R2A2A3S82S22S2dS2dA2S27S2dS2dR6R5A4S4dA3S21S3aA1M1S3bVKc;R2R1A2M2S0S24S3cA1S40S41R2A1S4cA2S25S3cS3eS4cA1A2A3F_;Fmd;Ftr;S4aG1S3bG2S0G1S4bR4A1S28S3aR3S28S3aS73S46Q8A1S3aS3fS4cA1S4fRcA1A4S26S3aS3dS47Q40M3RbA2S42R2A1A2S23S3aA1A3A3A3A3R9R5A1F_;F_;Fmd;Ftr;Fw;S7S21S46G3A1A1S49S2fS43S2fVJK;RcA1R9R2R1A5R7A3Ftp;Frho;F_;F_;F_;F_;FQ;FR;FE;Fc;Fn;FndX;").
Proof.
  intros ndX n c E R Q Hp Hsupp HKfd1 HQ rho tp. unfold ex_pipe in Hp. cbv zeta in Hp.
  destruct (nth_error (ss_objs (ax_S E)) (locate (ss_objs (ax_S E)) spM (SLit (- DEEP)))) as [o|] eqn:E1; [|discriminate].
  destruct (ob_shapeb o spM (SLit (- DEEP)) (SLit 0)) eqn:E2; [|discriminate]. apply ob_shapeb_sound in E2. subst o.
  destruct (same_but_objs _ _) eqn:E3; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:EI; [|discriminate] end.
  apply andb_prop in EI as [EI I5]. apply andb_prop in EI as [EI I4]. apply andb_prop in EI as [EI I3]. apply andb_prop in EI as [I1 I2].
  destruct (select_ok _ _) eqn:E4; [|discriminate].
  destruct (merge_objs_at _ 0) as [S4|] eqn:E5; [|discriminate].
  destruct (split_obj_at S4 0 (SLit (-1072))) as [S5|] eqn:E6; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E7; [|discriminate] end.
  destruct (entails_frA _ _ _) as [R'|] eqn:E8; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E9; [|discriminate] end. injection Hp as HR. subst R'.
  apply andb_prop in E9 as [E9 E10].
  apply andb_prop in E7 as [E7 E7j]. apply andb_prop in E7 as [E7 E7i]. apply andb_prop in E7 as [E7 E7h]. apply andb_prop in E7 as [E7 E7g].
  apply andb_prop in E7 as [E7 E7f]. apply andb_prop in E7 as [E7 E7e]. apply andb_prop in E7 as [E7 E7d]. apply andb_prop in E7 as [E7 E7c].
  apply andb_prop in E7 as [E7a E7b].
  destruct (state_diff (ex_S5c E S5) (ex_S6 (ex_S5c E S5))) as [[d6 [|]]|] eqn:E11; try discriminate.
  apply Pos.eqb_eq in E7a. apply sv_eqb_sound in E7j.
  eapply (X_exit_ex ndX n c E _ S4 S5 (ex_S6 (ex_S5c E S5)) _ R E7h E7i E7j _ E1 _ eq_refl E3 _ (conj I1 (conj I2 (conj I3 (conj I4 I5)))) eq_refl
            E4 E5 E6 E7a E7b E7c eq_refl E7d d6 E11 (d6_okb_sound d6 E7e) E7f E8 Hsupp HKfd1 E7g Q HQ).
Qed.

Section FreeCallEx.
Variables tb tl : sv.
Let t : sv * sv := ltac2:(tb__ "0|0|
S27S6S6Vtb;Vtl;A4").
Variable kept : list (sv * sv).
Variables bdJ bdX : list bitem.
Let ndJ : ndesc := ltac2:(tb__ "0|0|
S5bS26S22S6S6A2Vt;Vkept;A3S23S22S22S6S2dA2S6A2A1VbdJ;S5aA4").
Let ndX : ndesc := ltac2:(tb__ "0|0|
S5bVkept;S23S22S22S6S2dA2S6A2A1VbdX;S5aA4").
Variables (CF : axst) (s : wsub) (R : list sobj) (T : axst).
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0S24S21S9A1M0A1S7eVCF;S62Vs;A3S25G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S0S1fS7fVCF;S62Vs;VR;S26S31S64S23S31A1A3A5S20A3").
Hypothesis HcT : ltac2:(tb__ "0|0|
S0S1fSa9S48Vs;A2S20A3").
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S1fS70S48SaS30VCF;A1A1A2S20A3").
Hypothesis Hnb : ltac2:(tb__ "0|1|
S1S0S1fS5cSaS30VCF;A1A1M0VndJ;A2S20A3S0S1fSa5G0VbdX;A2S20A3A2").
Hypothesis Hs12 : ltac2:(tb__ "0|0|
S1S0S6S8bVs;PcA2Vtb;A3S0S6S8bVs;PdA2Vtl;A3A2").
Hypothesis Hpay : ltac2:(tb__ "0|0|
S0S1fSa7S8S30VCF;A1A1ScZ0A1Sa4VbdJ;VbdX;A5S20A3").
Hypothesis Hspf : ltac2:(tb__ "0|0|
S0S1fS75S8S30VCF;A1A1A1S20A3").
Hypothesis Hro : ltac2:(tb__ "0|0|
S0S1fS77S8S30VCF;A1A1S26S22S6S6A2Vt;Vkept;A3S25S29U0A2VR;A4S20A3").
Hypothesis Hxr : ltac2:(tb__ "0|1|
S0S1fS78S8S30VCF;A1M0A1S26S22S6S6A2Vt;Vkept;A3S25S29U0A2SdG0A1S76S33VCF;A1A6S20A3").
Hypothesis Hnz : ltac2:(tb__ "0|0|
S0S1fS83SeS11S13ScZ1000A1Vtb;A2A1S8S30VCF;A1A1A3S20A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S31Sa8S62VCF;Vs;VR;S64A5VT;A3").
Variable Q : world -> Prop.
Hypothesis HT' : ltac2:(tb__ "0|0|
S7S21S46Q40A1A1S49S2fS43S2fVJK;VndX;A1VT;R2R1A5VQ;A3Ftp';Frho';").

Lemma X_free_call_ex : ltac2:(tb__ "0|0|
S7S21S46Q40A1A1S49S2fS43S2fVJK;VndJ;A1VCF;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. destruct Hnb as [Hnb1 Hnb2]. destruct Hs12 as [Hs12a Hs13].
  apply etriple_factsA. intros HF.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF | exact Hspf]. }
  assert (Htnz : tnz rho t).
  { unfold tnz, t. cbn [fst]. pose proof (holds_mem _ _ _ HF Hnz) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X.
    rewrite Z.mod_small in X by lia. unfold uval in X |- *. lia. }
  apply (free_callA_ex segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 P0f [] [] BX0 PA HKc [] UStopLe CF s R rho tp
           ndJ 0%nat t bdX Q free_shape_nil ACX Hfr Hcc HcT Hnx Hnb1 Hnb2 eq_refl).
  - apply payA_of_bud_pay. exact Hpay.
  - exact HPAf.
  - apply (site_ok_drv ndJ CF s R rho (Some 0%nat) (Some (uval rho (wsub_get s 12%positive)))); try assumption.
    + intros Ai HF' HN HZ. exists t. split; [reflexivity|]. rewrite Hs12a. split; [exact Htnz | reflexivity].
    + intros Ai ms HF' HP0 Hav HN HD HZ HM. split; [|split; [| exact I]].
      * exact Htnz.
      * rewrite Hs12a, Hs13. reflexivity.
  - intros rho' tp'. unfold PreF, PostF in HT. rewrite HT. cbn [nd_tv nd_fr nd_am ndJ remove_nth]. fold ndX. apply HT'.
Qed.
End FreeCallEx.

Section FbChainEx.
Variable A0 : axst.
Variable bdJ bdX : list bitem.
Let ndJ' : ndesc := ltac2:(tb__ "0|1|
S5bS26S22S6S6A2M0S27S6S6S60S61A4S23G0A1A3S23S22S22S6S2dA2S6A2A1VbdJ;S5aA4").
Let ndX' : ndesc := ltac2:(tb__ "0|0|
S5bS23S22S6S6A2A1S23S22S22S6S2dA2S6A2A1VbdX;S5aA4").
Variables (E : axst) (S2 S4 : sstate) (idxs : list nat) (R : list sobj) (T Ex : axst).
Variable iw : nat.
Hypothesis HJwf : ltac2:(tb__ "0|2|
S1S0S1fS70S48SaS30VA0;A1M0A1M1A2S20A3S1S0S1fS10G0A1S2aA3S0S1fS5cG1VndJ';A2S20A3A2A2").
Hypothesis Hrun1 : ltac2:(tb__ "0|1|
S0S24S21S32A1M0A1S35S2fS68S66VA0;S20A5S25G0S26S32S37VE;S9cA2S23S32A1A3A2A3").
Hypothesis H1n : ltac2:(tb__ "0|0|
S0S24S9A1S84S9SdS30VE;A1A1Viw;A3S25S9S15S6fScS57S54S67Z50A2A1A1ScZ0A1S23S14A1S12A5A2A3").
Hypothesis H1e : ltac2:(tb__ "0|0|
S0SbSa3S30VE;A1Viw;S6aA3VS2;A3").
Hypothesis H1s : ltac2:(tb__ "0|0|
S0S1fS97S30VE;A1VS2;A2S20A3").
Hypothesis H2 : ltac2:(tb__ "0|0|
S0S1fS9eS2bS9SdVS2;A1A2Vidxs;A2S20A3").
Hypothesis H3 : ltac2:(tb__ "0|0|
S0S24SbA1S9aS9dVS2;S99SdVS2;A1Vidxs;A2A2U0A2S25SbVS4;A2A3").
Let CF : axst := ltac2:(tb__ "0|0|
S6cS27S6S6S60S61A4S36VS4;S33VE;A1S34VE;A1A3A2").
Hypothesis H4n : ltac2:(tb__ "0|0|
S0S2eSaVS4;A1SaS30VE;A1A1A3").
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0S24S21S9A1M0A1S7eVCF;S62S63VCF;A1A3S25G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S0S1fS7fVCF;S62S63VCF;A1VR;S26S31S64S23S31A1A3A5S20A3").
Hypothesis HcT : ltac2:(tb__ "0|0|
S0S1fSa9S48S63VCF;A1A2S20A3").
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S1fS70S48SaS30VE;A1A1A2S20A3").
Hypothesis Hnb : ltac2:(tb__ "0|1|
S1S0S1fS5cSaS30VE;A1A1M0VndJ';A2S20A3S0S1fSa5G0VbdX;A2S20A3A2").
Hypothesis Hs12 : ltac2:(tb__ "0|1|
S1S0S6S8bS63VCF;A1M0PcA2S60A3S0S6S8bG0PdA2S61A3A2").
Hypothesis Hpay : ltac2:(tb__ "0|0|
S0S1fSa7S8S30VCF;A1A1ScZ0A1Sa4VbdJ;VbdX;A5S20A3").
Hypothesis HspfE : ltac2:(tb__ "0|0|
S0S1fS75S8S30VE;A1A1A1S20A3").
Hypothesis Hspf : ltac2:(tb__ "0|0|
S0S1fS75S8S30VCF;A1A1A1S20A3").
Hypothesis Hro : ltac2:(tb__ "0|1|
S0S1fS77S8S30VCF;A1A1S26S22S6S6A2M0S27S6S6S60S61A4S23G0A1A3S25S29U0A2VR;A4S20A3").
Hypothesis Hxr : ltac2:(tb__ "0|2|
S0S1fS78S8S30VCF;A1M0A1S26S22S6S6A2M1S27S6S6S60S61A4S23G1A1A3S25S29U0A2SdG0A1S76S33VCF;A1A6S20A3").
Hypothesis HvB : ltac2:(tb__ "0|0|
S0S1fS83SeS11S13ScZ1000A1S60A2A1S8S30VCF;A1A1A3S20A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S31Sa8S62VCF;S63VCF;A1VR;S64A5VT;A3").
Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S1fS70S48SaS30VT;A1M0A1M1A2S20A3S1S0S1fS10G0A1S2aA3S0S1fS5cG1VndX';A2S20A3A2A2").
Hypothesis Hrun2 : ltac2:(tb__ "0|1|
S0S24S21S32A1M0A1S35S2fS68S66VT;S20A5S25G0S26S32S37VEx;S9cA2S23S32A1A3A2A3").
Variable Q : world -> Prop.
Hypothesis HX : ltac2:(tb__ "0|0|
S7S21S46Q40A1A1S49S2fS43S2fVJK;VndX';A1VEx;R2R1A5VQ;A3Ftp;Frho;").

Lemma fb_reshape : ltac2:(tb__ "0|1|
S7S21S46Q40A1A1S4aS74SeSfR3A1S8S30VE;A1A1A3S43S2fVJK;VndJ';A1M0VE;R4R3R2A6S43S2fG0VCF;R5R4R3A6F_;F_;Fw;Ftp;Frho1;").
Proof.
  intros rho1 tp w HF HS.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho1 sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF | exact HspfE]. }
  assert (HS1 : SPA segs (JK ndJ') (ax_setS E S2) rho1 tp w).
  { rewrite <- H1e. apply (SPA_reslice segs (JK ndJ') rho1 E iw _ O_deepM tp w H1n); try reflexivity.
    - rewrite H1e. exact H1s.
    - unfold O_deepM, spT. rewrite !obj_range_lits by (unfold DEEP; lia). rewrite U_add_lit by lia. unfold DEEP. f_equal; lia.
    - unfold O_deepM, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP; lia). unfold DEEP; lia.
    - exact HS. }
  pose proof (AxXform.SPA_select segs (JK ndJ') rho1 (mkAX S2 (ax_X E) (ax_base E)) idxs tp w H2 HS1) as HS2.
  pose proof (SPA_merge segs (JK ndJ') rho1 (mkAX (set_objs S2 (select (ss_objs S2) idxs)) (ax_X E) (ax_base E)) 0 S4 tp w H3 HS2) as HS3.
  unfold CF, dropX. apply SPA_x_sub; [|exact HS3]. cbn [ax_X]. apply In_dropX.
Qed.

Lemma X_fb_ex : ltac2:(tb__ "0|0|
S7S21S46Q40A1A1S49S2fS43S2fVJK;VndJ';A1VA0;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. destruct HJwf as (W1 & W2 & W3). destruct Hnb as [Hnb1 Hnb2]. destruct HTwf as (V1 & V2 & V3).
  eapply JK_erun; [exact Hrun1 | exact W2 | exact W1 | exact W3 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply etriple_factsA. intros HF.
  eapply (etriple_conseq (P := SPA segs (JK ndJ') CF rho1 tp)); [intros w HS; exact (fb_reshape rho1 tp w HF HS) | intros w' Hw'; exact Hw' |].
  assert (HnxC : ss_next (ax_S CF) = ss_next (ax_S E)) by (unfold CF, dropX; cbn [ax_S ax_setX]; exact H4n).
  apply (X_free_call_ex vB vCap [] bdJ bdX CF (s_fb CF) R T Hfr Hcc HcT); try assumption.
  - rewrite HnxC. exact Hnx.
  - rewrite HnxC. split; [exact Hnb1 | exact Hnb2].
  - intros rho' tp'. eapply JK_erun; [exact Hrun2 | exact V2 | exact V1 | exact V3 |].
    intros L rho3 [<-|[]] Hag3. cbn [la_state]. apply HX.
Qed.
End FbChainEx.

Lemma X_fb_pipe_ex : ltac2:(tb__ "0|5|
S21Sa6A1M0G0S31S31S4aOF_;S0S24S31A1S7aR5R4R3A3S25S31R2A2A3S7S21S46Q40A1A1M1S49S2fS43S2fVJK;S5bS23S22S6S6A2M2A1M3S23S22S22S6S2dA2S6A2A1M4R7S5aA4A1R5R2R1A5R4A3Ftp;Frho;S7G1S49S2fS43S2fVJK;S5bS26G2S27S6S6S60S61A4G3A3G4R9S5aA4A1R7R2R1A5R5A3Ftp;Frho;F_;F_;FQ;FEx;FA0;FbdX;FbdJ;").
Proof.
  intros bdJ bdX A0 Ex Q Hp HX rho tp. unfold fb_pipe in Hp. cbv zeta in Hp.
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E0; [|discriminate] end.
  apply andb_prop in E0 as [E0 E0c]. apply andb_prop in E0 as [E0a E0b]. apply negb_true in E0b.
  destruct (one_leaf (sym_runA segs FUEL_X CUTS_X A0 true)) as [E|] eqn:E1; [|discriminate]. apply one_leaf_sound in E1.
  destruct (nth_error (ss_objs (ax_S E)) _) as [o|] eqn:E2; [|discriminate].
  destruct (ob_shapeb o _ _ _) eqn:E3; [|discriminate]. apply ob_shapeb_sound in E3. subst o.
  destruct (same_but_objs _ _) eqn:E4; [|discriminate].
  destruct (select_ok _ _) eqn:E5; [|discriminate].
  destruct (merge_objs_at _ 0) as [S4|] eqn:E6; [|discriminate].
  destruct (entails_frA _ PreF _) as [R|] eqn:E7; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E8; [|discriminate] end.
  apply one_leaf_sound in Hp.
  apply andb_prop in E8 as [E8 Q3]. apply andb_prop in E8 as [E8 Q2]. apply andb_prop in E8 as [E8 Q1]. apply negb_true in Q2.
  apply andb_prop in E8 as [E8 P14]. apply andb_prop in E8 as [E8 P13]. apply andb_prop in E8 as [E8 P12].
  apply andb_prop in E8 as [E8 P11]. apply andb_prop in E8 as [E8 P10]. apply andb_prop in E8 as [E8 P9].
  apply andb_prop in E8 as [E8 P8]. apply andb_prop in E8 as [E8 P7]. apply andb_prop in E8 as [E8 P6].
  apply andb_prop in E8 as [E8 P5]. apply andb_prop in E8 as [E8 P4]. apply andb_prop in E8 as [E8 P3]. apply andb_prop in E8 as [P1 P2].
  apply Pos.eqb_eq in P1. apply sv_eqb_sound in P7. apply sv_eqb_sound in P8.
  eapply (X_fb_ex A0 bdJ bdX E _ S4 _ R _ Ex _ (conj E0a (conj E0b E0c)) E1 E2 eq_refl E4 E5 E6 P1 E7 P2 P3 P4 (conj P5 P6) (conj P7 P8)
            P9 P10 P11 P12 P13 P14 eq_refl (conj Q1 (conj Q2 Q3)) Hp Q HX).
Qed.

Lemma X_join_ex : ltac2:(tb__ "0|8|
S21Sa6A1M0G0S31S2dS2dS31S21S9A1M1S4aOF_;S0S24S31A1S7aR8R7R6A3S25S31R3A2A3S0S24G1A1S79S5bS23S22S6S6A2M2A1M3S23S22S22S6S2dA2S6A2A1M4R8S5aA4R4R6R5A4S25G1R3A2A3S82S22S2dS2dA2S27S2dS2dR7R6A4S4dA3S21S3aA1M5S3bVKc;R2R1A2M6S0S24S3cA1S40S41R2A1S4cA2S25S3cS3eS4cA1A2A3F_;Fmd;Ftr;S4aG5S3bG6S0G5S4bR4A1S28S3aR3S28S3aS73S46Q8A1S3aS3fS4cA1S4fRdA1A4S26S3aS3dS47Q40M7RcA2S42R2A1A2S23S3aA1A3A3A3A3RaR5A1F_;F_;Fmd;Ftr;Fw;S7S21S46G7A1A1S49S2fS43S2fVJK;S5bS26G2S27S6S6S60S61A4G3A3G4RfS5aA4A1RdR2R1A5R8A3Ftp;Frho;F_;F_;F_;F_;F_;FQ;FR;FEx;Fc;Fn;FA0;FbdX;FbdJ;").
Proof.
  intros bdJ bdX A0 n c Ex R Q Hfb Hex Hsupp HKfd1 HQ.
  apply (X_fb_pipe_ex bdJ bdX A0 Ex Q Hfb). apply (X_exit_pipe_ex (NDA [] [] bdX ANone) n c Ex R Q Hex Hsupp HKfd1 HQ).
Qed.

End SITE.
End DrvSiteEx.

