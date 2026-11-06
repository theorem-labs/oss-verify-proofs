(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "prod"; "nil"; "bool"; "true"; "option"; "length"; "app"; "nat"; "Some"; "cons"; "pair"; "false"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "False"; "or"; "True"; "not"; "proj1"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "ss_facts"; "eval"; "sobj"; "ss_next"; "agree_below"; "sv"; "ss_objs"; "holds"; "sprop"; "SLit"; "rl"; "ss_lenient"; "sstate"; "SAlu"; "mkSS"; "obj_holds"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM.M"; "JM"; "P0M"; "KcM"; "JMe"; "P0M_SH"; "JM_stable"; "Jop"; "KcM_ok"; "KcM_tc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "FdEntry"; "errno_ret"; "cstr_result"; "with_fds"; "CstrOk"; "CstrTooLong"; "FdChannel"; "fd_lookup"; "m_fds"; "m_fs"; "VmState"; "cstr_access_len_aux"; "read_cstr"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "of_nat"; "sub"; "div"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "ax_X"; "ax_setS"; "la_state"; "ax_base"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "nd_tv"; "JA"; "nd_below"; "ANone"; "JAi"; "tvinA"; "amode"; "apot"; "bxa"; "nd_am"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa"; "BX0"; "KV_T"; "HKVrng_T"; "KP_T"; "CST_drv"; "HCSTKV_T"; "SH0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM_states"; "nd_M"; "vFD"; "E_op"; "T_op"; "E_copen"; "L_R0"; "L_R0h"; "nd_R1"; "C_m65"; "bd_M0"; "s_R0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "tcons"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR"; "FD3"; "KcG"; "std_fds"; "P0Z"; "S_R0"; "nd_R0"; "SHR"; "SHR2"; "ZARG"; "CST_drv2"; "SLK1"; "Uv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "cls_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "open_may_succeed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ"; "lcarve"; "JAK"; "lc_obj"; "JA_carve"; "JA_uncarve"; "carve_okb"; "uncarve_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceM"; "S_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "Kc_ok"; "alloc_contractsA"; "alloc_contractsA_ex"; "with_vm"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@Corelib.Init.Nat"; "add"; "@Corelib.Init.Peano"; "le"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_read_byte"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "sys_input"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "IMG_HI"; "SHADOW_OFF";
"@Stdlib.PArith.BinPos.Pos"; "le"; "leb"; "leb_le"; "succ"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "path_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExit"; "ch1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw"; "ch2"; "EVS"; "Kw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite"; "HKV_K"; "HKP_K"; "JK_run"; "drv_xrb"; "robjs_checkD"; "site_ok_drv"; "sp0_factsb"; "xrs_checkD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "hid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tvz"; "tnz"; "tvd"; "tvv"; "@Stdlib.Arith.PeanoNat.Nat"; "ltb"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei"; "dotdot_path"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open"; "openat_errnos"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "O_arg1"; "sp0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM.M.Arg1"; "cstr1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "openat_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Restrict"; "ranges_avoid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysOpen"; "openat_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA"; "erunA_tr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "BUD"; "bx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceS"; "alloc_roomA"; "malloc_contractA_strong"; "malloc_contractA_strong_ex"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymCall SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV SysOpen.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface IfaceEx IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform MuslWLA DrvGlueA DrvGlueB SysA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.ErrnoA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvFw DrvIfaceT DrvIfaceR DrvIfaceM DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ot.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ob.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvR_facts DrvM_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oe.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ot.DrvSiteEx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nw.DrvJRe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.DrvRGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.DrvR_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvR_tstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvR_facts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oe.DrvM_tstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nl.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvErrno.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import PFAddr TAddr MAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma cstr_access_len_le : ltac2:(tb__ "0|6|
S19Q40M0A1S7S19Q8M1A1M2A1M3Fx;S2G2A1SaS0S51Z0M4R1A2S52S53S53R2S55S8G2R4A2A1A2Z1A2S54Z2Z40A2A2SaSa6R1S8G2R6A2A2S11G3R8S1aG0S53R5S55R2A1A2A2A1SbG2SaaG2R2S9G2R7ScG2S1aG1G4A2M5S4G2A1A3A3G5A4A2A3F_;Fj;S17Sa3G2G5R6A3A1Sa6S4fR8S1aG0R5A2R6A3Sa5S8G2R7A2U1A2A2F_;F_;F_;F_;Fz;Ffuel;Fs;Fmp;").
Proof.
  intros mp s. induction s as [|b s IH]; intros fuel z Hz Hnw Hmp Hnin.
  - destruct fuel as [|fuel]; cbn [cstr_access_len_aux length]; [lia|].
    specialize (Hmp 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in Hmp. cbn in Hmp. rewrite Hmp.
    unfold bv_eqb. rewrite Z.eqb_refl. lia.
  - destruct fuel as [|fuel]; cbn [cstr_access_len_aux length]; [lia|].
    pose proof (Hmp 0%nat ltac:(cbn; lia)) as H0. rewrite Z.add_0_r in H0. cbn [nth app] in H0. rewrite H0.
    assert (Hb : bv_eqb b (Z_to_bv 8 0) = false).
    { unfold bv_eqb. apply Z.eqb_neq. intros E. apply Hnin. left. apply bv_eq. exact E. }
    rewrite Hb. rewrite Z_to_bv64_add1. cbn [length] in Hnw.
    enough (cstr_access_len_aux mp (Z_to_bv 64 (z + 1)) fuel <= length s + 1)%nat by lia.
    apply IH; [lia | lia | | intros Hin; apply Hnin; right; exact Hin].
    intros j Hj. replace (z + 1 + Z.of_nat j) with (z + Z.of_nat (S j)) by lia.
    rewrite (Hmp (S j)) by (cbn [length]; lia). reflexivity.
Qed.

Lemma U_lit64 : ltac2:(tb__ "0|0|
S1cS0S12S51Z0R1A2S52R1S54Z2Z40A2A2A2S11S0S1bQ40S1fR3S27R2A1A2A2R2A3F_;Fz;Frho;").
Proof. intros rho z Hz. rewrite CursorGlue.U_lit, <- M64v_eq. apply Z.mod_small. lia. Qed.

Lemma fd3_lookup1 : ltac2:(tb__ "0|0|
S2S19Q8A1A1S11S7S44A1S4bS83R1A1Sb9A2SbS44S4aSb9A1A2A3Fp;").
Proof. intros p. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fd3_lookup2 : ltac2:(tb__ "0|0|
S2S19Q8A1A1S11S7S44A1S4bS83R1A1SbaA2SbS44S4aSbaA1A2A3Fp;").
Proof. intros p. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma ZARG_pcl2 : ltac2:(tb__ "0|2|
S0S0S0S51Z7fff80000000R3A2S51S53R4R3A2S54Z2Z2fA2M0A2S12S51S58S57Sb0R5A1Z8M1A2G1A2R3A2S52R3S53S58S57Sb0S56S53R5R4A2Z1A2A1G1A2G1A2G1A2A2A2S13S0S0S12S51Z0R1A2S12S12S51S56R7Z40A2R1A2S52R1G0A2A2S11S0R5Sb0R1A1A3A2A2Lx;A2F_;F_;F_;Fz;Fal;Fsp;").
Proof.
  intros sp al z Hsp Hal Hz. unfold Sh, SHADOW_OFF in *.
  pose proof (Z.div_mod (sp / 8 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sp / 8 + 2147450880) 8 ltac:(lia)).
  pose proof (Z.div_mod sp 8 ltac:(lia)). pose proof (Z.mod_pos_bound sp 8 ltac:(lia)).
  assert (U : (sp + al - 1) / 8 <= 2 ^ 44 - 1).
  { replace (2 ^ 44 - 1) with ((2 ^ 47 - 1) / 8) by reflexivity. apply Z.div_le_mono; lia. }
  assert (U2 : ((sp + al - 1) / 8 + 2147450880) / 8 <= (2 ^ 44 - 1 + 2147450880) / 8) by (apply Z.div_le_mono; lia).
  change ((2 ^ 44 - 1 + 2147450880) / 8) with (2 ^ 41 + 268431359) in U2.
  exists (8 * (z - 2147450880)). split; [lia|]. split; [lia|].
  rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Section M.
Variable AInv : ltac2:(tb__ "0|0|
S8fS1cS2S19Q40A1A1S42OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S95VCST;R1A2S12S51Z0R2A2S52R2Sb1A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S95VXGL;R1A2S12S51Z0R2A2S52R2Sb1A2A2F_;Fa;").
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HLF : law_fds_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S0S95S70R1A2S95VCST;R2A2F_;Fz;").
Hypothesis HLPP : law_pp_stmt AInv CST.
Hypothesis HCSTdrv2 : ltac2:(tb__ "0|0|
S0S95S8cR1A2S95VCST;R2A2F_;Fz;").
Variable ok : world -> Prop.
Variable Spec : list event -> Prop.
Hypothesis HOKJ : ltac2:(tb__ "0|0|
S35S1cS2S19Q40A1A1S2S43A1S42R5R4R3R2R1A4S81VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;S36S10Vok;R2A3F_;FJ;").
Hypothesis HOKP : ltac2:(tb__ "0|0|
S35S1cS2S19Q40A1A1S2S43A1S42R5R4R3R2R1A4S81VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;Sc6S10Vok;R2A3F_;FJ;").
Hypothesis Hokh : ok_halted ok Spec.
Hypothesis AC : ltac2:(tb__ "0|0|
Sa0S10S9eVAInv;VCST;VXGL;A5").

Hypothesis MS : ltac2:(tb__ "0|0|
Se2S10S9eVAInv;VCST;VXGL;A5").

Variable rhoM : valuation.
Hypothesis HtopM : ltac2:(tb__ "0|1|
S11S0S53S1bQ40M0S1dVrhoM;P1eA2A2Z800000A2S1bG0S1dVrhoM;P1A2A2A3").
Variable argv1 : list byte.
Variable T0 : list event.
Variable MDX : Model -> Prop.
Variable FS0 : Fs.
Hypothesis HMDXvm : ltac2:(tb__ "0|0|
S42S4eVMDX;R2A1VMDX;Sa2R2R3A2A1F_;Fv;Fmd;").
Hypothesis HMDXfds : ltac2:(tb__ "0|0|
S42S2S3S19Q40A1S44A2A1VMDX;R2A1VMDX;S47R2R3A2A1F_;Ff;Fmd;").
Hypothesis HMDXfs : ltac2:(tb__ "0|0|
S42VMDX;R1A1S11Sb7S4dR2A1VFS0;A3F_;Fmd;").
Hypothesis Hnonul : ~ In (Z_to_bv 8 0) argv1.
Hypothesis Hndd : ltac2:(tb__ "0|0|
S11S5Sb8Vargv1;ScfA2SeA3").
Hypothesis Hnsl : path_has_slash argv1 = false.
Hypothesis HtcT0 : tcons Spec T0.

Variable PA : AA -> Prop.
Hypothesis HPAm : ltac2:(tb__ "0|0|
S8fS8fS0S51Zfc01R1A2VPA;R4A1S93R5R4R3A3VPA;R5A1F_;F_;F_;Fn;FA';FA;").

Definition KcM (fds : list (word * FdEntry)) : KcA := ltac2:(tb__ "0|0|
S84VT0;VMDX;Vfds;S4S43A1A4").

Definition P0M (r : valuation) : Prop := ltac2:(tb__ "0|3|
S12S89Vr;A1S12S11S2S19Q8M0A1M1A1Sa9G1Sa5S8G1Vargv1;A2M2U1A2S28Vr;P3A2A3S9G1Vargv1;ScG1S1aG0Z0A2S4G1A1A3A3A3S12S11S0S8eVr;P9A2S55G2A1A3S12S12S8bVr;A1S8aVr;A1A2S8dVr;A1A2A2A2A2").
Definition JM (fds : list (word * FdEntry)) (nd : ndesc) : jpredA := ltac2:(tb__ "0|1|
S63VAInv;VCST;VXGL;S41S3aVfds;A1VrhoM;S39S4S3S0S0A2M0A1S4S3G0S0A2A1S6cVPA;Vnd;Ac").

Lemma KcM_ok : ltac2:(tb__ "0|0|
S2S3S19Q40A1S44A2A1S9fS3aR1A1A1Ffds;").
Proof. intros fds. apply KcG_ok. exact HMDXvm. Qed.
Lemma P0M_SH : ltac2:(tb__ "0|0|
S1cS39R1A1S72R2A1F_;Fr;").
Proof. intros r [[H _] _]. exact H. Qed.
Lemma KcM_tc : ltac2:(tb__ "0|0|
S2S3S19Q40A1S44A2A1S2S43A1S42S3aR3R2R1A3S81VSpec;R3A2F_;Fmd;Ftr;Ffds;").
Proof. intros fds tr md (-> & _ & _). rewrite app_nil_r. exact HtcT0. Qed.
Lemma JM_Kc : ltac2:(tb__ "0|3|
S2S3S19Q40A1M0S44A2A1M1S61S1cS2G0A1S2S43A1M2S42S38R6R5R4R3R2R1A6S12S11G2R3S9S43VT0;S4S43A1A3A3S12S11G1S4cR2A1R7A3VMDX;R2A1A2A2F_;Fmd;Ftr;Ftp;Frho;Fnd;Ffds;").
Proof. intros fds nd rho tp tr md (Ai & kc & _ & H & _). exact H. Qed.
Lemma JM_P0 : ltac2:(tb__ "0|1|
S2S3S19Q40A1M0S44A2A1S61S1cS2G0A1S2S43A1S42S38R6R5R4R3R2R1A6S12S39VrhoM;A1Sc5S41VrhoM;R5A3A2F_;Fmd;Ftr;Ftp;Frho;Fnd;Ffds;").
Proof. intros fds nd rho tp tr md (Ai & kc & Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _). split; [exact HP0 | exact Hav]. Qed.
Lemma JM_stable : ltac2:(tb__ "0|0|
S2S3S19Q40A1S44A2A1S61S1Sb3S41R1A2S11S5S64R2R3A2S6A3S37S10R3S38R5R4A2A3F_;F_;Fn;Fnd;Ffds;").
Proof. intros fds nd n Hn Hb. apply (stableA_JA segs AInv CST XGL NF _ rhoM P0M [] [] BX0 PA (KcM_ok fds) ALA n nd Hn Hb). Qed.
Lemma JM_okframe : ltac2:(tb__ "0|0|
S2S3S19Q40A1S44A2A1S61S36S10Vok;S38R2R1A2A3Fnd;Ffds;").
Proof. intros fds nd. apply HOKJ. intros rho tp tr md H. destruct (JM_Kc _ _ _ _ _ _ H) as (-> & _). rewrite app_nil_r. exact HtcT0. Qed.
Lemma JM_okpframe : ltac2:(tb__ "0|0|
S2S3S19Q40A1S44A2A1S61Sc6S10Vok;S38R2R1A2A3Fnd;Ffds;").
Proof. intros fds nd. apply HOKP. intros rho tp tr md H. destruct (JM_Kc _ _ _ _ _ _ H) as (-> & _). rewrite app_nil_r. exact HtcT0. Qed.

Let JM_run (fds : list (word * FdEntry)) : ltac2:(tb__ "0|3|
S61SaS2S0A1S5bS2S5aA1M0S1cS2S19Q40A1A1S82S11S7G0A1S60S10R7R6R5S6A5SbG0R4A2A3S11S5S29S59R6A1A1SeA3S11S5Sb4S41S21S59R7A1A1A2S6A3S11S5S64S21S59R8A1A1RbA2S6A3S5aS1cSa3S5aR2RaA3S22S21S59RcA1A1RaR2A3S7fS10Vok;S34S10S61S63VAInv;VCST;VXGL;S41S3aVfds;A1VrhoM;S39S4S3S0S0A2M1A1S4S3G1S0A2A1S6cVPA;R1AcLnd;M2R10A1S5eR4A1R3RaA5R9A4F_;F_;Frho';FL;S7fS10Vok;S34S10G2RdA1RaR8R7A5R6A4F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fleaves;FA;Fcuts;Ffuel;Fnd;") := ltac2:(tb__ "0|0|
SbfVAInv;VCST;VXGL;VALA;Vok;VSpec;VHOKJ;S3aVfds;A1S3fVfds;A1VrhoM;S39S40Vfds;A1VPA;Ad").
Let site_ok_drvM := site_ok_drv AInv CST XGL ALA HCSTdrv rhoM P0M.

Lemma JM_with_fds : ltac2:(tb__ "0|2|
S2S3S19Q40A1M0S44A2A1M1G1S61S1cS2G0A1S2S43A1S42S38R7R5R4R3R2R1A6S38R7R6R5R4R3S47R7R2A2A6F_;Fmd;Ftr;Ftp;Frho;Fnd;Ffds';Ffds;").
Proof.
  intros fds fds' nd rho tp tr md (Ai & kc & Hav & Hk & HM & REST). exists Ai, kc.
  split; [exact Hav|]. split.
  - destruct Hk as (H1 & H2 & H3). split; [exact H1|]. split; [apply m_fds_with_fds | apply HMDXfds; exact H3].
  - split; [apply HLF; exact HM | exact REST].
Qed.

Lemma JM_set_rw : ltac2:(tb__ "0|1|
S2S3S19Q40A1M0S44A2A1S61S1cS2G0A1S2S43A1S42S1G0Sb3S41R2A2S11S5S64R3R8A2S6A3S38RaR9R8R7R6R5A6S38RbRaSd6R9R5R4A3R8R7R6A6F_;F_;F_;Fr;Fv;Fmd;Ftr;Ftp;Frho;Fnd;Ffds;").
Proof.
  intros fds nd rho tp tr md v r Hv Hb H.
  eapply (JM_stable fds nd v Hv Hb); [apply agree_below_set_rw; lia | apply mat_equiv_refl | exact H].
Qed.

Lemma SHR_now : ltac2:(tb__ "0|2|
S2S3S19Q40A1M0S44A2A1S61S8fS0S1cS2G0A1S2S43A1S42S66VAInv;VCST;VXGL;S41S3aR8A1VrhoM;S39S4S3S0S0A2M1A1S4S3G1S0A2A1S6cVPA;R7R6R5R4R3R2R1A12S89R5A1F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;Ffds;").
Proof.
  intros fds nd Ai kc rho tp tr md (Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK0 & HP0 & _).
  destruct HP0 as [[[HZ [HP HPZ]] HZR] _]. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAP.STKP_kept segs CST XGL rhoM rho [] [] (eq_sym (proj1 Hav 30%positive eq_refl)) HK0 HPZ) as HPZn. destruct HK0 as [K1 _].
  assert (KEPT : forall lo len z, In (lo, len) CST_drv -> Sh lo <= z < Sh (lo + len) -> lo mod 8 = 0 -> 0 <= lo -> lo + len <= 0x643000 -> (lo + len <= 0x6211d0 \/ 0x6211d8 <= lo) -> rm rhoM (Z_to_bv 64 z) <> None ->
            rm rho (Z_to_bv 64 z) = rm rhoM (Z_to_bv 64 z)).
  { intros lo len z Hin Hz Hm Hlo Hhi Hne Hdef. unfold Sh, SHADOW_OFF in Hz. apply (K1 z ltac:(lia)).
    right. split; [|exact Hdef]. exists (8 * (z - SHADOW_OFF)). split; [unfold SHADOW_OFF; lia|]. split.
    - left. right. left. split; [apply HCSTdrv; exists lo, len; split; [exact Hin | unfold SHADOW_OFF; lia] | unfold errno_addrA, ERRNO_A, SHADOW_OFF; lia].
    - unfold Sh, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
  split; [split; [|split; [|exact HPZn]]|].
  - intros a Ha. rewrite (KEPT 0x641968 0x450 a); [exact (HZ a Ha) | cbn; tauto | unfold Sh, SHADOW_OFF; lia | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HZ a Ha) as HcE; congruence].
  - intros a Ha. destruct Ha as [Ha|Ha].
    + rewrite (KEPT 0x22b80 0xf40 a); [exact (HP a (or_introl Ha)) | cbn; tauto | unfold Sh, SHADOW_OFF; lia | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HP a (or_introl Ha)) as HcE; congruence].
    + rewrite (KEPT 0xe91c0 0x1840 a); [exact (HP a (or_intror Ha)) | cbn; tauto | unfold Sh, SHADOW_OFF; lia | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HP a (or_intror Ha)) as HcE; congruence].
  - intros z Hz. destruct Hz as [Hz|[Hz|Hz]].
    + rewrite (KEPT 0x21440 0x80 z); [exact (HZR z (or_introl Hz)) | cbn; tauto | exact Hz | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HZR z (or_introl Hz)) as HcE; congruence].
    +
      assert (KEPT2 : forall lo len z', In (lo, len) CST_drv2 -> Sh lo <= z' < Sh (lo + len) -> lo mod 8 = 0 -> 0 <= lo -> lo + len <= 0x643000 -> (lo + len <= 0x6211d0 \/ 0x6211d8 <= lo) -> rm rhoM (Z_to_bv 64 z') <> None ->
                rm rho (Z_to_bv 64 z') = rm rhoM (Z_to_bv 64 z')).
      { intros lo len z' Hin Hz' Hm Hlo Hhi Hne Hdef. unfold Sh, SHADOW_OFF in Hz'. apply (K1 z' ltac:(lia)).
        right. split; [|exact Hdef]. exists (8 * (z' - SHADOW_OFF)). split; [unfold SHADOW_OFF; lia|]. split.
        - left. right. left. split; [apply HCSTdrv2; exists lo, len; split; [exact Hin | unfold SHADOW_OFF; lia] | unfold errno_addrA, ERRNO_A, SHADOW_OFF; lia].
        - unfold Sh, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
      destruct (Z_lt_le_dec z (Sh 0x160c0)) as [Zlo|Zhi].
      * rewrite (KEPT2 0x16080 0x40 z); [exact (HZR z (or_intror (or_introl Hz))) | cbn; tauto | unfold Sh, SHADOW_OFF in *; lia | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HZR z (or_intror (or_introl Hz))) as HcE; congruence].
      * rewrite (KEPT 0x160c0 0x40 z); [exact (HZR z (or_intror (or_introl Hz))) | cbn; tauto | unfold Sh, SHADOW_OFF in *; lia | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HZR z (or_intror (or_introl Hz))) as HcE; congruence].
    + rewrite (KEPT 0x1a780 0x80 z); [exact (HZR z (or_intror (or_intror Hz))) | cbn; tauto | exact Hz | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HZR z (or_intror (or_intror Hz))) as HcE; congruence].
Qed.

Lemma ZX_now : ltac2:(tb__ "0|2|
S2S3S19Q40A1M0S44A2A1S61S8fS0S1cS2G0A1S2S43A1S42S66VAInv;VCST;VXGL;S41S3aR8A1VrhoM;S39S4S3S0S0A2M1A1S4S3G1S0A2A1S6cVPA;R7R6R5R4R3R2R1A12S12S8bR5A1S8aR5A1A2F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;Ffds;").
Proof.
  intros fds nd Ai kc rho tp tr md (Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK0 & HP0 & _).
  destruct HP0 as (_ & _ & _ & ((Z1 & Z2 & HZA) & HS2) & _). destruct HK0 as [K1 _].
  unfold ZARG, SHR2, Uv in *.
  rewrite <- (proj1 Hav 1%positive ltac:(unfold NF; lia)), <- (proj1 Hav 11%positive ltac:(unfold NF; lia)).
  split.
  - split; [exact Z1|]. split; [exact Z2|]. intros z Hz. rewrite <- (HZA z Hz). apply (K1 z).
    + destruct (ZARG_pcl2 _ _ z Z1 Z2 Hz) as (x & Hx0 & Hx & ->). unfold Sh, SHADOW_OFF in *. lia.
    + right. split; [|intro HcN; pose proof (HZA z Hz) as HcE; congruence]. destruct (ZARG_pcl2 _ _ z Z1 Z2 Hz) as (x & Hx0 & Hx & Ez). exists x. split; [exact Hx0|]. split; [left; left | exact Ez].
      unfold TobjJV.T0. cbn [Contract.V_TOP Malloc.Contract.V_TOP] in *. change (rw rhoM _) with (rw rhoM 30%positive) at 1. lia.
  - assert (KEPT : forall lo len z, In (lo, len) CST_drv2 -> Sh lo <= z < Sh (lo + len) -> lo mod 8 = 0 -> 0 <= lo -> lo + len <= 0x643000 -> (lo + len <= 0x6211d0 \/ 0x6211d8 <= lo) -> rm rhoM (Z_to_bv 64 z) <> None ->
              rm rho (Z_to_bv 64 z) = rm rhoM (Z_to_bv 64 z)).
    { intros lo len z Hin Hz Hm Hlo Hhi Hne Hdef. unfold Sh, SHADOW_OFF in Hz. apply (K1 z ltac:(lia)).
      right. split; [|exact Hdef]. exists (8 * (z - SHADOW_OFF)). split; [unfold SHADOW_OFF; lia|]. split.
      - left. right. left. split; [apply HCSTdrv2; exists lo, len; split; [exact Hin | unfold SHADOW_OFF; lia] | unfold errno_addrA, ERRNO_A, SHADOW_OFF; lia].
      - unfold Sh, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
    intros z Hz. destruct Hz as [Hz|Hz].
    + rewrite (KEPT 0x16080 0x40 z); [exact (HS2 z (or_introl Hz)) | cbn; tauto | exact Hz | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HS2 z (or_introl Hz)) as HcE; congruence].
    + rewrite (KEPT 0x1ee40 0x80 z); [exact (HS2 z (or_intror Hz)) | cbn; tauto | exact Hz | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HS2 z (or_intror Hz)) as HcE; congruence].
Qed.

Section Arg1.
Variables (rho : valuation) (tp : list word) (tr : list event) (ms : machine_state) (md : Model).
Hypothesis Hsp : ltac2:(tb__ "0|0|
Sc7S10Vrho;Vtp;S75SdS2S43A1SadVtr;SaeVms;Vmd;A2A4A5").
Hypothesis Hrl : ltac2:(tb__ "0|2|
S11S2S19Q8M0A1M1A1Sa9G1Sa5S8G1Vargv1;A2U1A2S28Vrho;P3A2A3S9G1Vargv1;ScG1S1aG0Z0A2S4G1A1A3A3A3").
Hypothesis HL1 : ltac2:(tb__ "0|0|
S11S0S1bQ40S1dVrho;P9A2A2S55S8S19Q8A1Vargv1;A2A1A3").
Let A1 : Z := bv_unsigned (rw rho 8%positive).
Let L1 : Z := bv_unsigned (rw rho 9%positive).
Let L3 : Z := bv_unsigned (rw rho 10%positive).

Lemma U_add_small : ltac2:(tb__ "0|1|
S1cS23S23S52S53S1bQ40M0S1fR3R2A2A2S1bG0S1fR3R1A2A2A2S54Z2Z40A2A2S11S0S1bG0S1fR4S2bSd1R3R2A3A2A2S53S1bG0S1fR4R3A2A2S1bG0S1fR4R2A2A2A2A3F_;Fb;Fa;Fr;").
Proof.
  intros r a b H. rewrite CursorGlue.U_add, <- M64v_eq. pose proof (urange (eval r a)). pose proof (urange (eval r b)). apply Z.mod_small. lia.
Qed.

Lemma arg1_nums : ltac2:(tb__ "0|1|
S12S51VL1;Z1ffffA2S12S51S53VA1;VL3;A2S54Z2M0Z2fA2A2S12S51Z0VA1;A2S12S51S53VL1;Z8A2VL3;A2S51VL3;S54G0Z16A2A2A2A2A2A2").
Proof.
  pose proof (smatch_pendingA_facts segs _ _ _ _ Hsp) as HF.
  destruct M_open as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F1 & F3 & F4 & F5 & F6).
  pose proof (holds_mem _ _ _ HF F1) as X1. pose proof (holds_mem _ _ _ HF F3) as X3.
  pose proof (holds_mem _ _ _ HF F4) as X4. pose proof (holds_mem _ _ _ HF F5) as X5. pose proof (holds_mem _ _ _ HF F6) as X6.
  cbn [holds] in X1, X3, X4, X5, X6. unfold vL1, vA1, vL3, add in *. rewrite !U_lit64 in X1, X3, X4, X6 by lia. cbn [eval] in X1, X4, X6.
  pose proof (urange (rw rho 8%positive)) as R8. pose proof (urange (rw rho 9%positive)) as R9. pose proof (urange (rw rho 10%positive)) as R10.
  assert (E2 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 8) (SVar 10))) = A1 + L3).
  { rewrite U_add_small; cbn [eval]; subst A1 L3; lia. }
  assert (E5 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 9) (SLit 8))) = L1 + 8).
  { rewrite U_add_small; rewrite U_lit64 by lia; cbn [eval]; subst L1; lia. }
  rewrite E2 in X3. rewrite E5 in X5. cbn [eval] in X5. subst A1 L1 L3. lia.
Qed.

Lemma arg1_obj : ltac2:(tb__ "0|0|
S2dS10Vrho;Sc8Vmd;Vtp;Vms;A3Sd2A4").
Proof.
  destruct M_open as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _).
  pose proof (objsA_hold segs rho tp E_op tr ms md 4 Hsp ltac:(apply (proj1 (nth_error_Some _ _)); rewrite Hn; discriminate)) as H.
  unfold obA in H. rewrite (nth_error_nth _ _ _ Hn) in H. exact H.
Qed.

Lemma arg1_len : Z.of_nat (length argv1) = L1.
Proof. subst L1. symmetry. exact HL1. Qed.

Lemma arg1_bytes : ltac2:(tb__ "0|3|
SaSa6R1S8S19Q8M0A1M1Vargv1;A2A2S11S7G1A1SacVms;S1aQ40S53VA1;S55R2A1A2A2A2SbG1SaaG1R2S9G1Vargv1;ScG1S1aG0Z0A2M2S4G1A1A3A3G2A4A2A3F_;Fj;").
Proof.
  intros j Hj. destruct arg1_nums as (N1 & N2 & N3 & N4 & N5). pose proof arg1_len as HL.
  destruct arg1_obj as (HB & Hw & Hc & Hd & Hdl).
  assert (Hlo : obj_lo_of rho O_arg1 = 0) by (unfold obj_lo_of; cbn [ob_lo O_arg1]; apply soff_lit_small; lia).
  assert (Hhi : obj_hi_of rho O_arg1 = L3).
  { unfold obj_hi_of. cbn [ob_hi O_arg1]. unfold vL3. rewrite (soff_snorm rho), snorm_small; unfold SymSoundV.U; cbn [eval]; subst L3; lia. }
  specialize (Hd (Z.of_nat j)). rewrite Hlo, Hhi in Hd. cbn [ob_cells ob_dflt ob_base O_arg1 dflt_holds] in Hd.
  apply (vms_read_byte_someA segs rho tp E_op tr ms md _ _ Hsp).
  subst A1. unfold vA1, rd in Hd. cbn [eval] in Hd. rewrite (Hd ltac:(lia) ltac:(intros HX; inversion HX)).
  rewrite <- Hrl. rewrite nth_firstn. replace (Z.to_nat (Z.of_nat j - 0)) with j by lia.
  destruct (Nat.ltb_spec j (length argv1 + 1)); [reflexivity | lia].
Qed.

Definition cstr1 : cstr_result := ltac2:(tb__ "0|0|
S5S46L_;SceS8S19Q8A1Vargv1;A2U1000A2S48Vargv1;A1S49X5x2").
Lemma arg1_cstr : ltac2:(tb__ "0|0|
S11S46S50SacVms;A1S1dVrho;P8A2A2Sd4A3").
Proof.
  destruct arg1_nums as (N1 & N2 & N3 & N4 & N5). pose proof arg1_len as HL.
  rewrite <- (Z_to_bv_bv_unsigned 64 (rw rho 8%positive)) at 1. fold A1. unfold read_cstr, cstr1.
  rewrite (read_cstr_aux_string (ms_read_byte ms) argv1 path_max A1); [| lia | lia | exact arg1_bytes | exact Hnonul].
  change path_max with 4096%nat. reflexivity.
Qed.

Lemma arg1_avoid : ltac2:(tb__ "0|0|
SdbSc9Vmd;Vtp;A2Sd5SafS10Vms;S1aQ40Z38A2A3A1A2").
Proof.
  destruct arg1_nums as (N1 & N2 & N3 & N4 & N5). pose proof arg1_len as HL.
  destruct M_open as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H11 & Hn & _).
  unfold openat_reads. rewrite sys_input_arg1, sys_input_mem.
  pose proof (smatch_pendingA_gpr segs rho tp E_op tr ms md 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1. rewrite H11 in G1.
  unfold vA1 in G1. cbn [eval] in G1. rewrite G1.
  apply ranges_avoid_cons; [| intros a n []].
  pose proof (cstr_access_len_le (ms_read_byte ms) argv1 path_max A1 ltac:(lia) ltac:(lia) arg1_bytes Hnonul) as LE.
  rewrite <- (Z_to_bv_bv_unsigned 64 (rw rho 8%positive)). fold A1.
  eapply (range_in_obj_avoidsA segs rho tp E_op tr ms md O_arg1); [exact Hsp | eapply nth_error_In; exact Hn | reflexivity | |];
    unfold obj_range, obj_lo_of, obj_hi_of; cbn [fst snd ob_base ob_lo ob_hi O_arg1]; unfold vA1; cbn [eval]; fold A1.
  - rewrite soff_lit_small by lia. rewrite Z_to_bv_small; [lia | rewrite InitState.mod64; lia].
  - unfold vL3. rewrite (soff_snorm rho), snorm_small by (unfold SymSoundV.U; cbn [eval]; lia). unfold SymSoundV.U. cbn [eval]. fold L3.
    rewrite Z_to_bv_small; [lia | rewrite InitState.mod64; lia].
Qed.
End Arg1.

Lemma openat_errnos_small : ltac2:(tb__ "0|0|
S0Sa3S0R1Sd0A3S12S52Z0R2A2S52R2Z1000A2A2F_;Fe;").
Proof. intros e H. unfold openat_errnos in H. cbn in H. unfold ENOMEM, EACCES, EMFILE, ENFILE in H. lia. Qed.

Lemma open_outcome : ltac2:(tb__ "0|2|
S42S19Q40M0A1M1S42S11S2S3G1S44A2A1S4cR3A1S85A3S11Sb7S4dR4A1VFS0;A3SdcR5S5S46L_;SceS8S19Q8A1Vargv1;A2U1000A2S48Vargv1;A1S49X5x2R4R3A4S15S13S0S0S12S12S52Z0R1A2S52R1Z1000A2A2S12S11G1R6S45R1A1A3S11S42R5R7A3A2A2Le;A2S12S94Vargv1;VFS0;A2S12S11G1R5S1aG0Z3A2A3S11S42R4S47S83Vargv1;A1R6A2A3A2A2A2F_;F_;F_;Fmd';Fr;Fmd;").
Proof.
  intros md r md' Hfds Hfs H. unfold open_may_succeed. rewrite PATH_MAX_eq.
  destruct (Nat.ltb_spec (length argv1) 4096) as [Hlen|Hlen].
  2:{ cbn [openat_post] in H. destruct H as [-> ->]. left. exists ENAMETOOLONG. unfold ENAMETOOLONG. repeat split; lia. }
  unfold openat_post in H.
  destruct argv1 as [|b q] eqn:Ea.
  { destruct H as [-> ->]. left. exists ENOENT. unfold ENOENT. repeat split; lia. }
  rewrite Hfds, alloc_fd_std, lookup3_std, (path_is_dirref_not_dotdot _ Hndd) in H. unfold FD3, open_entry.
  destruct (path_eqb (b :: q) dot_path) eqn:Hd.
  - destruct H as [(e & Hin & -> & ->)|(_ & -> & ->)].
    + left. exists e. pose proof (openat_errnos_small e Hin). auto.
    + right. split; [|split; [reflexivity|]].
      * apply path_eqb_eq in Hd. split; [lia|]. split; [discriminate|]. left. exact Hd.
      * unfold openat_dir_model. rewrite Hfds, alloc_fd_std. reflexivity.
  - rewrite Hfs in H. destruct (fs_lookup FS0 (b :: q)) as [F|] eqn:HF.
    + destruct H as [(e & Hin & -> & ->)|(_ & -> & ->)].
      * left. exists e. pose proof (openat_errnos_small e Hin). auto.
      * right. split; [|split; [reflexivity|]].
        -- split; [lia|]. split; [discriminate|]. right. rewrite ?HF. discriminate.
        -- unfold openat_file_model. rewrite Hfds, alloc_fd_std. reflexivity.
    + left. exists ENOENT. unfold ENOENT in *. destruct H as [-> ->]. repeat split; lia.
Qed.

Definition Jop (r : valuation) (t : list word) (tr : list event) (md : Model) : Prop := ltac2:(tb__ "0|3|
S15S13S0S0S12S12S52Z0R1A2S52R1Z1000A2A2S12S11S19Q40M0A1M1S1dVr;S74A2M2S45R1A1A3S38S85S73Vr;Vt;Vtr;Vmd;A6A2A2Le;A2S12S94Vargv1;VFS0;A2S12S11G1G2S1aG0Z3A2A3S38S83Vargv1;A1S73Vr;Vt;Vtr;Vmd;A6A2A2A2").

Lemma Jop_stable : ltac2:(tb__ "0|0|
S37S10Sb6S74A1S3eA3").
Proof.
  destruct M_open as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnf & Hb1 & Hb2 & _).
  apply Pos.leb_le in Hnf.
  intros r r' t tr md md' Hag Hme [(e & He & Hr & HJ)|(Ho & Hr & HJ)].
  - left. exists e. split; [exact He|]. split; [rewrite <- (proj1 Hag vFD ltac:(lia)); exact Hr|].
    eapply (JM_stable std_fds nd_M (Pos.succ vFD) ltac:(lia) Hb2); [exact Hag | exact Hme | exact HJ].
  - right. split; [exact Ho|]. split; [rewrite <- (proj1 Hag vFD ltac:(lia)); exact Hr|].
    eapply (JM_stable (FD3 argv1) nd_M (Pos.succ vFD) ltac:(lia) Hb2); [exact Hag | exact Hme | exact HJ].
Qed.

Lemma open_step : ltac2:(tb__ "0|6|
S1cS2S19Q40M0A1M1A1S0S1cS12S52Z0R2A2S52R2Z1000A2A2S22S74R5R2A3M2S11G1S1dR3S74A2M3S45R4A1A3S7fS10Vok;S34S10S38S85S73A2M4S76R4R6A5S80S14L_;M5A4F_;F_;F_;Frho';Fe;S1cS94Vargv1;VFS0;A2G2S11G1G3S1aG0Z3A2A3S7fS10Vok;S34S10S38S83Vargv1;A1S73A2S76R4R6A5G5A4F_;F_;F_;Frho';S7fS10Vok;S34S10G4S75R4R3A5G5A4F_;F_;Ftp;Frho;").
Proof.
  intros rho tp HE HO.
  destruct M_open as (Eaf & _ & _ & EvFD & _ & Hi & H17 & H10 & H12 & H11 & Hn & Hnf & Hb1 & Hb2 & _).
  pose proof Hnf as Hnf'. apply Pos.leb_le in Hnf.
  eapply triple_seq.
  { apply triple1_triple.
    apply (triple1_openatA segs ok (JM std_fds nd_M) Jop E_op rho tp (JM_okframe _ _) (JM_okpframe _ _));
      [rewrite <- EvFD; apply JM_stable; [exact Hnf | exact Hb1] | rewrite <- EvFD; apply Jop_stable | exact Hi | exact H17 | exact H10 | exact H12 | | |].
    -
      intros tr ms md Hsp HJ. destruct (JM_P0 _ _ _ _ _ _ HJ) as [[_ [Hrl0 [HL0 _]]] [Hw Hl]].
      apply (arg1_avoid rho tp tr ms md Hsp); [rewrite <- (Hl 3%positive); exact Hrl0 | rewrite <- (Hw 9%positive ltac:(unfold NF; lia)); exact HL0].
    -
      intros tr ms md Hsp HJ. destruct (JM_P0 _ _ _ _ _ _ HJ) as [[_ [Hrl0 [HL0 _]]] [Hw Hl]].
      rewrite H11. unfold vA1. cbn [eval].
      rewrite (arg1_cstr rho tp tr ms md Hsp ltac:(rewrite <- (Hl 3%positive); exact Hrl0) ltac:(rewrite <- (Hw 9%positive ltac:(unfold NF; lia)); exact HL0)).
      unfold cstr1. destruct (length argv1 <? 4096)%nat; [exact Hnsl | exact I].
    -
      intros tr ms md r md' Hsp HJ Hpost. destruct (JM_P0 _ _ _ _ _ _ HJ) as [[_ [Hrl0 [HL0 _]]] [Hw Hl]].
      assert (Hrl : firstn (length argv1 + 1) (rl rho 3%positive) = argv1 ++ [Z_to_bv 8 0]) by (rewrite <- (Hl 3%positive); exact Hrl0).
      assert (HL1 : bv_unsigned (rw rho 9%positive) = Z.of_nat (length argv1)) by (rewrite <- (Hw 9%positive ltac:(unfold NF; lia)); exact HL0).
      rewrite H11 in Hpost. unfold vA1 in Hpost. cbn [eval] in Hpost. rewrite (arg1_cstr rho tp tr ms md Hsp Hrl HL1) in Hpost. unfold cstr1 in Hpost.
      destruct (JM_Kc _ _ _ _ _ _ HJ) as (_ & Hfds & Hmdx).
      destruct (open_outcome md r md' Hfds (HMDXfs md Hmdx) Hpost)
        as [(e & He & -> & ->)|(Ho & -> & ->)].
      + left. exists e. split; [exact He|]. rewrite <- EvFD. split; [apply rho_set_rw_at|].
        apply JM_set_rw; [exact Hnf | exact Hb1 | exact HJ].
      + right. split; [exact Ho|]. rewrite <- EvFD. split; [apply rho_set_rw_at|].
        apply JM_set_rw; [exact Hnf | exact Hb1 |]. apply (JM_with_fds std_fds). exact HJ. }
  apply triple_ex. intros rho'. apply triple_pure. intros Hag. rewrite Eaf. rewrite <- EvFD in Hag.
  eapply (triple_conseq (P := fun w => (exists e, 0 < e < 4096 /\ rw rho' vFD = errno_ret e /\ SPA segs (JM std_fds nd_M) T_op rho' tp w)
                                    \/ (open_may_succeed argv1 FS0 /\ rw rho' vFD = Z_to_bv 64 3 /\ SPA segs (JM (FD3 argv1) nd_M) T_op rho' tp w)));
    [intros w [Hsm HJ] | intros w' Hw'; exact Hw' |].
  { destruct w as [tr [ms md]]. destruct HJ as [(e & He & Hr & HJ)|(Ho & Hr & HJ)].
    - left. exists e. split; [exact He|]. split; [exact Hr|]. split; [exact Hsm | exact HJ].
    - right. split; [exact Ho|]. split; [exact Hr|]. split; [exact Hsm | exact HJ]. }
  apply triple_disj.
  - apply triple_ex. intros e. apply triple_pure. intros He. apply triple_pure. intros Hr. exact (HE e rho' He Hag Hr).
  - apply triple_pure. intros Ho. apply triple_pure. intros Hr. exact (HO rho' Ho Hag Hr).
Qed.

Lemma r0_reshape : ltac2:(tb__ "0|3|
S1cS2S19Q40M0A1A1S80S94Vargv1;VFS0;A2Sa7S26S25R4A1S1eS59S78A1A1A3S12S51Z7fff80000000S1bG0S1fR5Sd3A2A2M1A2S51G1S56S54Z2Z2fA2Z10A2A2A2S34S10S38S83Vargv1;A1S7aA2M2S78R6R5R4A6S34S10G2S79R7R6R5A6F_;F_;F_;F_;Fw;Ftp4;Frho5;").
Proof.
  intros rho5 tp4 w Hmay HF5 Hsp5 HS.
  destruct M_r0 as (Q1n & Q1e & Q1s & Q1f & Q2e & Q2s & Q3e & Q3b & Q2nx & Q2fx & QvB & QTP & _ & Hent & Hs24 & Hs9 & Hs1 & Hs11 & _ & _ & Qnx & Qnb & Qtv & Qfr & Qbd & Qam).

  assert (HS1 : SPA segs (JM (FD3 argv1) nd_R1) (mkAX R1 (ax_X L_R0) (ax_base L_R0)) rho5 tp4 w).
  { rewrite <- Q1e. change (mkAX (set_obj_at (ax_S L_R0) 0 O_deep) (ax_X L_R0) (ax_base L_R0)) with (ax_setS L_R0 (set_obj_at (ax_S L_R0) 0 O_deep)).
    apply (SPA_reslice segs (JM (FD3 argv1) nd_R1) rho5 L_R0 0 O_winR O_deep tp4 w Q1n); [reflexivity | reflexivity | reflexivity | reflexivity | | | | | exact HS].
    - rewrite Q1e. exact Q1s.
    - unfold O_winR, O_deep. rewrite !obj_range_lits by (unfold DEEP; lia). rewrite U_add_lit by lia. f_equal; unfold DEEP; lia.
    - unfold O_deep, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP; lia). unfold DEEP; lia.
    - unfold O_deep, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP; lia). unfold DEEP; lia. }

  pose proof (AxXform.SPA_select segs (JM (FD3 argv1) nd_R1) rho5 (mkAX R1 (ax_X L_R0) (ax_base L_R0)) _ tp4 _ Q2e HS1) as HS2.
  cbn [ax_S ax_X ax_base] in HS2. rewrite Q2s in HS2.

  unfold L_R0h. rewrite <- Q3e.
  change (mkAX (add_facts r0_hints R2) (ax_X L_R0) (ax_base L_R0)) with (ax_with_facts (mkAX R2 (ax_X L_R0) (ax_base L_R0)) (r0_hints ++ ss_facts R2)).
  apply (SPA_refacts_JA segs); [exact HS2 | cbn [ax_S]; exact Q3b | ].
  intros tr md HJ HFc. apply Forall_app. split; [|exact HFc]. cbn [ax_S] in HFc. rewrite Q2fx in HFc.
  assert (Hnz : tnz rho5 (SVar vBn, SLit 65536)).
  { unfold tnz. cbn [fst]. pose proof (holds_mem _ _ _ HFc QvB) as X. cbn [holds] in X. rewrite U_lit64 in X by lia. cbn [eval] in X |- *. lia. }
  pose proof (JA_tv_facts segs AInv CST XGL NF (KcM (FD3 argv1)) rhoM P0M [] [] BX0 PA ALA nd_R1 rho5 tp4 tr md (SVar vBn, SLit 65536) eq_refl HJ ltac:(left; reflexivity) Hnz) as TF.
  unfold tv_factsA in TF. cbn [fst snd] in TF.
  inversion TF as [| ? ? T1 TF2]; subst. inversion TF2 as [| ? ? _ TF3]; subst. inversion TF3 as [| ? ? T3 TF4]; subst.
  inversion TF4 as [| ? ? T4 TF5]; subst. inversion TF5 as [| ? ? _ TF6]; subst. inversion TF6 as [| ? ? T6 TF7]; subst.
  inversion TF7 as [| ? ? T7 TF8]; subst. inversion TF8 as [| ? ? T8 _]; subst.

  unfold r0_hints. constructor; [exact T1|]. constructor; [exact T3|]. constructor; [exact T4|]. constructor; [exact T6|].
  constructor; [exact T8|]. constructor; [exact T7|].

  destruct (JM_P0 _ _ _ _ _ _ HJ) as [(_ & _ & HL9 & _) [Hw _]]. unfold Uv in HL9. rewrite (Hw 9%positive ltac:(unfold NF; lia)) in HL9.
  destruct Hmay as (Hlen & Hne & _). rewrite PATH_MAX_eq in Hlen.
  assert (H1 : 1 <= Z.of_nat (length argv1)) by (destruct argv1; [exfalso; exact (Hne eq_refl) | cbn; lia]).
  constructor; [cbn [holds]; unfold vL1; rewrite U_lit64 by lia; cbn [eval]; rewrite HL9; lia|].
  constructor; [cbn [holds]; unfold vL1; rewrite U_lit64 by lia; cbn [eval]; rewrite HL9; lia| constructor].
Qed.

Lemma r0_reorigin : ltac2:(tb__ "0|3|
S1cS2S19Q40A1A1S80S34S10S38S83Vargv1;A1M0S7aA2S79R3R2R1A6S34S10S63VAInv;VCST;VXGL;S41S84VT0;VMDX;G0S4S43A1A4Sd8R4S7dA2M1S86Vargv1;A1S4S3S0S0A2M2A1S4S3G2S0A2A1S6cVPA;S88AcS87G1R3R2A6F_;Fw;Ftp4;Frho5;").
Proof.
  intros rho5 tp4 w HS.
  destruct M_r0 as (Q1n & Q1e & Q1s & Q1f & Q2e & Q2s & Q3e & Q3b & Q2nx & Q2fx & QvB & QTP & Q1f' & Hent & Hs24 & Hs9 & Hs1 & Hs11 & Hs30 & Hs10 & Qnx & Qnb & Qtv & Qfr & Qbd & Qam).
  apply (SPA_reorigin_JA AInv CST XGL ALA NF (KcM (FD3 argv1)) [] [] BX0 PA ltac:(unfold NF; lia) ltac:(unfold NF; cbv; reflexivity) rhoM P0M (P0Z argv1) L_R0h S_R0 s_R0 nd_R1 nd_R0 rho5 tp4 w
           Hent Hs24 Hs30 Qnx Qnb Qtv Qfr Qbd Qam); [|exact HS].
  intros Ai kc HFh HP0 Hav HK Hk HJi. destruct HP0 as (_ & Hfirst & HL9 & _ & HSL). split; [|split; [|split; [|split; [|split; [|split]]]]].
  - unfold Uv. cbn [rho_sub rw]. rewrite Hs24. pose proof (holds_mem _ _ _ HFh QTP) as X. unfold vTP in X. cbn [holds eval] in X. cbn [eval].
    rewrite X. rewrite lit_unsigned. reflexivity.
  - pose proof (SHR_now _ _ _ _ _ _ _ _ HJi) as [SH1 SH2]. split; [exact SH1 | exact SH2].
  - cbn [rho_sub rl]. rewrite <- (proj2 Hav 3%positive). exact Hfirst.
  - unfold Uv. cbn [rho_sub rw]. rewrite Hs9. cbn [eval]. rewrite <- (proj1 Hav 9%positive ltac:(unfold NF; lia)). exact HL9.
  -
    pose proof (ZX_now _ _ _ _ _ _ _ _ HJi) as [Z1 Z2]. unfold ZARG, SHR2, Uv in *. cbn [rho_sub rw rm]. rewrite Hs1, Hs11. cbn [eval].
    split; [exact Z1 | exact Z2].
  -
    unfold TOPV, Uv. cbn [rho_sub rw]. unfold Iface.V_TOP in Hs30. rewrite Hs1, Hs30. cbn [eval].
    pose proof (proj2 (sp0_facts_sound rho5 _ HFh Q1f')) as X30. lia.
  -
    unfold SLK1, Uv in HSL |- *. cbn [rho_sub rw]. rewrite Hs9, Hs10. cbn [eval].
    rewrite <- (proj1 Hav 9%positive ltac:(unfold NF; lia)), <- (proj1 Hav 10%positive ltac:(unfold NF; lia)). exact HSL.
Qed.

Lemma MSGB_oomM : MSGB 0x14d9d 19 = msg_oom. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition JMe (fds : list (word * FdEntry)) (evs : list event) (nd : ndesc) : jpredA := ltac2:(tb__ "0|1|
S63VAInv;VCST;VXGL;S41S84VT0;VMDX;Vfds;Vevs;A4VrhoM;S39S4S3S0S0A2M0A1S4S3G0S0A2A1S6cVPA;Vnd;Ac").
Lemma JMe_nil : ltac2:(tb__ "0|0|
S2S3S19Q40A1S44A2A1S61S11S35S3bR2S4S43A1R1A3S38R2R1A2A3Fnd;Ffds;"). Proof. reflexivity. Qed.
Lemma KcGM_ok : ltac2:(tb__ "0|0|
S2S3S19Q40A1S44A2A1S2S43A1S9fS84VT0;VMDX;R2R1A4A1Fevs;Ffds;").
Proof. intros fds evs. apply KcG_ok. exact HMDXvm. Qed.
Lemma Kw_JM : ltac2:(tb__ "0|3|
S2S3S19Q40A1M0S44A2A1S2S43A1M1S61S1cS0S0SaS1cS2G0A1M2G1S42SbcS1cG2G1S42S3bRfReRdRcR3R2R1A7Lmd;Ltr;Lt;L_;R7R6R5R4R3R2R1A8S3bRcS9S43RbSbbR8R7R6A3A3RaR9R4R3R2A7F_;Fmd';Ftr';Ft;FrhoL;Fn;Flen;Fmsg;Frho1;Fnd;Fevs;Ffds;").
Proof.
  intros fds evs nd rho1 msg len n rhoL t tr' md' (tr0 & HJ & ->).
  destruct HJ as (Ai & kc & Hav & (Htr & Hfd & HX) & REST). exists Ai, kc. split; [exact Hav|]. split; [|exact REST].
  split; [rewrite Htr, <- app_assoc; reflexivity|]. split; [exact Hfd | exact HX].
Qed.
Let carveM (fds : list (word * FdEntry)) (evs : list event) : ltac2:(tb__ "0|4|
S61S5bS1cS2S19Q40A1A1S80S2S96A1S1S34S10S97VAInv;VCST;VXGL;S41VrhoM;S39S4S3S0S0A2M0A1M1S4S3G0S0A2A1M2S6cVPA;S84VT0;VMDX;Vfds;Vevs;A4M3R7AcR6R5R4R3A6S59R7A1S2aS2cS30R1A1S31R1A1S2fR1A1S2eR1A1S32R1A1S9S20S24R1A1Sa8S96S20S98R4A4A3S1eR1A1R3S29R1A1A9S2aS11S5S33R1A1S6A3S11S5Sb4S21R3A1R5A2S6A3S11S23S5fRbA1S27Sb2A1A3S11S5S9bS1eR5A1S24R5A1S5cRcA1S6dS6fS62RdA1R8A7S6A3S34S10S97VAInv;VCST;VXGL;S41VrhoM;S39G1G2S6cVPA;G3ReAcS5dRdR5A2RcRbRaA6F_;F_;F_;F_;TS';TS;F_;Fnx;FN;Fw;Ftp;Frho;FA;Fnd;") := ltac2:(tb__ "0|2|
S99VAInv;VCST;VXGL;VALA;S41VrhoM;S39S4S3S0S0A2M0A1S4S3G0S0A2A1S6cVPA;S6dSbdVAInv;VCST;VXGL;VALA;VHCSTdrv;VHLPP;S3aVfds;A1M1VrhoM;S39S3cVPA;VPA;AcS6eS6fSbeVAInv;VCST;VXGL;VHCSTdrv;G1VrhoM;S39S3cVPA;VPA;AaS84VT0;VMDX;Vfds;Vevs;A4A11").
Let uncarveM (fds : list (word * FdEntry)) (evs : list event) : ltac2:(tb__ "0|6|
S61S5bS1cS2S19Q40A1A1S2S43A1M0SabS42S2S20A1M1S2S96A1S9fS84VT0;VMDX;Vfds;Vevs;A4M2A1S11G1S24S59R9A1A1S9S20R3Sa8S96S20S98R2A4A3A3S11S5S9cS6dR3A2S6A3S11S68S6bRcA1S65A3S11S5S64S21S59RcA1A1RdA2S6A3S34S10S97VAInv;VCST;VXGL;S41VrhoM;S39S4S3S0S0A2M3A1M4S4S3G3S0A2A1M5S6cVPA;G2ReAcRdRcRbSdG0SadRaSaeR9R8A2A4A6S34S10S97VAInv;VCST;VXGL;S41VrhoM;S39G4G5S6cVPA;G2RfAcS5dReSdaS59ReA1R8A2A2Sd7RdSa8S96S20S98R7A4Sc8R9RcRaA3A3RcSdG0SadRbSaeRaR9A2A4A6F_;F_;F_;F_;F_;F_;FN;Fobjs;Fmd;Fms;Ftr;Ftp;Frho;FA;Fnd;") := ltac2:(tb__ "0|1|
S9aVAInv;VCST;VXGL;VALA;VHLV;S41VrhoM;S39S4S3S0S0A2M0A1S4S3G0S0A2A1S6cVPA;S6dSbdVAInv;VCST;VXGL;VALA;VHCSTdrv;VHLPP;S3aVfds;A1VrhoM;S39S3cVPA;VPA;AcS6eS71VAInv;VCST;VHCSTok;VHLPP;A4S84VT0;VMDX;Vfds;Vevs;A4A11").

Lemma room_M : ltac2:(tb__ "0|0|
S8fS0S1cSdeS7cS6aSdfS6cA1S69S65R1A2R2A3S92R3A1S91R3A1S90R3A1R1A6Se1R4Z10000A2F_;Frho;Fkc;FA;").
Proof.
  intros A kc rho HB. apply BUD_room in HB as (B0 & B1 & BV & BK). pose proof (apot_range ANone rho) as AR.
  unfold bxa, BX0 in B0, B1, BV, BK. cbn [fst snd bx2] in B0, B1, BV, BK.
  assert (EV : bsumV bd_M0 rho = V_T + 2 ^ 27 - 65536) by (unfold bd_M0; cbn [bsumV]; unfold bival, BIc; cbn [lfval bi_f bi_c bi_v bi_k]; lia).
  assert (EK : bsumK bd_M0 rho = KU * (K_T + 21)) by (unfold bd_M0; cbn [bsumK]; unfold bival, BIc; cbn [lfval bi_f bi_c bi_v bi_k]; lia).
  rewrite EV in BV. rewrite EK in BK.
  unfold alloc_roomA. unfold V_T, K_T, VMAX, KMAX, V_DRV, K_DRV, NCALLS, CV, CV0, CK_DIV, CK0, MAX_INPUT, KU in BV, BK |- *. lia.
Qed.

Section Safe.

Hypothesis Hcopen : ltac2:(tb__ "0|0|
S1cS2S19Q40A1A1S7fS10Vok;S34S10S38S85S73A2S77R2R1A5S80S14L_;A4Ftp;Frho;").

Hypothesis HR : ltac2:(tb__ "0|1|
S94Vargv1;VFS0;A2S1cS2S19Q40A1A1S7fS10Vok;S34S10S63VAInv;VCST;VXGL;S41S84VT0;VMDX;S83Vargv1;A1S4S43A1A4R2S86Vargv1;A1S4S3S0S0A2M0A1S4S3G0S0A2A1S6cVPA;S88AcS87R2R1A5S80S14L_;A4Ftp;Frho;F_;").

Theorem m_safe : ltac2:(tb__ "0|0|
S1cS2S19Q40A1A1S7fS10Vok;S34S10S38S85S73A2S9dR2R1A5S80S14L_;A4Ftp;Frho;").
Proof.
  intros rho tp.
  destruct M_runs as (Ru0 & _ & Ru1 & _ & Ru1F & _ & Ru2 & _ & Ru2n & _).
  destruct M_wf as (W0 & W1 & W1F & W2 & W2n & _).
  apply runwf_sound in W0 as (W0a & W0b & W0c). apply runwf_sound in W1 as (W1a & W1b & W1c). apply runwf_sound in W1F as (W1Fa & W1Fb & W1Fc).
  apply runwf_sound in W2 as (W2a & W2b & W2c). apply runwf_sound in W2n as (W2na & W2nb & W2nc).
  destruct M_open as (Eaf & E3 & EF & EvFD & EnT & _ & _ & _ & _ & _ & _ & Hnf & Hb1 & Hb2 & Fb3 & FbF & _).

  eapply (JM_run std_fds); [exact Ru0 | exact W0b | exact W0a | exact W0c |].
  intros Lf rho1 [<-|[]] Hag1. cbn [la_state].

  apply open_step.
  -
    intros e rho2 He Hag2 Hr.
    eapply (triple_conseq (P := SPA segs (JM std_fds nd_M) T_opF rho2 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
    { rewrite <- EF. apply (SPA_addn segs); [exact HS | | rewrite EnT; exact FbF].
      assert (HU : bv_unsigned (rw rho2 vFD) = 2 ^ 64 - e).
      { rewrite Hr. unfold errno_ret. rewrite lit_unsigned, <- (Z.mod_add (- e) 1 (2 ^ 64)), Z.mod_small by lia. lia. }
      unfold err_facts. repeat constructor; cbn [holds eval]; rewrite HU, lit_unsigned, Z.mod_small by lia; lia. }
    eapply (JM_run std_fds); [exact Ru1F | exact W1Fb | exact W1Fa | exact W1Fc |].
    intros Lf rho3 [<-|[]] Hag3. cbn [la_state]. apply Hcopen.
  -
    intros rho2 Ho Hag2 Hr.
    eapply (triple_conseq (P := SPA segs (JM (FD3 argv1) nd_M) T_op3 rho2 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
    { rewrite <- E3. apply (SPA_addn segs); [exact HS | | rewrite EnT; exact Fb3].
      unfold fd3_facts. repeat constructor. cbn [holds eval]. rewrite Hr. reflexivity. }

    eapply (JM_run (FD3 argv1)); [exact Ru1 | exact W1b | exact W1a | exact W1c |].
    intros Lf rho3o [<-|[]] Hag3. cbn [la_state].

    apply (errR_Ts ok _ E_m65 _ rho3o tp (proj1 M_errR) (JA_errno_blind segs AInv CST XGL ALA HCST (fun a Ha => HCSTdrv a (errno_in_CST_drv a Ha)) NF (KcM (FD3 argv1)) rhoM P0M [] [] BX0 PA _ nd_M W1c)). intros rho3 _ _ _. rewrite (proj2 M_errR).
    destruct M_malloc as (M1 & Mfr & Mcc & McN & McO & McT & Mnx & Mnb & Mbb & Ms12 & Mres & MvB & Mpay & Mspf & Mro & Mxr & MTn & MTk).
    eapply (triple_conseq (P := SPA segs (JM (FD3 argv1) nd_M) C_m65 rho3 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
    { unfold C_m65. exact (SPA_split segs (JM (FD3 argv1) nd_M) rho3 E_m65r 0 (SLit (-128)) C_m65S tp w M1 HS). }

    apply (malloc_callA_S segs AE_A AInv CST XGL ALA HCST HXGL NF (KcM (FD3 argv1)) rhoM P0M [] [] BX0 PA (KcM_ok _) PA ok [] UStopLe C_m65 s_m65 R_m65 rho3 tp
             nd_M bd_R0 (fun _ => False) malloc_shape_nil
             (okKK ok Spec HOKJ HOKP (KcM (FD3 argv1)) (KcM_tc _)) MS Mfr McO McT Mnx Mnb Mbb).
    + rewrite Ms12. reflexivity.
    + exact Mres.
    + rewrite Ms12. apply payA_of_bud_pay. exact Mpay.
    + intros A A' HPA Hk. eapply HPAm; [| exact HPA | exact Hk]. rewrite Ms12. unfold uval. rewrite U_lit64 by lia. lia.
    + intros A kc _ _ HB. rewrite Ms12. unfold nd_M in HB. cbn [nd_bd nd_am] in HB. unfold uval. rewrite U_lit64 by lia. exact (room_M A kc rho3 HB).
    + reflexivity.
    + vm_compute; discriminate.
    + vm_compute; discriminate.
    + apply (site_ok_drvM nd_M C_m65 s_m65 R_m65 rho3 None None); try assumption.
      * intros Ai HF' HN HZ. exact I.
      * intros Ai ms HF' HP0 Hav HN HD HZ HM. rewrite Ms12. split; [unfold uval; rewrite U_lit64 by lia; lia | exact I].
    +
      intros rho4 tp4. unfold PreM in MTk. rewrite MTk, MvB, Ms12. unfold nd_M. cbn [nd_tv nd_fr nd_am]. fold tv_R1. fold nd_R1.
      eapply (JM_run (FD3 argv1)); [exact Ru2 | exact W2b | exact W2a | exact W2c |].
      intros Lf rho5 [<-|[]] Hag5. cbn [la_state].
      destruct M_r0 as (Q1n & Q1e & Q1s & Q1f & _).
      apply triple_factsA. intros HF5.
      assert (Hsp5 : 0x7fff80000000 <= bv_unsigned (eval rho5 sp0) <= 2 ^ 47 - 16).
      { unfold sp0. cbn [eval]. pose proof (proj1 (sp0_facts_sound rho5 _ HF5 Q1f)). lia. }
      eapply (triple_conseq (P := SPA segs (JM (FD3 argv1) nd_R1) L_R0h rho5 tp4)); [intros w HS | intros w' Hw'; exact Hw' |].
      { exact (r0_reshape rho5 tp4 w Ho HF5 Hsp5 HS). }

      eapply (triple_conseq (P := SPA segs (JA AInv CST XGL NF (KcG T0 MDX (FD3 argv1) []) (rho_sub rho5 s_R0) (P0Z argv1) [] [] BX0 PA nd_R0) S_R0 (rho_sub rho5 s_R0) tp4));
        [intros w HS | intros w' Hw'; exact Hw' | apply (HR Ho)].
      exact (r0_reorigin rho5 tp4 w HS).
Qed.
End Safe.

Section Ex.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sa1S10S9eVAInv;VCST;VXGL;A5").
Hypothesis MSX : ltac2:(tb__ "0|0|
Se3S10S9eVAInv;VCST;VXGL;A5").
Variable Q : world -> Prop.

Let JM_erun (fds : list (word * FdEntry)) (nd : ndesc) (fuel : nat) (cuts : list Z) (A : axst) (leaves : list leafA) (rho : valuation) (tp : list word)
  (Hrun : sym_runA segs fuel cuts A true = Some leaves) (Hlen : ss_lenient (ax_S A) = false)
  (Hnf : (NF <=? ss_next (ax_S A))%positive = true) (Hnb : nd_below (ss_next (ax_S A)) nd = true) : ltac2:(tb__ "0|1|
S5aS1cSa3S5aR2Vleaves;A3S22S21S59VA;A1A1Vrho;R2A3S7eS10S34S10S38Vfds;Vnd;A2M0S5eR4A1R3Vtp;A5VQ;A3F_;F_;Frho';FL;S7eS10S34S10G0VA;Vrho;Vtp;A5VQ;A3F_;") := ltac2:(tb__ "0|3|
SddS10Vfuel;Vcuts;VA;Vleaves;S38Vfds;Vnd;A2Vrho;Vtp;VQ;VHrun;VHlen;S3dVfds;Vnd;S21S59VA;A1A1M0S18S11S5Sb4S41G0A2S6A3M1Sb3S41G0A2M2F_;G2G1F_;Sb5S41G0A2VHnf;A4VHnb;A5Ac").

Lemma open_step_ex_fail : ltac2:(tb__ "0|2|
S1cS2S19Q40A1M0A1S0S1cS12S52Z0R2A2S52R2Z1000A2A2S22S74R5R2A3S11G0S1dR3S74A2S45R4A1A3S7eS10S34S10S38S85S73A2M1S76R4R6A5VQ;A3F_;F_;F_;Frho';Fe;S7eS10S34S10G1S75R3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HE.
  destruct M_open as (Eaf & _ & _ & EvFD & _ & Hi & H17 & H10 & H12 & H11 & Hn & Hnf & Hb1 & Hb2 & _).
  pose proof Hnf as Hnf'. apply Pos.leb_le in Hnf.
  set (Jf := fun (r : valuation) (t : list word) (tr : list event) (md : Model) =>
               (exists e, 0 < e < 4096 /\ rw r vFD = errno_ret e) /\ JM std_fds nd_M r t tr md).
  eapply etriple_seq.
  { apply (etriple_openatA segs (JM std_fds nd_M) Jf E_op rho tp);
      [rewrite <- EvFD; apply JM_stable; [exact Hnf | exact Hb1] | rewrite <- EvFD | exact Hi | exact H17 | exact H10 | exact H12 | |].
    - intros r r' t tr md md' Hag Hme [(e & He & Hr) HJ]. split; [exists e; split; [exact He | rewrite <- (proj1 Hag vFD ltac:(lia)); exact Hr]|].
      eapply (JM_stable std_fds nd_M (Pos.succ vFD) ltac:(lia) Hb2); [exact Hag | exact Hme | exact HJ].
    - intros tr ms md Hsp HJ. destruct (JM_P0 _ _ _ _ _ _ HJ) as [[_ [Hrl0 [HL0 _]]] [Hw Hl]].
      apply (arg1_avoid rho tp tr ms md Hsp); [rewrite <- (Hl 3%positive); exact Hrl0 | rewrite <- (Hw 9%positive ltac:(unfold NF; lia)); exact HL0].
    - intros tr ms md Hsp HJ. destruct (JM_P0 _ _ _ _ _ _ HJ) as [[_ [Hrl0 [HL0 _]]] [Hw Hl]].
      assert (Hrl : firstn (length argv1 + 1) (rl rho 3%positive) = argv1 ++ [Z_to_bv 8 0]) by (rewrite <- (Hl 3%positive); exact Hrl0).
      assert (HL1 : bv_unsigned (rw rho 9%positive) = Z.of_nat (length argv1)) by (rewrite <- (Hw 9%positive ltac:(unfold NF; lia)); exact HL0).
      rewrite H11. unfold vA1. cbn [eval]. rewrite (arg1_cstr rho tp tr ms md Hsp Hrl HL1). unfold cstr1.
      split; [destruct (length argv1 <? 4096)%nat; [exact Hnsl | exact I]|].
      destruct (JM_Kc _ _ _ _ _ _ HJ) as (_ & Hfds & Hmdx).

      assert (EX : exists e, 0 < e < 4096 /\ openat_post md (if (length argv1 <? 4096)%nat then CstrOk argv1 else CstrTooLong) (errno_ret e) md).
      { destruct (Nat.ltb_spec (length argv1) 4096) as [Hlen|Hlen].
        2:{ exists ENAMETOOLONG. unfold ENAMETOOLONG. cbn [openat_post]. repeat split; lia. }
        unfold openat_post. destruct argv1 as [|b q] eqn:Ea; [exists ENOENT; unfold ENOENT; repeat split; lia|].
        rewrite (path_is_dirref_not_dotdot _ Hndd). destruct (path_eqb (b :: q) dot_path).
        - exists ENOMEM. split; [unfold ENOMEM; lia|]. left. exists ENOMEM. split; [left; reflexivity | auto].
        - destruct (fs_lookup (m_fs md) (b :: q)).
          + exists ENOMEM. split; [unfold ENOMEM; lia|]. left. exists ENOMEM. split; [left; reflexivity | auto].
          + exists ENOENT. unfold ENOENT. repeat split; lia. }
      destruct EX as (e & He & Hpost). exists (errno_ret e), md. split; [exact Hpost|].
      split; [exists e; split; [exact He | rewrite <- EvFD; apply rho_set_rw_at]|].
      rewrite <- EvFD. apply JM_set_rw; [exact Hnf | exact Hb1 | exact HJ]. }
  apply etriple_ex. intros rho'. apply etriple_pure. intros Hag. rewrite Eaf. rewrite <- EvFD in Hag.
  eapply (etriple_conseq (P := fun w => exists e, 0 < e < 4096 /\ rw rho' vFD = errno_ret e /\ SPA segs (JM std_fds nd_M) T_op rho' tp w));
    [intros w [Hsm [(e & He & Hr) HJ]] | intros w' Hw'; exact Hw' |].
  { exists e. split; [exact He|]. split; [exact Hr|]. split; [exact Hsm | exact HJ]. }
  apply etriple_ex. intros e. apply etriple_pure. intros He. apply etriple_pure. intros Hr. exact (HE e rho' He Hag Hr).
Qed.

Lemma open_step_ex_ok : ltac2:(tb__ "0|2|
S1cS2S19Q40M0A1M1A1S94Vargv1;VFS0;A2S1cS22S74R4R1A3S11G1S1dR2S74A2S1aG0Z3A2A3S7eS10S34S10S38S83Vargv1;A1S73A2S76R3R5A5VQ;A3F_;F_;Frho';S7eS10S34S10S38S85S73A2S75R4R3A5VQ;A3F_;F_;Ftp;Frho;").
Proof.
  intros rho tp Ho HO.
  destruct M_open as (Eaf & _ & _ & EvFD & _ & Hi & H17 & H10 & H12 & H11 & Hn & Hnf & Hb1 & Hb2 & _).
  pose proof Hnf as Hnf'. apply Pos.leb_le in Hnf.
  set (Jo := fun (r : valuation) (t : list word) (tr : list event) (md : Model) => rw r vFD = Z_to_bv 64 3 /\ JM (FD3 argv1) nd_M r t tr md).
  eapply etriple_seq.
  { apply (etriple_openatA segs (JM std_fds nd_M) Jo E_op rho tp);
      [rewrite <- EvFD; apply JM_stable; [exact Hnf | exact Hb1] | rewrite <- EvFD | exact Hi | exact H17 | exact H10 | exact H12 | |].
    - intros r r' t tr md md' Hag Hme [Hr HJ]. split; [rewrite <- (proj1 Hag vFD ltac:(lia)); exact Hr|].
      eapply (JM_stable (FD3 argv1) nd_M (Pos.succ vFD) ltac:(lia) Hb2); [exact Hag | exact Hme | exact HJ].
    - intros tr ms md Hsp HJ. destruct (JM_P0 _ _ _ _ _ _ HJ) as [[_ [Hrl0 [HL0 _]]] [Hw Hl]].
      apply (arg1_avoid rho tp tr ms md Hsp); [rewrite <- (Hl 3%positive); exact Hrl0 | rewrite <- (Hw 9%positive ltac:(unfold NF; lia)); exact HL0].
    - intros tr ms md Hsp HJ. destruct (JM_P0 _ _ _ _ _ _ HJ) as [[_ [Hrl0 [HL0 _]]] [Hw Hl]].
      assert (Hrl : firstn (length argv1 + 1) (rl rho 3%positive) = argv1 ++ [Z_to_bv 8 0]) by (rewrite <- (Hl 3%positive); exact Hrl0).
      assert (HL1 : bv_unsigned (rw rho 9%positive) = Z.of_nat (length argv1)) by (rewrite <- (Hw 9%positive ltac:(unfold NF; lia)); exact HL0).
      rewrite H11. unfold vA1. cbn [eval]. rewrite (arg1_cstr rho tp tr ms md Hsp Hrl HL1). unfold cstr1.
      split; [destruct (length argv1 <? 4096)%nat; [exact Hnsl | exact I]|].
      destruct (JM_Kc _ _ _ _ _ _ HJ) as (_ & Hfds & Hmdx).
      assert (Hpost : openat_post md (if (length argv1 <? 4096)%nat then CstrOk argv1 else CstrTooLong) (Z_to_bv 64 3) (with_fds (FD3 argv1) md)).
      { destruct Ho as (Hlen & Hne & Hor). rewrite PATH_MAX_eq in Hlen. destruct (Nat.ltb_spec (length argv1) 4096); [|lia].
        unfold openat_post. destruct argv1 as [|b q] eqn:Ea; [exfalso; exact (Hne eq_refl)|].
        rewrite Hfds, alloc_fd_std, lookup3_std, (path_is_dirref_not_dotdot _ Hndd). unfold FD3, open_entry.
        destruct (path_eqb (b :: q) dot_path) eqn:Hd.
        - right. split; [reflexivity|]. split; [reflexivity|]. unfold openat_dir_model. rewrite Hfds, alloc_fd_std. reflexivity.
        - destruct Hor as [Hdot|HF]; [rewrite Hdot, path_eqb_refl in Hd; discriminate|].
          rewrite (HMDXfs md Hmdx). destruct (fs_lookup FS0 (b :: q)) as [F|] eqn:HF'; [|exfalso; exact (HF eq_refl)].
          right. split; [reflexivity|]. split; [reflexivity|]. unfold openat_file_model. rewrite Hfds, alloc_fd_std. reflexivity. }
      exists (Z_to_bv 64 3), (with_fds (FD3 argv1) md). split; [exact Hpost|].
      split; [rewrite <- EvFD; apply rho_set_rw_at|].
      rewrite <- EvFD. apply JM_set_rw; [exact Hnf | exact Hb1 |]. apply (JM_with_fds std_fds). exact HJ. }
  apply etriple_ex. intros rho'. apply etriple_pure. intros Hag. rewrite Eaf. rewrite <- EvFD in Hag.
  eapply (etriple_conseq (P := fun w => rw rho' vFD = Z_to_bv 64 3 /\ SPA segs (JM (FD3 argv1) nd_M) T_op rho' tp w));
    [intros w [Hsm [Hr HJ]] | intros w' Hw'; exact Hw' |].
  { split; [exact Hr|]. split; [exact Hsm | exact HJ]. }
  apply etriple_pure. intros Hr. exact (HO rho' Hag Hr).
Qed.

Theorem m_ex_copen : ltac2:(tb__ "0|2|
S1cS2S19Q40A1A1M0S7eS10S34S10S38S85S73A2M1S77R2R1A5VQ;A3Ftp;Frho;S1cG0S7eS10S34S10G1S9dR2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros Hcopen rho tp.
  destruct M_runs as (Ru0 & _ & Ru1 & _ & Ru1F & _).
  destruct M_wf as (W0 & W1 & W1F & _).
  apply runwf_sound in W0 as (W0a & W0b & W0c). apply runwf_sound in W1F as (W1Fa & W1Fb & W1Fc).
  destruct M_open as (Eaf & E3 & EF & EvFD & EnT & _ & _ & _ & _ & _ & _ & Hnf & Hb1 & Hb2 & Fb3 & FbF & _).
  eapply (JM_erun std_fds nd_M); [exact Ru0 | exact W0b | exact W0a | exact W0c |].
  intros Lf rho1 [<-|[]] Hag1. cbn [la_state].
  apply open_step_ex_fail. intros e rho2 He Hag2 Hr.
  eapply (etriple_conseq (P := SPA segs (JM std_fds nd_M) T_opF rho2 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { rewrite <- EF. apply (SPA_addn segs); [exact HS | | rewrite EnT; exact FbF].
    assert (HU : bv_unsigned (rw rho2 vFD) = 2 ^ 64 - e).
    { rewrite Hr. unfold errno_ret. rewrite lit_unsigned, <- (Z.mod_add (- e) 1 (2 ^ 64)), Z.mod_small by lia. lia. }
    unfold err_facts. repeat constructor; cbn [holds eval]; rewrite HU, lit_unsigned, Z.mod_small by lia; lia. }
  eapply (JM_erun std_fds nd_M); [exact Ru1F | exact W1Fb | exact W1Fa | exact W1Fc |].
  intros Lf rho3 [<-|[]] Hag3. cbn [la_state]. apply Hcopen.
Qed.

Lemma m_ex_to_msite : ltac2:(tb__ "0|1|
S94Vargv1;VFS0;A2S1cS2S19Q40A1A1M0S7eS10S34S10S38S83Vargv1;A1S73A2S7bR2R1A5VQ;A3Ftp;Frho;S1cG0S7eS10S34S10S38S85S73A2S9dR2R1A5VQ;A3Ftp;Frho;F_;F_;").
Proof.
  intros Ho Hsite rho tp.
  destruct M_runs as (Ru0 & _ & Ru1 & _).
  destruct M_wf as (W0 & W1 & _).
  apply runwf_sound in W0 as (W0a & W0b & W0c). apply runwf_sound in W1 as (W1a & W1b & W1c).
  destruct M_open as (Eaf & E3 & EF & EvFD & EnT & _ & _ & _ & _ & _ & _ & Hnf & Hb1 & Hb2 & Fb3 & FbF & _).
  destruct M_malloc as (M1 & _).
  eapply (JM_erun std_fds nd_M); [exact Ru0 | exact W0b | exact W0a | exact W0c |].
  intros Lf rho1 [<-|[]] Hag1. cbn [la_state].
  apply (open_step_ex_ok rho1 tp Ho). intros rho2 Hag2 Hr.
  eapply (etriple_conseq (P := SPA segs (JM (FD3 argv1) nd_M) T_op3 rho2 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { rewrite <- E3. apply (SPA_addn segs); [exact HS | | rewrite EnT; exact Fb3].
    unfold fd3_facts. repeat constructor. cbn [holds eval]. rewrite Hr. reflexivity. }
  eapply (JM_erun (FD3 argv1) nd_M); [exact Ru1 | exact W1b | exact W1a | exact W1c |].
  intros Lf rho3o [<-|[]] Hag3. cbn [la_state].

  apply (errR_Te _ E_m65 _ rho3o tp (proj1 M_errR) (JA_errno_blind segs AInv CST XGL ALA HCST (fun a Ha => HCSTdrv a (errno_in_CST_drv a Ha)) NF (KcM (FD3 argv1)) rhoM P0M [] [] BX0 PA _ nd_M W1c)). intros rho3 _ _ _. rewrite (proj2 M_errR).
  eapply (etriple_conseq (P := SPA segs (JM (FD3 argv1) nd_M) C_m65 rho3 tp)); [intros w HS | intros w' Hw'; exact Hw' | apply Hsite].
  unfold C_m65. exact (SPA_split segs (JM (FD3 argv1) nd_M) rho3 E_m65r 0 (SLit (-128)) C_m65S tp w M1 HS).
Qed.

Theorem m_ex_R : ltac2:(tb__ "0|2|
S94Vargv1;VFS0;A2S1cS2S19Q40A1A1M0S7eS10S34S10S63VAInv;VCST;VXGL;S41S84VT0;VMDX;S83Vargv1;A1S4S43A1A4R2S86Vargv1;A1S4S3S0S0A2M1A1S4S3G1S0A2A1S6cVPA;S88AcS87R2R1A5VQ;A3Ftp;Frho;S1cG0S7eS10S34S10S38S85S73A2S9dR2R1A5VQ;A3Ftp;Frho;F_;F_;").
Proof.
  intros Ho HR. apply (m_ex_to_msite Ho). intros rho3 tp.
  destruct M_runs as (_ & _ & _ & _ & _ & _ & Ru2 & _).
  destruct M_wf as (_ & _ & _ & W2 & _). apply runwf_sound in W2 as (W2a & W2b & W2c).
  destruct M_malloc as (M1 & Mfr & Mcc & McN & McO & McT & Mnx & Mnb & Mbb & Ms12 & Mres & MvB & Mpay & Mspf & Mro & Mxr & MTn & MTk).
  apply (malloc_callA_ex_S segs AE_A AInv CST XGL ALA HCST HXGL NF (KcM (FD3 argv1)) rhoM P0M [] [] BX0 PA (KcM_ok _) PA [] UStopLe C_m65 s_m65 R_m65 rho3 tp
           nd_M bd_R0 Q malloc_shape_nil MSX Mfr McO McT Mnx Mnb Mbb).
  - rewrite Ms12. reflexivity.
  - exact Mres.
  - rewrite Ms12. apply payA_of_bud_pay. exact Mpay.
  - intros A A' HPA Hk. eapply HPAm; [| exact HPA | exact Hk]. rewrite Ms12. unfold uval. rewrite U_lit64 by lia. lia.
  - intros A kc _ _ HB. rewrite Ms12. unfold nd_M in HB. cbn [nd_bd nd_am] in HB. unfold uval. rewrite U_lit64 by lia. exact (room_M A kc rho3 HB).
  - reflexivity.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - apply (site_ok_drvM nd_M C_m65 s_m65 R_m65 rho3 None None); try assumption.
    + intros Ai HF' HN HZ. exact I.
    + intros Ai ms HF' HP0 Hav HN HD HZ HM. rewrite Ms12. split; [unfold uval; rewrite U_lit64 by lia; lia | exact I].
  - intros rho4 tp4. unfold PreM in MTk. rewrite MTk, MvB, Ms12. unfold nd_M. cbn [nd_tv nd_fr nd_am]. fold tv_R1. fold nd_R1.
    eapply (JM_erun (FD3 argv1) nd_R1); [exact Ru2 | exact W2b | exact W2a | exact W2c |].
    intros Lf rho5 [<-|[]] Hag5. cbn [la_state].
    destruct M_r0 as (Q1n & Q1e & Q1s & Q1f & Q2e & Q2s & Q3e & Q3b & Q2nx & Q2fx & QvB & QTP & _ & Hent & Hs24 & Hs9 & Hs1 & Hs11 & _ & _ & Qnx & Qnb & Qtv & Qfr & Qbd & Qam).
    apply etriple_factsA. intros HF5.
    assert (Hsp5 : 0x7fff80000000 <= bv_unsigned (eval rho5 sp0) <= 2 ^ 47 - 16).
    { unfold sp0. cbn [eval]. pose proof (proj1 (sp0_facts_sound rho5 _ HF5 Q1f)). lia. }
    eapply (etriple_conseq (P := SPA segs (JM (FD3 argv1) nd_R1) L_R0h rho5 tp4)); [intros w HS | intros w' Hw'; exact Hw' |].
    { exact (r0_reshape rho5 tp4 w Ho HF5 Hsp5 HS). }
    eapply (etriple_conseq (P := SPA segs (JA AInv CST XGL NF (KcG T0 MDX (FD3 argv1) []) (rho_sub rho5 s_R0) (P0Z argv1) [] [] BX0 PA nd_R0) S_R0 (rho_sub rho5 s_R0) tp4));
      [intros w HS | intros w' Hw'; exact Hw' | apply HR].
    exact (r0_reorigin rho5 tp4 w HS).
Qed.
End Ex.
End M.
